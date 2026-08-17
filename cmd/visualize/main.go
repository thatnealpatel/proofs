package main

import (
	"context"
	"crypto/rand"
	"embed"
	"encoding/hex"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"io"
	"io/fs"
	"log"
	"mime"
	"net"
	"net/http"
	"net/url"
	"os"
	"os/signal"
	"path/filepath"
	"strings"
	"sync"
	"syscall"
	"time"
)

const (
	defaultAddress          = "127.0.0.1:11111"
	maximumChunkBytes       = int64(2 << 20)
	maximumExportBytes      = int64(256 << 20)
	maximumPendingExports   = 2
	maximumCompletedExports = 8
	maximumStoredBytes      = int64(512 << 20)
	pendingExportLifetime   = 15 * time.Minute
	exportSweepInterval     = time.Minute
	uploadTimeout           = 30 * time.Second
	shutdownTimeout         = 10 * time.Second
)

var (
	errExportClosed   = errors.New("export is no longer open")
	errExportTooLarge = errors.New("export exceeds the maximum size")
)

// staticFiles is embedded so the visualizer works regardless of the process's
// current working directory.
//
//go:embed static/*
var staticFiles embed.FS

type pendingExport struct {
	mu sync.Mutex

	cond          *sync.Cond
	file          *os.File
	temporaryName string
	finalName     string
	written       int64
	expiresAt     time.Time
	closing       bool
	closed        bool
	nextBodyID    uint64
	activeBodies  map[uint64]io.ReadCloser
}

func newPendingExport(file *os.File, finalName string, expiresAt time.Time) *pendingExport {
	export := &pendingExport{
		file:          file,
		temporaryName: file.Name(),
		finalName:     finalName,
		expiresAt:     expiresAt,
		activeBodies:  make(map[uint64]io.ReadCloser),
	}
	export.cond = sync.NewCond(&export.mu)
	return export
}

func (e *pendingExport) beginBody(body io.ReadCloser, expiresAt time.Time) (uint64, bool) {
	e.mu.Lock()
	defer e.mu.Unlock()
	if e.closed || e.closing {
		return 0, false
	}
	e.nextBodyID++
	id := e.nextBodyID
	e.activeBodies[id] = body
	e.expiresAt = expiresAt
	return id, true
}

func (e *pendingExport) failBody(id uint64) {
	e.mu.Lock()
	delete(e.activeBodies, id)
	e.cond.Broadcast()
	e.mu.Unlock()
}

func (e *pendingExport) appendBody(id uint64, data []byte, limit int64, expiresAt time.Time) error {
	e.mu.Lock()
	defer e.mu.Unlock()
	defer e.cond.Broadcast()
	delete(e.activeBodies, id)
	if e.closed || e.closing {
		return errExportClosed
	}
	if int64(len(data)) > limit-e.written {
		return errExportTooLarge
	}
	written, err := e.file.Write(data)
	e.written += int64(written)
	if err != nil {
		return err
	}
	if written != len(data) {
		return io.ErrShortWrite
	}
	e.expiresAt = expiresAt
	return nil
}

func (e *pendingExport) publish() (string, int64, error) {
	e.mu.Lock()
	if e.closed || e.closing {
		e.mu.Unlock()
		return "", 0, errExportClosed
	}
	e.closing = true
	for len(e.activeBodies) != 0 && !e.closed {
		e.cond.Wait()
	}
	if e.closed {
		e.mu.Unlock()
		return "", 0, errExportClosed
	}

	file := e.file
	e.file = nil
	if err := file.Sync(); err != nil {
		e.closed = true
		e.mu.Unlock()
		return "", 0, errors.Join(err, closeAndRemove(file, e.temporaryName))
	}
	if err := file.Close(); err != nil {
		e.closed = true
		e.mu.Unlock()
		return "", 0, errors.Join(err, removeFile(e.temporaryName))
	}
	if err := os.Rename(e.temporaryName, e.finalName); err != nil {
		e.closed = true
		e.mu.Unlock()
		return "", 0, errors.Join(err, removeFile(e.temporaryName))
	}
	path, written := e.finalName, e.written
	e.closed = true
	e.mu.Unlock()
	return path, written, nil
}

func (e *pendingExport) detachForAbort(expiredAt *time.Time) (*os.File, []io.ReadCloser, bool) {
	e.mu.Lock()
	defer e.mu.Unlock()
	if e.closed || expiredAt != nil && expiredAt.Before(e.expiresAt) {
		return nil, nil, false
	}
	e.closed = true
	e.closing = true
	file := e.file
	e.file = nil
	bodies := make([]io.ReadCloser, 0, len(e.activeBodies))
	for _, body := range e.activeBodies {
		bodies = append(bodies, body)
	}
	e.activeBodies = make(map[uint64]io.ReadCloser)
	e.cond.Broadcast()
	return file, bodies, true
}

func (e *pendingExport) cleanupAborted(file *os.File, bodies []io.ReadCloser) error {
	var errs []error
	for _, body := range bodies {
		if err := body.Close(); err != nil {
			errs = append(errs, fmt.Errorf("close request body: %w", err))
		}
	}
	if file != nil {
		if err := file.Close(); err != nil {
			errs = append(errs, fmt.Errorf("close export: %w", err))
		}
	}
	if err := removeFile(e.temporaryName); err != nil {
		errs = append(errs, err)
	}
	return errors.Join(errs...)
}

func (e *pendingExport) abort() error {
	file, bodies, ok := e.detachForAbort(nil)
	if !ok {
		return nil
	}
	return e.cleanupAborted(file, bodies)
}

func (e *pendingExport) abortIfExpired(now time.Time) (bool, error) {
	file, bodies, expired := e.detachForAbort(&now)
	if !expired {
		return false, nil
	}
	return true, e.cleanupAborted(file, bodies)
}

type completedExport struct {
	path  string
	bytes int64
}

type workbenchExporter struct {
	dir        string
	privateDir bool

	mu        sync.Mutex
	pending   map[string]*pendingExport
	completed []completedExport
	stored    int64
	closed    bool
	stop      chan struct{}
	done      chan struct{}
	now       func() time.Time

	maxPending   int
	maxExport    int64
	maxCompleted int
	maxStored    int64
	lifetime     time.Duration
}

func newWorkbenchExporter(exportDir string) (*workbenchExporter, error) {
	privateDir := exportDir == ""
	if privateDir {
		var err error
		exportDir, err = os.MkdirTemp("", "proofs-viz-")
		if err != nil {
			return nil, fmt.Errorf("create private export directory: %w", err)
		}
	} else {
		if err := os.MkdirAll(exportDir, 0o700); err != nil {
			return nil, fmt.Errorf("create export directory: %w", err)
		}
		info, err := os.Lstat(exportDir)
		if err != nil {
			return nil, fmt.Errorf("inspect export directory: %w", err)
		}
		if !info.IsDir() || info.Mode()&os.ModeSymlink != 0 {
			return nil, fmt.Errorf("export path %q is not a directory", exportDir)
		}
	}

	exporter := &workbenchExporter{
		dir:          exportDir,
		privateDir:   privateDir,
		pending:      make(map[string]*pendingExport),
		stop:         make(chan struct{}),
		done:         make(chan struct{}),
		now:          time.Now,
		maxPending:   maximumPendingExports,
		maxExport:    maximumExportBytes,
		maxCompleted: maximumCompletedExports,
		maxStored:    maximumStoredBytes,
		lifetime:     pendingExportLifetime,
	}
	go exporter.reapLoop()
	return exporter, nil
}

func (e *workbenchExporter) reapLoop() {
	defer close(e.done)
	ticker := time.NewTicker(exportSweepInterval)
	defer ticker.Stop()
	for {
		select {
		case now := <-ticker.C:
			e.expire(now)
		case <-e.stop:
			return
		}
	}
}

func (e *workbenchExporter) expire(now time.Time) {
	e.mu.Lock()
	pending := make(map[string]*pendingExport, len(e.pending))
	for token, export := range e.pending {
		pending[token] = export
	}
	e.mu.Unlock()

	for token, export := range pending {
		expired, err := export.abortIfExpired(now)
		if !expired {
			continue
		}
		e.remove(token, export)
		if err != nil {
			log.Printf("expire workbench export: %v", err)
		}
	}
}

func (e *workbenchExporter) lookup(token string) *pendingExport {
	e.mu.Lock()
	defer e.mu.Unlock()
	return e.pending[token]
}

func (e *workbenchExporter) remove(token string, export *pendingExport) bool {
	e.mu.Lock()
	defer e.mu.Unlock()
	if e.pending[token] != export {
		return false
	}
	delete(e.pending, token)
	return true
}

func (e *workbenchExporter) abortExport(token string, export *pendingExport) error {
	e.remove(token, export)
	return export.abort()
}

func (e *workbenchExporter) recordCompleted(path string, size int64) {
	e.mu.Lock()
	e.completed = append(e.completed, completedExport{path: path, bytes: size})
	e.stored += size
	var remove []completedExport
	for len(e.completed) > e.maxCompleted || e.stored > e.maxStored {
		oldest := e.completed[0]
		e.completed = e.completed[1:]
		e.stored -= oldest.bytes
		remove = append(remove, oldest)
	}
	e.mu.Unlock()
	for _, export := range remove {
		if err := removeFile(export.path); err != nil {
			log.Printf("remove old workbench export: %v", err)
		}
	}
}

func (e *workbenchExporter) Close() error {
	e.mu.Lock()
	if e.closed {
		e.mu.Unlock()
		return nil
	}
	e.closed = true
	close(e.stop)
	pending := make([]*pendingExport, 0, len(e.pending))
	for _, export := range e.pending {
		pending = append(pending, export)
	}
	e.pending = make(map[string]*pendingExport)
	e.mu.Unlock()

	<-e.done
	var errs []error
	for _, export := range pending {
		if err := export.abort(); err != nil {
			errs = append(errs, err)
		}
	}
	if e.privateDir {
		if err := os.Remove(e.dir); err != nil && !errors.Is(err, os.ErrNotExist) && !errors.Is(err, syscall.ENOTEMPTY) {
			errs = append(errs, fmt.Errorf("remove private export directory: %w", err))
		}
	}
	return errors.Join(errs...)
}

func newHandler(exportDir string) (http.Handler, *workbenchExporter, error) {
	assets, err := fs.Sub(staticFiles, "static")
	if err != nil {
		return nil, nil, fmt.Errorf("open embedded UI: %w", err)
	}
	exporter, err := newWorkbenchExporter(exportDir)
	if err != nil {
		return nil, nil, err
	}
	files := http.FileServerFS(assets)
	handler := http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("X-Content-Type-Options", "nosniff")
		switch r.URL.Path {
		case "/api/export/workbench/start":
			exporter.start(w, r)
			return
		case "/api/export/workbench/chunk":
			exporter.chunk(w, r)
			return
		case "/api/export/workbench/finish":
			exporter.finish(w, r)
			return
		case "/api/export/workbench/cancel":
			exporter.cancel(w, r)
			return
		}
		if r.Method != http.MethodGet && r.Method != http.MethodHead {
			w.Header().Set("Allow", "GET, HEAD")
			http.Error(w, "method not allowed", http.StatusMethodNotAllowed)
			return
		}
		files.ServeHTTP(w, r)
	})
	return handler, exporter, nil
}

func (e *workbenchExporter) start(w http.ResponseWriter, r *http.Request) {
	if !requireMutationRequest(w, r) {
		return
	}
	e.expire(e.now())

	e.mu.Lock()
	if e.closed {
		e.mu.Unlock()
		http.Error(w, "export service is shutting down", http.StatusServiceUnavailable)
		return
	}
	if len(e.pending) >= e.maxPending {
		e.mu.Unlock()
		http.Error(w, "too many pending exports", http.StatusTooManyRequests)
		return
	}
	tokenBytes := make([]byte, 16)
	rand.Read(tokenBytes)
	token := hex.EncodeToString(tokenBytes)
	slug := safeSlug(r.Header.Get("X-Proofs-Viz-Construction"))
	temporary, err := os.CreateTemp(e.dir, "."+slug+"-workbench-*.json.tmp")
	if err != nil {
		e.mu.Unlock()
		http.Error(w, fmt.Sprintf("create export: %v", err), http.StatusInternalServerError)
		return
	}
	name := fmt.Sprintf("%s-workbench-%s-%s.json", slug, e.now().UTC().Format("20060102T150405.000000000Z"), token[:8])
	e.pending[token] = newPendingExport(temporary, filepath.Join(e.dir, name), e.now().Add(e.lifetime))
	e.mu.Unlock()
	writeJSON(w, struct {
		Token string `json:"token"`
	}{Token: token})
}

func (e *workbenchExporter) chunk(w http.ResponseWriter, r *http.Request) {
	if !requireMutationRequest(w, r) {
		return
	}
	mediaType, _, err := mime.ParseMediaType(r.Header.Get("Content-Type"))
	if err != nil || mediaType != "application/octet-stream" {
		http.Error(w, "Content-Type must be application/octet-stream", http.StatusUnsupportedMediaType)
		return
	}

	token := r.Header.Get("X-Proofs-Viz-Export-Token")
	export := e.lookup(token)
	if export == nil {
		http.Error(w, "unknown export token", http.StatusNotFound)
		return
	}
	body := http.MaxBytesReader(w, r.Body, maximumChunkBytes)
	bodyID, ok := export.beginBody(body, e.now().Add(e.lifetime))
	if !ok {
		if err := body.Close(); err != nil {
			log.Printf("close rejected export body: %v", err)
		}
		http.Error(w, "export is no longer open", http.StatusConflict)
		return
	}
	timer := time.AfterFunc(uploadTimeout, func() {
		if err := body.Close(); err != nil {
			log.Printf("close timed-out export body: %v", err)
		}
	})
	data, readErr := io.ReadAll(body)
	if !timer.Stop() {
		readErr = errors.Join(readErr, context.DeadlineExceeded)
	}
	if err := body.Close(); err != nil {
		readErr = errors.Join(readErr, err)
	}
	if readErr != nil {
		export.failBody(bodyID)
		cleanupErr := e.abortExport(token, export)
		http.Error(w, fmt.Sprintf("read export chunk: %v", errors.Join(readErr, cleanupErr)), http.StatusBadRequest)
		return
	}
	if err := export.appendBody(bodyID, data, e.maxExport, e.now().Add(e.lifetime)); err != nil {
		cleanupErr := e.abortExport(token, export)
		status := http.StatusBadRequest
		if errors.Is(err, errExportTooLarge) {
			status = http.StatusRequestEntityTooLarge
		}
		http.Error(w, fmt.Sprintf("write export chunk: %v", errors.Join(err, cleanupErr)), status)
		return
	}
	w.WriteHeader(http.StatusNoContent)
}

func (e *workbenchExporter) finish(w http.ResponseWriter, r *http.Request) {
	if !requireMutationRequest(w, r) {
		return
	}
	token := r.Header.Get("X-Proofs-Viz-Export-Token")
	export := e.lookup(token)
	if export == nil {
		http.Error(w, "unknown export token", http.StatusNotFound)
		return
	}
	path, written, err := export.publish()
	if err != nil {
		cleanupErr := e.abortExport(token, export)
		http.Error(w, fmt.Sprintf("publish export: %v", errors.Join(err, cleanupErr)), http.StatusInternalServerError)
		return
	}
	e.remove(token, export)
	e.recordCompleted(path, written)
	writeJSON(w, struct {
		Path  string `json:"path"`
		Bytes int64  `json:"bytes"`
	}{Path: path, Bytes: written})
}

func (e *workbenchExporter) cancel(w http.ResponseWriter, r *http.Request) {
	if !requireMutationRequest(w, r) {
		return
	}
	token := r.Header.Get("X-Proofs-Viz-Export-Token")
	if export := e.lookup(token); export != nil {
		if err := e.abortExport(token, export); err != nil {
			http.Error(w, fmt.Sprintf("cancel export: %v", err), http.StatusInternalServerError)
			return
		}
	}
	w.WriteHeader(http.StatusNoContent)
}

func requireMutationRequest(w http.ResponseWriter, r *http.Request) bool {
	if r.Method != http.MethodPost {
		w.Header().Set("Allow", "POST")
		http.Error(w, "method not allowed", http.StatusMethodNotAllowed)
		return false
	}
	if site := r.Header.Get("Sec-Fetch-Site"); site == "cross-site" {
		http.Error(w, "cross-site export request rejected", http.StatusForbidden)
		return false
	}
	origin := r.Header.Get("Origin")
	if origin == "" {
		return true
	}
	parsed, err := url.Parse(origin)
	if err != nil || (parsed.Scheme != "http" && parsed.Scheme != "https") || !strings.EqualFold(parsed.Host, r.Host) {
		http.Error(w, "cross-origin export request rejected", http.StatusForbidden)
		return false
	}
	return true
}

func writeJSON(w http.ResponseWriter, value any) {
	w.Header().Set("Content-Type", "application/json")
	if err := json.NewEncoder(w).Encode(value); err != nil {
		log.Printf("report workbench export: %v", err)
	}
}

func safeSlug(value string) string {
	value = strings.ToLower(value)
	var out strings.Builder
	separator := false
	for _, r := range value {
		if r >= 'a' && r <= 'z' || r >= '0' && r <= '9' || r == '-' || r == '_' {
			out.WriteRune(r)
			separator = r == '-'
		} else if out.Len() > 0 && !separator {
			out.WriteByte('-')
			separator = true
		}
		if out.Len() >= 64 {
			break
		}
	}
	result := strings.Trim(out.String(), "-")
	if result == "" {
		return "workbench"
	}
	return result
}

func closeAndRemove(file *os.File, name string) error {
	return errors.Join(file.Close(), removeFile(name))
}

func removeFile(name string) error {
	if err := os.Remove(name); err != nil && !errors.Is(err, os.ErrNotExist) {
		return fmt.Errorf("remove export %q: %w", name, err)
	}
	return nil
}

func loopbackAddress(address string) bool {
	host, _, err := net.SplitHostPort(address)
	if err != nil {
		return false
	}
	host = strings.Trim(host, "[]")
	return strings.EqualFold(host, "localhost") || net.ParseIP(host).IsLoopback()
}

func run() (err error) {
	addr := flag.String("addr", defaultAddress, "HTTP listen address")
	allowRemote := flag.Bool("allow-remote", false, "permit a non-loopback listen address; access control is delegated to the host network")
	flag.Parse()
	if !*allowRemote && !loopbackAddress(*addr) {
		return fmt.Errorf("refusing non-loopback address %q without -allow-remote", *addr)
	}

	handler, exporter, err := newHandler("")
	if err != nil {
		return err
	}
	defer func() {
		err = errors.Join(err, exporter.Close())
	}()

	server := &http.Server{
		Addr:              *addr,
		Handler:           handler,
		ReadHeaderTimeout: 5 * time.Second,
		ReadTimeout:       uploadTimeout,
		WriteTimeout:      uploadTimeout,
		IdleTimeout:       time.Minute,
	}
	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer stop()
	serverErrors := make(chan error, 1)
	go func() {
		serverErrors <- server.ListenAndServe()
	}()

	log.Printf("matrix multiplication tensor visualizer: http://%s", *addr)
	select {
	case serveErr := <-serverErrors:
		if !errors.Is(serveErr, http.ErrServerClosed) {
			return serveErr
		}
		return nil
	case <-ctx.Done():
		shutdownCtx, cancel := context.WithTimeout(context.Background(), shutdownTimeout)
		defer cancel()
		if shutdownErr := server.Shutdown(shutdownCtx); shutdownErr != nil {
			return errors.Join(shutdownErr, server.Close())
		}
		return nil
	}
}

func main() {
	if err := run(); err != nil {
		log.Fatal(err)
	}
}
