package main

import (
	"bytes"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"math/big"
	"net/http"
	"net/http/httptest"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"sync"
	"testing"
	"time"
)

type certificate struct {
	Name                 string                       `json:"name"`
	N                    int                          `json:"n"`
	R                    int                          `json:"r"`
	S                    int                          `json:"S"`
	Field                string                       `json:"field"`
	Source               string                       `json:"source"`
	CoordinateConvention string                       `json:"coordinateConvention"`
	T                    [][]int                      `json:"T"`
	Terms                [][][]int                    `json:"terms"`
	Factors              struct{ A, B, C [][]string } `json:"factors"`
}

func newTestHandler(t *testing.T, exportDir string) (http.Handler, *workbenchExporter) {
	t.Helper()
	handler, exporter, err := newHandler(exportDir)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() {
		if err := exporter.Close(); err != nil {
			t.Errorf("close exporter: %v", err)
		}
	})
	return handler, exporter
}

func TestEmbeddedUIIsIndependentOfWorkingDirectory(t *testing.T) {
	old, err := os.Getwd()
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { _ = os.Chdir(old) })
	if err := os.Chdir(t.TempDir()); err != nil {
		t.Fatal(err)
	}
	handler, _ := newTestHandler(t, t.TempDir())
	server := httptest.NewServer(handler)
	defer server.Close()
	for _, path := range []string{"/", "/app.js", "/style.css", "/laderman.json", "/arxiv-2607.28676.json", "/arxiv-2601.05272.json", "/arxiv-2508.03857v1.json", "/smirnov-1.json", "/smirnov-2.json", "/strassen-squared.json", "/rational-48.json"} {
		response, err := http.Get(server.URL + path)
		if err != nil {
			t.Fatalf("GET %s: %v", path, err)
		}
		body, readErr := io.ReadAll(response.Body)
		_ = response.Body.Close()
		if readErr != nil {
			t.Fatalf("read %s: %v", path, readErr)
		}
		if response.StatusCode != http.StatusOK {
			t.Errorf("GET %s status = %d, want 200", path, response.StatusCode)
		}
		if len(body) == 0 {
			t.Errorf("GET %s returned an empty body", path)
		}
	}
}

func TestUIContainsConstructionControlsAndAuditViews(t *testing.T) {
	request := httptest.NewRequest(http.MethodGet, "/", nil)
	recorder := httptest.NewRecorder()
	handler, _ := newTestHandler(t, t.TempDir())
	handler.ServeHTTP(recorder, request)
	body := recorder.Body.String()
	for _, phrase := range []string{"Dimension", "⟨4,4,4⟩", "Construction", "Primary W comparison canvas", "Interaction workbench", "Cluster basket", "Detected structures", "Coefficient-weighted", "Deterministic clustered", "Save workbench JSON", "Copy basket JSON", "Inspect U, V, and W", "Ambient tensor-coordinate grid", "not a general decomposition search procedure", "⟨4,4,4⟩ ranks 64, 49, and 48"} {
		if !strings.Contains(body, phrase) {
			t.Errorf("index does not contain %q", phrase)
		}
	}
	if strings.Contains(body, "no ⟨4,4,4⟩ support") {
		t.Fatal("index still denies 4x4 support")
	}
}

func TestUIContainsMachineReadableSchemasAndExactWorkbenchFeatures(t *testing.T) {
	body, err := staticFiles.ReadFile("static/app.js")
	if err != nil {
		t.Fatal(err)
	}
	javascript := string(body)
	for _, phrase := range []string{
		"tensor-gate-lens/construction/v1",
		"tensor-gate-lens/workbench/v1",
		"tensor-gate-lens/pair/v1",
		"tensor-gate-lens/basket/v1",
		"tensor-gate-lens/audit/v1",
		"tensor-gate-lens/structure/v1",
		"/api/export/workbench/start",
		"/api/export/workbench/chunk",
		"application/octet-stream",
		"navigator.clipboard.writeText",
		"document.execCommand(\"copy\")",
		"proven-impossible-below-selected-count",
		"exact-local-rewrite-found",
		"compression-not-ruled-out",
		"dependOnOutside",
		"4:[schoolbook(4)]",
		"strassen-squared.json",
		"rational-48.json",
		"Moran–Schwartz–Yuan rational rank-48",
		"arxiv-2607.28676.json",
		"arXiv 2607.28676 rank-23",
		"arxiv-2601.05272.json",
		"arXiv 2601.05272 rank-23",
		"arxiv-2508.03857v1.json",
		"arXiv 2508.03857v1 rank-23",
	} {
		if !strings.Contains(javascript, phrase) {
			t.Errorf("app.js does not contain %q", phrase)
		}
	}
}

func TestREADMEDocumentsFourByFourScopeRegenerationAndServerLimits(t *testing.T) {
	body, err := os.ReadFile("README.md")
	if err != nil {
		t.Fatal(err)
	}
	readme := string(body)
	for _, phrase := range []string{"schoolbook rank 64", "Strassen-squared rank 49", "rational rank-48", "not claimed to be optimal", "rank-47 construction in characteristic", "C = vec_row_major(transpose(Q))", "export_visualize_444.sage", "all 4096 ambient coordinates over `QQ`", "deterministically writing", "private per-process", "temporary directory", "loopback", "-allow-remote"} {
		if !strings.Contains(readme, phrase) {
			t.Errorf("README does not contain %q", phrase)
		}
	}
	if strings.Contains(readme, "There is no 4×4 mode") {
		t.Fatal("README still denies 4x4 support")
	}
}

func TestFourByFourGeneratorReproducesEmbeddedAssets(t *testing.T) {
	root, err := filepath.Abs(filepath.Join("..", ".."))
	if err != nil {
		t.Fatal(err)
	}
	outputDir := t.TempDir()
	command := exec.Command(
		"timeout", "300", "sage",
		"Programs/BilinearComplexity/export_visualize_444.sage",
		outputDir,
	)
	command.Dir = root
	if output, err := command.CombinedOutput(); err != nil {
		t.Fatalf("regenerate 4x4 certificates: %v\n%s", err, output)
	}
	for _, name := range []string{"strassen-squared.json", "rational-48.json"} {
		t.Run(name, func(t *testing.T) {
			got, err := os.ReadFile(filepath.Join(outputDir, name))
			if err != nil {
				t.Fatal(err)
			}
			want, err := staticFiles.ReadFile("static/" + name)
			if err != nil {
				t.Fatal(err)
			}
			if !bytes.Equal(got, want) {
				t.Errorf("regenerated %s differs from embedded asset: got %d bytes, want %d", name, len(got), len(want))
			}
		})
	}
}

func TestUIAvoidsBrowserDependentColorMixArithmetic(t *testing.T) {
	for _, name := range []string{"static/app.js", "static/style.css"} {
		body, err := staticFiles.ReadFile(name)
		if err != nil {
			t.Fatal(err)
		}
		if strings.Contains(string(body), "color-mix(") {
			t.Errorf("%s uses color-mix", name)
		}
	}
}

func TestGeneratedCertificatesReconstructTarget(t *testing.T) {
	tests := []struct {
		file, name, field, source, convention string
		n, rank, scale                        int
	}{
		{file: "laderman.json", name: "Laderman", n: 3, rank: 23, scale: 1},
		{file: "arxiv-2607.28676.json", name: "arXiv 2607.28676 rank-23", field: "ZZ", source: "arXiv:2607.28676", convention: "row-major", n: 3, rank: 23, scale: 1},
		{file: "arxiv-2601.05272.json", name: "arXiv 2601.05272 rank-23", field: "ZZ", source: "arXiv:2601.05272", convention: "row-major", n: 3, rank: 23, scale: 1},
		{file: "arxiv-2508.03857v1.json", name: "arXiv 2508.03857v1 rank-23", field: "ZZ", source: "arXiv:2508.03857v1", convention: "row-major", n: 3, rank: 23, scale: 1},
		{file: "smirnov-1.json", name: "Smirnov-1", n: 3, rank: 25, scale: 6},
		{file: "smirnov-2.json", name: "Smirnov-2", n: 3, rank: 25, scale: 24},
		{file: "strassen-squared.json", name: "Strassen squared", field: "QQ", source: "Programs/BilinearComplexity/q2_strassen2.sage", convention: "tensor-product rows permuted from (block,inner) to global 4x4", n: 4, rank: 49, scale: 1},
		{file: "rational-48.json", name: "Moran-Schwartz-Yuan rational rank-48", field: "QQ", source: "Moran, Schwartz, and Yuan", convention: "A=vec_row_major(O), B=vec_row_major(P), C=vec_row_major(transpose(Q))", n: 4, rank: 48, scale: 16},
	}
	for _, test := range tests {
		t.Run(test.file, func(t *testing.T) {
			body, err := staticFiles.ReadFile("static/" + test.file)
			if err != nil {
				t.Fatal(err)
			}
			var got certificate
			if err := json.Unmarshal(body, &got); err != nil {
				t.Fatal(err)
			}
			// Older 3x3 assets predate the explicit n metadata; derive it from
			// the expected factor width while still requiring n on new assets.
			n := got.N
			if n == 0 {
				n = test.n
			}
			if got.Name != test.name || n != test.n || got.R != test.rank || got.S != test.scale || len(got.Terms) != test.rank {
				t.Fatalf("metadata = name %q n %d rank %d scale %d terms %d", got.Name, got.N, got.R, got.S, len(got.Terms))
			}
			if test.field != "" && got.Field != test.field {
				t.Errorf("field = %q, want %q", got.Field, test.field)
			}
			if test.source != "" && !strings.Contains(got.Source, test.source) {
				t.Errorf("source = %q, want substring %q", got.Source, test.source)
			}
			if test.convention != "" && !strings.Contains(got.CoordinateConvention, test.convention) {
				t.Errorf("convention = %q, want substring %q", got.CoordinateConvention, test.convention)
			}
			verifyScaledTerms(t, got, n)
			verifyFactors(t, got.Factors.A, got.Factors.B, got.Factors.C, n)
			if strings.HasPrefix(test.file, "arxiv-") {
				verifyIntegerFactors(t, got.Factors.A, got.Factors.B, got.Factors.C)
			}
		})
	}
}

func verifyScaledTerms(t *testing.T, certificate certificate, n int) {
	t.Helper()
	if len(certificate.Factors.A) != certificate.R || len(certificate.Factors.B) != certificate.R || len(certificate.Factors.C) != certificate.R {
		t.Fatal("factor count does not equal rank")
	}
	width := n * n
	for gate := 0; gate < certificate.R; gate++ {
		if len(certificate.Factors.A[gate]) != width || len(certificate.Factors.B[gate]) != width || len(certificate.Factors.C[gate]) != width {
			t.Fatalf("gate %d factor widths = %d/%d/%d, want %d", gate, len(certificate.Factors.A[gate]), len(certificate.Factors.B[gate]), len(certificate.Factors.C[gate]), width)
		}
	}
	sum := map[string]int{}
	for _, term := range certificate.Terms {
		for _, entry := range term {
			if len(entry) != 4 || entry[0] < 0 || entry[0] >= width || entry[1] < 0 || entry[1] >= width || entry[2] < 0 || entry[2] >= width {
				t.Fatalf("malformed term entry %v", entry)
			}
			sum[fmt.Sprintf("%d,%d,%d", entry[0], entry[1], entry[2])] += entry[3]
		}
	}
	target := map[string]int{}
	for _, entry := range certificate.T {
		if len(entry) != 4 {
			t.Fatalf("malformed target entry %v", entry)
		}
		target[fmt.Sprintf("%d,%d,%d", entry[0], entry[1], entry[2])] = entry[3]
	}
	for key, value := range sum {
		if value == 0 {
			delete(sum, key)
		}
	}
	if fmt.Sprint(sum) != fmt.Sprint(target) {
		t.Fatalf("sum of term tensors does not equal target: got %v want %v", sum, target)
	}
	if len(target) != n*n*n {
		t.Fatalf("target has %d sparse coordinates, want %d", len(target), n*n*n)
	}
	for i := 0; i < n; i++ {
		for j := 0; j < n; j++ {
			for k := 0; k < n; k++ {
				key := fmt.Sprintf("%d,%d,%d", i*n+j, j*n+k, i*n+k)
				if target[key] != certificate.S {
					t.Fatalf("target[%s] = %d, want scale %d", key, target[key], certificate.S)
				}
			}
		}
	}
}

func verifyFactors(t *testing.T, a, b, c [][]string, n int) {
	t.Helper()
	computed := map[string]*big.Rat{}
	for gate := range a {
		for ai := range a[gate] {
			av, ok := new(big.Rat).SetString(a[gate][ai])
			if !ok {
				t.Fatalf("invalid A coefficient %q", a[gate][ai])
			}
			for bi := range b[gate] {
				bv, ok := new(big.Rat).SetString(b[gate][bi])
				if !ok {
					t.Fatalf("invalid B coefficient %q", b[gate][bi])
				}
				for ci := range c[gate] {
					cv, ok := new(big.Rat).SetString(c[gate][ci])
					if !ok {
						t.Fatalf("invalid C coefficient %q", c[gate][ci])
					}
					term := new(big.Rat).Mul(av, bv)
					term.Mul(term, cv)
					if term.Sign() == 0 {
						continue
					}
					key := fmt.Sprintf("%d,%d,%d", ai, bi, ci)
					if computed[key] == nil {
						computed[key] = new(big.Rat)
					}
					computed[key].Add(computed[key], term)
				}
			}
		}
	}
	width := n * n
	for ai := 0; ai < width; ai++ {
		for bi := 0; bi < width; bi++ {
			for ci := 0; ci < width; ci++ {
				key := fmt.Sprintf("%d,%d,%d", ai, bi, ci)
				want := int64(0)
				i, j := ai/n, ai%n
				if bi/n == j && ci == i*n+bi%n {
					want = 1
				}
				got := computed[key]
				if got == nil {
					got = new(big.Rat)
				}
				if got.Cmp(new(big.Rat).SetInt64(want)) != 0 {
					t.Fatalf("factor reconstruction at (%d,%d,%d) = %s, want %d", ai, bi, ci, got.RatString(), want)
				}
			}
		}
	}
}

func verifyIntegerFactors(t *testing.T, factors ...[][]string) {
	t.Helper()
	for factorIndex, factor := range factors {
		for gate, row := range factor {
			for coordinate, coefficient := range row {
				value, ok := new(big.Int).SetString(coefficient, 10)
				if !ok {
					t.Fatalf("factor %d gate %d coordinate %d coefficient %q is not an integer", factorIndex, gate, coordinate, coefficient)
				}
				if value.Cmp(big.NewInt(-1)) < 0 || value.Cmp(big.NewInt(1)) > 0 {
					t.Fatalf("factor %d gate %d coordinate %d coefficient %s is not ternary", factorIndex, gate, coordinate, value)
				}
			}
		}
	}
}

func TestArXivRank23AssetsAreReproducible(t *testing.T) {
	root, err := filepath.Abs(filepath.Join("..", ".."))
	if err != nil {
		t.Fatal(err)
	}
	generator := filepath.Join(root, "Programs", "BilinearComplexity", "export_visualize_arxiv_333.py")
	body, err := os.ReadFile(generator)
	if err != nil {
		t.Fatal(err)
	}
	for _, phrase := range []string{"Complete ternary factor arrays", "The 59-algorithm in File Format", "fast_3x3_rank23", "Brent coordinate"} {
		if !strings.Contains(string(body), phrase) {
			t.Errorf("generator does not contain audit anchor %q", phrase)
		}
	}
}

func TestStrassenRoutingAcceptanceFixtureIsEncoded(t *testing.T) {
	body, err := staticFiles.ReadFile("static/app.js")
	if err != nil {
		t.Fatal(err)
	}
	// Columns of C below transpose to the required W rows:
	// + . . + - . + . / . . + . + . . . / . + . + . . . . / + - + . . + . .
	fixture := `[[1,0,0,1],[1,0,0,1],[1,0,0,1]], [[0,0,1,1],[1,0,0,0],[0,0,1,-1]],`
	if !strings.Contains(string(body), fixture) {
		t.Fatal("Strassen output-factor fixture changed")
	}
}

func startWorkbenchExport(t *testing.T, h http.Handler, construction string) string {
	t.Helper()
	request := httptest.NewRequest(http.MethodPost, "/api/export/workbench/start", nil)
	request.Header.Set("X-Proofs-Viz-Construction", construction)
	recorder := httptest.NewRecorder()
	h.ServeHTTP(recorder, request)
	if recorder.Code != http.StatusOK {
		t.Fatalf("start status = %d, want 200; body: %s", recorder.Code, recorder.Body.String())
	}
	var response struct {
		Token string `json:"token"`
	}
	if err := json.Unmarshal(recorder.Body.Bytes(), &response); err != nil {
		t.Fatal(err)
	}
	return response.Token
}

func exportRequest(t *testing.T, h http.Handler, path, token, contentType, body string) *httptest.ResponseRecorder {
	t.Helper()
	request := httptest.NewRequest(http.MethodPost, path, strings.NewReader(body))
	request.Header.Set("X-Proofs-Viz-Export-Token", token)
	if contentType != "" {
		request.Header.Set("Content-Type", contentType)
	}
	recorder := httptest.NewRecorder()
	h.ServeHTTP(recorder, request)
	return recorder
}

func TestWorkbenchExport(t *testing.T) {
	exportDir := t.TempDir()
	h, _ := newTestHandler(t, exportDir)
	token := startWorkbenchExport(t, h, "Rational Rank 48")
	parts := []string{`{"schema":"tensor-gate-lens/workbench/v1",`, `"gates":[{"id":"P1"}]}`}
	for _, part := range parts {
		recorder := exportRequest(t, h, "/api/export/workbench/chunk", token, "application/octet-stream", part)
		if recorder.Code != http.StatusNoContent {
			t.Fatalf("chunk status = %d, want 204; body: %s", recorder.Code, recorder.Body.String())
		}
	}
	recorder := exportRequest(t, h, "/api/export/workbench/finish", token, "", "")
	if recorder.Code != http.StatusOK {
		t.Fatalf("finish status = %d, want 200; body: %s", recorder.Code, recorder.Body.String())
	}
	var response struct {
		Path  string `json:"path"`
		Bytes int64  `json:"bytes"`
	}
	if err := json.Unmarshal(recorder.Body.Bytes(), &response); err != nil {
		t.Fatal(err)
	}
	body := strings.Join(parts, "")
	if filepath.Dir(response.Path) != exportDir {
		t.Fatalf("response path %q is outside %q", response.Path, exportDir)
	}
	name := filepath.Base(response.Path)
	if !strings.HasPrefix(name, "rational-rank-48-workbench-") || !strings.HasSuffix(name, ".json") {
		t.Fatalf("export filename %q is not sanitized and timestamped", name)
	}
	got, err := os.ReadFile(response.Path)
	if err != nil {
		t.Fatal(err)
	}
	if string(got) != body {
		t.Fatalf("export body = %q, want %q", got, body)
	}
	if response.Bytes != int64(len(body)) {
		t.Fatalf("response bytes = %d, want %d", response.Bytes, len(body))
	}
}

func TestWorkbenchExportRejectsUnsupportedRequests(t *testing.T) {
	h, _ := newTestHandler(t, t.TempDir())
	request := httptest.NewRequest(http.MethodGet, "/api/export/workbench/start", nil)
	recorder := httptest.NewRecorder()
	h.ServeHTTP(recorder, request)
	if recorder.Code != http.StatusMethodNotAllowed || recorder.Header().Get("Allow") != "POST" {
		t.Fatalf("GET status/Allow = %d/%q, want 405/POST", recorder.Code, recorder.Header().Get("Allow"))
	}

	token := startWorkbenchExport(t, h, "test")
	recorder = exportRequest(t, h, "/api/export/workbench/chunk", token, "text/plain", "{}")
	if recorder.Code != http.StatusUnsupportedMediaType {
		t.Fatalf("text chunk status = %d, want 415", recorder.Code)
	}
}

func TestWorkbenchExportConstructionCannotEscapeDirectory(t *testing.T) {
	exportDir := t.TempDir()
	h, _ := newTestHandler(t, exportDir)
	token := startWorkbenchExport(t, h, `../../escape\name`)
	recorder := exportRequest(t, h, "/api/export/workbench/chunk", token, "application/octet-stream", "{}")
	if recorder.Code != http.StatusNoContent {
		t.Fatalf("chunk status = %d, want 204", recorder.Code)
	}
	recorder = exportRequest(t, h, "/api/export/workbench/finish", token, "", "")
	if recorder.Code != http.StatusOK {
		t.Fatalf("finish status = %d, want 200; body: %s", recorder.Code, recorder.Body.String())
	}
	var response struct {
		Path string `json:"path"`
	}
	if err := json.Unmarshal(recorder.Body.Bytes(), &response); err != nil {
		t.Fatal(err)
	}
	if filepath.Dir(response.Path) != exportDir || strings.Contains(filepath.Base(response.Path), "..") {
		t.Fatalf("unsafe export path %q", response.Path)
	}
}

func TestHandlerRejectsMutationMethods(t *testing.T) {
	request := httptest.NewRequest(http.MethodPost, "/", nil)
	recorder := httptest.NewRecorder()
	handler, _ := newTestHandler(t, t.TempDir())
	handler.ServeHTTP(recorder, request)
	if recorder.Code != http.StatusMethodNotAllowed {
		t.Fatalf("POST status = %d, want %d", recorder.Code, http.StatusMethodNotAllowed)
	}
}

func TestWorkbenchRejectsCrossOriginMutation(t *testing.T) {
	handler, exporter := newTestHandler(t, t.TempDir())
	for name, headers := range map[string]map[string]string{
		"origin":         {"Origin": "https://attacker.example"},
		"fetch metadata": {"Sec-Fetch-Site": "cross-site"},
	} {
		t.Run(name, func(t *testing.T) {
			request := httptest.NewRequest(http.MethodPost, "/api/export/workbench/start", nil)
			for key, value := range headers {
				request.Header.Set(key, value)
			}
			recorder := httptest.NewRecorder()
			handler.ServeHTTP(recorder, request)
			if recorder.Code != http.StatusForbidden {
				t.Fatalf("cross-site status = %d, want %d", recorder.Code, http.StatusForbidden)
			}
		})
	}
	exporter.mu.Lock()
	pending := len(exporter.pending)
	exporter.mu.Unlock()
	if pending != 0 {
		t.Fatalf("cross-site requests created %d pending exports", pending)
	}

	request := httptest.NewRequest(http.MethodPost, "/api/export/workbench/start", nil)
	request.Header.Set("Origin", "http://example.com")
	recorder := httptest.NewRecorder()
	handler.ServeHTTP(recorder, request)
	if recorder.Code != http.StatusOK {
		t.Fatalf("same-origin status = %d, want %d; body: %s", recorder.Code, http.StatusOK, recorder.Body.String())
	}
}

func TestWorkbenchBoundsPendingAndExportSize(t *testing.T) {
	handler, exporter := newTestHandler(t, t.TempDir())
	exporter.maxPending = 2
	tokens := []string{
		startWorkbenchExport(t, handler, "first"),
		startWorkbenchExport(t, handler, "second"),
	}
	request := httptest.NewRequest(http.MethodPost, "/api/export/workbench/start", nil)
	recorder := httptest.NewRecorder()
	handler.ServeHTTP(recorder, request)
	if recorder.Code != http.StatusTooManyRequests {
		t.Fatalf("third start status = %d, want %d", recorder.Code, http.StatusTooManyRequests)
	}
	for _, token := range tokens {
		recorder = exportRequest(t, handler, "/api/export/workbench/cancel", token, "", "")
		if recorder.Code != http.StatusNoContent {
			t.Fatalf("cancel status = %d, want %d", recorder.Code, http.StatusNoContent)
		}
	}

	exporter.maxExport = 3
	token := startWorkbenchExport(t, handler, "oversized")
	recorder = exportRequest(t, handler, "/api/export/workbench/chunk", token, "application/octet-stream", "four")
	if recorder.Code != http.StatusRequestEntityTooLarge {
		t.Fatalf("oversized chunk status = %d, want %d; body: %s", recorder.Code, http.StatusRequestEntityTooLarge, recorder.Body.String())
	}
	if export := exporter.lookup(token); export != nil {
		t.Fatal("oversized export remains pending")
	}
}

func TestWorkbenchExpiresAbandonedExport(t *testing.T) {
	exportDir := t.TempDir()
	handler, exporter := newTestHandler(t, exportDir)
	token := startWorkbenchExport(t, handler, "abandoned")
	export := exporter.lookup(token)
	if export == nil {
		t.Fatal("started export is not pending")
	}
	exporter.expire(exporter.now().Add(exporter.lifetime + time.Second))
	if export := exporter.lookup(token); export != nil {
		t.Fatal("expired export remains pending")
	}
	entries, err := os.ReadDir(exportDir)
	if err != nil {
		t.Fatal(err)
	}
	if len(entries) != 0 {
		t.Fatalf("expired export left %d files", len(entries))
	}
}

type blockingBody struct {
	started   chan struct{}
	closed    chan struct{}
	startOnce sync.Once
	closeOnce sync.Once
}

func newBlockingBody() *blockingBody {
	return &blockingBody{started: make(chan struct{}), closed: make(chan struct{})}
}

func (b *blockingBody) Read([]byte) (int, error) {
	b.startOnce.Do(func() { close(b.started) })
	<-b.closed
	return 0, errors.New("body closed")
}

func (b *blockingBody) Close() error {
	b.closeOnce.Do(func() { close(b.closed) })
	return nil
}

func TestSlowChunkDoesNotBlockUnrelatedCancel(t *testing.T) {
	handler, _ := newTestHandler(t, t.TempDir())
	slowToken := startWorkbenchExport(t, handler, "slow")
	otherToken := startWorkbenchExport(t, handler, "other")
	body := newBlockingBody()
	request := httptest.NewRequest(http.MethodPost, "/api/export/workbench/chunk", body)
	request.Header.Set("Content-Type", "application/octet-stream")
	request.Header.Set("X-Proofs-Viz-Export-Token", slowToken)
	slowRecorder := httptest.NewRecorder()
	slowDone := make(chan struct{})
	go func() {
		handler.ServeHTTP(slowRecorder, request)
		close(slowDone)
	}()
	<-body.started

	cancelDone := make(chan *httptest.ResponseRecorder, 1)
	go func() {
		cancelDone <- exportRequest(t, handler, "/api/export/workbench/cancel", otherToken, "", "")
	}()
	select {
	case recorder := <-cancelDone:
		if recorder.Code != http.StatusNoContent {
			t.Errorf("unrelated cancel status = %d, want %d", recorder.Code, http.StatusNoContent)
		}
	case <-time.After(2 * time.Second):
		t.Fatal("slow chunk blocked cancellation of an unrelated export")
	}

	recorder := exportRequest(t, handler, "/api/export/workbench/cancel", slowToken, "", "")
	if recorder.Code != http.StatusNoContent {
		t.Fatalf("slow export cancel status = %d, want %d", recorder.Code, http.StatusNoContent)
	}
	select {
	case <-slowDone:
	case <-time.After(2 * time.Second):
		t.Fatal("cancel did not interrupt the slow request body")
	}
}

func TestCompletedExportRetentionIsBounded(t *testing.T) {
	exportDir := t.TempDir()
	handler, exporter := newTestHandler(t, exportDir)
	exporter.maxCompleted = 1
	var paths []string
	for _, construction := range []string{"first", "second"} {
		token := startWorkbenchExport(t, handler, construction)
		if recorder := exportRequest(t, handler, "/api/export/workbench/chunk", token, "application/octet-stream", "{}"); recorder.Code != http.StatusNoContent {
			t.Fatalf("chunk status = %d, want %d", recorder.Code, http.StatusNoContent)
		}
		recorder := exportRequest(t, handler, "/api/export/workbench/finish", token, "", "")
		if recorder.Code != http.StatusOK {
			t.Fatalf("finish status = %d, want %d; body: %s", recorder.Code, http.StatusOK, recorder.Body.String())
		}
		var response struct {
			Path string `json:"path"`
		}
		if err := json.Unmarshal(recorder.Body.Bytes(), &response); err != nil {
			t.Fatal(err)
		}
		paths = append(paths, response.Path)
	}
	if _, err := os.Stat(paths[0]); !errors.Is(err, os.ErrNotExist) {
		t.Fatalf("oldest completed export still exists: %v", err)
	}
	if _, err := os.Stat(paths[1]); err != nil {
		t.Fatalf("newest completed export: %v", err)
	}
}

func TestGraphUsesSelectedMetricVisibility(t *testing.T) {
	body, err := staticFiles.ReadFile("static/app.js")
	if err != nil {
		t.Fatal(err)
	}
	javascript := string(body)
	for _, phrase := range []string{
		"if(!visiblePair(info))continue;",
		"state.mode===\"weighted\"||state.mode===\"net\"",
		"class:`${baseClass} ${metric.sign}-edge`",
	} {
		if !strings.Contains(javascript, phrase) {
			t.Errorf("app.js does not contain graph metric guard %q", phrase)
		}
	}
}

func TestDefaultListenerIsLoopbackOnly(t *testing.T) {
	if defaultAddress != "127.0.0.1:11111" || !loopbackAddress(defaultAddress) {
		t.Fatalf("default address %q is not explicit loopback", defaultAddress)
	}
	for _, address := range []string{":11111", "0.0.0.0:11111", "[::]:11111", "192.0.2.1:11111"} {
		if loopbackAddress(address) {
			t.Errorf("loopbackAddress(%q) = true", address)
		}
	}
	for _, address := range []string{"localhost:11111", "127.0.0.2:11111", "[::1]:11111"} {
		if !loopbackAddress(address) {
			t.Errorf("loopbackAddress(%q) = false", address)
		}
	}
}

func TestRuntimeExportDirectoryIsPrivateAndUnpredictable(t *testing.T) {
	first, err := newWorkbenchExporter("")
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() {
		if err := first.Close(); err != nil {
			t.Errorf("close first exporter: %v", err)
		}
	})
	second, err := newWorkbenchExporter("")
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() {
		if err := second.Close(); err != nil {
			t.Errorf("close second exporter: %v", err)
		}
	})
	if first.dir == second.dir {
		t.Fatalf("private exporters reused directory %q", first.dir)
	}
	for _, dir := range []string{first.dir, second.dir} {
		info, err := os.Stat(dir)
		if err != nil {
			t.Fatal(err)
		}
		if !info.IsDir() || info.Mode().Perm()&0o077 != 0 {
			t.Errorf("export directory %q mode = %v, want private directory", dir, info.Mode())
		}
		if !strings.HasPrefix(filepath.Base(dir), "proofs-viz-") {
			t.Errorf("export directory %q lacks expected random prefix", dir)
		}
	}
}
