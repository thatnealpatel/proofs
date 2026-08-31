// Command lemmasweep runs the Lemma
// M / Lemma D kill-test sweep over
// precomputed group data, verifying the
// Pf3 abelian-factor conjecture rho_0(A
// x G) = rho_0(G) for all finite abelian
// A.
//
// A SINGLE VIOLATION kills the
// conjecture: the engine surfaces it
// immediately with a loud banner, flushes
// the violation record, and exits
// nonzero.
//
// Input: JSON files under --data-dir
// produced by forge/export_tpp.sage (with
// abelianization extension). The target
// list is SmallGroup IDs read from a
// population JSONL or enumerated from the
// data dir.
//
// Output: JSONL records to --output
// with per-group results, schema
// backward-compatible with the Sage
// prototype's output.
//
// Modes:
//
//	--toy          all nonabelian groups order <= 16 (seconds)
//	--dry-run      population breakdown + projected runtime
//	(default)      full sweep over all available exported groups
//
// Mathematical reference: Pf3
// (.tasks/f5exp/docs/Pf3-abelian-factor.md)
package main

import (
	"bufio"
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"os"
	"path/filepath"
	"runtime"
	"sort"
	"strings"
	"sync"
	"time"

	"patel.codes/proofs/cmd/sieve/internal/tpp"
)

func main() {
	var (
		toyMode  = flag.Bool("toy", false, "toy mode: nonabelian groups order <= 16")
		dataDir  = flag.String("data-dir", "", "path to exported JSON data")
		output   = flag.String("output", "", "output JSONL path")
		lemmaD   = flag.Bool("lemma-d", false, "also run Lemma D probe")
		dryRun   = flag.Bool("dry-run", false, "print population stats and exit")
		targetID = flag.String("target-id", "", "run only this SmallGroup ID (e.g. 6_1)")
		limit    = flag.Int("limit", 0, "stop after N groups (0 = no limit)")
		workers  = flag.Int("workers", 0, "parallel workers (0 = NumCPU)")
		budget   = flag.Duration("budget", 10*time.Minute, "per-group time budget")
		popFile  = flag.String("population", "", "population JSONL listing target IDs")
	)
	flag.Parse()

	repoRoot := findRepoRoot()

	if *dataDir == "" {
		*dataDir = filepath.Join(repoRoot, "Scratch", "GroupSieve", "forge", "out", "tpp-data")
	}
	if *output == "" {
		*output = filepath.Join(repoRoot, "Scratch", "GroupSieve", "forge", "out", "lemmasweep", "lemmasweep-results.jsonl")
	}
	if *workers == 0 {
		*workers = runtime.NumCPU()
	}

	// Build target list.
	targets, err := buildTargets(*toyMode, *dataDir, *popFile, *targetID)
	if err != nil {
		fmt.Fprintf(os.Stderr, "error building targets: %v\n", err)
		os.Exit(1)
	}

	if *dryRun {
		printDryRun(targets)
		return
	}

	if *limit > 0 && len(targets) > *limit {
		targets = targets[:*limit]
	}

	// Load done IDs for resume.
	doneIDs := loadDoneIDs(*output)

	remaining := make([]target, 0, len(targets))
	for _, t := range targets {
		if _, ok := doneIDs[t.id]; !ok {
			remaining = append(remaining, t)
		}
	}

	fmt.Println(strings.Repeat("=", 70))
	fmt.Println("lemmasweep -- Lemma M/D kill-test engine (Go)")
	fmt.Printf("Targets: %d total, %d done, %d remaining\n",
		len(targets), len(doneIDs), len(remaining))
	fmt.Printf("Mode: Lemma M%s\n", map[bool]string{true: " + Lemma D", false: " only"}[*lemmaD])
	fmt.Printf("Workers: %d, Per-group budget: %v\n", *workers, *budget)
	fmt.Printf("Output: %s\n", *output)
	fmt.Println(strings.Repeat("=", 70))
	fmt.Println()

	if len(remaining) == 0 {
		fmt.Println("Nothing to do -- all targets complete.")
		return
	}

	// Open output file.
	if err := os.MkdirAll(filepath.Dir(*output), 0o755); err != nil {
		fmt.Fprintf(os.Stderr, "error creating output dir: %v\n", err)
		os.Exit(1)
	}
	outFile, err := os.OpenFile(*output, os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0o644)
	if err != nil {
		fmt.Fprintf(os.Stderr, "error opening output: %v\n", err)
		os.Exit(1)
	}
	defer outFile.Close()

	tStart := time.Now()
	nViolations := 0
	nDFailures := 0
	nProcessed := 0
	nErrors := 0

	for i, tgt := range remaining {
		t0 := time.Now()

		fmt.Printf("[%d/%d] SmallGroup(%s) order %d\n",
			i+1, len(remaining), tgt.id, tgt.order)

		rec := processGroup(tgt, *dataDir, *lemmaD, *budget, *workers)

		// Check violations.
		if rec.LemmaM != nil && rec.LemmaM.NViolations > 0 {
			nViolations += rec.LemmaM.NViolations
			fmt.Printf("\n!!! VIOLATION at %s !!!\n", tgt.id)
			for _, v := range rec.LemmaM.Violations {
				vj, _ := json.Marshal(v)
				fmt.Printf("  %s\n", vj)
			}
			fmt.Println()
		}
		if rec.LemmaD != nil && rec.LemmaD.NDFailures > 0 {
			nDFailures += rec.LemmaD.NDFailures
			fmt.Printf("\n!!! Lemma D failure at %s !!!\n", tgt.id)
			for _, f := range rec.LemmaD.DFailures {
				fj, _ := json.Marshal(f)
				fmt.Printf("  %s\n", fj)
			}
			fmt.Println()
		}
		if rec.Error != "" {
			nErrors++
			fmt.Printf("  ERROR: %s\n", rec.Error)
		}

		rec.ElapsedS = time.Since(t0).Seconds()

		// Write record.
		recBytes, err := json.Marshal(rec)
		if err != nil {
			fmt.Fprintf(os.Stderr, "  ERROR marshaling: %v\n", err)
			nErrors++
			continue
		}
		fmt.Fprintf(outFile, "%s\n", recBytes)
		outFile.Sync()
		nProcessed++

		// Progress report.
		if rec.LemmaM != nil {
			fmt.Printf("  beta0=%d checked=%d dead=%d violations=%d (%.1fs)\n",
				rec.LemmaM.Beta0, rec.LemmaM.Checked, rec.LemmaM.Dead,
				rec.LemmaM.NViolations, rec.ElapsedS)
		}

		// Projection after first 20 groups.
		if (i+1) == 20 && len(remaining) > 20 {
			elapsed := time.Since(tStart)
			rate := float64(i+1) / elapsed.Seconds()
			eta := float64(len(remaining)-i-1) / rate
			fmt.Printf("\n  Rate: %.2f groups/s, ETA: %.0f min\n\n", rate, eta/60)
		}
	}

	fmt.Println()
	fmt.Println(strings.Repeat("=", 70))
	fmt.Printf("Done: %d processed, %d errors, %.1f min elapsed.\n",
		nProcessed, nErrors, time.Since(tStart).Minutes())
	fmt.Printf("Lemma M violations: %d\n", nViolations)
	if *lemmaD {
		fmt.Printf("Lemma D failures: %d\n", nDFailures)
	}
	fmt.Println(strings.Repeat("=", 70))

	if nViolations > 0 {
		fmt.Println("\n*** CONJECTURE KILLED -- violations found. See output. ***")
		os.Exit(2)
	}
	if nErrors > 0 {
		os.Exit(1)
	}
}

// ---------------------------------------------------------------------------
// Target management
// ---------------------------------------------------------------------------

type target struct {
	id    string // "order_idx" e.g. "6_1"
	order int
	idx   int
}

func buildTargets(toyMode bool, dataDir, popFile, targetID string) ([]target, error) {
	if targetID != "" {
		order, idx, err := parseID(targetID)
		if err != nil {
			return nil, err
		}
		return []target{{id: targetID, order: order, idx: idx}}, nil
	}

	if popFile != "" {
		return loadPopulation(popFile)
	}

	// Scan data dir for available exported
	// files matching SmallGroup pattern.
	entries, err := os.ReadDir(dataDir)
	if err != nil {
		return nil, fmt.Errorf("read data dir %s: %w", dataDir, err)
	}

	var targets []target
	for _, e := range entries {
		name := e.Name()
		if !strings.HasSuffix(name, ".json") || name == "manifest.json" {
			continue
		}
		id := strings.TrimSuffix(name, ".json")
		order, idx, err := parseID(id)
		if err != nil {
			continue // skip non-SmallGroup files
		}
		if toyMode && order > 16 {
			continue
		}
		targets = append(targets, target{id: id, order: order, idx: idx})
	}

	sort.Slice(targets, func(i, j int) bool {
		if targets[i].order != targets[j].order {
			return targets[i].order < targets[j].order
		}
		return targets[i].idx < targets[j].idx
	})

	return targets, nil
}

func parseID(id string) (order, idx int, err error) {
	// Handle formats: "6_1", "ctrl_6_1",
	// etc. For lemma sweep we only care
	// about plain "order_idx" format.
	parts := strings.Split(id, "_")
	if len(parts) == 2 {
		order = parseInt(parts[0])
		idx = parseInt(parts[1])
		if order > 0 && idx > 0 {
			return order, idx, nil
		}
	}
	return 0, 0, fmt.Errorf("cannot parse SmallGroup ID %q", id)
}

func parseInt(s string) int {
	n := 0
	for _, c := range s {
		if c < '0' || c > '9' {
			return 0
		}
		n = n*10 + int(c-'0')
	}
	if len(s) == 0 {
		return 0
	}
	return n
}

func loadPopulation(path string) ([]target, error) {
	f, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	defer f.Close()

	var targets []target
	scanner := bufio.NewScanner(f)
	for scanner.Scan() {
		line := strings.TrimSpace(scanner.Text())
		if line == "" {
			continue
		}
		var rec struct {
			GroupID [2]int `json:"group_id"`
		}
		if err := json.Unmarshal([]byte(line), &rec); err != nil {
			continue
		}
		if rec.GroupID[0] > 0 {
			id := fmt.Sprintf("%d_%d", rec.GroupID[0], rec.GroupID[1])
			targets = append(targets, target{id: id, order: rec.GroupID[0], idx: rec.GroupID[1]})
		}
	}
	return targets, scanner.Err()
}

func loadDoneIDs(path string) map[string]struct{} {
	m := map[string]struct{}{}
	// Also scan sibling files for sharded resume.
	dir := filepath.Dir(path)
	entries, err := os.ReadDir(dir)
	if err != nil {
		return m
	}
	for _, e := range entries {
		if !strings.HasPrefix(e.Name(), "lemmasweep-results") {
			continue
		}
		if !strings.HasSuffix(e.Name(), ".jsonl") {
			continue
		}
		p := filepath.Join(dir, e.Name())
		f, err := os.Open(p)
		if err != nil {
			continue
		}
		scanner := bufio.NewScanner(f)
		for scanner.Scan() {
			line := strings.TrimSpace(scanner.Text())
			if line == "" {
				continue
			}
			var rec struct {
				GroupID [2]int `json:"group_id"`
			}
			if err := json.Unmarshal([]byte(line), &rec); err != nil {
				continue
			}
			if rec.GroupID[0] > 0 {
				id := fmt.Sprintf("%d_%d", rec.GroupID[0], rec.GroupID[1])
				m[id] = struct{}{}
			}
		}
		f.Close()
	}
	return m
}

func printDryRun(targets []target) {
	fmt.Println("=== lemmasweep dry-run ===")
	fmt.Printf("Total targets: %d\n", len(targets))

	byOrder := map[int]int{}
	for _, t := range targets {
		byOrder[t.order]++
	}
	orders := make([]int, 0, len(byOrder))
	for o := range byOrder {
		orders = append(orders, o)
	}
	sort.Ints(orders)

	fmt.Println("\nPopulation by order:")
	for _, o := range orders {
		fmt.Printf("  order %3d: %d groups\n", o, byOrder[o])
	}
}

// ---------------------------------------------------------------------------
// Per-group processing
// ---------------------------------------------------------------------------

// SweepRecord is one output JSONL record,
// schema-compatible with the Sage
// prototype's output.
type SweepRecord struct {
	GroupID   [2]int        `json:"group_id"`
	Order     int           `json:"order"`
	LemmaM    *LemmaMResult `json:"lemma_m,omitempty"`
	LemmaD    *LemmaDResult `json:"lemma_d,omitempty"`
	Violation bool          `json:"VIOLATION,omitempty"`
	DFailure  bool          `json:"D_FAILURE,omitempty"`
	ElapsedS  float64       `json:"elapsed_s"`
	Error     string        `json:"error,omitempty"`
}

// LemmaMResult holds Lemma M probe output.
type LemmaMResult struct {
	Beta0       int              `json:"beta0"`
	NSubgroups  int              `json:"n_subgroups"`
	Checked     int              `json:"checked"`
	Dead        int              `json:"dead"`
	NViolations int              `json:"n_violations"`
	Violations  []map[string]any `json:"violations"`
}

// LemmaDResult holds Lemma D probe output.
type LemmaDResult struct {
	Beta0      int              `json:"beta0"`
	NChecked   int              `json:"n_checked"`
	NDFailures int              `json:"n_D_failures"`
	DFailures  []map[string]any `json:"D_failures"`
}

func processGroup(tgt target, dataDir string, runD bool, budget time.Duration, workers int) SweepRecord {
	rec := SweepRecord{
		GroupID: [2]int{tgt.order, tgt.idx},
		Order:   tgt.order,
	}

	defer func() {
		if r := recover(); r != nil {
			rec.Error = fmt.Sprintf("panic: %v", r)
			fmt.Fprintf(os.Stderr, "PANIC processing %s: %v\n", tgt.id, r)
		}
	}()

	// Load group data.
	path := filepath.Join(dataDir, tgt.id+".json")
	g, err := tpp.LoadGroup(path)
	if err != nil {
		rec.Error = err.Error()
		return rec
	}

	ctx, cancel := context.WithTimeout(context.Background(), budget)
	defer cancel()

	// Run Lemma M.
	mResult := probeLemmaM(ctx, g, workers)
	rec.LemmaM = mResult
	if mResult.NViolations > 0 {
		rec.Violation = true
	}

	// Optionally run Lemma D.
	if runD {
		select {
		case <-ctx.Done():
			rec.Error = "budget exhausted before Lemma D"
			return rec
		default:
		}
		dResult := probeLemmaD(ctx, g, workers)
		rec.LemmaD = dResult
		if dResult.NDFailures > 0 {
			rec.DFailure = true
		}
	}

	return rec
}

// ---------------------------------------------------------------------------
// Lemma M probe
// ---------------------------------------------------------------------------

func probeLemmaM(ctx context.Context, g *tpp.Group, workers int) *LemmaMResult {
	n := len(g.Subgroups)
	nG := g.N

	// Compute beta0 using full TPP search.
	beta0 := computeBeta0(g)

	// Precompute abelianization data: for
	// each subgroup, its derived order,
	// invariants, and per-element exponent
	// vectors are already loaded in
	// g.Subgroups[i].

	// Lattice cache.
	var latMu sync.Mutex
	latCache := map[string][]tpp.AbelianSubgroup{}

	getLattice := func(invs []int) []tpp.AbelianSubgroup {
		key := invsKey(invs)
		latMu.Lock()
		if lat, ok := latCache[key]; ok {
			latMu.Unlock()
			return lat
		}
		latMu.Unlock()

		lat := tpp.AbelianLattice(invs)

		latMu.Lock()
		latCache[key] = lat
		latMu.Unlock()
		return lat
	}

	// Sweep all triples (iS, iT, iU).
	type tripleWork struct {
		iS, iT int
	}

	// Build work items: one per (iS, iT) pair.
	var workItems []tripleWork
	for iS := 0; iS < n; iS++ {
		for iT := 0; iT < n; iT++ {
			workItems = append(workItems, tripleWork{iS, iT})
		}
	}

	var (
		mu         sync.Mutex
		checked    int
		dead       int
		violations []map[string]any
	)

	// Fan out work across goroutines.
	if workers <= 0 {
		workers = 1
	}
	ch := make(chan tripleWork, len(workItems))
	for _, w := range workItems {
		ch <- w
	}
	close(ch)

	var wg sync.WaitGroup
	for w := 0; w < workers; w++ {
		wg.Add(1)
		go func() {
			defer wg.Done()

			localChecked := 0
			localDead := 0
			var localViol []map[string]any

			for wi := range ch {
				select {
				case <-ctx.Done():
					return
				default:
				}

				iS := wi.iS
				iT := wi.iT
				sS := &g.Subgroups[iS]
				sT := &g.Subgroups[iT]

				for iU := 0; iU < n; iU++ {
					sU := &g.Subgroups[iU]
					prod := sS.Order * sT.Order * sU.Order
					if prod <= beta0 {
						continue
					}

					dS := sS.DerivedOrder
					dT := sT.DerivedOrder
					dU := sU.DerivedOrder
					dprod := dS * dT * dU

					// Concatenated invariants.
					invs := concatInvs(sS.AbelianInvariants, sT.AbelianInvariants, sU.AbelianInvariants)

					lat := getLattice(invs)

					// Build nbar: the set of obstruction exponent vectors.
					nbar := map[uint64]struct{}{}
					isDead := false

					lenSInvs := len(sS.AbelianInvariants)
					lenTInvs := len(sT.AbelianInvariants)

					for _, si := range sS.EltList {
						svec := sS.ExponentVectors[si]
						for _, ti := range sT.EltList {
							// z = (s * t)^{-1}
							st := g.Table[int(si)*nG+int(ti)]
							zi := g.Inv[st]

							if !sU.Elts.Has(int(zi)) {
								continue
							}
							// Skip identity triple.
							if si == 0 && ti == 0 {
								continue
							}

							tvec := sT.ExponentVectors[ti]
							uvec := sU.ExponentVectors[zi]

							// Concatenate exponent vectors.
							v := concatVecs(svec, tvec, uvec, lenSInvs, lenTInvs, invs)

							// Check if v is zero (all
							// components zero mod invariants).
							allZero := true
							for ci, c := range v {
								r := c % invs[ci]
								if r < 0 {
									r += invs[ci]
								}
								if r != 0 {
									allZero = false
									break
								}
							}
							if allZero {
								isDead = true
								break
							}

							pk := tpp.PackExponentVec(v, invs)
							nbar[pk] = struct{}{}
						}
						if isDead {
							break
						}
					}

					if isDead {
						localDead++
						continue
					}

					localChecked++

					// Check each lattice subgroup.
					for _, sub := range lat {
						tot := sub.Order * dprod
						if tot <= beta0 {
							continue
						}
						// Check if nbar intersects sub.Elements.
						intersects := false
						for pk := range nbar {
							if _, ok := sub.Elements[pk]; ok {
								intersects = true
								break
							}
						}
						if !intersects {
							localViol = append(localViol, map[string]any{
								"S":          iS,
								"T":          iT,
								"U":          iU,
								"sizes":      [3]int{sS.Order, sT.Order, sU.Order},
								"sigma_size": tot,
							})
						}
					}
				}
			}

			mu.Lock()
			checked += localChecked
			dead += localDead
			violations = append(violations, localViol...)
			mu.Unlock()
		}()
	}

	wg.Wait()

	// Truncate violation list.
	truncViol := violations
	if len(truncViol) > 5 {
		truncViol = truncViol[:5]
	}

	return &LemmaMResult{
		Beta0:       beta0,
		NSubgroups:  n,
		Checked:     checked,
		Dead:        dead,
		NViolations: len(violations),
		Violations:  truncViol,
	}
}

// ---------------------------------------------------------------------------
// Lemma D probe
// ---------------------------------------------------------------------------

func probeLemmaD(ctx context.Context, g *tpp.Group, workers int) *LemmaDResult {
	n := len(g.Subgroups)
	nG := g.N

	beta0 := computeBeta0(g)

	// Build subgroup containment: for each
	// subgroup i, which other subgroups are
	// sub-subgroups of i? A subgroup j is
	// a subsubgroup of i iff j.Elts is a
	// subset of i.Elts.
	subsubs := make([][]int, n)
	for i := 0; i < n; i++ {
		var contained []int
		for j := 0; j < n; j++ {
			if isSubset(&g.Subgroups[j].Elts, &g.Subgroups[i].Elts) {
				contained = append(contained, j)
			}
		}
		// Sort by descending order for early exit in max_inside.
		sort.Slice(contained, func(a, b int) bool {
			return g.Subgroups[contained[a]].Order > g.Subgroups[contained[b]].Order
		})
		subsubs[i] = contained
	}

	// TPP cache.
	var tppMu sync.Mutex
	tppCache := map[[3]int]bool{}

	isTPPCached := func(iS, iT, iU int) bool {
		key := [3]int{iS, iT, iU}
		tppMu.Lock()
		val, ok := tppCache[key]
		tppMu.Unlock()
		if ok {
			return val
		}
		result := g.TPPSetCheck(&g.Subgroups[iS], &g.Subgroups[iT], &g.Subgroups[iU])
		tppMu.Lock()
		tppCache[key] = result
		tppMu.Unlock()
		return result
	}

	// max_inside: find the best TPP product among subtriples.
	maxInside := func(iS, iT, iU, need int) int {
		best := 0
		for _, jS := range subsubs[iS] {
			if g.Subgroups[jS].Order*g.Subgroups[iT].Order*g.Subgroups[iU].Order <= best {
				break
			}
			for _, jT := range subsubs[iT] {
				if g.Subgroups[jS].Order*g.Subgroups[jT].Order*g.Subgroups[iU].Order <= best {
					break
				}
				for _, jU := range subsubs[iU] {
					p := g.Subgroups[jS].Order * g.Subgroups[jT].Order * g.Subgroups[jU].Order
					if p <= best {
						break
					}
					if isTPPCached(jS, jT, jU) {
						best = p
						if best >= need {
							return best
						}
					}
				}
			}
		}
		return best
	}

	// Lattice cache.
	var latMu sync.Mutex
	latCache := map[string][]tpp.AbelianSubgroup{}

	getLattice := func(invs []int) []tpp.AbelianSubgroup {
		key := invsKey(invs)
		latMu.Lock()
		if lat, ok := latCache[key]; ok {
			latMu.Unlock()
			return lat
		}
		latMu.Unlock()
		lat := tpp.AbelianLattice(invs)
		latMu.Lock()
		latCache[key] = lat
		latMu.Unlock()
		return lat
	}

	var (
		mu       sync.Mutex
		nChecked int
		fails    []map[string]any
	)

	// Process triples sequentially (Lemma
	// D has heavier per-triple work due to
	// max_inside, and the tpp cache benefits
	// from sequential access).
	for iS := 0; iS < n; iS++ {
		select {
		case <-ctx.Done():
			break
		default:
		}
		sS := &g.Subgroups[iS]
		for iT := 0; iT < n; iT++ {
			sT := &g.Subgroups[iT]
			for iU := 0; iU < n; iU++ {
				sU := &g.Subgroups[iU]

				dS := sS.DerivedOrder
				dT := sT.DerivedOrder
				dU := sU.DerivedOrder
				dprod := dS * dT * dU

				invs := concatInvs(sS.AbelianInvariants, sT.AbelianInvariants, sU.AbelianInvariants)
				lat := getLattice(invs)

				lenSInvs := len(sS.AbelianInvariants)
				lenTInvs := len(sT.AbelianInvariants)

				// Build nbar.
				nbar := map[uint64]struct{}{}
				isDead := false

				for _, si := range sS.EltList {
					svec := sS.ExponentVectors[si]
					for _, ti := range sT.EltList {
						st := g.Table[int(si)*nG+int(ti)]
						zi := g.Inv[st]
						if !sU.Elts.Has(int(zi)) {
							continue
						}
						if si == 0 && ti == 0 {
							continue
						}
						tvec := sT.ExponentVectors[ti]
						uvec := sU.ExponentVectors[zi]
						v := concatVecs(svec, tvec, uvec, lenSInvs, lenTInvs, invs)

						allZero := true
						for ci, c := range v {
							r := c % invs[ci]
							if r < 0 {
								r += invs[ci]
							}
							if r != 0 {
								allZero = false
								break
							}
						}
						if allZero {
							isDead = true
							break
						}
						pk := tpp.PackExponentVec(v, invs)
						nbar[pk] = struct{}{}
					}
					if isDead {
						break
					}
				}
				if isDead {
					continue
				}

				// Find max eligible sigma size.
				maxSig := 0
				for _, sub := range lat {
					tot := sub.Order * dprod
					if tot <= maxSig {
						continue
					}
					intersects := false
					for pk := range nbar {
						if _, ok := sub.Elements[pk]; ok {
							intersects = true
							break
						}
					}
					if !intersects {
						maxSig = tot
					}
				}
				if maxSig <= 1 {
					continue
				}

				nChecked++
				wit := maxInside(iS, iT, iU, maxSig)
				if wit < maxSig {
					mu.Lock()
					fails = append(fails, map[string]any{
						"members":             [3]int{sS.Order, sT.Order, sU.Order},
						"max_eligible_sigma":  maxSig,
						"best_inside_witness": wit,
					})
					mu.Unlock()
				}
			}
		}
	}

	_ = workers // Lemma D runs sequentially for cache coherence.

	truncFails := fails
	if len(truncFails) > 5 {
		truncFails = truncFails[:5]
	}

	return &LemmaDResult{
		Beta0:      beta0,
		NChecked:   nChecked,
		NDFailures: len(fails),
		DFailures:  truncFails,
	}
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

// computeBeta0 computes beta_0(G) by
// exhaustive TPP search over all subgroup
// triples, matching the prototype
// semantics exactly.
func computeBeta0(g *tpp.Group) int {
	n := len(g.Subgroups)
	nG := g.N
	beta0 := 0

	for iS := 0; iS < n; iS++ {
		sS := &g.Subgroups[iS]
		for iT := 0; iT < n; iT++ {
			sT := &g.Subgroups[iT]
			if sS.Order*sT.Order > nG {
				continue
			}
			for iU := 0; iU < n; iU++ {
				sU := &g.Subgroups[iU]
				p := sS.Order * sT.Order * sU.Order
				if p <= beta0 {
					continue
				}
				if g.TPPSetCheck(sS, sT, sU) {
					beta0 = p
				}
			}
		}
	}
	return beta0
}

func isSubset(a, b *tpp.Bitset) bool {
	for i, w := range a.Words {
		if w & ^b.Words[i] != 0 {
			return false
		}
	}
	return true
}

func concatInvs(a, b, c []int) []int {
	r := make([]int, 0, len(a)+len(b)+len(c))
	r = append(r, a...)
	r = append(r, b...)
	r = append(r, c...)
	return r
}

func concatVecs(svec, tvec, uvec []int, lenS, lenT int, invs []int) []int {
	total := len(invs)
	v := make([]int, total)
	copy(v, svec)
	copy(v[lenS:], tvec)
	copy(v[lenS+lenT:], uvec)
	return v
}

func invsKey(invs []int) string {
	if len(invs) == 0 {
		return ""
	}
	buf := make([]byte, 0, len(invs)*4)
	for i, d := range invs {
		if i > 0 {
			buf = append(buf, ',')
		}
		buf = appendInt(buf, d)
	}
	return string(buf)
}

func appendInt(buf []byte, n int) []byte {
	if n == 0 {
		return append(buf, '0')
	}
	var tmp [20]byte
	i := len(tmp)
	for n > 0 {
		i--
		tmp[i] = byte('0' + n%10)
		n /= 10
	}
	return append(buf, tmp[i:]...)
}

func findRepoRoot() string {
	dir, err := os.Getwd()
	if err != nil {
		return "."
	}
	for {
		if _, err := os.Stat(filepath.Join(dir, "go.mod")); err == nil {
			return dir
		}
		parent := filepath.Dir(dir)
		if parent == dir {
			return "."
		}
		dir = parent
	}
}
