// Command beta0probe computes exact beta_0(G) for finite groups using the
// bitset TPP engine in internal/tpp, or hunts for threshold-exceeding triples.
//
// Two modes:
//
//   - exact (default): exhaustive search over all subgroup triples to find
//     beta_0(G) = max |S||T||U| over TPP triples (S,T,U). Emits semantics
//     "exact" ONLY when the search completed without timeout or budget cutoff.
//
//   - hunt -threshold N: emit the first TPP triple with |S||T||U| > N and
//     stop. Semantics is "lower_bound". Any hit is a potential conjecture
//     kill: the triple is brute-force re-checked and flagged KILL.
//
// Exhaustiveness argument for exact mode:
//
// The search visits every (classS, classT, classU) triple. For each, S is
// fixed to the class representative (TPP is conjugation-invariant), and T, U
// range over ALL subgroups in their classes. Order triples whose product <=
// current best are skipped (monotone pruning: they provably cannot be the
// maximum). Neumann Obs 3.1 pruning is a NECESSARY condition for TPP — no
// valid triple is excluded. The Murthy non-normality pruning excludes normal
// subgroups, which is correct (Murthy26 Prop 2.19(2): all three members of a
// nontrivial TPP triple are non-normal). No early size cutoff is applied
// beyond these provably sound filters. In contrast, the Sage prototype's
// flawed s_max^3 > |G| cutoff missed the 972 achiever on A_6 and returned 900
// (Pf3 section 5): this Go engine has no such cutoff.
//
// Usage:
//
//	beta0probe exact --data path/to/group.json [--output results.jsonl] [--target-budget 2h] [--workers N]
//	beta0probe hunt  --data path/to/group.json --threshold 120 [--output results.jsonl] [--target-budget 2h]
//
// Input: single group JSON file produced by export_tpp.sage.
// Output: JSONL records (one per run) to --output. Checkpoint/resume skips
// IDs already present. Progress prints at least every 30s.
package main

import (
	"bufio"
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"os"
	"runtime"
	"sort"
	"strings"
	"sync"
	"sync/atomic"
	"time"

	"patel.codes/proofs/cmd/sieve/internal/tpp"
)

// beta0Result holds the detailed result for a single target.
type beta0Result struct {
	ID          string  `json:"id"`
	Description string  `json:"description"`
	Order       int     `json:"order"`
	Mode        string  `json:"mode"` // "exact" or "hunt"
	Beta0       int64   `json:"beta0"`
	Rho0Exact   string  `json:"rho0_exact"`
	Rho0Float   float64 `json:"rho0_float"`

	// Witness triple details.
	WitnessOrders  [3]int   `json:"witness_orders"`             // (|S|, |T|, |U|)
	WitnessClasses [3]int   `json:"witness_classes"`            // (classS, classT, classU)
	WitnessCopies  [3]int   `json:"witness_copies,omitempty"`   // (copy index within class for S, T, U)
	WitnessElts    [3][]int `json:"witness_elements,omitempty"` // element index lists

	Semantics    string `json:"semantics"` // "exact", "lower_bound", "error"
	Threshold    int64  `json:"threshold,omitempty"`
	HuntKill     bool   `json:"hunt_kill,omitempty"`
	BruteRecheck bool   `json:"brute_recheck,omitempty"`

	NCandidates    int64   `json:"n_candidates"`
	NTPPChecks     int64   `json:"n_tpp_checks"`
	NTriplesTested int64   `json:"n_triples_tested"`
	NPrunedNormal  int64   `json:"n_pruned_normal"`
	NClasses       int     `json:"n_classes"`
	NSubgroups     int     `json:"n_subgroups"`
	RuntimeSeconds float64 `json:"runtime_seconds"`
	TimedOut       bool    `json:"timed_out"`
	Error          string  `json:"error,omitempty"`
}

func main() {
	// Parse subcommand.
	if len(os.Args) < 2 {
		usage()
		os.Exit(1)
	}
	mode := os.Args[1]
	if mode != "exact" && mode != "hunt" {
		fmt.Fprintf(os.Stderr, "error: unknown mode %q (want exact or hunt)\n", mode)
		usage()
		os.Exit(1)
	}

	fs := flag.NewFlagSet(mode, flag.ExitOnError)
	var (
		dataPath     = fs.String("data", "", "path to group JSON file (required)")
		output       = fs.String("output", "", "output JSONL path (default: stdout)")
		targetBudget = fs.Duration("target-budget", 2*time.Hour, "per-target time budget")
		globalBudget = fs.Duration("global-budget", 0, "global time budget (0 = unlimited)")
		workers      = fs.Int("workers", 0, "parallel workers (0 = NumCPU)")
		threshold    = fs.Int64("threshold", 0, "hunt threshold: stop at first triple with product > N")
		crossCheck   = fs.Bool("cross-check", false, "brute-force cross-validate every TPP check")
	)
	if err := fs.Parse(os.Args[2:]); err != nil {
		os.Exit(1)
	}

	if *dataPath == "" {
		fmt.Fprintf(os.Stderr, "error: --data is required\n")
		fs.Usage()
		os.Exit(1)
	}
	if mode == "hunt" && *threshold <= 0 {
		fmt.Fprintf(os.Stderr, "error: --threshold is required for hunt mode\n")
		os.Exit(1)
	}
	if *workers <= 0 {
		*workers = runtime.NumCPU()
	}

	// Load group.
	g, err := tpp.LoadGroup(*dataPath)
	if err != nil {
		fmt.Fprintf(os.Stderr, "error: %v\n", err)
		os.Exit(1)
	}

	fmt.Fprintf(os.Stderr, "beta0probe %s: %s (order %d, %d classes, %d subgroups)\n",
		mode, g.Description, g.N, len(g.Classes), len(g.Subgroups))

	// Check resume.
	if *output != "" {
		done, err := loadCompletedIDs(*output)
		if err != nil {
			fmt.Fprintf(os.Stderr, "warning: reading existing results: %v\n", err)
		}
		if _, ok := done[g.ID]; ok {
			fmt.Fprintf(os.Stderr, "SKIP: %s already in output\n", g.ID)
			return
		}
	}

	// Context with budgets.
	ctx := context.Background()
	if *globalBudget > 0 {
		var cancel context.CancelFunc
		ctx, cancel = context.WithTimeout(ctx, *globalBudget)
		defer cancel()
	}
	tctx, cancel := context.WithTimeout(ctx, *targetBudget)
	defer cancel()

	var result beta0Result
	switch mode {
	case "exact":
		result = runExact(tctx, g, *workers, *crossCheck)
	case "hunt":
		result = runHunt(tctx, g, *workers, *threshold, *crossCheck)
	}

	// Write result.
	rec, err := json.Marshal(result)
	if err != nil {
		fmt.Fprintf(os.Stderr, "error marshaling result: %v\n", err)
		os.Exit(1)
	}

	if *output != "" {
		f, err := os.OpenFile(*output, os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0o644)
		if err != nil {
			fmt.Fprintf(os.Stderr, "error opening output: %v\n", err)
			os.Exit(1)
		}
		if _, err := fmt.Fprintf(f, "%s\n", rec); err != nil {
			f.Close()
			fmt.Fprintf(os.Stderr, "error writing output: %v\n", err)
			os.Exit(1)
		}
		if err := f.Sync(); err != nil {
			fmt.Fprintf(os.Stderr, "warning: fsync: %v\n", err)
		}
		if err := f.Close(); err != nil {
			fmt.Fprintf(os.Stderr, "warning: close: %v\n", err)
		}
	} else {
		fmt.Println(string(rec))
	}

	// Summary to stderr.
	fmt.Fprintf(os.Stderr, "\n=== RESULT ===\n")
	fmt.Fprintf(os.Stderr, "  id:         %s\n", result.ID)
	fmt.Fprintf(os.Stderr, "  beta_0:     %d\n", result.Beta0)
	fmt.Fprintf(os.Stderr, "  rho_0:      %s (%.6f)\n", result.Rho0Exact, result.Rho0Float)
	fmt.Fprintf(os.Stderr, "  witness:    orders %v, classes %v\n", result.WitnessOrders, result.WitnessClasses)
	fmt.Fprintf(os.Stderr, "  semantics:  %s\n", result.Semantics)
	fmt.Fprintf(os.Stderr, "  runtime:    %.2fs\n", result.RuntimeSeconds)
	fmt.Fprintf(os.Stderr, "  tpp_checks: %d\n", result.NTPPChecks)
	fmt.Fprintf(os.Stderr, "  candidates: %d\n", result.NCandidates)
	if result.TimedOut {
		fmt.Fprintf(os.Stderr, "  TIMED OUT\n")
	}
	if result.HuntKill {
		fmt.Fprintf(os.Stderr, "  *** KILL: triple exceeds threshold %d ***\n", result.Threshold)
	}
	if result.Error != "" {
		fmt.Fprintf(os.Stderr, "  ERROR: %s\n", result.Error)
		os.Exit(1)
	}
}

// classInfo holds precomputed per-class data.
type classInfo struct {
	order    int
	isNormal bool
	repIdx   int
	members  []int
}

// witness holds the current best witness triple details.
type witness struct {
	product int64
	orders  [3]int
	classes [3]int
	copies  [3]int // index-within-class for S, T, U
	sIdx    int
	tIdx    int
	uIdx    int
	valid   bool
}

func runExact(ctx context.Context, g *tpp.Group, workers int, crossCheck bool) beta0Result {
	t0 := time.Now()
	nG := int64(g.N)

	classes := buildClassInfo(g)
	orderMap := buildOrderMap(classes)
	work, totalCandidates := buildWorkItems(classes, orderMap, nG, 0)

	// Best starts at trivial triple (G, {1}, {1}).
	var bestProduct atomic.Int64
	bestProduct.Store(nG)

	var bestMu sync.Mutex
	best := witness{
		product: nG,
		orders:  [3]int{int(nG), 1, 1},
	}

	var tppChecks, testedTotal, prunedNormal atomic.Int64
	var searchErr error

	lastProgress := time.Now()
	reportProgress := func() {
		now := time.Now()
		if now.Sub(lastProgress) < 30*time.Second {
			return
		}
		lastProgress = now
		bp := bestProduct.Load()
		rho := tpp.NewRational(bp, nG)
		fmt.Fprintf(os.Stderr, "  [%s] candidates %d/%d, best beta_0=%d (rho_0=%s), tpp_checks=%d\n",
			now.Format("15:04:05"),
			testedTotal.Load(), totalCandidates,
			bp, rho.String(), tppChecks.Load())
	}

	runWorkers(ctx, g, classes, work, workers, &bestProduct, func(prod int64, ci, cj, ck int, sIdx, tIdx, uIdx, tCopy, uCopy int) {
		bestMu.Lock()
		if prod > best.product {
			best = witness{
				product: prod,
				orders:  [3]int{classes[ci].order, classes[cj].order, classes[ck].order},
				classes: [3]int{ci, cj, ck},
				copies:  [3]int{0, tCopy, uCopy},
				sIdx:    sIdx,
				tIdx:    tIdx,
				uIdx:    uIdx,
				valid:   true,
			}
		}
		bestMu.Unlock()
	}, &tppChecks, &testedTotal, &prunedNormal, &searchErr, crossCheck, reportProgress)

	elapsed := time.Since(t0).Seconds()

	timedOut := false
	select {
	case <-ctx.Done():
		timedOut = true
	default:
	}

	semantics := "exact"
	if timedOut {
		semantics = "lower_bound"
	}
	errStr := ""
	if searchErr != nil {
		errStr = searchErr.Error()
		semantics = "error"
	}

	bp := best.product
	rho := tpp.NewRational(bp, nG)

	var witnessElts [3][]int
	if best.valid {
		witnessElts = extractWitnessElts(g, best.sIdx, best.tIdx, best.uIdx)
	}

	return beta0Result{
		ID:             g.ID,
		Description:    g.Description,
		Order:          g.N,
		Mode:           "exact",
		Beta0:          bp,
		Rho0Exact:      rho.String(),
		Rho0Float:      rho.Float64(),
		WitnessOrders:  best.orders,
		WitnessClasses: best.classes,
		WitnessCopies:  best.copies,
		WitnessElts:    witnessElts,
		Semantics:      semantics,
		NCandidates:    totalCandidates,
		NTPPChecks:     tppChecks.Load(),
		NTriplesTested: testedTotal.Load(),
		NPrunedNormal:  prunedNormal.Load(),
		NClasses:       len(g.Classes),
		NSubgroups:     len(g.Subgroups),
		RuntimeSeconds: elapsed,
		TimedOut:       timedOut,
		Error:          errStr,
	}
}

func runHunt(ctx context.Context, g *tpp.Group, workers int, threshold int64, crossCheck bool) beta0Result {
	t0 := time.Now()
	nG := int64(g.N)

	classes := buildClassInfo(g)
	orderMap := buildOrderMap(classes)
	// In hunt mode, only consider triples with product > threshold.
	work, totalCandidates := buildWorkItems(classes, orderMap, nG, threshold)

	// Hunt: we want the first triple that beats the threshold.
	// Start bestProduct at the threshold so the engine skips anything <= it.
	var bestProduct atomic.Int64
	bestProduct.Store(threshold)

	var bestMu sync.Mutex
	best := witness{product: 0}

	var tppChecks, testedTotal, prunedNormal atomic.Int64
	var searchErr error
	huntCtx, huntCancel := context.WithCancel(ctx)
	defer huntCancel()

	var found atomic.Bool

	lastProgress := time.Now()
	reportProgress := func() {
		now := time.Now()
		if now.Sub(lastProgress) < 30*time.Second {
			return
		}
		lastProgress = now
		fmt.Fprintf(os.Stderr, "  [%s] hunt: candidates %d/%d, tpp_checks=%d, threshold=%d\n",
			now.Format("15:04:05"),
			testedTotal.Load(), totalCandidates,
			tppChecks.Load(), threshold)
	}

	runWorkers(huntCtx, g, classes, work, workers, &bestProduct, func(prod int64, ci, cj, ck int, sIdx, tIdx, uIdx, tCopy, uCopy int) {
		if prod > threshold && !found.Load() {
			found.Store(true)
			bestMu.Lock()
			best = witness{
				product: prod,
				orders:  [3]int{classes[ci].order, classes[cj].order, classes[ck].order},
				classes: [3]int{ci, cj, ck},
				copies:  [3]int{0, tCopy, uCopy},
				sIdx:    sIdx,
				tIdx:    tIdx,
				uIdx:    uIdx,
				valid:   true,
			}
			bestMu.Unlock()
			huntCancel() // Stop all workers.
		}
	}, &tppChecks, &testedTotal, &prunedNormal, &searchErr, crossCheck, reportProgress)

	elapsed := time.Since(t0).Seconds()

	timedOut := false
	select {
	case <-ctx.Done():
		timedOut = true
	default:
	}

	semantics := "lower_bound"
	errStr := ""
	if searchErr != nil {
		errStr = searchErr.Error()
		semantics = "error"
	}

	// Brute-force re-check any hunt hit.
	huntKill := false
	bruteOK := false
	if best.valid && best.product > threshold {
		sRep := &g.Subgroups[best.sIdx]
		tSub := &g.Subgroups[best.tIdx]
		uSub := &g.Subgroups[best.uIdx]
		bruteOK = g.TPPBruteCheck(sRep, tSub, uSub)
		if bruteOK {
			huntKill = true
			fmt.Fprintf(os.Stderr, "\n*** KILL: TPP triple with product %d > threshold %d ***\n", best.product, threshold)
			fmt.Fprintf(os.Stderr, "  orders: %v, brute re-check: PASSED\n", best.orders)
		} else {
			errStr = fmt.Sprintf("HUNT HIT FAILED BRUTE RECHECK: product %d, orders %v", best.product, best.orders)
			semantics = "error"
		}
	}

	bp := best.product
	if bp == 0 {
		bp = nG // fallback to trivial
	}
	rho := tpp.NewRational(bp, nG)

	var witnessElts [3][]int
	if best.valid {
		witnessElts = extractWitnessElts(g, best.sIdx, best.tIdx, best.uIdx)
	}

	return beta0Result{
		ID:             g.ID,
		Description:    g.Description,
		Order:          g.N,
		Mode:           "hunt",
		Beta0:          bp,
		Rho0Exact:      rho.String(),
		Rho0Float:      rho.Float64(),
		WitnessOrders:  best.orders,
		WitnessClasses: best.classes,
		WitnessCopies:  best.copies,
		WitnessElts:    witnessElts,
		Semantics:      semantics,
		Threshold:      threshold,
		HuntKill:       huntKill,
		BruteRecheck:   bruteOK,
		NCandidates:    totalCandidates,
		NTPPChecks:     tppChecks.Load(),
		NTriplesTested: testedTotal.Load(),
		NPrunedNormal:  prunedNormal.Load(),
		NClasses:       len(g.Classes),
		NSubgroups:     len(g.Subgroups),
		RuntimeSeconds: elapsed,
		TimedOut:       timedOut,
		Error:          errStr,
	}
}

type workItem struct {
	cS, cT, cU int
	product    int
}

func buildClassInfo(g *tpp.Group) []classInfo {
	nC := len(g.Classes)
	classes := make([]classInfo, nC)
	for c := 0; c < nC; c++ {
		repIdx := g.ClassRep[c]
		rep := &g.Subgroups[repIdx]
		classes[c] = classInfo{
			order:    rep.Order,
			isNormal: rep.IsNormal,
			repIdx:   repIdx,
			members:  g.Classes[c],
		}
	}
	return classes
}

func buildOrderMap(classes []classInfo) map[int][]int {
	om := map[int][]int{}
	for c, ci := range classes {
		om[ci.order] = append(om[ci.order], c)
	}
	return om
}

func buildWorkItems(classes []classInfo, orderMap map[int][]int, nG int64, minProduct int64) ([]workItem, int64) {
	// Minimum product threshold: at least nG (trivial), or minProduct if higher.
	cutoff := nG
	if minProduct > cutoff {
		cutoff = minProduct
	}

	type orderTriple struct {
		product    int
		oS, oT, oU int
	}
	var triples []orderTriple
	for oS := range orderMap {
		for oT := range orderMap {
			for oU := range orderMap {
				prod := oS * oT * oU
				if int64(prod) <= cutoff {
					continue
				}
				// Neumann Obs 3.1.
				if int64(oS)*int64(oT+oU-1) > nG {
					continue
				}
				if int64(oT)*int64(oS+oU-1) > nG {
					continue
				}
				if int64(oU)*int64(oS+oT-1) > nG {
					continue
				}
				triples = append(triples, orderTriple{prod, oS, oT, oU})
			}
		}
	}
	sort.Slice(triples, func(i, j int) bool {
		return triples[i].product > triples[j].product
	})

	var work []workItem
	var totalCandidates int64
	for _, ot := range triples {
		for _, cs := range orderMap[ot.oS] {
			for _, ct := range orderMap[ot.oT] {
				for _, cu := range orderMap[ot.oU] {
					work = append(work, workItem{cs, ct, cu, ot.product})
					totalCandidates += int64(len(classes[ct].members)) * int64(len(classes[cu].members))
				}
			}
		}
	}
	sort.Slice(work, func(i, j int) bool {
		return work[i].product > work[j].product
	})
	return work, totalCandidates
}

// onHit is called when a TPP triple is found that beats the current best.
type onHitFunc func(prod int64, ci, cj, ck int, sIdx, tIdx, uIdx, tCopy, uCopy int)

func runWorkers(
	ctx context.Context,
	g *tpp.Group,
	classes []classInfo,
	work []workItem,
	workers int,
	bestProduct *atomic.Int64,
	onHit onHitFunc,
	tppChecks, testedTotal, prunedNormal *atomic.Int64,
	searchErr *error,
	crossCheck bool,
	reportProgress func(),
) {
	var wg sync.WaitGroup
	var errMu sync.Mutex
	workCh := make(chan workItem, len(work))
	for _, w := range work {
		workCh <- w
	}
	close(workCh)

	for w := 0; w < workers; w++ {
		wg.Add(1)
		go func() {
			defer func() {
				if r := recover(); r != nil {
					errMu.Lock()
					*searchErr = fmt.Errorf("panic in worker: %v", r)
					errMu.Unlock()
				}
				wg.Done()
			}()

			for wi := range workCh {
				select {
				case <-ctx.Done():
					return
				default:
				}

				prod := int64(wi.product)
				if prod <= bestProduct.Load() {
					continue
				}

				ci := classes[wi.cS]
				cj := classes[wi.cT]
				ck := classes[wi.cU]

				// Murthy pruning: non-trivial triple => all non-normal.
				if ci.isNormal || cj.isNormal || ck.isNormal {
					prunedNormal.Add(1)
					continue
				}

				sRep := &g.Subgroups[ci.repIdx]

				for tCopy, tIdx := range cj.members {
					select {
					case <-ctx.Done():
						return
					default:
					}

					tSub := &g.Subgroups[tIdx]

					for uCopy, uIdx := range ck.members {
						uSub := &g.Subgroups[uIdx]

						tppChecks.Add(1)
						testedTotal.Add(1)

						ok := g.TPPSetCheck(sRep, tSub, uSub)

						if crossCheck {
							okBrute := g.TPPBruteCheck(sRep, tSub, uSub)
							if ok != okBrute {
								errMu.Lock()
								*searchErr = fmt.Errorf(
									"TPP cross-validation mismatch: set=%v brute=%v, S class %d T idx %d U idx %d",
									ok, okBrute, wi.cS, tIdx, uIdx)
								errMu.Unlock()
								return
							}
						}

						if ok && prod > bestProduct.Load() {
							bestProduct.Store(prod)
							onHit(prod, wi.cS, wi.cT, wi.cU, ci.repIdx, tIdx, uIdx, tCopy, uCopy)
						}
					}
				}
				reportProgress()
			}
		}()
	}

	wg.Wait()
}

func extractWitnessElts(g *tpp.Group, sIdx, tIdx, uIdx int) [3][]int {
	var result [3][]int
	for i, idx := range [3]int{sIdx, tIdx, uIdx} {
		sub := &g.Subgroups[idx]
		elts := make([]int, len(sub.EltList))
		for j, e := range sub.EltList {
			elts[j] = int(e)
		}
		result[i] = elts
	}
	return result
}

func loadCompletedIDs(path string) (map[string]struct{}, error) {
	m := map[string]struct{}{}
	f, err := os.Open(path)
	if err != nil {
		if os.IsNotExist(err) {
			return m, nil
		}
		return m, err
	}
	defer f.Close()

	scanner := bufio.NewScanner(f)
	for scanner.Scan() {
		line := strings.TrimSpace(scanner.Text())
		if line == "" {
			continue
		}
		var rec struct {
			ID string `json:"id"`
		}
		if err := json.Unmarshal([]byte(line), &rec); err != nil {
			continue
		}
		if rec.ID != "" {
			m[rec.ID] = struct{}{}
		}
	}
	return m, scanner.Err()
}

func usage() {
	fmt.Fprintf(os.Stderr, "Usage: beta0probe <exact|hunt> [flags]\n")
	fmt.Fprintf(os.Stderr, "\nModes:\n")
	fmt.Fprintf(os.Stderr, "  exact    Exhaustive beta_0(G) computation\n")
	fmt.Fprintf(os.Stderr, "  hunt     Find first triple exceeding --threshold\n")
	fmt.Fprintf(os.Stderr, "\nRun 'beta0probe <mode> -help' for mode-specific flags.\n")
}
