package tpp

import (
	"context"
	"fmt"
	"sort"
	"sync"
	"sync/atomic"
	"time"
)

// SearchConfig controls the search for a single target.
type SearchConfig struct {
	// CrossValidate enables brute-force cross-validation of every TPP
	// result against the set-based checker (mandatory in toy mode).
	CrossValidate bool
	// Progress callback, called at most every ProgressInterval.
	Progress func(msg string)
	// ProgressInterval controls how often Progress is called.
	ProgressInterval time.Duration
	// Workers is the number of parallel goroutines per target.
	// 0 means runtime.NumCPU().
	Workers int
}

// Search computes rho_0(G) by exhaustive subgroup triple search.
//
// Search-space reduction: TPP is invariant under simultaneous
// conjugation (S,T,U) -> (S^g, T^g, U^g). So for each candidate
// we fix S to a class representative. T and U range over ALL subgroups
// in their conjugacy classes (mixed conjugation does NOT preserve TPP).
//
// The search enumerates order-triple buckets in descending product order,
// with early break once the remaining product cannot beat the current best.
func Search(ctx context.Context, g *Group, cfg SearchConfig) Result {
	t0 := time.Now()
	nC := len(g.Classes)
	nG := int64(g.N)

	stats := Stats{
		NConjClasses: nC,
		NSubgroups:   len(g.Subgroups),
	}

	// Precompute class orders and normality.
	type classInfo struct {
		order    int
		isNormal bool
		repIdx   int   // subgroup index of representative
		members  []int // all subgroup indices in this class
	}
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

	// Group classes by order.
	type orderBucket struct {
		order   int
		classes []int // indices into classes
	}
	orderMap := map[int][]int{}
	for c := 0; c < nC; c++ {
		o := classes[c].order
		orderMap[o] = append(orderMap[o], c)
	}

	// Build order-triple buckets, pruning by Neumann at the order level.
	type orderTriple struct {
		product    int
		oS, oT, oU int
	}
	var triples []orderTriple
	for oS := range orderMap {
		for oT := range orderMap {
			for oU := range orderMap {
				prod := oS * oT * oU
				// Only interesting if product > |G| (ratio > 1) or we might
				// need to confirm ratio = 1 exactly. Include all products >= |G|.
				if int64(prod) < nG {
					continue
				}
				// Neumann Obs 3.1: |X|(|Y|+|Z|-1) <= |G| for all rotations.
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

	// Count total candidates for progress.
	var totalCandidates int64
	for _, ot := range triples {
		cS := orderMap[ot.oS]
		cT := orderMap[ot.oT]
		cU := orderMap[ot.oU]
		// For each class-triple: S rep x all T-class members x all U-class members.
		for _, cs := range cS {
			for _, ct := range cT {
				for _, cu := range cU {
					_ = cs
					totalCandidates += int64(len(classes[ct].members)) * int64(len(classes[cu].members))
				}
			}
		}
	}
	stats.NCandidates = totalCandidates

	// Best product found so far (thread-safe).
	var bestProduct atomic.Int64
	bestProduct.Store(nG) // trivial triple: (G, {1}, {1})

	var bestMu sync.Mutex
	bestTriple := [3]int{int(nG), 1, 1}

	timedOut := false
	var searchErr error

	// Build the work queue: one work item per (classS, classT, classU).
	type workItem struct {
		cS, cT, cU int
		product    int
	}
	var work []workItem
	for _, ot := range triples {
		for _, cs := range orderMap[ot.oS] {
			for _, ct := range orderMap[ot.oT] {
				for _, cu := range orderMap[ot.oU] {
					work = append(work, workItem{cs, ct, cu, ot.product})
				}
			}
		}
	}

	// Sort work items by descending product for early termination.
	sort.Slice(work, func(i, j int) bool {
		return work[i].product > work[j].product
	})

	// Progress tracking.
	var testedTotal atomic.Int64
	var tppChecks atomic.Int64
	var prunedNormal atomic.Int64

	lastProgress := time.Now()
	progressInterval := cfg.ProgressInterval
	if progressInterval == 0 {
		progressInterval = 30 * time.Second
	}

	reportProgress := func() {
		if cfg.Progress == nil {
			return
		}
		now := time.Now()
		if now.Sub(lastProgress) < progressInterval {
			return
		}
		lastProgress = now
		bp := bestProduct.Load()
		rho := NewRational(bp, nG)
		cfg.Progress(fmt.Sprintf("  [%s] candidates %d/%d, best=%s, tpp_checks=%d",
			now.Format("15:04:05"),
			testedTotal.Load(), totalCandidates,
			rho.String(), tppChecks.Load()))
	}

	// Process work items. Use a single goroutine for simplicity and
	// correctness first; parallelism is across targets in the main loop.
	// Within a target, the work items are independent so we can parallelize.
	workers := cfg.Workers
	if workers <= 0 {
		workers = 1
	}

	var wg sync.WaitGroup
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
					bestMu.Lock()
					searchErr = fmt.Errorf("panic in worker: %v", r)
					bestMu.Unlock()
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

				// Early break: if this product cannot beat best, skip.
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

				// Fix S to the class representative.
				sRep := &g.Subgroups[ci.repIdx]

				// Iterate over all T in class cT, all U in class cU.
				for _, tIdx := range cj.members {
					select {
					case <-ctx.Done():
						return
					default:
					}

					tSub := &g.Subgroups[tIdx]

					for _, uIdx := range ck.members {
						uSub := &g.Subgroups[uIdx]

						tppChecks.Add(1)
						testedTotal.Add(1)

						ok := g.TPPSetCheck(sRep, tSub, uSub)

						if cfg.CrossValidate {
							okBrute := g.TPPBruteCheck(sRep, tSub, uSub)
							if ok != okBrute {
								bestMu.Lock()
								searchErr = fmt.Errorf(
									"TPP cross-validation mismatch: set=%v brute=%v, S=%v T=%v U=%v",
									ok, okBrute,
									sRep.EltList, tSub.EltList, uSub.EltList)
								bestMu.Unlock()
								return
							}
						}

						if ok && prod > bestProduct.Load() {
							bestProduct.Store(prod)
							bestMu.Lock()
							bestTriple = [3]int{ci.order, cj.order, ck.order}
							bestMu.Unlock()
						}
					}
				}
				reportProgress()
			}
		}()
	}

	wg.Wait()

	elapsed := time.Since(t0).Seconds()

	bp := bestProduct.Load()
	rho := NewRational(bp, nG)

	select {
	case <-ctx.Done():
		timedOut = true
	default:
	}

	stats.NTriplesTested = testedTotal.Load()
	stats.NTPPChecks = tppChecks.Load()
	stats.NPrunedNormal = prunedNormal.Load()

	semantics := "exact"
	if timedOut {
		semantics = "lower_bound"
	}

	errStr := ""
	if searchErr != nil {
		errStr = searchErr.Error()
		semantics = "error"
	}

	return Result{
		ID:              g.ID,
		Description:     g.Description,
		Order:           g.N,
		Rho0Exact:       rho.String(),
		Rho0Float:       rho.Float64(),
		AchievingTriple: bestTriple,
		ExpectedRho0:    g.ExpRho0,
		Category:        g.Category,
		Stats:           stats,
		RuntimeSeconds:  elapsed,
		TimedOut:        timedOut,
		Semantics:       semantics,
		Error:           errStr,
	}
}
