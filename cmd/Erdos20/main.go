package main

import (
	"context"
	"errors"
	"flag"
	"fmt"
	"math"
	"math/bits"
	"os"
	"strconv"
	"sync"
	"sync/atomic"
	"time"
)

const usageText = `Usage:
  Erdos20 search [flags]
  Erdos20 spread [flags]

Subcommands:
  search  exhaustive uniform-family search using exact sunflower numbers and shifts to a fixed point
  spread  run the spread-defect zoo using budgeted sunflower numbers and one lexicographic shift sweep

Run "Erdos20 <subcommand> -h" for subcommand flags.`

func main() {
	if len(os.Args) < 2 {
		fmt.Fprintln(os.Stderr, usageText)
		os.Exit(2)
	}
	var err error
	switch os.Args[1] {
	case "search":
		err = searchCommand(os.Args[2:])
	case "spread":
		err = spreadCommand(os.Args[2:])
	case "help", "-h", "--help":
		fmt.Println(usageText)
		return
	default:
		fmt.Fprintf(os.Stderr, "unknown subcommand %q\n\n%s\n", os.Args[1], usageText)
		os.Exit(2)
	}
	if errors.Is(err, flag.ErrHelp) {
		return
	}
	if err != nil {
		fmt.Fprintf(os.Stderr, "error: %v\n", err)
		os.Exit(1)
	}
}

func searchCommand(args []string) error {
	fs := flag.NewFlagSet("search", flag.ContinueOnError)
	fs.SetOutput(os.Stderr)
	fs.Usage = func() {
		fmt.Fprintln(fs.Output(), "Usage: Erdos20 search [flags]")
		fs.PrintDefaults()
	}
	timeout := fs.Duration("timeout", 5*time.Minute, "computation timeout")
	n := fs.Int("n", 6, "ground set size [n]")
	k := fs.Int("k", 3, "uniformity")
	workers := fs.Int("workers", 32, "parallel workers")
	if err := fs.Parse(args); err != nil {
		return err
	}
	if fs.NArg() != 0 {
		return fmt.Errorf("search: unexpected arguments: %v", fs.Args())
	}
	if *timeout <= 0 {
		return fmt.Errorf("search: timeout must be positive")
	}
	if *n < 0 || *n > bits.UintSize {
		return fmt.Errorf("search: n must be between 0 and %d", bits.UintSize)
	}
	if *k < 0 || *k > *n {
		return fmt.Errorf("search: k must be between 0 and n")
	}
	if *workers <= 0 {
		return fmt.Errorf("search: workers must be positive")
	}
	setCount := nChooseK(*n, *k)
	if setCount >= strconv.IntSize-1 {
		return fmt.Errorf("search: C(n,k)=%d is too large for exhaustive family enumeration", setCount)
	}

	ctx, cancel := context.WithTimeout(context.Background(), *timeout)
	defer cancel()
	runSearch(ctx, *n, *k, *workers)
	return nil
}

type searchResult struct {
	ratio   float64
	family  []uint
	shifted []uint
	tauF    int
	tauSF   int
}

func runSearch(ctx context.Context, n, k, workers int) {
	ksets := allKSets(n, k)
	total := (1 << len(ksets)) - 1
	fmt.Printf("n=%d k=%d: %d k-sets, %d families, %d workers\n", n, k, len(ksets), total, workers)

	start := time.Now()
	var checked atomic.Int64
	var found atomic.Bool
	var mu sync.Mutex
	best := searchResult{}
	var bestRatio atomic.Int64
	var wg sync.WaitGroup

	for w := 0; w < workers; w++ {
		wg.Add(1)
		go func(workerID int) {
			defer wg.Done()
			var local searchResult
			for mask := workerID + 1; mask <= total; mask += workers {
				if ctx.Err() != nil || found.Load() {
					return
				}
				family := maskToFamily(ksets, mask)
				if len(family) < 2 {
					checked.Add(1)
					continue
				}
				tauF := maxSunflowerExact(family)
				if tauF < 2 {
					checked.Add(1)
					continue
				}
				shifted := shiftToFixedPoint(family, n)
				tauSF := maxSunflowerExact(shifted)
				bound := 3 * tauF * tauF
				if tauSF > bound {
					if found.CompareAndSwap(false, true) {
						fmt.Fprintln(os.Stderr)
						fmt.Printf("COUNTEREXAMPLE: tau(F)=%d, tau(S(F))=%d, bound=3*%d^2=%d\n", tauF, tauSF, tauF, bound)
						fmt.Printf("  F = %v\n", familyToOneBasedSets(family))
						fmt.Printf("  S(F) = %v\n", familyToOneBasedSets(shifted))
					}
					return
				}
				ratio := float64(tauSF) / float64(bound)
				if ratio > local.ratio {
					local = searchResult{ratio, append([]uint(nil), family...), append([]uint(nil), shifted...), tauF, tauSF}
				}
				checked.Add(1)
			}
			mu.Lock()
			if local.ratio > best.ratio {
				best = local
				bestRatio.Store(int64(math.Float64bits(local.ratio)))
			}
			mu.Unlock()
		}(w)
	}

	done := make(chan struct{})
	go func() {
		wg.Wait()
		close(done)
	}()
	ticker := time.NewTicker(100 * time.Millisecond)
	defer ticker.Stop()
	for {
		select {
		case <-ticker.C:
			c := checked.Load()
			r := math.Float64frombits(uint64(bestRatio.Load()))
			fmt.Fprintf(os.Stderr, "\r  %s  checked %d / %d (%.1f%%) max_ratio=%.4f", time.Since(start).Truncate(time.Millisecond), c, total, 100*float64(c)/float64(total), r)
		case <-done:
			fmt.Fprint(os.Stderr, "\r\033[2K")
			elapsed := time.Since(start).Truncate(time.Millisecond)
			if !found.Load() {
				fmt.Printf("checked %d families in %s, no counterexample found\n", checked.Load(), elapsed)
				fmt.Printf("tightest: tau(F)=%d, tau(S(F))=%d, bound=%d, ratio=%.4f\n", best.tauF, best.tauSF, 3*best.tauF*best.tauF, best.ratio)
				fmt.Printf("  F = %v\n", familyToOneBasedSets(best.family))
			}
			return
		}
	}
}

func maskToFamily(ksets []uint, mask int) []uint {
	var family []uint
	for i, s := range ksets {
		if mask&(1<<i) != 0 {
			family = append(family, s)
		}
	}
	return family
}

func familyToOneBasedSets(family []uint) [][]int {
	result := make([][]int, 0, len(family))
	for _, s := range family {
		var elems []int
		for b := s; b != 0; b &= b - 1 {
			elems = append(elems, bits.TrailingZeros(b)+1)
		}
		result = append(result, elems)
	}
	return result
}
