package main

import (
	"fmt"
	"sort"
	"strings"
)

type subset struct {
	elems []int
	sum   int
	size  int
}

func (s subset) String() string {
	parts := make([]string, len(s.elems))
	for i, e := range s.elems {
		parts[i] = fmt.Sprintf("%d", e)
	}
	return "{" + strings.Join(parts, ",") + "}"
}

func allSubsets(n int) []subset {
	var out []subset
	for mask := 0; mask < (1 << n); mask++ {
		var s subset
		for j := 0; j < n; j++ {
			if mask&(1<<j) != 0 {
				s.elems = append(s.elems, j+1)
				s.sum += j + 1
				s.size++
			}
		}
		out = append(out, s)
	}
	return out
}

// runCounting prints both sides of identity (A) in detail for small n,
// showing exactly which objects each side counts.
//
// Formula side: for each k=1..n, nonempty S ⊆ {1,...,k} with k | sum(S).
// Combinatorial side: nonempty S ⊆ {1,...,n} with |S| | sum(S).
func runCounting(_ []string) {
	for n := 1; n <= 6; n++ {
		fmt.Printf("\n===== n = %d =====\n", n)

		// Formula side: collect (k, S) pairs
		type formulaEntry struct {
			k int
			s subset
			q int // sum/k
		}
		var fEntries []formulaEntry
		for k := 1; k <= n; k++ {
			for _, s := range allSubsets(k) {
				if s.size == 0 {
					continue
				}
				if s.sum%k == 0 {
					fEntries = append(fEntries, formulaEntry{k, s, s.sum / k})
				}
			}
		}

		// Combinatorial side: nonempty S ⊆ {1,...,n} with |S| | sum(S)
		type combEntry struct {
			s    subset
			mean int // sum/|S|
		}
		var cEntries []combEntry
		for _, s := range allSubsets(n) {
			if s.size == 0 {
				continue
			}
			if s.sum%s.size == 0 {
				cEntries = append(cEntries, combEntry{s, s.sum / s.size})
			}
		}

		fmt.Printf("Formula side (%d entries):\n", len(fEntries))
		for _, e := range fEntries {
			fmt.Printf("  k=%d: %s  sum=%d  q=sum/k=%d\n", e.k, e.s, e.s.sum, e.q)
		}
		fmt.Printf("Combinatorial side (%d entries):\n", len(cEntries))
		for _, e := range cEntries {
			fmt.Printf("  %s  |S|=%d  sum=%d  mean=%d\n", e.s, e.s.size, e.s.sum, e.mean)
		}

		// Check: do the (size, mean) pairs on the formula side match
		// the (k, q) pairs? i.e., is there a bijection by (k ↔ mean, |S| ↔ ???)?
		fmt.Println("Formula (k, q) pairs:")
		fPairs := make(map[[2]int]int)
		for _, e := range fEntries {
			fPairs[[2]int{e.k, e.q}]++
		}
		keys := make([][2]int, 0, len(fPairs))
		for k := range fPairs {
			keys = append(keys, k)
		}
		sort.Slice(keys, func(i, j int) bool {
			if keys[i][0] != keys[j][0] {
				return keys[i][0] < keys[j][0]
			}
			return keys[i][1] < keys[j][1]
		})
		for _, k := range keys {
			fmt.Printf("  (k=%d, q=%d): %d\n", k[0], k[1], fPairs[k])
		}

		fmt.Println("Combinatorial (|S|, mean) pairs:")
		cPairs := make(map[[2]int]int)
		for _, e := range cEntries {
			cPairs[[2]int{e.s.size, e.mean}]++
		}
		keys = keys[:0]
		for k := range cPairs {
			keys = append(keys, k)
		}
		sort.Slice(keys, func(i, j int) bool {
			if keys[i][0] != keys[j][0] {
				return keys[i][0] < keys[j][0]
			}
			return keys[i][1] < keys[j][1]
		})
		for _, k := range keys {
			fmt.Printf("  (|S|=%d, mean=%d): %d\n", k[0], k[1], cPairs[k])
		}

		if len(fEntries) != len(cEntries) {
			fmt.Printf("MISMATCH: %d != %d\n", len(fEntries), len(cEntries))
		} else {
			fmt.Printf("MATCH: both %d\n", len(fEntries))
		}
	}
}
