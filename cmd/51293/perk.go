package main

import "fmt"

// runPerk verifies the per-k identity that decomposes (A) into n
// independent single-k statements:
//
//   #{nonempty S ⊆ {1,...,k} : k | sum(S)}
//     = #{S ⊆ {1,...,k} : k ∈ S, |S| | sum(S)}
//
// If this holds for each k, then summing over k=1..n and using the
// fact that "k ∈ S with S ⊆ {1,...,k}" partitions subsets by max(S)
// gives identity (A): Σ (b(k)-1) = #{integer-mean subsets of {1,...,n}}.
//
// Gus Wiseman (OEIS A063776, 2019) observes this equality but no
// proof is cited.
func runPerk(_ []string) {
	fmt.Printf("%4s  %10s  %10s  %5s\n", "k", "mod-k", "max=k+mean", "match")
	for k := 1; k <= 22; k++ {
		modK := 0    // nonempty S ⊆ {1,...,k} with k | sum(S)
		maxK := 0    // S ⊆ {1,...,k} with k ∈ S and |S| | sum(S)
		for mask := 1; mask < (1 << k); mask++ {
			s, sz := 0, 0
			hasK := false
			for j := 0; j < k; j++ {
				if mask&(1<<j) != 0 {
					s += j + 1
					sz++
					if j+1 == k {
						hasK = true
					}
				}
			}
			if s%k == 0 {
				modK++
			}
			if hasK && s%sz == 0 {
				maxK++
			}
		}
		fmt.Printf("%4d  %10d  %10d  %5v\n", k, modK, maxK, modK == maxK)
	}
}
