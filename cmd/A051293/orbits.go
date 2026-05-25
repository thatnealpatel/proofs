package main

import "fmt"

// runOrbits explores the orbit structure of per_k_identity under rotation.
//
// For each k, the identity equates:
//   LHS: {nonempty S ⊆ {1,...,k} : k | sum(S)}
//   RHS: {S ⊆ {1,...,k} : k ∈ S, |S| | sum(S)}
//
// A natural bijection via rotation does NOT exist. The identity holds
// by double-counting: define for each nonempty S ⊆ {0,...,k-1}:
//
//   α(k,S) = #{r < k : k | (sum(S) + |S|·r)}
//   β(k,S) = #{j < |S| : |S| | (sum(S) + k·j)}
//
// Both equal gcd(|S|,k) when gcd(|S|,k) | sum(S), else 0.
// Summing over all nonempty S:
//   ∑ α = k·|LHS|   (rotation uniformity)
//   ∑ β = k·|RHS|    (host decomposition)
// Since α = β pointwise, |LHS| = |RHS|.
func runOrbits(_ []string) {
	for k := 1; k <= 16; k++ {
		sumAlpha := 0
		for mask := 1; mask < (1 << k); mask++ {
			d := popcount(mask)
			sm := subsetSum(mask, k)
			g := gcd(d, k)
			if sm%g == 0 {
				sumAlpha += g
			}
		}

		bComb := 0
		for mask := 0; mask < (1 << k); mask++ {
			if subsetSum(mask, k)%k == 0 {
				bComb++
			}
		}

		rhsCount := 0
		for mask := 1; mask < (1 << k); mask++ {
			if mask&(1<<(k-1)) == 0 {
				continue
			}
			d := popcount(mask)
			if subsetSum(mask, k)%d == 0 {
				rhsCount++
			}
		}

		fmt.Printf("k=%2d  ∑α=%6d  k·(b-1)=%6d  k·|RHS|=%6d  match=%v\n",
			k, sumAlpha, k*(bComb-1), k*rhsCount,
			sumAlpha == k*(bComb-1) && sumAlpha == k*rhsCount)
	}
}

func subsetSum(mask, k int) int {
	total := 0
	for i := 0; i < k; i++ {
		if mask&(1<<i) != 0 {
			total += i + 1
		}
	}
	return total
}

func popcount(x int) int {
	c := 0
	for x != 0 {
		c++
		x &= x - 1
	}
	return c
}

func gcd(a, b int) int {
	for b != 0 {
		a, b = b, a%b
	}
	return a
}
