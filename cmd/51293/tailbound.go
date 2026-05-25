package main

import (
	"fmt"
	"math"
	"math/big"
)

// fubiniExact computes fubini(n) exactly using the recurrence.
func fubiniExact(n int) *big.Int {
	if n == 0 {
		return big.NewInt(1)
	}
	s := new(big.Int)
	for k := 0; k < n; k++ {
		c := new(big.Int).Binomial(int64(n), int64(k))
		c.Mul(c, fubiniExact(k))
		s.Add(s, c)
	}
	return s
}

// runTailbound verifies the key identity and bound needed to close
// the last sorry in A051293.lean:
//
//   Identity:  ∑_{m=0}^i C(i,m)·fubini(m) = 2·fubini(i)  for i ≥ 1
//   Bound:     |∑_{j<n} j^i/2^j - 2·fubini(i)| ≤ 4·fubini(i)·n^i/2^n
//
// The identity follows from the Fubini recurrence:
//   fubini(i) = ∑_{m=0}^{i-1} C(i,m)·fubini(m)
// so the full sum ∑_{m=0}^i = fubini(i) + C(i,i)·fubini(i) = 2·fubini(i).
func runTailbound(_ []string) {
	fmt.Println("=== Identity: sum_{m=0}^i C(i,m)*fubini(m) vs 2*fubini(i) ===")
	for i := 0; i <= 10; i++ {
		sum := new(big.Int)
		for m := 0; m <= i; m++ {
			c := new(big.Int).Binomial(int64(i), int64(m))
			c.Mul(c, fubiniExact(m))
			sum.Add(sum, c)
		}
		twice := new(big.Int).Mul(big.NewInt(2), fubiniExact(i))
		fmt.Printf("i=%2d: sum=%s, 2*fubini(i)=%s, eq=%v\n", i, sum, twice, sum.Cmp(twice) == 0)
	}

	fmt.Println("\n=== Decomposition: recurrence part vs fubini(i) ===")
	for i := 1; i <= 8; i++ {
		recPart := new(big.Int)
		for m := 0; m < i; m++ {
			c := new(big.Int).Binomial(int64(i), int64(m))
			c.Mul(c, fubiniExact(m))
			recPart.Add(recPart, c)
		}
		fi := fubiniExact(i)
		fmt.Printf("i=%d: sum_{m<i} C(i,m)*fubini(m)=%s, fubini(i)=%s, eq=%v\n",
			i, recPart, fi, recPart.Cmp(fi) == 0)
	}

	fmt.Println("\n=== Tail bound: |partial - tsum| <= 4*fubini(i)*n^i/2^n ===")
	for i := 0; i <= 6; i++ {
		fi := float64(fubiniExact(i).Int64())
		tsum := 2.0 * fi
		for n := 1; n <= 20; n++ {
			partial := 0.0
			for j := 0; j < n; j++ {
				partial += math.Pow(float64(j), float64(i)) / math.Pow(2, float64(j))
			}
			lhs := math.Abs(partial - tsum)
			rhs := 4 * fi * math.Pow(float64(n), float64(i)) / math.Pow(2, float64(n))
			ratio := 0.0
			if rhs > 0 {
				ratio = lhs / rhs
			}
			if n <= 3 || n == 10 || n == 20 {
				fmt.Printf("i=%d n=%2d: |err|=%.6e bound=%.6e ratio=%.4f ok=%v\n",
					i, n, lhs, rhs, ratio, lhs <= rhs+1e-12)
			}
		}
	}
}
