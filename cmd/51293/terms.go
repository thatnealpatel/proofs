package main

import (
	"fmt"
	"math/big"
	"os"
	"runtime"
	"strconv"
	"sync"
)

var oeisTerms = [...]int64{
	1, 2, 5, 8, 15, 26, 45, 76, 135, 238,
	425, 768, 1399, 2570, 4761, 8856, 16567, 31138, 58733, 111164,
	211043, 401694, 766417, 1465488, 2807671, 5388782, 10359849, 19946832, 38459623, 74251094,
	143524761, 277742488, 538043663, 1043333934, 2025040765, 3933915348,
}

func runTerms(args []string) {
	N := len(oeisTerms)
	if len(args) > 0 {
		var err error
		N, err = strconv.Atoi(args[0])
		if err != nil {
			fmt.Fprintf(os.Stderr, "invalid N: %v\n", err)
			os.Exit(1)
		}
	}

	bs := computeB(N)

	one := big.NewInt(1)
	a := new(big.Int)
	verified := 0
	for k := 1; k <= N; k++ {
		a.Add(a, bs[k])
		a.Sub(a, one)
		fmt.Printf("a(%d) = %s\n", k, a)
		if k <= len(oeisTerms) && a.Cmp(big.NewInt(oeisTerms[k-1])) == 0 {
			verified++
		}
	}

	checked := min(N, len(oeisTerms))
	if checked > 0 {
		if verified == checked {
			fmt.Printf("\nverified: %d/%d terms match OEIS A051293\n", verified, checked)
		} else {
			fmt.Fprintf(os.Stderr, "\nERROR: only %d/%d terms match OEIS A051293\n", verified, checked)
			os.Exit(1)
		}
	}
}

// computeB computes b(k) for k=1..N in parallel.
// b(k) = (1/k) * Sum_{d|k, d odd} 2^(k/d) * phi(d)
func computeB(N int) []*big.Int {
	bs := make([]*big.Int, N+1)
	workers := runtime.GOMAXPROCS(0)
	var wg sync.WaitGroup
	wg.Add(workers)
	for w := range workers {
		go func() {
			defer wg.Done()
			for k := w + 1; k <= N; k += workers {
				bs[k] = bFunc(k)
			}
		}()
	}
	wg.Wait()
	return bs
}

func bFunc(k int) *big.Int {
	sum := new(big.Int)
	for d := 1; d <= k; d++ {
		if k%d != 0 || d%2 == 0 {
			continue
		}
		term := new(big.Int).Lsh(big.NewInt(1), uint(k/d))
		term.Mul(term, big.NewInt(int64(eulerPhi(d))))
		sum.Add(sum, term)
	}
	sum.Div(sum, big.NewInt(int64(k)))
	return sum
}

func eulerPhi(n int) int {
	if n == 1 {
		return 1
	}
	result := n
	temp := n
	for p := 2; p*p <= temp; p++ {
		if temp%p == 0 {
			for temp%p == 0 {
				temp /= p
			}
			result -= result / p
		}
	}
	if temp > 1 {
		result -= result / temp
	}
	return result
}
