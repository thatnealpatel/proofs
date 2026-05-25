package main

import (
	"fmt"
	"math/big"
	"runtime"
	"strconv"
	"sync"
)

func runDensity(args []string) {
	N := 10_000
	if len(args) > 0 {
		N, _ = strconv.Atoi(args[0])
	}

	isPrime := sieve(N + 2)
	workers := runtime.GOMAXPROCS(0)
	results := make([]int64, N+1)

	var wg sync.WaitGroup
	wg.Add(workers)
	for w := range workers {
		go func() {
			defer wg.Done()
			for n := w + 1; n <= N; n += workers {
				results[n] = h(n, isPrime)
			}
		}()
	}
	wg.Wait()

	freq := make(map[int64]int)
	primes := []int64{3, 5, 7, 11, 13, 17, 19, 23, 29, 31}
	step := max(N/10, 1)

	fmt.Printf("%8s", "n")
	for _, p := range primes {
		fmt.Printf("   δ_%-3d", p)
	}
	fmt.Printf("     Σ\n")

	for n := 1; n <= N; n++ {
		freq[results[n]]++
		if n%step == 0 {
			fmt.Printf("%8d", n)
			sum := 0.0
			for _, p := range primes {
				d := float64(freq[p]) / float64(n)
				fmt.Printf("  %.4f", d)
				sum += d
			}
			fmt.Printf("  %.4f\n", sum)
		}
	}
}

func sieve(n int) []bool {
	s := make([]bool, n)
	for i := 2; i < n; i++ {
		s[i] = true
	}
	for i := 2; i*i < n; i++ {
		if s[i] {
			for j := i * i; j < n; j += i {
				s[j] = false
			}
		}
	}
	return s
}

func h(n int, isPrime []bool) int64 {
	one := big.NewInt(1)
	g := new(big.Int).Lsh(big.NewInt(1), uint(n))
	g.Sub(g, one)
	if g.Cmp(one) <= 0 {
		return 2
	}
	r := new(big.Int)
	bn := big.NewInt(int64(n))
	for k := 3; k < len(isPrime); k++ {
		if !isPrime[k] {
			continue
		}
		r.Exp(big.NewInt(int64(k)), bn, g)
		r.Sub(r, one)
		if r.Sign() < 0 {
			r.Add(r, g)
		}
		g.GCD(nil, nil, g, r)
		if g.Cmp(one) <= 0 {
			return int64(k)
		}
	}
	return -1
}
