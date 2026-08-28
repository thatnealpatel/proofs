package main

import (
	"fmt"
	"os"
	"runtime"
	"strconv"
	"sync"
	"sync/atomic"
	"time"
)

func runCounter(args []string) {
	N := 1_000_000
	B := 10_000_000
	if len(args) > 0 {
		N, _ = strconv.Atoi(args[0])
	}
	if len(args) > 1 {
		B, _ = strconv.Atoi(args[1])
	}

	outName := fmt.Sprintf("%d.txt", time.Now().Unix())
	outFile, err := os.Create(outName)
	if err != nil {
		fmt.Fprintf(os.Stderr, "create %s: %v\n", outName, err)
		os.Exit(1)
	}
	defer outFile.Close()

	fmt.Printf("searching n=1..%d for phantom primes up to %d\n", N, B)
	fmt.Printf("counterexamples → %s\n", outName)

	primes, ord2, ord3 := buildOrderTable(B)
	fmt.Printf("sieved %d primes, order table built\n", len(primes))

	workers := runtime.GOMAXPROCS(0)
	var checked atomic.Int64
	var found atomic.Int64

	done := make(chan struct{})
	go func() {
		for {
			select {
			case <-done:
				fmt.Fprintf(os.Stderr, "\r%d / %d checked\n", checked.Load(), N)
				return
			case <-time.After(250 * time.Millisecond):
				fmt.Fprintf(os.Stderr, "\r%d / %d checked", checked.Load(), N)
			}
		}
	}()

	var wg sync.WaitGroup
	wg.Add(workers)
	for w := range workers {
		go func() {
			defer wg.Done()
			for n := w + 1; n <= N; n += workers {
				pred := predicted(n)
				if pred < 3 {
					checked.Add(1)
					continue
				}
				for i, q := range primes {
					if q <= int(pred) {
						continue
					}
					if ord2[i] == 0 || ord3[i] == 0 {
						continue
					}
					if n%ord2[i] != 0 || n%ord3[i] != 0 {
						continue
					}
					if verifyPhantom(n, q, int(pred), primes) {
						killer := firstKiller(n, q, int(pred), primes)
						fmt.Fprintf(outFile, "n=%d predicted=%d phantom=%d q-1=%d gcd(n,q-1)=%d killer=%d\n",
							n, pred, q, q-1, gcd(n, q-1), killer)
						found.Add(1)
					}
				}
				checked.Add(1)
			}
		}()
	}
	wg.Wait()
	close(done)

	fmt.Printf("checked %d values, found %d counterexamples\n", checked.Load(), found.Load())
}

func verifyPhantom(n, q, pred int, primes []int) bool {
	for _, k := range primes {
		if k > pred || k >= q {
			break
		}
		if powmod(k, n, q) != 1 {
			return false
		}
	}
	return true
}

func firstKiller(n, q, pred int, primes []int) int {
	for _, k := range primes {
		if k >= q {
			return q
		}
		if k <= pred {
			continue
		}
		if powmod(k, n, q) != 1 {
			return k
		}
	}
	return q
}

func gcd(a, b int) int {
	for b != 0 {
		a, b = b, a%b
	}
	return a
}

func buildOrderTable(B int) (primes []int, ord2, ord3 []int) {
	s := sieve(B)
	for i := 2; i < B; i++ {
		if s[i] {
			primes = append(primes, i)
		}
	}
	ord2 = make([]int, len(primes))
	ord3 = make([]int, len(primes))
	workers := runtime.GOMAXPROCS(0)
	var wg sync.WaitGroup
	wg.Add(workers)
	for w := range workers {
		go func() {
			defer wg.Done()
			for i := w; i < len(primes); i += workers {
				ord2[i] = mulOrder(2, primes[i])
				ord3[i] = mulOrder(3, primes[i])
			}
		}()
	}
	wg.Wait()
	return
}

func mulOrder(a, p int) int {
	if p <= 1 || a%p == 0 {
		return 0
	}
	factors := factorize(p - 1)
	ord := p - 1
	for _, f := range factors {
		for ord%f == 0 && powmod(a, ord/f, p) == 1 {
			ord /= f
		}
	}
	return ord
}

func factorize(n int) []int {
	var factors []int
	for d := 2; d*d <= n; d++ {
		if n%d == 0 {
			factors = append(factors, d)
			for n%d == 0 {
				n /= d
			}
		}
	}
	if n > 1 {
		factors = append(factors, n)
	}
	return factors
}

func powmod(base, exp, mod int) int {
	result := 1
	base %= mod
	for exp > 0 {
		if exp%2 == 1 {
			result = result * base % mod
		}
		exp /= 2
		base = base * base % mod
	}
	return result
}

func predicted(n int) int64 {
	best := int64(2)
	for d := 1; d*d <= n; d++ {
		if n%d != 0 {
			continue
		}
		if isPrimeSmall(d+1) && int64(d+1) > best {
			best = int64(d + 1)
		}
		d2 := n / d
		if isPrimeSmall(d2+1) && int64(d2+1) > best {
			best = int64(d2 + 1)
		}
	}
	return best
}

func isPrimeSmall(n int) bool {
	if n < 2 {
		return false
	}
	if n < 4 {
		return true
	}
	if n%2 == 0 || n%3 == 0 {
		return false
	}
	for i := 5; i*i <= n; i += 6 {
		if n%i == 0 || n%(i+2) == 0 {
			return false
		}
	}
	return true
}
