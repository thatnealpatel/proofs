package main

import (
	"fmt"
	"math/big"
	"os"
	"strconv"
)

func runConvergence(args []string) {
	N := 1000
	if len(args) > 0 {
		var err error
		N, err = strconv.Atoi(args[0])
		if err != nil {
			fmt.Fprintf(os.Stderr, "invalid N: %v\n", err)
			os.Exit(1)
		}
	}

	// A000670 (Fubini numbers): coefficients of the conjectured expansion
	// a(n) ~ (2^(n+1)/n) * Sum_{k>=0} fubini[k] / n^k
	fubini := [...]int64{1, 1, 3, 13, 75, 541, 4683}
	maxOrder := len(fubini) - 1

	bs := computeB(N)

	step := max(N/10, 1)

	fmt.Printf("%8s", "n")
	for m := range maxOrder {
		fmt.Printf("  %10s", fmt.Sprintf("->%d", fubini[m+1]))
	}
	fmt.Println()

	one := big.NewInt(1)
	a := new(big.Int)

	for k := 1; k <= N; k++ {
		a.Add(a, bs[k])
		a.Sub(a, one)

		if k%step != 0 {
			continue
		}

		// ratio = a(k) * k / 2^(k+1)
		// precision must exceed bit-length of a(k) for exact conversion
		prec := uint(k + 128)

		an := new(big.Float).SetPrec(prec).SetInt(a)
		nf := new(big.Float).SetPrec(prec).SetInt64(int64(k))
		pow2 := new(big.Float).SetPrec(prec).SetInt(new(big.Int).Lsh(big.NewInt(1), uint(k+1)))

		ratio := new(big.Float).SetPrec(prec).Mul(an, nf)
		ratio.Quo(ratio, pow2)

		fmt.Printf("%8d", k)

		rem := new(big.Float).SetPrec(prec).Copy(ratio)
		nPow := new(big.Float).SetPrec(prec).SetInt64(1) // n^0

		for m := range maxOrder {
			correction := new(big.Float).SetPrec(prec).SetInt64(fubini[m])
			correction.Quo(correction, nPow)
			rem.Sub(rem, correction)

			nPow.Mul(nPow, nf) // n^(m+1)

			display := new(big.Float).SetPrec(prec).Mul(rem, nPow)
			val, _ := display.Float64()
			fmt.Printf("  %10.4f", val)
		}
		fmt.Println()
	}
}
