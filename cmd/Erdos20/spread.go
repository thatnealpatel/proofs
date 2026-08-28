package main

import (
	"math"
	"math/big"
)

type spreadResult struct {
	RStar    float64 `json:"r_star"`
	WitnessZ []int   `json:"witness_z"`
	FZcard   int     `json:"witness_fz"`
	Fcard    int     `json:"witness_total"`
}

func computeSpread(family []uint) spreadResult {
	familySize := len(family)
	if familySize == 0 {
		return spreadResult{RStar: math.Inf(1)}
	}
	candidates := make(map[uint]struct{})
	for _, member := range family {
		for subset := member; subset != 0; subset = (subset - 1) & member {
			candidates[subset] = struct{}{}
		}
	}

	total := big.NewInt(int64(familySize))
	var bestZ uint
	var bestCount *big.Int
	bestSize := 0
	haveBest := false
	left := new(big.Int)
	right := new(big.Int)
	temporary := new(big.Int)
	for z := range candidates {
		count := 0
		for _, member := range family {
			if member&z == z {
				count++
			}
		}
		zSize := bitsOnesCount(z)
		candidateCount := big.NewInt(int64(count))
		if !haveBest {
			bestZ, bestCount, bestSize, haveBest = z, candidateCount, zSize, true
			continue
		}
		left.Exp(total, big.NewInt(int64(bestSize)), nil)
		temporary.Exp(bestCount, big.NewInt(int64(zSize)), nil)
		left.Mul(left, temporary)
		right.Exp(total, big.NewInt(int64(zSize)), nil)
		temporary.Exp(candidateCount, big.NewInt(int64(bestSize)), nil)
		right.Mul(right, temporary)
		if left.Cmp(right) < 0 {
			bestZ, bestCount, bestSize = z, candidateCount, zSize
		}
	}
	if !haveBest {
		return spreadResult{RStar: math.Inf(1)}
	}
	return spreadResult{
		RStar:    math.Pow(float64(familySize)/float64(bestCount.Int64()), 1/float64(bestSize)),
		WitnessZ: maskToSet(bestZ),
		FZcard:   int(bestCount.Int64()),
		Fcard:    familySize,
	}
}

func bitsOnesCount(value uint) int {
	count := 0
	for ; value != 0; value &= value - 1 {
		count++
	}
	return count
}
