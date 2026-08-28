package main

import (
	"context"
	"math/rand"
)

func buildFamilyB() []uint {
	sets := [][]int{
		{0, 1, 2, 15}, {0, 1, 3, 15}, {0, 1, 4, 5}, {0, 4, 14, 16}, {0, 4, 14, 18},
		{0, 8, 9, 15}, {0, 8, 10, 15}, {1, 2, 3, 4}, {1, 2, 3, 7}, {1, 4, 5, 8},
		{1, 5, 6, 12}, {2, 9, 11, 12}, {2, 3, 12, 13}, {2, 3, 6, 12}, {3, 11, 12, 17},
		{3, 11, 14, 15}, {4, 14, 15, 19},
	}
	family := make([]uint, 0, len(sets))
	for _, set := range sets {
		family = append(family, setToMask(set))
	}
	return sortFamily(family)
}

func allKSets(n, k int) []uint {
	var result []uint
	var generate func(int, int, uint)
	generate = func(start, chosen int, current uint) {
		if chosen == k {
			result = append(result, current)
			return
		}
		for i := start; i < n; i++ {
			generate(i+1, chosen+1, current|(uint(1)<<uint(i)))
		}
	}
	generate(0, 0, 0)
	return result
}

func buildStar(k, n int) []uint {
	var family []uint
	for _, set := range allKSets(n, k) {
		if set&1 != 0 {
			family = append(family, set)
		}
	}
	return sortFamily(family)
}

func buildCoSingleton(k, n int) []uint {
	top := uint(1) << uint(n-1)
	var family []uint
	for _, set := range allKSets(n, k) {
		if set&top == 0 {
			family = append(family, set)
		}
	}
	return sortFamily(family)
}

func buildRandom(k, n, count int, rng *rand.Rand) []uint {
	pool := allKSets(n, k)
	count = min(count, len(pool))
	rng.Shuffle(len(pool), func(i, j int) { pool[i], pool[j] = pool[j], pool[i] })
	return sortFamily(pool[:count])
}

func buildHighSpread(k, n, count int, rng *rand.Rand, threshold float64) ([]uint, float64) {
	pool := allKSets(n, k)
	count = min(count, len(pool))
	const maxTries = 4000
	var best []uint
	bestR := 0.0
	for try := 0; try < maxTries; try++ {
		rng.Shuffle(len(pool), func(i, j int) { pool[i], pool[j] = pool[j], pool[i] })
		family := sortFamily(append([]uint(nil), pool[:count]...))
		spread := computeSpread(family)
		if spread.RStar > bestR {
			bestR = spread.RStar
			best = family
		}
		if spread.RStar >= threshold {
			return family, spread.RStar
		}
	}
	return best, bestR
}

func searchHighRatioLowTau(ctx context.Context, k, n int) [][]uint {
	ksets := allKSets(n, k)
	if len(ksets) > 22 {
		return nil
	}
	total := (uint64(1) << uint(len(ksets))) - 1
	var best []candidate
	for mask := uint64(1); mask <= total; mask++ {
		if mask&0x3FFFF == 0 && ctx.Err() != nil {
			break
		}
		if popcount64(mask) > 14 {
			continue
		}
		var family []uint
		for i, set := range ksets {
			if mask&(uint64(1)<<uint(i)) != 0 {
				family = append(family, set)
			}
		}
		if len(family) < 3 {
			continue
		}
		tauF, _ := maxSunflowerBudgeted(family)
		if tauF < 1 || tauF > 2 {
			continue
		}
		shifted := shiftOneSweep(family, n)
		tauShifted, _ := maxSunflowerBudgeted(shifted)
		ratio := float64(tauShifted) / float64(tauF)
		if ratio >= 3 {
			best = append(best, candidate{append([]uint(nil), family...), ratio})
		}
	}
	sortCandidates(best)
	var result [][]uint
	seenRatio := map[float64]bool{}
	for _, candidate := range best {
		if seenRatio[candidate.ratio] {
			continue
		}
		seenRatio[candidate.ratio] = true
		result = append(result, sortFamily(candidate.family))
		if len(result) >= 3 {
			break
		}
	}
	return result
}

type candidate struct {
	family []uint
	ratio  float64
}

func sortCandidates(candidates []candidate) {
	for i := 1; i < len(candidates); i++ {
		for j := i; j > 0 && candidates[j].ratio > candidates[j-1].ratio; j-- {
			candidates[j], candidates[j-1] = candidates[j-1], candidates[j]
		}
	}
}

func popcount64(value uint64) int {
	count := 0
	for ; value != 0; value &= value - 1 {
		count++
	}
	return count
}

func nChooseK(n, k int) int {
	if k < 0 || k > n {
		return 0
	}
	if k > n-k {
		k = n - k
	}
	result := 1
	for i := 0; i < k; i++ {
		result = result * (n - i) / (i + 1)
	}
	return result
}
