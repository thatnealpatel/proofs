package main

import (
	"math/bits"
	"sort"
)

const zooSunflowerBudget = 40_000_000

type shiftMode uint8

const (
	shiftSingleSweep shiftMode = iota
	shiftFixedPoint
)

func setToMask(elems []int) uint {
	var m uint
	for _, e := range elems {
		m |= uint(1) << uint(e)
	}
	return m
}

func maskToSet(m uint) []int {
	elems := []int{}
	for b := m; b != 0; b &= b - 1 {
		elems = append(elems, bits.TrailingZeros(b))
	}
	return elems
}

func familyToSets(family []uint) [][]int {
	out := make([][]int, 0, len(family))
	for _, s := range family {
		out = append(out, maskToSet(s))
	}
	return out
}

func sortFamily(family []uint) []uint {
	cp := append([]uint(nil), family...)
	sort.Slice(cp, func(a, b int) bool { return cp[a] < cp[b] })
	return cp
}

func franklShiftSet(i, j int, s uint) uint {
	iBit := uint(1) << uint(i)
	jBit := uint(1) << uint(j)
	if s&iBit == 0 && s&jBit != 0 {
		return (s &^ jBit) | iBit
	}
	return s
}

func franklShift(i, j int, family []uint) ([]uint, bool) {
	fset := make(map[uint]struct{}, len(family))
	for _, s := range family {
		fset[s] = struct{}{}
	}
	out := make(map[uint]struct{}, len(family))
	changed := false
	for _, s := range family {
		shifted := franklShiftSet(i, j, s)
		if _, present := fset[shifted]; present {
			out[s] = struct{}{}
		} else {
			out[shifted] = struct{}{}
			if shifted != s {
				changed = true
			}
		}
	}
	result := make([]uint, 0, len(out))
	for s := range out {
		result = append(result, s)
	}
	return sortFamily(result), changed
}

func shiftOneSweep(family []uint, n int) []uint {
	result, _ := shiftSweeps(family, n, shiftSingleSweep)
	return result
}

func shiftToFixedPoint(family []uint, n int) []uint {
	result, _ := shiftSweeps(family, n, shiftFixedPoint)
	return result
}

func shiftSweeps(family []uint, n int, mode shiftMode) ([]uint, int) {
	cur := sortFamily(family)
	sweeps := 0
	for {
		sweeps++
		changed := false
		for i := 0; i < n; i++ {
			for j := i + 1; j < n; j++ {
				var pairChanged bool
				cur, pairChanged = franklShift(i, j, cur)
				changed = changed || pairChanged
			}
		}
		if mode == shiftSingleSweep || !changed {
			return cur, sweeps
		}
	}
}

func maxSunflowerExact(family []uint) int {
	value, _ := maxSunflower(family, 0)
	return value
}

func maxSunflowerBudgeted(family []uint) (int, bool) {
	return maxSunflower(family, zooSunflowerBudget)
}

func maxSunflowerWithBudget(family []uint, nodeBudget int) (int, bool) {
	if nodeBudget <= 0 {
		return maxSunflower(family, 1)
	}
	return maxSunflower(family, nodeBudget)
}

func maxSunflower(family []uint, nodeBudget int) (int, bool) {
	m := len(family)
	if m <= 1 {
		return m, true
	}
	best := 1
	exact := true
	kernels := map[uint]struct{}{0: {}}
	for i := 0; i < m; i++ {
		kernels[family[i]] = struct{}{}
		for j := i + 1; j < m; j++ {
			kernels[family[i]&family[j]] = struct{}{}
		}
	}
	type kernelPetals struct {
		petals []uint
		upper  int
	}
	groups := make([]kernelPetals, 0, len(kernels))
	for kernel := range kernels {
		petals := make([]uint, 0, m)
		for _, s := range family {
			if s&kernel == kernel {
				if petal := s &^ kernel; petal != 0 {
					petals = append(petals, petal)
				}
			}
		}
		if len(petals) <= 1 {
			continue
		}
		var union uint
		minimumSize := bits.UintSize
		for _, petal := range petals {
			union |= petal
			minimumSize = min(minimumSize, bits.OnesCount(petal))
		}
		upper := min(len(petals), bits.OnesCount(union)/minimumSize)
		groups = append(groups, kernelPetals{petals, upper})
	}
	sort.Slice(groups, func(i, j int) bool { return groups[i].upper > groups[j].upper })
	for _, group := range groups {
		if group.upper <= best {
			continue
		}
		value, complete := maxDisjoint(group.petals, nodeBudget)
		if !complete {
			exact = false
		}
		best = max(best, value)
	}
	return best, exact
}

func maxDisjoint(masks []uint, nodeBudget int) (int, bool) {
	if len(masks) == 0 {
		return 0, true
	}
	ordered := append([]uint(nil), masks...)
	sort.Slice(ordered, func(i, j int) bool {
		return bits.OnesCount(ordered[i]) > bits.OnesCount(ordered[j])
	})
	best := greedyPacking(ordered)
	exact := true
	nodes := 0
	var search func(int, int, uint)
	search = func(index, count int, used uint) {
		nodes++
		if nodeBudget > 0 && nodes > nodeBudget {
			exact = false
			return
		}
		best = max(best, count)
		if index == len(ordered) || count+len(ordered)-index <= best {
			return
		}
		if ordered[index]&used == 0 {
			search(index+1, count+1, used|ordered[index])
		}
		search(index+1, count, used)
	}
	search(0, 0, 0)
	return best, exact
}

func greedyPacking(masks []uint) int {
	var used uint
	count := 0
	for _, mask := range masks {
		if mask&used == 0 {
			used |= mask
			count++
		}
	}
	return count
}
