package tensor

import (
	"fmt"
	"math/big"
	"slices"

	"patel.codes/proofs/internal/ring"
)

type SharedMode int

const (
	SharedFirst SharedMode = iota
	SharedSecond
	SharedThird
)

type SharedFactorAnalysis struct {
	classes []SharedFactorClass
}

type SharedFactorClass struct {
	mode              SharedMode
	slots             []int
	complementaryRank int
	defect            int
}

func AnalyzeSharedFactors(scheme Scheme) (SharedFactorAnalysis, error) {
	if err := scheme.validateStructure(); err != nil {
		return SharedFactorAnalysis{}, fmt.Errorf("shared-factor analysis source scheme: %w", err)
	}
	if scheme.ring != ring.Z2 {
		return SharedFactorAnalysis{}, fmt.Errorf("shared-factor analysis requires ring Z2, got %d", scheme.ring)
	}

	classes := make([]SharedFactorClass, 0)
	for mode := SharedFirst; mode <= SharedThird; mode++ {
		classIndexes := make(map[string]int)
		modeClasses := make([]SharedFactorClass, 0)
		for slot, term := range scheme.terms {
			factor := term.factors[int(mode)]
			if matrixIsZero(factor) {
				continue
			}
			key := factorKey(factor)
			index, ok := classIndexes[key]
			if !ok {
				index = len(modeClasses)
				classIndexes[key] = index
				modeClasses = append(modeClasses, SharedFactorClass{mode: mode})
			}
			modeClasses[index].slots = append(modeClasses[index].slots, slot)
		}
		for _, class := range modeClasses {
			if len(class.slots) < 2 {
				continue
			}
			leftFactors, _ := sharedComplementaryFactorization(scheme, class.mode, class.slots)
			class.complementaryRank = len(leftFactors)
			class.defect = len(class.slots) - class.complementaryRank
			if class.defect < 0 {
				return SharedFactorAnalysis{}, fmt.Errorf("shared-factor class at mode %d and slot %d has rank %d above size %d", class.mode, class.slots[0], class.complementaryRank, len(class.slots))
			}
			if class.defect > 0 {
				replacement, err := NewSharedFactorReduction(scheme, class.mode, class.slots)
				if err != nil {
					return SharedFactorAnalysis{}, fmt.Errorf("validate shared-factor class at mode %d and slot %d: %w", class.mode, class.slots[0], err)
				}
				if len(replacement.insertedTerms) != class.complementaryRank {
					return SharedFactorAnalysis{}, fmt.Errorf("validate shared-factor class at mode %d and slot %d: replacement rank is %d, want %d", class.mode, class.slots[0], len(replacement.insertedTerms), class.complementaryRank)
				}
			}
			classes = append(classes, class)
		}
	}
	return SharedFactorAnalysis{classes: classes}, nil
}

func (a SharedFactorAnalysis) Classes() []SharedFactorClass {
	classes := make([]SharedFactorClass, len(a.classes))
	for i, class := range a.classes {
		classes[i] = class.clone()
	}
	return classes
}

func (c SharedFactorClass) Mode() SharedMode {
	return c.mode
}

func (c SharedFactorClass) Slots() []int {
	return append([]int(nil), c.slots...)
}

func (c SharedFactorClass) ComplementaryRank() int {
	return c.complementaryRank
}

func (c SharedFactorClass) Defect() int {
	return c.defect
}

func (c SharedFactorClass) ReductionStep() (SharedFactorReductionStep, bool) {
	if c.defect <= 0 {
		return SharedFactorReductionStep{}, false
	}
	return SharedFactorReductionStep{Mode: c.mode, Slots: append([]int(nil), c.slots...)}, true
}

func (c SharedFactorClass) clone() SharedFactorClass {
	c.slots = append([]int(nil), c.slots...)
	return c
}

func factorKey(factor Matrix) string {
	key := make([]byte, len(factor.entries))
	for i, entry := range factor.entries {
		key[i] = byte(entry)
	}
	return string(key)
}

func NewSharedFactorReduction(scheme Scheme, mode SharedMode, slots []int) (Replacement, error) {
	if err := scheme.validateStructure(); err != nil {
		return Replacement{}, fmt.Errorf("shared-factor source scheme: %w", err)
	}
	if mode < SharedFirst || mode > SharedThird {
		return Replacement{}, fmt.Errorf("shared-factor mode is unsupported: %d", mode)
	}
	if scheme.ring != ring.Z2 {
		return Replacement{}, fmt.Errorf("shared-factor reduction requires ring Z2, got %d", scheme.ring)
	}
	if len(slots) < 2 {
		return Replacement{}, fmt.Errorf("shared-factor reduction requires at least two slots, got %d", len(slots))
	}

	removed := append([]int(nil), slots...)
	slices.Sort(removed)
	for i, slot := range removed {
		if slot < 0 || slot >= len(scheme.terms) {
			return Replacement{}, fmt.Errorf("shared-factor slot is out of range: %d for %d terms", slot, len(scheme.terms))
		}
		if i > 0 && slot == removed[i-1] {
			return Replacement{}, fmt.Errorf("shared-factor slots contain duplicate %d", slot)
		}
	}

	sharedMode := int(mode)
	leftMode, rightMode := sharedComplementaryModes(mode)
	shared := scheme.terms[removed[0]].factors[sharedMode]
	if matrixIsZero(shared) {
		return Replacement{}, fmt.Errorf("shared factor at mode %d is zero", mode)
	}
	for _, slot := range removed[1:] {
		if !slices.Equal(shared.entries, scheme.terms[slot].factors[sharedMode].entries) {
			return Replacement{}, fmt.Errorf("selected terms do not have equal factors at mode %d", mode)
		}
	}

	leftFactors, rightFactors := sharedComplementaryFactorization(scheme, mode, removed)
	if len(leftFactors) >= len(removed) {
		return Replacement{}, fmt.Errorf("shared-factor matrix is not rank deficient: rank %d for %d slots", len(leftFactors), len(removed))
	}

	inserted := make([]RankOneTerm, len(leftFactors))
	leftShape := scheme.terms[removed[0]].factors[leftMode]
	rightShape := scheme.terms[removed[0]].factors[rightMode]
	for i := range inserted {
		left, err := NewMatrix(ring.Z2, leftShape.rows, leftShape.columns, leftFactors[i])
		if err != nil {
			return Replacement{}, fmt.Errorf("construct shared-factor left matrix %d: %w", i, err)
		}
		right, err := NewMatrix(ring.Z2, rightShape.rows, rightShape.columns, rightFactors[i])
		if err != nil {
			return Replacement{}, fmt.Errorf("construct shared-factor right matrix %d: %w", i, err)
		}
		factors := [3]Matrix{}
		factors[sharedMode] = shared
		factors[leftMode] = left
		factors[rightMode] = right
		inserted[i], err = NewRankOneTerm(factors[0], factors[1], factors[2])
		if err != nil {
			return Replacement{}, fmt.Errorf("construct shared-factor term %d: %w", i, err)
		}
	}

	replacement, err := NewReplacement(removed, inserted)
	if err != nil {
		return Replacement{}, fmt.Errorf("construct shared-factor replacement: %w", err)
	}
	if err := ValidateReplacement(scheme, replacement); err != nil {
		return Replacement{}, fmt.Errorf("validate shared-factor replacement: %w", err)
	}
	return replacement, nil
}

func matrixIsZero(matrix Matrix) bool {
	for _, entry := range matrix.entries {
		if entry != 0 {
			return false
		}
	}
	return true
}

func sharedComplementaryModes(mode SharedMode) (int, int) {
	modes := [3][2]int{{1, 2}, {0, 2}, {0, 1}}
	return modes[int(mode)][0], modes[int(mode)][1]
}

func sharedComplementaryFactorization(scheme Scheme, mode SharedMode, slots []int) ([][]int, [][]int) {
	leftMode, rightMode := sharedComplementaryModes(mode)
	rows := sharedFactorRows(scheme, slots, leftMode, rightMode)
	rightWidth := len(scheme.terms[slots[0]].factors[rightMode].entries)
	return factorGF2Rows(rows, rightWidth)
}

func sharedFactorRows(scheme Scheme, slots []int, leftMode, rightMode int) []big.Int {
	leftSize := len(scheme.terms[slots[0]].factors[leftMode].entries)
	rows := make([]big.Int, leftSize)
	for _, slot := range slots {
		term := scheme.terms[slot]
		right := entriesBitset(term.factors[rightMode].entries)
		for row, entry := range term.factors[leftMode].entries {
			if entry != 0 {
				rows[row].Xor(&rows[row], right)
			}
		}
	}
	return rows
}

func entriesBitset(entries []int) *big.Int {
	bits := new(big.Int)
	for i, entry := range entries {
		if entry != 0 {
			bits.SetBit(bits, i, 1)
		}
	}
	return bits
}

type gf2Pivot struct {
	value        *big.Int
	coefficients *big.Int
}

func factorGF2Rows(rows []big.Int, width int) ([][]int, [][]int) {
	selected := make([]*big.Int, 0)
	independent := make(map[int]*big.Int)
	for i := range rows {
		value := new(big.Int).Set(&rows[i])
		reduced := new(big.Int).Set(value)
		for reduced.Sign() != 0 {
			pivot := reduced.BitLen() - 1
			basis, ok := independent[pivot]
			if ok {
				reduced.Xor(reduced, basis)
				continue
			}
			independent[pivot] = new(big.Int).Set(reduced)
			selected = append(selected, value)
			break
		}
	}

	pivots := make(map[int]gf2Pivot)
	for i, row := range selected {
		value := new(big.Int).Set(row)
		coefficients := new(big.Int).SetBit(new(big.Int), i, 1)
		for value.Sign() != 0 {
			pivot := value.BitLen() - 1
			basis, ok := pivots[pivot]
			if ok {
				value.Xor(value, basis.value)
				coefficients.Xor(coefficients, basis.coefficients)
				continue
			}
			pivots[pivot] = gf2Pivot{
				value:        new(big.Int).Set(value),
				coefficients: new(big.Int).Set(coefficients),
			}
			break
		}
	}

	rowCoefficients := make([]*big.Int, len(rows))
	for i := range rows {
		value := new(big.Int).Set(&rows[i])
		coefficients := new(big.Int)
		for value.Sign() != 0 {
			pivot := value.BitLen() - 1
			basis := pivots[pivot]
			value.Xor(value, basis.value)
			coefficients.Xor(coefficients, basis.coefficients)
		}
		rowCoefficients[i] = coefficients
	}

	leftFactors := make([][]int, len(selected))
	rightFactors := make([][]int, len(selected))
	for basis := range selected {
		leftFactors[basis] = make([]int, len(rows))
		for row, coefficients := range rowCoefficients {
			leftFactors[basis][row] = int(coefficients.Bit(basis))
		}
		rightFactors[basis] = make([]int, width)
		for column := range width {
			rightFactors[basis][column] = int(selected[basis].Bit(column))
		}
	}
	return leftFactors, rightFactors
}
