package tensor

import (
	"fmt"
	"slices"
)

func NewOrdinaryFlipReplacement(
	scheme Scheme,
	mode SharedMode,
	firstSlot, secondSlot, coefficient int,
) (Replacement, error) {
	if err := scheme.validateStructure(); err != nil {
		return Replacement{}, fmt.Errorf("ordinary flip source scheme: %w", err)
	}
	if mode < SharedFirst || mode > SharedThird {
		return Replacement{}, fmt.Errorf("ordinary flip mode is unsupported: %d", mode)
	}
	if firstSlot < 0 || firstSlot >= len(scheme.terms) {
		return Replacement{}, fmt.Errorf("ordinary flip first slot is out of range: %d for %d terms", firstSlot, len(scheme.terms))
	}
	if secondSlot < 0 || secondSlot >= len(scheme.terms) {
		return Replacement{}, fmt.Errorf("ordinary flip second slot is out of range: %d for %d terms", secondSlot, len(scheme.terms))
	}
	if firstSlot == secondSlot {
		return Replacement{}, fmt.Errorf("ordinary flip source slots must be distinct, got %d twice", firstSlot)
	}

	coefficient = scheme.ring.Normalize(coefficient)
	if coefficient == 0 {
		return Replacement{}, fmt.Errorf("ordinary flip coefficient is zero in ring %d", scheme.ring)
	}

	sharedMode := int(mode)
	first := scheme.terms[firstSlot]
	second := scheme.terms[secondSlot]
	shared := first.factors[sharedMode]
	if matrixIsZero(shared) {
		return Replacement{}, fmt.Errorf("ordinary flip shared matrix at mode %d is zero", mode)
	}
	if !equalMatrices(shared, second.factors[sharedMode]) {
		return Replacement{}, fmt.Errorf("ordinary flip source matrices are not literally equal at mode %d", mode)
	}

	complementaryModes := [3][2]int{{1, 2}, {0, 2}, {0, 1}}
	lowerMode := complementaryModes[sharedMode][0]
	higherMode := complementaryModes[sharedMode][1]
	firstFactors := first.factors
	secondFactors := second.factors
	var err error
	firstFactors[lowerMode], err = addScaledMatrix(
		firstFactors[lowerMode],
		coefficient,
		secondFactors[lowerMode],
	)
	if err != nil {
		return Replacement{}, fmt.Errorf("ordinary flip first lower complement: %w", err)
	}
	negativeCoefficient := scheme.ring.Sub(0, coefficient)
	secondFactors[higherMode], err = addScaledMatrix(
		secondFactors[higherMode],
		negativeCoefficient,
		firstFactors[higherMode],
	)
	if err != nil {
		return Replacement{}, fmt.Errorf("ordinary flip second higher complement: %w", err)
	}

	inserted := make([]RankOneTerm, 2)
	inserted[0], err = NewRankOneTerm(firstFactors[0], firstFactors[1], firstFactors[2])
	if err != nil {
		return Replacement{}, fmt.Errorf("construct ordinary flip first term: %w", err)
	}
	inserted[1], err = NewRankOneTerm(secondFactors[0], secondFactors[1], secondFactors[2])
	if err != nil {
		return Replacement{}, fmt.Errorf("construct ordinary flip second term: %w", err)
	}

	removed := []int{firstSlot, secondSlot}
	slices.Sort(removed)
	replacement, err := NewReplacement(removed, inserted)
	if err != nil {
		return Replacement{}, fmt.Errorf("construct ordinary flip replacement: %w", err)
	}
	if err := ValidateReplacement(scheme, replacement); err != nil {
		return Replacement{}, fmt.Errorf("validate ordinary flip replacement: %w", err)
	}
	return replacement, nil
}

func equalMatrices(first, second Matrix) bool {
	return first.ring == second.ring &&
		first.rows == second.rows &&
		first.columns == second.columns &&
		slices.Equal(first.entries, second.entries)
}

func addScaledMatrix(base Matrix, coefficient int, addend Matrix) (Matrix, error) {
	if base.ring != addend.ring {
		return Matrix{}, fmt.Errorf("matrix rings differ: %d and %d", base.ring, addend.ring)
	}
	if base.rows != addend.rows || base.columns != addend.columns {
		return Matrix{}, fmt.Errorf(
			"matrix dimensions differ: %dx%d and %dx%d",
			base.rows,
			base.columns,
			addend.rows,
			addend.columns,
		)
	}
	entries := make([]int, len(base.entries))
	for i := range entries {
		entries[i] = base.ring.Add(base.entries[i], base.ring.Mul(coefficient, addend.entries[i]))
	}
	return NewMatrix(base.ring, base.rows, base.columns, entries)
}
