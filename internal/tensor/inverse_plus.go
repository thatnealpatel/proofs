package tensor

import (
	"fmt"
	"slices"

	"patel.codes/proofs/internal/ring"
)

type PlusVariant int

type inversePlusMatrixSum struct {
	target *Matrix
	first  Matrix
	second Matrix
}

const (
	PlusVariantSecondThirdFirst PlusVariant = 0
	PlusVariantThirdFirstSecond PlusVariant = 1
	PlusVariantFirstSecondThird PlusVariant = 2
)

func NewInversePlusReplacement(scheme Scheme, outputSlots [3]int, variant PlusVariant) (Replacement, error) {
	if err := scheme.validateStructure(); err != nil {
		return Replacement{}, fmt.Errorf("inverse Plus source scheme: %w", err)
	}
	if scheme.ring != ring.Z2 {
		return Replacement{}, fmt.Errorf("inverse Plus replacement requires ring Z2, got %d", scheme.ring)
	}
	if variant != PlusVariantSecondThirdFirst && variant != PlusVariantThirdFirstSecond && variant != PlusVariantFirstSecondThird {
		return Replacement{}, fmt.Errorf("inverse Plus variant is unsupported: %d", variant)
	}
	for output, slot := range outputSlots {
		if slot < 0 || slot >= len(scheme.terms) {
			return Replacement{}, fmt.Errorf("inverse Plus output slot %d is out of range: %d for %d terms", output, slot, len(scheme.terms))
		}
		for earlier := range output {
			if slot == outputSlots[earlier] {
				return Replacement{}, fmt.Errorf("inverse Plus output slots must be distinct, got %d at positions %d and %d", slot, earlier, output)
			}
		}
	}

	outputs := [3]RankOneTerm{}
	for output, slot := range outputSlots {
		outputs[output] = scheme.terms[slot]
	}
	recovered, err := inversePlusSources(outputs, variant)
	if err != nil {
		return Replacement{}, err
	}
	for mode := range 3 {
		if equalMatrices(recovered[0].factors[mode], recovered[1].factors[mode]) {
			return Replacement{}, fmt.Errorf("inverse Plus recovered source matrices must differ at factor %d", mode)
		}
	}

	replayed, err := inversePlusOutputs(recovered, variant)
	if err != nil {
		return Replacement{}, fmt.Errorf("replay inverse Plus variant %d: %w", variant, err)
	}
	for output := range outputs {
		for mode := range 3 {
			if !equalMatrices(replayed[output].factors[mode], outputs[output].factors[mode]) {
				return Replacement{}, fmt.Errorf("inverse Plus output replay differs at output %d factor %d", output, mode)
			}
		}
	}

	removed := append([]int(nil), outputSlots[:]...)
	slices.Sort(removed)
	replacement, err := NewReplacement(removed, []RankOneTerm{recovered[0], recovered[1]})
	if err != nil {
		return Replacement{}, fmt.Errorf("construct inverse Plus replacement: %w", err)
	}
	if err := ValidateReplacement(scheme, replacement); err != nil {
		return Replacement{}, fmt.Errorf("validate inverse Plus replacement: %w", err)
	}
	return replacement, nil
}

func inversePlusSources(outputs [3]RankOneTerm, variant PlusVariant) ([2]RankOneTerm, error) {
	x := outputs[0].factors
	y := outputs[1].factors
	z := outputs[2].factors
	sources := [2][3]Matrix{}
	sums := [3]inversePlusMatrixSum{}
	switch variant {
	case PlusVariantSecondThirdFirst:
		sources[0] = [3]Matrix{x[0], {}, x[2]}
		sources[1] = [3]Matrix{{}, y[1], y[2]}
		sums[0] = inversePlusMatrixSum{&sources[0][1], x[1], y[1]}
		sums[1] = inversePlusMatrixSum{&sources[1][0], y[0], x[0]}
	case PlusVariantThirdFirstSecond:
		sources[0] = [3]Matrix{x[0], x[1], {}}
		sources[1] = [3]Matrix{{}, {}, z[2]}
		sums[0] = inversePlusMatrixSum{&sources[0][2], x[2], z[2]}
		sums[1] = inversePlusMatrixSum{&sources[1][0], z[0], x[0]}
		sums[2] = inversePlusMatrixSum{&sources[1][1], y[1], x[1]}
	case PlusVariantFirstSecondThird:
		sources[0] = [3]Matrix{{}, x[1], x[2]}
		sources[1] = [3]Matrix{z[0], {}, {}}
		sums[0] = inversePlusMatrixSum{&sources[0][0], x[0], z[0]}
		sums[1] = inversePlusMatrixSum{&sources[1][1], z[1], x[1]}
		sums[2] = inversePlusMatrixSum{&sources[1][2], y[2], z[2]}
	default:
		return [2]RankOneTerm{}, fmt.Errorf("inverse Plus variant is unsupported: %d", variant)
	}
	for _, sum := range sums {
		if sum.target == nil {
			continue
		}
		matrix, err := addMatrices(sum.first, sum.second)
		if err != nil {
			return [2]RankOneTerm{}, fmt.Errorf("recover inverse Plus source matrix: %w", err)
		}
		*sum.target = matrix
	}

	recovered := [2]RankOneTerm{}
	for source := range recovered {
		term, err := NewRankOneTerm(sources[source][0], sources[source][1], sources[source][2])
		if err != nil {
			return [2]RankOneTerm{}, fmt.Errorf("construct inverse Plus recovered source %d: %w", source, err)
		}
		recovered[source] = term
	}
	return recovered, nil
}

func inversePlusOutputs(sources [2]RankOneTerm, variant PlusVariant) ([3]RankOneTerm, error) {
	first := sources[0].factors
	second := sources[1].factors
	sums := [3]Matrix{}
	for mode := range 3 {
		sum, err := addMatrices(first[mode], second[mode])
		if err != nil {
			return [3]RankOneTerm{}, fmt.Errorf("add source factors at mode %d: %w", mode, err)
		}
		sums[mode] = sum
	}

	factors := [3][3]Matrix{}
	switch variant {
	case PlusVariantSecondThirdFirst:
		factors[0] = [3]Matrix{first[0], sums[1], first[2]}
		factors[1] = [3]Matrix{sums[0], second[1], second[2]}
		factors[2] = [3]Matrix{first[0], second[1], sums[2]}
	case PlusVariantThirdFirstSecond:
		factors[0] = [3]Matrix{first[0], first[1], sums[2]}
		factors[1] = [3]Matrix{second[0], sums[1], second[2]}
		factors[2] = [3]Matrix{sums[0], first[1], second[2]}
	case PlusVariantFirstSecondThird:
		factors[0] = [3]Matrix{sums[0], first[1], first[2]}
		factors[1] = [3]Matrix{second[0], second[1], sums[2]}
		factors[2] = [3]Matrix{second[0], sums[1], first[2]}
	default:
		return [3]RankOneTerm{}, fmt.Errorf("inverse Plus variant is unsupported: %d", variant)
	}

	outputs := [3]RankOneTerm{}
	for output := range outputs {
		term, err := NewRankOneTerm(factors[output][0], factors[output][1], factors[output][2])
		if err != nil {
			return [3]RankOneTerm{}, fmt.Errorf("construct inverse Plus replay output %d: %w", output, err)
		}
		outputs[output] = term
	}
	return outputs, nil
}
