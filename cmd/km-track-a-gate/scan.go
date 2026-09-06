package main

import (
	"fmt"
	"slices"

	"patel.codes/proofs/internal/ring"
	"patel.codes/proofs/internal/tensor"
)

type kmOrientation struct {
	BMode int `json:"b_mode"`
	CMode int `json:"c_mode"`
	AMode int `json:"a_mode"`
}

type kmGuardCount struct {
	Guard string `json:"guard"`
	Count uint64 `json:"count"`
}

type kmArityScan struct {
	Orientation       kmOrientation  `json:"orientation"`
	Arity             int            `json:"arity"`
	Enumerated        uint64         `json:"enumerated"`
	Accepted          uint64         `json:"accepted"`
	Rejected          uint64         `json:"rejected"`
	GuardCounts       []kmGuardCount `json:"guard_counts"`
	AcceptedByChanged []uint64       `json:"accepted_by_changed_count"`
}

type kmOrientationIndex struct {
	Orientation      kmOrientation `json:"orientation"`
	FactorClasses    int           `json:"factor_classes"`
	RepeatedClasses  int           `json:"repeated_classes"`
	MaximumClassSize int           `json:"maximum_class_size"`
	IndexedTermCount int           `json:"indexed_term_count"`
}

type kmCandidate struct {
	Orientation    kmOrientation
	PivotSlot      int
	SourceSlots    []int
	ChangedIndices []int
	TargetTerms    []tensor.RankOneTerm
}

type kmScanResult struct {
	Indexes    []kmOrientationIndex
	Scans      []kmArityScan
	Candidates []kmCandidate
}

var kmOrientations = []kmOrientation{
	{BMode: 0, CMode: 1, AMode: 2},
	{BMode: 0, CMode: 2, AMode: 1},
	{BMode: 1, CMode: 0, AMode: 2},
	{BMode: 1, CMode: 2, AMode: 0},
	{BMode: 2, CMode: 0, AMode: 1},
	{BMode: 2, CMode: 1, AMode: 0},
}

var kmGuardNames = []string{
	"b0_not_sum",
	"source_not_injective",
	"output_c_zero",
	"output_not_injective",
	"context_not_disjoint",
}

func scanBinaryKMIndexedData(scheme tensor.Scheme, maximumArity int) (kmScanResult, error) {
	if scheme.Ring() != ring.Z2 {
		return kmScanResult{}, fmt.Errorf("binary KM scan requires ring Z2, got %d", scheme.Ring())
	}
	if maximumArity < 1 {
		return kmScanResult{}, fmt.Errorf("binary KM maximum arity is %d, want at least 1", maximumArity)
	}
	if err := tensor.ValidateNonzeroTerms(scheme); err != nil {
		return kmScanResult{}, fmt.Errorf("binary KM scan nonzero source: %w", err)
	}
	if err := tensor.ValidateDistinctTensors(scheme); err != nil {
		return kmScanResult{}, fmt.Errorf("binary KM scan distinct source: %w", err)
	}

	result := kmScanResult{}
	for _, orientation := range kmOrientations {
		classes := kmFactorClasses(scheme, orientation.AMode)
		index := kmOrientationIndex{
			Orientation:      orientation,
			FactorClasses:    len(classes),
			IndexedTermCount: scheme.TermCount(),
		}
		for _, class := range classes {
			if len(class) > 1 {
				index.RepeatedClasses++
			}
			index.MaximumClassSize = max(index.MaximumClassSize, len(class))
		}
		result.Indexes = append(result.Indexes, index)
		for arity := 1; arity <= maximumArity; arity++ {
			scan := kmArityScan{
				Orientation:       orientation,
				Arity:             arity,
				GuardCounts:       make([]kmGuardCount, len(kmGuardNames)),
				AcceptedByChanged: make([]uint64, arity+1),
			}
			for i, name := range kmGuardNames {
				scan.GuardCounts[i].Guard = name
			}
			var scanErr error
			for _, class := range classes {
				for _, pivot := range class {
					available := make([]int, 0, len(class)-1)
					for _, slot := range class {
						if slot != pivot {
							available = append(available, slot)
						}
					}
					forEachCombination(available, arity, func(sourceSlots []int) {
						if scanErr != nil {
							return
						}
						scan.Enumerated++
						candidate, rejection, err := checkKMCandidate(scheme, orientation, pivot, sourceSlots)
						if err != nil {
							scanErr = err
							return
						}
						if rejection != "" {
							scan.Rejected++
							guardIndex := slices.Index(kmGuardNames, rejection)
							if guardIndex < 0 {
								scanErr = fmt.Errorf("unregistered binary KM rejection %q", rejection)
								return
							}
							scan.GuardCounts[guardIndex].Count++
							return
						}
						scan.Accepted++
						scan.AcceptedByChanged[len(candidate.ChangedIndices)]++
						result.Candidates = append(result.Candidates, candidate)
					})
				}
			}
			if scanErr != nil {
				return kmScanResult{}, scanErr
			}
			result.Scans = append(result.Scans, scan)
		}
	}
	return result, nil
}

func kmFactorClasses(scheme tensor.Scheme, mode int) [][]int {
	indexes := make(map[string]int)
	classes := make([][]int, 0)
	for slot := range scheme.TermCount() {
		key := matrixKey(scheme.Term(slot).Factor(mode))
		index, ok := indexes[key]
		if !ok {
			index = len(classes)
			indexes[key] = index
			classes = append(classes, nil)
		}
		classes[index] = append(classes[index], slot)
	}
	return classes
}

func forEachCombination(values []int, size int, visit func([]int)) {
	if size > len(values) {
		return
	}
	combination := make([]int, size)
	var walk func(int, int)
	walk = func(depth, start int) {
		if depth == size {
			visit(append([]int(nil), combination...))
			return
		}
		for index := start; index <= len(values)-(size-depth); index++ {
			combination[depth] = values[index]
			walk(depth+1, index+1)
		}
	}
	walk(0, 0)
}

func checkKMCandidate(scheme tensor.Scheme, orientation kmOrientation, pivotSlot int, sourceSlots []int) (kmCandidate, string, error) {
	pivot := scheme.Term(pivotSlot)
	pivotB := pivot.Factor(orientation.BMode)
	bSum := make([]int, len(pivotB.Entries()))
	pairs := make(map[string]struct{}, len(sourceSlots))
	for _, slot := range sourceSlots {
		term := scheme.Term(slot)
		for i, entry := range term.Factor(orientation.BMode).Entries() {
			bSum[i] ^= entry
		}
		key := matrixKey(term.Factor(orientation.BMode)) + "\x00" + matrixKey(term.Factor(orientation.CMode))
		if _, found := pairs[key]; found {
			return kmCandidate{}, "source_not_injective", nil
		}
		pairs[key] = struct{}{}
	}
	if !slices.Equal(bSum, pivotB.Entries()) {
		return kmCandidate{}, "b0_not_sum", nil
	}

	support := make(map[int]struct{}, len(sourceSlots)+1)
	support[pivotSlot] = struct{}{}
	for _, slot := range sourceSlots {
		support[slot] = struct{}{}
	}
	targets := make([]tensor.RankOneTerm, len(sourceSlots))
	targetKeys := make(map[string]struct{}, len(sourceSlots))
	changed := make([]int, 0, len(sourceSlots))
	pivotC := pivot.Factor(orientation.CMode)
	for index, slot := range sourceSlots {
		source := scheme.Term(slot)
		outputC, err := addBinaryMatrices(source.Factor(orientation.CMode), pivotC)
		if err != nil {
			return kmCandidate{}, "", err
		}
		if matrixIsZeroPublic(outputC) {
			return kmCandidate{}, "output_c_zero", nil
		}
		factors := source.Factors()
		factors[orientation.CMode] = outputC
		target, err := tensor.NewRankOneTerm(factors[0], factors[1], factors[2])
		if err != nil {
			return kmCandidate{}, "", err
		}
		targets[index] = target
		key := termKeyPublic(target)
		if _, found := targetKeys[key]; found {
			return kmCandidate{}, "output_not_injective", nil
		}
		targetKeys[key] = struct{}{}
		matchesSource := false
		for _, sourceSlot := range sourceSlots {
			if equalTermsPublic(target, scheme.Term(sourceSlot)) {
				matchesSource = true
				break
			}
		}
		if !matchesSource {
			changed = append(changed, index)
		}
		for contextSlot := range scheme.TermCount() {
			if _, local := support[contextSlot]; local {
				continue
			}
			if equalTermsPublic(target, scheme.Term(contextSlot)) {
				return kmCandidate{}, "context_not_disjoint", nil
			}
		}
	}
	return kmCandidate{
		Orientation:    orientation,
		PivotSlot:      pivotSlot,
		SourceSlots:    append([]int(nil), sourceSlots...),
		ChangedIndices: changed,
		TargetTerms:    targets,
	}, "", nil
}

func addBinaryMatrices(first, second tensor.Matrix) (tensor.Matrix, error) {
	if first.Ring() != ring.Z2 || second.Ring() != ring.Z2 {
		return tensor.Matrix{}, fmt.Errorf("matrix addition requires Z2")
	}
	if first.Rows() != second.Rows() || first.Columns() != second.Columns() {
		return tensor.Matrix{}, fmt.Errorf("matrix shapes differ")
	}
	entries := first.Entries()
	secondEntries := second.Entries()
	for i := range entries {
		entries[i] ^= secondEntries[i]
	}
	return tensor.NewMatrix(ring.Z2, first.Rows(), first.Columns(), entries)
}

func matrixIsZeroPublic(matrix tensor.Matrix) bool {
	for _, entry := range matrix.Entries() {
		if entry != 0 {
			return false
		}
	}
	return true
}

func matrixKey(matrix tensor.Matrix) string {
	key := make([]byte, len(matrix.Entries()))
	for i, entry := range matrix.Entries() {
		key[i] = byte(entry)
	}
	return string(key)
}

func termKeyPublic(term tensor.RankOneTerm) string {
	return matrixKey(term.Factor(0)) + "\x00" + matrixKey(term.Factor(1)) + "\x00" + matrixKey(term.Factor(2))
}

func equalTermsPublic(first, second tensor.RankOneTerm) bool {
	for mode := range 3 {
		if !equalMatricesPublic(first.Factor(mode), second.Factor(mode)) {
			return false
		}
	}
	return true
}

func equalMatricesPublic(first, second tensor.Matrix) bool {
	return first.Ring() == second.Ring() && first.Rows() == second.Rows() && first.Columns() == second.Columns() && slices.Equal(first.Entries(), second.Entries())
}
