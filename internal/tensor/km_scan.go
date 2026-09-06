package tensor

import (
	"fmt"
	"slices"

	"patel.codes/proofs/internal/ring"
)

type KMOrientation struct {
	BMode int `json:"b_mode"`
	CMode int `json:"c_mode"`
	AMode int `json:"a_mode"`
}

type KMGuardCount struct {
	Guard string `json:"guard"`
	Count uint64 `json:"count"`
}

type KMArityScan struct {
	Orientation       KMOrientation  `json:"orientation"`
	Arity             int            `json:"arity"`
	Enumerated        uint64         `json:"enumerated"`
	Accepted          uint64         `json:"accepted"`
	Rejected          uint64         `json:"rejected"`
	GuardCounts       []KMGuardCount `json:"guard_counts"`
	AcceptedByChanged []uint64       `json:"accepted_by_changed_count"`
}

type KMOrientationIndex struct {
	Orientation      KMOrientation `json:"orientation"`
	FactorClasses    int           `json:"factor_classes"`
	RepeatedClasses  int           `json:"repeated_classes"`
	MaximumClassSize int           `json:"maximum_class_size"`
	IndexedTermCount int           `json:"indexed_term_count"`
}

type KMCandidate struct {
	Orientation    KMOrientation `json:"orientation"`
	PivotSlot      int           `json:"pivot_slot"`
	SourceSlots    []int         `json:"source_slots"`
	ChangedIndices []int         `json:"changed_indices"`
	targetTerms    []RankOneTerm
}

type KMScanResult struct {
	MaximumArity int                  `json:"maximum_arity"`
	Indexes      []KMOrientationIndex `json:"indexes"`
	Scans        []KMArityScan        `json:"scans"`
	Candidates   []KMCandidate        `json:"candidates"`
}

func (c KMCandidate) TargetTerms() []RankOneTerm {
	terms := make([]RankOneTerm, len(c.targetTerms))
	for i := range c.targetTerms {
		terms[i] = c.targetTerms[i].clone()
	}
	return terms
}

var kmOrientations = []KMOrientation{
	{BMode: 0, CMode: 2, AMode: 1},
	{BMode: 1, CMode: 0, AMode: 2},
	{BMode: 2, CMode: 1, AMode: 0},
}

var kmGuardNames = []string{
	"b0_not_sum",
	"source_not_injective",
	"output_c_zero",
	"output_not_injective",
	"context_not_disjoint",
}

func ScanBinaryKMIndexedData(scheme Scheme, maximumArity int) (KMScanResult, error) {
	if err := scheme.validateStructure(); err != nil {
		return KMScanResult{}, fmt.Errorf("binary KM scan source: %w", err)
	}
	if scheme.ring != ring.Z2 {
		return KMScanResult{}, fmt.Errorf("binary KM scan requires ring Z2, got %d", scheme.ring)
	}
	if maximumArity < 1 {
		return KMScanResult{}, fmt.Errorf("binary KM maximum arity is %d, want at least 1", maximumArity)
	}
	if err := ValidateNonzeroTerms(scheme); err != nil {
		return KMScanResult{}, fmt.Errorf("binary KM scan nonzero source: %w", err)
	}
	if err := ValidateDistinctTensors(scheme); err != nil {
		return KMScanResult{}, fmt.Errorf("binary KM scan distinct source: %w", err)
	}

	result := KMScanResult{MaximumArity: maximumArity}
	for _, orientation := range kmOrientations {
		classes := kmFactorClasses(scheme, orientation.AMode)
		index := KMOrientationIndex{
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
			scan := KMArityScan{
				Orientation:       orientation,
				Arity:             arity,
				GuardCounts:       make([]KMGuardCount, len(kmGuardNames)),
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
				return KMScanResult{}, scanErr
			}
			result.Scans = append(result.Scans, scan)
		}
	}
	return result, nil
}

func kmFactorClasses(scheme Scheme, mode int) [][]int {
	indexes := make(map[string]int)
	classes := make([][]int, 0)
	for slot, term := range scheme.terms {
		key := factorKey(term.factors[mode])
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

func checkKMCandidate(scheme Scheme, orientation KMOrientation, pivotSlot int, sourceSlots []int) (KMCandidate, string, error) {
	pivot := scheme.terms[pivotSlot]
	bSum := make([]int, len(pivot.factors[orientation.BMode].entries))
	pairs := make(map[string]struct{}, len(sourceSlots))
	for _, slot := range sourceSlots {
		term := scheme.terms[slot]
		for i, entry := range term.factors[orientation.BMode].entries {
			bSum[i] ^= entry
		}
		key := factorKey(term.factors[orientation.BMode]) + "\x00" + factorKey(term.factors[orientation.CMode])
		if _, found := pairs[key]; found {
			return KMCandidate{}, "source_not_injective", nil
		}
		pairs[key] = struct{}{}
	}
	if !slices.Equal(bSum, pivot.factors[orientation.BMode].entries) {
		return KMCandidate{}, "b0_not_sum", nil
	}

	support := make(map[int]struct{}, len(sourceSlots)+1)
	support[pivotSlot] = struct{}{}
	for _, slot := range sourceSlots {
		support[slot] = struct{}{}
	}
	targets := make([]RankOneTerm, len(sourceSlots))
	targetKeys := make(map[string]struct{}, len(sourceSlots))
	changed := make([]int, 0, len(sourceSlots))
	for index, slot := range sourceSlots {
		source := scheme.terms[slot]
		outputC, err := addMatrices(source.factors[orientation.CMode], pivot.factors[orientation.CMode])
		if err != nil {
			return KMCandidate{}, "", err
		}
		if matrixIsZero(outputC) {
			return KMCandidate{}, "output_c_zero", nil
		}
		factors := source.factors
		factors[orientation.CMode] = outputC
		target, err := NewRankOneTerm(factors[0], factors[1], factors[2])
		if err != nil {
			return KMCandidate{}, "", err
		}
		targets[index] = target
		key := termKey(target)
		if _, found := targetKeys[key]; found {
			return KMCandidate{}, "output_not_injective", nil
		}
		targetKeys[key] = struct{}{}
		matchesSource := false
		for _, sourceSlot := range sourceSlots {
			if equalTerms(target, scheme.terms[sourceSlot]) {
				matchesSource = true
				break
			}
		}
		if !matchesSource {
			changed = append(changed, index)
		}
		for contextSlot, contextTerm := range scheme.terms {
			if _, local := support[contextSlot]; local {
				continue
			}
			if equalTerms(target, contextTerm) {
				return KMCandidate{}, "context_not_disjoint", nil
			}
		}
	}
	return KMCandidate{
		Orientation:    orientation,
		PivotSlot:      pivotSlot,
		SourceSlots:    append([]int(nil), sourceSlots...),
		ChangedIndices: changed,
		targetTerms:    targets,
	}, "", nil
}

func termKey(term RankOneTerm) string {
	return factorKey(term.factors[0]) + "\x00" + factorKey(term.factors[1]) + "\x00" + factorKey(term.factors[2])
}

func equalTerms(first, second RankOneTerm) bool {
	for mode := range 3 {
		if !equalMatrices(first.factors[mode], second.factors[mode]) {
			return false
		}
	}
	return true
}
