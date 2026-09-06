package main

import (
	"slices"
	"testing"

	"patel.codes/proofs/internal/ring"
	"patel.codes/proofs/internal/tensor"
)

func TestPrivateScannerAcceptsSwappedRoleBroadCandidate(t *testing.T) {
	words := []triple{
		{1, 1, 3},
		{2, 1, 1},
		{4, 1, 2},
		{8, 2, 8},
	}
	terms := make([]tensor.RankOneTerm, len(words))
	for i, word := range words {
		var err error
		terms[i], err = scannerTestTerm(word)
		if err != nil {
			t.Fatal(err)
		}
	}
	scheme, err := tensor.NewScheme(terms)
	if err != nil {
		t.Fatal(err)
	}
	result, err := scanBinaryKMIndexedData(scheme, 5)
	if err != nil {
		t.Fatal(err)
	}
	orientation := kmOrientation{BMode: 2, CMode: 0, AMode: 1}
	for _, candidate := range result.Candidates {
		if candidate.Orientation == orientation && candidate.PivotSlot == 0 && slices.Equal(candidate.SourceSlots, []int{1, 2}) {
			if !slices.Equal(candidate.ChangedIndices, []int{0, 1}) {
				t.Fatalf("changed indices = %v, want [0 1]", candidate.ChangedIndices)
			}
			return
		}
	}
	t.Fatal("swapped-role n=2 candidate was not accepted")
}

func scannerTestTerm(words triple) (tensor.RankOneTerm, error) {
	matrices := [3]tensor.Matrix{}
	for mode, word := range words {
		entries := make([]int, 4)
		for bit := range entries {
			entries[bit] = int(word >> bit & 1)
		}
		matrix, err := tensor.NewMatrix(ring.Z2, 2, 2, entries)
		if err != nil {
			return tensor.RankOneTerm{}, err
		}
		matrices[mode] = matrix
	}
	return tensor.NewRankOneTerm(matrices[0], matrices[1], matrices[2])
}
