package tensor

import (
	"slices"
	"testing"

	"patel.codes/proofs/internal/ring"
)

func TestScanBinaryKMIndexedDataFindsBroadCandidate(t *testing.T) {
	terms := []struct {
		b uint16
		a uint16
		c uint16
	}{
		{3, 1, 1},
		{1, 1, 2},
		{2, 1, 4},
		{8, 2, 8},
	}
	schemeTerms := make([]RankOneTerm, len(terms))
	for i, words := range terms {
		var err error
		schemeTerms[i], err = kmTestTerm(words.b, words.a, words.c)
		if err != nil {
			t.Fatal(err)
		}
	}
	scheme, err := NewScheme(schemeTerms)
	if err != nil {
		t.Fatal(err)
	}
	result, err := ScanBinaryKMIndexedData(scheme, 5)
	if err != nil {
		t.Fatal(err)
	}
	var found bool
	for _, candidate := range result.Candidates {
		if candidate.Orientation == (KMOrientation{BMode: 0, CMode: 2, AMode: 1}) &&
			candidate.PivotSlot == 0 && slices.Equal(candidate.SourceSlots, []int{1, 2}) {
			found = true
			if !slices.Equal(candidate.ChangedIndices, []int{0, 1}) {
				t.Fatalf("changed indices = %v, want [0 1]", candidate.ChangedIndices)
			}
			if len(candidate.TargetTerms()) != 2 {
				t.Fatalf("target count = %d, want 2", len(candidate.TargetTerms()))
			}
		}
	}
	if !found {
		t.Fatal("broad n=2 candidate was not recognized")
	}
	for _, scan := range result.Scans {
		var rejected uint64
		for _, guard := range scan.GuardCounts {
			rejected += guard.Count
		}
		if rejected != scan.Rejected || scan.Accepted+scan.Rejected != scan.Enumerated {
			t.Fatalf("inconsistent scan counters: %+v", scan)
		}
	}
}

func TestScanBinaryKMIndexedDataRejectsBadBoundsAndRing(t *testing.T) {
	term, err := kmTestTerm(1, 1, 1)
	if err != nil {
		t.Fatal(err)
	}
	scheme, err := NewScheme([]RankOneTerm{term})
	if err != nil {
		t.Fatal(err)
	}
	if _, err := ScanBinaryKMIndexedData(scheme, 0); err == nil {
		t.Fatal("zero maximum arity was accepted")
	}
	matrix, err := NewMatrix(ring.Z3, 1, 1, []int{1})
	if err != nil {
		t.Fatal(err)
	}
	z3Term, err := NewRankOneTerm(matrix, matrix, matrix)
	if err != nil {
		t.Fatal(err)
	}
	z3Scheme, err := NewScheme([]RankOneTerm{z3Term})
	if err != nil {
		t.Fatal(err)
	}
	if _, err := ScanBinaryKMIndexedData(z3Scheme, 5); err == nil {
		t.Fatal("Z3 scheme was accepted")
	}
}

func kmTestTerm(first, second, third uint16) (RankOneTerm, error) {
	matrices := [3]Matrix{}
	for i, word := range []uint16{first, second, third} {
		entries := make([]int, 4)
		for bit := range entries {
			entries[bit] = int(word >> bit & 1)
		}
		matrix, err := NewMatrix(ring.Z2, 2, 2, entries)
		if err != nil {
			return RankOneTerm{}, err
		}
		matrices[i] = matrix
	}
	return NewRankOneTerm(matrices[0], matrices[1], matrices[2])
}
