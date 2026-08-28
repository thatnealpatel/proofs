package tensor

import (
	"reflect"
	"testing"

	"patel.codes/proofs/internal/ring"
)

func TestApplyReplacementUsesArbitrarySupportAndDeterministicOrder(t *testing.T) {
	source := mustScheme(t, []RankOneTerm{
		scalarTerm(t, ring.Z3, 1, 1, 1),
		scalarTerm(t, ring.Z3, 2, 1, 1),
		scalarTerm(t, ring.Z3, 1, 2, 1),
		scalarTerm(t, ring.Z3, 1, 1, 2),
		scalarTerm(t, ring.Z3, 2, 2, 1),
		scalarTerm(t, ring.Z3, 2, 1, 2),
		scalarTerm(t, ring.Z3, 1, 2, 2),
	})
	inserted := []RankOneTerm{
		scalarTerm(t, ring.Z3, 2, 2, 2),
		scalarTerm(t, ring.Z3, 1, 1, 1),
		scalarTerm(t, ring.Z3, 0, 1, 1),
	}
	replacement := mustReplacement(t, []int{1, 3, 5, 6}, inserted)
	if err := ValidateReplacement(source, replacement); err != nil {
		t.Fatal(err)
	}
	child, err := ApplyReplacement(source, replacement)
	if err != nil {
		t.Fatal(err)
	}
	want := [][3]int{{1, 1, 1}, {1, 2, 1}, {2, 2, 1}, {2, 2, 2}, {1, 1, 1}, {0, 1, 1}}
	if got := scalarFactors(child); !reflect.DeepEqual(got, want) {
		t.Fatalf("child factors = %v, want %v", got, want)
	}
	if ValidateNonzeroTerms(child) == nil {
		t.Fatal("child unexpectedly has only nonzero terms")
	}
	if ValidateDistinctTensors(child) == nil {
		t.Fatal("child unexpectedly has distinct tensors")
	}
}

func TestApplyReplacementPreservesRectangularCyclicFactors(t *testing.T) {
	for _, r := range []ring.Ring{ring.Z2, ring.Z3} {
		survivor := rectangularTerm(t, r, []int{0, 0, 1, 0, 0, 0}, []int{0, 0, 1}, []int{1, 0})
		first := rectangularTerm(t, r, []int{1, 0, 0, 0, 0, 0}, []int{1, 0, 0}, []int{1, 0})
		second := rectangularTerm(t, r, []int{0, 0, 0, 0, 1, 0}, []int{0, 1, 0}, []int{0, 1})
		source := mustScheme(t, []RankOneTerm{survivor, first, second})
		replacement := mustReplacement(t, []int{1, 2}, []RankOneTerm{second, first})
		child, err := ApplyReplacement(source, replacement)
		if err != nil {
			t.Fatalf("ApplyReplacement over %v: %v", r, err)
		}
		want := [][3][]int{termEntries(survivor), termEntries(second), termEntries(first)}
		if got := schemeEntries(child); !reflect.DeepEqual(got, want) {
			t.Fatalf("child over %v = %v, want %v", r, got, want)
		}
		bad := rectangularTerm(t, r, []int{0, 0, 0, 0, 0, 1}, []int{0, 1, 0}, []int{0, 1})
		inexact := mustReplacement(t, []int{1, 2}, []RankOneTerm{bad, first})
		if err := ValidateReplacement(source, inexact); err == nil {
			t.Fatalf("ValidateReplacement accepted unequal rectangular sums over %v", r)
		}
	}
}

func TestReplacementRejectsInvalidRemovedSlots(t *testing.T) {
	for _, slots := range [][]int{{-1}, {1, 1}, {2, 1}} {
		if _, err := NewReplacement(slots, nil); err == nil {
			t.Errorf("NewReplacement accepted removed slots %v", slots)
		}
	}
}

func TestValidateReplacementChecksApplicabilityAndExactSum(t *testing.T) {
	source := mustScheme(t, []RankOneTerm{
		scalarTerm(t, ring.Z3, 1, 1, 1),
		scalarTerm(t, ring.Z3, 2, 1, 1),
	})
	tests := []struct {
		name        string
		replacement Replacement
	}{
		{
			name:        "slot out of range",
			replacement: mustReplacement(t, []int{2}, nil),
		},
		{
			name:        "different sum",
			replacement: mustReplacement(t, []int{0}, []RankOneTerm{scalarTerm(t, ring.Z3, 2, 1, 1)}),
		},
		{
			name:        "different ring",
			replacement: mustReplacement(t, []int{0}, []RankOneTerm{scalarTerm(t, ring.Z2, 1, 1, 1)}),
		},
		{
			name: "different dimensions",
			replacement: mustReplacement(t, []int{0}, []RankOneTerm{mustTerm(t,
				mustMatrix(t, ring.Z3, 1, 1, []int{1}),
				mustMatrix(t, ring.Z3, 1, 2, []int{1, 0}),
				mustMatrix(t, ring.Z3, 2, 1, []int{1, 0}),
			)}),
		},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			if err := ValidateReplacement(source, test.replacement); err == nil {
				t.Fatal("ValidateReplacement accepted an inapplicable replacement")
			}
			if _, err := ApplyReplacement(source, test.replacement); err == nil {
				t.Fatal("ApplyReplacement accepted an inapplicable replacement")
			}
		})
	}
}

func TestReplacementCopiesInputsAndAccessors(t *testing.T) {
	source := mustScheme(t, []RankOneTerm{
		scalarTerm(t, ring.Z3, 1, 1, 1),
		scalarTerm(t, ring.Z3, 2, 1, 1),
	})
	removed := []int{1}
	inserted := []RankOneTerm{scalarTerm(t, ring.Z3, 2, 1, 1)}
	replacement := mustReplacement(t, removed, inserted)
	removed[0] = 0
	inserted[0].factors[0].entries[0] = 0
	returnedRemoved := replacement.RemovedSlots()
	returnedRemoved[0] = 0
	returnedInserted := replacement.InsertedTerms()
	returnedInserted[0].factors[0].entries[0] = 0
	if got, want := replacement.RemovedSlots(), []int{1}; !reflect.DeepEqual(got, want) {
		t.Fatalf("RemovedSlots() = %v, want %v", got, want)
	}
	if got := replacement.InsertedTerms()[0].Factor(0).At(0, 0); got != 2 {
		t.Fatalf("inserted factor = %d, want 2", got)
	}
	child, err := ApplyReplacement(source, replacement)
	if err != nil {
		t.Fatal(err)
	}
	source.terms[0].factors[0].entries[0] = 0
	replacement.insertedTerms[0].factors[0].entries[0] = 0
	if got, want := scalarFactors(child), [][3]int{{1, 1, 1}, {2, 1, 1}}; !reflect.DeepEqual(got, want) {
		t.Fatalf("child factors = %v, want %v", got, want)
	}
}

func TestEmptyReplacementAndRankZeroResult(t *testing.T) {
	source := mustScheme(t, []RankOneTerm{scalarTerm(t, ring.Z3, 1, 1, 1)})
	empty := mustReplacement(t, nil, nil)
	if err := ValidateReplacement(source, empty); err != nil {
		t.Fatal(err)
	}
	unchanged, err := ApplyReplacement(source, empty)
	if err != nil {
		t.Fatal(err)
	}
	if got, want := scalarFactors(unchanged), scalarFactors(source); !reflect.DeepEqual(got, want) {
		t.Fatalf("empty replacement produced %v, want %v", got, want)
	}

	zeroSource := mustScheme(t, []RankOneTerm{scalarTerm(t, ring.Z3, 0, 1, 1)})
	removeZero := mustReplacement(t, []int{0}, nil)
	if err := ValidateReplacement(zeroSource, removeZero); err != nil {
		t.Fatal(err)
	}
	rankZero, err := ApplyReplacement(zeroSource, removeZero)
	if err != nil {
		t.Fatal(err)
	}
	if rankZero.TermCount() != 0 {
		t.Fatalf("rank-zero result has %d terms", rankZero.TermCount())
	}
	if got, want := rankZero.Ring(), ring.Z3; got != want {
		t.Fatalf("rank-zero ring = %d, want %d", got, want)
	}
	if got, want := rankZero.Dimensions(), [3]int{1, 1, 1}; got != want {
		t.Fatalf("rank-zero dimensions = %v, want %v", got, want)
	}
	if err := ValidateNonzeroTerms(rankZero); err != nil {
		t.Fatal(err)
	}
	if err := ValidateDistinctTensors(rankZero); err != nil {
		t.Fatal(err)
	}
	if err := ValidateReplacement(rankZero, empty); err != nil {
		t.Fatal(err)
	}
	if _, err := ApplyReplacement(rankZero, empty); err != nil {
		t.Fatal(err)
	}
}

func rectangularTerm(t *testing.T, r ring.Ring, first, second, third []int) RankOneTerm {
	t.Helper()
	return mustTerm(t,
		mustMatrix(t, r, 2, 3, first),
		mustMatrix(t, r, 3, 1, second),
		mustMatrix(t, r, 1, 2, third),
	)
}

func termEntries(term RankOneTerm) [3][]int {
	return [3][]int{
		term.Factor(0).Entries(),
		term.Factor(1).Entries(),
		term.Factor(2).Entries(),
	}
}

func schemeEntries(scheme Scheme) [][3][]int {
	entries := make([][3][]int, scheme.TermCount())
	for i := range entries {
		entries[i] = termEntries(scheme.Term(i))
	}
	return entries
}

func scalarTerm(t *testing.T, r ring.Ring, first, second, third int) RankOneTerm {
	t.Helper()
	return mustTerm(t,
		mustMatrix(t, r, 1, 1, []int{first}),
		mustMatrix(t, r, 1, 1, []int{second}),
		mustMatrix(t, r, 1, 1, []int{third}),
	)
}

func scalarFactors(scheme Scheme) [][3]int {
	factors := make([][3]int, scheme.TermCount())
	for i := range factors {
		for j := range 3 {
			factors[i][j] = scheme.Term(i).Factor(j).At(0, 0)
		}
	}
	return factors
}

func mustReplacement(t *testing.T, removedSlots []int, insertedTerms []RankOneTerm) Replacement {
	t.Helper()
	replacement, err := NewReplacement(removedSlots, insertedTerms)
	if err != nil {
		t.Fatal(err)
	}
	return replacement
}
