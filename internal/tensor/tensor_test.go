package tensor

import (
	"bytes"
	"reflect"
	"strings"
	"testing"

	"patel.codes/proofs/internal/ring"
)

func TestStandardM2(t *testing.T) {
	for _, r := range []ring.Ring{ring.Z2, ring.Z3} {
		scheme := standardM2(t, r)
		if err := ValidateBrent(scheme); err != nil {
			t.Errorf("ValidateBrent over %v: %v", r, err)
		}
		if err := ValidateNonzeroTerms(scheme); err != nil {
			t.Errorf("ValidateNonzeroTerms over %v: %v", r, err)
		}
		if err := ValidateDistinctTensors(scheme); err != nil {
			t.Errorf("ValidateDistinctTensors over %v: %v", r, err)
		}
	}
}

func TestBadCoefficientFailsBrent(t *testing.T) {
	scheme := standardM2(t, ring.Z3)
	terms := scheme.Terms()
	factors := terms[0].Factors()
	entries := factors[0].Entries()
	entries[0] = 2
	factors[0] = mustMatrix(t, ring.Z3, 2, 2, entries)
	terms[0] = mustTerm(t, factors[0], factors[1], factors[2])
	bad := mustScheme(t, terms)
	if ValidateBrent(bad) == nil {
		t.Fatal("ValidateBrent accepted a bad coefficient")
	}
}

func TestNativeRectangularRoundTripAndNormalization(t *testing.T) {
	input := "2 3 1 1\n-1 +2 3 4 5 6\n7 -8 9\n10 11\n"
	scheme, err := ParseNative(ring.Z3, strings.NewReader(input))
	if err != nil {
		t.Fatal(err)
	}
	if got, want := scheme.Dimensions(), [3]int{2, 3, 1}; got != want {
		t.Fatalf("Dimensions() = %v, want %v", got, want)
	}
	wantFactors := [][]int{{2, 2, 0, 1, 2, 0}, {1, 1, 0}, {1, 2}}
	for i, want := range wantFactors {
		if got := scheme.Term(0).Factor(i).Entries(); !reflect.DeepEqual(got, want) {
			t.Errorf("factor %d = %v, want %v", i, got, want)
		}
	}
	var first bytes.Buffer
	if err := WriteNative(&first, scheme); err != nil {
		t.Fatal(err)
	}
	reparsed, err := ParseNative(ring.Z3, strings.NewReader(first.String()))
	if err != nil {
		t.Fatal(err)
	}
	var second bytes.Buffer
	if err := WriteNative(&second, reparsed); err != nil {
		t.Fatal(err)
	}
	if first.String() != second.String() {
		t.Fatalf("round trip changed native text:\n%s\n%s", first.String(), second.String())
	}
}

func TestNativeRankZeroRoundTrip(t *testing.T) {
	input := "2 3 1 0\n\n\n\n"
	scheme, err := ParseNative(ring.Z2, strings.NewReader(input))
	if err != nil {
		t.Fatal(err)
	}
	if scheme.TermCount() != 0 {
		t.Fatalf("TermCount() = %d, want 0", scheme.TermCount())
	}
	if got, want := scheme.Dimensions(), [3]int{2, 3, 1}; got != want {
		t.Fatalf("Dimensions() = %v, want %v", got, want)
	}
	if err := ValidateNonzeroTerms(scheme); err != nil {
		t.Fatal(err)
	}
	if err := ValidateDistinctTensors(scheme); err != nil {
		t.Fatal(err)
	}
	if err := ValidateBrent(scheme); err == nil {
		t.Fatal("ValidateBrent accepted a rank-zero matrix-multiplication scheme")
	}
	var output bytes.Buffer
	if err := WriteNative(&output, scheme); err != nil {
		t.Fatal(err)
	}
	if got := output.String(); got != input {
		t.Fatalf("WriteNative() = %q, want %q", got, input)
	}
	constructed, err := NewEmptyScheme(ring.Z2, [3]int{2, 3, 1})
	if err != nil {
		t.Fatal(err)
	}
	if got, want := constructed.Dimensions(), scheme.Dimensions(); got != want {
		t.Fatalf("NewEmptyScheme dimensions = %v, want %v", got, want)
	}
}

func TestNativeRejectsMalformedInput(t *testing.T) {
	inputs := []string{
		"2 2 2 00\n\n\n\n",
		"2 2 2 1\n1 0 0\n1 0 0 0\n1 0 0 0\n",
		"2 2 2 1\n1 0 0 x\n1 0 0 0\n1 0 0 0\n",
		"2 2 2 1\n1 0 0 0\n1 0 0 0\n1 0 0 0\nextra\n",
	}
	for _, input := range inputs {
		if _, err := ParseNative(ring.Z2, strings.NewReader(input)); err == nil {
			t.Errorf("ParseNative accepted %q", input)
		}
	}
}

func TestConstructorsRejectUnsupportedRing(t *testing.T) {
	if _, err := NewMatrix(ring.Ring(0), 1, 1, []int{0}); err == nil {
		t.Fatal("NewMatrix accepted an unsupported ring")
	}
	input := "1 1 1 1\n0\n0\n0\n"
	if _, err := ParseNative(ring.Ring(0), strings.NewReader(input)); err == nil {
		t.Fatal("ParseNative accepted an unsupported ring")
	}
}

func TestConstructorsAndSliceAccessorsCopy(t *testing.T) {
	entries := []int{1}
	matrix := mustMatrix(t, ring.Z2, 1, 1, entries)
	entries[0] = 0
	returned := matrix.Entries()
	returned[0] = 0
	if matrix.At(0, 0) != 1 {
		t.Fatal("matrix storage was mutated")
	}
	term := mustTerm(t, matrix, matrix, matrix)
	terms := []RankOneTerm{term}
	scheme := mustScheme(t, terms)
	terms[0] = RankOneTerm{}
	if _, err := NewScheme(terms); err == nil {
		t.Fatal("NewScheme accepted a zero-value term")
	}
	returnedTerms := scheme.Terms()
	returnedTerms[0] = RankOneTerm{}
	if scheme.Term(0).Factor(0).At(0, 0) != 1 {
		t.Fatal("scheme storage was mutated")
	}
}

func TestStateChecksAreSeparate(t *testing.T) {
	one := mustMatrix(t, ring.Z3, 1, 1, []int{1})
	two := mustMatrix(t, ring.Z3, 1, 1, []int{2})
	zero := mustMatrix(t, ring.Z3, 1, 1, []int{0})
	duplicateA := mustTerm(t, one, one, one)
	duplicateB := mustTerm(t, two, one, two)
	duplicates := mustScheme(t, []RankOneTerm{duplicateA, duplicateB})
	if err := ValidateNonzeroTerms(duplicates); err != nil {
		t.Fatal(err)
	}
	if ValidateDistinctTensors(duplicates) == nil {
		t.Fatal("equal tensors were accepted as distinct")
	}
	withZero := mustScheme(t, []RankOneTerm{duplicateA, mustTerm(t, zero, one, one)})
	if ValidateNonzeroTerms(withZero) == nil {
		t.Fatal("zero term was accepted")
	}
	if err := ValidateDistinctTensors(withZero); err != nil {
		t.Fatalf("distinctness check unexpectedly enforced nonzero terms: %v", err)
	}
}

func standardM2(t *testing.T, r ring.Ring) Scheme {
	t.Helper()
	terms := make([]RankOneTerm, 0, 8)
	for i := range 2 {
		for j := range 2 {
			for k := range 2 {
				u := make([]int, 4)
				v := make([]int, 4)
				w := make([]int, 4)
				u[2*i+k] = 1
				v[2*k+j] = 1
				w[2*j+i] = 1
				terms = append(terms, mustTerm(t,
					mustMatrix(t, r, 2, 2, u),
					mustMatrix(t, r, 2, 2, v),
					mustMatrix(t, r, 2, 2, w),
				))
			}
		}
	}
	return mustScheme(t, terms)
}

func mustMatrix(t *testing.T, r ring.Ring, rows, columns int, entries []int) Matrix {
	t.Helper()
	matrix, err := NewMatrix(r, rows, columns, entries)
	if err != nil {
		t.Fatal(err)
	}
	return matrix
}

func mustTerm(t *testing.T, first, second, third Matrix) RankOneTerm {
	t.Helper()
	term, err := NewRankOneTerm(first, second, third)
	if err != nil {
		t.Fatal(err)
	}
	return term
}

func mustScheme(t *testing.T, terms []RankOneTerm) Scheme {
	t.Helper()
	scheme, err := NewScheme(terms)
	if err != nil {
		t.Fatal(err)
	}
	return scheme
}
