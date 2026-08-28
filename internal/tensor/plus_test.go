package tensor

import (
	"fmt"
	"reflect"
	"strings"
	"testing"

	"patel.codes/proofs/internal/ring"
)

func TestNewPlusReplacementPackedExample(t *testing.T) {
	source := mustScheme(t, []RankOneTerm{
		packedTerm(t, ring.Z2, 9, 9, 9),
		packedTerm(t, ring.Z2, 12, 1, 10),
	})
	replacement, err := NewPlusReplacement(source, 0, 1)
	if err != nil {
		t.Fatal(err)
	}
	if got, want := replacement.RemovedSlots(), []int{0, 1}; !reflect.DeepEqual(got, want) {
		t.Fatalf("removed slots = %v, want %v", got, want)
	}
	if got, want := packedTerms(replacement.InsertedTerms()), [][3]int{{9, 8, 9}, {5, 1, 10}, {9, 1, 3}}; !reflect.DeepEqual(got, want) {
		t.Fatalf("inserted terms = %v, want %v", got, want)
	}
	if err := ValidateReplacement(source, replacement); err != nil {
		t.Fatal(err)
	}
}

func TestNewPlusReplacementSourceOrderIsSignificant(t *testing.T) {
	source := mustScheme(t, []RankOneTerm{
		packedTerm(t, ring.Z2, 9, 9, 9),
		packedTerm(t, ring.Z2, 12, 1, 10),
	})
	replacement, err := NewPlusReplacement(source, 1, 0)
	if err != nil {
		t.Fatal(err)
	}
	if got, want := replacement.RemovedSlots(), []int{0, 1}; !reflect.DeepEqual(got, want) {
		t.Fatalf("removed slots = %v, want %v", got, want)
	}
	if got, want := packedTerms(replacement.InsertedTerms()), [][3]int{{12, 8, 10}, {5, 9, 9}, {12, 9, 3}}; !reflect.DeepEqual(got, want) {
		t.Fatalf("inserted terms = %v, want %v", got, want)
	}
}

func TestNewPlusReplacementAppliesSurvivorsThenInsertions(t *testing.T) {
	survivor0 := packedTerm(t, ring.Z2, 1, 2, 4)
	qTerm := packedTerm(t, ring.Z2, 12, 1, 10)
	survivor2 := packedTerm(t, ring.Z2, 3, 5, 6)
	pTerm := packedTerm(t, ring.Z2, 9, 9, 9)
	source := mustScheme(t, []RankOneTerm{survivor0, qTerm, survivor2, pTerm})
	replacement, err := NewPlusReplacement(source, 3, 1)
	if err != nil {
		t.Fatal(err)
	}
	if err := ValidateReplacement(source, replacement); err != nil {
		t.Fatal(err)
	}
	child, err := ApplyReplacement(source, replacement)
	if err != nil {
		t.Fatal(err)
	}
	want := [][3]int{{1, 2, 4}, {3, 5, 6}, {9, 8, 9}, {5, 1, 10}, {9, 1, 3}}
	if got := packedTerms(child.Terms()); !reflect.DeepEqual(got, want) {
		t.Fatalf("applied terms = %v, want %v", got, want)
	}
}

func TestNewPlusReplacementRejectsEqualFactor(t *testing.T) {
	for _, test := range []struct {
		name   string
		factor int
		second [3]int
	}{
		{name: "factor 0", factor: 0, second: [3]int{9, 1, 10}},
		{name: "factor 1", factor: 1, second: [3]int{12, 9, 10}},
		{name: "factor 2", factor: 2, second: [3]int{12, 1, 9}},
	} {
		t.Run(test.name, func(t *testing.T) {
			source := mustScheme(t, []RankOneTerm{
				packedTerm(t, ring.Z2, 9, 9, 9),
				packedTerm(t, ring.Z2, test.second[0], test.second[1], test.second[2]),
			})
			_, err := NewPlusReplacement(source, 0, 1)
			if err == nil {
				t.Fatal("NewPlusReplacement accepted equal source factor matrices")
			}
			if want := fmt.Sprintf("factor %d", test.factor); !strings.Contains(err.Error(), want) {
				t.Fatalf("NewPlusReplacement error = %q, want it to contain %q", err, want)
			}
		})
	}
}

func TestNewPlusReplacementRejectsInvalidInputs(t *testing.T) {
	source := mustScheme(t, []RankOneTerm{
		packedTerm(t, ring.Z2, 9, 9, 9),
		packedTerm(t, ring.Z2, 12, 1, 10),
	})
	for _, test := range []struct {
		name string
		p    int
		q    int
		want string
	}{
		{name: "equal", p: 0, q: 0, want: "slots must be distinct"},
		{name: "negative p", p: -1, q: 0, want: "slot p is out of range"},
		{name: "negative q", p: 0, q: -1, want: "slot q is out of range"},
		{name: "large p", p: 2, q: 0, want: "slot p is out of range"},
		{name: "large q", p: 0, q: 2, want: "slot q is out of range"},
		{name: "equal negative", p: -1, q: -1, want: "slot p is out of range: -1 for 2 terms"},
		{name: "equal too large", p: 2, q: 2, want: "slot p is out of range: 2 for 2 terms"},
	} {
		t.Run(test.name, func(t *testing.T) {
			_, err := NewPlusReplacement(source, test.p, test.q)
			if err == nil {
				t.Fatal("NewPlusReplacement accepted invalid source slots")
			}
			if !strings.Contains(err.Error(), test.want) {
				t.Fatalf("NewPlusReplacement error = %q, want it to contain %q", err, test.want)
			}
		})
	}
	if _, err := NewPlusReplacement(Scheme{}, 0, 1); err == nil {
		t.Fatal("NewPlusReplacement accepted an invalid scheme")
	}
}

func TestNewPlusReplacementRejectsZ3(t *testing.T) {
	source := mustScheme(t, []RankOneTerm{
		packedTerm(t, ring.Z3, 9, 9, 9),
		packedTerm(t, ring.Z3, 12, 1, 10),
	})
	if _, err := NewPlusReplacement(source, 0, 1); err == nil {
		t.Fatal("NewPlusReplacement accepted Z3")
	}
}

func packedTerm(t *testing.T, r ring.Ring, first, second, third int) RankOneTerm {
	t.Helper()
	return mustTerm(t,
		mustMatrix(t, r, 2, 2, unpackMask(first)),
		mustMatrix(t, r, 2, 2, unpackMask(second)),
		mustMatrix(t, r, 2, 2, unpackMask(third)),
	)
}

func unpackMask(mask int) []int {
	entries := make([]int, 4)
	for i := range entries {
		entries[i] = mask >> i & 1
	}
	return entries
}

func packedTerms(terms []RankOneTerm) [][3]int {
	packed := make([][3]int, len(terms))
	for i, term := range terms {
		for factor := range 3 {
			for bit, entry := range term.Factor(factor).Entries() {
				packed[i][factor] |= entry << bit
			}
		}
	}
	return packed
}
