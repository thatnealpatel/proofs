package tensor

import (
	"fmt"
	"reflect"
	"strings"
	"testing"

	"patel.codes/proofs/internal/ring"
)

func TestPlusVariantValues(t *testing.T) {
	if PlusVariantSecondThirdFirst != 0 {
		t.Fatalf("PlusVariantSecondThirdFirst = %d, want 0", PlusVariantSecondThirdFirst)
	}
	if PlusVariantThirdFirstSecond != 1 {
		t.Fatalf("PlusVariantThirdFirstSecond = %d, want 1", PlusVariantThirdFirstSecond)
	}
	if PlusVariantFirstSecondThird != 2 {
		t.Fatalf("PlusVariantFirstSecondThird = %d, want 2", PlusVariantFirstSecondThird)
	}
}

func TestNewInversePlusReplacementPinsFormulaOutputOrder(t *testing.T) {
	sources := [2][3]int{{1, 2, 4}, {14, 7, 9}}
	tests := []struct {
		name    string
		variant PlusVariant
		outputs [][3]int
	}{
		{
			name:    "second third first",
			variant: PlusVariantSecondThirdFirst,
			outputs: [][3]int{{1, 5, 4}, {15, 7, 9}, {1, 7, 13}},
		},
		{
			name:    "third first second",
			variant: PlusVariantThirdFirstSecond,
			outputs: [][3]int{{1, 2, 13}, {14, 5, 9}, {15, 2, 9}},
		},
		{
			name:    "first second third",
			variant: PlusVariantFirstSecondThird,
			outputs: [][3]int{{15, 2, 4}, {14, 7, 13}, {14, 5, 4}},
		},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			outputs := packedTermTriples(t, ring.Z2, test.outputs)
			scheme := mustScheme(t, []RankOneTerm{outputs[2], outputs[0], outputs[1]})
			replacement, err := NewInversePlusReplacement(scheme, [3]int{1, 2, 0}, test.variant)
			if err != nil {
				t.Fatal(err)
			}
			if got, want := replacement.RemovedSlots(), []int{0, 1, 2}; !reflect.DeepEqual(got, want) {
				t.Fatalf("removed slots = %v, want %v", got, want)
			}
			if got, want := packedTerms(replacement.InsertedTerms()), sources[:]; !reflect.DeepEqual(got, want) {
				t.Fatalf("recovered sources = %v, want %v", got, want)
			}
			if err := ValidateReplacement(scheme, replacement); err != nil {
				t.Fatal(err)
			}
		})
	}
}

func TestNewInversePlusReplacementRoundTripsEveryVariantAndPhysicalPlacement(t *testing.T) {
	sources := [2][3]int{{1, 2, 4}, {14, 7, 9}}
	variants := []PlusVariant{
		PlusVariantSecondThirdFirst,
		PlusVariantThirdFirstSecond,
		PlusVariantFirstSecondThird,
	}
	permutations := [][3]int{
		{0, 1, 2},
		{0, 2, 1},
		{1, 0, 2},
		{1, 2, 0},
		{2, 0, 1},
		{2, 1, 0},
	}
	for _, variant := range variants {
		outputs := testInversePlusOutputs(t, sources, variant)
		for _, permutation := range permutations {
			name := fmt.Sprintf("variant %d placement %v", variant, permutation)
			t.Run(name, func(t *testing.T) {
				survivor0 := packedTerm(t, ring.Z2, 3, 6, 10)
				survivor1 := packedTerm(t, ring.Z2, 8, 11, 12)
				terms := []RankOneTerm{survivor0, outputs[permutation[0]], survivor1, outputs[permutation[1]], outputs[permutation[2]]}
				slots := [3]int{}
				for position, formulaOutput := range permutation {
					slots[formulaOutput] = [3]int{1, 3, 4}[position]
				}
				scheme := mustScheme(t, terms)
				replacement, err := NewInversePlusReplacement(scheme, slots, variant)
				if err != nil {
					t.Fatal(err)
				}
				if got, want := replacement.RemovedSlots(), []int{1, 3, 4}; !reflect.DeepEqual(got, want) {
					t.Fatalf("removed slots = %v, want %v", got, want)
				}
				if got, want := packedTerms(replacement.InsertedTerms()), sources[:]; !reflect.DeepEqual(got, want) {
					t.Fatalf("recovered sources = %v, want %v", got, want)
				}
				replayed, err := ApplyReplacement(scheme, replacement)
				if err != nil {
					t.Fatal(err)
				}
				want := [][3]int{{3, 6, 10}, {8, 11, 12}, sources[0], sources[1]}
				if got := packedTerms(replayed.Terms()); !reflect.DeepEqual(got, want) {
					t.Fatalf("applied terms = %v, want %v", got, want)
				}
			})
		}
	}
}

func TestNewInversePlusReplacementRoundTripsNewPlusReplacement(t *testing.T) {
	sources := [2][3]int{{1, 2, 4}, {14, 7, 9}}
	source := mustScheme(t, packedTermTriples(t, ring.Z2, sources[:]))
	forward, err := NewPlusReplacement(source, 0, 1)
	if err != nil {
		t.Fatal(err)
	}
	child, err := ApplyReplacement(source, forward)
	if err != nil {
		t.Fatal(err)
	}
	inverse, err := NewInversePlusReplacement(child, [3]int{0, 1, 2}, PlusVariantSecondThirdFirst)
	if err != nil {
		t.Fatal(err)
	}
	replayed, err := ApplyReplacement(child, inverse)
	if err != nil {
		t.Fatal(err)
	}
	if got, want := packedTerms(replayed.Terms()), sources[:]; !reflect.DeepEqual(got, want) {
		t.Fatalf("replayed sources = %v, want %v", got, want)
	}
}

func TestNewInversePlusReplacementAllowsZeroRecoveredFactor(t *testing.T) {
	sources := [2][3]int{{0, 2, 4}, {14, 7, 9}}
	source := mustScheme(t, packedTermTriples(t, ring.Z2, sources[:]))
	if err := ValidateNonzeroTerms(source); err == nil {
		t.Fatal("zero-factor source unexpectedly passed nonzero validation")
	}
	forward, err := NewPlusReplacement(source, 0, 1)
	if err != nil {
		t.Fatal(err)
	}
	child, err := ApplyReplacement(source, forward)
	if err != nil {
		t.Fatal(err)
	}
	inverse, err := NewInversePlusReplacement(child, [3]int{0, 1, 2}, PlusVariantSecondThirdFirst)
	if err != nil {
		t.Fatal(err)
	}
	replayed, err := ApplyReplacement(child, inverse)
	if err != nil {
		t.Fatal(err)
	}
	if got, want := packedTerms(replayed.Terms()), sources[:]; !reflect.DeepEqual(got, want) {
		t.Fatalf("replayed zero-factor sources = %v, want %v", got, want)
	}
	if err := ValidateNonzeroTerms(replayed); err == nil {
		t.Fatal("replayed zero-factor source unexpectedly passed nonzero validation")
	}
}

func TestNewInversePlusReplacementRejectsEveryReplayConstraintMutation(t *testing.T) {
	sources := [2][3]int{{1, 2, 4}, {14, 7, 9}}
	tests := []struct {
		variant   PlusVariant
		mutations [][2]int
	}{
		{
			variant: PlusVariantSecondThirdFirst,
			mutations: [][2]int{
				{0, 0}, {2, 0},
				{1, 1}, {2, 1},
				{0, 2}, {1, 2}, {2, 2},
			},
		},
		{
			variant: PlusVariantThirdFirstSecond,
			mutations: [][2]int{
				{0, 0}, {1, 0}, {2, 0},
				{0, 1}, {2, 1},
				{1, 2}, {2, 2},
			},
		},
		{
			variant: PlusVariantFirstSecondThird,
			mutations: [][2]int{
				{1, 0}, {2, 0},
				{0, 1}, {1, 1}, {2, 1},
				{0, 2}, {2, 2},
			},
		},
	}
	for _, test := range tests {
		for _, mutation := range test.mutations {
			name := fmt.Sprintf("variant %d output %d factor %d", test.variant, mutation[0], mutation[1])
			t.Run(name, func(t *testing.T) {
				outputs := testInversePlusOutputs(t, sources, test.variant)
				outputs[mutation[0]].factors[mutation[1]].entries[0] ^= 1
				scheme := mustScheme(t, outputs[:])
				_, err := NewInversePlusReplacement(scheme, [3]int{0, 1, 2}, test.variant)
				if err == nil || !strings.Contains(err.Error(), "output replay differs") {
					t.Fatalf("mutation produced error %v, want replay rejection", err)
				}
			})
		}
	}
}

func TestNewInversePlusReplacementRejectsSourceFactorCollisions(t *testing.T) {
	base := [2][3]int{{1, 2, 4}, {14, 7, 9}}
	variants := []PlusVariant{
		PlusVariantSecondThirdFirst,
		PlusVariantThirdFirstSecond,
		PlusVariantFirstSecondThird,
	}
	for _, variant := range variants {
		for mode := range 3 {
			name := fmt.Sprintf("variant %d factor %d", variant, mode)
			t.Run(name, func(t *testing.T) {
				sources := base
				sources[1][mode] = sources[0][mode]
				outputs := testInversePlusOutputs(t, sources, variant)
				scheme := mustScheme(t, outputs[:])
				_, err := NewInversePlusReplacement(scheme, [3]int{0, 1, 2}, variant)
				want := fmt.Sprintf("must differ at factor %d", mode)
				if err == nil || !strings.Contains(err.Error(), want) {
					t.Fatalf("error = %v, want text %q", err, want)
				}
			})
		}
	}
}

func TestNewInversePlusReplacementRejectsWrongRingAndMalformedScheme(t *testing.T) {
	z3 := mustScheme(t, []RankOneTerm{
		scalarTerm(t, ring.Z3, 1, 1, 1),
		scalarTerm(t, ring.Z3, 2, 1, 1),
		scalarTerm(t, ring.Z3, 1, 2, 1),
	})
	if _, err := NewInversePlusReplacement(z3, [3]int{0, 1, 2}, PlusVariantSecondThirdFirst); err == nil || !strings.Contains(err.Error(), "requires ring Z2") {
		t.Fatalf("Z3 produced error %v, want ring rejection", err)
	}

	validOutputs := testInversePlusOutputs(t, [2][3]int{{1, 2, 4}, {14, 7, 9}}, PlusVariantSecondThirdFirst)
	valid := mustScheme(t, validOutputs[:])
	invalidStorage := valid
	invalidStorage.terms[0].factors[0].entries = nil
	for name, scheme := range map[string]Scheme{
		"zero value":      {},
		"invalid storage": invalidStorage,
	} {
		t.Run(name, func(t *testing.T) {
			_, err := NewInversePlusReplacement(scheme, [3]int{0, 1, 2}, PlusVariantSecondThirdFirst)
			if err == nil || !strings.Contains(err.Error(), "source scheme") {
				t.Fatalf("malformed scheme produced error %v, want structural rejection", err)
			}
		})
	}
}

func TestNewInversePlusReplacementRejectsInvalidVariantAndSlots(t *testing.T) {
	outputs := testInversePlusOutputs(t, [2][3]int{{1, 2, 4}, {14, 7, 9}}, PlusVariantSecondThirdFirst)
	scheme := mustScheme(t, outputs[:])
	for _, variant := range []PlusVariant{-1, 3} {
		_, err := NewInversePlusReplacement(scheme, [3]int{0, 1, 2}, variant)
		if err == nil || !strings.Contains(err.Error(), "variant is unsupported") {
			t.Errorf("variant %d produced error %v, want variant rejection", variant, err)
		}
	}
	for _, test := range []struct {
		name  string
		slots [3]int
		want  string
	}{
		{name: "negative first", slots: [3]int{-1, 1, 2}, want: "slot 0 is out of range"},
		{name: "negative second", slots: [3]int{0, -1, 2}, want: "slot 1 is out of range"},
		{name: "negative third", slots: [3]int{0, 1, -1}, want: "slot 2 is out of range"},
		{name: "large first", slots: [3]int{3, 1, 2}, want: "slot 0 is out of range"},
		{name: "large second", slots: [3]int{0, 3, 2}, want: "slot 1 is out of range"},
		{name: "large third", slots: [3]int{0, 1, 3}, want: "slot 2 is out of range"},
		{name: "duplicate zero one", slots: [3]int{0, 0, 2}, want: "slots must be distinct"},
		{name: "duplicate zero two", slots: [3]int{0, 1, 0}, want: "slots must be distinct"},
		{name: "duplicate one two", slots: [3]int{0, 1, 1}, want: "slots must be distinct"},
	} {
		t.Run(test.name, func(t *testing.T) {
			_, err := NewInversePlusReplacement(scheme, test.slots, PlusVariantSecondThirdFirst)
			if err == nil || !strings.Contains(err.Error(), test.want) {
				t.Fatalf("slots %v produced error %v, want text %q", test.slots, err, test.want)
			}
		})
	}
}

func TestNewInversePlusReplacementLeavesGlobalOutputPolicySeparate(t *testing.T) {
	outputs := testInversePlusOutputs(t, [2][3]int{{1, 2, 4}, {14, 7, 9}}, PlusVariantSecondThirdFirst)
	zero := packedTerm(t, ring.Z2, 0, 1, 1)
	scheme := mustScheme(t, []RankOneTerm{zero, outputs[0], outputs[1], outputs[2], outputs[0]})
	if err := ValidateNonzeroTerms(scheme); err == nil {
		t.Fatal("fixture unexpectedly passed global nonzero validation")
	}
	if err := ValidateDistinctTensors(scheme); err == nil {
		t.Fatal("fixture unexpectedly passed global distinctness validation")
	}
	replacement, err := NewInversePlusReplacement(scheme, [3]int{1, 2, 3}, PlusVariantSecondThirdFirst)
	if err != nil {
		t.Fatal(err)
	}
	if err := ValidateReplacement(scheme, replacement); err != nil {
		t.Fatal(err)
	}
}

func packedTermTriples(t *testing.T, r ring.Ring, triples [][3]int) []RankOneTerm {
	t.Helper()
	terms := make([]RankOneTerm, len(triples))
	for i, triple := range triples {
		terms[i] = packedTerm(t, r, triple[0], triple[1], triple[2])
	}
	return terms
}

func testInversePlusOutputs(t *testing.T, sources [2][3]int, variant PlusVariant) [3]RankOneTerm {
	t.Helper()
	sums := [3]int{}
	for mode := range 3 {
		sums[mode] = sources[0][mode] ^ sources[1][mode]
	}
	triples := [3][3]int{}
	switch variant {
	case PlusVariantSecondThirdFirst:
		triples = [3][3]int{
			{sources[0][0], sums[1], sources[0][2]},
			{sums[0], sources[1][1], sources[1][2]},
			{sources[0][0], sources[1][1], sums[2]},
		}
	case PlusVariantThirdFirstSecond:
		triples = [3][3]int{
			{sources[0][0], sources[0][1], sums[2]},
			{sources[1][0], sums[1], sources[1][2]},
			{sums[0], sources[0][1], sources[1][2]},
		}
	case PlusVariantFirstSecondThird:
		triples = [3][3]int{
			{sums[0], sources[0][1], sources[0][2]},
			{sources[1][0], sources[1][1], sums[2]},
			{sources[1][0], sums[1], sources[0][2]},
		}
	default:
		t.Fatalf("unsupported test variant %d", variant)
	}
	terms := packedTermTriples(t, ring.Z2, triples[:])
	return [3]RankOneTerm{terms[0], terms[1], terms[2]}
}
