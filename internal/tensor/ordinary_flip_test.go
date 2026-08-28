package tensor

import (
	"reflect"
	"strings"
	"testing"

	"patel.codes/proofs/internal/ring"
)

func TestOrdinaryFlipEveryModeWithRectangularFactors(t *testing.T) {
	dimensions := [3]int{2, 3, 1}
	complements := [3][2]int{{1, 2}, {0, 2}, {0, 1}}
	for mode := SharedFirst; mode <= SharedThird; mode++ {
		t.Run(string(rune('0'+mode)), func(t *testing.T) {
			firstEntries := [3][]int{
				{1, 0, 2, 1, 0, 2},
				{0, 1, 2},
				{2, 1},
			}
			secondEntries := [3][]int{
				{2, 1, 0, 2, 1, 0},
				{1, 2, 0},
				{1, 0},
			}
			secondEntries[int(mode)] = append([]int(nil), firstEntries[int(mode)]...)
			source := mustCyclicScheme(t, ring.Z3, dimensions, [][3][]int{firstEntries, secondEntries})
			replacement, err := NewOrdinaryFlipReplacement(source, mode, 0, 1, 2)
			if err != nil {
				t.Fatal(err)
			}
			if got, want := replacement.RemovedSlots(), []int{0, 1}; !reflect.DeepEqual(got, want) {
				t.Fatalf("removed slots = %v, want %v", got, want)
			}
			wantFirst := cloneFactorEntries(firstEntries)
			wantSecond := cloneFactorEntries(secondEntries)
			lower, higher := complements[int(mode)][0], complements[int(mode)][1]
			wantFirst[lower] = addScaledEntries(ring.Z3, firstEntries[lower], 2, secondEntries[lower])
			wantSecond[higher] = addScaledEntries(ring.Z3, secondEntries[higher], ring.Z3.Sub(0, 2), firstEntries[higher])
			want := [][3][]int{wantFirst, wantSecond}
			if got := replacementTermEntries(replacement); !reflect.DeepEqual(got, want) {
				t.Fatalf("mode %d inserted factors = %v, want %v", mode, got, want)
			}
			if err := ValidateReplacement(source, replacement); err != nil {
				t.Fatal(err)
			}
		})
	}
}

func TestOrdinaryFlipZ2StoredFactorOraclesEveryMode(t *testing.T) {
	dimensions := [3]int{2, 3, 1}
	first := [3][]int{
		{1, 0, 1, 1, 0, 0},
		{0, 1, 1},
		{1, 0},
	}
	tests := []struct {
		name   string
		mode   SharedMode
		second [3][]int
		want   [][3][]int
	}{
		{
			name: "first",
			mode: SharedFirst,
			second: [3][]int{
				{1, 0, 1, 1, 0, 0},
				{1, 1, 0},
				{0, 1},
			},
			want: [][3][]int{
				{{1, 0, 1, 1, 0, 0}, {1, 0, 1}, {1, 0}},
				{{1, 0, 1, 1, 0, 0}, {1, 1, 0}, {1, 1}},
			},
		},
		{
			name: "second",
			mode: SharedSecond,
			second: [3][]int{
				{0, 1, 1, 0, 1, 0},
				{0, 1, 1},
				{0, 1},
			},
			want: [][3][]int{
				{{1, 1, 0, 1, 1, 0}, {0, 1, 1}, {1, 0}},
				{{0, 1, 1, 0, 1, 0}, {0, 1, 1}, {1, 1}},
			},
		},
		{
			name: "third",
			mode: SharedThird,
			second: [3][]int{
				{0, 1, 1, 0, 1, 0},
				{1, 1, 0},
				{1, 0},
			},
			want: [][3][]int{
				{{1, 1, 0, 1, 1, 0}, {0, 1, 1}, {1, 0}},
				{{0, 1, 1, 0, 1, 0}, {1, 0, 1}, {1, 0}},
			},
		},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			source := mustCyclicScheme(t, ring.Z2, dimensions, [][3][]int{first, test.second})
			replacement, err := NewOrdinaryFlipReplacement(source, test.mode, 0, 1, 1)
			if err != nil {
				t.Fatal(err)
			}
			if got := replacementTermEntries(replacement); !reflect.DeepEqual(got, test.want) {
				t.Fatalf("inserted factors = %v, want %v", got, test.want)
			}
		})
	}
}

func TestOrdinaryFlipZ3CoefficientTwoUsesSubtraction(t *testing.T) {
	source := mustScheme(t, []RankOneTerm{
		scalarTerm(t, ring.Z3, 1, 0, 1),
		scalarTerm(t, ring.Z3, 1, 1, 0),
	})
	replacement, err := NewOrdinaryFlipReplacement(source, SharedFirst, 0, 1, 2)
	if err != nil {
		t.Fatal(err)
	}
	if got, want := scalarTermFactors(replacement.InsertedTerms()), [][3]int{{1, 2, 1}, {1, 1, 1}}; !reflect.DeepEqual(got, want) {
		t.Fatalf("inserted factors = %v, want %v", got, want)
	}
}

func TestOrdinaryFlipNormalizesCoefficientAtIntegerBoundaries(t *testing.T) {
	maxInt := int(^uint(0) >> 1)
	minInt := -maxInt - 1
	coefficients := []int{0, 1, 2, 3, -1, -2, -3, maxInt, minInt}
	for _, r := range []ring.Ring{ring.Z2, ring.Z3} {
		t.Run(string(rune('0'+r)), func(t *testing.T) {
			source := mustScheme(t, []RankOneTerm{
				scalarTerm(t, r, 1, 0, 1),
				scalarTerm(t, r, 1, 1, 0),
			})
			canonical := make(map[int][]RankOneTerm)
			for q := 1; q < int(r); q++ {
				replacement, err := NewOrdinaryFlipReplacement(source, SharedFirst, 0, 1, q)
				if err != nil {
					t.Fatal(err)
				}
				canonical[q] = replacement.InsertedTerms()
			}
			for _, coefficient := range coefficients {
				replacement, err := NewOrdinaryFlipReplacement(source, SharedFirst, 0, 1, coefficient)
				normalized := r.Normalize(coefficient)
				if normalized == 0 {
					if err == nil || !strings.Contains(err.Error(), "coefficient is zero") {
						t.Fatalf("coefficient %d produced error %v, want zero rejection", coefficient, err)
					}
					continue
				}
				if err != nil {
					t.Fatalf("coefficient %d normalized to %d: %v", coefficient, normalized, err)
				}
				if got := replacement.InsertedTerms(); !reflect.DeepEqual(got, canonical[normalized]) {
					t.Fatalf("coefficient %d result = %v, want canonical %d result %v", coefficient, replacementTermEntries(replacement), normalized, termListEntries(canonical[normalized]))
				}
			}
		})
	}
}

func TestOrdinaryFlipOrderedSlotsAndSortedRemoval(t *testing.T) {
	source := mustScheme(t, []RankOneTerm{
		scalarTerm(t, ring.Z3, 1, 1, 1),
		scalarTerm(t, ring.Z3, 1, 2, 2),
	})
	forward, err := NewOrdinaryFlipReplacement(source, SharedFirst, 0, 1, 1)
	if err != nil {
		t.Fatal(err)
	}
	reversed, err := NewOrdinaryFlipReplacement(source, SharedFirst, 1, 0, 1)
	if err != nil {
		t.Fatal(err)
	}
	if got, want := reversed.RemovedSlots(), []int{0, 1}; !reflect.DeepEqual(got, want) {
		t.Fatalf("removed slots = %v, want %v", got, want)
	}
	if got, want := scalarTermFactors(forward.InsertedTerms()), [][3]int{{1, 0, 1}, {1, 2, 1}}; !reflect.DeepEqual(got, want) {
		t.Fatalf("forward inserted factors = %v, want %v", got, want)
	}
	if got, want := scalarTermFactors(reversed.InsertedTerms()), [][3]int{{1, 0, 2}, {1, 1, 2}}; !reflect.DeepEqual(got, want) {
		t.Fatalf("reversed inserted factors = %v, want %v", got, want)
	}
}

func TestOrdinaryFlipInverseReplayAcrossRingsAndModes(t *testing.T) {
	dimensions := [3]int{2, 2, 2}
	for _, r := range []ring.Ring{ring.Z2, ring.Z3} {
		for mode := SharedFirst; mode <= SharedThird; mode++ {
			t.Run(string(rune('0'+r))+string(rune('0'+mode)), func(t *testing.T) {
				firstEntries := [3][]int{
					{1, 0, 0, 1},
					{1, 1, 0, 0},
					{1, 0, 1, 0},
				}
				secondEntries := [3][]int{
					{0, 1, 1, 0},
					{0, 1, 0, 1},
					{0, 0, 1, 1},
				}
				secondEntries[int(mode)] = append([]int(nil), firstEntries[int(mode)]...)
				survivorEntries := [3][]int{
					{1, 1, 0, 0},
					{0, 0, 1, 1},
					{1, 0, 0, 1},
				}
				first := mustCyclicScheme(t, r, dimensions, [][3][]int{firstEntries}).Term(0)
				second := mustCyclicScheme(t, r, dimensions, [][3][]int{secondEntries}).Term(0)
				survivor := mustCyclicScheme(t, r, dimensions, [][3][]int{survivorEntries}).Term(0)
				source := mustScheme(t, []RankOneTerm{second, survivor, first})
				q := 1
				if r == ring.Z3 {
					q = 2
				}
				forward, err := NewOrdinaryFlipReplacement(source, mode, 2, 0, q)
				if err != nil {
					t.Fatal(err)
				}
				child, err := ApplyReplacement(source, forward)
				if err != nil {
					t.Fatal(err)
				}
				inverse, err := NewOrdinaryFlipReplacement(child, mode, 1, 2, r.Sub(0, q))
				if err != nil {
					t.Fatal(err)
				}
				replayed, err := ApplyReplacement(child, inverse)
				if err != nil {
					t.Fatal(err)
				}
				want := [][3][]int{termEntries(survivor), termEntries(first), termEntries(second)}
				if got := schemeEntries(replayed); !reflect.DeepEqual(got, want) {
					t.Fatalf("replayed terms = %v, want survivor then operational pair %v", got, want)
				}
			})
		}
	}
}

func TestOrdinaryFlipRequiresLiteralNonzeroSharedMatrix(t *testing.T) {
	dimensions := [3]int{1, 2, 1}
	projective := mustCyclicScheme(t, ring.Z3, dimensions, [][3][]int{
		{{1, 0}, {1, 0}, {1}},
		{{2, 0}, {2, 0}, {1}},
	})
	if _, err := NewOrdinaryFlipReplacement(projective, SharedFirst, 0, 1, 1); err == nil || !strings.Contains(err.Error(), "literally equal") {
		t.Fatalf("projectively shared matrices produced error %v, want literal-equality rejection", err)
	}
	literal := mustCyclicScheme(t, ring.Z3, dimensions, [][3][]int{
		{{1, 0}, {1, 0}, {1}},
		{{1, 0}, {2, 0}, {1}},
	})
	if _, err := NewOrdinaryFlipReplacement(literal, SharedFirst, 0, 1, 1); err != nil {
		t.Fatalf("literal shared matrices were rejected: %v", err)
	}
	zero := mustCyclicScheme(t, ring.Z3, dimensions, [][3][]int{
		{{0, 0}, {1, 0}, {1}},
		{{0, 0}, {2, 0}, {1}},
	})
	if _, err := NewOrdinaryFlipReplacement(zero, SharedFirst, 0, 1, 1); err == nil || !strings.Contains(err.Error(), "shared matrix at mode 0 is zero") {
		t.Fatalf("zero shared matrix produced error %v", err)
	}
}

func TestOrdinaryFlipAllowsDegenerateExactOutput(t *testing.T) {
	for _, test := range []struct {
		r     ring.Ring
		q     int
		terms [][3]int
	}{
		{r: ring.Z2, q: 1, terms: [][3]int{{1, 1, 1}, {1, 1, 1}}},
		{r: ring.Z3, q: 2, terms: [][3]int{{1, 1, 1}, {1, 1, 2}}},
	} {
		source := mustScheme(t, []RankOneTerm{
			scalarTerm(t, test.r, test.terms[0][0], test.terms[0][1], test.terms[0][2]),
			scalarTerm(t, test.r, test.terms[1][0], test.terms[1][1], test.terms[1][2]),
		})
		replacement, err := NewOrdinaryFlipReplacement(source, SharedFirst, 0, 1, test.q)
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
		if err := ValidateNonzeroTerms(child); err == nil {
			t.Fatalf("degenerate child over ring %d unexpectedly passed nonzero validation", test.r)
		}
	}
}

func TestOrdinaryFlipLeavesSurvivorCollisionToSeparateValidation(t *testing.T) {
	dimensions := [3]int{1, 2, 2}
	shared := []int{1, 0}
	firstLower := []int{1, 0, 0, 0}
	secondLower := []int{0, 1, 0, 0}
	firstHigher := []int{1, 0}
	secondHigher := []int{0, 1}
	survivorLower := []int{1, 1, 0, 0}
	source := mustCyclicScheme(t, ring.Z2, dimensions, [][3][]int{
		{shared, survivorLower, firstHigher},
		{shared, firstLower, firstHigher},
		{shared, secondLower, secondHigher},
	})
	if err := ValidateDistinctTensors(source); err != nil {
		t.Fatal(err)
	}
	replacement, err := NewOrdinaryFlipReplacement(source, SharedFirst, 1, 2, 1)
	if err != nil {
		t.Fatal(err)
	}
	child, err := ApplyReplacement(source, replacement)
	if err != nil {
		t.Fatal(err)
	}
	if err := ValidateNonzeroTerms(child); err != nil {
		t.Fatal(err)
	}
	if err := ValidateDistinctTensors(child); err == nil {
		t.Fatal("survivor collision unexpectedly passed distinctness validation")
	}
}

func TestOrdinaryFlipProducesValidGraphNeighbor(t *testing.T) {
	source := standardM2(t, ring.Z2)
	replacement, err := NewOrdinaryFlipReplacement(source, SharedFirst, 0, 2, 1)
	if err != nil {
		t.Fatal(err)
	}
	neighbor, err := ApplyReplacement(source, replacement)
	if err != nil {
		t.Fatal(err)
	}
	if err := ValidateBrent(neighbor); err != nil {
		t.Fatal(err)
	}
	if err := ValidateNonzeroTerms(neighbor); err != nil {
		t.Fatal(err)
	}
	if err := ValidateDistinctTensors(neighbor); err != nil {
		t.Fatal(err)
	}
}

func TestOrdinaryFlipErrorsAndPrecedence(t *testing.T) {
	valid := mustScheme(t, []RankOneTerm{
		scalarTerm(t, ring.Z3, 1, 1, 1),
		scalarTerm(t, ring.Z3, 1, 2, 2),
	})
	unequal := mustScheme(t, []RankOneTerm{
		scalarTerm(t, ring.Z3, 1, 1, 1),
		scalarTerm(t, ring.Z3, 2, 2, 2),
	})
	zeroFirst := mustScheme(t, []RankOneTerm{
		scalarTerm(t, ring.Z3, 0, 1, 1),
		scalarTerm(t, ring.Z3, 1, 2, 2),
	})
	tests := []struct {
		name        string
		scheme      Scheme
		mode        SharedMode
		first       int
		second      int
		coefficient int
		want        string
	}{
		{name: "source before mode", scheme: Scheme{}, mode: SharedMode(-1), first: -1, second: -1, coefficient: 0, want: "source scheme"},
		{name: "negative mode", scheme: valid, mode: SharedMode(-1), first: -1, second: -1, coefficient: 0, want: "mode is unsupported"},
		{name: "large mode", scheme: valid, mode: SharedMode(3), first: -1, second: -1, coefficient: 0, want: "mode is unsupported"},
		{name: "first before second", scheme: valid, mode: SharedFirst, first: -1, second: 2, coefficient: 0, want: "first slot is out of range"},
		{name: "large first", scheme: valid, mode: SharedFirst, first: 2, second: -1, coefficient: 0, want: "first slot is out of range"},
		{name: "second", scheme: valid, mode: SharedFirst, first: 0, second: -1, coefficient: 0, want: "second slot is out of range"},
		{name: "large second", scheme: valid, mode: SharedFirst, first: 0, second: 2, coefficient: 0, want: "second slot is out of range"},
		{name: "distinct before coefficient", scheme: valid, mode: SharedFirst, first: 0, second: 0, coefficient: 0, want: "slots must be distinct"},
		{name: "coefficient before sharing", scheme: unequal, mode: SharedFirst, first: 0, second: 1, coefficient: 3, want: "coefficient is zero"},
		{name: "zero shared before equality", scheme: zeroFirst, mode: SharedFirst, first: 0, second: 1, coefficient: 1, want: "shared matrix at mode 0 is zero"},
		{name: "literal equality", scheme: unequal, mode: SharedFirst, first: 0, second: 1, coefficient: 1, want: "literally equal"},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			_, err := NewOrdinaryFlipReplacement(test.scheme, test.mode, test.first, test.second, test.coefficient)
			if err == nil || !strings.Contains(err.Error(), test.want) {
				t.Fatalf("error = %v, want text %q", err, test.want)
			}
		})
	}
}

func TestOrdinaryFlipDoesNotMutateSourceOrReturnedData(t *testing.T) {
	source := mustCyclicScheme(t, ring.Z3, [3]int{2, 3, 1}, [][3][]int{
		{{1, 0, 2, 1, 0, 2}, {0, 1, 2}, {2, 1}},
		{{1, 0, 2, 1, 0, 2}, {1, 2, 0}, {1, 0}},
	})
	before := schemeEntries(source)
	replacement, err := NewOrdinaryFlipReplacement(source, SharedFirst, 0, 1, 2)
	if err != nil {
		t.Fatal(err)
	}
	wantReplacement := replacementTermEntries(replacement)
	removed := replacement.RemovedSlots()
	removed[0] = 99
	inserted := replacement.InsertedTerms()
	inserted[0].factors[1].entries[0] = 99
	if got := schemeEntries(source); !reflect.DeepEqual(got, before) {
		t.Fatalf("source changed from %v to %v", before, got)
	}
	if got := replacementTermEntries(replacement); !reflect.DeepEqual(got, wantReplacement) {
		t.Fatalf("replacement changed from %v to %v", wantReplacement, got)
	}
	if got, want := replacement.RemovedSlots(), []int{0, 1}; !reflect.DeepEqual(got, want) {
		t.Fatalf("removed slots changed to %v, want %v", got, want)
	}
}

func cloneFactorEntries(entries [3][]int) [3][]int {
	cloned := [3][]int{}
	for i := range cloned {
		cloned[i] = append([]int(nil), entries[i]...)
	}
	return cloned
}

func addScaledEntries(r ring.Ring, base []int, coefficient int, addend []int) []int {
	entries := make([]int, len(base))
	for i := range entries {
		entries[i] = r.Add(base[i], r.Mul(coefficient, addend[i]))
	}
	return entries
}

func scalarTermFactors(terms []RankOneTerm) [][3]int {
	factors := make([][3]int, len(terms))
	for i, term := range terms {
		for mode := range 3 {
			factors[i][mode] = term.Factor(mode).At(0, 0)
		}
	}
	return factors
}

func termListEntries(terms []RankOneTerm) [][3][]int {
	entries := make([][3][]int, len(terms))
	for i, term := range terms {
		entries[i] = termEntries(term)
	}
	return entries
}
