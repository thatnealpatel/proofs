package tensor

import (
	"reflect"
	"strings"
	"testing"

	"patel.codes/proofs/internal/ring"
)

func TestSharedFactorReductionSharedModeSelectors(t *testing.T) {
	dimensions := [3]int{2, 2, 2}
	shared := []int{0, 1, 0, 0}
	left := []int{1, 0, 1, 0}
	right := []int{0, 1, 0, 0}
	otherRight := []int{1, 1, 0, 0}
	complementaryModes := [3][2]int{{1, 2}, {0, 2}, {0, 1}}
	for mode := SharedFirst; mode <= SharedThird; mode++ {
		t.Run(string(rune('0'+mode)), func(t *testing.T) {
			sharedMode := int(mode)
			leftMode := complementaryModes[sharedMode][0]
			rightMode := complementaryModes[sharedMode][1]
			first := [3][]int{}
			second := [3][]int{}
			first[sharedMode], second[sharedMode] = shared, shared
			first[leftMode], second[leftMode] = make([]int, 4), left
			first[rightMode], second[rightMode] = otherRight, right
			source := mustCyclicScheme(t, ring.Z2, dimensions, [][3][]int{first, second})

			replacement, err := NewSharedFactorReduction(source, mode, []int{0, 1})
			if err != nil {
				t.Fatal(err)
			}
			want := [3][]int{}
			want[sharedMode] = shared
			want[leftMode] = left
			want[rightMode] = right
			if got := replacementTermEntries(replacement); !reflect.DeepEqual(got, [][3][]int{want}) {
				t.Fatalf("mode %d inserted factors = %v, want %v", mode, got, [][3][]int{want})
			}
		})
	}
}

func TestSharedFactorReductionRectangularDeterministicFactorOrder(t *testing.T) {
	dimensions := [3]int{2, 3, 2}
	shared := unitVector(6, 5)
	terms := [][3][]int{
		{shared, unitVector(6, 0), []int{1, 1, 0, 0}},
		{shared, unitVector(6, 1), []int{1, 0, 1, 0}},
		{shared, unitVector(6, 2), []int{0, 1, 1, 0}},
	}
	source := mustCyclicScheme(t, ring.Z2, dimensions, terms)
	replacement, err := NewSharedFactorReduction(source, SharedFirst, []int{0, 1, 2})
	if err != nil {
		t.Fatal(err)
	}
	want := [][3][]int{
		{shared, []int{1, 0, 1, 0, 0, 0}, []int{1, 1, 0, 0}},
		{shared, []int{0, 1, 1, 0, 0, 0}, []int{1, 0, 1, 0}},
	}
	if got := replacementTermEntries(replacement); !reflect.DeepEqual(got, want) {
		t.Fatalf("inserted factors = %v, want %v", got, want)
	}
}

func TestSharedFactorReductionSecondModeUsesIncreasingComplementOrder(t *testing.T) {
	dimensions := [3]int{1, 2, 2}
	shared := []int{0, 0, 1, 0}
	terms := [][3][]int{
		{[]int{1, 0}, shared, []int{1, 1}},
		{[]int{0, 1}, shared, []int{1, 0}},
		{[]int{0, 0}, shared, []int{0, 1}},
	}
	source := mustCyclicScheme(t, ring.Z2, dimensions, terms)
	replacement, err := NewSharedFactorReduction(source, SharedSecond, []int{0, 1, 2})
	if err != nil {
		t.Fatal(err)
	}
	want := [][3][]int{
		{[]int{1, 0}, shared, []int{1, 1}},
		{[]int{0, 1}, shared, []int{1, 0}},
	}
	if got := replacementTermEntries(replacement); !reflect.DeepEqual(got, want) {
		t.Fatalf("inserted factors = %v, want %v", got, want)
	}
}

func TestSharedFactorReductionSortsCopiedSlotsAndSavesMultipleTerms(t *testing.T) {
	dimensions := [3]int{2, 2, 2}
	shared := unitVector(4, 3)
	right := unitVector(4, 2)
	otherShared := unitVector(4, 0)
	terms := [][3][]int{
		{shared, unitVector(4, 0), right},
		{otherShared, unitVector(4, 0), unitVector(4, 0)},
		{shared, unitVector(4, 1), right},
		{shared, unitVector(4, 2), right},
		{shared, unitVector(4, 3), right},
	}
	source := mustCyclicScheme(t, ring.Z2, dimensions, terms)
	before := schemeEntries(source)
	slots := []int{4, 0, 3, 2}
	replacement, err := NewSharedFactorReduction(source, SharedFirst, slots)
	if err != nil {
		t.Fatal(err)
	}
	if got, want := slots, []int{4, 0, 3, 2}; !reflect.DeepEqual(got, want) {
		t.Fatalf("input slots changed to %v, want %v", got, want)
	}
	if got, want := replacement.RemovedSlots(), []int{0, 2, 3, 4}; !reflect.DeepEqual(got, want) {
		t.Fatalf("removed slots = %v, want %v", got, want)
	}
	if got := replacement.InsertedTerms(); len(got) != 1 {
		t.Fatalf("inserted term count = %d, want 1", len(got))
	}
	if got := schemeEntries(source); !reflect.DeepEqual(got, before) {
		t.Fatalf("source changed from %v to %v", before, got)
	}
	child, err := ApplyReplacement(source, replacement)
	if err != nil {
		t.Fatal(err)
	}
	if got, want := child.TermCount(), 2; got != want {
		t.Fatalf("child term count = %d, want %d", got, want)
	}
}

func TestSharedFactorReductionRankZeroDeletesToEmptyScheme(t *testing.T) {
	dimensions := [3]int{1, 2, 1}
	term := [3][]int{{1, 0}, {1, 1}, {1}}
	source := mustCyclicScheme(t, ring.Z2, dimensions, [][3][]int{term, term})
	replacement, err := NewSharedFactorReduction(source, SharedFirst, []int{1, 0})
	if err != nil {
		t.Fatal(err)
	}
	if got := len(replacement.InsertedTerms()); got != 0 {
		t.Fatalf("inserted term count = %d, want 0", got)
	}
	child, err := ApplyReplacement(source, replacement)
	if err != nil {
		t.Fatal(err)
	}
	if child.TermCount() != 0 {
		t.Fatalf("child term count = %d, want 0", child.TermCount())
	}
	if got, want := child.Dimensions(), dimensions; got != want {
		t.Fatalf("child dimensions = %v, want %v", got, want)
	}
}

func TestSharedFactorReductionUsesArbitraryWidthBitsets(t *testing.T) {
	dimensions := [3]int{1, 2, 35}
	shared := unitVector(35, 34)
	right := make([]int, 70)
	right[0], right[69] = 1, 1
	terms := [][3][]int{
		{unitVector(2, 0), right, shared},
		{unitVector(2, 1), right, shared},
	}
	source := mustCyclicScheme(t, ring.Z2, dimensions, terms)
	replacement, err := NewSharedFactorReduction(source, SharedThird, []int{0, 1})
	if err != nil {
		t.Fatal(err)
	}
	inserted := replacement.InsertedTerms()
	if len(inserted) != 1 {
		t.Fatalf("inserted term count = %d, want 1", len(inserted))
	}
	if got, want := inserted[0].Factor(0).Entries(), []int{1, 1}; !reflect.DeepEqual(got, want) {
		t.Fatalf("left factor = %v, want %v", got, want)
	}
	if got := inserted[0].Factor(1).Entries(); !reflect.DeepEqual(got, right) {
		t.Fatalf("70-coordinate right factor = %v, want %v", got, right)
	}
}

func TestSharedFactorReductionUsesArbitraryWidthCoefficientBitsets(t *testing.T) {
	dimensions := [3]int{1, 1, 65}
	terms := make([][3][]int, 66)
	for i := range 65 {
		terms[i] = [3][]int{{1}, unitVector(65, i), unitVector(65, i)}
	}
	terms[65] = [3][]int{{1}, make([]int, 65), unitVector(65, 0)}
	source := mustCyclicScheme(t, ring.Z2, dimensions, terms)
	replacement, err := NewSharedFactorReduction(source, SharedFirst, []int{
		65, 64, 63, 62, 61, 60, 59, 58, 57, 56, 55, 54, 53, 52, 51, 50, 49,
		48, 47, 46, 45, 44, 43, 42, 41, 40, 39, 38, 37, 36, 35, 34, 33, 32,
		31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15,
		14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0,
	})
	if err != nil {
		t.Fatal(err)
	}
	inserted := replacement.InsertedTerms()
	if got, want := len(inserted), 65; got != want {
		t.Fatalf("inserted term count = %d, want %d", got, want)
	}
	if got, want := inserted[64].Factor(1).Entries(), unitVector(65, 64); !reflect.DeepEqual(got, want) {
		t.Fatalf("left factor 64 = %v, want %v", got, want)
	}
	if got, want := inserted[64].Factor(2).Entries(), unitVector(65, 64); !reflect.DeepEqual(got, want) {
		t.Fatalf("right factor 64 = %v, want %v", got, want)
	}
}

func TestSharedFactorReductionAllowsZeroComplementaryFactors(t *testing.T) {
	dimensions := [3]int{2, 2, 2}
	shared := []int{1, 0, 0, 1}
	left := []int{1, 0, 1, 0}
	right := []int{0, 1, 0, 0}
	zero := make([]int, 4)
	for _, test := range []struct {
		name  string
		first [3][]int
	}{
		{
			name:  "left",
			first: [3][]int{shared, zero, []int{1, 1, 0, 0}},
		},
		{
			name:  "right",
			first: [3][]int{shared, []int{0, 1, 1, 0}, zero},
		},
	} {
		t.Run(test.name, func(t *testing.T) {
			second := [3][]int{shared, left, right}
			source := mustCyclicScheme(t, ring.Z2, dimensions, [][3][]int{test.first, second})
			replacement, err := NewSharedFactorReduction(source, SharedFirst, []int{0, 1})
			if err != nil {
				t.Fatal(err)
			}
			want := [][3][]int{{shared, left, right}}
			if got := replacementTermEntries(replacement); !reflect.DeepEqual(got, want) {
				t.Fatalf("inserted factors = %v, want %v", got, want)
			}
		})
	}
}

func TestSharedFactorReductionRejectsInvalidInputs(t *testing.T) {
	dimensions := [3]int{1, 2, 1}
	shared := []int{1, 0}
	deficient := mustCyclicScheme(t, ring.Z2, dimensions, [][3][]int{
		{shared, []int{1, 0}, []int{1}},
		{shared, []int{0, 1}, []int{1}},
	})
	for _, test := range []struct {
		name  string
		mode  SharedMode
		slots []int
		want  string
	}{
		{name: "negative mode", mode: SharedMode(-1), slots: []int{0, 1}, want: "mode is unsupported"},
		{name: "large mode", mode: SharedMode(3), slots: []int{0, 1}, want: "mode is unsupported"},
		{name: "empty", mode: SharedFirst, slots: nil, want: "at least two slots"},
		{name: "one", mode: SharedFirst, slots: []int{0}, want: "at least two slots"},
		{name: "duplicate", mode: SharedFirst, slots: []int{1, 0, 1}, want: "duplicate"},
		{name: "negative", mode: SharedFirst, slots: []int{0, -1}, want: "out of range"},
		{name: "large", mode: SharedFirst, slots: []int{0, 2}, want: "out of range"},
	} {
		t.Run(test.name, func(t *testing.T) {
			_, err := NewSharedFactorReduction(deficient, test.mode, test.slots)
			if err == nil || !strings.Contains(err.Error(), test.want) {
				t.Fatalf("error = %v, want text %q", err, test.want)
			}
		})
	}

	z3 := mustCyclicScheme(t, ring.Z3, dimensions, [][3][]int{
		{shared, []int{1, 0}, []int{1}},
		{shared, []int{0, 1}, []int{1}},
	})
	if _, err := NewSharedFactorReduction(z3, SharedFirst, []int{0, 1}); err == nil {
		t.Fatal("accepted Z3")
	}
	if _, err := NewSharedFactorReduction(Scheme{}, SharedFirst, []int{0, 1}); err == nil {
		t.Fatal("accepted invalid scheme")
	}

	zeroShared := mustCyclicScheme(t, ring.Z2, dimensions, [][3][]int{
		{{0, 0}, []int{1, 0}, []int{1}},
		{{0, 0}, []int{0, 1}, []int{1}},
	})
	if _, err := NewSharedFactorReduction(zeroShared, SharedFirst, []int{0, 1}); err == nil {
		t.Fatal("accepted zero shared factor")
	}
	unequal := mustCyclicScheme(t, ring.Z2, dimensions, [][3][]int{
		{{1, 0}, []int{1, 0}, []int{1}},
		{{0, 1}, []int{0, 1}, []int{1}},
	})
	if _, err := NewSharedFactorReduction(unequal, SharedFirst, []int{0, 1}); err == nil {
		t.Fatal("accepted unequal shared factors")
	}

	nondeficientDimensions := [3]int{1, 2, 2}
	nondeficient := mustCyclicScheme(t, ring.Z2, nondeficientDimensions, [][3][]int{
		{{1, 0}, unitVector(4, 0), unitVector(2, 0)},
		{{1, 0}, unitVector(4, 1), unitVector(2, 1)},
	})
	if _, err := NewSharedFactorReduction(nondeficient, SharedFirst, []int{0, 1}); err == nil {
		t.Fatal("accepted non-deficient matrix")
	}
}

func unitVector(size, index int) []int {
	entries := make([]int, size)
	entries[index] = 1
	return entries
}

func mustCyclicScheme(t *testing.T, r ring.Ring, dimensions [3]int, entries [][3][]int) Scheme {
	t.Helper()
	terms := make([]RankOneTerm, len(entries))
	for i, factors := range entries {
		terms[i] = mustTerm(t,
			mustMatrix(t, r, dimensions[0], dimensions[1], factors[0]),
			mustMatrix(t, r, dimensions[1], dimensions[2], factors[1]),
			mustMatrix(t, r, dimensions[2], dimensions[0], factors[2]),
		)
	}
	return mustScheme(t, terms)
}

func replacementTermEntries(replacement Replacement) [][3][]int {
	terms := replacement.InsertedTerms()
	entries := make([][3][]int, len(terms))
	for i, term := range terms {
		entries[i] = termEntries(term)
	}
	return entries
}
