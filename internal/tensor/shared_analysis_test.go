package tensor

import (
	"reflect"
	"strings"
	"testing"

	"patel.codes/proofs/internal/ring"
)

func TestAnalyzeSharedFactorsAllModesRectangularAndDefectZero(t *testing.T) {
	dimensions := [3]int{2, 3, 4}
	terms := [][3][]int{
		{unitVector(6, 0), unitVector(12, 0), unitVector(8, 0)},
		{unitVector(6, 0), unitVector(12, 1), unitVector(8, 1)},
		{unitVector(6, 2), unitVector(12, 2), unitVector(8, 2)},
		{unitVector(6, 3), unitVector(12, 2), unitVector(8, 3)},
		{unitVector(6, 4), unitVector(12, 4), unitVector(8, 4)},
		{unitVector(6, 5), unitVector(12, 5), unitVector(8, 4)},
	}
	source := mustCyclicScheme(t, ring.Z2, dimensions, terms)
	before := schemeEntries(source)
	analysis, err := AnalyzeSharedFactors(source)
	if err != nil {
		t.Fatal(err)
	}
	classes := analysis.Classes()
	if got, want := len(classes), 3; got != want {
		t.Fatalf("class count = %d, want %d", got, want)
	}
	for index, class := range classes {
		if got, want := class.Mode(), SharedMode(index); got != want {
			t.Fatalf("class %d mode = %d, want %d", index, got, want)
		}
		if got, want := class.Slots(), []int{2 * index, 2*index + 1}; !reflect.DeepEqual(got, want) {
			t.Fatalf("class %d slots = %v, want %v", index, got, want)
		}
		if got, want := class.ComplementaryRank(), 2; got != want {
			t.Fatalf("class %d rank = %d, want %d", index, got, want)
		}
		if got := class.Defect(); got != 0 {
			t.Fatalf("class %d defect = %d, want 0", index, got)
		}
		if step, ok := class.ReductionStep(); ok {
			t.Fatalf("class %d unexpectedly produced reduction step %+v", index, step)
		}
	}
	if got := schemeEntries(source); !reflect.DeepEqual(got, before) {
		t.Fatalf("source changed from %v to %v", before, got)
	}
}

func TestAnalyzeSharedFactorsStableWithinModeAndCopySafety(t *testing.T) {
	dimensions := [3]int{2, 3, 4}
	first := []int{1, 1, 0, 0, 0, 0}
	second := []int{0, 0, 1, 1, 0, 0}
	terms := [][3][]int{
		{first, unitVector(12, 0), unitVector(8, 0)},
		{second, unitVector(12, 1), unitVector(8, 1)},
		{second, unitVector(12, 2), unitVector(8, 2)},
		{first, unitVector(12, 3), unitVector(8, 3)},
	}
	source := mustCyclicScheme(t, ring.Z2, dimensions, terms)
	analysis, err := AnalyzeSharedFactors(source)
	if err != nil {
		t.Fatal(err)
	}
	classes := analysis.Classes()
	if got, want := len(classes), 2; got != want {
		t.Fatalf("class count = %d, want %d", got, want)
	}
	if got, want := classes[0].Slots(), []int{0, 3}; !reflect.DeepEqual(got, want) {
		t.Fatalf("first slots = %v, want %v", got, want)
	}
	if got, want := classes[1].Slots(), []int{1, 2}; !reflect.DeepEqual(got, want) {
		t.Fatalf("second slots = %v, want %v", got, want)
	}

	slots := classes[0].Slots()
	slots[0] = 99
	classes[0].slots[0] = 98
	classes = append(classes[:0], classes[1:]...)
	again := analysis.Classes()
	if got, want := again[0].Slots(), []int{0, 3}; !reflect.DeepEqual(got, want) {
		t.Fatalf("copied analysis slots = %v, want %v", got, want)
	}
}

func TestAnalyzeSharedFactorsPositiveDefectAndReductionStep(t *testing.T) {
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
	analysis, err := AnalyzeSharedFactors(source)
	if err != nil {
		t.Fatal(err)
	}
	var found *SharedFactorClass
	for _, class := range analysis.Classes() {
		if class.Mode() == SharedFirst && reflect.DeepEqual(class.Slots(), []int{0, 2, 3, 4}) {
			value := class
			found = &value
			break
		}
	}
	if found == nil {
		t.Fatal("missing maximal first-mode class")
	}
	if got, want := found.ComplementaryRank(), 1; got != want {
		t.Fatalf("rank = %d, want %d", got, want)
	}
	if got, want := found.Defect(), 3; got != want {
		t.Fatalf("defect = %d, want %d", got, want)
	}
	step, ok := found.ReductionStep()
	if !ok {
		t.Fatal("positive-defect class did not produce a reduction step")
	}
	step.Slots[0] = 99
	step, _ = found.ReductionStep()
	if got, want := step.Slots, []int{0, 2, 3, 4}; !reflect.DeepEqual(got, want) {
		t.Fatalf("copied step slots = %v, want %v", got, want)
	}
	result, err := ApplyTranscriptStep(source, TranscriptStep{SharedFactorReduction: &step})
	if err != nil {
		t.Fatal(err)
	}
	if got, want := result.TermCount(), 2; got != want {
		t.Fatalf("result terms = %d, want %d", got, want)
	}
}

func TestAnalyzeSharedFactorsRankZeroAndZeroSharedFactorPolicy(t *testing.T) {
	dimensions := [3]int{1, 2, 1}
	terms := [][3][]int{
		{{0, 0}, []int{1, 0}, []int{1}},
		{{0, 0}, []int{1, 0}, []int{1}},
	}
	source := mustCyclicScheme(t, ring.Z2, dimensions, terms)
	analysis, err := AnalyzeSharedFactors(source)
	if err != nil {
		t.Fatal(err)
	}
	classes := analysis.Classes()
	for _, class := range classes {
		if class.Mode() == SharedFirst {
			t.Fatalf("zero shared factors produced class %+v", class)
		}
	}
	if got, want := len(classes), 2; got != want {
		t.Fatalf("nonzero class count = %d, want %d", got, want)
	}
	for _, class := range classes {
		if got := class.ComplementaryRank(); got != 0 {
			t.Fatalf("mode %d rank = %d, want 0", class.Mode(), got)
		}
		if got, want := class.Defect(), 2; got != want {
			t.Fatalf("mode %d defect = %d, want %d", class.Mode(), got, want)
		}
		step, ok := class.ReductionStep()
		if !ok {
			t.Fatalf("mode %d rank-zero class has no step", class.Mode())
		}
		if _, err := NewSharedFactorReduction(source, step.Mode, step.Slots); err != nil {
			t.Fatalf("mode %d reduction: %v", class.Mode(), err)
		}
	}
}

func TestAnalyzeSharedFactorsRejectsRingAndInvalidStructure(t *testing.T) {
	dimensions := [3]int{1, 2, 1}
	z3 := mustCyclicScheme(t, ring.Z3, dimensions, [][3][]int{
		{{1, 0}, []int{1, 0}, []int{1}},
		{{1, 0}, []int{0, 1}, []int{1}},
	})
	if _, err := AnalyzeSharedFactors(z3); err == nil || !strings.Contains(err.Error(), "requires ring Z2") {
		t.Fatalf("Z3 error = %v", err)
	}
	if _, err := AnalyzeSharedFactors(Scheme{}); err == nil || !strings.Contains(err.Error(), "source scheme") {
		t.Fatalf("invalid-structure error = %v", err)
	}

	invalid := mustCyclicScheme(t, ring.Z2, dimensions, [][3][]int{
		{{1, 0}, []int{1, 0}, []int{1}},
		{{1, 0}, []int{0, 1}, []int{1}},
	})
	invalid.terms[0].factors[0].entries = nil
	if _, err := AnalyzeSharedFactors(invalid); err == nil || !strings.Contains(err.Error(), "invalid storage") {
		t.Fatalf("corrupt-storage error = %v", err)
	}
}
