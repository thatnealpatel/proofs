package main

import (
	"reflect"
	"testing"
)

func TestShiftModeContracts(t *testing.T) {
	family := []uint{2}
	single, singleSweeps := shiftSweeps(family, 2, shiftSingleSweep)
	fixed, fixedSweeps := shiftSweeps(family, 2, shiftFixedPoint)
	want := []uint{1}
	if !reflect.DeepEqual(single, want) || !reflect.DeepEqual(fixed, want) {
		t.Fatalf("shift endpoints: single=%v fixed=%v want=%v", single, fixed, want)
	}
	if singleSweeps != 1 {
		t.Fatalf("single-sweep mode made %d sweeps, want 1", singleSweeps)
	}
	if fixedSweeps != 2 {
		t.Fatalf("fixed-point mode made %d sweeps, want changing pass plus stable pass", fixedSweeps)
	}

	stable, stableSweeps := shiftSweeps(want, 2, shiftFixedPoint)
	if !reflect.DeepEqual(stable, want) || stableSweeps != 1 {
		t.Fatalf("already-fixed family: result=%v sweeps=%d", stable, stableSweeps)
	}
}

func TestExactAndBudgetLimitedSunflower(t *testing.T) {
	family := []uint{3, 1, 2}
	if got := maxSunflowerExact(family); got != 2 {
		t.Fatalf("exact sunflower number=%d, want 2", got)
	}
	got, exact := maxSunflowerWithBudget(family, 1)
	if exact {
		t.Fatal("one-node sunflower search unexpectedly reported exact")
	}
	if got != 1 {
		t.Fatalf("budget-limited lower bound=%d, want deliberately incomplete bound 1", got)
	}
}

func TestFamilyBCalibration(t *testing.T) {
	family := buildFamilyB()
	tau, exact := maxSunflowerBudgeted(family)
	if tau != 2 || !exact {
		t.Fatalf("familyB tau=(%d,%v), want (2,true)", tau, exact)
	}
	shifted := shiftOneSweep(family, 20)
	shiftedTau, shiftedExact := maxSunflowerBudgeted(shifted)
	if shiftedTau != 17 || !shiftedExact {
		t.Fatalf("shifted familyB tau=(%d,%v), want (17,true)", shiftedTau, shiftedExact)
	}
	if !isFullStar(shifted, []int{0, 1, 2}, 17) {
		t.Fatal("single-sweep familyB endpoint is not the calibrated full star")
	}
}
