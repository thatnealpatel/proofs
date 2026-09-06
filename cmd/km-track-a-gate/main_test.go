package main

import (
	"context"
	"fmt"
	"path/filepath"
	"testing"
	"time"

	"patel.codes/proofs/internal/tensor"
)

func TestAuthenticatedSevenStateGateEndToEnd(t *testing.T) {
	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()
	fixture := func(name string) string {
		return filepath.Join("..", "c659-plusflip-cert", "testdata", name)
	}
	c659, c659Binding, err := loadRoot(fixture("4x4x4_m47_c659_iteration5551_Z2.txt"), "c659-root", 4524, "25f47b5f37d2b7351dd5a2c5da65ff8ef5ba80ce53239d46cdfdef37e6eef403", "f61518b4864995fe5ba43f1b52819cc563c4c74326442ae12bbc338a491027cb", "f2edf6735401e203b532cc85e0783fb47684815a3207b3ec601f8503c48956d1")
	if err != nil {
		t.Fatal(err)
	}
	c680, c680Binding, err := loadRoot(fixture("4x4x4_m47_c680_iteration4356_Z2.txt"), "c680-root", 4524, "7e65a2fa888fcd9f32d9d68fd21ab8cdafeb4a39300cc77882def8e0115483e8", "f6e3264df6e1a8c39c0af212c0ee0b490c7d96b0169c21b131b4c496fe04889b", "021266950ca5db9dd40593da2ec85d043469c1a15c66a04a06c2dbe23813c598")
	if err != nil {
		t.Fatal(err)
	}
	if !c659Binding.Authenticated || !c680Binding.Authenticated {
		t.Fatal("roots were not authenticated")
	}
	plus, err := constructPlus(c659)
	if err != nil {
		t.Fatal(err)
	}
	plusBinding, err := bindConstructed("c659-plus-child", plus, "test", "0001430818e501c6964f6bf666e52a72cd0514605b3c69460e0d09cf80ec48e9")
	if err != nil {
		t.Fatal(err)
	}
	states := []stateSpec{
		{ID: "c659-root", Role: "zero-activation-control", Expected: c659Binding.CanonicalSHA256, Scheme: c659},
		{ID: "c680-root", Role: "zero-activation-control", Expected: c680Binding.CanonicalSHA256, Scheme: c680},
		{ID: "c659-plus-child", Role: "activation-corpus", Expected: plusBinding.CanonicalSHA256, Scheme: plus},
	}
	descriptors := []struct {
		first  int
		second int
		mode   tensor.SharedMode
		hash   string
	}{
		{45, 47, tensor.SharedFirst, "640392811b97cf64b2ccf0c382666ba1ea2b91b859f815d0c957574378da8c90"},
		{46, 47, tensor.SharedThird, "c567254223d480d8eaecde19d24f0aa96792208c41e2101a1270937bf1fe2934"},
		{47, 45, tensor.SharedFirst, "ee02607028804b19dbb6c075d2d290386dcb309cf740b826569b64550ebdddf0"},
		{47, 46, tensor.SharedThird, "cbf85f130f4bf6decd79785c85112135ab8e55a8aa745188383aeaa541171351"},
	}
	for index, descriptor := range descriptors {
		replacement, err := tensor.NewOrdinaryFlipReplacement(plus, descriptor.mode, descriptor.first, descriptor.second, 1)
		if err != nil {
			t.Fatal(err)
		}
		child, err := tensor.ApplyReplacement(plus, replacement)
		if err != nil {
			t.Fatal(err)
		}
		id := fmt.Sprintf("flip-output-%d", index+1)
		binding, err := bindConstructed(id, child, "test", descriptor.hash)
		if err != nil {
			t.Fatal(err)
		}
		states = append(states, stateSpec{ID: id, Role: "activation-corpus", Expected: binding.CanonicalSHA256, Scheme: child})
	}
	if len(states) != 7 {
		t.Fatalf("authenticated state count = %d, want 7", len(states))
	}

	rootHash := "f2edf6735401e203b532cc85e0783fb47684815a3207b3ec601f8503c48956d1"
	var enumerated, accepted, rejected uint64
	broad := 0
	positive := 0
	maximumClass := 0
	for _, state := range states {
		select {
		case <-ctx.Done():
			t.Fatal(ctx.Err())
		default:
		}
		report, err := scanState(state)
		if err != nil {
			t.Fatal(err)
		}
		for _, index := range report.Indexes {
			maximumClass = max(maximumClass, index.MaximumClassSize)
		}
		for _, scan := range report.Scans {
			enumerated += scan.Enumerated
			accepted += scan.Accepted
			rejected += scan.Rejected
		}
		for _, candidate := range report.Candidates {
			if candidate.Arity >= 2 && candidate.ChangedCount >= 2 && candidate.PredictedLengthMin >= 2 {
				broad++
			}
		}
		for _, class := range report.Classes {
			if class.Defect > 0 {
				positive++
				if class.ReductionEndpoint != rootHash {
					t.Fatalf("%s positive reduction endpoint = %s, want %s", state.ID, class.ReductionEndpoint, rootHash)
				}
			}
		}
	}
	if maximumClass > 2 {
		t.Fatalf("maximum common-factor class = %d, want <= 2", maximumClass)
	}
	if broad != 0 {
		t.Fatalf("broad candidates = %d, want 0", broad)
	}
	if enumerated != 48 || accepted != 8 || rejected != 40 {
		t.Fatalf("scanner totals = (%d,%d,%d), want (48,8,40)", enumerated, accepted, rejected)
	}
	if positive != 4 {
		t.Fatalf("positive analyzer reductions = %d, want 4", positive)
	}

	regression, err := replayC567Regression(states)
	if err != nil {
		t.Fatal(err)
	}
	if !regression.IndependentReplayPassed || regression.ChangedNativeMode != 2 || regression.Candidate.Arity != 1 || regression.Candidate.ChangedCount != 1 {
		t.Fatalf("unexpected regression: %+v", regression)
	}
	if regression.Candidate.Pivot != (triple{50360, 56576, 10405}) {
		t.Fatalf("pivot = %v", regression.Candidate.Pivot)
	}
	if len(regression.Candidate.Sources) != 1 || regression.Candidate.Sources[0] != (triple{50360, 56576, 273}) {
		t.Fatalf("sources = %v", regression.Candidate.Sources)
	}
	if len(regression.Candidate.Targets) != 1 || regression.Candidate.Targets[0] != (triple{50360, 56576, 10676}) {
		t.Fatalf("targets = %v", regression.Candidate.Targets)
	}
}
