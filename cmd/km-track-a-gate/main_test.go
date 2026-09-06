package main

import (
	"path/filepath"
	"testing"

	"patel.codes/proofs/internal/tensor"
)

func TestAuthenticatedCorpusAndC567Regression(t *testing.T) {
	rootPath := filepath.Join("..", "c659-plusflip-cert", "testdata", "4x4x4_m47_c659_iteration5551_Z2.txt")
	root, binding, err := loadRoot(rootPath, "c659-root", 4524, "25f47b5f37d2b7351dd5a2c5da65ff8ef5ba80ce53239d46cdfdef37e6eef403", "f61518b4864995fe5ba43f1b52819cc563c4c74326442ae12bbc338a491027cb", "f2edf6735401e203b532cc85e0783fb47684815a3207b3ec601f8503c48956d1")
	if err != nil {
		t.Fatal(err)
	}
	if !binding.Authenticated {
		t.Fatal("root was not authenticated")
	}
	plus, err := constructPlus(root)
	if err != nil {
		t.Fatal(err)
	}
	plusBinding, err := bindConstructed("c659-plus-child", plus, "test", "0001430818e501c6964f6bf666e52a72cd0514605b3c69460e0d09cf80ec48e9")
	if err != nil {
		t.Fatal(err)
	}
	replacement, err := tensor.NewOrdinaryFlipReplacement(plus, tensor.SharedThird, 46, 47, 1)
	if err != nil {
		t.Fatal(err)
	}
	c567, err := tensor.ApplyReplacement(plus, replacement)
	if err != nil {
		t.Fatal(err)
	}
	c567Binding, err := bindConstructed("flip-output-2", c567, "test", "c567254223d480d8eaecde19d24f0aa96792208c41e2101a1270937bf1fe2934")
	if err != nil {
		t.Fatal(err)
	}
	states := []stateSpec{
		{ID: "c659-plus-child", Expected: plusBinding.CanonicalSHA256, Scheme: plus},
		{ID: "flip-output-2", Expected: c567Binding.CanonicalSHA256, Scheme: c567},
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
