package main

import (
	"bytes"
	"io"
	"os"
	"os/exec"
	"path/filepath"
	"reflect"
	"strings"
	"testing"

	"patel.codes/proofs/internal/ring"
	"patel.codes/proofs/internal/tensor"
)

func TestRunHelpAndExplicitDomain(t *testing.T) {
	for _, argument := range []string{"-h", "--help"} {
		var stdout, stderr bytes.Buffer
		if err := run([]string{argument}, strings.NewReader(""), &stdout, &stderr); err != nil {
			t.Fatalf("run(%q): %v", argument, err)
		}
		if stdout.String() != usage || stderr.Len() != 0 {
			t.Fatalf("run(%q) stdout=%q stderr=%q", argument, stdout.String(), stderr.String())
		}
	}

	for _, test := range []struct {
		args []string
		want string
	}{
		{args: nil, want: "explicit domain"},
		{args: []string{"validate"}, want: "explicit domain"},
		{args: []string{"validate", "Z2"}, want: "unsupported domain"},
		{args: []string{"unknown", "z2"}, want: "unknown command"},
	} {
		var stdout, stderr bytes.Buffer
		err := run(test.args, strings.NewReader(""), &stdout, &stderr)
		if err == nil || !strings.Contains(err.Error(), test.want) {
			t.Fatalf("run(%v) error = %v, want %q", test.args, err, test.want)
		}
		if stdout.Len() != 0 {
			t.Fatalf("run(%v) stdout = %q", test.args, stdout.String())
		}
		if test.want != "unsupported domain" && stderr.String() != usage {
			t.Fatalf("run(%v) stderr = %q, want usage", test.args, stderr.String())
		}
	}
}

func TestRunValidateChecksAreExplicitAndSeparate(t *testing.T) {
	valid := "1 1 1 1\n1\n1\n1\n"
	var stdout, stderr bytes.Buffer
	if err := run([]string{"validate", "z2"}, strings.NewReader(valid), &stdout, &stderr); err != nil {
		t.Fatal(err)
	}
	const want = "{\n  \"domain\": \"z2\",\n  \"dimensions\": [\n    1,\n    1,\n    1\n  ],\n  \"terms\": 1,\n  \"checks\": {\n    \"brent\": true,\n    \"nonzero_terms\": true,\n    \"distinct_rank_one_tensors\": true\n  }\n}\n"
	if stdout.String() != want || stderr.Len() != 0 {
		t.Fatalf("validate stdout=%q stderr=%q", stdout.String(), stderr.String())
	}

	cases := []struct {
		name   string
		source string
		want   string
	}{
		{name: "Brent", source: "1 1 1 0\n\n\n\n", want: "Brent check"},
		{name: "nonzero", source: "1 1 1 2\n1 0\n1 1\n1 1\n", want: "nonzero-term check"},
		{name: "distinct", source: "1 1 1 3\n1 1 1\n1 1 1\n1 1 1\n", want: "distinct-rank-one-tensor check"},
	}
	for _, test := range cases {
		t.Run(test.name, func(t *testing.T) {
			stdout.Reset()
			stderr.Reset()
			err := run([]string{"validate", "z2"}, strings.NewReader(test.source), &stdout, &stderr)
			if err == nil || !strings.Contains(err.Error(), test.want) {
				t.Fatalf("validate error = %v, want %q", err, test.want)
			}
			if stdout.Len() != 0 || stderr.Len() != 0 {
				t.Fatalf("failed validate stdout=%q stderr=%q", stdout.String(), stderr.String())
			}
		})
	}
}

func TestRunValidateGenuinelyUsesZ3(t *testing.T) {
	const source = "1 1 1 1\n2\n2\n1\n"
	var stdout, stderr bytes.Buffer
	if err := run([]string{"validate", "z3"}, strings.NewReader(source), &stdout, &stderr); err != nil {
		t.Fatal(err)
	}
	const want = "{\n  \"domain\": \"z3\",\n  \"dimensions\": [\n    1,\n    1,\n    1\n  ],\n  \"terms\": 1,\n  \"checks\": {\n    \"brent\": true,\n    \"nonzero_terms\": true,\n    \"distinct_rank_one_tensors\": true\n  }\n}\n"
	if stdout.String() != want || stderr.Len() != 0 {
		t.Fatalf("validate z3 stdout=%q stderr=%q", stdout.String(), stderr.String())
	}
	stdout.Reset()
	if err := run([]string{"validate", "z2"}, strings.NewReader(source), &stdout, &stderr); err == nil {
		t.Fatal("Z3-distinguishing source unexpectedly validated over Z2")
	}
	if stdout.Len() != 0 || stderr.Len() != 0 {
		t.Fatalf("failed Z2 validation stdout=%q stderr=%q", stdout.String(), stderr.String())
	}
}

func TestRunExplainStableDiagnostic(t *testing.T) {
	source := "1 1 1 2\n1 0\n1 1\n1 1\n"
	var stdout, stderr bytes.Buffer
	if err := run([]string{"explain", "z2"}, strings.NewReader(source), &stdout, &stderr); err != nil {
		t.Fatal(err)
	}
	const want = "{\n  \"domain\": \"z2\",\n  \"dimensions\": [\n    1,\n    1,\n    1\n  ],\n  \"terms\": 2,\n  \"factors\": [\n    {\n      \"mode\": 0,\n      \"rows\": 1,\n      \"columns\": 1,\n      \"entries\": 2,\n      \"nonzero_entries\": 1,\n      \"zero_factors\": 1\n    },\n    {\n      \"mode\": 1,\n      \"rows\": 1,\n      \"columns\": 1,\n      \"entries\": 2,\n      \"nonzero_entries\": 2,\n      \"zero_factors\": 0\n    },\n    {\n      \"mode\": 2,\n      \"rows\": 1,\n      \"columns\": 1,\n      \"entries\": 2,\n      \"nonzero_entries\": 2,\n      \"zero_factors\": 0\n    }\n  ]\n}\n"
	if stdout.String() != want || stderr.Len() != 0 {
		t.Fatalf("explain stdout=%q stderr=%q", stdout.String(), stderr.String())
	}
}

func TestRunApplyUsesOneNamedConstructorAndPreservesOrder(t *testing.T) {
	source := packedPlusNative()
	var forward, reversed, stderr bytes.Buffer
	if err := run([]string{"apply", "z2", "plus", "0", "1"}, strings.NewReader(source), &forward, &stderr); err != nil {
		t.Fatal(err)
	}
	if stderr.Len() != 0 {
		t.Fatalf("apply stderr = %q", stderr.String())
	}
	stderr.Reset()
	if err := run([]string{"apply", "z2", "plus", "1", "0"}, strings.NewReader(source), &reversed, &stderr); err != nil {
		t.Fatal(err)
	}
	if forward.String() == reversed.String() {
		t.Fatal("reversing Plus source arguments did not change native output")
	}
	for name, output := range map[string]string{"forward": forward.String(), "reversed": reversed.String()} {
		scheme, err := tensor.ParseNative(ring.Z2, strings.NewReader(output))
		if err != nil {
			t.Fatalf("parse %s output: %v", name, err)
		}
		if scheme.TermCount() != 3 {
			t.Fatalf("%s term count = %d, want 3", name, scheme.TermCount())
		}
	}

	var stdout bytes.Buffer
	err := run([]string{"apply", "z2", "replacement", "0", "1"}, strings.NewReader(source), &stdout, &stderr)
	if err == nil || !strings.Contains(err.Error(), "unknown constructor") || stdout.Len() != 0 || stderr.String() != usage {
		t.Fatalf("raw replacement apply stdout=%q stderr=%q error=%v", stdout.String(), stderr.String(), err)
	}
}

func TestRunApplyOrdinaryFlipOverZ3(t *testing.T) {
	const source = "1 1 1 2\n1 1\n1 2\n1 2\n"
	var stdout, stderr bytes.Buffer
	if err := run([]string{"apply", "z3", "ordinary-flip", "first", "1", "0", "1"}, strings.NewReader(source), &stdout, &stderr); err != nil {
		t.Fatal(err)
	}
	const want = "1 1 1 2\n1 1\n0 1\n2 2\n"
	if stdout.String() != want || stderr.Len() != 0 {
		t.Fatalf("ordinary flip stdout=%q stderr=%q", stdout.String(), stderr.String())
	}
	result, err := tensor.ParseNative(ring.Z3, strings.NewReader(stdout.String()))
	if err != nil {
		t.Fatal(err)
	}
	if result.TermCount() != 2 {
		t.Fatalf("ordinary flip term count = %d, want 2", result.TermCount())
	}
}

func TestParseApplyStepAllConstructorKinds(t *testing.T) {
	cases := []struct {
		args []string
		kind string
	}{
		{args: []string{"plus", "3", "1"}, kind: "plus"},
		{args: []string{"ordinary-flip", "second", "7", "2", "-1"}, kind: "ordinary"},
		{args: []string{"inverse-plus", "third-first-second", "8", "3", "6"}, kind: "inverse"},
		{args: []string{"shared-factor", "third", "5", "0", "3"}, kind: "shared"},
	}
	for _, test := range cases {
		step, err := parseApplyStep(ring.Z3, test.args)
		if test.kind != "ordinary" {
			step, err = parseApplyStep(ring.Z2, test.args)
		}
		if err != nil {
			t.Fatalf("parseApplyStep(%v): %v", test.args, err)
		}
		switch test.kind {
		case "plus":
			if step.Plus == nil || *step.Plus != (tensor.PlusStep{P: 3, Q: 1}) {
				t.Fatalf("Plus step = %+v", step)
			}
		case "ordinary":
			want := tensor.OrdinaryFlipStep{Mode: tensor.SharedSecond, FirstSlot: 7, SecondSlot: 2, Coefficient: -1}
			if step.OrdinaryFlip == nil || *step.OrdinaryFlip != want {
				t.Fatalf("ordinary step = %+v", step)
			}
		case "inverse":
			want := tensor.InversePlusStep{OutputSlots: [3]int{8, 3, 6}, Variant: tensor.PlusVariantThirdFirstSecond}
			if step.InversePlus == nil || *step.InversePlus != want {
				t.Fatalf("inverse step = %+v", step)
			}
		case "shared":
			if step.SharedFactorReduction == nil || step.SharedFactorReduction.Mode != tensor.SharedThird || !reflect.DeepEqual(step.SharedFactorReduction.Slots, []int{5, 0, 3}) {
				t.Fatalf("shared step = %+v", step)
			}
		}
	}
}

func TestDocumentedModeAndVariantMappings(t *testing.T) {
	modes := []struct {
		text string
		want tensor.SharedMode
	}{
		{text: "first", want: tensor.SharedFirst},
		{text: "second", want: tensor.SharedSecond},
		{text: "third", want: tensor.SharedThird},
	}
	for _, test := range modes {
		got, err := parseMode(test.text)
		if err != nil || got != test.want {
			t.Fatalf("parseMode(%q) = %d, %v; want %d", test.text, got, err, test.want)
		}
		ordinary, err := parseApplyStep(ring.Z3, []string{"ordinary-flip", test.text, "0", "1", "1"})
		if err != nil || ordinary.OrdinaryFlip == nil || ordinary.OrdinaryFlip.Mode != test.want {
			t.Fatalf("ordinary-flip mode %q produced %+v, %v", test.text, ordinary, err)
		}
		shared, err := parseApplyStep(ring.Z2, []string{"shared-factor", test.text, "0", "1"})
		if err != nil || shared.SharedFactorReduction == nil || shared.SharedFactorReduction.Mode != test.want {
			t.Fatalf("shared-factor mode %q produced %+v, %v", test.text, shared, err)
		}
	}
	variants := []struct {
		text string
		want tensor.PlusVariant
	}{
		{text: "second-third-first", want: tensor.PlusVariantSecondThirdFirst},
		{text: "third-first-second", want: tensor.PlusVariantThirdFirstSecond},
		{text: "first-second-third", want: tensor.PlusVariantFirstSecondThird},
	}
	for _, test := range variants {
		got, err := parseVariant(test.text)
		if err != nil || got != test.want {
			t.Fatalf("parseVariant(%q) = %d, %v; want %d", test.text, got, err, test.want)
		}
		step, err := parseApplyStep(ring.Z2, []string{"inverse-plus", test.text, "0", "1", "2"})
		if err != nil || step.InversePlus == nil || step.InversePlus.Variant != test.want {
			t.Fatalf("inverse-plus variant %q produced %+v, %v", test.text, step, err)
		}
	}
}

func TestParseApplyStepRejectsIncompatibleDomainsAndAliases(t *testing.T) {
	for _, args := range [][]string{
		{"plus", "0", "1"},
		{"inverse-plus", "second-third-first", "0", "1", "2"},
		{"shared-factor", "first", "0", "1"},
	} {
		if _, err := parseApplyStep(ring.Z3, args); err == nil || !strings.Contains(err.Error(), "requires domain z2") {
			t.Fatalf("parseApplyStep(z3, %v) error = %v", args, err)
		}
	}
	for _, args := range [][]string{
		{"ordinary_flip", "first", "0", "1", "1"},
		{"ordinary-flip", "0", "0", "1", "1"},
		{"inverse-plus", "0", "0", "1", "2"},
	} {
		if _, err := parseApplyStep(ring.Z2, args); err == nil {
			t.Fatalf("parseApplyStep(%v) accepted undocumented alias", args)
		}
	}
}

func TestRunAnalyzeSharedExactJSON(t *testing.T) {
	const source = "1 2 1 3\n1 0 1 0 1 0\n1 0 0 1 1 0\n1 1 1\n"
	var stdout, stderr bytes.Buffer
	if err := run([]string{"analyze-shared", "z2"}, strings.NewReader(source), &stdout, &stderr); err != nil {
		t.Fatal(err)
	}
	const want = "{\n  \"domain\": \"z2\",\n  \"dimensions\": [\n    1,\n    2,\n    1\n  ],\n  \"terms\": 3,\n  \"classes\": [\n    {\n      \"mode\": 0,\n      \"slots\": [\n        0,\n        1,\n        2\n      ],\n      \"size\": 3,\n      \"complementary_rank\": 1,\n      \"defect\": 2\n    },\n    {\n      \"mode\": 1,\n      \"slots\": [\n        0,\n        2\n      ],\n      \"size\": 2,\n      \"complementary_rank\": 0,\n      \"defect\": 2\n    },\n    {\n      \"mode\": 2,\n      \"slots\": [\n        0,\n        1,\n        2\n      ],\n      \"size\": 3,\n      \"complementary_rank\": 1,\n      \"defect\": 2\n    }\n  ],\n  \"summary\": {\n    \"class_count\": 3,\n    \"positive_defect_classes\": 3,\n    \"maximum_individual_defect\": 2\n  }\n}\n"
	if stdout.String() != want || stderr.Len() != 0 {
		t.Fatalf("analyze-shared stdout=%q stderr=%q", stdout.String(), stderr.String())
	}
}

func TestRunAnalyzeSharedEmptyClassesAreArray(t *testing.T) {
	const source = "1 1 1 1\n1\n1\n1\n"
	var stdout, stderr bytes.Buffer
	if err := run([]string{"analyze-shared", "z2"}, strings.NewReader(source), &stdout, &stderr); err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(stdout.String(), "\"classes\": []") || stderr.Len() != 0 {
		t.Fatalf("analyze-shared stdout=%q stderr=%q", stdout.String(), stderr.String())
	}
}

func TestRunPreflightFailuresDoNotReadNativeInput(t *testing.T) {
	path := filepath.Join(t.TempDir(), "z2-trace.json")
	file, err := os.Create(path)
	if err != nil {
		t.Fatal(err)
	}
	writeErr := tensor.WriteTranscript(file, tensor.Transcript{
		Version:    tensor.TranscriptVersion,
		Ring:       ring.Z2,
		Dimensions: [3]int{1, 1, 1},
		Steps:      []tensor.TranscriptStep{},
	})
	closeErr := file.Close()
	if writeErr != nil || closeErr != nil {
		t.Fatalf("write transcript: %v; close: %v", writeErr, closeErr)
	}
	cases := []struct {
		name string
		args []string
	}{
		{name: "missing command", args: nil},
		{name: "invalid domain", args: []string{"validate", "Z2"}},
		{name: "incompatible analyzer", args: []string{"analyze-shared", "z3"}},
		{name: "analyzer extra argument", args: []string{"analyze-shared", "z2", "extra"}},
		{name: "incompatible constructor", args: []string{"apply", "z3", "plus", "0", "1"}},
		{name: "duplicate constructor slots", args: []string{"apply", "z2", "plus", "0", "0"}},
		{name: "invalid mode", args: []string{"apply", "z3", "ordinary-flip", "fourth", "0", "1", "1"}},
		{name: "replay domain mismatch", args: []string{"replay", "z3", path}},
	}
	for _, test := range cases {
		t.Run(test.name, func(t *testing.T) {
			reader := &failOnRead{}
			var stdout, stderr bytes.Buffer
			if err := run(test.args, reader, &stdout, &stderr); err == nil {
				t.Fatalf("run(%v) unexpectedly succeeded", test.args)
			}
			if reader.reads != 0 {
				t.Fatalf("run(%v) performed %d native reads", test.args, reader.reads)
			}
			if stdout.Len() != 0 {
				t.Fatalf("run(%v) stdout=%q", test.args, stdout.String())
			}
		})
	}
}

func TestRunReplayConsumesNativeAndTranscript(t *testing.T) {
	sourceText := packedPlusNative()
	source, err := tensor.ParseNative(ring.Z2, strings.NewReader(sourceText))
	if err != nil {
		t.Fatal(err)
	}
	transcriptValue, err := tensor.NewTranscript(source, []tensor.TranscriptStep{{Plus: &tensor.PlusStep{P: 0, Q: 1}}})
	if err != nil {
		t.Fatal(err)
	}
	path := filepath.Join(t.TempDir(), "trace.json")
	file, err := os.Create(path)
	if err != nil {
		t.Fatal(err)
	}
	writeErr := tensor.WriteTranscript(file, transcriptValue)
	closeErr := file.Close()
	if writeErr != nil || closeErr != nil {
		t.Fatalf("write transcript: %v; close: %v", writeErr, closeErr)
	}

	var replayed, applied, stderr bytes.Buffer
	if err := run([]string{"replay", "z2", path}, strings.NewReader(sourceText), &replayed, &stderr); err != nil {
		t.Fatal(err)
	}
	if err := run([]string{"apply", "z2", "plus", "0", "1"}, strings.NewReader(sourceText), &applied, &stderr); err != nil {
		t.Fatal(err)
	}
	if replayed.String() != applied.String() || stderr.Len() != 0 {
		t.Fatalf("replay=%q apply=%q stderr=%q", replayed.String(), applied.String(), stderr.String())
	}

	var stdout bytes.Buffer
	err = run([]string{"replay", "z3", path}, strings.NewReader("malformed"), &stdout, &stderr)
	if err == nil || !strings.Contains(err.Error(), "explicit domain 3 differs from transcript ring 2") || stdout.Len() != 0 {
		t.Fatalf("domain mismatch stdout=%q error=%v", stdout.String(), err)
	}
}

func TestRunReplayReportsCurrentStepIndex(t *testing.T) {
	sourceText := packedPlusNative()
	transcriptValue := tensor.Transcript{
		Version: tensor.TranscriptVersion, Ring: ring.Z2, Dimensions: [3]int{2, 2, 2},
		Steps: []tensor.TranscriptStep{
			{Plus: &tensor.PlusStep{P: 0, Q: 1}},
			{Plus: &tensor.PlusStep{P: 7, Q: 0}},
		},
	}
	path := filepath.Join(t.TempDir(), "bad-trace.json")
	file, err := os.Create(path)
	if err != nil {
		t.Fatal(err)
	}
	if err := tensor.WriteTranscript(file, transcriptValue); err != nil {
		t.Fatal(err)
	}
	if err := file.Close(); err != nil {
		t.Fatal(err)
	}
	var stdout, stderr bytes.Buffer
	err = run([]string{"replay", "z2", path}, strings.NewReader(sourceText), &stdout, &stderr)
	if err == nil || !strings.Contains(err.Error(), "transcript step 1 (plus)") || !strings.Contains(err.Error(), "7 for 3 terms") {
		t.Fatalf("replay step error = %v", err)
	}
	if stdout.Len() != 0 || stderr.Len() != 0 {
		t.Fatalf("failed replay stdout=%q stderr=%q", stdout.String(), stderr.String())
	}
}

func TestMainExitCodesAndStreams(t *testing.T) {
	path := filepath.Join(t.TempDir(), "trace.json")
	file, err := os.Create(path)
	if err != nil {
		t.Fatal(err)
	}
	writeErr := tensor.WriteTranscript(file, tensor.Transcript{
		Version:    tensor.TranscriptVersion,
		Ring:       ring.Z2,
		Dimensions: [3]int{1, 1, 1},
		Steps:      []tensor.TranscriptStep{},
	})
	closeErr := file.Close()
	if writeErr != nil || closeErr != nil {
		t.Fatalf("write transcript: %v; close: %v", writeErr, closeErr)
	}
	const validation = "{\n  \"domain\": \"z2\",\n  \"dimensions\": [\n    1,\n    1,\n    1\n  ],\n  \"terms\": 1,\n  \"checks\": {\n    \"brent\": true,\n    \"nonzero_terms\": true,\n    \"distinct_rank_one_tensors\": true\n  }\n}\n"
	cases := []struct {
		name        string
		args        []string
		stdin       string
		wantCode    int
		wantStdout  string
		wantStderr  string
		closeStderr bool
	}{
		{name: "help", args: []string{"--help"}, wantCode: 0, wantStdout: usage},
		{name: "usage failure", wantCode: 1, wantStderr: usage + "tensor: require a command and explicit domain\n"},
		{name: "malformed input", args: []string{"validate", "z2"}, stdin: "bad", wantCode: 1, wantStderr: "tensor: validate: parse z2 native source: native scheme has 1 lines, want 4\n"},
		{name: "success", args: []string{"validate", "z2"}, stdin: "1 1 1 1\n1\n1\n1\n", wantCode: 0, wantStdout: validation},
		{name: "replay failure", args: []string{"replay", "z3", path}, stdin: "unread", wantCode: 1, wantStderr: "tensor: replay: explicit domain 3 differs from transcript ring 2\n"},
		{name: "diagnostic write failure", args: []string{"validate", "Z2"}, wantCode: 2, closeStderr: true},
	}
	for _, test := range cases {
		t.Run(test.name, func(t *testing.T) {
			code, stdout, stderr := runMainProcess(t, test.args, test.stdin, test.closeStderr)
			if code != test.wantCode || stdout != test.wantStdout || stderr != test.wantStderr {
				t.Fatalf("main code=%d stdout=%q stderr=%q; want code=%d stdout=%q stderr=%q", code, stdout, stderr, test.wantCode, test.wantStdout, test.wantStderr)
			}
		})
	}
}

func TestTensorMainHelperProcess(t *testing.T) {
	if os.Getenv("TENSOR_MAIN_HELPER") != "1" {
		return
	}
	separator := -1
	for index, argument := range os.Args {
		if argument == "--" {
			separator = index
			break
		}
	}
	if separator < 0 {
		os.Exit(125)
	}
	if os.Getenv("TENSOR_MAIN_CLOSE_STDERR") == "1" {
		if err := os.Stderr.Close(); err != nil {
			os.Exit(126)
		}
	}
	os.Args = append([]string{"tensor"}, os.Args[separator+1:]...)
	main()
	os.Exit(0)
}

func runMainProcess(t *testing.T, args []string, stdin string, closeStderr bool) (int, string, string) {
	t.Helper()
	commandArgs := []string{"-test.run=^TestTensorMainHelperProcess$", "--"}
	commandArgs = append(commandArgs, args...)
	command := exec.Command(os.Args[0], commandArgs...)
	closeValue := "0"
	if closeStderr {
		closeValue = "1"
	}
	command.Env = append(os.Environ(), "TENSOR_MAIN_HELPER=1", "TENSOR_MAIN_CLOSE_STDERR="+closeValue)
	command.Stdin = strings.NewReader(stdin)
	var stdout, stderr bytes.Buffer
	command.Stdout = &stdout
	command.Stderr = &stderr
	err := command.Run()
	if err == nil {
		return 0, stdout.String(), stderr.String()
	}
	exitError, ok := err.(*exec.ExitError)
	if !ok {
		t.Fatalf("run helper process: %v", err)
	}
	return exitError.ExitCode(), stdout.String(), stderr.String()
}

func packedPlusNative() string {
	return "2 2 2 2\n1 0 0 1 0 0 1 1\n1 0 0 1 1 0 0 0\n1 0 0 1 0 1 0 1\n"
}

type failOnRead struct {
	reads int
}

func (reader *failOnRead) Read([]byte) (int, error) {
	reader.reads++
	return 0, io.ErrUnexpectedEOF
}
