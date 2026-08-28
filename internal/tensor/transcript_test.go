package tensor

import (
	"bytes"
	"reflect"
	"strings"
	"testing"

	"patel.codes/proofs/internal/ring"
)

func TestTranscriptReplaysAllConstructorKinds(t *testing.T) {
	t.Run("plus", func(t *testing.T) {
		source := mustScheme(t, []RankOneTerm{
			packedTerm(t, ring.Z2, 12, 1, 10),
			packedTerm(t, ring.Z2, 9, 9, 9),
		})
		got := replaySteps(t, source, []TranscriptStep{{Plus: &PlusStep{P: 1, Q: 0}}})
		want := [][3]int{{9, 8, 9}, {5, 1, 10}, {9, 1, 3}}
		if terms := packedTerms(got.Terms()); !reflect.DeepEqual(terms, want) {
			t.Fatalf("replayed Plus terms = %v, want %v", terms, want)
		}
	})

	t.Run("ordinary flip modes", func(t *testing.T) {
		cases := []struct {
			name   string
			mode   SharedMode
			second [3]int
			want   [][3]int
		}{
			{name: "first", mode: SharedFirst, second: [3]int{1, 2, 2}, want: [][3]int{{1, 0, 1}, {1, 2, 1}}},
			{name: "second", mode: SharedSecond, second: [3]int{2, 1, 2}, want: [][3]int{{0, 1, 1}, {2, 1, 1}}},
			{name: "third", mode: SharedThird, second: [3]int{2, 2, 1}, want: [][3]int{{0, 1, 1}, {2, 1, 1}}},
		}
		for _, test := range cases {
			t.Run(test.name, func(t *testing.T) {
				source := mustScheme(t, []RankOneTerm{
					scalarTerm(t, ring.Z3, 1, 1, 1),
					scalarTerm(t, ring.Z3, test.second[0], test.second[1], test.second[2]),
				})
				got := replaySteps(t, source, []TranscriptStep{{OrdinaryFlip: &OrdinaryFlipStep{
					Mode: test.mode, FirstSlot: 0, SecondSlot: 1, Coefficient: 1,
				}}})
				if terms := scalarTermFactors(got.Terms()); !reflect.DeepEqual(terms, test.want) {
					t.Fatalf("replayed ordinary flip terms = %v, want %v", terms, test.want)
				}
			})
		}
	})

	t.Run("inverse Plus variants", func(t *testing.T) {
		sources := [2][3]int{{1, 2, 4}, {14, 7, 9}}
		cases := []struct {
			name    string
			variant PlusVariant
		}{
			{name: "second-third-first", variant: PlusVariantSecondThirdFirst},
			{name: "third-first-second", variant: PlusVariantThirdFirstSecond},
			{name: "first-second-third", variant: PlusVariantFirstSecondThird},
		}
		for _, test := range cases {
			t.Run(test.name, func(t *testing.T) {
				outputs := testInversePlusOutputs(t, sources, test.variant)
				source := mustScheme(t, []RankOneTerm{outputs[2], outputs[0], outputs[1]})
				got := replaySteps(t, source, []TranscriptStep{{InversePlus: &InversePlusStep{
					OutputSlots: [3]int{1, 2, 0}, Variant: test.variant,
				}}})
				if terms := packedTerms(got.Terms()); !reflect.DeepEqual(terms, sources[:]) {
					t.Fatalf("replayed inverse Plus terms = %v, want %v", terms, sources)
				}
			})
		}
	})

	t.Run("shared-factor reduction modes", func(t *testing.T) {
		base := [][3][]int{
			{unitVector(4, 3), unitVector(4, 0), unitVector(4, 0)},
			{unitVector(4, 0), unitVector(4, 0), unitVector(4, 0)},
			{unitVector(4, 3), unitVector(4, 0), unitVector(4, 0)},
			{unitVector(4, 3), unitVector(4, 1), unitVector(4, 2)},
		}
		cases := []struct {
			name string
			mode SharedMode
		}{
			{name: "first", mode: SharedFirst},
			{name: "second", mode: SharedSecond},
			{name: "third", mode: SharedThird},
		}
		for _, test := range cases {
			t.Run(test.name, func(t *testing.T) {
				rotated := make([][3][]int, len(base))
				for termIndex, term := range base {
					for oldMode := range 3 {
						rotated[termIndex][(oldMode+int(test.mode))%3] = term[oldMode]
					}
				}
				source := mustCyclicScheme(t, ring.Z2, [3]int{2, 2, 2}, rotated)
				got := replaySteps(t, source, []TranscriptStep{{SharedFactorReduction: &SharedFactorReductionStep{
					Mode: test.mode, Slots: []int{3, 0, 2},
				}}})
				baseInserted := [3]int{8, 2, 4}
				wantInserted := [3]int{}
				for oldMode := range 3 {
					wantInserted[(oldMode+int(test.mode))%3] = baseInserted[oldMode]
				}
				want := [][3]int{{1, 1, 1}, wantInserted}
				if terms := packedTerms(got.Terms()); !reflect.DeepEqual(terms, want) {
					t.Fatalf("replayed shared-factor terms = %v, want %v", terms, want)
				}
			})
		}
	})
}

func TestTranscriptMultiStepSlotsIndexCurrentScheme(t *testing.T) {
	first := packedTerm(t, ring.Z2, 1, 2, 4)
	survivor := packedTerm(t, ring.Z2, 3, 6, 10)
	second := packedTerm(t, ring.Z2, 14, 7, 9)
	source := mustScheme(t, []RankOneTerm{second, survivor, first})
	steps := []TranscriptStep{
		{Plus: &PlusStep{P: 2, Q: 0}},
		{InversePlus: &InversePlusStep{OutputSlots: [3]int{1, 2, 3}, Variant: PlusVariantSecondThirdFirst}},
	}
	got := replaySteps(t, source, steps)
	want := [][3]int{{3, 6, 10}, {1, 2, 4}, {14, 7, 9}}
	if terms := packedTerms(got.Terms()); !reflect.DeepEqual(terms, want) {
		t.Fatalf("multi-step terms = %v, want %v", terms, want)
	}

	mutated := cloneTranscriptSteps(steps)
	mutated[1].InversePlus.OutputSlots = [3]int{0, 1, 2}
	_, err := NewTranscript(source, mutated)
	if err == nil || !strings.Contains(err.Error(), "transcript step 1 (inverse_plus)") {
		t.Fatalf("mutated current slots produced error %v", err)
	}
}

func TestTranscriptPreservesOrderedArguments(t *testing.T) {
	source := mustScheme(t, []RankOneTerm{
		packedTerm(t, ring.Z2, 9, 9, 9),
		packedTerm(t, ring.Z2, 12, 1, 10),
	})
	forward := replaySteps(t, source, []TranscriptStep{{Plus: &PlusStep{P: 0, Q: 1}}})
	reversed := replaySteps(t, source, []TranscriptStep{{Plus: &PlusStep{P: 1, Q: 0}}})
	if reflect.DeepEqual(packedTerms(forward.Terms()), packedTerms(reversed.Terms())) {
		t.Fatal("reversing ordered Plus arguments did not change replay")
	}

	outputs := testInversePlusOutputs(t, [2][3]int{{1, 2, 4}, {14, 7, 9}}, PlusVariantSecondThirdFirst)
	inverseSource := mustScheme(t, []RankOneTerm{outputs[2], outputs[0], outputs[1]})
	bad := Transcript{
		Version: TranscriptVersion, Ring: ring.Z2, Dimensions: inverseSource.Dimensions(),
		Steps: []TranscriptStep{{InversePlus: &InversePlusStep{OutputSlots: [3]int{0, 2, 1}, Variant: PlusVariantSecondThirdFirst}}},
	}
	if _, err := ReplayTranscript(inverseSource, bad); err == nil || !strings.Contains(err.Error(), "transcript step 0 (inverse_plus)") {
		t.Fatalf("permuted inverse output positions produced error %v", err)
	}
}

func TestTranscriptStrictRoundTripAndStableEncoding(t *testing.T) {
	source := mustScheme(t, []RankOneTerm{
		packedTerm(t, ring.Z2, 9, 9, 9),
		packedTerm(t, ring.Z2, 12, 1, 10),
	})
	transcript, err := NewTranscript(source, []TranscriptStep{{Plus: &PlusStep{P: 0, Q: 1}}})
	if err != nil {
		t.Fatal(err)
	}
	var first bytes.Buffer
	if err := WriteTranscript(&first, transcript); err != nil {
		t.Fatal(err)
	}
	const want = "{\n  \"version\": 1,\n  \"ring\": 2,\n  \"dimensions\": [\n    2,\n    2,\n    2\n  ],\n  \"steps\": [\n    {\n      \"plus\": {\n        \"p\": 0,\n        \"q\": 1\n      }\n    }\n  ]\n}\n"
	if first.String() != want {
		t.Fatalf("encoded transcript = %q, want %q", first.String(), want)
	}
	parsed, err := ParseTranscript(strings.NewReader(first.String()))
	if err != nil {
		t.Fatal(err)
	}
	var second bytes.Buffer
	if err := WriteTranscript(&second, parsed); err != nil {
		t.Fatal(err)
	}
	if second.String() != first.String() {
		t.Fatalf("round trip changed transcript:\n%s\n%s", first.String(), second.String())
	}
}

func TestTranscriptRoundTripsEveryConstructorEncoding(t *testing.T) {
	transcript := Transcript{
		Version:    TranscriptVersion,
		Ring:       ring.Z2,
		Dimensions: [3]int{2, 2, 2},
		Steps: []TranscriptStep{
			{Plus: &PlusStep{P: 0, Q: 1}},
			{OrdinaryFlip: &OrdinaryFlipStep{Mode: SharedSecond, FirstSlot: 1, SecondSlot: 2, Coefficient: 1}},
			{InversePlus: &InversePlusStep{OutputSlots: [3]int{2, 0, 1}, Variant: PlusVariantFirstSecondThird}},
			{SharedFactorReduction: &SharedFactorReductionStep{Mode: SharedThird, Slots: []int{2, 0}}},
		},
	}
	var encoded bytes.Buffer
	if err := WriteTranscript(&encoded, transcript); err != nil {
		t.Fatal(err)
	}
	parsed, err := ParseTranscript(strings.NewReader(encoded.String()))
	if err != nil {
		t.Fatal(err)
	}
	if !reflect.DeepEqual(parsed, transcript) {
		t.Fatalf("parsed transcript = %#v, want %#v", parsed, transcript)
	}
}

func TestTranscriptDecodedOperationsReplayExactSchemes(t *testing.T) {
	t.Run("plus", func(t *testing.T) {
		source := mustScheme(t, []RankOneTerm{
			packedTerm(t, ring.Z2, 12, 1, 10),
			packedTerm(t, ring.Z2, 9, 9, 9),
		})
		got := replayDecodedSteps(t, source, []TranscriptStep{{Plus: &PlusStep{P: 1, Q: 0}}})
		want := mustScheme(t, []RankOneTerm{
			packedTerm(t, ring.Z2, 9, 8, 9),
			packedTerm(t, ring.Z2, 5, 1, 10),
			packedTerm(t, ring.Z2, 9, 1, 3),
		})
		if !reflect.DeepEqual(got, want) {
			t.Fatalf("decoded Plus replay = %#v, want %#v", got, want)
		}
	})

	t.Run("ordinary flip", func(t *testing.T) {
		source := mustScheme(t, []RankOneTerm{
			scalarTerm(t, ring.Z3, 1, 1, 1),
			scalarTerm(t, ring.Z3, 1, 2, 2),
		})
		got := replayDecodedSteps(t, source, []TranscriptStep{{OrdinaryFlip: &OrdinaryFlipStep{
			Mode: SharedFirst, FirstSlot: 0, SecondSlot: 1, Coefficient: 1,
		}}})
		want := mustScheme(t, []RankOneTerm{
			scalarTerm(t, ring.Z3, 1, 0, 1),
			scalarTerm(t, ring.Z3, 1, 2, 1),
		})
		if !reflect.DeepEqual(got, want) {
			t.Fatalf("decoded ordinary-flip replay = %#v, want %#v", got, want)
		}
	})

	t.Run("inverse Plus", func(t *testing.T) {
		sourceFactors := [2][3]int{{1, 2, 4}, {14, 7, 9}}
		outputs := testInversePlusOutputs(t, sourceFactors, PlusVariantThirdFirstSecond)
		source := mustScheme(t, []RankOneTerm{outputs[2], outputs[0], outputs[1]})
		got := replayDecodedSteps(t, source, []TranscriptStep{{InversePlus: &InversePlusStep{
			OutputSlots: [3]int{1, 2, 0}, Variant: PlusVariantThirdFirstSecond,
		}}})
		want := mustScheme(t, []RankOneTerm{
			packedTerm(t, ring.Z2, 1, 2, 4),
			packedTerm(t, ring.Z2, 14, 7, 9),
		})
		if !reflect.DeepEqual(got, want) {
			t.Fatalf("decoded inverse-Plus replay = %#v, want %#v", got, want)
		}
	})

	t.Run("shared-factor reduction", func(t *testing.T) {
		shared := unitVector(4, 3)
		right := unitVector(4, 2)
		source := mustCyclicScheme(t, ring.Z2, [3]int{2, 2, 2}, [][3][]int{
			{shared, unitVector(4, 0), right},
			{unitVector(4, 0), unitVector(4, 0), unitVector(4, 0)},
			{shared, unitVector(4, 1), right},
			{shared, unitVector(4, 2), right},
		})
		got := replayDecodedSteps(t, source, []TranscriptStep{{SharedFactorReduction: &SharedFactorReductionStep{
			Mode: SharedFirst, Slots: []int{3, 0, 2},
		}}})
		want := mustScheme(t, []RankOneTerm{
			packedTerm(t, ring.Z2, 1, 1, 1),
			packedTerm(t, ring.Z2, 8, 7, 4),
		})
		if !reflect.DeepEqual(got, want) {
			t.Fatalf("decoded shared-factor replay = %#v, want %#v", got, want)
		}
	})
}

func TestTranscriptStrictDecodingRejectsMutations(t *testing.T) {
	valid := `{"version":1,"ring":2,"dimensions":[2,2,2],"steps":[{"plus":{"p":0,"q":1}}]}`
	mutations := []struct {
		name string
		text string
		want string
	}{
		{name: "duplicate", text: `{"version":1,"ring":2,"ring":3,"dimensions":[2,2,2],"steps":[]}`, want: "duplicate object key"},
		{name: "unknown", text: `{"version":1,"ring":2,"dimensions":[2,2,2],"steps":[],"extra":0}`, want: "unknown field"},
		{name: "case folded top level", text: `{"Version":1,"ring":2,"dimensions":[2,2,2],"steps":[]}`, want: `unknown field "Version"`},
		{name: "semantic duplicate", text: `{"version":2,"Version":1,"ring":2,"dimensions":[2,2,2],"steps":[]}`, want: `unknown field "Version"`},
		{name: "case folded constructor", text: `{"version":1,"ring":2,"dimensions":[2,2,2],"steps":[{"Plus":{"p":0,"q":1}}]}`, want: `unknown field "Plus"`},
		{name: "case folded argument", text: `{"version":1,"ring":2,"dimensions":[2,2,2],"steps":[{"plus":{"P":0,"q":1}}]}`, want: `unknown field "P"`},
		{name: "unknown argument", text: `{"version":1,"ring":2,"dimensions":[2,2,2],"steps":[{"plus":{"p":0,"q":1,"extra":0}}]}`, want: `unknown field "extra"`},
		{name: "missing argument", text: `{"version":1,"ring":2,"dimensions":[2,2,2],"steps":[{"plus":{"p":1}}]}`, want: "requires p and q"},
		{name: "two constructors", text: `{"version":1,"ring":2,"dimensions":[2,2,2],"steps":[{"plus":{"p":0,"q":1},"ordinary_flip":{"mode":0,"first_slot":0,"second_slot":1,"coefficient":1}}]}`, want: "exactly one constructor"},
		{name: "null steps", text: `{"version":1,"ring":2,"dimensions":[2,2,2],"steps":null}`, want: "steps must be an array"},
		{name: "wrong dimensions length", text: `{"version":1,"ring":2,"dimensions":[2,2],"steps":[]}`, want: "length 2, want 3"},
		{name: "incompatible ring", text: `{"version":1,"ring":3,"dimensions":[2,2,2],"steps":[{"plus":{"p":0,"q":1}}]}`, want: "Plus requires ring Z2"},
		{name: "trailing", text: valid + `{}`, want: "trailing JSON value"},
	}
	for _, mutation := range mutations {
		t.Run(mutation.name, func(t *testing.T) {
			_, err := ParseTranscript(strings.NewReader(mutation.text))
			if err == nil || !strings.Contains(err.Error(), mutation.want) {
				t.Fatalf("ParseTranscript error = %v, want %q", err, mutation.want)
			}
		})
	}
}

func TestTranscriptStrictOperationPayloadSchemas(t *testing.T) {
	cases := []struct {
		name    string
		payload string
		want    string
	}{
		{name: "plus duplicate", payload: `"plus":{"p":0,"p":1,"q":1}`, want: "duplicate object key"},
		{name: "plus unknown", payload: `"plus":{"p":0,"q":1,"extra":0}`, want: `unknown field "extra"`},
		{name: "plus case folded", payload: `"plus":{"P":0,"q":1}`, want: `unknown field "P"`},
		{name: "plus missing", payload: `"plus":{"p":0}`, want: "Plus requires p and q"},
		{name: "ordinary flip duplicate", payload: `"ordinary_flip":{"mode":0,"mode":1,"first_slot":0,"second_slot":1,"coefficient":1}`, want: "duplicate object key"},
		{name: "ordinary flip unknown", payload: `"ordinary_flip":{"mode":0,"first_slot":0,"second_slot":1,"coefficient":1,"extra":0}`, want: `unknown field "extra"`},
		{name: "ordinary flip case folded", payload: `"ordinary_flip":{"Mode":0,"first_slot":0,"second_slot":1,"coefficient":1}`, want: `unknown field "Mode"`},
		{name: "ordinary flip missing", payload: `"ordinary_flip":{"mode":0,"first_slot":0,"second_slot":1}`, want: "ordinary flip requires"},
		{name: "inverse Plus duplicate", payload: `"inverse_plus":{"output_slots":[0,1,2],"variant":0,"variant":1}`, want: "duplicate object key"},
		{name: "inverse Plus unknown", payload: `"inverse_plus":{"output_slots":[0,1,2],"variant":0,"extra":0}`, want: `unknown field "extra"`},
		{name: "inverse Plus case folded", payload: `"inverse_plus":{"Output_slots":[0,1,2],"variant":0}`, want: `unknown field "Output_slots"`},
		{name: "inverse Plus missing", payload: `"inverse_plus":{"output_slots":[0,1,2]}`, want: "inverse Plus requires"},
		{name: "shared factor duplicate", payload: `"shared_factor_reduction":{"mode":0,"slots":[0,1],"slots":[1,2]}`, want: "duplicate object key"},
		{name: "shared factor unknown", payload: `"shared_factor_reduction":{"mode":0,"slots":[0,1],"extra":0}`, want: `unknown field "extra"`},
		{name: "shared factor case folded", payload: `"shared_factor_reduction":{"Mode":0,"slots":[0,1]}`, want: `unknown field "Mode"`},
		{name: "shared factor missing", payload: `"shared_factor_reduction":{"mode":0}`, want: "shared-factor reduction requires"},
	}
	for _, test := range cases {
		t.Run(test.name, func(t *testing.T) {
			text := `{"version":1,"ring":2,"dimensions":[2,2,2],"steps":[{` + test.payload + `}]}`
			_, err := ParseTranscript(strings.NewReader(text))
			if err == nil || !strings.Contains(err.Error(), test.want) {
				t.Fatalf("ParseTranscript error = %v, want %q", err, test.want)
			}
		})
	}
}

func TestTranscriptStrictDecoderBoundaries(t *testing.T) {
	valid := `{"version":1,"ring":2,"dimensions":[2,2,2],"steps":[]}`
	cases := []struct {
		name string
		text string
		want string
	}{
		{name: "wrong top-level type", text: `{"version":"1","ring":2,"dimensions":[2,2,2],"steps":[]}`, want: "cannot unmarshal string"},
		{name: "wrong payload type", text: `{"version":1,"ring":2,"dimensions":[2,2,2],"steps":[{"plus":{"p":"0","q":1}}]}`, want: "cannot unmarshal string"},
		{name: "fractional integer", text: `{"version":1,"ring":2,"dimensions":[2,2,2],"steps":[{"ordinary_flip":{"mode":0,"first_slot":0,"second_slot":1,"coefficient":1.5}}]}`, want: "cannot unmarshal number"},
		{name: "numeric overflow", text: `{"version":999999999999999999999,"ring":2,"dimensions":[2,2,2],"steps":[]}`, want: "cannot unmarshal number"},
		{name: "null payload", text: `{"version":1,"ring":2,"dimensions":[2,2,2],"steps":[{"plus":null}]}`, want: "Plus requires p and q"},
		{name: "array payload", text: `{"version":1,"ring":2,"dimensions":[2,2,2],"steps":[{"plus":[]}]}`, want: "cannot unmarshal array"},
		{name: "malformed", text: `{"version":1`, want: "unexpected end of JSON input"},
		{name: "trailing value", text: valid + `{}`, want: "trailing JSON value"},
		{name: "trailing malformed", text: valid + `x`, want: "trailing data"},
	}
	for _, test := range cases {
		t.Run(test.name, func(t *testing.T) {
			_, err := ParseTranscript(strings.NewReader(test.text))
			if err == nil || !strings.Contains(err.Error(), test.want) {
				t.Fatalf("ParseTranscript error = %v, want %q", err, test.want)
			}
		})
	}
}

func TestParseTranscriptRejectsOversizeWithoutReadingSentinel(t *testing.T) {
	input := bytes.Repeat([]byte{' '}, MaxTranscriptBytes+1)
	input = append(input, '!')
	reader := bytes.NewReader(input)
	_, err := ParseTranscript(reader)
	if err == nil || !strings.Contains(err.Error(), "exceeds 16777216-byte limit") {
		t.Fatalf("ParseTranscript error = %v", err)
	}
	if reader.Len() != 1 {
		t.Fatalf("reader has %d bytes remaining, want sentinel only", reader.Len())
	}
	sentinel, err := reader.ReadByte()
	if err != nil {
		t.Fatal(err)
	}
	if sentinel != '!' {
		t.Fatalf("sentinel = %q, want !", sentinel)
	}
}

func TestTranscriptMetadataAndVersionFailClosed(t *testing.T) {
	source := mustScheme(t, []RankOneTerm{
		packedTerm(t, ring.Z2, 9, 9, 9),
		packedTerm(t, ring.Z2, 12, 1, 10),
	})
	base := Transcript{Version: TranscriptVersion, Ring: ring.Z2, Dimensions: [3]int{2, 2, 2}, Steps: []TranscriptStep{}}
	mutations := []struct {
		name       string
		transcript Transcript
		want       string
	}{
		{name: "version", transcript: Transcript{Version: 2, Ring: ring.Z2, Dimensions: base.Dimensions, Steps: []TranscriptStep{}}, want: "version 2"},
		{name: "ring", transcript: Transcript{Version: 1, Ring: ring.Z3, Dimensions: base.Dimensions, Steps: []TranscriptStep{}}, want: "source ring"},
		{name: "dimensions", transcript: Transcript{Version: 1, Ring: ring.Z2, Dimensions: [3]int{2, 2, 3}, Steps: []TranscriptStep{}}, want: "source dimensions"},
	}
	for _, mutation := range mutations {
		t.Run(mutation.name, func(t *testing.T) {
			_, err := ReplayTranscript(source, mutation.transcript)
			if err == nil || !strings.Contains(err.Error(), mutation.want) {
				t.Fatalf("ReplayTranscript error = %v, want %q", err, mutation.want)
			}
		})
	}
}

func TestNewTranscriptCopiesStepStorage(t *testing.T) {
	term := packedTerm(t, ring.Z2, 1, 2, 4)
	source := mustScheme(t, []RankOneTerm{term, term})
	slots := []int{1, 0}
	steps := []TranscriptStep{{SharedFactorReduction: &SharedFactorReductionStep{Mode: SharedFirst, Slots: slots}}}
	transcript, err := NewTranscript(source, steps)
	if err != nil {
		t.Fatal(err)
	}
	slots[0] = 9
	steps[0].SharedFactorReduction.Mode = SharedThird
	if got := transcript.Steps[0].SharedFactorReduction; got.Mode != SharedFirst || !reflect.DeepEqual(got.Slots, []int{1, 0}) {
		t.Fatalf("transcript storage changed to %+v", got)
	}
}

func replayDecodedSteps(t *testing.T, source Scheme, steps []TranscriptStep) Scheme {
	t.Helper()
	transcript := Transcript{
		Version:    TranscriptVersion,
		Ring:       source.Ring(),
		Dimensions: source.Dimensions(),
		Steps:      steps,
	}
	var encoded bytes.Buffer
	if err := WriteTranscript(&encoded, transcript); err != nil {
		t.Fatal(err)
	}
	decoded, err := ParseTranscript(strings.NewReader(encoded.String()))
	if err != nil {
		t.Fatal(err)
	}
	result, err := ReplayTranscript(source, decoded)
	if err != nil {
		t.Fatal(err)
	}
	return result
}

func replaySteps(t *testing.T, source Scheme, steps []TranscriptStep) Scheme {
	t.Helper()
	transcript, err := NewTranscript(source, steps)
	if err != nil {
		t.Fatal(err)
	}
	result, err := ReplayTranscript(source, transcript)
	if err != nil {
		t.Fatal(err)
	}
	return result
}
