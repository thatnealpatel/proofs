package main

import (
	"bytes"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"os"
	"reflect"
	"slices"
	"strings"
	"testing"

	"patel.codes/proofs/internal/tensor"
)

const (
	inverseTestSagePath      = "../../Programs/BilinearComplexity/c659_fixed_child_inverse_plus_oracle.sage"
	inverseTestArtifactPath  = "../../Programs/BilinearComplexity/c659_fixed_child_inverse_plus_oracle.json"
	inverseTestValidatorPath = "../../Programs/BilinearComplexity/validate_c659_fixed_child_inverse_plus_oracle.py"
)

type inverseTestHitExpectation struct {
	sequence         int
	compact          [4]int
	orientation      string
	positions        [3]int
	variant          int
	assignment       [3]int
	sources          [2]wordTriple
	classification   string
	identity         bool
	appliedOrdered   string
	appliedUnordered string
	parentOrdered    string
	parentUnordered  string
	scatterOrdered   string
	scatterUnordered string
}

var inverseTestRootWords = []wordTriple{
	{52995, 53248, 4237},
	{49356, 54078, 38},
	{3840, 16398, 321},
	{50184, 2056, 45101},
	{49678, 55014, 4231},
	{33928, 59908, 1606},
	{41640, 55748, 8226},
	{50360, 56576, 10676},
	{512, 9838, 80},
	{49870, 54843, 6},
	{33976, 1028, 2966},
	{33496, 68, 2730},
	{58078, 55770, 316},
	{53981, 55710, 273},
	{53976, 55560, 2457},
	{50376, 54536, 8228},
	{2056, 32776, 16452},
	{49886, 221, 10},
	{49164, 3822, 4135},
	{49404, 56784, 310},
	{36616, 16384, 56385},
	{33016, 1092, 8980},
	{520, 9736, 53469},
	{53983, 55697, 5},
	{514, 54894, 4113},
	{61695, 55700, 276},
	{41480, 136, 41130},
	{3855, 53256, 4116},
	{32520, 8, 35092},
	{32776, 34944, 30273},
	{50127, 53261, 4},
	{57870, 238, 160},
	{33416, 9924, 1638},
	{1032, 58888, 53325},
	{41688, 55628, 10686},
	{33800, 60928, 54859},
	{46264, 55556, 2452},
	{526, 54792, 144},
	{16131, 14, 412},
	{3848, 16392, 55620},
	{3843, 53262, 157},
	{53982, 55559, 13},
	{32904, 36036, 9796},
	{58094, 55604, 32},
	{3072, 57358, 64},
	{34696, 16388, 1092},
	{33288, 9856, 55019},
}

var inverseTestHits = []inverseTestHitExpectation{
	{
		sequence: 14, compact: [4]int{46, 45, 0, 2}, orientation: "ijk", positions: [3]int{0, 1, 2}, variant: 2, assignment: [3]int{46, 45, 47},
		sources: [2]wordTriple{{53981, 55710, 273}, {50360, 56576, 10676}}, classification: "c659_transposition_(7 13)", identity: false,
		appliedOrdered: "34fe1c066befdeb31cdf77c92453410c33a0d8a48516edc3c924c65aa5ec70b0", appliedUnordered: "f2edf6735401e203b532cc85e0783fb47684815a3207b3ec601f8503c48956d1",
		parentOrdered: "0db3f66cf7786d0a12ddda907b7e22ff3a55e5d6f793db1f7f8ee132d5c22e01", parentUnordered: "f2edf6735401e203b532cc85e0783fb47684815a3207b3ec601f8503c48956d1",
		scatterOrdered: "913109f1ab4662db336696a853ecb5bf77f60ea5a0b051117c4359469660e24a", scatterUnordered: "0001430818e501c6964f6bf666e52a72cd0514605b3c69460e0d09cf80ec48e9",
	},
	{
		sequence: 18, compact: [4]int{45, 46, 1, 0}, orientation: "ikj", positions: [3]int{0, 2, 1}, variant: 0, assignment: [3]int{45, 46, 47},
		sources: [2]wordTriple{{50360, 56576, 10676}, {53981, 55710, 273}}, classification: "c659_identity", identity: true,
		appliedOrdered: "9b1cb3410d70d91cfbe5c15c51801a05c5fccbd11e7243e833f00b8f28f2f1a7", appliedUnordered: "f2edf6735401e203b532cc85e0783fb47684815a3207b3ec601f8503c48956d1",
		parentOrdered: "f61518b4864995fe5ba43f1b52819cc563c4c74326442ae12bbc338a491027cb", parentUnordered: "f2edf6735401e203b532cc85e0783fb47684815a3207b3ec601f8503c48956d1",
		scatterOrdered: "913109f1ab4662db336696a853ecb5bf77f60ea5a0b051117c4359469660e24a", scatterUnordered: "0001430818e501c6964f6bf666e52a72cd0514605b3c69460e0d09cf80ec48e9",
	},
	{
		sequence: 42, compact: [4]int{45, 46, 2, 1}, orientation: "jik", positions: [3]int{1, 0, 2}, variant: 1, assignment: [3]int{45, 46, 47},
		sources: [2]wordTriple{{50360, 56576, 10676}, {53981, 55710, 273}}, classification: "c659_identity", identity: true,
		appliedOrdered: "9b1cb3410d70d91cfbe5c15c51801a05c5fccbd11e7243e833f00b8f28f2f1a7", appliedUnordered: "f2edf6735401e203b532cc85e0783fb47684815a3207b3ec601f8503c48956d1",
		parentOrdered: "f61518b4864995fe5ba43f1b52819cc563c4c74326442ae12bbc338a491027cb", parentUnordered: "f2edf6735401e203b532cc85e0783fb47684815a3207b3ec601f8503c48956d1",
		scatterOrdered: "913109f1ab4662db336696a853ecb5bf77f60ea5a0b051117c4359469660e24a", scatterUnordered: "0001430818e501c6964f6bf666e52a72cd0514605b3c69460e0d09cf80ec48e9",
	},
	{
		sequence: 62, compact: [4]int{46, 45, 3, 1}, orientation: "jki", positions: [3]int{1, 2, 0}, variant: 1, assignment: [3]int{46, 45, 47},
		sources: [2]wordTriple{{53981, 55710, 273}, {50360, 56576, 10676}}, classification: "c659_transposition_(7 13)", identity: false,
		appliedOrdered: "34fe1c066befdeb31cdf77c92453410c33a0d8a48516edc3c924c65aa5ec70b0", appliedUnordered: "f2edf6735401e203b532cc85e0783fb47684815a3207b3ec601f8503c48956d1",
		parentOrdered: "0db3f66cf7786d0a12ddda907b7e22ff3a55e5d6f793db1f7f8ee132d5c22e01", parentUnordered: "f2edf6735401e203b532cc85e0783fb47684815a3207b3ec601f8503c48956d1",
		scatterOrdered: "913109f1ab4662db336696a853ecb5bf77f60ea5a0b051117c4359469660e24a", scatterUnordered: "0001430818e501c6964f6bf666e52a72cd0514605b3c69460e0d09cf80ec48e9",
	},
	{
		sequence: 74, compact: [4]int{46, 45, 4, 0}, orientation: "kij", positions: [3]int{2, 0, 1}, variant: 0, assignment: [3]int{46, 45, 47},
		sources: [2]wordTriple{{53981, 55710, 273}, {50360, 56576, 10676}}, classification: "c659_transposition_(7 13)", identity: false,
		appliedOrdered: "34fe1c066befdeb31cdf77c92453410c33a0d8a48516edc3c924c65aa5ec70b0", appliedUnordered: "f2edf6735401e203b532cc85e0783fb47684815a3207b3ec601f8503c48956d1",
		parentOrdered: "0db3f66cf7786d0a12ddda907b7e22ff3a55e5d6f793db1f7f8ee132d5c22e01", parentUnordered: "f2edf6735401e203b532cc85e0783fb47684815a3207b3ec601f8503c48956d1",
		scatterOrdered: "913109f1ab4662db336696a853ecb5bf77f60ea5a0b051117c4359469660e24a", scatterUnordered: "0001430818e501c6964f6bf666e52a72cd0514605b3c69460e0d09cf80ec48e9",
	},
	{
		sequence: 102, compact: [4]int{45, 46, 5, 2}, orientation: "kji", positions: [3]int{2, 1, 0}, variant: 2, assignment: [3]int{45, 46, 47},
		sources: [2]wordTriple{{50360, 56576, 10676}, {53981, 55710, 273}}, classification: "c659_identity", identity: true,
		appliedOrdered: "9b1cb3410d70d91cfbe5c15c51801a05c5fccbd11e7243e833f00b8f28f2f1a7", appliedUnordered: "f2edf6735401e203b532cc85e0783fb47684815a3207b3ec601f8503c48956d1",
		parentOrdered: "f61518b4864995fe5ba43f1b52819cc563c4c74326442ae12bbc338a491027cb", parentUnordered: "f2edf6735401e203b532cc85e0783fb47684815a3207b3ec601f8503c48956d1",
		scatterOrdered: "913109f1ab4662db336696a853ecb5bf77f60ea5a0b051117c4359469660e24a", scatterUnordered: "0001430818e501c6964f6bf666e52a72cd0514605b3c69460e0d09cf80ec48e9",
	},
}

func TestInversePlusOrientationsAndEquationTables(t *testing.T) {
	orientations := []struct {
		name      string
		positions [3]int
		oriented  wordTriple
	}{
		{name: "ijk", positions: [3]int{0, 1, 2}, oriented: wordTriple{11, 22, 44}},
		{name: "ikj", positions: [3]int{0, 2, 1}, oriented: wordTriple{11, 44, 22}},
		{name: "jik", positions: [3]int{1, 0, 2}, oriented: wordTriple{22, 11, 44}},
		{name: "jki", positions: [3]int{1, 2, 0}, oriented: wordTriple{22, 44, 11}},
		{name: "kij", positions: [3]int{2, 0, 1}, oriented: wordTriple{44, 11, 22}},
		{name: "kji", positions: [3]int{2, 1, 0}, oriented: wordTriple{44, 22, 11}},
	}
	words := wordTriple{11, 22, 44}
	term, err := inversePlusTermFromWords(words)
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range orientations {
		t.Run(want.name, func(t *testing.T) {
			orientedWords := orientInversePlusWords(words, want.positions)
			if orientedWords != want.oriented {
				t.Fatalf("oriented words = %v, want %v", orientedWords, want.oriented)
			}
			if got := unorientInversePlusWords(orientedWords, want.positions); got != words {
				t.Fatalf("unoriented words = %v, want %v", got, words)
			}
			orientedTerm, err := orientTerm(term, want.positions)
			if err != nil {
				t.Fatal(err)
			}
			gotOrientedTerm, err := termWords(orientedTerm)
			if err != nil {
				t.Fatal(err)
			}
			if gotOrientedTerm != want.oriented {
				t.Fatalf("oriented term = %v, want %v", gotOrientedTerm, want.oriented)
			}
			roundTrip, err := unorientTerm(orientedTerm, want.positions)
			if err != nil {
				t.Fatal(err)
			}
			gotRoundTrip, err := termWords(roundTrip)
			if err != nil {
				t.Fatal(err)
			}
			if gotRoundTrip != words {
				t.Fatalf("unoriented term = %v, want %v", gotRoundTrip, words)
			}
		})
	}

	sources := [2]wordTriple{{1, 2, 4}, {8, 16, 32}}
	expectedOutputs := [3][3]wordTriple{
		{{1, 18, 4}, {9, 16, 32}, {1, 16, 36}},
		{{1, 2, 36}, {8, 18, 32}, {9, 2, 32}},
		{{9, 2, 4}, {8, 16, 36}, {8, 18, 4}},
	}
	expectedNames := [3][9]string{
		{
			"output0.factor_i=a1", "output0.factor_j=b1+b2", "output0.factor_k=c1",
			"output1.factor_i=a1+a2", "output1.factor_j=b2", "output1.factor_k=c2",
			"output2.factor_i=a1", "output2.factor_j=b2", "output2.factor_k=c1+c2",
		},
		{
			"output0.factor_i=a1", "output0.factor_j=b1", "output0.factor_k=c1+c2",
			"output1.factor_i=a2", "output1.factor_j=b1+b2", "output1.factor_k=c2",
			"output2.factor_i=a1+a2", "output2.factor_j=b1", "output2.factor_k=c2",
		},
		{
			"output0.factor_i=a1+a2", "output0.factor_j=b1", "output0.factor_k=c1",
			"output1.factor_i=a2", "output1.factor_j=b2", "output1.factor_k=c1+c2",
			"output2.factor_i=a2", "output2.factor_j=b1+b2", "output2.factor_k=c1",
		},
	}
	for variant := range 3 {
		actualOutputs, err := forwardInversePlusWords(sources, variant)
		if err != nil {
			t.Fatal(err)
		}
		if actualOutputs != expectedOutputs[variant] {
			t.Fatalf("variant %d outputs = %v, want %v", variant, actualOutputs, expectedOutputs[variant])
		}
		recovered, replayed, equations, consistent, err := recoverInversePlusWords(expectedOutputs[variant], variant)
		if err != nil {
			t.Fatal(err)
		}
		if recovered != sources || replayed != expectedOutputs[variant] || !consistent || len(equations) != 9 {
			t.Fatalf("variant %d recovery = sources %v replay %v consistent %t equations %d", variant, recovered, replayed, consistent, len(equations))
		}
		for equationIndex, equation := range equations {
			output := equationIndex / 3
			factor := equationIndex % 3
			if equation.Name != expectedNames[variant][equationIndex] || equation.Actual != expectedOutputs[variant][output][factor] || equation.Replayed != expectedOutputs[variant][output][factor] || !equation.Holds {
				t.Fatalf("variant %d equation %d = %+v", variant, equationIndex, equation)
			}
		}
		for mutatedFactor := range 3 {
			mutated := expectedOutputs[variant]
			mutated[2][mutatedFactor] ^= uint16(1) << (12 + mutatedFactor)
			_, _, mutatedEquations, mutatedConsistent, err := recoverInversePlusWords(mutated, variant)
			if err != nil {
				t.Fatal(err)
			}
			if mutatedConsistent {
				t.Fatalf("variant %d accepted mutation in output 2 factor %d", variant, mutatedFactor)
			}
			failed := make([]int, 0, 1)
			for equationIndex, equation := range mutatedEquations {
				if equation.Name != expectedNames[variant][equationIndex] {
					t.Fatalf("variant %d mutated equation %d name = %q", variant, equationIndex, equation.Name)
				}
				if !equation.Holds {
					failed = append(failed, equationIndex)
				}
			}
			if !slices.Equal(failed, []int{6 + mutatedFactor}) {
				t.Fatalf("variant %d mutation factor %d failed equations %v", variant, mutatedFactor, failed)
			}
		}
	}
}

func TestInversePlusDescriptorCoverageHitsAndCertificate(t *testing.T) {
	root, child := inverseTestRootAndChild(t)
	certificate, err := analyzeFixedChildInversePlus(root, child)
	if err != nil {
		t.Fatal(err)
	}
	orientations := [6]inversePlusOrientationV4{
		{Name: "ijk", Positions: [3]int{0, 1, 2}},
		{Name: "ikj", Positions: [3]int{0, 2, 1}},
		{Name: "jik", Positions: [3]int{1, 0, 2}},
		{Name: "jki", Positions: [3]int{1, 2, 0}},
		{Name: "kij", Positions: [3]int{2, 0, 1}},
		{Name: "kji", Positions: [3]int{2, 1, 0}},
	}
	assignments := [6][3]int{{45, 46, 47}, {45, 47, 46}, {46, 45, 47}, {46, 47, 45}, {47, 45, 46}, {47, 46, 45}}
	formulas := [3]string{
		"(a1,b1+b2,c1);(a1+a2,b2,c2);(a1,b2,c1+c2)",
		"(a1,b1,c1+c2);(a2,b1+b2,c2);(a1+a2,b1,c2)",
		"(a1+a2,b1,c1);(a2,b2,c1+c2);(a2,b1+b2,c1)",
	}
	acceptedSequences := []int{14, 18, 42, 62, 74, 102}
	acceptedSet := make(map[int]bool, len(acceptedSequences))
	for _, sequence := range acceptedSequences {
		acceptedSet[sequence] = true
	}
	var allStream bytes.Buffer
	var acceptedStream bytes.Buffer
	rejectedSequences := make([]int, 0, 102)
	sequence := 0
	for orientationIndex, orientation := range orientations {
		for variant := range 3 {
			for _, assignment := range assignments {
				record := certificate.Records[sequence]
				compact := [4]int{assignment[0], assignment[1], orientationIndex, variant}
				wantDescriptor := inversePlusDescriptorV4{
					Sequence: sequence, OrientationIndex: orientationIndex, Orientation: orientation.Name, Positions: orientation.Positions,
					Variant: variant, Formula: formulas[variant], Assignment: assignment, Compact: compact,
				}
				if record.Descriptor != wantDescriptor {
					t.Fatalf("record %d descriptor = %+v, want %+v", sequence, record.Descriptor, wantDescriptor)
				}
				line := fmt.Sprintf("[%d,%d,%d,%d]\n", compact[0], compact[1], compact[2], compact[3])
				allStream.WriteString(line)
				if acceptedSet[sequence] {
					if !record.Accepted {
						t.Fatalf("record %d rejected exact hit", sequence)
					}
					acceptedStream.WriteString(line)
				} else {
					if record.Accepted {
						t.Fatalf("record %d unexpectedly accepted", sequence)
					}
					rejectedSequences = append(rejectedSequences, sequence)
				}
				class := certificate.Deduplication.RawDescriptorClasses[sequence]
				if class.Class != sequence || class.Bytes != len(line) || class.PayloadASCII != line || class.PayloadHex != hex.EncodeToString([]byte(line)) || class.SHA256 != inverseTestSHA256([]byte(line)) || !slices.Equal(class.Sequences, []int{sequence}) {
					t.Fatalf("raw descriptor class %d = %+v", sequence, class)
				}
				sequence++
			}
		}
	}
	acceptedLiteral := "[46,45,0,2]\n[45,46,1,0]\n[45,46,2,1]\n[46,45,3,1]\n[46,45,4,0]\n[45,46,5,2]\n"
	if sequence != 108 || allStream.Len() != 1296 || inverseTestSHA256(allStream.Bytes()) != "e05ef47fc81d499b850748e1c1193280fd622c257b5a82ac5487491175cf4d94" {
		t.Fatalf("all descriptor stream = %d records, %d bytes, SHA-256 %s", sequence, allStream.Len(), inverseTestSHA256(allStream.Bytes()))
	}
	if acceptedStream.String() != acceptedLiteral || acceptedStream.Len() != 72 || inverseTestSHA256(acceptedStream.Bytes()) != "73fbb5130da5027c305ea14a8e18815d01fc8c7e7413737c69c8337bf330b5fc" {
		t.Fatalf("accepted descriptor stream = %q, %d bytes, SHA-256 %s", acceptedStream.String(), acceptedStream.Len(), inverseTestSHA256(acceptedStream.Bytes()))
	}
	if certificate.Method.EnumerationOrder != "orientation-major, variant-major, lexicographic assignment-major" || certificate.Method.OrientationOrder != orientations || certificate.Method.VariantOrder != [3]int{0, 1, 2} || certificate.Method.Formulas != formulas {
		t.Fatalf("enumeration method = %+v", certificate.Method)
	}
	if certificate.Enumeration.SlotIndexing != "zero-based" || certificate.Enumeration.SequenceIndexing != "zero-based" || certificate.Enumeration.DescriptorSchema != [4]string{"slotX", "slotY", "orientationIndex", "variant"} || certificate.Enumeration.DescriptorCount != 108 || !certificate.Enumeration.AllDescriptorsUnique || !certificate.Enumeration.AcceptedSequenceOrderVerified || !slices.Equal(certificate.Enumeration.AcceptedSequences, acceptedSequences) || !slices.Equal(certificate.Enumeration.RejectedSequences, rejectedSequences) {
		t.Fatalf("enumeration coverage = %+v", certificate.Enumeration)
	}
	if certificate.Streams.CompactDescriptorStreams != (inversePlusComputedStreamsV4{
		Encoding: "exact ASCII [slotX,slotY,orientationIndex,variant] plus LF per descriptor", AllBytes: 1296,
		AllSHA256: "e05ef47fc81d499b850748e1c1193280fd622c257b5a82ac5487491175cf4d94", AcceptedBytes: 72,
		AcceptedSHA256: "73fbb5130da5027c305ea14a8e18815d01fc8c7e7413737c69c8337bf330b5fc", Recomputed: true,
	}) {
		t.Fatalf("computed descriptor streams = %+v", certificate.Streams.CompactDescriptorStreams)
	}
	wantCounts := inversePlusCountsV4{
		DescriptorTotal: 108, AcceptedDescriptors: 6, RejectedDescriptors: 102, InverseEquationConsistent: 6, InverseEquationInconsistent: 102,
		ConstructorCalls: 6, AcceptedExactParentLineage: 6, AcceptedIdentityLineage: 3, AcceptedSwapSevenThirteenLineage: 3,
		AcceptedAlternateExactParent: 0, AcceptedLocalTensorReplay: 6, AcceptedScatterFixedChildReplay: 6, AcceptedParentTensorReplay: 6,
		AcceptedParentNonzero: 6, AcceptedParentCompleteTermDistinct: 6, AcceptedSourcePreconditionLegal: 6, UniqueRawDescriptors: 108,
		UniqueReconstructedSourcePairOrdered: 2, UniqueReconstructedSourcePairOrderForgotten: 1, UniqueReconstructedParentOrderedPayload: 2,
		UniqueReconstructedParentUnorderedPayload: 1,
	}
	if certificate.Counts != wantCounts {
		t.Fatalf("counts = %+v, want %+v", certificate.Counts, wantCounts)
	}
	for _, want := range inverseTestHits {
		record := certificate.Records[want.sequence]
		if !record.Accepted || record.Classification != "accepted_exact_parent_lineage" || record.Descriptor.Compact != want.compact || record.Descriptor.Orientation != want.orientation || record.Descriptor.Positions != want.positions || record.Descriptor.Variant != want.variant || record.Descriptor.Assignment != want.assignment {
			t.Fatalf("hit %d descriptor/classification = %+v / %q", want.sequence, record.Descriptor, record.Classification)
		}
		if record.SourcePolicy == nil || record.SourcePolicy.RecoveredSources != want.sources || !record.SourcePolicy.EvaluatedSeparatelyFromConstructor || len(record.SourcePolicy.ZeroFactorSourceTerms) != 0 || len(record.SourcePolicy.SourceFactorCollisionModes) != 0 || !record.SourcePolicy.AllSourceTermsNonzero || !record.SourcePolicy.AnalyzerNonzeroPolicyPassed || !record.SourcePolicy.SourcePreconditionLegal {
			t.Fatalf("hit %d source policy = %+v", want.sequence, record.SourcePolicy)
		}
		if record.Replacement == nil || record.Replay == nil || record.Lineage == nil {
			t.Fatalf("hit %d has incomplete endpoints", want.sequence)
		}
		lineage := record.Lineage
		if lineage.Classification != want.classification || lineage.IdentityLiteralMatch != want.identity || lineage.SwapSevenThirteenLiteralMatch == want.identity || !lineage.GeneratingAlias || lineage.AlternateExactParent || !lineage.LiteralFactorEquality || !lineage.SourceTermsEqualMappedRootSlots || lineage.OrbitEquivalenceStatus != "not_applicable_literal_lineage" || !lineage.NoSolverUsed {
			t.Fatalf("hit %d lineage = %+v", want.sequence, lineage)
		}
		mapping := make([]int, 47)
		wantParentWords := append([]wordTriple(nil), inverseTestRootWords...)
		for slot := range mapping {
			mapping[slot] = slot
		}
		if !want.identity {
			mapping[7], mapping[13] = mapping[13], mapping[7]
			wantParentWords[7], wantParentWords[13] = wantParentWords[13], wantParentWords[7]
		}
		if !slices.Equal(lineage.ParentSlotToRootSlot, mapping) || !slices.Equal(record.Replacement.Parent.Result.OrderedTerms, wantParentWords) || len(lineage.LiteralFactorEqualityWitnesses) != 47 {
			t.Fatalf("hit %d parent mapping or ordered terms changed", want.sequence)
		}
		for parentSlot, witness := range lineage.LiteralFactorEqualityWitnesses {
			rootSlot := mapping[parentSlot]
			if witness.ParentSlot != parentSlot || witness.RootSlot != rootSlot || witness.ParentFactors != inverseTestRootWords[rootSlot] || witness.RootFactors != inverseTestRootWords[rootSlot] || witness.FactorEqualities != [3]bool{true, true, true} || !witness.CompleteTermEqual {
				t.Fatalf("hit %d witness %d = %+v", want.sequence, parentSlot, witness)
			}
		}
		selectedCandidate := lineage.SwapSevenThirteenCandidateWitnesses
		if want.identity {
			selectedCandidate = lineage.IdentityCandidateWitnesses
		}
		if !reflect.DeepEqual(selectedCandidate, lineage.LiteralFactorEqualityWitnesses) || len(lineage.IdentityCandidateWitnesses) != 47 || len(lineage.SwapSevenThirteenCandidateWitnesses) != 47 {
			t.Fatalf("hit %d candidate witness selection changed", want.sequence)
		}
		replacement := record.Replacement
		if replacement.AppliedOrderedBytes != 290 || replacement.AppliedOrderedSHA256 != want.appliedOrdered || replacement.AppliedResult.TermCount != 47 || replacement.AppliedResult.UnorderedCanonicalSHA256 != want.appliedUnordered || replacement.Parent.OrderedFactorMajorBytes != 290 || replacement.Parent.OrderedFactorMajorSHA256 != want.parentOrdered || replacement.Parent.UnorderedCanonicalBytes != 290 || replacement.Parent.UnorderedCanonicalSHA256 != want.parentUnordered || replacement.Parent.Result.UnorderedCanonicalSHA256 != want.parentUnordered || record.Replay.ScatterOrderedSHA256 != want.scatterOrdered || record.Replay.ScatterUnorderedSHA256 != want.scatterUnordered {
			t.Fatalf("hit %d endpoint hashes = applied %s/%s parent %s/%s/%s scatter %s/%s", want.sequence, replacement.AppliedOrderedSHA256, replacement.AppliedResult.UnorderedCanonicalSHA256, replacement.Parent.OrderedFactorMajorSHA256, replacement.Parent.UnorderedCanonicalSHA256, replacement.Parent.Result.UnorderedCanonicalSHA256, record.Replay.ScatterOrderedSHA256, record.Replay.ScatterUnorderedSHA256)
		}
		orderedPayload, err := hex.DecodeString(replacement.Parent.OrderedFactorMajorPayloadHex)
		if err != nil {
			t.Fatal(err)
		}
		unorderedPayload, err := hex.DecodeString(replacement.Parent.UnorderedCanonicalPayloadHex)
		if err != nil {
			t.Fatal(err)
		}
		if len(orderedPayload) != 290 || inverseTestSHA256(orderedPayload) != want.parentOrdered || len(unorderedPayload) != 290 || inverseTestSHA256(unorderedPayload) != want.parentUnordered {
			t.Fatalf("hit %d endpoint payload bindings changed", want.sequence)
		}
	}
	wantDisclaimers := []string{
		"the result is bounded to the exact authenticated selected c659 root, the exact ordered fixed child, child slots 45,46,47, six listed orientations, and Plus variants 0,1,2",
		"reversed source order is a literal c659 lineage alias under root-slot transposition (7 13), never an alternate parent",
		"if a nonliteral valid parent were encountered, this frozen authenticated certificate would fail closed before publication; no equivalence solver would run and its orbit/equivalence status would remain unknown",
		"the result says nothing about other supports or other children",
		"the result does not establish or use a c680 bridge",
		"the result does not establish a rank-46 presentation",
		"the result does not establish a global orbit or orbit equivalence",
		"the result does not establish tensor-rank minimality or any tensor-rank lower bound",
		"the frozen Sage oracle v3 full semantic streams are bound as metadata and are not recomputed by this command",
	}
	if certificateSchema != "patel.codes/proofs/c659-plusflip-cert/v4" || certificate.Schema != "patel.codes/proofs/c659-plusflip-cert/fixed-child-inverse-plus/v4" || certificate.ExperimentID != "CC-1A-c659-fixed-v1" || certificate.Status != "complete" || certificate.Result != "bounded_no_alternate_parent" || certificate.Conclusion != "within this bounded fixed-child domain all six inverse-Plus hits are literal c659 lineage aliases, every reconstructed endpoint has the authenticated c659 unordered canonical hash, and the alternate-parent form of CC-1A is falsified for this child only" || certificate.Scope != "exactly the 108 orientation-major, variant-major, lexicographic formula-slot assignments on fixed child slots 45,46,47 of the authenticated selected c659 root's exact fixed Plus child" || !slices.Equal(certificate.ScopeDisclaimers, wantDisclaimers) {
		t.Fatalf("schema/result/scope = %q/%q/%q/%v", certificate.Schema, certificate.Result, certificate.Scope, certificate.ScopeDisclaimers)
	}
	binding := certificate.OracleBinding
	if binding.SageSource.Bytes != 43716 || binding.SageSource.SHA256 != "1dd78a71e4206936656e542d6b4c1f8e347f4c647dd77cfb25d68178dec61f8e" || binding.Artifact.Bytes != 206895 || binding.Artifact.SHA256 != "9616ca07d92a9fe70ae8a522bb13cd46bf9d77ea5f61b658beda8840a9b7e553" || binding.Validator.Bytes != 33407 || binding.Validator.SHA256 != "a1ae5a93abeb1a709b822e803cac20ca4999a6854ce31b1bf1266ac20f9eca73" || binding.FixedChildOrdered.Bytes != 296 || binding.FixedChildOrdered.SHA256 != "913109f1ab4662db336696a853ecb5bf77f60ea5a0b051117c4359469660e24a" {
		t.Fatalf("oracle file and fixed-child bindings = %+v", binding)
	}
	if binding.OracleRecomputedByCommand || binding.Schema != "c659-fixed-child-inverse-plus-oracle-v3" || certificate.Streams.FullSemanticRecordBinding.AllSHA256 != "85578bcb1f46796677c62c97261c6724ebd8b4f21424e63dbaaacac87569e48d" || certificate.Streams.FullSemanticRecordBinding.AcceptedSHA256 != "c2e1d98c809cc14f6a0c00e5b755f6a8fafe1e5b2a9fb2dbb0f3c04a2c86e1f0" {
		t.Fatalf("oracle recomputation/schema/streams = %+v", certificate.OracleBinding)
	}
	firstJSON, err := json.Marshal(certificate)
	if err != nil {
		t.Fatal(err)
	}
	secondCertificate, err := analyzeFixedChildInversePlus(root, child)
	if err != nil {
		t.Fatal(err)
	}
	secondJSON, err := json.Marshal(secondCertificate)
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(firstJSON, secondJSON) || len(firstJSON) != 409298 || inverseTestSHA256(firstJSON) != "b41fc757354e096270fdec37e0e5c4c11ca38730d033293c22b583e3b2cd1955" {
		t.Fatalf("deterministic JSON = equal %t, %d bytes, SHA-256 %s", bytes.Equal(firstJSON, secondJSON), len(firstJSON), inverseTestSHA256(firstJSON))
	}
}

func TestInversePlusConstructorBoundaryAndSourcePolicy(t *testing.T) {
	root, child := inverseTestRootAndChild(t)
	calls := 0
	inconsistentCalls := 0
	boundaryFailures := 0
	var inspectionErr error
	constructor := func(scheme tensor.Scheme, slots [3]int, variant tensor.PlusVariant) (tensor.Replacement, error) {
		calls++
		if slots != [3]int{0, 1, 2} || scheme.TermCount() != 3 {
			boundaryFailures++
		}
		words, err := schemeWords(scheme)
		if err != nil {
			inspectionErr = err
			return tensor.Replacement{}, err
		}
		outputs := [3]wordTriple{words[0], words[1], words[2]}
		_, _, _, consistent, err := recoverInversePlusWords(outputs, int(variant))
		if err != nil {
			inspectionErr = err
			return tensor.Replacement{}, err
		}
		if !consistent {
			inconsistentCalls++
		}
		return tensor.NewInversePlusReplacement(scheme, slots, variant)
	}
	certificate, err := analyzeFixedChildInversePlusWithConstructor(root, child, constructor)
	if err != nil {
		t.Fatal(err)
	}
	if inspectionErr != nil || calls != 6 || inconsistentCalls != 0 || boundaryFailures != 0 || certificate.Counts.ConstructorCalls != 6 {
		t.Fatalf("constructor boundary = calls %d inconsistent %d boundary failures %d inspection error %v", calls, inconsistentCalls, boundaryFailures, inspectionErr)
	}
	calledRecords := 0
	for _, record := range certificate.Records {
		if record.Constructor.Called {
			calledRecords++
			if !record.Accepted || !record.IndependentRecovery.AllNamedEquationsHold {
				t.Fatalf("constructor entered inconsistent record %d", record.Descriptor.Sequence)
			}
		} else if record.Accepted {
			t.Fatalf("accepted record %d skipped constructor", record.Descriptor.Sequence)
		}
	}
	if calledRecords != 6 {
		t.Fatalf("called record count = %d", calledRecords)
	}
	sentinel := errors.New("injected inverse constructor failure")
	failureCalls := 0
	_, err = analyzeFixedChildInversePlusWithConstructor(root, child, func(tensor.Scheme, [3]int, tensor.PlusVariant) (tensor.Replacement, error) {
		failureCalls++
		return tensor.Replacement{}, sentinel
	})
	if !errors.Is(err, sentinel) || failureCalls != 1 || !strings.Contains(err.Error(), "descriptor 14") || !strings.Contains(err.Error(), "tensor.NewInversePlusReplacement") {
		t.Fatalf("injected constructor failure = calls %d error %v", failureCalls, err)
	}

	nonzeroSources := [2]wordTriple{{1, 2, 4}, {8, 16, 32}}
	zeroSources, collisionModes := inversePlusSourcePolicy(nonzeroSources)
	if len(zeroSources) != 0 || len(collisionModes) != 0 {
		t.Fatalf("nonzero source policy = zero %v collisions %v", zeroSources, collisionModes)
	}
	zeroFactorSources := [2]wordTriple{{0, 2, 4}, {8, 16, 32}}
	outputs, err := forwardInversePlusWords(zeroFactorSources, 0)
	if err != nil {
		t.Fatal(err)
	}
	recovered, _, _, consistent, err := recoverInversePlusWords(outputs, 0)
	if err != nil {
		t.Fatal(err)
	}
	if !consistent || recovered != zeroFactorSources {
		t.Fatalf("zero-factor algebraic recovery = %v consistent %t", recovered, consistent)
	}
	terms := make([]tensor.RankOneTerm, 3)
	for index, words := range outputs {
		terms[index], err = inversePlusTermFromWords(words)
		if err != nil {
			t.Fatal(err)
		}
	}
	temporary, err := tensor.NewScheme(terms)
	if err != nil {
		t.Fatal(err)
	}
	if _, err := tensor.NewInversePlusReplacement(temporary, [3]int{0, 1, 2}, 0); err != nil {
		t.Fatalf("algebraic constructor imposed analyzer nonzero policy: %v", err)
	}
	zeroSources, collisionModes = inversePlusSourcePolicy(zeroFactorSources)
	if !slices.Equal(zeroSources, []int{0}) || len(collisionModes) != 0 {
		t.Fatalf("zero-factor source policy = zero %v collisions %v", zeroSources, collisionModes)
	}
	collisionSources := [2]wordTriple{{1, 2, 4}, {8, 2, 32}}
	zeroSources, collisionModes = inversePlusSourcePolicy(collisionSources)
	if len(zeroSources) != 0 || !slices.Equal(collisionModes, []int{1}) {
		t.Fatalf("collision source policy = zero %v collisions %v", zeroSources, collisionModes)
	}
}

func TestInversePlusExactByteCollisionDefenseAndAlternateLineage(t *testing.T) {
	const collidingDigest = "caller-supplied-equal-digest"
	expectedEndpoint := inversePlusEndpointPayloadV4{
		Ordered:         []byte{1, 2, 3},
		Canonical:       []byte{4, 5, 6},
		OrderedSHA256:   collidingDigest,
		CanonicalSHA256: collidingDigest,
	}
	if inversePlusEndpointExact(expectedEndpoint, inversePlusEndpointPayloadV4{Ordered: []byte{1, 2, 9}, Canonical: []byte{4, 5, 6}, OrderedSHA256: collidingDigest, CanonicalSHA256: collidingDigest}) {
		t.Fatal("endpoint exactness accepted distinct ordered bytes with equal caller-supplied digests")
	}
	if inversePlusEndpointExact(expectedEndpoint, inversePlusEndpointPayloadV4{Ordered: []byte{1, 2, 3}, Canonical: []byte{4, 5, 9}, OrderedSHA256: collidingDigest, CanonicalSHA256: collidingDigest}) {
		t.Fatal("endpoint exactness accepted distinct canonical bytes with equal caller-supplied digests")
	}
	if !inversePlusEndpointExact(expectedEndpoint, inversePlusEndpointPayloadV4{Ordered: []byte{1, 2, 3}, Canonical: []byte{4, 5, 6}, OrderedSHA256: "different", CanonicalSHA256: "different"}) {
		t.Fatal("endpoint exactness rejected literal ordered and canonical byte equality")
	}

	dedupe := newInversePlusExactByteDedupeWithHash(func([]byte) string { return "constant-hash" })
	firstPayload := []byte("first exact payload")
	secondPayload := []byte("second exact payload")
	if class := dedupe.add(firstPayload, 4); class != 0 {
		t.Fatalf("first class = %d", class)
	}
	if class := dedupe.add(secondPayload, 9); class != 1 {
		t.Fatalf("colliding distinct class = %d", class)
	}
	if class := dedupe.add(append([]byte(nil), firstPayload...), 12); class != 0 {
		t.Fatalf("repeated exact class = %d", class)
	}
	firstPayload[0] = 'X'
	classes := dedupe.publicClasses(true)
	if len(classes) != 2 || dedupe.collisionsWithDifferentPayloads != 1 || classes[0].SHA256 != "constant-hash" || classes[1].SHA256 != "constant-hash" || classes[0].PayloadASCII != "first exact payload" || classes[1].PayloadASCII != "second exact payload" || !slices.Equal(classes[0].Sequences, []int{4, 12}) || !slices.Equal(classes[1].Sequences, []int{9}) {
		t.Fatalf("constant-hash exact-byte classes = %+v, collisions %d", classes, dedupe.collisionsWithDifferentPayloads)
	}

	reversedParent := append([]wordTriple(nil), inverseTestRootWords...)
	reversedParent[7], reversedParent[13] = reversedParent[13], reversedParent[7]
	reversedSources := [2]wordTriple{inverseTestRootWords[13], inverseTestRootWords[7]}
	reversed := classifyFixedChildInversePlusLineage(reversedParent, inverseTestRootWords, reversedSources)
	if reversed.Classification != "c659_transposition_(7 13)" || !reversed.GeneratingAlias || reversed.AlternateExactParent || reversed.IdentityLiteralMatch || !reversed.SwapSevenThirteenLiteralMatch || !reversed.SourceTermsEqualMappedRootSlots || reversed.OrbitEquivalenceStatus != "not_applicable_literal_lineage" || !reversed.NoSolverUsed || len(reversed.LiteralFactorEqualityWitnesses) != 47 {
		t.Fatalf("reversed source lineage = %+v", reversed)
	}
	alternateParent := append([]wordTriple(nil), inverseTestRootWords...)
	alternateParent[0][0] ^= 1
	alternate := classifyFixedChildInversePlusLineage(alternateParent, inverseTestRootWords, [2]wordTriple{inverseTestRootWords[7], inverseTestRootWords[13]})
	if alternate.Classification != "unknown_alternate" || alternate.GeneratingAlias || !alternate.AlternateExactParent || alternate.IdentityLiteralMatch || alternate.SwapSevenThirteenLiteralMatch || alternate.ParentExactRootOrderMatch || alternate.LiteralFactorEquality || alternate.SourceTermsEqualMappedRootSlots || alternate.OrbitEquivalenceStatus != "unknown" || !alternate.NoSolverUsed || len(alternate.IdentityCandidateWitnesses) != 47 || len(alternate.SwapSevenThirteenCandidateWitnesses) != 47 || len(alternate.LiteralFactorEqualityWitnesses) != 0 {
		t.Fatalf("synthetic alternate lineage = %+v", alternate)
	}
}

func TestInversePlusRepositoryOracleArtifacts(t *testing.T) {
	files := []struct {
		path   string
		bytes  int
		sha256 string
	}{
		{path: inverseTestSagePath, bytes: 43716, sha256: "1dd78a71e4206936656e542d6b4c1f8e347f4c647dd77cfb25d68178dec61f8e"},
		{path: inverseTestArtifactPath, bytes: 206895, sha256: "9616ca07d92a9fe70ae8a522bb13cd46bf9d77ea5f61b658beda8840a9b7e553"},
		{path: inverseTestValidatorPath, bytes: 33407, sha256: "a1ae5a93abeb1a709b822e803cac20ca4999a6854ce31b1bf1266ac20f9eca73"},
	}
	var artifactBytes []byte
	for _, want := range files {
		data, err := os.ReadFile(want.path)
		if err != nil {
			t.Fatal(err)
		}
		if len(data) != want.bytes || inverseTestSHA256(data) != want.sha256 {
			t.Fatalf("artifact %s = %d bytes SHA-256 %s, want %d/%s", want.path, len(data), inverseTestSHA256(data), want.bytes, want.sha256)
		}
		if want.path == inverseTestArtifactPath {
			artifactBytes = data
		}
	}
	var artifact struct {
		Schema     string `json:"schema"`
		FixedChild struct {
			OrderedBytes  int    `json:"ordered_factor_major_bytes"`
			OrderedSHA256 string `json:"ordered_factor_major_sha256"`
		} `json:"fixed_child"`
		Streams struct {
			Compact struct {
				AllBytes       int    `json:"all_bytes"`
				AllSHA256      string `json:"all_sha256"`
				AcceptedBytes  int    `json:"accepted_bytes"`
				AcceptedSHA256 string `json:"accepted_sha256"`
			} `json:"compact_descriptor_streams"`
			Semantic struct {
				AllBytes       int    `json:"all_bytes"`
				AllSHA256      string `json:"all_sha256"`
				AcceptedBytes  int    `json:"accepted_bytes"`
				AcceptedSHA256 string `json:"accepted_sha256"`
			} `json:"full_semantic_record_streams"`
		} `json:"streams"`
	}
	if err := json.Unmarshal(artifactBytes, &artifact); err != nil {
		t.Fatal(err)
	}
	if artifact.Schema != "c659-fixed-child-inverse-plus-oracle-v3" || artifact.FixedChild.OrderedBytes != 296 || artifact.FixedChild.OrderedSHA256 != "913109f1ab4662db336696a853ecb5bf77f60ea5a0b051117c4359469660e24a" {
		t.Fatalf("oracle schema/ordered child = %q/%d/%s", artifact.Schema, artifact.FixedChild.OrderedBytes, artifact.FixedChild.OrderedSHA256)
	}
	if artifact.Streams.Compact.AllBytes != 1296 || artifact.Streams.Compact.AllSHA256 != "e05ef47fc81d499b850748e1c1193280fd622c257b5a82ac5487491175cf4d94" || artifact.Streams.Compact.AcceptedBytes != 72 || artifact.Streams.Compact.AcceptedSHA256 != "73fbb5130da5027c305ea14a8e18815d01fc8c7e7413737c69c8337bf330b5fc" || artifact.Streams.Semantic.AllBytes != 171217 || artifact.Streams.Semantic.AllSHA256 != "85578bcb1f46796677c62c97261c6724ebd8b4f21424e63dbaaacac87569e48d" || artifact.Streams.Semantic.AcceptedBytes != 65038 || artifact.Streams.Semantic.AcceptedSHA256 != "c2e1d98c809cc14f6a0c00e5b755f6a8fafe1e5b2a9fb2dbb0f3c04a2c86e1f0" {
		t.Fatalf("oracle streams = %+v", artifact.Streams)
	}
}

func inverseTestRootAndChild(t *testing.T) (tensor.Scheme, tensor.Scheme) {
	t.Helper()
	root, err := loadRootCandidate("testdata/4x4x4_m47_c659_iteration5551_Z2.txt", declaredRootSpecs[0])
	if err != nil {
		t.Fatal(err)
	}
	words, err := schemeWords(root.Scheme)
	if err != nil {
		t.Fatal(err)
	}
	if !slices.Equal(words, inverseTestRootWords) {
		t.Fatalf("authenticated root words changed")
	}
	child, err := constructFixedPlus(root.Scheme)
	if err != nil {
		t.Fatal(err)
	}
	return root.Scheme, child.Scheme
}

func inverseTestSHA256(data []byte) string {
	digest := sha256.Sum256(data)
	return fmt.Sprintf("%x", digest)
}
