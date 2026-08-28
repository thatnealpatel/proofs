package main

import (
	"bytes"
	"encoding/binary"
	"encoding/json"
	"errors"
	"io"
	"os"
	"path/filepath"
	"reflect"
	"slices"
	"strings"
	"testing"
	"testing/iotest"

	"patel.codes/proofs/internal/ring"
	"patel.codes/proofs/internal/tensor"
)

const (
	testPriorScanOutputRule = "the independently completed c659 variant-0 Plus scan selected the least 64-character lowercase SHA-256 hexadecimal digest string of the unordered-canonical output bytes, compared lexicographically bytewise in ASCII order, not the least unordered-canonical bytes; this command only binds that scan and does not recompute it"

	testC659RawBytes             = 4524
	testC680RawBytes             = 4524
	testRootOrderedPayloadBytes  = 290
	testC659RawSHA256            = "25f47b5f37d2b7351dd5a2c5da65ff8ef5ba80ce53239d46cdfdef37e6eef403"
	testC680RawSHA256            = "7e65a2fa888fcd9f32d9d68fd21ab8cdafeb4a39300cc77882def8e0115483e8"
	testC659OrderedPayloadSHA256 = "f61518b4864995fe5ba43f1b52819cc563c4c74326442ae12bbc338a491027cb"
	testC680OrderedPayloadSHA256 = "f6e3264df6e1a8c39c0af212c0ee0b490c7d96b0169c21b131b4c496fe04889b"
	testC659UnorderedSHA256      = "f2edf6735401e203b532cc85e0783fb47684815a3207b3ec601f8503c48956d1"
	testC680UnorderedSHA256      = "021266950ca5db9dd40593da2ec85d043469c1a15c66a04a06c2dbe23813c598"
	testPlusChildSHA256          = "0001430818e501c6964f6bf666e52a72cd0514605b3c69460e0d09cf80ec48e9"
	testFirstFlipSHA256          = "640392811b97cf64b2ccf0c382666ba1ea2b91b859f815d0c957574378da8c90"
	testSecondFlipSHA256         = "c567254223d480d8eaecde19d24f0aa96792208c41e2101a1270937bf1fe2934"
	testThirdFlipSHA256          = "ee02607028804b19dbb6c075d2d290386dcb309cf740b826569b64550ebdddf0"
	testFourthFlipSHA256         = "cbf85f130f4bf6decd79785c85112135ab8e55a8aa745188383aeaa541171351"
	testCandidateCount           = 6768
	testAcceptedCount            = 4
	testRejectedCount            = 6764
	testUniqueOutputCount        = 4
	testMaximalClassCount        = 10
	testDefectZeroCount          = 6
	testDefectOneCount           = 4
	testDefectAtLeastTwoCount    = 0
	testReductionCount           = 4
	testSemanticSHA256           = "3815b52e97e44e4e31c81d2b0515982f6598fb765c832ca7d23f75229f95bfcf"
	testCompleteOutputSHA256     = "b067dd4008f35fb8b85ab1693e9e54d5d6dc11ac3b1336e584092753332cfe49"
	testUsage                    = "Usage: c659-plusflip-cert C659_ROOT_PATH C680_ROOT_PATH\n"
)

type acceptedAttemptExpectation struct {
	Sequence   int
	Descriptor flipDescriptor
	SHA256     string
}

var testAcceptedAttempts = []acceptedAttemptExpectation{
	{Sequence: 6483, Descriptor: flipDescriptor{FirstSlot: 45, SecondSlot: 47, SharedMode: 0, Coefficient: 1}, SHA256: testFirstFlipSHA256},
	{Sequence: 6626, Descriptor: flipDescriptor{FirstSlot: 46, SecondSlot: 47, SharedMode: 2, Coefficient: 1}, SHA256: testSecondFlipSHA256},
	{Sequence: 6762, Descriptor: flipDescriptor{FirstSlot: 47, SecondSlot: 45, SharedMode: 0, Coefficient: 1}, SHA256: testThirdFlipSHA256},
	{Sequence: 6767, Descriptor: flipDescriptor{FirstSlot: 47, SecondSlot: 46, SharedMode: 2, Coefficient: 1}, SHA256: testFourthFlipSHA256},
}

var testPlusInserted = []wordTriple{
	{50360, 56576, 10405},
	{5733, 55710, 273},
	{50360, 1182, 273},
}

var testReductionInsertions = []preregisteredReduction{
	{OutputHash: testSecondFlipSHA256, SharedMode: 0, Inserted: wordTriple{50360, 56576, 10676}},
	{OutputHash: testSecondFlipSHA256, SharedMode: 1, Inserted: wordTriple{50360, 56576, 10676}},
	{OutputHash: testThirdFlipSHA256, SharedMode: 1, Inserted: wordTriple{53981, 55710, 273}},
	{OutputHash: testThirdFlipSHA256, SharedMode: 2, Inserted: wordTriple{53981, 55710, 273}},
}

type testRootPaths struct {
	C659 string
	C680 string
}

func rootPathsForTest(t *testing.T) testRootPaths {
	t.Helper()
	paths := testRootPaths{
		C659: os.Getenv("C659_ROOT_PATH"),
		C680: os.Getenv("C680_ROOT_PATH"),
	}
	if paths.C659 == "" {
		paths.C659 = filepath.Join("testdata", c659RootFileName)
	}
	if paths.C680 == "" {
		paths.C680 = filepath.Join("testdata", c680RootFileName)
	}
	for role, path := range map[string]string{c659RootRole: paths.C659, c680RootRole: paths.C680} {
		if _, err := os.Stat(path); err != nil {
			t.Fatalf("authenticated %s root is unavailable: %v", role, err)
		}
	}
	return paths
}

func experimentForTest(t *testing.T) semanticCertificate {
	t.Helper()
	paths := rootPathsForTest(t)
	semantic, err := executeExperiment(paths.C659, paths.C680)
	if err != nil {
		t.Fatalf("executeExperiment: %v", err)
	}
	return semantic
}

func TestFixedPlusOrientationAndReindex(t *testing.T) {
	paths := rootPathsForTest(t)
	c659Root, err := loadRootCandidate(paths.C659, declaredRootSpecs[0])
	if err != nil {
		t.Fatal(err)
	}
	for _, slot := range plusRootSlots {
		oriented, err := orientTerm(c659Root.Scheme.Term(slot), plusOrientation)
		if err != nil {
			t.Fatal(err)
		}
		roundTrip, err := unorientTerm(oriented, plusOrientation)
		if err != nil {
			t.Fatal(err)
		}
		got, err := termWords(roundTrip)
		if err != nil {
			t.Fatal(err)
		}
		want, err := termWords(c659Root.Scheme.Term(slot))
		if err != nil {
			t.Fatal(err)
		}
		if got != want {
			t.Fatalf("slot %d orientation round trip = %v, want %v", slot, got, want)
		}
	}
	if _, err := orientTerm(c659Root.Scheme.Term(7), [3]int{0, 0, 1}); err == nil {
		t.Fatal("orientTerm accepted a repeated position")
	}
	if _, err := unorientTerm(c659Root.Scheme.Term(7), [3]int{0, 1, 3}); err == nil {
		t.Fatal("unorientTerm accepted an out-of-range position")
	}
	plus, err := constructFixedPlus(c659Root.Scheme)
	if err != nil {
		t.Fatal(err)
	}
	if plus.Certificate.Descriptor.OrientationPositions != [3]int{0, 2, 1} {
		t.Fatalf("orientation = %v", plus.Certificate.Descriptor.OrientationPositions)
	}
	if plus.Certificate.Child.UnorderedCanonicalSHA256 != testPlusChildSHA256 {
		t.Fatalf("child hash = %s", plus.Certificate.Child.UnorderedCanonicalSHA256)
	}
	if !slices.Equal(plus.Certificate.Replacement.InsertedTerms, testPlusInserted) {
		t.Fatalf("insertions = %v", plus.Certificate.Replacement.InsertedTerms)
	}
	if !slices.Equal(plus.Certificate.OutputOrder.InsertionResultSlots, []int{45, 46, 47}) {
		t.Fatalf("insertion slots = %v", plus.Certificate.OutputOrder.InsertionResultSlots)
	}
	if len(plus.Certificate.OutputOrder.SurvivorParentSlots) != 45 {
		t.Fatalf("survivor count = %d", len(plus.Certificate.OutputOrder.SurvivorParentSlots))
	}
	for resultSlot, rootSlot := range plus.Certificate.OutputOrder.SurvivorParentSlots {
		got, err := termWords(plus.Scheme.Term(resultSlot))
		if err != nil {
			t.Fatal(err)
		}
		want, err := termWords(c659Root.Scheme.Term(rootSlot))
		if err != nil {
			t.Fatal(err)
		}
		if got != want {
			t.Fatalf("child survivor %d = %v, root slot %d = %v", resultSlot, got, rootSlot, want)
		}
	}
	for index, slot := range plus.Certificate.OutputOrder.InsertionResultSlots {
		got, err := termWords(plus.Scheme.Term(slot))
		if err != nil {
			t.Fatal(err)
		}
		if got != testPlusInserted[index] {
			t.Fatalf("child insertion slot %d = %v, want %v", slot, got, testPlusInserted[index])
		}
	}
}

func TestCanonicalEncodingAndBindings(t *testing.T) {
	first := testTerm(t, wordTriple{1, 256, 2})
	second := testTerm(t, wordTriple{256, 1, 1})
	scheme, err := tensor.NewScheme([]tensor.RankOneTerm{second, first})
	if err != nil {
		t.Fatal(err)
	}
	encoded, err := canonicalBytes(scheme)
	if err != nil {
		t.Fatal(err)
	}
	expected := make([]byte, 0, 20)
	for _, value := range []uint16{4, 4, 4, 2, 1, 256, 2, 256, 1, 1} {
		expected = binary.LittleEndian.AppendUint16(expected, value)
	}
	if !bytes.Equal(encoded, expected) {
		t.Fatalf("canonical bytes = %x, want %x", encoded, expected)
	}
	if bytes.Compare(encoded[8:14], encoded[14:20]) <= 0 {
		t.Fatal("fixture does not discriminate numeric tuple sorting from little-endian byte sorting")
	}
	paths := rootPathsForTest(t)
	c659Root, err := loadRootCandidate(paths.C659, declaredRootSpecs[0])
	if err != nil {
		t.Fatal(err)
	}
	ordered, err := orderedFactorMajorBytes(c659Root.Scheme)
	if err != nil {
		t.Fatal(err)
	}
	if sha256Hex(ordered) != testC659OrderedPayloadSHA256 {
		t.Fatalf("ordered c659 root hash = %s", sha256Hex(ordered))
	}
	canonical, err := canonicalBytes(c659Root.Scheme)
	if err != nil {
		t.Fatal(err)
	}
	if sha256Hex(canonical) != testC659UnorderedSHA256 {
		t.Fatalf("unordered c659 root hash = %s", sha256Hex(canonical))
	}
	words, err := schemeWords(c659Root.Scheme)
	if err != nil {
		t.Fatal(err)
	}
	for mode := range 3 {
		for slot := range c659Root.Scheme.TermCount() {
			offset := 8 + 2*(mode*c659Root.Scheme.TermCount()+slot)
			if got := binary.LittleEndian.Uint16(ordered[offset : offset+2]); got != words[slot][mode] {
				t.Fatalf("factor-major word mode %d slot %d = %d, want %d", mode, slot, got, words[slot][mode])
			}
		}
	}
	for offset := 14; offset < len(canonical); offset += 6 {
		prior := wordTriple{
			binary.LittleEndian.Uint16(canonical[offset-6 : offset-4]),
			binary.LittleEndian.Uint16(canonical[offset-4 : offset-2]),
			binary.LittleEndian.Uint16(canonical[offset-2 : offset]),
		}
		current := wordTriple{
			binary.LittleEndian.Uint16(canonical[offset : offset+2]),
			binary.LittleEndian.Uint16(canonical[offset+2 : offset+4]),
			binary.LittleEndian.Uint16(canonical[offset+4 : offset+6]),
		}
		if compareTriples(prior, current) > 0 {
			t.Fatalf("canonical terms are not numerically sorted at byte offset %d", offset)
		}
	}
}

func TestProductionConstantsMatchIndependentLiterals(t *testing.T) {
	stringChecks := []struct {
		name string
		got  string
		want string
	}{
		{name: "c659 raw SHA-256", got: expectedC659RawSHA256, want: testC659RawSHA256},
		{name: "c680 raw SHA-256", got: expectedC680RawSHA256, want: testC680RawSHA256},
		{name: "c659 ordered SHA-256", got: expectedC659OrderedFactorMajorSHA256, want: testC659OrderedPayloadSHA256},
		{name: "c680 ordered SHA-256", got: expectedC680OrderedFactorMajorSHA256, want: testC680OrderedPayloadSHA256},
		{name: "c659 unordered SHA-256", got: expectedC659UnorderedCanonicalSHA256, want: testC659UnorderedSHA256},
		{name: "c680 unordered SHA-256", got: expectedC680UnorderedCanonicalSHA256, want: testC680UnorderedSHA256},
		{name: "Plus child SHA-256", got: expectedPlusChildSHA256, want: testPlusChildSHA256},
		{name: "prior scan output rule", got: priorScanOutputRule, want: testPriorScanOutputRule},
		{name: "semantic SHA-256", got: expectedSemanticSHA256, want: testSemanticSHA256},
		{name: "complete output SHA-256", got: expectedCompleteOutputSHA256, want: testCompleteOutputSHA256},
		{name: "usage", got: usage, want: testUsage},
	}
	for _, check := range stringChecks {
		if check.got != check.want {
			t.Fatalf("production %s = %q, independent test literal = %q", check.name, check.got, check.want)
		}
	}
	intChecks := []struct {
		name string
		got  int
		want int
	}{
		{name: "c659 raw bytes", got: expectedC659RawBytes, want: testC659RawBytes},
		{name: "c680 raw bytes", got: expectedC680RawBytes, want: testC680RawBytes},
		{name: "root ordered payload bytes", got: expectedRootOrderedFactorMajorPayloadBytes, want: testRootOrderedPayloadBytes},
		{name: "candidate count", got: expectedCandidateCount, want: testCandidateCount},
		{name: "accepted count", got: expectedAcceptedCount, want: testAcceptedCount},
		{name: "rejected count", got: expectedRejectedCount, want: testRejectedCount},
		{name: "unique output count", got: expectedUniqueOutputCount, want: testUniqueOutputCount},
		{name: "maximal class count", got: expectedMaximalClassCount, want: testMaximalClassCount},
		{name: "defect-zero count", got: expectedDefectZeroCount, want: testDefectZeroCount},
		{name: "defect-one count", got: expectedDefectOneCount, want: testDefectOneCount},
		{name: "defect-at-least-two count", got: expectedDefectAtLeastTwoCount, want: testDefectAtLeastTwoCount},
		{name: "reduction count", got: expectedReductionCount, want: testReductionCount},
	}
	for _, check := range intChecks {
		if check.got != check.want {
			t.Fatalf("production %s = %d, independent test literal = %d", check.name, check.got, check.want)
		}
	}
	if len(expectedFlips) != len(testAcceptedAttempts) {
		t.Fatalf("production accepted registrations = %d, independent test literals = %d", len(expectedFlips), len(testAcceptedAttempts))
	}
	for index, want := range testAcceptedAttempts {
		if expectedFlips[index].Descriptor != want.Descriptor || expectedFlips[index].Hash != want.SHA256 {
			t.Fatalf("production accepted registration %d = %+v, independent test literal = %+v", index, expectedFlips[index], want)
		}
	}
	if !slices.Equal(expectedPlusInserted, testPlusInserted) {
		t.Fatalf("production Plus insertions = %v, independent test literals = %v", expectedPlusInserted, testPlusInserted)
	}
	if !reflect.DeepEqual(expectedReductions, testReductionInsertions) {
		t.Fatalf("production reduction registrations = %v, independent test literals = %v", expectedReductions, testReductionInsertions)
	}
}

func TestDeclaredRootAuthenticationAndSelection(t *testing.T) {
	paths := rootPathsForTest(t)
	c659, err := loadRootCandidate(paths.C659, declaredRootSpecs[0])
	if err != nil {
		t.Fatal(err)
	}
	c680, err := loadRootCandidate(paths.C680, declaredRootSpecs[1])
	if err != nil {
		t.Fatal(err)
	}
	candidates := [2]rootState{c659, c680}
	for index, want := range []struct {
		role      string
		raw       string
		ordered   string
		unordered string
	}{
		{role: c659RootRole, raw: testC659RawSHA256, ordered: testC659OrderedPayloadSHA256, unordered: testC659UnorderedSHA256},
		{role: c680RootRole, raw: testC680RawSHA256, ordered: testC680OrderedPayloadSHA256, unordered: testC680UnorderedSHA256},
	} {
		candidate := candidates[index]
		certificate := candidate.Certificate
		if certificate.Role != want.role || certificate.RawBytes != testC659RawBytes || certificate.RawSHA256 != want.raw || certificate.OrderedFactorMajorPayloadBytes != testRootOrderedPayloadBytes || certificate.OrderedFactorMajorSHA256 != want.ordered || certificate.UnorderedCanonicalSHA256 != want.unordered {
			t.Fatalf("candidate %d certificate = %+v", index, certificate)
		}
		if certificate.Ring != "GF(2)" || certificate.Dimensions != [3]int{4, 4, 4} || certificate.TermCount != 47 {
			t.Fatalf("candidate %d shape/ring = %+v", index, certificate)
		}
		if !certificate.Checks.BrentReplay || !certificate.Checks.NonzeroTerms || !certificate.Checks.DistinctRankOneTerms {
			t.Fatalf("candidate %d checks = %+v", index, certificate.Checks)
		}
		literal := certificate.LiteralFactorScreening
		if literal.FactorOccurrences != 141 || literal.NonzeroFactors != 141 || literal.RepeatedClasses != 0 || literal.RepeatedPairs != 0 {
			t.Fatalf("candidate %d literal factor screening = %+v", index, literal)
		}
	}
	selection, selected, err := selectDeclaredRoots(candidates, c659RootID)
	if err != nil {
		t.Fatal(err)
	}
	if selected.Certificate.ID != c659RootID || selection.SelectedRootID != c659RootID || selection.RequiredSelectedRootID != c659RootID || !selection.RequiredSelectionVerified {
		t.Fatalf("selection = %+v", selection)
	}
	comparison := selection.Comparison
	if comparison.Rule != "lexicographically compare the bound 64-character lowercase SHA-256 hexadecimal digest strings bytewise in ASCII order; the lower character at the first difference wins" || comparison.DigestEncoding != "64-character lowercase hexadecimal SHA-256 digest of the complete ordered factor-major root payload" {
		t.Fatalf("comparison rule = %+v", comparison)
	}
	if comparison.CompareResult != -1 || comparison.Result != "left_digest_less_than_right_digest" || comparison.CommonPrefixCharacters != 2 {
		t.Fatalf("comparison = %+v", comparison)
	}
	if comparison.Left.RootID != c659RootID || comparison.Left.Digest != testC659OrderedPayloadSHA256 || comparison.Right.RootID != c680RootID || comparison.Right.Digest != testC680OrderedPayloadSHA256 {
		t.Fatalf("comparison digest bindings = %+v / %+v", comparison.Left, comparison.Right)
	}
	if comparison.FirstDifference == nil || *comparison.FirstDifference != (rootDigestCharacterDifference{ZeroBasedPosition: 2, LeftCharacter: "1", RightCharacter: "e", LeftASCII: 49, RightASCII: 101}) {
		t.Fatalf("first difference = %+v", comparison.FirstDifference)
	}
}

func TestRootSelectionUsesDigestLexicographicOrder(t *testing.T) {
	const (
		leftDigest  = "6e340b9cffb37a989ca544e6bb780a2c78901d3fb33738768511a30617afa01d"
		rightDigest = "4bf5122f344554c53bde2ebb8cd2b7e3d1600ad631c385a5d7cce23c7785459a"
	)
	makeCandidate := func(index int, payload byte, digest string) rootState {
		spec := declaredRootSpecs[index]
		return rootState{
			OrderedFactorMajorPayloadBytes: []byte{payload},
			Certificate: rootCandidateCertificate{
				ArgumentPosition:               spec.ArgumentPosition,
				Role:                           spec.Role,
				ID:                             spec.ID,
				OrderedFactorMajorPayloadBytes: 1,
				OrderedFactorMajorSHA256:       digest,
			},
		}
	}
	left := makeCandidate(0, 0, leftDigest)
	right := makeCandidate(1, 1, rightDigest)
	if sha256Hex(left.OrderedFactorMajorPayloadBytes) != leftDigest || sha256Hex(right.OrderedFactorMajorPayloadBytes) != rightDigest {
		t.Fatal("synthetic digest literals do not bind their payloads")
	}
	if bytes.Compare(left.OrderedFactorMajorPayloadBytes, right.OrderedFactorMajorPayloadBytes) >= 0 || strings.Compare(leftDigest, rightDigest) <= 0 {
		t.Fatal("synthetic roots do not oppose payload byte order and digest string order")
	}
	selection, selected, err := selectDeclaredRoots([2]rootState{left, right}, c680RootID)
	if err != nil {
		t.Fatal(err)
	}
	if selected.Certificate.ID != c680RootID || selection.SelectedRootID != c680RootID || !selection.RequiredSelectionVerified {
		t.Fatalf("digest-selected root = %+v", selection)
	}
	comparison := selection.Comparison
	if comparison.CompareResult != 1 || comparison.Result != "right_digest_less_than_left_digest" || comparison.CommonPrefixCharacters != 0 {
		t.Fatalf("digest comparison = %+v", comparison)
	}
	if comparison.FirstDifference == nil || *comparison.FirstDifference != (rootDigestCharacterDifference{ZeroBasedPosition: 0, LeftCharacter: "6", RightCharacter: "4", LeftASCII: 54, RightASCII: 52}) {
		t.Fatalf("digest first difference = %+v", comparison.FirstDifference)
	}
	for _, malformedDigest := range []struct {
		name   string
		digest string
		want   string
	}{
		{name: "short", digest: leftDigest[:63], want: "want 64"},
		{name: "uppercase", digest: "E" + leftDigest[1:], want: "want lowercase hexadecimal"},
	} {
		malformed := left
		malformed.Certificate.OrderedFactorMajorSHA256 = malformedDigest.digest
		if _, _, err := selectDeclaredRoots([2]rootState{malformed, right}, c680RootID); err == nil || !strings.Contains(err.Error(), "ordered factor-major SHA-256 binding") || !strings.Contains(err.Error(), malformedDigest.want) {
			t.Fatalf("%s digest error = %v", malformedDigest.name, err)
		}
	}
}

func TestPriorScanOutputRuleUsesDigestStringOrder(t *testing.T) {
	firstCanonical := []byte{0}
	secondCanonical := []byte{1}
	const (
		firstDigest  = "6e340b9cffb37a989ca544e6bb780a2c78901d3fb33738768511a30617afa01d"
		secondDigest = "4bf5122f344554c53bde2ebb8cd2b7e3d1600ad631c385a5d7cce23c7785459a"
	)
	if sha256Hex(firstCanonical) != firstDigest || sha256Hex(secondCanonical) != secondDigest {
		t.Fatal("fixture digest literals do not bind their canonical bytes")
	}
	if bytes.Compare(firstCanonical, secondCanonical) >= 0 || strings.Compare(firstDigest, secondDigest) <= 0 {
		t.Fatal("fixture does not oppose canonical byte order and lowercase digest string order")
	}
	outputs := []struct {
		canonical []byte
		digest    string
	}{
		{canonical: firstCanonical, digest: firstDigest},
		{canonical: secondCanonical, digest: secondDigest},
	}
	selected := outputs[0]
	for _, output := range outputs[1:] {
		if strings.Compare(output.digest, selected.digest) < 0 {
			selected = output
		}
	}
	if !bytes.Equal(selected.canonical, secondCanonical) || selected.digest != secondDigest {
		t.Fatalf("digest-order selection = canonical %x digest %s", selected.canonical, selected.digest)
	}
	binding := makePriorScanBinding()
	if binding.Selection.OutputRule != testPriorScanOutputRule {
		t.Fatalf("prior scan output rule = %q, want %q", binding.Selection.OutputRule, testPriorScanOutputRule)
	}
	if binding.Selection.ChildSHA256 != testPlusChildSHA256 || binding.C659PlusScanRecomputedByCommand || binding.C659PlusOutputMinimumProvedByCommand {
		t.Fatalf("prior scan selection binding = %+v", binding)
	}
}

func TestRootSelectionMismatchFailsClosed(t *testing.T) {
	paths := rootPathsForTest(t)
	c659, err := loadRootCandidate(paths.C659, declaredRootSpecs[0])
	if err != nil {
		t.Fatal(err)
	}
	c680, err := loadRootCandidate(paths.C680, declaredRootSpecs[1])
	if err != nil {
		t.Fatal(err)
	}
	c659Payload := append([]byte(nil), c659.OrderedFactorMajorPayloadBytes...)
	c659.OrderedFactorMajorPayloadBytes = append([]byte(nil), c680.OrderedFactorMajorPayloadBytes...)
	c659.Certificate.OrderedFactorMajorPayloadBytes = len(c659.OrderedFactorMajorPayloadBytes)
	c659.Certificate.OrderedFactorMajorSHA256 = sha256Hex(c659.OrderedFactorMajorPayloadBytes)
	c680.OrderedFactorMajorPayloadBytes = c659Payload
	c680.Certificate.OrderedFactorMajorPayloadBytes = len(c680.OrderedFactorMajorPayloadBytes)
	c680.Certificate.OrderedFactorMajorSHA256 = sha256Hex(c680.OrderedFactorMajorPayloadBytes)
	selection, _, err := selectDeclaredRoots([2]rootState{c659, c680}, c659RootID)
	if err == nil || !strings.Contains(err.Error(), "root selection chose") || !strings.Contains(err.Error(), "require "+c659RootID) {
		t.Fatalf("selection mismatch error = %v", err)
	}
	if selection.SelectedRootID != c680RootID || selection.RequiredSelectionVerified {
		t.Fatalf("mismatched selection = %+v", selection)
	}
}

func TestDeterministicGF2Elimination(t *testing.T) {
	rows := []uint16{0, 273, 273, 273, 273, 0, 0, 273, 10405, 0, 10676, 10405, 10405, 0, 10405, 10405}
	first := eliminateRows(rows)
	second := eliminateRows(append([]uint16(nil), rows...))
	if !reflect.DeepEqual(first, second) {
		t.Fatalf("elimination is not deterministic: %v and %v", first, second)
	}
	if first.Rank != 2 {
		t.Fatalf("rank = %d, want 2", first.Rank)
	}
	if !slices.Equal(first.PivotColumns, []int{8, 13}) {
		t.Fatalf("pivots = %v, want [8 13]", first.PivotColumns)
	}
	if !slices.Equal(first.BasisRows, []uint16{273, 10405}) {
		t.Fatalf("basis rows = %v", first.BasisRows)
	}
	if rowsHash(rows) != "5143a461215653283ee13b3fe3daf72288fd2f7bd90800390db3baa8739e521a" {
		t.Fatalf("row hash = %s", rowsHash(rows))
	}
	deficient := []uint16{0, 0, 0, 0, 0, 0, 0, 0, 10676, 0, 10676, 10676, 10676, 0, 10676, 10676}
	got := eliminateRows(deficient)
	if got.Rank != 1 || !slices.Equal(got.PivotColumns, []int{13}) || !slices.Equal(got.BasisRows, []uint16{10676}) {
		t.Fatalf("deficient elimination = %+v", got)
	}
	if rowsHash(deficient) != "6cc7d27a222bd831ad14bdb9870aca5dee05420c520e0611c49ca323f8ec7131" {
		t.Fatalf("deficient row hash = %s", rowsHash(deficient))
	}
}

func TestOrdinaryFlipRejectionClassificationIsStructural(t *testing.T) {
	first := testTerm(t, wordTriple{1, 2, 4})
	equalShared := testTerm(t, wordTriple{1, 8, 16})
	unequalShared := testTerm(t, wordTriple{3, 8, 16})
	zeroShared := testTerm(t, wordTriple{0, 8, 16})

	makeScheme := func(second tensor.RankOneTerm) tensor.Scheme {
		t.Helper()
		scheme, err := tensor.NewScheme([]tensor.RankOneTerm{first, second})
		if err != nil {
			t.Fatal(err)
		}
		return scheme
	}
	descriptor := flipDescriptor{FirstSlot: 0, SecondSlot: 1, SharedMode: 0, Coefficient: 1}
	unequal := makeScheme(unequalShared)
	if _, err := tensor.NewOrdinaryFlipReplacement(unequal, tensor.SharedFirst, 0, 1, 1); err == nil {
		t.Fatal("ordinary flip constructor accepted unequal shared factors")
	}
	if !ordinaryFlipHasLiteralInequality(unequal, descriptor) {
		t.Fatal("unequal nonzero shared factors were not structurally classified")
	}
	equal := makeScheme(equalShared)
	if ordinaryFlipHasLiteralInequality(equal, descriptor) {
		t.Fatal("equal nonzero shared factors were classified as unequal")
	}
	zeroFirst, err := tensor.NewScheme([]tensor.RankOneTerm{zeroShared, unequalShared})
	if err != nil {
		t.Fatal(err)
	}
	if _, err := tensor.NewOrdinaryFlipReplacement(zeroFirst, tensor.SharedFirst, 0, 1, 1); err == nil {
		t.Fatal("ordinary flip constructor accepted a zero first shared factor")
	}
	if ordinaryFlipHasLiteralInequality(zeroFirst, descriptor) {
		t.Fatal("zero first shared factor was classified as literal inequality")
	}
	zeroBoth, err := tensor.NewScheme([]tensor.RankOneTerm{zeroShared, zeroShared})
	if err != nil {
		t.Fatal(err)
	}
	if ordinaryFlipHasLiteralInequality(zeroBoth, descriptor) {
		t.Fatal("equal zero shared factors were classified as literal inequality")
	}
	for _, invalid := range []flipDescriptor{
		{FirstSlot: 0, SecondSlot: 0, SharedMode: 0, Coefficient: 1},
		{FirstSlot: 0, SecondSlot: 1, SharedMode: 3, Coefficient: 1},
		{FirstSlot: 0, SecondSlot: 1, SharedMode: 0, Coefficient: 0},
	} {
		if ordinaryFlipHasLiteralInequality(unequal, invalid) {
			t.Fatalf("invalid descriptor %+v was classified as literal inequality", invalid)
		}
	}
}

func TestCompleteAttemptStreamAndPreregisteredOutputs(t *testing.T) {
	semantic := experimentForTest(t)
	if len(semantic.Attempts) != testCandidateCount {
		t.Fatalf("attempt count = %d", len(semantic.Attempts))
	}
	acceptedBySequence := make(map[int]acceptedAttemptExpectation, len(testAcceptedAttempts))
	for _, expected := range testAcceptedAttempts {
		acceptedBySequence[expected.Sequence] = expected
	}
	sequence := 0
	accepted := 0
	for first := range 48 {
		for second := range 48 {
			if first == second {
				continue
			}
			for mode := range 3 {
				attempt := semantic.Attempts[sequence]
				wantDescriptor := flipDescriptor{FirstSlot: first, SecondSlot: second, SharedMode: mode, Coefficient: 1}
				if attempt.Sequence != sequence || attempt.Descriptor != wantDescriptor {
					t.Fatalf("attempt %d = sequence %d descriptor %v, want %v", sequence, attempt.Sequence, attempt.Descriptor, wantDescriptor)
				}
				if want, ok := acceptedBySequence[sequence]; ok {
					accepted++
					if attempt.Descriptor != want.Descriptor || attempt.Outcome != "accepted" || attempt.Rejection != nil || attempt.AcceptedRecord == nil || *attempt.AcceptedRecord != accepted-1 || attempt.OutputSHA256 == nil || *attempt.OutputSHA256 != want.SHA256 {
						t.Fatalf("accepted attempt %d = %+v, want %+v", sequence, attempt, want)
					}
				} else if attempt.Outcome != "rejected" || attempt.Rejection == nil || attempt.Rejection.Code != "shared_factors_not_literally_equal" || attempt.AcceptedRecord != nil || attempt.OutputSHA256 != nil {
					t.Fatalf("rejected attempt %d = %+v", sequence, attempt)
				}
				sequence++
			}
		}
	}
	if sequence != testCandidateCount || accepted != testAcceptedCount {
		t.Fatalf("stream ended at %d with %d accepted", sequence, accepted)
	}
	if len(semantic.Records) != len(testAcceptedAttempts) || len(semantic.UniqueOutputs) != len(testAcceptedAttempts) {
		t.Fatalf("records/outputs = %d/%d", len(semantic.Records), len(semantic.UniqueOutputs))
	}
	for index, expected := range testAcceptedAttempts {
		record := semantic.Records[index]
		if record.AttemptSequence != expected.Sequence || record.Descriptor != expected.Descriptor || record.Result.UnorderedCanonicalSHA256 != expected.SHA256 {
			t.Fatalf("record %d = sequence %d descriptor %v hash %s", index, record.AttemptSequence, record.Descriptor, record.Result.UnorderedCanonicalSHA256)
		}
		if record.UniqueOutput != index || semantic.UniqueOutputs[index].UnorderedSHA256 != expected.SHA256 {
			t.Fatalf("record/output index %d did not preserve first-seen lineage", index)
		}
		if !record.Result.Checks.BrentReplay || !record.Result.Checks.NonzeroTerms || !record.Result.Checks.DistinctRankOneTerms {
			t.Fatalf("record %d checks = %+v", index, record.Result.Checks)
		}
		if len(semantic.UniqueOutputs[index].Lineages) != 1 || semantic.UniqueOutputs[index].Lineages[0].Record != index || semantic.UniqueOutputs[index].Lineages[0].AttemptSequence != expected.Sequence {
			t.Fatalf("output %d lineages = %+v", index, semantic.UniqueOutputs[index].Lineages)
		}
	}
}

func TestMaximalClassesRowsAndReductions(t *testing.T) {
	semantic := experimentForTest(t)
	type classKey struct {
		Output string
		Mode   int
		Factor uint16
	}
	type classExpected struct {
		Slots  []int
		Hash   string
		Rank   int
		Defect int
	}
	expected := map[classKey]classExpected{
		{testFirstFlipSHA256, 0, 50360}:  {[]int{46, 47}, "5143a461215653283ee13b3fe3daf72288fd2f7bd90800390db3baa8739e521a", 2, 0},
		{testFirstFlipSHA256, 1, 55710}:  {[]int{45, 46}, "1812fa803ae4c459ed981b55e06de0e3a850d58b01e90d61baaa7fd83c7f46f4", 2, 0},
		{testSecondFlipSHA256, 0, 50360}: {[]int{45, 47}, "6cc7d27a222bd831ad14bdb9870aca5dee05420c520e0611c49ca323f8ec7131", 1, 1},
		{testSecondFlipSHA256, 1, 56576}: {[]int{45, 47}, "388ab351fb4dd5208c62218437a2c3f1fa4f4bd0134f1dc592f1725f22afe72a", 1, 1},
		{testSecondFlipSHA256, 2, 273}:   {[]int{46, 47}, "f6ba41fe1b7fc823191221da9744ced71e29cf3d87897c32ce5929d396131fa9", 2, 0},
		{testThirdFlipSHA256, 0, 50360}:  {[]int{46, 47}, "5143a461215653283ee13b3fe3daf72288fd2f7bd90800390db3baa8739e521a", 2, 0},
		{testThirdFlipSHA256, 1, 55710}:  {[]int{45, 46}, "88124e6268407432f0eb930881943672b29fd972462db0d3560aaec33a11ae7a", 1, 1},
		{testThirdFlipSHA256, 2, 273}:    {[]int{45, 46}, "7d7726b7348552da99007c041c396a11b3e6ab16dcc1ea52d8788851336dac56", 1, 1},
		{testFourthFlipSHA256, 1, 56576}: {[]int{45, 47}, "1812fa803ae4c459ed981b55e06de0e3a850d58b01e90d61baaa7fd83c7f46f4", 2, 0},
		{testFourthFlipSHA256, 2, 273}:   {[]int{46, 47}, "f6ba41fe1b7fc823191221da9744ced71e29cf3d87897c32ce5929d396131fa9", 2, 0},
	}
	seen := make(map[classKey]bool)
	classes := 0
	positive := 0
	for _, output := range semantic.UniqueOutputs {
		for screenIndex, screen := range output.Screens {
			classes++
			key := classKey{output.UnorderedSHA256, screen.SharedMode, screen.SharedFactorWord}
			want, ok := expected[key]
			if !ok {
				t.Fatalf("unexpected class %+v", key)
			}
			if seen[key] {
				t.Fatalf("duplicate class %+v", key)
			}
			seen[key] = true
			if screen.Screen != screenIndex || !screen.Nonzero || !screen.Maximal || len(screen.Slots) < 2 || len(screen.Rows) != 16 {
				t.Fatalf("class %+v metadata = %+v", key, screen)
			}
			if !slices.Equal(screen.Slots, want.Slots) || screen.RowsSHA256 != want.Hash || rowsHash(screen.Rows) != want.Hash || screen.Rank != want.Rank || screen.Defect != want.Defect || screen.Elimination.Rank != want.Rank {
				t.Fatalf("class %+v = slots %v hash %s rank %d defect %d", key, screen.Slots, screen.RowsSHA256, screen.Rank, screen.Defect)
			}
			if screen.Defect == 0 {
				if !screen.ProperSubsetsExcluded || screen.Reduction != nil {
					t.Fatalf("defect-zero class %+v did not record proper-subset exclusion", key)
				}
				continue
			}
			positive++
			if screen.ProperSubsetsExcluded || screen.Reduction == nil {
				t.Fatalf("positive class %+v reduction = %+v", key, screen.Reduction)
			}
			reduction := screen.Reduction
			if reduction.Replacement.Constructor != "tensor.NewSharedFactorReduction" || !reduction.Replacement.TensorIdentityVerified {
				t.Fatalf("class %+v witness = %+v", key, reduction.Replacement)
			}
			if reduction.Result.TermCount != 47 || reduction.Result.UnorderedCanonicalSHA256 != testC659UnorderedSHA256 {
				t.Fatalf("class %+v result = %d %s", key, reduction.Result.TermCount, reduction.Result.UnorderedCanonicalSHA256)
			}
			if !reduction.Result.Checks.BrentReplay || !reduction.Result.Checks.NonzeroTerms || !reduction.Result.Checks.DistinctRankOneTerms {
				t.Fatalf("class %+v result checks = %+v", key, reduction.Result.Checks)
			}
			registered := -1
			for index, expectedReduction := range testReductionInsertions {
				if expectedReduction.OutputHash == output.UnorderedSHA256 && expectedReduction.SharedMode == screen.SharedMode {
					registered = index
					break
				}
			}
			if registered < 0 || !slices.Equal(reduction.Replacement.InsertedTerms, []wordTriple{testReductionInsertions[registered].Inserted}) {
				t.Fatalf("class %+v inserted terms = %v", key, reduction.Replacement.InsertedTerms)
			}
		}
	}
	if classes != testMaximalClassCount || len(seen) != len(expected) || positive != testReductionCount {
		t.Fatalf("class totals = classes %d seen %d positive %d", classes, len(seen), positive)
	}
	coverage := semantic.Coverage
	if coverage.MaximalClasses != 10 || coverage.DefectZeroClasses != 6 || coverage.DefectOneClasses != 4 || coverage.DefectAtLeastTwoClasses != 0 || coverage.ReplayedPositiveReductions != 4 || !coverage.Complete {
		t.Fatalf("coverage = %+v", coverage)
	}
}

func TestSemanticDigestAndOutputDeterminism(t *testing.T) {
	semantic := experimentForTest(t)
	first, err := makeReport(semantic)
	if err != nil {
		t.Fatal(err)
	}
	second, err := makeReport(semantic)
	if err != nil {
		t.Fatal(err)
	}
	if first.Envelope.SemanticSHA256 != testSemanticSHA256 || second.Envelope.SemanticSHA256 != testSemanticSHA256 {
		t.Fatalf("semantic digests = %s and %s", first.Envelope.SemanticSHA256, second.Envelope.SemanticSHA256)
	}
	if !semantic.PriorScan.DeclaredTwoRootSelectionClosedByCommand || semantic.PriorScan.C659PlusScanRecomputedByCommand || semantic.PriorScan.C659PlusOutputMinimumProvedByCommand || semantic.PriorScan.Selection.OutputRule != testPriorScanOutputRule || !strings.Contains(semantic.PriorScan.Selection.RootRule, "least 64-character lowercase SHA-256 hexadecimal digest string") || !strings.Contains(semantic.PriorScan.Selection.RootRule, "bytewise in ASCII order") || !strings.Contains(semantic.PriorScan.BindingStatement, "prior c659 variant-0 Plus scan remains bound") || !strings.Contains(semantic.PriorScan.BindingStatement, "not recomputed") {
		t.Fatalf("prior scan provenance = %+v", semantic.PriorScan)
	}
	firstJSON, err := json.Marshal(first)
	if err != nil {
		t.Fatal(err)
	}
	secondJSON, err := json.Marshal(second)
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(firstJSON, secondJSON) {
		t.Fatal("repeated report serialization differs")
	}
	paths := rootPathsForTest(t)
	replayed, err := executeExperiment(paths.C659, paths.C680)
	if err != nil {
		t.Fatal(err)
	}
	replayedJSON, err := json.Marshal(replayed)
	if err != nil {
		t.Fatal(err)
	}
	semanticJSON, err := json.Marshal(semantic)
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(semanticJSON, replayedJSON) {
		t.Fatal("independent experiment replays differ")
	}
	first.Runtime.Measurement = "variable"
	first.Envelope.SemanticSHA256 = "not-the-semantic-digest"
	recomputed, err := makeReport(first.Semantic)
	if err != nil {
		t.Fatal(err)
	}
	if recomputed.Envelope.SemanticSHA256 != testSemanticSHA256 {
		t.Fatalf("runtime/envelope mutation changed digest to %s", recomputed.Envelope.SemanticSHA256)
	}
}

func TestCLIPrettyOutputSHA256(t *testing.T) {
	paths := rootPathsForTest(t)
	var output bytes.Buffer
	if err := run([]string{paths.C659, paths.C680}, &output); err != nil {
		t.Fatal(err)
	}
	if got := sha256Hex(output.Bytes()); got != testCompleteOutputSHA256 {
		t.Fatalf("pretty CLI output SHA-256 = %s, want %s", got, testCompleteOutputSHA256)
	}
}

func TestCLIHelpAndArity(t *testing.T) {
	for _, argument := range []string{"-h", "--help"} {
		var output bytes.Buffer
		if err := run([]string{argument}, &output); err != nil {
			t.Fatalf("run(%q): %v", argument, err)
		}
		if output.String() != testUsage {
			t.Fatalf("run(%q) output = %q, want %q", argument, output.String(), testUsage)
		}
	}
	for _, args := range [][]string{nil, {"one"}, {"one", "two", "three"}, {"-h", "extra", "path"}} {
		var output bytes.Buffer
		err := run(args, &output)
		if err == nil || !strings.Contains(err.Error(), "exactly two root paths in order c659 then c680") {
			t.Fatalf("run(%v) error = %v", args, err)
		}
		if output.String() != testUsage {
			t.Fatalf("run(%v) output = %q, want %q", args, output.String(), testUsage)
		}
	}
}

func TestRootAuthenticationFailClosedPrecedence(t *testing.T) {
	paths := rootPathsForTest(t)
	for index, fixture := range []struct {
		role          string
		path          string
		rawBytes      int
		rawSHA256     string
		orderedSHA256 string
		unordered     string
	}{
		{role: c659RootRole, path: paths.C659, rawBytes: testC659RawBytes, rawSHA256: testC659RawSHA256, orderedSHA256: testC659OrderedPayloadSHA256, unordered: testC659UnorderedSHA256},
		{role: c680RootRole, path: paths.C680, rawBytes: testC680RawBytes, rawSHA256: testC680RawSHA256, orderedSHA256: testC680OrderedPayloadSHA256, unordered: testC680UnorderedSHA256},
	} {
		spec := declaredRootSpecs[index]
		raw, err := os.ReadFile(fixture.path)
		if err != nil {
			t.Fatal(err)
		}
		if len(raw) != fixture.rawBytes || sha256Hex(raw) != fixture.rawSHA256 {
			t.Fatalf("independent %s fixture binding = %d bytes, SHA-256 %s", fixture.role, len(raw), sha256Hex(raw))
		}
		directory := t.TempDir()
		short := filepath.Join(directory, fixture.role+"-short.txt")
		if err := os.WriteFile(short, []byte("not a native scheme\n"), 0o600); err != nil {
			t.Fatal(err)
		}
		if _, err := loadRootCandidate(short, spec); err == nil || !strings.Contains(err.Error(), fixture.role+" root has 20 raw bytes") || strings.Contains(err.Error(), "parse declared") {
			t.Fatalf("short %s root error = %v", fixture.role, err)
		}

		exactMalformed := filepath.Join(directory, fixture.role+"-exact-malformed.txt")
		if err := os.WriteFile(exactMalformed, bytes.Repeat([]byte{'x'}, fixture.rawBytes), 0o600); err != nil {
			t.Fatal(err)
		}
		if _, err := loadRootCandidate(exactMalformed, spec); err == nil || !strings.Contains(err.Error(), "raw SHA-256") || strings.Contains(err.Error(), "parse declared") {
			t.Fatalf("exact-size malformed %s root error = %v", fixture.role, err)
		}

		oversized := filepath.Join(directory, fixture.role+"-oversized.txt")
		if err := os.WriteFile(oversized, append(append([]byte(nil), raw...), 'x'), 0o600); err != nil {
			t.Fatal(err)
		}
		if _, err := loadRootCandidate(oversized, spec); err == nil || !strings.Contains(err.Error(), fixture.role+" root has 4525 raw bytes") || strings.Contains(err.Error(), "raw SHA-256") || strings.Contains(err.Error(), "parse declared") {
			t.Fatalf("oversized %s root error = %v", fixture.role, err)
		}

		altered := append([]byte(nil), raw...)
		headerEnd := bytes.IndexByte(altered, '\n')
		coefficient := bytes.IndexAny(altered[headerEnd+1:], "01")
		if coefficient < 0 {
			t.Fatalf("%s root has no coefficient to alter", fixture.role)
		}
		coefficient += headerEnd + 1
		if altered[coefficient] == '0' {
			altered[coefficient] = '1'
		} else {
			altered[coefficient] = '0'
		}
		wrongRoot := filepath.Join(directory, fixture.role+"-wrong-root.txt")
		if err := os.WriteFile(wrongRoot, altered, 0o600); err != nil {
			t.Fatal(err)
		}
		if _, err := loadRootCandidate(wrongRoot, spec); err == nil || !strings.Contains(err.Error(), "raw SHA-256") || strings.Contains(err.Error(), "parse declared") {
			t.Fatalf("wrong authenticated %s root error = %v", fixture.role, err)
		}

		parserEquivalent := append([]byte(nil), raw...)
		space := bytes.IndexByte(parserEquivalent, ' ')
		if space < 0 {
			t.Fatalf("%s root has no space to mutate", fixture.role)
		}
		parserEquivalent[space] = '\t'
		if len(parserEquivalent) != fixture.rawBytes || sha256Hex(parserEquivalent) == fixture.rawSHA256 {
			t.Fatalf("%s parser-equivalent mutation did not change only the raw binding", fixture.role)
		}
		parsed, err := tensor.ParseNative(ring.Z2, bytes.NewReader(parserEquivalent))
		if err != nil {
			t.Fatalf("parse parser-equivalent %s mutation: %v", fixture.role, err)
		}
		ordered, err := orderedFactorMajorBytes(parsed)
		if err != nil {
			t.Fatal(err)
		}
		canonical, err := canonicalBytes(parsed)
		if err != nil {
			t.Fatal(err)
		}
		if len(ordered) != testRootOrderedPayloadBytes || sha256Hex(ordered) != fixture.orderedSHA256 || sha256Hex(canonical) != fixture.unordered {
			t.Fatalf("parser-equivalent %s mutation payload hashes = %d bytes, ordered %s, unordered %s", fixture.role, len(ordered), sha256Hex(ordered), sha256Hex(canonical))
		}
		parserEquivalentPath := filepath.Join(directory, fixture.role+"-parser-equivalent.txt")
		if err := os.WriteFile(parserEquivalentPath, parserEquivalent, 0o600); err != nil {
			t.Fatal(err)
		}
		if _, err := loadRootCandidate(parserEquivalentPath, spec); err == nil || !strings.Contains(err.Error(), "raw SHA-256") || strings.Contains(err.Error(), "parse declared") {
			t.Fatalf("parser-equivalent %s root authentication error = %v", fixture.role, err)
		}

		counter := &countingReader{reader: bytes.NewReader(bytes.Repeat([]byte{'x'}, fixture.rawBytes+100))}
		if _, _, err := readAuthenticatedRoot(counter, spec); err == nil || !strings.Contains(err.Error(), "4525 raw bytes") {
			t.Fatalf("bounded oversized %s read error = %v", fixture.role, err)
		}
		if counter.bytesRead != fixture.rawBytes+1 {
			t.Fatalf("bounded %s reader consumed %d bytes, want %d", fixture.role, counter.bytesRead, fixture.rawBytes+1)
		}

		sentinel := errors.New("injected read failure")
		reader := io.MultiReader(bytes.NewReader(bytes.Repeat([]byte{'x'}, fixture.rawBytes)), iotest.ErrReader(sentinel))
		if _, _, err := readAuthenticatedRoot(reader, spec); !errors.Is(err, sentinel) {
			t.Fatalf("%s read error = %v, want injected failure", fixture.role, err)
		}
	}
}

func TestBothRootPathsAreRequiredAndFailClosed(t *testing.T) {
	paths := rootPathsForTest(t)
	missing := filepath.Join(t.TempDir(), "absent-root.txt")
	for _, args := range [][]string{
		{missing, paths.C680},
		{paths.C659, missing},
		{paths.C680, paths.C659},
	} {
		var output bytes.Buffer
		err := run(args, &output)
		if err == nil {
			t.Fatalf("run(%v) accepted missing or role-swapped root", args)
		}
		if output.Len() != 0 {
			t.Fatalf("run(%v) emitted unauthenticated output: %q", args, output.String())
		}
	}
}

type countingReader struct {
	reader    io.Reader
	bytesRead int
}

func (r *countingReader) Read(buffer []byte) (int, error) {
	count, err := r.reader.Read(buffer)
	r.bytesRead += count
	return count, err
}

func testTerm(t *testing.T, words wordTriple) tensor.RankOneTerm {
	t.Helper()
	matrices := [3]tensor.Matrix{}
	for mode, word := range words {
		entries := make([]int, 16)
		for index := range 16 {
			entries[index] = int(word >> index & 1)
		}
		matrix, err := tensor.NewMatrix(ring.Z2, 4, 4, entries)
		if err != nil {
			t.Fatal(err)
		}
		matrices[mode] = matrix
	}
	term, err := tensor.NewRankOneTerm(matrices[0], matrices[1], matrices[2])
	if err != nil {
		t.Fatal(err)
	}
	return term
}

func compareTriples(first, second wordTriple) int {
	for mode := range 3 {
		if first[mode] < second[mode] {
			return -1
		}
		if first[mode] > second[mode] {
			return 1
		}
	}
	return 0
}
