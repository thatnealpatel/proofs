package main

import (
	"bytes"
	"encoding/hex"
	"errors"
	"io"
	"os"
	"path/filepath"
	"runtime"
	"slices"
	"strconv"
	"strings"
	"syscall"
	"testing"

	"patel.codes/proofs/internal/tensor"
)

type countingReader struct {
	calls int
}

func (reader *countingReader) Read([]byte) (int, error) {
	reader.calls++
	return 0, errors.New("unexpected stdin read")
}

type controlledWriter struct {
	limit int
	err   error
	value []byte
}

func (writer *controlledWriter) Write(value []byte) (int, error) {
	written := min(writer.limit, len(value))
	writer.value = append(writer.value, value[:written]...)
	return written, writer.err
}

func repositoryFile(id string) string {
	_, file, _, _ := runtime.Caller(0)
	return filepath.Join(filepath.Dir(file), "..", "..", filepath.FromSlash(id))
}

func encodeRoot(t *testing.T, words []triple) []byte {
	t.Helper()
	scheme, err := schemeFromWords(words)
	if err != nil {
		t.Fatal(err)
	}
	var encoded bytes.Buffer
	if err := tensor.WriteNative(&encoded, scheme); err != nil {
		t.Fatal(err)
	}
	return encoded.Bytes()
}

func decodeHex(t *testing.T, value string) []byte {
	t.Helper()
	decoded, err := hex.DecodeString(value)
	if err != nil {
		t.Fatal(err)
	}
	return decoded
}

func TestRunHelpArityAndStdinContract(t *testing.T) {
	for _, argument := range []string{"-h", "--help"} {
		stdin := &countingReader{}
		var stdout, stderr bytes.Buffer
		if err := run([]string{argument}, stdin, &stdout, &stderr); err != nil {
			t.Fatalf("%s: %v", argument, err)
		}
		if stdout.String() != usage || stderr.Len() != 0 || stdin.calls != 0 {
			t.Fatalf("%s produced stdout=%q stderr=%q stdin calls=%d", argument, stdout.String(), stderr.String(), stdin.calls)
		}
	}
	cases := [][]string{nil, {"root"}, {"a", "b"}, {"a", "b", "c", "d"}}
	for _, args := range cases {
		stdin := &countingReader{}
		var stdout, stderr bytes.Buffer
		err := run(args, stdin, &stdout, &stderr)
		if err == nil || !strings.Contains(err.Error(), "got "+strconv.Itoa(len(args))) {
			t.Fatalf("arity %d error = %v", len(args), err)
		}
		if stdout.Len() != 0 || stderr.String() != usage || stdin.calls != 0 {
			t.Fatalf("arity %d produced stdout=%q stderr=%q stdin calls=%d", len(args), stdout.String(), stderr.String(), stdin.calls)
		}
	}
	stdin := &countingReader{}
	var stdout, stderr bytes.Buffer
	err := run([]string{repositoryFile("missing-root"), "unused", "unused"}, stdin, &stdout, &stderr)
	if err == nil || !strings.Contains(err.Error(), "c659 root: open authenticated descriptor") {
		t.Fatalf("three-path failure = %v", err)
	}
	if stdin.calls != 0 || stdout.Len() != 0 || stderr.Len() != 0 {
		t.Fatalf("three-path failure used stdin/output: calls=%d stdout=%q stderr=%q", stdin.calls, stdout.String(), stderr.String())
	}
}

func TestRunPropagatesUsageWriterFailures(t *testing.T) {
	short := &controlledWriter{limit: len(usage) - 1}
	if err := run([]string{"--help"}, &countingReader{}, short, io.Discard); !errors.Is(err, io.ErrShortWrite) {
		t.Fatalf("short help error = %v", err)
	}
	short = &controlledWriter{limit: 0}
	if err := run(nil, &countingReader{}, io.Discard, short); !errors.Is(err, io.ErrShortWrite) {
		t.Fatalf("short usage error = %v", err)
	}
	sentinel := errors.New("writer sentinel")
	failed := &controlledWriter{limit: 0, err: sentinel}
	if err := run([]string{"-h"}, &countingReader{}, failed, io.Discard); !errors.Is(err, sentinel) {
		t.Fatalf("help writer error = %v", err)
	}
}

func TestReadAuthenticatedBoundaries(t *testing.T) {
	directory := t.TempDir()
	value := []byte("authenticated payload")
	regular := filepath.Join(directory, "regular")
	if err := os.WriteFile(regular, value, 0o600); err != nil {
		t.Fatal(err)
	}
	spec := inputSpec{Role: "synthetic", Size: len(value), SHA256: digest(value)}
	got, err := readAuthenticated(regular, spec)
	if err != nil || !bytes.Equal(got, value) {
		t.Fatalf("regular input = %x, %v", got, err)
	}
	for name, changed := range map[string]inputSpec{
		"short declared size": {Role: "synthetic", Size: len(value) - 1, SHA256: digest(value)},
		"long declared size":  {Role: "synthetic", Size: len(value) + 1, SHA256: digest(value)},
		"negative size":       {Role: "synthetic", Size: -1, SHA256: digest(value)},
		"wrong hash":          {Role: "synthetic", Size: len(value), SHA256: digest([]byte("other"))},
		"malformed hash":      {Role: "synthetic", Size: len(value), SHA256: "not-a-sha256"},
	} {
		if _, err := readAuthenticated(regular, changed); err == nil {
			t.Fatalf("%s accepted", name)
		}
	}
	empty := filepath.Join(directory, "empty")
	if err := os.WriteFile(empty, nil, 0o600); err != nil {
		t.Fatal(err)
	}
	if got, err := readAuthenticated(empty, inputSpec{Role: "empty", Size: 0, SHA256: digest(nil)}); err != nil || len(got) != 0 {
		t.Fatalf("empty boundary = %x, %v", got, err)
	}
	if _, err := readAuthenticated(filepath.Join(directory, "absent"), spec); err == nil {
		t.Fatal("missing path accepted")
	}
	if _, err := readAuthenticated(directory, inputSpec{Role: "directory", Size: 0, SHA256: digest(nil)}); err == nil {
		t.Fatal("directory accepted")
	}
	link := filepath.Join(directory, "link")
	if err := os.Symlink(regular, link); err != nil {
		t.Fatal(err)
	}
	if _, err := readAuthenticated(link, spec); err == nil {
		t.Fatal("symbolic link accepted")
	}
}

func TestReadAuthenticatedRejectsFIFOWithoutBlocking(t *testing.T) {
	path := filepath.Join(t.TempDir(), "fifo")
	if err := syscall.Mkfifo(path, 0o600); err != nil {
		t.Fatal(err)
	}
	if _, err := readAuthenticated(path, inputSpec{Role: "fifo", Size: 0, SHA256: digest(nil)}); err == nil {
		t.Fatal("FIFO accepted")
	}
}

func TestAuthenticatedRootsAndSemanticGates(t *testing.T) {
	for _, spec := range []rootSpec{c659Spec, c680Spec} {
		raw, err := readAuthenticated(repositoryFile(spec.Input.ID), spec.Input)
		if err != nil {
			t.Fatalf("%s authentication: %v", spec.Input.Role, err)
		}
		words, err := parseRoot(raw, spec)
		if err != nil {
			t.Fatalf("%s semantics: %v", spec.Input.Role, err)
		}
		if len(words) != rootTerms || digest(orderedPayload(words)) != spec.OrderedSHA256 || digest(canonicalPayload(words)) != spec.CanonicalSHA256 {
			t.Fatalf("%s semantic payload mismatch", spec.Input.Role)
		}
	}
	raw, err := os.ReadFile(repositoryFile(c659RootID))
	if err != nil {
		t.Fatal(err)
	}
	words, err := parseRoot(raw, c659Spec)
	if err != nil {
		t.Fatal(err)
	}
	if _, err := parseRoot([]byte("malformed native root"), c659Spec); err == nil || !strings.Contains(err.Error(), "parse") {
		t.Fatalf("malformed root error = %v", err)
	}
	if _, err := parseRoot(encodeRoot(t, words[:rootTerms-1]), c659Spec); err == nil || !strings.Contains(err.Error(), "term count mismatch") {
		t.Fatalf("short root error = %v", err)
	}
	zero := slices.Clone(words)
	zero[0][0] = 0
	if _, err := parseRoot(encodeRoot(t, zero), c659Spec); err == nil || !strings.Contains(err.Error(), "nonzero validation") {
		t.Fatalf("zero factor root error = %v", err)
	}
	duplicate := slices.Clone(words)
	duplicate[1] = duplicate[0]
	if _, err := parseRoot(encodeRoot(t, duplicate), c659Spec); err == nil || !strings.Contains(err.Error(), "distinct validation") {
		t.Fatalf("duplicate root error = %v", err)
	}
	reordered := slices.Clone(words)
	reordered[0], reordered[1] = reordered[1], reordered[0]
	if _, err := parseRoot(encodeRoot(t, reordered), c659Spec); err == nil || !strings.Contains(err.Error(), "ordered payload SHA-256") {
		t.Fatalf("reordered root error = %v", err)
	}
	wrongCanonical := c659Spec
	wrongCanonical.CanonicalSHA256 = digest(nil)
	if _, err := parseRoot(raw, wrongCanonical); err == nil || !strings.Contains(err.Error(), "canonical payload SHA-256") {
		t.Fatalf("canonical authentication error = %v", err)
	}
	semanticEquivalent := bytes.Replace(raw, []byte(" 0 "), []byte(" 2 "), 1)
	if bytes.Equal(semanticEquivalent, raw) {
		t.Fatal("failed to form semantic-equivalent raw mutation")
	}
	if _, err := parseRoot(semanticEquivalent, c659Spec); err != nil {
		t.Fatalf("semantic-equivalent root should reach raw authentication boundary: %v", err)
	}
	path := filepath.Join(t.TempDir(), "semantic-equivalent")
	if err := os.WriteFile(path, semanticEquivalent, 0o600); err != nil {
		t.Fatal(err)
	}
	if _, err := readAuthenticated(path, c659Spec.Input); err == nil || !strings.Contains(err.Error(), "SHA-256") {
		t.Fatalf("semantic-equivalent raw mutation authentication error = %v", err)
	}
}

func TestFrozenOrientationsFormulaAndConstructor(t *testing.T) {
	wantOrientations := [][3]int{{0, 1, 2}, {0, 2, 1}, {1, 0, 2}, {1, 2, 0}, {2, 0, 1}, {2, 1, 0}}
	wantNames := []string{"ijk", "ikj", "jik", "jki", "kij", "kji"}
	if !slices.Equal(orientations, wantOrientations) || !slices.Equal(orientationNames, wantNames) {
		t.Fatalf("orientation freeze = %v %v", orientations, orientationNames)
	}
	first := triple{0x000f, 0x00f0, 0x0f00}
	second := triple{0x3333, 0x5555, 0xaaaa}
	want := [6][3]triple{
		{{0x000f, 0x55a5, 0x0f00}, {0x333c, 0x5555, 0xaaaa}, {0x000f, 0x5555, 0xa5aa}},
		{{0x000f, 0x00f0, 0xa5aa}, {0x333c, 0x5555, 0xaaaa}, {0x000f, 0x55a5, 0xaaaa}},
		{{0x333c, 0x00f0, 0x0f00}, {0x3333, 0x55a5, 0xaaaa}, {0x3333, 0x00f0, 0xa5aa}},
		{{0x000f, 0x00f0, 0xa5aa}, {0x3333, 0x55a5, 0xaaaa}, {0x333c, 0x00f0, 0xaaaa}},
		{{0x333c, 0x00f0, 0x0f00}, {0x3333, 0x5555, 0xa5aa}, {0x3333, 0x55a5, 0x0f00}},
		{{0x000f, 0x55a5, 0x0f00}, {0x3333, 0x5555, 0xa5aa}, {0x333c, 0x5555, 0x0f00}},
	}
	for index, positions := range orientations {
		if got := formulaPlus(first, second, positions); got != want[index] {
			t.Fatalf("orientation %d formula = %v, want %v", index, got, want[index])
		}
		got, err := constructorPlus(first, second, positions)
		if err != nil {
			t.Fatalf("orientation %d constructor: %v", index, err)
		}
		if got != want[index] {
			t.Fatalf("orientation %d constructor = %v, want %v", index, got, want[index])
		}
		if unorient(orient(first, positions), positions) != first || unorient(orient(second, positions), positions) != second {
			t.Fatalf("orientation %d does not round trip", index)
		}
	}
}

func TestPayloadEncodingAndCanonicalOrder(t *testing.T) {
	terms := []triple{{2, 1, 9}, {1, 10, 3}}
	original := slices.Clone(terms)
	wantCanonical := decodeHex(t, "040004000400020001000a000300020001000900")
	wantOrdered := decodeHex(t, "04000400040002000200010001000a0009000300")
	if got := canonicalPayload(terms); !bytes.Equal(got, wantCanonical) {
		t.Fatalf("canonical payload = %x, want %x", got, wantCanonical)
	}
	if got := orderedPayload(terms); !bytes.Equal(got, wantOrdered) {
		t.Fatalf("ordered payload = %x, want %x", got, wantOrdered)
	}
	if !slices.Equal(terms, original) {
		t.Fatalf("canonicalization mutated terms: %v", terms)
	}
	if got := appendU16(nil, 0x1234, 0xabcd); !bytes.Equal(got, []byte{0x34, 0x12, 0xcd, 0xab}) {
		t.Fatalf("uint16 encoding = %x", got)
	}
	if got := appendU32(nil, 0x12345678, 0x90abcdef); !bytes.Equal(got, []byte{0x78, 0x56, 0x34, 0x12, 0xef, 0xcd, 0xab, 0x90}) {
		t.Fatalf("uint32 encoding = %x", got)
	}
}

func TestExactClassesAliasesCopiesAndCollisionDefense(t *testing.T) {
	values := [][]byte{{0x20}, {0x10}, {0x20}}
	classes, err := exactClasses(values, "synthetic child", digest)
	if err != nil {
		t.Fatal(err)
	}
	if len(classes) != 2 || !bytes.Equal(classes[0].Value, []byte{0x10}) || !bytes.Equal(classes[1].Value, []byte{0x20}) {
		t.Fatalf("sorted classes = %#v", classes)
	}
	if !slices.Equal(classes[0].Members, []int{1}) || !slices.Equal(classes[1].Members, []int{0, 2}) {
		t.Fatalf("class aliases = %v %v", classes[0].Members, classes[1].Members)
	}
	values[0][0] = 0xff
	if !bytes.Equal(classes[1].Value, []byte{0x20}) {
		t.Fatalf("class retained caller storage: %x", classes[1].Value)
	}
	constantHash := func([]byte) string { return "one bucket" }
	equalClasses, err := exactClasses([][]byte{{1, 2}, {1, 2}}, "equal", constantHash)
	if err != nil || len(equalClasses) != 1 || !slices.Equal(equalClasses[0].Members, []int{0, 1}) {
		t.Fatalf("equal aliases in one bucket = %#v, %v", equalClasses, err)
	}
	if _, err := exactClasses([][]byte{{1, 2}, {1, 3}}, "synthetic child", constantHash); err == nil || !strings.Contains(err.Error(), "synthetic child SHA-256 collision on differing exact bytes") {
		t.Fatalf("differing collision error = %v", err)
	}
}

func TestCorpusChildSectionOffsetTamperAndTruncation(t *testing.T) {
	if corpusChildOffset != 103776 || corpusChildSectionSize != canonicalClasses*childPayloadBytes {
		t.Fatalf("corpus child contract = offset %d size %d", corpusChildOffset, corpusChildSectionSize)
	}
	corpus, err := readAuthenticated(repositoryFile(corpusID), corpusSpec)
	if err != nil {
		t.Fatal(err)
	}
	end := corpusChildOffset + corpusChildSectionSize
	regenerated := append([]byte(nil), corpus[corpusChildOffset:end]...)
	if err := verifyCorpusChildSection(corpus, regenerated); err != nil {
		t.Fatal(err)
	}
	corpus[0] ^= 1
	if err := verifyCorpusChildSection(corpus, regenerated); err != nil {
		t.Fatalf("byte before section affected replay: %v", err)
	}
	corpus[0] ^= 1
	corpus[end] ^= 1
	if err := verifyCorpusChildSection(corpus, regenerated); err != nil {
		t.Fatalf("byte after section affected replay: %v", err)
	}
	corpus[end] ^= 1
	corpus[corpusChildOffset] ^= 1
	if err := verifyCorpusChildSection(corpus, regenerated); err == nil || !strings.Contains(err.Error(), "section SHA-256 mismatch") {
		t.Fatalf("section tamper error = %v", err)
	}
	corpus[corpusChildOffset] ^= 1
	regenerated[len(regenerated)-1] ^= 1
	if err := verifyCorpusChildSection(corpus, regenerated); err == nil || !strings.Contains(err.Error(), "regenerated c659 class payload stream differs") {
		t.Fatalf("regenerated tamper error = %v", err)
	}
	regenerated[len(regenerated)-1] ^= 1
	if err := verifyCorpusChildSection(corpus[:end-1], regenerated); err == nil || !strings.Contains(err.Error(), "exceeds corpus boundary") {
		t.Fatalf("truncated corpus error = %v", err)
	}
	if err := verifyCorpusChildSection(nil, regenerated); err == nil || !strings.Contains(err.Error(), "exceeds corpus boundary") {
		t.Fatalf("empty corpus error = %v", err)
	}
}

func TestExactIntersectionAndPositiveCertificateBranch(t *testing.T) {
	left := []exactClass{
		{Value: []byte{0x00}, Members: []int{7}},
		{Value: []byte{0x10}, Members: []int{11}},
		{Value: []byte{0x10, 0x00}, Members: []int{13}},
		{Value: []byte{0xff}, Members: []int{17}},
	}
	right := []exactClass{
		{Value: []byte{0x01}, Members: []int{19}},
		{Value: append([]byte(nil), left[1].Value...), Members: []int{23}},
		{Value: []byte{0x80}, Members: []int{29}},
		{Value: append([]byte(nil), left[3].Value...), Members: []int{31}},
	}
	intersection := intersectExact(left, right)
	if len(intersection) != 2 || !bytes.Equal(intersection[0], []byte{0x10}) || !bytes.Equal(intersection[1], []byte{0xff}) {
		t.Fatalf("exact intersection = %x", intersection)
	}
	intersection[0][0] ^= 1
	if !bytes.Equal(left[1].Value, []byte{0x10}) || !bytes.Equal(right[1].Value, []byte{0x10}) {
		t.Fatal("intersection aliases an input class")
	}
	intersection = intersectExact(left, right)
	c659 := &frontier{Classes: left}
	c680 := &frontier{Classes: right}
	certificate := buildCertificate(c659, c680, intersection)
	if certificate.Result != "complete_common_exact_variant_0_one_plus_child_payload_found" || certificate.ExactComparison.ExactIntersectionCount != 2 || certificate.ExactComparison.ExactUnionCount != 6 {
		t.Fatalf("positive certificate result = %q intersection=%d union=%d", certificate.Result, certificate.ExactComparison.ExactIntersectionCount, certificate.ExactComparison.ExactUnionCount)
	}
	if !slices.Equal(certificate.ExactComparison.SortedIntersectionPayloadsHex, []string{"10", "ff"}) {
		t.Fatalf("intersection hex = %v", certificate.ExactComparison.SortedIntersectionPayloadsHex)
	}
	stream := certificate.ExactComparison.IntersectionPayloadStream
	if stream.Count != 2 || stream.Bytes != 2 || stream.SHA256 != digest([]byte{0x10, 0xff}) || stream.DomainSeparatedSHA256 != domainDigest("intersection.sorted_payloads", []byte{0x10, 0xff}) {
		t.Fatalf("intersection stream = %+v", stream)
	}
	negative := buildCertificate(c659, c680, nil)
	if negative.Result != "complete_no_common_exact_variant_0_one_plus_child_payload" || negative.ExactComparison.ExactIntersectionCount != 0 {
		t.Fatalf("negative certificate result = %q count=%d", negative.Result, negative.ExactComparison.ExactIntersectionCount)
	}
}

func TestWriteAllFullShortAndError(t *testing.T) {
	value := []byte("certificate bytes")
	var full bytes.Buffer
	if err := writeAll(&full, value); err != nil || !bytes.Equal(full.Bytes(), value) {
		t.Fatalf("full write = %q, %v", full.Bytes(), err)
	}
	short := &controlledWriter{limit: len(value) - 1}
	if err := writeAll(short, value); !errors.Is(err, io.ErrShortWrite) {
		t.Fatalf("short write error = %v", err)
	}
	sentinel := errors.New("write sentinel")
	failed := &controlledWriter{limit: 0, err: sentinel}
	if err := writeAll(failed, value); !errors.Is(err, sentinel) {
		t.Fatalf("failed write error = %v", err)
	}
	fullWithError := &controlledWriter{limit: len(value), err: sentinel}
	if err := writeAll(fullWithError, value); !errors.Is(err, sentinel) {
		t.Fatalf("full write with error = %v", err)
	}
}

func TestValidateChildMutationDiscrimination(t *testing.T) {
	raw, err := os.ReadFile(repositoryFile(c659RootID))
	if err != nil {
		t.Fatal(err)
	}
	root, err := parseRoot(raw, c659Spec)
	if err != nil {
		t.Fatal(err)
	}
	outputs, err := constructorPlus(root[0], root[1], orientations[0])
	if err != nil {
		t.Fatal(err)
	}
	child := append(append([]triple(nil), root[2:]...), outputs[:]...)
	if err := validateChild(child); err != nil {
		t.Fatalf("valid child: %v", err)
	}
	zero := slices.Clone(child)
	zero[0][0] = 0
	if err := validateChild(zero); err == nil || !strings.Contains(err.Error(), "nonzero") {
		t.Fatalf("zero mutation error = %v", err)
	}
	duplicate := slices.Clone(child)
	duplicate[1] = duplicate[0]
	if err := validateChild(duplicate); err == nil || !strings.Contains(err.Error(), "distinct") {
		t.Fatalf("duplicate mutation error = %v", err)
	}
	brent := slices.Clone(child)
	brent[0][0] ^= 1
	if err := validateChild(brent); err == nil || !strings.Contains(err.Error(), "Brent") {
		t.Fatalf("Brent mutation error = %v", err)
	}
}

func TestRunAuthenticatedFrozenInputs(t *testing.T) {
	args := []string{repositoryFile(c659RootID), repositoryFile(c680RootID), repositoryFile(corpusID)}
	stdin := &countingReader{}
	var stdout, stderr bytes.Buffer
	if err := run(args, stdin, &stdout, &stderr); err != nil {
		t.Fatal(err)
	}
	if stdin.calls != 0 || stderr.Len() != 0 {
		t.Fatalf("successful run used stdin or stderr: calls=%d stderr=%q", stdin.calls, stderr.String())
	}
	if got := digest(stdout.Bytes()); got != "a77e588e4c1768cd41c9401b4b3c9e54b96b96cb4e2b584447199453a1d747e6" {
		t.Fatalf("certificate SHA-256 = %s", got)
	}
	for _, required := range []string{
		`"result": "complete_no_common_exact_variant_0_one_plus_child_payload"`,
		`"exact_intersection_count": 0`,
		`"exact_bytes_equal": true`,
		`"nonzero_distinct_brent_valid_children": 12972`,
	} {
		if !strings.Contains(stdout.String(), required) {
			t.Fatalf("certificate lacks %q", required)
		}
	}
}
