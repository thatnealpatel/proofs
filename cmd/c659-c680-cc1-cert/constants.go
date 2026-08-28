package main

const (
	commandName  = "c659-c680-cc1-cert"
	outputSchema = "patel.codes/proofs/c659-c680-cc1-cert/v1"

	c659RootID = "cmd/c659-plusflip-cert/testdata/4x4x4_m47_c659_iteration5551_Z2.txt"
	c680RootID = "cmd/c659-plusflip-cert/testdata/4x4x4_m47_c680_iteration4356_Z2.txt"
	corpusID   = "Programs/BilinearComplexity/c659_all_child_wedge_inverse_plus_oracle.bin"

	rootBytes   = 4524
	corpusBytes = 7775908

	c659RawSHA256       = "25f47b5f37d2b7351dd5a2c5da65ff8ef5ba80ce53239d46cdfdef37e6eef403"
	c680RawSHA256       = "7e65a2fa888fcd9f32d9d68fd21ab8cdafeb4a39300cc77882def8e0115483e8"
	corpusSHA256        = "eac882916c80e3617e542434625c999d3177ed3d1d5fd67204d1152b50ee19a2"
	c659OrderedSHA256   = "f61518b4864995fe5ba43f1b52819cc563c4c74326442ae12bbc338a491027cb"
	c680OrderedSHA256   = "f6e3264df6e1a8c39c0af212c0ee0b490c7d96b0169c21b131b4c496fe04889b"
	c659CanonicalSHA256 = "f2edf6735401e203b532cc85e0783fb47684815a3207b3ec601f8503c48956d1"
	c680CanonicalSHA256 = "021266950ca5db9dd40593da2ec85d043469c1a15c66a04a06c2dbe23813c598"

	rootTerms              = 47
	orderedDescriptors     = 47 * 46 * 6
	canonicalClasses       = 6486
	childPayloadBytes      = 296
	corpusChildOffset      = 103776
	corpusChildSectionSize = 1919856
	c659ChildStreamSHA256  = "855b7242ed561ecffc9f636929e3f6171d2d8d1f7863ee1391f8b506a8fa5443"
)

var orientations = [][3]int{{0, 1, 2}, {0, 2, 1}, {1, 0, 2}, {1, 2, 0}, {2, 0, 1}, {2, 1, 0}}
var orientationNames = []string{"ijk", "ikj", "jik", "jki", "kij", "kji"}

type inputSpec struct {
	Role   string
	ID     string
	Size   int
	SHA256 string
}

type rootSpec struct {
	Input           inputSpec
	OrderedSHA256   string
	CanonicalSHA256 string
}

var c659Spec = rootSpec{
	Input:           inputSpec{Role: "c659 root", ID: c659RootID, Size: rootBytes, SHA256: c659RawSHA256},
	OrderedSHA256:   c659OrderedSHA256,
	CanonicalSHA256: c659CanonicalSHA256,
}

var c680Spec = rootSpec{
	Input:           inputSpec{Role: "c680 root", ID: c680RootID, Size: rootBytes, SHA256: c680RawSHA256},
	OrderedSHA256:   c680OrderedSHA256,
	CanonicalSHA256: c680CanonicalSHA256,
}

var corpusSpec = inputSpec{Role: "c659 all-child corpus", ID: corpusID, Size: corpusBytes, SHA256: corpusSHA256}

type triple [3]uint16

type exactClass struct {
	Value   []byte
	Members []int
}

type frontier struct {
	DescriptorStream        []byte
	DescriptorPayloadStream []byte
	ClassPayloadStream      []byte
	AliasStream             []byte
	Classes                 []exactClass
	ConstructorReplays      int
	FormulaReplays          int
	ChildValidations        int
}
