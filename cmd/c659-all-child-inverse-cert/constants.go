package main

const (
	commandName  = "c659-all-child-inverse-cert"
	schema       = "c659-all-child-wedge-inverse-plus-oracle-v1"
	outputSchema = "patel.codes/proofs/c659-all-child-inverse-cert/v1"

	sourceID    = "Programs/BilinearComplexity/c659_all_child_wedge_inverse_plus_oracle.sage"
	summaryID   = "Programs/BilinearComplexity/c659_all_child_wedge_inverse_plus_oracle.json"
	corpusID    = "Programs/BilinearComplexity/c659_all_child_wedge_inverse_plus_oracle.bin"
	validatorID = "Programs/BilinearComplexity/validate_c659_all_child_wedge_inverse_plus_oracle.py"
	rootID      = "cmd/c659-plusflip-cert/testdata/4x4x4_m47_c659_iteration5551_Z2.txt"

	sourceSize    = 38923
	summarySize   = 11232
	corpusSize    = 7775908
	validatorSize = 49165
	rootSize      = 4524

	sourceSHA256        = "f1bdfe82af6d080468fbafdeafb49dcf1fe75d5f1652475d2dd088bc31dec285"
	summarySHA256       = "d92f72aafec5435985b1a000e25224d7e27f1126b898ee03563e7e836511fcf1"
	corpusSHA256        = "eac882916c80e3617e542434625c999d3177ed3d1d5fd67204d1152b50ee19a2"
	validatorSHA256     = "918649100f723cd3ceaa9137757d12634f08e20b3c985a6daf821396b4ea5526"
	rootSHA256          = "25f47b5f37d2b7351dd5a2c5da65ff8ef5ba80ce53239d46cdfdef37e6eef403"
	rootOrderedSHA256   = "f61518b4864995fe5ba43f1b52819cc563c4c74326442ae12bbc338a491027cb"
	rootCanonicalSHA256 = "f2edf6735401e203b532cc85e0783fb47684815a3207b3ec601f8503c48956d1"
	tensorSHA256        = "1ae43419be8f86b7063141475bb207725b43bc4d1c6cae2c11a948b7359863bd"
	childStreamSHA256   = "855b7242ed561ecffc9f636929e3f6171d2d8d1f7863ee1391f8b506a8fa5443"
)

var orientations = [][3]int{{0, 1, 2}, {0, 2, 1}, {1, 0, 2}, {1, 2, 0}, {2, 0, 1}, {2, 1, 0}}
var orientationNames = []string{"ijk", "ikj", "jik", "jki", "kij", "kji"}
var formulas = []string{
	"(a1,b1+b2,c1);(a1+a2,b2,c2);(a1,b2,c1+c2)",
	"(a1,b1,c1+c2);(a2,b1+b2,c2);(a1+a2,b1,c2)",
	"(a1+a2,b1,c1);(a2,b2,c1+c2);(a2,b1+b2,c1)",
}
var terminals = []string{"residual_failure", "source_policy_failure", "inverse_equation_failure", "invalid_parent", "exact_c659_parent", "alternate_valid_parent"}
var sectionOrder = []string{"forward_descriptors", "child_payloads", "child_aliases", "ordered_realizations", "raw_wedges", "derived_descriptors", "accepted_records", "source_classes", "parent_classes", "alias_inverse_coverage"}

type inputSpec struct {
	Role   string
	ID     string
	Size   int
	SHA256 string
}

var inputSpecs = []inputSpec{
	{"root", rootID, rootSize, rootSHA256},
	{"producer source", sourceID, sourceSize, sourceSHA256},
	{"summary", summaryID, summarySize, summarySHA256},
	{"corpus", corpusID, corpusSize, corpusSHA256},
	{"validator", validatorID, validatorSize, validatorSHA256},
}

type triple [3]uint16

type exactClass struct {
	value   []byte
	members []int
}

type forwardRow struct {
	first, second        uint16
	orientation, variant uint8
	child                uint16
}
type wedgeRow struct {
	child                                    uint16
	center, a, b, legA, legB, residual, pass uint8
	firstDescriptor                          uint32
}
type descriptorRow struct {
	wedge                                                 uint32
	child                                                 uint16
	assignment, variant, x, y, z, i, j, k, pass, terminal uint8
	sourceClass, parentClass                              uint16
	accepted, alias                                       uint32
}
type acceptedRow struct {
	descriptor               uint32
	mask                     uint16
	sources                  [2]triple
	sourceClass, parentClass uint16
	alias                    uint32
	flags, terminal          uint8
}

type sectionContract struct {
	name, layout string
	recordSize   int
	fields       []string
}

var sectionContracts = []sectionContract{
	{"forward_descriptors", "<HHBBH", 8, []string{"source_first_root_slot:u16", "source_second_root_slot:u16", "orientation_index:u8", "variant:u8", "child_index:u16"}},
	{"child_payloads", "296-byte canonical child: <4H header then 48 lexicographic <HHH terms", 296, []string{"canonical_child_payload"}},
	{"child_aliases", "<II", 8, []string{"least_forward_descriptor_index:u32", "other_forward_descriptor_index:u32"}},
	{"ordered_realizations", "<I then 296 bytes then 48B then 48B then 48B", 444, []string{"least_descriptor:u32", "ordered_factor_major_child:296B", "ordered_to_canonical:48xu8", "canonical_to_ordered:48xu8", "ordered_provenance:48xu8;0..46=root slot,128=X,129=Y,130=Z"}},
	{"raw_wedges", "<H7BI", 13, []string{"child_index:u16", "center:u8", "color_a:u8", "color_b:u8", "leg_a:u8", "leg_b:u8", "residual_leg:u8", "residual_pass:u8", "first_descriptor_index:u32"}},
	{"derived_descriptors", "<IH10BHHII", 28, []string{"wedge_index:u32", "child_index:u16", "assignment:u8", "variant:u8", "X:u8", "Y:u8", "Z:u8", "i:u8", "j:u8", "k:u8", "residual_pass:u8", "terminal:u8", "source_class:u16", "parent_class:u16", "accepted_index:u32", "forward_alias_index:u32"}},
	{"accepted_records", "<IH6HHHIBB", 28, []string{"descriptor_index:u32", "nine_equation_mask:u16", "ordered_sources:6xu16", "source_class:u16", "parent_class:u16", "forward_alias_index:u32", "validation_flags:u8;bit0=all_nine_equations_and_formula_replay,bit1=source_policy,bit2=local_tensor,bit3=child_scatter,bit4=parent_tensor_nonzero_distinct", "terminal:u8"}},
	{"source_classes", "6H plus H", 14, []string{"lexicographically_sorted_source_pair:6xu16", "multiplicity:u16"}},
	{"parent_classes", "290-byte canonical parent plus <IBB", 296, []string{"canonical_parent_payload:290B", "multiplicity:u32", "classification:u8;0=root,1=alternate", "orbit_status:u8;0=known_root,1=unknown"}},
	{"alias_inverse_coverage", "<II", 8, []string{"forward_alias_index:u32", "accepted_record_index:u32"}},
}
