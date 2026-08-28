package main

import (
	"bytes"
	"encoding/binary"
	"encoding/hex"
	"fmt"
	"slices"

	"patel.codes/proofs/internal/ring"
	"patel.codes/proofs/internal/tensor"
)

const (
	fixedChildInversePlusSchemaV4             = "patel.codes/proofs/c659-plusflip-cert/fixed-child-inverse-plus/v4"
	fixedChildInversePlusOracleSchemaV3       = "c659-fixed-child-inverse-plus-oracle-v3"
	fixedChildInversePlusOracleSourceBytes    = 43716
	fixedChildInversePlusOracleArtifactBytes  = 206895
	fixedChildInversePlusValidatorBytes       = 33407
	fixedChildInversePlusOracleSourceSHA256   = "1dd78a71e4206936656e542d6b4c1f8e347f4c647dd77cfb25d68178dec61f8e"
	fixedChildInversePlusOracleArtifactSHA256 = "9616ca07d92a9fe70ae8a522bb13cd46bf9d77ea5f61b658beda8840a9b7e553"
	fixedChildInversePlusValidatorSHA256      = "a1ae5a93abeb1a709b822e803cac20ca4999a6854ce31b1bf1266ac20f9eca73"
	fixedChildInversePlusOracleSemanticSHA256 = "4017a2d52372609a01d0e3aa53fd153d5d85d6932c9b70648f581d7dd968085c"
	fixedChildInversePlusTensorSHA256         = "1ae43419be8f86b7063141475bb207725b43bc4d1c6cae2c11a948b7359863bd"
	fixedChildInversePlusChildOrderedSHA256   = "913109f1ab4662db336696a853ecb5bf77f60ea5a0b051117c4359469660e24a"
	fixedChildInversePlusSwappedRootSHA256    = "0db3f66cf7786d0a12ddda907b7e22ff3a55e5d6f793db1f7f8ee132d5c22e01"
	fixedChildInversePlusAllDescriptorSHA256  = "e05ef47fc81d499b850748e1c1193280fd622c257b5a82ac5487491175cf4d94"
	fixedChildInversePlusHitDescriptorSHA256  = "73fbb5130da5027c305ea14a8e18815d01fc8c7e7413737c69c8337bf330b5fc"
	fixedChildInversePlusAllRecordsSHA256     = "85578bcb1f46796677c62c97261c6724ebd8b4f21424e63dbaaacac87569e48d"
	fixedChildInversePlusHitRecordsSHA256     = "c2e1d98c809cc14f6a0c00e5b755f6a8fafe1e5b2a9fb2dbb0f3c04a2c86e1f0"
)

var fixedChildInversePlusOrientations = [6]inversePlusOrientationV4{
	{Name: "ijk", Positions: [3]int{0, 1, 2}},
	{Name: "ikj", Positions: [3]int{0, 2, 1}},
	{Name: "jik", Positions: [3]int{1, 0, 2}},
	{Name: "jki", Positions: [3]int{1, 2, 0}},
	{Name: "kij", Positions: [3]int{2, 0, 1}},
	{Name: "kji", Positions: [3]int{2, 1, 0}},
}

var fixedChildInversePlusFormulas = [3]string{
	"(a1,b1+b2,c1);(a1+a2,b2,c2);(a1,b2,c1+c2)",
	"(a1,b1,c1+c2);(a2,b1+b2,c2);(a1+a2,b1,c2)",
	"(a1+a2,b1,c1);(a2,b2,c1+c2);(a2,b1+b2,c1)",
}

var fixedChildInversePlusEquationNames = [3][9]string{
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

var fixedChildInversePlusAssignments = [6][3]int{
	{45, 46, 47},
	{45, 47, 46},
	{46, 45, 47},
	{46, 47, 45},
	{47, 45, 46},
	{47, 46, 45},
}

var fixedChildInversePlusExpectedSequences = [6]int{14, 18, 42, 62, 74, 102}

var fixedChildInversePlusExpectedCompactDescriptors = [6][4]int{
	{46, 45, 0, 2},
	{45, 46, 1, 0},
	{45, 46, 2, 1},
	{46, 45, 3, 1},
	{46, 45, 4, 0},
	{45, 46, 5, 2},
}

var fixedChildInversePlusRootSources = [2]wordTriple{
	{50360, 56576, 10676},
	{53981, 55710, 273},
}

type fixedChildInversePlusCertificateV4 struct {
	Schema           string                          `json:"schema"`
	ExperimentID     string                          `json:"experiment_id"`
	Status           string                          `json:"status"`
	OracleBinding    inversePlusOracleBindingV4      `json:"oracle_binding"`
	Inputs           inversePlusInputsV4             `json:"inputs"`
	Method           inversePlusMethodV4             `json:"method"`
	Enumeration      inversePlusEnumerationV4        `json:"enumeration"`
	Records          []inversePlusRecordV4           `json:"records"`
	Counts           inversePlusCountsV4             `json:"counts"`
	Deduplication    inversePlusDeduplicationV4      `json:"deduplication"`
	Streams          inversePlusStreamsV4            `json:"streams"`
	Result           string                          `json:"result"`
	Conclusion       string                          `json:"conclusion"`
	Scope            string                          `json:"scope"`
	ScopeDisclaimers []string                        `json:"scope_disclaimers"`
	SelfChecks       inversePlusAnalyzerSelfChecksV4 `json:"self_checks"`
}

type inversePlusOracleBindingV4 struct {
	OracleRecomputedByCommand bool                         `json:"oracle_recomputed_by_command"`
	Schema                    string                       `json:"schema"`
	SageSource                inversePlusFileBindingV4     `json:"sage_source"`
	Artifact                  inversePlusArtifactBindingV4 `json:"artifact"`
	Validator                 inversePlusFileBindingV4     `json:"static_validator"`
	RootRaw                   inversePlusFileBindingV4     `json:"root_raw"`
	RootOrdered               inversePlusPayloadBindingV4  `json:"root_ordered_factor_major"`
	RootUnordered             inversePlusPayloadBindingV4  `json:"root_unordered_canonical"`
	RootTensor                inversePlusPayloadBindingV4  `json:"root_tensor"`
	FixedChildOrdered         inversePlusPayloadBindingV4  `json:"fixed_child_ordered_factor_major"`
	FixedChildUnordered       inversePlusPayloadBindingV4  `json:"fixed_child_unordered_canonical"`
	FixedChildTensor          inversePlusPayloadBindingV4  `json:"fixed_child_tensor"`
	CompactDescriptorStreams  inversePlusFrozenStreamsV4   `json:"compact_descriptor_streams"`
	FullSemanticRecordStreams inversePlusFrozenStreamsV4   `json:"full_semantic_record_streams"`
	BindingStatement          string                       `json:"binding_statement"`
}

type inversePlusFileBindingV4 struct {
	RepositoryRelativeID string `json:"repository_relative_id"`
	Bytes                int    `json:"bytes"`
	SHA256               string `json:"sha256"`
}

type inversePlusArtifactBindingV4 struct {
	RepositoryRelativeID           string `json:"repository_relative_id"`
	Bytes                          int    `json:"bytes"`
	SHA256                         string `json:"sha256"`
	SemanticAndSourceBindingSHA256 string `json:"semantic_and_source_binding_sha256"`
}

type inversePlusPayloadBindingV4 struct {
	Bytes  int    `json:"bytes"`
	SHA256 string `json:"sha256"`
}

type inversePlusFrozenStreamsV4 struct {
	Encoding       string `json:"encoding"`
	AllBytes       int    `json:"all_bytes"`
	AllSHA256      string `json:"all_sha256"`
	AcceptedBytes  int    `json:"accepted_bytes"`
	AcceptedSHA256 string `json:"accepted_sha256"`
}

type inversePlusInputsV4 struct {
	Root         inversePlusSchemeBindingV4     `json:"authenticated_selected_c659_root"`
	FixedChild   inversePlusSchemeBindingV4     `json:"exact_fixed_child"`
	Relationship inversePlusInputRelationshipV4 `json:"relationship"`
}

type inversePlusSchemeBindingV4 struct {
	Ring                     string       `json:"ring"`
	Dimensions               [3]int       `json:"dimensions"`
	TermCount                int          `json:"term_count"`
	OrderedFactorMajorBytes  int          `json:"ordered_factor_major_bytes"`
	OrderedFactorMajorSHA256 string       `json:"ordered_factor_major_sha256"`
	UnorderedCanonicalBytes  int          `json:"unordered_canonical_bytes"`
	UnorderedCanonicalSHA256 string       `json:"unordered_canonical_sha256"`
	Checks                   schemeChecks `json:"checks"`
}

type inversePlusInputRelationshipV4 struct {
	RootSourceSlots                [2]int `json:"root_source_slots"`
	ChildInsertionSlots            [3]int `json:"child_insertion_slots"`
	RootSurvivorsEqualChildPrefix  bool   `json:"root_survivors_equal_child_prefix"`
	ForwardInsertedTermsEqualChild bool   `json:"forward_inserted_terms_equal_child"`
	ExactOrderedChildVerified      bool   `json:"exact_ordered_child_verified"`
}

type inversePlusMethodV4 struct {
	EnumerationOrder     string                      `json:"enumeration_order"`
	AssignmentSemantics  string                      `json:"assignment_semantics"`
	OrientationOrder     [6]inversePlusOrientationV4 `json:"orientation_order"`
	VariantOrder         [3]int                      `json:"variant_order"`
	Formulas             [3]string                   `json:"formulas"`
	NamedEquations       [3][9]string                `json:"named_equations_by_variant"`
	IndependentRecovery  string                      `json:"independent_recovery"`
	Constructor          string                      `json:"constructor"`
	ParentReconstruction string                      `json:"parent_reconstruction"`
	LineageRule          string                      `json:"lineage_rule"`
}

type inversePlusOrientationV4 struct {
	Name      string `json:"name"`
	Positions [3]int `json:"positions"`
}

type inversePlusEnumerationV4 struct {
	SlotIndexing                  string    `json:"slot_indexing"`
	SequenceIndexing              string    `json:"sequence_indexing"`
	DescriptorSchema              [4]string `json:"compact_descriptor_schema"`
	DescriptorSemantics           string    `json:"compact_descriptor_semantics"`
	DescriptorCount               int       `json:"descriptor_count"`
	AcceptedSequences             []int     `json:"accepted_sequences"`
	RejectedSequences             []int     `json:"rejected_sequences"`
	AcceptedCompactDescriptors    [][4]int  `json:"accepted_compact_descriptors"`
	AllDescriptorsUnique          bool      `json:"all_descriptors_unique"`
	AcceptedSequenceOrderVerified bool      `json:"accepted_sequence_order_verified"`
}

type inversePlusDescriptorV4 struct {
	Sequence         int    `json:"sequence"`
	OrientationIndex int    `json:"orientation_index"`
	Orientation      string `json:"orientation"`
	Positions        [3]int `json:"positions"`
	Variant          int    `json:"variant"`
	Formula          string `json:"formula"`
	Assignment       [3]int `json:"assignment"`
	Compact          [4]int `json:"compact"`
}

type inversePlusRecordV4 struct {
	Descriptor          inversePlusDescriptorV4          `json:"descriptor"`
	Accepted            bool                             `json:"accepted"`
	Classification      string                           `json:"classification"`
	IndependentRecovery inversePlusIndependentRecoveryV4 `json:"independent_recovery"`
	Constructor         inversePlusConstructorStageV4    `json:"constructor_stage"`
	SourcePolicy        *inversePlusSourcePolicyV4       `json:"source_policy"`
	Replacement         *inversePlusReplacementStageV4   `json:"replacement_stage"`
	Replay              *inversePlusReplayStageV4        `json:"replay_stage"`
	Lineage             *inversePlusLineageV4            `json:"lineage"`
}

type inversePlusIndependentRecoveryV4 struct {
	CompletedBeforeConstructor bool                         `json:"completed_before_constructor"`
	OrientedActualOutputs      [3]wordTriple                `json:"oriented_actual_outputs"`
	OrientedRecoveredSources   [2]wordTriple                `json:"oriented_recovered_sources"`
	OrientedReplayedOutputs    [3]wordTriple                `json:"oriented_replayed_outputs"`
	NamedEquations             []inversePlusNamedEquationV4 `json:"named_equations"`
	AllNamedEquationsHold      bool                         `json:"all_named_equations_hold"`
}

type inversePlusNamedEquationV4 struct {
	Name     string `json:"name"`
	Actual   uint16 `json:"actual"`
	Replayed uint16 `json:"replayed"`
	Holds    bool   `json:"holds"`
}

type inversePlusConstructorStageV4 struct {
	Called                      bool                `json:"called"`
	Status                      string              `json:"status"`
	SkipReason                  string              `json:"skip_reason"`
	API                         string              `json:"api"`
	TemporaryFormulaOutputSlots [3]int              `json:"temporary_formula_output_slots"`
	TemporaryOrientedTerms      [3]wordTriple       `json:"temporary_oriented_terms"`
	Replacement                 *replacementWitness `json:"replacement"`
	RecoveredOrientedSources    [2]wordTriple       `json:"recovered_oriented_sources"`
	MatchedIndependentRecovery  bool                `json:"matched_independent_recovery"`
}

type inversePlusSourcePolicyV4 struct {
	EvaluatedSeparatelyFromConstructor bool          `json:"evaluated_separately_from_constructor"`
	RecoveredSources                   [2]wordTriple `json:"recovered_sources"`
	ZeroFactorSourceTerms              []int         `json:"zero_factor_source_terms"`
	SourceFactorCollisionModes         []int         `json:"source_factor_collision_modes"`
	AllSourceTermsNonzero              bool          `json:"all_source_terms_nonzero"`
	AnalyzerNonzeroPolicyPassed        bool          `json:"analyzer_nonzero_policy_passed"`
	SourcePreconditionLegal            bool          `json:"source_precondition_legal"`
}

type inversePlusReplacementStageV4 struct {
	API                        string              `json:"api"`
	ExactActualChildSlots      [3]int              `json:"exact_actual_child_slots"`
	Replacement                replacementWitness  `json:"replacement"`
	ValidationAPI              string              `json:"validation_api"`
	ValidationPassed           bool                `json:"validation_passed"`
	AppliedOutputOrder         outputOrderWitness  `json:"applied_output_order"`
	AppliedOutputOrderVerified bool                `json:"applied_output_order_verified"`
	AppliedResult              schemeResult        `json:"applied_result"`
	AppliedOrderedBytes        int                 `json:"applied_ordered_factor_major_bytes"`
	AppliedOrderedSHA256       string              `json:"applied_ordered_factor_major_sha256"`
	Parent                     inversePlusParentV4 `json:"reconstructed_parent"`
}

type inversePlusParentV4 struct {
	ReconstructionRule           string       `json:"reconstruction_rule"`
	SourceParentSlots            [2]int       `json:"source_parent_slots"`
	Result                       schemeResult `json:"result"`
	OrderedFactorMajorBytes      int          `json:"ordered_factor_major_bytes"`
	OrderedFactorMajorSHA256     string       `json:"ordered_factor_major_sha256"`
	OrderedFactorMajorPayloadHex string       `json:"ordered_factor_major_payload_hex"`
	UnorderedCanonicalBytes      int          `json:"unordered_canonical_bytes"`
	UnorderedCanonicalSHA256     string       `json:"unordered_canonical_sha256"`
	UnorderedCanonicalPayloadHex string       `json:"unordered_canonical_payload_hex"`
	ZeroFactorTerms              []int        `json:"zero_factor_terms"`
	DuplicateCompleteTermGroups  [][]int      `json:"duplicate_complete_term_groups"`
}

type inversePlusReplayStageV4 struct {
	IndependentLocalTensorIdentity bool               `json:"independent_local_tensor_identity"`
	ForwardFormulaOutputs          [3]wordTriple      `json:"forward_formula_outputs"`
	FormulaOutputMatches           [3]bool            `json:"formula_output_matches"`
	ForwardFormulaOrderExact       bool               `json:"forward_formula_order_exact"`
	ScatteredInsertionTerms        [3]wordTriple      `json:"scattered_insertion_terms"`
	ScatterReplacement             replacementWitness `json:"scatter_replacement"`
	ScatterOutputOrder             outputOrderWitness `json:"scatter_output_order"`
	ScatterOutputOrderVerified     bool               `json:"scatter_output_order_verified"`
	ScatterFixedChildExact         bool               `json:"scatter_fixed_child_exact"`
	ScatterOrderedSHA256           string             `json:"scatter_ordered_factor_major_sha256"`
	ScatterUnorderedSHA256         string             `json:"scatter_unordered_canonical_sha256"`
}

type inversePlusLineageV4 struct {
	Classification                      string                               `json:"classification"`
	GeneratingAlias                     bool                                 `json:"generating_alias"`
	AlternateExactParent                bool                                 `json:"alternate_exact_parent"`
	IdentityLiteralMatch                bool                                 `json:"identity_literal_match"`
	SwapSevenThirteenLiteralMatch       bool                                 `json:"swap_7_13_literal_match"`
	ParentExactRootOrderMatch           bool                                 `json:"parent_exact_root_order_match"`
	ParentSlotToRootSlot                []int                                `json:"parent_slot_to_root_slot"`
	LiteralFactorEquality               bool                                 `json:"literal_factor_equality"`
	LiteralFactorEqualityWitnesses      []inversePlusFactorEqualityWitnessV4 `json:"literal_factor_equality_witnesses"`
	IdentityCandidateWitnesses          []inversePlusFactorEqualityWitnessV4 `json:"identity_candidate_witnesses"`
	SwapSevenThirteenCandidateWitnesses []inversePlusFactorEqualityWitnessV4 `json:"swap_7_13_candidate_witnesses"`
	SourceParentSlots                   [2]int                               `json:"source_parent_slots"`
	SourceTermsEqualMappedRootSlots     bool                                 `json:"source_terms_equal_mapped_root_slots"`
	OrbitEquivalenceStatus              string                               `json:"orbit_equivalence_status"`
	NoSolverUsed                        bool                                 `json:"no_solver_used"`
}

type inversePlusFactorEqualityWitnessV4 struct {
	ParentSlot        int        `json:"parent_slot"`
	RootSlot          int        `json:"root_slot"`
	ParentFactors     wordTriple `json:"parent_factors"`
	RootFactors       wordTriple `json:"root_factors"`
	FactorEqualities  [3]bool    `json:"factor_equalities"`
	CompleteTermEqual bool       `json:"complete_term_equal"`
}

type inversePlusCountsV4 struct {
	DescriptorTotal                             int `json:"descriptor_total_count"`
	AcceptedDescriptors                         int `json:"accepted_descriptor_count"`
	RejectedDescriptors                         int `json:"rejected_descriptor_count"`
	InverseEquationConsistent                   int `json:"inverse_equation_consistent_count"`
	InverseEquationInconsistent                 int `json:"inverse_equation_inconsistent_count"`
	ConstructorCalls                            int `json:"constructor_call_count"`
	AcceptedExactParentLineage                  int `json:"accepted_exact_parent_lineage_count"`
	AcceptedIdentityLineage                     int `json:"accepted_identity_lineage_count"`
	AcceptedSwapSevenThirteenLineage            int `json:"accepted_swap_7_13_lineage_count"`
	AcceptedAlternateExactParent                int `json:"accepted_alternate_exact_parent_count"`
	AcceptedLocalTensorReplay                   int `json:"accepted_local_tensor_replay_count"`
	AcceptedScatterFixedChildReplay             int `json:"accepted_scatter_fixed_child_replay_count"`
	AcceptedParentTensorReplay                  int `json:"accepted_parent_tensor_replay_count"`
	AcceptedParentNonzero                       int `json:"accepted_parent_nonzero_count"`
	AcceptedParentCompleteTermDistinct          int `json:"accepted_parent_complete_term_distinct_count"`
	AcceptedSourcePreconditionLegal             int `json:"accepted_source_precondition_legal_count"`
	UniqueRawDescriptors                        int `json:"unique_raw_descriptor_count"`
	UniqueReconstructedSourcePairOrdered        int `json:"accepted_unique_reconstructed_source_pair_ordered_count"`
	UniqueReconstructedSourcePairOrderForgotten int `json:"accepted_unique_reconstructed_source_pair_order_forgotten_count"`
	UniqueReconstructedParentOrderedPayload     int `json:"accepted_unique_reconstructed_parent_ordered_payload_count"`
	UniqueReconstructedParentUnorderedPayload   int `json:"accepted_unique_reconstructed_parent_unordered_payload_count"`
}

type inversePlusDeduplicationV4 struct {
	Domain                                 string                         `json:"domain"`
	CollisionDefense                       string                         `json:"collision_defense"`
	SHA256CollisionsWithDifferentPayloads  int                            `json:"sha256_collisions_with_different_payloads"`
	RawDescriptorKey                       string                         `json:"raw_descriptor_key"`
	RawDescriptorClasses                   []inversePlusExactBytesClassV4 `json:"raw_descriptor_classes"`
	OrderedSourcePairKey                   string                         `json:"ordered_source_pair_key"`
	OrderedSourcePairClasses               []inversePlusSourcePairClassV4 `json:"ordered_source_pair_classes"`
	SourceOrderForgottenPairKey            string                         `json:"source_order_forgotten_pair_key"`
	SourceOrderForgottenPairClasses        []inversePlusSourcePairClassV4 `json:"source_order_forgotten_pair_classes"`
	OrderedParentPayloadKey                string                         `json:"ordered_parent_payload_key"`
	OrderedParentPayloadClasses            []inversePlusExactBytesClassV4 `json:"ordered_parent_payload_classes"`
	UnorderedCanonicalParentPayloadKey     string                         `json:"unordered_canonical_parent_payload_key"`
	UnorderedCanonicalParentPayloadClasses []inversePlusExactBytesClassV4 `json:"unordered_canonical_parent_payload_classes"`
}

type inversePlusExactBytesClassV4 struct {
	Class        int    `json:"class"`
	SHA256       string `json:"sha256"`
	Bytes        int    `json:"bytes"`
	PayloadHex   string `json:"payload_hex"`
	PayloadASCII string `json:"payload_ascii"`
	Sequences    []int  `json:"sequences"`
}

type inversePlusSourcePairClassV4 struct {
	Class      int                          `json:"class"`
	SourcePair [2]wordTriple                `json:"source_pair"`
	ExactBytes inversePlusExactBytesClassV4 `json:"exact_bytes"`
}

type inversePlusStreamsV4 struct {
	CompactDescriptorStreams  inversePlusComputedStreamsV4 `json:"compact_descriptor_streams"`
	FullSemanticRecordBinding inversePlusFrozenStreamsV4   `json:"full_semantic_record_binding"`
}

type inversePlusComputedStreamsV4 struct {
	Encoding       string `json:"encoding"`
	AllBytes       int    `json:"all_bytes"`
	AllSHA256      string `json:"all_sha256"`
	AcceptedBytes  int    `json:"accepted_bytes"`
	AcceptedSHA256 string `json:"accepted_sha256"`
	Recomputed     bool   `json:"recomputed_by_command"`
}

type inversePlusAnalyzerSelfChecksV4 struct {
	InputAuthenticationPinned                    bool `json:"input_authentication_pinned"`
	OrientationOrderPinned                       bool `json:"orientation_order_pinned"`
	VariantOrderPinned                           bool `json:"variant_order_pinned"`
	AssignmentOrderPinned                        bool `json:"assignment_order_pinned"`
	AllRawDescriptorsUniqueWithCollisionDefense  bool `json:"all_raw_descriptors_unique_with_collision_defense"`
	AcceptedSequenceAndDescriptorFreezeVerified  bool `json:"accepted_sequence_and_descriptor_freeze_verified"`
	ConstructorNeverCalledForInconsistentRecords bool `json:"constructor_never_called_for_inconsistent_records"`
	AllPostHitStagesVerified                     bool `json:"all_post_hit_stages_verified"`
	LiteralLineageWitnessesComplete              bool `json:"literal_lineage_witnesses_complete"`
	DescriptorStreamDigestsRecomputed            bool `json:"descriptor_stream_digests_recomputed"`
	OracleFullSemanticStreamDigestsBound         bool `json:"oracle_full_semantic_stream_digests_bound"`
}

type inversePlusConstructorV4 func(tensor.Scheme, [3]int, tensor.PlusVariant) (tensor.Replacement, error)

type inversePlusEndpointPayloadV4 struct {
	Ordered         []byte
	Canonical       []byte
	OrderedSHA256   string
	CanonicalSHA256 string
}

func inversePlusEndpointExact(first, second inversePlusEndpointPayloadV4) bool {
	return bytes.Equal(first.Ordered, second.Ordered) && bytes.Equal(first.Canonical, second.Canonical)
}

type inversePlusExactByteDedupe struct {
	classes                         []inversePlusExactByteDedupeClass
	buckets                         map[string][]int
	hash                            func([]byte) string
	collisionsWithDifferentPayloads int
}

type inversePlusExactByteDedupeClass struct {
	sha256    string
	payload   []byte
	sequences []int
}

func AnalyzeFixedChildInversePlus(root, child tensor.Scheme) (fixedChildInversePlusCertificateV4, error) {
	return analyzeFixedChildInversePlus(root, child)
}

func analyzeFixedChildInversePlus(root, child tensor.Scheme) (fixedChildInversePlusCertificateV4, error) {
	return analyzeFixedChildInversePlusWithConstructor(root, child, tensor.NewInversePlusReplacement)
}

func analyzeFixedChildInversePlusWithConstructor(root, child tensor.Scheme, constructor inversePlusConstructorV4) (fixedChildInversePlusCertificateV4, error) {
	inputs, rootWords, childWords, err := authenticateFixedChildInversePlusInputs(root, child)
	if err != nil {
		return fixedChildInversePlusCertificateV4{}, err
	}
	method := inversePlusMethodV4{
		EnumerationOrder:     "orientation-major, variant-major, lexicographic assignment-major",
		AssignmentSemantics:  "assignment gives child slots assigned respectively to formula outputs X, Y, Z (outputs 0, 1, 2)",
		OrientationOrder:     fixedChildInversePlusOrientations,
		VariantOrder:         [3]int{0, 1, 2},
		Formulas:             fixedChildInversePlusFormulas,
		NamedEquations:       fixedChildInversePlusEquationNames,
		IndependentRecovery:  "recover oriented source words from formula outputs 0 and 1, then evaluate all nine named equations before any tensor constructor call",
		Constructor:          "tensor.NewInversePlusReplacement on a formula-order oriented three-term temporary scheme with slots (0,1,2)",
		ParentReconstruction: "retain exact child slots 0 through 44 as survivors and insert the ordered recovered source pair at parent slots 7 and 13",
		LineageRule:          "literal complete-term and factor equality under only identity or transposition (7 13); unknown_alternate otherwise; no solver",
	}
	records := make([]inversePlusRecordV4, 0, 108)
	acceptedSequences := make([]int, 0, 6)
	rejectedSequences := make([]int, 0, 102)
	acceptedCompact := make([][4]int, 0, 6)
	allDescriptorStream := make([]byte, 0, 1296)
	acceptedDescriptorStream := make([]byte, 0, 72)
	rawDescriptorDedupe := newInversePlusExactByteDedupe()
	orderedSourceDedupe := newInversePlusExactByteDedupe()
	forgottenSourceDedupe := newInversePlusExactByteDedupe()
	orderedParentDedupe := newInversePlusExactByteDedupe()
	unorderedParentDedupe := newInversePlusExactByteDedupe()
	counts := inversePlusCountsV4{}
	sequence := 0
	for orientationIndex, orientation := range fixedChildInversePlusOrientations {
		for variantValue := range 3 {
			variant := tensor.PlusVariant(variantValue)
			for _, assignment := range fixedChildInversePlusAssignments {
				compact := [4]int{assignment[0], assignment[1], orientationIndex, variantValue}
				descriptorLine := inversePlusCompactDescriptorLine(compact)
				allDescriptorStream = append(allDescriptorStream, descriptorLine...)
				rawDescriptorDedupe.add(descriptorLine, sequence)
				descriptor := inversePlusDescriptorV4{
					Sequence:         sequence,
					OrientationIndex: orientationIndex,
					Orientation:      orientation.Name,
					Positions:        orientation.Positions,
					Variant:          variantValue,
					Formula:          fixedChildInversePlusFormulas[variantValue],
					Assignment:       assignment,
					Compact:          compact,
				}
				orientedOutputs := [3]wordTriple{}
				for output, slot := range assignment {
					orientedOutputs[output] = orientInversePlusWords(childWords[slot], orientation.Positions)
				}
				orientedSources, orientedReplay, equations, consistent, err := recoverInversePlusWords(orientedOutputs, variantValue)
				if err != nil {
					return fixedChildInversePlusCertificateV4{}, fmt.Errorf("descriptor %d independent recovery: %w", sequence, err)
				}
				record := inversePlusRecordV4{
					Descriptor:     descriptor,
					Accepted:       consistent,
					Classification: "inverse_equation_inconsistent",
					IndependentRecovery: inversePlusIndependentRecoveryV4{
						CompletedBeforeConstructor: true,
						OrientedActualOutputs:      orientedOutputs,
						OrientedRecoveredSources:   orientedSources,
						OrientedReplayedOutputs:    orientedReplay,
						NamedEquations:             equations,
						AllNamedEquationsHold:      consistent,
					},
					Constructor: inversePlusConstructorStageV4{
						Called:                      false,
						Status:                      "skipped",
						SkipReason:                  "inverse_equation_inconsistent",
						API:                         "tensor.NewInversePlusReplacement",
						TemporaryFormulaOutputSlots: [3]int{0, 1, 2},
						TemporaryOrientedTerms:      orientedOutputs,
					},
				}
				counts.DescriptorTotal++
				if !consistent {
					counts.RejectedDescriptors++
					counts.InverseEquationInconsistent++
					rejectedSequences = append(rejectedSequences, sequence)
					records = append(records, record)
					sequence++
					continue
				}
				counts.AcceptedDescriptors++
				counts.InverseEquationConsistent++
				counts.ConstructorCalls++
				acceptedSequences = append(acceptedSequences, sequence)
				acceptedCompact = append(acceptedCompact, compact)
				acceptedDescriptorStream = append(acceptedDescriptorStream, descriptorLine...)
				record.Classification = "accepted_exact_parent_lineage"
				if err := completeFixedChildInversePlusHit(root, child, rootWords, childWords, variant, descriptor, orientedSources, orientedOutputs, constructor, &record, &counts, orderedSourceDedupe, forgottenSourceDedupe, orderedParentDedupe, unorderedParentDedupe); err != nil {
					return fixedChildInversePlusCertificateV4{}, fmt.Errorf("descriptor %d compact %v algebraic hit: %w", sequence, compact, err)
				}
				records = append(records, record)
				sequence++
			}
		}
	}
	if sequence != 108 {
		return fixedChildInversePlusCertificateV4{}, fmt.Errorf("inverse Plus enumeration produced %d descriptors, want 108", sequence)
	}
	counts.UniqueRawDescriptors = len(rawDescriptorDedupe.classes)
	counts.UniqueReconstructedSourcePairOrdered = len(orderedSourceDedupe.classes)
	counts.UniqueReconstructedSourcePairOrderForgotten = len(forgottenSourceDedupe.classes)
	counts.UniqueReconstructedParentOrderedPayload = len(orderedParentDedupe.classes)
	counts.UniqueReconstructedParentUnorderedPayload = len(unorderedParentDedupe.classes)
	if err := validateFixedChildInversePlusFinalCounts(counts, acceptedSequences, acceptedCompact); err != nil {
		return fixedChildInversePlusCertificateV4{}, err
	}
	allDescriptorHash := sha256Hex(allDescriptorStream)
	acceptedDescriptorHash := sha256Hex(acceptedDescriptorStream)
	if len(allDescriptorStream) != 1296 || allDescriptorHash != fixedChildInversePlusAllDescriptorSHA256 {
		return fixedChildInversePlusCertificateV4{}, fmt.Errorf("all compact descriptor stream is %d bytes SHA-256 %s, want 1296 bytes SHA-256 %s", len(allDescriptorStream), allDescriptorHash, fixedChildInversePlusAllDescriptorSHA256)
	}
	if len(acceptedDescriptorStream) != 72 || acceptedDescriptorHash != fixedChildInversePlusHitDescriptorSHA256 {
		return fixedChildInversePlusCertificateV4{}, fmt.Errorf("accepted compact descriptor stream is %d bytes SHA-256 %s, want 72 bytes SHA-256 %s", len(acceptedDescriptorStream), acceptedDescriptorHash, fixedChildInversePlusHitDescriptorSHA256)
	}
	collisionCount := rawDescriptorDedupe.collisionsWithDifferentPayloads + orderedSourceDedupe.collisionsWithDifferentPayloads + forgottenSourceDedupe.collisionsWithDifferentPayloads + orderedParentDedupe.collisionsWithDifferentPayloads + unorderedParentDedupe.collisionsWithDifferentPayloads
	if collisionCount != 0 {
		return fixedChildInversePlusCertificateV4{}, fmt.Errorf("exact-byte deduplication observed %d SHA-256 bucket collisions with different payloads", collisionCount)
	}
	if err := validateFixedChildInversePlusRecordStages(records); err != nil {
		return fixedChildInversePlusCertificateV4{}, err
	}
	return fixedChildInversePlusCertificateV4{
		Schema:        fixedChildInversePlusSchemaV4,
		ExperimentID:  "CC-1A-c659-fixed-v1",
		Status:        "complete",
		OracleBinding: makeFixedChildInversePlusOracleBinding(),
		Inputs:        inputs,
		Method:        method,
		Enumeration: inversePlusEnumerationV4{
			SlotIndexing:                  "zero-based",
			SequenceIndexing:              "zero-based",
			DescriptorSchema:              [4]string{"slotX", "slotY", "orientationIndex", "variant"},
			DescriptorSemantics:           "slotX and slotY are child slots assigned to formula outputs 0 and 1; slotZ/output 2 is the remaining member of {45,46,47}",
			DescriptorCount:               len(records),
			AcceptedSequences:             acceptedSequences,
			RejectedSequences:             rejectedSequences,
			AcceptedCompactDescriptors:    acceptedCompact,
			AllDescriptorsUnique:          counts.UniqueRawDescriptors == 108,
			AcceptedSequenceOrderVerified: true,
		},
		Records: records,
		Counts:  counts,
		Deduplication: inversePlusDeduplicationV4{
			Domain:                                 "all 108 raw descriptors for descriptor deduplication and all six algebraic hits with multiplicity retained for source-pair and parent-payload deduplication",
			CollisionDefense:                       "SHA-256 selects a bucket only; exact bytes.Equal comparison within every bucket decides equality and different payloads are never merged",
			SHA256CollisionsWithDifferentPayloads:  collisionCount,
			RawDescriptorKey:                       "exact canonical ASCII [slotX,slotY,orientationIndex,variant] plus LF",
			RawDescriptorClasses:                   rawDescriptorDedupe.publicClasses(true),
			OrderedSourcePairKey:                   "exact literal ordered six-word source pair encoded as six little-endian uint16 words with no header",
			OrderedSourcePairClasses:               inversePlusSourcePairClasses(orderedSourceDedupe, records, false),
			SourceOrderForgottenPairKey:            "exact literal source pair after numeric lexicographic sorting of the two complete three-word terms, encoded as six little-endian uint16 words with no header",
			SourceOrderForgottenPairClasses:        inversePlusSourcePairClasses(forgottenSourceDedupe, records, true),
			OrderedParentPayloadKey:                "exact ordered factor-major binary parent payload including header",
			OrderedParentPayloadClasses:            orderedParentDedupe.publicClasses(false),
			UnorderedCanonicalParentPayloadKey:     "exact numeric-lexicographically sorted complete-term binary parent payload including header",
			UnorderedCanonicalParentPayloadClasses: unorderedParentDedupe.publicClasses(false),
		},
		Streams: inversePlusStreamsV4{
			CompactDescriptorStreams: inversePlusComputedStreamsV4{
				Encoding:       "exact ASCII [slotX,slotY,orientationIndex,variant] plus LF per descriptor",
				AllBytes:       len(allDescriptorStream),
				AllSHA256:      allDescriptorHash,
				AcceptedBytes:  len(acceptedDescriptorStream),
				AcceptedSHA256: acceptedDescriptorHash,
				Recomputed:     true,
			},
			FullSemanticRecordBinding: makeFixedChildInversePlusOracleBinding().FullSemanticRecordStreams,
		},
		Result:     "bounded_no_alternate_parent",
		Conclusion: "within this bounded fixed-child domain all six inverse-Plus hits are literal c659 lineage aliases, every reconstructed endpoint has the authenticated c659 unordered canonical hash, and the alternate-parent form of CC-1A is falsified for this child only",
		Scope:      "exactly the 108 orientation-major, variant-major, lexicographic formula-slot assignments on fixed child slots 45,46,47 of the authenticated selected c659 root's exact fixed Plus child",
		ScopeDisclaimers: []string{
			"the result is bounded to the exact authenticated selected c659 root, the exact ordered fixed child, child slots 45,46,47, six listed orientations, and Plus variants 0,1,2",
			"reversed source order is a literal c659 lineage alias under root-slot transposition (7 13), never an alternate parent",
			"if a nonliteral valid parent were encountered, this frozen authenticated certificate would fail closed before publication; no equivalence solver would run and its orbit/equivalence status would remain unknown",
			"the result says nothing about other supports or other children",
			"the result does not establish or use a c680 bridge",
			"the result does not establish a rank-46 presentation",
			"the result does not establish a global orbit or orbit equivalence",
			"the result does not establish tensor-rank minimality or any tensor-rank lower bound",
			"the frozen Sage oracle v3 full semantic streams are bound as metadata and are not recomputed by this command",
		},
		SelfChecks: inversePlusAnalyzerSelfChecksV4{
			InputAuthenticationPinned:                    true,
			OrientationOrderPinned:                       true,
			VariantOrderPinned:                           true,
			AssignmentOrderPinned:                        true,
			AllRawDescriptorsUniqueWithCollisionDefense:  true,
			AcceptedSequenceAndDescriptorFreezeVerified:  true,
			ConstructorNeverCalledForInconsistentRecords: true,
			AllPostHitStagesVerified:                     true,
			LiteralLineageWitnessesComplete:              true,
			DescriptorStreamDigestsRecomputed:            true,
			OracleFullSemanticStreamDigestsBound:         true,
		},
	}, nil
}

func authenticateFixedChildInversePlusInputs(root, child tensor.Scheme) (inversePlusInputsV4, []wordTriple, []wordTriple, error) {
	rootBinding, rootWords, rootOrdered, rootUnordered, err := authenticateInversePlusScheme(root, "selected c659 root", 47, 290, expectedC659OrderedFactorMajorSHA256, expectedC659UnorderedCanonicalSHA256)
	if err != nil {
		return inversePlusInputsV4{}, nil, nil, err
	}
	childBinding, childWords, childOrdered, childUnordered, err := authenticateInversePlusScheme(child, "fixed child", 48, 296, fixedChildInversePlusChildOrderedSHA256, expectedPlusChildSHA256)
	if err != nil {
		return inversePlusInputsV4{}, nil, nil, err
	}
	if len(rootOrdered) != 290 || len(rootUnordered) != 290 || len(childOrdered) != 296 || len(childUnordered) != 296 {
		return inversePlusInputsV4{}, nil, nil, fmt.Errorf("inverse Plus authenticated payload lengths changed")
	}
	survivors := make([]wordTriple, 0, 45)
	for slot, words := range rootWords {
		if slot != 7 && slot != 13 {
			survivors = append(survivors, words)
		}
	}
	rootSurvivorsEqualChildPrefix := slices.Equal(survivors, childWords[:45])
	if !rootSurvivorsEqualChildPrefix {
		return inversePlusInputsV4{}, nil, nil, fmt.Errorf("fixed child slots 0 through 44 do not exactly equal selected c659 root survivors after removing slots 7 and 13")
	}
	orientedRootSources := [2]wordTriple{
		orientInversePlusWords(rootWords[7], [3]int{0, 2, 1}),
		orientInversePlusWords(rootWords[13], [3]int{0, 2, 1}),
	}
	orientedInserted, err := forwardInversePlusWords(orientedRootSources, 0)
	if err != nil {
		return inversePlusInputsV4{}, nil, nil, fmt.Errorf("replay fixed child insertion: %w", err)
	}
	insertedEqual := true
	for output := range 3 {
		insertedEqual = insertedEqual && unorientInversePlusWords(orientedInserted[output], [3]int{0, 2, 1}) == childWords[45+output]
	}
	if !insertedEqual {
		return inversePlusInputsV4{}, nil, nil, fmt.Errorf("fixed child slots 45 through 47 do not exactly equal the selected c659 root slots 7 and 13 variant-0 ikj Plus outputs")
	}
	return inversePlusInputsV4{
		Root:       rootBinding,
		FixedChild: childBinding,
		Relationship: inversePlusInputRelationshipV4{
			RootSourceSlots:                [2]int{7, 13},
			ChildInsertionSlots:            [3]int{45, 46, 47},
			RootSurvivorsEqualChildPrefix:  rootSurvivorsEqualChildPrefix,
			ForwardInsertedTermsEqualChild: insertedEqual,
			ExactOrderedChildVerified:      true,
		},
	}, rootWords, childWords, nil
}

func authenticateInversePlusScheme(scheme tensor.Scheme, role string, termCount, payloadBytes int, orderedSHA256, unorderedSHA256 string) (inversePlusSchemeBindingV4, []wordTriple, []byte, []byte, error) {
	if scheme.Ring() != ring.Z2 {
		return inversePlusSchemeBindingV4{}, nil, nil, nil, fmt.Errorf("%s ring is %d, want Z2", role, scheme.Ring())
	}
	if scheme.Dimensions() != [3]int{4, 4, 4} {
		return inversePlusSchemeBindingV4{}, nil, nil, nil, fmt.Errorf("%s dimensions are %v, want [4 4 4]", role, scheme.Dimensions())
	}
	if scheme.TermCount() != termCount {
		return inversePlusSchemeBindingV4{}, nil, nil, nil, fmt.Errorf("%s has %d terms, want %d", role, scheme.TermCount(), termCount)
	}
	checks, err := validateSchemeSeparately(scheme)
	if err != nil {
		return inversePlusSchemeBindingV4{}, nil, nil, nil, fmt.Errorf("validate %s: %w", role, err)
	}
	words, err := schemeWords(scheme)
	if err != nil {
		return inversePlusSchemeBindingV4{}, nil, nil, nil, fmt.Errorf("encode %s words: %w", role, err)
	}
	ordered, err := orderedFactorMajorBytes(scheme)
	if err != nil {
		return inversePlusSchemeBindingV4{}, nil, nil, nil, fmt.Errorf("encode %s ordered payload: %w", role, err)
	}
	unordered, err := canonicalBytes(scheme)
	if err != nil {
		return inversePlusSchemeBindingV4{}, nil, nil, nil, fmt.Errorf("encode %s unordered payload: %w", role, err)
	}
	if len(ordered) != payloadBytes || sha256Hex(ordered) != orderedSHA256 {
		return inversePlusSchemeBindingV4{}, nil, nil, nil, fmt.Errorf("%s ordered factor-major payload is %d bytes SHA-256 %s, want %d bytes SHA-256 %s", role, len(ordered), sha256Hex(ordered), payloadBytes, orderedSHA256)
	}
	if len(unordered) != payloadBytes || sha256Hex(unordered) != unorderedSHA256 {
		return inversePlusSchemeBindingV4{}, nil, nil, nil, fmt.Errorf("%s unordered canonical payload is %d bytes SHA-256 %s, want %d bytes SHA-256 %s", role, len(unordered), sha256Hex(unordered), payloadBytes, unorderedSHA256)
	}
	return inversePlusSchemeBindingV4{
		Ring:                     "GF(2)",
		Dimensions:               scheme.Dimensions(),
		TermCount:                scheme.TermCount(),
		OrderedFactorMajorBytes:  len(ordered),
		OrderedFactorMajorSHA256: sha256Hex(ordered),
		UnorderedCanonicalBytes:  len(unordered),
		UnorderedCanonicalSHA256: sha256Hex(unordered),
		Checks:                   checks,
	}, words, ordered, unordered, nil
}

func completeFixedChildInversePlusHit(root, child tensor.Scheme, rootWords, childWords []wordTriple, variant tensor.PlusVariant, descriptor inversePlusDescriptorV4, independentOrientedSources [2]wordTriple, orientedOutputs [3]wordTriple, constructor inversePlusConstructorV4, record *inversePlusRecordV4, counts *inversePlusCountsV4, orderedSourceDedupe, forgottenSourceDedupe, orderedParentDedupe, unorderedParentDedupe *inversePlusExactByteDedupe) error {
	orientedTerms := make([]tensor.RankOneTerm, 3)
	for output, childSlot := range descriptor.Assignment {
		term, err := orientTerm(child.Term(childSlot), descriptor.Positions)
		if err != nil {
			return fmt.Errorf("orient formula output %d from child slot %d: %w", output, childSlot, err)
		}
		words, err := termWords(term)
		if err != nil {
			return fmt.Errorf("encode oriented formula output %d: %w", output, err)
		}
		if words != orientedOutputs[output] {
			return fmt.Errorf("oriented temporary output %d is %v, independent words are %v", output, words, orientedOutputs[output])
		}
		orientedTerms[output] = term
	}
	temporary, err := tensor.NewScheme(orientedTerms)
	if err != nil {
		return fmt.Errorf("construct formula-order oriented temporary scheme: %w", err)
	}
	inverseReplacement, err := constructor(temporary, [3]int{0, 1, 2}, variant)
	if err != nil {
		return fmt.Errorf("tensor.NewInversePlusReplacement: %w", err)
	}
	constructorWitness, err := makeReplacementWitness(temporary, inverseReplacement, "tensor.NewInversePlusReplacement on formula-order oriented temporary scheme")
	if err != nil {
		return fmt.Errorf("record inverse constructor replacement: %w", err)
	}
	if !slices.Equal(inverseReplacement.RemovedSlots(), []int{0, 1, 2}) || len(inverseReplacement.InsertedTerms()) != 2 {
		return fmt.Errorf("inverse constructor removed slots %v and inserted %d terms, want [0 1 2] and 2", inverseReplacement.RemovedSlots(), len(inverseReplacement.InsertedTerms()))
	}
	constructorOrientedSources := [2]wordTriple{}
	sourceTerms := make([]tensor.RankOneTerm, 2)
	sourceWords := [2]wordTriple{}
	for source, orientedTerm := range inverseReplacement.InsertedTerms() {
		constructorOrientedSources[source], err = termWords(orientedTerm)
		if err != nil {
			return fmt.Errorf("encode constructor oriented source %d: %w", source, err)
		}
		if constructorOrientedSources[source] != independentOrientedSources[source] {
			return fmt.Errorf("constructor oriented source %d is %v, independent recovery is %v", source, constructorOrientedSources[source], independentOrientedSources[source])
		}
		sourceTerms[source], err = unorientTerm(orientedTerm, descriptor.Positions)
		if err != nil {
			return fmt.Errorf("unorient constructor source %d: %w", source, err)
		}
		sourceWords[source], err = termWords(sourceTerms[source])
		if err != nil {
			return fmt.Errorf("encode unorient constructor source %d: %w", source, err)
		}
		if sourceWords[source] != unorientInversePlusWords(independentOrientedSources[source], descriptor.Positions) {
			return fmt.Errorf("unoriented source %d is %v, independent recovery is %v", source, sourceWords[source], unorientInversePlusWords(independentOrientedSources[source], descriptor.Positions))
		}
	}
	record.Constructor = inversePlusConstructorStageV4{
		Called:                      true,
		Status:                      "succeeded",
		API:                         "tensor.NewInversePlusReplacement",
		TemporaryFormulaOutputSlots: [3]int{0, 1, 2},
		TemporaryOrientedTerms:      orientedOutputs,
		Replacement:                 &constructorWitness,
		RecoveredOrientedSources:    constructorOrientedSources,
		MatchedIndependentRecovery:  true,
	}
	zeroSources, collisionModes := inversePlusSourcePolicy(sourceWords)
	sourceLegal := len(zeroSources) == 0 && len(collisionModes) == 0
	record.SourcePolicy = &inversePlusSourcePolicyV4{
		EvaluatedSeparatelyFromConstructor: true,
		RecoveredSources:                   sourceWords,
		ZeroFactorSourceTerms:              zeroSources,
		SourceFactorCollisionModes:         collisionModes,
		AllSourceTermsNonzero:              len(zeroSources) == 0,
		AnalyzerNonzeroPolicyPassed:        len(zeroSources) == 0,
		SourcePreconditionLegal:            sourceLegal,
	}
	if !sourceLegal {
		return fmt.Errorf("separate recovered-source policy failed with zero-factor source terms %v and collision modes %v", zeroSources, collisionModes)
	}
	counts.AcceptedSourcePreconditionLegal++
	if err := validateExpectedFixedChildInversePlusSourcePair(descriptor.Sequence, sourceWords); err != nil {
		return err
	}
	exactSlots := [3]int{45, 46, 47}
	replacement, err := tensor.NewReplacement(exactSlots[:], sourceTerms)
	if err != nil {
		return fmt.Errorf("tensor.NewReplacement on exact child slots: %w", err)
	}
	if err := tensor.ValidateReplacement(child, replacement); err != nil {
		return fmt.Errorf("tensor.ValidateReplacement on exact child slots: %w", err)
	}
	replacementWitnessValue, err := makeReplacementWitness(child, replacement, "tensor.NewReplacement on exact actual child slots with unorient constructor sources")
	if err != nil {
		return fmt.Errorf("record exact child replacement: %w", err)
	}
	applied, err := tensor.ApplyReplacement(child, replacement)
	if err != nil {
		return fmt.Errorf("tensor.ApplyReplacement on exact child slots: %w", err)
	}
	if applied.TermCount() != 47 {
		return fmt.Errorf("applied inverse replacement has %d terms, want 47", applied.TermCount())
	}
	appliedOrder := makeOutputOrder(child.TermCount(), replacement.RemovedSlots(), len(replacement.InsertedTerms()))
	if err := verifyOutputOrder(child, applied, replacement, appliedOrder); err != nil {
		return fmt.Errorf("verify applied inverse output order: %w", err)
	}
	appliedResult, _, err := checkedSchemeResult(applied)
	if err != nil {
		return fmt.Errorf("validate applied inverse result: %w", err)
	}
	appliedOrdered, err := orderedFactorMajorBytes(applied)
	if err != nil {
		return fmt.Errorf("encode applied inverse ordered payload: %w", err)
	}
	parentTerms := make([]tensor.RankOneTerm, 0, 47)
	survivorIndex := 0
	for parentSlot := range 47 {
		switch parentSlot {
		case 7:
			parentTerms = append(parentTerms, sourceTerms[0])
		case 13:
			parentTerms = append(parentTerms, sourceTerms[1])
		default:
			parentTerms = append(parentTerms, child.Term(survivorIndex))
			survivorIndex++
		}
	}
	if survivorIndex != 45 {
		return fmt.Errorf("parent reconstruction consumed %d survivors, want 45", survivorIndex)
	}
	parent, err := tensor.NewScheme(parentTerms)
	if err != nil {
		return fmt.Errorf("construct ordered reconstructed parent: %w", err)
	}
	parentResult, parentCanonical, err := checkedSchemeResult(parent)
	if err != nil {
		return fmt.Errorf("validate reconstructed parent Brent/nonzero/distinct stages: %w", err)
	}
	if parent.TermCount() != 47 {
		return fmt.Errorf("reconstructed parent has %d terms, want 47", parent.TermCount())
	}
	parentOrdered, err := orderedFactorMajorBytes(parent)
	if err != nil {
		return fmt.Errorf("encode reconstructed parent ordered payload: %w", err)
	}
	parentCanonicalAgain, err := canonicalBytes(parent)
	if err != nil {
		return fmt.Errorf("encode reconstructed parent canonical payload: %w", err)
	}
	if !bytes.Equal(parentCanonical, parentCanonicalAgain) {
		return fmt.Errorf("reconstructed parent canonical encodings differ")
	}
	parentZeroTerms, parentDuplicateGroups := inversePlusTermPolicies(parentResult.OrderedTerms)
	if len(parentZeroTerms) != 0 || len(parentDuplicateGroups) != 0 {
		return fmt.Errorf("reconstructed parent policy has zero-factor terms %v and duplicate complete-term groups %v", parentZeroTerms, parentDuplicateGroups)
	}
	counts.AcceptedParentTensorReplay++
	counts.AcceptedParentNonzero++
	counts.AcceptedParentCompleteTermDistinct++
	lineage := classifyFixedChildInversePlusLineage(parentResult.OrderedTerms, rootWords, sourceWords)
	if lineage.GeneratingAlias {
		counts.AcceptedExactParentLineage++
	} else {
		counts.AcceptedAlternateExactParent++
		record.Classification = "accepted_unknown_alternate_parent"
	}
	if lineage.IdentityLiteralMatch {
		counts.AcceptedIdentityLineage++
	}
	if lineage.SwapSevenThirteenLiteralMatch {
		counts.AcceptedSwapSevenThirteenLineage++
	}
	parentOrderedHash := sha256Hex(parentOrdered)
	parentCanonicalHash := sha256Hex(parentCanonical)
	if lineage.IdentityLiteralMatch && parentOrderedHash != expectedC659OrderedFactorMajorSHA256 {
		return fmt.Errorf("identity-lineage parent ordered SHA-256 is %s, want %s", parentOrderedHash, expectedC659OrderedFactorMajorSHA256)
	}
	if lineage.SwapSevenThirteenLiteralMatch && parentOrderedHash != fixedChildInversePlusSwappedRootSHA256 {
		return fmt.Errorf("swap-lineage parent ordered SHA-256 is %s, want %s", parentOrderedHash, fixedChildInversePlusSwappedRootSHA256)
	}
	if lineage.GeneratingAlias && parentCanonicalHash != expectedC659UnorderedCanonicalSHA256 {
		return fmt.Errorf("reconstructed parent unordered SHA-256 is %s, want %s", parentCanonicalHash, expectedC659UnorderedCanonicalSHA256)
	}
	localTensorIdentity := inversePlusLocalTensorEqual(sourceWords, descriptor.Assignment, childWords)
	if !localTensorIdentity {
		return fmt.Errorf("independent local two-source/three-output tensor identity failed")
	}
	counts.AcceptedLocalTensorReplay++
	forwardOriented, err := forwardInversePlusWords(independentOrientedSources, descriptor.Variant)
	if err != nil {
		return fmt.Errorf("independent forward replay: %w", err)
	}
	forwardOutputs := [3]wordTriple{}
	formulaMatches := [3]bool{}
	for output := range 3 {
		forwardOutputs[output] = unorientInversePlusWords(forwardOriented[output], descriptor.Positions)
		formulaMatches[output] = forwardOutputs[output] == childWords[descriptor.Assignment[output]]
	}
	if !formulaMatches[0] || !formulaMatches[1] || !formulaMatches[2] {
		return fmt.Errorf("forward formula replay flags are %v, want all true", formulaMatches)
	}
	scatteredWords := [3]wordTriple{}
	scatteredTerms := make([]tensor.RankOneTerm, 3)
	for output, childSlot := range descriptor.Assignment {
		physical := childSlot - 45
		scatteredWords[physical] = forwardOutputs[output]
	}
	for physical := range 3 {
		if scatteredWords[physical] != childWords[45+physical] {
			return fmt.Errorf("scattered formula output at physical insertion %d is %v, fixed child has %v", physical, scatteredWords[physical], childWords[45+physical])
		}
		scatteredTerms[physical], err = inversePlusTermFromWords(scatteredWords[physical])
		if err != nil {
			return fmt.Errorf("construct scattered insertion term %d: %w", physical, err)
		}
	}
	scatterReplacement, err := tensor.NewReplacement([]int{7, 13}, scatteredTerms)
	if err != nil {
		return fmt.Errorf("construct forward scatter replacement: %w", err)
	}
	if err := tensor.ValidateReplacement(parent, scatterReplacement); err != nil {
		return fmt.Errorf("validate forward scatter replacement: %w", err)
	}
	scatterWitness, err := makeReplacementWitness(parent, scatterReplacement, "tensor.NewReplacement with formula outputs scattered to fixed child insertion order")
	if err != nil {
		return fmt.Errorf("record forward scatter replacement: %w", err)
	}
	scatteredChild, err := tensor.ApplyReplacement(parent, scatterReplacement)
	if err != nil {
		return fmt.Errorf("apply forward scatter replacement: %w", err)
	}
	scatterOrder := makeOutputOrder(parent.TermCount(), scatterReplacement.RemovedSlots(), len(scatterReplacement.InsertedTerms()))
	if err := verifyOutputOrder(parent, scatteredChild, scatterReplacement, scatterOrder); err != nil {
		return fmt.Errorf("verify forward scatter output order: %w", err)
	}
	scatterOrdered, err := orderedFactorMajorBytes(scatteredChild)
	if err != nil {
		return fmt.Errorf("encode scattered child ordered payload: %w", err)
	}
	scatterCanonical, err := canonicalBytes(scatteredChild)
	if err != nil {
		return fmt.Errorf("encode scattered child canonical payload: %w", err)
	}
	fixedChildOrdered, err := orderedFactorMajorBytes(child)
	if err != nil {
		return fmt.Errorf("encode authenticated fixed child ordered payload for scatter comparison: %w", err)
	}
	fixedChildCanonical, err := canonicalBytes(child)
	if err != nil {
		return fmt.Errorf("encode authenticated fixed child canonical payload for scatter comparison: %w", err)
	}
	scatterEndpoint := inversePlusEndpointPayloadV4{
		Ordered:         scatterOrdered,
		Canonical:       scatterCanonical,
		OrderedSHA256:   sha256Hex(scatterOrdered),
		CanonicalSHA256: sha256Hex(scatterCanonical),
	}
	fixedEndpoint := inversePlusEndpointPayloadV4{
		Ordered:         fixedChildOrdered,
		Canonical:       fixedChildCanonical,
		OrderedSHA256:   fixedChildInversePlusChildOrderedSHA256,
		CanonicalSHA256: expectedPlusChildSHA256,
	}
	fixedChildExact := inversePlusEndpointExact(scatterEndpoint, fixedEndpoint)
	if !fixedChildExact || scatterEndpoint.OrderedSHA256 != fixedEndpoint.OrderedSHA256 || scatterEndpoint.CanonicalSHA256 != fixedEndpoint.CanonicalSHA256 {
		return fmt.Errorf("forward scatter did not replay exact fixed child: exact=%t ordered=%s unordered=%s", fixedChildExact, sha256Hex(scatterOrdered), sha256Hex(scatterCanonical))
	}
	counts.AcceptedScatterFixedChildReplay++
	record.Replacement = &inversePlusReplacementStageV4{
		API:                        "tensor.NewReplacement",
		ExactActualChildSlots:      exactSlots,
		Replacement:                replacementWitnessValue,
		ValidationAPI:              "tensor.ValidateReplacement",
		ValidationPassed:           true,
		AppliedOutputOrder:         appliedOrder,
		AppliedOutputOrderVerified: true,
		AppliedResult:              appliedResult,
		AppliedOrderedBytes:        len(appliedOrdered),
		AppliedOrderedSHA256:       sha256Hex(appliedOrdered),
		Parent: inversePlusParentV4{
			ReconstructionRule:           "insert recovered source 0 at parent slot 7 and source 1 at parent slot 13 while mapping fixed child survivors 0 through 44 increasingly around them",
			SourceParentSlots:            [2]int{7, 13},
			Result:                       parentResult,
			OrderedFactorMajorBytes:      len(parentOrdered),
			OrderedFactorMajorSHA256:     parentOrderedHash,
			OrderedFactorMajorPayloadHex: hex.EncodeToString(parentOrdered),
			UnorderedCanonicalBytes:      len(parentCanonical),
			UnorderedCanonicalSHA256:     parentCanonicalHash,
			UnorderedCanonicalPayloadHex: hex.EncodeToString(parentCanonical),
			ZeroFactorTerms:              parentZeroTerms,
			DuplicateCompleteTermGroups:  parentDuplicateGroups,
		},
	}
	record.Replay = &inversePlusReplayStageV4{
		IndependentLocalTensorIdentity: localTensorIdentity,
		ForwardFormulaOutputs:          forwardOutputs,
		FormulaOutputMatches:           formulaMatches,
		ForwardFormulaOrderExact:       true,
		ScatteredInsertionTerms:        scatteredWords,
		ScatterReplacement:             scatterWitness,
		ScatterOutputOrder:             scatterOrder,
		ScatterOutputOrderVerified:     true,
		ScatterFixedChildExact:         fixedChildExact,
		ScatterOrderedSHA256:           sha256Hex(scatterOrdered),
		ScatterUnorderedSHA256:         sha256Hex(scatterCanonical),
	}
	record.Lineage = &lineage
	orderedSourceDedupe.add(inversePlusSourcePairBytes(sourceWords, false), descriptor.Sequence)
	forgottenSourceDedupe.add(inversePlusSourcePairBytes(sourceWords, true), descriptor.Sequence)
	orderedParentDedupe.add(parentOrdered, descriptor.Sequence)
	unorderedParentDedupe.add(parentCanonical, descriptor.Sequence)
	return nil
}

func recoverInversePlusWords(outputs [3]wordTriple, variant int) ([2]wordTriple, [3]wordTriple, []inversePlusNamedEquationV4, bool, error) {
	firstOutput := outputs[0]
	secondOutput := outputs[1]
	sources := [2]wordTriple{}
	switch variant {
	case 0:
		a1, b2, c1 := firstOutput[0], secondOutput[1], firstOutput[2]
		a2, b1, c2 := secondOutput[0]^a1, firstOutput[1]^b2, secondOutput[2]
		sources = [2]wordTriple{{a1, b1, c1}, {a2, b2, c2}}
	case 1:
		a1, b1, c2 := firstOutput[0], firstOutput[1], secondOutput[2]
		c1, a2, b2 := firstOutput[2]^c2, secondOutput[0], secondOutput[1]^b1
		sources = [2]wordTriple{{a1, b1, c1}, {a2, b2, c2}}
	case 2:
		a2, b1, c1 := secondOutput[0], firstOutput[1], firstOutput[2]
		a1, b2, c2 := firstOutput[0]^a2, secondOutput[1], secondOutput[2]^c1
		sources = [2]wordTriple{{a1, b1, c1}, {a2, b2, c2}}
	default:
		return [2]wordTriple{}, [3]wordTriple{}, nil, false, fmt.Errorf("unsupported Plus variant %d", variant)
	}
	replayed, err := forwardInversePlusWords(sources, variant)
	if err != nil {
		return [2]wordTriple{}, [3]wordTriple{}, nil, false, err
	}
	equations := make([]inversePlusNamedEquationV4, 0, 9)
	all := true
	coordinate := 0
	for output := range 3 {
		for factor := range 3 {
			holds := replayed[output][factor] == outputs[output][factor]
			equations = append(equations, inversePlusNamedEquationV4{
				Name:     fixedChildInversePlusEquationNames[variant][coordinate],
				Actual:   outputs[output][factor],
				Replayed: replayed[output][factor],
				Holds:    holds,
			})
			all = all && holds
			coordinate++
		}
	}
	return sources, replayed, equations, all, nil
}

func forwardInversePlusWords(sources [2]wordTriple, variant int) ([3]wordTriple, error) {
	first, second := sources[0], sources[1]
	sums := wordTriple{first[0] ^ second[0], first[1] ^ second[1], first[2] ^ second[2]}
	switch variant {
	case 0:
		return [3]wordTriple{
			{first[0], sums[1], first[2]},
			{sums[0], second[1], second[2]},
			{first[0], second[1], sums[2]},
		}, nil
	case 1:
		return [3]wordTriple{
			{first[0], first[1], sums[2]},
			{second[0], sums[1], second[2]},
			{sums[0], first[1], second[2]},
		}, nil
	case 2:
		return [3]wordTriple{
			{sums[0], first[1], first[2]},
			{second[0], second[1], sums[2]},
			{second[0], sums[1], first[2]},
		}, nil
	default:
		return [3]wordTriple{}, fmt.Errorf("unsupported Plus variant %d", variant)
	}
}

func orientInversePlusWords(words wordTriple, positions [3]int) wordTriple {
	return wordTriple{words[positions[0]], words[positions[1]], words[positions[2]]}
}

func unorientInversePlusWords(words wordTriple, positions [3]int) wordTriple {
	result := wordTriple{}
	for orientedMode, sourceMode := range positions {
		result[sourceMode] = words[orientedMode]
	}
	return result
}

func inversePlusTermFromWords(words wordTriple) (tensor.RankOneTerm, error) {
	matrices := [3]tensor.Matrix{}
	for mode, word := range words {
		entries := make([]int, 16)
		for bit := range 16 {
			entries[bit] = int(word >> bit & 1)
		}
		matrix, err := tensor.NewMatrix(ring.Z2, 4, 4, entries)
		if err != nil {
			return tensor.RankOneTerm{}, fmt.Errorf("factor %d: %w", mode, err)
		}
		matrices[mode] = matrix
	}
	term, err := tensor.NewRankOneTerm(matrices[0], matrices[1], matrices[2])
	if err != nil {
		return tensor.RankOneTerm{}, err
	}
	return term, nil
}

func inversePlusSourcePolicy(sources [2]wordTriple) ([]int, []int) {
	zeroSources := make([]int, 0)
	for source, words := range sources {
		if words[0] == 0 || words[1] == 0 || words[2] == 0 {
			zeroSources = append(zeroSources, source)
		}
	}
	collisionModes := make([]int, 0)
	for mode := range 3 {
		if sources[0][mode] == sources[1][mode] {
			collisionModes = append(collisionModes, mode)
		}
	}
	return zeroSources, collisionModes
}

func inversePlusTermPolicies(terms []wordTriple) ([]int, [][]int) {
	zeroTerms := make([]int, 0)
	groups := make(map[wordTriple][]int)
	order := make([]wordTriple, 0, len(terms))
	for slot, term := range terms {
		if term[0] == 0 || term[1] == 0 || term[2] == 0 {
			zeroTerms = append(zeroTerms, slot)
		}
		if _, exists := groups[term]; !exists {
			order = append(order, term)
		}
		groups[term] = append(groups[term], slot)
	}
	duplicates := make([][]int, 0)
	for _, term := range order {
		if len(groups[term]) > 1 {
			duplicates = append(duplicates, append([]int(nil), groups[term]...))
		}
	}
	return zeroTerms, duplicates
}

func inversePlusLocalTensorEqual(sources [2]wordTriple, assignment [3]int, childWords []wordTriple) bool {
	var sourceTensor, outputTensor [64]uint64
	for _, source := range sources {
		inversePlusXOROuter(&sourceTensor, source)
	}
	for _, slot := range assignment {
		inversePlusXOROuter(&outputTensor, childWords[slot])
	}
	return sourceTensor == outputTensor
}

func inversePlusXOROuter(value *[64]uint64, term wordTriple) {
	for first := range 16 {
		if term[0]&(uint16(1)<<first) == 0 {
			continue
		}
		for second := range 16 {
			if term[1]&(uint16(1)<<second) == 0 {
				continue
			}
			base := (first*16 + second) * 16
			for third := range 16 {
				if term[2]&(uint16(1)<<third) != 0 {
					coordinate := base + third
					value[coordinate/64] ^= uint64(1) << (coordinate % 64)
				}
			}
		}
	}
}

func classifyFixedChildInversePlusLineage(parentWords, rootWords []wordTriple, sources [2]wordTriple) inversePlusLineageV4 {
	identityMapping := make([]int, 47)
	swapMapping := make([]int, 47)
	for slot := range 47 {
		identityMapping[slot] = slot
		swapMapping[slot] = slot
	}
	swapMapping[7], swapMapping[13] = swapMapping[13], swapMapping[7]
	identityWitnesses, identityMatch := inversePlusMappingWitnesses(parentWords, rootWords, identityMapping)
	swapWitnesses, swapMatch := inversePlusMappingWitnesses(parentWords, rootWords, swapMapping)
	result := inversePlusLineageV4{
		Classification:                      "unknown_alternate",
		GeneratingAlias:                     false,
		AlternateExactParent:                true,
		IdentityLiteralMatch:                identityMatch,
		SwapSevenThirteenLiteralMatch:       swapMatch,
		ParentExactRootOrderMatch:           identityMatch,
		IdentityCandidateWitnesses:          identityWitnesses,
		SwapSevenThirteenCandidateWitnesses: swapWitnesses,
		SourceParentSlots:                   [2]int{7, 13},
		OrbitEquivalenceStatus:              "unknown",
		NoSolverUsed:                        true,
	}
	if identityMatch {
		result.Classification = "c659_identity"
		result.GeneratingAlias = true
		result.AlternateExactParent = false
		result.ParentSlotToRootSlot = identityMapping
		result.LiteralFactorEquality = true
		result.LiteralFactorEqualityWitnesses = identityWitnesses
		result.SourceTermsEqualMappedRootSlots = sources[0] == rootWords[7] && sources[1] == rootWords[13]
		result.OrbitEquivalenceStatus = "not_applicable_literal_lineage"
	} else if swapMatch {
		result.Classification = "c659_transposition_(7 13)"
		result.GeneratingAlias = true
		result.AlternateExactParent = false
		result.ParentSlotToRootSlot = swapMapping
		result.LiteralFactorEquality = true
		result.LiteralFactorEqualityWitnesses = swapWitnesses
		result.SourceTermsEqualMappedRootSlots = sources[0] == rootWords[13] && sources[1] == rootWords[7]
		result.OrbitEquivalenceStatus = "not_applicable_literal_lineage"
	}
	return result
}

func inversePlusMappingWitnesses(parentWords, rootWords []wordTriple, mapping []int) ([]inversePlusFactorEqualityWitnessV4, bool) {
	witnesses := make([]inversePlusFactorEqualityWitnessV4, 47)
	all := len(parentWords) == 47 && len(rootWords) == 47 && len(mapping) == 47
	for parentSlot := range 47 {
		rootSlot := mapping[parentSlot]
		parentFactors := parentWords[parentSlot]
		rootFactors := rootWords[rootSlot]
		factorEqualities := [3]bool{
			parentFactors[0] == rootFactors[0],
			parentFactors[1] == rootFactors[1],
			parentFactors[2] == rootFactors[2],
		}
		complete := factorEqualities[0] && factorEqualities[1] && factorEqualities[2]
		all = all && complete
		witnesses[parentSlot] = inversePlusFactorEqualityWitnessV4{
			ParentSlot:        parentSlot,
			RootSlot:          rootSlot,
			ParentFactors:     parentFactors,
			RootFactors:       rootFactors,
			FactorEqualities:  factorEqualities,
			CompleteTermEqual: complete,
		}
	}
	return witnesses, all
}

func validateExpectedFixedChildInversePlusSourcePair(sequence int, sources [2]wordTriple) error {
	reversed := sequence == 14 || sequence == 62 || sequence == 74
	expected := fixedChildInversePlusRootSources
	if reversed {
		expected[0], expected[1] = expected[1], expected[0]
	}
	if sources != expected {
		return fmt.Errorf("sequence %d recovered exact source pair %v, want literal pair %v", sequence, sources, expected)
	}
	return nil
}

func validateFixedChildInversePlusFinalCounts(counts inversePlusCountsV4, acceptedSequences []int, acceptedCompact [][4]int) error {
	expected := inversePlusCountsV4{
		DescriptorTotal:                             108,
		AcceptedDescriptors:                         6,
		RejectedDescriptors:                         102,
		InverseEquationConsistent:                   6,
		InverseEquationInconsistent:                 102,
		ConstructorCalls:                            6,
		AcceptedExactParentLineage:                  6,
		AcceptedIdentityLineage:                     3,
		AcceptedSwapSevenThirteenLineage:            3,
		AcceptedAlternateExactParent:                0,
		AcceptedLocalTensorReplay:                   6,
		AcceptedScatterFixedChildReplay:             6,
		AcceptedParentTensorReplay:                  6,
		AcceptedParentNonzero:                       6,
		AcceptedParentCompleteTermDistinct:          6,
		AcceptedSourcePreconditionLegal:             6,
		UniqueRawDescriptors:                        108,
		UniqueReconstructedSourcePairOrdered:        2,
		UniqueReconstructedSourcePairOrderForgotten: 1,
		UniqueReconstructedParentOrderedPayload:     2,
		UniqueReconstructedParentUnorderedPayload:   1,
	}
	if counts != expected {
		return fmt.Errorf("inverse Plus final counts are %+v, want %+v", counts, expected)
	}
	if !slices.Equal(acceptedSequences, fixedChildInversePlusExpectedSequences[:]) {
		return fmt.Errorf("accepted sequences are %v, want %v", acceptedSequences, fixedChildInversePlusExpectedSequences)
	}
	if !slices.Equal(acceptedCompact, fixedChildInversePlusExpectedCompactDescriptors[:]) {
		return fmt.Errorf("accepted compact descriptors are %v, want %v", acceptedCompact, fixedChildInversePlusExpectedCompactDescriptors)
	}
	return nil
}

func validateFixedChildInversePlusRecordStages(records []inversePlusRecordV4) error {
	if len(records) != 108 {
		return fmt.Errorf("record stage validation received %d records, want 108", len(records))
	}
	for sequence, record := range records {
		if record.Descriptor.Sequence != sequence {
			return fmt.Errorf("record %d has sequence %d", sequence, record.Descriptor.Sequence)
		}
		if !record.IndependentRecovery.CompletedBeforeConstructor {
			return fmt.Errorf("record %d did not complete independent recovery before constructor", sequence)
		}
		if !record.Accepted {
			if record.Constructor.Called || record.Constructor.Status != "skipped" || record.SourcePolicy != nil || record.Replacement != nil || record.Replay != nil || record.Lineage != nil {
				return fmt.Errorf("inconsistent record %d entered a constructor or post-hit stage", sequence)
			}
			continue
		}
		lineageComplete := record.Lineage != nil && ((record.Lineage.GeneratingAlias && !record.Lineage.AlternateExactParent && len(record.Lineage.LiteralFactorEqualityWitnesses) == 47) || (!record.Lineage.GeneratingAlias && record.Lineage.AlternateExactParent && record.Lineage.Classification == "unknown_alternate" && record.Lineage.OrbitEquivalenceStatus == "unknown" && record.Lineage.NoSolverUsed))
		if !record.Constructor.Called || record.Constructor.Status != "succeeded" || record.SourcePolicy == nil || !record.SourcePolicy.SourcePreconditionLegal || record.Replacement == nil || !record.Replacement.ValidationPassed || record.Replay == nil || !record.Replay.IndependentLocalTensorIdentity || !record.Replay.ForwardFormulaOrderExact || !record.Replay.ScatterFixedChildExact || !lineageComplete {
			return fmt.Errorf("accepted record %d has an incomplete or failed post-hit stage", sequence)
		}
		for _, witness := range record.Lineage.LiteralFactorEqualityWitnesses {
			if !witness.CompleteTermEqual || !witness.FactorEqualities[0] || !witness.FactorEqualities[1] || !witness.FactorEqualities[2] {
				return fmt.Errorf("accepted record %d has a failed literal lineage witness at parent slot %d", sequence, witness.ParentSlot)
			}
		}
	}
	return nil
}

func makeFixedChildInversePlusOracleBinding() inversePlusOracleBindingV4 {
	return inversePlusOracleBindingV4{
		OracleRecomputedByCommand: false,
		Schema:                    fixedChildInversePlusOracleSchemaV3,
		SageSource: inversePlusFileBindingV4{
			RepositoryRelativeID: "Programs/BilinearComplexity/c659_fixed_child_inverse_plus_oracle.sage",
			Bytes:                fixedChildInversePlusOracleSourceBytes,
			SHA256:               fixedChildInversePlusOracleSourceSHA256,
		},
		Artifact: inversePlusArtifactBindingV4{
			RepositoryRelativeID:           "Programs/BilinearComplexity/c659_fixed_child_inverse_plus_oracle.json",
			Bytes:                          fixedChildInversePlusOracleArtifactBytes,
			SHA256:                         fixedChildInversePlusOracleArtifactSHA256,
			SemanticAndSourceBindingSHA256: fixedChildInversePlusOracleSemanticSHA256,
		},
		Validator: inversePlusFileBindingV4{
			RepositoryRelativeID: "Programs/BilinearComplexity/validate_c659_fixed_child_inverse_plus_oracle.py",
			Bytes:                fixedChildInversePlusValidatorBytes,
			SHA256:               fixedChildInversePlusValidatorSHA256,
		},
		RootRaw: inversePlusFileBindingV4{
			RepositoryRelativeID: "cmd/c659-plusflip-cert/testdata/4x4x4_m47_c659_iteration5551_Z2.txt",
			Bytes:                expectedC659RawBytes,
			SHA256:               expectedC659RawSHA256,
		},
		RootOrdered: inversePlusPayloadBindingV4{
			Bytes:  expectedRootOrderedFactorMajorPayloadBytes,
			SHA256: expectedC659OrderedFactorMajorSHA256,
		},
		RootUnordered: inversePlusPayloadBindingV4{
			Bytes:  expectedRootOrderedFactorMajorPayloadBytes,
			SHA256: expectedC659UnorderedCanonicalSHA256,
		},
		RootTensor: inversePlusPayloadBindingV4{
			Bytes:  512,
			SHA256: fixedChildInversePlusTensorSHA256,
		},
		FixedChildOrdered: inversePlusPayloadBindingV4{
			Bytes:  296,
			SHA256: fixedChildInversePlusChildOrderedSHA256,
		},
		FixedChildUnordered: inversePlusPayloadBindingV4{
			Bytes:  296,
			SHA256: expectedPlusChildSHA256,
		},
		FixedChildTensor: inversePlusPayloadBindingV4{
			Bytes:  512,
			SHA256: fixedChildInversePlusTensorSHA256,
		},
		CompactDescriptorStreams: inversePlusFrozenStreamsV4{
			Encoding:       "canonical ASCII [slotX,slotY,orientationIndex,variant] plus LF per descriptor; slotZ/formula output 2 is the remaining member of {45,46,47}",
			AllBytes:       1296,
			AllSHA256:      fixedChildInversePlusAllDescriptorSHA256,
			AcceptedBytes:  72,
			AcceptedSHA256: fixedChildInversePlusHitDescriptorSHA256,
		},
		FullSemanticRecordStreams: inversePlusFrozenStreamsV4{
			Encoding:       "one complete canonical JSON semantic record plus LF, in descriptor enumeration order",
			AllBytes:       171217,
			AllSHA256:      fixedChildInversePlusAllRecordsSHA256,
			AcceptedBytes:  65038,
			AcceptedSHA256: fixedChildInversePlusHitRecordsSHA256,
		},
		BindingStatement: "the v3 Sage oracle source, artifact, authenticated root, exact ordered child, and frozen stream hashes are metadata bindings only; oracle_recomputed_by_command is false",
	}
}

func inversePlusCompactDescriptorLine(descriptor [4]int) []byte {
	return []byte(fmt.Sprintf("[%d,%d,%d,%d]\n", descriptor[0], descriptor[1], descriptor[2], descriptor[3]))
}

func inversePlusSourcePairBytes(sources [2]wordTriple, forgetOrder bool) []byte {
	ordered := sources
	if forgetOrder && inversePlusCompareWords(ordered[1], ordered[0]) < 0 {
		ordered[0], ordered[1] = ordered[1], ordered[0]
	}
	result := make([]byte, 0, 12)
	for _, source := range ordered {
		for _, word := range source {
			result = binary.LittleEndian.AppendUint16(result, word)
		}
	}
	return result
}

func inversePlusCompareWords(first, second wordTriple) int {
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

func newInversePlusExactByteDedupe() *inversePlusExactByteDedupe {
	return newInversePlusExactByteDedupeWithHash(sha256Hex)
}

func newInversePlusExactByteDedupeWithHash(hash func([]byte) string) *inversePlusExactByteDedupe {
	return &inversePlusExactByteDedupe{buckets: make(map[string][]int), hash: hash}
}

func (dedupe *inversePlusExactByteDedupe) add(payload []byte, sequence int) int {
	digest := dedupe.hash(payload)
	bucket := dedupe.buckets[digest]
	for _, classIndex := range bucket {
		if bytes.Equal(dedupe.classes[classIndex].payload, payload) {
			dedupe.classes[classIndex].sequences = append(dedupe.classes[classIndex].sequences, sequence)
			return classIndex
		}
	}
	if len(bucket) != 0 {
		dedupe.collisionsWithDifferentPayloads++
	}
	classIndex := len(dedupe.classes)
	dedupe.classes = append(dedupe.classes, inversePlusExactByteDedupeClass{
		sha256:    digest,
		payload:   append([]byte(nil), payload...),
		sequences: []int{sequence},
	})
	dedupe.buckets[digest] = append(bucket, classIndex)
	return classIndex
}

func (dedupe *inversePlusExactByteDedupe) publicClasses(includeASCII bool) []inversePlusExactBytesClassV4 {
	result := make([]inversePlusExactBytesClassV4, len(dedupe.classes))
	for index, class := range dedupe.classes {
		ascii := ""
		if includeASCII {
			ascii = string(class.payload)
		}
		result[index] = inversePlusExactBytesClassV4{
			Class:        index,
			SHA256:       class.sha256,
			Bytes:        len(class.payload),
			PayloadHex:   hex.EncodeToString(class.payload),
			PayloadASCII: ascii,
			Sequences:    append([]int(nil), class.sequences...),
		}
	}
	return result
}

func inversePlusSourcePairClasses(dedupe *inversePlusExactByteDedupe, records []inversePlusRecordV4, forgetOrder bool) []inversePlusSourcePairClassV4 {
	byteClasses := dedupe.publicClasses(false)
	result := make([]inversePlusSourcePairClassV4, len(byteClasses))
	for index, class := range byteClasses {
		sequence := class.Sequences[0]
		sources := records[sequence].SourcePolicy.RecoveredSources
		if forgetOrder && inversePlusCompareWords(sources[1], sources[0]) < 0 {
			sources[0], sources[1] = sources[1], sources[0]
		}
		result[index] = inversePlusSourcePairClassV4{
			Class:      index,
			SourcePair: sources,
			ExactBytes: class,
		}
	}
	return result
}
