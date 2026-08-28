package main

type wordTriple [3]uint16

type rootSpec struct {
	ArgumentPosition         int
	Role                     string
	ID                       string
	RootFileName             string
	RawBytes                 int
	RawSHA256                string
	OrderedFactorMajorSHA256 string
	UnorderedCanonicalSHA256 string
}

type rootSelectionCertificate struct {
	DeclaredArgumentRoles     []string                   `json:"declared_argument_roles"`
	Candidates                []rootCandidateCertificate `json:"candidates"`
	Comparison                rootComparisonCertificate  `json:"comparison"`
	SelectedRootID            string                     `json:"selected_root_id"`
	RequiredSelectedRootID    string                     `json:"required_selected_root_id"`
	RequiredSelectionVerified bool                       `json:"required_selection_verified"`
}

type rootCandidateCertificate struct {
	ArgumentPosition               int                `json:"argument_position"`
	Role                           string             `json:"role"`
	ID                             string             `json:"id"`
	RootFileName                   string             `json:"root_file_name"`
	Ring                           string             `json:"ring"`
	Dimensions                     [3]int             `json:"dimensions"`
	TermCount                      int                `json:"term_count"`
	RawBytes                       int                `json:"raw_bytes"`
	RawSHA256                      string             `json:"raw_sha256"`
	OrderedFactorMajorPayloadBytes int                `json:"ordered_factor_major_payload_bytes"`
	OrderedFactorMajorSHA256       string             `json:"ordered_factor_major_sha256"`
	UnorderedCanonicalSHA256       string             `json:"unordered_canonical_sha256"`
	Checks                         schemeChecks       `json:"checks"`
	LiteralFactorScreening         literalFactorCheck `json:"literal_factor_screening"`
}

type rootComparisonCertificate struct {
	Rule                   string                         `json:"rule"`
	DigestEncoding         string                         `json:"digest_encoding"`
	Left                   rootDigestBinding              `json:"left"`
	Right                  rootDigestBinding              `json:"right"`
	CommonPrefixCharacters int                            `json:"common_prefix_characters"`
	FirstDifference        *rootDigestCharacterDifference `json:"first_difference"`
	CompareResult          int                            `json:"compare_result"`
	Result                 string                         `json:"result"`
}

type rootDigestBinding struct {
	RootID string `json:"root_id"`
	Digest string `json:"digest"`
}

type rootDigestCharacterDifference struct {
	ZeroBasedPosition int    `json:"zero_based_position"`
	LeftCharacter     string `json:"left_character"`
	RightCharacter    string `json:"right_character"`
	LeftASCII         int    `json:"left_ascii"`
	RightASCII        int    `json:"right_ascii"`
}

type preregisteredFlip struct {
	Descriptor flipDescriptor
	Hash       string
}

type preregisteredReduction struct {
	OutputHash string
	SharedMode int
	Inserted   wordTriple
}

type report struct {
	Envelope envelope            `json:"envelope"`
	Runtime  runtimeBinding      `json:"runtime"`
	Semantic semanticCertificate `json:"semantic"`
}

type envelope struct {
	Schema           string   `json:"schema"`
	DigestAlgorithm  string   `json:"digest_algorithm"`
	SemanticEncoding string   `json:"semantic_encoding"`
	SemanticSHA256   string   `json:"semantic_sha256"`
	ExcludedFields   []string `json:"excluded_fields"`
}

type runtimeBinding struct {
	Measurement string `json:"measurement"`
	Reason      string `json:"reason"`
}

type semanticCertificate struct {
	Schema                string                             `json:"schema"`
	Experiment            string                             `json:"experiment"`
	Encodings             encodingCertificate                `json:"encodings"`
	RootSelection         rootSelectionCertificate           `json:"root_selection"`
	PriorScan             priorScanBinding                   `json:"prior_scan_binding"`
	FixedPlus             plusCertificate                    `json:"fixed_plus"`
	FixedChildInversePlus fixedChildInversePlusCertificateV4 `json:"fixed_child_inverse_plus"`
	Coverage              coverageCertificate                `json:"coverage"`
	Attempts              []attemptCertificate               `json:"attempts"`
	Records               []flipRecord                       `json:"records"`
	UniqueOutputs         []uniqueOutput                     `json:"unique_outputs"`
	Summary               summaryCertificate                 `json:"summary"`
}

type encodingCertificate struct {
	FactorWord          string `json:"factor_word"`
	Header              string `json:"header"`
	UnorderedCanonical  string `json:"unordered_canonical"`
	OrderedRootPayload  string `json:"ordered_factor_major_root_payload"`
	ClassRows           string `json:"class_rows"`
	ClassRowHash        string `json:"class_row_hash"`
	SemanticDigestInput string `json:"semantic_digest_input"`
}

type schemeChecks struct {
	BrentReplay          bool `json:"brent_replay"`
	NonzeroTerms         bool `json:"nonzero_terms"`
	DistinctRankOneTerms bool `json:"distinct_rank_one_terms"`
}

type literalFactorCheck struct {
	FactorOccurrences int `json:"factor_occurrences"`
	NonzeroFactors    int `json:"nonzero_factors"`
	RepeatedClasses   int `json:"repeated_nonzero_literal_classes"`
	RepeatedPairs     int `json:"repeated_nonzero_literal_pairs"`
}

type priorScanBinding struct {
	Status                                  string             `json:"status"`
	DeclaredTwoRootSelectionClosedByCommand bool               `json:"declared_two_root_selection_closed_by_command"`
	C659PlusScanRecomputedByCommand         bool               `json:"c659_plus_scan_recomputed_by_command"`
	DescriptorStreamSHA256                  string             `json:"descriptor_stream_sha256"`
	Domain                                  priorScanDomain    `json:"domain"`
	Selection                               priorScanSelection `json:"selection"`
	C659PlusOutputMinimumProvedByCommand    bool               `json:"c659_plus_output_minimum_proved_by_command"`
	BindingStatement                        string             `json:"binding_statement"`
}

type priorScanDomain struct {
	Root                  string `json:"root"`
	RootSlotPairs         int    `json:"root_slot_pairs"`
	RootSlotOrders        int    `json:"root_slot_orders"`
	OuterOrientations     int    `json:"outer_orientations"`
	PlusVariant           int    `json:"plus_variant"`
	OrderedDescriptors    int    `json:"ordered_descriptors"`
	UniqueOutputs         int    `json:"unique_outputs"`
	EqualFactorSubsets    int    `json:"equal_factor_subsets"`
	PositiveDefectSubsets int    `json:"positive_defect_subsets"`
}

type priorScanSelection struct {
	RootRule    string `json:"root_rule"`
	OutputRule  string `json:"output_rule"`
	RootSlots   [2]int `json:"root_slots"`
	Orientation string `json:"orientation"`
	ChildSHA256 string `json:"child_sha256"`
}

type plusDescriptor struct {
	Kind                 string `json:"kind"`
	Variant              int    `json:"variant"`
	RootSlots            [2]int `json:"root_slots"`
	SlotIndexing         string `json:"slot_indexing"`
	OrientationName      string `json:"orientation_name"`
	OrientationPositions [3]int `json:"orientation_positions"`
}

type plusCertificate struct {
	Descriptor         plusDescriptor     `json:"descriptor"`
	Adaptation         []string           `json:"adaptation"`
	TemporaryPairSlots [2]int             `json:"temporary_pair_slots"`
	Replacement        replacementWitness `json:"replacement"`
	OutputOrder        outputOrderWitness `json:"output_order"`
	Child              schemeResult       `json:"child"`
}

type replacementWitness struct {
	Constructor            string       `json:"constructor"`
	RemovedSlots           []int        `json:"removed_slots"`
	RemovedTerms           []wordTriple `json:"removed_terms"`
	InsertedTerms          []wordTriple `json:"inserted_terms"`
	ValidationAPI          string       `json:"validation_api"`
	TensorIdentityVerified bool         `json:"tensor_identity_verified"`
}

type outputOrderWitness struct {
	Rule                 string `json:"rule"`
	SurvivorParentSlots  []int  `json:"survivor_parent_slots"`
	SurvivorResultSlots  []int  `json:"survivor_result_slots"`
	InsertionResultSlots []int  `json:"insertion_result_slots"`
}

type schemeResult struct {
	TermCount                int          `json:"term_count"`
	UnorderedCanonicalSHA256 string       `json:"unordered_canonical_sha256"`
	OrderedTerms             []wordTriple `json:"ordered_terms"`
	Checks                   schemeChecks `json:"checks"`
}

type flipDescriptor struct {
	FirstSlot   int `json:"first_slot"`
	SecondSlot  int `json:"second_slot"`
	SharedMode  int `json:"shared_mode"`
	Coefficient int `json:"coefficient"`
}

type attemptCertificate struct {
	Sequence       int              `json:"sequence"`
	Descriptor     flipDescriptor   `json:"descriptor"`
	Outcome        string           `json:"outcome"`
	Rejection      *rejectionRecord `json:"rejection"`
	AcceptedRecord *int             `json:"accepted_record"`
	OutputSHA256   *string          `json:"output_sha256"`
}

type rejectionRecord struct {
	Code             string `json:"code"`
	ConstructorError string `json:"constructor_error"`
}

type flipRecord struct {
	Record          int                `json:"record"`
	AttemptSequence int                `json:"attempt_sequence"`
	Descriptor      flipDescriptor     `json:"descriptor"`
	ParentSHA256    string             `json:"parent_sha256"`
	Replacement     replacementWitness `json:"replacement"`
	OutputOrder     outputOrderWitness `json:"output_order"`
	Result          schemeResult       `json:"result"`
	UniqueOutput    int                `json:"unique_output"`
}

type uniqueOutput struct {
	Index                int                `json:"index"`
	DedupeKey            string             `json:"dedupe_key"`
	UnorderedSHA256      string             `json:"unordered_sha256"`
	RepresentativeRecord int                `json:"representative_record"`
	Lineages             []lineageReference `json:"lineages"`
	RepresentativeTerms  []wordTriple       `json:"representative_terms"`
	Screens              []classScreen      `json:"screens"`
}

type lineageReference struct {
	Record          int            `json:"record"`
	AttemptSequence int            `json:"attempt_sequence"`
	Descriptor      flipDescriptor `json:"descriptor"`
}

type classScreen struct {
	Screen                int                    `json:"screen"`
	SharedMode            int                    `json:"shared_mode"`
	SharedFactorWord      uint16                 `json:"shared_factor_word"`
	SharedFactorHex       string                 `json:"shared_factor_hex"`
	Nonzero               bool                   `json:"nonzero"`
	Maximal               bool                   `json:"maximal"`
	Slots                 []int                  `json:"slots"`
	Terms                 []wordTriple           `json:"terms"`
	ComplementaryModes    [2]int                 `json:"complementary_modes"`
	Rows                  []uint16               `json:"rows"`
	RowsSHA256            string                 `json:"rows_sha256"`
	Elimination           eliminationCertificate `json:"elimination"`
	ClassSize             int                    `json:"class_size"`
	Rank                  int                    `json:"rank"`
	Defect                int                    `json:"defect"`
	ProperSubsetsExcluded bool                   `json:"proper_subsets_positive_defect_excluded"`
	Conclusion            string                 `json:"conclusion"`
	Reduction             *reductionCertificate  `json:"reduction"`
}

type eliminationCertificate struct {
	Algorithm      string   `json:"algorithm"`
	InputRowOrder  string   `json:"input_row_order"`
	PivotRule      string   `json:"pivot_rule"`
	PivotColumns   []int    `json:"pivot_columns"`
	BasisRows      []uint16 `json:"basis_rows"`
	InputResiduals []uint16 `json:"input_residuals"`
	Rank           int      `json:"rank"`
}

type reductionCertificate struct {
	Classification string             `json:"classification"`
	Replacement    replacementWitness `json:"replacement"`
	OutputOrder    outputOrderWitness `json:"output_order"`
	Result         schemeResult       `json:"result"`
}

type coverageCertificate struct {
	SlotCount                  int           `json:"slot_count"`
	OrderedDistinctSlotPairs   int           `json:"ordered_distinct_slot_pairs"`
	SharedModes                []int         `json:"shared_modes"`
	Coefficient                int           `json:"coefficient"`
	DeclaredCandidates         int           `json:"declared_candidates"`
	RecordedAttempts           int           `json:"recorded_attempts"`
	Accepted                   int           `json:"accepted"`
	Rejected                   int           `json:"rejected"`
	RejectionsByCode           []countByCode `json:"rejections_by_code"`
	UniqueUnorderedOutputs     int           `json:"unique_unordered_outputs"`
	MaximalClasses             int           `json:"maximal_nonzero_equal_factor_classes"`
	DefectZeroClasses          int           `json:"defect_zero_classes"`
	DefectOneClasses           int           `json:"defect_one_classes"`
	DefectAtLeastTwoClasses    int           `json:"defect_at_least_two_classes"`
	ReplayedPositiveReductions int           `json:"replayed_positive_reductions"`
	Complete                   bool          `json:"complete"`
	DomainStatement            string        `json:"domain_statement"`
}

type countByCode struct {
	Code  string `json:"code"`
	Count int    `json:"count"`
}

type summaryCertificate struct {
	AcceptedDescriptors        []descriptorHash `json:"accepted_descriptors"`
	ReductionResultHashes      []string         `json:"reduction_result_hashes"`
	ResultClassification       string           `json:"result_classification"`
	ScopedNegative             string           `json:"scoped_negative"`
	FullClassTheoremUse        string           `json:"full_class_theorem_use"`
	CanonicalMinimumProved     bool             `json:"canonical_minimum_proved"`
	TensorRankMinimumProved    bool             `json:"tensor_rank_minimum_proved"`
	PresentationUpperBoundOnly bool             `json:"presentation_upper_bound_only"`
}

type descriptorHash struct {
	Descriptor flipDescriptor `json:"descriptor"`
	SHA256     string         `json:"sha256"`
}
