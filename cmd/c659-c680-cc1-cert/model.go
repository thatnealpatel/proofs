package main

type inputBinding struct {
	ArgumentPosition     int    `json:"argument_position"`
	Role                 string `json:"role"`
	RepositoryRelativeID string `json:"repository_relative_id"`
	Bytes                int    `json:"bytes"`
	SHA256               string `json:"sha256"`
	Authenticated        bool   `json:"authenticated"`
}

type orientationBinding struct {
	Index     int    `json:"index"`
	Name      string `json:"name"`
	Positions [3]int `json:"positions"`
}

type moveContractReport struct {
	Move                     string               `json:"move"`
	Variant                  int                  `json:"variant"`
	RootTerms                int                  `json:"root_terms"`
	OrderedDistinctPairs     int                  `json:"ordered_distinct_pairs_per_root"`
	Orientations             []orientationBinding `json:"orientations"`
	DescriptorOrder          string               `json:"descriptor_order"`
	DescriptorEncoding       string               `json:"descriptor_encoding"`
	DescriptorsPerRoot       int                  `json:"descriptors_per_root"`
	Constructor              string               `json:"constructor"`
	IndependentReplay        string               `json:"independent_replay"`
	ChildRequirement         string               `json:"child_requirement"`
	Canonicalization         string               `json:"canonicalization"`
	CanonicalPayloadEncoding string               `json:"canonical_payload_encoding"`
	CanonicalPayloadBytes    int                  `json:"canonical_payload_bytes"`
	EqualityRule             string               `json:"equality_rule"`
	HashCollisionDefense     string               `json:"hash_collision_defense"`
}

type streamReport struct {
	ID                    string `json:"id"`
	Encoding              string `json:"encoding"`
	Count                 int    `json:"count"`
	Bytes                 int    `json:"bytes"`
	SHA256                string `json:"sha256"`
	DomainSeparatedSHA256 string `json:"domain_separated_sha256"`
}

type rootPayloadBinding struct {
	Bytes  int    `json:"bytes"`
	SHA256 string `json:"sha256"`
}

type frontierReport struct {
	OrderedDescriptors                int          `json:"ordered_descriptors"`
	ConstructorReplays                int          `json:"tensor_new_plus_replacement_replays"`
	IndependentFormulaReplays         int          `json:"independent_formula_replays"`
	NonzeroDistinctBrentValidChildren int          `json:"nonzero_distinct_brent_valid_children"`
	ExactCanonicalClasses             int          `json:"exact_canonical_classes"`
	AliasesPerClass                   int          `json:"aliases_per_class"`
	DescriptorStream                  streamReport `json:"descriptor_stream"`
	DescriptorCanonicalPayloadStream  streamReport `json:"descriptor_canonical_payload_stream"`
	SortedClassPayloadStream          streamReport `json:"sorted_class_payload_stream"`
	SortedClassAliasStream            streamReport `json:"sorted_class_alias_stream"`
}

type rootReport struct {
	Role                      string             `json:"role"`
	Terms                     int                `json:"terms"`
	OrderedFactorMajorPayload rootPayloadBinding `json:"ordered_factor_major_payload"`
	CanonicalRootPayload      rootPayloadBinding `json:"canonical_root_payload"`
	Nonzero                   bool               `json:"nonzero"`
	Distinct                  bool               `json:"distinct"`
	BrentValid                bool               `json:"brent_valid"`
	Frontier                  frontierReport     `json:"frontier"`
}

type corpusReplayReport struct {
	InputRole                  string       `json:"input_role"`
	SectionID                  string       `json:"section_id"`
	Offset                     int          `json:"offset"`
	Size                       int          `json:"size"`
	AuthenticatedSectionSHA256 string       `json:"authenticated_section_sha256"`
	RegeneratedStream          streamReport `json:"regenerated_stream"`
	ExactBytesEqual            bool         `json:"exact_bytes_equal"`
}

type comparisonReport struct {
	Method                        string       `json:"method"`
	HashesUsedAsEqualityEvidence  bool         `json:"hashes_used_as_equality_evidence"`
	C659Classes                   int          `json:"c659_classes"`
	C680Classes                   int          `json:"c680_classes"`
	ExactIntersectionCount        int          `json:"exact_intersection_count"`
	ExactUnionCount               int          `json:"exact_union_count"`
	SortedIntersectionPayloadsHex []string     `json:"sorted_intersection_payloads_lowercase_hex"`
	IntersectionPayloadStream     streamReport `json:"intersection_payload_stream"`
}

type scopeReport struct {
	Established string   `json:"established"`
	Excluded    []string `json:"excluded"`
}

type certificate struct {
	Schema              string             `json:"schema"`
	ExperimentID        string             `json:"experiment_id"`
	Status              string             `json:"status"`
	Result              string             `json:"result"`
	AuthenticatedInputs []inputBinding     `json:"authenticated_inputs"`
	MoveContract        moveContractReport `json:"move_contract"`
	Roots               []rootReport       `json:"roots"`
	CorpusReplay        corpusReplayReport `json:"corpus_replay"`
	ExactComparison     comparisonReport   `json:"exact_comparison"`
	Scope               scopeReport        `json:"scope"`
}
