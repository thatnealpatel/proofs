package main

const (
	commandName                                = "c659-plusflip-cert"
	certificateSchema                          = "patel.codes/proofs/c659-plusflip-cert/v3"
	c659RootRole                               = "c659"
	c680RootRole                               = "c680"
	c659RootID                                 = "c659_iteration5551_Z2"
	c680RootID                                 = "c680_iteration4356_Z2"
	c659RootFileName                           = "4x4x4_m47_c659_iteration5551_Z2.txt"
	c680RootFileName                           = "4x4x4_m47_c680_iteration4356_Z2.txt"
	expectedC659RawSHA256                      = "25f47b5f37d2b7351dd5a2c5da65ff8ef5ba80ce53239d46cdfdef37e6eef403"
	expectedC680RawSHA256                      = "7e65a2fa888fcd9f32d9d68fd21ab8cdafeb4a39300cc77882def8e0115483e8"
	expectedC659OrderedFactorMajorSHA256       = "f61518b4864995fe5ba43f1b52819cc563c4c74326442ae12bbc338a491027cb"
	expectedC680OrderedFactorMajorSHA256       = "f6e3264df6e1a8c39c0af212c0ee0b490c7d96b0169c21b131b4c496fe04889b"
	expectedC659UnorderedCanonicalSHA256       = "f2edf6735401e203b532cc85e0783fb47684815a3207b3ec601f8503c48956d1"
	expectedC680UnorderedCanonicalSHA256       = "021266950ca5db9dd40593da2ec85d043469c1a15c66a04a06c2dbe23813c598"
	expectedPriorDescriptorSHA256              = "a3914d011a7983ed5dd241f8924144a225533e0a33c85df018091ae70ab755d9"
	priorScanOutputRule                        = "the independently completed c659 variant-0 Plus scan selected the least 64-character lowercase SHA-256 hexadecimal digest string of the unordered-canonical output bytes, compared lexicographically bytewise in ASCII order, not the least unordered-canonical bytes; this command only binds that scan and does not recompute it"
	expectedPlusChildSHA256                    = "0001430818e501c6964f6bf666e52a72cd0514605b3c69460e0d09cf80ec48e9"
	expectedFirstFlipSHA256                    = "640392811b97cf64b2ccf0c382666ba1ea2b91b859f815d0c957574378da8c90"
	expectedSecondFlipSHA256                   = "c567254223d480d8eaecde19d24f0aa96792208c41e2101a1270937bf1fe2934"
	expectedThirdFlipSHA256                    = "ee02607028804b19dbb6c075d2d290386dcb309cf740b826569b64550ebdddf0"
	expectedFourthFlipSHA256                   = "cbf85f130f4bf6decd79785c85112135ab8e55a8aa745188383aeaa541171351"
	expectedSemanticSHA256                     = "3815b52e97e44e4e31c81d2b0515982f6598fb765c832ca7d23f75229f95bfcf"
	expectedCompleteOutputSHA256               = "b067dd4008f35fb8b85ab1693e9e54d5d6dc11ac3b1336e584092753332cfe49"
	expectedC659RawBytes                       = 4524
	expectedC680RawBytes                       = 4524
	expectedRootOrderedFactorMajorPayloadBytes = 290
	expectedRootTerms                          = 47
	expectedPlusChildTerms                     = 48
	expectedCandidateCount                     = 6768
	expectedAcceptedCount                      = 4
	expectedRejectedCount                      = 6764
	expectedUniqueOutputCount                  = 4
	expectedMaximalClassCount                  = 10
	expectedDefectZeroCount                    = 6
	expectedDefectOneCount                     = 4
	expectedDefectAtLeastTwoCount              = 0
	expectedReductionCount                     = 4
	expectedPriorPlusDescriptors               = 12972
	expectedPriorUniquePlusOutputs             = 6486
	expectedPriorEqualFactorSubsets            = 13926
	expectedPriorPositiveDefectSubsets         = 0
)

var (
	expectedDimensions = [3]int{4, 4, 4}
	declaredRootSpecs  = [2]rootSpec{
		{
			ArgumentPosition:         1,
			Role:                     c659RootRole,
			ID:                       c659RootID,
			RootFileName:             c659RootFileName,
			RawBytes:                 expectedC659RawBytes,
			RawSHA256:                expectedC659RawSHA256,
			OrderedFactorMajorSHA256: expectedC659OrderedFactorMajorSHA256,
			UnorderedCanonicalSHA256: expectedC659UnorderedCanonicalSHA256,
		},
		{
			ArgumentPosition:         2,
			Role:                     c680RootRole,
			ID:                       c680RootID,
			RootFileName:             c680RootFileName,
			RawBytes:                 expectedC680RawBytes,
			RawSHA256:                expectedC680RawSHA256,
			OrderedFactorMajorSHA256: expectedC680OrderedFactorMajorSHA256,
			UnorderedCanonicalSHA256: expectedC680UnorderedCanonicalSHA256,
		},
	}
	plusRootSlots        = [2]int{7, 13}
	plusOrientation      = [3]int{0, 2, 1}
	plusInsertionSlots   = [3]int{45, 46, 47}
	expectedPlusInserted = []wordTriple{
		{50360, 56576, 10405},
		{5733, 55710, 273},
		{50360, 1182, 273},
	}
	expectedFlips = []preregisteredFlip{
		{Descriptor: flipDescriptor{FirstSlot: 45, SecondSlot: 47, SharedMode: 0, Coefficient: 1}, Hash: expectedFirstFlipSHA256},
		{Descriptor: flipDescriptor{FirstSlot: 46, SecondSlot: 47, SharedMode: 2, Coefficient: 1}, Hash: expectedSecondFlipSHA256},
		{Descriptor: flipDescriptor{FirstSlot: 47, SecondSlot: 45, SharedMode: 0, Coefficient: 1}, Hash: expectedThirdFlipSHA256},
		{Descriptor: flipDescriptor{FirstSlot: 47, SecondSlot: 46, SharedMode: 2, Coefficient: 1}, Hash: expectedFourthFlipSHA256},
	}
	expectedReductions = []preregisteredReduction{
		{OutputHash: expectedSecondFlipSHA256, SharedMode: 0, Inserted: wordTriple{50360, 56576, 10676}},
		{OutputHash: expectedSecondFlipSHA256, SharedMode: 1, Inserted: wordTriple{50360, 56576, 10676}},
		{OutputHash: expectedThirdFlipSHA256, SharedMode: 1, Inserted: wordTriple{53981, 55710, 273}},
		{OutputHash: expectedThirdFlipSHA256, SharedMode: 2, Inserted: wordTriple{53981, 55710, 273}},
	}
)
