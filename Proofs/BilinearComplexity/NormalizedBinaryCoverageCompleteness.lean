import BilinearComplexity.NormalizedBinaryCoverageTargetSetBridge
import BilinearComplexity.NormalizedBinaryCoveragePrimitiveTargetChecks221
import BilinearComplexity.NormalizedBinaryCoveragePrimitiveTargetChecks411
import BilinearComplexity.NormalizedBinaryCoveragePrimitiveTargetChecks321
import BilinearComplexity.NormalizedBinaryCoveragePrimitiveTargetChecks222
import BilinearComplexity.NormalizedBinaryCompactSemanticSupportBridge

set_option autoImplicit false

/-!
# Completeness of the normalized binary literal target tables

The four frozen primitive target checks and the compact semantic support bridge
are combined with the generic target-set theorem to identify each literal
coverage target set with the independently enumerated set of exact relations.

AI disclosure: produced with AI assistance (see `README`).
-/

namespace BilinearComplexity.NormalizedBinaryCoverageCompleteness

open NormalizedBinaryCarrier
open NormalizedBinaryCoverageTables
open NormalizedBinaryRelationEnumeration
open NormalizedBinaryCompactEnumeration
open NormalizedBinaryCoverageTargetSetBridge
open NormalizedBinaryCoveragePrimitiveTargetChecks
open NormalizedBinaryCompactSemanticSupportBridge

/-- The literal profile-221 target set contains exactly all semantic exact
relations of profile 221. -/
theorem literalTargetSet221_eq_allExactRelations :
    literalTargetSet221 = allExactRelations profile221 := by
  exact decodedTargetSet_eq_allExactRelations_of_rawTargets_eq
    rawActions221 packed221 exactCodes221
    rawTargets221_eq_serializedTenSplits exactCodes221_decodedSupport_iff

/-- The literal profile-411 target set contains exactly all semantic exact
relations of profile 411. -/
theorem literalTargetSet411_eq_allExactRelations :
    literalTargetSet411 = allExactRelations profile411 := by
  exact decodedTargetSet_eq_allExactRelations_of_rawTargets_eq
    rawActions411 packed411 exactCodes411
    rawTargets411_eq_serializedTenSplits exactCodes411_decodedSupport_iff

/-- The literal profile-321 target set contains exactly all semantic exact
relations of profile 321. -/
theorem literalTargetSet321_eq_allExactRelations :
    literalTargetSet321 = allExactRelations profile321 := by
  exact decodedTargetSet_eq_allExactRelations_of_rawTargets_eq
    rawActions321 packed321 exactCodes321
    rawTargets321_eq_serializedTenSplits exactCodes321_decodedSupport_iff

/-- The literal profile-222 target set contains exactly all semantic exact
relations of profile 222. -/
theorem literalTargetSet222_eq_allExactRelations :
    literalTargetSet222 = allExactRelations profile222 := by
  exact decodedTargetSet_eq_allExactRelations_of_rawTargets_eq
    rawActions222 packed222 exactCodes222
    rawTargets222_eq_serializedTenSplits exactCodes222_decodedSupport_iff

#check @literalTargetSet221_eq_allExactRelations
#check @literalTargetSet411_eq_allExactRelations
#check @literalTargetSet321_eq_allExactRelations
#check @literalTargetSet222_eq_allExactRelations
#print axioms literalTargetSet221_eq_allExactRelations
#print axioms literalTargetSet411_eq_allExactRelations
#print axioms literalTargetSet321_eq_allExactRelations
#print axioms literalTargetSet222_eq_allExactRelations

end BilinearComplexity.NormalizedBinaryCoverageCompleteness
