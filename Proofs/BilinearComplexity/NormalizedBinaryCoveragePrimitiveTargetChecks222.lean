import BilinearComplexity.NormalizedBinaryCoverageTables
import BilinearComplexity.NormalizedBinaryCoverageTargetData
import BilinearComplexity.NormalizedBinaryCompactEnumerationChecks222

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-!
# Primitive target equality for profile 222

This frozen computation checks the complete serialized target list, including
its order and every endpoint mask, against the compact exact-code table.

AI disclosure: produced with AI assistance (see `README`).
-/

namespace BilinearComplexity.NormalizedBinaryCoveragePrimitiveTargetChecks

open NormalizedBinaryCoverageData
open NormalizedBinaryCoverageTables
open NormalizedBinaryCoverageTargetData
open NormalizedBinaryCompactEnumeration

/-- The profile-222 raw actions have exactly the serialized targets obtained by
taking all ten ordered splits of every checked compact exact code. -/
theorem rawTargets222_eq_serializedTenSplits :
    rawActions222.map (·.target) =
      exactCodes222.flatMap (serializedTenSplits packed222) := by
  decide

#print axioms rawTargets222_eq_serializedTenSplits

end BilinearComplexity.NormalizedBinaryCoveragePrimitiveTargetChecks
