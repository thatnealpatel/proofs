import BilinearComplexity.NormalizedBinaryCoverageTables
import BilinearComplexity.NormalizedBinaryCoverageTargetData
import BilinearComplexity.NormalizedBinaryCompactEnumerationChecksSmall

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-!
# Primitive target equality for profile 221

This frozen computation checks the complete serialized target list, including
its order and every endpoint mask, against the compact exact-code table.

AI disclosure: produced with AI assistance (see `README`).
-/

namespace BilinearComplexity.NormalizedBinaryCoveragePrimitiveTargetChecks

open NormalizedBinaryCoverageData
open NormalizedBinaryCoverageTables
open NormalizedBinaryCoverageTargetData
open NormalizedBinaryCompactEnumeration

/-- The profile-221 raw actions have exactly the serialized targets obtained by
taking all ten ordered splits of every checked compact exact code. -/
theorem rawTargets221_eq_serializedTenSplits :
    rawActions221.map (·.target) =
      exactCodes221.flatMap (serializedTenSplits packed221) := by
  decide

#print axioms rawTargets221_eq_serializedTenSplits

end BilinearComplexity.NormalizedBinaryCoveragePrimitiveTargetChecks
