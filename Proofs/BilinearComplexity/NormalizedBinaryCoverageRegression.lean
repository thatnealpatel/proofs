import BilinearComplexity.NormalizedBinaryCompactEnumerationCore
import BilinearComplexity.NormalizedBinaryCoverageData

set_option autoImplicit false
set_option maxRecDepth 1000000

/-!
# Small compact-coverage regression checks

These ground checks cover the compact counting helpers and the literal target
set decoder without reopening the frozen exhaustive table-check modules.
They do not prove semantic coverage or instantiate the normalized compiler.

AI disclosure: produced with AI assistance (see `README`).
-/

namespace BilinearComplexity.NormalizedBinaryCoverageRegression

open NormalizedBinaryCarrier
open NormalizedBinaryCompactEnumeration
open NormalizedBinaryCoverageData

example : exactSupportCount packed221 = 9 := by decide

example : exactSupportCountAtFirst packed221 9 = 0 := by decide

example : exactSupportCountFirstBlock packed221 0 0 = 0 := by decide

example : RawCoverageAction.decodedTargetSet
    ([] : List (RawCoverageAction profile221 (Fin 3))) = ∅ := rfl

end BilinearComplexity.NormalizedBinaryCoverageRegression
