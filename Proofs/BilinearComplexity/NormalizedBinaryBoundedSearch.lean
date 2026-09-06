import BilinearComplexity.FiniteBoundedSearch
import BilinearComplexity.NormalizedBinaryNativeSuccessors

set_option autoImplicit false

/-!
# Certified bounded normalized binary native search

This module instantiates the generic exhaustive finite-set path search with the
proved-complete normalized binary native successor enumeration.  The returned
object contains an actual `BinaryCircuit.MovePath`, exact depth and altitude
bounds, and a lower bound against every native competitor satisfying the same
bounds.  The zero-edge root makes the search domain nonempty.

The reference search retains the complete path tree, including duplicate
successor presentations.  Its only runtime rejection is the exact endpoint
cardinality ceiling at each extension.
-/

namespace BilinearComplexity.NormalizedBinaryBoundedSearch

open BinaryCircuit
open NormalizedBinaryCarrier
open NormalizedBinaryAllModeMove

/-- The certified result type for normalized binary bounded search. -/
abbrev Result {p : Profile} (D : State p) (k H : ℕ) :=
  FiniteBoundedSearch.Result (@AllModeMove p) D k H

/-- Exhaustively search every normalized binary native path within the supplied
primitive-depth and cardinality bounds and return a minimum-cardinality
endpoint with its complete certificate.  Callers supply only the honest root
ceiling condition; successor coverage is the proved S1 theorem. -/
def optimize {p : Profile} (D : State p) (k H : ℕ) (hD : D.card ≤ H) :
    Result D k H :=
  FiniteBoundedSearch.optimize
    NormalizedBinaryNativeSuccessors.certifiedSuccessors
    (fun h => NormalizedBinaryNativeSuccessors.exists_mem_certifiedSuccessors_iff.mpr h)
    D k H hD

/-- The path selected by normalized bounded search preserves tensor evaluation. -/
theorem Result.preserves_evaluation {p : Profile} {D : State p} {k H : ℕ}
    (result : Result D k H) :
    stateEvaluation result.finish = stateEvaluation D :=
  allModeMovePath_preserves_evaluation result.path

/-- At depth zero the executable optimizer returns the root itself. -/
theorem optimize_zero_finish {p : Profile} (D : State p) (H : ℕ)
    (hD : D.card ≤ H) :
    (optimize D 0 H hD).finish = D := by
  exact FiniteBoundedSearch.optimize_zero_finish
    NormalizedBinaryNativeSuccessors.certifiedSuccessors
    (fun h => NormalizedBinaryNativeSuccessors.exists_mem_certifiedSuccessors_iff.mpr h)
    D H hD

example :
    let p : Profile := ⟨0, 0, 0⟩
    let D : State p := ∅
    (optimize D 0 0 (by decide)).finish = D := by
  rfl

#eval
  let p : Profile := ⟨0, 0, 0⟩
  let D : State p := ∅
  (optimize D 0 0 (by decide)).finish.card

#check @NormalizedBinaryNativeSuccessors.certifiedSuccessors
#check @NormalizedBinaryNativeSuccessors.exists_mem_certifiedSuccessors_iff
#check @optimize
#check @Result.preserves_evaluation
#print axioms optimize
#print axioms Result.preserves_evaluation

end BilinearComplexity.NormalizedBinaryBoundedSearch
