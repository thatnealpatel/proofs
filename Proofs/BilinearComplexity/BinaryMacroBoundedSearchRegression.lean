import BilinearComplexity.BinaryMacroBoundedSearch
import BilinearComplexity.NormalizedBinarySearchRegression

set_option autoImplicit false

/-!
# Macro-assisted search ground and executable regressions

The frozen S-B1 tests at budgets zero and one are boundary checks only: no
five-circuit macro fits those budgets. The separate borrowing-context test
executes the automatic provider at budget two and retains genuine macro traces.
These tests are not the complete primitive-versus-macro benchmark matrix.
-/

namespace BilinearComplexity.BinaryMacroBoundedSearch.Regression

open BinaryCircuit BinaryAmbientCarrier BinaryAmbientMoves
open BinaryAmbientTensorCoordinates BinaryAmbientFullFrame
open NormalizedBinaryCarrier (F2 profile221)
open NormalizedBinarySearchRegression NormalizedBinaryReplay221
open BinaryContextualMacroRecognition

/-- Identity full frame of the first binary factor. -/
abbrev firstFrame := LinearEquiv.refl F2 (Coord profile221.first)

/-- Identity full frame of the second binary factor. -/
abbrev secondFrame := LinearEquiv.refl F2 (Coord profile221.second)

/-- Identity full frame of the third binary factor. -/
abbrev thirdFrame := LinearEquiv.refl F2 (Coord profile221.third)

/-- S-B1 is a nonempty, concrete root satisfying the optimizer's ceiling. -/
example : suppliedState.Nonempty ∧ suppliedState.card ≤ 3 := by
  constructor
  · exact ⟨E11, by decide⟩
  · decide

/-- All intended coordinate and carrier domains of S-B1 are nonempty. -/
example : Nonempty (Coord 2) ∧ Nonempty (Coord 1) ∧
    Nonempty (Carrier (Coord 2) (Coord 2) (Coord 1)) :=
  ⟨⟨0⟩, ⟨0⟩, ⟨E11⟩⟩

/-- Automatic annotated S-B1 search at primitive budget zero. -/
def result0 : Result firstFrame secondFrame thirdFrame suppliedState 0 3 :=
  optimize firstFrame secondFrame thirdFrame suppliedState 0 3 (by decide)

/-- Automatic annotated S-B1 search at primitive budget one. -/
def result1 : Result firstFrame secondFrame thirdFrame suppliedState 1 3 :=
  optimize firstFrame secondFrame thirdFrame suppliedState 1 3 (by decide)

/-- Budget zero keeps the exact S-B1 root. -/
theorem result0_finish : result0.finish = suppliedState := by
  simp [result0, optimize, boundedCandidates, chooseBest, prefer, Candidate.root]

/-- The zero-budget regression has three terms and zero primitive edges. -/
theorem result0_data : result0.finish.card = 3 ∧
    (result0.path firstFrame secondFrame thirdFrame).length = 0 := by
  constructor
  · rw [result0_finish]
    exact suppliedState_card
  · exact Nat.le_zero.mp result0.length_le

/-- The independent one-edge S-B1 reduction is an ambient competitor only; it
is not supplied to either executable optimizer. -/
def comparisonPath : MovePath
    (AllModeMove (U := Coord profile221.first) (V := Coord profile221.second)
      (W := Coord profile221.third)) suppliedState S0 :=
  MovePath.one (BinaryAmbientMoves.Coordinate.allModeMove_iff_normalized.mpr
    (NormalizedBinaryAllModeMove.allModeMove_of_move
      (.directedNarrowPairReduction suppliedReduction)))

/-- The independently checked competitor has length one and ceiling three. -/
theorem comparisonPath_data : comparisonPath.length = 1 ∧ comparisonPath.altitude = 3 := by
  simp only [comparisonPath, MovePath.one, MovePath.length, MovePath.altitude,
    suppliedState_card, comparisonState_card]
  decide

/-- The one-budget automatic macro optimizer attains exactly two S-B1 terms. -/
theorem result1_card : result1.finish.card = 2 := by
  apply Nat.le_antisymm
  · have h := result1.optimal comparisonPath comparisonPath_data.1.le comparisonPath_data.2.le
    exact h.trans comparisonState_card.le
  · have h := two_le_endpoint_card_of_length_le_one
      (normalizePath firstFrame secondFrame thirdFrame
        (result1.path firstFrame secondFrame thirdFrame))
      ((normalizeState_card firstFrame secondFrame thirdFrame suppliedState).trans suppliedState_card)
      ((normalizePath_length firstFrame secondFrame thirdFrame _).trans_le result1.length_le)
    exact (normalizeState_card firstFrame secondFrame thirdFrame result1.finish) ▸ h

/-- Macro admission below cost two is exactly empty, not an optimization heuristic. -/
theorem low_budget_macros_empty :
    recognizedKeyList firstFrame secondFrame thirdFrame suppliedState 0 3 = [] ∧
      recognizedKeyList firstFrame secondFrame thirdFrame suppliedState 1 3 = [] := by
  constructor <;> rfl

example : admittedMacros firstFrame secondFrame thirdFrame suppliedState 0 3 = [] := rfl
example : admittedMacros firstFrame secondFrame thirdFrame suppliedState 1 3 = [] := rfl

/-- Every automatically generated borrowing-context macro is turned into a
one-node annotated trace, retaining the actual compiler result. -/
def borrowingMacroTraces : List (Candidate firstFrame secondFrame thirdFrame 2 7
    BinaryContextBorrowing221.contextualStart) :=
  (macroSteps firstFrame secondFrame thirdFrame
    BinaryContextBorrowing221.contextualStart 2 7).map fun step =>
      (Candidate.root firstFrame secondFrame thirdFrame 2 7
        BinaryContextBorrowing221.contextualStart).extend firstFrame secondFrame thirdFrame step

#eval (result0.finish.card, (result0.path firstFrame secondFrame thirdFrame).length,
  (result0.path firstFrame secondFrame thirdFrame).altitude,
  (result0.trace.macros firstFrame secondFrame thirdFrame).length)
#eval (result1.finish.card, (result1.path firstFrame secondFrame thirdFrame).length,
  (result1.path firstFrame secondFrame thirdFrame).altitude,
  (result1.trace.macros firstFrame secondFrame thirdFrame).length)
/-- Executable summaries of actual admitted, provenance-bearing macro traces. -/
def borrowingTraceData := borrowingMacroTraces.map fun candidate =>
  let path := candidate.path firstFrame secondFrame thirdFrame
  (path.vertices.map Finset.card, path.length, path.altitude,
    (candidate.trace.macros firstFrame secondFrame thirdFrame).length)

/-- Run the genuine automatic-macro regression in a compiled executable. Empty
admission is a failed regression, not a successful vacuous test. -/
def runBorrowingTraceRegression : IO Unit := do
  let data := borrowingTraceData
  if data.isEmpty then
    throw (IO.userError "automatic borrowing-context macro admission was empty")
  IO.println (reprStr data)

#check @borrowingMacroTraces
#check @borrowingTraceData
#check @runBorrowingTraceRegression
#check @result0_finish
#check @comparisonPath_data
#check @low_budget_macros_empty
#check @result0_data
#check @result1_card
#print axioms result0_data
#print axioms result1_card
#print axioms borrowingMacroTraces

end BilinearComplexity.BinaryMacroBoundedSearch.Regression
