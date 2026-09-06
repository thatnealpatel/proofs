import BilinearComplexity.BinaryContextualMacroRecognition

set_option autoImplicit false

namespace BilinearComplexity.BinaryContextualMacroRecognition.Regression

open BinaryCircuit NormalizedBinaryCarrier BinaryAmbientTensorCoordinates
open NormalizedBinaryReplay221 BinaryContextBorrowing221

/-- Identity full frame for the first factor of the borrowing regression. -/
abbrev firstFrame := LinearEquiv.refl F2 (Coord profile221.first)

/-- Identity full frame for the second factor of the borrowing regression. -/
abbrev secondFrame := LinearEquiv.refl F2 (Coord profile221.second)

/-- Identity full frame for the third factor of the borrowing regression. -/
abbrev thirdFrame := LinearEquiv.refl F2 (Coord profile221.third)

/-- The forward endpoint key, used only to inspect automatic enumeration. -/
def forwardKey : MacroKey (U := Coord profile221.first)
    (V := Coord profile221.second) (W := Coord profile221.third) :=
  ⟨.forward, endpointA, endpointB⟩

/-- The reverse endpoint key has an independently recognized three-term source. -/
def reverseKey : MacroKey (U := Coord profile221.first)
    (V := Coord profile221.second) (W := Coord profile221.third) :=
  ⟨.reverse, endpointA, endpointB⟩

/-- Execute recognition and retain the actual proof-bearing forward compilation
when its key is present. No presentation or witness path is supplied. -/
def forwardResult : Option
    (RecognizedMacro firstFrame secondFrame thirdFrame contextualStart) :=
  if h : forwardKey ∈ recognizeMacroKeys firstFrame secondFrame thirdFrame
      contextualStart 2 7 then
    some (compileRecognized firstFrame secondFrame thirdFrame contextualStart
      2 7 forwardKey h)
  else none

/-- Execute the same public recognizer in the reverse direction. -/
def reverseResult : Option
    (RecognizedMacro firstFrame secondFrame thirdFrame contextualFinish) :=
  if h : reverseKey ∈ recognizeMacroKeys firstFrame secondFrame thirdFrame
      contextualFinish 2 7 then
    some (compileRecognized firstFrame secondFrame thirdFrame contextualFinish
      2 7 reverseKey h)
  else none

/-- Rejection below two primitive steps follows from the generic cost theorem,
not from a supplied path or an external negative search. -/
theorem one_step_budget_rejected :
    recognizeMacroKeys firstFrame secondFrame thirdFrame contextualStart 1 7 = ∅ :=
  recognizeMacroKeys_eq_empty_of_lt_two firstFrame secondFrame thirdFrame
    contextualStart 1 7 (by decide)

#eval forwardKey ∈ recognizeMacroKeys firstFrame secondFrame thirdFrame contextualStart 2 7
#eval reverseKey ∈ recognizeMacroKeys firstFrame secondFrame thirdFrame contextualFinish 2 7
#eval forwardKey ∈ recognizeMacroKeys firstFrame secondFrame thirdFrame contextualStart 1 7
#eval forwardKey ∈ recognizeMacroKeys firstFrame secondFrame thirdFrame contextualStart 2 6
#eval decide (Applicable firstFrame secondFrame thirdFrame (endpointA ∪ {E12}) forwardKey)
#eval forwardResult.map fun r =>
  (decide (r.context = contextC), r.path.vertices.map Finset.card, r.path.length, r.path.altitude)
#eval reverseResult.map fun r =>
  (decide (r.context = contextC), r.path.vertices.map Finset.card, r.path.length, r.path.altitude)

#print axioms one_step_budget_rejected
#print axioms forwardResult
#print axioms reverseResult

end BilinearComplexity.BinaryContextualMacroRecognition.Regression
