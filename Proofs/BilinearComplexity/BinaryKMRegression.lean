import BilinearComplexity.BinaryKMReduction
import BilinearComplexity.BinaryAmbientMoveSupport
import BilinearComplexity.NormalizedBinaryCompactMaskSemantics

set_option autoImplicit false

/-!
# Public regressions for the effective indexed binary KM compiler

The four inputs in this file are the frozen coordinate regressions from the
indexed KM campaign. Coordinates are serialized as little-endian natural-number
bit masks in the native `(B,C,A)` order. Compiler execution and trace packets
are added below through the public `BinaryKMReduction` interface.
-/

namespace BilinearComplexity.BinaryKMRegression

open scoped BigOperators symmDiff
open BinaryAmbientCarrier
open BinaryAmbientMoves
open BinaryCircuit
open BinaryKMIndexedData
open BinaryKMReduction
open NormalizedBinaryCarrier
open NormalizedBinaryCompactMaskSemantics
open Lean

/-- A serialized native carrier atom, in `(B,C,A)` mask order. -/
structure MaskTerm where
  b : Nat
  c : Nat
  a : Nat
  deriving DecidableEq, Repr, ToJson

/-- Serialize a coordinate carrier atom as three little-endian masks. -/
def serializeTerm {dB dC dA : Nat}
    (t : Carrier (CoordinateVector dB) (CoordinateVector dC) (CoordinateVector dA)) :
    MaskTerm :=
  ⟨vectorMask t.1.1, vectorMask t.2.1.1, vectorMask t.2.2.1⟩

/-- Decode a nonzero in-range mask as an optional coordinate factor. -/
def factorOfMask? (d m : Nat) : Option (NonzeroVector d) :=
  if hpos : 0 < m then
    if hbound : m < 2 ^ d then
      some ⟨maskVector d m,
        NormalizedBinaryFiveCircuitRows.coordinateVectorOfMask_ne_zero d m hpos hbound⟩
    else none
  else none

/-- Decode three checked masks as an optional native coordinate carrier atom. -/
def termOfMasks? (dB dC dA : Nat) (m : MaskTerm) :
    Option (Carrier (CoordinateVector dB) (CoordinateVector dC) (CoordinateVector dA)) := do
  let b ← factorOfMask? dB m.b
  let c ← factorOfMask? dC m.c
  let a ← factorOfMask? dA m.a
  return (b, c, a)

/-- Enumerate all mask triples for nonzero factors in the three dimensions. -/
def allMaskTerms (dB dC dA : Nat) : List MaskTerm :=
  (List.range (2 ^ dB)).flatMap fun b =>
    (List.range (2 ^ dC)).flatMap fun c =>
      (List.range (2 ^ dA)).filterMap fun a =>
        let m : MaskTerm := ⟨b, c, a⟩
        (termOfMasks? dB dC dA m).map fun _ => m

/-- Serialize a coordinate state by scanning all valid mask triples in a fixed order. -/
def serializeState {dB dC dA : Nat}
    (D : State (CoordinateVector dB) (CoordinateVector dC) (CoordinateVector dA)) :
    List MaskTerm :=
  (allMaskTerms dB dC dA).filter fun m =>
    match termOfMasks? dB dC dA m with
    | some t => decide (t ∈ D)
    | none => false

example : factorOfMask? 2 0 = none := by decide

example : factorOfMask? 2 3 = some ⟨maskVector 2 3, by decide⟩ := by decide

example : allMaskTerms 1 1 1 = [⟨1, 1, 1⟩] := by decide

example : serializeTerm
    (⟨maskVector 2 1, by decide⟩, ⟨maskVector 2 3, by decide⟩,
      ⟨maskVector 1 1, by decide⟩) = ⟨1, 3, 1⟩ := by
  decide

example : serializeState
    ({(⟨maskVector 2 2, by decide⟩, ⟨maskVector 2 1, by decide⟩,
        ⟨maskVector 1 1, by decide⟩),
      (⟨maskVector 2 1, by decide⟩, ⟨maskVector 2 1, by decide⟩,
        ⟨maskVector 1 1, by decide⟩)} :
      State (CoordinateVector 2) (CoordinateVector 2) (CoordinateVector 1)) =
    [⟨1, 1, 1⟩, ⟨2, 1, 1⟩] := by
  decide

/-- Boolean checker equivalent to certified context admissibility. -/
def contextAdmissibilityCheck {B C A : Type*}
    [AddCommGroup B] [AddCommGroup C] [AddCommGroup A]
    [DecidableEq B] [DecidableEq C] [DecidableEq A]
    {n : Nat} (d : Data (B := B) (C := C) (A := A) n)
    (context : State B C A) : Bool :=
  decide (context ∩ d.sourceState = ∅) && decide (context ∩ d.targetState = ∅)

/-- The executable context checker is true exactly on admissible contexts. -/
theorem contextAdmissibilityCheck_eq_true_iff {B C A : Type*}
    [AddCommGroup B] [AddCommGroup C] [AddCommGroup A]
    [DecidableEq B] [DecidableEq C] [DecidableEq A]
    {n : Nat} (d : Data (B := B) (C := C) (A := A) n)
    (context : State B C A) :
    contextAdmissibilityCheck d context = true ↔ d.ContextAdmissible context := by
  simp only [contextAdmissibilityCheck, Bool.and_eq_true, decide_eq_true_eq]
  rw [BinaryKMIndexedData.Data.ContextAdmissible,
    Finset.disjoint_iff_inter_eq_empty, Finset.disjoint_iff_inter_eq_empty]

/-- Case 1: five independent first-mode factors, giving a six-to-five move. -/
def case1Data :
    Data (B := CoordinateVector 5) (C := CoordinateVector 2)
      (A := CoordinateVector 1) 5 := {
  a := maskVector 1 1
  b0 := maskVector 5 31
  c0 := maskVector 2 1
  b := ![maskVector 5 1, maskVector 5 2, maskVector 5 4,
    maskVector 5 8, maskVector 5 16]
  c := fun _ => maskVector 2 2
  a_ne_zero := by decide
  b0_ne_zero := by decide
  c0_ne_zero := by decide
  b_ne_zero := by decide
  c_ne_zero := by decide
  outputC_ne_zero := by decide
  b0_eq_sum := by decide
  source_injective := by decide }

/-- Case 1 has empty unchanged context. -/
def case1Context :
    State (CoordinateVector 5) (CoordinateVector 2) (CoordinateVector 1) := ∅

/-- Case 1's empty context is admissible. -/
theorem case1Context_admissible : case1Data.ContextAdmissible case1Context :=
  (contextAdmissibilityCheck_eq_true_iff case1Data case1Context).mp (by decide)

example : case1Data.sourceState.card = 6 ∧ case1Data.targetState.card = 5 ∧
    case1Data.changedIndices.card = 5 := by
  refine ⟨case1Data.sourceState_card, case1Data.targetState_card, ?_⟩
  decide

/-- Case 2 uses the same indexed data as case 1. -/
def case2Data :
    Data (B := CoordinateVector 5) (C := CoordinateVector 2)
      (A := CoordinateVector 1) 5 :=
  case1Data

/-- Case 2 occupies the masks `(30,1,1)` and `(1,1,1)` in the context. -/
def case2Context :
    State (CoordinateVector 5) (CoordinateVector 2) (CoordinateVector 1) :=
  {(⟨maskVector 5 30, by decide⟩, ⟨maskVector 2 1, by decide⟩,
      ⟨maskVector 1 1, by decide⟩),
    (⟨maskVector 5 1, by decide⟩, ⟨maskVector 2 1, by decide⟩,
      ⟨maskVector 1 1, by decide⟩)}

example : case2Data = case1Data := rfl

example : serializeState case2Context = [⟨1, 1, 1⟩, ⟨30, 1, 1⟩] := by decide

/-- Case 2's occupied auxiliary context is endpoint-disjoint and admissible. -/
theorem case2Context_admissible : case2Data.ContextAdmissible case2Context :=
  (contextAdmissibilityCheck_eq_true_iff case2Data case2Context).mp (by decide)

example : (case2Data.sourceEndpoint case2Context).card = 8 ∧
    (case2Data.targetEndpoint case2Context).card = 7 := by
  have hcontext : case2Context.card = 2 := by decide
  constructor
  · rw [case2Data.context_sourceEndpoint_card case2Context case2Context_admissible,
      hcontext]
  · rw [case2Data.context_targetEndpoint_card case2Context case2Context_admissible,
      hcontext]

/-- Case 3: three changed terms with proper residuals alternating between zero and one. -/
def case3Data :
    Data (B := CoordinateVector 1) (C := CoordinateVector 3)
      (A := CoordinateVector 1) 3 := {
  a := maskVector 1 1
  b0 := maskVector 1 1
  c0 := maskVector 3 1
  b := fun _ => maskVector 1 1
  c := ![maskVector 3 2, maskVector 3 4, maskVector 3 6]
  a_ne_zero := by decide
  b0_ne_zero := by decide
  c0_ne_zero := by decide
  b_ne_zero := by decide
  c_ne_zero := by decide
  outputC_ne_zero := by decide
  b0_eq_sum := by decide
  source_injective := by decide }

/-- Case 3 has empty unchanged context. -/
def case3Context :
    State (CoordinateVector 1) (CoordinateVector 3) (CoordinateVector 1) := ∅

/-- Case 3's empty context is admissible. -/
theorem case3Context_admissible : case3Data.ContextAdmissible case3Context :=
  (contextAdmissibilityCheck_eq_true_iff case3Data case3Context).mp (by decide)

example : case3Data.sourceState.card = 4 ∧ case3Data.targetState.card = 3 ∧
    case3Data.changedIndices.card = 3 := by
  refine ⟨case3Data.sourceState_card, case3Data.targetState_card, ?_⟩
  decide

/-- Case 4: an overlap two-cycle at indices zero and one, with only index two changed. -/
def case4Data :
    Data (B := CoordinateVector 2) (C := CoordinateVector 2)
      (A := CoordinateVector 1) 3 := {
  a := maskVector 1 1
  b0 := maskVector 2 2
  c0 := maskVector 2 1
  b := ![maskVector 2 1, maskVector 2 1, maskVector 2 2]
  c := ![maskVector 2 2, maskVector 2 3, maskVector 2 2]
  a_ne_zero := by decide
  b0_ne_zero := by decide
  c0_ne_zero := by decide
  b_ne_zero := by decide
  c_ne_zero := by decide
  outputC_ne_zero := by decide
  b0_eq_sum := by decide
  source_injective := by decide }

/-- Case 4 has empty unchanged context. -/
def case4Context :
    State (CoordinateVector 2) (CoordinateVector 2) (CoordinateVector 1) := ∅

/-- Case 4's empty context is admissible. -/
theorem case4Context_admissible : case4Data.ContextAdmissible case4Context :=
  (contextAdmissibilityCheck_eq_true_iff case4Data case4Context).mp (by decide)

example : case4Data.sourceState.card = 4 ∧ case4Data.targetState.card = 3 ∧
    case4Data.changedIndices = {2} ∧ case4Data.unchangedIndices = {0, 1} := by
  refine ⟨case4Data.sourceState_card, case4Data.targetState_card, ?_, ?_⟩
  · decide
  · decide

/-- The malformed case-1 output condition obtained by replacing `c[0]` with `c0`. -/
def case1BadOutputCheck : Bool :=
  decide (maskVector 2 1 + maskVector 2 1 ≠ 0)

example : case1BadOutputCheck = false := by decide

/-- Replacing `c[0]` by `c0` cannot supply the certified nonzero-output field. -/
theorem case1_bad_output_rejected :
    ¬(maskVector 2 1 + maskVector 2 1 ≠ 0) := by
  decide

/-- The target atom `(1,3,1)` whose insertion into context must be rejected. -/
def case1OccupiedTargetContext :
    State (CoordinateVector 5) (CoordinateVector 2) (CoordinateVector 1) :=
  {case1Data.targetTerm 0}

example : contextAdmissibilityCheck case1Data case1Context = true := by decide

/-- Decidable context-admissibility result for the occupied-target negative check. -/
def case1OccupiedTargetContextCheck : Bool :=
  contextAdmissibilityCheck case1Data case1OccupiedTargetContext

example : serializeState case1OccupiedTargetContext = [⟨1, 3, 1⟩] := by decide

example : case1OccupiedTargetContextCheck = false := by decide

/-- A context containing target atom `(1,3,1)` is not admissible. -/
theorem case1_occupied_target_context_rejected :
    ¬case1Data.ContextAdmissible case1OccupiedTargetContext := by
  intro hadmiss
  have hcheck := (contextAdmissibilityCheck_eq_true_iff
    case1Data case1OccupiedTargetContext).mpr hadmiss
  have hfalse : case1OccupiedTargetContextCheck = false := by decide
  change case1OccupiedTargetContextCheck = true at hcheck
  rw [hfalse] at hcheck
  contradiction

/-- One named negative-regression result in a machine-readable packet. -/
structure GuardResult where
  label : String
  rejected : Bool
  deriving Repr, ToJson

/-- Machine-readable observations from one actual certified compiler result. -/
structure RegressionPacket where
  label : String
  dimensions : List Nat
  context : List MaskTerm
  aMask : Nat
  b0Mask : Nat
  c0Mask : Nat
  bMasks : List Nat
  cMasks : List Nat
  pivot : MaskTerm
  changedIndices : List Nat
  suffixResidualMasks : List Nat
  source : List MaskTerm
  target : List MaskTerm
  vertices : List (List MaskTerm)
  localCosts : List Nat
  primitiveLength : Nat
  cardTrace : List Nat
  contextCardTrace : List Nat
  altitude : Nat
  carrier : List MaskTerm
  sourceMatches : Bool
  targetMatches : Bool
  contextInitiallyPresent : Bool
  contextRestored : Bool
  outsideCarrierStable : Bool
  carrierMatches : Bool
  lengthMatchesCosts : Bool
  lengthWithinBound : Bool
  altitudeWithinBound : Bool
  relationCertified : Bool
  evaluationReplayCertified : Bool
  negativeGuards : List GuardResult
  deriving Repr, ToJson

/-- Every intrinsic ambient move preserves the ambient tensor evaluation. -/
theorem allModeMove_preserves_evaluation
    {B C A : Type*} [AddCommGroup B] [AddCommGroup C] [AddCommGroup A]
    [Module F2 B] [Module F2 C] [Module F2 A]
    [DecidableEq B] [DecidableEq C] [DecidableEq A]
    {D E : State B C A} (h : AllModeMove D E) :
    BinaryAmbientCarrier.stateEvaluation D =
      BinaryAmbientCarrier.stateEvaluation E := by
  have hsymmDiff :
      BinaryAmbientCarrier.stateEvaluation (D ∆ E) =
        BinaryAmbientCarrier.stateEvaluation D +
          BinaryAmbientCarrier.stateEvaluation E := by
    simpa only [BinaryAmbientCarrier.stateEvaluation,
      BinaryCircuit.evaluation, BinaryCircuit.toggle] using
      (BinaryCircuit.evaluation_symmDiff
        (value := BinaryAmbientCarrier.tensorEvaluation
          (U := B) (V := C) (W := A)) D E)
  have hsum : BinaryAmbientCarrier.stateEvaluation D +
      BinaryAmbientCarrier.stateEvaluation E = 0 := by
    rw [← hsymmDiff]
    exact BinaryAmbientMoveSupport.AllModeMove.support_evaluation h
  calc
    BinaryAmbientCarrier.stateEvaluation D =
        BinaryAmbientCarrier.stateEvaluation D + 0 := (add_zero _).symm
    _ = BinaryAmbientCarrier.stateEvaluation D +
        (BinaryAmbientCarrier.stateEvaluation D +
          BinaryAmbientCarrier.stateEvaluation E) := by rw [hsum]
    _ = (BinaryAmbientCarrier.stateEvaluation D +
          BinaryAmbientCarrier.stateEvaluation D) +
        BinaryAmbientCarrier.stateEvaluation E := (add_assoc _ _ _).symm
    _ = BinaryAmbientCarrier.stateEvaluation E := by
      rw [BinaryCircuit.add_self_eq_zero, zero_add]

/-- Every actual vertex returned by the public compiler has the source evaluation. -/
theorem compilation_vertex_evaluation
    {B C A : Type*} [AddCommGroup B] [AddCommGroup C] [AddCommGroup A]
    [Module F2 B] [Module F2 C] [Module F2 A]
    [DecidableEq B] [DecidableEq C] [DecidableEq A]
    {n : Nat} (d : Data (B := B) (C := C) (A := A) n)
    (context : State B C A) (result : Compilation d context)
    (X : State B C A) (hX : X ∈ result.path.vertices) :
    BinaryAmbientCarrier.stateEvaluation X =
      BinaryAmbientCarrier.stateEvaluation (d.sourceEndpoint context) := by
  apply result.path.vertex_property
    (P := fun Y => BinaryAmbientCarrier.stateEvaluation Y =
      BinaryAmbientCarrier.stateEvaluation (d.sourceEndpoint context))
  · rfl
  · intro Y Z hYZ hY
    calc
      BinaryAmbientCarrier.stateEvaluation Z =
          BinaryAmbientCarrier.stateEvaluation Y :=
        (allModeMove_preserves_evaluation hYZ).symm
      _ = BinaryAmbientCarrier.stateEvaluation (d.sourceEndpoint context) := hY
  · exact hX

/-- Build the JSON-facing trace packet directly from a public compilation. -/
def makePacket {dB dC dA n : Nat} (label : String)
    (d : Data (B := CoordinateVector dB) (C := CoordinateVector dC)
      (A := CoordinateVector dA) n)
    (context : State (CoordinateVector dB) (CoordinateVector dC) (CoordinateVector dA))
    (result : Compilation d context) (negativeGuards : List GuardResult := []) :
    RegressionPacket :=
  let source := d.sourceEndpoint context
  let target := d.targetEndpoint context
  let vertices := result.path.vertices
  {
    label := label
    dimensions := [dB, dC, dA]
    context := serializeState context
    aMask := vectorMask d.a
    b0Mask := vectorMask d.b0
    c0Mask := vectorMask d.c0
    bMasks := (List.ofFn d.b).map vectorMask
    cMasks := (List.ofFn d.c).map vectorMask
    pivot := serializeTerm d.pivot
    changedIndices := (changedList d).map Fin.val
    suffixResidualMasks := (changedList d).tails.map fun indices =>
      vectorMask (suffixResidual d indices)
    source := serializeState source
    target := serializeState target
    vertices := vertices.map serializeState
    localCosts := result.localCosts
    primitiveLength := result.path.length
    cardTrace := vertices.map Finset.card
    contextCardTrace := vertices.map fun X => (context ∩ X).card
    altitude := result.path.altitude
    carrier := serializeState result.carrier
    sourceMatches := decide
      (vertices.head?.map serializeState = some (serializeState source))
    targetMatches := decide
      (vertices.getLast?.map serializeState = some (serializeState target))
    contextInitiallyPresent := decide (context \ source = ∅)
    contextRestored := decide (context \ target = ∅)
    outsideCarrierStable := vertices.all fun X =>
      decide (X \ result.carrier = source \ result.carrier)
    carrierMatches := decide
      (result.carrier = d.sourceState ∪ d.targetState ∪ foldCarrier d (changedList d))
    lengthMatchesCosts := decide (result.path.length = result.localCosts.sum)
    lengthWithinBound := decide (result.path.length ≤ 2 * d.changedIndices.card)
    altitudeWithinBound := decide (result.path.altitude ≤ source.card)
    relationCertified := true
    evaluationReplayCertified := true
    negativeGuards := negativeGuards
  }

/-- Actual public compiler result for frozen case 1. -/
def case1Compilation : Compilation case1Data case1Context :=
  compile case1Data case1Context case1Context_admissible

/-- Actual public compiler result for frozen case 2. -/
def case2Compilation : Compilation case2Data case2Context :=
  compile case2Data case2Context case2Context_admissible

/-- Actual public compiler result for frozen case 3. -/
def case3Compilation : Compilation case3Data case3Context :=
  compile case3Data case3Context case3Context_admissible

/-- Actual public compiler result for frozen case 4. -/
def case4Compilation : Compilation case4Data case4Context :=
  compile case4Data case4Context case4Context_admissible

/-- JSON-facing packet for frozen case 1, including both negative guards. -/
def case1Packet : RegressionPacket :=
  makePacket "case1-beyond-five" case1Data case1Context case1Compilation
    [⟨"c0-output-rejected", !case1BadOutputCheck⟩,
      ⟨"occupied-target-context-rejected", !case1OccupiedTargetContextCheck⟩]

/-- JSON-facing packet for frozen case 2. -/
def case2Packet : RegressionPacket :=
  makePacket "case2-occupied-auxiliaries" case2Data case2Context case2Compilation

/-- JSON-facing packet for frozen case 3. -/
def case3Packet : RegressionPacket :=
  makePacket "case3-zero-internal-residual" case3Data case3Context case3Compilation

/-- JSON-facing packet for frozen case 4. -/
def case4Packet : RegressionPacket :=
  makePacket "case4-endpoint-overlap" case4Data case4Context case4Compilation

example : case1Packet.label = "case1-beyond-five" := rfl
example : case2Packet.label = "case2-occupied-auxiliaries" := rfl
example : case3Packet.label = "case3-zero-internal-residual" := rfl
example : case4Packet.label = "case4-endpoint-overlap" := rfl

end BilinearComplexity.BinaryKMRegression
