import BilinearComplexity.NormalizedBinaryContextualKernel
import BilinearComplexity.NormalizedBinaryFiveCircuitRows

set_option autoImplicit false

/-!
# Contextual certificates for normalized binary five-circuit rows

This generated module contains candidate witness literals selected by the
external contextual search.  The external census is not trusted or imported:
Lean independently checks every native fixed-move replay, compact guard,
decision-tree coverage fact, endpoint, and constructed path length.  The
selected one- or two-bit guards are properties of these particular decision
trees, not a theorem that arbitrary contextual paths depend on only those bits.
See `NormalizedBinaryContextual.md` for provenance, reconstruction, and the
mask-coordinate convention.
-/

namespace BilinearComplexity.NormalizedBinaryContextualCertificates

open BinaryCircuit
open NormalizedBinaryCarrier
open NormalizedBinaryModePermutation
open NormalizedBinaryAllModeMove
open NormalizedBinaryAllModeMoveTransport
open NormalizedBinaryAllModeMoveData
open NormalizedBinaryFiveCircuitRows
open NormalizedBinaryContextualKernel

private abbrev stateDecidableEq321 (q : Profile) : DecidableEq (State q) :=
  @Finset.decidableEq (Carrier q) inferInstance

local instance instDecidableEqState321 (q : Profile) : DecidableEq (State q) :=
  stateDecidableEq321 q

local macro "maskTerm(" p:term "," a:num "," b:num "," c:num ")" : term =>
  `(carrierOfMasks $p $a $b $c (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide))

/-- Replayed guarded template 0 for the forward direction of row `32101`. -/
def row32101ForwardTemplate0 :
    ContextualPathTemplate profile321 row32101Start row32101Finish where
  moves := [⟨.bac, .reduction maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩,
    ⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 1, 3, 1) maskTerm(inversePermProfile .abc profile321, 2, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩,
    ⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩]
  present := ∅
  absent := {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 3, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32101Start ∪ ∅ = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1)} := by
      unfold row32101Start
      decide
    have hfinish : row32101Finish ∪ ∅ = {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32101Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .reduction maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1)} = some {maskTerm(profile321, 1, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 1, 3, 1) maskTerm(inversePermProfile .abc profile321, 2, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 3, 1)} = some {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1)} = some {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 1 for the forward direction of row `32101`. -/
def row32101ForwardTemplate1 :
    ContextualPathTemplate profile321 row32101Start row32101Finish where
  moves := [⟨.bac, .reduction maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩,
    ⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩,
    ⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 1, 3, 1) maskTerm(inversePermProfile .abc profile321, 2, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩]
  present := {maskTerm(profile321, 3, 3, 1)}
  absent := {maskTerm(profile321, 1, 3, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32101Start ∪ {maskTerm(profile321, 3, 3, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 3, 1)} := by
      unfold row32101Start
      decide
    have hfinish : row32101Finish ∪ {maskTerm(profile321, 3, 3, 1)} = {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32101Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .reduction maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 3, 1)} = some {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 3, 1)} = some {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 1, 3, 1) maskTerm(inversePermProfile .abc profile321, 2, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 2 for the forward direction of row `32101`. -/
def row32101ForwardTemplate2 :
    ContextualPathTemplate profile321 row32101Start row32101Finish where
  moves := [⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 1, 3, 1) maskTerm(inversePermProfile .abc profile321, 2, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩,
    ⟨.bac, .reduction maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩,
    ⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩]
  present := {maskTerm(profile321, 1, 3, 1)}
  absent := {maskTerm(profile321, 3, 3, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32101Start ∪ {maskTerm(profile321, 1, 3, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 1, 3, 1)} := by
      unfold row32101Start
      decide
    have hfinish : row32101Finish ∪ {maskTerm(profile321, 1, 3, 1)} = {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32101Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 1, 3, 1) maskTerm(inversePermProfile .abc profile321, 2, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 1, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .reduction maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1)} = some {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1)} = some {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 3 for the forward direction of row `32101`. -/
def row32101ForwardTemplate3 :
    ContextualPathTemplate profile321 row32101Start row32101Finish where
  moves := [⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩,
    ⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 1, 3, 1) maskTerm(inversePermProfile .abc profile321, 2, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩,
    ⟨.bac, .reduction maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩]
  present := {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 3, 1)}
  absent := ∅
  support_eq := by decide
  replay := by
    have hstart : row32101Start ∪ {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 3, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 3, 1)} := by
      unfold row32101Start
      decide
    have hfinish : row32101Finish ∪ {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 3, 1)} = {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32101Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 1, 3, 1) maskTerm(inversePermProfile .abc profile321, 2, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.bac, .reduction maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Total compact decision tree for the forward direction of row `32101`. -/
def row32101ForwardContextualTree :
    ContextualDecisionTree profile321 row32101Start row32101Finish 3 :=
  .branch maskTerm(profile321, 1, 3, 1)
    (.branch maskTerm(profile321, 3, 3, 1)
      (.leaf row32101ForwardTemplate0 (by decide))
      (.leaf row32101ForwardTemplate1 (by decide)))
    (.branch maskTerm(profile321, 3, 3, 1)
      (.leaf row32101ForwardTemplate2 (by decide))
      (.leaf row32101ForwardTemplate3 (by decide)))

/-- Kernel-checked full guard coverage for the forward tree of row `32101`. -/
theorem row32101ForwardContextualTree_valid :
    row32101ForwardContextualTree.Valid ∅ ∅ := by
  unfold row32101ForwardContextualTree
  unfold row32101ForwardTemplate0
  unfold row32101ForwardTemplate1
  unfold row32101ForwardTemplate2
  unfold row32101ForwardTemplate3
  simp only [ContextualDecisionTree.Valid]
  repeat' apply And.intro
  all_goals
    intro x hx
    aesop

/-- Executably select actual fixed witnesses for the forward direction of row `32101`. -/
def row32101ForwardContextualMoves (C : State profile321) : List (FixedMoveData profile321) :=
  row32101ForwardContextualTree.selectMoves C

/-- The selected forward witness list for row `32101` replays in every endpoint-disjoint context. -/
theorem run?_row32101ForwardContextualMoves (C : State profile321)
    (hC : Disjoint C (row32101Start ∪ row32101Finish)) :
    run? (C ∪ row32101Start) (row32101ForwardContextualMoves C) =
      some (C ∪ row32101Finish) := by
  exact row32101ForwardContextualTree.selectMoves_run? ∅ ∅
    row32101ForwardContextualTree_valid (Finset.empty_subset C)
    (Finset.disjoint_empty_right C) hC

/-- Compile the selected forward witnesses of row `32101` to an actual dependent move path. -/
def row32101ForwardContextualPath (C : State profile321)
    (hC : Disjoint C (row32101Start ∪ row32101Finish)) :
    MovePath (@AllModeMove profile321) (C ∪ row32101Start) (C ∪ row32101Finish) :=
  row32101ForwardContextualTree.toMovePath
    row32101ForwardContextualTree_valid hC

/-- The compiled forward contextual path for row `32101` has exact length `3`. -/
@[simp] theorem row32101ForwardContextualPath_length (C : State profile321)
    (hC : Disjoint C (row32101Start ∪ row32101Finish)) :
    (row32101ForwardContextualPath C hC).length = 3 := by
  exact ContextualDecisionTree.toMovePath_length _ _ _

/-- Replayed guarded template 0 for the reverse direction of row `32101`. -/
def row32101ReverseTemplate0 :
    ContextualPathTemplate profile321 row32101Finish row32101Start where
  moves := [⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩,
    ⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 2, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 1, 3, 1)⟩,
    ⟨.bac, .split maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1)⟩]
  present := ∅
  absent := {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 3, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32101Finish ∪ ∅ = {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32101Finish
      decide
    have hfinish : row32101Start ∪ ∅ = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1)} := by
      unfold row32101Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 2, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 1, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1)} = some {maskTerm(profile321, 1, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.bac, .split maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 1 for the reverse direction of row `32101`. -/
def row32101ReverseTemplate1 :
    ContextualPathTemplate profile321 row32101Finish row32101Start where
  moves := [⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 2, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 1, 3, 1)⟩,
    ⟨.bac, .split maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1)⟩,
    ⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩]
  present := {maskTerm(profile321, 3, 3, 1)}
  absent := {maskTerm(profile321, 1, 3, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32101Finish ∪ {maskTerm(profile321, 3, 3, 1)} = {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32101Finish
      decide
    have hfinish : row32101Start ∪ {maskTerm(profile321, 3, 3, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 3, 1)} := by
      unfold row32101Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 2, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 1, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .split maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 2 for the reverse direction of row `32101`. -/
def row32101ReverseTemplate2 :
    ContextualPathTemplate profile321 row32101Finish row32101Start where
  moves := [⟨.bac, .split maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1)⟩,
    ⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩,
    ⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 2, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 1, 3, 1)⟩]
  present := {maskTerm(profile321, 1, 3, 1)}
  absent := {maskTerm(profile321, 3, 3, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32101Finish ∪ {maskTerm(profile321, 1, 3, 1)} = {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32101Finish
      decide
    have hfinish : row32101Start ∪ {maskTerm(profile321, 1, 3, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 1, 3, 1)} := by
      unfold row32101Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .split maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 2, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 1, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 1, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 3 for the reverse direction of row `32101`. -/
def row32101ReverseTemplate3 :
    ContextualPathTemplate profile321 row32101Finish row32101Start where
  moves := [⟨.bac, .split maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1)⟩,
    ⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 2, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 1, 3, 1)⟩,
    ⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩]
  present := {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 3, 1)}
  absent := ∅
  support_eq := by decide
  replay := by
    have hstart : row32101Finish ∪ {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 3, 1)} = {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32101Finish
      decide
    have hfinish : row32101Start ∪ {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 3, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 3, 1)} := by
      unfold row32101Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .split maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 2, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 1, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Total compact decision tree for the reverse direction of row `32101`. -/
def row32101ReverseContextualTree :
    ContextualDecisionTree profile321 row32101Finish row32101Start 3 :=
  .branch maskTerm(profile321, 1, 3, 1)
    (.branch maskTerm(profile321, 3, 3, 1)
      (.leaf row32101ReverseTemplate0 (by decide))
      (.leaf row32101ReverseTemplate1 (by decide)))
    (.branch maskTerm(profile321, 3, 3, 1)
      (.leaf row32101ReverseTemplate2 (by decide))
      (.leaf row32101ReverseTemplate3 (by decide)))

/-- Kernel-checked full guard coverage for the reverse tree of row `32101`. -/
theorem row32101ReverseContextualTree_valid :
    row32101ReverseContextualTree.Valid ∅ ∅ := by
  unfold row32101ReverseContextualTree
  unfold row32101ReverseTemplate0
  unfold row32101ReverseTemplate1
  unfold row32101ReverseTemplate2
  unfold row32101ReverseTemplate3
  simp only [ContextualDecisionTree.Valid]
  repeat' apply And.intro
  all_goals
    intro x hx
    aesop

/-- Executably select actual fixed witnesses for the reverse direction of row `32101`. -/
def row32101ReverseContextualMoves (C : State profile321) : List (FixedMoveData profile321) :=
  row32101ReverseContextualTree.selectMoves C

/-- The selected reverse witness list for row `32101` replays in every endpoint-disjoint context. -/
theorem run?_row32101ReverseContextualMoves (C : State profile321)
    (hC : Disjoint C (row32101Finish ∪ row32101Start)) :
    run? (C ∪ row32101Finish) (row32101ReverseContextualMoves C) =
      some (C ∪ row32101Start) := by
  exact row32101ReverseContextualTree.selectMoves_run? ∅ ∅
    row32101ReverseContextualTree_valid (Finset.empty_subset C)
    (Finset.disjoint_empty_right C) hC

/-- Compile the selected reverse witnesses of row `32101` to an actual dependent move path. -/
def row32101ReverseContextualPath (C : State profile321)
    (hC : Disjoint C (row32101Finish ∪ row32101Start)) :
    MovePath (@AllModeMove profile321) (C ∪ row32101Finish) (C ∪ row32101Start) :=
  row32101ReverseContextualTree.toMovePath
    row32101ReverseContextualTree_valid hC

/-- The compiled reverse contextual path for row `32101` has exact length `3`. -/
@[simp] theorem row32101ReverseContextualPath_length (C : State profile321)
    (hC : Disjoint C (row32101Finish ∪ row32101Start)) :
    (row32101ReverseContextualPath C hC).length = 3 := by
  exact ContextualDecisionTree.toMovePath_length _ _ _

/-- Replayed guarded template 0 for the forward direction of row `32102`. -/
def row32102ForwardTemplate0 :
    ContextualPathTemplate profile321 row32102Start row32102Finish where
  moves := [⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1) maskTerm(inversePermProfile .bac profile321, 1, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩,
    ⟨.bac, .split maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 4, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 7, 1)⟩]
  present := {maskTerm(profile321, 3, 2, 1)}
  absent := {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 1, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32102Start ∪ {maskTerm(profile321, 3, 2, 1)} = {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1)} := by
      unfold row32102Start
      decide
    have hfinish : row32102Finish ∪ {maskTerm(profile321, 3, 2, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32102Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1) maskTerm(inversePermProfile .bac profile321, 1, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1)} = some {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 4, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .split maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 4, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 4, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 4, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 7, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 4, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 1 for the forward direction of row `32102`. -/
def row32102ForwardTemplate1 :
    ContextualPathTemplate profile321 row32102Start row32102Finish where
  moves := [⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩,
    ⟨.bac, .split maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 4, 1) maskTerm(inversePermProfile .bac profile321, 1, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 7, 1)⟩]
  present := {maskTerm(profile321, 3, 1, 1)}
  absent := {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 2, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32102Start ∪ {maskTerm(profile321, 3, 1, 1)} = {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 4, 3, 1)} := by
      unfold row32102Start
      decide
    have hfinish : row32102Finish ∪ {maskTerm(profile321, 3, 1, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32102Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 4, 3, 1)} = some {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .split maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 4, 1) maskTerm(inversePermProfile .bac profile321, 1, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 7, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 2 for the forward direction of row `32102`. -/
def row32102ForwardTemplate2 :
    ContextualPathTemplate profile321 row32102Start row32102Finish where
  moves := [⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 2, 3, 1) maskTerm(inversePermProfile .abc profile321, 1, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩,
    ⟨.bac, .split maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1)⟩,
    ⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩]
  present := ∅
  absent := {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 3, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32102Start ∪ ∅ = {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 4, 3, 1)} := by
      unfold row32102Start
      decide
    have hfinish : row32102Finish ∪ ∅ = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32102Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 2, 3, 1) maskTerm(inversePermProfile .abc profile321, 1, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 4, 3, 1)} = some {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .split maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 3 for the forward direction of row `32102`. -/
def row32102ForwardTemplate3 :
    ContextualPathTemplate profile321 row32102Start row32102Finish where
  moves := [⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 2, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 1, 3, 1)⟩,
    ⟨.bac, .split maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1)⟩,
    ⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩]
  present := {maskTerm(profile321, 3, 3, 1)}
  absent := {maskTerm(profile321, 1, 3, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32102Start ∪ {maskTerm(profile321, 3, 3, 1)} = {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1)} := by
      unfold row32102Start
      decide
    have hfinish : row32102Finish ∪ {maskTerm(profile321, 3, 3, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32102Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 2, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 1, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1)} = some {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 4, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .split maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 4, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 4, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 4, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 4 for the forward direction of row `32102`. -/
def row32102ForwardTemplate4 :
    ContextualPathTemplate profile321 row32102Start row32102Finish where
  moves := [⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 4, 1) maskTerm(inversePermProfile .bac profile321, 1, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩,
    ⟨.bac, .split maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 7, 1)⟩]
  present := {maskTerm(profile321, 5, 2, 1)}
  absent := {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 5, 1, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32102Start ∪ {maskTerm(profile321, 5, 2, 1)} = {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 5, 2, 1)} := by
      unfold row32102Start
      decide
    have hfinish : row32102Finish ∪ {maskTerm(profile321, 5, 2, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 5, 2, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32102Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 4, 1) maskTerm(inversePermProfile .bac profile321, 1, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 5, 2, 1)} = some {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 5, 1, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .split maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 5, 1, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 5, 1, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 7, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 5, 1, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 5, 2, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 5 for the forward direction of row `32102`. -/
def row32102ForwardTemplate5 :
    ContextualPathTemplate profile321 row32102Start row32102Finish where
  moves := [⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 4, 1) maskTerm(inversePermProfile .bac profile321, 2, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩,
    ⟨.bac, .split maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1) maskTerm(inversePermProfile .bac profile321, 1, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 7, 1)⟩]
  present := {maskTerm(profile321, 5, 1, 1)}
  absent := {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 5, 2, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32102Start ∪ {maskTerm(profile321, 5, 1, 1)} = {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 5, 1, 1)} := by
      unfold row32102Start
      decide
    have hfinish : row32102Finish ∪ {maskTerm(profile321, 5, 1, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 5, 1, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32102Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 4, 1) maskTerm(inversePermProfile .bac profile321, 2, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 5, 1, 1)} = some {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 5, 2, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .split maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 5, 2, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 5, 2, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1) maskTerm(inversePermProfile .bac profile321, 1, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 7, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 5, 2, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 5, 1, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 6 for the forward direction of row `32102`. -/
def row32102ForwardTemplate6 :
    ContextualPathTemplate profile321 row32102Start row32102Finish where
  moves := [⟨.bac, .split maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1) maskTerm(inversePermProfile .bac profile321, 1, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 4, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 7, 1)⟩]
  present := {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 2, 1)}
  absent := {maskTerm(profile321, 3, 1, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32102Start ∪ {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 2, 1)} = {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1)} := by
      unfold row32102Start
      decide
    have hfinish : row32102Finish ∪ {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 2, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32102Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .split maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1) maskTerm(inversePermProfile .bac profile321, 1, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 4, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 4, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 7, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 4, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 7 for the forward direction of row `32102`. -/
def row32102ForwardTemplate7 :
    ContextualPathTemplate profile321 row32102Start row32102Finish where
  moves := [⟨.bac, .split maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 4, 1) maskTerm(inversePermProfile .bac profile321, 1, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 7, 1)⟩]
  present := {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 1, 1)}
  absent := {maskTerm(profile321, 3, 2, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32102Start ∪ {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 1, 1)} = {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 4, 3, 1)} := by
      unfold row32102Start
      decide
    have hfinish : row32102Finish ∪ {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 1, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32102Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .split maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 4, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 4, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 4, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 4, 1) maskTerm(inversePermProfile .bac profile321, 1, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 7, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 8 for the forward direction of row `32102`. -/
def row32102ForwardTemplate8 :
    ContextualPathTemplate profile321 row32102Start row32102Finish where
  moves := [⟨.bac, .split maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1)⟩,
    ⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 2, 3, 1) maskTerm(inversePermProfile .abc profile321, 1, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩,
    ⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩]
  present := {maskTerm(profile321, 1, 3, 1)}
  absent := {maskTerm(profile321, 3, 3, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32102Start ∪ {maskTerm(profile321, 1, 3, 1)} = {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 4, 3, 1)} := by
      unfold row32102Start
      decide
    have hfinish : row32102Finish ∪ {maskTerm(profile321, 1, 3, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32102Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .split maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 4, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 4, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 2, 3, 1) maskTerm(inversePermProfile .abc profile321, 1, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 4, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 9 for the forward direction of row `32102`. -/
def row32102ForwardTemplate9 :
    ContextualPathTemplate profile321 row32102Start row32102Finish where
  moves := [⟨.bac, .split maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1)⟩,
    ⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 2, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 1, 3, 1)⟩,
    ⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩]
  present := {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 3, 1)}
  absent := ∅
  support_eq := by decide
  replay := by
    have hstart : row32102Start ∪ {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 3, 1)} = {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1)} := by
      unfold row32102Start
      decide
    have hfinish : row32102Finish ∪ {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 3, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32102Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .split maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 2, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 1, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 4, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 4, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 10 for the forward direction of row `32102`. -/
def row32102ForwardTemplate10 :
    ContextualPathTemplate profile321 row32102Start row32102Finish where
  moves := [⟨.bac, .split maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 4, 1) maskTerm(inversePermProfile .bac profile321, 1, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 7, 1)⟩]
  present := {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 5, 2, 1)}
  absent := {maskTerm(profile321, 5, 1, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32102Start ∪ {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 5, 2, 1)} = {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 5, 2, 1)} := by
      unfold row32102Start
      decide
    have hfinish : row32102Finish ∪ {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 5, 2, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 5, 2, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32102Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .split maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 5, 2, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 5, 2, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 4, 1) maskTerm(inversePermProfile .bac profile321, 1, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 5, 2, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 5, 1, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 7, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 5, 1, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 5, 2, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 11 for the forward direction of row `32102`. -/
def row32102ForwardTemplate11 :
    ContextualPathTemplate profile321 row32102Start row32102Finish where
  moves := [⟨.bac, .split maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 4, 1) maskTerm(inversePermProfile .bac profile321, 2, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1) maskTerm(inversePermProfile .bac profile321, 1, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 7, 1)⟩]
  present := {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 5, 1, 1)}
  absent := {maskTerm(profile321, 5, 2, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32102Start ∪ {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 5, 1, 1)} = {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 5, 1, 1)} := by
      unfold row32102Start
      decide
    have hfinish : row32102Finish ∪ {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 5, 1, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 5, 1, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32102Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .split maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 5, 1, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 5, 1, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 4, 1) maskTerm(inversePermProfile .bac profile321, 2, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 5, 1, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 5, 2, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1) maskTerm(inversePermProfile .bac profile321, 1, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 7, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 5, 2, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 5, 1, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Total compact decision tree for the forward direction of row `32102`. -/
def row32102ForwardContextualTree :
    ContextualDecisionTree profile321 row32102Start row32102Finish 3 :=
  .branch maskTerm(profile321, 1, 3, 1)
    (.branch maskTerm(profile321, 3, 1, 1)
      (.branch maskTerm(profile321, 5, 1, 1)
        (.branch maskTerm(profile321, 3, 2, 1)
          (.branch maskTerm(profile321, 5, 2, 1)
            (.branch maskTerm(profile321, 3, 3, 1)
              (.leaf row32102ForwardTemplate2 (by decide))
              (.leaf row32102ForwardTemplate3 (by decide)))
            (.leaf row32102ForwardTemplate4 (by decide)))
          (.leaf row32102ForwardTemplate0 (by decide)))
        (.branch maskTerm(profile321, 3, 2, 1)
          (.branch maskTerm(profile321, 5, 2, 1)
            (.leaf row32102ForwardTemplate5 (by decide))
            (.branch maskTerm(profile321, 3, 3, 1)
              (.leaf row32102ForwardTemplate2 (by decide))
              (.leaf row32102ForwardTemplate3 (by decide))))
          (.leaf row32102ForwardTemplate0 (by decide))))
      (.branch maskTerm(profile321, 5, 1, 1)
        (.branch maskTerm(profile321, 3, 2, 1)
          (.leaf row32102ForwardTemplate1 (by decide))
          (.branch maskTerm(profile321, 5, 2, 1)
            (.branch maskTerm(profile321, 3, 3, 1)
              (.leaf row32102ForwardTemplate2 (by decide))
              (.leaf row32102ForwardTemplate3 (by decide)))
            (.leaf row32102ForwardTemplate4 (by decide))))
        (.branch maskTerm(profile321, 3, 2, 1)
          (.leaf row32102ForwardTemplate1 (by decide))
          (.branch maskTerm(profile321, 5, 2, 1)
            (.leaf row32102ForwardTemplate5 (by decide))
            (.branch maskTerm(profile321, 3, 3, 1)
              (.leaf row32102ForwardTemplate2 (by decide))
              (.leaf row32102ForwardTemplate3 (by decide)))))))
    (.branch maskTerm(profile321, 3, 1, 1)
      (.branch maskTerm(profile321, 5, 1, 1)
        (.branch maskTerm(profile321, 3, 2, 1)
          (.branch maskTerm(profile321, 5, 2, 1)
            (.branch maskTerm(profile321, 3, 3, 1)
              (.leaf row32102ForwardTemplate8 (by decide))
              (.leaf row32102ForwardTemplate9 (by decide)))
            (.leaf row32102ForwardTemplate10 (by decide)))
          (.leaf row32102ForwardTemplate6 (by decide)))
        (.branch maskTerm(profile321, 3, 2, 1)
          (.branch maskTerm(profile321, 5, 2, 1)
            (.leaf row32102ForwardTemplate11 (by decide))
            (.branch maskTerm(profile321, 3, 3, 1)
              (.leaf row32102ForwardTemplate8 (by decide))
              (.leaf row32102ForwardTemplate9 (by decide))))
          (.leaf row32102ForwardTemplate6 (by decide))))
      (.branch maskTerm(profile321, 5, 1, 1)
        (.branch maskTerm(profile321, 3, 2, 1)
          (.leaf row32102ForwardTemplate7 (by decide))
          (.branch maskTerm(profile321, 5, 2, 1)
            (.branch maskTerm(profile321, 3, 3, 1)
              (.leaf row32102ForwardTemplate8 (by decide))
              (.leaf row32102ForwardTemplate9 (by decide)))
            (.leaf row32102ForwardTemplate10 (by decide))))
        (.branch maskTerm(profile321, 3, 2, 1)
          (.leaf row32102ForwardTemplate7 (by decide))
          (.branch maskTerm(profile321, 5, 2, 1)
            (.leaf row32102ForwardTemplate11 (by decide))
            (.branch maskTerm(profile321, 3, 3, 1)
              (.leaf row32102ForwardTemplate8 (by decide))
              (.leaf row32102ForwardTemplate9 (by decide)))))))

/-- Kernel-checked full guard coverage for the forward tree of row `32102`. -/
theorem row32102ForwardContextualTree_valid :
    row32102ForwardContextualTree.Valid ∅ ∅ := by
  unfold row32102ForwardContextualTree
  unfold row32102ForwardTemplate0
  unfold row32102ForwardTemplate1
  unfold row32102ForwardTemplate2
  unfold row32102ForwardTemplate3
  unfold row32102ForwardTemplate4
  unfold row32102ForwardTemplate5
  unfold row32102ForwardTemplate6
  unfold row32102ForwardTemplate7
  unfold row32102ForwardTemplate8
  unfold row32102ForwardTemplate9
  unfold row32102ForwardTemplate10
  unfold row32102ForwardTemplate11
  simp only [ContextualDecisionTree.Valid]
  repeat' apply And.intro
  all_goals
    intro x hx
    aesop

/-- Executably select actual fixed witnesses for the forward direction of row `32102`. -/
def row32102ForwardContextualMoves (C : State profile321) : List (FixedMoveData profile321) :=
  row32102ForwardContextualTree.selectMoves C

/-- The selected forward witness list for row `32102` replays in every endpoint-disjoint context. -/
theorem run?_row32102ForwardContextualMoves (C : State profile321)
    (hC : Disjoint C (row32102Start ∪ row32102Finish)) :
    run? (C ∪ row32102Start) (row32102ForwardContextualMoves C) =
      some (C ∪ row32102Finish) := by
  exact row32102ForwardContextualTree.selectMoves_run? ∅ ∅
    row32102ForwardContextualTree_valid (Finset.empty_subset C)
    (Finset.disjoint_empty_right C) hC

/-- Compile the selected forward witnesses of row `32102` to an actual dependent move path. -/
def row32102ForwardContextualPath (C : State profile321)
    (hC : Disjoint C (row32102Start ∪ row32102Finish)) :
    MovePath (@AllModeMove profile321) (C ∪ row32102Start) (C ∪ row32102Finish) :=
  row32102ForwardContextualTree.toMovePath
    row32102ForwardContextualTree_valid hC

/-- The compiled forward contextual path for row `32102` has exact length `3`. -/
@[simp] theorem row32102ForwardContextualPath_length (C : State profile321)
    (hC : Disjoint C (row32102Start ∪ row32102Finish)) :
    (row32102ForwardContextualPath C hC).length = 3 := by
  exact ContextualDecisionTree.toMovePath_length _ _ _

/-- Replayed guarded template 0 for the reverse direction of row `32102`. -/
def row32102ReverseTemplate0 :
    ContextualPathTemplate profile321 row32102Finish row32102Start where
  moves := [⟨.bac, .reduction maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 1, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 7, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 4, 1)⟩]
  present := {maskTerm(profile321, 3, 2, 1)}
  absent := {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 1, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32102Finish ∪ {maskTerm(profile321, 3, 2, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32102Finish
      decide
    have hfinish : row32102Start ∪ {maskTerm(profile321, 3, 2, 1)} = {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1)} := by
      unfold row32102Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .reduction maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 1, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 7, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 4, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 1 for the reverse direction of row `32102`. -/
def row32102ReverseTemplate1 :
    ContextualPathTemplate profile321 row32102Finish row32102Start where
  moves := [⟨.bac, .reduction maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 7, 1) maskTerm(inversePermProfile .bac profile321, 1, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 4, 1)⟩]
  present := {maskTerm(profile321, 3, 1, 1)}
  absent := {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 2, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32102Finish ∪ {maskTerm(profile321, 3, 1, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32102Finish
      decide
    have hfinish : row32102Start ∪ {maskTerm(profile321, 3, 1, 1)} = {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 4, 3, 1)} := by
      unfold row32102Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .reduction maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 7, 1) maskTerm(inversePermProfile .bac profile321, 1, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 4, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 4, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 2 for the reverse direction of row `32102`. -/
def row32102ReverseTemplate2 :
    ContextualPathTemplate profile321 row32102Finish row32102Start where
  moves := [⟨.bac, .reduction maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩,
    ⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 1, 3, 1) maskTerm(inversePermProfile .abc profile321, 2, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩,
    ⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1)⟩]
  present := ∅
  absent := {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 3, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32102Finish ∪ ∅ = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32102Finish
      decide
    have hfinish : row32102Start ∪ ∅ = {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 4, 3, 1)} := by
      unfold row32102Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .reduction maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 1, 3, 1) maskTerm(inversePermProfile .abc profile321, 2, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 4, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 3 for the reverse direction of row `32102`. -/
def row32102ReverseTemplate3 :
    ContextualPathTemplate profile321 row32102Finish row32102Start where
  moves := [⟨.bac, .reduction maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩,
    ⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 1, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 2, 3, 1)⟩,
    ⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 7, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1)⟩]
  present := {maskTerm(profile321, 3, 3, 1)}
  absent := {maskTerm(profile321, 1, 3, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32102Finish ∪ {maskTerm(profile321, 3, 3, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32102Finish
      decide
    have hfinish : row32102Start ∪ {maskTerm(profile321, 3, 3, 1)} = {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1)} := by
      unfold row32102Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .reduction maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 1, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 2, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 7, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 4 for the reverse direction of row `32102`. -/
def row32102ReverseTemplate4 :
    ContextualPathTemplate profile321 row32102Finish row32102Start where
  moves := [⟨.bac, .reduction maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 1, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 4, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 7, 1) maskTerm(inversePermProfile .bac profile321, 2, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1)⟩]
  present := {maskTerm(profile321, 5, 2, 1)}
  absent := {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 5, 1, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32102Finish ∪ {maskTerm(profile321, 5, 2, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 5, 2, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32102Finish
      decide
    have hfinish : row32102Start ∪ {maskTerm(profile321, 5, 2, 1)} = {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 5, 2, 1)} := by
      unfold row32102Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .reduction maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 5, 2, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 5, 2, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 1, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 4, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 5, 2, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 5, 1, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 7, 1) maskTerm(inversePermProfile .bac profile321, 2, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 5, 1, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 5, 2, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 5 for the reverse direction of row `32102`. -/
def row32102ReverseTemplate5 :
    ContextualPathTemplate profile321 row32102Finish row32102Start where
  moves := [⟨.bac, .reduction maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 4, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 7, 1) maskTerm(inversePermProfile .bac profile321, 1, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1)⟩]
  present := {maskTerm(profile321, 5, 1, 1)}
  absent := {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 5, 2, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32102Finish ∪ {maskTerm(profile321, 5, 1, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 5, 1, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32102Finish
      decide
    have hfinish : row32102Start ∪ {maskTerm(profile321, 5, 1, 1)} = {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 5, 1, 1)} := by
      unfold row32102Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .reduction maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 5, 1, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 5, 1, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 4, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 5, 1, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 5, 2, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 7, 1) maskTerm(inversePermProfile .bac profile321, 1, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 5, 2, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 5, 1, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 6 for the reverse direction of row `32102`. -/
def row32102ReverseTemplate6 :
    ContextualPathTemplate profile321 row32102Finish row32102Start where
  moves := [⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 1, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1)⟩,
    ⟨.bac, .reduction maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 7, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 4, 1)⟩]
  present := {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 2, 1)}
  absent := {maskTerm(profile321, 3, 1, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32102Finish ∪ {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 2, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32102Finish
      decide
    have hfinish : row32102Start ∪ {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 2, 1)} = {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1)} := by
      unfold row32102Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 1, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .reduction maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 7, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 4, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 7 for the reverse direction of row `32102`. -/
def row32102ReverseTemplate7 :
    ContextualPathTemplate profile321 row32102Finish row32102Start where
  moves := [⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1)⟩,
    ⟨.bac, .reduction maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 7, 1) maskTerm(inversePermProfile .bac profile321, 1, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 4, 1)⟩]
  present := {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 1, 1)}
  absent := {maskTerm(profile321, 3, 2, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32102Finish ∪ {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 1, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32102Finish
      decide
    have hfinish : row32102Start ∪ {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 1, 1)} = {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 4, 3, 1)} := by
      unfold row32102Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .reduction maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 7, 1) maskTerm(inversePermProfile .bac profile321, 1, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 4, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 4, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 8 for the reverse direction of row `32102`. -/
def row32102ReverseTemplate8 :
    ContextualPathTemplate profile321 row32102Finish row32102Start where
  moves := [⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 1, 3, 1) maskTerm(inversePermProfile .abc profile321, 2, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩,
    ⟨.bac, .reduction maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩,
    ⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1)⟩]
  present := {maskTerm(profile321, 1, 3, 1)}
  absent := {maskTerm(profile321, 3, 3, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32102Finish ∪ {maskTerm(profile321, 1, 3, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32102Finish
      decide
    have hfinish : row32102Start ∪ {maskTerm(profile321, 1, 3, 1)} = {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 4, 3, 1)} := by
      unfold row32102Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 1, 3, 1) maskTerm(inversePermProfile .abc profile321, 2, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .reduction maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 4, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 9 for the reverse direction of row `32102`. -/
def row32102ReverseTemplate9 :
    ContextualPathTemplate profile321 row32102Finish row32102Start where
  moves := [⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 1, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 2, 3, 1)⟩,
    ⟨.bac, .reduction maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩,
    ⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 7, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1)⟩]
  present := {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 3, 1)}
  absent := ∅
  support_eq := by decide
  replay := by
    have hstart : row32102Finish ∪ {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 3, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32102Finish
      decide
    have hfinish : row32102Start ∪ {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 3, 1)} = {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1)} := by
      unfold row32102Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 1, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 2, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .reduction maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 7, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 10 for the reverse direction of row `32102`. -/
def row32102ReverseTemplate10 :
    ContextualPathTemplate profile321 row32102Finish row32102Start where
  moves := [⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 1, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 4, 1)⟩,
    ⟨.bac, .reduction maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 7, 1) maskTerm(inversePermProfile .bac profile321, 2, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1)⟩]
  present := {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 5, 2, 1)}
  absent := {maskTerm(profile321, 5, 1, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32102Finish ∪ {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 5, 2, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 5, 2, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32102Finish
      decide
    have hfinish : row32102Start ∪ {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 5, 2, 1)} = {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 5, 2, 1)} := by
      unfold row32102Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 1, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 4, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 5, 2, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 5, 1, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .reduction maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 5, 1, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 5, 1, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 7, 1) maskTerm(inversePermProfile .bac profile321, 2, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 5, 1, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 5, 2, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 11 for the reverse direction of row `32102`. -/
def row32102ReverseTemplate11 :
    ContextualPathTemplate profile321 row32102Finish row32102Start where
  moves := [⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 4, 1)⟩,
    ⟨.bac, .reduction maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 7, 1) maskTerm(inversePermProfile .bac profile321, 1, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1)⟩]
  present := {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 5, 1, 1)}
  absent := {maskTerm(profile321, 5, 2, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32102Finish ∪ {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 5, 1, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 5, 1, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32102Finish
      decide
    have hfinish : row32102Start ∪ {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 5, 1, 1)} = {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 5, 1, 1)} := by
      unfold row32102Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 4, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 5, 1, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 5, 2, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .reduction maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 5, 2, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 5, 2, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 7, 1) maskTerm(inversePermProfile .bac profile321, 1, 5, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 5, 2, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 5, 1, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Total compact decision tree for the reverse direction of row `32102`. -/
def row32102ReverseContextualTree :
    ContextualDecisionTree profile321 row32102Finish row32102Start 3 :=
  .branch maskTerm(profile321, 1, 3, 1)
    (.branch maskTerm(profile321, 3, 1, 1)
      (.branch maskTerm(profile321, 5, 1, 1)
        (.branch maskTerm(profile321, 3, 2, 1)
          (.branch maskTerm(profile321, 5, 2, 1)
            (.branch maskTerm(profile321, 3, 3, 1)
              (.leaf row32102ReverseTemplate2 (by decide))
              (.leaf row32102ReverseTemplate3 (by decide)))
            (.leaf row32102ReverseTemplate4 (by decide)))
          (.leaf row32102ReverseTemplate0 (by decide)))
        (.branch maskTerm(profile321, 3, 2, 1)
          (.branch maskTerm(profile321, 5, 2, 1)
            (.leaf row32102ReverseTemplate5 (by decide))
            (.branch maskTerm(profile321, 3, 3, 1)
              (.leaf row32102ReverseTemplate2 (by decide))
              (.leaf row32102ReverseTemplate3 (by decide))))
          (.leaf row32102ReverseTemplate0 (by decide))))
      (.branch maskTerm(profile321, 5, 1, 1)
        (.branch maskTerm(profile321, 3, 2, 1)
          (.leaf row32102ReverseTemplate1 (by decide))
          (.branch maskTerm(profile321, 5, 2, 1)
            (.branch maskTerm(profile321, 3, 3, 1)
              (.leaf row32102ReverseTemplate2 (by decide))
              (.leaf row32102ReverseTemplate3 (by decide)))
            (.leaf row32102ReverseTemplate4 (by decide))))
        (.branch maskTerm(profile321, 3, 2, 1)
          (.leaf row32102ReverseTemplate1 (by decide))
          (.branch maskTerm(profile321, 5, 2, 1)
            (.leaf row32102ReverseTemplate5 (by decide))
            (.branch maskTerm(profile321, 3, 3, 1)
              (.leaf row32102ReverseTemplate2 (by decide))
              (.leaf row32102ReverseTemplate3 (by decide)))))))
    (.branch maskTerm(profile321, 3, 1, 1)
      (.branch maskTerm(profile321, 5, 1, 1)
        (.branch maskTerm(profile321, 3, 2, 1)
          (.branch maskTerm(profile321, 5, 2, 1)
            (.branch maskTerm(profile321, 3, 3, 1)
              (.leaf row32102ReverseTemplate8 (by decide))
              (.leaf row32102ReverseTemplate9 (by decide)))
            (.leaf row32102ReverseTemplate10 (by decide)))
          (.leaf row32102ReverseTemplate6 (by decide)))
        (.branch maskTerm(profile321, 3, 2, 1)
          (.branch maskTerm(profile321, 5, 2, 1)
            (.leaf row32102ReverseTemplate11 (by decide))
            (.branch maskTerm(profile321, 3, 3, 1)
              (.leaf row32102ReverseTemplate8 (by decide))
              (.leaf row32102ReverseTemplate9 (by decide))))
          (.leaf row32102ReverseTemplate6 (by decide))))
      (.branch maskTerm(profile321, 5, 1, 1)
        (.branch maskTerm(profile321, 3, 2, 1)
          (.leaf row32102ReverseTemplate7 (by decide))
          (.branch maskTerm(profile321, 5, 2, 1)
            (.branch maskTerm(profile321, 3, 3, 1)
              (.leaf row32102ReverseTemplate8 (by decide))
              (.leaf row32102ReverseTemplate9 (by decide)))
            (.leaf row32102ReverseTemplate10 (by decide))))
        (.branch maskTerm(profile321, 3, 2, 1)
          (.leaf row32102ReverseTemplate7 (by decide))
          (.branch maskTerm(profile321, 5, 2, 1)
            (.leaf row32102ReverseTemplate11 (by decide))
            (.branch maskTerm(profile321, 3, 3, 1)
              (.leaf row32102ReverseTemplate8 (by decide))
              (.leaf row32102ReverseTemplate9 (by decide)))))))

/-- Kernel-checked full guard coverage for the reverse tree of row `32102`. -/
theorem row32102ReverseContextualTree_valid :
    row32102ReverseContextualTree.Valid ∅ ∅ := by
  unfold row32102ReverseContextualTree
  unfold row32102ReverseTemplate0
  unfold row32102ReverseTemplate1
  unfold row32102ReverseTemplate2
  unfold row32102ReverseTemplate3
  unfold row32102ReverseTemplate4
  unfold row32102ReverseTemplate5
  unfold row32102ReverseTemplate6
  unfold row32102ReverseTemplate7
  unfold row32102ReverseTemplate8
  unfold row32102ReverseTemplate9
  unfold row32102ReverseTemplate10
  unfold row32102ReverseTemplate11
  simp only [ContextualDecisionTree.Valid]
  repeat' apply And.intro
  all_goals
    intro x hx
    aesop

/-- Executably select actual fixed witnesses for the reverse direction of row `32102`. -/
def row32102ReverseContextualMoves (C : State profile321) : List (FixedMoveData profile321) :=
  row32102ReverseContextualTree.selectMoves C

/-- The selected reverse witness list for row `32102` replays in every endpoint-disjoint context. -/
theorem run?_row32102ReverseContextualMoves (C : State profile321)
    (hC : Disjoint C (row32102Finish ∪ row32102Start)) :
    run? (C ∪ row32102Finish) (row32102ReverseContextualMoves C) =
      some (C ∪ row32102Start) := by
  exact row32102ReverseContextualTree.selectMoves_run? ∅ ∅
    row32102ReverseContextualTree_valid (Finset.empty_subset C)
    (Finset.disjoint_empty_right C) hC

/-- Compile the selected reverse witnesses of row `32102` to an actual dependent move path. -/
def row32102ReverseContextualPath (C : State profile321)
    (hC : Disjoint C (row32102Finish ∪ row32102Start)) :
    MovePath (@AllModeMove profile321) (C ∪ row32102Finish) (C ∪ row32102Start) :=
  row32102ReverseContextualTree.toMovePath
    row32102ReverseContextualTree_valid hC

/-- The compiled reverse contextual path for row `32102` has exact length `3`. -/
@[simp] theorem row32102ReverseContextualPath_length (C : State profile321)
    (hC : Disjoint C (row32102Finish ∪ row32102Start)) :
    (row32102ReverseContextualPath C hC).length = 3 := by
  exact ContextualDecisionTree.toMovePath_length _ _ _

/-- Replayed guarded template 0 for the forward direction of row `32103`. -/
def row32103ForwardTemplate0 :
    ContextualPathTemplate profile321 row32103Start row32103Finish where
  moves := [⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1)⟩,
    ⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩]
  present := {maskTerm(profile321, 2, 3, 1)}
  absent := {maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 3, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32103Start ∪ {maskTerm(profile321, 2, 3, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 2, 3, 1)} := by
      unfold row32103Start
      decide
    have hfinish : row32103Finish ∪ {maskTerm(profile321, 2, 3, 1)} = {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32103Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 2, 3, 1)} = some {maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 3, 1)} = some {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1)} = some {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 1 for the forward direction of row `32103`. -/
def row32103ForwardTemplate1 :
    ContextualPathTemplate profile321 row32103Start row32103Finish where
  moves := [⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1)⟩]
  present := {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1)}
  absent := {maskTerm(profile321, 1, 2, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32103Start ∪ {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1)} := by
      unfold row32103Start
      decide
    have hfinish : row32103Finish ∪ {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1)} = {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32103Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 2 for the forward direction of row `32103`. -/
def row32103ForwardTemplate2 :
    ContextualPathTemplate profile321 row32103Start row32103Finish where
  moves := [⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1)⟩,
    ⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩]
  present := {maskTerm(profile321, 1, 2, 1)}
  absent := {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32103Start ∪ {maskTerm(profile321, 1, 2, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 1, 1)} := by
      unfold row32103Start
      decide
    have hfinish : row32103Finish ∪ {maskTerm(profile321, 1, 2, 1)} = {maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32103Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 1, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 2, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 2, 1)} = some {maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1)} = some {maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 3 for the forward direction of row `32103`. -/
def row32103ForwardTemplate3 :
    ContextualPathTemplate profile321 row32103Start row32103Finish where
  moves := [⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1)⟩,
    ⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1)⟩]
  present := {maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 3, 1)}
  absent := {maskTerm(profile321, 2, 3, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32103Start ∪ {maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 3, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 3, 1)} := by
      unfold row32103Start
      decide
    have hfinish : row32103Finish ∪ {maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 3, 1)} = {maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32103Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 4 for the forward direction of row `32103`. -/
def row32103ForwardTemplate4 :
    ContextualPathTemplate profile321 row32103Start row32103Finish where
  moves := [⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 2, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 2, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 2, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1)⟩,
    ⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩]
  present := {maskTerm(profile321, 2, 2, 1)}
  absent := {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 3, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32103Start ∪ {maskTerm(profile321, 2, 2, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 2, 2, 1)} := by
      unfold row32103Start
      decide
    have hfinish : row32103Finish ∪ {maskTerm(profile321, 2, 2, 1)} = {maskTerm(profile321, 2, 2, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32103Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 2, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 2, 2, 1)} = some {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 2, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 2, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 2, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 2, 1)} = some {maskTerm(profile321, 2, 2, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 2, 2, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1)} = some {maskTerm(profile321, 2, 2, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 5 for the forward direction of row `32103`. -/
def row32103ForwardTemplate5 :
    ContextualPathTemplate profile321 row32103Start row32103Finish where
  moves := [⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 2, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1)⟩,
    ⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 2, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 2, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1)⟩]
  present := {maskTerm(profile321, 2, 2, 1), maskTerm(profile321, 3, 3, 1)}
  absent := {maskTerm(profile321, 1, 3, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32103Start ∪ {maskTerm(profile321, 2, 2, 1), maskTerm(profile321, 3, 3, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 2, 2, 1), maskTerm(profile321, 3, 3, 1)} := by
      unfold row32103Start
      decide
    have hfinish : row32103Finish ∪ {maskTerm(profile321, 2, 2, 1), maskTerm(profile321, 3, 3, 1)} = {maskTerm(profile321, 2, 2, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32103Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 2, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 2, 2, 1), maskTerm(profile321, 3, 3, 1)} = some {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1)} = some {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 2, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 2, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 2, 2, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 6 for the forward direction of row `32103`. -/
def row32103ForwardTemplate6 :
    ContextualPathTemplate profile321 row32103Start row32103Finish where
  moves := [⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 2, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 2, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 2, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1)⟩,
    ⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩]
  present := {maskTerm(profile321, 1, 3, 1)}
  absent := {maskTerm(profile321, 2, 2, 1), maskTerm(profile321, 3, 3, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32103Start ∪ {maskTerm(profile321, 1, 3, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 1, 1)} := by
      unfold row32103Start
      decide
    have hfinish : row32103Finish ∪ {maskTerm(profile321, 1, 3, 1)} = {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32103Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 2, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 2, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 1, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 2, 1), maskTerm(profile321, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 2, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 2, 1), maskTerm(profile321, 3, 3, 1)} = some {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1)} = some {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 7 for the forward direction of row `32103`. -/
def row32103ForwardTemplate7 :
    ContextualPathTemplate profile321 row32103Start row32103Finish where
  moves := [⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 2, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 2, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 2, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1)⟩]
  present := {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 3, 1)}
  absent := {maskTerm(profile321, 2, 2, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32103Start ∪ {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 3, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 3, 1)} := by
      unfold row32103Start
      decide
    have hfinish : row32103Finish ∪ {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 3, 1)} = {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32103Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 2, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 2, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 2, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 2, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 2, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 8 for the forward direction of row `32103`. -/
def row32103ForwardTemplate8 :
    ContextualPathTemplate profile321 row32103Start row32103Finish where
  moves := [⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 1, 1, 1) maskTerm(inversePermProfile .abc profile321, 2, 1, 1) maskTerm(inversePermProfile .abc profile321, 3, 1, 1)⟩,
    ⟨.bac, .split maskTerm(inversePermProfile .bac profile321, 1, 3, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1)⟩,
    ⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩]
  present := ∅
  absent := {maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 3, 3, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32103Start ∪ ∅ = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1)} := by
      unfold row32103Start
      decide
    have hfinish : row32103Finish ∪ ∅ = {maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32103Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 1, 1, 1) maskTerm(inversePermProfile .abc profile321, 2, 1, 1) maskTerm(inversePermProfile .abc profile321, 3, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1)} = some {maskTerm(profile321, 3, 1, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .split maskTerm(inversePermProfile .bac profile321, 1, 3, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 3, 1, 1)} = some {maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1)} = some {maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 9 for the forward direction of row `32103`. -/
def row32103ForwardTemplate9 :
    ContextualPathTemplate profile321 row32103Start row32103Finish where
  moves := [⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 1, 1, 1) maskTerm(inversePermProfile .abc profile321, 2, 1, 1) maskTerm(inversePermProfile .abc profile321, 3, 1, 1)⟩,
    ⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩,
    ⟨.bac, .split maskTerm(inversePermProfile .bac profile321, 1, 3, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1)⟩]
  present := {maskTerm(profile321, 3, 3, 1)}
  absent := {maskTerm(profile321, 3, 1, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32103Start ∪ {maskTerm(profile321, 3, 3, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 3, 1)} := by
      unfold row32103Start
      decide
    have hfinish : row32103Finish ∪ {maskTerm(profile321, 3, 3, 1)} = {maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32103Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 1, 1, 1) maskTerm(inversePermProfile .abc profile321, 2, 1, 1) maskTerm(inversePermProfile .abc profile321, 3, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 3, 1)} = some {maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 3, 3, 1)} = some {maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.bac, .split maskTerm(inversePermProfile .bac profile321, 1, 3, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 10 for the forward direction of row `32103`. -/
def row32103ForwardTemplate10 :
    ContextualPathTemplate profile321 row32103Start row32103Finish where
  moves := [⟨.bac, .split maskTerm(inversePermProfile .bac profile321, 1, 3, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1)⟩,
    ⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 1, 1, 1) maskTerm(inversePermProfile .abc profile321, 2, 1, 1) maskTerm(inversePermProfile .abc profile321, 3, 1, 1)⟩,
    ⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩]
  present := {maskTerm(profile321, 3, 1, 1)}
  absent := {maskTerm(profile321, 3, 3, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32103Start ∪ {maskTerm(profile321, 3, 1, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 1, 1)} := by
      unfold row32103Start
      decide
    have hfinish : row32103Finish ∪ {maskTerm(profile321, 3, 1, 1)} = {maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32103Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .split maskTerm(inversePermProfile .bac profile321, 1, 3, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 1, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 1, 1, 1) maskTerm(inversePermProfile .abc profile321, 2, 1, 1) maskTerm(inversePermProfile .abc profile321, 3, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1)} = some {maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1)} = some {maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 11 for the forward direction of row `32103`. -/
def row32103ForwardTemplate11 :
    ContextualPathTemplate profile321 row32103Start row32103Finish where
  moves := [⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩,
    ⟨.bac, .split maskTerm(inversePermProfile .bac profile321, 1, 3, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1)⟩,
    ⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 1, 1, 1) maskTerm(inversePermProfile .abc profile321, 2, 1, 1) maskTerm(inversePermProfile .abc profile321, 3, 1, 1)⟩]
  present := {maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 3, 3, 1)}
  absent := ∅
  support_eq := by decide
  replay := by
    have hstart : row32103Start ∪ {maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 3, 3, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 3, 3, 1)} := by
      unfold row32103Start
      decide
    have hfinish : row32103Finish ∪ {maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 3, 3, 1)} = {maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32103Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 3, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .split maskTerm(inversePermProfile .bac profile321, 1, 3, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 1, 1, 1) maskTerm(inversePermProfile .abc profile321, 2, 1, 1) maskTerm(inversePermProfile .abc profile321, 3, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Total compact decision tree for the forward direction of row `32103`. -/
def row32103ForwardContextualTree :
    ContextualDecisionTree profile321 row32103Start row32103Finish 3 :=
  .branch maskTerm(profile321, 1, 2, 1)
    (.branch maskTerm(profile321, 1, 3, 1)
      (.branch maskTerm(profile321, 2, 2, 1)
        (.branch maskTerm(profile321, 2, 3, 1)
          (.branch maskTerm(profile321, 3, 1, 1)
            (.branch maskTerm(profile321, 3, 3, 1)
              (.leaf row32103ForwardTemplate8 (by decide))
              (.leaf row32103ForwardTemplate9 (by decide)))
            (.branch maskTerm(profile321, 3, 3, 1)
              (.leaf row32103ForwardTemplate10 (by decide))
              (.leaf row32103ForwardTemplate11 (by decide))))
          (.branch maskTerm(profile321, 3, 3, 1)
            (.leaf row32103ForwardTemplate0 (by decide))
            (.leaf row32103ForwardTemplate1 (by decide))))
        (.branch maskTerm(profile321, 2, 3, 1)
          (.branch maskTerm(profile321, 3, 3, 1)
            (.leaf row32103ForwardTemplate4 (by decide))
            (.leaf row32103ForwardTemplate5 (by decide)))
          (.branch maskTerm(profile321, 3, 3, 1)
            (.leaf row32103ForwardTemplate0 (by decide))
            (.leaf row32103ForwardTemplate1 (by decide)))))
      (.branch maskTerm(profile321, 2, 2, 1)
        (.branch maskTerm(profile321, 2, 3, 1)
          (.branch maskTerm(profile321, 3, 3, 1)
            (.leaf row32103ForwardTemplate6 (by decide))
            (.leaf row32103ForwardTemplate7 (by decide)))
          (.branch maskTerm(profile321, 3, 3, 1)
            (.leaf row32103ForwardTemplate0 (by decide))
            (.leaf row32103ForwardTemplate1 (by decide))))
        (.branch maskTerm(profile321, 2, 3, 1)
          (.branch maskTerm(profile321, 3, 1, 1)
            (.branch maskTerm(profile321, 3, 3, 1)
              (.leaf row32103ForwardTemplate8 (by decide))
              (.leaf row32103ForwardTemplate9 (by decide)))
            (.branch maskTerm(profile321, 3, 3, 1)
              (.leaf row32103ForwardTemplate10 (by decide))
              (.leaf row32103ForwardTemplate11 (by decide))))
          (.branch maskTerm(profile321, 3, 3, 1)
            (.leaf row32103ForwardTemplate0 (by decide))
            (.leaf row32103ForwardTemplate1 (by decide))))))
    (.branch maskTerm(profile321, 1, 3, 1)
      (.branch maskTerm(profile321, 2, 2, 1)
        (.branch maskTerm(profile321, 2, 3, 1)
          (.branch maskTerm(profile321, 3, 3, 1)
            (.leaf row32103ForwardTemplate2 (by decide))
            (.leaf row32103ForwardTemplate3 (by decide)))
          (.branch maskTerm(profile321, 3, 1, 1)
            (.branch maskTerm(profile321, 3, 3, 1)
              (.leaf row32103ForwardTemplate8 (by decide))
              (.leaf row32103ForwardTemplate9 (by decide)))
            (.branch maskTerm(profile321, 3, 3, 1)
              (.leaf row32103ForwardTemplate10 (by decide))
              (.leaf row32103ForwardTemplate11 (by decide)))))
        (.branch maskTerm(profile321, 2, 3, 1)
          (.branch maskTerm(profile321, 3, 3, 1)
            (.leaf row32103ForwardTemplate2 (by decide))
            (.leaf row32103ForwardTemplate3 (by decide)))
          (.branch maskTerm(profile321, 3, 3, 1)
            (.leaf row32103ForwardTemplate4 (by decide))
            (.leaf row32103ForwardTemplate5 (by decide)))))
      (.branch maskTerm(profile321, 2, 2, 1)
        (.branch maskTerm(profile321, 2, 3, 1)
          (.branch maskTerm(profile321, 3, 3, 1)
            (.leaf row32103ForwardTemplate2 (by decide))
            (.leaf row32103ForwardTemplate3 (by decide)))
          (.branch maskTerm(profile321, 3, 3, 1)
            (.leaf row32103ForwardTemplate6 (by decide))
            (.leaf row32103ForwardTemplate7 (by decide))))
        (.branch maskTerm(profile321, 2, 3, 1)
          (.branch maskTerm(profile321, 3, 3, 1)
            (.leaf row32103ForwardTemplate2 (by decide))
            (.leaf row32103ForwardTemplate3 (by decide)))
          (.branch maskTerm(profile321, 3, 1, 1)
            (.branch maskTerm(profile321, 3, 3, 1)
              (.leaf row32103ForwardTemplate8 (by decide))
              (.leaf row32103ForwardTemplate9 (by decide)))
            (.branch maskTerm(profile321, 3, 3, 1)
              (.leaf row32103ForwardTemplate10 (by decide))
              (.leaf row32103ForwardTemplate11 (by decide)))))))

/-- Kernel-checked full guard coverage for the forward tree of row `32103`. -/
theorem row32103ForwardContextualTree_valid :
    row32103ForwardContextualTree.Valid ∅ ∅ := by
  unfold row32103ForwardContextualTree
  unfold row32103ForwardTemplate0
  unfold row32103ForwardTemplate1
  unfold row32103ForwardTemplate2
  unfold row32103ForwardTemplate3
  unfold row32103ForwardTemplate4
  unfold row32103ForwardTemplate5
  unfold row32103ForwardTemplate6
  unfold row32103ForwardTemplate7
  unfold row32103ForwardTemplate8
  unfold row32103ForwardTemplate9
  unfold row32103ForwardTemplate10
  unfold row32103ForwardTemplate11
  simp only [ContextualDecisionTree.Valid]
  repeat' apply And.intro
  all_goals
    intro x hx
    aesop

/-- Executably select actual fixed witnesses for the forward direction of row `32103`. -/
def row32103ForwardContextualMoves (C : State profile321) : List (FixedMoveData profile321) :=
  row32103ForwardContextualTree.selectMoves C

/-- The selected forward witness list for row `32103` replays in every endpoint-disjoint context. -/
theorem run?_row32103ForwardContextualMoves (C : State profile321)
    (hC : Disjoint C (row32103Start ∪ row32103Finish)) :
    run? (C ∪ row32103Start) (row32103ForwardContextualMoves C) =
      some (C ∪ row32103Finish) := by
  exact row32103ForwardContextualTree.selectMoves_run? ∅ ∅
    row32103ForwardContextualTree_valid (Finset.empty_subset C)
    (Finset.disjoint_empty_right C) hC

/-- Compile the selected forward witnesses of row `32103` to an actual dependent move path. -/
def row32103ForwardContextualPath (C : State profile321)
    (hC : Disjoint C (row32103Start ∪ row32103Finish)) :
    MovePath (@AllModeMove profile321) (C ∪ row32103Start) (C ∪ row32103Finish) :=
  row32103ForwardContextualTree.toMovePath
    row32103ForwardContextualTree_valid hC

/-- The compiled forward contextual path for row `32103` has exact length `3`. -/
@[simp] theorem row32103ForwardContextualPath_length (C : State profile321)
    (hC : Disjoint C (row32103Start ∪ row32103Finish)) :
    (row32103ForwardContextualPath C hC).length = 3 := by
  exact ContextualDecisionTree.toMovePath_length _ _ _

/-- Replayed guarded template 0 for the reverse direction of row `32103`. -/
def row32103ReverseTemplate0 :
    ContextualPathTemplate profile321 row32103Finish row32103Start where
  moves := [⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 3, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1)⟩,
    ⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1)⟩]
  present := {maskTerm(profile321, 2, 3, 1)}
  absent := {maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 3, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32103Finish ∪ {maskTerm(profile321, 2, 3, 1)} = {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32103Finish
      decide
    have hfinish : row32103Start ∪ {maskTerm(profile321, 2, 3, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 2, 3, 1)} := by
      unfold row32103Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 3, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 2, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 1 for the reverse direction of row `32103`. -/
def row32103ReverseTemplate1 :
    ContextualPathTemplate profile321 row32103Finish row32103Start where
  moves := [⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 3, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1)⟩,
    ⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩]
  present := {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1)}
  absent := {maskTerm(profile321, 1, 2, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32103Finish ∪ {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1)} = {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32103Finish
      decide
    have hfinish : row32103Start ∪ {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1)} := by
      unfold row32103Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 3, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 2 for the reverse direction of row `32103`. -/
def row32103ReverseTemplate2 :
    ContextualPathTemplate profile321 row32103Finish row32103Start where
  moves := [⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 3, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1)⟩]
  present := {maskTerm(profile321, 1, 2, 1)}
  absent := {maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32103Finish ∪ {maskTerm(profile321, 1, 2, 1)} = {maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32103Finish
      decide
    have hfinish : row32103Start ∪ {maskTerm(profile321, 1, 2, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 1, 1)} := by
      unfold row32103Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 2, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 3, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 2, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 1, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 3 for the reverse direction of row `32103`. -/
def row32103ReverseTemplate3 :
    ContextualPathTemplate profile321 row32103Finish row32103Start where
  moves := [⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 3, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1)⟩,
    ⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩]
  present := {maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 3, 1)}
  absent := {maskTerm(profile321, 2, 3, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32103Finish ∪ {maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 3, 1)} = {maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32103Finish
      decide
    have hfinish : row32103Start ∪ {maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 3, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 3, 1)} := by
      unfold row32103Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 3, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 4 for the reverse direction of row `32103`. -/
def row32103ReverseTemplate4 :
    ContextualPathTemplate profile321 row32103Finish row32103Start where
  moves := [⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 2, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 2, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 2, 1)⟩]
  present := {maskTerm(profile321, 2, 2, 1)}
  absent := {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 3, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32103Finish ∪ {maskTerm(profile321, 2, 2, 1)} = {maskTerm(profile321, 2, 2, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32103Finish
      decide
    have hfinish : row32103Start ∪ {maskTerm(profile321, 2, 2, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 2, 2, 1)} := by
      unfold row32103Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 2, 2, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 2, 2, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 2, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 2, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 2, 2, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1)} = some {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 2, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 2, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 2, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 2, 2, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 5 for the reverse direction of row `32103`. -/
def row32103ReverseTemplate5 :
    ContextualPathTemplate profile321 row32103Finish row32103Start where
  moves := [⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 2, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 2, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 2, 1)⟩,
    ⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩]
  present := {maskTerm(profile321, 2, 2, 1), maskTerm(profile321, 3, 3, 1)}
  absent := {maskTerm(profile321, 1, 3, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32103Finish ∪ {maskTerm(profile321, 2, 2, 1), maskTerm(profile321, 3, 3, 1)} = {maskTerm(profile321, 2, 2, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32103Finish
      decide
    have hfinish : row32103Start ∪ {maskTerm(profile321, 2, 2, 1), maskTerm(profile321, 3, 3, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 2, 2, 1), maskTerm(profile321, 3, 3, 1)} := by
      unfold row32103Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 2, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 2, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 2, 2, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 2, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 2, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 2, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 2, 2, 1), maskTerm(profile321, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 6 for the reverse direction of row `32103`. -/
def row32103ReverseTemplate6 :
    ContextualPathTemplate profile321 row32103Finish row32103Start where
  moves := [⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 2, 1)⟩,
    ⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 2, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 2, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩]
  present := {maskTerm(profile321, 1, 3, 1)}
  absent := {maskTerm(profile321, 2, 2, 1), maskTerm(profile321, 3, 3, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32103Finish ∪ {maskTerm(profile321, 1, 3, 1)} = {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32103Finish
      decide
    have hfinish : row32103Start ∪ {maskTerm(profile321, 1, 3, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 1, 1)} := by
      unfold row32103Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 2, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 2, 1), maskTerm(profile321, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 2, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 2, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 2, 1), maskTerm(profile321, 3, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 1, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 7 for the reverse direction of row `32103`. -/
def row32103ReverseTemplate7 :
    ContextualPathTemplate profile321 row32103Finish row32103Start where
  moves := [⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 2, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 2, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 2, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩,
    ⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩]
  present := {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 3, 1)}
  absent := {maskTerm(profile321, 2, 2, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32103Finish ∪ {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 3, 1)} = {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32103Finish
      decide
    have hfinish : row32103Start ∪ {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 3, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 3, 1)} := by
      unfold row32103Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 3, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 2, 2, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 2, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 2, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 2, 1) maskTerm(inversePermProfile .bac profile321, 3, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 2, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 1, 3, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 8 for the reverse direction of row `32103`. -/
def row32103ReverseTemplate8 :
    ContextualPathTemplate profile321 row32103Finish row32103Start where
  moves := [⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩,
    ⟨.bac, .reduction maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 3, 1)⟩,
    ⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 3, 1, 1) maskTerm(inversePermProfile .abc profile321, 1, 1, 1) maskTerm(inversePermProfile .abc profile321, 2, 1, 1)⟩]
  present := ∅
  absent := {maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 3, 3, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32103Finish ∪ ∅ = {maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32103Finish
      decide
    have hfinish : row32103Start ∪ ∅ = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1)} := by
      unfold row32103Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .reduction maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1)} = some {maskTerm(profile321, 3, 1, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 3, 1, 1) maskTerm(inversePermProfile .abc profile321, 1, 1, 1) maskTerm(inversePermProfile .abc profile321, 2, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 3, 1, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 9 for the reverse direction of row `32103`. -/
def row32103ReverseTemplate9 :
    ContextualPathTemplate profile321 row32103Finish row32103Start where
  moves := [⟨.bac, .reduction maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 3, 1)⟩,
    ⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 3, 1, 1) maskTerm(inversePermProfile .abc profile321, 1, 1, 1) maskTerm(inversePermProfile .abc profile321, 2, 1, 1)⟩,
    ⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩]
  present := {maskTerm(profile321, 3, 3, 1)}
  absent := {maskTerm(profile321, 3, 1, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32103Finish ∪ {maskTerm(profile321, 3, 3, 1)} = {maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32103Finish
      decide
    have hfinish : row32103Start ∪ {maskTerm(profile321, 3, 3, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 3, 1)} := by
      unfold row32103Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .reduction maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 3, 1, 1) maskTerm(inversePermProfile .abc profile321, 1, 1, 1) maskTerm(inversePermProfile .abc profile321, 2, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 10 for the reverse direction of row `32103`. -/
def row32103ReverseTemplate10 :
    ContextualPathTemplate profile321 row32103Finish row32103Start where
  moves := [⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 3, 1, 1) maskTerm(inversePermProfile .abc profile321, 1, 1, 1) maskTerm(inversePermProfile .abc profile321, 2, 1, 1)⟩,
    ⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩,
    ⟨.bac, .reduction maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 3, 1)⟩]
  present := {maskTerm(profile321, 3, 1, 1)}
  absent := {maskTerm(profile321, 3, 3, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32103Finish ∪ {maskTerm(profile321, 3, 1, 1)} = {maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32103Finish
      decide
    have hfinish : row32103Start ∪ {maskTerm(profile321, 3, 1, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 1, 1)} := by
      unfold row32103Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 3, 1, 1) maskTerm(inversePermProfile .abc profile321, 1, 1, 1) maskTerm(inversePermProfile .abc profile321, 2, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.bac, .reduction maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 1, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 11 for the reverse direction of row `32103`. -/
def row32103ReverseTemplate11 :
    ContextualPathTemplate profile321 row32103Finish row32103Start where
  moves := [⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 3, 1, 1) maskTerm(inversePermProfile .abc profile321, 1, 1, 1) maskTerm(inversePermProfile .abc profile321, 2, 1, 1)⟩,
    ⟨.bac, .reduction maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 3, 1)⟩,
    ⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩]
  present := {maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 3, 3, 1)}
  absent := ∅
  support_eq := by decide
  replay := by
    have hstart : row32103Finish ∪ {maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 3, 3, 1)} = {maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32103Finish
      decide
    have hfinish : row32103Start ∪ {maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 3, 3, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 3, 3, 1)} := by
      unfold row32103Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 3, 1, 1) maskTerm(inversePermProfile .abc profile321, 1, 1, 1) maskTerm(inversePermProfile .abc profile321, 2, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .reduction maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Total compact decision tree for the reverse direction of row `32103`. -/
def row32103ReverseContextualTree :
    ContextualDecisionTree profile321 row32103Finish row32103Start 3 :=
  .branch maskTerm(profile321, 1, 2, 1)
    (.branch maskTerm(profile321, 1, 3, 1)
      (.branch maskTerm(profile321, 2, 2, 1)
        (.branch maskTerm(profile321, 2, 3, 1)
          (.branch maskTerm(profile321, 3, 1, 1)
            (.branch maskTerm(profile321, 3, 3, 1)
              (.leaf row32103ReverseTemplate8 (by decide))
              (.leaf row32103ReverseTemplate9 (by decide)))
            (.branch maskTerm(profile321, 3, 3, 1)
              (.leaf row32103ReverseTemplate10 (by decide))
              (.leaf row32103ReverseTemplate11 (by decide))))
          (.branch maskTerm(profile321, 3, 3, 1)
            (.leaf row32103ReverseTemplate0 (by decide))
            (.leaf row32103ReverseTemplate1 (by decide))))
        (.branch maskTerm(profile321, 2, 3, 1)
          (.branch maskTerm(profile321, 3, 3, 1)
            (.leaf row32103ReverseTemplate4 (by decide))
            (.leaf row32103ReverseTemplate5 (by decide)))
          (.branch maskTerm(profile321, 3, 3, 1)
            (.leaf row32103ReverseTemplate0 (by decide))
            (.leaf row32103ReverseTemplate1 (by decide)))))
      (.branch maskTerm(profile321, 2, 2, 1)
        (.branch maskTerm(profile321, 2, 3, 1)
          (.branch maskTerm(profile321, 3, 3, 1)
            (.leaf row32103ReverseTemplate6 (by decide))
            (.leaf row32103ReverseTemplate7 (by decide)))
          (.branch maskTerm(profile321, 3, 3, 1)
            (.leaf row32103ReverseTemplate0 (by decide))
            (.leaf row32103ReverseTemplate1 (by decide))))
        (.branch maskTerm(profile321, 2, 3, 1)
          (.branch maskTerm(profile321, 3, 1, 1)
            (.branch maskTerm(profile321, 3, 3, 1)
              (.leaf row32103ReverseTemplate8 (by decide))
              (.leaf row32103ReverseTemplate9 (by decide)))
            (.branch maskTerm(profile321, 3, 3, 1)
              (.leaf row32103ReverseTemplate10 (by decide))
              (.leaf row32103ReverseTemplate11 (by decide))))
          (.branch maskTerm(profile321, 3, 3, 1)
            (.leaf row32103ReverseTemplate0 (by decide))
            (.leaf row32103ReverseTemplate1 (by decide))))))
    (.branch maskTerm(profile321, 1, 3, 1)
      (.branch maskTerm(profile321, 2, 2, 1)
        (.branch maskTerm(profile321, 2, 3, 1)
          (.branch maskTerm(profile321, 3, 3, 1)
            (.leaf row32103ReverseTemplate2 (by decide))
            (.leaf row32103ReverseTemplate3 (by decide)))
          (.branch maskTerm(profile321, 3, 1, 1)
            (.branch maskTerm(profile321, 3, 3, 1)
              (.leaf row32103ReverseTemplate8 (by decide))
              (.leaf row32103ReverseTemplate9 (by decide)))
            (.branch maskTerm(profile321, 3, 3, 1)
              (.leaf row32103ReverseTemplate10 (by decide))
              (.leaf row32103ReverseTemplate11 (by decide)))))
        (.branch maskTerm(profile321, 2, 3, 1)
          (.branch maskTerm(profile321, 3, 3, 1)
            (.leaf row32103ReverseTemplate2 (by decide))
            (.leaf row32103ReverseTemplate3 (by decide)))
          (.branch maskTerm(profile321, 3, 3, 1)
            (.leaf row32103ReverseTemplate4 (by decide))
            (.leaf row32103ReverseTemplate5 (by decide)))))
      (.branch maskTerm(profile321, 2, 2, 1)
        (.branch maskTerm(profile321, 2, 3, 1)
          (.branch maskTerm(profile321, 3, 3, 1)
            (.leaf row32103ReverseTemplate2 (by decide))
            (.leaf row32103ReverseTemplate3 (by decide)))
          (.branch maskTerm(profile321, 3, 3, 1)
            (.leaf row32103ReverseTemplate6 (by decide))
            (.leaf row32103ReverseTemplate7 (by decide))))
        (.branch maskTerm(profile321, 2, 3, 1)
          (.branch maskTerm(profile321, 3, 3, 1)
            (.leaf row32103ReverseTemplate2 (by decide))
            (.leaf row32103ReverseTemplate3 (by decide)))
          (.branch maskTerm(profile321, 3, 1, 1)
            (.branch maskTerm(profile321, 3, 3, 1)
              (.leaf row32103ReverseTemplate8 (by decide))
              (.leaf row32103ReverseTemplate9 (by decide)))
            (.branch maskTerm(profile321, 3, 3, 1)
              (.leaf row32103ReverseTemplate10 (by decide))
              (.leaf row32103ReverseTemplate11 (by decide)))))))

/-- Kernel-checked full guard coverage for the reverse tree of row `32103`. -/
theorem row32103ReverseContextualTree_valid :
    row32103ReverseContextualTree.Valid ∅ ∅ := by
  unfold row32103ReverseContextualTree
  unfold row32103ReverseTemplate0
  unfold row32103ReverseTemplate1
  unfold row32103ReverseTemplate2
  unfold row32103ReverseTemplate3
  unfold row32103ReverseTemplate4
  unfold row32103ReverseTemplate5
  unfold row32103ReverseTemplate6
  unfold row32103ReverseTemplate7
  unfold row32103ReverseTemplate8
  unfold row32103ReverseTemplate9
  unfold row32103ReverseTemplate10
  unfold row32103ReverseTemplate11
  simp only [ContextualDecisionTree.Valid]
  repeat' apply And.intro
  all_goals
    intro x hx
    aesop

/-- Executably select actual fixed witnesses for the reverse direction of row `32103`. -/
def row32103ReverseContextualMoves (C : State profile321) : List (FixedMoveData profile321) :=
  row32103ReverseContextualTree.selectMoves C

/-- The selected reverse witness list for row `32103` replays in every endpoint-disjoint context. -/
theorem run?_row32103ReverseContextualMoves (C : State profile321)
    (hC : Disjoint C (row32103Finish ∪ row32103Start)) :
    run? (C ∪ row32103Finish) (row32103ReverseContextualMoves C) =
      some (C ∪ row32103Start) := by
  exact row32103ReverseContextualTree.selectMoves_run? ∅ ∅
    row32103ReverseContextualTree_valid (Finset.empty_subset C)
    (Finset.disjoint_empty_right C) hC

/-- Compile the selected reverse witnesses of row `32103` to an actual dependent move path. -/
def row32103ReverseContextualPath (C : State profile321)
    (hC : Disjoint C (row32103Finish ∪ row32103Start)) :
    MovePath (@AllModeMove profile321) (C ∪ row32103Finish) (C ∪ row32103Start) :=
  row32103ReverseContextualTree.toMovePath
    row32103ReverseContextualTree_valid hC

/-- The compiled reverse contextual path for row `32103` has exact length `3`. -/
@[simp] theorem row32103ReverseContextualPath_length (C : State profile321)
    (hC : Disjoint C (row32103Finish ∪ row32103Start)) :
    (row32103ReverseContextualPath C hC).length = 3 := by
  exact ContextualDecisionTree.toMovePath_length _ _ _

/-- Replayed guarded template 0 for the forward direction of row `32104`. -/
def row32104ForwardTemplate0 :
    ContextualPathTemplate profile321 row32104Start row32104Finish where
  moves := [⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1)⟩,
    ⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩]
  present := ∅
  absent := {maskTerm(profile321, 3, 3, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32104Start ∪ ∅ = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 3, 1)} := by
      unfold row32104Start
      decide
    have hfinish : row32104Finish ∪ ∅ = {maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32104Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 3, 1)} = some {maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 3, 1)} = some {maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, Option.bind_some]

/-- Replayed guarded template 1 for the forward direction of row `32104`. -/
def row32104ForwardTemplate1 :
    ContextualPathTemplate profile321 row32104Start row32104Finish where
  moves := [⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1)⟩]
  present := {maskTerm(profile321, 3, 3, 1)}
  absent := ∅
  support_eq := by decide
  replay := by
    have hstart : row32104Start ∪ {maskTerm(profile321, 3, 3, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1)} := by
      unfold row32104Start
      decide
    have hfinish : row32104Finish ∪ {maskTerm(profile321, 3, 3, 1)} = {maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32104Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, Option.bind_some]

/-- Total compact decision tree for the forward direction of row `32104`. -/
def row32104ForwardContextualTree :
    ContextualDecisionTree profile321 row32104Start row32104Finish 2 :=
  .branch maskTerm(profile321, 3, 3, 1)
    (.leaf row32104ForwardTemplate0 (by decide))
    (.leaf row32104ForwardTemplate1 (by decide))

/-- Kernel-checked full guard coverage for the forward tree of row `32104`. -/
theorem row32104ForwardContextualTree_valid :
    row32104ForwardContextualTree.Valid ∅ ∅ := by
  unfold row32104ForwardContextualTree
  unfold row32104ForwardTemplate0
  unfold row32104ForwardTemplate1
  simp only [ContextualDecisionTree.Valid]
  repeat' apply And.intro
  all_goals
    intro x hx
    aesop

/-- Executably select actual fixed witnesses for the forward direction of row `32104`. -/
def row32104ForwardContextualMoves (C : State profile321) : List (FixedMoveData profile321) :=
  row32104ForwardContextualTree.selectMoves C

/-- The selected forward witness list for row `32104` replays in every endpoint-disjoint context. -/
theorem run?_row32104ForwardContextualMoves (C : State profile321)
    (hC : Disjoint C (row32104Start ∪ row32104Finish)) :
    run? (C ∪ row32104Start) (row32104ForwardContextualMoves C) =
      some (C ∪ row32104Finish) := by
  exact row32104ForwardContextualTree.selectMoves_run? ∅ ∅
    row32104ForwardContextualTree_valid (Finset.empty_subset C)
    (Finset.disjoint_empty_right C) hC

/-- Compile the selected forward witnesses of row `32104` to an actual dependent move path. -/
def row32104ForwardContextualPath (C : State profile321)
    (hC : Disjoint C (row32104Start ∪ row32104Finish)) :
    MovePath (@AllModeMove profile321) (C ∪ row32104Start) (C ∪ row32104Finish) :=
  row32104ForwardContextualTree.toMovePath
    row32104ForwardContextualTree_valid hC

/-- The compiled forward contextual path for row `32104` has exact length `2`. -/
@[simp] theorem row32104ForwardContextualPath_length (C : State profile321)
    (hC : Disjoint C (row32104Start ∪ row32104Finish)) :
    (row32104ForwardContextualPath C hC).length = 2 := by
  exact ContextualDecisionTree.toMovePath_length _ _ _

/-- Replayed guarded template 0 for the reverse direction of row `32104`. -/
def row32104ReverseTemplate0 :
    ContextualPathTemplate profile321 row32104Finish row32104Start where
  moves := [⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1)⟩]
  present := ∅
  absent := {maskTerm(profile321, 3, 3, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32104Finish ∪ ∅ = {maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32104Finish
      decide
    have hfinish : row32104Start ∪ ∅ = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 3, 1)} := by
      unfold row32104Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, Option.bind_some]

/-- Replayed guarded template 1 for the reverse direction of row `32104`. -/
def row32104ReverseTemplate1 :
    ContextualPathTemplate profile321 row32104Finish row32104Start where
  moves := [⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1)⟩,
    ⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩]
  present := {maskTerm(profile321, 3, 3, 1)}
  absent := ∅
  support_eq := by decide
  replay := by
    have hstart : row32104Finish ∪ {maskTerm(profile321, 3, 3, 1)} = {maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32104Finish
      decide
    have hfinish : row32104Start ∪ {maskTerm(profile321, 3, 3, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1)} := by
      unfold row32104Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 2, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 2, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 2, 3, 1), maskTerm(profile321, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, Option.bind_some]

/-- Total compact decision tree for the reverse direction of row `32104`. -/
def row32104ReverseContextualTree :
    ContextualDecisionTree profile321 row32104Finish row32104Start 2 :=
  .branch maskTerm(profile321, 3, 3, 1)
    (.leaf row32104ReverseTemplate0 (by decide))
    (.leaf row32104ReverseTemplate1 (by decide))

/-- Kernel-checked full guard coverage for the reverse tree of row `32104`. -/
theorem row32104ReverseContextualTree_valid :
    row32104ReverseContextualTree.Valid ∅ ∅ := by
  unfold row32104ReverseContextualTree
  unfold row32104ReverseTemplate0
  unfold row32104ReverseTemplate1
  simp only [ContextualDecisionTree.Valid]
  repeat' apply And.intro
  all_goals
    intro x hx
    aesop

/-- Executably select actual fixed witnesses for the reverse direction of row `32104`. -/
def row32104ReverseContextualMoves (C : State profile321) : List (FixedMoveData profile321) :=
  row32104ReverseContextualTree.selectMoves C

/-- The selected reverse witness list for row `32104` replays in every endpoint-disjoint context. -/
theorem run?_row32104ReverseContextualMoves (C : State profile321)
    (hC : Disjoint C (row32104Finish ∪ row32104Start)) :
    run? (C ∪ row32104Finish) (row32104ReverseContextualMoves C) =
      some (C ∪ row32104Start) := by
  exact row32104ReverseContextualTree.selectMoves_run? ∅ ∅
    row32104ReverseContextualTree_valid (Finset.empty_subset C)
    (Finset.disjoint_empty_right C) hC

/-- Compile the selected reverse witnesses of row `32104` to an actual dependent move path. -/
def row32104ReverseContextualPath (C : State profile321)
    (hC : Disjoint C (row32104Finish ∪ row32104Start)) :
    MovePath (@AllModeMove profile321) (C ∪ row32104Finish) (C ∪ row32104Start) :=
  row32104ReverseContextualTree.toMovePath
    row32104ReverseContextualTree_valid hC

/-- The compiled reverse contextual path for row `32104` has exact length `2`. -/
@[simp] theorem row32104ReverseContextualPath_length (C : State profile321)
    (hC : Disjoint C (row32104Finish ∪ row32104Start)) :
    (row32104ReverseContextualPath C hC).length = 2 := by
  exact ContextualDecisionTree.toMovePath_length _ _ _

/-- Replayed guarded template 0 for the forward direction of row `32105`. -/
def row32105ForwardTemplate0 :
    ContextualPathTemplate profile321 row32105Start row32105Finish where
  moves := [⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 2, 1)⟩,
    ⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩]
  present := ∅
  absent := {maskTerm(profile321, 3, 3, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32105Start ∪ ∅ = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 3, 2, 1)} := by
      unfold row32105Start
      decide
    have hfinish : row32105Finish ∪ ∅ = {maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32105Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 2, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 3, 2, 1)} = some {maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 3, 1)} = some {maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, Option.bind_some]

/-- Replayed guarded template 1 for the forward direction of row `32105`. -/
def row32105ForwardTemplate1 :
    ContextualPathTemplate profile321 row32105Start row32105Finish where
  moves := [⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 2, 1)⟩]
  present := {maskTerm(profile321, 3, 3, 1)}
  absent := ∅
  support_eq := by decide
  replay := by
    have hstart : row32105Start ∪ {maskTerm(profile321, 3, 3, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1)} := by
      unfold row32105Start
      decide
    have hfinish : row32105Finish ∪ {maskTerm(profile321, 3, 3, 1)} = {maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32105Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 3, 3, 1) maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1) maskTerm(inversePermProfile .bac profile321, 3, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 2, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, Option.bind_some]

/-- Total compact decision tree for the forward direction of row `32105`. -/
def row32105ForwardContextualTree :
    ContextualDecisionTree profile321 row32105Start row32105Finish 2 :=
  .branch maskTerm(profile321, 3, 3, 1)
    (.leaf row32105ForwardTemplate0 (by decide))
    (.leaf row32105ForwardTemplate1 (by decide))

/-- Kernel-checked full guard coverage for the forward tree of row `32105`. -/
theorem row32105ForwardContextualTree_valid :
    row32105ForwardContextualTree.Valid ∅ ∅ := by
  unfold row32105ForwardContextualTree
  unfold row32105ForwardTemplate0
  unfold row32105ForwardTemplate1
  simp only [ContextualDecisionTree.Valid]
  repeat' apply And.intro
  all_goals
    intro x hx
    aesop

/-- Executably select actual fixed witnesses for the forward direction of row `32105`. -/
def row32105ForwardContextualMoves (C : State profile321) : List (FixedMoveData profile321) :=
  row32105ForwardContextualTree.selectMoves C

/-- The selected forward witness list for row `32105` replays in every endpoint-disjoint context. -/
theorem run?_row32105ForwardContextualMoves (C : State profile321)
    (hC : Disjoint C (row32105Start ∪ row32105Finish)) :
    run? (C ∪ row32105Start) (row32105ForwardContextualMoves C) =
      some (C ∪ row32105Finish) := by
  exact row32105ForwardContextualTree.selectMoves_run? ∅ ∅
    row32105ForwardContextualTree_valid (Finset.empty_subset C)
    (Finset.disjoint_empty_right C) hC

/-- Compile the selected forward witnesses of row `32105` to an actual dependent move path. -/
def row32105ForwardContextualPath (C : State profile321)
    (hC : Disjoint C (row32105Start ∪ row32105Finish)) :
    MovePath (@AllModeMove profile321) (C ∪ row32105Start) (C ∪ row32105Finish) :=
  row32105ForwardContextualTree.toMovePath
    row32105ForwardContextualTree_valid hC

/-- The compiled forward contextual path for row `32105` has exact length `2`. -/
@[simp] theorem row32105ForwardContextualPath_length (C : State profile321)
    (hC : Disjoint C (row32105Start ∪ row32105Finish)) :
    (row32105ForwardContextualPath C hC).length = 2 := by
  exact ContextualDecisionTree.toMovePath_length _ _ _

/-- Replayed guarded template 0 for the reverse direction of row `32105`. -/
def row32105ReverseTemplate0 :
    ContextualPathTemplate profile321 row32105Finish row32105Start where
  moves := [⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 3, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1)⟩]
  present := ∅
  absent := {maskTerm(profile321, 3, 3, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32105Finish ∪ ∅ = {maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32105Finish
      decide
    have hfinish : row32105Start ∪ ∅ = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 3, 2, 1)} := by
      unfold row32105Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 3, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 3, 2, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, Option.bind_some]

/-- Replayed guarded template 1 for the reverse direction of row `32105`. -/
def row32105ReverseTemplate1 :
    ContextualPathTemplate profile321 row32105Finish row32105Start where
  moves := [⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 3, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1)⟩,
    ⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩]
  present := {maskTerm(profile321, 3, 3, 1)}
  absent := ∅
  support_eq := by decide
  replay := by
    have hstart : row32105Finish ∪ {maskTerm(profile321, 3, 3, 1)} = {maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32105Finish
      decide
    have hfinish : row32105Start ∪ {maskTerm(profile321, 3, 3, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1)} := by
      unfold row32105Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 3, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 2, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 1, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 3, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 4, 3, 1) maskTerm(inversePermProfile .abc profile321, 7, 3, 1) maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 4, 3, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, Option.bind_some]

/-- Total compact decision tree for the reverse direction of row `32105`. -/
def row32105ReverseContextualTree :
    ContextualDecisionTree profile321 row32105Finish row32105Start 2 :=
  .branch maskTerm(profile321, 3, 3, 1)
    (.leaf row32105ReverseTemplate0 (by decide))
    (.leaf row32105ReverseTemplate1 (by decide))

/-- Kernel-checked full guard coverage for the reverse tree of row `32105`. -/
theorem row32105ReverseContextualTree_valid :
    row32105ReverseContextualTree.Valid ∅ ∅ := by
  unfold row32105ReverseContextualTree
  unfold row32105ReverseTemplate0
  unfold row32105ReverseTemplate1
  simp only [ContextualDecisionTree.Valid]
  repeat' apply And.intro
  all_goals
    intro x hx
    aesop

/-- Executably select actual fixed witnesses for the reverse direction of row `32105`. -/
def row32105ReverseContextualMoves (C : State profile321) : List (FixedMoveData profile321) :=
  row32105ReverseContextualTree.selectMoves C

/-- The selected reverse witness list for row `32105` replays in every endpoint-disjoint context. -/
theorem run?_row32105ReverseContextualMoves (C : State profile321)
    (hC : Disjoint C (row32105Finish ∪ row32105Start)) :
    run? (C ∪ row32105Finish) (row32105ReverseContextualMoves C) =
      some (C ∪ row32105Start) := by
  exact row32105ReverseContextualTree.selectMoves_run? ∅ ∅
    row32105ReverseContextualTree_valid (Finset.empty_subset C)
    (Finset.disjoint_empty_right C) hC

/-- Compile the selected reverse witnesses of row `32105` to an actual dependent move path. -/
def row32105ReverseContextualPath (C : State profile321)
    (hC : Disjoint C (row32105Finish ∪ row32105Start)) :
    MovePath (@AllModeMove profile321) (C ∪ row32105Finish) (C ∪ row32105Start) :=
  row32105ReverseContextualTree.toMovePath
    row32105ReverseContextualTree_valid hC

/-- The compiled reverse contextual path for row `32105` has exact length `2`. -/
@[simp] theorem row32105ReverseContextualPath_length (C : State profile321)
    (hC : Disjoint C (row32105Finish ∪ row32105Start)) :
    (row32105ReverseContextualPath C hC).length = 2 := by
  exact ContextualDecisionTree.toMovePath_length _ _ _

/-- Replayed guarded template 0 for the forward direction of row `32106`. -/
def row32106ForwardTemplate0 :
    ContextualPathTemplate profile321 row32106Start row32106Finish where
  moves := [⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 1, 1, 1) maskTerm(inversePermProfile .abc profile321, 2, 1, 1) maskTerm(inversePermProfile .abc profile321, 3, 1, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 4, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 7, 1)⟩]
  present := ∅
  absent := {maskTerm(profile321, 3, 1, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32106Start ∪ ∅ = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 4, 3, 1)} := by
      unfold row32106Start
      decide
    have hfinish : row32106Finish ∪ ∅ = {maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32106Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 1, 1, 1) maskTerm(inversePermProfile .abc profile321, 2, 1, 1) maskTerm(inversePermProfile .abc profile321, 3, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 4, 3, 1)} = some {maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 4, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 4, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 7, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 4, 3, 1)} = some {maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, Option.bind_some]

/-- Replayed guarded template 1 for the forward direction of row `32106`. -/
def row32106ForwardTemplate1 :
    ContextualPathTemplate profile321 row32106Start row32106Finish where
  moves := [⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 4, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 7, 1)⟩,
    ⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 1, 1, 1) maskTerm(inversePermProfile .abc profile321, 2, 1, 1) maskTerm(inversePermProfile .abc profile321, 3, 1, 1)⟩]
  present := {maskTerm(profile321, 3, 1, 1)}
  absent := ∅
  support_eq := by decide
  replay := by
    have hstart : row32106Start ∪ {maskTerm(profile321, 3, 1, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 4, 3, 1)} := by
      unfold row32106Start
      decide
    have hfinish : row32106Finish ∪ {maskTerm(profile321, 3, 1, 1)} = {maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32106Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 1, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 4, 1) maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 7, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 4, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile321, 1, 1, 1) maskTerm(inversePermProfile .abc profile321, 2, 1, 1) maskTerm(inversePermProfile .abc profile321, 3, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, Option.bind_some]

/-- Total compact decision tree for the forward direction of row `32106`. -/
def row32106ForwardContextualTree :
    ContextualDecisionTree profile321 row32106Start row32106Finish 2 :=
  .branch maskTerm(profile321, 3, 1, 1)
    (.leaf row32106ForwardTemplate0 (by decide))
    (.leaf row32106ForwardTemplate1 (by decide))

/-- Kernel-checked full guard coverage for the forward tree of row `32106`. -/
theorem row32106ForwardContextualTree_valid :
    row32106ForwardContextualTree.Valid ∅ ∅ := by
  unfold row32106ForwardContextualTree
  unfold row32106ForwardTemplate0
  unfold row32106ForwardTemplate1
  simp only [ContextualDecisionTree.Valid]
  repeat' apply And.intro
  all_goals
    intro x hx
    aesop

/-- Executably select actual fixed witnesses for the forward direction of row `32106`. -/
def row32106ForwardContextualMoves (C : State profile321) : List (FixedMoveData profile321) :=
  row32106ForwardContextualTree.selectMoves C

/-- The selected forward witness list for row `32106` replays in every endpoint-disjoint context. -/
theorem run?_row32106ForwardContextualMoves (C : State profile321)
    (hC : Disjoint C (row32106Start ∪ row32106Finish)) :
    run? (C ∪ row32106Start) (row32106ForwardContextualMoves C) =
      some (C ∪ row32106Finish) := by
  exact row32106ForwardContextualTree.selectMoves_run? ∅ ∅
    row32106ForwardContextualTree_valid (Finset.empty_subset C)
    (Finset.disjoint_empty_right C) hC

/-- Compile the selected forward witnesses of row `32106` to an actual dependent move path. -/
def row32106ForwardContextualPath (C : State profile321)
    (hC : Disjoint C (row32106Start ∪ row32106Finish)) :
    MovePath (@AllModeMove profile321) (C ∪ row32106Start) (C ∪ row32106Finish) :=
  row32106ForwardContextualTree.toMovePath
    row32106ForwardContextualTree_valid hC

/-- The compiled forward contextual path for row `32106` has exact length `2`. -/
@[simp] theorem row32106ForwardContextualPath_length (C : State profile321)
    (hC : Disjoint C (row32106Start ∪ row32106Finish)) :
    (row32106ForwardContextualPath C hC).length = 2 := by
  exact ContextualDecisionTree.toMovePath_length _ _ _

/-- Replayed guarded template 0 for the reverse direction of row `32106`. -/
def row32106ReverseTemplate0 :
    ContextualPathTemplate profile321 row32106Finish row32106Start where
  moves := [⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 7, 1) maskTerm(inversePermProfile .bac profile321, 1, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 4, 1)⟩,
    ⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 2, 1, 1) maskTerm(inversePermProfile .abc profile321, 3, 1, 1) maskTerm(inversePermProfile .abc profile321, 1, 1, 1)⟩]
  present := ∅
  absent := {maskTerm(profile321, 3, 1, 1)}
  support_eq := by decide
  replay := by
    have hstart : row32106Finish ∪ ∅ = {maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32106Finish
      decide
    have hfinish : row32106Start ∪ ∅ = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 4, 3, 1)} := by
      unfold row32106Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 7, 1) maskTerm(inversePermProfile .bac profile321, 1, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 4, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 4, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 2, 1, 1) maskTerm(inversePermProfile .abc profile321, 3, 1, 1) maskTerm(inversePermProfile .abc profile321, 1, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 4, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 4, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, Option.bind_some]

/-- Replayed guarded template 1 for the reverse direction of row `32106`. -/
def row32106ReverseTemplate1 :
    ContextualPathTemplate profile321 row32106Finish row32106Start where
  moves := [⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 2, 1, 1) maskTerm(inversePermProfile .abc profile321, 3, 1, 1) maskTerm(inversePermProfile .abc profile321, 1, 1, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 7, 1) maskTerm(inversePermProfile .bac profile321, 1, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 4, 1)⟩]
  present := {maskTerm(profile321, 3, 1, 1)}
  absent := ∅
  support_eq := by decide
  replay := by
    have hstart : row32106Finish ∪ {maskTerm(profile321, 3, 1, 1)} = {maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 7, 3, 1)} := by
      unfold row32106Finish
      decide
    have hfinish : row32106Start ∪ {maskTerm(profile321, 3, 1, 1)} = {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 4, 3, 1)} := by
      unfold row32106Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile321, 2, 1, 1) maskTerm(inversePermProfile .abc profile321, 3, 1, 1) maskTerm(inversePermProfile .abc profile321, 1, 1, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 2, 1, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 7, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile321, 2, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 7, 1) maskTerm(inversePermProfile .bac profile321, 1, 3, 1) maskTerm(inversePermProfile .bac profile321, 3, 4, 1)⟩ : FixedMoveData profile321).step? {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 3, 2, 1), maskTerm(profile321, 7, 3, 1)} = some {maskTerm(profile321, 1, 1, 1), maskTerm(profile321, 3, 1, 1), maskTerm(profile321, 4, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, Option.bind_some]

/-- Total compact decision tree for the reverse direction of row `32106`. -/
def row32106ReverseContextualTree :
    ContextualDecisionTree profile321 row32106Finish row32106Start 2 :=
  .branch maskTerm(profile321, 3, 1, 1)
    (.leaf row32106ReverseTemplate0 (by decide))
    (.leaf row32106ReverseTemplate1 (by decide))

/-- Kernel-checked full guard coverage for the reverse tree of row `32106`. -/
theorem row32106ReverseContextualTree_valid :
    row32106ReverseContextualTree.Valid ∅ ∅ := by
  unfold row32106ReverseContextualTree
  unfold row32106ReverseTemplate0
  unfold row32106ReverseTemplate1
  simp only [ContextualDecisionTree.Valid]
  repeat' apply And.intro
  all_goals
    intro x hx
    aesop

/-- Executably select actual fixed witnesses for the reverse direction of row `32106`. -/
def row32106ReverseContextualMoves (C : State profile321) : List (FixedMoveData profile321) :=
  row32106ReverseContextualTree.selectMoves C

/-- The selected reverse witness list for row `32106` replays in every endpoint-disjoint context. -/
theorem run?_row32106ReverseContextualMoves (C : State profile321)
    (hC : Disjoint C (row32106Finish ∪ row32106Start)) :
    run? (C ∪ row32106Finish) (row32106ReverseContextualMoves C) =
      some (C ∪ row32106Start) := by
  exact row32106ReverseContextualTree.selectMoves_run? ∅ ∅
    row32106ReverseContextualTree_valid (Finset.empty_subset C)
    (Finset.disjoint_empty_right C) hC

/-- Compile the selected reverse witnesses of row `32106` to an actual dependent move path. -/
def row32106ReverseContextualPath (C : State profile321)
    (hC : Disjoint C (row32106Finish ∪ row32106Start)) :
    MovePath (@AllModeMove profile321) (C ∪ row32106Finish) (C ∪ row32106Start) :=
  row32106ReverseContextualTree.toMovePath
    row32106ReverseContextualTree_valid hC

/-- The compiled reverse contextual path for row `32106` has exact length `2`. -/
@[simp] theorem row32106ReverseContextualPath_length (C : State profile321)
    (hC : Disjoint C (row32106Finish ∪ row32106Start)) :
    (row32106ReverseContextualPath C hC).length = 2 := by
  exact ContextualDecisionTree.toMovePath_length _ _ _

end BilinearComplexity.NormalizedBinaryContextualCertificates
