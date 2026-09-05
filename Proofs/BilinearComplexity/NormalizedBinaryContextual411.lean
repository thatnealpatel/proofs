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

private abbrev stateDecidableEq411 (q : Profile) : DecidableEq (State q) :=
  @Finset.decidableEq (Carrier q) inferInstance

local instance instDecidableEqState411 (q : Profile) : DecidableEq (State q) :=
  stateDecidableEq411 q

local macro "maskTerm(" p:term "," a:num "," b:num "," c:num ")" : term =>
  `(carrierOfMasks $p $a $b $c (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide))

/-- Replayed guarded template 0 for the forward direction of row `41101`. -/
def row41101ForwardTemplate0 :
    ContextualPathTemplate profile411 row41101Start row41101Finish where
  moves := [⟨.abc, .split maskTerm(inversePermProfile .abc profile411, 2, 1, 1) maskTerm(inversePermProfile .abc profile411, 4, 1, 1) maskTerm(inversePermProfile .abc profile411, 6, 1, 1)⟩,
    ⟨.abc, .split maskTerm(inversePermProfile .abc profile411, 1, 1, 1) maskTerm(inversePermProfile .abc profile411, 8, 1, 1) maskTerm(inversePermProfile .abc profile411, 9, 1, 1)⟩,
    ⟨.abc, .reduction maskTerm(inversePermProfile .abc profile411, 6, 1, 1) maskTerm(inversePermProfile .abc profile411, 9, 1, 1) maskTerm(inversePermProfile .abc profile411, 15, 1, 1)⟩]
  present := ∅
  absent := {maskTerm(profile411, 6, 1, 1), maskTerm(profile411, 9, 1, 1)}
  support_eq := by decide
  replay := by
    have hstart : row41101Start ∪ ∅ = {maskTerm(profile411, 1, 1, 1), maskTerm(profile411, 2, 1, 1)} := by
      unfold row41101Start
      decide
    have hfinish : row41101Finish ∪ ∅ = {maskTerm(profile411, 4, 1, 1), maskTerm(profile411, 8, 1, 1), maskTerm(profile411, 15, 1, 1)} := by
      unfold row41101Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile411, 2, 1, 1) maskTerm(inversePermProfile .abc profile411, 4, 1, 1) maskTerm(inversePermProfile .abc profile411, 6, 1, 1)⟩ : FixedMoveData profile411).step? {maskTerm(profile411, 1, 1, 1), maskTerm(profile411, 2, 1, 1)} = some {maskTerm(profile411, 1, 1, 1), maskTerm(profile411, 4, 1, 1), maskTerm(profile411, 6, 1, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile411, 1, 1, 1) maskTerm(inversePermProfile .abc profile411, 8, 1, 1) maskTerm(inversePermProfile .abc profile411, 9, 1, 1)⟩ : FixedMoveData profile411).step? {maskTerm(profile411, 1, 1, 1), maskTerm(profile411, 4, 1, 1), maskTerm(profile411, 6, 1, 1)} = some {maskTerm(profile411, 4, 1, 1), maskTerm(profile411, 6, 1, 1), maskTerm(profile411, 8, 1, 1), maskTerm(profile411, 9, 1, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile411, 6, 1, 1) maskTerm(inversePermProfile .abc profile411, 9, 1, 1) maskTerm(inversePermProfile .abc profile411, 15, 1, 1)⟩ : FixedMoveData profile411).step? {maskTerm(profile411, 4, 1, 1), maskTerm(profile411, 6, 1, 1), maskTerm(profile411, 8, 1, 1), maskTerm(profile411, 9, 1, 1)} = some {maskTerm(profile411, 4, 1, 1), maskTerm(profile411, 8, 1, 1), maskTerm(profile411, 15, 1, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 1 for the forward direction of row `41101`. -/
def row41101ForwardTemplate1 :
    ContextualPathTemplate profile411 row41101Start row41101Finish where
  moves := [⟨.abc, .split maskTerm(inversePermProfile .abc profile411, 2, 1, 1) maskTerm(inversePermProfile .abc profile411, 4, 1, 1) maskTerm(inversePermProfile .abc profile411, 6, 1, 1)⟩,
    ⟨.abc, .reduction maskTerm(inversePermProfile .abc profile411, 1, 1, 1) maskTerm(inversePermProfile .abc profile411, 9, 1, 1) maskTerm(inversePermProfile .abc profile411, 8, 1, 1)⟩,
    ⟨.abc, .split maskTerm(inversePermProfile .abc profile411, 6, 1, 1) maskTerm(inversePermProfile .abc profile411, 9, 1, 1) maskTerm(inversePermProfile .abc profile411, 15, 1, 1)⟩]
  present := {maskTerm(profile411, 9, 1, 1)}
  absent := {maskTerm(profile411, 6, 1, 1)}
  support_eq := by decide
  replay := by
    have hstart : row41101Start ∪ {maskTerm(profile411, 9, 1, 1)} = {maskTerm(profile411, 1, 1, 1), maskTerm(profile411, 2, 1, 1), maskTerm(profile411, 9, 1, 1)} := by
      unfold row41101Start
      decide
    have hfinish : row41101Finish ∪ {maskTerm(profile411, 9, 1, 1)} = {maskTerm(profile411, 4, 1, 1), maskTerm(profile411, 8, 1, 1), maskTerm(profile411, 9, 1, 1), maskTerm(profile411, 15, 1, 1)} := by
      unfold row41101Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile411, 2, 1, 1) maskTerm(inversePermProfile .abc profile411, 4, 1, 1) maskTerm(inversePermProfile .abc profile411, 6, 1, 1)⟩ : FixedMoveData profile411).step? {maskTerm(profile411, 1, 1, 1), maskTerm(profile411, 2, 1, 1), maskTerm(profile411, 9, 1, 1)} = some {maskTerm(profile411, 1, 1, 1), maskTerm(profile411, 4, 1, 1), maskTerm(profile411, 6, 1, 1), maskTerm(profile411, 9, 1, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile411, 1, 1, 1) maskTerm(inversePermProfile .abc profile411, 9, 1, 1) maskTerm(inversePermProfile .abc profile411, 8, 1, 1)⟩ : FixedMoveData profile411).step? {maskTerm(profile411, 1, 1, 1), maskTerm(profile411, 4, 1, 1), maskTerm(profile411, 6, 1, 1), maskTerm(profile411, 9, 1, 1)} = some {maskTerm(profile411, 4, 1, 1), maskTerm(profile411, 6, 1, 1), maskTerm(profile411, 8, 1, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile411, 6, 1, 1) maskTerm(inversePermProfile .abc profile411, 9, 1, 1) maskTerm(inversePermProfile .abc profile411, 15, 1, 1)⟩ : FixedMoveData profile411).step? {maskTerm(profile411, 4, 1, 1), maskTerm(profile411, 6, 1, 1), maskTerm(profile411, 8, 1, 1)} = some {maskTerm(profile411, 4, 1, 1), maskTerm(profile411, 8, 1, 1), maskTerm(profile411, 9, 1, 1), maskTerm(profile411, 15, 1, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 2 for the forward direction of row `41101`. -/
def row41101ForwardTemplate2 :
    ContextualPathTemplate profile411 row41101Start row41101Finish where
  moves := [⟨.abc, .reduction maskTerm(inversePermProfile .abc profile411, 2, 1, 1) maskTerm(inversePermProfile .abc profile411, 6, 1, 1) maskTerm(inversePermProfile .abc profile411, 4, 1, 1)⟩,
    ⟨.abc, .split maskTerm(inversePermProfile .abc profile411, 1, 1, 1) maskTerm(inversePermProfile .abc profile411, 8, 1, 1) maskTerm(inversePermProfile .abc profile411, 9, 1, 1)⟩,
    ⟨.abc, .split maskTerm(inversePermProfile .abc profile411, 9, 1, 1) maskTerm(inversePermProfile .abc profile411, 6, 1, 1) maskTerm(inversePermProfile .abc profile411, 15, 1, 1)⟩]
  present := {maskTerm(profile411, 6, 1, 1)}
  absent := {maskTerm(profile411, 9, 1, 1)}
  support_eq := by decide
  replay := by
    have hstart : row41101Start ∪ {maskTerm(profile411, 6, 1, 1)} = {maskTerm(profile411, 1, 1, 1), maskTerm(profile411, 2, 1, 1), maskTerm(profile411, 6, 1, 1)} := by
      unfold row41101Start
      decide
    have hfinish : row41101Finish ∪ {maskTerm(profile411, 6, 1, 1)} = {maskTerm(profile411, 4, 1, 1), maskTerm(profile411, 6, 1, 1), maskTerm(profile411, 8, 1, 1), maskTerm(profile411, 15, 1, 1)} := by
      unfold row41101Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile411, 2, 1, 1) maskTerm(inversePermProfile .abc profile411, 6, 1, 1) maskTerm(inversePermProfile .abc profile411, 4, 1, 1)⟩ : FixedMoveData profile411).step? {maskTerm(profile411, 1, 1, 1), maskTerm(profile411, 2, 1, 1), maskTerm(profile411, 6, 1, 1)} = some {maskTerm(profile411, 1, 1, 1), maskTerm(profile411, 4, 1, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile411, 1, 1, 1) maskTerm(inversePermProfile .abc profile411, 8, 1, 1) maskTerm(inversePermProfile .abc profile411, 9, 1, 1)⟩ : FixedMoveData profile411).step? {maskTerm(profile411, 1, 1, 1), maskTerm(profile411, 4, 1, 1)} = some {maskTerm(profile411, 4, 1, 1), maskTerm(profile411, 8, 1, 1), maskTerm(profile411, 9, 1, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile411, 9, 1, 1) maskTerm(inversePermProfile .abc profile411, 6, 1, 1) maskTerm(inversePermProfile .abc profile411, 15, 1, 1)⟩ : FixedMoveData profile411).step? {maskTerm(profile411, 4, 1, 1), maskTerm(profile411, 8, 1, 1), maskTerm(profile411, 9, 1, 1)} = some {maskTerm(profile411, 4, 1, 1), maskTerm(profile411, 6, 1, 1), maskTerm(profile411, 8, 1, 1), maskTerm(profile411, 15, 1, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 3 for the forward direction of row `41101`. -/
def row41101ForwardTemplate3 :
    ContextualPathTemplate profile411 row41101Start row41101Finish where
  moves := [⟨.abc, .reduction maskTerm(inversePermProfile .abc profile411, 2, 1, 1) maskTerm(inversePermProfile .abc profile411, 6, 1, 1) maskTerm(inversePermProfile .abc profile411, 4, 1, 1)⟩,
    ⟨.abc, .split maskTerm(inversePermProfile .abc profile411, 9, 1, 1) maskTerm(inversePermProfile .abc profile411, 6, 1, 1) maskTerm(inversePermProfile .abc profile411, 15, 1, 1)⟩,
    ⟨.abc, .split maskTerm(inversePermProfile .abc profile411, 1, 1, 1) maskTerm(inversePermProfile .abc profile411, 8, 1, 1) maskTerm(inversePermProfile .abc profile411, 9, 1, 1)⟩]
  present := {maskTerm(profile411, 6, 1, 1), maskTerm(profile411, 9, 1, 1)}
  absent := ∅
  support_eq := by decide
  replay := by
    have hstart : row41101Start ∪ {maskTerm(profile411, 6, 1, 1), maskTerm(profile411, 9, 1, 1)} = {maskTerm(profile411, 1, 1, 1), maskTerm(profile411, 2, 1, 1), maskTerm(profile411, 6, 1, 1), maskTerm(profile411, 9, 1, 1)} := by
      unfold row41101Start
      decide
    have hfinish : row41101Finish ∪ {maskTerm(profile411, 6, 1, 1), maskTerm(profile411, 9, 1, 1)} = {maskTerm(profile411, 4, 1, 1), maskTerm(profile411, 6, 1, 1), maskTerm(profile411, 8, 1, 1), maskTerm(profile411, 9, 1, 1), maskTerm(profile411, 15, 1, 1)} := by
      unfold row41101Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile411, 2, 1, 1) maskTerm(inversePermProfile .abc profile411, 6, 1, 1) maskTerm(inversePermProfile .abc profile411, 4, 1, 1)⟩ : FixedMoveData profile411).step? {maskTerm(profile411, 1, 1, 1), maskTerm(profile411, 2, 1, 1), maskTerm(profile411, 6, 1, 1), maskTerm(profile411, 9, 1, 1)} = some {maskTerm(profile411, 1, 1, 1), maskTerm(profile411, 4, 1, 1), maskTerm(profile411, 9, 1, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile411, 9, 1, 1) maskTerm(inversePermProfile .abc profile411, 6, 1, 1) maskTerm(inversePermProfile .abc profile411, 15, 1, 1)⟩ : FixedMoveData profile411).step? {maskTerm(profile411, 1, 1, 1), maskTerm(profile411, 4, 1, 1), maskTerm(profile411, 9, 1, 1)} = some {maskTerm(profile411, 1, 1, 1), maskTerm(profile411, 4, 1, 1), maskTerm(profile411, 6, 1, 1), maskTerm(profile411, 15, 1, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile411, 1, 1, 1) maskTerm(inversePermProfile .abc profile411, 8, 1, 1) maskTerm(inversePermProfile .abc profile411, 9, 1, 1)⟩ : FixedMoveData profile411).step? {maskTerm(profile411, 1, 1, 1), maskTerm(profile411, 4, 1, 1), maskTerm(profile411, 6, 1, 1), maskTerm(profile411, 15, 1, 1)} = some {maskTerm(profile411, 4, 1, 1), maskTerm(profile411, 6, 1, 1), maskTerm(profile411, 8, 1, 1), maskTerm(profile411, 9, 1, 1), maskTerm(profile411, 15, 1, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Total compact decision tree for the forward direction of row `41101`. -/
def row41101ForwardContextualTree :
    ContextualDecisionTree profile411 row41101Start row41101Finish 3 :=
  .branch maskTerm(profile411, 3, 1, 1)
    (.branch maskTerm(profile411, 5, 1, 1)
      (.branch maskTerm(profile411, 6, 1, 1)
        (.branch maskTerm(profile411, 9, 1, 1)
          (.leaf row41101ForwardTemplate0 (by decide))
          (.leaf row41101ForwardTemplate1 (by decide)))
        (.branch maskTerm(profile411, 9, 1, 1)
          (.leaf row41101ForwardTemplate2 (by decide))
          (.leaf row41101ForwardTemplate3 (by decide))))
      (.branch maskTerm(profile411, 6, 1, 1)
        (.branch maskTerm(profile411, 9, 1, 1)
          (.leaf row41101ForwardTemplate0 (by decide))
          (.leaf row41101ForwardTemplate1 (by decide)))
        (.branch maskTerm(profile411, 9, 1, 1)
          (.leaf row41101ForwardTemplate2 (by decide))
          (.leaf row41101ForwardTemplate3 (by decide)))))
    (.branch maskTerm(profile411, 5, 1, 1)
      (.branch maskTerm(profile411, 6, 1, 1)
        (.branch maskTerm(profile411, 9, 1, 1)
          (.leaf row41101ForwardTemplate0 (by decide))
          (.leaf row41101ForwardTemplate1 (by decide)))
        (.branch maskTerm(profile411, 9, 1, 1)
          (.leaf row41101ForwardTemplate2 (by decide))
          (.leaf row41101ForwardTemplate3 (by decide))))
      (.branch maskTerm(profile411, 6, 1, 1)
        (.branch maskTerm(profile411, 9, 1, 1)
          (.leaf row41101ForwardTemplate0 (by decide))
          (.leaf row41101ForwardTemplate1 (by decide)))
        (.branch maskTerm(profile411, 9, 1, 1)
          (.leaf row41101ForwardTemplate2 (by decide))
          (.leaf row41101ForwardTemplate3 (by decide)))))

/-- Kernel-checked full guard coverage for the forward tree of row `41101`. -/
theorem row41101ForwardContextualTree_valid :
    row41101ForwardContextualTree.Valid ∅ ∅ := by
  unfold row41101ForwardContextualTree
  unfold row41101ForwardTemplate0
  unfold row41101ForwardTemplate1
  unfold row41101ForwardTemplate2
  unfold row41101ForwardTemplate3
  simp only [ContextualDecisionTree.Valid]
  repeat' apply And.intro
  all_goals
    intro x hx
    aesop

/-- Executably select actual fixed witnesses for the forward direction of row `41101`. -/
def row41101ForwardContextualMoves (C : State profile411) : List (FixedMoveData profile411) :=
  row41101ForwardContextualTree.selectMoves C

/-- The selected forward witness list for row `41101` replays in every endpoint-disjoint context. -/
theorem run?_row41101ForwardContextualMoves (C : State profile411)
    (hC : Disjoint C (row41101Start ∪ row41101Finish)) :
    run? (C ∪ row41101Start) (row41101ForwardContextualMoves C) =
      some (C ∪ row41101Finish) := by
  exact row41101ForwardContextualTree.selectMoves_run? ∅ ∅
    row41101ForwardContextualTree_valid (Finset.empty_subset C)
    (Finset.disjoint_empty_right C) hC

/-- Compile the selected forward witnesses of row `41101` to an actual dependent move path. -/
def row41101ForwardContextualPath (C : State profile411)
    (hC : Disjoint C (row41101Start ∪ row41101Finish)) :
    MovePath (@AllModeMove profile411) (C ∪ row41101Start) (C ∪ row41101Finish) :=
  row41101ForwardContextualTree.toMovePath
    row41101ForwardContextualTree_valid hC

/-- The compiled forward contextual path for row `41101` has exact length `3`. -/
@[simp] theorem row41101ForwardContextualPath_length (C : State profile411)
    (hC : Disjoint C (row41101Start ∪ row41101Finish)) :
    (row41101ForwardContextualPath C hC).length = 3 := by
  exact ContextualDecisionTree.toMovePath_length _ _ _

/-- Replayed guarded template 0 for the reverse direction of row `41101`. -/
def row41101ReverseTemplate0 :
    ContextualPathTemplate profile411 row41101Finish row41101Start where
  moves := [⟨.abc, .split maskTerm(inversePermProfile .abc profile411, 4, 1, 1) maskTerm(inversePermProfile .abc profile411, 2, 1, 1) maskTerm(inversePermProfile .abc profile411, 6, 1, 1)⟩,
    ⟨.abc, .reduction maskTerm(inversePermProfile .abc profile411, 6, 1, 1) maskTerm(inversePermProfile .abc profile411, 15, 1, 1) maskTerm(inversePermProfile .abc profile411, 9, 1, 1)⟩,
    ⟨.abc, .reduction maskTerm(inversePermProfile .abc profile411, 8, 1, 1) maskTerm(inversePermProfile .abc profile411, 9, 1, 1) maskTerm(inversePermProfile .abc profile411, 1, 1, 1)⟩]
  present := ∅
  absent := {maskTerm(profile411, 6, 1, 1), maskTerm(profile411, 9, 1, 1)}
  support_eq := by decide
  replay := by
    have hstart : row41101Finish ∪ ∅ = {maskTerm(profile411, 4, 1, 1), maskTerm(profile411, 8, 1, 1), maskTerm(profile411, 15, 1, 1)} := by
      unfold row41101Finish
      decide
    have hfinish : row41101Start ∪ ∅ = {maskTerm(profile411, 1, 1, 1), maskTerm(profile411, 2, 1, 1)} := by
      unfold row41101Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile411, 4, 1, 1) maskTerm(inversePermProfile .abc profile411, 2, 1, 1) maskTerm(inversePermProfile .abc profile411, 6, 1, 1)⟩ : FixedMoveData profile411).step? {maskTerm(profile411, 4, 1, 1), maskTerm(profile411, 8, 1, 1), maskTerm(profile411, 15, 1, 1)} = some {maskTerm(profile411, 2, 1, 1), maskTerm(profile411, 6, 1, 1), maskTerm(profile411, 8, 1, 1), maskTerm(profile411, 15, 1, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile411, 6, 1, 1) maskTerm(inversePermProfile .abc profile411, 15, 1, 1) maskTerm(inversePermProfile .abc profile411, 9, 1, 1)⟩ : FixedMoveData profile411).step? {maskTerm(profile411, 2, 1, 1), maskTerm(profile411, 6, 1, 1), maskTerm(profile411, 8, 1, 1), maskTerm(profile411, 15, 1, 1)} = some {maskTerm(profile411, 2, 1, 1), maskTerm(profile411, 8, 1, 1), maskTerm(profile411, 9, 1, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile411, 8, 1, 1) maskTerm(inversePermProfile .abc profile411, 9, 1, 1) maskTerm(inversePermProfile .abc profile411, 1, 1, 1)⟩ : FixedMoveData profile411).step? {maskTerm(profile411, 2, 1, 1), maskTerm(profile411, 8, 1, 1), maskTerm(profile411, 9, 1, 1)} = some {maskTerm(profile411, 1, 1, 1), maskTerm(profile411, 2, 1, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 1 for the reverse direction of row `41101`. -/
def row41101ReverseTemplate1 :
    ContextualPathTemplate profile411 row41101Finish row41101Start where
  moves := [⟨.abc, .split maskTerm(inversePermProfile .abc profile411, 4, 1, 1) maskTerm(inversePermProfile .abc profile411, 2, 1, 1) maskTerm(inversePermProfile .abc profile411, 6, 1, 1)⟩,
    ⟨.abc, .reduction maskTerm(inversePermProfile .abc profile411, 8, 1, 1) maskTerm(inversePermProfile .abc profile411, 9, 1, 1) maskTerm(inversePermProfile .abc profile411, 1, 1, 1)⟩,
    ⟨.abc, .reduction maskTerm(inversePermProfile .abc profile411, 6, 1, 1) maskTerm(inversePermProfile .abc profile411, 15, 1, 1) maskTerm(inversePermProfile .abc profile411, 9, 1, 1)⟩]
  present := {maskTerm(profile411, 9, 1, 1)}
  absent := {maskTerm(profile411, 6, 1, 1)}
  support_eq := by decide
  replay := by
    have hstart : row41101Finish ∪ {maskTerm(profile411, 9, 1, 1)} = {maskTerm(profile411, 4, 1, 1), maskTerm(profile411, 8, 1, 1), maskTerm(profile411, 9, 1, 1), maskTerm(profile411, 15, 1, 1)} := by
      unfold row41101Finish
      decide
    have hfinish : row41101Start ∪ {maskTerm(profile411, 9, 1, 1)} = {maskTerm(profile411, 1, 1, 1), maskTerm(profile411, 2, 1, 1), maskTerm(profile411, 9, 1, 1)} := by
      unfold row41101Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile411, 4, 1, 1) maskTerm(inversePermProfile .abc profile411, 2, 1, 1) maskTerm(inversePermProfile .abc profile411, 6, 1, 1)⟩ : FixedMoveData profile411).step? {maskTerm(profile411, 4, 1, 1), maskTerm(profile411, 8, 1, 1), maskTerm(profile411, 9, 1, 1), maskTerm(profile411, 15, 1, 1)} = some {maskTerm(profile411, 2, 1, 1), maskTerm(profile411, 6, 1, 1), maskTerm(profile411, 8, 1, 1), maskTerm(profile411, 9, 1, 1), maskTerm(profile411, 15, 1, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile411, 8, 1, 1) maskTerm(inversePermProfile .abc profile411, 9, 1, 1) maskTerm(inversePermProfile .abc profile411, 1, 1, 1)⟩ : FixedMoveData profile411).step? {maskTerm(profile411, 2, 1, 1), maskTerm(profile411, 6, 1, 1), maskTerm(profile411, 8, 1, 1), maskTerm(profile411, 9, 1, 1), maskTerm(profile411, 15, 1, 1)} = some {maskTerm(profile411, 1, 1, 1), maskTerm(profile411, 2, 1, 1), maskTerm(profile411, 6, 1, 1), maskTerm(profile411, 15, 1, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile411, 6, 1, 1) maskTerm(inversePermProfile .abc profile411, 15, 1, 1) maskTerm(inversePermProfile .abc profile411, 9, 1, 1)⟩ : FixedMoveData profile411).step? {maskTerm(profile411, 1, 1, 1), maskTerm(profile411, 2, 1, 1), maskTerm(profile411, 6, 1, 1), maskTerm(profile411, 15, 1, 1)} = some {maskTerm(profile411, 1, 1, 1), maskTerm(profile411, 2, 1, 1), maskTerm(profile411, 9, 1, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 2 for the reverse direction of row `41101`. -/
def row41101ReverseTemplate2 :
    ContextualPathTemplate profile411 row41101Finish row41101Start where
  moves := [⟨.abc, .reduction maskTerm(inversePermProfile .abc profile411, 4, 1, 1) maskTerm(inversePermProfile .abc profile411, 6, 1, 1) maskTerm(inversePermProfile .abc profile411, 2, 1, 1)⟩,
    ⟨.abc, .split maskTerm(inversePermProfile .abc profile411, 8, 1, 1) maskTerm(inversePermProfile .abc profile411, 1, 1, 1) maskTerm(inversePermProfile .abc profile411, 9, 1, 1)⟩,
    ⟨.abc, .reduction maskTerm(inversePermProfile .abc profile411, 9, 1, 1) maskTerm(inversePermProfile .abc profile411, 15, 1, 1) maskTerm(inversePermProfile .abc profile411, 6, 1, 1)⟩]
  present := {maskTerm(profile411, 6, 1, 1)}
  absent := {maskTerm(profile411, 9, 1, 1)}
  support_eq := by decide
  replay := by
    have hstart : row41101Finish ∪ {maskTerm(profile411, 6, 1, 1)} = {maskTerm(profile411, 4, 1, 1), maskTerm(profile411, 6, 1, 1), maskTerm(profile411, 8, 1, 1), maskTerm(profile411, 15, 1, 1)} := by
      unfold row41101Finish
      decide
    have hfinish : row41101Start ∪ {maskTerm(profile411, 6, 1, 1)} = {maskTerm(profile411, 1, 1, 1), maskTerm(profile411, 2, 1, 1), maskTerm(profile411, 6, 1, 1)} := by
      unfold row41101Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile411, 4, 1, 1) maskTerm(inversePermProfile .abc profile411, 6, 1, 1) maskTerm(inversePermProfile .abc profile411, 2, 1, 1)⟩ : FixedMoveData profile411).step? {maskTerm(profile411, 4, 1, 1), maskTerm(profile411, 6, 1, 1), maskTerm(profile411, 8, 1, 1), maskTerm(profile411, 15, 1, 1)} = some {maskTerm(profile411, 2, 1, 1), maskTerm(profile411, 8, 1, 1), maskTerm(profile411, 15, 1, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile411, 8, 1, 1) maskTerm(inversePermProfile .abc profile411, 1, 1, 1) maskTerm(inversePermProfile .abc profile411, 9, 1, 1)⟩ : FixedMoveData profile411).step? {maskTerm(profile411, 2, 1, 1), maskTerm(profile411, 8, 1, 1), maskTerm(profile411, 15, 1, 1)} = some {maskTerm(profile411, 1, 1, 1), maskTerm(profile411, 2, 1, 1), maskTerm(profile411, 9, 1, 1), maskTerm(profile411, 15, 1, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile411, 9, 1, 1) maskTerm(inversePermProfile .abc profile411, 15, 1, 1) maskTerm(inversePermProfile .abc profile411, 6, 1, 1)⟩ : FixedMoveData profile411).step? {maskTerm(profile411, 1, 1, 1), maskTerm(profile411, 2, 1, 1), maskTerm(profile411, 9, 1, 1), maskTerm(profile411, 15, 1, 1)} = some {maskTerm(profile411, 1, 1, 1), maskTerm(profile411, 2, 1, 1), maskTerm(profile411, 6, 1, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 3 for the reverse direction of row `41101`. -/
def row41101ReverseTemplate3 :
    ContextualPathTemplate profile411 row41101Finish row41101Start where
  moves := [⟨.abc, .reduction maskTerm(inversePermProfile .abc profile411, 4, 1, 1) maskTerm(inversePermProfile .abc profile411, 6, 1, 1) maskTerm(inversePermProfile .abc profile411, 2, 1, 1)⟩,
    ⟨.abc, .reduction maskTerm(inversePermProfile .abc profile411, 8, 1, 1) maskTerm(inversePermProfile .abc profile411, 9, 1, 1) maskTerm(inversePermProfile .abc profile411, 1, 1, 1)⟩,
    ⟨.abc, .split maskTerm(inversePermProfile .abc profile411, 15, 1, 1) maskTerm(inversePermProfile .abc profile411, 6, 1, 1) maskTerm(inversePermProfile .abc profile411, 9, 1, 1)⟩]
  present := {maskTerm(profile411, 6, 1, 1), maskTerm(profile411, 9, 1, 1)}
  absent := ∅
  support_eq := by decide
  replay := by
    have hstart : row41101Finish ∪ {maskTerm(profile411, 6, 1, 1), maskTerm(profile411, 9, 1, 1)} = {maskTerm(profile411, 4, 1, 1), maskTerm(profile411, 6, 1, 1), maskTerm(profile411, 8, 1, 1), maskTerm(profile411, 9, 1, 1), maskTerm(profile411, 15, 1, 1)} := by
      unfold row41101Finish
      decide
    have hfinish : row41101Start ∪ {maskTerm(profile411, 6, 1, 1), maskTerm(profile411, 9, 1, 1)} = {maskTerm(profile411, 1, 1, 1), maskTerm(profile411, 2, 1, 1), maskTerm(profile411, 6, 1, 1), maskTerm(profile411, 9, 1, 1)} := by
      unfold row41101Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile411, 4, 1, 1) maskTerm(inversePermProfile .abc profile411, 6, 1, 1) maskTerm(inversePermProfile .abc profile411, 2, 1, 1)⟩ : FixedMoveData profile411).step? {maskTerm(profile411, 4, 1, 1), maskTerm(profile411, 6, 1, 1), maskTerm(profile411, 8, 1, 1), maskTerm(profile411, 9, 1, 1), maskTerm(profile411, 15, 1, 1)} = some {maskTerm(profile411, 2, 1, 1), maskTerm(profile411, 8, 1, 1), maskTerm(profile411, 9, 1, 1), maskTerm(profile411, 15, 1, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile411, 8, 1, 1) maskTerm(inversePermProfile .abc profile411, 9, 1, 1) maskTerm(inversePermProfile .abc profile411, 1, 1, 1)⟩ : FixedMoveData profile411).step? {maskTerm(profile411, 2, 1, 1), maskTerm(profile411, 8, 1, 1), maskTerm(profile411, 9, 1, 1), maskTerm(profile411, 15, 1, 1)} = some {maskTerm(profile411, 1, 1, 1), maskTerm(profile411, 2, 1, 1), maskTerm(profile411, 15, 1, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile411, 15, 1, 1) maskTerm(inversePermProfile .abc profile411, 6, 1, 1) maskTerm(inversePermProfile .abc profile411, 9, 1, 1)⟩ : FixedMoveData profile411).step? {maskTerm(profile411, 1, 1, 1), maskTerm(profile411, 2, 1, 1), maskTerm(profile411, 15, 1, 1)} = some {maskTerm(profile411, 1, 1, 1), maskTerm(profile411, 2, 1, 1), maskTerm(profile411, 6, 1, 1), maskTerm(profile411, 9, 1, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Total compact decision tree for the reverse direction of row `41101`. -/
def row41101ReverseContextualTree :
    ContextualDecisionTree profile411 row41101Finish row41101Start 3 :=
  .branch maskTerm(profile411, 3, 1, 1)
    (.branch maskTerm(profile411, 5, 1, 1)
      (.branch maskTerm(profile411, 6, 1, 1)
        (.branch maskTerm(profile411, 9, 1, 1)
          (.leaf row41101ReverseTemplate0 (by decide))
          (.leaf row41101ReverseTemplate1 (by decide)))
        (.branch maskTerm(profile411, 9, 1, 1)
          (.leaf row41101ReverseTemplate2 (by decide))
          (.leaf row41101ReverseTemplate3 (by decide))))
      (.branch maskTerm(profile411, 6, 1, 1)
        (.branch maskTerm(profile411, 9, 1, 1)
          (.leaf row41101ReverseTemplate0 (by decide))
          (.leaf row41101ReverseTemplate1 (by decide)))
        (.branch maskTerm(profile411, 9, 1, 1)
          (.leaf row41101ReverseTemplate2 (by decide))
          (.leaf row41101ReverseTemplate3 (by decide)))))
    (.branch maskTerm(profile411, 5, 1, 1)
      (.branch maskTerm(profile411, 6, 1, 1)
        (.branch maskTerm(profile411, 9, 1, 1)
          (.leaf row41101ReverseTemplate0 (by decide))
          (.leaf row41101ReverseTemplate1 (by decide)))
        (.branch maskTerm(profile411, 9, 1, 1)
          (.leaf row41101ReverseTemplate2 (by decide))
          (.leaf row41101ReverseTemplate3 (by decide))))
      (.branch maskTerm(profile411, 6, 1, 1)
        (.branch maskTerm(profile411, 9, 1, 1)
          (.leaf row41101ReverseTemplate0 (by decide))
          (.leaf row41101ReverseTemplate1 (by decide)))
        (.branch maskTerm(profile411, 9, 1, 1)
          (.leaf row41101ReverseTemplate2 (by decide))
          (.leaf row41101ReverseTemplate3 (by decide)))))

/-- Kernel-checked full guard coverage for the reverse tree of row `41101`. -/
theorem row41101ReverseContextualTree_valid :
    row41101ReverseContextualTree.Valid ∅ ∅ := by
  unfold row41101ReverseContextualTree
  unfold row41101ReverseTemplate0
  unfold row41101ReverseTemplate1
  unfold row41101ReverseTemplate2
  unfold row41101ReverseTemplate3
  simp only [ContextualDecisionTree.Valid]
  repeat' apply And.intro
  all_goals
    intro x hx
    aesop

/-- Executably select actual fixed witnesses for the reverse direction of row `41101`. -/
def row41101ReverseContextualMoves (C : State profile411) : List (FixedMoveData profile411) :=
  row41101ReverseContextualTree.selectMoves C

/-- The selected reverse witness list for row `41101` replays in every endpoint-disjoint context. -/
theorem run?_row41101ReverseContextualMoves (C : State profile411)
    (hC : Disjoint C (row41101Finish ∪ row41101Start)) :
    run? (C ∪ row41101Finish) (row41101ReverseContextualMoves C) =
      some (C ∪ row41101Start) := by
  exact row41101ReverseContextualTree.selectMoves_run? ∅ ∅
    row41101ReverseContextualTree_valid (Finset.empty_subset C)
    (Finset.disjoint_empty_right C) hC

/-- Compile the selected reverse witnesses of row `41101` to an actual dependent move path. -/
def row41101ReverseContextualPath (C : State profile411)
    (hC : Disjoint C (row41101Finish ∪ row41101Start)) :
    MovePath (@AllModeMove profile411) (C ∪ row41101Finish) (C ∪ row41101Start) :=
  row41101ReverseContextualTree.toMovePath
    row41101ReverseContextualTree_valid hC

/-- The compiled reverse contextual path for row `41101` has exact length `3`. -/
@[simp] theorem row41101ReverseContextualPath_length (C : State profile411)
    (hC : Disjoint C (row41101Finish ∪ row41101Start)) :
    (row41101ReverseContextualPath C hC).length = 3 := by
  exact ContextualDecisionTree.toMovePath_length _ _ _

end BilinearComplexity.NormalizedBinaryContextualCertificates
