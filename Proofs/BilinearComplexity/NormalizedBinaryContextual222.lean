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

private abbrev stateDecidableEq222 (q : Profile) : DecidableEq (State q) :=
  @Finset.decidableEq (Carrier q) inferInstance

local instance instDecidableEqState222 (q : Profile) : DecidableEq (State q) :=
  stateDecidableEq222 q

local macro "maskTerm(" p:term "," a:num "," b:num "," c:num ")" : term =>
  `(carrierOfMasks $p $a $b $c (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide))

/-- Replayed guarded template 0 for the forward direction of row `22201`. -/
def row22201ForwardTemplate0 :
    ContextualPathTemplate profile222 row22201Start row22201Finish where
  moves := [⟨.bca, .reduction maskTerm(inversePermProfile .bca profile222, 1, 1, 1) maskTerm(inversePermProfile .bca profile222, 2, 1, 1) maskTerm(inversePermProfile .bca profile222, 3, 1, 1)⟩,
    ⟨.bac, .split maskTerm(inversePermProfile .bac profile222, 1, 1, 3) maskTerm(inversePermProfile .bac profile222, 2, 1, 3) maskTerm(inversePermProfile .bac profile222, 3, 1, 3)⟩,
    ⟨.abc, .split maskTerm(inversePermProfile .abc profile222, 1, 3, 3) maskTerm(inversePermProfile .abc profile222, 2, 3, 3) maskTerm(inversePermProfile .abc profile222, 3, 3, 3)⟩]
  present := ∅
  absent := {maskTerm(profile222, 1, 1, 3), maskTerm(profile222, 1, 3, 3)}
  support_eq := by decide
  replay := by
    have hstart : row22201Start ∪ ∅ = {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 1, 2)} := by
      unfold row22201Start
      decide
    have hfinish : row22201Finish ∪ ∅ = {maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 2, 3, 3), maskTerm(profile222, 3, 3, 3)} := by
      unfold row22201Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bca, .reduction maskTerm(inversePermProfile .bca profile222, 1, 1, 1) maskTerm(inversePermProfile .bca profile222, 2, 1, 1) maskTerm(inversePermProfile .bca profile222, 3, 1, 1)⟩ : FixedMoveData profile222).step? {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 1, 2)} = some {maskTerm(profile222, 1, 1, 3)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .split maskTerm(inversePermProfile .bac profile222, 1, 1, 3) maskTerm(inversePermProfile .bac profile222, 2, 1, 3) maskTerm(inversePermProfile .bac profile222, 3, 1, 3)⟩ : FixedMoveData profile222).step? {maskTerm(profile222, 1, 1, 3)} = some {maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 1, 3, 3)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile222, 1, 3, 3) maskTerm(inversePermProfile .abc profile222, 2, 3, 3) maskTerm(inversePermProfile .abc profile222, 3, 3, 3)⟩ : FixedMoveData profile222).step? {maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 1, 3, 3)} = some {maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 2, 3, 3), maskTerm(profile222, 3, 3, 3)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 1 for the forward direction of row `22201`. -/
def row22201ForwardTemplate1 :
    ContextualPathTemplate profile222 row22201Start row22201Finish where
  moves := [⟨.bca, .reduction maskTerm(inversePermProfile .bca profile222, 1, 1, 1) maskTerm(inversePermProfile .bca profile222, 2, 1, 1) maskTerm(inversePermProfile .bca profile222, 3, 1, 1)⟩,
    ⟨.abc, .split maskTerm(inversePermProfile .abc profile222, 1, 3, 3) maskTerm(inversePermProfile .abc profile222, 2, 3, 3) maskTerm(inversePermProfile .abc profile222, 3, 3, 3)⟩,
    ⟨.bac, .split maskTerm(inversePermProfile .bac profile222, 1, 1, 3) maskTerm(inversePermProfile .bac profile222, 2, 1, 3) maskTerm(inversePermProfile .bac profile222, 3, 1, 3)⟩]
  present := {maskTerm(profile222, 1, 3, 3)}
  absent := {maskTerm(profile222, 1, 1, 3)}
  support_eq := by decide
  replay := by
    have hstart : row22201Start ∪ {maskTerm(profile222, 1, 3, 3)} = {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 1, 3, 3)} := by
      unfold row22201Start
      decide
    have hfinish : row22201Finish ∪ {maskTerm(profile222, 1, 3, 3)} = {maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 1, 3, 3), maskTerm(profile222, 2, 3, 3), maskTerm(profile222, 3, 3, 3)} := by
      unfold row22201Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bca, .reduction maskTerm(inversePermProfile .bca profile222, 1, 1, 1) maskTerm(inversePermProfile .bca profile222, 2, 1, 1) maskTerm(inversePermProfile .bca profile222, 3, 1, 1)⟩ : FixedMoveData profile222).step? {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 1, 3, 3)} = some {maskTerm(profile222, 1, 1, 3), maskTerm(profile222, 1, 3, 3)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile222, 1, 3, 3) maskTerm(inversePermProfile .abc profile222, 2, 3, 3) maskTerm(inversePermProfile .abc profile222, 3, 3, 3)⟩ : FixedMoveData profile222).step? {maskTerm(profile222, 1, 1, 3), maskTerm(profile222, 1, 3, 3)} = some {maskTerm(profile222, 1, 1, 3), maskTerm(profile222, 2, 3, 3), maskTerm(profile222, 3, 3, 3)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.bac, .split maskTerm(inversePermProfile .bac profile222, 1, 1, 3) maskTerm(inversePermProfile .bac profile222, 2, 1, 3) maskTerm(inversePermProfile .bac profile222, 3, 1, 3)⟩ : FixedMoveData profile222).step? {maskTerm(profile222, 1, 1, 3), maskTerm(profile222, 2, 3, 3), maskTerm(profile222, 3, 3, 3)} = some {maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 1, 3, 3), maskTerm(profile222, 2, 3, 3), maskTerm(profile222, 3, 3, 3)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 2 for the forward direction of row `22201`. -/
def row22201ForwardTemplate2 :
    ContextualPathTemplate profile222 row22201Start row22201Finish where
  moves := [⟨.bac, .split maskTerm(inversePermProfile .bac profile222, 1, 1, 3) maskTerm(inversePermProfile .bac profile222, 2, 1, 3) maskTerm(inversePermProfile .bac profile222, 3, 1, 3)⟩,
    ⟨.bca, .reduction maskTerm(inversePermProfile .bca profile222, 1, 1, 1) maskTerm(inversePermProfile .bca profile222, 2, 1, 1) maskTerm(inversePermProfile .bca profile222, 3, 1, 1)⟩,
    ⟨.abc, .split maskTerm(inversePermProfile .abc profile222, 1, 3, 3) maskTerm(inversePermProfile .abc profile222, 2, 3, 3) maskTerm(inversePermProfile .abc profile222, 3, 3, 3)⟩]
  present := {maskTerm(profile222, 1, 1, 3)}
  absent := {maskTerm(profile222, 1, 3, 3)}
  support_eq := by decide
  replay := by
    have hstart : row22201Start ∪ {maskTerm(profile222, 1, 1, 3)} = {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 1, 1, 3)} := by
      unfold row22201Start
      decide
    have hfinish : row22201Finish ∪ {maskTerm(profile222, 1, 1, 3)} = {maskTerm(profile222, 1, 1, 3), maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 2, 3, 3), maskTerm(profile222, 3, 3, 3)} := by
      unfold row22201Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .split maskTerm(inversePermProfile .bac profile222, 1, 1, 3) maskTerm(inversePermProfile .bac profile222, 2, 1, 3) maskTerm(inversePermProfile .bac profile222, 3, 1, 3)⟩ : FixedMoveData profile222).step? {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 1, 1, 3)} = some {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 1, 3, 3)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bca, .reduction maskTerm(inversePermProfile .bca profile222, 1, 1, 1) maskTerm(inversePermProfile .bca profile222, 2, 1, 1) maskTerm(inversePermProfile .bca profile222, 3, 1, 1)⟩ : FixedMoveData profile222).step? {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 1, 3, 3)} = some {maskTerm(profile222, 1, 1, 3), maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 1, 3, 3)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile222, 1, 3, 3) maskTerm(inversePermProfile .abc profile222, 2, 3, 3) maskTerm(inversePermProfile .abc profile222, 3, 3, 3)⟩ : FixedMoveData profile222).step? {maskTerm(profile222, 1, 1, 3), maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 1, 3, 3)} = some {maskTerm(profile222, 1, 1, 3), maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 2, 3, 3), maskTerm(profile222, 3, 3, 3)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 3 for the forward direction of row `22201`. -/
def row22201ForwardTemplate3 :
    ContextualPathTemplate profile222 row22201Start row22201Finish where
  moves := [⟨.abc, .split maskTerm(inversePermProfile .abc profile222, 1, 3, 3) maskTerm(inversePermProfile .abc profile222, 2, 3, 3) maskTerm(inversePermProfile .abc profile222, 3, 3, 3)⟩,
    ⟨.bac, .split maskTerm(inversePermProfile .bac profile222, 1, 1, 3) maskTerm(inversePermProfile .bac profile222, 2, 1, 3) maskTerm(inversePermProfile .bac profile222, 3, 1, 3)⟩,
    ⟨.bca, .reduction maskTerm(inversePermProfile .bca profile222, 1, 1, 1) maskTerm(inversePermProfile .bca profile222, 2, 1, 1) maskTerm(inversePermProfile .bca profile222, 3, 1, 1)⟩]
  present := {maskTerm(profile222, 1, 1, 3), maskTerm(profile222, 1, 3, 3)}
  absent := ∅
  support_eq := by decide
  replay := by
    have hstart : row22201Start ∪ {maskTerm(profile222, 1, 1, 3), maskTerm(profile222, 1, 3, 3)} = {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 1, 1, 3), maskTerm(profile222, 1, 3, 3)} := by
      unfold row22201Start
      decide
    have hfinish : row22201Finish ∪ {maskTerm(profile222, 1, 1, 3), maskTerm(profile222, 1, 3, 3)} = {maskTerm(profile222, 1, 1, 3), maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 1, 3, 3), maskTerm(profile222, 2, 3, 3), maskTerm(profile222, 3, 3, 3)} := by
      unfold row22201Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile222, 1, 3, 3) maskTerm(inversePermProfile .abc profile222, 2, 3, 3) maskTerm(inversePermProfile .abc profile222, 3, 3, 3)⟩ : FixedMoveData profile222).step? {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 1, 1, 3), maskTerm(profile222, 1, 3, 3)} = some {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 1, 1, 3), maskTerm(profile222, 2, 3, 3), maskTerm(profile222, 3, 3, 3)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .split maskTerm(inversePermProfile .bac profile222, 1, 1, 3) maskTerm(inversePermProfile .bac profile222, 2, 1, 3) maskTerm(inversePermProfile .bac profile222, 3, 1, 3)⟩ : FixedMoveData profile222).step? {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 1, 1, 3), maskTerm(profile222, 2, 3, 3), maskTerm(profile222, 3, 3, 3)} = some {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 1, 3, 3), maskTerm(profile222, 2, 3, 3), maskTerm(profile222, 3, 3, 3)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.bca, .reduction maskTerm(inversePermProfile .bca profile222, 1, 1, 1) maskTerm(inversePermProfile .bca profile222, 2, 1, 1) maskTerm(inversePermProfile .bca profile222, 3, 1, 1)⟩ : FixedMoveData profile222).step? {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 1, 3, 3), maskTerm(profile222, 2, 3, 3), maskTerm(profile222, 3, 3, 3)} = some {maskTerm(profile222, 1, 1, 3), maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 1, 3, 3), maskTerm(profile222, 2, 3, 3), maskTerm(profile222, 3, 3, 3)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Total compact decision tree for the forward direction of row `22201`. -/
def row22201ForwardContextualTree :
    ContextualDecisionTree profile222 row22201Start row22201Finish 3 :=
  .branch maskTerm(profile222, 1, 3, 3)
    (.branch maskTerm(profile222, 1, 1, 3)
      (.leaf row22201ForwardTemplate0 (by decide))
      (.leaf row22201ForwardTemplate2 (by decide)))
    (.branch maskTerm(profile222, 1, 1, 3)
      (.leaf row22201ForwardTemplate1 (by decide))
      (.leaf row22201ForwardTemplate3 (by decide)))

/-- Kernel-checked full guard coverage for the forward tree of row `22201`. -/
theorem row22201ForwardContextualTree_valid :
    row22201ForwardContextualTree.Valid ∅ ∅ := by
  unfold row22201ForwardContextualTree
  unfold row22201ForwardTemplate0
  unfold row22201ForwardTemplate1
  unfold row22201ForwardTemplate2
  unfold row22201ForwardTemplate3
  simp only [ContextualDecisionTree.Valid]
  repeat' apply And.intro
  all_goals
    intro x hx
    aesop

/-- Executably select actual fixed witnesses for the forward direction of row `22201`. -/
def row22201ForwardContextualMoves (C : State profile222) : List (FixedMoveData profile222) :=
  row22201ForwardContextualTree.selectMoves C

/-- The selected forward witness list for row `22201` replays in every endpoint-disjoint context. -/
theorem run?_row22201ForwardContextualMoves (C : State profile222)
    (hC : Disjoint C (row22201Start ∪ row22201Finish)) :
    run? (C ∪ row22201Start) (row22201ForwardContextualMoves C) =
      some (C ∪ row22201Finish) := by
  exact row22201ForwardContextualTree.selectMoves_run? ∅ ∅
    row22201ForwardContextualTree_valid (Finset.empty_subset C)
    (Finset.disjoint_empty_right C) hC

/-- Compile the selected forward witnesses of row `22201` to an actual dependent move path. -/
def row22201ForwardContextualPath (C : State profile222)
    (hC : Disjoint C (row22201Start ∪ row22201Finish)) :
    MovePath (@AllModeMove profile222) (C ∪ row22201Start) (C ∪ row22201Finish) :=
  row22201ForwardContextualTree.toMovePath
    row22201ForwardContextualTree_valid hC

/-- The compiled forward contextual path for row `22201` has exact length `3`. -/
@[simp] theorem row22201ForwardContextualPath_length (C : State profile222)
    (hC : Disjoint C (row22201Start ∪ row22201Finish)) :
    (row22201ForwardContextualPath C hC).length = 3 := by
  exact ContextualDecisionTree.toMovePath_length _ _ _

/-- Replayed guarded template 0 for the reverse direction of row `22201`. -/
def row22201ReverseTemplate0 :
    ContextualPathTemplate profile222 row22201Finish row22201Start where
  moves := [⟨.abc, .reduction maskTerm(inversePermProfile .abc profile222, 2, 3, 3) maskTerm(inversePermProfile .abc profile222, 3, 3, 3) maskTerm(inversePermProfile .abc profile222, 1, 3, 3)⟩,
    ⟨.bac, .reduction maskTerm(inversePermProfile .bac profile222, 2, 1, 3) maskTerm(inversePermProfile .bac profile222, 3, 1, 3) maskTerm(inversePermProfile .bac profile222, 1, 1, 3)⟩,
    ⟨.bca, .split maskTerm(inversePermProfile .bca profile222, 3, 1, 1) maskTerm(inversePermProfile .bca profile222, 1, 1, 1) maskTerm(inversePermProfile .bca profile222, 2, 1, 1)⟩]
  present := ∅
  absent := {maskTerm(profile222, 1, 1, 3), maskTerm(profile222, 1, 3, 3)}
  support_eq := by decide
  replay := by
    have hstart : row22201Finish ∪ ∅ = {maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 2, 3, 3), maskTerm(profile222, 3, 3, 3)} := by
      unfold row22201Finish
      decide
    have hfinish : row22201Start ∪ ∅ = {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 1, 2)} := by
      unfold row22201Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile222, 2, 3, 3) maskTerm(inversePermProfile .abc profile222, 3, 3, 3) maskTerm(inversePermProfile .abc profile222, 1, 3, 3)⟩ : FixedMoveData profile222).step? {maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 2, 3, 3), maskTerm(profile222, 3, 3, 3)} = some {maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 1, 3, 3)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .reduction maskTerm(inversePermProfile .bac profile222, 2, 1, 3) maskTerm(inversePermProfile .bac profile222, 3, 1, 3) maskTerm(inversePermProfile .bac profile222, 1, 1, 3)⟩ : FixedMoveData profile222).step? {maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 1, 3, 3)} = some {maskTerm(profile222, 1, 1, 3)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.bca, .split maskTerm(inversePermProfile .bca profile222, 3, 1, 1) maskTerm(inversePermProfile .bca profile222, 1, 1, 1) maskTerm(inversePermProfile .bca profile222, 2, 1, 1)⟩ : FixedMoveData profile222).step? {maskTerm(profile222, 1, 1, 3)} = some {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 1, 2)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 1 for the reverse direction of row `22201`. -/
def row22201ReverseTemplate1 :
    ContextualPathTemplate profile222 row22201Finish row22201Start where
  moves := [⟨.bac, .reduction maskTerm(inversePermProfile .bac profile222, 2, 1, 3) maskTerm(inversePermProfile .bac profile222, 3, 1, 3) maskTerm(inversePermProfile .bac profile222, 1, 1, 3)⟩,
    ⟨.bca, .split maskTerm(inversePermProfile .bca profile222, 3, 1, 1) maskTerm(inversePermProfile .bca profile222, 1, 1, 1) maskTerm(inversePermProfile .bca profile222, 2, 1, 1)⟩,
    ⟨.abc, .reduction maskTerm(inversePermProfile .abc profile222, 2, 3, 3) maskTerm(inversePermProfile .abc profile222, 3, 3, 3) maskTerm(inversePermProfile .abc profile222, 1, 3, 3)⟩]
  present := {maskTerm(profile222, 1, 3, 3)}
  absent := {maskTerm(profile222, 1, 1, 3)}
  support_eq := by decide
  replay := by
    have hstart : row22201Finish ∪ {maskTerm(profile222, 1, 3, 3)} = {maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 1, 3, 3), maskTerm(profile222, 2, 3, 3), maskTerm(profile222, 3, 3, 3)} := by
      unfold row22201Finish
      decide
    have hfinish : row22201Start ∪ {maskTerm(profile222, 1, 3, 3)} = {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 1, 3, 3)} := by
      unfold row22201Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .reduction maskTerm(inversePermProfile .bac profile222, 2, 1, 3) maskTerm(inversePermProfile .bac profile222, 3, 1, 3) maskTerm(inversePermProfile .bac profile222, 1, 1, 3)⟩ : FixedMoveData profile222).step? {maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 1, 3, 3), maskTerm(profile222, 2, 3, 3), maskTerm(profile222, 3, 3, 3)} = some {maskTerm(profile222, 1, 1, 3), maskTerm(profile222, 2, 3, 3), maskTerm(profile222, 3, 3, 3)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bca, .split maskTerm(inversePermProfile .bca profile222, 3, 1, 1) maskTerm(inversePermProfile .bca profile222, 1, 1, 1) maskTerm(inversePermProfile .bca profile222, 2, 1, 1)⟩ : FixedMoveData profile222).step? {maskTerm(profile222, 1, 1, 3), maskTerm(profile222, 2, 3, 3), maskTerm(profile222, 3, 3, 3)} = some {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 2, 3, 3), maskTerm(profile222, 3, 3, 3)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile222, 2, 3, 3) maskTerm(inversePermProfile .abc profile222, 3, 3, 3) maskTerm(inversePermProfile .abc profile222, 1, 3, 3)⟩ : FixedMoveData profile222).step? {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 2, 3, 3), maskTerm(profile222, 3, 3, 3)} = some {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 1, 3, 3)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 2 for the reverse direction of row `22201`. -/
def row22201ReverseTemplate2 :
    ContextualPathTemplate profile222 row22201Finish row22201Start where
  moves := [⟨.bca, .split maskTerm(inversePermProfile .bca profile222, 3, 1, 1) maskTerm(inversePermProfile .bca profile222, 1, 1, 1) maskTerm(inversePermProfile .bca profile222, 2, 1, 1)⟩,
    ⟨.abc, .reduction maskTerm(inversePermProfile .abc profile222, 2, 3, 3) maskTerm(inversePermProfile .abc profile222, 3, 3, 3) maskTerm(inversePermProfile .abc profile222, 1, 3, 3)⟩,
    ⟨.bac, .reduction maskTerm(inversePermProfile .bac profile222, 2, 1, 3) maskTerm(inversePermProfile .bac profile222, 3, 1, 3) maskTerm(inversePermProfile .bac profile222, 1, 1, 3)⟩]
  present := {maskTerm(profile222, 1, 1, 3)}
  absent := {maskTerm(profile222, 1, 3, 3)}
  support_eq := by decide
  replay := by
    have hstart : row22201Finish ∪ {maskTerm(profile222, 1, 1, 3)} = {maskTerm(profile222, 1, 1, 3), maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 2, 3, 3), maskTerm(profile222, 3, 3, 3)} := by
      unfold row22201Finish
      decide
    have hfinish : row22201Start ∪ {maskTerm(profile222, 1, 1, 3)} = {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 1, 1, 3)} := by
      unfold row22201Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bca, .split maskTerm(inversePermProfile .bca profile222, 3, 1, 1) maskTerm(inversePermProfile .bca profile222, 1, 1, 1) maskTerm(inversePermProfile .bca profile222, 2, 1, 1)⟩ : FixedMoveData profile222).step? {maskTerm(profile222, 1, 1, 3), maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 2, 3, 3), maskTerm(profile222, 3, 3, 3)} = some {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 2, 3, 3), maskTerm(profile222, 3, 3, 3)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile222, 2, 3, 3) maskTerm(inversePermProfile .abc profile222, 3, 3, 3) maskTerm(inversePermProfile .abc profile222, 1, 3, 3)⟩ : FixedMoveData profile222).step? {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 2, 3, 3), maskTerm(profile222, 3, 3, 3)} = some {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 1, 3, 3)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.bac, .reduction maskTerm(inversePermProfile .bac profile222, 2, 1, 3) maskTerm(inversePermProfile .bac profile222, 3, 1, 3) maskTerm(inversePermProfile .bac profile222, 1, 1, 3)⟩ : FixedMoveData profile222).step? {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 1, 3, 3)} = some {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 1, 1, 3)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Replayed guarded template 3 for the reverse direction of row `22201`. -/
def row22201ReverseTemplate3 :
    ContextualPathTemplate profile222 row22201Finish row22201Start where
  moves := [⟨.bca, .split maskTerm(inversePermProfile .bca profile222, 3, 1, 1) maskTerm(inversePermProfile .bca profile222, 1, 1, 1) maskTerm(inversePermProfile .bca profile222, 2, 1, 1)⟩,
    ⟨.bac, .reduction maskTerm(inversePermProfile .bac profile222, 2, 1, 3) maskTerm(inversePermProfile .bac profile222, 3, 1, 3) maskTerm(inversePermProfile .bac profile222, 1, 1, 3)⟩,
    ⟨.abc, .reduction maskTerm(inversePermProfile .abc profile222, 2, 3, 3) maskTerm(inversePermProfile .abc profile222, 3, 3, 3) maskTerm(inversePermProfile .abc profile222, 1, 3, 3)⟩]
  present := {maskTerm(profile222, 1, 1, 3), maskTerm(profile222, 1, 3, 3)}
  absent := ∅
  support_eq := by decide
  replay := by
    have hstart : row22201Finish ∪ {maskTerm(profile222, 1, 1, 3), maskTerm(profile222, 1, 3, 3)} = {maskTerm(profile222, 1, 1, 3), maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 1, 3, 3), maskTerm(profile222, 2, 3, 3), maskTerm(profile222, 3, 3, 3)} := by
      unfold row22201Finish
      decide
    have hfinish : row22201Start ∪ {maskTerm(profile222, 1, 1, 3), maskTerm(profile222, 1, 3, 3)} = {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 1, 1, 3), maskTerm(profile222, 1, 3, 3)} := by
      unfold row22201Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bca, .split maskTerm(inversePermProfile .bca profile222, 3, 1, 1) maskTerm(inversePermProfile .bca profile222, 1, 1, 1) maskTerm(inversePermProfile .bca profile222, 2, 1, 1)⟩ : FixedMoveData profile222).step? {maskTerm(profile222, 1, 1, 3), maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 1, 3, 3), maskTerm(profile222, 2, 3, 3), maskTerm(profile222, 3, 3, 3)} = some {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 1, 3, 3), maskTerm(profile222, 2, 3, 3), maskTerm(profile222, 3, 3, 3)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .reduction maskTerm(inversePermProfile .bac profile222, 2, 1, 3) maskTerm(inversePermProfile .bac profile222, 3, 1, 3) maskTerm(inversePermProfile .bac profile222, 1, 1, 3)⟩ : FixedMoveData profile222).step? {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 1, 3, 3), maskTerm(profile222, 2, 3, 3), maskTerm(profile222, 3, 3, 3)} = some {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 1, 1, 3), maskTerm(profile222, 2, 3, 3), maskTerm(profile222, 3, 3, 3)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep2 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile222, 2, 3, 3) maskTerm(inversePermProfile .abc profile222, 3, 3, 3) maskTerm(inversePermProfile .abc profile222, 1, 3, 3)⟩ : FixedMoveData profile222).step? {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 1, 1, 3), maskTerm(profile222, 2, 3, 3), maskTerm(profile222, 3, 3, 3)} = some {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 1, 1, 3), maskTerm(profile222, 1, 3, 3)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, hstep2, Option.bind_some]

/-- Total compact decision tree for the reverse direction of row `22201`. -/
def row22201ReverseContextualTree :
    ContextualDecisionTree profile222 row22201Finish row22201Start 3 :=
  .branch maskTerm(profile222, 1, 3, 3)
    (.branch maskTerm(profile222, 1, 1, 3)
      (.leaf row22201ReverseTemplate0 (by decide))
      (.leaf row22201ReverseTemplate2 (by decide)))
    (.branch maskTerm(profile222, 1, 1, 3)
      (.leaf row22201ReverseTemplate1 (by decide))
      (.leaf row22201ReverseTemplate3 (by decide)))

/-- Kernel-checked full guard coverage for the reverse tree of row `22201`. -/
theorem row22201ReverseContextualTree_valid :
    row22201ReverseContextualTree.Valid ∅ ∅ := by
  unfold row22201ReverseContextualTree
  unfold row22201ReverseTemplate0
  unfold row22201ReverseTemplate1
  unfold row22201ReverseTemplate2
  unfold row22201ReverseTemplate3
  simp only [ContextualDecisionTree.Valid]
  repeat' apply And.intro
  all_goals
    intro x hx
    aesop

/-- Executably select actual fixed witnesses for the reverse direction of row `22201`. -/
def row22201ReverseContextualMoves (C : State profile222) : List (FixedMoveData profile222) :=
  row22201ReverseContextualTree.selectMoves C

/-- The selected reverse witness list for row `22201` replays in every endpoint-disjoint context. -/
theorem run?_row22201ReverseContextualMoves (C : State profile222)
    (hC : Disjoint C (row22201Finish ∪ row22201Start)) :
    run? (C ∪ row22201Finish) (row22201ReverseContextualMoves C) =
      some (C ∪ row22201Start) := by
  exact row22201ReverseContextualTree.selectMoves_run? ∅ ∅
    row22201ReverseContextualTree_valid (Finset.empty_subset C)
    (Finset.disjoint_empty_right C) hC

/-- Compile the selected reverse witnesses of row `22201` to an actual dependent move path. -/
def row22201ReverseContextualPath (C : State profile222)
    (hC : Disjoint C (row22201Finish ∪ row22201Start)) :
    MovePath (@AllModeMove profile222) (C ∪ row22201Finish) (C ∪ row22201Start) :=
  row22201ReverseContextualTree.toMovePath
    row22201ReverseContextualTree_valid hC

/-- The compiled reverse contextual path for row `22201` has exact length `3`. -/
@[simp] theorem row22201ReverseContextualPath_length (C : State profile222)
    (hC : Disjoint C (row22201Finish ∪ row22201Start)) :
    (row22201ReverseContextualPath C hC).length = 3 := by
  exact ContextualDecisionTree.toMovePath_length _ _ _

/-- Replayed guarded template 0 for the forward direction of row `22202`. -/
def row22202ForwardTemplate0 :
    ContextualPathTemplate profile222 row22202Start row22202Finish where
  moves := [⟨.cba, .flip maskTerm(inversePermProfile .cba profile222, 1, 1, 1) maskTerm(inversePermProfile .cba profile222, 3, 2, 1) maskTerm(inversePermProfile .cba profile222, 2, 1, 1) maskTerm(inversePermProfile .cba profile222, 3, 3, 1)⟩,
    ⟨.abc, .split maskTerm(inversePermProfile .abc profile222, 1, 3, 3) maskTerm(inversePermProfile .abc profile222, 2, 3, 3) maskTerm(inversePermProfile .abc profile222, 3, 3, 3)⟩]
  present := ∅
  absent := {maskTerm(profile222, 1, 3, 3)}
  support_eq := by decide
  replay := by
    have hstart : row22202Start ∪ ∅ = {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 2, 3)} := by
      unfold row22202Start
      decide
    have hfinish : row22202Finish ∪ ∅ = {maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 2, 3, 3), maskTerm(profile222, 3, 3, 3)} := by
      unfold row22202Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.cba, .flip maskTerm(inversePermProfile .cba profile222, 1, 1, 1) maskTerm(inversePermProfile .cba profile222, 3, 2, 1) maskTerm(inversePermProfile .cba profile222, 2, 1, 1) maskTerm(inversePermProfile .cba profile222, 3, 3, 1)⟩ : FixedMoveData profile222).step? {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 2, 3)} = some {maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 1, 3, 3)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile222, 1, 3, 3) maskTerm(inversePermProfile .abc profile222, 2, 3, 3) maskTerm(inversePermProfile .abc profile222, 3, 3, 3)⟩ : FixedMoveData profile222).step? {maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 1, 3, 3)} = some {maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 2, 3, 3), maskTerm(profile222, 3, 3, 3)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, Option.bind_some]

/-- Replayed guarded template 1 for the forward direction of row `22202`. -/
def row22202ForwardTemplate1 :
    ContextualPathTemplate profile222 row22202Start row22202Finish where
  moves := [⟨.abc, .split maskTerm(inversePermProfile .abc profile222, 1, 3, 3) maskTerm(inversePermProfile .abc profile222, 2, 3, 3) maskTerm(inversePermProfile .abc profile222, 3, 3, 3)⟩,
    ⟨.cba, .flip maskTerm(inversePermProfile .cba profile222, 1, 1, 1) maskTerm(inversePermProfile .cba profile222, 3, 2, 1) maskTerm(inversePermProfile .cba profile222, 2, 1, 1) maskTerm(inversePermProfile .cba profile222, 3, 3, 1)⟩]
  present := {maskTerm(profile222, 1, 3, 3)}
  absent := ∅
  support_eq := by decide
  replay := by
    have hstart : row22202Start ∪ {maskTerm(profile222, 1, 3, 3)} = {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 1, 3, 3)} := by
      unfold row22202Start
      decide
    have hfinish : row22202Finish ∪ {maskTerm(profile222, 1, 3, 3)} = {maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 1, 3, 3), maskTerm(profile222, 2, 3, 3), maskTerm(profile222, 3, 3, 3)} := by
      unfold row22202Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile222, 1, 3, 3) maskTerm(inversePermProfile .abc profile222, 2, 3, 3) maskTerm(inversePermProfile .abc profile222, 3, 3, 3)⟩ : FixedMoveData profile222).step? {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 1, 3, 3)} = some {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 2, 3, 3), maskTerm(profile222, 3, 3, 3)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.cba, .flip maskTerm(inversePermProfile .cba profile222, 1, 1, 1) maskTerm(inversePermProfile .cba profile222, 3, 2, 1) maskTerm(inversePermProfile .cba profile222, 2, 1, 1) maskTerm(inversePermProfile .cba profile222, 3, 3, 1)⟩ : FixedMoveData profile222).step? {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 2, 3, 3), maskTerm(profile222, 3, 3, 3)} = some {maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 1, 3, 3), maskTerm(profile222, 2, 3, 3), maskTerm(profile222, 3, 3, 3)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, Option.bind_some]

/-- Total compact decision tree for the forward direction of row `22202`. -/
def row22202ForwardContextualTree :
    ContextualDecisionTree profile222 row22202Start row22202Finish 2 :=
  .branch maskTerm(profile222, 1, 3, 3)
    (.leaf row22202ForwardTemplate0 (by decide))
    (.leaf row22202ForwardTemplate1 (by decide))

/-- Kernel-checked full guard coverage for the forward tree of row `22202`. -/
theorem row22202ForwardContextualTree_valid :
    row22202ForwardContextualTree.Valid ∅ ∅ := by
  unfold row22202ForwardContextualTree
  unfold row22202ForwardTemplate0
  unfold row22202ForwardTemplate1
  simp only [ContextualDecisionTree.Valid]
  repeat' apply And.intro
  all_goals
    intro x hx
    aesop

/-- Executably select actual fixed witnesses for the forward direction of row `22202`. -/
def row22202ForwardContextualMoves (C : State profile222) : List (FixedMoveData profile222) :=
  row22202ForwardContextualTree.selectMoves C

/-- The selected forward witness list for row `22202` replays in every endpoint-disjoint context. -/
theorem run?_row22202ForwardContextualMoves (C : State profile222)
    (hC : Disjoint C (row22202Start ∪ row22202Finish)) :
    run? (C ∪ row22202Start) (row22202ForwardContextualMoves C) =
      some (C ∪ row22202Finish) := by
  exact row22202ForwardContextualTree.selectMoves_run? ∅ ∅
    row22202ForwardContextualTree_valid (Finset.empty_subset C)
    (Finset.disjoint_empty_right C) hC

/-- Compile the selected forward witnesses of row `22202` to an actual dependent move path. -/
def row22202ForwardContextualPath (C : State profile222)
    (hC : Disjoint C (row22202Start ∪ row22202Finish)) :
    MovePath (@AllModeMove profile222) (C ∪ row22202Start) (C ∪ row22202Finish) :=
  row22202ForwardContextualTree.toMovePath
    row22202ForwardContextualTree_valid hC

/-- The compiled forward contextual path for row `22202` has exact length `2`. -/
@[simp] theorem row22202ForwardContextualPath_length (C : State profile222)
    (hC : Disjoint C (row22202Start ∪ row22202Finish)) :
    (row22202ForwardContextualPath C hC).length = 2 := by
  exact ContextualDecisionTree.toMovePath_length _ _ _

/-- Replayed guarded template 0 for the reverse direction of row `22202`. -/
def row22202ReverseTemplate0 :
    ContextualPathTemplate profile222 row22202Finish row22202Start where
  moves := [⟨.abc, .reduction maskTerm(inversePermProfile .abc profile222, 2, 3, 3) maskTerm(inversePermProfile .abc profile222, 3, 3, 3) maskTerm(inversePermProfile .abc profile222, 1, 3, 3)⟩,
    ⟨.cba, .flip maskTerm(inversePermProfile .cba profile222, 2, 1, 1) maskTerm(inversePermProfile .cba profile222, 3, 3, 1) maskTerm(inversePermProfile .cba profile222, 1, 1, 1) maskTerm(inversePermProfile .cba profile222, 3, 2, 1)⟩]
  present := ∅
  absent := {maskTerm(profile222, 1, 3, 3)}
  support_eq := by decide
  replay := by
    have hstart : row22202Finish ∪ ∅ = {maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 2, 3, 3), maskTerm(profile222, 3, 3, 3)} := by
      unfold row22202Finish
      decide
    have hfinish : row22202Start ∪ ∅ = {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 2, 3)} := by
      unfold row22202Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile222, 2, 3, 3) maskTerm(inversePermProfile .abc profile222, 3, 3, 3) maskTerm(inversePermProfile .abc profile222, 1, 3, 3)⟩ : FixedMoveData profile222).step? {maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 2, 3, 3), maskTerm(profile222, 3, 3, 3)} = some {maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 1, 3, 3)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.cba, .flip maskTerm(inversePermProfile .cba profile222, 2, 1, 1) maskTerm(inversePermProfile .cba profile222, 3, 3, 1) maskTerm(inversePermProfile .cba profile222, 1, 1, 1) maskTerm(inversePermProfile .cba profile222, 3, 2, 1)⟩ : FixedMoveData profile222).step? {maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 1, 3, 3)} = some {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 2, 3)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, Option.bind_some]

/-- Replayed guarded template 1 for the reverse direction of row `22202`. -/
def row22202ReverseTemplate1 :
    ContextualPathTemplate profile222 row22202Finish row22202Start where
  moves := [⟨.cba, .flip maskTerm(inversePermProfile .cba profile222, 2, 1, 1) maskTerm(inversePermProfile .cba profile222, 3, 3, 1) maskTerm(inversePermProfile .cba profile222, 1, 1, 1) maskTerm(inversePermProfile .cba profile222, 3, 2, 1)⟩,
    ⟨.abc, .reduction maskTerm(inversePermProfile .abc profile222, 2, 3, 3) maskTerm(inversePermProfile .abc profile222, 3, 3, 3) maskTerm(inversePermProfile .abc profile222, 1, 3, 3)⟩]
  present := {maskTerm(profile222, 1, 3, 3)}
  absent := ∅
  support_eq := by decide
  replay := by
    have hstart : row22202Finish ∪ {maskTerm(profile222, 1, 3, 3)} = {maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 1, 3, 3), maskTerm(profile222, 2, 3, 3), maskTerm(profile222, 3, 3, 3)} := by
      unfold row22202Finish
      decide
    have hfinish : row22202Start ∪ {maskTerm(profile222, 1, 3, 3)} = {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 1, 3, 3)} := by
      unfold row22202Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.cba, .flip maskTerm(inversePermProfile .cba profile222, 2, 1, 1) maskTerm(inversePermProfile .cba profile222, 3, 3, 1) maskTerm(inversePermProfile .cba profile222, 1, 1, 1) maskTerm(inversePermProfile .cba profile222, 3, 2, 1)⟩ : FixedMoveData profile222).step? {maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 1, 3, 3), maskTerm(profile222, 2, 3, 3), maskTerm(profile222, 3, 3, 3)} = some {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 2, 3, 3), maskTerm(profile222, 3, 3, 3)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile222, 2, 3, 3) maskTerm(inversePermProfile .abc profile222, 3, 3, 3) maskTerm(inversePermProfile .abc profile222, 1, 3, 3)⟩ : FixedMoveData profile222).step? {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 2, 3, 3), maskTerm(profile222, 3, 3, 3)} = some {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 1, 3, 3)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, Option.bind_some]

/-- Total compact decision tree for the reverse direction of row `22202`. -/
def row22202ReverseContextualTree :
    ContextualDecisionTree profile222 row22202Finish row22202Start 2 :=
  .branch maskTerm(profile222, 1, 3, 3)
    (.leaf row22202ReverseTemplate0 (by decide))
    (.leaf row22202ReverseTemplate1 (by decide))

/-- Kernel-checked full guard coverage for the reverse tree of row `22202`. -/
theorem row22202ReverseContextualTree_valid :
    row22202ReverseContextualTree.Valid ∅ ∅ := by
  unfold row22202ReverseContextualTree
  unfold row22202ReverseTemplate0
  unfold row22202ReverseTemplate1
  simp only [ContextualDecisionTree.Valid]
  repeat' apply And.intro
  all_goals
    intro x hx
    aesop

/-- Executably select actual fixed witnesses for the reverse direction of row `22202`. -/
def row22202ReverseContextualMoves (C : State profile222) : List (FixedMoveData profile222) :=
  row22202ReverseContextualTree.selectMoves C

/-- The selected reverse witness list for row `22202` replays in every endpoint-disjoint context. -/
theorem run?_row22202ReverseContextualMoves (C : State profile222)
    (hC : Disjoint C (row22202Finish ∪ row22202Start)) :
    run? (C ∪ row22202Finish) (row22202ReverseContextualMoves C) =
      some (C ∪ row22202Start) := by
  exact row22202ReverseContextualTree.selectMoves_run? ∅ ∅
    row22202ReverseContextualTree_valid (Finset.empty_subset C)
    (Finset.disjoint_empty_right C) hC

/-- Compile the selected reverse witnesses of row `22202` to an actual dependent move path. -/
def row22202ReverseContextualPath (C : State profile222)
    (hC : Disjoint C (row22202Finish ∪ row22202Start)) :
    MovePath (@AllModeMove profile222) (C ∪ row22202Finish) (C ∪ row22202Start) :=
  row22202ReverseContextualTree.toMovePath
    row22202ReverseContextualTree_valid hC

/-- The compiled reverse contextual path for row `22202` has exact length `2`. -/
@[simp] theorem row22202ReverseContextualPath_length (C : State profile222)
    (hC : Disjoint C (row22202Finish ∪ row22202Start)) :
    (row22202ReverseContextualPath C hC).length = 2 := by
  exact ContextualDecisionTree.toMovePath_length _ _ _

/-- Replayed guarded template 0 for the forward direction of row `22203`. -/
def row22203ForwardTemplate0 :
    ContextualPathTemplate profile222 row22203Start row22203Finish where
  moves := [⟨.bca, .split maskTerm(inversePermProfile .bca profile222, 1, 1, 1) maskTerm(inversePermProfile .bca profile222, 2, 1, 1) maskTerm(inversePermProfile .bca profile222, 3, 1, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile222, 1, 1, 3) maskTerm(inversePermProfile .bac profile222, 3, 2, 3) maskTerm(inversePermProfile .bac profile222, 2, 1, 3) maskTerm(inversePermProfile .bac profile222, 3, 3, 3)⟩]
  present := ∅
  absent := {maskTerm(profile222, 1, 1, 3)}
  support_eq := by decide
  replay := by
    have hstart : row22203Start ∪ ∅ = {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 2, 3, 3)} := by
      unfold row22203Start
      decide
    have hfinish : row22203Finish ∪ ∅ = {maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 3, 3, 3)} := by
      unfold row22203Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bca, .split maskTerm(inversePermProfile .bca profile222, 1, 1, 1) maskTerm(inversePermProfile .bca profile222, 2, 1, 1) maskTerm(inversePermProfile .bca profile222, 3, 1, 1)⟩ : FixedMoveData profile222).step? {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 2, 3, 3)} = some {maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 1, 1, 3), maskTerm(profile222, 2, 3, 3)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile222, 1, 1, 3) maskTerm(inversePermProfile .bac profile222, 3, 2, 3) maskTerm(inversePermProfile .bac profile222, 2, 1, 3) maskTerm(inversePermProfile .bac profile222, 3, 3, 3)⟩ : FixedMoveData profile222).step? {maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 1, 1, 3), maskTerm(profile222, 2, 3, 3)} = some {maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 3, 3, 3)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, Option.bind_some]

/-- Replayed guarded template 1 for the forward direction of row `22203`. -/
def row22203ForwardTemplate1 :
    ContextualPathTemplate profile222 row22203Start row22203Finish where
  moves := [⟨.bac, .flip maskTerm(inversePermProfile .bac profile222, 1, 1, 3) maskTerm(inversePermProfile .bac profile222, 3, 2, 3) maskTerm(inversePermProfile .bac profile222, 2, 1, 3) maskTerm(inversePermProfile .bac profile222, 3, 3, 3)⟩,
    ⟨.bca, .split maskTerm(inversePermProfile .bca profile222, 1, 1, 1) maskTerm(inversePermProfile .bca profile222, 2, 1, 1) maskTerm(inversePermProfile .bca profile222, 3, 1, 1)⟩]
  present := {maskTerm(profile222, 1, 1, 3)}
  absent := ∅
  support_eq := by decide
  replay := by
    have hstart : row22203Start ∪ {maskTerm(profile222, 1, 1, 3)} = {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 1, 3), maskTerm(profile222, 2, 3, 3)} := by
      unfold row22203Start
      decide
    have hfinish : row22203Finish ∪ {maskTerm(profile222, 1, 1, 3)} = {maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 1, 1, 3), maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 3, 3, 3)} := by
      unfold row22203Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile222, 1, 1, 3) maskTerm(inversePermProfile .bac profile222, 3, 2, 3) maskTerm(inversePermProfile .bac profile222, 2, 1, 3) maskTerm(inversePermProfile .bac profile222, 3, 3, 3)⟩ : FixedMoveData profile222).step? {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 1, 3), maskTerm(profile222, 2, 3, 3)} = some {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 3, 3, 3)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bca, .split maskTerm(inversePermProfile .bca profile222, 1, 1, 1) maskTerm(inversePermProfile .bca profile222, 2, 1, 1) maskTerm(inversePermProfile .bca profile222, 3, 1, 1)⟩ : FixedMoveData profile222).step? {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 3, 3, 3)} = some {maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 1, 1, 3), maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 3, 3, 3)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, Option.bind_some]

/-- Total compact decision tree for the forward direction of row `22203`. -/
def row22203ForwardContextualTree :
    ContextualDecisionTree profile222 row22203Start row22203Finish 2 :=
  .branch maskTerm(profile222, 1, 1, 3)
    (.leaf row22203ForwardTemplate0 (by decide))
    (.leaf row22203ForwardTemplate1 (by decide))

/-- Kernel-checked full guard coverage for the forward tree of row `22203`. -/
theorem row22203ForwardContextualTree_valid :
    row22203ForwardContextualTree.Valid ∅ ∅ := by
  unfold row22203ForwardContextualTree
  unfold row22203ForwardTemplate0
  unfold row22203ForwardTemplate1
  simp only [ContextualDecisionTree.Valid]
  repeat' apply And.intro
  all_goals
    intro x hx
    aesop

/-- Executably select actual fixed witnesses for the forward direction of row `22203`. -/
def row22203ForwardContextualMoves (C : State profile222) : List (FixedMoveData profile222) :=
  row22203ForwardContextualTree.selectMoves C

/-- The selected forward witness list for row `22203` replays in every endpoint-disjoint context. -/
theorem run?_row22203ForwardContextualMoves (C : State profile222)
    (hC : Disjoint C (row22203Start ∪ row22203Finish)) :
    run? (C ∪ row22203Start) (row22203ForwardContextualMoves C) =
      some (C ∪ row22203Finish) := by
  exact row22203ForwardContextualTree.selectMoves_run? ∅ ∅
    row22203ForwardContextualTree_valid (Finset.empty_subset C)
    (Finset.disjoint_empty_right C) hC

/-- Compile the selected forward witnesses of row `22203` to an actual dependent move path. -/
def row22203ForwardContextualPath (C : State profile222)
    (hC : Disjoint C (row22203Start ∪ row22203Finish)) :
    MovePath (@AllModeMove profile222) (C ∪ row22203Start) (C ∪ row22203Finish) :=
  row22203ForwardContextualTree.toMovePath
    row22203ForwardContextualTree_valid hC

/-- The compiled forward contextual path for row `22203` has exact length `2`. -/
@[simp] theorem row22203ForwardContextualPath_length (C : State profile222)
    (hC : Disjoint C (row22203Start ∪ row22203Finish)) :
    (row22203ForwardContextualPath C hC).length = 2 := by
  exact ContextualDecisionTree.toMovePath_length _ _ _

/-- Replayed guarded template 0 for the reverse direction of row `22203`. -/
def row22203ReverseTemplate0 :
    ContextualPathTemplate profile222 row22203Finish row22203Start where
  moves := [⟨.bac, .flip maskTerm(inversePermProfile .bac profile222, 2, 1, 3) maskTerm(inversePermProfile .bac profile222, 3, 3, 3) maskTerm(inversePermProfile .bac profile222, 1, 1, 3) maskTerm(inversePermProfile .bac profile222, 3, 2, 3)⟩,
    ⟨.bca, .reduction maskTerm(inversePermProfile .bca profile222, 2, 1, 1) maskTerm(inversePermProfile .bca profile222, 3, 1, 1) maskTerm(inversePermProfile .bca profile222, 1, 1, 1)⟩]
  present := ∅
  absent := {maskTerm(profile222, 1, 1, 3)}
  support_eq := by decide
  replay := by
    have hstart : row22203Finish ∪ ∅ = {maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 3, 3, 3)} := by
      unfold row22203Finish
      decide
    have hfinish : row22203Start ∪ ∅ = {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 2, 3, 3)} := by
      unfold row22203Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile222, 2, 1, 3) maskTerm(inversePermProfile .bac profile222, 3, 3, 3) maskTerm(inversePermProfile .bac profile222, 1, 1, 3) maskTerm(inversePermProfile .bac profile222, 3, 2, 3)⟩ : FixedMoveData profile222).step? {maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 3, 3, 3)} = some {maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 1, 1, 3), maskTerm(profile222, 2, 3, 3)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bca, .reduction maskTerm(inversePermProfile .bca profile222, 2, 1, 1) maskTerm(inversePermProfile .bca profile222, 3, 1, 1) maskTerm(inversePermProfile .bca profile222, 1, 1, 1)⟩ : FixedMoveData profile222).step? {maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 1, 1, 3), maskTerm(profile222, 2, 3, 3)} = some {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 2, 3, 3)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, Option.bind_some]

/-- Replayed guarded template 1 for the reverse direction of row `22203`. -/
def row22203ReverseTemplate1 :
    ContextualPathTemplate profile222 row22203Finish row22203Start where
  moves := [⟨.bca, .reduction maskTerm(inversePermProfile .bca profile222, 2, 1, 1) maskTerm(inversePermProfile .bca profile222, 3, 1, 1) maskTerm(inversePermProfile .bca profile222, 1, 1, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile222, 2, 1, 3) maskTerm(inversePermProfile .bac profile222, 3, 3, 3) maskTerm(inversePermProfile .bac profile222, 1, 1, 3) maskTerm(inversePermProfile .bac profile222, 3, 2, 3)⟩]
  present := {maskTerm(profile222, 1, 1, 3)}
  absent := ∅
  support_eq := by decide
  replay := by
    have hstart : row22203Finish ∪ {maskTerm(profile222, 1, 1, 3)} = {maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 1, 1, 3), maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 3, 3, 3)} := by
      unfold row22203Finish
      decide
    have hfinish : row22203Start ∪ {maskTerm(profile222, 1, 1, 3)} = {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 1, 3), maskTerm(profile222, 2, 3, 3)} := by
      unfold row22203Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bca, .reduction maskTerm(inversePermProfile .bca profile222, 2, 1, 1) maskTerm(inversePermProfile .bca profile222, 3, 1, 1) maskTerm(inversePermProfile .bca profile222, 1, 1, 1)⟩ : FixedMoveData profile222).step? {maskTerm(profile222, 1, 1, 2), maskTerm(profile222, 1, 1, 3), maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 3, 3, 3)} = some {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 3, 3, 3)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile222, 2, 1, 3) maskTerm(inversePermProfile .bac profile222, 3, 3, 3) maskTerm(inversePermProfile .bac profile222, 1, 1, 3) maskTerm(inversePermProfile .bac profile222, 3, 2, 3)⟩ : FixedMoveData profile222).step? {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 2, 3), maskTerm(profile222, 3, 3, 3)} = some {maskTerm(profile222, 1, 1, 1), maskTerm(profile222, 1, 1, 3), maskTerm(profile222, 2, 3, 3)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, Option.bind_some]

/-- Total compact decision tree for the reverse direction of row `22203`. -/
def row22203ReverseContextualTree :
    ContextualDecisionTree profile222 row22203Finish row22203Start 2 :=
  .branch maskTerm(profile222, 1, 1, 3)
    (.leaf row22203ReverseTemplate0 (by decide))
    (.leaf row22203ReverseTemplate1 (by decide))

/-- Kernel-checked full guard coverage for the reverse tree of row `22203`. -/
theorem row22203ReverseContextualTree_valid :
    row22203ReverseContextualTree.Valid ∅ ∅ := by
  unfold row22203ReverseContextualTree
  unfold row22203ReverseTemplate0
  unfold row22203ReverseTemplate1
  simp only [ContextualDecisionTree.Valid]
  repeat' apply And.intro
  all_goals
    intro x hx
    aesop

/-- Executably select actual fixed witnesses for the reverse direction of row `22203`. -/
def row22203ReverseContextualMoves (C : State profile222) : List (FixedMoveData profile222) :=
  row22203ReverseContextualTree.selectMoves C

/-- The selected reverse witness list for row `22203` replays in every endpoint-disjoint context. -/
theorem run?_row22203ReverseContextualMoves (C : State profile222)
    (hC : Disjoint C (row22203Finish ∪ row22203Start)) :
    run? (C ∪ row22203Finish) (row22203ReverseContextualMoves C) =
      some (C ∪ row22203Start) := by
  exact row22203ReverseContextualTree.selectMoves_run? ∅ ∅
    row22203ReverseContextualTree_valid (Finset.empty_subset C)
    (Finset.disjoint_empty_right C) hC

/-- Compile the selected reverse witnesses of row `22203` to an actual dependent move path. -/
def row22203ReverseContextualPath (C : State profile222)
    (hC : Disjoint C (row22203Finish ∪ row22203Start)) :
    MovePath (@AllModeMove profile222) (C ∪ row22203Finish) (C ∪ row22203Start) :=
  row22203ReverseContextualTree.toMovePath
    row22203ReverseContextualTree_valid hC

/-- The compiled reverse contextual path for row `22203` has exact length `2`. -/
@[simp] theorem row22203ReverseContextualPath_length (C : State profile222)
    (hC : Disjoint C (row22203Finish ∪ row22203Start)) :
    (row22203ReverseContextualPath C hC).length = 2 := by
  exact ContextualDecisionTree.toMovePath_length _ _ _

end BilinearComplexity.NormalizedBinaryContextualCertificates
