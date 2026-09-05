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

private abbrev stateDecidableEq221 (q : Profile) : DecidableEq (State q) :=
  @Finset.decidableEq (Carrier q) inferInstance

local instance instDecidableEqState221 (q : Profile) : DecidableEq (State q) :=
  stateDecidableEq221 q

local macro "maskTerm(" p:term "," a:num "," b:num "," c:num ")" : term =>
  `(carrierOfMasks $p $a $b $c (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide))

/-- Replayed guarded template 0 for the forward direction of row `22101`. -/
def row22101ForwardTemplate0 :
    ContextualPathTemplate profile221 row22101Start row22101Finish where
  moves := [⟨.bac, .split maskTerm(inversePermProfile .bac profile221, 1, 1, 1) maskTerm(inversePermProfile .bac profile221, 2, 1, 1) maskTerm(inversePermProfile .bac profile221, 3, 1, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile221, 2, 2, 1) maskTerm(inversePermProfile .bac profile221, 3, 1, 1) maskTerm(inversePermProfile .bac profile221, 1, 2, 1) maskTerm(inversePermProfile .bac profile221, 3, 3, 1)⟩]
  present := ∅
  absent := {maskTerm(profile221, 1, 3, 1)}
  support_eq := by decide
  replay := by
    have hstart : row22101Start ∪ ∅ = {maskTerm(profile221, 1, 1, 1), maskTerm(profile221, 2, 2, 1)} := by
      unfold row22101Start
      decide
    have hfinish : row22101Finish ∪ ∅ = {maskTerm(profile221, 1, 2, 1), maskTerm(profile221, 2, 1, 1), maskTerm(profile221, 3, 3, 1)} := by
      unfold row22101Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .split maskTerm(inversePermProfile .bac profile221, 1, 1, 1) maskTerm(inversePermProfile .bac profile221, 2, 1, 1) maskTerm(inversePermProfile .bac profile221, 3, 1, 1)⟩ : FixedMoveData profile221).step? {maskTerm(profile221, 1, 1, 1), maskTerm(profile221, 2, 2, 1)} = some {maskTerm(profile221, 1, 2, 1), maskTerm(profile221, 1, 3, 1), maskTerm(profile221, 2, 2, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile221, 2, 2, 1) maskTerm(inversePermProfile .bac profile221, 3, 1, 1) maskTerm(inversePermProfile .bac profile221, 1, 2, 1) maskTerm(inversePermProfile .bac profile221, 3, 3, 1)⟩ : FixedMoveData profile221).step? {maskTerm(profile221, 1, 2, 1), maskTerm(profile221, 1, 3, 1), maskTerm(profile221, 2, 2, 1)} = some {maskTerm(profile221, 1, 2, 1), maskTerm(profile221, 2, 1, 1), maskTerm(profile221, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, Option.bind_some]

/-- Replayed guarded template 1 for the forward direction of row `22101`. -/
def row22101ForwardTemplate1 :
    ContextualPathTemplate profile221 row22101Start row22101Finish where
  moves := [⟨.bac, .flip maskTerm(inversePermProfile .bac profile221, 2, 2, 1) maskTerm(inversePermProfile .bac profile221, 3, 1, 1) maskTerm(inversePermProfile .bac profile221, 1, 2, 1) maskTerm(inversePermProfile .bac profile221, 3, 3, 1)⟩,
    ⟨.bac, .split maskTerm(inversePermProfile .bac profile221, 1, 1, 1) maskTerm(inversePermProfile .bac profile221, 2, 1, 1) maskTerm(inversePermProfile .bac profile221, 3, 1, 1)⟩]
  present := {maskTerm(profile221, 1, 3, 1)}
  absent := ∅
  support_eq := by decide
  replay := by
    have hstart : row22101Start ∪ {maskTerm(profile221, 1, 3, 1)} = {maskTerm(profile221, 1, 1, 1), maskTerm(profile221, 1, 3, 1), maskTerm(profile221, 2, 2, 1)} := by
      unfold row22101Start
      decide
    have hfinish : row22101Finish ∪ {maskTerm(profile221, 1, 3, 1)} = {maskTerm(profile221, 1, 2, 1), maskTerm(profile221, 1, 3, 1), maskTerm(profile221, 2, 1, 1), maskTerm(profile221, 3, 3, 1)} := by
      unfold row22101Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile221, 2, 2, 1) maskTerm(inversePermProfile .bac profile221, 3, 1, 1) maskTerm(inversePermProfile .bac profile221, 1, 2, 1) maskTerm(inversePermProfile .bac profile221, 3, 3, 1)⟩ : FixedMoveData profile221).step? {maskTerm(profile221, 1, 1, 1), maskTerm(profile221, 1, 3, 1), maskTerm(profile221, 2, 2, 1)} = some {maskTerm(profile221, 1, 1, 1), maskTerm(profile221, 2, 1, 1), maskTerm(profile221, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .split maskTerm(inversePermProfile .bac profile221, 1, 1, 1) maskTerm(inversePermProfile .bac profile221, 2, 1, 1) maskTerm(inversePermProfile .bac profile221, 3, 1, 1)⟩ : FixedMoveData profile221).step? {maskTerm(profile221, 1, 1, 1), maskTerm(profile221, 2, 1, 1), maskTerm(profile221, 3, 3, 1)} = some {maskTerm(profile221, 1, 2, 1), maskTerm(profile221, 1, 3, 1), maskTerm(profile221, 2, 1, 1), maskTerm(profile221, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, Option.bind_some]

/-- Total compact decision tree for the forward direction of row `22101`. -/
def row22101ForwardContextualTree :
    ContextualDecisionTree profile221 row22101Start row22101Finish 2 :=
  .branch maskTerm(profile221, 1, 3, 1)
    (.leaf row22101ForwardTemplate0 (by decide))
    (.leaf row22101ForwardTemplate1 (by decide))

/-- Kernel-checked full guard coverage for the forward tree of row `22101`. -/
theorem row22101ForwardContextualTree_valid :
    row22101ForwardContextualTree.Valid ∅ ∅ := by
  unfold row22101ForwardContextualTree
  unfold row22101ForwardTemplate0
  unfold row22101ForwardTemplate1
  simp only [ContextualDecisionTree.Valid]
  repeat' apply And.intro
  all_goals
    intro x hx
    aesop

/-- Executably select actual fixed witnesses for the forward direction of row `22101`. -/
def row22101ForwardContextualMoves (C : State profile221) : List (FixedMoveData profile221) :=
  row22101ForwardContextualTree.selectMoves C

/-- The selected forward witness list for row `22101` replays in every endpoint-disjoint context. -/
theorem run?_row22101ForwardContextualMoves (C : State profile221)
    (hC : Disjoint C (row22101Start ∪ row22101Finish)) :
    run? (C ∪ row22101Start) (row22101ForwardContextualMoves C) =
      some (C ∪ row22101Finish) := by
  exact row22101ForwardContextualTree.selectMoves_run? ∅ ∅
    row22101ForwardContextualTree_valid (Finset.empty_subset C)
    (Finset.disjoint_empty_right C) hC

/-- Compile the selected forward witnesses of row `22101` to an actual dependent move path. -/
def row22101ForwardContextualPath (C : State profile221)
    (hC : Disjoint C (row22101Start ∪ row22101Finish)) :
    MovePath (@AllModeMove profile221) (C ∪ row22101Start) (C ∪ row22101Finish) :=
  row22101ForwardContextualTree.toMovePath
    row22101ForwardContextualTree_valid hC

/-- The compiled forward contextual path for row `22101` has exact length `2`. -/
@[simp] theorem row22101ForwardContextualPath_length (C : State profile221)
    (hC : Disjoint C (row22101Start ∪ row22101Finish)) :
    (row22101ForwardContextualPath C hC).length = 2 := by
  exact ContextualDecisionTree.toMovePath_length _ _ _

/-- Replayed guarded template 0 for the reverse direction of row `22101`. -/
def row22101ReverseTemplate0 :
    ContextualPathTemplate profile221 row22101Finish row22101Start where
  moves := [⟨.bac, .flip maskTerm(inversePermProfile .bac profile221, 1, 2, 1) maskTerm(inversePermProfile .bac profile221, 3, 3, 1) maskTerm(inversePermProfile .bac profile221, 2, 2, 1) maskTerm(inversePermProfile .bac profile221, 3, 1, 1)⟩,
    ⟨.bac, .reduction maskTerm(inversePermProfile .bac profile221, 2, 1, 1) maskTerm(inversePermProfile .bac profile221, 3, 1, 1) maskTerm(inversePermProfile .bac profile221, 1, 1, 1)⟩]
  present := ∅
  absent := {maskTerm(profile221, 1, 3, 1)}
  support_eq := by decide
  replay := by
    have hstart : row22101Finish ∪ ∅ = {maskTerm(profile221, 1, 2, 1), maskTerm(profile221, 2, 1, 1), maskTerm(profile221, 3, 3, 1)} := by
      unfold row22101Finish
      decide
    have hfinish : row22101Start ∪ ∅ = {maskTerm(profile221, 1, 1, 1), maskTerm(profile221, 2, 2, 1)} := by
      unfold row22101Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile221, 1, 2, 1) maskTerm(inversePermProfile .bac profile221, 3, 3, 1) maskTerm(inversePermProfile .bac profile221, 2, 2, 1) maskTerm(inversePermProfile .bac profile221, 3, 1, 1)⟩ : FixedMoveData profile221).step? {maskTerm(profile221, 1, 2, 1), maskTerm(profile221, 2, 1, 1), maskTerm(profile221, 3, 3, 1)} = some {maskTerm(profile221, 1, 2, 1), maskTerm(profile221, 1, 3, 1), maskTerm(profile221, 2, 2, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .reduction maskTerm(inversePermProfile .bac profile221, 2, 1, 1) maskTerm(inversePermProfile .bac profile221, 3, 1, 1) maskTerm(inversePermProfile .bac profile221, 1, 1, 1)⟩ : FixedMoveData profile221).step? {maskTerm(profile221, 1, 2, 1), maskTerm(profile221, 1, 3, 1), maskTerm(profile221, 2, 2, 1)} = some {maskTerm(profile221, 1, 1, 1), maskTerm(profile221, 2, 2, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, Option.bind_some]

/-- Replayed guarded template 1 for the reverse direction of row `22101`. -/
def row22101ReverseTemplate1 :
    ContextualPathTemplate profile221 row22101Finish row22101Start where
  moves := [⟨.bac, .reduction maskTerm(inversePermProfile .bac profile221, 2, 1, 1) maskTerm(inversePermProfile .bac profile221, 3, 1, 1) maskTerm(inversePermProfile .bac profile221, 1, 1, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile221, 1, 2, 1) maskTerm(inversePermProfile .bac profile221, 3, 3, 1) maskTerm(inversePermProfile .bac profile221, 2, 2, 1) maskTerm(inversePermProfile .bac profile221, 3, 1, 1)⟩]
  present := {maskTerm(profile221, 1, 3, 1)}
  absent := ∅
  support_eq := by decide
  replay := by
    have hstart : row22101Finish ∪ {maskTerm(profile221, 1, 3, 1)} = {maskTerm(profile221, 1, 2, 1), maskTerm(profile221, 1, 3, 1), maskTerm(profile221, 2, 1, 1), maskTerm(profile221, 3, 3, 1)} := by
      unfold row22101Finish
      decide
    have hfinish : row22101Start ∪ {maskTerm(profile221, 1, 3, 1)} = {maskTerm(profile221, 1, 1, 1), maskTerm(profile221, 1, 3, 1), maskTerm(profile221, 2, 2, 1)} := by
      unfold row22101Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .reduction maskTerm(inversePermProfile .bac profile221, 2, 1, 1) maskTerm(inversePermProfile .bac profile221, 3, 1, 1) maskTerm(inversePermProfile .bac profile221, 1, 1, 1)⟩ : FixedMoveData profile221).step? {maskTerm(profile221, 1, 2, 1), maskTerm(profile221, 1, 3, 1), maskTerm(profile221, 2, 1, 1), maskTerm(profile221, 3, 3, 1)} = some {maskTerm(profile221, 1, 1, 1), maskTerm(profile221, 2, 1, 1), maskTerm(profile221, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile221, 1, 2, 1) maskTerm(inversePermProfile .bac profile221, 3, 3, 1) maskTerm(inversePermProfile .bac profile221, 2, 2, 1) maskTerm(inversePermProfile .bac profile221, 3, 1, 1)⟩ : FixedMoveData profile221).step? {maskTerm(profile221, 1, 1, 1), maskTerm(profile221, 2, 1, 1), maskTerm(profile221, 3, 3, 1)} = some {maskTerm(profile221, 1, 1, 1), maskTerm(profile221, 1, 3, 1), maskTerm(profile221, 2, 2, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, Option.bind_some]

/-- Total compact decision tree for the reverse direction of row `22101`. -/
def row22101ReverseContextualTree :
    ContextualDecisionTree profile221 row22101Finish row22101Start 2 :=
  .branch maskTerm(profile221, 1, 3, 1)
    (.leaf row22101ReverseTemplate0 (by decide))
    (.leaf row22101ReverseTemplate1 (by decide))

/-- Kernel-checked full guard coverage for the reverse tree of row `22101`. -/
theorem row22101ReverseContextualTree_valid :
    row22101ReverseContextualTree.Valid ∅ ∅ := by
  unfold row22101ReverseContextualTree
  unfold row22101ReverseTemplate0
  unfold row22101ReverseTemplate1
  simp only [ContextualDecisionTree.Valid]
  repeat' apply And.intro
  all_goals
    intro x hx
    aesop

/-- Executably select actual fixed witnesses for the reverse direction of row `22101`. -/
def row22101ReverseContextualMoves (C : State profile221) : List (FixedMoveData profile221) :=
  row22101ReverseContextualTree.selectMoves C

/-- The selected reverse witness list for row `22101` replays in every endpoint-disjoint context. -/
theorem run?_row22101ReverseContextualMoves (C : State profile221)
    (hC : Disjoint C (row22101Finish ∪ row22101Start)) :
    run? (C ∪ row22101Finish) (row22101ReverseContextualMoves C) =
      some (C ∪ row22101Start) := by
  exact row22101ReverseContextualTree.selectMoves_run? ∅ ∅
    row22101ReverseContextualTree_valid (Finset.empty_subset C)
    (Finset.disjoint_empty_right C) hC

/-- Compile the selected reverse witnesses of row `22101` to an actual dependent move path. -/
def row22101ReverseContextualPath (C : State profile221)
    (hC : Disjoint C (row22101Finish ∪ row22101Start)) :
    MovePath (@AllModeMove profile221) (C ∪ row22101Finish) (C ∪ row22101Start) :=
  row22101ReverseContextualTree.toMovePath
    row22101ReverseContextualTree_valid hC

/-- The compiled reverse contextual path for row `22101` has exact length `2`. -/
@[simp] theorem row22101ReverseContextualPath_length (C : State profile221)
    (hC : Disjoint C (row22101Finish ∪ row22101Start)) :
    (row22101ReverseContextualPath C hC).length = 2 := by
  exact ContextualDecisionTree.toMovePath_length _ _ _

/-- Replayed guarded template 0 for the forward direction of row `22102`. -/
def row22102ForwardTemplate0 :
    ContextualPathTemplate profile221 row22102Start row22102Finish where
  moves := [⟨.abc, .split maskTerm(inversePermProfile .abc profile221, 1, 1, 1) maskTerm(inversePermProfile .abc profile221, 2, 1, 1) maskTerm(inversePermProfile .abc profile221, 3, 1, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile221, 1, 3, 1) maskTerm(inversePermProfile .bac profile221, 2, 1, 1) maskTerm(inversePermProfile .bac profile221, 3, 3, 1) maskTerm(inversePermProfile .bac profile221, 2, 2, 1)⟩]
  present := ∅
  absent := {maskTerm(profile221, 3, 1, 1)}
  support_eq := by decide
  replay := by
    have hstart : row22102Start ∪ ∅ = {maskTerm(profile221, 1, 1, 1), maskTerm(profile221, 1, 2, 1)} := by
      unfold row22102Start
      decide
    have hfinish : row22102Finish ∪ ∅ = {maskTerm(profile221, 2, 1, 1), maskTerm(profile221, 2, 2, 1), maskTerm(profile221, 3, 3, 1)} := by
      unfold row22102Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile221, 1, 1, 1) maskTerm(inversePermProfile .abc profile221, 2, 1, 1) maskTerm(inversePermProfile .abc profile221, 3, 1, 1)⟩ : FixedMoveData profile221).step? {maskTerm(profile221, 1, 1, 1), maskTerm(profile221, 1, 2, 1)} = some {maskTerm(profile221, 1, 2, 1), maskTerm(profile221, 2, 1, 1), maskTerm(profile221, 3, 1, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile221, 1, 3, 1) maskTerm(inversePermProfile .bac profile221, 2, 1, 1) maskTerm(inversePermProfile .bac profile221, 3, 3, 1) maskTerm(inversePermProfile .bac profile221, 2, 2, 1)⟩ : FixedMoveData profile221).step? {maskTerm(profile221, 1, 2, 1), maskTerm(profile221, 2, 1, 1), maskTerm(profile221, 3, 1, 1)} = some {maskTerm(profile221, 2, 1, 1), maskTerm(profile221, 2, 2, 1), maskTerm(profile221, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, Option.bind_some]

/-- Replayed guarded template 1 for the forward direction of row `22102`. -/
def row22102ForwardTemplate1 :
    ContextualPathTemplate profile221 row22102Start row22102Finish where
  moves := [⟨.bac, .flip maskTerm(inversePermProfile .bac profile221, 1, 3, 1) maskTerm(inversePermProfile .bac profile221, 2, 1, 1) maskTerm(inversePermProfile .bac profile221, 3, 3, 1) maskTerm(inversePermProfile .bac profile221, 2, 2, 1)⟩,
    ⟨.abc, .split maskTerm(inversePermProfile .abc profile221, 1, 1, 1) maskTerm(inversePermProfile .abc profile221, 2, 1, 1) maskTerm(inversePermProfile .abc profile221, 3, 1, 1)⟩]
  present := {maskTerm(profile221, 3, 1, 1)}
  absent := ∅
  support_eq := by decide
  replay := by
    have hstart : row22102Start ∪ {maskTerm(profile221, 3, 1, 1)} = {maskTerm(profile221, 1, 1, 1), maskTerm(profile221, 1, 2, 1), maskTerm(profile221, 3, 1, 1)} := by
      unfold row22102Start
      decide
    have hfinish : row22102Finish ∪ {maskTerm(profile221, 3, 1, 1)} = {maskTerm(profile221, 2, 1, 1), maskTerm(profile221, 2, 2, 1), maskTerm(profile221, 3, 1, 1), maskTerm(profile221, 3, 3, 1)} := by
      unfold row22102Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile221, 1, 3, 1) maskTerm(inversePermProfile .bac profile221, 2, 1, 1) maskTerm(inversePermProfile .bac profile221, 3, 3, 1) maskTerm(inversePermProfile .bac profile221, 2, 2, 1)⟩ : FixedMoveData profile221).step? {maskTerm(profile221, 1, 1, 1), maskTerm(profile221, 1, 2, 1), maskTerm(profile221, 3, 1, 1)} = some {maskTerm(profile221, 1, 1, 1), maskTerm(profile221, 2, 2, 1), maskTerm(profile221, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.abc, .split maskTerm(inversePermProfile .abc profile221, 1, 1, 1) maskTerm(inversePermProfile .abc profile221, 2, 1, 1) maskTerm(inversePermProfile .abc profile221, 3, 1, 1)⟩ : FixedMoveData profile221).step? {maskTerm(profile221, 1, 1, 1), maskTerm(profile221, 2, 2, 1), maskTerm(profile221, 3, 3, 1)} = some {maskTerm(profile221, 2, 1, 1), maskTerm(profile221, 2, 2, 1), maskTerm(profile221, 3, 1, 1), maskTerm(profile221, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, Option.bind_some]

/-- Total compact decision tree for the forward direction of row `22102`. -/
def row22102ForwardContextualTree :
    ContextualDecisionTree profile221 row22102Start row22102Finish 2 :=
  .branch maskTerm(profile221, 3, 1, 1)
    (.leaf row22102ForwardTemplate0 (by decide))
    (.leaf row22102ForwardTemplate1 (by decide))

/-- Kernel-checked full guard coverage for the forward tree of row `22102`. -/
theorem row22102ForwardContextualTree_valid :
    row22102ForwardContextualTree.Valid ∅ ∅ := by
  unfold row22102ForwardContextualTree
  unfold row22102ForwardTemplate0
  unfold row22102ForwardTemplate1
  simp only [ContextualDecisionTree.Valid]
  repeat' apply And.intro
  all_goals
    intro x hx
    aesop

/-- Executably select actual fixed witnesses for the forward direction of row `22102`. -/
def row22102ForwardContextualMoves (C : State profile221) : List (FixedMoveData profile221) :=
  row22102ForwardContextualTree.selectMoves C

/-- The selected forward witness list for row `22102` replays in every endpoint-disjoint context. -/
theorem run?_row22102ForwardContextualMoves (C : State profile221)
    (hC : Disjoint C (row22102Start ∪ row22102Finish)) :
    run? (C ∪ row22102Start) (row22102ForwardContextualMoves C) =
      some (C ∪ row22102Finish) := by
  exact row22102ForwardContextualTree.selectMoves_run? ∅ ∅
    row22102ForwardContextualTree_valid (Finset.empty_subset C)
    (Finset.disjoint_empty_right C) hC

/-- Compile the selected forward witnesses of row `22102` to an actual dependent move path. -/
def row22102ForwardContextualPath (C : State profile221)
    (hC : Disjoint C (row22102Start ∪ row22102Finish)) :
    MovePath (@AllModeMove profile221) (C ∪ row22102Start) (C ∪ row22102Finish) :=
  row22102ForwardContextualTree.toMovePath
    row22102ForwardContextualTree_valid hC

/-- The compiled forward contextual path for row `22102` has exact length `2`. -/
@[simp] theorem row22102ForwardContextualPath_length (C : State profile221)
    (hC : Disjoint C (row22102Start ∪ row22102Finish)) :
    (row22102ForwardContextualPath C hC).length = 2 := by
  exact ContextualDecisionTree.toMovePath_length _ _ _

/-- Replayed guarded template 0 for the reverse direction of row `22102`. -/
def row22102ReverseTemplate0 :
    ContextualPathTemplate profile221 row22102Finish row22102Start where
  moves := [⟨.bac, .flip maskTerm(inversePermProfile .bac profile221, 3, 3, 1) maskTerm(inversePermProfile .bac profile221, 2, 2, 1) maskTerm(inversePermProfile .bac profile221, 1, 3, 1) maskTerm(inversePermProfile .bac profile221, 2, 1, 1)⟩,
    ⟨.abc, .reduction maskTerm(inversePermProfile .abc profile221, 2, 1, 1) maskTerm(inversePermProfile .abc profile221, 3, 1, 1) maskTerm(inversePermProfile .abc profile221, 1, 1, 1)⟩]
  present := ∅
  absent := {maskTerm(profile221, 3, 1, 1)}
  support_eq := by decide
  replay := by
    have hstart : row22102Finish ∪ ∅ = {maskTerm(profile221, 2, 1, 1), maskTerm(profile221, 2, 2, 1), maskTerm(profile221, 3, 3, 1)} := by
      unfold row22102Finish
      decide
    have hfinish : row22102Start ∪ ∅ = {maskTerm(profile221, 1, 1, 1), maskTerm(profile221, 1, 2, 1)} := by
      unfold row22102Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile221, 3, 3, 1) maskTerm(inversePermProfile .bac profile221, 2, 2, 1) maskTerm(inversePermProfile .bac profile221, 1, 3, 1) maskTerm(inversePermProfile .bac profile221, 2, 1, 1)⟩ : FixedMoveData profile221).step? {maskTerm(profile221, 2, 1, 1), maskTerm(profile221, 2, 2, 1), maskTerm(profile221, 3, 3, 1)} = some {maskTerm(profile221, 1, 2, 1), maskTerm(profile221, 2, 1, 1), maskTerm(profile221, 3, 1, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile221, 2, 1, 1) maskTerm(inversePermProfile .abc profile221, 3, 1, 1) maskTerm(inversePermProfile .abc profile221, 1, 1, 1)⟩ : FixedMoveData profile221).step? {maskTerm(profile221, 1, 2, 1), maskTerm(profile221, 2, 1, 1), maskTerm(profile221, 3, 1, 1)} = some {maskTerm(profile221, 1, 1, 1), maskTerm(profile221, 1, 2, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, Option.bind_some]

/-- Replayed guarded template 1 for the reverse direction of row `22102`. -/
def row22102ReverseTemplate1 :
    ContextualPathTemplate profile221 row22102Finish row22102Start where
  moves := [⟨.abc, .reduction maskTerm(inversePermProfile .abc profile221, 2, 1, 1) maskTerm(inversePermProfile .abc profile221, 3, 1, 1) maskTerm(inversePermProfile .abc profile221, 1, 1, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile221, 3, 3, 1) maskTerm(inversePermProfile .bac profile221, 2, 2, 1) maskTerm(inversePermProfile .bac profile221, 1, 3, 1) maskTerm(inversePermProfile .bac profile221, 2, 1, 1)⟩]
  present := {maskTerm(profile221, 3, 1, 1)}
  absent := ∅
  support_eq := by decide
  replay := by
    have hstart : row22102Finish ∪ {maskTerm(profile221, 3, 1, 1)} = {maskTerm(profile221, 2, 1, 1), maskTerm(profile221, 2, 2, 1), maskTerm(profile221, 3, 1, 1), maskTerm(profile221, 3, 3, 1)} := by
      unfold row22102Finish
      decide
    have hfinish : row22102Start ∪ {maskTerm(profile221, 3, 1, 1)} = {maskTerm(profile221, 1, 1, 1), maskTerm(profile221, 1, 2, 1), maskTerm(profile221, 3, 1, 1)} := by
      unfold row22102Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.abc, .reduction maskTerm(inversePermProfile .abc profile221, 2, 1, 1) maskTerm(inversePermProfile .abc profile221, 3, 1, 1) maskTerm(inversePermProfile .abc profile221, 1, 1, 1)⟩ : FixedMoveData profile221).step? {maskTerm(profile221, 2, 1, 1), maskTerm(profile221, 2, 2, 1), maskTerm(profile221, 3, 1, 1), maskTerm(profile221, 3, 3, 1)} = some {maskTerm(profile221, 1, 1, 1), maskTerm(profile221, 2, 2, 1), maskTerm(profile221, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile221, 3, 3, 1) maskTerm(inversePermProfile .bac profile221, 2, 2, 1) maskTerm(inversePermProfile .bac profile221, 1, 3, 1) maskTerm(inversePermProfile .bac profile221, 2, 1, 1)⟩ : FixedMoveData profile221).step? {maskTerm(profile221, 1, 1, 1), maskTerm(profile221, 2, 2, 1), maskTerm(profile221, 3, 3, 1)} = some {maskTerm(profile221, 1, 1, 1), maskTerm(profile221, 1, 2, 1), maskTerm(profile221, 3, 1, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, Option.bind_some]

/-- Total compact decision tree for the reverse direction of row `22102`. -/
def row22102ReverseContextualTree :
    ContextualDecisionTree profile221 row22102Finish row22102Start 2 :=
  .branch maskTerm(profile221, 3, 1, 1)
    (.leaf row22102ReverseTemplate0 (by decide))
    (.leaf row22102ReverseTemplate1 (by decide))

/-- Kernel-checked full guard coverage for the reverse tree of row `22102`. -/
theorem row22102ReverseContextualTree_valid :
    row22102ReverseContextualTree.Valid ∅ ∅ := by
  unfold row22102ReverseContextualTree
  unfold row22102ReverseTemplate0
  unfold row22102ReverseTemplate1
  simp only [ContextualDecisionTree.Valid]
  repeat' apply And.intro
  all_goals
    intro x hx
    aesop

/-- Executably select actual fixed witnesses for the reverse direction of row `22102`. -/
def row22102ReverseContextualMoves (C : State profile221) : List (FixedMoveData profile221) :=
  row22102ReverseContextualTree.selectMoves C

/-- The selected reverse witness list for row `22102` replays in every endpoint-disjoint context. -/
theorem run?_row22102ReverseContextualMoves (C : State profile221)
    (hC : Disjoint C (row22102Finish ∪ row22102Start)) :
    run? (C ∪ row22102Finish) (row22102ReverseContextualMoves C) =
      some (C ∪ row22102Start) := by
  exact row22102ReverseContextualTree.selectMoves_run? ∅ ∅
    row22102ReverseContextualTree_valid (Finset.empty_subset C)
    (Finset.disjoint_empty_right C) hC

/-- Compile the selected reverse witnesses of row `22102` to an actual dependent move path. -/
def row22102ReverseContextualPath (C : State profile221)
    (hC : Disjoint C (row22102Finish ∪ row22102Start)) :
    MovePath (@AllModeMove profile221) (C ∪ row22102Finish) (C ∪ row22102Start) :=
  row22102ReverseContextualTree.toMovePath
    row22102ReverseContextualTree_valid hC

/-- The compiled reverse contextual path for row `22102` has exact length `2`. -/
@[simp] theorem row22102ReverseContextualPath_length (C : State profile221)
    (hC : Disjoint C (row22102Finish ∪ row22102Start)) :
    (row22102ReverseContextualPath C hC).length = 2 := by
  exact ContextualDecisionTree.toMovePath_length _ _ _

/-- Replayed guarded template 0 for the forward direction of row `22103`. -/
def row22103ForwardTemplate0 :
    ContextualPathTemplate profile221 row22103Start row22103Finish where
  moves := [⟨.bac, .flip maskTerm(inversePermProfile .bac profile221, 1, 1, 1) maskTerm(inversePermProfile .bac profile221, 3, 3, 1) maskTerm(inversePermProfile .bac profile221, 2, 1, 1) maskTerm(inversePermProfile .bac profile221, 3, 2, 1)⟩,
    ⟨.bac, .split maskTerm(inversePermProfile .bac profile221, 3, 2, 1) maskTerm(inversePermProfile .bac profile221, 1, 2, 1) maskTerm(inversePermProfile .bac profile221, 2, 2, 1)⟩]
  present := ∅
  absent := {maskTerm(profile221, 2, 3, 1)}
  support_eq := by decide
  replay := by
    have hstart : row22103Start ∪ ∅ = {maskTerm(profile221, 1, 1, 1), maskTerm(profile221, 3, 3, 1)} := by
      unfold row22103Start
      decide
    have hfinish : row22103Finish ∪ ∅ = {maskTerm(profile221, 1, 2, 1), maskTerm(profile221, 2, 1, 1), maskTerm(profile221, 2, 2, 1)} := by
      unfold row22103Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile221, 1, 1, 1) maskTerm(inversePermProfile .bac profile221, 3, 3, 1) maskTerm(inversePermProfile .bac profile221, 2, 1, 1) maskTerm(inversePermProfile .bac profile221, 3, 2, 1)⟩ : FixedMoveData profile221).step? {maskTerm(profile221, 1, 1, 1), maskTerm(profile221, 3, 3, 1)} = some {maskTerm(profile221, 1, 2, 1), maskTerm(profile221, 2, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .split maskTerm(inversePermProfile .bac profile221, 3, 2, 1) maskTerm(inversePermProfile .bac profile221, 1, 2, 1) maskTerm(inversePermProfile .bac profile221, 2, 2, 1)⟩ : FixedMoveData profile221).step? {maskTerm(profile221, 1, 2, 1), maskTerm(profile221, 2, 3, 1)} = some {maskTerm(profile221, 1, 2, 1), maskTerm(profile221, 2, 1, 1), maskTerm(profile221, 2, 2, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, Option.bind_some]

/-- Replayed guarded template 1 for the forward direction of row `22103`. -/
def row22103ForwardTemplate1 :
    ContextualPathTemplate profile221 row22103Start row22103Finish where
  moves := [⟨.bac, .split maskTerm(inversePermProfile .bac profile221, 3, 2, 1) maskTerm(inversePermProfile .bac profile221, 1, 2, 1) maskTerm(inversePermProfile .bac profile221, 2, 2, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile221, 1, 1, 1) maskTerm(inversePermProfile .bac profile221, 3, 3, 1) maskTerm(inversePermProfile .bac profile221, 2, 1, 1) maskTerm(inversePermProfile .bac profile221, 3, 2, 1)⟩]
  present := {maskTerm(profile221, 2, 3, 1)}
  absent := ∅
  support_eq := by decide
  replay := by
    have hstart : row22103Start ∪ {maskTerm(profile221, 2, 3, 1)} = {maskTerm(profile221, 1, 1, 1), maskTerm(profile221, 2, 3, 1), maskTerm(profile221, 3, 3, 1)} := by
      unfold row22103Start
      decide
    have hfinish : row22103Finish ∪ {maskTerm(profile221, 2, 3, 1)} = {maskTerm(profile221, 1, 2, 1), maskTerm(profile221, 2, 1, 1), maskTerm(profile221, 2, 2, 1), maskTerm(profile221, 2, 3, 1)} := by
      unfold row22103Finish
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .split maskTerm(inversePermProfile .bac profile221, 3, 2, 1) maskTerm(inversePermProfile .bac profile221, 1, 2, 1) maskTerm(inversePermProfile .bac profile221, 2, 2, 1)⟩ : FixedMoveData profile221).step? {maskTerm(profile221, 1, 1, 1), maskTerm(profile221, 2, 3, 1), maskTerm(profile221, 3, 3, 1)} = some {maskTerm(profile221, 1, 1, 1), maskTerm(profile221, 2, 1, 1), maskTerm(profile221, 2, 2, 1), maskTerm(profile221, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile221, 1, 1, 1) maskTerm(inversePermProfile .bac profile221, 3, 3, 1) maskTerm(inversePermProfile .bac profile221, 2, 1, 1) maskTerm(inversePermProfile .bac profile221, 3, 2, 1)⟩ : FixedMoveData profile221).step? {maskTerm(profile221, 1, 1, 1), maskTerm(profile221, 2, 1, 1), maskTerm(profile221, 2, 2, 1), maskTerm(profile221, 3, 3, 1)} = some {maskTerm(profile221, 1, 2, 1), maskTerm(profile221, 2, 1, 1), maskTerm(profile221, 2, 2, 1), maskTerm(profile221, 2, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, Option.bind_some]

/-- Total compact decision tree for the forward direction of row `22103`. -/
def row22103ForwardContextualTree :
    ContextualDecisionTree profile221 row22103Start row22103Finish 2 :=
  .branch maskTerm(profile221, 2, 3, 1)
    (.leaf row22103ForwardTemplate0 (by decide))
    (.leaf row22103ForwardTemplate1 (by decide))

/-- Kernel-checked full guard coverage for the forward tree of row `22103`. -/
theorem row22103ForwardContextualTree_valid :
    row22103ForwardContextualTree.Valid ∅ ∅ := by
  unfold row22103ForwardContextualTree
  unfold row22103ForwardTemplate0
  unfold row22103ForwardTemplate1
  simp only [ContextualDecisionTree.Valid]
  repeat' apply And.intro
  all_goals
    intro x hx
    aesop

/-- Executably select actual fixed witnesses for the forward direction of row `22103`. -/
def row22103ForwardContextualMoves (C : State profile221) : List (FixedMoveData profile221) :=
  row22103ForwardContextualTree.selectMoves C

/-- The selected forward witness list for row `22103` replays in every endpoint-disjoint context. -/
theorem run?_row22103ForwardContextualMoves (C : State profile221)
    (hC : Disjoint C (row22103Start ∪ row22103Finish)) :
    run? (C ∪ row22103Start) (row22103ForwardContextualMoves C) =
      some (C ∪ row22103Finish) := by
  exact row22103ForwardContextualTree.selectMoves_run? ∅ ∅
    row22103ForwardContextualTree_valid (Finset.empty_subset C)
    (Finset.disjoint_empty_right C) hC

/-- Compile the selected forward witnesses of row `22103` to an actual dependent move path. -/
def row22103ForwardContextualPath (C : State profile221)
    (hC : Disjoint C (row22103Start ∪ row22103Finish)) :
    MovePath (@AllModeMove profile221) (C ∪ row22103Start) (C ∪ row22103Finish) :=
  row22103ForwardContextualTree.toMovePath
    row22103ForwardContextualTree_valid hC

/-- The compiled forward contextual path for row `22103` has exact length `2`. -/
@[simp] theorem row22103ForwardContextualPath_length (C : State profile221)
    (hC : Disjoint C (row22103Start ∪ row22103Finish)) :
    (row22103ForwardContextualPath C hC).length = 2 := by
  exact ContextualDecisionTree.toMovePath_length _ _ _

/-- Replayed guarded template 0 for the reverse direction of row `22103`. -/
def row22103ReverseTemplate0 :
    ContextualPathTemplate profile221 row22103Finish row22103Start where
  moves := [⟨.bac, .reduction maskTerm(inversePermProfile .bac profile221, 1, 2, 1) maskTerm(inversePermProfile .bac profile221, 2, 2, 1) maskTerm(inversePermProfile .bac profile221, 3, 2, 1)⟩,
    ⟨.bac, .flip maskTerm(inversePermProfile .bac profile221, 2, 1, 1) maskTerm(inversePermProfile .bac profile221, 3, 2, 1) maskTerm(inversePermProfile .bac profile221, 1, 1, 1) maskTerm(inversePermProfile .bac profile221, 3, 3, 1)⟩]
  present := ∅
  absent := {maskTerm(profile221, 2, 3, 1)}
  support_eq := by decide
  replay := by
    have hstart : row22103Finish ∪ ∅ = {maskTerm(profile221, 1, 2, 1), maskTerm(profile221, 2, 1, 1), maskTerm(profile221, 2, 2, 1)} := by
      unfold row22103Finish
      decide
    have hfinish : row22103Start ∪ ∅ = {maskTerm(profile221, 1, 1, 1), maskTerm(profile221, 3, 3, 1)} := by
      unfold row22103Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .reduction maskTerm(inversePermProfile .bac profile221, 1, 2, 1) maskTerm(inversePermProfile .bac profile221, 2, 2, 1) maskTerm(inversePermProfile .bac profile221, 3, 2, 1)⟩ : FixedMoveData profile221).step? {maskTerm(profile221, 1, 2, 1), maskTerm(profile221, 2, 1, 1), maskTerm(profile221, 2, 2, 1)} = some {maskTerm(profile221, 1, 2, 1), maskTerm(profile221, 2, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile221, 2, 1, 1) maskTerm(inversePermProfile .bac profile221, 3, 2, 1) maskTerm(inversePermProfile .bac profile221, 1, 1, 1) maskTerm(inversePermProfile .bac profile221, 3, 3, 1)⟩ : FixedMoveData profile221).step? {maskTerm(profile221, 1, 2, 1), maskTerm(profile221, 2, 3, 1)} = some {maskTerm(profile221, 1, 1, 1), maskTerm(profile221, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, Option.bind_some]

/-- Replayed guarded template 1 for the reverse direction of row `22103`. -/
def row22103ReverseTemplate1 :
    ContextualPathTemplate profile221 row22103Finish row22103Start where
  moves := [⟨.bac, .flip maskTerm(inversePermProfile .bac profile221, 2, 1, 1) maskTerm(inversePermProfile .bac profile221, 3, 2, 1) maskTerm(inversePermProfile .bac profile221, 1, 1, 1) maskTerm(inversePermProfile .bac profile221, 3, 3, 1)⟩,
    ⟨.bac, .reduction maskTerm(inversePermProfile .bac profile221, 1, 2, 1) maskTerm(inversePermProfile .bac profile221, 2, 2, 1) maskTerm(inversePermProfile .bac profile221, 3, 2, 1)⟩]
  present := {maskTerm(profile221, 2, 3, 1)}
  absent := ∅
  support_eq := by decide
  replay := by
    have hstart : row22103Finish ∪ {maskTerm(profile221, 2, 3, 1)} = {maskTerm(profile221, 1, 2, 1), maskTerm(profile221, 2, 1, 1), maskTerm(profile221, 2, 2, 1), maskTerm(profile221, 2, 3, 1)} := by
      unfold row22103Finish
      decide
    have hfinish : row22103Start ∪ {maskTerm(profile221, 2, 3, 1)} = {maskTerm(profile221, 1, 1, 1), maskTerm(profile221, 2, 3, 1), maskTerm(profile221, 3, 3, 1)} := by
      unfold row22103Start
      decide
    rw [hstart, hfinish]
    have hstep0 : (⟨.bac, .flip maskTerm(inversePermProfile .bac profile221, 2, 1, 1) maskTerm(inversePermProfile .bac profile221, 3, 2, 1) maskTerm(inversePermProfile .bac profile221, 1, 1, 1) maskTerm(inversePermProfile .bac profile221, 3, 3, 1)⟩ : FixedMoveData profile221).step? {maskTerm(profile221, 1, 2, 1), maskTerm(profile221, 2, 1, 1), maskTerm(profile221, 2, 2, 1), maskTerm(profile221, 2, 3, 1)} = some {maskTerm(profile221, 1, 1, 1), maskTerm(profile221, 2, 1, 1), maskTerm(profile221, 2, 2, 1), maskTerm(profile221, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    have hstep1 : (⟨.bac, .reduction maskTerm(inversePermProfile .bac profile221, 1, 2, 1) maskTerm(inversePermProfile .bac profile221, 2, 2, 1) maskTerm(inversePermProfile .bac profile221, 3, 2, 1)⟩ : FixedMoveData profile221).step? {maskTerm(profile221, 1, 1, 1), maskTerm(profile221, 2, 1, 1), maskTerm(profile221, 2, 2, 1), maskTerm(profile221, 3, 3, 1)} = some {maskTerm(profile221, 1, 1, 1), maskTerm(profile221, 2, 3, 1), maskTerm(profile221, 3, 3, 1)} := by
      apply FixedMoveData.step?_eq_some_of_source
      · simp only [SourceMoveData.Legal]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals decide
      · decide
    simp only [run?, hstep0, hstep1, Option.bind_some]

/-- Total compact decision tree for the reverse direction of row `22103`. -/
def row22103ReverseContextualTree :
    ContextualDecisionTree profile221 row22103Finish row22103Start 2 :=
  .branch maskTerm(profile221, 2, 3, 1)
    (.leaf row22103ReverseTemplate0 (by decide))
    (.leaf row22103ReverseTemplate1 (by decide))

/-- Kernel-checked full guard coverage for the reverse tree of row `22103`. -/
theorem row22103ReverseContextualTree_valid :
    row22103ReverseContextualTree.Valid ∅ ∅ := by
  unfold row22103ReverseContextualTree
  unfold row22103ReverseTemplate0
  unfold row22103ReverseTemplate1
  simp only [ContextualDecisionTree.Valid]
  repeat' apply And.intro
  all_goals
    intro x hx
    aesop

/-- Executably select actual fixed witnesses for the reverse direction of row `22103`. -/
def row22103ReverseContextualMoves (C : State profile221) : List (FixedMoveData profile221) :=
  row22103ReverseContextualTree.selectMoves C

/-- The selected reverse witness list for row `22103` replays in every endpoint-disjoint context. -/
theorem run?_row22103ReverseContextualMoves (C : State profile221)
    (hC : Disjoint C (row22103Finish ∪ row22103Start)) :
    run? (C ∪ row22103Finish) (row22103ReverseContextualMoves C) =
      some (C ∪ row22103Start) := by
  exact row22103ReverseContextualTree.selectMoves_run? ∅ ∅
    row22103ReverseContextualTree_valid (Finset.empty_subset C)
    (Finset.disjoint_empty_right C) hC

/-- Compile the selected reverse witnesses of row `22103` to an actual dependent move path. -/
def row22103ReverseContextualPath (C : State profile221)
    (hC : Disjoint C (row22103Finish ∪ row22103Start)) :
    MovePath (@AllModeMove profile221) (C ∪ row22103Finish) (C ∪ row22103Start) :=
  row22103ReverseContextualTree.toMovePath
    row22103ReverseContextualTree_valid hC

/-- The compiled reverse contextual path for row `22103` has exact length `2`. -/
@[simp] theorem row22103ReverseContextualPath_length (C : State profile221)
    (hC : Disjoint C (row22103Finish ∪ row22103Start)) :
    (row22103ReverseContextualPath C hC).length = 2 := by
  exact ContextualDecisionTree.toMovePath_length _ _ _

end BilinearComplexity.NormalizedBinaryContextualCertificates
