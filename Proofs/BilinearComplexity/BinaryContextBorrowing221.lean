import BilinearComplexity.BinaryAmbientCircuitModels
import BilinearComplexity.BinaryAmbientMoveSupport

set_option autoImplicit false

/-!
# Minimal profile-221 context borrowing

This module gives a concrete obstruction to keeping a local context fixed while
replaying a five-circuit relation.  It works in the actual intrinsic coordinate
spaces `CoordinateVector 2`, `CoordinateVector 2`, and `CoordinateVector 1`.
The displayed two-edge native path temporarily borrows `31` from the context,
then restores it.  Circuit minimality proves that no first native edge can
retain the whole context, and hence no path between the displayed endpoints can
retain it at every vertex.
-/

namespace BilinearComplexity.BinaryContextBorrowing221

open scoped symmDiff
open BinaryCircuit
open NormalizedBinaryCarrier
open NormalizedBinaryReplay221
open NormalizedBinaryFiveCircuitRows
open NormalizedBinaryFiveCircuitCertificate
open BinaryAmbientCarrier
open BinaryAmbientMoves
open BinaryAmbientCircuitModels
open BinaryAmbientMoveSupport

/-- A rank-one term in the actual intrinsic profile-`221` coordinate spaces. -/
abbrev Term221 := NormalizedBinaryCarrier.Carrier profile221

/-- A finite-set state in the actual intrinsic profile-`221` coordinate spaces. -/
abbrev State221 := NormalizedBinaryCarrier.State profile221

/-- The intrinsic native all-mode relation in the actual profile-`221` spaces. -/
abbrev NativeMove221 : State221 → State221 → Prop :=
  BinaryAmbientMoves.AllModeMove

/-- The term `13 = (e₁,e₁+e₂,w)` used by the fixed context. -/
def term13 : Term221 := (e1, ep, w)

/-- The term `23 = (e₂,e₁+e₂,w)` used by the fixed context. -/
def term23 : Term221 := (e2, ep, w)

/-- The term `32 = (e₁+e₂,e₂,w)` used by the fixed context. -/
def term32 : Term221 := (ep, e2, w)

/-- The two-term side `A = {11,22}` of the minimal five-circuit. -/
def endpointA : State221 := {E11, E22}

/-- The three-term side `B = {12,21,33}` of the minimal five-circuit. -/
def endpointB : State221 := {E12, E21, J}

/-- The four-term context `C = {13,23,31,32}`. -/
def contextC : State221 := {term13, term23, E31, term32}

/-- The contextual source state `C ∪ A`. -/
def contextualStart : State221 := contextC ∪ endpointA

/-- The full-state intermediate after the Flip `{22,31} → {12,33}`. -/
def borrowingMiddle : State221 := {E11, E12, term13, term23, term32, J}

/-- The contextual target state `C ∪ B`. -/
def contextualFinish : State221 := contextC ∪ endpointB

example : term13 = (e1, ep, w) := rfl
example : term23 = (e2, ep, w) := rfl
example : term32 = (ep, e2, w) := rfl
example : endpointA = row22101Start := by decide
example : endpointB = row22101Finish := by decide
example : contextualStart = contextC ∪ endpointA := rfl
example : borrowingMiddle = {E11, E12, term13, term23, term32, J} := rfl
example : contextualFinish = contextC ∪ endpointB := rfl

/-- The two endpoint sides have cardinalities two and three, the context has
cardinality four, and all three displayed sets are pairwise disjoint. -/
theorem endpoint_context_cardinality_and_disjointness :
    endpointA.card = 2 ∧ endpointB.card = 3 ∧ contextC.card = 4 ∧
      Disjoint endpointA endpointB ∧ Disjoint contextC endpointA ∧
      Disjoint contextC endpointB := by
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The circuit and its context partition the entire nine-term profile-`221`
carrier. -/
theorem context_union_circuit_eq_univ :
    contextC ∪ (endpointA ∪ endpointB) = Finset.univ := by
  decide

/-- The displayed context is exactly the complement of the five-circuit. -/
theorem context_eq_complement_circuit :
    contextC = Finset.univ \ (endpointA ∪ endpointB) := by
  decide

/-- The endpoint union is a genuine circuit for evaluation in the nested
intrinsic tensor product, not merely for a coordinate-array surrogate. -/
theorem endpoint_ambient_circuit :
    Circuit (@BinaryAmbientCarrier.tensorEvaluation
      (CoordinateVector 2) (CoordinateVector 2) (CoordinateVector 1)
      _ _ _ _ _ _) (endpointA ∪ endpointB) := by
  apply (coordinateCircuit_iff_ambientCircuit profile221
    (endpointA ∪ endpointB)).mp
  have hA : endpointA = row22101Start := by decide
  have hB : endpointB = row22101Finish := by decide
  rw [hA, hB]
  exact row22101Certificate.circuit

/-- The first full-state step is the native intrinsic third-mode Flip
`{22,31} → {12,33}`. -/
theorem borrowing_first_flip :
    BinaryAmbientMoves.SourceThirdFlip
      E22 E31 E12 J contextualStart borrowingMiddle := by
  apply BinaryAmbientMoves.Coordinate.sourceThirdFlip_iff.mpr
  unfold NormalizedBinaryReplay221.SourceThirdFlip
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide

/-- The second full-state step is the native intrinsic first-mode Split
`11 → {21,31}`. -/
theorem borrowing_second_split :
    BinaryAmbientMoves.GeneratedFirstSplit
      E11 E21 E31 borrowingMiddle contextualFinish := by
  apply BinaryAmbientMoves.Coordinate.generatedFirstSplit_iff.mpr
  unfold NormalizedBinaryReplay221.GeneratedFirstSplit
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide

/-- The actual two-edge intrinsic full-state path: first Flip
`{22,31} → {12,33}`, then Split `11 → {21,31}`. -/
def borrowingPath :
    MovePath NativeMove221 contextualStart contextualFinish :=
  .snoc
    (.snoc (.singleton contextualStart)
      (.abc (.sourceThirdFlip borrowing_first_flip)))
    (.abc (.generatedFirstSplit borrowing_second_split))

example : Nonempty (MovePath NativeMove221
    contextualStart contextualFinish) :=
  ⟨borrowingPath⟩

/-- The native borrowing path has exactly two edges. -/
@[simp] theorem borrowingPath_length : borrowingPath.length = 2 := by
  simp [borrowingPath, BilinearComplexity.BinaryCircuit.MovePath.length]

/-- The native borrowing path records exactly the source, borrowing
intermediate, and restored target states. -/
@[simp] theorem borrowingPath_vertices :
    borrowingPath.vertices =
      [contextualStart, borrowingMiddle, contextualFinish] := by
  simp [borrowingPath, BilinearComplexity.BinaryCircuit.MovePath.vertices]

/-- The native path has source/intermediate cardinality six and target
cardinality seven, hence exact altitude seven. -/
theorem borrowing_state_cardinalities_and_altitude :
    contextualStart.card = 6 ∧ borrowingMiddle.card = 6 ∧
      contextualFinish.card = 7 ∧ borrowingPath.altitude = 7 := by
  have hStartCard : contextualStart.card = 6 := by decide
  have hMiddleCard : borrowingMiddle.card = 6 := by decide
  have hFinishCard : contextualFinish.card = 7 := by decide
  refine ⟨hStartCard, hMiddleCard, hFinishCard, ?_⟩
  simp only [borrowingPath, BinaryCircuit.MovePath.altitude]
  rw [hStartCard, hMiddleCard, hFinishCard]
  decide

/-- The first edge genuinely borrows the context term `31`, which is absent
from the intermediate state. -/
theorem borrowed_term_absent : E31 ∉ borrowingMiddle := by
  decide

/-- The second edge restores every context term at the final state. -/
theorem context_restored : contextC ⊆ contextualFinish := by
  exact Finset.subset_union_left

private theorem nativeMove221_support_cycle {D E : State221}
    (hMove : NativeMove221 D E) :
    BinaryCycle (@BinaryAmbientCarrier.tensorEvaluation
      (CoordinateVector profile221.first)
      (CoordinateVector profile221.second)
      (CoordinateVector profile221.third) _ _ _ _ _ _) (D ∆ E) := by
  have hNormalizedMove :
      NormalizedBinaryAllModeMove.AllModeMove D E :=
    BinaryAmbientMoves.Coordinate.allModeMove_iff_normalized.mp hMove
  have hNormalizedEvaluation :=
    NormalizedBinaryAllModeMove.AllModeMove.preserves_evaluation
      hNormalizedMove
  have hNormalizedSupport :
      NormalizedBinaryCarrier.stateEvaluation (D ∆ E) = 0 := by
    change BinaryCircuit.evaluation
      (@NormalizedBinaryCarrier.tensorEvaluation profile221) (D ∆ E) = 0
    calc
      BinaryCircuit.evaluation
          (@NormalizedBinaryCarrier.tensorEvaluation profile221) (D ∆ E) =
          NormalizedBinaryCarrier.stateEvaluation D +
            NormalizedBinaryCarrier.stateEvaluation E :=
        BinaryCircuit.evaluation_symmDiff
          (@NormalizedBinaryCarrier.tensorEvaluation profile221) D E
      _ = 0 := by
        rw [hNormalizedEvaluation]
        exact BinaryCircuit.add_self_eq_zero _
  have hAmbientSupport :=
    (coordinate_stateEvaluation_eq_iff_ambientStateEvaluation
      (D ∆ E) (∅ : State221)).mp (by
        simpa only [NormalizedBinaryCarrier.stateEvaluation,
          BinaryCircuit.evaluation, Finset.sum_empty] using hNormalizedSupport)
  rw [BinaryCycle]
  exact hAmbientSupport.trans BinaryAmbientCarrier.stateEvaluation_empty

universe u v

variable {α : Type u} [DecidableEq α]

/-- A five-circuit occupying the complement of a retained context forbids any
three- or four-term zero-evaluation symmetric-difference support. -/
theorem circuit_complement_support_obstruction
    {V : Type v} [AddCommGroup V] [Module F2 V]
    [Fintype α] (value : α → V) (K C D : BinaryCircuit.Scheme α)
    (hCircuit : Circuit value K) (hKcard : K.card = 5)
    (hDK : D ∪ K = Finset.univ) (hOutside : Finset.univ \ K ⊆ C) :
    ¬ ∃ E : BinaryCircuit.Scheme α,
      C ⊆ E ∧
      ((D ∆ E).card = 3 ∨ (D ∆ E).card = 4) ∧
      BinaryCycle value (D ∆ E) := by
  rintro ⟨E, hCE, hSupportCard, hSupportCycle⟩
  have hSupportSubset : D ∆ E ⊆ K := by
    intro x hxSupport
    by_contra hxK
    have hxDK : x ∈ D ∪ K := by
      rw [hDK]
      exact Finset.mem_univ x
    have hxD : x ∈ D := (Finset.mem_union.mp hxDK).resolve_right hxK
    have hxOutside : x ∈ Finset.univ \ K :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxK⟩
    have hxE : x ∈ E := hCE (hOutside hxOutside)
    rw [Finset.mem_symmDiff] at hxSupport
    rcases hxSupport with hDE | hED
    · exact hDE.2 hxE
    · exact hED.2 hxD
  have hSupportNonempty : (D ∆ E).Nonempty := by
    apply Finset.card_pos.mp
    rcases hSupportCard with hCard | hCard <;> omega
  have hSupportNe : D ∆ E ≠ K := by
    intro hEq
    rw [hEq, hKcard] at hSupportCard
    omega
  have hSupportProper : D ∆ E ⊂ K :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hSupportSubset, hSupportNe⟩
  exact hCircuit.2.2 (D ∆ E) hSupportProper hSupportNonempty hSupportCycle

/-- In the intrinsic minimal profile-`221` carrier, no native first edge from
`C ∪ A` can retain all four terms of `C`.  This statement is deliberately not
asserted after embedding the configuration into a larger ambient carrier. -/
theorem no_first_native_move_retains_context {E : State221}
    (hMove : NativeMove221 contextualStart E) :
    ¬ contextC ⊆ E := by
  intro hContext
  have hCoordinateCircuit :
      Circuit (@NormalizedBinaryCarrier.tensorEvaluation profile221)
        (endpointA ∪ endpointB) := by
    have hA : endpointA = row22101Start := by decide
    have hB : endpointB = row22101Finish := by decide
    rw [hA, hB]
    exact row22101Certificate.circuit
  have hProfileCircuit :
      Circuit (@BinaryAmbientCarrier.tensorEvaluation
        (CoordinateVector profile221.first)
        (CoordinateVector profile221.second)
        (CoordinateVector profile221.third) _ _ _ _ _ _)
        (endpointA ∪ endpointB) :=
    (coordinateCircuit_iff_ambientCircuit profile221
      (endpointA ∪ endpointB)).mp hCoordinateCircuit
  have hOutside : Finset.univ \ (endpointA ∪ endpointB) ⊆ contextC := by
    simpa only [context_eq_complement_circuit] using
      (Finset.Subset.rfl :
        Finset.univ \ (endpointA ∪ endpointB) ⊆
          Finset.univ \ (endpointA ∪ endpointB))
  have hObstruction := circuit_complement_support_obstruction
    (@BinaryAmbientCarrier.tensorEvaluation
      (CoordinateVector profile221.first)
      (CoordinateVector profile221.second)
      (CoordinateVector profile221.third) _ _ _ _ _ _)
    (endpointA ∪ endpointB) contextC contextualStart
    hProfileCircuit (by decide) (by decide) hOutside
  apply hObstruction
  exact ⟨E, hContext,
    BinaryAmbientMoveSupport.AllModeMove.support_card hMove,
    nativeMove221_support_cycle hMove⟩

/-- Every nonconstant finite move path has an actual first edge and records the
target of that edge as a path vertex. -/
theorem MovePath.exists_first_step
    {R : BinaryCircuit.Scheme α → BinaryCircuit.Scheme α → Prop}
    {D F : BinaryCircuit.Scheme α} (path : MovePath R D F) (hDF : D ≠ F) :
    ∃ E, R D E ∧ PathVertex path E := by
  induction path with
  | singleton => exact (hDF rfl).elim
  | @snoc E F path hEF ih =>
      by_cases hDE : D = E
      · subst E
        refine ⟨F, hEF, ?_⟩
        exact MovePath.end_mem_vertices (.snoc path hEF)
      · obtain ⟨Y, hDY, hY⟩ := ih hDE
        refine ⟨Y, hDY, ?_⟩
        simpa only [PathVertex, MovePath.vertices, List.mem_append,
          List.mem_singleton] using Or.inl hY

/-- If no first edge out of `D` can retain `C`, then no nonconstant path out of
`D` retains `C` at every actual vertex. -/
theorem MovePath.not_forall_vertex_retains_of_no_first_step
    {R : BinaryCircuit.Scheme α → BinaryCircuit.Scheme α → Prop}
    {C D F : BinaryCircuit.Scheme α}
    (hNo : ∀ E, R D E → ¬ C ⊆ E) (hDF : D ≠ F)
    (path : MovePath R D F) :
    ¬ ∀ X, PathVertex path X → C ⊆ X := by
  intro hRetains
  obtain ⟨E, hDE, hE⟩ :=
    BilinearComplexity.BinaryContextBorrowing221.MovePath.exists_first_step
      path hDF
  exact hNo E hDE (hRetains E hE)

/-- In the intrinsic minimal profile-`221` carrier, no native path from the
displayed source to the displayed target retains every term of `C` at every
vertex.  No persistence claim under enlargement of the ambient spaces is made. -/
theorem no_native_path_retains_context
    (path : MovePath NativeMove221 contextualStart contextualFinish) :
    ¬ ∀ X, PathVertex path X → contextC ⊆ X := by
  apply MovePath.not_forall_vertex_retains_of_no_first_step
    (R := NativeMove221) (C := contextC) (D := contextualStart)
    (F := contextualFinish)
    (fun _ hMove => no_first_native_move_retains_context hMove)
    (by decide) path

end BilinearComplexity.BinaryContextBorrowing221
