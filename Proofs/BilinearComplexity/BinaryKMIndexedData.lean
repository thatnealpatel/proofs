import BilinearComplexity.BinaryAmbientCarrier

set_option autoImplicit false

/-!
# Effective indexed binary KM data and overlap preprocessing

The native factor order is `(b,c,a)`, so the common factor is third. A `Data n`
packages exactly the active coefficient-one terms. Coefficient-zero terms remain
in the arbitrary unchanged context supplied to `ContextAdmissible`.
-/

namespace BilinearComplexity.BinaryKMIndexedData

open scoped BigOperators TensorProduct
open NormalizedBinaryCarrier (F2)
open BinaryAmbientCarrier

universe uB uC uA

variable {B : Type uB} {C : Type uC} {A : Type uA}
variable [AddCommGroup B] [AddCommGroup C] [AddCommGroup A]
variable [Module F2 B] [Module F2 C] [Module F2 A]
variable [DecidableEq B] [DecidableEq C] [DecidableEq A]

/-- Effective indexed KM input data in the `(b,c,a)` orientation. -/
structure Data (n : Nat) where
  a : A
  b0 : B
  c0 : C
  b : Fin n → B
  c : Fin n → C
  a_ne_zero : a ≠ 0
  b0_ne_zero : b0 ≠ 0
  c0_ne_zero : c0 ≠ 0
  b_ne_zero : ∀ i, b i ≠ 0
  c_ne_zero : ∀ i, c i ≠ 0
  outputC_ne_zero : ∀ i, c i + c0 ≠ 0
  b0_eq_sum : b0 = ∑ i, b i
  source_injective : Function.Injective fun i => (b i, c i)

namespace Data

variable {n : Nat}

/-- The distinguished pivot `b₀ ⊗ c₀ ⊗ a`. -/
def pivot (d : Data (B := B) (C := C) (A := A) n) : Carrier B C A :=
  (⟨d.b0, d.b0_ne_zero⟩, ⟨d.c0, d.c0_ne_zero⟩, ⟨d.a, d.a_ne_zero⟩)

/-- Active source term `bᵢ ⊗ cᵢ ⊗ a`. -/
def sourceTerm (d : Data (B := B) (C := C) (A := A) n) (i : Fin n) : Carrier B C A :=
  (⟨d.b i, d.b_ne_zero i⟩, ⟨d.c i, d.c_ne_zero i⟩, ⟨d.a, d.a_ne_zero⟩)

/-- Active target term `bᵢ ⊗ (cᵢ + c₀) ⊗ a`. -/
def targetTerm (d : Data (B := B) (C := C) (A := A) n) (i : Fin n) : Carrier B C A :=
  (⟨d.b i, d.b_ne_zero i⟩, ⟨d.c i + d.c0, d.outputC_ne_zero i⟩,
    ⟨d.a, d.a_ne_zero⟩)

/-- Finite set of all indexed source terms, excluding the pivot. -/
def sourceActive (d : Data (B := B) (C := C) (A := A) n) : State B C A :=
  Finset.univ.image d.sourceTerm

/-- Finite set of all indexed target terms. -/
def targetActive (d : Data (B := B) (C := C) (A := A) n) : State B C A :=
  Finset.univ.image d.targetTerm

/-- Local source state consisting of the pivot and active source terms. -/
def sourceState (d : Data (B := B) (C := C) (A := A) n) : State B C A :=
  insert d.pivot d.sourceActive

/-- Local target state consisting of all active target terms. -/
def targetState (d : Data (B := B) (C := C) (A := A) n) : State B C A :=
  d.targetActive

/-- A context is admissible when it is disjoint from both complete local endpoints. -/
def ContextAdmissible (d : Data (B := B) (C := C) (A := A) n)
    (context : State B C A) : Prop :=
  Disjoint context d.sourceState ∧ Disjoint context d.targetState

/-- Complete source endpoint obtained by adjoining an admissible context. -/
def sourceEndpoint (d : Data (B := B) (C := C) (A := A) n)
    (context : State B C A) : State B C A := context ∪ d.sourceState

/-- Complete target endpoint obtained by adjoining an admissible context. -/
def targetEndpoint (d : Data (B := B) (C := C) (A := A) n)
    (context : State B C A) : State B C A := context ∪ d.targetState

/-- Indices whose target terms do not already occur in the active source set. -/
def changedIndices (d : Data (B := B) (C := C) (A := A) n) : Finset (Fin n) :=
  Finset.univ.filter fun i => d.targetTerm i ∉ d.sourceActive

/-- Indices belonging to source-target overlap cycles. -/
def unchangedIndices (d : Data (B := B) (C := C) (A := A) n) : Finset (Fin n) :=
  Finset.univ.filter fun i => d.targetTerm i ∈ d.sourceActive

/-- Source terms at genuinely changed indices. -/
def changedSource (d : Data (B := B) (C := C) (A := A) n) : State B C A :=
  d.changedIndices.image d.sourceTerm

/-- Target terms at genuinely changed indices. -/
def changedTarget (d : Data (B := B) (C := C) (A := A) n) : State B C A :=
  d.changedIndices.image d.targetTerm

/-- The common endpoint state formed by all discarded overlap cycles. -/
def unchangedState (d : Data (B := B) (C := C) (A := A) n) : State B C A :=
  d.unchangedIndices.image d.sourceTerm

/-- The strict local source left after endpoint overlap is put into the fixed state. -/
def workSource (d : Data (B := B) (C := C) (A := A) n) : State B C A :=
  insert d.pivot d.changedSource

/-- The strict local target left after endpoint overlap is put into the fixed state. -/
def workTarget (d : Data (B := B) (C := C) (A := A) n) : State B C A :=
  d.changedTarget

/-- The caller context together with all unchanged overlap cycles. -/
def fixedState (d : Data (B := B) (C := C) (A := A) n)
    (context : State B C A) : State B C A :=
  context ∪ d.unchangedState

/-- Compute the unique overlap partner when one exists, and return the input otherwise. -/
def overlapPartner (d : Data (B := B) (C := C) (A := A) n) (i : Fin n) : Fin n :=
  if h : ∃ j, d.sourceTerm j = d.targetTerm i then
    Fin.find (fun j => d.sourceTerm j = d.targetTerm i) h
  else i

private lemma binary_add_self_eq_zero (x : B) : x + x = 0 :=
  BinaryCircuit.add_self_eq_zero x

private lemma add_add_cancel_right_charTwo (x y : C) : (x + y) + y = x := by
  rw [add_assoc, BinaryCircuit.add_self_eq_zero, add_zero]

/-- Supplied source-pair injectivity implies injectivity of packaged source atoms. -/
lemma sourceTerm_injective (d : Data (B := B) (C := C) (A := A) n) :
    Function.Injective d.sourceTerm := by
  intro i j h
  apply d.source_injective
  exact Prod.ext (congrArg (fun t : Carrier B C A => t.1.1) h)
    (congrArg (fun t : Carrier B C A => t.2.1.1) h)

/-- Translation by `c₀` preserves injectivity, so target injectivity is derived. -/
lemma targetTerm_injective (d : Data (B := B) (C := C) (A := A) n) :
    Function.Injective d.targetTerm := by
  intro i j h
  apply d.source_injective
  apply Prod.ext
  · exact congrArg (fun t : Carrier B C A => t.1.1) h
  · have hc := congrArg (fun t : Carrier B C A => t.2.1.1) h
    dsimp [targetTerm] at hc
    exact add_right_cancel hc

/-- Every active source differs from the pivot, derived from target nonzeroness. -/
lemma pivot_ne_sourceTerm (d : Data (B := B) (C := C) (A := A) n) (i : Fin n) :
    d.pivot ≠ d.sourceTerm i := by
  intro h
  have hc : d.c0 = d.c i := congrArg (fun t : Carrier B C A => t.2.1.1) h
  apply d.outputC_ne_zero i
  rw [← hc, BinaryCircuit.add_self_eq_zero]

/-- Every active target differs from the pivot, derived from source nonzeroness. -/
lemma pivot_ne_targetTerm (d : Data (B := B) (C := C) (A := A) n) (i : Fin n) :
    d.pivot ≠ d.targetTerm i := by
  intro h
  have hc : d.c0 = d.c i + d.c0 := congrArg (fun t : Carrier B C A => t.2.1.1) h
  apply d.c_ne_zero i
  have hcancel := congrArg (fun x => x + d.c0) hc
  simpa only [BinaryCircuit.add_self_eq_zero, add_zero, add_add_cancel_right_charTwo]
    using hcancel.symm

/-- The active source set has exactly `n` atoms. -/
lemma sourceActive_card (d : Data (B := B) (C := C) (A := A) n) :
    d.sourceActive.card = n := by
  simpa only [sourceActive, Finset.card_univ, Fintype.card_fin] using
    Finset.card_image_of_injective (Finset.univ : Finset (Fin n)) d.sourceTerm_injective

/-- The active target set has exactly `n` atoms. -/
lemma targetActive_card (d : Data (B := B) (C := C) (A := A) n) :
    d.targetActive.card = n := by
  simpa only [targetActive, Finset.card_univ, Fintype.card_fin] using
    Finset.card_image_of_injective (Finset.univ : Finset (Fin n)) d.targetTerm_injective

/-- The pivot is absent from the active source set. -/
lemma pivot_not_mem_sourceActive (d : Data (B := B) (C := C) (A := A) n) :
    d.pivot ∉ d.sourceActive := by
  simp only [sourceActive, Finset.mem_image, Finset.mem_univ, true_and, not_exists]
  exact fun i h => d.pivot_ne_sourceTerm i h.symm

/-- The local source has exactly `n + 1` atoms. -/
lemma sourceState_card (d : Data (B := B) (C := C) (A := A) n) :
    d.sourceState.card = n + 1 := by
  rw [sourceState, Finset.card_insert_of_notMem d.pivot_not_mem_sourceActive,
    sourceActive_card]

/-- The local target has exactly `n` atoms. -/
lemma targetState_card (d : Data (B := B) (C := C) (A := A) n) :
    d.targetState.card = n := d.targetActive_card

/-- An admissible contextual source has exactly `|context| + n + 1` atoms. -/
lemma context_sourceEndpoint_card (d : Data (B := B) (C := C) (A := A) n)
    (context : State B C A) (h : d.ContextAdmissible context) :
    (d.sourceEndpoint context).card = context.card + n + 1 := by
  rw [sourceEndpoint, Finset.card_union_of_disjoint h.1, sourceState_card, add_assoc]

/-- An admissible contextual target has exactly `|context| + n` atoms. -/
lemma context_targetEndpoint_card (d : Data (B := B) (C := C) (A := A) n)
    (context : State B C A) (h : d.ContextAdmissible context) :
    (d.targetEndpoint context).card = context.card + n := by
  rw [targetEndpoint, Finset.card_union_of_disjoint h.2, targetState_card]

/-- Each target atom evaluates as its source atom plus its pivot contribution. -/
lemma targetTerm_evaluation (d : Data (B := B) (C := C) (A := A) n) (i : Fin n) :
    tensorEvaluation (d.targetTerm i) =
      tensorEvaluation (d.sourceTerm i) + d.b i ⊗ₜ[F2] (d.c0 ⊗ₜ[F2] d.a) := by
  simp only [tensorEvaluation_eq_tmul, sourceTerm, targetTerm]
  rw [TensorProduct.add_tmul, TensorProduct.tmul_add]

/-- The indexed KM local source and target have equal tensor evaluation. -/
lemma sourceState_evaluation_eq_targetState
    (d : Data (B := B) (C := C) (A := A) n) :
    stateEvaluation d.sourceState = stateEvaluation d.targetState := by
  rw [sourceState, stateEvaluation, Finset.sum_insert d.pivot_not_mem_sourceActive]
  rw [sourceActive, Finset.sum_image]
  · rw [targetState, targetActive, stateEvaluation, Finset.sum_image]
    · simp_rw [d.targetTerm_evaluation]
      rw [Finset.sum_add_distrib, ← TensorProduct.sum_tmul]
      rw [← d.b0_eq_sum]
      exact add_comm _ _
    · exact Set.injOn_of_injective d.targetTerm_injective
  · exact Set.injOn_of_injective d.sourceTerm_injective

/-- Adjoining an admissible context preserves endpoint evaluation equality. -/
lemma context_endpoint_evaluation
    (d : Data (B := B) (C := C) (A := A) n) (context : State B C A)
    (h : d.ContextAdmissible context) :
    stateEvaluation (d.sourceEndpoint context) =
      stateEvaluation (d.targetEndpoint context) := by
  rw [sourceEndpoint, targetEndpoint, stateEvaluation_union h.1,
    stateEvaluation_union h.2, d.sourceState_evaluation_eq_targetState]

/-- On an unchanged index, the computed partner source is its target. -/
lemma overlapPartner_spec (d : Data (B := B) (C := C) (A := A) n)
    {i : Fin n} (hi : i ∈ d.unchangedIndices) :
    d.sourceTerm (d.overlapPartner i) = d.targetTerm i := by
  have hex : ∃ j, d.sourceTerm j = d.targetTerm i := by
    simpa only [unchangedIndices, Finset.mem_filter, Finset.mem_univ, true_and,
      sourceActive, Finset.mem_image, Finset.mem_univ, true_and] using hi
  simp only [overlapPartner, dif_pos hex]
  exact Fin.find_spec hex

/-- Updating an unchanged index's partner returns the original source atom. -/
lemma target_overlapPartner_eq_sourceTerm (d : Data (B := B) (C := C) (A := A) n)
    {i : Fin n} (hi : i ∈ d.unchangedIndices) :
    d.targetTerm (d.overlapPartner i) = d.sourceTerm i := by
  have hs := d.overlapPartner_spec hi
  apply Prod.ext
  · apply Subtype.ext
    simpa only [sourceTerm, targetTerm] using
      congrArg (fun t : Carrier B C A => t.1.1) hs
  · apply Prod.ext
    · apply Subtype.ext
      have hc := congrArg (fun t : Carrier B C A => t.2.1.1) hs
      dsimp [sourceTerm, targetTerm] at hc ⊢
      rw [hc, add_add_cancel_right_charTwo]
    · rfl

/-- The computed overlap partner is itself unchanged. -/
lemma overlapPartner_mem_unchanged (d : Data (B := B) (C := C) (A := A) n)
    {i : Fin n} (hi : i ∈ d.unchangedIndices) :
    d.overlapPartner i ∈ d.unchangedIndices := by
  simp only [unchangedIndices, Finset.mem_filter, Finset.mem_univ, true_and,
    sourceActive, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨i, d.target_overlapPartner_eq_sourceTerm hi |>.symm⟩

/-- The computed partner map is involutive on unchanged indices. -/
lemma overlapPartner_involutive (d : Data (B := B) (C := C) (A := A) n)
    {i : Fin n} (hi : i ∈ d.unchangedIndices) :
    d.overlapPartner (d.overlapPartner i) = i := by
  apply d.sourceTerm_injective
  rw [d.overlapPartner_spec (d.overlapPartner_mem_unchanged hi),
    d.target_overlapPartner_eq_sourceTerm hi]

/-- Overlap cycles have no fixed indices. -/
lemma overlapPartner_ne (d : Data (B := B) (C := C) (A := A) n)
    {i : Fin n} (hi : i ∈ d.unchangedIndices) :
    d.overlapPartner i ≠ i := by
  intro h
  have hs := d.overlapPartner_spec hi
  rw [h] at hs
  have hc := congrArg (fun t : Carrier B C A => t.2.1.1) hs
  dsimp [sourceTerm, targetTerm] at hc
  apply d.c0_ne_zero
  have hcancel : d.c i + 0 = d.c i + d.c0 := by simpa only [add_zero] using hc
  exact (add_left_cancel hcancel).symm

/-- Every unchanged index belongs to an explicit fixed-point-free overlap two-cycle. -/
lemma overlapPartner_twoCycle (d : Data (B := B) (C := C) (A := A) n)
    {i : Fin n} (hi : i ∈ d.unchangedIndices) :
    d.overlapPartner i ∈ d.unchangedIndices ∧
      d.overlapPartner i ≠ i ∧
      d.sourceTerm (d.overlapPartner i) = d.targetTerm i ∧
      d.targetTerm (d.overlapPartner i) = d.sourceTerm i :=
  ⟨d.overlapPartner_mem_unchanged hi, d.overlapPartner_ne hi,
    d.overlapPartner_spec hi, d.target_overlapPartner_eq_sourceTerm hi⟩

/-- Both indices in an overlap two-cycle have the same `b` factor. -/
lemma b_overlapPartner_eq (d : Data (B := B) (C := C) (A := A) n)
    {i : Fin n} (hi : i ∈ d.unchangedIndices) :
    d.b (d.overlapPartner i) = d.b i := by
  exact congrArg (fun t : Carrier B C A => t.1.1) (d.overlapPartner_spec hi)

/-- The discarded overlap cycles contribute zero to the `b`-factor sum. -/
lemma unchanged_b_sum_eq_zero (d : Data (B := B) (C := C) (A := A) n) :
    ∑ i ∈ d.unchangedIndices, d.b i = 0 := by
  apply Finset.sum_involution (fun i _ => d.overlapPartner i)
  · intro i hi
    rw [d.b_overlapPartner_eq hi, BinaryCircuit.add_self_eq_zero]
  · intro i hi _
    exact d.overlapPartner_ne hi
  · exact fun i hi => d.overlapPartner_mem_unchanged hi
  · exact fun i hi => d.overlapPartner_involutive hi

/-- Removing all overlap cycles preserves the KM identity `∑ bᵢ = b₀`. -/
lemma changed_b_sum_eq_b0 (d : Data (B := B) (C := C) (A := A) n) :
    ∑ i ∈ d.changedIndices, d.b i = d.b0 := by
  have hpartition := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun i => d.targetTerm i ∉ d.sourceActive) d.b
  have hnot : (∑ i ∈ Finset.univ with ¬d.targetTerm i ∉ d.sourceActive, d.b i) = 0 := by
    simpa only [unchangedIndices, not_not] using d.unchanged_b_sum_eq_zero
  rw [hnot, add_zero] at hpartition
  change Finset.sum (Finset.univ.filter
    (fun i => d.targetTerm i ∉ d.sourceActive)) d.b = d.b0
  exact hpartition.trans d.b0_eq_sum.symm

/-- At least one index genuinely changes because `b₀` is nonzero. -/
lemma changedIndices_nonempty (d : Data (B := B) (C := C) (A := A) n) :
    d.changedIndices.Nonempty := by
  by_contra h
  have hsum := d.changed_b_sum_eq_b0
  rw [Finset.not_nonempty_iff_eq_empty.mp h] at hsum
  simp only [Finset.sum_empty] at hsum
  exact d.b0_ne_zero hsum.symm

/-- Changed and unchanged indices are disjoint. -/
lemma changedIndices_disjoint_unchangedIndices
    (d : Data (B := B) (C := C) (A := A) n) :
    Disjoint d.changedIndices d.unchangedIndices := by
  rw [Finset.disjoint_left]
  intro i hc hu
  exact (Finset.mem_filter.mp hc).2 (Finset.mem_filter.mp hu).2

/-- Changed and unchanged indices partition all `Fin n` indices. -/
lemma changedIndices_union_unchangedIndices
    (d : Data (B := B) (C := C) (A := A) n) :
    d.changedIndices ∪ d.unchangedIndices = Finset.univ := by
  ext i
  simp only [changedIndices, unchangedIndices, Finset.mem_union, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro
    trivial
  · intro
    by_cases h : d.targetTerm i ∈ d.sourceActive
    · exact Or.inr h
    · exact Or.inl h

/-- The changed and unchanged cardinalities add to the supplied active arity. -/
lemma changedIndices_card_add_unchangedIndices_card
    (d : Data (B := B) (C := C) (A := A) n) :
    d.changedIndices.card + d.unchangedIndices.card = n := by
  rw [← Finset.card_union_of_disjoint d.changedIndices_disjoint_unchangedIndices,
    d.changedIndices_union_unchangedIndices, Finset.card_univ, Fintype.card_fin]

/-- Changed source and target states are disjoint. -/
lemma changedSource_disjoint_changedTarget (d : Data (B := B) (C := C) (A := A) n) :
    Disjoint d.changedSource d.changedTarget := by
  rw [Finset.disjoint_left]
  intro t hs ht
  rcases Finset.mem_image.mp hs with ⟨i, hi, rfl⟩
  rcases Finset.mem_image.mp ht with ⟨j, hj, heq⟩
  have htarget_mem : d.targetTerm j ∈ d.sourceActive := by
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, heq.symm⟩
  exact (Finset.mem_filter.mp hj).2 htarget_mem

/-- Updating all unchanged indices merely permutes their finite state. -/
lemma unchanged_target_eq_unchangedState (d : Data (B := B) (C := C) (A := A) n) :
    d.unchangedIndices.image d.targetTerm = d.unchangedState := by
  ext t
  constructor
  · intro ht
    rcases Finset.mem_image.mp ht with ⟨i, hi, rfl⟩
    exact Finset.mem_image.mpr ⟨d.overlapPartner i, d.overlapPartner_mem_unchanged hi,
      d.overlapPartner_spec hi⟩
  · intro ht
    rcases Finset.mem_image.mp ht with ⟨i, hi, rfl⟩
    exact Finset.mem_image.mpr ⟨d.overlapPartner i, d.overlapPartner_mem_unchanged hi,
      d.target_overlapPartner_eq_sourceTerm hi⟩

/-- The active source is exactly its changed and unchanged pieces. -/
lemma sourceActive_eq_changed_union_unchanged (d : Data (B := B) (C := C) (A := A) n) :
    d.sourceActive = d.changedSource ∪ d.unchangedState := by
  ext t
  simp only [sourceActive, changedSource, unchangedState, Finset.mem_image,
    Finset.mem_union]
  constructor
  · rintro ⟨i, _, rfl⟩
    by_cases h : d.targetTerm i ∈ d.sourceActive
    · right
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩, rfl⟩
    · left
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩, rfl⟩
  · rintro (⟨i, _, rfl⟩ | ⟨i, _, rfl⟩) <;> exact ⟨i, Finset.mem_univ i, rfl⟩

/-- The active target is exactly its changed and unchanged pieces. -/
lemma targetActive_eq_changed_union_unchanged (d : Data (B := B) (C := C) (A := A) n) :
    d.targetActive = d.changedTarget ∪ d.unchangedState := by
  rw [← d.unchanged_target_eq_unchangedState]
  ext t
  simp only [targetActive, changedTarget, Finset.mem_image, Finset.mem_union]
  constructor
  · rintro ⟨i, _, rfl⟩
    by_cases h : d.targetTerm i ∈ d.sourceActive
    · right
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩, rfl⟩
    · left
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩, rfl⟩
  · rintro (⟨i, _, rfl⟩ | ⟨i, _, rfl⟩) <;> exact ⟨i, Finset.mem_univ i, rfl⟩

/-- The source endpoint decomposes into pivot, changed source, and unchanged state. -/
lemma sourceState_eq_pivot_changed_unchanged (d : Data (B := B) (C := C) (A := A) n) :
    d.sourceState = insert d.pivot (d.changedSource ∪ d.unchangedState) := by
  rw [sourceState, d.sourceActive_eq_changed_union_unchanged]

/-- The target endpoint decomposes into changed target and unchanged state. -/
lemma targetState_eq_changed_union_unchanged (d : Data (B := B) (C := C) (A := A) n) :
    d.targetState = d.changedTarget ∪ d.unchangedState := by
  exact d.targetActive_eq_changed_union_unchanged

/-- The pivot is absent from the active target set. -/
lemma pivot_not_mem_targetActive (d : Data (B := B) (C := C) (A := A) n) :
    d.pivot ∉ d.targetActive := by
  simp only [targetActive, Finset.mem_image, Finset.mem_univ, true_and, not_exists]
  exact fun i h => d.pivot_ne_targetTerm i h.symm

/-- Source-target overlap is exactly the unchanged two-cycle state. -/
lemma sourceState_inter_targetState_eq_unchangedState
    (d : Data (B := B) (C := C) (A := A) n) :
    d.sourceState ∩ d.targetState = d.unchangedState := by
  ext t
  simp only [sourceState, Finset.mem_inter, Finset.mem_insert, targetState]
  constructor
  · rintro ⟨hp | hs, ht⟩
    · subst t
      exact False.elim (d.pivot_not_mem_targetActive ht)
    · rcases Finset.mem_image.mp ht with ⟨i, _, rfl⟩
      have hi : i ∈ d.unchangedIndices := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hs⟩
      exact Finset.mem_image.mpr ⟨d.overlapPartner i, d.overlapPartner_mem_unchanged hi,
        d.overlapPartner_spec hi⟩
  · intro ht
    rcases Finset.mem_image.mp ht with ⟨i, hi, rfl⟩
    constructor
    · right
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    · rw [← d.target_overlapPartner_eq_sourceTerm hi]
      exact Finset.mem_image.mpr ⟨d.overlapPartner i, Finset.mem_univ _, rfl⟩

/-- Changed source atoms are counted exactly by changed indices. -/
lemma changedSource_card (d : Data (B := B) (C := C) (A := A) n) :
    d.changedSource.card = d.changedIndices.card := by
  exact Finset.card_image_of_injective d.changedIndices d.sourceTerm_injective

/-- Changed target atoms are counted exactly by changed indices. -/
lemma changedTarget_card (d : Data (B := B) (C := C) (A := A) n) :
    d.changedTarget.card = d.changedIndices.card := by
  exact Finset.card_image_of_injective d.changedIndices d.targetTerm_injective

/-- Unchanged atoms are counted exactly by unchanged indices. -/
lemma unchangedState_card (d : Data (B := B) (C := C) (A := A) n) :
    d.unchangedState.card = d.unchangedIndices.card := by
  exact Finset.card_image_of_injective d.unchangedIndices d.sourceTerm_injective

/-- Changed source atoms are disjoint from the unchanged state. -/
lemma changedSource_disjoint_unchangedState
    (d : Data (B := B) (C := C) (A := A) n) :
    Disjoint d.changedSource d.unchangedState := by
  rw [Finset.disjoint_left]
  intro t ht hu
  rcases Finset.mem_image.mp ht with ⟨i, hi, rfl⟩
  rcases Finset.mem_image.mp hu with ⟨j, hj, heq⟩
  have hij : i = j := d.sourceTerm_injective heq.symm
  subst j
  exact (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2

/-- Changed target atoms are disjoint from the unchanged state. -/
lemma changedTarget_disjoint_unchangedState
    (d : Data (B := B) (C := C) (A := A) n) :
    Disjoint d.changedTarget d.unchangedState := by
  rw [← d.unchanged_target_eq_unchangedState, Finset.disjoint_left]
  intro t ht hu
  rcases Finset.mem_image.mp ht with ⟨i, hi, rfl⟩
  rcases Finset.mem_image.mp hu with ⟨j, hj, heq⟩
  have hij : i = j := d.targetTerm_injective heq.symm
  subst j
  exact (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2

/-- The pivot is absent from the changed source state. -/
lemma pivot_not_mem_changedSource (d : Data (B := B) (C := C) (A := A) n) :
    d.pivot ∉ d.changedSource := by
  intro hp
  apply d.pivot_not_mem_sourceActive
  rcases Finset.mem_image.mp hp with ⟨i, _, heq⟩
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, heq⟩

/-- The strict work source has one more atom than the changed index count. -/
lemma workSource_card (d : Data (B := B) (C := C) (A := A) n) :
    d.workSource.card = d.changedIndices.card + 1 := by
  rw [workSource, Finset.card_insert_of_notMem d.pivot_not_mem_changedSource,
    d.changedSource_card]

/-- The strict work target has exactly the changed index count. -/
lemma workTarget_card (d : Data (B := B) (C := C) (A := A) n) :
    d.workTarget.card = d.changedIndices.card := by
  exact d.changedTarget_card

/-- The unchanged state is disjoint from the strict work source. -/
lemma unchangedState_disjoint_workSource
    (d : Data (B := B) (C := C) (A := A) n) :
    Disjoint d.unchangedState d.workSource := by
  rw [Finset.disjoint_left]
  intro t hu hw
  rw [workSource, Finset.mem_insert] at hw
  rcases hw with hp | hc
  · subst t
    apply d.pivot_not_mem_sourceActive
    rcases Finset.mem_image.mp hu with ⟨i, _, heq⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, heq⟩
  · exact Finset.disjoint_left.mp d.changedSource_disjoint_unchangedState hc hu

/-- The unchanged state is disjoint from the strict work target. -/
lemma unchangedState_disjoint_workTarget
    (d : Data (B := B) (C := C) (A := A) n) :
    Disjoint d.unchangedState d.workTarget := by
  exact d.changedTarget_disjoint_unchangedState.symm

/-- The complete source is the fixed state union the strict work source. -/
lemma sourceEndpoint_eq_fixedState_union_workSource
    (d : Data (B := B) (C := C) (A := A) n) (context : State B C A) :
    d.sourceEndpoint context = d.fixedState context ∪ d.workSource := by
  rw [sourceEndpoint, d.sourceState_eq_pivot_changed_unchanged, fixedState, workSource]
  ext t
  simp only [Finset.mem_union, Finset.mem_insert]
  tauto

/-- The complete target is the fixed state union the strict work target. -/
lemma targetEndpoint_eq_fixedState_union_workTarget
    (d : Data (B := B) (C := C) (A := A) n) (context : State B C A) :
    d.targetEndpoint context = d.fixedState context ∪ d.workTarget := by
  rw [targetEndpoint, d.targetState_eq_changed_union_unchanged, fixedState, workTarget]
  ext t
  simp only [Finset.mem_union]
  tauto

/-- Endpoint admissibility makes the fixed state disjoint from the strict work source. -/
lemma fixedState_disjoint_workSource
    (d : Data (B := B) (C := C) (A := A) n) (context : State B C A)
    (h : d.ContextAdmissible context) :
    Disjoint (d.fixedState context) d.workSource := by
  rw [Finset.disjoint_left]
  intro t hf hw
  rcases Finset.mem_union.mp hf with hc | hu
  · apply Finset.disjoint_left.mp h.1 hc
    rw [d.sourceState_eq_pivot_changed_unchanged]
    rw [workSource, Finset.mem_insert] at hw
    rcases hw with hp | hc'
    · exact Finset.mem_insert.mpr (Or.inl hp)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_union_left _ hc'))
  · exact Finset.disjoint_left.mp d.unchangedState_disjoint_workSource hu hw

/-- Endpoint admissibility makes the fixed state disjoint from the strict work target. -/
lemma fixedState_disjoint_workTarget
    (d : Data (B := B) (C := C) (A := A) n) (context : State B C A)
    (h : d.ContextAdmissible context) :
    Disjoint (d.fixedState context) d.workTarget := by
  rw [Finset.disjoint_left]
  intro t hf hw
  rcases Finset.mem_union.mp hf with hc | hu
  · apply Finset.disjoint_left.mp h.2 hc
    rw [d.targetState_eq_changed_union_unchanged]
    exact Finset.mem_union_left _ hw
  · exact Finset.disjoint_left.mp d.unchangedState_disjoint_workTarget hu hw

end Data

example : ∃ d : Data (B := F2) (C := Fin 2 → F2) (A := F2) 1,
    d.sourceActive.card = 1 ∧ d.targetActive.card = 1 ∧
    d.sourceState.card = 2 ∧ d.targetState.card = 1 ∧
    d.changedIndices = Finset.univ ∧ d.unchangedIndices = ∅ ∧
    d.workSource.card = 2 ∧ d.workTarget.card = 1 ∧ d.fixedState ∅ = ∅ ∧
    d.ContextAdmissible ∅ ∧
    stateEvaluation d.sourceState = stateEvaluation d.targetState := by
  let d : Data (B := F2) (C := Fin 2 → F2) (A := F2) 1 := {
    a := 1
    b0 := 1
    c0 := fun i => if i = 0 then 1 else 0
    b := fun _ => 1
    c := fun _ i => if i = 1 then 1 else 0
    a_ne_zero := by decide
    b0_ne_zero := by decide
    c0_ne_zero := by decide
    b_ne_zero := by intro; decide
    c_ne_zero := by intro; decide
    outputC_ne_zero := by intro; decide
    b0_eq_sum := by simp
    source_injective := fun _ _ _ => Subsingleton.elim _ _ }
  refine ⟨d, d.sourceActive_card, d.targetActive_card, d.sourceState_card,
    d.targetState_card, ?_, ?_, d.workSource_card, d.workTarget_card, ?_, ?_,
    d.sourceState_evaluation_eq_targetState⟩
  · decide
  · decide
  · have hu : d.unchangedIndices = ∅ := by decide
    simp only [Data.fixedState, hu, Data.unchangedState, Finset.image_empty,
      Finset.union_empty]
  · simp [Data.ContextAdmissible]

example : ∃ d : Data (B := Fin 2 → F2) (C := Fin 2 → F2) (A := F2) 3,
    d.unchangedIndices.card = 2 ∧ d.changedIndices.card = 1 ∧
    d.sourceState ∩ d.targetState = d.unchangedState ∧
    (∑ i ∈ d.changedIndices, d.b i) = d.b0 := by
  let d : Data (B := Fin 2 → F2) (C := Fin 2 → F2) (A := F2) 3 := {
    a := 1
    b0 := fun i => if i = 1 then 1 else 0
    c0 := fun i => if i = 0 then 1 else 0
    b := fun i => if i = 2 then (fun j => if j = 1 then 1 else 0)
      else (fun j => if j = 0 then 1 else 0)
    c := fun i => if i = 1 then (fun _ => 1)
      else (fun j => if j = 1 then 1 else 0)
    a_ne_zero := by decide
    b0_ne_zero := by decide
    c0_ne_zero := by decide
    b_ne_zero := by intro i; fin_cases i <;> decide
    c_ne_zero := by intro i; fin_cases i <;> decide
    outputC_ne_zero := by intro i; fin_cases i <;> decide
    b0_eq_sum := by decide
    source_injective := by decide }
  refine ⟨d, ?_, ?_, d.sourceState_inter_targetState_eq_unchangedState,
    d.changed_b_sum_eq_b0⟩
  · decide
  · decide

end BilinearComplexity.BinaryKMIndexedData
