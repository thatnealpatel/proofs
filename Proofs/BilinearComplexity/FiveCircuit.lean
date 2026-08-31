import BilinearComplexity.NormalizedBinaryCarrier

set_option autoImplicit false

/-!
# Automatic five-element binary circuits

A binary cycle of cardinality five is inclusion-minimal when its supported
carrier values are nonzero and injective. The same argument packages disjoint
two- and three-element sides of an equal-evaluation identity into a circuit,
including the normalized binary tensor specialization.

AI disclosure: produced with AI assistance (see `Proofs/README`).
-/

namespace BilinearComplexity.BinaryCircuit

section Generic

universe u v

variable {α : Type u} {V : Type v} [DecidableEq α] [AddCommGroup V]
  [Module (ZMod 2) V]

private theorem not_binaryCycle_of_nonempty_card_le_two
    (value : α → V) (S : Scheme α) (hS : S.Nonempty) (hCard : S.card ≤ 2)
    (hNonzero : ∀ a ∈ S, value a ≠ 0)
    (hInjective : Set.InjOn value (S : Set α)) :
    ¬ BinaryCycle value S := by
  intro hCycle
  have hCardPos : 0 < S.card := Finset.card_pos.mpr hS
  have hCardCases : S.card = 1 ∨ S.card = 2 := by omega
  rcases hCardCases with hCardOne | hCardTwo
  · obtain ⟨a, hSa⟩ := Finset.card_eq_one.mp hCardOne
    subst S
    apply hNonzero a (by simp)
    simpa only [BinaryCycle, evaluation, Finset.sum_singleton] using hCycle
  · obtain ⟨a, b, hab, hSab⟩ := Finset.card_eq_two.mp hCardTwo
    subst S
    have hsum : value a + value b = 0 := by
      simpa [BinaryCycle, evaluation, hab] using hCycle
    have hsame : value a = value b := by
      apply add_left_cancel (a := value a)
      exact (hsum.trans (add_self_eq_zero (value a)).symm).symm
    have habEq : a = b := hInjective (by simp) (by simp) hsame
    exact hab habEq

/-- A five-element binary cycle with nonzero carrier values that are injective
on its support is automatically inclusion-minimal. -/
theorem circuit_of_binaryCycle_card_five {value : α → V} {C : Scheme α}
    (hCycle : BinaryCycle value C) (hCard : C.card = 5)
    (hNonzero : ∀ a ∈ C, value a ≠ 0)
    (hInjective : Set.InjOn value (C : Set α)) :
    Circuit value C := by
  have hCNonempty : C.Nonempty := Finset.card_pos.mp (by omega)
  refine ⟨hCycle, hCNonempty, ?_⟩
  intro Z hZC hZNonempty hZCycle
  have hZSubset : Z ⊆ C := hZC.subset
  let W := C \ Z
  have hWNonempty : W.Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro hCZ
    exact hZC.ne (Finset.Subset.antisymm hZSubset hCZ)
  have hDisjoint : Disjoint Z W := by
    exact Finset.disjoint_sdiff
  have hUnion : Z ∪ W = C := by
    exact Finset.union_sdiff_of_subset hZSubset
  have hWCycle : BinaryCycle value W := by
    rw [BinaryCycle]
    have hEval := evaluation_union (value := value) hDisjoint
    rw [hUnion, hCycle, hZCycle] at hEval
    simpa only [zero_add] using hEval.symm
  have hCardSum : Z.card + W.card = 5 := by
    rw [← Finset.card_union_of_disjoint hDisjoint, hUnion, hCard]
  have hSmall : Z.card ≤ 2 ∨ W.card ≤ 2 := by omega
  rcases hSmall with hZSmall | hWSmall
  · exact not_binaryCycle_of_nonempty_card_le_two value Z hZNonempty hZSmall
      (fun a ha => hNonzero a (hZSubset ha))
      (fun _ ha _ hb => hInjective (by simpa using hZSubset ha) (by simpa using hZSubset hb))
      hZCycle
  · have hWSubset : W ⊆ C := Finset.sdiff_subset
    exact not_binaryCycle_of_nonempty_card_le_two value W hWNonempty hWSmall
      (fun a ha => hNonzero a (hWSubset ha))
      (fun _ ha _ hb => hInjective (by simpa using hWSubset ha) (by simpa using hWSubset hb))
      hWCycle

#check @not_binaryCycle_of_nonempty_card_le_two

/-- Two disjoint sides of cardinalities two and three with equal evaluation
form a five-element circuit when all union values are nonzero and injective. -/
theorem circuit_union_of_disjoint_card_two_card_three {value : α → V}
    {A B : Scheme α} (hDisjoint : Disjoint A B) (hCardA : A.card = 2)
    (hCardB : B.card = 3) (hEvaluation : evaluation value A = evaluation value B)
    (hNonzero : ∀ a ∈ A ∪ B, value a ≠ 0)
    (hInjective : Set.InjOn value ((A ∪ B : Scheme α) : Set α)) :
    Circuit value (A ∪ B) := by
  apply circuit_of_binaryCycle_card_five
  · rw [BinaryCycle, evaluation_union hDisjoint, hEvaluation, add_self_eq_zero]
  · rw [Finset.card_union_of_disjoint hDisjoint, hCardA, hCardB]
  · exact hNonzero
  · exact hInjective

end Generic

example :
    let value : Fin 5 → (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2) :=
      ![(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1), (1, 1, 1, 1)]
    let C : Scheme (Fin 5) := Finset.univ
    BinaryCycle value C ∧ C.card = 5 ∧
      (∀ a ∈ C, value a ≠ 0) ∧ Set.InjOn value (C : Set (Fin 5)) := by
  dsimp
  refine ⟨?_, by decide, by decide, ?_⟩
  · change evaluation
      ![(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1), (1, 1, 1, 1)]
      Finset.univ = 0
    decide
  · rw [Finset.coe_univ, Set.injOn_univ]
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

#check @circuit_of_binaryCycle_card_five
#check @circuit_union_of_disjoint_card_two_card_three
#print axioms circuit_of_binaryCycle_card_five
#print axioms circuit_union_of_disjoint_card_two_card_three

end BilinearComplexity.BinaryCircuit

namespace BilinearComplexity.NormalizedBinaryCarrier

open BinaryCircuit

/-- Two disjoint normalized tensor states of cardinalities two and three with
equal tensor evaluation have a five-element union circuit. -/
theorem tensorEvaluation_circuit_union_of_disjoint_card_two_card_three
    {p : Profile} {A B : State p} (hDisjoint : Disjoint A B)
    (hCardA : A.card = 2) (hCardB : B.card = 3)
    (hEvaluation : stateEvaluation A = stateEvaluation B) :
    Circuit (@tensorEvaluation p) (A ∪ B) := by
  apply circuit_union_of_disjoint_card_two_card_three hDisjoint hCardA hCardB hEvaluation
  · intro t _
    exact tensorEvaluation_ne_zero t
  · intro s _ t _ hst
    exact tensorEvaluation_injective hst

#check @tensorEvaluation_circuit_union_of_disjoint_card_two_card_three
#print axioms tensorEvaluation_circuit_union_of_disjoint_card_two_card_three

end BilinearComplexity.NormalizedBinaryCarrier
