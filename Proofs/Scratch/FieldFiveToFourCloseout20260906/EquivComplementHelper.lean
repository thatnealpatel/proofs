import Mathlib

set_option autoImplicit false

namespace Equiv

variable {α β γ δ : Type*}

/-- For an equivalence out of a sum, the range of the right summand is the
complement of the range of the left summand. -/
theorem range_inr_eq_compl_range_inl (e : α ⊕ β ≃ γ) :
    Set.range (fun b : β => e (.inr b)) =
      (Set.range (fun a : α => e (.inl a)))ᶜ := by
  ext x
  constructor
  · rintro ⟨b, rfl⟩ ⟨a, ha⟩
    exact Sum.inl_ne_inr (e.injective ha)
  · intro hx
    obtain ⟨s, rfl⟩ := e.surjective x
    cases s with
    | inl a =>
        exact False.elim (hx ⟨a, rfl⟩)
    | inr b =>
        exact ⟨b, rfl⟩

/-- Equivalences out of the same sum with equal left-summand ranges also have
equal right-summand ranges. -/
theorem range_inr_eq_of_range_inl_eq (e f : α ⊕ β ≃ γ)
    (hleft : Set.range (fun a : α => e (.inl a)) =
      Set.range (fun a : α => f (.inl a))) :
    Set.range (fun b : β => e (.inr b)) =
      Set.range (fun b : β => f (.inr b)) := by
  calc
    Set.range (fun b : β => e (.inr b)) =
        (Set.range (fun a : α => e (.inl a)))ᶜ := range_inr_eq_compl_range_inl e
    _ = (Set.range (fun a : α => f (.inl a)))ᶜ :=
      congrArg (fun s : Set γ => sᶜ) hleft
    _ = Set.range (fun b : β => f (.inr b)) :=
      (range_inr_eq_compl_range_inl f).symm

/-- Equal left-summand ranges imply equal right-summand ranges after applying
an arbitrary function; the function need not be injective. -/
theorem range_comp_inr_eq_of_range_inl_eq (e f : α ⊕ β ≃ γ) (g : γ → δ)
    (hleft : Set.range (fun a : α => e (.inl a)) =
      Set.range (fun a : α => f (.inl a))) :
    Set.range (fun b : β => g (e (.inr b))) =
      Set.range (fun b : β => g (f (.inr b))) := by
  have hright := range_inr_eq_of_range_inl_eq e f hleft
  ext x
  constructor
  · rintro ⟨b, rfl⟩
    have hx : e (.inr b) ∈ Set.range (fun b : β => f (.inr b)) := by
      rw [← hright]
      exact ⟨b, rfl⟩
    obtain ⟨b', hb'⟩ := hx
    exact ⟨b', congrArg g hb'⟩
  · rintro ⟨b, rfl⟩
    have hx : f (.inr b) ∈ Set.range (fun b : β => e (.inr b)) := by
      rw [hright]
      exact ⟨b, rfl⟩
    obtain ⟨b', hb'⟩ := hx
    exact ⟨b', congrArg g hb'⟩

example : Set.range (fun b : Fin 3 =>
      (finSumFinEquiv : Fin 2 ⊕ Fin 3 ≃ Fin 5) (Sum.inr b)) =
    (Set.range (fun a : Fin 2 => finSumFinEquiv (Sum.inl a)))ᶜ := by
  exact range_inr_eq_compl_range_inl finSumFinEquiv

example (g : Fin 5 → Bool) :
    Set.range (fun b : Fin 3 => g (finSumFinEquiv (Sum.inr b))) =
      Set.range (fun b : Fin 3 => g (finSumFinEquiv (Sum.inr b))) := by
  exact range_comp_inr_eq_of_range_inl_eq
    (finSumFinEquiv : Fin 2 ⊕ Fin 3 ≃ Fin 5) finSumFinEquiv g rfl

#check @range_inr_eq_of_range_inl_eq
#check @range_comp_inr_eq_of_range_inl_eq
#print axioms range_inr_eq_compl_range_inl
#print axioms range_inr_eq_of_range_inl_eq
#print axioms range_comp_inr_eq_of_range_inl_eq

end Equiv
