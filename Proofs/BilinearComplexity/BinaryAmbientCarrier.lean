import BilinearComplexity.NormalizedBinaryCarrier
import Mathlib.LinearAlgebra.TensorProduct.Basic

set_option autoImplicit false

/-!
# Ambient binary tensor carriers

This module defines finite-set states of nonzero factor triples in three arbitrary
modules over `𝔽₂`.  It contains no choice of coordinates.  Decidable equality is
required explicitly by operations on finite states.
-/

namespace BilinearComplexity.BinaryAmbientCarrier

open scoped TensorProduct BigOperators

universe u v w

open NormalizedBinaryCarrier (F2)

/-- A nonzero vector in an ambient additive group. -/
abbrev NonzeroVector (U : Type u) [Zero U] : Type u := {x : U // x ≠ 0}

/-- An ordered triple of nonzero factors in arbitrary ambient spaces. -/
abbrev Carrier (U : Type u) (V : Type v) (W : Type w)
    [Zero U] [Zero V] [Zero W] : Type (max u v w) :=
  NonzeroVector U × NonzeroVector V × NonzeroVector W

/-- An ambient state has finite-set semantics. -/
abbrev State (U : Type u) (V : Type v) (W : Type w)
    [Zero U] [Zero V] [Zero W] : Type (max u v w) :=
  Finset (Carrier U V W)

/-- An ordered triple of supplied nonzero vectors inhabits the ambient carrier. -/
theorem carrier_nonempty_of_nonzero
    {U : Type u} {V : Type v} {W : Type w}
    [Zero U] [Zero V] [Zero W]
    (u : U) (v : V) (w : W) (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) :
    Nonempty (Carrier U V W) :=
  ⟨⟨u, hu⟩, ⟨v, hv⟩, ⟨w, hw⟩⟩

/-- Evaluate an ambient factor triple as a nested pure tensor. -/
def tensorEvaluation
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    (t : Carrier U V W) : U ⊗[F2] (V ⊗[F2] W) :=
  t.1.1 ⊗ₜ (t.2.1.1 ⊗ₜ t.2.2.1)

/-- Unfolding ambient term evaluation exposes its nested pure tensor. -/
@[simp] theorem tensorEvaluation_eq_tmul
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    (t : Carrier U V W) :
    tensorEvaluation t = t.1.1 ⊗ₜ (t.2.1.1 ⊗ₜ t.2.2.1) := rfl

/-- Evaluate a finite ambient state by summing its pure tensors. -/
def stateEvaluation
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    (D : State U V W) : U ⊗[F2] (V ⊗[F2] W) :=
  ∑ t ∈ D, tensorEvaluation t

/-- The exact span of the first factors occurring in a state. -/
def firstSpan
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    [DecidableEq (Carrier U V W)]
    (D : State U V W) : Submodule F2 U :=
  Submodule.span F2 ((fun t : Carrier U V W => t.1.1) '' (D : Set (Carrier U V W)))

/-- The exact span of the second factors occurring in a state. -/
def secondSpan
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    [DecidableEq (Carrier U V W)]
    (D : State U V W) : Submodule F2 V :=
  Submodule.span F2 ((fun t : Carrier U V W => t.2.1.1) '' (D : Set (Carrier U V W)))

/-- The exact span of the third factors occurring in a state. -/
def thirdSpan
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    [DecidableEq (Carrier U V W)]
    (D : State U V W) : Submodule F2 W :=
  Submodule.span F2 ((fun t : Carrier U V W => t.2.2.1) '' (D : Set (Carrier U V W)))

/-- Every first factor occurring in a state lies in its exact first span. -/
theorem first_mem_firstSpan
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    [DecidableEq (Carrier U V W)]
    {D : State U V W} {t : Carrier U V W} (ht : t ∈ D) :
    t.1.1 ∈ firstSpan D := by
  apply Submodule.subset_span
  exact ⟨t, by simpa using ht, rfl⟩

/-- Every second factor occurring in a state lies in its exact second span. -/
theorem second_mem_secondSpan
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    [DecidableEq (Carrier U V W)]
    {D : State U V W} {t : Carrier U V W} (ht : t ∈ D) :
    t.2.1.1 ∈ secondSpan D := by
  apply Submodule.subset_span
  exact ⟨t, by simpa using ht, rfl⟩

/-- Every third factor occurring in a state lies in its exact third span. -/
theorem third_mem_thirdSpan
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    [DecidableEq (Carrier U V W)]
    {D : State U V W} {t : Carrier U V W} (ht : t ∈ D) :
    t.2.2.1 ∈ thirdSpan D := by
  apply Submodule.subset_span
  exact ⟨t, by simpa using ht, rfl⟩

/-- The empty state evaluates to the zero tensor. -/
@[simp] theorem stateEvaluation_empty
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W] :
    stateEvaluation (∅ : State U V W) = 0 := by
  simp [stateEvaluation]

/-- Evaluation is additive on unions of disjoint states. -/
@[simp] theorem stateEvaluation_union
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    [DecidableEq (Carrier U V W)]
    {D E : State U V W} (h : Disjoint D E) :
    stateEvaluation (D ∪ E) = stateEvaluation D + stateEvaluation E := by
  simp [stateEvaluation, Finset.sum_union h]

end BilinearComplexity.BinaryAmbientCarrier
