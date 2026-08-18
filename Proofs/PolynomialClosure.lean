/-
  PolynomialClosure — reusable polynomial zero-locus closure and polynomial maps.

  This is deliberately neutral infrastructure: it knows only affine coordinate
  spaces, not tensors or any topological interpretation of closure.
-/
import Mathlib.RingTheory.Nullstellensatz

set_option autoImplicit false

namespace PolynomialClosure

/-- The polynomial closure of `s`: the common zero locus of every polynomial
that vanishes on `s`, over the specified field. -/
def closure (k : Type*) [Field k] {ι : Type*} (s : Set (ι → k)) : Set (ι → k) :=
  MvPolynomial.zeroLocus k (MvPolynomial.vanishingIdeal k s)

/-- Membership in polynomial closure means satisfying every polynomial that
vanishes on the original set. -/
theorem mem_closure_iff {k : Type*} [Field k] {ι : Type*} {s : Set (ι → k)}
    {x : ι → k} :
    x ∈ closure k s ↔ ∀ p ∈ MvPolynomial.vanishingIdeal k s,
      MvPolynomial.eval x p = 0 :=
  Iff.rfl

/-- Every set is contained in its polynomial closure. -/
theorem subset_closure {k : Type*} [Field k] {ι : Type*} (s : Set (ι → k)) :
    s ⊆ closure k s :=
  MvPolynomial.zeroLocus_vanishingIdeal_le s

/-- Polynomial closure is monotone with respect to inclusion. -/
theorem closure_mono {k : Type*} [Field k] {ι : Type*} {s t : Set (ι → k)}
    (hst : s ⊆ t) : closure k s ⊆ closure k t := by
  exact MvPolynomial.zeroLocus_anti_mono
    (MvPolynomial.vanishingIdeal_anti_mono hst)

/-- A coordinate description of a polynomial map between affine coordinate
spaces. `coordinate j` is the polynomial defining output coordinate `j`. -/
structure Map (k : Type*) [Field k] (ι κ : Type*) where
  coordinate : κ → MvPolynomial ι k

/-- Evaluate a coordinatewise polynomial map at an affine point. -/
noncomputable def Map.eval {k : Type*} [Field k] {ι κ : Type*} (f : Map k ι κ)
    (x : ι → k) : κ → k :=
  fun j => MvPolynomial.eval x (f.coordinate j)

/-- Ground truth: evaluation of a polynomial map is coordinatewise polynomial
evaluation. -/
@[simp] theorem Map.eval_apply {k : Type*} [Field k] {ι κ : Type*}
    (f : Map k ι κ) (x : ι → k) (j : κ) :
    f.eval x j = MvPolynomial.eval x (f.coordinate j) :=
  rfl

/-- Polynomial maps preserve polynomial closure: if the map sends `s` into
`t`, it sends the polynomial closure of `s` into that of `t`. The proof is
substitution of the coordinate polynomials into every equation of `t`. -/
theorem Map.mapsTo_closure {k : Type*} [Field k] {ι κ : Type*}
    (f : Map k ι κ) {s : Set (ι → k)} {t : Set (κ → k)}
    (hmap : Set.MapsTo f.eval s t) : Set.MapsTo f.eval (closure k s) (closure k t) := by
  intro x hx
  rw [mem_closure_iff]
  intro p hp
  let pullback : MvPolynomial ι k :=
    MvPolynomial.eval₂ MvPolynomial.C f.coordinate p
  have hpullback : pullback ∈ MvPolynomial.vanishingIdeal k s := by
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    intro y hy
    simp only [MvPolynomial.aeval_eq_eval]
    rw [show MvPolynomial.eval y pullback = MvPolynomial.eval (f.eval y) p by
      dsimp [pullback]
      rw [MvPolynomial.eval_eval₂]
      have hc : (MvPolynomial.eval y).comp MvPolynomial.C = RingHom.id k := by
        ext z
        simp
      rw [hc, MvPolynomial.eval₂_id]
      rfl]
    exact hp (f.eval y) (hmap hy)
  have hzero : MvPolynomial.eval x pullback = 0 := mem_closure_iff.mp hx _ hpullback
  rw [show MvPolynomial.eval (f.eval x) p = MvPolynomial.eval x pullback by
    dsimp [pullback]
    rw [MvPolynomial.eval_eval₂]
    have hc : (MvPolynomial.eval x).comp MvPolynomial.C = RingHom.id k := by
      ext z
      simp
    rw [hc, MvPolynomial.eval₂_id]
    rfl]
  exact hzero

#check @closure
#check @mem_closure_iff
#check @subset_closure
#check @closure_mono
#check @Map.eval
#check @Map.eval_apply
#check @Map.mapsTo_closure

/-- The closure API is jointly satisfiable even in a positive-dimensional
space: the identity polynomial map carries the singleton `{0}` into itself. -/
example :
    let f : Map ℚ (Fin 1) (Fin 1) := ⟨fun i => MvPolynomial.X i⟩
    Set.MapsTo f.eval ({0} : Set (Fin 1 → ℚ)) {0} := by
  dsimp
  intro x hx
  rw [Set.mem_singleton_iff] at hx ⊢
  subst x
  funext i
  simp [Map.eval]

#print axioms mem_closure_iff
#print axioms subset_closure
#print axioms closure_mono
#print axioms Map.eval_apply
#print axioms Map.mapsTo_closure

end PolynomialClosure
