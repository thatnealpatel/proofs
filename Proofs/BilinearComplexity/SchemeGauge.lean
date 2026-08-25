import BilinearComplexity.LinearElimination
import BilinearComplexity.SchemeDeformation
import BilinearComplexity.SchemeAction
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Quotient.Basic

set_option autoImplicit false

namespace BilinearComplexity
namespace Scheme
namespace Deformation

variable {k : Type*} {a b c r : ℕ}

/-- The derivative of all independent product-one term scalings, parametrized by two scalars per ordered term. -/
def termScalingDerivative [CommRing k] (S : Scheme k a b c r) :
    (Fin r → k × k) →ₗ[k] Variation k a b c r where
  toFun x := fun s => (
    ((x s).1 + (x s).2) • (S.term s).1,
    (-(x s).1) • (S.term s).2.1,
    (-(x s).2) • (S.term s).2.2)
  map_add' x y := by
    funext s
    apply Prod.ext
    · funext i
      simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add, Pi.smul_apply, smul_eq_mul]
      ring
    · apply Prod.ext
      · funext j
        simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add, Pi.smul_apply, smul_eq_mul]
        ring
      · funext l
        simp only [Pi.add_apply, Prod.snd_add, Pi.smul_apply, smul_eq_mul]
        ring
  map_smul' t x := by
    funext s
    apply Prod.ext
    · funext i
      simp only [Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, smul_eq_mul]
      ring
    · apply Prod.ext
      · funext j
        simp only [Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, smul_eq_mul]
        ring
      · funext l
        simp only [Pi.smul_apply, Prod.smul_snd, RingHom.id_apply, smul_eq_mul]
        ring

/-- Insert one pair of scaling parameters at one ordered term and zero at every other term. -/
def localScalingParameters [CommRing k] (s : Fin r) :
    (k × k) →ₗ[k] (Fin r → k × k) where
  toFun x t := if t = s then x else 0
  map_add' x y := by
    funext t
    by_cases h : t = s <;> simp only [h, if_true, if_false, Pi.add_apply, add_zero]
  map_smul' q x := by
    funext t
    by_cases h : t = s <;>
      simp only [h, if_true, if_false, Pi.smul_apply, RingHom.id_apply, smul_zero]

/-- The two-parameter derivative of product-one scaling at a single ordered term. -/
def localTermScalingDerivative [CommRing k] (S : Scheme k a b c r) (s : Fin r) :
    (k × k) →ₗ[k] Variation k a b c r :=
  (termScalingDerivative S).comp (localScalingParameters s)

/-- The local derivative scaling the first factor up and the second factor down. -/
def firstSecondScalingDirection [CommRing k] (S : Scheme k a b c r) (s : Fin r) :
    Variation k a b c r :=
  localTermScalingDerivative S s (1, 0)

/-- The local derivative scaling the first factor up and the third factor down. -/
def firstThirdScalingDirection [CommRing k] (S : Scheme k a b c r) (s : Fin r) :
    Variation k a b c r :=
  localTermScalingDerivative S s (0, 1)

/-- Concrete local scaling directions for one nonzero scalar rank-one term. -/
example :
    let S : Scheme (ZMod 5) 1 1 1 1 := ⟨fun _ => (![1], ![2], ![3])⟩
    firstSecondScalingDirection S 0 0 = (![1], ![3], ![0]) ∧
      firstThirdScalingDirection S 0 0 = (![1], ![0], ![2]) := by
  decide

/-- Every concrete term-scaling derivative cancels directly in the Jacobian. -/
theorem jacobian_termScalingDerivative [CommRing k] (S : Scheme k a b c r)
    (x : Fin r → k × k) : jacobian S (termScalingDerivative S x) = 0 := by
  funext i j l
  simp only [jacobian_apply, linearCoefficient, Pi.zero_apply]
  apply Finset.sum_eq_zero
  intro s _hs
  change (((x s).1 + (x s).2) * (S.term s).1 i) *
      (S.term s).2.1 j * (S.term s).2.2 l +
      (S.term s).1 i * (-(x s).1 * (S.term s).2.1 j) * (S.term s).2.2 l +
      (S.term s).1 i * (S.term s).2.1 j * (-(x s).2 * (S.term s).2.2 l) = 0
  ring

/-- The first/second local scaling direction lies in the Jacobian kernel. -/
theorem firstSecondScalingDirection_mem_ker [CommRing k] (S : Scheme k a b c r)
    (s : Fin r) : firstSecondScalingDirection S s ∈ LinearMap.ker (jacobian S) := by
  exact jacobian_termScalingDerivative S (localScalingParameters s (1, 0))

/-- The first/third local scaling direction lies in the Jacobian kernel. -/
theorem firstThirdScalingDirection_mem_ker [CommRing k] (S : Scheme k a b c r)
    (s : Fin r) : firstThirdScalingDirection S s ∈ LinearMap.ker (jacobian S) := by
  exact jacobian_termScalingDerivative S (localScalingParameters s (0, 1))

/-- A nonzero evaluated rank-one term has a nonzero first factor. -/
theorem first_factor_ne_zero_of_termNonzero [CommSemiring k] (S : Scheme k a b c r)
    (s : Fin r) (hs : S.TermNonzero s) : (S.term s).1 ≠ 0 := by
  intro hzero
  apply hs
  funext i j l
  simp only [TriadData.eval, triad, Pi.zero_apply]
  rw [show (S.term s).1 i = 0 by rw [hzero]; rfl]
  simp only [zero_mul]

/-- A nonzero evaluated rank-one term has a nonzero second factor. -/
theorem second_factor_ne_zero_of_termNonzero [CommSemiring k] (S : Scheme k a b c r)
    (s : Fin r) (hs : S.TermNonzero s) : (S.term s).2.1 ≠ 0 := by
  intro hzero
  apply hs
  funext i j l
  simp only [TriadData.eval, triad, Pi.zero_apply]
  rw [show (S.term s).2.1 j = 0 by rw [hzero]; rfl]
  simp only [mul_zero, zero_mul]

/-- A nonzero evaluated rank-one term has a nonzero third factor. -/
theorem third_factor_ne_zero_of_termNonzero [CommSemiring k] (S : Scheme k a b c r)
    (s : Fin r) (hs : S.TermNonzero s) : (S.term s).2.2 ≠ 0 := by
  intro hzero
  apply hs
  funext i j l
  simp only [TriadData.eval, triad, Pi.zero_apply]
  rw [show (S.term s).2.2 l = 0 by rw [hzero]; rfl]
  simp only [mul_zero]

/-- For a nonzero term over a field, its two scaling parameters give distinct derivative directions. -/
theorem localTermScalingDerivative_injective [Field k] (S : Scheme k a b c r)
    (s : Fin r) (hs : S.TermNonzero s) :
    Function.Injective (localTermScalingDerivative S s) := by
  intro x y hxy
  apply Prod.ext
  · have hsecond := congrArg (fun d : Variation k a b c r => (d s).2.1) hxy
    have hxsecond : ((localTermScalingDerivative S s) x s).2.1 =
        (-(x.1)) • (S.term s).2.1 := by
      change (-(if s = s then x else 0).1) • (S.term s).2.1 = _
      rw [if_pos rfl]
    have hysecond : ((localTermScalingDerivative S s) y s).2.1 =
        (-(y.1)) • (S.term s).2.1 := by
      change (-(if s = s then y else 0).1) • (S.term s).2.1 = _
      rw [if_pos rfl]
    rw [hxsecond, hysecond] at hsecond
    have hfactor := second_factor_ne_zero_of_termNonzero S s hs
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hfactor
    have hcoord := congrFun hsecond j
    change (-(x.1) * (S.term s).2.1 j) =
      (-(y.1) * (S.term s).2.1 j) at hcoord
    exact neg_injective (mul_right_cancel₀ hj hcoord)
  · have hthird := congrArg (fun d : Variation k a b c r => (d s).2.2) hxy
    have hxthird : ((localTermScalingDerivative S s) x s).2.2 =
        (-(x.2)) • (S.term s).2.2 := by
      change (-(if s = s then x else 0).2) • (S.term s).2.2 = _
      rw [if_pos rfl]
    have hythird : ((localTermScalingDerivative S s) y s).2.2 =
        (-(y.2)) • (S.term s).2.2 := by
      change (-(if s = s then y else 0).2) • (S.term s).2.2 = _
      rw [if_pos rfl]
    rw [hxthird, hythird] at hthird
    have hfactor := third_factor_ne_zero_of_termNonzero S s hs
    obtain ⟨l, hl⟩ := Function.ne_iff.mp hfactor
    have hcoord := congrFun hthird l
    change (-(x.2) * (S.term s).2.2 l) =
      (-(y.2) * (S.term s).2.2 l) at hcoord
    exact neg_injective (mul_right_cancel₀ hl hcoord)

/-- At a nonzero term, neither of the two audited local scaling directions degenerates to zero. -/
theorem scalingDirections_ne_zero [Field k] (S : Scheme k a b c r) (s : Fin r)
    (hs : S.TermNonzero s) :
    firstSecondScalingDirection S s ≠ 0 ∧ firstThirdScalingDirection S s ≠ 0 := by
  have hinj := localTermScalingDerivative_injective S s hs
  constructor
  · intro hzero
    have h := hinj (hzero.trans (map_zero (localTermScalingDerivative S s)).symm)
    exact one_ne_zero (congrArg Prod.fst h)
  · intro hzero
    have h := hinj (hzero.trans (map_zero (localTermScalingDerivative S s)).symm)
    exact one_ne_zero (congrArg Prod.snd h)

variable {n₁ n₂ n₃ : ℕ}

/-- Three arbitrary vertex endomorphisms parametrizing the derivative of sandwich action. -/
abbrev SandwichLie (k : Type*) (n₁ n₂ n₃ : ℕ) :=
  Matrix (Fin n₁) (Fin n₁) k × Matrix (Fin n₂) (Fin n₂) k ×
    Matrix (Fin n₃) (Fin n₃) k

/-- The infinitesimal sandwich map `(AU-UB, BV-VC, CW-WA)` on every ordered matrix term. -/
def infinitesimalSandwich [CommRing k] (S : MatrixScheme k n₁ n₂ n₃ r) :
    SandwichLie k n₁ n₂ n₃ →ₗ[k]
      Variation k (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) r where
  toFun X := fun s => (
    flattenMatrix (X.1 * reshapeVector (S.term s).1 -
      reshapeVector (S.term s).1 * X.2.1),
    flattenMatrix (X.2.1 * reshapeVector (S.term s).2.1 -
      reshapeVector (S.term s).2.1 * X.2.2),
    flattenMatrix (X.2.2 * reshapeVector (S.term s).2.2 -
      reshapeVector (S.term s).2.2 * X.1))
  map_add' X Y := by
    funext s
    apply Prod.ext
    · funext z
      change (((X.1 + Y.1) * reshapeVector (S.term s).1 -
          reshapeVector (S.term s).1 * (X.2.1 + Y.2.1))
            ((matrixIndexEquiv n₁ n₂).symm z).1 ((matrixIndexEquiv n₁ n₂).symm z).2) =
        ((X.1 * reshapeVector (S.term s).1 - reshapeVector (S.term s).1 * X.2.1)
            ((matrixIndexEquiv n₁ n₂).symm z).1 ((matrixIndexEquiv n₁ n₂).symm z).2) +
          ((Y.1 * reshapeVector (S.term s).1 - reshapeVector (S.term s).1 * Y.2.1)
            ((matrixIndexEquiv n₁ n₂).symm z).1 ((matrixIndexEquiv n₁ n₂).symm z).2)
      simp only [Matrix.add_mul, Matrix.mul_add,
        Matrix.add_apply, Matrix.sub_apply]
      ring
    · apply Prod.ext
      · funext z
        change (((X.2.1 + Y.2.1) * reshapeVector (S.term s).2.1 -
            reshapeVector (S.term s).2.1 * (X.2.2 + Y.2.2))
              ((matrixIndexEquiv n₂ n₃).symm z).1 ((matrixIndexEquiv n₂ n₃).symm z).2) =
          ((X.2.1 * reshapeVector (S.term s).2.1 -
              reshapeVector (S.term s).2.1 * X.2.2)
              ((matrixIndexEquiv n₂ n₃).symm z).1 ((matrixIndexEquiv n₂ n₃).symm z).2) +
            ((Y.2.1 * reshapeVector (S.term s).2.1 -
              reshapeVector (S.term s).2.1 * Y.2.2)
              ((matrixIndexEquiv n₂ n₃).symm z).1 ((matrixIndexEquiv n₂ n₃).symm z).2)
        simp only [Matrix.add_mul, Matrix.mul_add,
          Matrix.add_apply, Matrix.sub_apply]
        ring
      · funext z
        change (((X.2.2 + Y.2.2) * reshapeVector (S.term s).2.2 -
            reshapeVector (S.term s).2.2 * (X.1 + Y.1))
              ((matrixIndexEquiv n₃ n₁).symm z).1 ((matrixIndexEquiv n₃ n₁).symm z).2) =
          ((X.2.2 * reshapeVector (S.term s).2.2 -
              reshapeVector (S.term s).2.2 * X.1)
              ((matrixIndexEquiv n₃ n₁).symm z).1 ((matrixIndexEquiv n₃ n₁).symm z).2) +
            ((Y.2.2 * reshapeVector (S.term s).2.2 -
              reshapeVector (S.term s).2.2 * Y.1)
              ((matrixIndexEquiv n₃ n₁).symm z).1 ((matrixIndexEquiv n₃ n₁).symm z).2)
        simp only [Matrix.add_mul, Matrix.mul_add,
          Matrix.add_apply, Matrix.sub_apply]
        ring
  map_smul' t X := by
    funext s
    apply Prod.ext
    · funext z
      change (((t • X.1) * reshapeVector (S.term s).1 -
          reshapeVector (S.term s).1 * (t • X.2.1))
            ((matrixIndexEquiv n₁ n₂).symm z).1 ((matrixIndexEquiv n₁ n₂).symm z).2) =
        t * ((X.1 * reshapeVector (S.term s).1 - reshapeVector (S.term s).1 * X.2.1)
            ((matrixIndexEquiv n₁ n₂).symm z).1 ((matrixIndexEquiv n₁ n₂).symm z).2)
      simp only [Matrix.smul_mul, Matrix.mul_smul,
        Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
      ring
    · apply Prod.ext
      · funext z
        change (((t • X.2.1) * reshapeVector (S.term s).2.1 -
            reshapeVector (S.term s).2.1 * (t • X.2.2))
              ((matrixIndexEquiv n₂ n₃).symm z).1 ((matrixIndexEquiv n₂ n₃).symm z).2) =
          t * ((X.2.1 * reshapeVector (S.term s).2.1 -
              reshapeVector (S.term s).2.1 * X.2.2)
              ((matrixIndexEquiv n₂ n₃).symm z).1 ((matrixIndexEquiv n₂ n₃).symm z).2)
        simp only [Matrix.smul_mul, Matrix.mul_smul,
          Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
        ring
      · funext z
        change (((t • X.2.2) * reshapeVector (S.term s).2.2 -
            reshapeVector (S.term s).2.2 * (t • X.1))
              ((matrixIndexEquiv n₃ n₁).symm z).1 ((matrixIndexEquiv n₃ n₁).symm z).2) =
          t * ((X.2.2 * reshapeVector (S.term s).2.2 -
              reshapeVector (S.term s).2.2 * X.1)
              ((matrixIndexEquiv n₃ n₁).symm z).1 ((matrixIndexEquiv n₃ n₁).symm z).2)
        simp only [Matrix.smul_mul, Matrix.mul_smul,
          Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
        ring

/-- First-factor coordinates of the infinitesimal sandwich map are `AU-UB`. -/
@[simp] theorem matrixEntry_infinitesimalSandwich_first [CommRing k]
    (S : MatrixScheme k n₁ n₂ n₃ r) (X : SandwichLie k n₁ n₂ n₃)
    (s : Fin r) (i : Fin n₁) (j : Fin n₂) :
    matrixEntry ((infinitesimalSandwich S X) s).1 i j =
      (∑ p, X.1 i p * matrixEntry (S.term s).1 p j) -
        ∑ q, matrixEntry (S.term s).1 i q * X.2.1 q j := by
  change matrixEntry (flattenMatrix (X.1 * reshapeVector (S.term s).1 -
      reshapeVector (S.term s).1 * X.2.1)) i j = _
  rw [flattenMatrix_entry]
  simp only [Matrix.sub_apply, Matrix.mul_apply, reshapeVector_apply]

/-- Second-factor coordinates of the infinitesimal sandwich map are `BV-VC`. -/
@[simp] theorem matrixEntry_infinitesimalSandwich_second [CommRing k]
    (S : MatrixScheme k n₁ n₂ n₃ r) (X : SandwichLie k n₁ n₂ n₃)
    (s : Fin r) (j : Fin n₂) (l : Fin n₃) :
    matrixEntry ((infinitesimalSandwich S X) s).2.1 j l =
      (∑ q, X.2.1 j q * matrixEntry (S.term s).2.1 q l) -
        ∑ t, matrixEntry (S.term s).2.1 j t * X.2.2 t l := by
  change matrixEntry (flattenMatrix (X.2.1 * reshapeVector (S.term s).2.1 -
      reshapeVector (S.term s).2.1 * X.2.2)) j l = _
  rw [flattenMatrix_entry]
  simp only [Matrix.sub_apply, Matrix.mul_apply, reshapeVector_apply]

/-- Third-factor coordinates of the infinitesimal sandwich map are `CW-WA`. -/
@[simp] theorem matrixEntry_infinitesimalSandwich_third [CommRing k]
    (S : MatrixScheme k n₁ n₂ n₃ r) (X : SandwichLie k n₁ n₂ n₃)
    (s : Fin r) (l : Fin n₃) (i : Fin n₁) :
    matrixEntry ((infinitesimalSandwich S X) s).2.2 l i =
      (∑ t, X.2.2 l t * matrixEntry (S.term s).2.2 t i) -
        ∑ p, matrixEntry (S.term s).2.2 l p * X.1 p i := by
  change matrixEntry (flattenMatrix (X.2.2 * reshapeVector (S.term s).2.2 -
      reshapeVector (S.term s).2.2 * X.1)) l i = _
  rw [flattenMatrix_entry]
  simp only [Matrix.sub_apply, Matrix.mul_apply, reshapeVector_apply]

/-- For a Brent decomposition, every infinitesimal sandwich direction cancels directly in the Jacobian. -/
theorem jacobian_infinitesimalSandwich [CommRing k]
    (S : MatrixScheme k n₁ n₂ n₃ r) (hS : S.Brent)
    (X : SandwichLie k n₁ n₂ n₃) : jacobian S (infinitesimalSandwich S X) = 0 := by
  rcases X with ⟨A, B, C⟩
  funext x y z
  obtain ⟨⟨i, j⟩, rfl⟩ := (matrixIndexEquiv n₁ n₂).surjective x
  obtain ⟨⟨j', l⟩, rfl⟩ := (matrixIndexEquiv n₂ n₃).surjective y
  obtain ⟨⟨l', i'⟩, rfl⟩ := (matrixIndexEquiv n₃ n₁).surjective z
  change (∑ s, (
    matrixEntry ((infinitesimalSandwich S (A, B, C)) s).1 i j *
        matrixEntry (S.term s).2.1 j' l * matrixEntry (S.term s).2.2 l' i' +
      matrixEntry (S.term s).1 i j *
        matrixEntry ((infinitesimalSandwich S (A, B, C)) s).2.1 j' l *
          matrixEntry (S.term s).2.2 l' i' +
      matrixEntry (S.term s).1 i j * matrixEntry (S.term s).2.1 j' l *
        matrixEntry ((infinitesimalSandwich S (A, B, C)) s).2.2 l' i')) = 0
  simp only [matrixEntry_infinitesimalSandwich_first,
    matrixEntry_infinitesimalSandwich_second, matrixEntry_infinitesimalSandwich_third]
  have hApos :
      (∑ s, (∑ p, A i p * matrixEntry (S.term s).1 p j) *
        matrixEntry (S.term s).2.1 j' l * matrixEntry (S.term s).2.2 l' i') =
      A i i' * ((if j = j' then 1 else 0) * (if l = l' then 1 else 0)) := by
    calc
      _ = ∑ p, A i p * (∑ s, matrixEntry (S.term s).1 p j *
          matrixEntry (S.term s).2.1 j' l * matrixEntry (S.term s).2.2 l' i') := by
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro p _hp
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _hs
        ring
      _ = _ := by
        apply Finset.sum_congr rfl
        intro p _hp
        rw [hS p j j' l l' i']
      _ = _ := by
        by_cases hj : j = j' <;> by_cases hl : l = l' <;> simp [hj, hl]
  have hAneg :
      (∑ s, matrixEntry (S.term s).1 i j * matrixEntry (S.term s).2.1 j' l *
        (∑ p, matrixEntry (S.term s).2.2 l' p * A p i')) =
      A i i' * ((if j = j' then 1 else 0) * (if l = l' then 1 else 0)) := by
    calc
      _ = ∑ p, (∑ s, matrixEntry (S.term s).1 i j *
          matrixEntry (S.term s).2.1 j' l * matrixEntry (S.term s).2.2 l' p) *
            A p i' := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro p _hp
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro s _hs
        ring
      _ = _ := by
        apply Finset.sum_congr rfl
        intro p _hp
        rw [hS i j j' l l' p]
      _ = _ := by
        by_cases hj : j = j' <;> by_cases hl : l = l' <;> simp [hj, hl]
  have hBneg :
      (∑ s, (∑ q, matrixEntry (S.term s).1 i q * B q j) *
        matrixEntry (S.term s).2.1 j' l * matrixEntry (S.term s).2.2 l' i') =
      B j' j * ((if l = l' then 1 else 0) * (if i = i' then 1 else 0)) := by
    calc
      _ = ∑ q, (∑ s, matrixEntry (S.term s).1 i q *
          matrixEntry (S.term s).2.1 j' l * matrixEntry (S.term s).2.2 l' i') *
            B q j := by
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro q _hq
        apply Finset.sum_congr rfl
        intro s _hs
        ring
      _ = _ := by
        apply Finset.sum_congr rfl
        intro q _hq
        rw [hS i q j' l l' i']
      _ = _ := by
        by_cases hl : l = l' <;> by_cases hi : i = i' <;> simp [hl, hi]
  have hBpos :
      (∑ s, matrixEntry (S.term s).1 i j *
        (∑ q, B j' q * matrixEntry (S.term s).2.1 q l) *
          matrixEntry (S.term s).2.2 l' i') =
      B j' j * ((if l = l' then 1 else 0) * (if i = i' then 1 else 0)) := by
    calc
      _ = ∑ q, B j' q * (∑ s, matrixEntry (S.term s).1 i j *
          matrixEntry (S.term s).2.1 q l * matrixEntry (S.term s).2.2 l' i') := by
        simp_rw [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro q _hq
        apply Finset.sum_congr rfl
        intro s _hs
        ring
      _ = _ := by
        apply Finset.sum_congr rfl
        intro q _hq
        rw [hS i j q l l' i']
      _ = _ := by
        by_cases hl : l = l' <;> by_cases hi : i = i' <;> simp [hl, hi]
  have hCneg :
      (∑ s, matrixEntry (S.term s).1 i j *
        (∑ t, matrixEntry (S.term s).2.1 j' t * C t l) *
          matrixEntry (S.term s).2.2 l' i') =
      C l' l * ((if j = j' then 1 else 0) * (if i = i' then 1 else 0)) := by
    calc
      _ = ∑ t, (∑ s, matrixEntry (S.term s).1 i j *
          matrixEntry (S.term s).2.1 j' t * matrixEntry (S.term s).2.2 l' i') *
            C t l := by
        simp_rw [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro t _ht
        apply Finset.sum_congr rfl
        intro s _hs
        ring
      _ = _ := by
        apply Finset.sum_congr rfl
        intro t _ht
        rw [hS i j j' t l' i']
      _ = _ := by
        by_cases hj : j = j' <;> by_cases hi : i = i' <;> simp [hj, hi]
  have hCpos :
      (∑ s, matrixEntry (S.term s).1 i j * matrixEntry (S.term s).2.1 j' l *
        (∑ t, C l' t * matrixEntry (S.term s).2.2 t i')) =
      C l' l * ((if j = j' then 1 else 0) * (if i = i' then 1 else 0)) := by
    calc
      _ = ∑ t, C l' t * (∑ s, matrixEntry (S.term s).1 i j *
          matrixEntry (S.term s).2.1 j' l * matrixEntry (S.term s).2.2 t i') := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro t _ht
        apply Finset.sum_congr rfl
        intro s _hs
        ring
      _ = _ := by
        apply Finset.sum_congr rfl
        intro t _ht
        rw [hS i j j' l t i']
      _ = _ := by
        by_cases hj : j = j' <;> by_cases hi : i = i' <;> simp [hj, hi]
  simp_rw [sub_mul, mul_sub]
  simp_rw [sub_mul]
  simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hApos, hAneg, hBneg, hBpos, hCneg, hCpos]
  ring

/-- Parameters for the combined term-scaling and infinitesimal-sandwich derivative. -/
abbrev GaugeParameters (k : Type*) (n₁ n₂ n₃ r : ℕ) :=
  (Fin r → k × k) × SandwichLie k n₁ n₂ n₃

/-- The combined gauge derivative `dH`, adding term scalings and infinitesimal sandwiches. -/
def gaugeDerivative [CommRing k] (S : MatrixScheme k n₁ n₂ n₃ r) :
    GaugeParameters k n₁ n₂ n₃ r →ₗ[k]
      Variation k (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) r where
  toFun x := termScalingDerivative S x.1 + infinitesimalSandwich S x.2
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    module
  map_smul' t x := by
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, RingHom.id_apply]
    module

/-- The combined gauge space `G` is exactly the range of `dH`. -/
def gaugeSpace [CommRing k] (S : MatrixScheme k n₁ n₂ n₃ r) :
    Submodule k (Variation k (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) r) :=
  LinearMap.range (gaugeDerivative S)

/-- Every term-scaling derivative belongs to the combined gauge space. -/
theorem termScalingDerivative_mem_gaugeSpace [CommRing k]
    (S : MatrixScheme k n₁ n₂ n₃ r) (x : Fin r → k × k) :
    termScalingDerivative S x ∈ gaugeSpace S := by
  refine ⟨(x, 0), ?_⟩
  change termScalingDerivative S x + infinitesimalSandwich S 0 = termScalingDerivative S x
  rw [map_zero, add_zero]

/-- Every infinitesimal sandwich derivative belongs to the combined gauge space. -/
theorem infinitesimalSandwich_mem_gaugeSpace [CommRing k]
    (S : MatrixScheme k n₁ n₂ n₃ r) (X : SandwichLie k n₁ n₂ n₃) :
    infinitesimalSandwich S X ∈ gaugeSpace S := by
  refine ⟨(0, X), ?_⟩
  change termScalingDerivative S 0 + infinitesimalSandwich S X = infinitesimalSandwich S X
  rw [map_zero, zero_add]

/-- At a Brent point every combined gauge derivative lies in the Jacobian kernel. -/
theorem gaugeDerivative_mem_ker [CommRing k] (S : MatrixScheme k n₁ n₂ n₃ r)
    (hS : S.Brent) (x : GaugeParameters k n₁ n₂ n₃ r) :
    gaugeDerivative S x ∈ LinearMap.ker (jacobian S) := by
  change jacobian S (termScalingDerivative S x.1 + infinitesimalSandwich S x.2) = 0
  rw [map_add, jacobian_termScalingDerivative S x.1,
    jacobian_infinitesimalSandwich S hS x.2, add_zero]

/-- At a Brent point the full combined gauge space is contained in the Jacobian kernel. -/
theorem gaugeSpace_le_ker [CommRing k] (S : MatrixScheme k n₁ n₂ n₃ r)
    (hS : S.Brent) : gaugeSpace S ≤ LinearMap.ker (jacobian S) := by
  rintro d ⟨x, rfl⟩
  exact gaugeDerivative_mem_ker S hS x

/-- The ambient normal tangent module uses the intersection of `G` with `ker J` as denominator. -/
abbrev NormalTangent [CommRing k] (S : MatrixScheme k n₁ n₂ n₃ r) :=
  LinearMap.ker (jacobian S) ⧸
    (gaugeSpace S).comap (LinearMap.ker (jacobian S)).subtype

/-- The ambient gauge denominator inside the Jacobian kernel. -/
abbrev ambientGaugeInKernel [CommRing k] (S : MatrixScheme k n₁ n₂ n₃ r) :=
  (gaugeSpace S).comap (LinearMap.ker (jacobian S)).subtype

/-- A proof-carrying gauge normalization is an explicit linear projection onto
ambient gauge directions inside `ker J`.  The range and fixed-point laws certify
that subtracting the projection selects a genuine complement representative. -/
structure GaugeNormalization [CommRing k] (S : MatrixScheme k n₁ n₂ n₃ r) where
  /-- The explicit gauge projection on the Jacobian kernel. -/
  projection : LinearMap.ker (jacobian S) →ₗ[k] LinearMap.ker (jacobian S)
  /-- Every projected vector is an actual ambient gauge direction. -/
  range_le_gauge : LinearMap.range projection ≤ ambientGaugeInKernel S
  /-- The projection fixes every gauge vector in the kernel. -/
  fixes_gauge : ∀ d ∈ ambientGaugeInKernel S, projection d = d

namespace GaugeNormalization

/-- Subtract the certified gauge projection to obtain the normalized kernel representative. -/
def normalized [CommRing k] {S : MatrixScheme k n₁ n₂ n₃ r}
    (N : GaugeNormalization S) :
    LinearMap.ker (jacobian S) →ₗ[k] LinearMap.ker (jacobian S) :=
  LinearMap.id - N.projection

/-- Normalization is literally subtraction of the certified gauge projection. -/
@[simp] theorem normalized_apply [CommRing k] {S : MatrixScheme k n₁ n₂ n₃ r}
    (N : GaugeNormalization S) (d : LinearMap.ker (jacobian S)) :
    N.normalized d = d - N.projection d := rfl

/-- The normalized representative lies in the kernel of the gauge projection. -/
@[simp] theorem projection_normalized [CommRing k]
    {S : MatrixScheme k n₁ n₂ n₃ r} (N : GaugeNormalization S)
    (d : LinearMap.ker (jacobian S)) : N.projection (N.normalized d) = 0 := by
  have hprojection : N.projection d ∈ ambientGaugeInKernel S :=
    N.range_le_gauge ⟨d, rfl⟩
  rw [normalized_apply, map_sub,
    N.fixes_gauge (N.projection d) hprojection, sub_self]

/-- A kernel vector normalizes to zero exactly when it was gauge. -/
theorem normalized_eq_zero_iff [CommRing k]
    {S : MatrixScheme k n₁ n₂ n₃ r} (N : GaugeNormalization S)
    (d : LinearMap.ker (jacobian S)) :
    N.normalized d = 0 ↔ d ∈ ambientGaugeInKernel S := by
  constructor
  · intro hzero
    have heq : d = N.projection d := by
      rw [normalized_apply, sub_eq_zero] at hzero
      exact hzero
    rw [heq]
    exact N.range_le_gauge ⟨d, rfl⟩
  · intro hgauge
    rw [normalized_apply, N.fixes_gauge d hgauge, sub_self]

/-- Gauge normalization preserves the class in the exact ambient normal quotient. -/
theorem normalClass_normalized [CommRing k]
    {S : MatrixScheme k n₁ n₂ n₃ r} (N : GaugeNormalization S)
    (d : LinearMap.ker (jacobian S)) :
    (ambientGaugeInKernel S).mkQ (N.normalized d) =
      (ambientGaugeInKernel S).mkQ d := by
  rw [normalized_apply, map_sub]
  have hprojection : (ambientGaugeInKernel S).mkQ (N.projection d) = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact N.range_le_gauge ⟨d, rfl⟩
  rw [hprojection, sub_zero]

end GaugeNormalization

/-- The kernel of a masked Jacobian remains in the masked variation domain. -/
def restrictedKernel [CommRing k] (S : Scheme k a b c r) (M : VariationMask a b c r) :
    Submodule k (M.allowed (k := k)) :=
  LinearMap.ker (M.restrictedJacobian S)

/-- Restricted gauge is the ambient gauge preimage, then restricted to the masked kernel subtype. -/
def restrictedGauge [CommRing k] (S : MatrixScheme k n₁ n₂ n₃ r)
    (M : VariationMask (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) r) :
    Submodule k (restrictedKernel S M) :=
  ((gaugeSpace S).comap M.inclusion).comap (restrictedKernel S M).subtype

/-- If a normalized kernel representative is supported in a mask whose
restricted kernel certificate proves every vector gauge, that representative is zero. -/
theorem GaugeNormalization.normalized_eq_zero_of_supported_of_restrictedGauge_eq_top
    [CommRing k] (S : MatrixScheme k n₁ n₂ n₃ r)
    (M : VariationMask (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) r)
    (N : GaugeNormalization S) (htop : restrictedGauge S M = ⊤)
    (d : LinearMap.ker (jacobian S))
    (hmask : (N.normalized d).1 ∈ M.allowed) : N.normalized d = 0 := by
  let restricted : restrictedKernel S M :=
    ⟨⟨(N.normalized d).1, hmask⟩, (N.normalized d).2⟩
  have hrestricted : restricted ∈ restrictedGauge S M := by
    rw [htop]
    exact Submodule.mem_top
  have hnormalizedGauge : N.normalized d ∈ ambientGaugeInKernel S := by
    change M.inclusion restricted.1 ∈ gaugeSpace S at hrestricted
    change (N.normalized d).1 ∈ gaugeSpace S
    exact hrestricted
  calc
    N.normalized d = N.projection (N.normalized d) :=
      (N.fixes_gauge (N.normalized d) hnormalizedGauge).symm
    _ = 0 := N.projection_normalized d

/-- At a Brent point the ambient gauge preimage under any mask lies in the restricted kernel. -/
theorem gauge_preimage_le_restrictedKernel [CommRing k]
    (S : MatrixScheme k n₁ n₂ n₃ r) (hS : S.Brent)
    (M : VariationMask (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) r) :
    (gaugeSpace S).comap M.inclusion ≤ restrictedKernel S M := by
  intro d hd
  change jacobian S (M.inclusion d) = 0
  exact gaugeSpace_le_ker S hS hd

/-- A masked kernel vector maps canonically to the ambient Jacobian kernel. -/
def restrictedKernelToAmbient [CommRing k] (S : Scheme k a b c r)
    (M : VariationMask a b c r) :
    restrictedKernel S M →ₗ[k] LinearMap.ker (jacobian S) where
  toFun d := ⟨M.inclusion d.1, d.2⟩
  map_add' d e := by
    apply Subtype.ext
    simp only [Submodule.coe_add, map_add]
  map_smul' t d := by
    apply Subtype.ext
    simp only [Submodule.coe_smul_of_tower, map_smul, RingHom.id_apply]

/-- The restricted normal tangent quotient uses exactly the restricted gauge submodule. -/
abbrev RestrictedNormalTangent [CommRing k] (S : MatrixScheme k n₁ n₂ n₃ r)
    (M : VariationMask (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) r) :=
  ↥(restrictedKernel S M) ⧸ (restrictedGauge S M).toAddSubgroup

/-- Scalar multiplication on the restricted normal tangent descends from its kernel module. -/
instance restrictedNormalTangentSMul [CommRing k] (S : MatrixScheme k n₁ n₂ n₃ r)
    (M : VariationMask (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) r) :
    SMul k (RestrictedNormalTangent S M) where
  smul t := Quotient.map' (t • ·) (by
    intro x y hxy
    rw [QuotientAddGroup.leftRel_apply] at hxy ⊢
    change -(t • x) + t • y ∈ restrictedGauge S M
    simpa only [smul_neg, smul_add] using (restrictedGauge S M).smul_mem t hxy)

/-- The exact restricted normal tangent quotient carries its descended module structure. -/
instance restrictedNormalTangentModule [CommRing k] (S : MatrixScheme k n₁ n₂ n₃ r)
    (M : VariationMask (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) r) :
    Module k (RestrictedNormalTangent S M) := by
  let q : restrictedKernel S M →+ RestrictedNormalTangent S M :=
    { toFun := fun d => Quotient.mk'' d
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hq : Function.Surjective q := by
    intro z
    refine Quotient.inductionOn' z ?_
    intro d
    exact ⟨d, rfl⟩
  exact Function.Surjective.module k q hq (fun _ _ => rfl)

/-- The zero restricted normal class is represented by the zero kernel vector. -/
def restrictedNormalZeroClass [CommRing k] (S : MatrixScheme k n₁ n₂ n₃ r)
    (M : VariationMask (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) r) :
    RestrictedNormalTangent S M :=
  Quotient.mk'' 0

/-- The quotient class of a masked kernel vector in the restricted normal tangent. -/
def restrictedNormalClass [CommRing k] (S : MatrixScheme k n₁ n₂ n₃ r)
    (M : VariationMask (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) r)
    (d : restrictedKernel S M) : RestrictedNormalTangent S M :=
  Quotient.mk'' d

/-- Scalar multiplication of a restricted normal class is represented by scalar multiplication in the kernel. -/
@[simp]
theorem restrictedNormalClass_smul [CommRing k] (S : MatrixScheme k n₁ n₂ n₃ r)
    (M : VariationMask (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) r)
    (t : k) (d : restrictedKernel S M) :
    t • restrictedNormalClass S M d = restrictedNormalClass S M (t • d) := by
  rfl

/-- The restricted quotient for one binary scalar term has its descended module structure. -/
example :
    Module (ZMod 2)
      (RestrictedNormalTangent
        (⟨fun _ => (![1], ![1], ![1])⟩ : MatrixScheme (ZMod 2) 1 1 1 1)
        (VariationMask.full {0})) := by
  infer_instance

/-- The ambient normal class of the image of a masked kernel vector. -/
def ambientNormalClass [CommRing k] (S : MatrixScheme k n₁ n₂ n₃ r)
    (M : VariationMask (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) r)
    (d : restrictedKernel S M) : NormalTangent S :=
  ((gaugeSpace S).comap (LinearMap.ker (jacobian S)).subtype).mkQ
    (restrictedKernelToAmbient S M d)

/-- A restricted kernel vector is nongauge exactly when its restricted quotient class differs from the zero class. -/
theorem not_mem_restrictedGauge_iff_restrictedNormalClass_ne_zero [CommRing k]
    (S : MatrixScheme k n₁ n₂ n₃ r)
    (M : VariationMask (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) r)
    (d : restrictedKernel S M) :
    d ∉ restrictedGauge S M ↔
      restrictedNormalClass S M d ≠ restrictedNormalZeroClass S M := by
  change (¬d ∈ restrictedGauge S M) ↔
    ¬(Quotient.mk'' d : ↥(restrictedKernel S M) ⧸
      (restrictedGauge S M).toAddSubgroup) = Quotient.mk'' 0
  rw [Quotient.eq'']
  rw [QuotientAddGroup.leftRel_apply]
  have hiff : d ∈ restrictedGauge S M ↔
      -d + 0 ∈ (restrictedGauge S M).toAddSubgroup := by
    calc
      _ ↔ -d ∈ (restrictedGauge S M).toAddSubgroup :=
        (@AddSubgroup.neg_mem_iff _ _ ((restrictedGauge S M).toAddSubgroup) d).symm
      _ ↔ _ := by rw [add_zero]
  exact not_congr hiff

/-- For every mask, nongauge in the restricted kernel is equivalent to a nonzero ambient normal class. -/
theorem not_mem_restrictedGauge_iff_ambientNormalClass_ne_zero [CommRing k]
    (S : MatrixScheme k n₁ n₂ n₃ r)
    (M : VariationMask (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) r)
    (d : restrictedKernel S M) :
    d ∉ restrictedGauge S M ↔ ambientNormalClass S M d ≠ 0 := by
  change d ∉ restrictedGauge S M ↔
    ¬((gaugeSpace S).comap (LinearMap.ker (jacobian S)).subtype).mkQ
      (restrictedKernelToAmbient S M d) = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rfl

/-- A genuinely first nonzero coefficient of a semantic order-three arc,
viewed in the ambient Jacobian kernel. -/
def arcLeadingKernel [CommRing k] (S : MatrixScheme k n₁ n₂ n₃ r)
    (A : OrderThreeArc S) (q : Fin 3)
    (hlower : ∀ p, p < q → A.coefficient p = 0)
    (hnonzero : A.coefficient q ≠ 0) : LinearMap.ker (jacobian S) :=
  ⟨A.coefficient q, (A.genuine_first_nonzero_mem_ker q hlower hnonzero).2⟩

/-- The ambient leading-kernel witness has the selected arc coefficient as its value. -/
@[simp] theorem arcLeadingKernel_val [CommRing k]
    (S : MatrixScheme k n₁ n₂ n₃ r) (A : OrderThreeArc S) (q : Fin 3)
    (hlower : ∀ p, p < q → A.coefficient p = 0)
    (hnonzero : A.coefficient q ≠ 0) :
    (arcLeadingKernel S A q hlower hnonzero).1 = A.coefficient q := rfl

/-- The ambient leading-kernel witness is genuinely nonzero. -/
theorem arcLeadingKernel_ne_zero [CommRing k]
    (S : MatrixScheme k n₁ n₂ n₃ r) (A : OrderThreeArc S) (q : Fin 3)
    (hlower : ∀ p, p < q → A.coefficient p = 0)
    (hnonzero : A.coefficient q ≠ 0) :
    arcLeadingKernel S A q hlower hnonzero ≠ 0 := by
  intro hzero
  apply hnonzero
  change (arcLeadingKernel S A q hlower hnonzero).1 = 0
  exact congrArg Subtype.val hzero

/-- A supported genuinely first nonzero coefficient of a semantic order-three
arc, viewed in the masked Jacobian kernel. -/
def arcLeadingRestrictedKernel [CommRing k]
    (S : MatrixScheme k n₁ n₂ n₃ r)
    (M : VariationMask (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) r)
    (A : OrderThreeArc S) (q : Fin 3)
    (hlower : ∀ p, p < q → A.coefficient p = 0)
    (hnonzero : A.coefficient q ≠ 0)
    (hmask : A.coefficient q ∈ M.allowed) : restrictedKernel S M :=
  ⟨⟨A.coefficient q, hmask⟩,
    (arcLeadingKernel S A q hlower hnonzero).2⟩

/-- A masked first nonzero coefficient is restricted nongauge exactly when it
is ambient nongauge. -/
theorem arcLeading_not_mem_restrictedGauge_iff [CommRing k]
    (S : MatrixScheme k n₁ n₂ n₃ r)
    (M : VariationMask (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) r)
    (A : OrderThreeArc S) (q : Fin 3)
    (hlower : ∀ p, p < q → A.coefficient p = 0)
    (hnonzero : A.coefficient q ≠ 0)
    (hmask : A.coefficient q ∈ M.allowed) :
    arcLeadingRestrictedKernel S M A q hlower hnonzero hmask ∉
        restrictedGauge S M ↔
      A.coefficient q ∉ gaugeSpace S := by
  rfl

/-- A supported first nonzero coefficient has a nonzero restricted normal
class whenever it is ambient nongauge. -/
theorem arcLeading_restrictedNormalClass_ne_zero [CommRing k]
    (S : MatrixScheme k n₁ n₂ n₃ r)
    (M : VariationMask (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) r)
    (A : OrderThreeArc S) (q : Fin 3)
    (hlower : ∀ p, p < q → A.coefficient p = 0)
    (hnonzero : A.coefficient q ≠ 0)
    (hmask : A.coefficient q ∈ M.allowed)
    (hnongauge : A.coefficient q ∉ gaugeSpace S) :
    restrictedNormalClass S M
        (arcLeadingRestrictedKernel S M A q hlower hnonzero hmask) ≠
      restrictedNormalZeroClass S M := by
  apply (not_mem_restrictedGauge_iff_restrictedNormalClass_ne_zero S M _).mp
  exact (arcLeading_not_mem_restrictedGauge_iff S M A q hlower hnonzero hmask).mpr
    hnongauge

/-- Apply a proof-carrying gauge normalization to the genuinely first nonzero
coefficient of a semantic order-three arc. -/
def normalizedArcLeadingKernel [CommRing k]
    (S : MatrixScheme k n₁ n₂ n₃ r) (N : GaugeNormalization S)
    (A : OrderThreeArc S) (q : Fin 3)
    (hlower : ∀ p, p < q → A.coefficient p = 0)
    (hnonzero : A.coefficient q ≠ 0) : LinearMap.ker (jacobian S) :=
  N.normalized (arcLeadingKernel S A q hlower hnonzero)

/-- The normalized semantic-arc leading coefficient is the certified
normalization of its ambient kernel witness. -/
@[simp] theorem normalizedArcLeadingKernel_apply [CommRing k]
    (S : MatrixScheme k n₁ n₂ n₃ r) (N : GaugeNormalization S)
    (A : OrderThreeArc S) (q : Fin 3)
    (hlower : ∀ p, p < q → A.coefficient p = 0)
    (hnonzero : A.coefficient q ≠ 0) :
    normalizedArcLeadingKernel S N A q hlower hnonzero =
      N.normalized (arcLeadingKernel S A q hlower hnonzero) := rfl

/-- Gauge normalization preserves the ambient normal class of a semantic arc's
first nonzero coefficient. -/
theorem normalClass_normalizedArcLeadingKernel [CommRing k]
    (S : MatrixScheme k n₁ n₂ n₃ r) (N : GaugeNormalization S)
    (A : OrderThreeArc S) (q : Fin 3)
    (hlower : ∀ p, p < q → A.coefficient p = 0)
    (hnonzero : A.coefficient q ≠ 0) :
    (ambientGaugeInKernel S).mkQ
        (normalizedArcLeadingKernel S N A q hlower hnonzero) =
      (ambientGaugeInKernel S).mkQ
        (arcLeadingKernel S A q hlower hnonzero) :=
  N.normalClass_normalized (arcLeadingKernel S A q hlower hnonzero)

/-- If the normalized leading coefficient is supported in a certified mask
whose restricted kernel is all gauge, then that normalized coefficient
vanishes.  This is a finite order-three, support-scoped conclusion. -/
theorem normalizedArcLeadingKernel_eq_zero_of_supported_of_restrictedGauge_eq_top
    [CommRing k] (S : MatrixScheme k n₁ n₂ n₃ r)
    (M : VariationMask (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) r)
    (N : GaugeNormalization S) (htop : restrictedGauge S M = ⊤)
    (A : OrderThreeArc S) (q : Fin 3)
    (hlower : ∀ p, p < q → A.coefficient p = 0)
    (hnonzero : A.coefficient q ≠ 0)
    (hmask : (normalizedArcLeadingKernel S N A q hlower hnonzero).1 ∈
      M.allowed) :
    normalizedArcLeadingKernel S N A q hlower hnonzero = 0 :=
  GaugeNormalization.normalized_eq_zero_of_supported_of_restrictedGauge_eq_top
    S M N htop (arcLeadingKernel S A q hlower hnonzero) hmask

/-- A certified all-gauge restricted kernel excludes a supported nonzero
normalized leading coefficient of a genuine semantic order-three arc. -/
theorem no_supported_nonzero_normalizedLeading_arc_of_restrictedGauge_eq_top
    [CommRing k] (S : MatrixScheme k n₁ n₂ n₃ r)
    (M : VariationMask (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) r)
    (N : GaugeNormalization S) (htop : restrictedGauge S M = ⊤) :
    ¬ ∃ (A : OrderThreeArc S) (q : Fin 3)
      (hlower : ∀ p, p < q → A.coefficient p = 0)
      (hnonzero : A.coefficient q ≠ 0),
      normalizedArcLeadingKernel S N A q hlower hnonzero ≠ 0 ∧
      (normalizedArcLeadingKernel S N A q hlower hnonzero).1 ∈ M.allowed := by
  rintro ⟨A, q, hlower, hnonzero, hnormalized, hmask⟩
  exact hnormalized
    (normalizedArcLeadingKernel_eq_zero_of_supported_of_restrictedGauge_eq_top
      S M N htop A q hlower hnonzero hmask)

/-- The same finite, support-scoped rejection criterion with the all-gauge fact
presented as the inclusion `⊤ ≤ restrictedGauge`. -/
theorem no_normalizedLeading_arc_of_restrictedKernel_le_gauge [CommRing k]
    (S : MatrixScheme k n₁ n₂ n₃ r)
    (M : VariationMask (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) r)
    (N : GaugeNormalization S)
    (hrigid : (⊤ : Submodule k (restrictedKernel S M)) ≤ restrictedGauge S M) :
    ¬ ∃ (A : OrderThreeArc S) (q : Fin 3)
      (hlower : ∀ p, p < q → A.coefficient p = 0)
      (hnonzero : A.coefficient q ≠ 0),
      normalizedArcLeadingKernel S N A q hlower hnonzero ≠ 0 ∧
      (normalizedArcLeadingKernel S N A q hlower hnonzero).1 ∈ M.allowed := by
  have htop : restrictedGauge S M = ⊤ := top_unique hrigid
  exact no_supported_nonzero_normalizedLeading_arc_of_restrictedGauge_eq_top
    S M N htop

/-- A binary complement certificate excludes every restricted nongauge direction
for an actual characteristic-two scheme once explicit coordinate equivalences
identify the mapped certificate matrix with its restricted Jacobian and identify
the supplied gauge basis with the geometric restricted gauge preimage. -/
theorem certified_restrictedGauge_eq_top_over_charTwo
    {K ambient gauge complement equations : Type*}
    {n₁ n₂ n₃ r : ℕ}
    [Field K] [CharP K 2]
    [Fintype ambient] [Fintype gauge] [Fintype complement]
    [Fintype equations]
    [DecidableEq ambient] [DecidableEq gauge]
    [DecidableEq equations] [DecidableEq complement]
    (d : GaugeComplementDecomposition (ZMod 2) ambient gauge complement)
    (A : Matrix equations ambient (ZMod 2))
    (hGauge : A * d.gaugeBasis = 0)
    (c : EliminationCertificate (A * d.complementBasis)
      (Fintype.card complement))
    (S : MatrixScheme K n₁ n₂ n₃ r)
    (M : VariationMask (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) r)
    (domainCoordinates : (ambient → K) ≃ₗ[K] M.allowed (k := K))
    (equationCoordinates : (equations → K) ≃ₗ[K]
      Tensor K (n₁ * n₂) (n₂ * n₃) (n₃ * n₁))
    (hJacobianCoordinates : ∀ x,
      M.restrictedJacobian S (domainCoordinates x) =
        equationCoordinates
          ((A.map (ZMod.castHom (dvd_refl 2) K)).mulVecLin x))
    (hGaugeCoordinates : ∀ x,
      M.inclusion (domainCoordinates x) ∈ gaugeSpace S ↔
        x ∈ LinearMap.range
          (d.gaugeBasis.map (ZMod.castHom (dvd_refl 2) K)).mulVecLin) :
    restrictedGauge S M = ⊤ := by
  have hmatrix := certified_kernel_eq_mappedGauge_over_charTwo
    (K := K) d A hGauge c
  apply top_unique
  intro v _hv
  let x : ambient → K := domainCoordinates.symm v.1
  have hmatrixZero :
      (A.map (ZMod.castHom (dvd_refl 2) K)).mulVecLin x = 0 := by
    apply equationCoordinates.injective
    rw [map_zero]
    calc
      equationCoordinates
          ((A.map (ZMod.castHom (dvd_refl 2) K)).mulVecLin x) =
          M.restrictedJacobian S (domainCoordinates x) :=
        (hJacobianCoordinates x).symm
      _ = M.restrictedJacobian S v.1 := by
        rw [LinearEquiv.apply_symm_apply]
      _ = 0 := v.2
  have hxKernel : x ∈ LinearMap.ker
      (A.map (ZMod.castHom (dvd_refl 2) K)).mulVecLin := hmatrixZero
  have hxGauge : x ∈ LinearMap.range
      (d.gaugeBasis.map (ZMod.castHom (dvd_refl 2) K)).mulVecLin := by
    rw [← hmatrix]
    exact hxKernel
  change M.inclusion v.1 ∈ gaugeSpace S
  have hgauge := (hGaugeCoordinates x).mpr hxGauge
  simpa [x] using hgauge

/- A nondegenerate binary fixture exercising the certified restricted-gauge bridge. -/
namespace CertifiedBridgeFixture

open Matrix

/-- The binary field used by the certified bridge fixture. -/
abbrev F := ZMod 2

/-- The one-term `1×1×1` binary multiplication scheme. -/
def scheme : MatrixScheme F 1 1 1 1 := ⟨fun _ => (![1], ![1], ![1])⟩

/-- A two-coordinate mask fixing only the third factor. -/
def mask : VariationMask 1 1 1 1 where
  terms := {0}
  first := fun _ => {0}
  second := fun _ => {0}
  third := fun _ => ∅

/-- The concrete one-term scheme satisfies the Brent equations. -/
theorem brent : scheme.Brent := by
  intro i j j' l l' i'
  fin_cases i
  fin_cases j
  fin_cases j'
  fin_cases l
  fin_cases l'
  fin_cases i'
  decide

example : (scheme.term 0).eval ≠ 0 := by decide

/-- Coordinates identifying the two-dimensional masked variation domain. -/
noncomputable def domainCoordinates : (Fin 2 → F) ≃ₗ[F] mask.allowed (k := F) where
  toFun x := ⟨fun _ => (![x 0], ![x 1], ![0]), by
    simp [VariationMask.allowed, mask]
  ⟩
  invFun d := ![(d.1 0).1 0, (d.1 0).2.1 0]
  left_inv x := by
    funext i
    fin_cases i <;> rfl
  right_inv d := by
    apply Subtype.ext
    funext s
    fin_cases s
    rcases d.2 with ⟨_hterms, _hfirst, _hsecond, hthird⟩
    apply Prod.ext
    · funext i
      fin_cases i
      rfl
    · apply Prod.ext
      · funext j
        fin_cases j
        rfl
      · funext l
        fin_cases l
        exact (hthird 0 0 (by simp [mask])).symm
  map_add' x y := by
    apply Subtype.ext
    funext s
    fin_cases s
    ext i <;> fin_cases i <;> rfl
  map_smul' t x := by
    apply Subtype.ext
    funext s
    fin_cases s
    ext i <;> fin_cases i <;> rfl

/-- Coordinates identifying the one-dimensional equation space. -/
noncomputable def equationCoordinates : (Fin 1 → F) ≃ₗ[F] Tensor F 1 1 1 where
  toFun x := fun _ _ _ => x 0
  invFun T := fun _ => T 0 0 0
  left_inv x := by funext i; fin_cases i; rfl
  right_inv T := by funext i j l; fin_cases i; fin_cases j; fin_cases l; rfl
  map_add' x y := by rfl
  map_smul' t x := by rfl

/-- The coordinate matrix `[1,1]` for the restricted Jacobian. -/
def jacobianMatrix : Matrix (Fin 1) (Fin 2) F := !![1, 1]

example : jacobianMatrix = !![1, 1] := rfl

/-- A verified gauge-line/complement-line decomposition of the domain. -/
def gaugeComplement : GaugeComplementDecomposition F (Fin 2) (Fin 1) (Fin 1) := by
  refine
    { gaugeBasis := !![1; 1]
      complementBasis := !![0; 1]
      gaugeCoordinates := !![1, 0]
      complementCoordinates := !![1, 1]
      split := by decide
      gauge_leftInverse := by decide
      complement_leftInverse := by decide
      gaugeCoordinates_complement := by decide
      complementCoordinates_gauge := by decide }

/-- A replayed full-rank elimination certificate on the complement column. -/
def complementCertificate :
    EliminationCertificate (jacobianMatrix * gaugeComplement.complementBasis) 1 := by
  classical
  refine
    { rowEquiv := (finSumFinEquiv (m := 1) (n := 0)).symm
      colEquiv := (finSumFinEquiv (m := 1) (n := 0)).symm
      left := 1
      leftInv := 1
      right := 1
      rightInv := 1
      leftInv_left := by simp
      left_leftInv := by simp
      rightInv_right := by simp
      right_rightInv := by simp
      replay := by decide
      kernelBasis := 0
      kernelCoordinates := 0
      kernelHomotopy := 1
      kernel_zero := by decide
      kernel_split := by decide
      kernel_leftInverse := by decide }

example : jacobianMatrix * gaugeComplement.gaugeBasis = 0 := by decide

/-- The abstract restricted Jacobian agrees with its concrete coordinate matrix. -/
theorem jacobianCoordinates (x : Fin 2 → F) :
    mask.restrictedJacobian scheme (domainCoordinates x) =
      equationCoordinates
        ((jacobianMatrix.map (ZMod.castHom (dvd_refl 2) F)).mulVecLin x) := by
  revert x
  decide

/-- Gauge membership agrees with the concrete gauge-basis column space. -/
theorem gaugeCoordinates (x : Fin 2 → F) :
    mask.inclusion (domainCoordinates x) ∈ gaugeSpace scheme ↔
      x ∈ LinearMap.range
        (gaugeComplement.gaugeBasis.map (ZMod.castHom (dvd_refl 2) F)).mulVecLin := by
  have hmatrix : LinearMap.ker
        (jacobianMatrix.map (ZMod.castHom (dvd_refl 2) F)).mulVecLin =
      LinearMap.range
        (gaugeComplement.gaugeBasis.map (ZMod.castHom (dvd_refl 2) F)).mulVecLin :=
    certified_kernel_eq_mappedGauge_over_charTwo gaugeComplement jacobianMatrix
      (by decide) complementCertificate
  constructor
  · intro hgauge
    have hkernel : mask.restrictedJacobian scheme (domainCoordinates x) = 0 :=
      gaugeSpace_le_ker scheme brent hgauge
    have hmatrixZero :
        (jacobianMatrix.map (ZMod.castHom (dvd_refl 2) F)).mulVecLin x = 0 := by
      apply equationCoordinates.injective
      rw [map_zero, ← jacobianCoordinates x]
      exact hkernel
    rw [← hmatrix]
    exact hmatrixZero
  · rintro ⟨z, hz⟩
    have hz0 := congrFun hz 0
    have hz1 := congrFun hz 1
    have hx : x 1 = x 0 := by
      simpa [gaugeComplement, Matrix.mulVec, dotProduct] using hz1.symm.trans hz0
    have hflat : flattenMatrix (0 : Matrix (Fin 1) (Fin 1) F) = 0 := by decide
    refine ⟨((fun _ => (x 0, 0)), 0), ?_⟩
    change gaugeDerivative scheme ((fun _ => (x 0, 0)), 0) =
      (fun _ => (![x 0], ![x 1], ![0]))
    funext s
    fin_cases s
    apply Prod.ext
    · funext i
      fin_cases i
      simp [gaugeDerivative, termScalingDerivative, infinitesimalSandwich,
        scheme, hflat]
    · apply Prod.ext
      · funext j
        fin_cases j
        simp [gaugeDerivative, termScalingDerivative, infinitesimalSandwich,
          scheme, hx, hflat]
      · funext l
        fin_cases l
        simp [gaugeDerivative, termScalingDerivative, infinitesimalSandwich,
          scheme, hflat]

/-- The certified bridge proves that this nonzero two-dimensional fixture has only gauge kernel. -/
theorem restrictedGauge_eq_top : restrictedGauge scheme mask = ⊤ :=
  certified_restrictedGauge_eq_top_over_charTwo gaugeComplement jacobianMatrix
    (by decide) complementCertificate scheme mask domainCoordinates equationCoordinates
    jacobianCoordinates gaugeCoordinates

/-- The represented singleton term is nonzero, so its scaling tangent directions
are genuine. -/
theorem termNonzero : scheme.TermNonzero 0 := by
  intro hzero
  have hentry := congrFun (congrFun (congrFun hzero 0) 0) 0
  norm_num [scheme, TriadData.eval, triad] at hentry

/-- For the nondegenerate scalar scheme, every ambient Jacobian-kernel vector is
an explicit product-one term scaling. -/
theorem ambientGaugeInKernel_eq_top : ambientGaugeInKernel scheme = ⊤ := by
  apply top_unique
  intro d _hd
  change d.1 ∈ gaugeSpace scheme
  have hentry := congrFun (congrFun (congrFun d.2 0) 0) 0
  change linearCoefficient scheme d.1 0 0 0 = 0 at hentry
  have hsum : (d.1 0).1 0 + (d.1 0).2.1 0 + (d.1 0).2.2 0 = 0 := by
    simpa [scheme, linearCoefficient] using hentry
  have hfirst : (d.1 0).2.1 0 + (d.1 0).2.2 0 = (d.1 0).1 0 := by
    have hneg : (d.1 0).2.1 0 + (d.1 0).2.2 0 = -(d.1 0).1 0 := by
      linear_combination hsum
    simpa only [ZMod.neg_eq_self_mod_two] using hneg
  let x : Fin 1 → F × F :=
    fun _ => ((d.1 0).2.1 0, (d.1 0).2.2 0)
  have hx : termScalingDerivative scheme x = d.1 := by
    funext s
    fin_cases s
    apply Prod.ext
    · funext i
      fin_cases i
      simp [termScalingDerivative, scheme, x, hfirst]
    · apply Prod.ext
      · funext j
        fin_cases j
        simp [termScalingDerivative, scheme, x]
      · funext l
        fin_cases l
        simp [termScalingDerivative, scheme, x]
  rw [← hx]
  exact termScalingDerivative_mem_gaugeSpace scheme x

/-- Identity on the exact ambient kernel is an explicit gauge normalization for
this scheme because that kernel has just been proved entirely gauge. -/
noncomputable def normalization : GaugeNormalization scheme where
  projection := LinearMap.id
  range_le_gauge := by
    rw [ambientGaugeInKernel_eq_top]
    exact fun _ _ => Submodule.mem_top
  fixes_gauge := by
    intro d _hd
    rfl

/-- In characteristic two, the factors `(1+t)` and `(1+t+t²+t³)` define a
nonconstant product-one semantic arc modulo `t⁴` through the bridge scheme. -/
noncomputable def reciprocalScalingArc : OrderThreeArc scheme where
  first := fun _ => (![1], ![1], ![0])
  second := fun _ => (![0], ![1], ![0])
  third := fun _ => (![0], ![1], ![0])
  represented := by
    funext i j l
    fin_cases i
    fin_cases j
    fin_cases l
    simp only [sumTensor, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
      TriadData.eval, triad, Nat.reduceMul, orderThreeScheme,
      AdjoinRoot.algebraMap_eq, scheme, cons_val_fin_one, map_one, mul_one, map_zero,
      mul_zero, add_zero, Fin.zero_eta, Finset.sum_const, Finset.card_singleton,
      one_smul, mapTensor]
    ring_nf
    rw [truncatedParameter_pow_four]
    have htwoF : (2 : F) = 0 := CharP.cast_eq_zero F 2
    have htwo : (2 : TruncatedPolynomial F) =
        algebraMap F (TruncatedPolynomial F) (2 : F) := by
      exact (map_natCast (algebraMap F (TruncatedPolynomial F)) 2).symm
    rw [htwo, htwoF, map_zero]
    simp

/-- The concrete reciprocal arc has a genuinely nonzero linear coefficient. -/
theorem reciprocalScalingArc_first_ne_zero :
    reciprocalScalingArc.coefficient 0 ≠ 0 := by
  intro hzero
  have hentry := congrFun (congrArg Prod.fst (congrFun hzero 0)) 0
  change (1 : F) = 0 at hentry
  exact one_ne_zero hentry

/-- No coefficient precedes the reciprocal arc's nonzero linear coefficient. -/
theorem reciprocalScalingArc_first_initial :
    ∀ p, p < (0 : Fin 3) → reciprocalScalingArc.coefficient p = 0 := by
  intro p hp
  exact (Fin.not_lt_zero p hp).elim

/-- The reciprocal arc's nonzero linear coefficient lies in the certified mask. -/
theorem reciprocalScalingArc_first_mem_allowed :
    reciprocalScalingArc.coefficient 0 ∈ mask.allowed := by
  simp [OrderThreeArc.coefficient, reciprocalScalingArc, VariationMask.allowed, mask]

/-- The support-scoped rejection is nonvacuous at the arc level: a concrete
supported nonzero leading coefficient exists, and the certified normalization sends it to zero. -/
theorem reciprocalScalingArc_normalization_witness :
    ∃ (A : OrderThreeArc scheme) (q : Fin 3)
      (hlower : ∀ p, p < q → A.coefficient p = 0)
      (hnonzero : A.coefficient q ≠ 0),
      A.coefficient q ∈ mask.allowed ∧
      normalizedArcLeadingKernel scheme normalization A q hlower hnonzero = 0 ∧
      (normalizedArcLeadingKernel scheme normalization A q hlower hnonzero).1 ∈
        mask.allowed := by
  refine ⟨reciprocalScalingArc, 0, reciprocalScalingArc_first_initial,
    reciprocalScalingArc_first_ne_zero, reciprocalScalingArc_first_mem_allowed, ?_, ?_⟩
  · apply Subtype.ext
    simp [normalizedArcLeadingKernel, GaugeNormalization.normalized, normalization]
  · rw [show normalizedArcLeadingKernel scheme normalization reciprocalScalingArc 0
        reciprocalScalingArc_first_initial reciprocalScalingArc_first_ne_zero = 0 by
      apply Subtype.ext
      simp [normalizedArcLeadingKernel, GaugeNormalization.normalized, normalization]]
    exact Submodule.zero_mem _

/-- A concrete nonzero element of the exact ambient Jacobian kernel. -/
def scalingKernel : LinearMap.ker (jacobian scheme) :=
  ⟨firstSecondScalingDirection scheme 0,
    firstSecondScalingDirection_mem_ker scheme 0⟩

/-- The concrete scaling kernel vector is supported in the certified two-coordinate mask. -/
theorem scalingKernel_mem_allowed : scalingKernel.1 ∈ mask.allowed := by
  simp [VariationMask.allowed, mask, scalingKernel, firstSecondScalingDirection,
    localTermScalingDerivative, termScalingDerivative, localScalingParameters, scheme]

/-- The supported scaling vector as an element of the exact restricted Jacobian kernel. -/
def scalingRestrictedKernel : restrictedKernel scheme mask :=
  ⟨⟨scalingKernel.1, scalingKernel_mem_allowed⟩, scalingKernel.2⟩

/-- The concrete ambient kernel used by the normalization fixture is nontrivial. -/
theorem scalingKernel_ne_zero : scalingKernel ≠ 0 := by
  intro hzero
  apply (scalingDirections_ne_zero scheme 0 termNonzero).1
  exact congrArg Subtype.val hzero

/-- The exact restricted kernel in the support-scoped fixture is nontrivial. -/
theorem scalingRestrictedKernel_ne_zero : scalingRestrictedKernel ≠ 0 := by
  intro hzero
  apply scalingKernel_ne_zero
  apply Subtype.ext
  exact congrArg (fun d : restrictedKernel scheme mask => d.1.1) hzero

/-- The concrete normalization preserves the class of a genuine nonzero kernel
vector in the exact ambient normal quotient. -/
theorem normalization_preserves_scalingClass :
    (ambientGaugeInKernel scheme).mkQ (normalization.normalized scalingKernel) =
      (ambientGaugeInKernel scheme).mkQ scalingKernel :=
  normalization.normalClass_normalized scalingKernel

/-- Ambient class preservation and support-scoped semantic-arc rejection are
jointly instantiated on one nondegenerate scheme and its certified nonempty mask. -/
theorem normalization_and_support_rejection :
    ((ambientGaugeInKernel scheme).mkQ (normalization.normalized scalingKernel) =
      (ambientGaugeInKernel scheme).mkQ scalingKernel) ∧
    scalingRestrictedKernel ≠ 0 ∧
    (¬ ∃ (A : OrderThreeArc scheme) (q : Fin 3)
      (hlower : ∀ p, p < q → A.coefficient p = 0)
      (hnonzero : A.coefficient q ≠ 0),
      normalizedArcLeadingKernel scheme normalization A q hlower hnonzero ≠ 0 ∧
      (normalizedArcLeadingKernel scheme normalization A q hlower hnonzero).1 ∈
        mask.allowed) := by
  exact ⟨normalization_preserves_scalingClass, scalingRestrictedKernel_ne_zero,
    no_supported_nonzero_normalizedLeading_arc_of_restrictedGauge_eq_top
      scheme mask normalization restrictedGauge_eq_top⟩

end CertifiedBridgeFixture

/-- The term-scaling subspace visible in selected full `4×4×4` term blocks. -/
def fullBlockTermScaling [CommRing k] (S : MatrixScheme k 4 4 4 r)
    (I : Finset (Fin r)) :
    Submodule k ((VariationMask.full (a := 4 * 4) (b := 4 * 4) (c := 4 * 4) I).allowed
      (k := k)) :=
  (LinearMap.range (termScalingDerivative S)).comap
    (VariationMask.full (a := 4 * 4) (b := 4 * 4) (c := 4 * 4) I).inclusion

/-- Membership in the full-block scaling space is exactly ambient membership in the scaling range. -/
theorem mem_fullBlockTermScaling_iff [CommRing k] (S : MatrixScheme k 4 4 4 r)
    (I : Finset (Fin r))
    (d : (VariationMask.full (a := 4 * 4) (b := 4 * 4) (c := 4 * 4) I).allowed
      (k := k)) :
    d ∈ fullBlockTermScaling S I ↔
      (VariationMask.full (a := 4 * 4) (b := 4 * 4) (c := 4 * 4) I).inclusion d ∈
        LinearMap.range (termScalingDerivative S) := by
  rfl

/-- Full-block scaling directions regarded as a subspace of the restricted kernel. -/
def fullBlockScalingInKernel [CommRing k] (S : MatrixScheme k 4 4 4 r)
    (I : Finset (Fin r)) :
    Submodule k (restrictedKernel S
      (VariationMask.full (a := 4 * 4) (b := 4 * 4) (c := 4 * 4) I)) :=
  (fullBlockTermScaling S I).comap
    (restrictedKernel S
      (VariationMask.full (a := 4 * 4) (b := 4 * 4) (c := 4 * 4) I)).subtype

/-- The full-block scaling subspace is contained in the restricted combined gauge. -/
theorem fullBlockScalingInKernel_le_restrictedGauge [CommRing k]
    (S : MatrixScheme k 4 4 4 r) (I : Finset (Fin r)) :
    fullBlockScalingInKernel S I ≤ restrictedGauge S
      (VariationMask.full (a := 4 * 4) (b := 4 * 4) (c := 4 * 4) I) := by
  intro d hd
  rcases hd with ⟨x, hx⟩
  change (VariationMask.full (a := 4 * 4) (b := 4 * 4) (c := 4 * 4) I).inclusion
    ((restrictedKernel S
      (VariationMask.full (a := 4 * 4) (b := 4 * 4) (c := 4 * 4) I)).subtype d) ∈
    gaugeSpace S
  rw [← hx]
  exact termScalingDerivative_mem_gaugeSpace S x

/-- Coordinates for the two infinitesimal rescalings of one full nonzero term. -/
def localScalingToFullBlock [CommRing k]
    (S : MatrixScheme k 4 4 4 r) (s : Fin r) :
    (k × k) →ₗ[k] fullBlockTermScaling S {s} where
  toFun x := ⟨⟨localTermScalingDerivative S s x, by
    rw [VariationMask.mem_allowed_full_iff]
    intro t ht
    have hts : t ≠ s := by simpa only [Finset.mem_singleton] using ht
    change termScalingDerivative S (localScalingParameters s x) t = 0
    simp [termScalingDerivative, localScalingParameters, hts]⟩,
    ⟨localScalingParameters s x, rfl⟩⟩
  map_add' x y := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_add (localTermScalingDerivative S s) x y
  map_smul' q x := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_smul (localTermScalingDerivative S s) q x

/-- A nonzero term makes its two local scaling coordinates independent. -/
theorem localScalingToFullBlock_bijective [Field k]
    (S : MatrixScheme k 4 4 4 r) (s : Fin r)
    (hs : S.TermNonzero s) : Function.Bijective (localScalingToFullBlock S s) := by
  constructor
  · intro x y hxy
    apply localTermScalingDerivative_injective S s hs
    exact congrArg (fun d : fullBlockTermScaling S {s} => d.1.1) hxy
  · rintro ⟨d, y, hy⟩
    let x := y s
    refine ⟨x, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    funext t
    by_cases hts : t = s
    · subst t
      change termScalingDerivative S (localScalingParameters s x) s =
        (VariationMask.full (a := 4 * 4) (b := 4 * 4) (c := 4 * 4) {s}).inclusion d s
      rw [← hy]
      simp [termScalingDerivative, localScalingParameters, x]
    · have hdSupport :=
        (VariationMask.mem_allowed_full_iff (k := k) {s} d.1).mp d.2
      change termScalingDerivative S (localScalingParameters s x) t = d.1 t
      rw [hdSupport t (by simpa only [Finset.mem_singleton])]
      simp [termScalingDerivative, localScalingParameters, hts]

/-- The two scalar coordinates are linearly equivalent to one full-block term-scaling space. -/
noncomputable def localFullBlockTermScalingEquiv [Field k]
    (S : MatrixScheme k 4 4 4 r) (s : Fin r)
    (hs : S.TermNonzero s) : (k × k) ≃ₗ[k] fullBlockTermScaling S {s} :=
  LinearEquiv.ofBijective (localScalingToFullBlock S s)
    (localScalingToFullBlock_bijective S s hs)

/-- The full-block term-scaling space is canonically the same module when
regarded inside the restricted Jacobian kernel. -/
noncomputable def fullBlockTermScalingEquivInKernel [CommRing k]
    (S : MatrixScheme k 4 4 4 r) (I : Finset (Fin r)) :
    fullBlockTermScaling S I ≃ₗ[k] fullBlockScalingInKernel S I where
  toFun d := ⟨⟨d.1, by
    change jacobian S
      ((VariationMask.full (a := 16) (b := 16) (c := 16) I).inclusion d.1) = 0
    rcases d.2 with ⟨x, hx⟩
    rw [← hx]
    exact jacobian_termScalingDerivative S x⟩, d.2⟩
  invFun d := ⟨d.1.1, d.2⟩
  left_inv d := by rfl
  right_inv d := by rfl
  map_add' d e := by rfl
  map_smul' q d := by rfl

/-- A full-block scaling audit records exact local-kernel identification,
explicit two-coordinate models for every selected term, and a disjoint-support
direct-sum decomposition of the resulting global scaling subspace. -/
structure FullBlockScalingAudit [Field k]
    (S : MatrixScheme k 4 4 4 r) (I : Finset (Fin r)) where
  /-- Explicit two-dimensional coordinates for each selected local scaling space. -/
  localScalingCoordinates : ∀ s : ↥I,
    (k × k) ≃ₗ[k] fullBlockTermScaling S {s.1}
  /-- The full-block local Jacobian kernel has no directions beyond term scaling. -/
  localKernel_eq_scaling : ∀ s : ↥I,
    restrictedKernel S
        (VariationMask.full (a := 4 * 4) (b := 4 * 4) (c := 4 * 4) {s.1}) =
      fullBlockTermScaling S {s.1}
  /-- The local kernels assemble without overlap into the global selected scaling space. -/
  disjointSupportDecomposition :
    DirectSum (↥I) (fun s => restrictedKernel S
      (VariationMask.full (a := 4 * 4) (b := 4 * 4) (c := 4 * 4) {s.1})) ≃ₗ[k]
      fullBlockScalingInKernel S I

namespace FullBlockScalingAudit

/-- A full-block audit derives, rather than assumes, the global scaling dimension `2 * |I|`. -/
theorem finrank_fullBlockScalingInKernel [Field k]
    {S : MatrixScheme k 4 4 4 r} {I : Finset (Fin r)}
    (audit : FullBlockScalingAudit S I) :
    Module.finrank k (fullBlockScalingInKernel S I) = 2 * I.card := by
  let coordinateEquiv :
      fullBlockScalingInKernel S I ≃ₗ[k] (↥I → k × k) :=
    audit.disjointSupportDecomposition.symm |>.trans
      (DirectSum.linearEquivFunOnFintype k (↥I)
        (fun s => restrictedKernel S
          (VariationMask.full (a := 4 * 4) (b := 4 * 4) (c := 4 * 4) {s.1}))) |>.trans
      (LinearEquiv.piCongrRight (fun s =>
        (LinearEquiv.ofEq _ _ (audit.localKernel_eq_scaling s)).trans
          (audit.localScalingCoordinates s).symm))
  rw [coordinateEquiv.finrank_eq, Module.finrank_pi_fintype]
  simp [Nat.mul_comm]

end FullBlockScalingAudit

/- A nondegenerate singleton model validating every field of the full-block audit interface. -/
namespace FullBlockAuditFixture

/-- The binary field used by the full-block audit fixture. -/
abbrev F := ZMod 2

/-- The first standard vector in the sixteen-dimensional factor space. -/
def basisVector : Fin 16 → F := fun i => if i = 0 then 1 else 0

example : basisVector 0 = 1 := by simp [basisVector]
example : basisVector 1 = 0 := by simp [basisVector]

/-- A single nonzero sparse rank-one term in a full `4×4×4` block. -/
def scheme : MatrixScheme F 4 4 4 1 :=
  ⟨fun _ => (basisVector, basisVector, basisVector)⟩

/-- The full singleton mask selecting the fixture's only `16+16+16` coordinate block. -/
abbrev mask : VariationMask 16 16 16 1 := VariationMask.full {0}

/-- The represented singleton term is genuinely nonzero. -/
theorem termNonzero : scheme.TermNonzero 0 := by
  intro hzero
  have hentry := congrFun (congrFun (congrFun hzero 0) 0) 0
  norm_num [scheme, basisVector, TriadData.eval, triad] at hentry

/-- Coordinate form of the sparse fixture's restricted Jacobian equation. -/
theorem jacobian_entry (d : mask.allowed (k := F))
    (hd : mask.restrictedJacobian scheme d = 0) (i j l : Fin 16) :
    (d.1 0).1 i * basisVector j * basisVector l +
      basisVector i * (d.1 0).2.1 j * basisVector l +
      basisVector i * basisVector j * (d.1 0).2.2 l = 0 := by
  have hentry := congrFun (congrFun (congrFun hd i) j) l
  change linearCoefficient scheme d.1 i j l = 0 at hentry
  simpa [scheme, linearCoefficient] using hentry

/-- The nonzero sparse singleton has exactly its two term-scaling directions in
the full local restricted kernel. -/
theorem localKernel_eq_scaling :
    restrictedKernel scheme mask = fullBlockTermScaling scheme {0} := by
  apply le_antisymm
  · intro d hd
    let x : Fin 1 → F × F := fun _ => ((d.1 0).2.1 0, (d.1 0).2.2 0)
    refine ⟨x, ?_⟩
    funext s
    fin_cases s
    apply Prod.ext
    · funext i
      by_cases hi : i = 0
      · subst i
        have h000 := jacobian_entry d hd 0 0 0
        simp only [Fin.isValue, basisVector, ↓reduceIte, mul_one, one_mul] at h000
        change ((x 0).1 + (x 0).2) * basisVector 0 = (d.1 0).1 0
        simp only [x, basisVector, if_pos, mul_one]
        have hvw : (d.1 0).2.1 0 + (d.1 0).2.2 0 = -(d.1 0).1 0 := by
          linear_combination h000
        simpa only [ZMod.neg_eq_self_mod_two] using hvw
      · have hi0 := jacobian_entry d hd i 0 0
        simp only [Fin.isValue, basisVector, ↓reduceIte, mul_one, hi, zero_mul,
          add_zero] at hi0
        change ((x 0).1 + (x 0).2) * basisVector i = (d.1 0).1 i
        simp [basisVector, hi, hi0]
    · apply Prod.ext
      · funext j
        by_cases hj : j = 0
        · subst j
          change (-(x 0).1) * basisVector 0 = (d.1 0).2.1 0
          simp [x, basisVector]
        · have hj0 := jacobian_entry d hd 0 j 0
          simp only [Fin.isValue, basisVector, hj, ↓reduceIte, mul_zero, mul_one,
            one_mul, zero_add, zero_mul, add_zero] at hj0
          change (-(x 0).1) * basisVector j = (d.1 0).2.1 j
          simp [basisVector, hj, hj0]
      · funext l
        by_cases hl : l = 0
        · subst l
          change (-(x 0).2) * basisVector 0 = (d.1 0).2.2 0
          simp [x, basisVector]
        · have hl0 := jacobian_entry d hd 0 0 l
          simp only [Fin.isValue, basisVector, ↓reduceIte, mul_one, hl, mul_zero,
            one_mul, add_zero, zero_add] at hl0
          change (-(x 0).2) * basisVector l = (d.1 0).2.2 l
          simp [basisVector, hl, hl0]
  · intro d hd
    rcases hd with ⟨x, hx⟩
    change jacobian scheme
      ((VariationMask.full (a := 16) (b := 16) (c := 16) {0}).inclusion d) = 0
    rw [← hx]
    exact jacobian_termScalingDerivative scheme x

/-- The sparse singleton supplies a joint, nonzero witness for all local and
direct-sum fields of `FullBlockScalingAudit`.  It is an interface fixture, not
a numerical `46|I|` rank assertion. -/
noncomputable def audit : FullBlockScalingAudit scheme {0} where
  localScalingCoordinates s :=
    localFullBlockTermScalingEquiv scheme s.1 (by
      have hs : s.1 = (0 : Fin 1) := Finset.mem_singleton.mp s.2
      rw [hs]
      exact termNonzero)
  localKernel_eq_scaling s := by
    have hs : s.1 = (0 : Fin 1) := Finset.mem_singleton.mp s.2
    rw [hs]
    exact localKernel_eq_scaling
  disjointSupportDecomposition := by
    let hlocalEquiv : restrictedKernel scheme mask ≃ₗ[F]
        fullBlockTermScaling scheme {0} :=
      LinearEquiv.ofEq _ _ localKernel_eq_scaling
    exact
      (DirectSum.linearEquivFunOnFintype F (↥({0} : Finset (Fin 1)))
        (fun s => restrictedKernel scheme
          (VariationMask.full (a := 16) (b := 16) (c := 16) {s.1}))).trans
      ((LinearEquiv.piUnique F
        (fun s : ↥({0} : Finset (Fin 1)) => restrictedKernel scheme
          (VariationMask.full (a := 16) (b := 16) (c := 16) {s.1}))).trans
        (hlocalEquiv.trans (fullBlockTermScalingEquivInKernel scheme {0})))

example : Module.finrank F (fullBlockScalingInKernel scheme {0}) = 2 := by
  simpa using audit.finrank_fullBlockScalingInKernel

/-- The singleton full mask is the entire nonempty 48-coordinate variation
space of the fixture. -/
theorem allowed_finrank : Module.finrank F (mask.allowed (k := F)) = 48 := by
  have htop : mask.allowed (k := F) = ⊤ := by
    ext d
    simp [mask, VariationMask.mem_allowed_full_iff]
  rw [htop]
  simp [Module.finrank_pi_fintype, Module.finrank_prod]

/-- The exact local-kernel identification and its two scaling coordinates force
nullity two; rank-nullity then derives, rather than assumes, restricted rank 46. -/
theorem restrictedJacobian_range_finrank :
    Module.finrank F (LinearMap.range (mask.restrictedJacobian scheme)) = 46 := by
  have hkernel : Module.finrank F (restrictedKernel scheme mask) = 2 := by
    rw [localKernel_eq_scaling]
    calc
      Module.finrank F (fullBlockTermScaling scheme {0}) =
          Module.finrank F (F × F) :=
        (localFullBlockTermScalingEquiv scheme 0 termNonzero).finrank_eq.symm
      _ = 2 := by simp [Module.finrank_prod]
  have hdomain := allowed_finrank
  have hnullity := LinearMap.finrank_range_add_finrank_ker
    (mask.restrictedJacobian scheme)
  change Module.finrank F (LinearMap.range (mask.restrictedJacobian scheme)) +
      Module.finrank F (restrictedKernel scheme mask) =
      Module.finrank F (mask.allowed (k := F)) at hnullity
  omega

end FullBlockAuditFixture

/-- Over `ZMod 2`, an audited full-block decomposition together with the
`48|I|` domain and `46|I|` Jacobian dimensions forces every restricted kernel
direction in the selected full `4×4×4` blocks to be gauge. -/
theorem binary_fullBlock_restrictedGauge_eq_top
    (S : MatrixScheme (ZMod 2) 4 4 4 r) (I : Finset (Fin r))
    (audit : FullBlockScalingAudit S I)
    (hfullDomain : Module.finrank (ZMod 2)
      ((VariationMask.full (a := 4 * 4) (b := 4 * 4) (c := 4 * 4) I).allowed
        (k := ZMod 2)) = 48 * I.card)
    (hrank46 : Module.finrank (ZMod 2) (LinearMap.range
      ((VariationMask.full (a := 4 * 4) (b := 4 * 4) (c := 4 * 4) I).restrictedJacobian S)) =
        46 * I.card) :
    restrictedGauge S
      (VariationMask.full (a := 4 * 4) (b := 4 * 4) (c := 4 * 4) I) = ⊤ := by
  let M := VariationMask.full (a := 4 * 4) (b := 4 * 4) (c := 4 * 4) I
  have hnullity := LinearMap.finrank_range_add_finrank_ker (M.restrictedJacobian S)
  have hkerFinrank : Module.finrank (ZMod 2) (restrictedKernel S M) = 2 * I.card := by
    change Module.finrank (ZMod 2) (LinearMap.ker (M.restrictedJacobian S)) = 2 * I.card
    change Module.finrank (ZMod 2) (LinearMap.range (M.restrictedJacobian S)) +
      Module.finrank (ZMod 2) (LinearMap.ker (M.restrictedJacobian S)) =
        Module.finrank (ZMod 2) (M.allowed (k := ZMod 2)) at hnullity
    change Module.finrank (ZMod 2) (M.allowed (k := ZMod 2)) = 48 * I.card at hfullDomain
    change Module.finrank (ZMod 2) (LinearMap.range (M.restrictedJacobian S)) =
      46 * I.card at hrank46
    omega
  have hscalingTop : fullBlockScalingInKernel S I = ⊤ := by
    apply @Submodule.eq_top_of_finrank_eq (ZMod 2)
      (restrictedKernel S
        (VariationMask.full (a := 4 * 4) (b := 4 * 4) (c := 4 * 4) I))
      (inferInstanceAs (DivisionRing (ZMod 2)))
      (inferInstanceAs (AddCommGroup (restrictedKernel S
        (VariationMask.full (a := 4 * 4) (b := 4 * 4) (c := 4 * 4) I))))
      (inferInstanceAs (Module (ZMod 2) (restrictedKernel S
        (VariationMask.full (a := 4 * 4) (b := 4 * 4) (c := 4 * 4) I))))
      (inferInstanceAs (FiniteDimensional (ZMod 2) (restrictedKernel S
        (VariationMask.full (a := 4 * 4) (b := 4 * 4) (c := 4 * 4) I))))
    calc
      Module.finrank (ZMod 2) (fullBlockScalingInKernel S I) = 2 * I.card :=
        audit.finrank_fullBlockScalingInKernel
      _ = Module.finrank (ZMod 2) (restrictedKernel S M) := hkerFinrank.symm
  apply top_unique
  intro d _hd
  apply fullBlockScalingInKernel_le_restrictedGauge S I
  rw [hscalingTop]
  exact Submodule.mem_top

/-- The audited binary `46|I|` criterion makes every restricted normal class equal to zero. -/
theorem binary_fullBlock_restrictedNormalClass_eq_zero
    (S : MatrixScheme (ZMod 2) 4 4 4 r) (I : Finset (Fin r))
    (audit : FullBlockScalingAudit S I)
    (hfullDomain : Module.finrank (ZMod 2)
      ((VariationMask.full (a := 4 * 4) (b := 4 * 4) (c := 4 * 4) I).allowed
        (k := ZMod 2)) = 48 * I.card)
    (hrank46 : Module.finrank (ZMod 2) (LinearMap.range
      ((VariationMask.full (a := 4 * 4) (b := 4 * 4) (c := 4 * 4) I).restrictedJacobian S)) =
        46 * I.card)
    (d : restrictedKernel S
      (VariationMask.full (a := 4 * 4) (b := 4 * 4) (c := 4 * 4) I)) :
    restrictedNormalClass S
        (VariationMask.full (a := 4 * 4) (b := 4 * 4) (c := 4 * 4) I) d =
      restrictedNormalZeroClass S
        (VariationMask.full (a := 4 * 4) (b := 4 * 4) (c := 4 * 4) I) := by
  have hgaugeTop := binary_fullBlock_restrictedGauge_eq_top S I audit
    hfullDomain hrank46
  by_contra hne
  have hnongauge :=
    (not_mem_restrictedGauge_iff_restrictedNormalClass_ne_zero S _ d).mpr hne
  apply hnongauge
  rw [hgaugeTop]
  exact Submodule.mem_top

namespace FullBlockAuditFixture

/-- The concrete singleton audit jointly supplies the 48-coordinate domain and
the derived rank-46 restricted Jacobian required by the binary full-block theorem. -/
theorem restrictedGauge_eq_top : restrictedGauge scheme mask = ⊤ := by
  apply binary_fullBlock_restrictedGauge_eq_top scheme {0} audit
  · simpa [mask] using allowed_finrank
  · simpa [mask] using restrictedJacobian_range_finrank

/-- Every class in the exact restricted normal quotient of the audited
singleton fixture is zero. -/
theorem restrictedNormalClass_eq_zero (d : restrictedKernel scheme mask) :
    restrictedNormalClass scheme mask d = restrictedNormalZeroClass scheme mask := by
  apply binary_fullBlock_restrictedNormalClass_eq_zero scheme {0} audit
  · simpa [mask] using allowed_finrank
  · simpa [mask] using restrictedJacobian_range_finrank

end FullBlockAuditFixture

#check @termScalingDerivative
#check @jacobian_termScalingDerivative
#check @localTermScalingDerivative_injective
#check @jacobian_infinitesimalSandwich
#check @gaugeSpace_le_ker
#check @GaugeNormalization
#check @GaugeNormalization.normalClass_normalized
#check @GaugeNormalization.normalized_eq_zero_of_supported_of_restrictedGauge_eq_top
#check @restrictedGauge
#check @restrictedNormalTangentModule
#check @restrictedNormalClass_smul
#check @not_mem_restrictedGauge_iff_restrictedNormalClass_ne_zero
#check @not_mem_restrictedGauge_iff_ambientNormalClass_ne_zero
#check @arcLeadingKernel
#check @normalizedArcLeadingKernel
#check @normalClass_normalizedArcLeadingKernel
#check @normalizedArcLeadingKernel_eq_zero_of_supported_of_restrictedGauge_eq_top
#check @no_supported_nonzero_normalizedLeading_arc_of_restrictedGauge_eq_top
#check @no_normalizedLeading_arc_of_restrictedKernel_le_gauge
#check @certified_restrictedGauge_eq_top_over_charTwo
#check @CertifiedBridgeFixture.restrictedGauge_eq_top
#check @CertifiedBridgeFixture.normalization
#check @CertifiedBridgeFixture.reciprocalScalingArc
#check @CertifiedBridgeFixture.reciprocalScalingArc_normalization_witness
#check @CertifiedBridgeFixture.scalingRestrictedKernel_ne_zero
#check @CertifiedBridgeFixture.normalization_preserves_scalingClass
#check @CertifiedBridgeFixture.normalization_and_support_rejection
#check @FullBlockScalingAudit
#check @FullBlockScalingAudit.finrank_fullBlockScalingInKernel
#check @FullBlockAuditFixture.audit
#check @FullBlockAuditFixture.allowed_finrank
#check @FullBlockAuditFixture.restrictedJacobian_range_finrank
#check @binary_fullBlock_restrictedGauge_eq_top
#check @FullBlockAuditFixture.restrictedGauge_eq_top
#check @FullBlockAuditFixture.restrictedNormalClass_eq_zero
#check @binary_fullBlock_restrictedNormalClass_eq_zero

#print axioms jacobian_termScalingDerivative
#print axioms localTermScalingDerivative_injective
#print axioms jacobian_infinitesimalSandwich
#print axioms gaugeSpace_le_ker
#print axioms GaugeNormalization.normalClass_normalized
#print axioms GaugeNormalization.normalized_eq_zero_of_supported_of_restrictedGauge_eq_top
#print axioms restrictedNormalClass_smul
#print axioms not_mem_restrictedGauge_iff_restrictedNormalClass_ne_zero
#print axioms not_mem_restrictedGauge_iff_ambientNormalClass_ne_zero
#print axioms normalClass_normalizedArcLeadingKernel
#print axioms normalizedArcLeadingKernel_eq_zero_of_supported_of_restrictedGauge_eq_top
#print axioms no_supported_nonzero_normalizedLeading_arc_of_restrictedGauge_eq_top
#print axioms no_normalizedLeading_arc_of_restrictedKernel_le_gauge
#print axioms certified_restrictedGauge_eq_top_over_charTwo
#print axioms CertifiedBridgeFixture.restrictedGauge_eq_top
#print axioms CertifiedBridgeFixture.ambientGaugeInKernel_eq_top
#print axioms CertifiedBridgeFixture.reciprocalScalingArc_normalization_witness
#print axioms CertifiedBridgeFixture.scalingRestrictedKernel_ne_zero
#print axioms CertifiedBridgeFixture.normalization_preserves_scalingClass
#print axioms CertifiedBridgeFixture.normalization_and_support_rejection
#print axioms FullBlockScalingAudit.finrank_fullBlockScalingInKernel
#print axioms FullBlockAuditFixture.localKernel_eq_scaling
#print axioms FullBlockAuditFixture.allowed_finrank
#print axioms FullBlockAuditFixture.restrictedJacobian_range_finrank
#print axioms binary_fullBlock_restrictedGauge_eq_top
#print axioms FullBlockAuditFixture.restrictedGauge_eq_top
#print axioms FullBlockAuditFixture.restrictedNormalClass_eq_zero
#print axioms binary_fullBlock_restrictedNormalClass_eq_zero

end Deformation
end Scheme
end BilinearComplexity
