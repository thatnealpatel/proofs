import BilinearComplexity.Scheme
import Mathlib.Algebra.Polynomial.Div
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.AdjoinRoot

set_option autoImplicit false

namespace BilinearComplexity
namespace Scheme
namespace Deformation

variable {k : Type*} {a b c r : ℕ}

/-- The ambient module of first-order changes of all three factors in every ordered slot. -/
abbrev Variation (k : Type*) (a b c r : ℕ) :=
  Fin r → TriadData k a b c

/-- The coefficient linear in a variation in the expansion of the represented tensor. -/
def linearCoefficient [CommRing k] (S : Scheme k a b c r)
    (d : Variation k a b c r) : Tensor k a b c :=
  fun i j l => ∑ s, (
    (d s).1 i * (S.term s).2.1 j * (S.term s).2.2 l +
    (S.term s).1 i * (d s).2.1 j * (S.term s).2.2 l +
    (S.term s).1 i * (S.term s).2.1 j * (d s).2.2 l)

/-- The Jacobian of the ordered-scheme summation map at `S`. -/
def jacobian [CommRing k] (S : Scheme k a b c r) :
    Variation k a b c r →ₗ[k] Tensor k a b c where
  toFun := linearCoefficient S
  map_add' d e := by
    funext i j l
    simp only [linearCoefficient, Pi.add_apply, Prod.fst_add, Prod.snd_add]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _hs
    ring
  map_smul' t d := by
    funext i j l
    simp only [linearCoefficient, Pi.smul_apply, Prod.smul_fst, Prod.smul_snd,
      Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _hs
    ring

/-- Evaluation of the Jacobian exposes the explicit linear coefficient formula. -/
@[simp] theorem jacobian_apply [CommRing k] (S : Scheme k a b c r)
    (d : Variation k a b c r) :
    jacobian S d = linearCoefficient S d := rfl

/-- The coefficient quadratic in one variation in the rank-one expansion. -/
def quadraticCoefficient [CommRing k] (S : Scheme k a b c r)
    (d : Variation k a b c r) : Tensor k a b c :=
  fun i j l => ∑ s, (
    (d s).1 i * (d s).2.1 j * (S.term s).2.2 l +
    (d s).1 i * (S.term s).2.1 j * (d s).2.2 l +
    (S.term s).1 i * (d s).2.1 j * (d s).2.2 l)

/-- The coefficient cubic in one variation in the rank-one expansion. -/
def cubicCoefficient [CommRing k] (_S : Scheme k a b c r)
    (d : Variation k a b c r) : Tensor k a b c :=
  fun i j l => ∑ s, (d s).1 i * (d s).2.1 j * (d s).2.2 l

/-- The symmetric bilinear mixed quadratic coefficient of two independent variations. -/
def mixedQuadraticCoefficient [CommRing k] (S : Scheme k a b c r)
    (d e : Variation k a b c r) : Tensor k a b c :=
  fun i j l => ∑ s, (
    ((d s).1 i * (e s).2.1 j + (e s).1 i * (d s).2.1 j) *
        (S.term s).2.2 l +
    ((d s).1 i * (e s).2.2 l + (e s).1 i * (d s).2.2 l) *
        (S.term s).2.1 j +
    ((d s).2.1 j * (e s).2.2 l + (e s).2.1 j * (d s).2.2 l) *
        (S.term s).1 i)

/-- The mixed quadratic coefficient is additive in its first variation. -/
theorem mixedQuadraticCoefficient_add_left [CommRing k] (S : Scheme k a b c r)
    (d e f : Variation k a b c r) :
    mixedQuadraticCoefficient S (d + e) f =
      mixedQuadraticCoefficient S d f + mixedQuadraticCoefficient S e f := by
  funext i j l
  simp only [mixedQuadraticCoefficient, Pi.add_apply, Prod.fst_add, Prod.snd_add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _hs
  ring

/-- The mixed quadratic coefficient is symmetric in its two variations. -/
theorem mixedQuadraticCoefficient_comm [CommRing k] (S : Scheme k a b c r)
    (d e : Variation k a b c r) :
    mixedQuadraticCoefficient S d e = mixedQuadraticCoefficient S e d := by
  funext i j l
  simp only [mixedQuadraticCoefficient]
  apply Finset.sum_congr rfl
  intro s _hs
  ring

/-- On the diagonal the mixed coefficient is twice the quadratic coefficient. -/
theorem mixedQuadraticCoefficient_self [CommRing k] (S : Scheme k a b c r)
    (d : Variation k a b c r) :
    mixedQuadraticCoefficient S d d = (2 : k) • quadraticCoefficient S d := by
  funext i j l
  simp only [mixedQuadraticCoefficient, quadraticCoefficient, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _hs
  ring

/-- The quadratic coefficient of the zero variation vanishes. -/
@[simp] theorem quadraticCoefficient_zero [CommRing k] (S : Scheme k a b c r) :
    quadraticCoefficient S 0 = 0 := by
  funext i j l
  simp [quadraticCoefficient]

/-- The cubic coefficient of the zero variation vanishes. -/
@[simp] theorem cubicCoefficient_zero [CommRing k] (S : Scheme k a b c r) :
    cubicCoefficient S 0 = 0 := by
  funext i j l
  simp [cubicCoefficient]

/-- The mixed coefficient vanishes when both variations vanish. -/
@[simp] theorem mixedQuadraticCoefficient_zero_zero [CommRing k] (S : Scheme k a b c r) :
    mixedQuadraticCoefficient S 0 0 = 0 := by
  funext i j l
  simp [mixedQuadraticCoefficient]

/-- Perturb every factor of every ordered term by the same scalar parameter. -/
def perturb [CommRing k] (S : Scheme k a b c r)
    (d : Variation k a b c r) (t : k) : Scheme k a b c r :=
  ⟨fun s =>
    (fun i => (S.term s).1 i + t * (d s).1 i,
      fun j => (S.term s).2.1 j + t * (d s).2.1 j,
      fun l => (S.term s).2.2 l + t * (d s).2.2 l)⟩

/-- Direct one-term trilinear expansion through its exact cubic term. -/
theorem oneTerm_expansion [CommRing k]
    (U : Fin a → k) (V : Fin b → k) (W : Fin c → k)
    (u : Fin a → k) (v : Fin b → k) (w : Fin c → k) (t : k) :
    (fun i j l => (U i + t * u i) * (V j + t * v j) * (W l + t * w l)) =
      fun i j l =>
        U i * V j * W l +
        t * (u i * V j * W l + U i * v j * W l + U i * V j * w l) +
        t ^ 2 * (u i * v j * W l + u i * V j * w l + U i * v j * w l) +
        t ^ 3 * (u i * v j * w l) := by
  funext i j l
  ring

/-- Summing the one-term identities gives the exact linear, quadratic, and cubic expansion. -/
theorem sumTensor_perturb [CommRing k] (S : Scheme k a b c r)
    (d : Variation k a b c r) (t : k) :
    (perturb S d t).sumTensor =
      S.sumTensor + t • jacobian S d + t ^ 2 • quadraticCoefficient S d +
        t ^ 3 • cubicCoefficient S d := by
  funext i j l
  simp only [sumTensor, perturb, TriadData.eval, triad, jacobian_apply,
    linearCoefficient, quadraticCoefficient, cubicCoefficient, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _hs
  ring

/-- The coefficient at order four in a two-coefficient factor perturbation. -/
def twoStepQuarticCoefficient [CommRing k] (S : Scheme k a b c r)
    (d₁ d₂ : Variation k a b c r) : Tensor k a b c :=
  fun i j l => ∑ s, (
    (d₂ s).1 i * (d₂ s).2.1 j * (S.term s).2.2 l +
    (d₂ s).1 i * (S.term s).2.1 j * (d₂ s).2.2 l +
    (S.term s).1 i * (d₂ s).2.1 j * (d₂ s).2.2 l +
    (d₁ s).1 i * (d₁ s).2.1 j * (d₂ s).2.2 l +
    (d₁ s).1 i * (d₂ s).2.1 j * (d₁ s).2.2 l +
    (d₂ s).1 i * (d₁ s).2.1 j * (d₁ s).2.2 l)

/-- The coefficient at order five in a two-coefficient factor perturbation. -/
def twoStepQuinticCoefficient [CommRing k] (_S : Scheme k a b c r)
    (d₁ d₂ : Variation k a b c r) : Tensor k a b c :=
  fun i j l => ∑ s, (
    (d₁ s).1 i * (d₂ s).2.1 j * (d₂ s).2.2 l +
    (d₂ s).1 i * (d₁ s).2.1 j * (d₂ s).2.2 l +
    (d₂ s).1 i * (d₂ s).2.1 j * (d₁ s).2.2 l)

/-- A two-step perturbation stores independent first and second factor coefficients. -/
def perturbTwoStep [CommRing k] (S : Scheme k a b c r)
    (d₁ d₂ : Variation k a b c r) (t : k) : Scheme k a b c r :=
  ⟨fun s =>
    (fun i => (S.term s).1 i + t * (d₁ s).1 i + t ^ 2 * (d₂ s).1 i,
      fun j => (S.term s).2.1 j + t * (d₁ s).2.1 j + t ^ 2 * (d₂ s).2.1 j,
      fun l => (S.term s).2.2 l + t * (d₁ s).2.2 l + t ^ 2 * (d₂ s).2.2 l)⟩

/-- Exact two-step expansion; in particular, the cubic coefficient is
`J d₃ + mixedQuadratic d₁ d₂ + C d₁` after adding an independent third coefficient. -/
theorem sumTensor_perturbTwoStep [CommRing k] (S : Scheme k a b c r)
    (d₁ d₂ : Variation k a b c r) (t : k) :
    (perturbTwoStep S d₁ d₂ t).sumTensor =
      S.sumTensor +
      t • jacobian S d₁ +
      t ^ 2 • (jacobian S d₂ + quadraticCoefficient S d₁) +
      t ^ 3 • (mixedQuadraticCoefficient S d₁ d₂ + cubicCoefficient S d₁) +
      t ^ 4 • twoStepQuarticCoefficient S d₁ d₂ +
      t ^ 5 • twoStepQuinticCoefficient S d₁ d₂ +
      t ^ 6 • cubicCoefficient S d₂ := by
  funext i j l
  simp only [sumTensor, perturbTwoStep, TriadData.eval, triad, jacobian_apply,
    linearCoefficient, quadraticCoefficient, cubicCoefficient, mixedQuadraticCoefficient,
    twoStepQuarticCoefficient, twoStepQuinticCoefficient, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  repeat' rw [Finset.mul_sum]
  simp only [← Finset.sum_add_distrib]
  repeat' rw [Finset.mul_sum]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _hs
  ring

/-- A coordinate mask specifies a finite term support and the allowed coordinates in each leg. -/
structure VariationMask (a b c r : ℕ) where
  /-- Ordered slots on which any variation is allowed. -/
  terms : Finset (Fin r)
  /-- Allowed first-factor coordinates in each slot. -/
  first : Fin r → Finset (Fin a)
  /-- Allowed second-factor coordinates in each slot. -/
  second : Fin r → Finset (Fin b)
  /-- Allowed third-factor coordinates in each slot. -/
  third : Fin r → Finset (Fin c)

namespace VariationMask

/-- The submodule of ambient variations supported on exactly the allowed term/coordinate mask. -/
def allowed [CommRing k] (M : VariationMask a b c r) :
    Submodule k (Variation k a b c r) where
  carrier := {d | (∀ s, s ∉ M.terms → d s = 0) ∧
    (∀ s i, i ∉ M.first s → (d s).1 i = 0) ∧
    (∀ s j, j ∉ M.second s → (d s).2.1 j = 0) ∧
    (∀ s l, l ∉ M.third s → (d s).2.2 l = 0)}
  zero_mem' := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro s _hs
      rfl
    · intro s i _hi
      rfl
    · intro s j _hj
      rfl
    · intro s l _hl
      rfl
  add_mem' := by
    rintro d e ⟨hdTerms, hd₁, hd₂, hd₃⟩ ⟨heTerms, he₁, he₂, he₃⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro s hs
      simp only [Pi.add_apply, hdTerms s hs, heTerms s hs, add_zero]
    · intro s i hi
      simp only [Pi.add_apply, Prod.fst_add, Pi.add_apply, hd₁ s i hi, he₁ s i hi, add_zero]
    · intro s j hj
      simp only [Pi.add_apply, Prod.snd_add, Prod.fst_add, Pi.add_apply,
        hd₂ s j hj, he₂ s j hj, add_zero]
    · intro s l hl
      simp only [Pi.add_apply, Prod.snd_add, Pi.add_apply, hd₃ s l hl, he₃ s l hl, add_zero]
  smul_mem' := by
    rintro t d ⟨hdTerms, hd₁, hd₂, hd₃⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro s hs
      simp only [Pi.smul_apply, hdTerms s hs, smul_zero]
    · intro s i hi
      simp only [Pi.smul_apply, Prod.smul_fst, Pi.smul_apply, hd₁ s i hi, smul_zero]
    · intro s j hj
      simp only [Pi.smul_apply, Prod.smul_snd, Prod.smul_fst, Pi.smul_apply,
        hd₂ s j hj, smul_zero]
    · intro s l hl
      simp only [Pi.smul_apply, Prod.smul_snd, Pi.smul_apply, hd₃ s l hl, smul_zero]

/-- A full-block mask allows all three factor-coordinate blocks on the selected terms. -/
def full (I : Finset (Fin r)) : VariationMask a b c r where
  terms := I
  first := fun _ => Finset.univ
  second := fun _ => Finset.univ
  third := fun _ => Finset.univ

/-- Membership in a full-block mask is exactly vanishing away from the selected terms. -/
theorem mem_allowed_full_iff [CommRing k] (I : Finset (Fin r))
    (d : Variation k a b c r) :
    d ∈ (full (a := a) (b := b) (c := c) I).allowed ↔
      ∀ s, s ∉ I → d s = 0 := by
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_, ?_, ?_⟩
    · intro s i hi
      exact (hi (Finset.mem_univ i)).elim
    · intro s j hj
      exact (hj (Finset.mem_univ j)).elim
    · intro s l hl
      exact (hl (Finset.mem_univ l)).elim

/-- The canonical inclusion of allowed variations into the ambient variation module. -/
def inclusion [CommRing k] (M : VariationMask a b c r) :
    M.allowed (k := k) →ₗ[k] Variation k a b c r :=
  M.allowed.subtype

/-- The restricted Jacobian is the ambient Jacobian after the explicit support inclusion. -/
def restrictedJacobian [CommRing k] (S : Scheme k a b c r)
    (M : VariationMask a b c r) : M.allowed (k := k) →ₗ[k] Tensor k a b c :=
  (jacobian S).comp M.inclusion

/-- Failure of restricted range membership rejects exactly corrections using this mask. -/
theorem no_correction_of_not_mem_range [CommRing k] (S : Scheme k a b c r)
    (M : VariationMask a b c r) (residual : Tensor k a b c)
    (hresidual : residual ∉ LinearMap.range (M.restrictedJacobian S)) :
    ¬ ∃ d : M.allowed (k := k), M.restrictedJacobian S d = residual := by
  rintro ⟨d, hd⟩
  exact hresidual ⟨d, hd⟩

/-- A restricted correction exists exactly when the scoped residual is in the scoped range. -/
theorem correction_iff_mem_range [CommRing k] (S : Scheme k a b c r)
    (M : VariationMask a b c r) (residual : Tensor k a b c) :
    (∃ d : M.allowed (k := k), M.restrictedJacobian S d = residual) ↔
      residual ∈ LinearMap.range (M.restrictedJacobian S) := by
  rfl

end VariationMask

/-- The truncated-polynomial coefficient ring `k[t]/(t^4)`. -/
abbrev TruncatedPolynomial (k : Type*) [CommRing k] :=
  AdjoinRoot ((Polynomial.X : Polynomial k) ^ 4)

/-- The residue class of `t` in `k[t]/(t^4)`. -/
noncomputable def truncatedParameter (k : Type*) [CommRing k] : TruncatedPolynomial k :=
  AdjoinRoot.root ((Polynomial.X : Polynomial k) ^ 4)

/-- The truncated parameter has fourth power zero. -/
@[simp] theorem truncatedParameter_pow_four (k : Type*) [CommRing k] :
    truncatedParameter k ^ 4 = 0 := by
  change AdjoinRoot.mk ((Polynomial.X : Polynomial k) ^ 4) (Polynomial.X ^ 4) = 0
  exact AdjoinRoot.mk_eq_zero.mpr dvd_rfl

/-- Specialization at `t = 0` from the truncated-polynomial ring back to its coefficient ring. -/
noncomputable def truncatedResidue (k : Type*) [CommRing k] :
    TruncatedPolynomial k →+* k :=
  AdjoinRoot.lift (RingHom.id k) 0 (by simp)

/-- Residue specialization sends the truncated parameter to zero. -/
@[simp] theorem truncatedResidue_parameter (k : Type*) [CommRing k] :
    truncatedResidue k (truncatedParameter k) = 0 := by
  exact AdjoinRoot.lift_root _

/-- Residue specialization is the identity on scalar coefficients. -/
@[simp] theorem truncatedResidue_algebraMap (k : Type*) [CommRing k] (x : k) :
    truncatedResidue k (algebraMap k (TruncatedPolynomial k) x) = x := by
  exact AdjoinRoot.lift_of _

/-- Vanishing of a polynomial with only first, second, and third truncated coefficients forces
all three coefficients to vanish. -/
theorem truncatedPolynomial_coefficients_eq_zero [CommRing k] (x₁ x₂ x₃ : k)
    (h : truncatedParameter k * algebraMap k (TruncatedPolynomial k) x₁ +
      truncatedParameter k ^ 2 * algebraMap k (TruncatedPolynomial k) x₂ +
      truncatedParameter k ^ 3 * algebraMap k (TruncatedPolynomial k) x₃ = 0) :
    x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0 := by
  change AdjoinRoot.mk ((Polynomial.X : Polynomial k) ^ 4)
    (Polynomial.X * Polynomial.C x₁ + Polynomial.X ^ 2 * Polynomial.C x₂ +
      Polynomial.X ^ 3 * Polynomial.C x₃) = 0 at h
  have hdvd : (Polynomial.X : Polynomial k) ^ 4 ∣
      Polynomial.X * Polynomial.C x₁ + Polynomial.X ^ 2 * Polynomial.C x₂ +
        Polynomial.X ^ 3 * Polynomial.C x₃ := AdjoinRoot.mk_eq_zero.mp h
  have hcoeff := Polynomial.X_pow_dvd_iff.mp hdvd
  constructor
  · simpa using hcoeff 1 (by decide)
  constructor
  · simpa using hcoeff 2 (by decide)
  · simpa using hcoeff 3 (by decide)

/-- The genuine `k[t]/(t^4)` scheme with the displayed first three factor coefficients. -/
noncomputable def orderThreeScheme [CommRing k] (S : Scheme k a b c r)
    (d₁ d₂ d₃ : Variation k a b c r) :
    Scheme (TruncatedPolynomial k) a b c r :=
  ⟨fun s =>
    (fun i => algebraMap k (TruncatedPolynomial k) ((S.term s).1 i) +
      truncatedParameter k * algebraMap k (TruncatedPolynomial k) ((d₁ s).1 i) +
      truncatedParameter k ^ 2 * algebraMap k (TruncatedPolynomial k) ((d₂ s).1 i) +
      truncatedParameter k ^ 3 * algebraMap k (TruncatedPolynomial k) ((d₃ s).1 i),
    fun j => algebraMap k (TruncatedPolynomial k) ((S.term s).2.1 j) +
      truncatedParameter k * algebraMap k (TruncatedPolynomial k) ((d₁ s).2.1 j) +
      truncatedParameter k ^ 2 * algebraMap k (TruncatedPolynomial k) ((d₂ s).2.1 j) +
      truncatedParameter k ^ 3 * algebraMap k (TruncatedPolynomial k) ((d₃ s).2.1 j),
    fun l => algebraMap k (TruncatedPolynomial k) ((S.term s).2.2 l) +
      truncatedParameter k * algebraMap k (TruncatedPolynomial k) ((d₁ s).2.2 l) +
      truncatedParameter k ^ 2 * algebraMap k (TruncatedPolynomial k) ((d₂ s).2.2 l) +
      truncatedParameter k ^ 3 * algebraMap k (TruncatedPolynomial k) ((d₃ s).2.2 l))⟩

/-- Residue specialization of the truncated scheme is literally the base scheme. -/
@[simp] theorem orderThreeScheme_map_truncatedResidue [CommRing k]
    (S : Scheme k a b c r) (d₁ d₂ d₃ : Variation k a b c r) :
    (orderThreeScheme S d₁ d₂ d₃).map (truncatedResidue k) = S := by
  apply congrArg Scheme.mk
  funext s
  apply Prod.ext
  · funext i
    simp only [orderThreeScheme, map_add, map_mul,
      truncatedResidue_parameter, pow_succ, pow_zero, one_mul, zero_mul, add_zero]
    exact truncatedResidue_algebraMap k _
  · apply Prod.ext
    · funext j
      simp only [orderThreeScheme, map_add, map_mul,
        truncatedResidue_parameter, pow_succ, pow_zero, one_mul, zero_mul, add_zero]
      exact truncatedResidue_algebraMap k _
    · funext l
      simp only [orderThreeScheme, map_add, map_mul,
        truncatedResidue_parameter, pow_succ, pow_zero, one_mul, zero_mul, add_zero]
      exact truncatedResidue_algebraMap k _

/-- Direct multiplication of three factor arcs over a ring with a fourth-power-zero parameter,
retaining exactly the coefficients through order three. -/
theorem orderThreeFactor_expansion {R : Type*} [CommRing R] (t : R) (ht : t ^ 4 = 0)
    (U V W u₁ v₁ w₁ u₂ v₂ w₂ u₃ v₃ w₃ : R) :
    (U + t * u₁ + t ^ 2 * u₂ + t ^ 3 * u₃) *
      (V + t * v₁ + t ^ 2 * v₂ + t ^ 3 * v₃) *
      (W + t * w₁ + t ^ 2 * w₂ + t ^ 3 * w₃) =
    U * V * W +
    t * (u₁ * V * W + U * v₁ * W + U * V * w₁) +
    t ^ 2 * (u₂ * V * W + U * v₂ * W + U * V * w₂ +
      u₁ * v₁ * W + u₁ * V * w₁ + U * v₁ * w₁) +
    t ^ 3 * (u₃ * V * W + U * v₃ * W + U * V * w₃ +
      (u₁ * v₂ + u₂ * v₁) * W + (u₁ * w₂ + u₂ * w₁) * V +
      (v₁ * w₂ + v₂ * w₁) * U + u₁ * v₁ * w₁) := by
  have ht5 : t ^ 5 = 0 := by
    calc
      t ^ 5 = t ^ 4 * t := by ring
      _ = 0 := by rw [ht, zero_mul]
  have ht6 : t ^ 6 = 0 := by
    calc
      t ^ 6 = t ^ 4 * t ^ 2 := by ring
      _ = 0 := by rw [ht, zero_mul]
  have ht7 : t ^ 7 = 0 := by
    calc
      t ^ 7 = t ^ 4 * t ^ 3 := by ring
      _ = 0 := by rw [ht, zero_mul]
  have ht8 : t ^ 8 = 0 := by
    calc
      t ^ 8 = t ^ 4 * t ^ 4 := by ring
      _ = 0 := by rw [ht, zero_mul]
  have ht9 : t ^ 9 = 0 := by
    calc
      t ^ 9 = t ^ 4 * t ^ 5 := by ring
      _ = 0 := by rw [ht, zero_mul]
  ring_nf
  simp only [ht, ht5, ht6, ht7, ht8, ht9, zero_mul, mul_zero, add_zero]

/-- The represented tensor of the truncated scheme has exactly the expected first, second,
and third coefficients after scalar extension to `k[t]/(t^4)`. -/
theorem sumTensor_orderThreeScheme [CommRing k] (S : Scheme k a b c r)
    (d₁ d₂ d₃ : Variation k a b c r) :
    (orderThreeScheme S d₁ d₂ d₃).sumTensor =
      Scheme.mapTensor (algebraMap k (TruncatedPolynomial k)) S.sumTensor +
      (truncatedParameter k •
        Scheme.mapTensor (algebraMap k (TruncatedPolynomial k)) (jacobian S d₁) +
      truncatedParameter k ^ 2 • Scheme.mapTensor (algebraMap k (TruncatedPolynomial k))
        (jacobian S d₂ + quadraticCoefficient S d₁) +
      truncatedParameter k ^ 3 • Scheme.mapTensor (algebraMap k (TruncatedPolynomial k))
        (jacobian S d₃ + mixedQuadraticCoefficient S d₁ d₂ + cubicCoefficient S d₁)) := by
  have ht5 : truncatedParameter k ^ 5 = 0 := by
    calc
      truncatedParameter k ^ 5 = truncatedParameter k ^ 4 * truncatedParameter k := by ring
      _ = 0 := by rw [truncatedParameter_pow_four, zero_mul]
  have ht6 : truncatedParameter k ^ 6 = 0 := by
    calc
      truncatedParameter k ^ 6 = truncatedParameter k ^ 4 * truncatedParameter k ^ 2 := by ring
      _ = 0 := by rw [truncatedParameter_pow_four, zero_mul]
  have ht7 : truncatedParameter k ^ 7 = 0 := by
    calc
      truncatedParameter k ^ 7 = truncatedParameter k ^ 4 * truncatedParameter k ^ 3 := by ring
      _ = 0 := by rw [truncatedParameter_pow_four, zero_mul]
  have ht8 : truncatedParameter k ^ 8 = 0 := by
    calc
      truncatedParameter k ^ 8 = truncatedParameter k ^ 4 * truncatedParameter k ^ 4 := by ring
      _ = 0 := by rw [truncatedParameter_pow_four, zero_mul]
  have ht9 : truncatedParameter k ^ 9 = 0 := by
    calc
      truncatedParameter k ^ 9 = truncatedParameter k ^ 4 * truncatedParameter k ^ 5 := by ring
      _ = 0 := by rw [truncatedParameter_pow_four, zero_mul]
  funext i j l
  simp only [sumTensor, orderThreeScheme, TriadData.eval, triad, Scheme.mapTensor,
    jacobian_apply, linearCoefficient, quadraticCoefficient, cubicCoefficient,
    mixedQuadraticCoefficient, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    map_sum, map_add, map_mul]
  simp only [mul_add]
  repeat' rw [Finset.mul_sum]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _hs
  ring_nf
  simp only [truncatedParameter_pow_four, ht5, ht6, ht7, ht8, ht9,
    zero_mul, mul_zero, add_zero]

/-- The first lifting equation for an exact truncated decomposition. -/
def FirstOrderEquation [CommRing k] (S : Scheme k a b c r)
    (d₁ : Variation k a b c r) : Prop :=
  jacobian S d₁ = 0

/-- The second lifting equation, with an independent second coefficient. -/
def SecondOrderEquation [CommRing k] (S : Scheme k a b c r)
    (d₁ d₂ : Variation k a b c r) : Prop :=
  jacobian S d₂ + quadraticCoefficient S d₁ = 0

/-- The third lifting equation displays both the mixed quadratic and cubic coefficients. -/
def ThirdOrderEquation [CommRing k] (S : Scheme k a b c r)
    (d₁ d₂ d₃ : Variation k a b c r) : Prop :=
  jacobian S d₃ + mixedQuadraticCoefficient S d₁ d₂ + cubicCoefficient S d₁ = 0

/-- A finite order-three arc is a genuine ordered scheme over `k[t]/(t^4)` whose represented
tensor is literally the scalar extension of the base represented tensor. -/
structure OrderThreeArc [CommRing k] (S : Scheme k a b c r) where
  /-- First factor coefficient. -/
  first : Variation k a b c r
  /-- Second factor coefficient. -/
  second : Variation k a b c r
  /-- Third factor coefficient. -/
  third : Variation k a b c r
  /-- Semantic equality of represented tensors over the truncated-polynomial coefficient ring. -/
  represented : (orderThreeScheme S first second third).sumTensor =
    Scheme.mapTensor (algebraMap k (TruncatedPolynomial k)) S.sumTensor

/-- The truncated-polynomial scheme carried by an order-three arc. -/
noncomputable def OrderThreeArc.scheme [CommRing k] {S : Scheme k a b c r}
    (A : OrderThreeArc S) : Scheme (TruncatedPolynomial k) a b c r :=
  orderThreeScheme S A.first A.second A.third

/-- The scheme carried by an order-three arc specializes under residue to its base scheme. -/
@[simp] theorem OrderThreeArc.scheme_map_truncatedResidue [CommRing k]
    {S : Scheme k a b c r} (A : OrderThreeArc S) :
    A.scheme.map (truncatedResidue k) = S := by
  exact orderThreeScheme_map_truncatedResidue S A.first A.second A.third

/-- The represented tensor of an order-three arc is the literal base scalar extension. -/
theorem OrderThreeArc.scheme_sumTensor [CommRing k] {S : Scheme k a b c r}
    (A : OrderThreeArc S) :
    A.scheme.sumTensor = Scheme.mapTensor (algebraMap k (TruncatedPolynomial k)) S.sumTensor :=
  A.represented

/-- Validity of the base ordered decomposition reflects to every semantic order-three arc.
The residue specialization detects nonzero evaluated terms and collisions between ordered slots. -/
theorem OrderThreeArc.scheme_valid [CommRing k] {T : Tensor k a b c}
    {S : Scheme k a b c r} (A : OrderThreeArc S) (hS : S.Valid T) :
    A.scheme.Valid (Scheme.mapTensor (algebraMap k (TruncatedPolynomial k)) T) := by
  refine ⟨A.scheme_sumTensor.trans (congrArg
    (Scheme.mapTensor (algebraMap k (TruncatedPolynomial k))) hS.1), ?_, ?_⟩
  · intro s hzero
    apply hS.2.1 s
    have hterm : Scheme.mapTensor (truncatedResidue k) (A.scheme.term s).eval =
        (S.term s).eval := by
      rw [← Scheme.eval_map]
      exact congrArg (fun R => (R.term s).eval) A.scheme_map_truncatedResidue
    rw [← hterm, hzero]
    funext i j l
    simp only [Scheme.mapTensor, Pi.zero_apply, map_zero]
  · intro s t hst
    apply hS.2.2
    change (S.term s).eval = (S.term t).eval
    have hs : Scheme.mapTensor (truncatedResidue k) (A.scheme.term s).eval =
        (S.term s).eval := by
      rw [← Scheme.eval_map]
      exact congrArg (fun R => (R.term s).eval) A.scheme_map_truncatedResidue
    have ht : Scheme.mapTensor (truncatedResidue k) (A.scheme.term t).eval =
        (S.term t).eval := by
      rw [← Scheme.eval_map]
      exact congrArg (fun R => (R.term t).eval) A.scheme_map_truncatedResidue
    rw [← hs, ← ht]
    exact congrArg (Scheme.mapTensor (truncatedResidue k)) hst

/-- A validity-bearing semantic arc packages valid base and truncated ordered decompositions,
without quotienting or relabeling the termwise coefficient data carried by its arc. -/
structure ValidOrderThreeArc [CommRing k] (T : Tensor k a b c)
    (S : Scheme k a b c r) where
  /-- The ordered semantic order-three arc. -/
  arc : OrderThreeArc S
  /-- Validity of the ordered base decomposition. -/
  base_valid : S.Valid T
  /-- Validity of the ordered truncated decomposition over `k[t]/(t^4)`. -/
  truncated_valid : arc.scheme.Valid
    (Scheme.mapTensor (algebraMap k (TruncatedPolynomial k)) T)

/-- Attach base and truncated validity to a semantic order-three arc. -/
noncomputable def OrderThreeArc.withValidity [CommRing k] {T : Tensor k a b c}
    {S : Scheme k a b c r} (A : OrderThreeArc S) (hS : S.Valid T) :
    ValidOrderThreeArc T S where
  arc := A
  base_valid := hS
  truncated_valid := A.scheme_valid hS

/-- The constant truncated-polynomial scheme supplies an order-three arc through every base
scheme, jointly witnessing satisfiability of the semantic arc predicate. -/
noncomputable def OrderThreeArc.constant [CommRing k] (S : Scheme k a b c r) :
    OrderThreeArc S where
  first := 0
  second := 0
  third := 0
  represented := by
    rw [sumTensor_orderThreeScheme]
    have hJzero : jacobian S (0 : Variation k a b c r) = 0 := map_zero (jacobian S)
    rw [hJzero, quadraticCoefficient_zero, cubicCoefficient_zero,
      mixedQuadraticCoefficient_zero_zero]
    have hmapzero : Scheme.mapTensor (algebraMap k (TruncatedPolynomial k))
        (0 : Tensor k a b c) = 0 := by
      funext i j l
      simp only [Scheme.mapTensor, Pi.zero_apply, map_zero]
    simp only [hmapzero, smul_zero, add_zero]

private theorem OrderThreeArc.coefficient_equations [CommRing k]
    {S : Scheme k a b c r} (A : OrderThreeArc S) :
    FirstOrderEquation S A.first ∧ SecondOrderEquation S A.first A.second ∧
      ThirdOrderEquation S A.first A.second A.third := by
  have hcoeff (i : Fin a) (j : Fin b) (l : Fin c) :
      jacobian S A.first i j l = 0 ∧
      (jacobian S A.second + quadraticCoefficient S A.first) i j l = 0 ∧
      (jacobian S A.third + mixedQuadraticCoefficient S A.first A.second +
        cubicCoefficient S A.first) i j l = 0 := by
    have hentry := congrFun (congrFun (congrFun
      ((sumTensor_orderThreeScheme S A.first A.second A.third).symm.trans A.represented)
      i) j) l
    simp only [Pi.add_apply, Pi.smul_apply, Scheme.mapTensor, smul_eq_mul] at hentry
    have hzero :
        truncatedParameter k * algebraMap k (TruncatedPolynomial k)
          (jacobian S A.first i j l) +
        truncatedParameter k ^ 2 * algebraMap k (TruncatedPolynomial k)
          ((jacobian S A.second + quadraticCoefficient S A.first) i j l) +
        truncatedParameter k ^ 3 * algebraMap k (TruncatedPolynomial k)
          ((jacobian S A.third + mixedQuadraticCoefficient S A.first A.second +
            cubicCoefficient S A.first) i j l) = 0 := by
      calc
        _ = (Scheme.mapTensor (algebraMap k (TruncatedPolynomial k)) S.sumTensor i j l +
            (truncatedParameter k * algebraMap k (TruncatedPolynomial k)
              (jacobian S A.first i j l) +
            truncatedParameter k ^ 2 * algebraMap k (TruncatedPolynomial k)
              ((jacobian S A.second + quadraticCoefficient S A.first) i j l) +
            truncatedParameter k ^ 3 * algebraMap k (TruncatedPolynomial k)
              ((jacobian S A.third + mixedQuadraticCoefficient S A.first A.second +
                cubicCoefficient S A.first) i j l))) -
              Scheme.mapTensor (algebraMap k (TruncatedPolynomial k)) S.sumTensor i j l := by
          ring
        _ = Scheme.mapTensor (algebraMap k (TruncatedPolynomial k)) S.sumTensor i j l -
              Scheme.mapTensor (algebraMap k (TruncatedPolynomial k)) S.sumTensor i j l :=
          congrArg (fun x => x -
            Scheme.mapTensor (algebraMap k (TruncatedPolynomial k)) S.sumTensor i j l) hentry
        _ = 0 := sub_self _
    exact truncatedPolynomial_coefficients_eq_zero _ _ _ hzero
  refine ⟨?_, ?_, ?_⟩
  · funext i j l
    exact (hcoeff i j l).1
  · funext i j l
    exact (hcoeff i j l).2.1
  · funext i j l
    exact (hcoeff i j l).2.2

/-- The first coefficient equation is derived from the represented-tensor equality of the
truncated-polynomial scheme. -/
theorem OrderThreeArc.first_eq [CommRing k] {S : Scheme k a b c r}
    (A : OrderThreeArc S) : FirstOrderEquation S A.first :=
  A.coefficient_equations.1

/-- The second coefficient equation is derived from the represented-tensor equality of the
truncated-polynomial scheme. -/
theorem OrderThreeArc.second_eq [CommRing k] {S : Scheme k a b c r}
    (A : OrderThreeArc S) : SecondOrderEquation S A.first A.second :=
  A.coefficient_equations.2.1

/-- The third coefficient equation is derived from the represented-tensor equality of the
truncated-polynomial scheme. -/
theorem OrderThreeArc.third_eq [CommRing k] {S : Scheme k a b c r}
    (A : OrderThreeArc S) : ThirdOrderEquation S A.first A.second A.third :=
  A.coefficient_equations.2.2

/-- The coefficient selected from a three-step truncation. -/
def OrderThreeArc.coefficient [CommRing k] {S : Scheme k a b c r}
    (A : OrderThreeArc S) : Fin 3 → Variation k a b c r :=
  ![A.first, A.second, A.third]

/-- Any coefficient preceded by zero lower coefficients satisfies the Jacobian kernel equation. -/
theorem OrderThreeArc.coefficient_mem_ker_of_lower_eq_zero [CommRing k]
    {S : Scheme k a b c r} (A : OrderThreeArc S) (q : Fin 3)
    (hlower : ∀ p, p < q → A.coefficient p = 0) :
    A.coefficient q ∈ LinearMap.ker (jacobian S) := by
  fin_cases q
  · exact A.first_eq
  · have hfirst : A.first = 0 := hlower 0 (by decide)
    change jacobian S A.second = 0
    have hsecond := A.second_eq
    change jacobian S A.second + quadraticCoefficient S A.first = 0 at hsecond
    rw [hfirst, quadraticCoefficient_zero, add_zero] at hsecond
    exact hsecond
  · have hfirst : A.first = 0 := hlower 0 (by decide)
    have hsecond : A.second = 0 := hlower 1 (by decide)
    change jacobian S A.third = 0
    have hthird := A.third_eq
    change jacobian S A.third + mixedQuadraticCoefficient S A.first A.second +
      cubicCoefficient S A.first = 0 at hthird
    rw [hfirst, hsecond, mixedQuadraticCoefficient_zero_zero, cubicCoefficient_zero,
      add_zero, add_zero] at hthird
    exact hthird

/-- A coefficient explicitly certified as the first nonzero coefficient is
nonzero and satisfies the Jacobian kernel equation. -/
theorem OrderThreeArc.first_nonzero_mem_ker [CommRing k]
    {S : Scheme k a b c r} (A : OrderThreeArc S) (q : Fin 3)
    (hlower : ∀ p, p < q → A.coefficient p = 0)
    (hnonzero : A.coefficient q ≠ 0) :
    A.coefficient q ≠ 0 ∧ A.coefficient q ∈ LinearMap.ker (jacobian S) :=
  ⟨hnonzero, A.coefficient_mem_ker_of_lower_eq_zero q hlower⟩

/-- Stable explicit-nontriviality form of the first-nonzero kernel theorem. -/
theorem OrderThreeArc.genuine_first_nonzero_mem_ker [CommRing k]
    {S : Scheme k a b c r} (A : OrderThreeArc S) (q : Fin 3)
    (hlower : ∀ p, p < q → A.coefficient p = 0)
    (hnonzero : A.coefficient q ≠ 0) :
    A.coefficient q ≠ 0 ∧ A.coefficient q ∈ LinearMap.ker (jacobian S) :=
  A.first_nonzero_mem_ker q hlower hnonzero

/-- The semantic order-three arc predicate is jointly satisfiable for every base scheme. -/
example [CommRing k] (S : Scheme k a b c r) : Nonempty (OrderThreeArc S) :=
  ⟨OrderThreeArc.constant S⟩

/- A concrete validity-bearing semantic arc with a genuinely nonzero first coefficient. -/
namespace SemanticArcFixture

/-- The prime field used by the validity-bearing semantic arc fixture. -/
abbrev F := ZMod 101

/-- The nonzero tensor represented by the one-term fixture. -/
def target : Tensor F 1 1 1 := fun _ _ _ => 1

/-- The one-term ordered base scheme with three nonzero scalar factors. -/
def base : Scheme F 1 1 1 1 := ⟨fun _ => (![1], ![1], ![1])⟩

/-- The linear term of reciprocal term scaling: multiply the first factor by `1+t`. -/
def firstDirection : Variation F 1 1 1 1 := fun _ => (![1], ![-1], ![0])

/-- The quadratic term in the truncated reciprocal of `1+t`. -/
def secondDirection : Variation F 1 1 1 1 := fun _ => (![0], ![1], ![0])

/-- The cubic term in the truncated reciprocal of `1+t`. -/
def thirdDirection : Variation F 1 1 1 1 := fun _ => (![0], ![-1], ![0])

/-- The base fixture is a valid ordered decomposition of its nonzero target. -/
theorem base_valid : base.Valid target := by
  refine ⟨?_, ?_, ?_⟩
  · funext i j l
    fin_cases i
    fin_cases j
    fin_cases l
    simp [Scheme.sumTensor, base, target, TriadData.eval, triad]
  · intro s hzero
    have hentry := congrFun (congrFun (congrFun hzero 0) 0) 0
    change (1 : F) = 0 at hentry
    have hone : (1 : F) ≠ 0 := by decide
    exact hone hentry
  · intro s t _hst
    exact Subsingleton.elim s t

/-- The reciprocal term-scaling coefficients define a semantic order-three arc: modulo
`t^4`, `(1+t)(1-t+t^2-t^3)=1`, while the third factor remains one. -/
noncomputable def arc : OrderThreeArc base where
  first := firstDirection
  second := secondDirection
  third := thirdDirection
  represented := by
    funext i j l
    fin_cases i
    fin_cases j
    fin_cases l
    simp only [sumTensor, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
      TriadData.eval, triad, orderThreeScheme, AdjoinRoot.algebraMap_eq, base,
      Matrix.cons_val_fin_one, map_one, firstDirection, mul_one, secondDirection,
      map_zero, mul_zero, add_zero, thirdDirection, map_neg, mul_neg, Fin.zero_eta,
      Finset.sum_const, Finset.card_singleton, one_smul, mapTensor]
    ring_nf
    rw [truncatedParameter_pow_four]
    ring

/-- The fixture literally packages valid base and truncated ordered decompositions. -/
noncomputable def validArc : ValidOrderThreeArc target base :=
  arc.withValidity base_valid

/-- The truncated term-scaling scheme is valid for the scalar-extended nonzero target. -/
theorem truncated_valid : arc.scheme.Valid
    (Scheme.mapTensor (algebraMap F (TruncatedPolynomial F)) target) :=
  validArc.truncated_valid

/-- The fixture's semantic represented-tensor equality is exposed independently of validity. -/
theorem represented : arc.scheme.sumTensor =
    Scheme.mapTensor (algebraMap F (TruncatedPolynomial F)) base.sumTensor :=
  arc.scheme_sumTensor

/-- The first coefficient of the valid term-scaling arc is genuinely nonzero. -/
theorem first_coefficient_ne_zero : arc.coefficient 0 ≠ 0 := by
  intro hzero
  have hentry := congrFun (congrArg Prod.fst (congrFun hzero 0)) 0
  change (1 : F) = 0 at hentry
  have hone : (1 : F) ≠ 0 := by decide
  exact hone hentry

/-- There are no coefficients below the fixture's nonzero linear coefficient. -/
theorem first_coefficient_is_initial :
    ∀ p, p < (0 : Fin 3) → arc.coefficient p = 0 := by
  intro p hp
  exact (Fin.not_lt_zero p hp).elim

end SemanticArcFixture

/-- The full cokernel of the ambient Jacobian. -/
abbrev JacobianCokernel [CommRing k] (S : Scheme k a b c r) :=
  Tensor k a b c ⧸ LinearMap.range (jacobian S)

/-- The cokernel of a Jacobian restricted to the specified variation mask. -/
abbrev RestrictedJacobianCokernel [CommRing k] (S : Scheme k a b c r)
    (M : VariationMask a b c r) :=
  Tensor k a b c ⧸ LinearMap.range (M.restrictedJacobian S)

/-- The second-order obstruction class of a prescribed first-order kernel direction. -/
def obstructionClass [CommRing k] (S : Scheme k a b c r)
    (d₁ : LinearMap.ker (jacobian S)) : JacobianCokernel S :=
  (LinearMap.range (jacobian S)).mkQ (quadraticCoefficient S d₁.1)

/-- The same quadratic residual viewed in the cokernel of a specified restricted Jacobian. -/
def restrictedObstructionClass [CommRing k] (S : Scheme k a b c r)
    (M : VariationMask a b c r) (d₁ : LinearMap.ker (jacobian S)) :
    RestrictedJacobianCokernel S M :=
  (LinearMap.range (M.restrictedJacobian S)).mkQ (quadraticCoefficient S d₁.1)

/-- Vanishing of the full obstruction is equivalent to existence of an unrestricted second
coefficient solving the second lifting equation. -/
theorem obstructionClass_eq_zero_iff [CommRing k] (S : Scheme k a b c r)
    (d₁ : LinearMap.ker (jacobian S)) :
    obstructionClass S d₁ = 0 ↔
      ∃ d₂ : Variation k a b c r,
        jacobian S d₂ + quadraticCoefficient S d₁.1 = 0 := by
  rw [obstructionClass, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨e, he⟩
    refine ⟨-e, ?_⟩
    rw [map_neg, he]
    simp only [neg_add_cancel]
  · rintro ⟨d₂, hd₂⟩
    refine ⟨-d₂, ?_⟩
    rw [map_neg]
    calc
      -(jacobian S d₂) = -(jacobian S d₂) + 0 := (add_zero _).symm
      _ = -(jacobian S d₂) +
          (jacobian S d₂ + quadraticCoefficient S d₁.1) :=
        congrArg (fun x => -(jacobian S d₂) + x) hd₂.symm
      _ = quadraticCoefficient S d₁.1 := by
        simp only [neg_add_cancel_left]

/-- Vanishing of the restricted obstruction is equivalent to a second coefficient using
exactly the variables allowed by the specified mask. -/
theorem restrictedObstructionClass_eq_zero_iff [CommRing k]
    (S : Scheme k a b c r) (M : VariationMask a b c r)
    (d₁ : LinearMap.ker (jacobian S)) :
    restrictedObstructionClass S M d₁ = 0 ↔
      ∃ d₂ : M.allowed (k := k),
        M.restrictedJacobian S d₂ + quadraticCoefficient S d₁.1 = 0 := by
  rw [restrictedObstructionClass, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨e, he⟩
    refine ⟨-e, ?_⟩
    rw [map_neg, he]
    simp only [neg_add_cancel]
  · rintro ⟨d₂, hd₂⟩
    refine ⟨-d₂, ?_⟩
    rw [map_neg]
    calc
      -(M.restrictedJacobian S d₂) = -(M.restrictedJacobian S d₂) + 0 :=
        (add_zero _).symm
      _ = -(M.restrictedJacobian S d₂) +
          (M.restrictedJacobian S d₂ + quadraticCoefficient S d₁.1) :=
        congrArg (fun x => -(M.restrictedJacobian S d₂) + x) hd₂.symm
      _ = quadraticCoefficient S d₁.1 := by
        simp only [neg_add_cancel_left]

/-- The second-order equation of a three-step truncation makes its first coefficient's full
obstruction class vanish; this is only a necessary finite-order consequence. -/
theorem OrderThreeArc.obstructionClass_first_eq_zero [CommRing k]
    {S : Scheme k a b c r} (A : OrderThreeArc S) :
    obstructionClass S ⟨A.first, A.first_eq⟩ = 0 := by
  apply (obstructionClass_eq_zero_iff S ⟨A.first, A.first_eq⟩).mpr
  exact ⟨A.second, A.second_eq⟩

/-- A nonzero full-cokernel class forbids a second-order lift even when all scheme coordinates
are available to the second coefficient. -/
theorem no_unrestricted_secondOrderLift_of_obstruction_ne_zero [CommRing k]
    (S : Scheme k a b c r) (d₁ : LinearMap.ker (jacobian S))
    (hobs : obstructionClass S d₁ ≠ 0) :
    ¬ ∃ d₂ : Variation k a b c r,
      jacobian S d₂ + quadraticCoefficient S d₁.1 = 0 := by
  intro hlift
  exact hobs ((obstructionClass_eq_zero_iff S d₁).mpr hlift)

/-- A nonzero restricted-cokernel class forbids a second coefficient only in the domain
selected by that mask. -/
theorem no_restricted_secondOrderLift_of_obstruction_ne_zero [CommRing k]
    (S : Scheme k a b c r) (M : VariationMask a b c r)
    (d₁ : LinearMap.ker (jacobian S))
    (hobs : restrictedObstructionClass S M d₁ ≠ 0) :
    ¬ ∃ d₂ : M.allowed (k := k),
      M.restrictedJacobian S d₂ + quadraticCoefficient S d₁.1 = 0 := by
  intro hlift
  exact hobs ((restrictedObstructionClass_eq_zero_iff S M d₁).mpr hlift)

/-- The same-mask obstruction test concerns only second coefficients in the specified
restricted domain. -/
theorem no_restricted_secondOrderLift_of_not_mem_range [CommRing k]
    (S : Scheme k a b c r) (M : VariationMask a b c r)
    (d₁ : LinearMap.ker (jacobian S))
    (hobs : -quadraticCoefficient S d₁.1 ∉
      LinearMap.range (M.restrictedJacobian S)) :
    ¬ ∃ d₂ : M.allowed (k := k),
      M.restrictedJacobian S d₂ + quadraticCoefficient S d₁.1 = 0 := by
  rintro ⟨d₂, hd₂⟩
  apply hobs
  refine ⟨d₂, ?_⟩
  exact eq_neg_of_add_eq_zero_left hd₂

/-- The affine family of first-order solutions obtained by adding a parametrized kernel family. -/
def affineFirstOrder [CommRing k] {z : Type*} [AddCommGroup z] [Module k z]
    (d₀ : Variation k a b c r) (N : z →ₗ[k] Variation k a b c r) (p : z) :
    Variation k a b c r :=
  d₀ + N p

/-- If a particular first-order solution and every direction in `N` solve the same linear
system, the whole displayed affine family does too. -/
theorem jacobian_affineFirstOrder [CommRing k] {z : Type*} [AddCommGroup z] [Module k z]
    (S : Scheme k a b c r) (d₀ : Variation k a b c r)
    (N : z →ₗ[k] Variation k a b c r) (residual : Tensor k a b c)
    (hd₀ : jacobian S d₀ = residual)
    (hN : LinearMap.range N ≤ LinearMap.ker (jacobian S)) (p : z) :
    jacobian S (affineFirstOrder d₀ N p) = residual := by
  rw [affineFirstOrder, map_add, hd₀]
  have hzero : jacobian S (N p) = 0 := hN ⟨p, rfl⟩
  rw [hzero, add_zero]

/-- Rejecting every member of an affine first-order family requires the quadratic obstruction
check for every parameter, rather than only at the base point or on generators. -/
theorem no_secondOrderLift_on_affine_family [CommRing k]
    {z : Type*} [AddCommGroup z] [Module k z]
    (S : Scheme k a b c r) (d₀ : Variation k a b c r)
    (N : z →ₗ[k] Variation k a b c r)
    (hkernel : ∀ p, affineFirstOrder d₀ N p ∈ LinearMap.ker (jacobian S))
    (hobs : ∀ p, obstructionClass S ⟨affineFirstOrder d₀ N p, hkernel p⟩ ≠ 0) :
    ¬ ∃ p d₂, jacobian S d₂ + quadraticCoefficient S (affineFirstOrder d₀ N p) = 0 := by
  rintro ⟨p, d₂, hlift⟩
  exact hobs p ((obstructionClass_eq_zero_iff S
    ⟨affineFirstOrder d₀ N p, hkernel p⟩).mpr ⟨d₂, hlift⟩)

/-- Over characteristic two the diagonal of the polarization vanishes, so it cannot recover
the quadratic coefficient. -/
theorem mixedQuadratic_self_eq_zero_of_charTwo [CommRing k] [CharP k 2]
    (S : Scheme k a b c r) (d : Variation k a b c r) :
    mixedQuadraticCoefficient S d d = 0 := by
  rw [mixedQuadraticCoefficient_self]
  have htwo : (2 : k) = 0 := CharP.cast_eq_zero k 2
  rw [htwo, zero_smul]

/-- A direct scalar test over `F₂`: polarization vanishes on the diagonal while the quadratic
coefficient is nonzero. -/
example :
    let S : Scheme (ZMod 2) 1 1 1 1 := ⟨fun _ => (![1], ![1], ![1])⟩
    let d : Variation (ZMod 2) 1 1 1 1 := fun _ => (![1], ![1], ![0])
    mixedQuadraticCoefficient S d d = 0 ∧ quadraticCoefficient S d ≠ 0 := by
  dsimp only
  constructor
  · exact mixedQuadratic_self_eq_zero_of_charTwo _ _
  · intro hzero
    have hentry := congrFun (congrFun (congrFun hzero 0) 0) 0
    norm_num [quadraticCoefficient] at hentry

/-- Independently reduced ground values over `ZMod 101` distinguish the Jacobian, quadratic,
cubic, mixed, direct one-step, and direct two-step formulas; every expected value is nonzero. -/
example :
    let S : Scheme (ZMod 101) 1 1 1 1 := ⟨fun _ => (![2], ![3], ![5])⟩
    let d₁ : Variation (ZMod 101) 1 1 1 1 := fun _ => (![7], ![11], ![13])
    let d₂ : Variation (ZMod 101) 1 1 1 1 := fun _ => (![17], ![19], ![29])
    jacobian S d₁ 0 0 0 = 91 ∧
      quadraticCoefficient S d₁ 0 0 0 = 35 ∧
      cubicCoefficient S d₁ 0 0 0 = 92 ∧
      mixedQuadraticCoefficient S d₁ d₂ 0 0 0 = 65 ∧
      (perturb S d₁ (4 : ZMod 101)).sumTensor 0 0 0 = 75 ∧
      (perturbTwoStep S d₁ d₂ (4 : ZMod 101)).sumTensor 0 0 0 = 40 := by
  decide

example :
    let S : Scheme (ZMod 101) 1 1 1 1 := ⟨fun _ => (![2], ![3], ![5])⟩
    let d₁ : Variation (ZMod 101) 1 1 1 1 := fun _ => (![7], ![11], ![13])
    let d₂ : Variation (ZMod 101) 1 1 1 1 := fun _ => (![17], ![19], ![29])
    jacobian S d₁ 0 0 0 ≠ 0 ∧
      quadraticCoefficient S d₁ 0 0 0 ≠ 0 ∧
      cubicCoefficient S d₁ 0 0 0 ≠ 0 ∧
      mixedQuadraticCoefficient S d₁ d₂ 0 0 0 ≠ 0 ∧
      (perturb S d₁ (4 : ZMod 101)).sumTensor 0 0 0 ≠ 0 ∧
      (perturbTwoStep S d₁ d₂ (4 : ZMod 101)).sumTensor 0 0 0 ≠ 0 := by
  decide

namespace TwoStepCoefficientOracle

/-- Ground scheme for direct evaluation of the high-order two-step coefficients. -/
def base : Scheme (ZMod 101) 1 1 1 1 := ⟨fun _ => (![2], ![3], ![5])⟩

/-- First ground variation for direct high-order coefficient evaluation. -/
def first : Variation (ZMod 101) 1 1 1 1 := fun _ => (![7], ![11], ![13])

/-- Second ground variation for direct high-order coefficient evaluation. -/
def second : Variation (ZMod 101) 1 1 1 1 := fun _ => (![17], ![19], ![29])

/-- Direct reduction of the defining finite sums gives the quartic, quintic, and terminal
cubic values, independently of the two-step expansion theorem. -/
theorem values :
    twoStepQuarticCoefficient base first second 0 0 0 = 85 ∧
      twoStepQuinticCoefficient base first second 0 0 0 = 46 ∧
      cubicCoefficient base second 0 0 0 = 75 := by
  decide

/-- All three independently computed high-order oracle values are nonzero. -/
theorem nonzero :
    twoStepQuarticCoefficient base first second 0 0 0 ≠ 0 ∧
      twoStepQuinticCoefficient base first second 0 0 0 ≠ 0 ∧
      cubicCoefficient base second 0 0 0 ≠ 0 := by
  decide

end TwoStepCoefficientOracle

#check @TruncatedPolynomial
#check @truncatedResidue
#check @orderThreeScheme
#check @orderThreeScheme_map_truncatedResidue
#check @orderThreeFactor_expansion
#check @sumTensor_orderThreeScheme
#check @OrderThreeArc
#check @OrderThreeArc.scheme
#check @OrderThreeArc.scheme_map_truncatedResidue
#check @OrderThreeArc.scheme_sumTensor
#check @OrderThreeArc.scheme_valid
#check @ValidOrderThreeArc
#check @OrderThreeArc.withValidity
#check @SemanticArcFixture.validArc
#check @SemanticArcFixture.base_valid
#check @SemanticArcFixture.truncated_valid
#check @SemanticArcFixture.represented
#check @SemanticArcFixture.first_coefficient_ne_zero
#check @TwoStepCoefficientOracle.values
#check @TwoStepCoefficientOracle.nonzero
#check @OrderThreeArc.first_eq
#check @OrderThreeArc.second_eq
#check @OrderThreeArc.third_eq
#check @OrderThreeArc.genuine_first_nonzero_mem_ker
#check @sumTensor_perturb
#check @sumTensor_perturbTwoStep
#check @VariationMask.restrictedJacobian
#check @VariationMask.no_correction_of_not_mem_range
#check @OrderThreeArc.first_nonzero_mem_ker
#check @obstructionClass_eq_zero_iff
#check @restrictedObstructionClass_eq_zero_iff
#check @OrderThreeArc.obstructionClass_first_eq_zero
#check @no_unrestricted_secondOrderLift_of_obstruction_ne_zero
#check @no_restricted_secondOrderLift_of_obstruction_ne_zero
#check @no_restricted_secondOrderLift_of_not_mem_range
#check @no_secondOrderLift_on_affine_family

#print axioms truncatedPolynomial_coefficients_eq_zero
#print axioms orderThreeScheme_map_truncatedResidue
#print axioms orderThreeFactor_expansion
#print axioms sumTensor_orderThreeScheme
#print axioms OrderThreeArc.scheme_map_truncatedResidue
#print axioms OrderThreeArc.scheme_sumTensor
#print axioms OrderThreeArc.scheme_valid
#print axioms SemanticArcFixture.base_valid
#print axioms SemanticArcFixture.truncated_valid
#print axioms SemanticArcFixture.represented
#print axioms SemanticArcFixture.first_coefficient_ne_zero
#print axioms TwoStepCoefficientOracle.values
#print axioms TwoStepCoefficientOracle.nonzero
#print axioms OrderThreeArc.first_eq
#print axioms OrderThreeArc.second_eq
#print axioms OrderThreeArc.third_eq
#print axioms OrderThreeArc.genuine_first_nonzero_mem_ker
#print axioms sumTensor_perturb
#print axioms sumTensor_perturbTwoStep
#print axioms VariationMask.no_correction_of_not_mem_range
#print axioms OrderThreeArc.first_nonzero_mem_ker
#print axioms obstructionClass_eq_zero_iff
#print axioms restrictedObstructionClass_eq_zero_iff
#print axioms OrderThreeArc.obstructionClass_first_eq_zero
#print axioms no_unrestricted_secondOrderLift_of_obstruction_ne_zero
#print axioms no_restricted_secondOrderLift_of_obstruction_ne_zero
#print axioms no_restricted_secondOrderLift_of_not_mem_range
#print axioms no_secondOrderLift_on_affine_family

end Deformation
end Scheme
end BilinearComplexity
