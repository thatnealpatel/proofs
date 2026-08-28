import BilinearComplexity.SharedFactorReduction

set_option autoImplicit false

open scoped BigOperators

namespace BilinearComplexity

variable {k : Type*} [Field k]
variable {a b c r : ℕ}

/-- Multiplication of a matrix by a nonzero field scalar does not change its rank. -/
theorem matrix_rank_smul_of_ne_zero (A : Matrix (Fin b) (Fin c) k)
    {beta : k} (hbeta : beta ≠ 0) : (beta • A).rank = A.rank := by
  unfold Matrix.rank
  have hlin : (beta • A).mulVecLin = beta • A.mulVecLin := by
    apply LinearMap.ext
    intro x
    exact Matrix.smul_mulVec beta A x
  rw [hlin, LinearMap.range_smul A.mulVecLin beta hbeta]

/-- A nonzero common first factor contracts any tensor-rank upper bound to a matrix-rank bound. -/
theorem matrix_rank_le_of_rankLE_common_first_factor
    (u : Fin a → k) (hu : u ≠ 0) (A : Matrix (Fin b) (Fin c) k) {q : ℕ}
    (hT : RankLE (fun i j l => u i * A j l) q) : A.rank ≤ q := by
  obtain ⟨i0, hi0⟩ : ∃ i0, u i0 ≠ 0 := by
    by_contra hnone
    simp only [not_exists, not_not] at hnone
    exact hu (funext hnone)
  obtain ⟨x, y, z, hxyz⟩ := hT
  let B : Fin q → Matrix (Fin b) (Fin c) k := fun s =>
    Matrix.vecMulVec (((u i0)⁻¹ * x s i0) • y s) (z s)
  have hA : A = ∑ s, B s := by
    ext j l
    have hat := congrFun (congrFun (congrFun hxyz i0) j) l
    simp only [B, Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul] at hat ⊢
    calc
      A j l = (u i0)⁻¹ * (u i0 * A j l) := by field_simp
      _ = (u i0)⁻¹ * (∑ s, x s i0 * y s j * z s l) := congrArg ((u i0)⁻¹ * ·) hat
      _ = ∑ s, (u i0)⁻¹ * x s i0 * y s j * z s l := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s hs
        ring
  rw [hA]
  have hB : ∀ s, (B s).rank ≤ 1 := by
    intro s
    exact matrix_rank_vecMulVec_le_one
      (fun t => ((u i0)⁻¹ * x t i0) • y t) z s
  simpa only [Finset.card_univ, Fintype.card_fin] using
    matrix_rank_sum_le_card B hB Finset.univ

namespace Scheme
namespace Replacement

/--
A nonempty full first-mode projective fiber, with nonzero weights relative to a
nonzero representative. Membership is exactly proportionality to the representative
by a nonzero field scalar.
-/
structure ProjectiveFirstFactorFiber (S : Scheme k a b c r) where
  representative : Fin a → k
  representative_ne_zero : representative ≠ 0
  slots : Finset (Fin r)
  anchor : Fin r
  anchor_mem : anchor ∈ slots
  weight : Fin r → k
  weight_ne_zero : ∀ s ∈ slots, weight s ≠ 0
  first_eq : ∀ s ∈ slots, (S.term s).1 = weight s • representative
  mem_iff : ∀ s, s ∈ slots ↔
    ∃ alpha : k, alpha ≠ 0 ∧ (S.term s).1 = alpha • representative

namespace ProjectiveFirstFactorFiber

variable {S : Scheme k a b c r}

/-- The fiber is occupied by its anchor. -/
theorem slots_nonempty (F : ProjectiveFirstFactorFiber S) : F.slots.Nonempty :=
  ⟨F.anchor, F.anchor_mem⟩

/-- The weighted complementary matrix at one scheme slot has rank at most one. -/
def weightedTerm (F : ProjectiveFirstFactorFiber S) (s : Fin r) :
    Matrix (Fin b) (Fin c) k :=
  F.weight s • Matrix.vecMulVec (S.term s).2.1 (S.term s).2.2

/-- The weighted complementary matrix over the full projective first-factor fiber. -/
def complementaryMatrix (F : ProjectiveFirstFactorFiber S) :
    Matrix (Fin b) (Fin c) k :=
  ∑ s ∈ F.slots, F.weightedTerm s

/-- The tensor sum of the original terms in the full projective fiber. -/
def localTensor (F : ProjectiveFirstFactorFiber S) : Tensor k a b c :=
  fun i j l => ∑ s ∈ F.slots,
    (S.term s).1 i * (S.term s).2.1 j * (S.term s).2.2 l

/-- The inverse-adjusted fiber weights associated with a scalar `beta`.
For representative rescaling, `beta` must be nonzero. -/
def rescaledWeight (F : ProjectiveFirstFactorFiber S) (beta : k) (s : Fin r) : k :=
  beta⁻¹ * F.weight s

/-- The weighted matrix family associated with the inverse-adjusted weights. -/
def rescaledWeightedTerm (F : ProjectiveFirstFactorFiber S) (beta : k) (s : Fin r) :
    Matrix (Fin b) (Fin c) k :=
  F.rescaledWeight beta s • Matrix.vecMulVec (S.term s).2.1 (S.term s).2.2

/-- Every weighted complementary term has matrix rank at most one. -/
theorem weightedTerm_rank_le_one (F : ProjectiveFirstFactorFiber S) (s : Fin r) :
    (F.weightedTerm s).rank ≤ 1 := by
  rw [weightedTerm, ← Matrix.smul_vecMulVec]
  exact matrix_rank_vecMulVec_le_one
    (fun t => F.weight t • (S.term t).2.1) (fun t => (S.term t).2.2) s

/-- The sum with rescaled weights is the inverse scalar multiple of the original sum. -/
theorem sum_rescaledWeightedTerm (F : ProjectiveFirstFactorFiber S) (beta : k) :
    (∑ s ∈ F.slots, F.rescaledWeightedTerm beta s) =
      beta⁻¹ • F.complementaryMatrix := by
  simp only [rescaledWeightedTerm, rescaledWeight, complementaryMatrix]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  unfold weightedTerm
  simp only [smul_smul]

/-- Complementary-matrix rank is preserved by the explicit nonzero representative rescaling. -/
theorem rank_sum_rescaledWeightedTerm (F : ProjectiveFirstFactorFiber S)
    {beta : k} (hbeta : beta ≠ 0) :
    (∑ s ∈ F.slots, F.rescaledWeightedTerm beta s).rank =
      F.complementaryMatrix.rank := by
  rw [F.sum_rescaledWeightedTerm beta]
  exact matrix_rank_smul_of_ne_zero F.complementaryMatrix (inv_ne_zero hbeta)

/-- Guarded natural matrix defect is preserved by the explicit nonzero representative rescaling. -/
theorem defect_rescaledWeightedTerm (F : ProjectiveFirstFactorFiber S)
    {beta : k} (hbeta : beta ≠ 0) :
    matrixRankDefectNat (F.rescaledWeightedTerm beta) F.slots =
      matrixRankDefectNat F.weightedTerm F.slots := by
  unfold matrixRankDefectNat
  rw [F.rank_sum_rescaledWeightedTerm hbeta]
  rfl

/-- Positive defect on a subset forces positive defect on its full projective fiber. -/
theorem defect_pos_of_subset (F : ProjectiveFirstFactorFiber S)
    {I : Finset (Fin r)} (hI : I ⊆ F.slots)
    (hpos : 0 < matrixRankDefectNat F.weightedTerm I) :
    0 < matrixRankDefectNat F.weightedTerm F.slots := by
  exact matrixRankDefectNat_pos_of_subset
    F.weightedTerm F.weightedTerm_rank_le_one hI hpos

/-- Rescaled weights reproduce every first factor using the rescaled representative. -/
theorem first_eq_rescaled (F : ProjectiveFirstFactorFiber S)
    {beta : k} (hbeta : beta ≠ 0) {s : Fin r} (hs : s ∈ F.slots) :
    (S.term s).1 = F.rescaledWeight beta s • (beta • F.representative) := by
  rw [F.first_eq s hs]
  ext i
  simp only [rescaledWeight, Pi.smul_apply, smul_eq_mul]
  field_simp

/-- Nonzero rescaling constructs the same full projective fiber with adjusted weights. -/
def rescale (F : ProjectiveFirstFactorFiber S) (beta : k) (hbeta : beta ≠ 0) :
    ProjectiveFirstFactorFiber S where
  representative := beta • F.representative
  representative_ne_zero := smul_ne_zero hbeta F.representative_ne_zero
  slots := F.slots
  anchor := F.anchor
  anchor_mem := F.anchor_mem
  weight := F.rescaledWeight beta
  weight_ne_zero := by
    intro s hs
    exact mul_ne_zero (inv_ne_zero hbeta) (F.weight_ne_zero s hs)
  first_eq := by
    intro s hs
    exact F.first_eq_rescaled hbeta hs
  mem_iff := by
    intro s
    constructor
    · intro hs
      refine ⟨F.rescaledWeight beta s,
        mul_ne_zero (inv_ne_zero hbeta) (F.weight_ne_zero s hs), ?_⟩
      exact F.first_eq_rescaled hbeta hs
    · rintro ⟨alpha, halpha, heq⟩
      apply (F.mem_iff s).2
      refine ⟨alpha * beta, mul_ne_zero halpha hbeta, ?_⟩
      rw [heq]
      simp only [smul_smul]

/-- The actual fiber-rescaling constructor preserves complementary-matrix rank. -/
theorem rescale_complementaryMatrix_rank (F : ProjectiveFirstFactorFiber S)
    {beta : k} (hbeta : beta ≠ 0) :
    (F.rescale beta hbeta).complementaryMatrix.rank = F.complementaryMatrix.rank := by
  simpa only [complementaryMatrix, rescale, weightedTerm, rescaledWeightedTerm] using
    F.rank_sum_rescaledWeightedTerm hbeta

/-- The actual fiber-rescaling constructor preserves full-fiber defect. -/
theorem rescale_defect (F : ProjectiveFirstFactorFiber S)
    {beta : k} (hbeta : beta ≠ 0) :
    matrixRankDefectNat (F.rescale beta hbeta).weightedTerm (F.rescale beta hbeta).slots =
      matrixRankDefectNat F.weightedTerm F.slots := by
  have hslots : (F.rescale beta hbeta).slots = F.slots := rfl
  have hterm : (F.rescale beta hbeta).weightedTerm = F.rescaledWeightedTerm beta := by
    funext s
    rfl
  rw [hslots, hterm]
  exact F.defect_rescaledWeightedTerm hbeta

/-- The local fiber tensor is its representative times its weighted complementary matrix. -/
theorem localTensor_apply (F : ProjectiveFirstFactorFiber S)
    (i : Fin a) (j : Fin b) (l : Fin c) :
    F.localTensor i j l = F.representative i * F.complementaryMatrix j l := by
  simp only [localTensor, complementaryMatrix, weightedTerm, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hfirst := congrFun (F.first_eq s hs) i
  simp only [Pi.smul_apply, smul_eq_mul] at hfirst
  rw [hfirst]
  ring

/-- The local fiber tensor has a decomposition of complementary-matrix rank. -/
theorem localTensor_rankLE_rank (F : ProjectiveFirstFactorFiber S) :
    RankLE F.localTensor F.complementaryMatrix.rank := by
  have hcommon := rankLE_common_first_factor_matrix F.representative F.complementaryMatrix
  suffices F.localTensor =
      (fun i j l => F.representative i * F.complementaryMatrix j l) by
    rw [this]
    exact hcommon
  funext i j l
  exact F.localTensor_apply i j l

/--
Positive full-fiber defect is equivalent to the existence of a strictly shorter
arbitrary tensor decomposition of the selected local tensor.
-/
theorem defect_pos_iff_exists_shorter_rankLE (F : ProjectiveFirstFactorFiber S) :
    0 < matrixRankDefectNat F.weightedTerm F.slots ↔
      ∃ q < F.slots.card, RankLE F.localTensor q := by
  constructor
  · intro hpos
    refine ⟨F.complementaryMatrix.rank, ?_, F.localTensor_rankLE_rank⟩
    change 0 < F.slots.card - F.complementaryMatrix.rank at hpos
    omega
  · rintro ⟨q, hq, hlocal⟩
    have hcommon :
        RankLE (fun i j l => F.representative i * F.complementaryMatrix j l) q := by
      suffices (fun i j l => F.representative i * F.complementaryMatrix j l) =
          F.localTensor by
        rw [this]
        exact hlocal
      funext i j l
      exact (F.localTensor_apply i j l).symm
    have hrankq : F.complementaryMatrix.rank ≤ q :=
      matrix_rank_le_of_rankLE_common_first_factor F.representative
        F.representative_ne_zero F.complementaryMatrix hcommon
    change 0 < F.slots.card - F.complementaryMatrix.rank
    omega

private def projectiveFiberFixtureScheme : Scheme ℚ 1 1 1 2 where
  term s :=
    (fun _ => (s.val + 1 : ℚ), fun _ => 1, fun _ => 1)

private def projectiveFiberFixture : ProjectiveFirstFactorFiber projectiveFiberFixtureScheme where
  representative := fun _ => 1
  representative_ne_zero := by
    intro hzero
    have hvalue := congrFun hzero (0 : Fin 1)
    norm_num at hvalue
  slots := Finset.univ
  anchor := 0
  anchor_mem := Finset.mem_univ 0
  weight s := s.val + 1
  weight_ne_zero := by
    intro s hs
    positivity
  first_eq := by
    intro s hs
    funext i
    simp only [projectiveFiberFixtureScheme, Pi.smul_apply, smul_eq_mul]
    ring
  mem_iff := by
    intro s
    constructor
    · intro hs
      refine ⟨s.val + 1, by positivity, ?_⟩
      funext i
      simp only [projectiveFiberFixtureScheme, Pi.smul_apply, smul_eq_mul]
      ring
    · intro hs
      exact Finset.mem_univ s

example : projectiveFiberFixture.slots.card = 2 := by decide

example : projectiveFiberFixture.slots.Nonempty := projectiveFiberFixture.slots_nonempty

example : projectiveFiberFixture.weight (0 : Fin 2) = 1 := by
  norm_num [projectiveFiberFixture]

example : projectiveFiberFixture.weightedTerm (0 : Fin 2) (0 : Fin 1) (0 : Fin 1) = 1 := by
  norm_num [weightedTerm, projectiveFiberFixture, projectiveFiberFixtureScheme,
    Matrix.vecMulVec_apply]

example : projectiveFiberFixture.complementaryMatrix (0 : Fin 1) (0 : Fin 1) = 3 := by
  norm_num [complementaryMatrix, weightedTerm, projectiveFiberFixture,
    projectiveFiberFixtureScheme, Matrix.vecMulVec_apply, Fin.sum_univ_two]

example : projectiveFiberFixture.localTensor (0 : Fin 1) (0 : Fin 1) (0 : Fin 1) = 3 := by
  norm_num [localTensor, projectiveFiberFixture, projectiveFiberFixtureScheme, Fin.sum_univ_two]

example : projectiveFiberFixture.rescaledWeight 2 (0 : Fin 2) = (1 / 2 : ℚ) := by
  norm_num [rescaledWeight, projectiveFiberFixture]

example : projectiveFiberFixture.rescaledWeightedTerm 2 (0 : Fin 2)
    (0 : Fin 1) (0 : Fin 1) = (1 / 2 : ℚ) := by
  norm_num [rescaledWeightedTerm, rescaledWeight, projectiveFiberFixture,
    projectiveFiberFixtureScheme, Matrix.vecMulVec_apply]

example : (projectiveFiberFixture.rescale 2 (by norm_num)).representative (0 : Fin 1) = 2 := by
  norm_num [rescale, projectiveFiberFixture]

example :
    (projectiveFiberFixtureScheme.term (0 : Fin 2)).1 ≠
      (projectiveFiberFixtureScheme.term (1 : Fin 2)).1 := by
  intro heq
  have hvalue := congrFun heq (0 : Fin 1)
  norm_num [projectiveFiberFixtureScheme] at hvalue

end ProjectiveFirstFactorFiber
end Scheme.Replacement
end BilinearComplexity

#check @BilinearComplexity.matrix_rank_smul_of_ne_zero
#check @BilinearComplexity.matrix_rank_le_of_rankLE_common_first_factor
#check @BilinearComplexity.Scheme.Replacement.ProjectiveFirstFactorFiber.rescale_complementaryMatrix_rank
#check @BilinearComplexity.Scheme.Replacement.ProjectiveFirstFactorFiber.rescale_defect
#check @BilinearComplexity.Scheme.Replacement.ProjectiveFirstFactorFiber.localTensor_apply
#check @BilinearComplexity.Scheme.Replacement.ProjectiveFirstFactorFiber.defect_pos_of_subset
#check @BilinearComplexity.Scheme.Replacement.ProjectiveFirstFactorFiber.defect_pos_iff_exists_shorter_rankLE
#print axioms BilinearComplexity.matrix_rank_smul_of_ne_zero
#print axioms BilinearComplexity.matrix_rank_le_of_rankLE_common_first_factor
#print axioms BilinearComplexity.Scheme.Replacement.ProjectiveFirstFactorFiber.rescale_complementaryMatrix_rank
#print axioms BilinearComplexity.Scheme.Replacement.ProjectiveFirstFactorFiber.rescale_defect
#print axioms BilinearComplexity.Scheme.Replacement.ProjectiveFirstFactorFiber.localTensor_apply
#print axioms BilinearComplexity.Scheme.Replacement.ProjectiveFirstFactorFiber.localTensor_rankLE_rank
#print axioms BilinearComplexity.Scheme.Replacement.ProjectiveFirstFactorFiber.defect_pos_of_subset
#print axioms BilinearComplexity.Scheme.Replacement.ProjectiveFirstFactorFiber.defect_pos_iff_exists_shorter_rankLE
