/-
  BilinearComplexity/LinearFlattening — linear matrix-valued tensor
  flattenings, rank bounds, and minor certificates.
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import BilinearComplexity.Basic

set_option autoImplicit false

namespace BilinearComplexity

section MatrixRank

variable {k rows cols ι : Type*} [Field k] [Fintype rows] [Fintype cols]

/-- Natural-valued matrix rank is subadditive over a field. -/
theorem matrix_rank_add_le (A B : Matrix rows cols k) :
    (A + B).rank ≤ A.rank + B.rank := by
  rw [Matrix.rank, Matrix.rank, Matrix.rank, Matrix.mulVecLin_add]
  have hrange : LinearMap.range (A.mulVecLin + B.mulVecLin) ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rintro _ ⟨x, rfl⟩
    exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩
  calc
    Module.finrank k (LinearMap.range (A.mulVecLin + B.mulVecLin)) ≤
        Module.finrank k ↥(LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin) :=
      Submodule.finrank_mono hrange
    _ ≤ Module.finrank k (LinearMap.range A.mulVecLin) +
        Module.finrank k (LinearMap.range B.mulVecLin) := by
      have hdim := Submodule.finrank_sup_add_finrank_inf_eq
        (LinearMap.range A.mulVecLin) (LinearMap.range B.mulVecLin)
      omega

/-- Matrix rank of a finite sum is at most the sum of the matrix ranks. -/
theorem matrix_rank_sum_le (s : Finset ι) (A : ι → Matrix rows cols k) :
    (∑ i ∈ s, A i).rank ≤ ∑ i ∈ s, (A i).rank := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (matrix_rank_add_le (A i) (∑ j ∈ s, A j)).trans
        (Nat.add_le_add_left ih _)

#check @matrix_rank_add_le
#check @matrix_rank_sum_le

end MatrixRank

section LinearBound

variable {k : Type*} [Field k] {a b c r q : ℕ}
variable {rows cols : Type*} [Fintype rows] [Fintype cols]

/-- A linear matrix-valued flattening whose simple tensors have rank at most
`q` sends every tensor with an `r`-term triad decomposition to a matrix of
rank at most `r * q`. -/
theorem rank_linearMap_le_mul_of_rankLE
    (F : Tensor k a b c →ₗ[k] Matrix rows cols k)
    (hsimple : ∀ (u : Fin a → k) (v : Fin b → k) (w : Fin c → k),
      (F (fun i j l => u i * v j * w l)).rank ≤ q)
    {T : Tensor k a b c} (hT : RankLE T r) :
    (F T).rank ≤ r * q := by
  classical
  obtain ⟨u, v, w, hdecomp⟩ := hT
  rw [hdecomp]
  have hsum : (fun i j l => ∑ s, u s i * v s j * w s l) =
      ∑ s : Fin r, fun i j l => u s i * v s j * w s l := by
    funext i j l
    simp
  rw [hsum, map_sum]
  calc
    (∑ s : Fin r, F (fun i j l => u s i * v s j * w s l)).rank ≤
        ∑ s : Fin r, (F (fun i j l => u s i * v s j * w s l)).rank :=
      matrix_rank_sum_le Finset.univ _
    _ ≤ ∑ _s : Fin r, q := Finset.sum_le_sum fun s _ => hsimple (u s) (v s) (w s)
    _ = r * q := by simp

/-- A nonzero square minor of size `m`, selected by arbitrary row and column
maps, certifies that the ambient matrix has rank at least `m`; injectivity of
the selecting maps is not an assumption because nonzero determinant forces it
when needed. -/
theorem le_rank_of_submatrix_det_ne_zero {m : ℕ} (M : Matrix rows cols k)
    (ri : Fin m → rows) (ci : Fin m → cols)
    (hdet : (M.submatrix ri ci).det ≠ 0) : m ≤ M.rank := by
  classical
  have hunitDet : IsUnit (M.submatrix ri ci).det := (isUnit_iff_ne_zero).mpr hdet
  have hunit : IsUnit (M.submatrix ri ci) :=
    (Matrix.isUnit_iff_isUnit_det (A := M.submatrix ri ci)).mpr hunitDet
  calc
    m = Fintype.card (Fin m) := (Fintype.card_fin m).symm
    _ = (M.submatrix ri ci).rank := (Matrix.rank_of_isUnit _ hunit).symm
    _ ≤ M.rank := Matrix.rank_submatrix_le M ri ci

/-- A nonzero `m × m` minor of a linear flattening, together with an
`r`-term tensor decomposition and a simple-image bound `q`, yields the
numerical certificate `m ≤ r * q`. -/
theorem le_mul_of_submatrix_det_ne_zero_of_rankLE
    (F : Tensor k a b c →ₗ[k] Matrix rows cols k)
    (hsimple : ∀ (u : Fin a → k) (v : Fin b → k) (w : Fin c → k),
      (F (fun i j l => u i * v j * w l)).rank ≤ q)
    {m : ℕ} (ri : Fin m → rows) (ci : Fin m → cols) {T : Tensor k a b c}
    (hdet : ((F T).submatrix ri ci).det ≠ 0) (hT : RankLE T r) :
    m ≤ r * q :=
  (le_rank_of_submatrix_det_ne_zero (F T) ri ci hdet).trans
    (rank_linearMap_le_mul_of_rankLE F hsimple hT)

/-- Threshold form of the minor certificate: if `r * q < m`, the tensor
cannot have an `r`-term triad decomposition. -/
theorem not_rankLE_of_mul_lt_of_submatrix_det_ne_zero
    (F : Tensor k a b c →ₗ[k] Matrix rows cols k)
    (hsimple : ∀ (u : Fin a → k) (v : Fin b → k) (w : Fin c → k),
      (F (fun i j l => u i * v j * w l)).rank ≤ q)
    {m : ℕ} (ri : Fin m → rows) (ci : Fin m → cols) {T : Tensor k a b c}
    (hdet : ((F T).submatrix ri ci).det ≠ 0) (hrm : r * q < m) :
    ¬ RankLE T r := by
  intro hT
  exact (Nat.not_le_of_lt hrm)
    (le_mul_of_submatrix_det_ne_zero_of_rankLE F hsimple ri ci hdet hT)

#check @rank_linearMap_le_mul_of_rankLE
#check @le_rank_of_submatrix_det_ne_zero
#check @le_mul_of_submatrix_det_ne_zero_of_rankLE
#check @not_rankLE_of_mul_lt_of_submatrix_det_ne_zero

end LinearBound

section EdgeAudits

/-- The generic linear-flattening bound explicitly includes the `r = 0`
edge case (and therefore forces the image rank to be zero). -/
example {k : Type*} [Field k] {a b c : ℕ} {rows cols : Type*}
    [Fintype rows] [Fintype cols]
    (F : Tensor k a b c →ₗ[k] Matrix rows cols k)
    (hsimple : ∀ (u : Fin a → k) (v : Fin b → k) (w : Fin c → k),
      (F (fun i j l => u i * v j * w l)).rank ≤ 3)
    {T : Tensor k a b c} (hT : RankLE T 0) : (F T).rank = 0 := by
  exact Nat.le_zero.mp (rank_linearMap_le_mul_of_rankLE F hsimple hT)

/-- The generic bound includes `q = 0`, even for positive decomposition
length; every admitted image then has rank zero. -/
example {k : Type*} [Field k] {a b c : ℕ} {rows cols : Type*}
    [Fintype rows] [Fintype cols]
    (F : Tensor k a b c →ₗ[k] Matrix rows cols k)
    (hsimple : ∀ (u : Fin a → k) (v : Fin b → k) (w : Fin c → k),
      (F (fun i j l => u i * v j * w l)).rank ≤ 0)
    {T : Tensor k a b c} (hT : RankLE T 5) : (F T).rank = 0 := by
  exact Nat.le_zero.mp (rank_linearMap_le_mul_of_rankLE F hsimple hT)

/-- Empty matrix dimensions are covered: every image into a matrix with no
rows has rank zero. -/
example {k : Type*} [Field k] {a b c : ℕ}
    (F : Tensor k a b c →ₗ[k] Matrix (Fin 0) (Fin 4) k) (T : Tensor k a b c) :
    (F T).rank = 0 := by
  exact Nat.le_zero.mp ((Matrix.rank_le_card_height (F T)).trans_eq (Fintype.card_fin 0))

/-- An empty minor cannot satisfy the strict threshold premise: its size is
zero, while every natural product `r * q` is nonnegative. -/
example (r q : ℕ) : ¬ r * q < 0 := Nat.not_lt_zero _

end EdgeAudits

#print axioms matrix_rank_add_le
#print axioms matrix_rank_sum_le
#print axioms rank_linearMap_le_mul_of_rankLE
#print axioms le_rank_of_submatrix_det_ne_zero
#print axioms le_mul_of_submatrix_det_ne_zero_of_rankLE
#print axioms not_rankLE_of_mul_lt_of_submatrix_det_ne_zero

end BilinearComplexity
