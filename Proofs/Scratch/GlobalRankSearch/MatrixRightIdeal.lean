/-
  Scratch/GlobalRankSearch/MatrixRightIdeal — the dimension of a principal
  left ideal of a full matrix algebra.

  The range `{X * b | X ∈ Mₙ(k)}` is the principal left ideal `Mₙ(k)b`:
  multiplication by an arbitrary matrix occurs on the left of its fixed
  generator `b`.  Its rows are independent choices from the row space of
  `b`.  In Mathlib's column-oriented `mulVec` convention, that row space is
  `range (transpose b).mulVecLin`.
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Rank

set_option autoImplicit false

namespace BilinearComplexity

open scoped Matrix

/-- Right multiplication by `b`, whose range is the principal left ideal
`Mₙ(k)b`. -/
def matrixRightMul {k : Type*} [Semiring k] {n : ℕ}
    (b : Matrix (Fin n) (Fin n) k) :
    Matrix (Fin n) (Fin n) k →ₗ[k] Matrix (Fin n) (Fin n) k :=
  { toFun := fun X => X * b
    map_add' := fun X Y => Matrix.add_mul X Y b
    map_smul' := fun c X => Matrix.smul_mul c X b }

/-- Evaluation of right multiplication is matrix multiplication on the right. -/
@[simp]
theorem matrixRightMul_apply {k : Type*} [Semiring k] {n : ℕ}
    (b X : Matrix (Fin n) (Fin n) k) : matrixRightMul b X = X * b := rfl

/-- Ground check: right multiplication uses rows of the left input and columns
of the fixed right input. -/
example : matrixRightMul !![(1 : ℚ), 2; 3, 4] !![0, 1; 1, 0] = !![3, 4; 1, 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrixRightMul, Matrix.mul_apply, Fin.sum_univ_two]

/-- The principal left ideal `Mₙ(k)b` is linearly equivalent to `n` independent
copies of the row space of `b`, represented in Mathlib's column convention as
the range of `(transpose b).mulVecLin`. -/
noncomputable def rangeMatrixRightMulEquivRows {k : Type*} [CommSemiring k] {n : ℕ}
    (b : Matrix (Fin n) (Fin n) k) :
    LinearMap.range (matrixRightMul b) ≃ₗ[k]
      (Fin n → LinearMap.range (Matrix.transpose b).mulVecLin) := by
  classical
  let Rb := LinearMap.range (matrixRightMul b)
  let Row := LinearMap.range (Matrix.transpose b).mulVecLin
  let e : Rb ≃ₗ[k] (Fin n → Row) :=
    { toFun := fun Y i =>
        ⟨fun j => Y.1 i j, by
          obtain ⟨X, hX⟩ := Y.2
          refine ⟨X i, ?_⟩
          funext j
          have hentry := congrFun (congrFun hX i) j
          simpa only [matrixRightMul_apply, Matrix.mul_apply, Matrix.mulVecLin_apply,
            Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm] using hentry⟩
      map_add' := by
        intro X Y
        ext i j
        rfl
      map_smul' := by
        intro c X
        ext i j
        rfl
      invFun := fun f =>
        ⟨fun i j => (f i).1 j, by
          choose X hX using fun i => (f i).2
          refine ⟨fun i j => X i j, ?_⟩
          ext i j
          have hentry := congrFun (hX i) j
          change (∑ q, X i q * b q j) = (f i).1 j
          calc
            (∑ q, X i q * b q j) = ∑ q, b q j * X i q := by
              apply Finset.sum_congr rfl
              intro q _
              exact mul_comm _ _
            _ = (f i).1 j := by
              simpa only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
                Matrix.transpose_apply] using hentry⟩
      left_inv := by
        intro Y
        ext i j
        rfl
      right_inv := by
        intro f
        ext i j
        rfl }
  exact e

/-- Ground check for the row-space equivalence: the unique row of a `1 × 1`
right multiple is sent to that same scalar row. -/
example :
    let Y : LinearMap.range (matrixRightMul !![(2 : ℚ)]) :=
      ⟨!![(6 : ℚ)], ⟨!![(3 : ℚ)], by
        ext i j
        fin_cases i
        fin_cases j
        norm_num [matrixRightMul, Matrix.mul_apply]⟩⟩
    (((rangeMatrixRightMulEquivRows !![(2 : ℚ)]) Y) 0).1 0 = 6 := by
  rfl

/-- Over every field, including finite fields and in every size (also `n = 0`),
the principal left ideal `Mₙ(k)b` has dimension `n * rank(b)`.  Equivalently,
the linear map `X ↦ X * b` has range of that exact dimension. -/
theorem finrank_range_matrixRightMul {k : Type*} [Field k] {n : ℕ}
    (b : Matrix (Fin n) (Fin n) k) :
    Module.finrank k (LinearMap.range (matrixRightMul b)) = n * b.rank := by
  classical
  let Row := LinearMap.range (Matrix.transpose b).mulVecLin
  calc
    Module.finrank k (LinearMap.range (matrixRightMul b)) =
        Module.finrank k (Fin n → Row) :=
      (rangeMatrixRightMulEquivRows b).finrank_eq
    _ = ∑ _ : Fin n, Module.finrank k Row := Module.finrank_pi_fintype k
    _ = n * Module.finrank k Row := by simp
    _ = n * (Matrix.transpose b).rank := by rw [Matrix.rank]
    _ = n * b.rank := by rw [Matrix.rank_transpose]

/-- The exact formula includes the zero-size and zero-matrix boundary cases. -/
example : Module.finrank ℚ
    (LinearMap.range (matrixRightMul (0 : Matrix (Fin 0) (Fin 0) ℚ))) = 0 := by
  rw [finrank_range_matrixRightMul]
  simp

/-- For the identity in `M₃(ℚ)`, the principal left ideal is the whole
nine-dimensional matrix algebra. -/
example : Module.finrank ℚ
    (LinearMap.range (matrixRightMul (1 : Matrix (Fin 3) (Fin 3) ℚ))) = 9 := by
  rw [finrank_range_matrixRightMul, Matrix.rank_one]
  norm_num

/-- A noninvertible three-by-three matrix has rank at most two over every field. -/
theorem rank_le_two_of_not_isUnit_fin3 {k : Type*} [Field k]
    (b : Matrix (Fin 3) (Fin 3) k) (hb : ¬ IsUnit b) : b.rank ≤ 2 := by
  classical
  have hrank : b.rank ≤ 3 := by simpa using Matrix.rank_le_width b
  by_contra hnot
  have hfull : b.rank = 3 := by omega
  apply hb
  rw [← Matrix.mulVec_surjective_iff_isUnit]
  change Function.Surjective b.mulVecLin
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  rw [← Matrix.rank, hfull]
  simp

/-- The principal left ideal generated by a noninvertible matrix in `M₃(k)`
has dimension at most six, uniformly over all fields. -/
theorem finrank_range_matrixRightMul_le_six_of_not_isUnit {k : Type*} [Field k]
    (b : Matrix (Fin 3) (Fin 3) k) (hb : ¬ IsUnit b) :
    Module.finrank k (LinearMap.range (matrixRightMul b)) ≤ 6 := by
  rw [finrank_range_matrixRightMul]
  have hrank := rank_le_two_of_not_isUnit_fin3 b hb
  omega

/-- If the noninvertible generator in `M₃(k)` is nonzero, its principal left
ideal has dimension exactly three or exactly six. -/
theorem finrank_range_matrixRightMul_eq_three_or_six_of_ne_zero_of_not_isUnit
    {k : Type*} [Field k] (b : Matrix (Fin 3) (Fin 3) k)
    (hb0 : b ≠ 0) (hbunit : ¬ IsUnit b) :
    Module.finrank k (LinearMap.range (matrixRightMul b)) = 3 ∨
      Module.finrank k (LinearMap.range (matrixRightMul b)) = 6 := by
  classical
  have hrank0 : b.rank ≠ 0 := by
    intro hzero
    have hrange : LinearMap.range b.mulVecLin = ⊥ := by
      apply Submodule.finrank_eq_zero.mp
      simpa only [Matrix.rank] using hzero
    have hmap : b.mulVecLin = 0 := LinearMap.range_eq_bot.mp hrange
    apply hb0
    ext i j
    have hcol := LinearMap.congr_fun hmap (Pi.single j 1)
    change b.mulVec (Pi.single j 1) = 0 at hcol
    rw [Matrix.mulVec_single_one] at hcol
    exact congrFun hcol i
  have hrank_le : b.rank ≤ 2 := rank_le_two_of_not_isUnit_fin3 b hbunit
  have hrank_cases : b.rank = 1 ∨ b.rank = 2 := by omega
  rw [finrank_range_matrixRightMul]
  rcases hrank_cases with hrank | hrank
  · left
    omega
  · right
    omega

/-- Jointly satisfiable sharp example: the rational diagonal matrix
`diag(1,1,0)` is noninvertible and generates a six-dimensional left ideal. -/
example :
    let b : Matrix (Fin 3) (Fin 3) ℚ := !![1, 0, 0; 0, 1, 0; 0, 0, 0]
    b ≠ 0 ∧ ¬ IsUnit b ∧
      Module.finrank ℚ (LinearMap.range (matrixRightMul b)) = 6 := by
  dsimp
  let b : Matrix (Fin 3) (Fin 3) ℚ := !![1, 0, 0; 0, 1, 0; 0, 0, 0]
  have hbdiag : b = Matrix.diagonal ![(1 : ℚ), 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hrank : b.rank = 2 := by
    rw [hbdiag, Matrix.rank_diagonal]
    change Fintype.card {i : Fin 3 // ![(1 : ℚ), 1, 0] i ≠ 0} = 2
    decide
  have hnot : ¬ IsUnit b := by
    intro hunit
    have hfull := Matrix.rank_of_isUnit b hunit
    rw [hrank] at hfull
    norm_num at hfull
  have hb0 : b ≠ 0 := by
    intro hzero
    have hentry := congrFun (congrFun hzero 0) 0
    norm_num [b] at hentry
  refine ⟨hb0, hnot, ?_⟩
  rw [finrank_range_matrixRightMul, hrank]

#check @matrixRightMul
#check @matrixRightMul_apply
#check @rangeMatrixRightMulEquivRows
#check @finrank_range_matrixRightMul
#check @rank_le_two_of_not_isUnit_fin3
#check @finrank_range_matrixRightMul_le_six_of_not_isUnit
#check @finrank_range_matrixRightMul_eq_three_or_six_of_ne_zero_of_not_isUnit

#print axioms matrixRightMul_apply
#print axioms rangeMatrixRightMulEquivRows
#print axioms finrank_range_matrixRightMul
#print axioms rank_le_two_of_not_isUnit_fin3
#print axioms finrank_range_matrixRightMul_le_six_of_not_isUnit
#print axioms finrank_range_matrixRightMul_eq_three_or_six_of_ne_zero_of_not_isUnit

end BilinearComplexity
