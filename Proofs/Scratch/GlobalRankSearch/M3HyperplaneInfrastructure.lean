/-
  Scratch/GlobalRankSearch/M3HyperplaneInfrastructure — dual-matrix orbit
  classification and first-mode hyperplane substitution for three-by-three
  matrix multiplication.

  This file proves reusable infrastructure and reduction ingredients only.
  The arbitrary-field rank-20 target remains open: in particular, no endpoint
  theorem assumes the currently incompatible package of three representative
  hyperplane lower bounds.
-/
import Scratch.GlobalRankSearch.M3Structural
import Mathlib.LinearAlgebra.Matrix.StdBasis

set_option autoImplicit false

namespace BilinearComplexity

open scoped Matrix

/-- The coefficient matrix of a linear functional on three-by-three matrices,
read on the standard matrix units. -/
def m3DualMatrix {k : Type*} [CommSemiring k]
    (φ : Matrix (Fin 3) (Fin 3) k →ₗ[k] k) : Matrix (Fin 3) (Fin 3) k :=
  fun i j => φ (squareMatrixUnit i j)

/-- `m3DualMatrix` recovers the row-major coefficients used by `m3Form`. -/
theorem m3DualMatrix_m3Form {k : Type*} [CommSemiring k] (u : Fin 9 → k) :
    m3DualMatrix (m3Form u) = fun i j => u (m3Equiv (i, j)) := by
  classical
  ext i j
  change (∑ x, u x * m3ToVec (squareMatrixUnit i j) x) =
    u (m3Equiv (i, j))
  rw [← Equiv.sum_comp m3Equiv]
  simp only [m3ToVec, Equiv.symm_apply_apply, squareMatrixUnit, mul_ite,
    mul_one, mul_zero]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro q _ hq
      simp [hq]
    · simp
  · intro p _ hp
    simp [hp]
  · simp

/-- A matrix functional has zero coefficient matrix exactly when it is the
zero functional. -/
theorem m3DualMatrix_eq_zero_iff {k : Type*} [CommSemiring k]
    (φ : Matrix (Fin 3) (Fin 3) k →ₗ[k] k) :
    m3DualMatrix φ = 0 ↔ φ = 0 := by
  classical
  constructor
  · intro hcoeff
    apply (Matrix.stdBasis k (Fin 3) (Fin 3)).ext
    rintro ⟨i, j⟩
    rw [Matrix.stdBasis_eq_single]
    have hunit : Matrix.single i j (1 : k) = squareMatrixUnit i j := by
      ext p q
      simp only [Matrix.single_apply, squareMatrixUnit]
      by_cases hcoordinates : i = p ∧ j = q
      · obtain ⟨rfl, rfl⟩ := hcoordinates
        simp
      · have hreverse : ¬ (p = i ∧ q = j) := by
          rintro ⟨hpi, hqj⟩
          exact hcoordinates ⟨hpi.symm, hqj.symm⟩
        simp [hcoordinates, hreverse]
    rw [hunit]
    have hij : φ (squareMatrixUnit i j) = 0 := by
      change m3DualMatrix φ i j = 0
      rw [hcoeff]
      rfl
    simpa only [LinearMap.zero_apply] using hij
  · rintro rfl
    ext i j
    simp [m3DualMatrix]

/-- The standard rank-one first-mode representative, with coefficient matrix
`E₁₁`. -/
def m3RankOneForm {k : Type*} [CommSemiring k] :
    Matrix (Fin 3) (Fin 3) k →ₗ[k] k :=
  m3Form ![1, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The standard rank-two first-mode representative, with coefficient matrix
`diag(1,1,0)`. -/
def m3RankTwoForm {k : Type*} [CommSemiring k] :
    Matrix (Fin 3) (Fin 3) k →ₗ[k] k :=
  m3Form ![1, 0, 0, 0, 1, 0, 0, 0, 0]

/-- The standard rank-three first-mode representative, with coefficient
matrix `I₃`. -/
def m3RankThreeForm {k : Type*} [CommSemiring k] :
    Matrix (Fin 3) (Fin 3) k →ₗ[k] k :=
  m3Form ![1, 0, 0, 0, 1, 0, 0, 0, 1]

/-- The coefficient matrix of `m3RankOneForm` is `E₁₁`. -/
theorem m3DualMatrix_m3RankOneForm {k : Type*} [CommSemiring k] :
    m3DualMatrix (m3RankOneForm (k := k)) = Matrix.diagonal ![1, 0, 0] := by
  rw [m3RankOneForm, m3DualMatrix_m3Form]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The coefficient matrix of `m3RankTwoForm` is `diag(1,1,0)`. -/
theorem m3DualMatrix_m3RankTwoForm {k : Type*} [CommSemiring k] :
    m3DualMatrix (m3RankTwoForm (k := k)) = Matrix.diagonal ![1, 1, 0] := by
  rw [m3RankTwoForm, m3DualMatrix_m3Form]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The coefficient matrix of `m3RankThreeForm` is `I₃`. -/
theorem m3DualMatrix_m3RankThreeForm {k : Type*} [CommSemiring k] :
    m3DualMatrix (m3RankThreeForm (k := k)) = Matrix.diagonal ![1, 1, 1] := by
  rw [m3RankThreeForm, m3DualMatrix_m3Form]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Precomposition of a matrix functional by the linear change of variables
`A ↦ P * A * Q`. -/
def m3LeftRightForm {k : Type*} [CommSemiring k]
    (φ : Matrix (Fin 3) (Fin 3) k →ₗ[k] k)
    (P Q : Matrix (Fin 3) (Fin 3) k) :
    Matrix (Fin 3) (Fin 3) k →ₗ[k] k :=
  φ.comp
    ({ toFun := fun A => P * A * Q
       map_add' := by
         intro A B
         simp only [Matrix.mul_add, Matrix.add_mul]
       map_smul' := by
         intro c A
         simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply] } :
      Matrix (Fin 3) (Fin 3) k →ₗ[k] Matrix (Fin 3) (Fin 3) k)

/-- Evaluation of `m3LeftRightForm` is precomposition by left-right matrix
multiplication. -/
theorem m3LeftRightForm_apply {k : Type*} [CommSemiring k]
    (φ : Matrix (Fin 3) (Fin 3) k →ₗ[k] k)
    (P Q A : Matrix (Fin 3) (Fin 3) k) :
    m3LeftRightForm φ P Q A = φ (P * A * Q) := rfl

/-- A functional is the sum of its standard-matrix-unit coefficients times
the corresponding input entries. -/
theorem apply_eq_sum_m3DualMatrix_mul {k : Type*} [CommSemiring k]
    (φ : Matrix (Fin 3) (Fin 3) k →ₗ[k] k)
    (A : Matrix (Fin 3) (Fin 3) k) :
    φ A = ∑ i, ∑ j, m3DualMatrix φ i j * A i j := by
  classical
  have hmatrix : A = ∑ i, ∑ j, A i j • squareMatrixUnit i j := by
    ext p q
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      squareMatrixUnit, mul_ite, mul_one, mul_zero]
    symm
    rw [Finset.sum_eq_single p]
    · rw [Finset.sum_eq_single q]
      · simp
      · intro j _ hj
        simp [Ne.symm hj]
      · simp
    · intro i _ hi
      apply Finset.sum_eq_zero
      intro j _
      simp [Ne.symm hi]
    · simp
  nth_rewrite 1 [hmatrix]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [map_smul, m3DualMatrix, smul_eq_mul, mul_comm]

/-- Left-right precomposition acts on coefficient matrices by transposed left
and right multiplication. -/
theorem m3DualMatrix_m3LeftRightForm {k : Type*} [CommSemiring k]
    (φ : Matrix (Fin 3) (Fin 3) k →ₗ[k] k)
    (P Q : Matrix (Fin 3) (Fin 3) k) :
    m3DualMatrix (m3LeftRightForm φ P Q) =
      Pᵀ * m3DualMatrix φ * Qᵀ := by
  classical
  ext i j
  have hentry (a b : Fin 3) :
      (P * squareMatrixUnit i j * Q : Matrix (Fin 3) (Fin 3) k) a b =
        P a i * Q j b := by
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single j]
    · rw [Matrix.mul_apply]
      rw [Finset.sum_eq_single i]
      · simp only [squareMatrixUnit, and_self, ↓reduceIte, mul_one]
      · intro x _ hx
        simp [squareMatrixUnit, hx]
      · simp
    · intro x _ hx
      have hzero :
          (P * squareMatrixUnit i j : Matrix (Fin 3) (Fin 3) k) a x = 0 := by
        rw [Matrix.mul_apply]
        apply Finset.sum_eq_zero
        intro y _
        simp [squareMatrixUnit, hx]
      rw [hzero, zero_mul]
    · simp
  change m3LeftRightForm φ P Q (squareMatrixUnit i j) =
    (Pᵀ * m3DualMatrix φ * Qᵀ) i j
  rw [m3LeftRightForm_apply, apply_eq_sum_m3DualMatrix_mul]
  simp_rw [hentry]
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- The coefficient-matrix construction is injective on matrix
functionals. -/
theorem m3DualMatrix_injective {k : Type*} [CommSemiring k] :
    Function.Injective
      (m3DualMatrix : (Matrix (Fin 3) (Fin 3) k →ₗ[k] k) →
        Matrix (Fin 3) (Fin 3) k) := by
  intro φ ψ hcoeff
  ext A
  rw [apply_eq_sum_m3DualMatrix_mul, apply_eq_sum_m3DualMatrix_mul, hcoeff]

/-- Invertible left-right precomposition preserves the rank of the
coefficient matrix. -/
theorem m3DualMatrix_rank_m3LeftRightForm {k : Type*} [Field k]
    (φ : Matrix (Fin 3) (Fin 3) k →ₗ[k] k)
    (P Q : Matrix (Fin 3) (Fin 3) k) [Invertible P] [Invertible Q] :
    (m3DualMatrix (m3LeftRightForm φ P Q)).rank =
      (m3DualMatrix φ).rank := by
  rw [m3DualMatrix_m3LeftRightForm]
  have hPdet : IsUnit Pᵀ.det :=
    (Matrix.isUnit_iff_isUnit_det Pᵀ).mp (isUnit_of_invertible Pᵀ)
  have hQdet : IsUnit Qᵀ.det :=
    (Matrix.isUnit_iff_isUnit_det Qᵀ).mp (isUnit_of_invertible Qᵀ)
  rw [Matrix.rank_mul_eq_left_of_isUnit_det Qᵀ (Pᵀ * m3DualMatrix φ) hQdet]
  rw [Matrix.rank_mul_eq_right_of_isUnit_det Pᵀ (m3DualMatrix φ) hPdet]

/-- Removing a simultaneous permutation from a matrix normal form preserves
invertibility of the left and right factors. -/
private theorem exists_isUnit_mul_eq_of_eq_submatrix {k : Type*} [Field k]
    (M D V U : Matrix (Fin 3) (Fin 3) k) (σ : Fin 3 ≃ Fin 3)
    (hV : IsUnit V) (hU : IsUnit U)
    (hform : V * M * U = D.submatrix σ σ) :
    ∃ V' U' : Matrix (Fin 3) (Fin 3) k,
      IsUnit V' ∧ IsUnit U' ∧ V' * M * U' = D := by
  classical
  let S : Matrix (Fin 3) (Fin 3) k :=
    (1 : Matrix (Fin 3) (Fin 3) k).submatrix σ (Equiv.refl (Fin 3))
  letI : Invertible (1 : Matrix (Fin 3) (Fin 3) k) := invertibleOne
  letI : Invertible S :=
    Matrix.submatrixEquivInvertible (1 : Matrix (Fin 3) (Fin 3) k)
      σ (Equiv.refl (Fin 3))
  have htranspose : Sᵀ =
      (1 : Matrix (Fin 3) (Fin 3) k).submatrix (Equiv.refl (Fin 3)) σ := by
    simp only [S, Matrix.transpose_submatrix, Matrix.transpose_one]
  have hrecover : Sᵀ * (D.submatrix σ σ) * S = D := by
    rw [htranspose]
    change
      ((1 : Matrix (Fin 3) (Fin 3) k).submatrix (Equiv.refl (Fin 3)) σ *
          D.submatrix σ σ) *
        (1 : Matrix (Fin 3) (Fin 3) k).submatrix σ (Equiv.refl (Fin 3)) = D
    rw [Matrix.submatrix_mul_equiv, Matrix.one_mul]
    rw [Matrix.submatrix_mul_equiv, Matrix.mul_one]
    rfl
  refine ⟨Sᵀ * V, U * S, (isUnit_of_invertible Sᵀ).mul hV,
    hU.mul (isUnit_of_invertible S), ?_⟩
  calc
    (Sᵀ * V) * M * (U * S) = Sᵀ * (V * M * U) * S := by
      simp only [Matrix.mul_assoc]
    _ = Sᵀ * (D.submatrix σ σ) * S := by rw [hform]
    _ = D := hrecover

/-- Every rank-one three-by-three matrix is left-right equivalent over its
base field to `E₁₁`. -/
theorem matrix_fin_three_rank_one_normal_form {k : Type*} [Field k]
    (M : Matrix (Fin 3) (Fin 3) k) (hrank : M.rank = 1) :
    ∃ V U : Matrix (Fin 3) (Fin 3) k,
      IsUnit V ∧ IsUnit U ∧ V * M * U = Matrix.diagonal ![1, 0, 0] := by
  classical
  let NormalForm : ℕ → Prop := fun n =>
    ∃ V U : Matrix (Fin 3) (Fin 3) k,
      ∃ e : Fin 3 ≃ Fin n ⊕ Fin (Fintype.card (Fin 3) - n),
        IsUnit V ∧ IsUnit U ∧
          V * M * U = (Matrix.fromBlocks
            (1 : Matrix (Fin n) (Fin n) k) 0 0 0).submatrix e e
  have hnormalGeneral : NormalForm M.rank :=
    Matrix.exists_rank_normal_form M
  have hnormalFixed : NormalForm 1 :=
    (congrArg NormalForm hrank).mp hnormalGeneral
  dsimp only [NormalForm] at hnormalFixed
  obtain ⟨V, U, e, hV, hU, hform⟩ := hnormalFixed
  let τ : Fin (Fintype.card (Fin 3) - 1) ≃ Fin 2 := finCongr (by norm_num)
  let ρ : Fin 1 ⊕ Fin (Fintype.card (Fin 3) - 1) ≃ Fin 1 ⊕ Fin 2 :=
    (Equiv.refl (Fin 1)).sumCongr τ
  let e' : Fin 3 ≃ Fin 1 ⊕ Fin 2 := e.trans ρ
  have hcastBlock :
      (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) k) 0 0 0).submatrix e e =
        (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) k) 0 0
          (0 : Matrix (Fin 2) (Fin 2) k)).submatrix e' e' := by
    ext i j
    simp only [Matrix.submatrix_apply]
    rcases hi : e i with x | x <;> rcases hj : e j with y | y
    all_goals simp [e', ρ, τ, hi, hj]
  let σ : Fin 3 ≃ Fin 3 := e'.trans finSumFinEquiv
  have hblock :
      (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) k) 0 0
          (0 : Matrix (Fin 2) (Fin 2) k)).submatrix e' e' =
        (Matrix.diagonal ![(1 : k), 0, 0]).submatrix σ σ := by
    ext i j
    simp only [Matrix.submatrix_apply]
    rcases hi : e' i with x | x <;> rcases hj : e' j with y | y
    all_goals fin_cases x <;> fin_cases y <;>
      simp [σ, hi, hj, finSumFinEquiv]
  exact exists_isUnit_mul_eq_of_eq_submatrix M (Matrix.diagonal ![1, 0, 0])
    V U σ hV hU (hform.trans (hcastBlock.trans hblock))

/-- Every rank-two three-by-three matrix is left-right equivalent over its
base field to `diag(1, 1, 0)`. -/
theorem matrix_fin_three_rank_two_normal_form {k : Type*} [Field k]
    (M : Matrix (Fin 3) (Fin 3) k) (hrank : M.rank = 2) :
    ∃ V U : Matrix (Fin 3) (Fin 3) k,
      IsUnit V ∧ IsUnit U ∧ V * M * U = Matrix.diagonal ![1, 1, 0] := by
  classical
  let NormalForm : ℕ → Prop := fun n =>
    ∃ V U : Matrix (Fin 3) (Fin 3) k,
      ∃ e : Fin 3 ≃ Fin n ⊕ Fin (Fintype.card (Fin 3) - n),
        IsUnit V ∧ IsUnit U ∧
          V * M * U = (Matrix.fromBlocks
            (1 : Matrix (Fin n) (Fin n) k) 0 0 0).submatrix e e
  have hnormalGeneral : NormalForm M.rank :=
    Matrix.exists_rank_normal_form M
  have hnormalFixed : NormalForm 2 :=
    (congrArg NormalForm hrank).mp hnormalGeneral
  dsimp only [NormalForm] at hnormalFixed
  obtain ⟨V, U, e, hV, hU, hform⟩ := hnormalFixed
  let τ : Fin (Fintype.card (Fin 3) - 2) ≃ Fin 1 := finCongr (by norm_num)
  let ρ : Fin 2 ⊕ Fin (Fintype.card (Fin 3) - 2) ≃ Fin 2 ⊕ Fin 1 :=
    (Equiv.refl (Fin 2)).sumCongr τ
  let e' : Fin 3 ≃ Fin 2 ⊕ Fin 1 := e.trans ρ
  have hcastBlock :
      (Matrix.fromBlocks (1 : Matrix (Fin 2) (Fin 2) k) 0 0 0).submatrix e e =
        (Matrix.fromBlocks (1 : Matrix (Fin 2) (Fin 2) k) 0 0
          (0 : Matrix (Fin 1) (Fin 1) k)).submatrix e' e' := by
    ext i j
    simp only [Matrix.submatrix_apply]
    rcases hi : e i with x | x <;> rcases hj : e j with y | y
    all_goals simp [e', ρ, τ, hi, hj]
  let σ : Fin 3 ≃ Fin 3 := e'.trans finSumFinEquiv
  have hblock :
      (Matrix.fromBlocks (1 : Matrix (Fin 2) (Fin 2) k) 0 0
          (0 : Matrix (Fin 1) (Fin 1) k)).submatrix e' e' =
        (Matrix.diagonal ![(1 : k), 1, 0]).submatrix σ σ := by
    ext i j
    simp only [Matrix.submatrix_apply]
    rcases hi : e' i with x | x <;> rcases hj : e' j with y | y
    all_goals fin_cases x <;> fin_cases y <;>
      simp [σ, hi, hj, finSumFinEquiv]
  exact exists_isUnit_mul_eq_of_eq_submatrix M (Matrix.diagonal ![1, 1, 0])
    V U σ hV hU (hform.trans (hcastBlock.trans hblock))

/-- Every rank-three three-by-three matrix is left-right equivalent over its
base field to the identity matrix. -/
theorem matrix_fin_three_rank_three_normal_form {k : Type*} [Field k]
    (M : Matrix (Fin 3) (Fin 3) k) (hrank : M.rank = 3) :
    ∃ V U : Matrix (Fin 3) (Fin 3) k,
      IsUnit V ∧ IsUnit U ∧ V * M * U = Matrix.diagonal ![1, 1, 1] := by
  classical
  let NormalForm : ℕ → Prop := fun n =>
    ∃ V U : Matrix (Fin 3) (Fin 3) k,
      ∃ e : Fin 3 ≃ Fin n ⊕ Fin (Fintype.card (Fin 3) - n),
        IsUnit V ∧ IsUnit U ∧
          V * M * U = (Matrix.fromBlocks
            (1 : Matrix (Fin n) (Fin n) k) 0 0 0).submatrix e e
  have hnormalGeneral : NormalForm M.rank :=
    Matrix.exists_rank_normal_form M
  have hnormalFixed : NormalForm 3 :=
    (congrArg NormalForm hrank).mp hnormalGeneral
  dsimp only [NormalForm] at hnormalFixed
  obtain ⟨V, U, e, hV, hU, hform⟩ := hnormalFixed
  let τ : Fin (Fintype.card (Fin 3) - 3) ≃ Fin 0 := finCongr (by norm_num)
  let ρ : Fin 3 ⊕ Fin (Fintype.card (Fin 3) - 3) ≃ Fin 3 ⊕ Fin 0 :=
    (Equiv.refl (Fin 3)).sumCongr τ
  let e' : Fin 3 ≃ Fin 3 ⊕ Fin 0 := e.trans ρ
  have hcastBlock :
      (Matrix.fromBlocks (1 : Matrix (Fin 3) (Fin 3) k) 0 0 0).submatrix e e =
        (Matrix.fromBlocks (1 : Matrix (Fin 3) (Fin 3) k) 0 0
          (0 : Matrix (Fin 0) (Fin 0) k)).submatrix e' e' := by
    ext i j
    simp only [Matrix.submatrix_apply]
    rcases hi : e i with x | x <;> rcases hj : e j with y | y
    all_goals simp [e', ρ, τ, hi, hj]
  let σ : Fin 3 ≃ Fin 3 := e'.trans finSumFinEquiv
  have hblock :
      (Matrix.fromBlocks (1 : Matrix (Fin 3) (Fin 3) k) 0 0
          (0 : Matrix (Fin 0) (Fin 0) k)).submatrix e' e' =
        (Matrix.diagonal ![(1 : k), 1, 1]).submatrix σ σ := by
    ext i j
    simp only [Matrix.submatrix_apply]
    rcases hi : e' i with x | x <;> rcases hj : e' j with y | y
    all_goals fin_cases x <;> fin_cases y <;>
      simp [σ, hi, hj, finSumFinEquiv]
  exact exists_isUnit_mul_eq_of_eq_submatrix M (Matrix.diagonal ![1, 1, 1])
    V U σ hV hU (hform.trans (hcastBlock.trans hblock))

/-- A coefficient-rank-one functional is in the invertible left-right orbit of
`m3RankOneForm`.  The equality is oriented so that restricted algorithms can
be transported from the arbitrary functional to the representative. -/
theorem m3RankOneForm_eq_leftRight_of_rank_eq_one {k : Type*} [Field k]
    (φ : Matrix (Fin 3) (Fin 3) k →ₗ[k] k)
    (hrank : (m3DualMatrix φ).rank = 1) :
    ∃ P Q : Matrix (Fin 3) (Fin 3) k,
      IsUnit P ∧ IsUnit Q ∧ m3RankOneForm = m3LeftRightForm φ P Q := by
  obtain ⟨V, U, hV, hU, hform⟩ :=
    matrix_fin_three_rank_one_normal_form (m3DualMatrix φ) hrank
  letI : Invertible V := hV.invertible
  letI : Invertible U := hU.invertible
  refine ⟨Vᵀ, Uᵀ, isUnit_of_invertible Vᵀ, isUnit_of_invertible Uᵀ, ?_⟩
  apply m3DualMatrix_injective
  rw [m3DualMatrix_m3RankOneForm, m3DualMatrix_m3LeftRightForm,
    Matrix.transpose_transpose, Matrix.transpose_transpose, hform]

/-- A coefficient-rank-two functional is in the invertible left-right orbit of
`m3RankTwoForm`.  This statement is valid over every field. -/
theorem m3RankTwoForm_eq_leftRight_of_rank_eq_two {k : Type*} [Field k]
    (φ : Matrix (Fin 3) (Fin 3) k →ₗ[k] k)
    (hrank : (m3DualMatrix φ).rank = 2) :
    ∃ P Q : Matrix (Fin 3) (Fin 3) k,
      IsUnit P ∧ IsUnit Q ∧ m3RankTwoForm = m3LeftRightForm φ P Q := by
  obtain ⟨V, U, hV, hU, hform⟩ :=
    matrix_fin_three_rank_two_normal_form (m3DualMatrix φ) hrank
  letI : Invertible V := hV.invertible
  letI : Invertible U := hU.invertible
  refine ⟨Vᵀ, Uᵀ, isUnit_of_invertible Vᵀ, isUnit_of_invertible Uᵀ, ?_⟩
  apply m3DualMatrix_injective
  rw [m3DualMatrix_m3RankTwoForm, m3DualMatrix_m3LeftRightForm,
    Matrix.transpose_transpose, Matrix.transpose_transpose, hform]

/-- A coefficient-rank-three functional is in the invertible left-right orbit
of `m3RankThreeForm`.  This statement is valid over every field. -/
theorem m3RankThreeForm_eq_leftRight_of_rank_eq_three {k : Type*} [Field k]
    (φ : Matrix (Fin 3) (Fin 3) k →ₗ[k] k)
    (hrank : (m3DualMatrix φ).rank = 3) :
    ∃ P Q : Matrix (Fin 3) (Fin 3) k,
      IsUnit P ∧ IsUnit Q ∧ m3RankThreeForm = m3LeftRightForm φ P Q := by
  obtain ⟨V, U, hV, hU, hform⟩ :=
    matrix_fin_three_rank_three_normal_form (m3DualMatrix φ) hrank
  letI : Invertible V := hV.invertible
  letI : Invertible U := hU.invertible
  refine ⟨Vᵀ, Uᵀ, isUnit_of_invertible Vᵀ, isUnit_of_invertible Uᵀ, ?_⟩
  apply m3DualMatrix_injective
  rw [m3DualMatrix_m3RankThreeForm, m3DualMatrix_m3LeftRightForm,
    Matrix.transpose_transpose, Matrix.transpose_transpose, hform]

/-- Ground truth: left-right precomposition by two identity matrices does not
change a functional. -/
example (φ : Matrix (Fin 3) (Fin 3) ℚ →ₗ[ℚ] ℚ) :
    m3LeftRightForm φ 1 1 = φ := by
  ext A
  simp only [m3LeftRightForm_apply, Matrix.one_mul, Matrix.mul_one]

/-- Ground truth: the coefficient matrix of the `(0,0)` entry functional is
exactly the first standard matrix unit. -/
example :
    m3DualMatrix (m3Form (k := ℚ) ![1, 0, 0, 0, 0, 0, 0, 0, 0]) =
      !![1, 0, 0; 0, 0, 0; 0, 0, 0] := by
  rw [m3DualMatrix_m3Form]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- An ordinary bilinear algorithm for matrix multiplication after the first
input has been restricted to the kernel hyperplane of `φ`.  Thus
`¬ M3HyperplaneRankLE φ 18` is the assertion that this restriction has tensor
rank at least nineteen. -/
def M3HyperplaneRankLE {k : Type*} [Field k]
    (φ : Matrix (Fin 3) (Fin 3) k →ₗ[k] k) (r : ℕ) : Prop :=
  ∃ (α : Fin r → LinearMap.ker φ →ₗ[k] k)
    (β : Fin r → Matrix (Fin 3) (Fin 3) k →ₗ[k] k)
    (C : Fin r → Matrix (Fin 3) (Fin 3) k),
    ∀ A B i l, (A.1 * B) i l = ∑ s, α s A * β s B * C s i l

/-- Every first-mode hyperplane restriction admits the unrestricted
schoolbook twenty-seven-product algorithm. -/
theorem M3HyperplaneRankLE.twentySeven {k : Type*} [Field k]
    (φ : Matrix (Fin 3) (Fin 3) k →ₗ[k] k) :
    M3HyperplaneRankLE φ 27 := by
  obtain ⟨α, β, C, hmul⟩ :=
    rankLE_matMulTensor_three_to_bilinear (rankLE_matMulTensor k 3 3 3)
  refine ⟨fun s => (α s).domRestrict (LinearMap.ker φ), β, C, ?_⟩
  intro A B i l
  exact hmul A.1 B i l

/-- The definition has the expected unrestricted boundary case: the zero
functional admits the schoolbook twenty-seven-term algorithm. -/
example : M3HyperplaneRankLE
    (0 : Matrix (Fin 3) (Fin 3) ℚ →ₗ[ℚ] ℚ) 27 :=
  M3HyperplaneRankLE.twentySeven 0

/-- Left-right symmetry transports a restricted algorithm.  If `ψ A` is
`φ (P * A * Q)` and `P,Q` are invertible, then an algorithm on `ker φ`
induces one of the same length on `ker ψ`; the second input is changed by
`Q⁻¹` and the output by `P⁻¹`. -/
theorem M3HyperplaneRankLE.of_leftRight {k : Type*} [Field k] {r : ℕ}
    {φ ψ : Matrix (Fin 3) (Fin 3) k →ₗ[k] k}
    (P Q : Matrix (Fin 3) (Fin 3) k) [Invertible P] [Invertible Q]
    (hrelation : ∀ A, ψ A = φ (P * A * Q))
    (h : M3HyperplaneRankLE φ r) : M3HyperplaneRankLE ψ r := by
  classical
  let τ : LinearMap.ker ψ →ₗ[k] LinearMap.ker φ :=
    { toFun := fun A => ⟨P * A.1 * Q, by
        change φ (P * A.1 * Q) = 0
        rw [← hrelation]
        exact A.2⟩
      map_add' := by
        intro A B
        apply Subtype.ext
        simp only [Submodule.coe_add, Matrix.mul_add, Matrix.add_mul]
      map_smul' := by
        intro c A
        apply Subtype.ext
        simp only [SetLike.val_smul, Matrix.mul_smul, Matrix.smul_mul,
          RingHom.id_apply] }
  let ρ : Matrix (Fin 3) (Fin 3) k →ₗ[k] Matrix (Fin 3) (Fin 3) k :=
    { toFun := fun B => ⅟Q * B
      map_add' := fun A B => Matrix.mul_add (⅟Q) A B
      map_smul' := fun c A => Matrix.mul_smul (⅟Q) c A }
  obtain ⟨α, β, C, halgorithm⟩ := h
  refine ⟨fun s => (α s).comp τ, fun s => (β s).comp ρ,
    fun s => ⅟P * C s, ?_⟩
  intro A B i l
  have hdecomp : (P * A.1 * Q) * (⅟Q * B) =
      ∑ s, (α s (τ A) * β s (ρ B)) • C s := by
    ext p q
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    change ((τ A).1 * ρ B) p q =
      ∑ s, α s (τ A) * β s (ρ B) * C s p q
    exact halgorithm (τ A) (ρ B) p q
  have hrecover : A.1 * B = ⅟P * ((P * A.1 * Q) * (⅟Q * B)) := by
    simp only [Matrix.mul_assoc, Matrix.mul_invOf_cancel_left,
      Matrix.invOf_mul_cancel_left]
  calc
    (A.1 * B) i l = (⅟P * ((P * A.1 * Q) * (⅟Q * B))) i l := by rw [hrecover]
    _ = (⅟P * ∑ s, (α s (τ A) * β s (ρ B)) • C s) i l := by rw [hdecomp]
    _ = ∑ s, ((α s).comp τ) A * ((β s).comp ρ) B * (⅟P * C s) i l := by
      rw [Matrix.mul_sum]
      simp only [Matrix.sum_apply, Matrix.mul_smul, Matrix.smul_apply,
        smul_eq_mul, LinearMap.coe_comp, Function.comp_apply]

/-- An algorithm on a coefficient-rank-one functional transports to the fixed
representative `m3RankOneForm`. -/
theorem M3HyperplaneRankLE.rankOneRepresentative_of_rank_eq_one
    {k : Type*} [Field k] {r : ℕ}
    {φ : Matrix (Fin 3) (Fin 3) k →ₗ[k] k}
    (h : M3HyperplaneRankLE φ r) (hrank : (m3DualMatrix φ).rank = 1) :
    M3HyperplaneRankLE (m3RankOneForm (k := k)) r := by
  obtain ⟨P, Q, hP, hQ, hform⟩ :=
    m3RankOneForm_eq_leftRight_of_rank_eq_one φ hrank
  letI : Invertible P := hP.invertible
  letI : Invertible Q := hQ.invertible
  apply M3HyperplaneRankLE.of_leftRight (φ := φ)
    (ψ := m3RankOneForm (k := k)) P Q _ h
  intro A
  rw [hform, m3LeftRightForm_apply]

/-- An algorithm on a coefficient-rank-two functional transports to the fixed
representative `m3RankTwoForm`. -/
theorem M3HyperplaneRankLE.rankTwoRepresentative_of_rank_eq_two
    {k : Type*} [Field k] {r : ℕ}
    {φ : Matrix (Fin 3) (Fin 3) k →ₗ[k] k}
    (h : M3HyperplaneRankLE φ r) (hrank : (m3DualMatrix φ).rank = 2) :
    M3HyperplaneRankLE (m3RankTwoForm (k := k)) r := by
  obtain ⟨P, Q, hP, hQ, hform⟩ :=
    m3RankTwoForm_eq_leftRight_of_rank_eq_two φ hrank
  letI : Invertible P := hP.invertible
  letI : Invertible Q := hQ.invertible
  apply M3HyperplaneRankLE.of_leftRight (φ := φ)
    (ψ := m3RankTwoForm (k := k)) P Q _ h
  intro A
  rw [hform, m3LeftRightForm_apply]

/-- An algorithm on a coefficient-rank-three functional transports to the
fixed representative `m3RankThreeForm`. -/
theorem M3HyperplaneRankLE.rankThreeRepresentative_of_rank_eq_three
    {k : Type*} [Field k] {r : ℕ}
    {φ : Matrix (Fin 3) (Fin 3) k →ₗ[k] k}
    (h : M3HyperplaneRankLE φ r) (hrank : (m3DualMatrix φ).rank = 3) :
    M3HyperplaneRankLE (m3RankThreeForm (k := k)) r := by
  obtain ⟨P, Q, hP, hQ, hform⟩ :=
    m3RankThreeForm_eq_leftRight_of_rank_eq_three φ hrank
  letI : Invertible P := hP.invertible
  letI : Invertible Q := hQ.invertible
  apply M3HyperplaneRankLE.of_leftRight (φ := φ)
    (ψ := m3RankThreeForm (k := k)) P Q _ h
  intro A
  rw [hform, m3LeftRightForm_apply]

/-- Substitution reduction: an `(r+1)`-term decomposition of `M3` yields an
`r`-term algorithm on the kernel of one nonzero first-mode form. -/
theorem m3_exists_hyperplane_rankLE_of_rankLE_succ {k : Type*} [Field k]
    {r : ℕ} (h : RankLE (matMulTensor k 3 3 3) (r + 1)) :
    ∃ φ : Matrix (Fin 3) (Fin 3) k →ₗ[k] k,
      φ ≠ 0 ∧ M3HyperplaneRankLE φ r := by
  classical
  obtain ⟨α, β, C, hmul⟩ := rankLE_matMulTensor_three_to_bilinear h
  obtain ⟨e, _he, hαe⟩ := m3_exists_nine_independent_first_forms α β C hmul
  let s : Fin (r + 1) := e 0
  have hαs : α s ≠ 0 := by
    have hnonzero := hαe.ne_zero 0
    simpa only [Function.comp_apply, s] using hnonzero
  refine ⟨α s, hαs, ?_⟩
  refine ⟨fun q => (α (s.succAbove q)).domRestrict (LinearMap.ker (α s)),
    fun q => β (s.succAbove q), fun q => C (s.succAbove q), ?_⟩
  intro A B i l
  have heq := hmul A.1 B i l
  rw [Fin.sum_univ_succAbove _ s] at heq
  have hkill : α s A.1 = 0 := A.2
  simp only [hkill, zero_mul, zero_add] at heq
  exact heq

/-- A nonzero first-mode form belongs to exactly one of the three possible
left-right matrix-rank strata: coefficient-matrix rank one, two, or three. -/
theorem m3DualMatrix_rank_eq_one_or_two_or_three_of_ne_zero
    {k : Type*} [Field k] (φ : Matrix (Fin 3) (Fin 3) k →ₗ[k] k)
    (hφ : φ ≠ 0) :
    (m3DualMatrix φ).rank = 1 ∨ (m3DualMatrix φ).rank = 2 ∨
      (m3DualMatrix φ).rank = 3 := by
  classical
  let M := m3DualMatrix φ
  have hM : M ≠ 0 := by
    intro hzero
    apply hφ
    exact (m3DualMatrix_eq_zero_iff φ).mp hzero
  have hrank0 : M.rank ≠ 0 := by
    intro hzero
    have hrange : LinearMap.range M.mulVecLin = ⊥ := by
      apply Submodule.finrank_eq_zero.mp
      simpa only [Matrix.rank] using hzero
    have hmap : M.mulVecLin = 0 := LinearMap.range_eq_bot.mp hrange
    apply hM
    ext i j
    have hcol := LinearMap.congr_fun hmap (Pi.single j 1)
    change M.mulVec (Pi.single j 1) = 0 at hcol
    rw [Matrix.mulVec_single_one] at hcol
    exact congrFun hcol i
  have hrank_le : M.rank ≤ 3 := by
    simpa using Matrix.rank_le_width M
  have hrank_pos : 0 < M.rank := Nat.pos_of_ne_zero hrank0
  by_cases hrankOne : M.rank = 1
  · exact Or.inl hrankOne
  by_cases hrankTwo : M.rank = 2
  · exact Or.inr (Or.inl hrankTwo)
  · right
    right
    have hrankThree : M.rank = 3 := by omega
    simpa only [M] using hrankThree

/-- Every nonzero three-by-three matrix functional belongs to the invertible
left-right orbit of one of the three standard rank representatives.  This
field-uniform disjunction records the complete orbit classification. -/
theorem m3_exists_representative_leftRight_of_ne_zero
    {k : Type*} [Field k] (φ : Matrix (Fin 3) (Fin 3) k →ₗ[k] k)
    (hφ : φ ≠ 0) :
    (∃ P Q : Matrix (Fin 3) (Fin 3) k,
        IsUnit P ∧ IsUnit Q ∧
          m3RankOneForm (k := k) = m3LeftRightForm φ P Q) ∨
      (∃ P Q : Matrix (Fin 3) (Fin 3) k,
        IsUnit P ∧ IsUnit Q ∧
          m3RankTwoForm (k := k) = m3LeftRightForm φ P Q) ∨
      (∃ P Q : Matrix (Fin 3) (Fin 3) k,
        IsUnit P ∧ IsUnit Q ∧
          m3RankThreeForm (k := k) = m3LeftRightForm φ P Q) := by
  rcases m3DualMatrix_rank_eq_one_or_two_or_three_of_ne_zero φ hφ with
    hrank | hrank | hrank
  · exact Or.inl (m3RankOneForm_eq_leftRight_of_rank_eq_one φ hrank)
  · exact Or.inr (Or.inl
      (m3RankTwoForm_eq_leftRight_of_rank_eq_two φ hrank))
  · exact Or.inr (Or.inr
      (m3RankThreeForm_eq_leftRight_of_rank_eq_three φ hrank))

/-- Joint ground truth for the three representative-transport theorems:
over `ℚ`, each standard form simultaneously has a twenty-seven-product
hyperplane algorithm and the coefficient-matrix rank required by its theorem. -/
example :
    let φ₁ := m3RankOneForm (k := ℚ)
    let φ₂ := m3RankTwoForm (k := ℚ)
    let φ₃ := m3RankThreeForm (k := ℚ)
    (M3HyperplaneRankLE φ₁ 27 ∧ (m3DualMatrix φ₁).rank = 1) ∧
      (M3HyperplaneRankLE φ₂ 27 ∧ (m3DualMatrix φ₂).rank = 2) ∧
      (M3HyperplaneRankLE φ₃ 27 ∧ (m3DualMatrix φ₃).rank = 3) := by
  dsimp only
  refine ⟨⟨M3HyperplaneRankLE.twentySeven m3RankOneForm, ?_⟩,
    ⟨M3HyperplaneRankLE.twentySeven m3RankTwoForm, ?_⟩,
    M3HyperplaneRankLE.twentySeven m3RankThreeForm, ?_⟩
  · rw [m3DualMatrix_m3RankOneForm, Matrix.rank_diagonal]
    decide
  · rw [m3DualMatrix_m3RankTwoForm, Matrix.rank_diagonal]
    decide
  · rw [m3DualMatrix_m3RankThreeForm, Matrix.rank_diagonal]
    decide

#check @m3DualMatrix
#check @m3DualMatrix_m3Form
#check @m3DualMatrix_eq_zero_iff
#check @m3RankOneForm
#check @m3RankTwoForm
#check @m3RankThreeForm
#check @m3DualMatrix_m3RankOneForm
#check @m3DualMatrix_m3RankTwoForm
#check @m3DualMatrix_m3RankThreeForm
#check @m3LeftRightForm
#check @m3LeftRightForm_apply
#check @apply_eq_sum_m3DualMatrix_mul
#check @m3DualMatrix_m3LeftRightForm
#check @m3DualMatrix_injective
#check @m3DualMatrix_rank_m3LeftRightForm
#check @matrix_fin_three_rank_one_normal_form
#check @matrix_fin_three_rank_two_normal_form
#check @matrix_fin_three_rank_three_normal_form
#check @m3RankOneForm_eq_leftRight_of_rank_eq_one
#check @m3RankTwoForm_eq_leftRight_of_rank_eq_two
#check @m3RankThreeForm_eq_leftRight_of_rank_eq_three
#check @M3HyperplaneRankLE
#check @M3HyperplaneRankLE.twentySeven
#check @M3HyperplaneRankLE.of_leftRight
#check @M3HyperplaneRankLE.rankOneRepresentative_of_rank_eq_one
#check @M3HyperplaneRankLE.rankTwoRepresentative_of_rank_eq_two
#check @M3HyperplaneRankLE.rankThreeRepresentative_of_rank_eq_three
#check @m3_exists_hyperplane_rankLE_of_rankLE_succ
#check @m3DualMatrix_rank_eq_one_or_two_or_three_of_ne_zero
#check @m3_exists_representative_leftRight_of_ne_zero

#print axioms m3DualMatrix_m3Form
#print axioms m3DualMatrix_eq_zero_iff
#print axioms m3DualMatrix_m3RankOneForm
#print axioms m3DualMatrix_m3RankTwoForm
#print axioms m3DualMatrix_m3RankThreeForm
#print axioms m3LeftRightForm_apply
#print axioms apply_eq_sum_m3DualMatrix_mul
#print axioms m3DualMatrix_m3LeftRightForm
#print axioms m3DualMatrix_injective
#print axioms m3DualMatrix_rank_m3LeftRightForm
#print axioms matrix_fin_three_rank_one_normal_form
#print axioms matrix_fin_three_rank_two_normal_form
#print axioms matrix_fin_three_rank_three_normal_form
#print axioms m3RankOneForm_eq_leftRight_of_rank_eq_one
#print axioms m3RankTwoForm_eq_leftRight_of_rank_eq_two
#print axioms m3RankThreeForm_eq_leftRight_of_rank_eq_three
#print axioms M3HyperplaneRankLE.twentySeven
#print axioms M3HyperplaneRankLE.of_leftRight
#print axioms M3HyperplaneRankLE.rankOneRepresentative_of_rank_eq_one
#print axioms M3HyperplaneRankLE.rankTwoRepresentative_of_rank_eq_two
#print axioms M3HyperplaneRankLE.rankThreeRepresentative_of_rank_eq_three
#print axioms m3_exists_hyperplane_rankLE_of_rankLE_succ
#print axioms m3DualMatrix_rank_eq_one_or_two_or_three_of_ne_zero
#print axioms m3_exists_representative_leftRight_of_ne_zero

end BilinearComplexity
