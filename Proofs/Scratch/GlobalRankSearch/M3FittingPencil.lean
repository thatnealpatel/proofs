/-
  Scratch/GlobalRankSearch/M3FittingPencil — rank-one matrix-pencil
  factorization induced by a hyperplane algorithm for three-by-three matrix
  multiplication.
-/
import Scratch.GlobalRankSearch.ContractionSupport
import Scratch.GlobalRankSearch.M3HyperplaneInfrastructure
import Mathlib.LinearAlgebra.Matrix.Kronecker

set_option autoImplicit false

namespace BilinearComplexity

open scoped Matrix

/-- The coefficient vector of a matrix functional, indexed by product
coordinates in row-column order. -/
def m3FunctionalVec {k : Type*} [CommSemiring k]
    (β : Matrix (Fin 3) (Fin 3) k →ₗ[k] k) : Fin 3 × Fin 3 → k :=
  fun jl => β (squareMatrixUnit jl.1 jl.2)

/-- Ground check: the coefficient of the `(1, 2)` entry functional at its own
product coordinate is one. -/
example :
    m3FunctionalVec (m3Form (k := ℚ) ![0, 0, 0, 0, 0, 1, 0, 0, 0]) (1, 2) = 1 := by
  change m3DualMatrix (m3Form (k := ℚ) ![0, 0, 0, 0, 0, 1, 0, 0, 0]) 1 2 = 1
  rw [m3DualMatrix_m3Form]
  rfl

/-- Vectorize an output matrix using its row and column as product
coordinates. -/
def m3OutputVec {k : Type*} (C : Matrix (Fin 3) (Fin 3) k) : Fin 3 × Fin 3 → k :=
  fun il => C il.1 il.2

/-- Ground check: output vectorization preserves the `(2, 1)` entry. -/
example : m3OutputVec !![(1 : ℚ), 2, 3; 4, 5, 6; 7, 8, 9] (2, 1) = 8 := by
  rfl

/-- A matrix functional evaluates as the sum of its product-coordinate
coefficients times the corresponding matrix entries. -/
theorem m3LinearMap_apply_eq_sum_functionalVec_mul {k : Type*} [CommSemiring k]
    (β : Matrix (Fin 3) (Fin 3) k →ₗ[k] k)
    (B : Matrix (Fin 3) (Fin 3) k) :
    β B = ∑ jl, m3FunctionalVec β jl * m3OutputVec B jl := by
  rw [apply_eq_sum_m3DualMatrix_mul]
  rw [Fintype.sum_prod_type]
  rfl

/-- Every hyperplane algorithm gives a rank-one matrix-pencil factorization of
left multiplication by each matrix in the defining hyperplane. -/
theorem M3HyperplaneRankLE.exists_fittingPencil_factorization
    {k : Type*} [Field k] {r : ℕ}
    {φ : Matrix (Fin 3) (Fin 3) k →ₗ[k] k}
    (h : M3HyperplaneRankLE φ r) :
    ∃ (α : Fin r → LinearMap.ker φ →ₗ[k] k)
      (β : Fin r → Matrix (Fin 3) (Fin 3) k →ₗ[k] k)
      (C : Fin r → Matrix (Fin 3) (Fin 3) k),
      ∀ A : LinearMap.ker φ,
        repeatedBlock (n := 3) A.1 =
          ∑ s, α s A • Matrix.vecMulVec (m3OutputVec (C s)) (m3FunctionalVec (β s)) := by
  classical
  obtain ⟨α, β, C, halgorithm⟩ := h
  refine ⟨α, β, C, ?_⟩
  intro A
  ext il jl
  have hevaluation := halgorithm A (squareMatrixUnit jl.1 jl.2) il.1 il.2
  have hmul :
      ((A.1 * (squareMatrixUnit jl.1 jl.2 : Matrix (Fin 3) (Fin 3) k)) il.1 il.2) =
        if il.2 = jl.2 then A.1 il.1 jl.1 else 0 := by
    rw [Matrix.mul_apply]
    by_cases hcolumn : il.2 = jl.2
    · rw [if_pos hcolumn]
      rw [Finset.sum_eq_single jl.1]
      · simp [squareMatrixUnit, hcolumn]
      · intro q _ hq
        simp [squareMatrixUnit, hq]
      · simp
    · rw [if_neg hcolumn]
      apply Finset.sum_eq_zero
      intro q _
      simp [squareMatrixUnit, hcolumn]
  rw [hmul] at hevaluation
  simp only [repeatedBlock, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, m3OutputVec, m3FunctionalVec, smul_eq_mul]
  rw [hevaluation]
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- Three repeated blocks of a three-by-three matrix have three times the
matrix rank. -/
theorem m3_repeatedBlock_rank {k : Type*} [Field k]
    (A : Matrix (Fin 3) (Fin 3) k) :
    (repeatedBlock (n := 3) A).rank = 3 * A.rank := by
  exact repeatedBlock_rank A

/-- Three repeated blocks of a three-by-three matrix have determinant equal to
the cube of the original determinant. -/
theorem m3_repeatedBlock_det {k : Type*} [CommRing k]
    (A : Matrix (Fin 3) (Fin 3) k) :
    (repeatedBlock (n := 3) A).det = A.det ^ 3 := by
  classical
  have hkronecker :
      repeatedBlock (n := 3) A =
        Matrix.kronecker A (1 : Matrix (Fin 3) (Fin 3) k) := by
    ext il jl
    change (if il.2 = jl.2 then A il.1 jl.1 else 0) =
      A il.1 jl.1 * (1 : Matrix (Fin 3) (Fin 3) k) il.2 jl.2
    by_cases hblock : il.2 = jl.2
    · rw [if_pos hblock, hblock]
      simp
    · rw [if_neg hblock]
      simp [hblock]
  rw [hkronecker]
  change
    (Matrix.kroneckerMap (fun x y : k => x * y) A
      (1 : Matrix (Fin 3) (Fin 3) k)).det = A.det ^ 3
  rw [Matrix.det_kronecker]
  simp

/-- Satisfiability regression: the zero-functional hyperplane has a concrete
schoolbook algorithm whose witnesses also supply the fitting-pencil
factorization for every matrix. -/
example :
    ∃ (α : Fin 27 → LinearMap.ker
        (0 : Matrix (Fin 3) (Fin 3) ℚ →ₗ[ℚ] ℚ) →ₗ[ℚ] ℚ)
      (β : Fin 27 → Matrix (Fin 3) (Fin 3) ℚ →ₗ[ℚ] ℚ)
      (C : Fin 27 → Matrix (Fin 3) (Fin 3) ℚ),
      ∀ A : LinearMap.ker
        (0 : Matrix (Fin 3) (Fin 3) ℚ →ₗ[ℚ] ℚ),
        repeatedBlock (n := 3) A.1 =
          ∑ s, α s A • Matrix.vecMulVec (m3OutputVec (C s)) (m3FunctionalVec (β s)) :=
  (M3HyperplaneRankLE.twentySeven
    (0 : Matrix (Fin 3) (Fin 3) ℚ →ₗ[ℚ] ℚ)).exists_fittingPencil_factorization

#check @m3FunctionalVec
#check @m3OutputVec
#check @m3LinearMap_apply_eq_sum_functionalVec_mul
#check @M3HyperplaneRankLE.exists_fittingPencil_factorization
#check @m3_repeatedBlock_rank
#check @m3_repeatedBlock_det

#print axioms m3LinearMap_apply_eq_sum_functionalVec_mul
#print axioms M3HyperplaneRankLE.exists_fittingPencil_factorization
#print axioms m3_repeatedBlock_rank
#print axioms m3_repeatedBlock_det

end BilinearComplexity
