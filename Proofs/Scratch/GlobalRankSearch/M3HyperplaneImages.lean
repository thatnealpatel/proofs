/-
  Scratch/GlobalRankSearch/M3HyperplaneImages — dimensions of images of
  hyperplanes under left and right multiplication in `M₃`.
-/
import Scratch.GlobalRankSearch.MatrixRightIdeal
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Scratch.GlobalRankSearch.M3HyperplaneInfrastructure

set_option autoImplicit false

namespace BilinearComplexity

open scoped Matrix

/-- Restricting a finite-dimensional linear map to a nonzero functional's
kernel either preserves its image dimension, or lowers it by exactly one.  The
one-dimensional loss occurs exactly when the map's kernel lies in the
functional's kernel. -/
theorem finrank_range_domRestrict_ker_dichotomy
    {k V W : Type*} [Field k] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k V]
    (f : V →ₗ[k] W) (φ : V →ₗ[k] k) (hφ : φ ≠ 0) :
    ((LinearMap.ker f ≤ LinearMap.ker φ) ∧
        Module.finrank k (LinearMap.range
          (f.domRestrict (LinearMap.ker φ))) + 1 =
          Module.finrank k (LinearMap.range f)) ∨
      (¬ LinearMap.ker f ≤ LinearMap.ker φ) ∧
        Module.finrank k (LinearMap.range
          (f.domRestrict (LinearMap.ker φ))) =
          Module.finrank k (LinearMap.range f) := by
  let g := f.domRestrict (LinearMap.ker φ)
  let ψ := φ.domRestrict (LinearMap.ker f)
  let e : LinearMap.ker g ≃ₗ[k] LinearMap.ker ψ :=
    { toFun := fun x => ⟨⟨x.1.1, by exact x.2⟩, x.1.2⟩
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        intro c x
        rfl
      invFun := fun x => ⟨⟨x.1.1, x.2⟩, by exact x.1.2⟩
      left_inv := by
        intro x
        rfl
      right_inv := by
        intro x
        rfl }
  have hkerDim : Module.finrank k (LinearMap.ker g) =
      Module.finrank k (LinearMap.ker ψ) := e.finrank_eq
  have hφDim : Module.finrank k (LinearMap.ker φ) + 1 =
      Module.finrank k V :=
    Module.Dual.finrank_ker_add_one_of_ne_zero hφ
  have hgRank := LinearMap.finrank_range_add_finrank_ker g
  have hfRank := LinearMap.finrank_range_add_finrank_ker f
  by_cases hcontain : LinearMap.ker f ≤ LinearMap.ker φ
  · left
    refine ⟨hcontain, ?_⟩
    have hψ : ψ = 0 := by
      ext x
      exact hcontain x.2
    have hψKer : Module.finrank k (LinearMap.ker ψ) =
        Module.finrank k (LinearMap.ker f) := by
      rw [hψ, LinearMap.ker_zero, finrank_top]
    dsimp only [g, ψ] at hkerDim hgRank hψKer
    omega
  · right
    refine ⟨hcontain, ?_⟩
    have hψNe : ψ ≠ 0 := by
      intro hψ
      apply hcontain
      intro x hx
      change φ x = 0
      have heval := LinearMap.congr_fun hψ ⟨x, hx⟩
      exact heval
    have hψDim : Module.finrank k (LinearMap.ker ψ) + 1 =
        Module.finrank k (LinearMap.ker f) :=
      Module.Dual.finrank_ker_add_one_of_ne_zero hψNe
    dsimp only [g, ψ] at hkerDim hgRank hψDim
    omega

/-- Over a field, left multiplication by `b` has image dimension
`n * rank(b)`, including the zero-dimensional case `n = 0`. -/
theorem finrank_range_mulLeftLinearMap {k : Type*} [Field k] {n : ℕ}
    (b : Matrix (Fin n) (Fin n) k) :
    Module.finrank k (LinearMap.range (mulLeftLinearMap (Fin n) k b)) = n * b.rank := by
  let T := Matrix.transposeLinearEquiv (R := k) (m := Fin n) (n := Fin n) (α := k)
  let hkerEquiv : LinearMap.ker (mulLeftLinearMap (Fin n) k b) ≃ₗ[k]
      LinearMap.ker (matrixRightMul bᵀ) :=
    { toFun := fun X => ⟨T X.1, by
          change X.1ᵀ * bᵀ = 0
          have hzero := congrArg Matrix.transpose X.2
          change (b * X.1)ᵀ = 0 at hzero
          simpa only [Matrix.transpose_mul, Matrix.transpose_transpose,
            Matrix.transpose_zero] using hzero⟩
      map_add' := by
        intro X Y
        apply Subtype.ext
        exact T.map_add X.1 Y.1
      map_smul' := by
        intro c X
        apply Subtype.ext
        exact T.map_smul c X.1
      invFun := fun Y => ⟨T.symm Y.1, by
          change b * Y.1ᵀ = 0
          have hzero := congrArg Matrix.transpose Y.2
          change (Y.1 * bᵀ)ᵀ = 0 at hzero
          simpa only [Matrix.transpose_mul, Matrix.transpose_transpose,
            Matrix.transpose_zero] using hzero⟩
      left_inv := by
        intro X
        apply Subtype.ext
        exact T.symm_apply_apply X.1
      right_inv := by
        intro Y
        apply Subtype.ext
        exact T.apply_symm_apply Y.1 }
  have hleft := LinearMap.finrank_range_add_finrank_ker (mulLeftLinearMap (Fin n) k b)
  have hright := LinearMap.finrank_range_add_finrank_ker (matrixRightMul bᵀ)
  have hker := hkerEquiv.finrank_eq
  rw [finrank_range_matrixRightMul, Matrix.rank_transpose] at hright
  have hdomain : Module.finrank k (Matrix (Fin n) (Fin n) k) = n * n := by
    rw [Module.finrank_matrix]
    simp
  rw [hdomain] at hleft hright
  omega

/-- The functional whose coefficient matrix is `C`. -/
def m3MatrixForm {k : Type*} [CommSemiring k]
    (C : Matrix (Fin 3) (Fin 3) k) : Matrix (Fin 3) (Fin 3) k →ₗ[k] k :=
  m3Form (fun x => C (m3Equiv.symm x).1 (m3Equiv.symm x).2)

/-- The coefficient matrix of `m3MatrixForm C` is exactly `C`. -/
@[simp]
theorem m3DualMatrix_m3MatrixForm {k : Type*} [CommSemiring k]
    (C : Matrix (Fin 3) (Fin 3) k) :
    m3DualMatrix (m3MatrixForm C) = C := by
  rw [m3MatrixForm, m3DualMatrix_m3Form]
  ext i j
  simp

/-- Ground check: `m3MatrixForm` reads an off-diagonal coefficient in
row-column orientation. -/
example :
    m3MatrixForm !![(1 : ℚ), 2, 3; 4, 5, 6; 7, 8, 9]
      !![0, 1, 0; 0, 0, 0; 0, 0, 0] = 2 := by
  rw [apply_eq_sum_m3DualMatrix_mul, m3DualMatrix_m3MatrixForm]
  norm_num [Fin.sum_univ_succ]

/-- Precomposing a functional by right multiplication multiplies its
coefficient matrix on the right by the transpose. -/
theorem m3DualMatrix_comp_matrixRightMul {k : Type*} [CommSemiring k]
    (ψ : Matrix (Fin 3) (Fin 3) k →ₗ[k] k)
    (B : Matrix (Fin 3) (Fin 3) k) :
    m3DualMatrix (ψ.comp (matrixRightMul B)) = m3DualMatrix ψ * Bᵀ := by
  have hcomp : ψ.comp (matrixRightMul B) = m3LeftRightForm ψ 1 B := by
    ext A
    simp only [LinearMap.coe_comp, Function.comp_apply, matrixRightMul_apply,
      m3LeftRightForm_apply, Matrix.one_mul]
  rw [hcomp, m3DualMatrix_m3LeftRightForm, Matrix.transpose_one, Matrix.one_mul]

/-- Precomposing a functional by left multiplication multiplies its
coefficient matrix on the left by the transpose. -/
theorem m3DualMatrix_comp_mulLeftLinearMap {k : Type*} [CommSemiring k]
    (ψ : Matrix (Fin 3) (Fin 3) k →ₗ[k] k)
    (B : Matrix (Fin 3) (Fin 3) k) :
    m3DualMatrix (ψ.comp (mulLeftLinearMap (Fin 3) k B)) = Bᵀ * m3DualMatrix ψ := by
  have hcomp : ψ.comp (mulLeftLinearMap (Fin 3) k B) = m3LeftRightForm ψ B 1 := by
    ext A
    simp only [LinearMap.coe_comp, Function.comp_apply, mulLeftLinearMap_apply,
      m3LeftRightForm_apply, Matrix.mul_one]
  rw [hcomp, m3DualMatrix_m3LeftRightForm, Matrix.transpose_one, Matrix.mul_one]

/-- For right multiplication, the exceptional kernel containment is equivalent
to the dual coefficient matrix lying in the principal left ideal generated by
`Bᵀ`. -/
theorem ker_matrixRightMul_le_ker_iff_m3DualMatrix_mem_range
    {k : Type*} [Field k]
    (φ : Matrix (Fin 3) (Fin 3) k →ₗ[k] k)
    (B : Matrix (Fin 3) (Fin 3) k) :
    LinearMap.ker (matrixRightMul B) ≤ LinearMap.ker φ ↔
      m3DualMatrix φ ∈ LinearMap.range (matrixRightMul Bᵀ) := by
  constructor
  · intro hcontain
    have hann : φ ∈ (LinearMap.ker (matrixRightMul B)).dualAnnihilator :=
      Submodule.mem_dualAnnihilator φ |>.mpr fun X hX => hcontain hX
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hann
    obtain ⟨ψ, hψ⟩ := hann
    refine ⟨m3DualMatrix ψ, ?_⟩
    change m3DualMatrix ψ * Bᵀ = m3DualMatrix φ
    rw [← m3DualMatrix_comp_matrixRightMul]
    apply congrArg m3DualMatrix
    simpa only [LinearMap.dualMap_apply'] using hψ
  · rintro ⟨C, hC⟩
    let ψ := m3MatrixForm C
    have hfactor : ψ.comp (matrixRightMul B) = φ := by
      apply m3DualMatrix_injective
      rw [m3DualMatrix_comp_matrixRightMul, m3DualMatrix_m3MatrixForm]
      exact hC
    intro X hX
    change φ X = 0
    rw [← hfactor]
    change (matrixRightMul B) X = 0 at hX
    change ψ ((matrixRightMul B) X) = 0
    rw [hX, map_zero]

/-- For left multiplication, the exceptional kernel containment is equivalent
to the dual coefficient matrix lying in the range of left multiplication by
`Bᵀ`. -/
theorem ker_mulLeftLinearMap_le_ker_iff_m3DualMatrix_mem_range
    {k : Type*} [Field k]
    (φ : Matrix (Fin 3) (Fin 3) k →ₗ[k] k)
    (B : Matrix (Fin 3) (Fin 3) k) :
    LinearMap.ker (mulLeftLinearMap (Fin 3) k B) ≤ LinearMap.ker φ ↔
      m3DualMatrix φ ∈ LinearMap.range (mulLeftLinearMap (Fin 3) k Bᵀ) := by
  constructor
  · intro hcontain
    have hann : φ ∈ (LinearMap.ker (mulLeftLinearMap (Fin 3) k B)).dualAnnihilator :=
      Submodule.mem_dualAnnihilator φ |>.mpr fun X hX => hcontain hX
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hann
    obtain ⟨ψ, hψ⟩ := hann
    refine ⟨m3DualMatrix ψ, ?_⟩
    change Bᵀ * m3DualMatrix ψ = m3DualMatrix φ
    rw [← m3DualMatrix_comp_mulLeftLinearMap]
    apply congrArg m3DualMatrix
    simpa only [LinearMap.dualMap_apply'] using hψ
  · rintro ⟨C, hC⟩
    let ψ := m3MatrixForm C
    have hfactor : ψ.comp (mulLeftLinearMap (Fin 3) k B) = φ := by
      apply m3DualMatrix_injective
      rw [m3DualMatrix_comp_mulLeftLinearMap, m3DualMatrix_m3MatrixForm]
      exact hC
    intro X hX
    change φ X = 0
    rw [← hfactor]
    change (mulLeftLinearMap (Fin 3) k B) X = 0 at hX
    change ψ ((mulLeftLinearMap (Fin 3) k B) X) = 0
    rw [hX, map_zero]

/-- The image of the hyperplane `ker φ` under right multiplication by `B` has
full dimension `3 * rank(B)`, except that it has codimension one precisely
when the multiplication kernel lies in `ker φ`. -/
theorem m3_finrank_range_rightMul_domRestrict_ker_dichotomy
    {k : Type*} [Field k]
    (φ : Matrix (Fin 3) (Fin 3) k →ₗ[k] k) (hφ : φ ≠ 0)
    (B : Matrix (Fin 3) (Fin 3) k) :
    ((LinearMap.ker (matrixRightMul B) ≤ LinearMap.ker φ) ∧
        Module.finrank k (LinearMap.range
          ((matrixRightMul B).domRestrict (LinearMap.ker φ))) + 1 =
          3 * B.rank) ∨
      (¬ LinearMap.ker (matrixRightMul B) ≤ LinearMap.ker φ) ∧
        Module.finrank k (LinearMap.range
          ((matrixRightMul B).domRestrict (LinearMap.ker φ))) =
          3 * B.rank := by
  simpa only [finrank_range_matrixRightMul] using
    finrank_range_domRestrict_ker_dichotomy (matrixRightMul B) φ hφ

/-- The one-dimensional loss for a right-multiplication hyperplane image occurs
if and only if the multiplication kernel lies in the defining hyperplane. -/
theorem m3_finrank_range_rightMul_domRestrict_add_one_iff
    {k : Type*} [Field k]
    (φ : Matrix (Fin 3) (Fin 3) k →ₗ[k] k) (hφ : φ ≠ 0)
    (B : Matrix (Fin 3) (Fin 3) k) :
    Module.finrank k (LinearMap.range
        ((matrixRightMul B).domRestrict (LinearMap.ker φ))) + 1 =
        3 * B.rank ↔
      LinearMap.ker (matrixRightMul B) ≤ LinearMap.ker φ := by
  rcases m3_finrank_range_rightMul_domRestrict_ker_dichotomy φ hφ B with
    ⟨hcontain, hdim⟩ | ⟨hcontain, hdim⟩
  · exact ⟨fun _ => hcontain, fun _ => hdim⟩
  · constructor
    · intro hloss
      exfalso
      rw [hdim] at hloss
      omega
    · exact fun h => (hcontain h).elim

/-- The symmetric left-multiplication image has the same full-versus-one-less
dimension dichotomy. -/
theorem m3_finrank_range_leftMul_domRestrict_ker_dichotomy
    {k : Type*} [Field k]
    (φ : Matrix (Fin 3) (Fin 3) k →ₗ[k] k) (hφ : φ ≠ 0)
    (B : Matrix (Fin 3) (Fin 3) k) :
    ((LinearMap.ker (mulLeftLinearMap (Fin 3) k B) ≤ LinearMap.ker φ) ∧
        Module.finrank k (LinearMap.range
          ((mulLeftLinearMap (Fin 3) k B).domRestrict (LinearMap.ker φ))) + 1 =
          3 * B.rank) ∨
      (¬ LinearMap.ker (mulLeftLinearMap (Fin 3) k B) ≤ LinearMap.ker φ) ∧
        Module.finrank k (LinearMap.range
          ((mulLeftLinearMap (Fin 3) k B).domRestrict (LinearMap.ker φ))) =
          3 * B.rank := by
  simpa only [finrank_range_mulLeftLinearMap] using
    finrank_range_domRestrict_ker_dichotomy (mulLeftLinearMap (Fin 3) k B) φ hφ

/-- The one-dimensional loss for a left-multiplication hyperplane image occurs
if and only if the multiplication kernel lies in the defining hyperplane. -/
theorem m3_finrank_range_leftMul_domRestrict_add_one_iff
    {k : Type*} [Field k]
    (φ : Matrix (Fin 3) (Fin 3) k →ₗ[k] k) (hφ : φ ≠ 0)
    (B : Matrix (Fin 3) (Fin 3) k) :
    Module.finrank k (LinearMap.range
        ((mulLeftLinearMap (Fin 3) k B).domRestrict (LinearMap.ker φ))) + 1 =
        3 * B.rank ↔
      LinearMap.ker (mulLeftLinearMap (Fin 3) k B) ≤ LinearMap.ker φ := by
  rcases m3_finrank_range_leftMul_domRestrict_ker_dichotomy φ hφ B with
    ⟨hcontain, hdim⟩ | ⟨hcontain, hdim⟩
  · exact ⟨fun _ => hcontain, fun _ => hdim⟩
  · constructor
    · intro hloss
      exfalso
      rw [hdim] at hloss
      omega
    · exact fun h => (hcontain h).elim

/-- The diagonal matrix with only its first diagonal entry nonzero has
rank one over every field. -/
private theorem m3_rank_diagonal_one_zero_zero {k : Type*} [Field k] :
    (Matrix.diagonal ![(1 : k), 0, 0]).rank = 1 := by
  classical
  rw [Matrix.rank_diagonal]
  let e : {i : Fin 3 // (![1, 0, 0] : Fin 3 → k) i ≠ 0} ≃ Fin 1 :=
    { toFun := fun _ => 0
      invFun := fun _ => ⟨0, by simp⟩
      left_inv := by
        rintro ⟨i, hi⟩
        apply Subtype.ext
        fin_cases i
        · rfl
        · simp at hi
        · simp at hi
      right_inv := by
        intro i
        fin_cases i
        rfl }
  exact Fintype.card_congr e

/-- Ground truth for the exceptional right-multiplication case: restricting
`A ↦ A * diag(1,0,0)` by the equation `A₀₀ = 0` leaves a two-dimensional
image. -/
example {k : Type*} [Field k] :
    let B : Matrix (Fin 3) (Fin 3) k := Matrix.diagonal ![1, 0, 0]
    let φ := m3MatrixForm (Matrix.diagonal ![(1 : k), 0, 0])
    LinearMap.ker (matrixRightMul B) ≤ LinearMap.ker φ ∧
      Module.finrank k (LinearMap.range
        ((matrixRightMul B).domRestrict (LinearMap.ker φ))) = 2 := by
  classical
  dsimp only
  let B : Matrix (Fin 3) (Fin 3) k := Matrix.diagonal ![1, 0, 0]
  let C : Matrix (Fin 3) (Fin 3) k := Matrix.diagonal ![1, 0, 0]
  let φ := m3MatrixForm C
  have hφ : φ ≠ 0 := by
    intro hzero
    have hcoeff : m3DualMatrix φ = 0 :=
      (m3DualMatrix_eq_zero_iff φ).mpr hzero
    rw [m3DualMatrix_m3MatrixForm] at hcoeff
    have hentry := congrFun (congrFun hcoeff 0) 0
    norm_num [C] at hentry
  have hrank : B.rank = 1 := by
    simpa only [B] using m3_rank_diagonal_one_zero_zero (k := k)
  have hcontain : LinearMap.ker (matrixRightMul B) ≤ LinearMap.ker φ := by
    rw [ker_matrixRightMul_le_ker_iff_m3DualMatrix_mem_range]
    refine ⟨C, ?_⟩
    rw [m3DualMatrix_m3MatrixForm]
    change C * Bᵀ = C
    dsimp only [B]
    rw [Matrix.diagonal_transpose]
    ext i j
    rw [Matrix.mul_diagonal]
    dsimp only [C]
    fin_cases i <;> fin_cases j <;> simp
  refine ⟨hcontain, ?_⟩
  rcases m3_finrank_range_rightMul_domRestrict_ker_dichotomy φ hφ B with
    ⟨_, hdim⟩ | ⟨hnot, _⟩
  · rw [hrank] at hdim
    norm_num at hdim
    have hlocal : Module.finrank k (LinearMap.range
        ((matrixRightMul B).domRestrict (LinearMap.ker φ))) = 2 := by
      omega
    simpa only [B, C, φ] using hlocal
  · exact (hnot hcontain).elim

/-- Ground truth for a nonexceptional right-multiplication case: the equation
`A₀₁ = 0` does not constrain the surviving first column, so the image remains
three-dimensional. -/
example {k : Type*} [Field k] :
    let B : Matrix (Fin 3) (Fin 3) k := Matrix.diagonal ![1, 0, 0]
    let φ := m3MatrixForm !![(0 : k), 1, 0; 0, 0, 0; 0, 0, 0]
    (¬ LinearMap.ker (matrixRightMul B) ≤ LinearMap.ker φ) ∧
      Module.finrank k (LinearMap.range
        ((matrixRightMul B).domRestrict (LinearMap.ker φ))) = 3 := by
  classical
  dsimp only
  let B : Matrix (Fin 3) (Fin 3) k := Matrix.diagonal ![1, 0, 0]
  let C : Matrix (Fin 3) (Fin 3) k := !![0, 1, 0; 0, 0, 0; 0, 0, 0]
  let φ := m3MatrixForm C
  have hφ : φ ≠ 0 := by
    intro hzero
    have hcoeff : m3DualMatrix φ = 0 :=
      (m3DualMatrix_eq_zero_iff φ).mpr hzero
    rw [m3DualMatrix_m3MatrixForm] at hcoeff
    have hentry := congrFun (congrFun hcoeff 0) 1
    norm_num [C] at hentry
  have hrank : B.rank = 1 := by
    simpa only [B] using m3_rank_diagonal_one_zero_zero (k := k)
  have hnot : ¬ LinearMap.ker (matrixRightMul B) ≤ LinearMap.ker φ := by
    rw [ker_matrixRightMul_le_ker_iff_m3DualMatrix_mem_range]
    rintro ⟨D, hD⟩
    rw [m3DualMatrix_m3MatrixForm] at hD
    change D * Bᵀ = C at hD
    have hentry := congrFun (congrFun hD 0) 1
    dsimp only [B] at hentry
    rw [Matrix.diagonal_transpose, Matrix.mul_diagonal] at hentry
    norm_num [C] at hentry
  refine ⟨hnot, ?_⟩
  rcases m3_finrank_range_rightMul_domRestrict_ker_dichotomy φ hφ B with
    ⟨hcontain, _⟩ | ⟨_, hdim⟩
  · exact (hnot hcontain).elim
  · rw [hrank] at hdim
    norm_num at hdim ⊢
    exact hdim

/-- Ground truth for both branches of the symmetric left-multiplication
statement: `A₀₀ = 0` is exceptional, whereas `A₁₀ = 0` is not. -/
example {k : Type*} [Field k] :
    let B : Matrix (Fin 3) (Fin 3) k := Matrix.diagonal ![1, 0, 0]
    let φ₀ := m3MatrixForm (Matrix.diagonal ![(1 : k), 0, 0])
    let φ₁ := m3MatrixForm !![(0 : k), 0, 0; 1, 0, 0; 0, 0, 0]
    Module.finrank k (LinearMap.range
        ((mulLeftLinearMap (Fin 3) k B).domRestrict (LinearMap.ker φ₀))) = 2 ∧
      Module.finrank k (LinearMap.range
        ((mulLeftLinearMap (Fin 3) k B).domRestrict (LinearMap.ker φ₁))) = 3 := by
  classical
  dsimp only
  let B : Matrix (Fin 3) (Fin 3) k := Matrix.diagonal ![1, 0, 0]
  let C₀ : Matrix (Fin 3) (Fin 3) k := Matrix.diagonal ![1, 0, 0]
  let C₁ : Matrix (Fin 3) (Fin 3) k := !![0, 0, 0; 1, 0, 0; 0, 0, 0]
  let φ₀ := m3MatrixForm C₀
  let φ₁ := m3MatrixForm C₁
  have hφ₀ : φ₀ ≠ 0 := by
    intro hzero
    have hcoeff : m3DualMatrix φ₀ = 0 :=
      (m3DualMatrix_eq_zero_iff φ₀).mpr hzero
    rw [m3DualMatrix_m3MatrixForm] at hcoeff
    have hentry := congrFun (congrFun hcoeff 0) 0
    norm_num [C₀] at hentry
  have hφ₁ : φ₁ ≠ 0 := by
    intro hzero
    have hcoeff : m3DualMatrix φ₁ = 0 :=
      (m3DualMatrix_eq_zero_iff φ₁).mpr hzero
    rw [m3DualMatrix_m3MatrixForm] at hcoeff
    have hentry := congrFun (congrFun hcoeff 1) 0
    norm_num [C₁] at hentry
  have hrank : B.rank = 1 := by
    simpa only [B] using m3_rank_diagonal_one_zero_zero (k := k)
  have hcontain : LinearMap.ker (mulLeftLinearMap (Fin 3) k B) ≤ LinearMap.ker φ₀ := by
    rw [ker_mulLeftLinearMap_le_ker_iff_m3DualMatrix_mem_range]
    refine ⟨C₀, ?_⟩
    rw [m3DualMatrix_m3MatrixForm]
    change Bᵀ * C₀ = C₀
    dsimp only [B]
    rw [Matrix.diagonal_transpose]
    ext i j
    rw [Matrix.diagonal_mul]
    dsimp only [C₀]
    fin_cases i <;> fin_cases j <;> simp
  have hnot : ¬ LinearMap.ker (mulLeftLinearMap (Fin 3) k B) ≤ LinearMap.ker φ₁ := by
    rw [ker_mulLeftLinearMap_le_ker_iff_m3DualMatrix_mem_range]
    rintro ⟨D, hD⟩
    rw [m3DualMatrix_m3MatrixForm] at hD
    change Bᵀ * D = C₁ at hD
    have hentry := congrFun (congrFun hD 1) 0
    dsimp only [B] at hentry
    rw [Matrix.diagonal_transpose, Matrix.diagonal_mul] at hentry
    norm_num [C₁] at hentry
  constructor
  · rcases m3_finrank_range_leftMul_domRestrict_ker_dichotomy φ₀ hφ₀ B with
      ⟨_, hdim⟩ | ⟨hcontra, _⟩
    · rw [hrank] at hdim
      norm_num at hdim
      have hlocal : Module.finrank k (LinearMap.range
          ((mulLeftLinearMap (Fin 3) k B).domRestrict (LinearMap.ker φ₀))) = 2 := by
        omega
      simpa only [B, C₀, φ₀] using hlocal
    · exact (hcontra hcontain).elim
  · rcases m3_finrank_range_leftMul_domRestrict_ker_dichotomy φ₁ hφ₁ B with
      ⟨hcontra, _⟩ | ⟨_, hdim⟩
    · exact (hnot hcontra).elim
    · rw [hrank] at hdim
      norm_num at hdim ⊢
      exact hdim

#check @finrank_range_domRestrict_ker_dichotomy
#check @finrank_range_mulLeftLinearMap
#check @m3MatrixForm
#check @m3DualMatrix_m3MatrixForm
#check @m3DualMatrix_comp_matrixRightMul
#check @m3DualMatrix_comp_mulLeftLinearMap
#check @ker_matrixRightMul_le_ker_iff_m3DualMatrix_mem_range
#check @ker_mulLeftLinearMap_le_ker_iff_m3DualMatrix_mem_range
#check @m3_finrank_range_rightMul_domRestrict_ker_dichotomy
#check @m3_finrank_range_rightMul_domRestrict_add_one_iff
#check @m3_finrank_range_leftMul_domRestrict_ker_dichotomy
#check @m3_finrank_range_leftMul_domRestrict_add_one_iff

#print axioms finrank_range_domRestrict_ker_dichotomy
#print axioms finrank_range_mulLeftLinearMap
#print axioms m3DualMatrix_m3MatrixForm
#print axioms m3DualMatrix_comp_matrixRightMul
#print axioms m3DualMatrix_comp_mulLeftLinearMap
#print axioms ker_matrixRightMul_le_ker_iff_m3DualMatrix_mem_range
#print axioms ker_mulLeftLinearMap_le_ker_iff_m3DualMatrix_mem_range
#print axioms m3_finrank_range_rightMul_domRestrict_ker_dichotomy
#print axioms m3_finrank_range_rightMul_domRestrict_add_one_iff
#print axioms m3_finrank_range_leftMul_domRestrict_ker_dichotomy
#print axioms m3_finrank_range_leftMul_domRestrict_add_one_iff

end BilinearComplexity
