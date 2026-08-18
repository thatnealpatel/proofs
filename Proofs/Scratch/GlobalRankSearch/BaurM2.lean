/-
  Scratch/GlobalRankSearch/BaurM2 — the field-uniform Baur lower bound for
  two-by-two matrix multiplication.

  Coordinates are row-major in the first two tensor modes.  The third tensor
  mode of `matMulTensor` is packed as `(output column, output row)`, so the
  output factor is explicitly transposed by `m2Output` below.
-/
import BilinearComplexity.RankCalculus
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Rank

set_option autoImplicit false

namespace BilinearComplexity

open scoped Matrix

/-- Row-major equivalence between pairs of two-valued indices and four coordinates. -/
def m2Equiv : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv

/-- Unpack four row-major coordinates as a two-by-two matrix. -/
def m2OfVec {k : Type*} (x : Fin 4 → k) : Matrix (Fin 2) (Fin 2) k :=
  fun i j => x (m2Equiv (i, j))

/-- Pack a two-by-two matrix in row-major order. -/
def m2ToVec {k : Type*} (A : Matrix (Fin 2) (Fin 2) k) : Fin 4 → k :=
  fun x => A (m2Equiv.symm x).1 (m2Equiv.symm x).2

/-- Interpret a third-mode factor as an output matrix.  The swapped pair is
required because `matMulTensor` packs its third mode as `(column,row)`. -/
def m2Output {k : Type*} (w : Fin 4 → k) : Matrix (Fin 2) (Fin 2) k :=
  fun i l => w (m2Equiv (l, i))

/-- Ground check that `m2Equiv` uses row-major order. -/
example :
    m2Equiv ((0, 0) : Fin 2 × Fin 2) = 0 ∧
      m2Equiv ((0, 1) : Fin 2 × Fin 2) = 1 ∧
      m2Equiv ((1, 0) : Fin 2 × Fin 2) = 2 ∧
      m2Equiv ((1, 1) : Fin 2 × Fin 2) = 3 := by
  decide

/-- Ground check for row-major coordinate unpacking. -/
example : m2OfVec (k := ℚ) ![0, 1, 2, 3] = !![0, 1; 2, 3] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Ground check for row-major matrix packing. -/
example : m2ToVec (k := ℚ) !![0, 1; 2, 3] = ![0, 1, 2, 3] := by
  funext x
  fin_cases x <;> rfl

/-- Ground check for the transposed third-mode output convention. -/
example : m2Output (k := ℚ) ![0, 1, 2, 3] = !![0, 2; 1, 3] := by
  ext i l
  fin_cases i <;> fin_cases l <;> rfl

/-- A decomposition term's first- or second-mode linear functional. -/
def m2Form {k : Type*} [CommSemiring k] (u : Fin 4 → k) :
    Matrix (Fin 2) (Fin 2) k →ₗ[k] k :=
  { toFun := fun A => ∑ x, u x * m2ToVec A x
    map_add' := by
      intro A B
      simp only [m2ToVec, Matrix.add_apply, mul_add, Finset.sum_add_distrib]
    map_smul' := by
      intro c A
      simp [m2ToVec, Finset.mul_sum, mul_left_comm] }

/-- Evaluation of `m2Form` is the coordinate-weighted finite sum. -/
@[simp]
theorem m2Form_apply {k : Type*} [CommSemiring k] (u : Fin 4 → k)
    (A : Matrix (Fin 2) (Fin 2) k) :
    m2Form u A = ∑ x, u x * m2ToVec A x := rfl

/-- Packing and then unpacking a two-by-two matrix changes no entry. -/
theorem m2OfVec_toVec {k : Type*} (A : Matrix (Fin 2) (Fin 2) k) :
    m2OfVec (m2ToVec A) = A := by
  ext i j
  simp [m2OfVec, m2ToVec]

/-- Unpacking and then packing four coordinates changes no coordinate. -/
theorem m2ToVec_ofVec {k : Type*} (x : Fin 4 → k) :
    m2ToVec (m2OfVec x) = x := by
  funext q
  simp [m2OfVec, m2ToVec]

/-- Exact coordinate bridge from an `r`-triad decomposition of
`matMulTensor` to an `r`-product bilinear matrix-multiplication algorithm.
The use of `m2Output` records the third-mode transpose rather than hiding it
in a simplifier step. -/
theorem rankLE_matMulTensor_two_to_bilinear {k : Type*} [Field k]
    {r : ℕ} (h : RankLE (matMulTensor k 2 2 2) r) :
    ∃ (α β : Fin r → Matrix (Fin 2) (Fin 2) k →ₗ[k] k)
      (C : Fin r → Matrix (Fin 2) (Fin 2) k),
      ∀ A B i l, (A * B) i l = ∑ s, α s A * β s B * C s i l := by
  classical
  obtain ⟨u, v, w, hdecomp⟩ := h
  refine ⟨fun s => m2Form (u s), fun s => m2Form (v s),
    fun s => m2Output (w s), ?_⟩
  intro A B i l
  simp only [Matrix.mul_apply, m2Form_apply, m2Output]
  change (∑ j, A i j * B j l) =
    ∑ s, (∑ x, u s x * m2ToVec A x) * (∑ y, v s y * m2ToVec B y) *
      w s (m2Equiv (l, i))
  calc
    (∑ j, A i j * B j l) =
        ∑ p : Fin 2 × Fin 2, ∑ q : Fin 2 × Fin 2,
          A p.1 p.2 * B q.1 q.2 * matMulTensor k 2 2 2 (m2Equiv p)
            (m2Equiv q) (m2Equiv (l, i)) := by
              simp only [Fintype.sum_prod_type]
              fin_cases i <;> fin_cases l <;>
                simp [Fin.sum_univ_two, matMulTensor_apply, m2Equiv]
    _ = ∑ p : Fin 2 × Fin 2, ∑ q : Fin 2 × Fin 2,
          A p.1 p.2 * B q.1 q.2 *
            (∑ s, u s (m2Equiv p) * v s (m2Equiv q) *
              w s (m2Equiv (l, i))) := by
              apply Finset.sum_congr rfl
              intro p _
              apply Finset.sum_congr rfl
              intro q _
              rw [hdecomp]
    _ = ∑ s, (∑ p : Fin 2 × Fin 2, u s (m2Equiv p) * A p.1 p.2) *
          (∑ q : Fin 2 × Fin 2, v s (m2Equiv q) * B q.1 q.2) *
            w s (m2Equiv (l, i)) := by
              calc
                (∑ p, ∑ q, A p.1 p.2 * B q.1 q.2 *
                    (∑ s, u s (m2Equiv p) * v s (m2Equiv q) * w s (m2Equiv (l, i)))) =
                    ∑ p, ∑ q, ∑ s,
                      A p.1 p.2 * B q.1 q.2 *
                        (u s (m2Equiv p) * v s (m2Equiv q) * w s (m2Equiv (l, i))) := by
                  simp only [Finset.mul_sum]
                _ = ∑ q, ∑ p, ∑ s,
                      A p.1 p.2 * B q.1 q.2 *
                        (u s (m2Equiv p) * v s (m2Equiv q) * w s (m2Equiv (l, i))) :=
                  Finset.sum_comm
                _ = ∑ q, ∑ s, ∑ p,
                      A p.1 p.2 * B q.1 q.2 *
                        (u s (m2Equiv p) * v s (m2Equiv q) * w s (m2Equiv (l, i))) := by
                  apply Finset.sum_congr rfl
                  intro q _
                  exact Finset.sum_comm
                _ = ∑ s, ∑ q, ∑ p,
                      A p.1 p.2 * B q.1 q.2 *
                        (u s (m2Equiv p) * v s (m2Equiv q) * w s (m2Equiv (l, i))) :=
                  Finset.sum_comm
                _ = ∑ s, ∑ p, ∑ q,
                      A p.1 p.2 * B q.1 q.2 *
                        (u s (m2Equiv p) * v s (m2Equiv q) * w s (m2Equiv (l, i))) := by
                  apply Finset.sum_congr rfl
                  intro s _
                  exact Finset.sum_comm
                _ = ∑ s, (∑ p, u s (m2Equiv p) * A p.1 p.2) *
                      (∑ q, v s (m2Equiv q) * B q.1 q.2) * w s (m2Equiv (l, i)) := by
                  simp only [Finset.sum_mul, Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro s _
                  rw [Finset.sum_comm]
                  apply Finset.sum_congr rfl
                  intro q _
                  apply Finset.sum_congr rfl
                  intro p _
                  ring
    _ = ∑ s, (∑ x : Fin 4, u s x * m2ToVec A x) *
          (∑ y : Fin 4, v s y * m2ToVec B y) * w s (m2Equiv (l, i)) := by
            apply Finset.sum_congr rfl
            intro s _
            have hu : (∑ p : Fin 2 × Fin 2, u s (m2Equiv p) * A p.1 p.2) =
                ∑ x : Fin 4, u s x * m2ToVec A x := by
              calc
                _ = ∑ p : Fin 2 × Fin 2,
                    u s (m2Equiv p) * m2ToVec A (m2Equiv p) := by simp [m2ToVec]
                _ = _ := Equiv.sum_comp m2Equiv
                  (fun x : Fin 4 => u s x * m2ToVec A x)
            have hv : (∑ q : Fin 2 × Fin 2, v s (m2Equiv q) * B q.1 q.2) =
                ∑ y : Fin 4, v s y * m2ToVec B y := by
              calc
                _ = ∑ q : Fin 2 × Fin 2,
                    v s (m2Equiv q) * m2ToVec B (m2Equiv q) := by simp [m2ToVec]
                _ = _ := Equiv.sum_comp m2Equiv
                  (fun y : Fin 4 => v s y * m2ToVec B y)
            rw [hu, hv]

/-- If fewer linear functionals are imposed than the dimension of a finite-dimensional
space, their common kernel contains a nonzero vector. -/
theorem exists_ne_zero_in_common_kernel {k V ι : Type*} [Field k]
    [AddCommGroup V] [Module k V] [Module.Finite k V] [Fintype ι]
    (f : ι → V →ₗ[k] k) (hcard : Fintype.card ι < Module.finrank k V) :
    ∃ x, x ≠ 0 ∧ ∀ i, f i x = 0 := by
  let F : V →ₗ[k] (ι → k) := LinearMap.pi f
  by_contra hn
  have hz : ∀ x, (∀ i, f i x = 0) → x = 0 := by
    intro x hx
    by_contra hx0
    exact hn ⟨x, hx0, hx⟩
  have hF : Function.Injective F := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hz
    intro i
    have hi := congrFun hxy i
    simpa [F] using sub_eq_zero.mpr hi
  have hdim := LinearMap.finrank_le_finrank_of_injective hF
  rw [Module.finrank_pi] at hdim
  omega

/-- The common-kernel hypotheses are jointly satisfiable in dimension two. -/
example : ∃ x : Fin 2 → ℚ, x ≠ 0 ∧
    ∀ _i : Fin 1, (0 : (Fin 2 → ℚ) →ₗ[ℚ] ℚ) x = 0 := by
  exact exists_ne_zero_in_common_kernel
    (fun _ : Fin 1 => (0 : (Fin 2 → ℚ) →ₗ[ℚ] ℚ)) (by simp)

/-- Independent linear functionals can interpolate arbitrary prescribed values. -/
theorem linearIndependent_evaluation_surjective {k V ι : Type*} [Field k]
    [AddCommGroup V] [Module k V] [Module.Finite k V] [Fintype ι]
    (f : ι → V →ₗ[k] k) (hf : LinearIndependent k f) :
    Function.Surjective (LinearMap.pi f) := by
  intro y
  let S := Submodule.span k (Set.range f)
  let g0 : S →ₗ[k] k := (Finsupp.linearCombination k y).comp hf.repr
  obtain ⟨g, hg⟩ := LinearMap.exists_extend g0
  let x : V := (Module.evalEquiv k V).symm g
  refine ⟨x, ?_⟩
  funext i
  change f i x = y i
  have hmem : f i ∈ S := Submodule.subset_span (Set.mem_range_self i)
  have hgi := LinearMap.congr_fun hg ⟨f i, hmem⟩
  change g (f i) = g0 ⟨f i, hmem⟩ at hgi
  have hxg : Module.Dual.eval k V x = g := (Module.evalEquiv k V).apply_symm_apply g
  have hxgi := LinearMap.congr_fun hxg (f i)
  rw [← Module.Dual.eval_apply k V x (f i), hxgi, hgi]
  simp [g0, LinearIndependent.repr_eq_single hf i ⟨f i, hmem⟩ rfl]

/-- The interpolation hypotheses are jointly satisfiable for the identity functional. -/
example : Function.Surjective
    (LinearMap.pi (fun _ : Fin 1 => (LinearMap.id : ℚ →ₗ[ℚ] ℚ))) := by
  apply linearIndependent_evaluation_surjective
  rw [linearIndependent_unique_iff]
  intro hzero
  have hvalue := LinearMap.congr_fun hzero (1 : ℚ)
  norm_num at hvalue

/-- A finite family contains an indexed independent subfamily of every size
not exceeding the dimension of its span.  The embedding retains original
source indices, including in the presence of duplicate or zero vectors. -/
theorem exists_indexed_linearIndependent_of_le_finrank_span
    {k V ι : Type*} [Field k] [AddCommGroup V] [Module k V] [Fintype ι]
    (f : ι → V) (n : ℕ)
    (hn : n ≤ Module.finrank k (Submodule.span k (Set.range f))) :
    ∃ e : Fin n → ι, Function.Injective e ∧ LinearIndependent k (f ∘ e) := by
  classical
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' k f
  letI : Fintype κ := Fintype.ofInjective a ha
  have hnκ : n ≤ Fintype.card κ := by
    rw [← finrank_span_eq_card hli, hspan]
    exact hn
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := Finset.univ) hnκ
  let eκ : Fin n → κ := fun i =>
    ((Fintype.equivFinOfCardEq (α := s) (by simpa using hs)).symm i).val
  have heκ : Function.Injective eκ := by
    intro i j hij
    apply (Fintype.equivFinOfCardEq (α := s) (by simpa using hs)).symm.injective
    exact Subtype.ext hij
  refine ⟨a ∘ eκ, ha.comp heκ, ?_⟩
  exact hli.comp eκ heκ

/-- The indexed-subfamily hypotheses are jointly satisfiable for a singleton family. -/
example : ∃ e : Fin 1 → Fin 1, Function.Injective e ∧
    LinearIndependent ℚ ((fun _ : Fin 1 => (1 : ℚ)) ∘ e) := by
  apply exists_indexed_linearIndependent_of_le_finrank_span
    (fun _ : Fin 1 => (1 : ℚ)) 1
  simp

/-- The span of an indexed finite family has dimension at most the cardinality
of its source, without assuming that the family has distinct or nonzero terms. -/
theorem finrank_span_range_le_card {k V ι : Type*} [Field k]
    [AddCommGroup V] [Module k V] [Fintype ι] (f : ι → V) :
    Module.finrank k (Submodule.span k (Set.range f)) ≤ Fintype.card ι := by
  classical
  calc
    _ ≤ (Set.range f).toFinset.card := finrank_span_le_card (R := k) (Set.range f)
    _ = Fintype.card (Set.range f) := Set.toFinset_card _
    _ ≤ Fintype.card ι := Fintype.card_range_le f

/-- The matrix unit with its only nonzero entry in row `i`, column `j`. -/
def m2MatrixUnit {k : Type*} [Zero k] [One k] (i j : Fin 2) :
    Matrix (Fin 2) (Fin 2) k := fun p q => if p = i ∧ q = j then 1 else 0

/-- Nonempty ground check for the matrix-unit convention. -/
example : m2MatrixUnit (k := ℚ) 1 0 = !![0, 0; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- A nonzero principal right ideal of `M₂(k)` cannot be contained in a
proper principal left ideal.  Concretely, if every `aY` is some `Xb`, then
`b` is invertible. -/
theorem m2_isUnit_of_rightIdeal_le_leftIdeal {k : Type*} [Field k]
    {a b : Matrix (Fin 2) (Fin 2) k} (ha : a ≠ 0)
    (hcontain : ∀ Y, ∃ X, a * Y = X * b) : IsUnit b := by
  classical
  obtain ⟨i, j, hij⟩ : ∃ i j, a i j ≠ 0 := by
    by_contra h
    push Not at h
    apply ha
    ext p q
    exact h p q
  choose X hX using fun l : Fin 2 => hcontain (m2MatrixUnit j l)
  let R : Matrix (Fin 2) (Fin 2) k := fun l q => X l i q / a i j
  have hleft : R * b = 1 := by
    ext l q
    have heq := congrFun (congrFun (hX l) i) q
    simp only [Matrix.mul_apply] at heq ⊢
    change (∑ x, X l i x / a i j * b x q) = if l = q then 1 else 0
    have hrow : (∑ x, X l i x * b x q) =
        a i j * (if q = l then 1 else 0) := by
      rw [← heq]
      fin_cases i <;> fin_cases j <;> fin_cases l <;> fin_cases q <;>
        simp [m2MatrixUnit]
    have hsum : (∑ x, X l i x / a i j * b x q) =
        (∑ x, X l i x * b x q) / a i j := by
      rw [div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [hsum, hrow]
    by_cases hlq : l = q
    · subst q
      simp [hij]
    · simp [hlq, Ne.symm hlq]
  rw [Matrix.isUnit_iff_isUnit_det]
  have hdet : R.det * b.det = 1 := by
    rw [← Matrix.det_mul, hleft, Matrix.det_one]
  exact IsUnit.of_mul_eq_one R.det (by simpa [mul_comm] using hdet)

/-- Principal-ideal containment is jointly satisfiable for the identity matrix. -/
example : IsUnit (1 : Matrix (Fin 2) (Fin 2) ℚ) := by
  apply m2_isUnit_of_rightIdeal_le_leftIdeal (a := 1)
  · exact one_ne_zero
  · intro Y
    exact ⟨Y, by simp⟩

/-- Right multiplication by a fixed two-by-two matrix, as a linear map. -/
def m2RightMul {k : Type*} [CommSemiring k] (b : Matrix (Fin 2) (Fin 2) k) :
    Matrix (Fin 2) (Fin 2) k →ₗ[k] Matrix (Fin 2) (Fin 2) k :=
  { toFun := fun X => X * b
    map_add' := fun X Y => Matrix.add_mul X Y b
    map_smul' := fun c X => Matrix.smul_mul c X b }

/-- Evaluation formula for right multiplication. -/
theorem m2RightMul_apply {k : Type*} [CommSemiring k]
    (b X : Matrix (Fin 2) (Fin 2) k) : m2RightMul b X = X * b := rfl

/-- Every nonzero principal left ideal of `M₂(k)` has dimension at least two. -/
theorem two_le_finrank_range_m2RightMul {k : Type*} [Field k]
    {b : Matrix (Fin 2) (Fin 2) k} (hb : b ≠ 0) :
    2 ≤ Module.finrank k (LinearMap.range (m2RightMul b)) := by
  classical
  obtain ⟨i, j, hij⟩ : ∃ i j, b i j ≠ 0 := by
    by_contra h
    push Not at h
    apply hb
    ext p q
    exact h p q
  let D : Fin 2 → Matrix (Fin 2) (Fin 2) k := fun l => m2MatrixUnit l i * b
  have hD1 : D 1 ≠ 0 := by
    intro hzero
    have hentry := congrFun (congrFun hzero 1) j
    simp [D, Matrix.mul_apply, m2MatrixUnit, hij] at hentry
  have hD10 : ∀ c : k, c • D 1 ≠ D 0 := by
    intro c heq
    have hentry := congrFun (congrFun heq 0) j
    simp [D, Matrix.mul_apply, m2MatrixUnit] at hentry
    exact hij hentry.symm
  let d : Fin 2 → LinearMap.range (m2RightMul b) := fun l =>
    ⟨D l, ⟨m2MatrixUnit l i, rfl⟩⟩
  have hd : LinearIndependent k d := by
    rw [linearIndependent_fin2]
    constructor
    · intro hzero
      apply hD1
      exact congrArg Subtype.val hzero
    · intro c heq
      apply hD10 c
      exact congrArg Subtype.val heq
  simpa using hd.fintype_card_le_finrank

/-- The right-multiplication range hypothesis is satisfiable for the identity matrix. -/
example : 2 ≤ Module.finrank ℚ
    (LinearMap.range (m2RightMul (1 : Matrix (Fin 2) (Fin 2) ℚ))) := by
  exact two_le_finrank_range_m2RightMul one_ne_zero

/-- The first-factor forms in any six-product algorithm for `M₂(k)` contain
three independent forms, retained at their original summand indices. -/
theorem exists_three_independent_first_forms {k : Type*} [Field k]
    (α β : Fin 6 → Matrix (Fin 2) (Fin 2) k →ₗ[k] k)
    (C : Fin 6 → Matrix (Fin 2) (Fin 2) k)
    (hmul : ∀ A B i l, (A * B) i l = ∑ s, α s A * β s B * C s i l) :
    ∃ e : Fin 3 → Fin 6, Function.Injective e ∧ LinearIndependent k (α ∘ e) := by
  classical
  let M := Matrix (Fin 2) (Fin 2) k
  let S := Submodule.span k (Set.range α)
  have hdimM : Module.finrank k M = 4 := by simp [M, Module.finrank_matrix]
  have hS : 4 ≤ Module.finrank k S := by
    by_contra hn
    have hlt : Module.finrank k S < 4 := by omega
    let B := Module.Basis.ofVectorSpace k S
    letI : Fintype (Module.Basis.ofVectorSpaceIndex k S) := Fintype.ofFinite _
    have hcardB : Fintype.card (Module.Basis.ofVectorSpaceIndex k S) <
        Module.finrank k M := by
      rw [hdimM, ← Module.finrank_eq_card_basis B]
      exact hlt
    obtain ⟨A, hA, hzero⟩ := exists_ne_zero_in_common_kernel
      (fun i => (B i).val) hcardB
    have hzS : ∀ φ : S, φ.val A = 0 := by
      intro φ
      let ev : S →ₗ[k] k :=
        { toFun := fun ψ => ψ.val A
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      have hev : ev = 0 := B.ext (fun i => hzero i)
      exact LinearMap.congr_fun hev φ
    have hzα : ∀ s, α s A = 0 := fun s =>
      hzS ⟨α s, Submodule.subset_span (Set.mem_range_self s)⟩
    apply hA
    ext i l
    have hmul_A_one := hmul A 1 i l
    simp only [Matrix.mul_one] at hmul_A_one
    rw [hmul_A_one]
    simp [hzα]
  apply exists_indexed_linearIndependent_of_le_finrank_span α 3
  exact le_trans (by omega) hS

/-- The final pivot in Baur's argument.  Once two output vectors lie in the
principal left ideal `M₂(k)b`, two restricted second forms interpolate on
that ideal, and a nonzero `a` kills the three complementary first forms,
the alleged six-product algorithm forces `aM₂(k) ⊆ M₂(k)b`; this contradicts
noninvertibility of `b`. -/
theorem baur_m2_final_pivot_impossible {k : Type*} [Field k]
    (α β : Fin 6 → Matrix (Fin 2) (Fin 2) k →ₗ[k] k)
    (C : Fin 6 → Matrix (Fin 2) (Fin 2) k)
    (hmul : ∀ A B i l, (A * B) i l = ∑ s, α s A * β s B * C s i l)
    (b : Matrix (Fin 2) (Fin 2) k) (hbunit : ¬ IsUnit b)
    (hC0 : ∃ D, C 0 = D * b)
    (hmatch : ∀ Y, ∃ X, β 1 (X * b) = β 1 Y ∧ β 2 (X * b) = β 2 Y)
    (a : Matrix (Fin 2) (Fin 2) k) (ha : a ≠ 0)
    (ha3 : α 3 a = 0) (ha4 : α 4 a = 0) (ha5 : α 5 a = 0) : False := by
  classical
  obtain ⟨D, hD⟩ := hC0
  apply hbunit
  apply m2_isUnit_of_rightIdeal_le_leftIdeal ha
  intro Y
  obtain ⟨X, hβ1, hβ2⟩ := hmatch Y
  let W := X * b
  let t := α 0 a * (β 0 Y - β 0 W)
  refine ⟨a * X + t • D, ?_⟩
  have hdiff : a * Y - a * W = t • C 0 := by
    ext i l
    rw [Matrix.sub_apply, Matrix.smul_apply, hmul a Y i l, hmul a W i l]
    simp only [Fin.sum_univ_six]
    change
      (α 0 a * β 0 Y * C 0 i l + α 1 a * β 1 Y * C 1 i l +
          α 2 a * β 2 Y * C 2 i l + α 3 a * β 3 Y * C 3 i l +
          α 4 a * β 4 Y * C 4 i l + α 5 a * β 5 Y * C 5 i l) -
        (α 0 a * β 0 W * C 0 i l + α 1 a * β 1 W * C 1 i l +
          α 2 a * β 2 W * C 2 i l + α 3 a * β 3 W * C 3 i l +
          α 4 a * β 4 W * C 4 i l + α 5 a * β 5 W * C 5 i l) =
        t * C 0 i l
    have hβ1' : β 1 W = β 1 Y := hβ1
    have hβ2' : β 2 W = β 2 Y := hβ2
    rw [hβ1', hβ2', ha3, ha4, ha5]
    simp only [zero_mul, add_zero]
    dsimp only [t]
    ring
  calc
    a * Y = a * W + t • C 0 := by
      rw [← hdiff]
      abel
    _ = a * (X * b) + t • (D * b) := by rw [hD]
    _ = (a * X + t • D) * b := by
      rw [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc]

/-- No six scalar products compute multiplication in `M₂(k)`, over any field.
The proof performs the two factor-family normalizations sequentially and only
then applies one final permutation of the original indexed summands. -/
theorem six_product_m2_impossible {k : Type*} [Field k]
    (α β : Fin 6 → Matrix (Fin 2) (Fin 2) k →ₗ[k] k)
    (C : Fin 6 → Matrix (Fin 2) (Fin 2) k)
    (hmul : ∀ A B i l, (A * B) i l = ∑ s, α s A * β s B * C s i l) : False := by
  classical
  obtain ⟨e, he, hαe⟩ := exists_three_independent_first_forms α β C hmul
  let I : Finset (Fin 6) := Finset.univ.image e
  have hcardI : I.card = 3 := by simp [I, Finset.card_image_of_injective _ he]
  let J := {s : Fin 6 // s ∉ I}
  letI : Fintype J := Fintype.ofFinite J
  have hcardJ : Fintype.card J = 3 := by
    rw [Fintype.card_subtype_compl]
    have hcoe : Fintype.card (↥I) = I.card := by simp
    rw [hcoe, hcardI]
    simp
  have hdimM : Module.finrank k (Matrix (Fin 2) (Fin 2) k) = 4 := by
    simp [Module.finrank_matrix]
  obtain ⟨b, hb, hbJ⟩ := exists_ne_zero_in_common_kernel
    (fun s : J => β s.val) (by rw [hcardJ, hdimM]; omega)
  have hb_out : ∀ s, s ∉ I → β s b = 0 := fun s hs => hbJ ⟨s, hs⟩
  let T := Submodule.span k (Set.range (C ∘ e))
  have hprod (X : Matrix (Fin 2) (Fin 2) k) :
      X * b = ∑ s, (α s X * β s b) • C s := by
    change (fun i l => (X * b) i l) = _
    funext i l
    exact hmul X b i l
  have hrange : LinearMap.range (m2RightMul b) ≤ T := by
    rintro Z ⟨X, rfl⟩
    change X * b ∈ T
    rw [hprod X]
    apply Submodule.sum_mem
    intro s _
    by_cases hs : s ∈ I
    · rw [Finset.mem_image] at hs
      obtain ⟨t, _, rfl⟩ := hs
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self t))
    · simp [hb_out s hs]
  have hfinT : Module.finrank k T ≤ 3 := by
    exact le_trans (finrank_span_range_le_card (k := k) (C ∘ e)) (by simp)
  have hbunit : ¬ IsUnit b := by
    intro hunit
    have hsurj : Function.Surjective (m2RightMul b) := by
      intro Y
      obtain ⟨u, hu⟩ := hunit
      refine ⟨Y * (↑(u⁻¹) : Matrix (Fin 2) (Fin 2) k), ?_⟩
      change (Y * (↑(u⁻¹) : Matrix (Fin 2) (Fin 2) k)) * b = Y
      rw [← hu, Matrix.mul_assoc]
      simp
    have htop : LinearMap.range (m2RightMul b) = ⊤ := LinearMap.range_eq_top.mpr hsurj
    have hmono := Submodule.finrank_mono hrange
    rw [htop] at hmono
    have hfour : 4 ≤ Module.finrank k T := by
      rw [← hdimM]
      simpa using hmono
    omega
  have hq : ∃ q : Fin 3, β (e q) b ≠ 0 := by
    by_contra hn
    push Not at hn
    have hβall : ∀ s, β s b = 0 := by
      intro s
      by_cases hs : s ∈ I
      · rw [Finset.mem_image] at hs
        obtain ⟨q, _, rfl⟩ := hs
        exact hn q
      · exact hb_out s hs
    apply hb
    ext i l
    have hmul_one_b := hmul 1 b i l
    simp only [Matrix.one_mul] at hmul_one_b
    rw [hmul_one_b]
    simp [hβall]
  obtain ⟨q, hβq⟩ := hq
  obtain ⟨A, hA⟩ := linearIndependent_evaluation_surjective (α ∘ e) hαe
    (fun t => if t = q then 1 else 0)
  have hAeval (t : Fin 3) : α (e t) A = if t = q then 1 else 0 := congrFun hA t
  have hAb : A * b = β (e q) b • C (e q) := by
    rw [hprod]
    rw [Finset.sum_eq_single (e q)]
    · rw [hAeval]
      simp
    · intro s _ hsneq
      by_cases hs : s ∈ I
      · rw [Finset.mem_image] at hs
        obtain ⟨t, _, ht⟩ := hs
        subst s
        have htq : t ≠ q := fun h => hsneq (congrArg e h)
        rw [hAeval]
        simp [htq]
      · simp [hb_out s hs]
    · simp
  have hCq : ∃ D, C (e q) = D * b := by
    refine ⟨(β (e q) b)⁻¹ • A, ?_⟩
    rw [Matrix.smul_mul, hAb]
    simp [hβq]
  let K := {s : Fin 6 // s ≠ e q}
  letI : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = 5 := by simp [K]
  have hsep : ∀ Y : Matrix (Fin 2) (Fin 2) k,
      (∀ s : K, β s.val Y = 0) → Y = 0 := by
    intro Y hYzero
    by_contra hY
    let U := Submodule.span k (Set.range (fun _ : Fin 1 => C (e q)))
    have hrangeY : LinearMap.range (m2RightMul Y) ≤ U := by
      rintro Z ⟨X, rfl⟩
      change X * Y ∈ U
      have hXY : X * Y = ∑ s, (α s X * β s Y) • C s := by
        change (fun i l => (X * Y) i l) = _
        funext i l
        exact hmul X Y i l
      rw [hXY]
      apply Submodule.sum_mem
      intro s _
      by_cases hs : s = e q
      · subst s
        exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self 0))
      · simp [hYzero ⟨s, hs⟩]
    have hfinU : Module.finrank k U ≤ 1 := by
      exact le_trans (finrank_span_range_le_card (k := k)
        (fun _ : Fin 1 => C (e q))) (by simp)
    have hmono := Submodule.finrank_mono hrangeY
    have htwo := two_le_finrank_range_m2RightMul hY
    omega
  let L := LinearMap.range (m2RightMul b)
  let fK : K → L →ₗ[k] k := fun s => (β s.val).domRestrict L
  have hsepL : ∀ W : L, (∀ s, fK s W = 0) → W = 0 := by
    intro W hW
    apply Subtype.ext
    apply hsep W.val
    exact hW
  have hspanK : 2 ≤ Module.finrank k (Submodule.span k (Set.range fK)) := by
    have hdimL : 2 ≤ Module.finrank k L := two_le_finrank_range_m2RightMul hb
    by_contra hn
    have hlt : Module.finrank k (Submodule.span k (Set.range fK)) < 2 := by omega
    let S := Submodule.span k (Set.range fK)
    have hltS : Module.finrank k S < 2 := hlt
    let B := Module.Basis.ofVectorSpace k S
    letI : Fintype (Module.Basis.ofVectorSpaceIndex k S) := Fintype.ofFinite _
    have hcardB : Fintype.card (Module.Basis.ofVectorSpaceIndex k S) <
        Module.finrank k L := by
      rw [← Module.finrank_eq_card_basis B]
      omega
    obtain ⟨W, hW, hzero⟩ := exists_ne_zero_in_common_kernel
      (fun i => (B i).val) hcardB
    have hzS : ∀ φ : S, φ.val W = 0 := by
      intro φ
      let ev : S →ₗ[k] k :=
        { toFun := fun ψ => ψ.val W
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      have hev : ev = 0 := B.ext (fun i => hzero i)
      exact LinearMap.congr_fun hev φ
    apply hW
    apply hsepL W
    intro s
    exact hzS ⟨fK s, Submodule.subset_span (Set.mem_range_self s)⟩
  obtain ⟨r, hr, hfr⟩ :=
    exists_indexed_linearIndependent_of_le_finrank_span fK 2 hspanK
  have hmatch : ∀ Y : Matrix (Fin 2) (Fin 2) k, ∃ X,
      β (r 0).val (X * b) = β (r 0).val Y ∧
      β (r 1).val (X * b) = β (r 1).val Y := by
    intro Y
    obtain ⟨W, hW⟩ := linearIndependent_evaluation_surjective (fK ∘ r) hfr
      (fun t => β (r t).val Y)
    obtain ⟨X, hX⟩ := W.property
    refine ⟨X, ?_, ?_⟩
    · have hW_zero := congrFun hW 0
      change β (r 0).val W.val = β (r 0).val Y at hW_zero
      rw [← hX] at hW_zero
      exact hW_zero
    · have hW_one := congrFun hW 1
      change β (r 1).val W.val = β (r 1).val Y at hW_one
      rw [← hX] at hW_one
      exact hW_one
  let P : Finset K := Finset.univ.image r
  have hcardP : P.card = 2 := by simp [P, Finset.card_image_of_injective _ hr]
  let R := {s : K // s ∉ P}
  letI : Fintype R := Fintype.ofFinite R
  have hcardR : Fintype.card R = 3 := by
    rw [Fintype.card_subtype_compl]
    have hcoe : Fintype.card (↥P) = P.card := by simp
    rw [hcoe, hcardP, hcardK]
  obtain ⟨a, ha, haR⟩ := exists_ne_zero_in_common_kernel
    (fun s : R => α s.val.val) (by rw [hcardR, hdimM]; omega)
  let tail : Fin 3 → R := (Fintype.equivFinOfCardEq (α := R) hcardR).symm
  have htail : Function.Injective tail :=
    (Fintype.equivFinOfCardEq (α := R) hcardR).symm.injective
  have hqr (t : Fin 2) : (r t).val ≠ e q := (r t).property
  have hqt (u : Fin 3) : (tail u).val.val ≠ e q := (tail u).val.property
  have hrt (t : Fin 2) (u : Fin 3) : (r t).val ≠ (tail u).val.val := by
    intro h
    apply (tail u).property
    rw [Finset.mem_image]
    exact ⟨t, Finset.mem_univ _, Subtype.ext h⟩
  have hr01 : (r 0).val ≠ (r 1).val := by
    intro h
    exact Fin.zero_ne_one (hr (Subtype.ext h))
  have ht01 : (tail 0).val.val ≠ (tail 1).val.val := by
    intro h
    exact Fin.zero_ne_one (htail (Subtype.ext (Subtype.ext h)))
  have ht02 : (tail 0).val.val ≠ (tail 2).val.val := by
    intro h
    exact (by decide : (0 : Fin 3) ≠ 2) (htail (Subtype.ext (Subtype.ext h)))
  have ht12 : (tail 1).val.val ≠ (tail 2).val.val := by
    intro h
    exact (by decide : (1 : Fin 3) ≠ 2) (htail (Subtype.ext (Subtype.ext h)))
  let σ : Fin 6 → Fin 6 := ![e q, (r 0).val, (r 1).val,
    (tail 0).val.val, (tail 1).val.val, (tail 2).val.val]
  have hσinj : Function.Injective σ := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;>
      simp only [σ] at hxy ⊢
    all_goals try { exact (hqr _ hxy.symm).elim }
    all_goals try { exact (hqr _ hxy).elim }
    all_goals try { exact (hqt _ hxy.symm).elim }
    all_goals try { exact (hqt _ hxy).elim }
    all_goals try { exact (hr01 hxy).elim }
    all_goals try { exact (hr01 hxy.symm).elim }
    all_goals try { exact (hrt _ _ hxy).elim }
    all_goals try { exact (hrt _ _ hxy.symm).elim }
    all_goals try { exact (ht01 hxy).elim }
    all_goals try { exact (ht01 hxy.symm).elim }
    all_goals try { exact (ht02 hxy).elim }
    all_goals try { exact (ht02 hxy.symm).elim }
    all_goals try { exact (ht12 hxy).elim }
    all_goals try { exact (ht12 hxy.symm).elim }
  let σe : Fin 6 ≃ Fin 6 := Equiv.ofBijective σ
    ((Fintype.bijective_iff_injective_and_card σ).mpr ⟨hσinj, rfl⟩)
  let α' : Fin 6 → Matrix (Fin 2) (Fin 2) k →ₗ[k] k := α ∘ σ
  let β' : Fin 6 → Matrix (Fin 2) (Fin 2) k →ₗ[k] k := β ∘ σ
  let C' : Fin 6 → Matrix (Fin 2) (Fin 2) k := C ∘ σ
  have hmul' : ∀ A B i l,
      (A * B) i l = ∑ s, α' s A * β' s B * C' s i l := by
    intro X Y i l
    rw [hmul X Y i l]
    exact (Equiv.sum_comp σe (fun s => α s X * β s Y * C s i l)).symm
  apply baur_m2_final_pivot_impossible α' β' C' hmul' b hbunit
    (by simpa [C', σ] using hCq)
    (by simpa [β', σ] using hmatch) a ha
  · simpa [α', σ] using haR (tail 0)
  · simpa [α', σ] using haR (tail 1)
  · simpa [α', σ] using haR (tail 2)

/-- A six-term `RankLE` decomposition of the two-by-two multiplication tensor
is impossible over every field. -/
theorem not_rankLE_matMulTensor_two_six (k : Type*) [Field k] :
    ¬ RankLE (matMulTensor k 2 2 2) 6 := by
  intro h
  obtain ⟨α, β, C, hmul⟩ := rankLE_matMulTensor_two_to_bilinear h
  exact six_product_m2_impossible α β C hmul

/-- The ordinary tensor rank of two-by-two matrix multiplication is at least
seven over every field. -/
theorem seven_le_rank_matMulTensor_field (k : Type*) [Field k] :
    7 ≤ rank (matMulTensor k 2 2 2) := by
  by_contra h
  apply not_rankLE_matMulTensor_two_six k
  apply rankLE_of_rank_le
  omega

/-- The coordinate bridge is nonvacuous: the schoolbook eight-term
`RankLE` decomposition supplies a bilinear algorithm over the rationals. -/
example : ∃ (α β : Fin 8 → Matrix (Fin 2) (Fin 2) ℚ →ₗ[ℚ] ℚ)
    (C : Fin 8 → Matrix (Fin 2) (Fin 2) ℚ),
    ∀ A B i l, (A * B) i l = ∑ s, α s A * β s B * C s i l := by
  exact rankLE_matMulTensor_two_to_bilinear (rankLE_matMulTensor ℚ 2 2 2)

#check @m2OfVec
#check @m2ToVec
#check @m2Output
#check @m2Form
#check @rankLE_matMulTensor_two_to_bilinear
#check @exists_ne_zero_in_common_kernel
#check @linearIndependent_evaluation_surjective
#check @exists_indexed_linearIndependent_of_le_finrank_span
#check @finrank_span_range_le_card
#check @exists_three_independent_first_forms
#check @m2_isUnit_of_rightIdeal_le_leftIdeal
#check @two_le_finrank_range_m2RightMul
#check @baur_m2_final_pivot_impossible
#check @six_product_m2_impossible
#check @not_rankLE_matMulTensor_two_six
#check @seven_le_rank_matMulTensor_field

#print axioms m2OfVec_toVec
#print axioms m2ToVec_ofVec
#print axioms m2RightMul_apply
#print axioms m2_isUnit_of_rightIdeal_le_leftIdeal
#print axioms two_le_finrank_range_m2RightMul
#print axioms baur_m2_final_pivot_impossible
#print axioms rankLE_matMulTensor_two_to_bilinear
#print axioms six_product_m2_impossible
#print axioms not_rankLE_matMulTensor_two_six
#print axioms seven_le_rank_matMulTensor_field

end BilinearComplexity
