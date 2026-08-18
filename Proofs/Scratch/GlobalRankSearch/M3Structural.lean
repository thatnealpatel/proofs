/-
  Scratch/GlobalRankSearch/M3Structural — field-uniform structural normalization
  for finite bilinear algorithms for three-by-three matrix multiplication.

  The active indices at `b` are those whose second form does not vanish at
  `b`.  The principal left ideal is `M₃(k)b = range (matrixRightMul b)`.
-/
import Scratch.GlobalRankSearch.BaurM2
import Scratch.GlobalRankSearch.MatrixRightIdeal
import Mathlib.LinearAlgebra.Matrix.Notation

set_option autoImplicit false

namespace BilinearComplexity

open scoped Matrix

/-- Indices active after evaluating a finite family of second forms at `b`. -/
noncomputable def m3ActiveSupport {k : Type*} [Semiring k] {r : ℕ}
    (β : Fin r → Matrix (Fin 3) (Fin 3) k →ₗ[k] k)
    (b : Matrix (Fin 3) (Fin 3) k) : Finset (Fin r) :=
  @Finset.filter (Fin r) (fun s => β s b ≠ 0)
    (fun _ => Classical.propDecidable _) Finset.univ

/-- Membership in the active support means precisely nonvanishing at `b`. -/
theorem mem_m3ActiveSupport_iff {k : Type*} [Semiring k] {r : ℕ}
    (β : Fin r → Matrix (Fin 3) (Fin 3) k →ₗ[k] k)
    (b : Matrix (Fin 3) (Fin 3) k) (s : Fin r) :
    s ∈ m3ActiveSupport β b ↔ β s b ≠ 0 := by
  classical
  simp [m3ActiveSupport]

/-- The span in the dual of `M₃(k)b` of all inactive restricted second forms.
The subtype retains duplicate and zero summands. -/
noncomputable def m3InactiveRestrictionSpan {k : Type*} [CommSemiring k] {r : ℕ}
    (β : Fin r → Matrix (Fin 3) (Fin 3) k →ₗ[k] k)
    (b : Matrix (Fin 3) (Fin 3) k) :
    Submodule k (LinearMap.range (matrixRightMul b) →ₗ[k] k) :=
  Submodule.span k (Set.range (fun s : {s : Fin r // s ∉ m3ActiveSupport β b} =>
    (β s.1).domRestrict (LinearMap.range (matrixRightMul b))))

/-- A nonempty zero family has empty active support, a nonempty inactive
index type, and bottom inactive restriction span. -/
example :
    let β := fun _ : Fin 1 =>
      (0 : Matrix (Fin 3) (Fin 3) ℚ →ₗ[ℚ] ℚ)
    m3ActiveSupport β (0 : Matrix (Fin 3) (Fin 3) ℚ) = ∅ ∧
      Nonempty {s : Fin 1 // s ∉ m3ActiveSupport β 0} ∧
      m3InactiveRestrictionSpan β (0 : Matrix (Fin 3) (Fin 3) ℚ) = ⊥ := by
  dsimp
  have hempty : m3ActiveSupport
      (fun _ : Fin 1 => (0 : Matrix (Fin 3) (Fin 3) ℚ →ₗ[ℚ] ℚ)) 0 = ∅ := by
    simp [m3ActiveSupport]
  refine ⟨hempty, ⟨⟨0, by simp [hempty]⟩⟩, ?_⟩
  rw [m3InactiveRestrictionSpan]
  have hrestricted : (fun s : {s : Fin 1 // s ∉
      m3ActiveSupport (fun _ : Fin 1 =>
        (0 : Matrix (Fin 3) (Fin 3) ℚ →ₗ[ℚ] ℚ)) 0} =>
      ((0 : Matrix (Fin 3) (Fin 3) ℚ →ₗ[ℚ] ℚ)).domRestrict
        (LinearMap.range (matrixRightMul 0))) = 0 := by
    funext s
    ext X
    rfl
  rw [hrestricted]
  simp

/-- Row-major equivalence between pairs of three-valued indices and nine coordinates. -/
def m3Equiv : Fin 3 × Fin 3 ≃ Fin 9 := finProdFinEquiv

/-- Pack a three-by-three matrix in row-major order. -/
def m3ToVec {k : Type*} (A : Matrix (Fin 3) (Fin 3) k) : Fin 9 → k :=
  fun x => A (m3Equiv.symm x).1 (m3Equiv.symm x).2

/-- Interpret a third-mode factor as an output matrix.  The swapped pair records
that `matMulTensor` packs its third mode as `(output column, output row)`. -/
def m3Output {k : Type*} (w : Fin 9 → k) : Matrix (Fin 3) (Fin 3) k :=
  fun i l => w (m3Equiv (l, i))

/-- A packed coefficient vector as a matrix linear functional. -/
def m3Form {k : Type*} [CommSemiring k] (u : Fin 9 → k) :
    Matrix (Fin 3) (Fin 3) k →ₗ[k] k :=
  { toFun := fun A => ∑ x, u x * m3ToVec A x
    map_add' := by intro A B; simp only [m3ToVec, Matrix.add_apply, mul_add,
      Finset.sum_add_distrib]
    map_smul' := by intro c A; simp [m3ToVec, Finset.mul_sum, mul_left_comm] }

/-- Ground checks for row-major input packing and transposed output unpacking. -/
example : m3ToVec (k := ℚ) !![0, 1, 2; 3, 4, 5; 6, 7, 8] =
    ![0, 1, 2, 3, 4, 5, 6, 7, 8] := by
  funext x
  fin_cases x <;> rfl

example : m3Output (k := ℚ) ![0, 1, 2, 3, 4, 5, 6, 7, 8] =
    !![0, 3, 6; 1, 4, 7; 2, 5, 8] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- A coefficient supported at row-major coordinate `(1, 1)` evaluates the
corresponding matrix entry. -/
example : m3Form (k := ℚ) ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    !![0, 1, 2; 3, 4, 5; 6, 7, 8] = 4 := by
  norm_num [m3Form, m3ToVec, m3Equiv, Fin.sum_univ_succ]
  rfl

/-- A `RankLE` decomposition of the packed `3 × 3` multiplication tensor gives
an ordinary bilinear matrix-multiplication algorithm with the correct output
transpose. -/
theorem rankLE_matMulTensor_three_to_bilinear {k : Type*} [Field k] {r : ℕ}
    (h : RankLE (matMulTensor k 3 3 3) r) :
    ∃ (α β : Fin r → Matrix (Fin 3) (Fin 3) k →ₗ[k] k)
      (C : Fin r → Matrix (Fin 3) (Fin 3) k),
      ∀ A B i l, (A * B) i l = ∑ s, α s A * β s B * C s i l := by
  classical
  obtain ⟨u, v, w, hdecomp⟩ := h
  refine ⟨fun s => m3Form (u s), fun s => m3Form (v s),
    fun s => m3Output (w s), ?_⟩
  intro A B i l
  simp only [Matrix.mul_apply, m3Form, m3Output]
  change (∑ j, A i j * B j l) =
    ∑ s, (∑ x, u s x * m3ToVec A x) * (∑ y, v s y * m3ToVec B y) *
      w s (m3Equiv (l, i))
  calc
    (∑ j, A i j * B j l) =
        ∑ p : Fin 3 × Fin 3, ∑ q : Fin 3 × Fin 3,
          A p.1 p.2 * B q.1 q.2 * matMulTensor k 3 3 3 (m3Equiv p)
            (m3Equiv q) (m3Equiv (l, i)) := by
              simp_rw [matMulTensor_apply]
              simp only [m3Equiv, Equiv.symm_apply_apply, mul_ite, mul_one, mul_zero]
              symm
              rw [Fintype.sum_prod_type]
              rw [Finset.sum_eq_single i]
              · simp only [Fintype.sum_prod_type]
                apply Finset.sum_congr rfl
                intro j _
                rw [Finset.sum_eq_single j]
                · rw [Finset.sum_eq_single l]
                  · simp
                  · intro q _ hq
                    simp [hq]
                  · simp
                · intro q _ hq
                  simp [Ne.symm hq]
                · simp
              · intro p _ hp
                have hip : i ≠ p := Ne.symm hp
                simp [hip]
              · simp
    _ = ∑ p : Fin 3 × Fin 3, ∑ q : Fin 3 × Fin 3,
          A p.1 p.2 * B q.1 q.2 *
            (∑ s, u s (m3Equiv p) * v s (m3Equiv q) * w s (m3Equiv (l, i))) := by
              apply Finset.sum_congr rfl
              intro p _
              apply Finset.sum_congr rfl
              intro q _
              rw [hdecomp]
    _ = ∑ s, (∑ p : Fin 3 × Fin 3, u s (m3Equiv p) * A p.1 p.2) *
          (∑ q : Fin 3 × Fin 3, v s (m3Equiv q) * B q.1 q.2) *
            w s (m3Equiv (l, i)) := by
              calc
                (∑ p, ∑ q, A p.1 p.2 * B q.1 q.2 *
                    (∑ s, u s (m3Equiv p) * v s (m3Equiv q) * w s (m3Equiv (l, i)))) =
                    ∑ p, ∑ q, ∑ s, A p.1 p.2 * B q.1 q.2 *
                      (u s (m3Equiv p) * v s (m3Equiv q) * w s (m3Equiv (l, i))) := by
                  simp only [Finset.mul_sum]
                _ = ∑ q, ∑ p, ∑ s, A p.1 p.2 * B q.1 q.2 *
                      (u s (m3Equiv p) * v s (m3Equiv q) * w s (m3Equiv (l, i))) :=
                  Finset.sum_comm
                _ = ∑ q, ∑ s, ∑ p, A p.1 p.2 * B q.1 q.2 *
                      (u s (m3Equiv p) * v s (m3Equiv q) * w s (m3Equiv (l, i))) := by
                  apply Finset.sum_congr rfl
                  intro q _
                  exact Finset.sum_comm
                _ = ∑ s, ∑ q, ∑ p, A p.1 p.2 * B q.1 q.2 *
                      (u s (m3Equiv p) * v s (m3Equiv q) * w s (m3Equiv (l, i))) :=
                  Finset.sum_comm
                _ = ∑ s, ∑ p, ∑ q, A p.1 p.2 * B q.1 q.2 *
                      (u s (m3Equiv p) * v s (m3Equiv q) * w s (m3Equiv (l, i))) := by
                  apply Finset.sum_congr rfl
                  intro s _
                  exact Finset.sum_comm
                _ = ∑ s, (∑ p, u s (m3Equiv p) * A p.1 p.2) *
                      (∑ q, v s (m3Equiv q) * B q.1 q.2) * w s (m3Equiv (l, i)) := by
                  simp only [Finset.sum_mul, Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro s _
                  rw [Finset.sum_comm]
                  apply Finset.sum_congr rfl
                  intro q _
                  apply Finset.sum_congr rfl
                  intro p _
                  ring
    _ = ∑ s, (∑ x : Fin 9, u s x * m3ToVec A x) *
          (∑ y : Fin 9, v s y * m3ToVec B y) * w s (m3Equiv (l, i)) := by
            apply Finset.sum_congr rfl
            intro s _
            have hu : (∑ p : Fin 3 × Fin 3, u s (m3Equiv p) * A p.1 p.2) =
                ∑ x : Fin 9, u s x * m3ToVec A x := by
              calc
                _ = ∑ p : Fin 3 × Fin 3,
                    u s (m3Equiv p) * m3ToVec A (m3Equiv p) := by simp [m3ToVec]
                _ = _ := Equiv.sum_comp m3Equiv
                  (fun x : Fin 9 => u s x * m3ToVec A x)
            have hv : (∑ q : Fin 3 × Fin 3, v s (m3Equiv q) * B q.1 q.2) =
                ∑ y : Fin 9, v s y * m3ToVec B y := by
              calc
                _ = ∑ q : Fin 3 × Fin 3,
                    v s (m3Equiv q) * m3ToVec B (m3Equiv q) := by simp [m3ToVec]
                _ = _ := Equiv.sum_comp m3Equiv
                  (fun y : Fin 9 => v s y * m3ToVec B y)
            rw [hu, hv]

/-- A matrix-unit convention valid in every positive size. -/
def squareMatrixUnit {k : Type*} [Zero k] [One k] {n : ℕ} (i j : Fin n) :
    Matrix (Fin n) (Fin n) k := fun p q => if p = i ∧ q = j then 1 else 0

/-- Ground check for the matrix-unit row/column orientation. -/
example : squareMatrixUnit (k := ℚ) (n := 3) 1 2 =
    !![0, 0, 0; 0, 0, 1; 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Matrix-ring simplicity in the orientation used by Baur interpolation:
if a nonzero matrix `a` satisfies `aMₙ(k) ⊆ Mₙ(k)b`, then `b` is a unit. -/
theorem matrix_isUnit_of_rightIdeal_le_leftIdeal {k : Type*} [Field k] {n : ℕ}
    (_hn : 0 < n) {a b : Matrix (Fin n) (Fin n) k} (ha : a ≠ 0)
    (hcontain : ∀ Y, ∃ X, a * Y = X * b) : IsUnit b := by
  classical
  obtain ⟨i, j, hij⟩ : ∃ i j, a i j ≠ 0 := by
    by_contra h
    push Not at h
    apply ha
    ext p q
    exact h p q
  choose X hX using fun l : Fin n => hcontain (squareMatrixUnit j l)
  let R : Matrix (Fin n) (Fin n) k := fun l q => X l i q / a i j
  have hleft : R * b = 1 := by
    ext l q
    have heq := congrFun (congrFun (hX l) i) q
    simp only [Matrix.mul_apply] at heq ⊢
    change (∑ x, X l i x / a i j * b x q) = if l = q then 1 else 0
    have hrow : (∑ x, X l i x * b x q) = a i j * (if q = l then 1 else 0) := by
      rw [← heq]
      simp only [squareMatrixUnit]
      rw [Finset.sum_eq_single j]
      · simp
      · intro x _ hx; simp [hx]
      · simp
    have hsum : (∑ x, X l i x / a i j * b x q) =
        (∑ x, X l i x * b x q) / a i j := by
      rw [div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [hsum, hrow]
    by_cases hlq : l = q
    · subst q; simp [hij]
    · simp [hlq, Ne.symm hlq]
  rw [Matrix.isUnit_iff_isUnit_det]
  have hdet : R.det * b.det = 1 := by rw [← Matrix.det_mul, hleft, Matrix.det_one]
  exact IsUnit.of_mul_eq_one R.det (by simpa [mul_comm] using hdet)

/-- The identity matrices give a concrete joint model of the hypotheses and
conclusion of matrix-ring simplicity in size three. -/
example :
    (1 : Matrix (Fin 3) (Fin 3) ℚ) ≠ 0 ∧
      (∀ Y, ∃ X, (1 : Matrix (Fin 3) (Fin 3) ℚ) * Y = X * 1) ∧
      IsUnit (1 : Matrix (Fin 3) (Fin 3) ℚ) := by
  simp

section Algorithm

variable {k : Type*} [Field k] {r : ℕ}
variable (α β : Fin r → Matrix (Fin 3) (Fin 3) k →ₗ[k] k)
variable (C : Fin r → Matrix (Fin 3) (Fin 3) k)
variable (hmul : ∀ A B i l, (A * B) i l = ∑ s, α s A * β s B * C s i l)

include hmul

private theorem m3_product_sum (A B : Matrix (Fin 3) (Fin 3) k) :
    A * B = ∑ s, (α s A * β s B) • C s := by
  ext i l
  rw [hmul A B i l]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

/-- The first forms of every finite exact algorithm span the full matrix dual. -/
theorem m3_first_forms_span_top : Submodule.span k (Set.range α) = ⊤ := by
  classical
  let S := Submodule.span k (Set.range α)
  have hdimM : Module.finrank k (Matrix (Fin 3) (Fin 3) k) = 9 := by
    simp [Module.finrank_matrix]
  have hdimDual : Module.finrank k
      (Matrix (Fin 3) (Fin 3) k →ₗ[k] k) = 9 := by
    simp [Module.finrank_matrix]
  have hS : 9 ≤ Module.finrank k S := by
    by_contra hn
    have hlt : Module.finrank k S < 9 := by omega
    let B := Module.Basis.ofVectorSpace k S
    letI : Fintype (Module.Basis.ofVectorSpaceIndex k S) := Fintype.ofFinite _
    obtain ⟨A, hA, hzero⟩ := exists_ne_zero_in_common_kernel
      (fun i => (B i).1) (by
        rw [← Module.finrank_eq_card_basis B, hdimM]
        exact hlt)
    have hzS : ∀ ψ : S, ψ.1 A = 0 := by
      intro ψ
      let ev : S →ₗ[k] k :=
        { toFun := fun q => q.1 A
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      have hev : ev = 0 := B.ext (fun i => hzero i)
      exact LinearMap.congr_fun hev ψ
    have hzα : ∀ s, α s A = 0 := fun s =>
      hzS ⟨α s, Submodule.subset_span (Set.mem_range_self s)⟩
    apply hA
    ext i l
    have he := hmul A 1 i l
    simp [hzα] at he
    exact he
  apply Submodule.eq_top_of_finrank_eq
  rw [hdimDual]
  exact le_antisymm (by simpa [hdimDual] using Submodule.finrank_le S) hS

/-- Every finite exact algorithm contains nine independent first forms at their
original summand indices. -/
theorem m3_exists_nine_independent_first_forms :
    ∃ e : Fin 9 → Fin r, Function.Injective e ∧ LinearIndependent k (α ∘ e) := by
  classical
  apply exists_indexed_linearIndependent_of_le_finrank_span α 9
  rw [m3_first_forms_span_top α β C hmul]
  simp [Module.finrank_matrix]

/-- If active first forms are independent, each active output is in `M₃(k)b`. -/
theorem m3_active_output_mem_range (b : Matrix (Fin 3) (Fin 3) k)
    (hα : LinearIndependent k (fun s : ↥(m3ActiveSupport β b) => α s.1))
    (s : Fin r) (hs : s ∈ m3ActiveSupport β b) :
    C s ∈ LinearMap.range (matrixRightMul b) := by
  classical
  let S := m3ActiveSupport β b
  let ss : S := ⟨s, hs⟩
  obtain ⟨A, hA⟩ := linearIndependent_evaluation_surjective
    (fun t : S => α t.1) hα (fun t => if t = ss then 1 else 0)
  have hprod : A * b = β s b • C s := by
    rw [m3_product_sum α β C hmul, Finset.sum_eq_single s]
    · have hAss := congrFun hA ss
      simp only [if_pos] at hAss
      change α s A = 1 at hAss
      rw [hAss]
      simp
    · intro t _ hts
      by_cases ht : t ∈ S
      · let tt : S := ⟨t, ht⟩
        have hAtt := congrFun hA tt
        have hne : tt ≠ ss := fun heq => hts (congrArg Subtype.val heq)
        simp only [hne, if_false] at hAtt
        change α t A = 0 at hAtt
        simp [hAtt]
      · have hβt : β t b = 0 := not_ne_iff.mp (by
          simpa [S, mem_m3ActiveSupport_iff] using ht)
        simp [hβt]
    · intro hsnot; exact (hsnot (Finset.mem_univ s)).elim
  have hscaled : β s b • C s ∈ LinearMap.range (matrixRightMul b) := ⟨A, hprod⟩
  have hβs := (mem_m3ActiveSupport_iff β b s).mp hs
  have hscaled' := Submodule.smul_mem (LinearMap.range (matrixRightMul b))
    (β s b)⁻¹ hscaled
  simpa [hβs] using hscaled'

/-- Products by `b` lie in the span of active outputs. -/
theorem m3_range_le_span_active_outputs (b : Matrix (Fin 3) (Fin 3) k) :
    LinearMap.range (matrixRightMul b) ≤
      Submodule.span k (Set.range (fun s : ↥(m3ActiveSupport β b) => C s.1)) := by
  classical
  rintro Z ⟨A, rfl⟩
  rw [matrixRightMul_apply, m3_product_sum α β C hmul]
  apply Submodule.sum_mem
  intro s _
  by_cases hs : s ∈ m3ActiveSupport β b
  · exact Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨⟨s, hs⟩, rfl⟩)
  · have hz : β s b = 0 := not_ne_iff.mp (by
      simpa [mem_m3ActiveSupport_iff] using hs)
    simp [hz]

/-- At a unit `b`, exactly nine terms are active; active first forms and outputs
are independent and active outputs span all of `M₃(k)`. -/
theorem m3_unit_active_rigidity (b : Matrix (Fin 3) (Fin 3) k) (hb : IsUnit b)
    (hα : LinearIndependent k (fun s : ↥(m3ActiveSupport β b) => α s.1)) :
    (m3ActiveSupport β b).card = 9 ∧
      LinearIndependent k (fun s : ↥(m3ActiveSupport β b) => α s.1) ∧
      LinearIndependent k (fun s : ↥(m3ActiveSupport β b) => C s.1) ∧
      Submodule.span k (Set.range (fun s : ↥(m3ActiveSupport β b) => C s.1)) = ⊤ := by
  classical
  let S := m3ActiveSupport β b
  let T := Submodule.span k (Set.range (fun s : S => C s.1))
  obtain ⟨u, hu⟩ := hb
  have hrange : LinearMap.range (matrixRightMul b) = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro Y
    refine ⟨Y * (↑(u⁻¹) : Matrix (Fin 3) (Fin 3) k), ?_⟩
    change (Y * (↑(u⁻¹) : Matrix (Fin 3) (Fin 3) k)) * b = Y
    rw [← hu, Matrix.mul_assoc]
    simp
  have hT : T = ⊤ := top_unique (by
    rw [← hrange]
    exact m3_range_le_span_active_outputs α β C hmul b)
  have hcard_le : S.card ≤ 9 := by
    have hdim := hα.fintype_card_le_finrank
    simpa [S, Module.finrank_matrix] using hdim
  have hnine_le : 9 ≤ S.card := by
    have hdimT : Module.finrank k T = 9 := by rw [hT]; simp [Module.finrank_matrix]
    rw [← hdimT]
    change Module.finrank k (Submodule.span k
      (Set.range (fun s : S => C s.1))) ≤ S.card
    simpa using finrank_span_range_le_card (k := k) (fun s : S => C s.1)
  have hcard : S.card = 9 := by omega
  have hC : LinearIndependent k (fun s : S => C s.1) := by
    rw [linearIndependent_iff_card_eq_finrank_span]
    change Fintype.card S = Module.finrank k
      (Submodule.span k (Set.range (fun s : S => C s.1)))
    calc
      Fintype.card S = 9 := by simpa using hcard
      _ = Module.finrank k T := by rw [hT]; simp [Module.finrank_matrix]
      _ = _ := rfl
  exact ⟨hcard, hα, hC, hT⟩

omit hmul in
/-- Complementary vanishing alone makes the active family a subfamily of an
independent nine-element first-form family. -/
theorem m3_active_linearIndependent_of_basis_interface
    (b : Matrix (Fin 3) (Fin 3) k) (e : Fin 9 → Fin r)
    (hαe : LinearIndependent k (α ∘ e))
    (hcomp : ∀ s, s ∉ Finset.univ.image e → β s b = 0) :
    LinearIndependent k (fun s : ↥(m3ActiveSupport β b) => α s.1) := by
  classical
  let S := m3ActiveSupport β b
  have hsubset : S ⊆ Finset.univ.image e := by
    intro s hs
    by_contra hnot
    exact (mem_m3ActiveSupport_iff β b s).mp hs (hcomp s hnot)
  let f : S → Fin 9 := fun s => Classical.choose (Finset.mem_image.mp (hsubset s.property))
  have hfval (s : S) : e (f s) = s.1 :=
    (Classical.choose_spec (Finset.mem_image.mp (hsubset s.property))).2
  have hf : Function.Injective f := by
    intro s t hst
    apply Subtype.ext
    rw [← hfval s, ← hfval t, hst]
  rw [show (fun s : S => α s.1) = (α ∘ e) ∘ f by
    funext s; simp only [Function.comp_apply, hfval]]
  exact hαe.comp f hf

/-- General strengthened Baur interpolation: an independent inactive restricted
subfamily of size `d` forces `active.card + d + 9 ≤ r`. -/
theorem m3_active_card_add_inactive_subfamily_add_nine_le
    (b : Matrix (Fin 3) (Fin 3) k) (hbunit : ¬ IsUnit b)
    (hα : LinearIndependent k (fun s : ↥(m3ActiveSupport β b) => α s.1))
    (d : ℕ) (e : Fin d → {s : Fin r // s ∉ m3ActiveSupport β b})
    (he : Function.Injective e)
    (hβe : LinearIndependent k (fun q =>
      (β (e q).1).domRestrict (LinearMap.range (matrixRightMul b)))) :
    (m3ActiveSupport β b).card + d + 9 ≤ r := by
  classical
  let S := m3ActiveSupport β b
  let ep : Fin d → Fin r := fun q => (e q).1
  let P : Finset (Fin r) := Finset.univ.image ep
  have hep : Function.Injective ep := fun _ _ h => he (Subtype.ext h)
  have hcardP : P.card = d := by simp [P, Finset.card_image_of_injective _ hep]
  have hdisj : Disjoint S P := by
    rw [Finset.disjoint_left]
    intro s hsS hsP
    rw [Finset.mem_image] at hsP
    obtain ⟨q, _, rfl⟩ := hsP
    exact (e q).property hsS
  let Rset : Finset (Fin r) := Finset.univ \ (S ∪ P)
  let R := ↥Rset
  have hcardR : Rset.card + S.card + d = r := by
    have hunion : (S ∪ P).card = S.card + d := by
      rw [Finset.card_union_of_disjoint hdisj, hcardP]
    have hp := Finset.card_sdiff_add_card_eq_card
      (show S ∪ P ⊆ Finset.univ from Finset.subset_univ _)
    have hp' : Rset.card + (S ∪ P).card = r := by
      simpa [Rset] using hp
    simpa [hunion, Nat.add_assoc] using hp'
  by_contra hbound
  change ¬ S.card + d + 9 ≤ r at hbound
  have hRltFinset : Rset.card < 9 := by omega
  have hRlt : Fintype.card R < 9 := by
    simpa [R] using hRltFinset
  obtain ⟨a, ha, haR⟩ := exists_ne_zero_in_common_kernel
    (fun q : R => α q.1) (by simpa [Module.finrank_matrix] using hRlt)
  have hCactive : ∀ s, s ∈ S → C s ∈ LinearMap.range (matrixRightMul b) :=
    fun s hs => m3_active_output_mem_range α β C hmul b hα s hs
  apply hbunit
  apply matrix_isUnit_of_rightIdeal_le_leftIdeal (n := 3) (by omega) ha
  intro Y
  obtain ⟨W, hW⟩ := linearIndependent_evaluation_surjective
    (fun q => (β (e q).1).domRestrict (LinearMap.range (matrixRightMul b))) hβe
    (fun q => β (e q).1 Y)
  obtain ⟨X, hX⟩ := W.property
  have hmatch (q : Fin d) : β (e q).1 (X * b) = β (e q).1 Y := by
    have hq := congrFun hW q
    change β (e q).1 W.1 = β (e q).1 Y at hq
    rw [← hX] at hq
    exact hq
  have hdiff : a * Y - a * (X * b) =
      ∑ s, (α s a * (β s Y - β s (X * b))) • C s := by
    rw [m3_product_sum α β C hmul, m3_product_sum α β C hmul,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s _
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hdiffmem : a * Y - a * (X * b) ∈ LinearMap.range (matrixRightMul b) := by
    rw [hdiff]
    apply Submodule.sum_mem
    intro s _
    by_cases hs : s ∈ S
    · exact Submodule.smul_mem _ _ (hCactive s hs)
    · by_cases hp : s ∈ P
      · rw [Finset.mem_image] at hp
        obtain ⟨q, _, rfl⟩ := hp
        have hq := hmatch q
        change β (ep q) (X * b) = β (ep q) Y at hq
        rw [hq]
        simp
      · have hr : s ∈ Rset := by
          simp only [Rset, Finset.mem_sdiff, Finset.mem_univ, true_and,
            Finset.mem_union, not_or]
          exact ⟨hs, hp⟩
        simp [haR (⟨s, hr⟩ : R)]
  have haWmem : a * (X * b) ∈ LinearMap.range (matrixRightMul b) := by
    refine ⟨a * X, ?_⟩
    simp only [matrixRightMul_apply, Matrix.mul_assoc]
  have haYmem := Submodule.add_mem (LinearMap.range (matrixRightMul b))
    hdiffmem haWmem
  have haYmem' : a * Y ∈ LinearMap.range (matrixRightMul b) := by
    simpa only [sub_add_cancel] using haYmem
  obtain ⟨Z, hZ⟩ := haYmem'
  exact ⟨Z, by simpa only [matrixRightMul_apply] using hZ.symm⟩

/-- Exact general singular normalization in subtraction-free cardinal form. -/
theorem m3_active_card_add_finrank_inactive_add_nine_le
    (b : Matrix (Fin 3) (Fin 3) k) (hbunit : ¬ IsUnit b)
    (hα : LinearIndependent k (fun s : ↥(m3ActiveSupport β b) => α s.1)) :
    (m3ActiveSupport β b).card +
      Module.finrank k (m3InactiveRestrictionSpan β b) + 9 ≤ r := by
  classical
  let I := {s : Fin r // s ∉ m3ActiveSupport β b}
  let f : I → LinearMap.range (matrixRightMul b) →ₗ[k] k := fun s =>
    (β s.1).domRestrict (LinearMap.range (matrixRightMul b))
  let d := Module.finrank k (m3InactiveRestrictionSpan β b)
  have hd : d ≤ Module.finrank k (Submodule.span k (Set.range f)) := by
    rfl
  obtain ⟨e, he, hlie⟩ := exists_indexed_linearIndependent_of_le_finrank_span f d hd
  exact m3_active_card_add_inactive_subfamily_add_nine_le α β C hmul b hbunit hα d e he
    (by change LinearIndependent k (f ∘ e); exact hlie)

/-- The schoolbook twenty-seven-term algorithm at `b = 0` jointly
instantiates the full hypotheses of both generic singular inequalities; the
independent inactive subfamily is chosen empty. -/
example : ∃ (α β : Fin 27 → Matrix (Fin 3) (Fin 3) ℚ →ₗ[ℚ] ℚ)
    (C : Fin 27 → Matrix (Fin 3) (Fin 3) ℚ)
    (e : Fin 0 → {s : Fin 27 // s ∉ m3ActiveSupport β 0}),
    (∀ A B i l, (A * B) i l = ∑ s, α s A * β s B * C s i l) ∧
      ¬ IsUnit (0 : Matrix (Fin 3) (Fin 3) ℚ) ∧
      LinearIndependent ℚ
        (fun s : ↥(m3ActiveSupport β 0) => α s.1) ∧
      Function.Injective e ∧
      LinearIndependent ℚ (fun q =>
        (β (e q).1).domRestrict
          (LinearMap.range (matrixRightMul (0 : Matrix (Fin 3) (Fin 3) ℚ)))) ∧
      (m3ActiveSupport β 0).card + 0 + 9 ≤ 27 ∧
      (m3ActiveSupport β 0).card +
        Module.finrank ℚ (m3InactiveRestrictionSpan β 0) + 9 ≤ 27 := by
  obtain ⟨α, β, C, hmul⟩ :=
    rankLE_matMulTensor_three_to_bilinear (rankLE_matMulTensor ℚ 3 3 3)
  have hempty : m3ActiveSupport β (0 : Matrix (Fin 3) (Fin 3) ℚ) = ∅ := by
    ext s
    simp [mem_m3ActiveSupport_iff]
  letI : IsEmpty ↥(m3ActiveSupport β (0 : Matrix (Fin 3) (Fin 3) ℚ)) :=
    ⟨fun s => by simpa [hempty] using s.property⟩
  let e : Fin 0 → {s : Fin 27 // s ∉ m3ActiveSupport β 0} :=
    fun q => Fin.elim0 q
  have hα : LinearIndependent ℚ
      (fun s : ↥(m3ActiveSupport β 0) => α s.1) :=
    linearIndependent_empty_type
  have he : Function.Injective e := fun q => Fin.elim0 q
  have hβe : LinearIndependent ℚ (fun q =>
      (β (e q).1).domRestrict
        (LinearMap.range (matrixRightMul (0 : Matrix (Fin 3) (Fin 3) ℚ)))) :=
    linearIndependent_empty_type
  have hsubfamily := m3_active_card_add_inactive_subfamily_add_nine_le
    α β C hmul 0 not_isUnit_zero hα 0 e he hβe
  have hfinrank := m3_active_card_add_finrank_inactive_add_nine_le
    α β C hmul 0 not_isUnit_zero hα
  exact ⟨α, β, C, e, hmul, not_isUnit_zero, hα, he, hβe,
    hsubfamily, hfinrank⟩

end Algorithm

/-- Sound endpoint for an ordinary seventeen-term `RankLE` decomposition.
It exports a nonzero common-kernel matrix and explicitly branches on whether
that matrix is a unit; no singularity is inferred from kernel construction. -/
theorem rankLE_m3_seventeen_structural_dichotomy {k : Type*} [Field k]
    (h : RankLE (matMulTensor k 3 3 3) 17) :
    ∃ (α β : Fin 17 → Matrix (Fin 3) (Fin 3) k →ₗ[k] k)
      (C : Fin 17 → Matrix (Fin 3) (Fin 3) k)
      (b : Matrix (Fin 3) (Fin 3) k),
      b ≠ 0 ∧
      (∀ A B i l, (A * B) i l = ∑ s, α s A * β s B * C s i l) ∧
      ((IsUnit b ∧
          (m3ActiveSupport β b).card = 9 ∧
          LinearIndependent k (fun s : ↥(m3ActiveSupport β b) => α s.1) ∧
          LinearIndependent k (fun s : ↥(m3ActiveSupport β b) => C s.1) ∧
          Submodule.span k
            (Set.range (fun s : ↥(m3ActiveSupport β b) => C s.1)) = ⊤) ∨
        (¬ IsUnit b ∧
          (m3ActiveSupport β b).card +
            Module.finrank k (m3InactiveRestrictionSpan β b) ≤ 8 ∧
          (Module.finrank k (LinearMap.range (matrixRightMul b)) = 3 ∨
            Module.finrank k (LinearMap.range (matrixRightMul b)) = 6))) := by
  classical
  obtain ⟨α, β, C, hmul⟩ := rankLE_matMulTensor_three_to_bilinear h
  obtain ⟨e, he, hαe⟩ := m3_exists_nine_independent_first_forms α β C hmul
  let I : Finset (Fin 17) := Finset.univ.image e
  have hcardI : I.card = 9 := by simp [I, Finset.card_image_of_injective _ he]
  let J := {s : Fin 17 // s ∉ I}
  have hcardJ : Fintype.card J = 8 := by
    rw [Fintype.card_subtype_compl]
    simp [hcardI]
  obtain ⟨b, hb0, hbJ⟩ := exists_ne_zero_in_common_kernel
    (fun s : J => β s.1) (by simp [hcardJ, Module.finrank_matrix])
  have hcomp : ∀ s, s ∉ Finset.univ.image e → β s b = 0 := by
    intro s hs
    exact hbJ ⟨s, by simpa [I] using hs⟩
  have hαactive :=
    m3_active_linearIndependent_of_basis_interface α β b e hαe hcomp
  refine ⟨α, β, C, b, hb0, hmul, ?_⟩
  by_cases hbunit : IsUnit b
  · have hrigid := m3_unit_active_rigidity α β C hmul b hbunit hαactive
    exact Or.inl ⟨hbunit, hrigid⟩
  · have hgeneral := m3_active_card_add_finrank_inactive_add_nine_le
      α β C hmul b hbunit hαactive
    have hbound : (m3ActiveSupport β b).card +
        Module.finrank k (m3InactiveRestrictionSpan β b) ≤ 8 := by
      omega
    have hrange :=
      finrank_range_matrixRightMul_eq_three_or_six_of_ne_zero_of_not_isUnit
        b hb0 hbunit
    exact Or.inr ⟨hbunit, hbound, hrange⟩

#check @m3ActiveSupport
#check @m3InactiveRestrictionSpan
#check @m3Equiv
#check @m3ToVec
#check @m3Output
#check @m3Form
#check @rankLE_matMulTensor_three_to_bilinear
#check @matrix_isUnit_of_rightIdeal_le_leftIdeal
#check @m3_first_forms_span_top
#check @m3_exists_nine_independent_first_forms
#check @m3_active_output_mem_range
#check @m3_range_le_span_active_outputs
#check @m3_unit_active_rigidity
#check @m3_active_linearIndependent_of_basis_interface
#check @m3_active_card_add_inactive_subfamily_add_nine_le
#check @m3_active_card_add_finrank_inactive_add_nine_le
#check @rankLE_m3_seventeen_structural_dichotomy

#print axioms rankLE_matMulTensor_three_to_bilinear
#print axioms matrix_isUnit_of_rightIdeal_le_leftIdeal
#print axioms m3_first_forms_span_top
#print axioms m3_exists_nine_independent_first_forms
#print axioms m3_active_output_mem_range
#print axioms m3_range_le_span_active_outputs
#print axioms m3_unit_active_rigidity
#print axioms m3_active_linearIndependent_of_basis_interface
#print axioms m3_active_card_add_inactive_subfamily_add_nine_le
#print axioms m3_active_card_add_finrank_inactive_add_nine_le
#print axioms rankLE_m3_seventeen_structural_dichotomy

end BilinearComplexity
