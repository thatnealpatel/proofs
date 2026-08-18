/-
  Scratch/GlobalRankSearch/WBoundary — the rational W tensor at the second
  K0 boundary: honest rank three and an explicit two-term degeneration.

  The degeneration varies the tensor.  It is not a rank-two decomposition of
  the fixed W tensor, nor a statement about an unsaturated determinantal fiber.
-/
import Scratch.GlobalRankSearch.SliceCover
import BilinearComplexity.BorderRank
import Mathlib.Algebra.MvPolynomial.Polynomial

set_option autoImplicit false

namespace BilinearComplexity

/-- The first standard coordinate vector of `ℚ²`. -/
def wE0 (i : Fin 2) : ℚ := if i = 0 then 1 else 0

/-- The second standard coordinate vector of `ℚ²`. -/
def wE1 (i : Fin 2) : ℚ := if i = 1 then 1 else 0

/-- The rational W tensor, in the convention `e100 + e010 + e001`. -/
def wTensor : Tensor ℚ 2 2 2 := fun i j l =>
  wE1 i * wE0 j * wE0 l +
  wE0 i * wE1 j * wE0 l +
  wE0 i * wE0 j * wE1 l

/-- The degree-two polynomial family specializing to W at zero.  Its linear
term contains the three coordinates with two ones, and its quadratic term is
`e111`. -/
def wDegeneration (t : ℚ) : Tensor ℚ 2 2 2 := fun i j l =>
  wTensor i j l + t *
    (wE1 i * wE1 j * wE0 l +
     wE1 i * wE0 j * wE1 l +
     wE0 i * wE1 j * wE1 l) +
    t ^ 2 * (wE1 i * wE1 j * wE1 l)

/-- The polynomial coordinate of the W degeneration. -/
noncomputable def wDegenerationPolynomial (i j l : Fin 2) : Polynomial ℚ :=
  Polynomial.C (wTensor i j l) +
    Polynomial.C
      (wE1 i * wE1 j * wE0 l +
       wE1 i * wE0 j * wE1 l +
       wE0 i * wE1 j * wE1 l) * Polynomial.X +
    Polynomial.C (wE1 i * wE1 j * wE1 l) * Polynomial.X ^ 2

/-! Coordinate and specialization ground checks. -/

example : wE0 0 = 1 := rfl
example : wE0 1 = 0 := rfl
example : wE1 0 = 0 := rfl
example : wE1 1 = 1 := rfl

example : wTensor 1 0 0 = 1 := by norm_num [wTensor, wE0, wE1]
example : wTensor 0 1 0 = 1 := by norm_num [wTensor, wE0, wE1]
example : wTensor 0 0 1 = 1 := by norm_num [wTensor, wE0, wE1]
example : wTensor 0 0 0 = 0 := by norm_num [wTensor, wE0, wE1]
example : wTensor 1 1 1 = 0 := by norm_num [wTensor, wE0, wE1]

/-- The varying family really specializes to W at parameter zero. -/
theorem wDegeneration_zero : wDegeneration 0 = wTensor := by
  funext i j l
  simp [wDegeneration]

/-- Evaluation of each polynomial coordinate gives the corresponding entry of
`wDegeneration`. -/
theorem wDegenerationPolynomial_eval (t : ℚ) (i j l : Fin 2) :
    (wDegenerationPolynomial i j l).eval t = wDegeneration t i j l := by
  simp only [wDegenerationPolynomial, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_pow, wDegeneration]
  ring

example : (wDegenerationPolynomial 1 1 1).eval 3 = 9 := by
  norm_num [wDegenerationPolynomial, wTensor, wE0, wE1]

example : wDegeneration 3 1 1 0 = 3 := by
  norm_num [wDegeneration, wTensor, wE0, wE1]

example : (wDegenerationPolynomial 1 1 0).eval 3 = 3 := by
  norm_num [wDegenerationPolynomial, wTensor, wE0, wE1]

/-- Every rank-one matrix lying in the plane of the two mode-one W slices has
zero coefficient along the off-diagonal slice.  Thus the only projective
rank-one direction in that slice plane is the repeated `e00` direction. -/
theorem rankOne_in_wSlicePlane_offDiagonal_eq_zero
    (v w : Fin 2 → ℚ) (lambda mu : ℚ)
    (hplane : rankOneMatrixVector v w = fun jl =>
      lambda * modeOneSlice wTensor 0 jl + mu * modeOneSlice wTensor 1 jl) :
    lambda = 0 := by
  have h01 := congrFun hplane (0, 1)
  have h10 := congrFun hplane (1, 0)
  have h11 := congrFun hplane (1, 1)
  norm_num [rankOneMatrixVector, modeOneSlice, wTensor, wE0, wE1] at h01 h10
  have h11zero : v 1 * w 1 = 0 := by
    calc
      v 1 * w 1 =
          lambda * modeOneSlice wTensor 0 (1, 1) +
            mu * modeOneSlice wTensor 1 (1, 1) := h11
      _ = 0 := by norm_num [modeOneSlice, wTensor, wE0, wE1]
  have hsquare : lambda ^ 2 = 0 := by
    calc
      lambda ^ 2 = (v 0 * w 1) * (v 1 * w 0) := by rw [h01, h10]; ring
      _ = (v 0 * w 0) * (v 1 * w 1) := by ring
      _ = 0 := by rw [h11zero, mul_zero]
  exact sq_eq_zero_iff.mp hsquare

/-- The W tensor admits its displayed three-simple-tensor decomposition. -/
theorem wTensor_rankLE_three : RankLE wTensor 3 := by
  let u : Fin 3 → Fin 2 → ℚ := fun s i =>
    if s = 0 then wE1 i else if s = 1 then wE0 i else wE0 i
  let v : Fin 3 → Fin 2 → ℚ := fun s j =>
    if s = 0 then wE0 j else if s = 1 then wE1 j else wE0 j
  let w : Fin 3 → Fin 2 → ℚ := fun s l =>
    if s = 0 then wE0 l else if s = 1 then wE0 l else wE1 l
  refine ⟨u, v, w, ?_⟩
  funext i j l
  have htwo_ne_one : (2 : Fin 3) ≠ 1 := by decide
  fin_cases i <;> fin_cases j <;> fin_cases l <;>
    norm_num [u, v, w, wTensor, wE0, wE1, Fin.sum_univ_succ, htwo_ne_one]

/-- Two rank-one matrices cannot cover both mode-one slices of W.  The proof
uses `rankLE_iff_sliceCover` and the intrinsic rank-one-direction theorem for
the W slice plane. -/
theorem wTensor_not_rankLE_two : ¬ RankLE wTensor 2 := by
  intro hrank
  obtain ⟨v, w, hcover⟩ := rankLE_iff_sliceCover.mp hrank
  have hzero := hcover (0 : Fin 2)
  have hone := hcover (1 : Fin 2)
  rw [Submodule.mem_span_range_iff_exists_fun] at hzero hone
  obtain ⟨x, hx⟩ := hzero
  obtain ⟨y, hy⟩ := hone
  let A : Fin 2 → Fin 2 × Fin 2 → ℚ :=
    fun s => rankOneMatrixVector (v s) (w s)
  have hx' : (∑ s, x s • A s) = modeOneSlice wTensor 0 := by
    simpa [A] using hx
  have hy' : (∑ s, y s • A s) = modeOneSlice wTensor 1 := by
    simpa [A] using hy
  let D : ℚ := x 0 * y 1 - x 1 * y 0
  have hD : D ≠ 0 := by
    intro hDzero
    have hx00 := congrFun hx' (0, 0)
    have hy00 := congrFun hy' (0, 0)
    have hx01 := congrFun hx' (0, 1)
    norm_num [modeOneSlice, wTensor, wE0, wE1,
      Fin.sum_univ_succ] at hx00 hy00 hx01
    have hx0identity : x 0 = D * A 1 (0, 0) := by
      calc
        x 0 = x 0 * 1 := by ring
        _ = x 0 * (y 0 * A 0 (0, 0) + y 1 * A 1 (0, 0)) := by rw [hy00]
        _ = (x 0 * y 1 - x 1 * y 0) * A 1 (0, 0) +
            y 0 * (x 0 * A 0 (0, 0) + x 1 * A 1 (0, 0)) := by ring
        _ = D * A 1 (0, 0) := by rw [hx00, mul_zero, add_zero]
    have hx0 : x 0 = 0 := by
      rw [hDzero, zero_mul] at hx0identity
      exact hx0identity
    have hx1identity : x 1 = -D * A 0 (0, 0) := by
      calc
        x 1 = x 1 * 1 := by ring
        _ = x 1 * (y 0 * A 0 (0, 0) + y 1 * A 1 (0, 0)) := by rw [hy00]
        _ = -(x 0 * y 1 - x 1 * y 0) * A 0 (0, 0) +
            y 1 * (x 0 * A 0 (0, 0) + x 1 * A 1 (0, 0)) := by ring
        _ = -D * A 0 (0, 0) := by rw [hx00, mul_zero, add_zero]
    have hx1 : x 1 = 0 := by
      rw [hDzero, neg_zero, zero_mul] at hx1identity
      exact hx1identity
    rw [hx0, hx1] at hx01
    norm_num at hx01
  have hA0plane : A 0 = fun jl =>
      (y 1 / D) * modeOneSlice wTensor 0 jl +
        (-x 1 / D) * modeOneSlice wTensor 1 jl := by
    funext jl
    have hxjl := congrFun hx' jl
    have hyjl := congrFun hy' jl
    simp only [Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      at hxjl hyjl
    field_simp [hD]
    dsimp [D]
    linear_combination y 1 * hxjl - x 1 * hyjl
  have hA1plane : A 1 = fun jl =>
      (-y 0 / D) * modeOneSlice wTensor 0 jl +
        (x 0 / D) * modeOneSlice wTensor 1 jl := by
    funext jl
    have hxjl := congrFun hx' jl
    have hyjl := congrFun hy' jl
    simp only [Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      at hxjl hyjl
    field_simp [hD]
    dsimp [D]
    linear_combination x 0 * hyjl - y 0 * hxjl
  have hy1div : y 1 / D = 0 :=
    rankOne_in_wSlicePlane_offDiagonal_eq_zero (v 0) (w 0) _ _ (by
      simpa [A] using hA0plane)
  have hy0div : -y 0 / D = 0 :=
    rankOne_in_wSlicePlane_offDiagonal_eq_zero (v 1) (w 1) _ _ (by
      simpa [A] using hA1plane)
  have hy1 : y 1 = 0 := (div_eq_zero_iff).mp hy1div |>.resolve_right hD
  have hy0 : y 0 = 0 := by
    have hneg : -y 0 = 0 := (div_eq_zero_iff).mp hy0div |>.resolve_right hD
    exact neg_eq_zero.mp hneg
  have hy00 := congrFun hy' (0, 0)
  norm_num [A, modeOneSlice, wTensor, wE0, wE1, Fin.sum_univ_succ,
    hy0, hy1] at hy00

/-- The honest tensor rank of rational W is exactly three. -/
theorem wTensor_rank_eq_three : rank wTensor = 3 := by
  apply le_antisymm (rank_le_of_rankLE wTensor_rankLE_three)
  by_contra hlt
  have hle : rank wTensor ≤ 2 := by omega
  exact wTensor_not_rankLE_two (rankLE_of_rank_le hle)

/-- The degeneration is genuinely varying: at parameter one its `e111`
coordinate is nonzero, unlike W.  In particular, this family is not an
unsaturated decomposition inside the fixed-W determinantal fiber. -/
theorem wDegeneration_one_ne_wTensor : wDegeneration 1 ≠ wTensor := by
  intro heq
  have h111 := congrFun (congrFun (congrFun heq (1 : Fin 2)) 1) 1
  norm_num [wDegeneration, wTensor, wE0, wE1] at h111

/-- At every nonzero parameter, the varying polynomial family has an explicit
two-triad decomposition. -/
theorem wDegeneration_rankLE_two {t : ℚ} (ht : t ≠ 0) :
    RankLE (wDegeneration t) 2 := by
  let z : Fin 2 → ℚ := fun i => wE0 i + t * wE1 i
  let u : Fin 2 → Fin 2 → ℚ := fun s i =>
    if s = 0 then (1 / t) * z i else (-1 / t) * wE0 i
  let v : Fin 2 → Fin 2 → ℚ := fun s i => if s = 0 then z i else wE0 i
  let w : Fin 2 → Fin 2 → ℚ := fun s i => if s = 0 then z i else wE0 i
  refine ⟨u, v, w, ?_⟩
  funext i j l
  fin_cases i <;> fin_cases j <;> fin_cases l <;>
    norm_num [u, v, w, z, wDegeneration, wTensor, wE0, wE1, ht]
  all_goals field_simp
  all_goals ring

/-- The exact polynomial-closure border rank of W is at most two.  The closure
bridge is sound here because every defining polynomial pulls back to a
univariate polynomial vanishing at infinitely many nonzero rational points. -/
theorem wTensor_borderRankLE_two : BorderRankLE wTensor 2 := by
  rw [borderRankLE_iff]
  intro p hp
  let q : Polynomial ℚ := MvPolynomial.eval₂ Polynomial.C
    (fun ij => wDegenerationPolynomial ij.1 ij.2.1 ij.2.2) p
  have hqeval (t : ℚ) : q.eval t = MvPolynomial.eval (entries (wDegeneration t)) p := by
    dsimp [q]
    rw [MvPolynomial.polynomial_eval_eval₂]
    rw [show (Polynomial.evalRingHom t).comp Polynomial.C = RingHom.id ℚ by
      ext z
      simp]
    rw [MvPolynomial.eval₂_id]
    have hcoords :
        (fun s => Polynomial.eval t (wDegenerationPolynomial s.1 s.2.1 s.2.2)) =
          entries (wDegeneration t) := by
      funext ij
      exact wDegenerationPolynomial_eval t ij.1 ij.2.1 ij.2.2
    rw [hcoords]
  have hroots : Set.Infinite {t : ℚ | q.IsRoot t} := by
    let f : ℕ → ℚ := fun n => n + 1
    have hf : Function.Injective f := by
      intro m n hmn
      dsimp [f] at hmn
      have hadd : m + 1 = n + 1 := by
        exact_mod_cast hmn
      omega
    apply (Set.infinite_range_of_injective hf).mono
    rintro t ⟨n, rfl⟩
    change q.eval (f n) = 0
    rw [hqeval]
    apply hp
    exact ⟨wDegeneration (f n), wDegeneration_rankLE_two (by
      dsimp [f]
      positivity), rfl⟩
  have hq : q = 0 := Polynomial.eq_zero_of_infinite_isRoot q hroots
  have hzero := hqeval 0
  rw [hq, wDegeneration_zero] at hzero
  simpa using hzero.symm

/-! Joint satisfiability and interface audits. -/

/-- The upper-rank, lower-rank, specialization, generic rank-two, and closure
claims are jointly realized by the definitions above. -/
example :
    RankLE wTensor 3 ∧ ¬ RankLE wTensor 2 ∧
      wDegeneration 0 = wTensor ∧
      (∀ t : ℚ, t ≠ 0 → RankLE (wDegeneration t) 2) ∧
      BorderRankLE wTensor 2 :=
  ⟨wTensor_rankLE_three, wTensor_not_rankLE_two, wDegeneration_zero,
    fun _ ht => wDegeneration_rankLE_two ht, wTensor_borderRankLE_two⟩

#check @wE0
#check @wE1
#check @wTensor
#check @wDegeneration
#check @wDegenerationPolynomial
#check @wDegeneration_zero
#check @wDegenerationPolynomial_eval
#check @rankOne_in_wSlicePlane_offDiagonal_eq_zero
#check @wTensor_rankLE_three
#check @wTensor_not_rankLE_two
#check @wTensor_rank_eq_three
#check @wDegeneration_one_ne_wTensor
#check @wDegeneration_rankLE_two
#check @wTensor_borderRankLE_two

#print axioms wDegeneration_zero
#print axioms wDegenerationPolynomial_eval
#print axioms rankOne_in_wSlicePlane_offDiagonal_eq_zero
#print axioms wTensor_rankLE_three
#print axioms wTensor_not_rankLE_two
#print axioms wTensor_rank_eq_three
#print axioms wDegeneration_one_ne_wTensor
#print axioms wDegeneration_rankLE_two
#print axioms wTensor_borderRankLE_two

end BilinearComplexity
