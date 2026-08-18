/-
  BilinearComplexity/BorderRank — rectangular polynomial-closure border rank
  and symbolic determinantal equations.

  `BorderRankLE` in this file is defined over an arbitrary field as polynomial
  closure, not as a Euclidean or pre-existing Zariski-topological closure.
  Identifying it with classical complex border rank requires a separate bridge
  through algebraic closedness, secant varieties, and the relevant topology;
  no such equivalence is claimed or proved here.
-/
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import BilinearComplexity.Flattening
import PolynomialClosure

set_option autoImplicit false

namespace BilinearComplexity

/-- The rectangular tensor-entry index set for shape `a × b × c`. -/
abbrev EntryIndex (a b c : ℕ) := Fin a × Fin b × Fin c

/-- The entry vector of a rectangular tensor, used as its affine-coordinate
point for multivariate polynomial evaluation. -/
def entries {k : Type*} {a b c : ℕ} (T : Tensor k a b c) : EntryIndex a b c → k :=
  fun ijl => T ijl.1 ijl.2.1 ijl.2.2

/-- Ground truth: the entry vector uses the three rectangular coordinates in
order. -/
example {k : Type*} {a b c : ℕ} (T : Tensor k a b c)
    (i : Fin a) (j : Fin b) (l : Fin c) : entries T (i, j, l) = T i j l :=
  rfl

/-- The affine entry-vector locus of tensors admitting an `r`-triad
decomposition. This is the ordinary, closure-free rank-`≤ r` locus. -/
def rankLocus (k : Type*) [CommSemiring k] (a b c r : ℕ) :
    Set (EntryIndex a b c → k) :=
  {x | ∃ T : Tensor k a b c, RankLE T r ∧ x = entries T}

/-- Unfolding membership in the ordinary rectangular rank locus. -/
theorem mem_rankLocus {k : Type*} [CommSemiring k] {a b c r : ℕ}
    {x : EntryIndex a b c → k} :
    x ∈ rankLocus k a b c r ↔
      ∃ T : Tensor k a b c, RankLE T r ∧ x = entries T :=
  Iff.rfl

/-- Polynomial-closure border rank at most `r` over an arbitrary field:
`entries T` lies in the common zero locus of all field-coefficient
polynomials vanishing on the ordinary rank-`≤ r` locus. Equivalence with
classical complex border rank needs a separate algebraic-geometric/topological
bridge and is not proved here. -/
def BorderRankLE {k : Type*} [Field k] {a b c : ℕ}
    (T : Tensor k a b c) (r : ℕ) : Prop :=
  entries T ∈ PolynomialClosure.closure k (rankLocus k a b c r)

/-- The defining universal-polynomial characterization of rectangular
polynomial-closure border rank. -/
theorem borderRankLE_iff {k : Type*} [Field k] {a b c r : ℕ}
    {T : Tensor k a b c} :
    BorderRankLE T r ↔
      ∀ p ∈ MvPolynomial.vanishingIdeal k (rankLocus k a b c r),
        MvPolynomial.eval (entries T) p = 0 :=
  PolynomialClosure.mem_closure_iff

/-- Ordinary rank at most `r` implies polynomial-closure border rank at most
`r`. -/
theorem RankLE.borderRankLE {k : Type*} [Field k] {a b c r : ℕ}
    {T : Tensor k a b c} (hT : RankLE T r) : BorderRankLE T r :=
  PolynomialClosure.subset_closure (rankLocus k a b c r) ⟨T, hT, rfl⟩

/-- Polynomial-closure border rank is monotone in the rank threshold. -/
theorem BorderRankLE.mono {k : Type*} [Field k] {a b c r r' : ℕ}
    {T : Tensor k a b c} (hT : BorderRankLE T r) (hrr' : r ≤ r') :
    BorderRankLE T r' := by
  have hlocus : rankLocus k a b c r ⊆ rankLocus k a b c r' := by
    rintro x ⟨S, hS, rfl⟩
    exact ⟨S, hS.mono hrr', rfl⟩
  exact PolynomialClosure.closure_mono hlocus hT

/-! ## Symbolic linear matrix constructions -/

/-- A symbolic lift of a tensor-linear matrix construction. Its polynomial
matrix is part of the data, and `eval_matrix` explicitly certifies that
specializing tensor-entry variables recovers the fixed-field linear map.
This bridge is intentionally required: linearity of `F` alone does not imply
a symbolic determinant identity. -/
structure SymbolicMatrixLift {k : Type*} [Field k] {a b c : ℕ}
    {rows cols : Type*} (F : Tensor k a b c →ₗ[k] Matrix rows cols k) where
  matrix : Matrix rows cols (MvPolynomial (EntryIndex a b c) k)
  eval_matrix : ∀ (T : Tensor k a b c) (i : rows) (j : cols),
    MvPolynomial.eval (entries T) (matrix i j) = F T i j

/-- Evaluating a symbolic lifted minor gives the matching concrete minor. -/
theorem SymbolicMatrixLift.eval_det_submatrix {k : Type*} [Field k]
    {a b c m : ℕ} {rows cols : Type*}
    {F : Tensor k a b c →ₗ[k] Matrix rows cols k} (L : SymbolicMatrixLift F)
    (T : Tensor k a b c) (ri : Fin m → rows) (ci : Fin m → cols) :
    MvPolynomial.eval (entries T) ((L.matrix.submatrix ri ci).det) =
      ((F T).submatrix ri ci).det := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  exact L.eval_matrix T (ri i) (ci j)

/-- Every square minor larger than the rank of a matrix over a field has zero
determinant; row and column selectors need not be injective. -/
theorem det_submatrix_eq_zero_of_rank_le {k : Type*} [Field k]
    {rows cols : Type*} [Fintype rows] [Fintype cols] {r : ℕ} {M : Matrix rows cols k}
    (hM : M.rank ≤ r) (ri : Fin (r + 1) → rows) (ci : Fin (r + 1) → cols) :
    (M.submatrix ri ci).det = 0 := by
  by_contra hdet
  have hrank : r + 1 ≤ M.rank := le_rank_of_submatrix_det_ne_zero M ri ci hdet
  omega

/-- For a symbolic lift whose concrete simple images have rank at most `q`,
every `(r*q+1)` minor polynomial vanishes on the ordinary rank-`≤ r` locus. -/
theorem SymbolicMatrixLift.det_submatrix_mem_vanishingIdeal
    {k : Type*} [Field k] {a b c r q : ℕ}
    {rows cols : Type*} [Fintype rows] [Fintype cols]
    {F : Tensor k a b c →ₗ[k] Matrix rows cols k} (L : SymbolicMatrixLift F)
    (hsimple : ∀ (u : Fin a → k) (v : Fin b → k) (w : Fin c → k),
      (F (fun i j l => u i * v j * w l)).rank ≤ q)
    (ri : Fin (r * q + 1) → rows) (ci : Fin (r * q + 1) → cols) :
    (L.matrix.submatrix ri ci).det ∈
      MvPolynomial.vanishingIdeal k (rankLocus k a b c r) := by
  rw [MvPolynomial.mem_vanishingIdeal_iff]
  rintro x ⟨T, hT, rfl⟩
  simp only [MvPolynomial.aeval_eq_eval]
  rw [L.eval_det_submatrix]
  exact det_submatrix_eq_zero_of_rank_le
    (rank_linearMap_le_mul_of_rankLE F hsimple hT) ri ci

/-- Generic determinantal vanishing on polynomial closure: under the explicit
symbolic evaluation contract and the simple-image rank bound `q`, every
`(r*q+1)` minor of `F T` vanishes for polynomial-closure border rank `≤ r`. -/
theorem BorderRankLE.det_submatrix_eq_zero
    {k : Type*} [Field k] {a b c r q : ℕ}
    {rows cols : Type*} [Fintype rows] [Fintype cols]
    {F : Tensor k a b c →ₗ[k] Matrix rows cols k} {T : Tensor k a b c}
    (hT : BorderRankLE T r)
    (L : SymbolicMatrixLift F)
    (hsimple : ∀ (u : Fin a → k) (v : Fin b → k) (w : Fin c → k),
      (F (fun i j l => u i * v j * w l)).rank ≤ q)
    (ri : Fin (r * q + 1) → rows) (ci : Fin (r * q + 1) → cols) :
    ((F T).submatrix ri ci).det = 0 := by
  rw [← L.eval_det_submatrix T ri ci]
  exact borderRankLE_iff.mp hT _ (L.det_submatrix_mem_vanishingIdeal hsimple ri ci)

/-! ## Ordinary flattening regression -/

/-- The polynomial-valued ordinary first-factor flattening. -/
noncomputable def symbolicFlattening (k : Type*) [Field k] (a b c : ℕ) :
    SymbolicMatrixLift (flatteningLinear (k := k) (a := a) (b := b) (c := c)) where
  matrix i jl := MvPolynomial.X (i, jl.1, jl.2)
  eval_matrix T i jl := by simp [entries, flatteningLinear_apply, flattening]

/-- Ground truth: the symbolic ordinary flattening has the expected entry
variable. -/
example {k : Type*} [Field k] {a b c : ℕ} (i : Fin a) (j : Fin b) (l : Fin c) :
    (symbolicFlattening k a b c).matrix i (j, l) = MvPolynomial.X (i, j, l) :=
  rfl

/-- Regression theorem: ordinary `(r+1)` flattening minors vanish at every
tensor of rectangular polynomial-closure border rank at most `r`. -/
theorem BorderRankLE.flattening_det_submatrix_eq_zero
    {k : Type*} [Field k] {a b c r : ℕ} {T : Tensor k a b c}
    (hT : BorderRankLE T r) (ri : Fin (r + 1) → Fin a)
    (ci : Fin (r + 1) → Fin b × Fin c) :
    ((flattening T).submatrix ri ci).det = 0 := by
  change ((flatteningLinear T).submatrix ri ci).det = 0
  rw [← (symbolicFlattening k a b c).eval_det_submatrix T ri ci]
  apply borderRankLE_iff.mp hT
  rw [MvPolynomial.mem_vanishingIdeal_iff]
  rintro x ⟨S, hS, rfl⟩
  simp only [MvPolynomial.aeval_eq_eval]
  rw [(symbolicFlattening k a b c).eval_det_submatrix]
  exact det_submatrix_eq_zero_of_rank_le hS.rank_flatteningLinear_le ri ci

#check @entries
#check @rankLocus
#check @mem_rankLocus
#check @BorderRankLE
#check @borderRankLE_iff
#check @RankLE.borderRankLE
#check @BorderRankLE.mono
#check @SymbolicMatrixLift.eval_det_submatrix
#check @SymbolicMatrixLift.det_submatrix_mem_vanishingIdeal
#check @BorderRankLE.det_submatrix_eq_zero
#check @symbolicFlattening
#check @BorderRankLE.flattening_det_submatrix_eq_zero

/-- Genuine determinantal regression: the all-ones `2 × 2 × 1` rank-one
tensor satisfies both the generic symbolic-lift theorem and the specialized
ordinary-flattening theorem on injective selectors for the full `2 × 2`
minor. -/
example :
    let T : Tensor ℚ 2 2 1 := fun _ _ _ => 1
    let ri : Fin 2 → Fin 2 := id
    let ci : Fin 2 → Fin 2 × Fin 1 := fun i => (i, 0)
    ((flatteningLinear T).submatrix ri ci).det = 0 ∧
      ((flattening T).submatrix ri ci).det = 0 := by
  dsimp
  let u : Fin 1 → Fin 2 → ℚ := fun _ _ => 1
  let v : Fin 1 → Fin 2 → ℚ := fun _ _ => 1
  let w : Fin 1 → Fin 1 → ℚ := fun _ _ => 1
  have hdecomp : (fun _ _ _ => (1 : ℚ) : Tensor ℚ 2 2 1) =
      fun i j l => ∑ s, u s i * v s j * w s l := by
    funext i j l
    simp [u, v, w]
  have hR : RankLE (fun _ _ _ => (1 : ℚ) : Tensor ℚ 2 2 1) 1 := by
    exact ⟨u, v, w, hdecomp⟩
  have hB : BorderRankLE (fun _ _ _ => (1 : ℚ) : Tensor ℚ 2 2 1) 1 :=
    hR.borderRankLE
  constructor
  · exact hB.det_submatrix_eq_zero (q := 1) (symbolicFlattening ℚ 2 2 1)
      rank_flatteningLinear_simple_le_one id (fun i => (i, 0))
  · exact hB.flattening_det_submatrix_eq_zero id (fun i => (i, 0))

/-- The symbolic `2 × 2` flattening minor used above is genuinely nonzero:
evaluating it on the tensor whose flattening is the `2 × 2` identity gives
determinant one. -/
example :
    let ri : Fin 2 → Fin 2 := id
    let ci : Fin 2 → Fin 2 × Fin 1 := fun i => (i, 0)
    ((symbolicFlattening ℚ 2 2 1).matrix.submatrix ri ci).det ≠ 0 := by
  dsimp
  let I : Tensor ℚ 2 2 1 := fun i j _ => if i = j then 1 else 0
  intro hzero
  have heval := (symbolicFlattening ℚ 2 2 1).eval_det_submatrix
    I id (fun i => (i, 0))
  rw [hzero] at heval
  norm_num [I, flatteningLinear_apply, flattening, Matrix.det_fin_two] at heval

/-- Boundary audit: polynomial-closure border rank zero is satisfiable for the
zero tensor in a positive-dimensional shape. -/
example : BorderRankLE (0 : Tensor ℚ 2 2 1) 0 :=
  (rankLE_zero_iff.mpr rfl).borderRankLE

/-- Boundary audit: `q = 0` is jointly satisfiable with an actual zero linear
matrix construction, its zero symbolic lift, the simple-image rank bound, and
the generic closure-level minor theorem. -/
example :
    ∃ (F : Tensor ℚ 2 2 1 →ₗ[ℚ] Matrix (Fin 1) (Fin 1) ℚ)
      (L : SymbolicMatrixLift F),
      (∀ (u : Fin 2 → ℚ) (v : Fin 2 → ℚ) (w : Fin 1 → ℚ),
        (F (fun i j l => u i * v j * w l)).rank ≤ 0) ∧
      L.matrix = 0 ∧
      ((F (0 : Tensor ℚ 2 2 1)).submatrix id id).det = 0 := by
  let F : Tensor ℚ 2 2 1 →ₗ[ℚ] Matrix (Fin 1) (Fin 1) ℚ := 0
  let L : SymbolicMatrixLift F :=
    { matrix := 0
      eval_matrix := by intros; simp [F] }
  have hsimple : ∀ (u : Fin 2 → ℚ) (v : Fin 2 → ℚ) (w : Fin 1 → ℚ),
      (F (fun i j l => u i * v j * w l)).rank ≤ 0 := by
    intro u v w
    simp [F]
  have hR : RankLE (0 : Tensor ℚ 2 2 1) 0 := rankLE_zero_iff.mpr rfl
  have hB : BorderRankLE (0 : Tensor ℚ 2 2 1) 3 :=
    (hR.mono (Nat.zero_le 3)).borderRankLE
  refine Exists.intro F ?_
  refine Exists.intro L ?_
  constructor
  · exact hsimple
  constructor
  · rfl
  · exact hB.det_submatrix_eq_zero (q := 0) L hsimple id id

/-- Boundary audit: a zero-dimensional first factor is admitted, and its
unique tensor has ordinary and polynomial-closure border rank zero. -/
example : BorderRankLE (0 : Tensor ℚ 0 2 1) 0 :=
  (rankLE_zero_iff.mpr rfl).borderRankLE

#print axioms mem_rankLocus
#print axioms borderRankLE_iff
#print axioms RankLE.borderRankLE
#print axioms BorderRankLE.mono
#print axioms SymbolicMatrixLift.eval_det_submatrix
#print axioms det_submatrix_eq_zero_of_rank_le
#print axioms SymbolicMatrixLift.det_submatrix_mem_vanishingIdeal
#print axioms BorderRankLE.det_submatrix_eq_zero
#print axioms BorderRankLE.flattening_det_submatrix_eq_zero

end BilinearComplexity
