/-
  BilinearComplexity/KoszulFlattening — the finite-coordinate U-mode p = 1
  Koszul flattening and ordinary tensor-rank certificates.

  For T in U ⊗ V ⊗ W, the map is V* ⊗ U → Λ²U ⊗ W.  We use no
  exterior-algebra library: a wedge row is the ordered pair (p,q), p < q.
  Columns are (j,s) in V × U and rows are (l,(p,q)) in W × {p<q}; these
  finite product types are the matrix index sets, with the ordered-pair basis
  fixed by p<q.  With standard bases and e_p ∧ e_q positive,
  the entry is T p j l when s=q, is -T q j l when s=p, and is zero otherwise.
  Thus it is the coefficient of e_i ∧ e_s in the contraction of T against
  the V* basis vector indexed by j.

  This construction is the p=1 Koszul flattening used in J. M. Landsberg and
  G. Ottaviani, “New lower bounds for the border rank of matrix
  multiplication”, arXiv:1112.6007, Theory of Computing 11 (2015),
  DOI 10.4086/toc.2015.v011a011.
-/
import BilinearComplexity.LinearFlattening

set_option autoImplicit false

namespace BilinearComplexity

/-- The coordinate basis of `Λ²(k^a)`: ordered pairs `(p,q)` with `p < q`.
The strict inequality chooses exactly one orientation of each unequal pair. -/
abbrev KoszulPair (a : ℕ) := {pq : Fin a × Fin a // pq.1 < pq.2}

example : Fintype.card (KoszulPair 0) = 0 := by decide
example : Fintype.card (KoszulPair 1) = 0 := by decide
example : Fintype.card (KoszulPair 3) = 3 := by decide

/-- The explicit U-mode, `p=1` Koszul matrix.  A column `(j,s)` represents
`e_j^* ⊗ e_s`; a row `(l,⟨p,q⟩)` represents `(e_p ∧ e_q) ⊗ e_l`.
Its signs are fixed by `e_p ∧ e_q` being positive for `p < q`. -/
def koszulMatrix {k : Type*} [CommRing k] {a b c : ℕ} (T : Tensor k a b c) :
    Matrix (Fin c × KoszulPair a) (Fin b × Fin a) k := fun row col =>
  if col.2 = row.2.1.2 then T row.2.1.1 col.1 row.1
  else if col.2 = row.2.1.1 then -T row.2.1.2 col.1 row.1
  else 0

/-- Entry formula for the finite-coordinate Koszul matrix. -/
@[simp] theorem koszulMatrix_apply {k : Type*} [CommRing k] {a b c : ℕ}
    (T : Tensor k a b c) (row : Fin c × KoszulPair a) (col : Fin b × Fin a) :
    koszulMatrix T row col =
      if col.2 = row.2.1.2 then T row.2.1.1 col.1 row.1
      else if col.2 = row.2.1.1 then -T row.2.1.2 col.1 row.1
      else 0 := rfl

/-- The Koszul construction as a field-linear tensor-to-matrix map. -/
def koszulLinear (k : Type*) [Field k] (a b c : ℕ) :
    Tensor k a b c →ₗ[k] Matrix (Fin c × KoszulPair a) (Fin b × Fin a) k where
  toFun := koszulMatrix
  map_add' T S := by
    ext row col
    simp only [koszulMatrix_apply, Pi.add_apply, Matrix.add_apply]
    split_ifs <;> simp [add_comm]
  map_smul' x T := by
    ext row col
    simp only [koszulMatrix_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> simp [mul_neg]

/-- Applying the linear wrapper is definitionally the coordinate matrix. -/
@[simp] theorem koszulLinear_apply {k : Type*} [Field k] {a b c : ℕ}
    (T : Tensor k a b c) : koszulLinear k a b c T = koszulMatrix T := rfl

private def simpleKoszulLeft {k : Type*} [Field k] {a c : ℕ}
    (u : Fin a → k) (w : Fin c → k) :
    Matrix (Fin c × KoszulPair a) (Fin a) k := fun row s =>
  (if s = row.2.1.2 then u row.2.1.1
   else if s = row.2.1.1 then -u row.2.1.2 else 0) * w row.1

private def simpleKoszulRight {k : Type*} [Field k] {a b : ℕ}
    (v : Fin b → k) : Matrix (Fin a) (Fin b × Fin a) k := fun s col =>
  if s = col.2 then v col.1 else 0

private theorem koszulMatrix_simple_factor {k : Type*} [Field k] {a b c : ℕ}
    (u : Fin a → k) (v : Fin b → k) (w : Fin c → k) :
    koszulMatrix (fun i j l => u i * v j * w l) =
      simpleKoszulLeft u w * simpleKoszulRight v := by
  classical
  ext row col
  simp only [koszulMatrix_apply, Matrix.mul_apply, simpleKoszulLeft,
    simpleKoszulRight]
  simp [Finset.sum_ite_eq', mul_assoc]
  split_ifs <;> ring

private theorem simpleKoszulLeft_mulVec_u {k : Type*} [Field k] {a c : ℕ}
    (u : Fin a → k) (w : Fin c → k) :
    (simpleKoszulLeft u w).mulVecLin u = 0 := by
  classical
  funext row
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    simpleKoszulLeft, Pi.zero_apply]
  calc
    (∑ s, (if s = row.2.1.2 then u row.2.1.1
        else if s = row.2.1.1 then -u row.2.1.2 else 0) * w row.1 * u s) =
        ∑ s, ((if row.2.1.2 = s then u row.2.1.1 * w row.1 * u s else 0) +
          (if row.2.1.1 = s then -u row.2.1.2 * w row.1 * u s else 0)) := by
      apply Finset.sum_congr rfl
      intro s _hs
      by_cases hq : s = row.2.1.2
      · subst s
        simp [ne_of_lt row.2.2]
      · by_cases hp : s = row.2.1.1
        · subst s
          have hqp : row.2.1.2 ≠ row.2.1.1 := ne_of_gt row.2.2
          simp [hq, hqp]
        · simp [hq, hp, Ne.symm hq, Ne.symm hp]
    _ = 0 := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, neg_mul]
      ring

private theorem simpleKoszulLeft_rank_le {k : Type*} [Field k] {a c : ℕ}
    (u : Fin a → k) (w : Fin c → k) :
    (simpleKoszulLeft u w).rank ≤ a.pred := by
  classical
  by_cases hu : u = 0
  · subst u
    have hzero : simpleKoszulLeft (0 : Fin a → k) w = 0 := by
      ext row s
      simp [simpleKoszulLeft]
    rw [hzero, Matrix.rank_zero]
    omega
  · have ha : 0 < a := by
      by_contra hapos
      have ha0 : a = 0 := Nat.eq_zero_of_not_pos hapos
      subst a
      exact hu (Subsingleton.elim _ _)
    have hsuccPred : Nat.succ a.pred = a := Nat.succ_pred_eq_of_pos ha
    have hker : LinearMap.ker (simpleKoszulLeft u w).mulVecLin ≠ ⊥ := by
      intro hbot
      have humem : u ∈ LinearMap.ker (simpleKoszulLeft u w).mulVecLin := by
        exact simpleKoszulLeft_mulVec_u u w
      rw [hbot, Submodule.mem_bot] at humem
      exact hu humem
    have hkerDim : 1 ≤ Module.finrank k
        (LinearMap.ker (simpleKoszulLeft u w).mulVecLin) :=
      Submodule.one_le_finrank_iff.mpr hker
    have hrankNull := LinearMap.finrank_range_add_finrank_ker
      (simpleKoszulLeft u w).mulVecLin
    rw [Module.finrank_pi, Fintype.card_fin] at hrankNull
    rw [Matrix.rank]
    omega

/-- Every simple tensor has Koszul-matrix rank at most `a.pred`, the total,
edge-safe form of the usual `a - 1` bound.  The proof factors through the `a`
U-columns and uses the genuine kernel vector `u`: the `(p,q)` coordinate of
`u ∧ u` is `u_p*u_q-u_q*u_p=0`.  Hence it also covers `a=0`, `a=1`, and
characteristic two. -/
theorem koszul_rank_simple_le {k : Type*} [Field k] {a b c : ℕ}
    (u : Fin a → k) (v : Fin b → k) (w : Fin c → k) :
    (koszulLinear k a b c (fun i j l => u i * v j * w l)).rank ≤ a.pred := by
  rw [koszulLinear_apply, koszulMatrix_simple_factor]
  exact (Matrix.rank_mul_le_left _ _).trans (simpleKoszulLeft_rank_le u w)

/-- An `r`-term ordinary tensor decomposition gives Koszul rank at most
`r * a.pred`; here `a.pred` is the total, edge-safe form of the usual
`a - 1` factor. -/
theorem koszul_rank_le_mul_of_rankLE {k : Type*} [Field k] {a b c r : ℕ}
    {T : Tensor k a b c} (hT : RankLE T r) :
    (koszulLinear k a b c T).rank ≤ r * a.pred :=
  rank_linearMap_le_mul_of_rankLE (koszulLinear k a b c) koszul_rank_simple_le hT

/-- A nonzero `m × m` Koszul minor and an `r`-term decomposition certify the
numerical inequality `m ≤ r * a.pred`, using the total edge-safe version of
the usual `a - 1` factor. -/
theorem koszul_le_mul_of_minor_ne_zero_of_rankLE {k : Type*} [Field k]
    {a b c r m : ℕ} (ri : Fin m → Fin c × KoszulPair a)
    (ci : Fin m → Fin b × Fin a) {T : Tensor k a b c}
    (hdet : (((koszulLinear k a b c) T).submatrix ri ci).det ≠ 0)
    (hT : RankLE T r) : m ≤ r * a.pred :=
  le_mul_of_submatrix_det_ne_zero_of_rankLE (koszulLinear k a b c)
    koszul_rank_simple_le ri ci hdet hT

/-- Division-free strict-threshold certificate: a nonzero Koszul minor of
size `m` rules out rank at most `r` whenever `r * a.pred < m`; `a.pred` is
the total, edge-safe form of the usual `a - 1` factor. -/
theorem koszul_not_rankLE_of_mul_lt_of_minor_ne_zero {k : Type*} [Field k]
    {a b c r m : ℕ} (ri : Fin m → Fin c × KoszulPair a)
    (ci : Fin m → Fin b × Fin a) {T : Tensor k a b c}
    (hdet : (((koszulLinear k a b c) T).submatrix ri ci).det ≠ 0)
    (hrm : r * a.pred < m) : ¬ RankLE T r :=
  not_rankLE_of_mul_lt_of_submatrix_det_ne_zero (koszulLinear k a b c)
    koszul_rank_simple_le ri ci hdet hrm

#check @koszulMatrix_apply
#check @koszulLinear_apply
#check @koszul_rank_simple_le
#check @koszul_rank_le_mul_of_rankLE
#check @koszul_le_mul_of_minor_ne_zero_of_rankLE
#check @koszul_not_rankLE_of_mul_lt_of_minor_ne_zero

/-! Coordinate, sign, characteristic, and degeneracy audits. -/

example {k : Type*} [Field k] (T : Tensor k 2 1 1) :
    koszulMatrix T (0, ⟨(0, 1), by decide⟩) (0, 1) = T 0 0 0 := by simp

example {k : Type*} [Field k] (T : Tensor k 2 1 1) :
    koszulMatrix T (0, ⟨(0, 1), by decide⟩) (0, 0) = -T 1 0 0 := by simp

example {k : Type*} [Field k] (T : Tensor k 3 1 1) :
    koszulMatrix T (0, ⟨(0, 1), by decide⟩) (0, 2) = 0 := by simp

example : koszulMatrix (a := 2) (b := 1) (c := 1)
    (fun _ _ _ => (1 : ZMod 2))
    (0, ⟨(0, 1), by decide⟩) (0, 0) = 1 := by decide

example {k : Type*} [Field k] {b c : ℕ} (T : Tensor k 0 b c) :
    (koszulLinear k 0 b c T).rank = 0 := by
  exact Nat.le_zero.mp (koszul_rank_le_mul_of_rankLE (rankLE_mul T))

example {k : Type*} [Field k] {b c : ℕ} (T : Tensor k 1 b c) :
    (koszulLinear k 1 b c T).rank = 0 := by
  exact Nat.le_zero.mp (koszul_rank_le_mul_of_rankLE (rankLE_mul T))

private def certificateTensor : Tensor ℚ 2 1 1 := fun i _ _ => if i = 0 then 1 else 0

example : RankLE certificateTensor 1 := by
  refine ⟨fun _ i => if i = 0 then 1 else 0, fun _ _ => 1, fun _ _ => 1, ?_⟩
  funext i j l
  simp [certificateTensor]

example : ((koszulLinear ℚ 2 1 1 certificateTensor).submatrix
    (fun _ : Fin 1 => (0, ⟨(0, 1), by decide⟩))
    (fun _ : Fin 1 => (0, 1))).det ≠ 0 := by
  norm_num [certificateTensor]

example : ¬ RankLE certificateTensor 0 := by
  apply koszul_not_rankLE_of_mul_lt_of_minor_ne_zero
    (m := 1) (fun _ => (0, ⟨(0, 1), by decide⟩)) (fun _ => (0, 1))
  · norm_num [certificateTensor]
  · decide

#print axioms koszulMatrix_apply
#print axioms koszulLinear_apply
#print axioms koszul_rank_simple_le
#print axioms koszul_rank_le_mul_of_rankLE
#print axioms koszul_le_mul_of_minor_ne_zero_of_rankLE
#print axioms koszul_not_rankLE_of_mul_lt_of_minor_ne_zero

end BilinearComplexity
