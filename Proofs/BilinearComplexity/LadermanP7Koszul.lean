/-
  BilinearComplexity/LadermanP7Koszul — a local six-gate Koszul certificate.

  The factors below are the intrinsic/projected coordinates reconstructed from
  `cmd/visualize/static/laderman.json` for one-based Laderman gates P6--P11.
  Lean does not parse that JSON: the rational coordinates are stated explicitly
  here.  This proves only that this projected six-gate tensor is incompressible
  to five terms (also in polynomial closure).  It is not a claim about classical
  complex border rank, the full M3 tensor, or a rank-23 lower bound.
-/
import BilinearComplexity.BorderRank
import BilinearComplexity.KoszulFlattening

set_option autoImplicit false

namespace BilinearComplexity

/-- Projected first-factor coordinates of one-based Laderman gates P6--P11. -/
def ladermanP7A : Fin 6 → Fin 3 → ℚ :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![-1, 1, 0], ![-1, 0, 0], ![0, 1, -1]]

/-- Second-factor coordinates of one-based Laderman gates P6--P11. -/
def ladermanP7B : Fin 6 → Fin 4 → ℚ :=
  ![![1, 0, 0, 0], ![0, 1, 0, 0], ![1, 1, 0, 0], ![0, 0, 1, 0],
    ![0, 1, -1, 0], ![0, 0, 0, 1]]

/-- Third-factor coordinates of one-based Laderman gates P6--P11. -/
def ladermanP7C : Fin 6 → Fin 4 → ℚ :=
  ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1],
    ![0, -1, -1, 0], ![0, 1, 0, 1]]

/-- The projected P6--P11 tensor, defined transparently as its six simple terms. -/
def ladermanP7Tensor : Tensor ℚ 3 4 4 := fun i j l =>
  ∑ s : Fin 6, ladermanP7A s i * ladermanP7B s j * ladermanP7C s l

/-! Ground-truth checks for the copied factor coordinates and tensor. -/

example : ladermanP7A 3 = ![-1, 1, 0] := rfl
example : ladermanP7B 4 = ![0, 1, -1, 0] := rfl
example : ladermanP7C 5 = ![0, 1, 0, 1] := rfl
example : ladermanP7Tensor 0 0 0 = 1 := by norm_num [ladermanP7Tensor, ladermanP7A, ladermanP7B, ladermanP7C, Fin.sum_univ_succ]

private abbrev p01 : KoszulPair 3 := ⟨(0, 1), by decide⟩
private abbrev p02 : KoszulPair 3 := ⟨(0, 2), by decide⟩
private abbrev p12 : KoszulPair 3 := ⟨(1, 2), by decide⟩

/-- The eleven Koszul rows, in `(c,wedge)` order, obtained by omitting
zero-based full row 2, namely `(c=0,wedge=(1,2))`. -/
def ladermanP7Rows : Fin 11 → Fin 4 × KoszulPair 3 :=
  ![(0, p01), (0, p02),
    (1, p01), (1, p02), (1, p12),
    (2, p01), (2, p02), (2, p12),
    (3, p01), (3, p02), (3, p12)]

/-- The eleven Koszul columns, in `(b,a)` order, obtained by omitting
zero-based full column 11, namely `(b=3,a=2)`. -/
def ladermanP7Cols : Fin 11 → Fin 4 × Fin 3 :=
  ![(0, 0), (0, 1), (0, 2),
    (1, 0), (1, 1), (1, 2),
    (2, 0), (2, 1), (2, 2),
    (3, 0), (3, 1)]

/-- The selected `11 × 11` concrete Koszul minor. -/
def ladermanP7Minor : Matrix (Fin 11) (Fin 11) ℚ :=
  (koszulLinear ℚ 3 4 4 ladermanP7Tensor).submatrix ladermanP7Rows ladermanP7Cols

/-- The selected minor written out explicitly; this keeps reconstruction from
coordinate factors separate from the elementary inverse multiplication. -/
def ladermanP7MinorData : Matrix (Fin 11) (Fin 11) ℚ :=
  ![![0,1,0,0,0,0,0,0,0,0,0],
    ![0,0,1,0,0,0,0,0,0,0,0],
    ![0,0,0,-1,1,0,0,-1,0,-1,0],
    ![0,0,0,0,0,1,0,0,-1,1,0],
    ![0,0,0,0,0,1,0,0,0,0,1],
    ![0,0,0,0,1,0,0,-1,0,0,0],
    ![-1,0,0,-1,0,1,0,0,-1,0,0],
    ![0,-1,0,0,-1,0,0,0,0,0,0],
    ![0,0,0,0,0,0,-1,-1,0,-1,0],
    ![0,0,0,0,0,0,0,0,-1,1,0],
    ![0,0,0,0,0,0,0,0,1,0,1]]

set_option maxHeartbeats 2000000 in
/-- Reconstruction check: the factor sum and explicit selectors give exactly
the displayed selected minor. -/
theorem ladermanP7Minor_eq_data : ladermanP7Minor = ladermanP7MinorData := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ladermanP7Minor, ladermanP7MinorData, ladermanP7Rows,
      ladermanP7Cols, ladermanP7Tensor, ladermanP7A, ladermanP7B, ladermanP7C,
      koszulLinear, koszulMatrix, Fin.sum_univ_succ, Matrix.cons_val_two,
      Matrix.cons_val_three] <;> decide

/-- An explicit right inverse for the selected Koszul minor. -/
def ladermanP7MinorInverse : Matrix (Fin 11) (Fin 11) ℚ :=
  ![![0,0,1,1,0,-1,-1,0,0,0,0],
    ![1,0,0,0,0,0,0,0,0,0,0],
    ![0,1,0,0,0,0,0,0,0,0,0],
    ![0,0,-1,-1,1,1,0,0,0,0,-1],
    ![-1,0,0,0,0,0,0,-1,0,0,0],
    ![0,0,0,1,0,0,0,0,0,-1,0],
    ![1,0,0,-1,1,1,0,1,-1,0,-1],
    ![-1,0,0,0,0,-1,0,-1,0,0,0],
    ![0,0,0,1,-1,0,0,0,0,-1,1],
    ![0,0,0,1,-1,0,0,0,0,0,1],
    ![0,0,0,-1,1,0,0,0,0,1,0]]

example : ladermanP7MinorData 0 1 = 1 := rfl
example : ladermanP7MinorInverse 0 2 = 1 := rfl

/-! Selector and sign audits against the framework's row/column conventions. -/

example : ladermanP7Rows 2 = (1, p01) := rfl
example : ladermanP7Rows 10 = (3, p12) := rfl
example : ladermanP7Cols 10 = (3, 1) := rfl
example : koszulMatrix ladermanP7Tensor (0, p01) (0, 1) = 1 := by
  norm_num [ladermanP7Tensor, ladermanP7A, ladermanP7B, ladermanP7C, koszulMatrix, Fin.sum_univ_succ]
example : koszulMatrix ladermanP7Tensor (1, p01) (1, 0) = -1 := by
  norm_num [ladermanP7Tensor, ladermanP7A, ladermanP7B, ladermanP7C, koszulMatrix, Fin.sum_univ_succ]
example : koszulMatrix ladermanP7Tensor (0, p12) (0, 2) = 0 := by
  norm_num [ladermanP7Tensor, ladermanP7A, ladermanP7B, ladermanP7C, koszulMatrix, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000 in
/-- Kernel-checked arithmetic certificate that the displayed matrix really is
a right inverse of the selected concrete minor. -/
theorem ladermanP7Minor_mul_inverse :
    ladermanP7Minor * ladermanP7MinorInverse = 1 := by
  rw [ladermanP7Minor_eq_data]
  ext i j
  simp only [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [ladermanP7MinorData, ladermanP7MinorInverse, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.cons_val_three]

/-- The determinant of the selected `11 × 11` Koszul minor is nonzero. -/
theorem ladermanP7Minor_det_ne_zero : ladermanP7Minor.det ≠ 0 :=
  Matrix.det_ne_zero_of_right_inverse ladermanP7Minor_mul_inverse

/-- The P6--P11 projected tensor has an explicit six-term decomposition. -/
theorem ladermanP7_rankLE_six : RankLE ladermanP7Tensor 6 := by
  exact ⟨ladermanP7A, ladermanP7B, ladermanP7C, rfl⟩

/-- The P6--P11 projected tensor cannot be expressed as five simple tensors. -/
theorem ladermanP7_not_rankLE_five : ¬ RankLE ladermanP7Tensor 5 := by
  apply koszul_not_rankLE_of_mul_lt_of_minor_ne_zero ladermanP7Rows ladermanP7Cols
  · exact ladermanP7Minor_det_ne_zero
  · decide

/-- The polynomial matrix whose entries are the signed tensor-coordinate
variables in the `p=1` Koszul construction. -/
noncomputable def ladermanP7SymbolicKoszul : SymbolicMatrixLift (koszulLinear ℚ 3 4 4) where
  matrix row col :=
    if col.2 = row.2.1.2 then MvPolynomial.X (row.2.1.1, col.1, row.1)
    else if col.2 = row.2.1.1 then -MvPolynomial.X (row.2.1.2, col.1, row.1)
    else 0
  eval_matrix T row col := by
    simp only [koszulLinear_apply, koszulMatrix_apply]
    split_ifs <;> simp [entries]

example : ladermanP7SymbolicKoszul.matrix (0, p01) (0, 1) =
    MvPolynomial.X (0, 0, 0) := rfl

/-- Polynomial-closure border rank of the projected tensor is at most six. -/
theorem ladermanP7_borderRankLE_six : BorderRankLE ladermanP7Tensor 6 :=
  ladermanP7_rankLE_six.borderRankLE

/-- The projected tensor is not in the polynomial closure of the rank-at-most-five
locus, certified by the same Koszul minor with nonzero determinant and an explicit
symbolic lift. -/
theorem ladermanP7_not_borderRankLE_five : ¬ BorderRankLE ladermanP7Tensor 5 := by
  intro hborder
  have hzero := hborder.det_submatrix_eq_zero (q := 2) ladermanP7SymbolicKoszul
    koszul_rank_simple_le ladermanP7Rows ladermanP7Cols
  exact ladermanP7Minor_det_ne_zero hzero

/-- Joint non-vacuity audit: the explicit six-term witness and the nonzero
determinant of the selected minor hold simultaneously for the same projected tensor. -/
theorem ladermanP7_certificate_nonvacuous :
    RankLE ladermanP7Tensor 6 ∧ ladermanP7Minor.det ≠ 0 :=
  ⟨ladermanP7_rankLE_six, ladermanP7Minor_det_ne_zero⟩

#check @ladermanP7_rankLE_six
#check @ladermanP7_not_rankLE_five
#check @ladermanP7_borderRankLE_six
#check @ladermanP7_not_borderRankLE_five
#check @ladermanP7_certificate_nonvacuous

#print axioms ladermanP7Minor_eq_data
#print axioms ladermanP7Minor_mul_inverse
#print axioms ladermanP7Minor_det_ne_zero
#print axioms ladermanP7_rankLE_six
#print axioms ladermanP7_not_rankLE_five
#print axioms ladermanP7_borderRankLE_six
#print axioms ladermanP7_not_borderRankLE_five
#print axioms ladermanP7_certificate_nonvacuous

end BilinearComplexity
