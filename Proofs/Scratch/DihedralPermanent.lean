/-
  Scratch/DihedralPermanent — the permanent of the dihedral character table
  (OEIS A085805).

  A085805's name reads "the dihedral group D_k" and never defines `D_k`;
  this file reads `k` as the group ORDER — a data-pinned interpretation, not
  OEIS text: the permanent of `DihedralGroup(m)`'s table (order `2m`) is
  nonzero at `m = 2, 10, 18`, i.e. orders 4, 20, 36 = the entry's terms, and
  the entry's original cross-ref A017089 (`a(n) = 8n + 2`) is exactly that
  index sequence.  The entry's comment — unsigned, hence by OEIS convention
  due to the submitter Yuval Dekel (Jul 24 2003) — reads "Probably these are
  the numbers of the form 16m+4", i.e. `k ≡ 4 (mod 16)`.

  RESULTS (all sorry-free; axioms ⊆ {propext, Classical.choice, Quot.sound}):
  * `permanent_dihedralTableOdd` — vanishing for all odd rotation numbers
    (group orders ≡ 2 mod 4), over any commutative ring, for any entries.
  * `permanent_dihedralTableEven_eq_zero` — vanishing for rotation
    half-order `M ≢ 1 (mod 4)` (group order `4M ≢ 4 (mod 16)`), over any
    commutative ring whose entry function satisfies
    `C (M k - t) = (-1)^k C t`; `permanent_dihedralTableEven_cos_eq_zero`
    instantiates it over `ℝ` with `C t = 2 cos (π t / M)`.  Together these
    settle the VANISHING direction of the conjecture for the explicit
    table family.
  * `permanent_dihedralTableEven_eq_four_mul` — for `M ≡ 1 (mod 4)` the
    permanent reduces to `4 · perm (tableAB C M)`.
  * `permanent_dihedralTableEven_one` (order 4: value 8) and
    `permanent_dihedralTable_order_twenty` (order 20: value -576) —
    certified nonzero instances; the latter via an exact `ℤ√5` kernel
    computation bridged through `2cos(π/5) = (1+√5)/2`.
  * `NonvanishingConjecture` — the open direction (`M ≡ 1 (mod 4)` implies
    a nonzero permanent), stated as a `Prop`, not asserted.  Order 36
    (`M = 9`, exact value -13824) needs exact arithmetic in the cubic field
    `ℚ(cos(π/9))` and a 10! ≈ 3.6M-monomial certificate, out of kernel
    reach here; it is covered by the conjecture statement only.

  The vanishing proof is a multilinear expansion in the four
  linear-character rows followed by two sign involutions (a column scaling
  and a column permutation), all over an arbitrary commutative ring with a
  single functional equation for the "cosine" entries.

  Conventions (order `2m` dihedral group):
  * `m = 2M` even: `M + 3` conjugacy classes.  Columns `0..M` are the
    rotation classes `r^j`, column `M+1` is the reflection class of `s`,
    column `M+2` the reflection class of `rs`.  Rows `0..3` are the four
    linear characters (trivial, determinant, and the two characters with
    `r ↦ -1`), row `3+h` (for `1 ≤ h ≤ M-1`) is the two-dimensional
    character `χ_h` with `χ_h(r^j) = 2cos(π h j / M)` and `χ_h = 0` on
    reflections.
  * `m = 2K+1` odd: `K + 2` classes.  Columns `0..K` are rotations, column
    `K+1` the single reflection class; rows are trivial, sign, and `χ_h`
    (`1 ≤ h ≤ K`).

  DISCLOSURE: the matrices here are explicit data.  The claim that
  `dihedralTableEven`/`dihedralTableOdd` coincide with the character table
  of `DihedralGroup m` as defined via Mathlib's representation theory is
  NOT formalized (that bridge is a separate project); the theorems below
  are about the explicit family, which follows the standard textbook
  character table of dihedral groups.  Ground-truth `example`s pin the
  small cases against independently computed data (Sage/GAP character
  tables, exact cyclotomic arithmetic).

  Route (verified exactly in Sage for `M ≤ 10` before formalization):
  with `U/V` the shared rotation parts of the linear rows and `W/X` their
  reflection parts, multilinearity gives
      perm T = -perm (W,W,V,V,χ) - perm (U,U,X,X,χ).
  Scaling column `r^j` by `(-1)^j` and column `rs` by `-1` carries the
  second matrix into the first up to a row involution, giving
      perm (W,W,V,V,χ) = (-1)^{M(M+1)/2 + 1} · perm (U,U,X,X,χ);
  the column involution `r^j ↦ r^{M-j}` scales row `χ_h` by `(-1)^h`, so
      perm (U,U,X,X,χ) = (-1)^{M(M-1)/2} · perm (U,U,X,X,χ).
  Together these kill the permanent unless `M ≡ 1 (mod 4)`, i.e. unless
  the group order `4M ≡ 4 (mod 16)`.  For odd `m` the two linear rows agree
  away from the reflection column and the permanent vanishes outright.
-/
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.Zsqrtd.ToReal

set_option autoImplicit false

namespace DihedralPermanent

open Matrix Finset Equiv

/-! ## General permanent API

Mathlib's `Matrix.permanent` file provides permutation invariance and
single-row scaling; here we add additivity in a row, a swap identity, a
"difference of squares" pair expansion, a Hall-type vanishing criterion,
all-row/all-column scaling, Laplace expansion along column zero, and a
computable evaluator `permFin` for explicit matrices. -/

section PermanentAPI

variable {n : Type*} [DecidableEq n] [Fintype n]
variable {R : Type*} [CommRing R]

/-- The permanent is additive in each row. -/
theorem permanent_updateRow_add (A : Matrix n n R) (i : n) (u v : n → R) :
    (A.updateRow i (u + v)).permanent
      = (A.updateRow i u).permanent + (A.updateRow i v).permanent := by
  simp only [Matrix.permanent, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hprod : ∀ w : n → R,
      ∏ c, (A.updateRow i w) (σ c) c
        = w (σ⁻¹ i) * ∏ c ∈ Finset.univ.erase (σ⁻¹ i), A (σ c) c := by
    intro w
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (σ⁻¹ i))]
    have hself : (A.updateRow i w) (σ (σ⁻¹ i)) (σ⁻¹ i) = w (σ⁻¹ i) := by
      rw [Equiv.Perm.inv_def, Equiv.apply_symm_apply, Matrix.updateRow_self]
    rw [hself]
    congr 1
    refine Finset.prod_congr rfl fun c hc => ?_
    have hci : σ c ≠ i := by
      intro h
      exact (Finset.mem_erase.mp hc).1
        (by rw [← h, Equiv.Perm.inv_def, Equiv.symm_apply_apply])
    rw [Matrix.updateRow_ne hci]
  rw [hprod, hprod, hprod, Pi.add_apply, add_mul]

/-- Negating the fresh row negates the permanent. -/
theorem permanent_updateRow_neg (A : Matrix n n R) (i : n) (u : n → R) :
    (A.updateRow i (-u)).permanent = -(A.updateRow i u).permanent := by
  have h : -u = (-1 : R) • u := by rw [neg_one_smul]
  rw [h, Matrix.permanent_updateRow_smul, neg_one_mul]

/-- Exchanging the fresh values written into two distinct rows does not
change the permanent. -/
theorem permanent_updateRow_swap (A : Matrix n n R) {i k : n} (hik : i ≠ k)
    (u v : n → R) :
    ((A.updateRow i u).updateRow k v).permanent
      = ((A.updateRow i v).updateRow k u).permanent := by
  have hmat : (A.updateRow i v).updateRow k u
      = ((A.updateRow i u).updateRow k v).submatrix (Equiv.swap i k) id := by
    ext a b
    rcases eq_or_ne a i with rfl | hai
    · simp only [Matrix.submatrix_apply, id_eq, Equiv.swap_apply_left,
        Matrix.updateRow_self, Matrix.updateRow_ne hik]
    · rcases eq_or_ne a k with rfl | hak
      · simp only [Matrix.submatrix_apply, id_eq, Equiv.swap_apply_right,
          Matrix.updateRow_self, Matrix.updateRow_ne hik]
      · simp only [Matrix.submatrix_apply, id_eq,
          Equiv.swap_apply_of_ne_of_ne hai hak,
          Matrix.updateRow_ne hai, Matrix.updateRow_ne hak]
  rw [hmat, Matrix.permanent_permute_cols]

/-- "Difference of squares" for a pair of rows: writing `p + q` and `p - q`
into two distinct rows, the mixed terms of the multilinear expansion cancel
and only the pure terms survive. -/
theorem permanent_updateRow_pair (A : Matrix n n R) {i k : n} (hik : i ≠ k)
    (p q : n → R) :
    ((A.updateRow i (p + q)).updateRow k (p - q)).permanent
      = ((A.updateRow i p).updateRow k p).permanent
        - ((A.updateRow i q).updateRow k q).permanent := by
  have hexp : ∀ w : n → R,
      ((A.updateRow i (p + q)).updateRow k w).permanent
        = ((A.updateRow i p).updateRow k w).permanent
          + ((A.updateRow i q).updateRow k w).permanent := by
    intro w
    rw [Matrix.updateRow_comm _ hik, permanent_updateRow_add,
      Matrix.updateRow_comm _ hik.symm, Matrix.updateRow_comm _ hik.symm]
  have hsub : p - q = p + -q := sub_eq_add_neg p q
  rw [hsub, permanent_updateRow_add, permanent_updateRow_neg, hexp p, hexp q,
    permanent_updateRow_swap A hik q p]
  ring

/-- Hall-type vanishing: if every nonzero entry of the columns in `s` lies in
a row from `t`, and `t` is strictly smaller than `s`, the permanent is zero
(the columns of `s` cannot be matched injectively into `t`). -/
theorem permanent_eq_zero_of_cols_subset (A : Matrix n n R) (s t : Finset n)
    (hst : t.card < s.card) (hz : ∀ j ∈ s, ∀ i, i ∉ t → A i j = 0) :
    A.permanent = 0 := by
  refine Finset.sum_eq_zero fun σ _ => ?_
  obtain ⟨j, hjs, hjt⟩ : ∃ j ∈ s, σ j ∉ t := by
    by_contra h
    push Not at h
    exact absurd (Finset.card_le_card_of_injOn σ h (σ.injective.injOn))
      (Nat.not_le.mpr hst)
  exact Finset.prod_eq_zero (Finset.mem_univ j) (hz j hjs (σ j) hjt)

/-- Row version of `permanent_eq_zero_of_cols_subset`: rows in `s` supported
inside a strictly smaller column set `t` force a zero permanent. -/
theorem permanent_eq_zero_of_rows_subset (A : Matrix n n R) (s t : Finset n)
    (hst : t.card < s.card) (hz : ∀ i ∈ s, ∀ j, j ∉ t → A i j = 0) :
    A.permanent = 0 := by
  rw [← Matrix.permanent_transpose]
  exact permanent_eq_zero_of_cols_subset Aᵀ s t hst
    (fun j hj i hi => hz j hj i hi)

/-- Scaling every column `j` by `g j` multiplies the permanent by `∏ j, g j`. -/
theorem permanent_col_scale (A : Matrix n n R) (g : n → R) :
    (Matrix.of fun i j => g j * A i j).permanent
      = (∏ j, g j) * A.permanent := by
  simp only [Matrix.permanent, Matrix.of_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun σ _ => by rw [Finset.prod_mul_distrib]

/-- Scaling every row `i` by `w i` multiplies the permanent by `∏ i, w i`. -/
theorem permanent_row_scale (A : Matrix n n R) (w : n → R) :
    (Matrix.of fun i j => w i * A i j).permanent
      = (∏ i, w i) * A.permanent := by
  simp only [Matrix.permanent, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_mul_distrib, Equiv.prod_comp σ w]

/-- Ring homomorphisms commute with the permanent. -/
theorem permanent_map {S : Type*} [CommRing S] (f : R →+* S)
    (A : Matrix n n R) :
    (A.map f).permanent = f A.permanent := by
  simp only [Matrix.permanent, Matrix.map_apply, map_sum, map_prod]

end PermanentAPI

section Laplace

variable {R : Type*} [CommRing R]

/-- Laplace expansion of the permanent along column `0` (the signless analogue
of `Matrix.det_succ_column_zero`). -/
theorem permanent_succ_column_zero {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) R) :
    A.permanent
      = ∑ p : Fin (N + 1), A p 0 * (A.submatrix p.succAbove Fin.succ).permanent := by
  rw [Matrix.permanent, Finset.univ_perm_fin_succ, ← Finset.univ_product_univ]
  simp only [Finset.sum_map, Equiv.toEmbedding_apply, Finset.sum_product]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hsplit : ∀ e : Equiv.Perm (Fin N),
      ∏ j, A (Equiv.Perm.decomposeFin.symm (p, e) j) j
        = A p 0 * ∏ x : Fin N, A (Equiv.swap 0 p ((e x).succ)) x.succ := by
    intro e
    rw [Fin.prod_univ_succ]
    simp only [Equiv.Perm.decomposeFin_symm_apply_zero,
      Equiv.Perm.decomposeFin_symm_apply_succ]
  simp only [hsplit, ← Finset.mul_sum]
  congr 1
  induction p using Fin.cases with
  | zero =>
      simp only [Equiv.swap_self, Equiv.refl_apply, Fin.succAbove_zero,
        Matrix.permanent, Matrix.submatrix_apply]
  | succ i =>
      have hswap : ∀ (e : Equiv.Perm (Fin N)) (x : Fin N),
          Equiv.swap 0 i.succ ((e x).succ)
            = i.succ.succAbove ((i.cycleRange * e) x) := by
        intro e x
        rw [Equiv.Perm.mul_apply, Fin.succAbove_cycleRange]
      simp only [hswap]
      rw [Matrix.permanent]
      simp only [Matrix.submatrix_apply]
      exact (Group.mulLeft_bijective i.cycleRange).sum_comp
        (fun e => ∏ x : Fin N, A (i.succ.succAbove (e x)) x.succ)

/-- Computable signless first-column Laplace expansion; used to evaluate
permanents of explicit matrices by kernel reduction (`decide`). -/
def permFin : (N : ℕ) → Matrix (Fin N) (Fin N) R → R
  | 0, _ => 1
  | N + 1, A => ∑ p : Fin (N + 1), A p 0 * permFin N (A.submatrix p.succAbove Fin.succ)

/-- `permFin` computes the permanent. -/
theorem permFin_eq_permanent :
    ∀ (N : ℕ) (A : Matrix (Fin N) (Fin N) R), permFin N A = A.permanent
  | 0, A => by rw [permFin, Matrix.permanent_isEmpty]
  | N + 1, A => by
      rw [permFin, permanent_succ_column_zero]
      exact Finset.sum_congr rfl fun p _ => by rw [permFin_eq_permanent N]

end Laplace

/-! ## The dihedral character tables as explicit matrices

For `m = 2M` the table is `(M+3) × (M+3)`: columns `0..M` are the rotation
classes `r^j`, column `M+1` the reflection class of `s`, column `M+2` the
reflection class of `rs`; rows `0..3` are the linear characters
(trivial `= U + W`, determinant `= U - W`, and the two characters killing
`r^2` `= V ± X`), row `3+h` is `χ_h`.  The entry function `C : ℤ → R`
abstracts `t ↦ 2 cos (π t / M)`; every theorem states exactly which
functional equation of `C` it consumes. -/

section Tables

variable {R : Type*} [CommRing R]

/-- Shared rotation part of the trivial/determinant rows: `1` on the rotation
columns `0..M`, `0` on the two reflection columns. -/
def rowU (M : ℕ) : Fin (M + 3) → R := fun j => if (j : ℕ) ≤ M then 1 else 0

/-- Shared rotation part of the two order-two linear rows: `(-1)^j` on
rotation column `j`, `0` on the reflection columns. -/
def rowV (M : ℕ) : Fin (M + 3) → R :=
  fun j => if (j : ℕ) ≤ M then (-1) ^ (j : ℕ) else 0

/-- Indicator of the reflection column `M+1` (class of `s`). -/
def rowA (M : ℕ) : Fin (M + 3) → R := fun j => if (j : ℕ) = M + 1 then 1 else 0

/-- Indicator of the reflection column `M+2` (class of `rs`). -/
def rowB (M : ℕ) : Fin (M + 3) → R := fun j => if (j : ℕ) = M + 2 then 1 else 0

/-- Common reflection part of the trivial/determinant rows. -/
def rowW (M : ℕ) : Fin (M + 3) → R := rowA M + rowB M

/-- Common reflection part (up to sign) of the two order-two linear rows. -/
def rowX (M : ℕ) : Fin (M + 3) → R := rowA M - rowB M

/-- Row of the two-dimensional character `χ_h`: `C (h·j)` on rotation column
`j`, `0` on the reflection columns. -/
def rowChi (C : ℤ → R) (M h : ℕ) : Fin (M + 3) → R :=
  fun j => if (j : ℕ) ≤ M then C ((h : ℤ) * ((j : ℕ) : ℤ)) else 0

/-- Skeleton of the even table: four prescribed rows `r0..r3` on top of the
`χ_h` rows (`h = (i : ℕ) - 3` in row `i ≥ 4`). -/
def tableOf (C : ℤ → R) (M : ℕ) (r0 r1 r2 r3 : Fin (M + 3) → R) :
    Matrix (Fin (M + 3)) (Fin (M + 3)) R :=
  Matrix.of fun i j =>
    if (i : ℕ) = 0 then r0 j
    else if (i : ℕ) = 1 then r1 j
    else if (i : ℕ) = 2 then r2 j
    else if (i : ℕ) = 3 then r3 j
    else rowChi C M ((i : ℕ) - 3) j

/-- The character table of the dihedral group of order `4M` (rotation order
`m = 2M`), as explicit data.  For `M = 1` this is the Klein four-group table.
The intended entry function is `C t = 2 cos (π t / M)`; the vanishing
theorems consume only the functional equation
`C (M k - t) = (-1)^k C t`. -/
def dihedralTableEven (C : ℤ → R) (M : ℕ) :
    Matrix (Fin (M + 3)) (Fin (M + 3)) R :=
  tableOf C M (rowU M + rowW M) (rowU M - rowW M) (rowV M + rowX M)
    (rowV M - rowX M)

/-- All-ones rotation part for the odd table (`m = 2K+1` rotations `0..K`). -/
def rowZ (K : ℕ) : Fin (K + 2) → R := fun j => if (j : ℕ) ≤ K then 1 else 0

/-- Indicator of the single reflection column `K+1` of the odd table. -/
def rowRefl (K : ℕ) : Fin (K + 2) → R :=
  fun j => if (j : ℕ) = K + 1 then 1 else 0

/-- `χ_h` row of the odd table. -/
def rowChiOdd (C : ℤ → R) (K h : ℕ) : Fin (K + 2) → R :=
  fun j => if (j : ℕ) ≤ K then C ((h : ℤ) * ((j : ℕ) : ℤ)) else 0

/-- The character table of the dihedral group of order `2(2K+1)`, as explicit
data: columns `0..K` are the rotation classes, column `K+1` the single
reflection class; rows are trivial (`Z + refl`), sign (`Z - refl`), and `χ_h`
(`h = (i : ℕ) - 1` in row `i ≥ 2`).  The intended entry function is
`C t = 2 cos (2 π t / (2K+1))`, but the vanishing theorem holds for every
`C`. -/
def dihedralTableOdd (C : ℤ → R) (K : ℕ) :
    Matrix (Fin (K + 2)) (Fin (K + 2)) R :=
  Matrix.of fun i j =>
    if (i : ℕ) = 0 then rowZ K j + rowRefl K j
    else if (i : ℕ) = 1 then rowZ K j - rowRefl K j
    else rowChiOdd C K ((i : ℕ) - 1) j

/-- Ground truth: at `M = 1` the even table is the Klein four-group character
table, independently of `C`. -/
example (C : ℤ → ℚ) :
    dihedralTableEven C 1 =
      !![1, 1, 1, 1; 1, 1, -1, -1; 1, -1, 1, -1; 1, -1, -1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [dihedralTableEven, tableOf, rowU, rowV, rowW, rowX, rowA, rowB]

/-- Ground truth: at `K = 1` (the symmetric group `S₃`, order 6) the odd
table has rows `(1,1,1)`, `(1,1,-1)`, `(C 0, C 1, 0)`; with
`C t = 2cos(2πt/3)` this is the standard `S₃` table `(2, -1, 0)`. -/
example (C : ℤ → ℚ) :
    dihedralTableOdd C 1 = !![1, 1, 1; 1, 1, -1; C 0, C 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [dihedralTableOdd, rowZ, rowRefl, rowChiOdd]

end Tables

/-! ## Vanishing for odd rotation order (group order ≡ 2 mod 4) -/

section OddCase

variable {R : Type*} [CommRing R]

/-- **Vanishing, odd case.**  The permanent of the dihedral character table
with an odd rotation number `m = 2K+1` (group order `2m ≡ 2 mod 4`) is zero,
over any commutative ring and for every entry function `C`: the trivial and
sign rows agree away from the reflection column, and the multilinear
expansion in these two rows collapses. -/
theorem permanent_dihedralTableOdd (C : ℤ → R) (K : ℕ) :
    (dihedralTableOdd C K).permanent = 0 := by
  have h01 : (0 : Fin (K + 2)) ≠ 1 := by
    intro h
    exact absurd (congrArg Fin.val h) (by simp)
  have hstack : dihedralTableOdd C K
      = ((dihedralTableOdd C K).updateRow 0 (rowZ K + rowRefl K)).updateRow 1
          (rowZ K - rowRefl K) := by
    ext i j
    rcases eq_or_ne i 1 with rfl | hi1
    · rw [Matrix.updateRow_self]
      simp only [dihedralTableOdd, Matrix.of_apply, Fin.val_one]
      norm_num
    · rw [Matrix.updateRow_ne hi1]
      rcases eq_or_ne i 0 with rfl | hi0
      · rw [Matrix.updateRow_self]
        simp only [dihedralTableOdd, Matrix.of_apply, Fin.val_zero]
        norm_num
      · rw [Matrix.updateRow_ne hi0]
  rw [hstack, permanent_updateRow_pair _ h01]
  have hz : (((dihedralTableOdd C K).updateRow 0 (rowZ K)).updateRow 1
      (rowZ K)).permanent = 0 := by
    refine permanent_eq_zero_of_cols_subset _ {(⟨K + 1, by omega⟩ : Fin (K + 2))} ∅
      (by simp) ?_
    intro j hj i _
    have hjv : (j : ℕ) = K + 1 := by
      have := Finset.mem_singleton.mp hj
      exact congrArg Fin.val this
    have hrowZ : rowZ (R := R) K j = 0 := by
      simp only [rowZ, hjv]
      norm_num
    rcases eq_or_ne i 1 with rfl | hi1
    · rw [Matrix.updateRow_self]; exact hrowZ
    · rw [Matrix.updateRow_ne hi1]
      rcases eq_or_ne i 0 with rfl | hi0
      · rw [Matrix.updateRow_self]; exact hrowZ
      · rw [Matrix.updateRow_ne hi0]
        have hi0v : (i : ℕ) ≠ 0 := fun h => hi0 (Fin.ext h)
        have hi1v : (i : ℕ) ≠ 1 := fun h => hi1 (Fin.ext h)
        simp only [dihedralTableOdd, Matrix.of_apply, if_neg hi0v, if_neg hi1v,
          rowChiOdd, hjv]
        norm_num
  have hr : (((dihedralTableOdd C K).updateRow 0 (rowRefl K)).updateRow 1
      (rowRefl K)).permanent = 0 := by
    refine permanent_eq_zero_of_rows_subset _ {0, 1}
      {(⟨K + 1, by omega⟩ : Fin (K + 2))} (by simp [h01]) ?_
    intro i hi j hj
    have hjv : (j : ℕ) ≠ K + 1 := by
      intro h
      exact hj (Finset.mem_singleton.mpr (Fin.ext h))
    have hrefl : rowRefl (R := R) K j = 0 := by
      simp only [rowRefl, if_neg hjv]
    rcases Finset.mem_insert.mp hi with rfl | hi1
    · rw [Matrix.updateRow_ne h01, Matrix.updateRow_self]; exact hrefl
    · rw [Finset.mem_singleton.mp hi1, Matrix.updateRow_self]; exact hrefl
  rw [hz, hr, sub_zero]

end OddCase

/-! ## Vanishing for even rotation order (group order ≡ 0 mod 4)

All working lemmas are stated at rotation half-order `M + 1`, so the four
linear rows (indices `0..3` of `Fin (M+1+3)`) always exist; the public
theorem restates the result for arbitrary `1 ≤ M`.  Throughout, `hC` is the
single functional equation `C ((M+1)·k - t) = (-1)^k · C t`, satisfied by the
intended entries `C t = 2 cos (π t / (M+1))`. -/

section EvenCase

variable {R : Type*} [CommRing R]

private lemma updateRow_tableOf_zero (C : ℤ → R) (M : ℕ)
    (s0 s1 s2 s3 r : Fin (M + 1 + 3) → R) :
    (tableOf C (M + 1) s0 s1 s2 s3).updateRow ⟨0, by omega⟩ r
      = tableOf C (M + 1) r s1 s2 s3 := by
  ext i j
  rcases eq_or_ne i ⟨0, by omega⟩ with rfl | hi
  · rw [Matrix.updateRow_self]
    simp only [tableOf, Matrix.of_apply, reduceIte]
  · rw [Matrix.updateRow_ne hi]
    have hv : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
    simp only [tableOf, Matrix.of_apply, if_neg hv]

private lemma updateRow_tableOf_one (C : ℤ → R) (M : ℕ)
    (s0 s1 s2 s3 r : Fin (M + 1 + 3) → R) :
    (tableOf C (M + 1) s0 s1 s2 s3).updateRow ⟨1, by omega⟩ r
      = tableOf C (M + 1) s0 r s2 s3 := by
  ext i j
  rcases eq_or_ne i ⟨1, by omega⟩ with rfl | hi
  · rw [Matrix.updateRow_self]
    simp only [tableOf, Matrix.of_apply]
    norm_num
  · rw [Matrix.updateRow_ne hi]
    have hv : (i : ℕ) ≠ 1 := fun h => hi (Fin.ext h)
    by_cases h0 : (i : ℕ) = 0
    · simp only [tableOf, Matrix.of_apply, h0, reduceIte]
    · simp only [tableOf, Matrix.of_apply, if_neg h0, if_neg hv]

private lemma updateRow_tableOf_two (C : ℤ → R) (M : ℕ)
    (s0 s1 s2 s3 r : Fin (M + 1 + 3) → R) :
    (tableOf C (M + 1) s0 s1 s2 s3).updateRow ⟨2, by omega⟩ r
      = tableOf C (M + 1) s0 s1 r s3 := by
  ext i j
  rcases eq_or_ne i ⟨2, by omega⟩ with rfl | hi
  · rw [Matrix.updateRow_self]
    simp only [tableOf, Matrix.of_apply]
    norm_num
  · rw [Matrix.updateRow_ne hi]
    have hv : (i : ℕ) ≠ 2 := fun h => hi (Fin.ext h)
    by_cases h0 : (i : ℕ) = 0
    · simp only [tableOf, Matrix.of_apply, h0, reduceIte]
    · by_cases h1 : (i : ℕ) = 1
      · simp only [tableOf, Matrix.of_apply, h1, reduceIte]
      · simp only [tableOf, Matrix.of_apply, if_neg h0, if_neg h1, if_neg hv]

private lemma updateRow_tableOf_three (C : ℤ → R) (M : ℕ)
    (s0 s1 s2 s3 r : Fin (M + 1 + 3) → R) :
    (tableOf C (M + 1) s0 s1 s2 s3).updateRow ⟨3, by omega⟩ r
      = tableOf C (M + 1) s0 s1 s2 r := by
  ext i j
  rcases eq_or_ne i ⟨3, by omega⟩ with rfl | hi
  · rw [Matrix.updateRow_self]
    simp only [tableOf, Matrix.of_apply]
    norm_num
  · rw [Matrix.updateRow_ne hi]
    have hv : (i : ℕ) ≠ 3 := fun h => hi (Fin.ext h)
    by_cases h0 : (i : ℕ) = 0
    · simp only [tableOf, Matrix.of_apply, h0, reduceIte]
    · by_cases h1 : (i : ℕ) = 1
      · simp only [tableOf, Matrix.of_apply, h1, reduceIte]
      · by_cases h2 : (i : ℕ) = 2
        · simp only [tableOf, Matrix.of_apply, h2, reduceIte]
        · simp only [tableOf, Matrix.of_apply, if_neg h0, if_neg h1,
            if_neg h2, if_neg hv]

/-- The pure `U,U,V,V` term of the expansion vanishes: both reflection
columns are identically zero. -/
private lemma permanent_tableUUVV (C : ℤ → R) (M : ℕ) :
    (tableOf C (M + 1) (rowU (M + 1)) (rowU (M + 1)) (rowV (M + 1))
      (rowV (M + 1))).permanent = 0 := by
  have hne : (⟨M + 1 + 1, by omega⟩ : Fin (M + 1 + 3)) ≠ ⟨M + 1 + 2, by omega⟩ :=
    Fin.ne_of_val_ne (show M + 1 + 1 ≠ M + 1 + 2 by omega)
  refine permanent_eq_zero_of_cols_subset _
    {⟨M + 1 + 1, by omega⟩, ⟨M + 1 + 2, by omega⟩} ∅
    (by rw [Finset.card_pair hne, Finset.card_empty]; omega) ?_
  intro j hj i _
  have hnle : ¬((j : ℕ) ≤ M + 1) := by
    rcases Finset.mem_insert.mp hj with h | h
    · have hjv : (j : ℕ) = M + 1 + 1 := by rw [h]
      omega
    · have hjv : (j : ℕ) = M + 1 + 2 := by rw [Finset.mem_singleton.mp h]
      omega
  simp only [tableOf, Matrix.of_apply]
  split_ifs <;> simp only [rowU, rowV, rowChi, if_neg hnle]

/-- The pure `W,W,X,X` term of the expansion vanishes: rows `0,1,2` are
supported in the two reflection columns. -/
private lemma permanent_tableWWXX (C : ℤ → R) (M : ℕ) :
    (tableOf C (M + 1) (rowW (M + 1)) (rowW (M + 1)) (rowX (M + 1))
      (rowX (M + 1))).permanent = 0 := by
  have hne : (⟨M + 1 + 1, by omega⟩ : Fin (M + 1 + 3)) ≠ ⟨M + 1 + 2, by omega⟩ :=
    Fin.ne_of_val_ne (show M + 1 + 1 ≠ M + 1 + 2 by omega)
  have h01 : (⟨0, by omega⟩ : Fin (M + 1 + 3)) ≠ ⟨1, by omega⟩ :=
    Fin.ne_of_val_ne (show (0 : ℕ) ≠ 1 by omega)
  have h02 : (⟨0, by omega⟩ : Fin (M + 1 + 3)) ≠ ⟨2, by omega⟩ :=
    Fin.ne_of_val_ne (show (0 : ℕ) ≠ 2 by omega)
  have h12 : (⟨1, by omega⟩ : Fin (M + 1 + 3)) ≠ ⟨2, by omega⟩ :=
    Fin.ne_of_val_ne (show (1 : ℕ) ≠ 2 by omega)
  refine permanent_eq_zero_of_rows_subset _
    {⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩}
    {⟨M + 1 + 1, by omega⟩, ⟨M + 1 + 2, by omega⟩} ?_ ?_
  · rw [Finset.card_pair hne]
    rw [Finset.card_insert_of_notMem (by simp),
      Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
    omega
  · intro i hi j hj
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    have hja : (j : ℕ) ≠ M + 1 + 1 := fun h => hj.1 (Fin.ext h)
    have hjb : (j : ℕ) ≠ M + 1 + 2 := fun h => hj.2 (Fin.ext h)
    have hentry : ∀ v : Fin (M + 1 + 3) → R,
        v = rowW (M + 1) ∨ v = rowX (M + 1) → v j = 0 := by
      rintro v (rfl | rfl) <;>
        simp only [rowW, rowX, Pi.add_apply, Pi.sub_apply, rowA, rowB,
          if_neg hja, if_neg hjb] <;>
        norm_num
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · refine Eq.trans ?_ (hentry (rowW (M + 1)) (Or.inl rfl))
      simp only [tableOf, Matrix.of_apply]
      norm_num
    · rcases Finset.mem_insert.mp hi' with rfl | hi''
      · refine Eq.trans ?_ (hentry (rowW (M + 1)) (Or.inl rfl))
        simp only [tableOf, Matrix.of_apply]
        norm_num
      · rw [Finset.mem_singleton.mp hi'']
        refine Eq.trans ?_ (hentry (rowX (M + 1)) (Or.inr rfl))
        simp only [tableOf, Matrix.of_apply]
        norm_num

private lemma tableOf_apply_zero (C : ℤ → R) (M : ℕ)
    (s0 s1 s2 s3 : Fin (M + 3) → R) {i : Fin (M + 3)} (j : Fin (M + 3))
    (h : (i : ℕ) = 0) : tableOf C M s0 s1 s2 s3 i j = s0 j := by
  simp only [tableOf, Matrix.of_apply, h, reduceIte]

private lemma tableOf_apply_one (C : ℤ → R) (M : ℕ)
    (s0 s1 s2 s3 : Fin (M + 3) → R) {i : Fin (M + 3)} (j : Fin (M + 3))
    (h : (i : ℕ) = 1) : tableOf C M s0 s1 s2 s3 i j = s1 j := by
  simp only [tableOf, Matrix.of_apply, h, reduceIte]
  norm_num

private lemma tableOf_apply_two (C : ℤ → R) (M : ℕ)
    (s0 s1 s2 s3 : Fin (M + 3) → R) {i : Fin (M + 3)} (j : Fin (M + 3))
    (h : (i : ℕ) = 2) : tableOf C M s0 s1 s2 s3 i j = s2 j := by
  simp only [tableOf, Matrix.of_apply, h, reduceIte]
  norm_num

private lemma tableOf_apply_three (C : ℤ → R) (M : ℕ)
    (s0 s1 s2 s3 : Fin (M + 3) → R) {i : Fin (M + 3)} (j : Fin (M + 3))
    (h : (i : ℕ) = 3) : tableOf C M s0 s1 s2 s3 i j = s3 j := by
  simp only [tableOf, Matrix.of_apply, h, reduceIte]
  norm_num

private lemma tableOf_apply_ge (C : ℤ → R) (M : ℕ)
    (s0 s1 s2 s3 : Fin (M + 3) → R) {i : Fin (M + 3)} (j : Fin (M + 3))
    (h : 4 ≤ (i : ℕ)) :
    tableOf C M s0 s1 s2 s3 i j = rowChi C M ((i : ℕ) - 3) j := by
  simp only [tableOf, Matrix.of_apply, if_neg (show ¬(i : ℕ) = 0 by omega),
    if_neg (show ¬(i : ℕ) = 1 by omega), if_neg (show ¬(i : ℕ) = 2 by omega),
    if_neg (show ¬(i : ℕ) = 3 by omega)]

/-- Multilinear expansion of the even table in its four linear rows: the
mixed terms cancel, the `U,U,V,V` and `W,W,X,X` terms die, and
`perm T = -perm (W,W,V,V,χ) - perm (U,U,X,X,χ)`. -/
private lemma permanent_even_expansion (C : ℤ → R) (M : ℕ) :
    (dihedralTableEven C (M + 1)).permanent
      = -(tableOf C (M + 1) (rowW (M + 1)) (rowW (M + 1)) (rowV (M + 1))
            (rowV (M + 1))).permanent
        - (tableOf C (M + 1) (rowU (M + 1)) (rowU (M + 1)) (rowX (M + 1))
            (rowX (M + 1))).permanent := by
  have h01 : (⟨0, by omega⟩ : Fin (M + 1 + 3)) ≠ ⟨1, by omega⟩ :=
    Fin.ne_of_val_ne (show (0 : ℕ) ≠ 1 by omega)
  have h23 : (⟨2, by omega⟩ : Fin (M + 1 + 3)) ≠ ⟨3, by omega⟩ :=
    Fin.ne_of_val_ne (show (2 : ℕ) ≠ 3 by omega)
  have step1 : (dihedralTableEven C (M + 1)).permanent
      = (tableOf C (M + 1) (rowU (M + 1) + rowW (M + 1))
            (rowU (M + 1) - rowW (M + 1)) (rowV (M + 1)) (rowV (M + 1))).permanent
        - (tableOf C (M + 1) (rowU (M + 1) + rowW (M + 1))
            (rowU (M + 1) - rowW (M + 1)) (rowX (M + 1)) (rowX (M + 1))).permanent := by
    have hT : dihedralTableEven C (M + 1)
        = ((tableOf C (M + 1) (rowU (M + 1) + rowW (M + 1))
              (rowU (M + 1) - rowW (M + 1)) (rowX (M + 1))
              (rowX (M + 1))).updateRow ⟨2, by omega⟩
            (rowV (M + 1) + rowX (M + 1))).updateRow ⟨3, by omega⟩
            (rowV (M + 1) - rowX (M + 1)) := by
      rw [updateRow_tableOf_two, updateRow_tableOf_three]
      simp only [dihedralTableEven]
    rw [hT, permanent_updateRow_pair _ h23, updateRow_tableOf_two,
      updateRow_tableOf_three, updateRow_tableOf_two, updateRow_tableOf_three]
  have step2 : ∀ w2 w3 : Fin (M + 1 + 3) → R,
      (tableOf C (M + 1) (rowU (M + 1) + rowW (M + 1))
          (rowU (M + 1) - rowW (M + 1)) w2 w3).permanent
        = (tableOf C (M + 1) (rowU (M + 1)) (rowU (M + 1)) w2 w3).permanent
          - (tableOf C (M + 1) (rowW (M + 1)) (rowW (M + 1)) w2 w3).permanent := by
    intro w2 w3
    have hT : tableOf C (M + 1) (rowU (M + 1) + rowW (M + 1))
          (rowU (M + 1) - rowW (M + 1)) w2 w3
        = ((tableOf C (M + 1) (rowU (M + 1)) (rowU (M + 1)) w2
              w3).updateRow ⟨0, by omega⟩
            (rowU (M + 1) + rowW (M + 1))).updateRow ⟨1, by omega⟩
            (rowU (M + 1) - rowW (M + 1)) := by
      rw [updateRow_tableOf_zero, updateRow_tableOf_one]
    rw [hT, permanent_updateRow_pair _ h01, updateRow_tableOf_zero,
      updateRow_tableOf_one, updateRow_tableOf_zero, updateRow_tableOf_one]
  rw [step1, step2, step2, permanent_tableUUVV, permanent_tableWWXX]
  ring

/-- **Involution 1** (column scaling).  Scaling rotation column `j` by
`(-1)^j` and the `rs` column by `-1` carries `(U,U,X,X,χ_h)` into
`(W,W,V,V,χ_{M+1-h})` up to the row involution `h ↦ M+1-h`; the product of
the scalars is `(-1)^{(M+2)(M+1)/2 + 1}`. -/
private lemma permanent_tableWWVV_eq (C : ℤ → R) (M : ℕ)
    (hC : ∀ (k : ℕ) (t : ℤ), C (((M + 1 : ℕ) : ℤ) * k - t) = (-1) ^ k * C t) :
    (tableOf C (M + 1) (rowW (M + 1)) (rowW (M + 1)) (rowV (M + 1))
        (rowV (M + 1))).permanent
      = (-1 : R) ^ ((M + 2) * (M + 1) / 2 + 1)
        * (tableOf C (M + 1) (rowU (M + 1)) (rowU (M + 1)) (rowX (M + 1))
            (rowX (M + 1))).permanent := by
  set gnat : ℕ → R := fun v =>
    if v ≤ M + 1 then (-1) ^ v else if v = M + 1 + 1 then 1 else -1 with hgnat
  set f : Fin (M + 1 + 3) → Fin (M + 1 + 3) := fun i =>
    if (i : ℕ) = 0 then ⟨2, by omega⟩
    else if (i : ℕ) = 1 then ⟨3, by omega⟩
    else if (i : ℕ) = 2 then ⟨0, by omega⟩
    else if (i : ℕ) = 3 then ⟨1, by omega⟩
    else ⟨M + 7 - max 4 (i : ℕ), by omega⟩ with hf
  have hv0 : ((⟨0, by omega⟩ : Fin (M + 1 + 3)) : ℕ) = 0 := rfl
  have hv1 : ((⟨1, by omega⟩ : Fin (M + 1 + 3)) : ℕ) = 1 := rfl
  have hv2 : ((⟨2, by omega⟩ : Fin (M + 1 + 3)) : ℕ) = 2 := rfl
  have hv3 : ((⟨3, by omega⟩ : Fin (M + 1 + 3)) : ℕ) = 3 := rfl
  have hfinv : Function.Involutive f := by
    intro i
    by_cases h0 : (i : ℕ) = 0
    · simp only [hf, h0, reduceIte]
      exact Fin.ext (show (0 : ℕ) = (i : ℕ) by omega)
    · by_cases h1 : (i : ℕ) = 1
      · simp only [hf, h1, reduceIte]
        exact Fin.ext (show (1 : ℕ) = (i : ℕ) by omega)
      · by_cases h2 : (i : ℕ) = 2
        · simp only [hf, h2, reduceIte]
          exact Fin.ext (show (2 : ℕ) = (i : ℕ) by omega)
        · by_cases h3 : (i : ℕ) = 3
          · simp only [hf, h3, reduceIte]
            exact Fin.ext (show (3 : ℕ) = (i : ℕ) by omega)
          · simp only [hf, if_neg h0, if_neg h1, if_neg h2, if_neg h3]
            rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
              if_neg (by omega)]
            exact Fin.ext
              (show M + 7 - max 4 (M + 7 - max 4 (i : ℕ)) = (i : ℕ) by omega)
  have key : (Matrix.of fun (i j : Fin (M + 1 + 3)) => gnat (j : ℕ)
        * tableOf C (M + 1) (rowU (M + 1)) (rowU (M + 1)) (rowX (M + 1))
            (rowX (M + 1)) i j)
      = (tableOf C (M + 1) (rowW (M + 1)) (rowW (M + 1)) (rowV (M + 1))
          (rowV (M + 1))).submatrix (⇑(Function.Involutive.toPerm f hfinv)) id := by
    ext i j
    simp only [Matrix.of_apply, Matrix.submatrix_apply,
      Function.Involutive.coe_toPerm, id_eq]
    have hUtoV : gnat (j : ℕ) * rowU (M + 1) j = rowV (M + 1) j := by
      by_cases hj : (j : ℕ) ≤ M + 1
      · simp only [hgnat, rowU, rowV, if_pos hj, mul_one]
      · simp only [hgnat, rowU, rowV, if_neg hj, mul_zero]
    have hXtoW : gnat (j : ℕ) * rowX (M + 1) j = rowW (M + 1) j := by
      by_cases hj : (j : ℕ) ≤ M + 1
      · have hA : rowA (R := R) (M + 1) j = 0 := by
          simp only [rowA]
          rw [if_neg (show ¬((j : ℕ) = M + 1 + 1) by omega)]
        have hB : rowB (R := R) (M + 1) j = 0 := by
          simp only [rowB]
          rw [if_neg (show ¬((j : ℕ) = M + 1 + 2) by omega)]
        simp only [rowX, rowW, Pi.sub_apply, Pi.add_apply, hA, hB]
        ring
      · by_cases hj2 : (j : ℕ) = M + 1 + 1
        · have hA : rowA (R := R) (M + 1) j = 1 := by
            simp only [rowA]
            rw [if_pos hj2]
          have hB : rowB (R := R) (M + 1) j = 0 := by
            simp only [rowB]
            rw [if_neg (show ¬((j : ℕ) = M + 1 + 2) by omega)]
          have hg : gnat (j : ℕ) = 1 := by
            simp only [hgnat]
            rw [if_neg hj, if_pos hj2]
          simp only [rowX, rowW, Pi.sub_apply, Pi.add_apply, hA, hB, hg]
          ring
        · have hj3 : (j : ℕ) = M + 1 + 2 := by omega
          have hA : rowA (R := R) (M + 1) j = 0 := by
            simp only [rowA]
            rw [if_neg (show ¬((j : ℕ) = M + 1 + 1) by omega)]
          have hB : rowB (R := R) (M + 1) j = 1 := by
            simp only [rowB]
            rw [if_pos hj3]
          have hg : gnat (j : ℕ) = -1 := by
            simp only [hgnat]
            rw [if_neg hj, if_neg (show ¬((j : ℕ) = M + 1 + 1) by omega)]
          simp only [rowX, rowW, Pi.sub_apply, Pi.add_apply, hA, hB, hg]
          ring
    by_cases h0 : (i : ℕ) = 0
    · have hfi : f i = ⟨2, by omega⟩ := by simp only [hf, h0, reduceIte]
      rw [tableOf_apply_zero _ _ _ _ _ _ _ h0, hfi,
        tableOf_apply_two _ _ _ _ _ _ _ hv2]
      exact hUtoV
    · by_cases h1 : (i : ℕ) = 1
      · have hfi : f i = ⟨3, by omega⟩ := by
          simp only [hf, h1, reduceIte]
          norm_num
        rw [tableOf_apply_one _ _ _ _ _ _ _ h1, hfi,
          tableOf_apply_three _ _ _ _ _ _ _ hv3]
        exact hUtoV
      · by_cases h2 : (i : ℕ) = 2
        · have hfi : f i = ⟨0, by omega⟩ := by
            simp only [hf, if_neg h0, h2, reduceIte]
            norm_num
          rw [tableOf_apply_two _ _ _ _ _ _ _ h2, hfi,
            tableOf_apply_zero _ _ _ _ _ _ _ hv0]
          exact hXtoW
        · by_cases h3 : (i : ℕ) = 3
          · have hfi : f i = ⟨1, by omega⟩ := by
              simp only [hf, if_neg h0, h3, reduceIte]
              norm_num
            rw [tableOf_apply_three _ _ _ _ _ _ _ h3, hfi,
              tableOf_apply_one _ _ _ _ _ _ _ hv1]
            exact hXtoW
          · have h4 : 4 ≤ (i : ℕ) := by omega
            have hfi : f i = ⟨M + 7 - (i : ℕ), by omega⟩ := by
              simp only [hf, if_neg h0, if_neg h1, if_neg h2, if_neg h3]
              exact Fin.ext
                (show M + 7 - max 4 (i : ℕ) = M + 7 - (i : ℕ) by omega)
            have hvfi : ((⟨M + 7 - (i : ℕ), by omega⟩ :
                Fin (M + 1 + 3)) : ℕ) = M + 7 - (i : ℕ) := rfl
            rw [tableOf_apply_ge _ _ _ _ _ _ _ h4, hfi,
              tableOf_apply_ge _ _ _ _ _ _ _
                (show 4 ≤ M + 7 - (i : ℕ) by omega), hvfi]
            by_cases hj : (j : ℕ) ≤ M + 1
            · simp only [rowChi, if_pos hj, hgnat]
              rw [show (((M + 7 - (i : ℕ) - 3 : ℕ)) : ℤ) * ((j : ℕ) : ℤ)
                    = ((M + 1 : ℕ) : ℤ) * ((j : ℕ) : ℤ)
                      - (((i : ℕ) - 3 : ℕ) : ℤ) * ((j : ℕ) : ℤ) from by
                  push_cast [Nat.cast_sub (show 3 ≤ M + 7 - (i : ℕ) by omega),
                    Nat.cast_sub (show (i : ℕ) ≤ M + 7 by omega),
                    Nat.cast_sub (show 3 ≤ (i : ℕ) by omega)]
                  ring,
                hC (j : ℕ) ((((i : ℕ) - 3 : ℕ) : ℤ) * ((j : ℕ) : ℤ))]
            · simp only [rowChi, if_neg hj, hgnat, mul_zero]
  have hprod : (∏ j : Fin (M + 1 + 3), gnat (j : ℕ))
      = (-1 : R) ^ ((M + 2) * (M + 1) / 2 + 1) := by
    rw [Fin.prod_univ_eq_prod_range gnat (M + 1 + 3),
      show M + 1 + 3 = (M + 2) + 1 + 1 from by omega,
      Finset.prod_range_succ, Finset.prod_range_succ]
    have hrot : (∏ v ∈ Finset.range (M + 2), gnat v)
        = ∏ v ∈ Finset.range (M + 2), (-1 : R) ^ v := by
      refine Finset.prod_congr rfl fun v hv => ?_
      have hvle : v ≤ M + 1 := by
        have := Finset.mem_range.mp hv
        omega
      simp only [hgnat, if_pos hvle]
    have hs : gnat (M + 2) = 1 := by simp [hgnat]
    have hrs : gnat (M + 2 + 1) = -1 := by simp [hgnat]
    rw [hrot, hs, hrs, Finset.prod_pow_eq_pow_sum, Finset.sum_range_id,
      show M + 2 - 1 = M + 1 from by omega, pow_succ]
    ring
  calc (tableOf C (M + 1) (rowW (M + 1)) (rowW (M + 1)) (rowV (M + 1))
        (rowV (M + 1))).permanent
      = ((tableOf C (M + 1) (rowW (M + 1)) (rowW (M + 1)) (rowV (M + 1))
          (rowV (M + 1))).submatrix
            (⇑(Function.Involutive.toPerm f hfinv)) id).permanent :=
        (Matrix.permanent_permute_cols _ _).symm
    _ = (Matrix.of fun (i j : Fin (M + 1 + 3)) => gnat (j : ℕ)
          * tableOf C (M + 1) (rowU (M + 1)) (rowU (M + 1)) (rowX (M + 1))
              (rowX (M + 1)) i j).permanent := by rw [key]
    _ = (∏ j : Fin (M + 1 + 3), gnat (j : ℕ))
          * (tableOf C (M + 1) (rowU (M + 1)) (rowU (M + 1)) (rowX (M + 1))
              (rowX (M + 1))).permanent := permanent_col_scale _ _
    _ = (-1 : R) ^ ((M + 2) * (M + 1) / 2 + 1)
          * (tableOf C (M + 1) (rowU (M + 1)) (rowU (M + 1)) (rowX (M + 1))
              (rowX (M + 1))).permanent := by rw [hprod]

/-- **Involution 2** (column permutation).  The substitution `j ↦ M+1-j` on
rotation columns fixes `(U,U,X,X,χ)` up to scaling row `χ_h` by `(-1)^h`;
hence its permanent is fixed by the sign `(-1)^{(M+1)M/2}`. -/
private lemma permanent_tableUUXX_self (C : ℤ → R) (M : ℕ)
    (hC : ∀ (k : ℕ) (t : ℤ), C (((M + 1 : ℕ) : ℤ) * k - t) = (-1) ^ k * C t) :
    (tableOf C (M + 1) (rowU (M + 1)) (rowU (M + 1)) (rowX (M + 1))
        (rowX (M + 1))).permanent
      = (-1 : R) ^ ((M + 1) * M / 2)
        * (tableOf C (M + 1) (rowU (M + 1)) (rowU (M + 1)) (rowX (M + 1))
            (rowX (M + 1))).permanent := by
  set wnat : ℕ → R := fun v =>
    if v ≤ 3 then 1 else (-1) ^ (v - 3) with hwnat
  set t : Fin (M + 1 + 3) → Fin (M + 1 + 3) := fun j =>
    if (j : ℕ) ≤ M + 1 then ⟨M + 1 - (j : ℕ), by omega⟩ else j with ht
  have htinv : Function.Involutive t := by
    intro j
    by_cases hj : (j : ℕ) ≤ M + 1
    · simp only [ht, if_pos hj,
        if_pos (show M + 1 - (j : ℕ) ≤ M + 1 by omega)]
      exact Fin.ext (show M + 1 - (M + 1 - (j : ℕ)) = (j : ℕ) by omega)
    · simp only [ht, if_neg hj]
  have key : (tableOf C (M + 1) (rowU (M + 1)) (rowU (M + 1)) (rowX (M + 1))
        (rowX (M + 1))).submatrix id (⇑(Function.Involutive.toPerm t htinv))
      = Matrix.of fun (i j : Fin (M + 1 + 3)) => wnat (i : ℕ)
          * tableOf C (M + 1) (rowU (M + 1)) (rowU (M + 1)) (rowX (M + 1))
              (rowX (M + 1)) i j := by
    ext i j
    simp only [Matrix.of_apply, Matrix.submatrix_apply,
      Function.Involutive.coe_toPerm, id_eq]
    have hUfix : rowU (R := R) (M + 1) (t j) = rowU (R := R) (M + 1) j := by
      by_cases hj : (j : ℕ) ≤ M + 1
      · have hval : ((⟨M + 1 - (j : ℕ), by omega⟩ : Fin (M + 1 + 3)) : ℕ)
            = M + 1 - (j : ℕ) := rfl
        simp only [ht, rowU, hval,
          if_pos (show M + 1 - (j : ℕ) ≤ M + 1 by omega), if_pos hj]
      · simp only [ht, if_neg hj]
    have hXfix : rowX (R := R) (M + 1) (t j) = rowX (R := R) (M + 1) j := by
      by_cases hj : (j : ℕ) ≤ M + 1
      · simp only [ht, if_pos hj, rowX, rowA, rowB, Pi.sub_apply,
          if_neg (show ¬(M + 1 - (j : ℕ) = M + 1 + 1) by omega),
          if_neg (show ¬(M + 1 - (j : ℕ) = M + 1 + 2) by omega),
          if_neg (show ¬((j : ℕ) = M + 1 + 1) by omega),
          if_neg (show ¬((j : ℕ) = M + 1 + 2) by omega)]
      · simp only [ht, if_neg hj]
    by_cases h0 : (i : ℕ) = 0
    · rw [tableOf_apply_zero _ _ _ _ _ _ _ h0, tableOf_apply_zero _ _ _ _ _ _ _ h0,
        hwnat]
      simp only [if_pos (show (i : ℕ) ≤ 3 by omega), one_mul]
      exact hUfix
    · by_cases h1 : (i : ℕ) = 1
      · rw [tableOf_apply_one _ _ _ _ _ _ _ h1, tableOf_apply_one _ _ _ _ _ _ _ h1,
          hwnat]
        simp only [if_pos (show (i : ℕ) ≤ 3 by omega), one_mul]
        exact hUfix
      · by_cases h2 : (i : ℕ) = 2
        · rw [tableOf_apply_two _ _ _ _ _ _ _ h2, tableOf_apply_two _ _ _ _ _ _ _ h2,
            hwnat]
          simp only [if_pos (show (i : ℕ) ≤ 3 by omega), one_mul]
          exact hXfix
        · by_cases h3 : (i : ℕ) = 3
          · rw [tableOf_apply_three _ _ _ _ _ _ _ h3,
              tableOf_apply_three _ _ _ _ _ _ _ h3, hwnat]
            simp only [if_pos (show (i : ℕ) ≤ 3 by omega), one_mul]
            exact hXfix
          · have h4 : 4 ≤ (i : ℕ) := by omega
            rw [tableOf_apply_ge _ _ _ _ _ _ _ h4, tableOf_apply_ge _ _ _ _ _ _ _ h4,
              hwnat]
            simp only [if_neg (show ¬((i : ℕ) ≤ 3) by omega)]
            by_cases hj : (j : ℕ) ≤ M + 1
            · have hval : ((⟨M + 1 - (j : ℕ), by omega⟩ : Fin (M + 1 + 3)) : ℕ)
                  = M + 1 - (j : ℕ) := rfl
              simp only [ht, rowChi, hval,
                if_pos (show M + 1 - (j : ℕ) ≤ M + 1 by omega), if_pos hj]
              rw [show ((((i : ℕ) - 3 : ℕ)) : ℤ) * ((M + 1 - (j : ℕ) : ℕ) : ℤ)
                    = ((M + 1 : ℕ) : ℤ) * (((i : ℕ) - 3 : ℕ) : ℤ)
                      - (((i : ℕ) - 3 : ℕ) : ℤ) * ((j : ℕ) : ℤ) from by
                  push_cast [Nat.cast_sub (show (j : ℕ) ≤ M + 1 by omega),
                    Nat.cast_sub (show 3 ≤ (i : ℕ) by omega)]
                  ring,
                hC ((i : ℕ) - 3) ((((i : ℕ) - 3 : ℕ) : ℤ) * ((j : ℕ) : ℤ))]
            · simp only [ht, if_neg hj, rowChi, mul_zero]
  have hprod : (∏ i : Fin (M + 1 + 3), wnat (i : ℕ))
      = (-1 : R) ^ ((M + 1) * M / 2) := by
    rw [Fin.prod_univ_eq_prod_range wnat (M + 1 + 3),
      show M + 1 + 3 = 4 + M from by omega, Finset.prod_range_add]
    have h1 : (∏ x ∈ Finset.range 4, wnat x) = 1 := by
      refine Finset.prod_eq_one fun x hx => ?_
      have : x ≤ 3 := by
        have := Finset.mem_range.mp hx
        omega
      simp only [hwnat, if_pos this]
    have h2 : (∏ x ∈ Finset.range M, wnat (4 + x))
        = ∏ x ∈ Finset.range M, (-1 : R) ^ (x + 1) := by
      refine Finset.prod_congr rfl fun x _ => ?_
      simp only [hwnat, if_neg (show ¬(4 + x ≤ 3) by omega),
        show 4 + x - 3 = x + 1 from by omega]
    have hsum : (∑ x ∈ Finset.range M, (x + 1)) = (M + 1) * M / 2 := by
      have hshift : (∑ x ∈ Finset.range M, (x + 1))
          = ∑ x ∈ Finset.range (M + 1), x := by
        rw [Finset.sum_range_succ' (fun x => x) M]
        simp
      rw [hshift, Finset.sum_range_id, show M + 1 - 1 = M from by omega]
    rw [h1, h2, Finset.prod_pow_eq_pow_sum, hsum, one_mul]
  calc (tableOf C (M + 1) (rowU (M + 1)) (rowU (M + 1)) (rowX (M + 1))
        (rowX (M + 1))).permanent
      = ((tableOf C (M + 1) (rowU (M + 1)) (rowU (M + 1)) (rowX (M + 1))
          (rowX (M + 1))).submatrix id
            (⇑(Function.Involutive.toPerm t htinv))).permanent :=
        (Matrix.permanent_permute_rows _ _).symm
    _ = (Matrix.of fun (i j : Fin (M + 1 + 3)) => wnat (i : ℕ)
          * tableOf C (M + 1) (rowU (M + 1)) (rowU (M + 1)) (rowX (M + 1))
              (rowX (M + 1)) i j).permanent := by rw [key]
    _ = (∏ i : Fin (M + 1 + 3), wnat (i : ℕ))
          * (tableOf C (M + 1) (rowU (M + 1)) (rowU (M + 1)) (rowX (M + 1))
              (rowX (M + 1))).permanent := permanent_row_scale _ _
    _ = (-1 : R) ^ ((M + 1) * M / 2)
          * (tableOf C (M + 1) (rowU (M + 1)) (rowU (M + 1)) (rowX (M + 1))
              (rowX (M + 1))).permanent := by rw [hprod]

/-- Assembly of the even case at half-order `M + 1`. -/
private lemma permanent_even_aux (C : ℤ → R) (M : ℕ)
    (hC : ∀ (k : ℕ) (t : ℤ), C (((M + 1 : ℕ) : ℤ) * k - t) = (-1) ^ k * C t)
    (hM4 : (M + 1) % 4 ≠ 1) :
    (dihedralTableEven C (M + 1)).permanent = 0 := by
  set p := (tableOf C (M + 1) (rowU (M + 1)) (rowU (M + 1)) (rowX (M + 1))
    (rowX (M + 1))).permanent with hp
  have hexp := permanent_even_expansion C M
  rw [permanent_tableWWVV_eq C M hC, ← hp] at hexp
  have h4 : (M + 1) % 4 = 0 ∨ (M + 1) % 4 = 2 ∨ (M + 1) % 4 = 3 := by omega
  rcases h4 with h | h | h
  · -- `M+1 = 4a`: exponent `(4a+1)(4a)/2 = 2a(4a+1)` is even, the two terms cancel.
    obtain ⟨a, ha⟩ : ∃ a, M + 1 = 4 * a := ⟨(M + 1) / 4, by omega⟩
    have hdiv : (M + 2) * (M + 1) / 2 = 2 * (a * (4 * a + 1)) :=
      Nat.div_eq_of_eq_mul_left (by norm_num)
        (by rw [show M + 2 = 4 * a + 1 from by omega, ha]; ring)
    have hsign : (-1 : R) ^ ((M + 2) * (M + 1) / 2 + 1) = -1 := by
      rw [pow_succ, hdiv, (even_two_mul _).neg_one_pow, one_mul]
    rw [hsign] at hexp
    rw [hexp]
    ring
  · -- `M+1 = 4a+2`: both exponents are odd; involution 2 kills `p` 2-torsion-free.
    obtain ⟨a, ha⟩ : ∃ a, M + 1 = 4 * a + 2 := ⟨(M + 1) / 4, by omega⟩
    have hdiv1 : (M + 2) * (M + 1) / 2 = (4 * a + 3) * (2 * a + 1) :=
      Nat.div_eq_of_eq_mul_left (by norm_num)
        (by rw [show M + 2 = 4 * a + 3 from by omega, ha]; ring)
    have hodd1 : Odd ((4 * a + 3) * (2 * a + 1)) :=
      ⟨4 * a * a + 5 * a + 1, by ring⟩
    have hsign1 : (-1 : R) ^ ((M + 2) * (M + 1) / 2 + 1) = 1 := by
      rw [pow_succ, hdiv1, hodd1.neg_one_pow]
      ring
    rw [hsign1, one_mul] at hexp
    have hdiv2 : (M + 1) * M / 2 = (2 * a + 1) * (4 * a + 1) :=
      Nat.div_eq_of_eq_mul_left (by norm_num)
        (by rw [ha, show M = 4 * a + 1 from by omega]; ring)
    have hodd2 : Odd ((2 * a + 1) * (4 * a + 1)) :=
      ⟨4 * a * a + 3 * a, by ring⟩
    have hUX := permanent_tableUUXX_self C M hC
    rw [← hp, hdiv2, hodd2.neg_one_pow] at hUX
    have hpp : p + p = 0 := by linear_combination hUX
    rw [hexp]
    linear_combination -hpp
  · -- `M+1 = 4a+3`: exponent `(4a+4)(4a+3)/2 = 2(a+1)(4a+3)` is even again.
    obtain ⟨a, ha⟩ : ∃ a, M + 1 = 4 * a + 3 := ⟨(M + 1) / 4, by omega⟩
    have hdiv : (M + 2) * (M + 1) / 2 = 2 * ((a + 1) * (4 * a + 3)) :=
      Nat.div_eq_of_eq_mul_left (by norm_num)
        (by rw [show M + 2 = 4 * a + 4 from by omega, ha]; ring)
    have hsign : (-1 : R) ^ ((M + 2) * (M + 1) / 2 + 1) = -1 := by
      rw [pow_succ, hdiv, (even_two_mul _).neg_one_pow, one_mul]
    rw [hsign] at hexp
    rw [hexp]
    ring

/-- **Vanishing, even case.**  Over any commutative ring, the permanent of
the dihedral table of rotation half-order `M` (dihedral order `4M`) vanishes
whenever `M ≢ 1 (mod 4)`, i.e. whenever the group order is not `≡ 4 mod 16`.
The entry function `C` need only satisfy the functional equation
`C (M k - t) = (-1)^k C t`, which holds for `C t = 2 cos (π t / M)`. -/
theorem permanent_dihedralTableEven_eq_zero (C : ℤ → R) (M : ℕ) (hM : 1 ≤ M)
    (hC : ∀ (k : ℕ) (t : ℤ), C ((M : ℕ) * k - t) = (-1) ^ k * C t)
    (hM4 : M % 4 ≠ 1) :
    (dihedralTableEven C M).permanent = 0 := by
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  exact permanent_even_aux C M' hC hM4

end EvenCase

/-! ## The real cosine entries, certificates, and the open direction -/

section RealEntries

/-- The intended entry function: `cosEntry M t = 2 cos (π t / M)` is the
value `χ_h(r^j)` of the two-dimensional dihedral characters at `t = h·j`
(for rotation half-order `M`, i.e. rotation order `2M`). -/
noncomputable def cosEntry (M : ℕ) : ℤ → ℝ :=
  fun t => 2 * Real.cos (Real.pi * (t : ℝ) / (M : ℝ))

/-- Ground truth for `cosEntry`: `χ_h(e) = 2` and, at `M = 2` (order 8),
`χ_1(r) = 2cos(π/2) = 0`. -/
example : cosEntry 5 0 = 2 ∧ cosEntry 2 1 = 0 := by
  constructor
  · simp [cosEntry]
  · simp only [cosEntry]
    rw [show (Real.pi * ((1 : ℤ) : ℝ) / ((2 : ℕ) : ℝ)) = Real.pi / 2 from by
      push_cast; ring]
    simp [Real.cos_pi_div_two]

/-- The cosine entries satisfy the master functional equation
`C (M k - t) = (-1)^k C t` consumed by the even-case vanishing theorem. -/
theorem cosEntry_master (M : ℕ) (hM : 1 ≤ M) :
    ∀ (k : ℕ) (t : ℤ),
      cosEntry M ((M : ℕ) * k - t) = (-1) ^ k * cosEntry M t := by
  intro k t
  have hM0 : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have harg : Real.pi * ((((M : ℤ) * k - t) : ℤ) : ℝ) / (M : ℝ)
      = (k : ℝ) * Real.pi - Real.pi * (t : ℝ) / (M : ℝ) := by
    push_cast
    field_simp
  simp only [cosEntry]
  rw [harg, Real.cos_sub, Real.cos_nat_mul_pi, Real.sin_nat_mul_pi]
  ring

/-- **Vanishing over `ℝ` with the true cosine entries**: the permanent of
the explicit character table of the dihedral group of order `4M` vanishes
whenever `4M ≢ 4 (mod 16)`.  Together with `permanent_dihedralTableOdd`
this settles the vanishing direction of the OEIS A085805 conjecture for the
explicit table family. -/
theorem permanent_dihedralTableEven_cos_eq_zero (M : ℕ) (hM : 1 ≤ M)
    (hM4 : M % 4 ≠ 1) :
    (dihedralTableEven (cosEntry M) M).permanent = 0 :=
  permanent_dihedralTableEven_eq_zero (cosEntry M) M hM
    (cosEntry_master M hM) hM4

/-- Joint satisfiability of the even-case hypotheses at the smallest live
instance `M = 2` (dihedral order 8): the cosine entries satisfy the
functional equation and `2 % 4 ≠ 1`. -/
example : (dihedralTableEven (cosEntry 2) 2).permanent = 0 :=
  permanent_dihedralTableEven_cos_eq_zero 2 (by norm_num) (by norm_num)

end RealEntries

section Certificates

variable {R : Type*} [CommRing R]

private lemma klein_eq (C : ℤ → R) :
    dihedralTableEven C 1
      = !![1, 1, 1, 1; 1, 1, -1, -1; 1, -1, 1, -1; 1, -1, -1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [dihedralTableEven, tableOf, rowU, rowV, rowW, rowX, rowA, rowB]

private lemma permanent_klein_int :
    (!![1, 1, 1, 1; 1, 1, -1, -1; 1, -1, 1, -1; 1, -1, -1, 1] :
      Matrix (Fin 4) (Fin 4) ℤ).permanent = 8 := by
  rw [← permFin_eq_permanent]
  decide

/-- **Certificate, dihedral order 4** (`M = 1`, the Klein four-group): the
permanent of the table is `8` over any commutative ring — nonzero as soon
as `(8 : R) ≠ 0`, e.g. over `ℝ`.  Order `4 ≡ 4 (mod 16)` is the first
member of A085805. -/
theorem permanent_dihedralTableEven_one (C : ℤ → R) :
    (dihedralTableEven C 1).permanent = 8 := by
  have hmap : (dihedralTableEven C 1 : Matrix (Fin 4) (Fin 4) R)
      = (!![1, 1, 1, 1; 1, 1, -1, -1; 1, -1, 1, -1; 1, -1, -1, 1] :
          Matrix (Fin 4) (Fin 4) ℤ).map (Int.castRingHom R) := by
    rw [klein_eq C]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.map_apply]
  rw [hmap, permanent_map, permanent_klein_int]
  norm_num

/-- The order-4 permanent is nonzero over `ℝ`: `4 ∈ A085805`. -/
example : (dihedralTableEven (cosEntry 1) 1).permanent ≠ 0 := by
  rw [permanent_dihedralTableEven_one (cosEntry 1)]
  norm_num

/-- Auxiliary table with rows `U, U, A, B, χ`: the fully reduced core of the
even permanent.  For `M ≡ 1 (mod 4)`,
`perm (dihedralTableEven C M) = 4 · perm (tableAB C M)`. -/
def tableAB (C : ℤ → R) (M : ℕ) : Matrix (Fin (M + 3)) (Fin (M + 3)) R :=
  tableOf C M (rowU M) (rowU M) (rowA M) (rowB M)

private lemma permanent_tableUUXX_eq_AB (C : ℤ → R) (M : ℕ) :
    (tableOf C (M + 1) (rowU (M + 1)) (rowU (M + 1)) (rowX (M + 1))
        (rowX (M + 1))).permanent
      = -2 * (tableOf C (M + 1) (rowU (M + 1)) (rowU (M + 1)) (rowA (M + 1))
          (rowB (M + 1))).permanent := by
  have hX : (rowX (M + 1) : Fin (M + 1 + 3) → R)
      = rowA (M + 1) + -rowB (M + 1) := sub_eq_add_neg _ _
  have h23 : (⟨2, by omega⟩ : Fin (M + 1 + 3)) ≠ ⟨3, by omega⟩ :=
    Fin.ne_of_val_ne (show (2 : ℕ) ≠ 3 by omega)
  -- expand row 2
  have step2 : ∀ w3 : Fin (M + 1 + 3) → R,
      (tableOf C (M + 1) (rowU (M + 1)) (rowU (M + 1)) (rowX (M + 1))
          w3).permanent
        = (tableOf C (M + 1) (rowU (M + 1)) (rowU (M + 1)) (rowA (M + 1))
            w3).permanent
          - (tableOf C (M + 1) (rowU (M + 1)) (rowU (M + 1)) (rowB (M + 1))
              w3).permanent := by
    intro w3
    have hT : tableOf C (M + 1) (rowU (M + 1)) (rowU (M + 1)) (rowX (M + 1)) w3
        = (tableOf C (M + 1) (rowU (M + 1)) (rowU (M + 1)) (rowB (M + 1))
            w3).updateRow ⟨2, by omega⟩ (rowA (M + 1) + -rowB (M + 1)) := by
      rw [updateRow_tableOf_two, ← hX]
    rw [hT, permanent_updateRow_add, permanent_updateRow_neg,
      updateRow_tableOf_two, updateRow_tableOf_two]
    ring
  -- expand row 3
  have step3 : ∀ w2 : Fin (M + 1 + 3) → R,
      (tableOf C (M + 1) (rowU (M + 1)) (rowU (M + 1)) w2
          (rowX (M + 1))).permanent
        = (tableOf C (M + 1) (rowU (M + 1)) (rowU (M + 1)) w2
            (rowA (M + 1))).permanent
          - (tableOf C (M + 1) (rowU (M + 1)) (rowU (M + 1)) w2
              (rowB (M + 1))).permanent := by
    intro w2
    have hT : tableOf C (M + 1) (rowU (M + 1)) (rowU (M + 1)) w2 (rowX (M + 1))
        = (tableOf C (M + 1) (rowU (M + 1)) (rowU (M + 1)) w2
            (rowB (M + 1))).updateRow ⟨3, by omega⟩
            (rowA (M + 1) + -rowB (M + 1)) := by
      rw [updateRow_tableOf_three, ← hX]
    rw [hT, permanent_updateRow_add, permanent_updateRow_neg,
      updateRow_tableOf_three, updateRow_tableOf_three]
    ring
  -- the two aligned-indicator tables die
  have hAA : (tableOf C (M + 1) (rowU (M + 1)) (rowU (M + 1)) (rowA (M + 1))
      (rowA (M + 1))).permanent = 0 := by
    refine permanent_eq_zero_of_rows_subset _ {⟨2, by omega⟩, ⟨3, by omega⟩}
      {⟨M + 1 + 1, by omega⟩} ?_ ?_
    · rw [Finset.card_pair h23, Finset.card_singleton]
      omega
    · intro i hi j hj
      have hjv : (j : ℕ) ≠ M + 1 + 1 := fun h =>
        hj (Finset.mem_singleton.mpr (Fin.ext h))
      have hval : rowA (R := R) (M + 1) j = 0 := by
        simp only [rowA]
        rw [if_neg hjv]
      rcases Finset.mem_insert.mp hi with rfl | hi'
      · rw [tableOf_apply_two _ _ _ _ _ _ _ rfl]
        exact hval
      · rw [Finset.mem_singleton.mp hi', tableOf_apply_three _ _ _ _ _ _ _ rfl]
        exact hval
  have hBB : (tableOf C (M + 1) (rowU (M + 1)) (rowU (M + 1)) (rowB (M + 1))
      (rowB (M + 1))).permanent = 0 := by
    refine permanent_eq_zero_of_rows_subset _ {⟨2, by omega⟩, ⟨3, by omega⟩}
      {⟨M + 1 + 2, by omega⟩} ?_ ?_
    · rw [Finset.card_pair h23, Finset.card_singleton]
      omega
    · intro i hi j hj
      have hjv : (j : ℕ) ≠ M + 1 + 2 := fun h =>
        hj (Finset.mem_singleton.mpr (Fin.ext h))
      have hval : rowB (R := R) (M + 1) j = 0 := by
        simp only [rowB]
        rw [if_neg hjv]
      rcases Finset.mem_insert.mp hi with rfl | hi'
      · rw [tableOf_apply_two _ _ _ _ _ _ _ rfl]
        exact hval
      · rw [Finset.mem_singleton.mp hi', tableOf_apply_three _ _ _ _ _ _ _ rfl]
        exact hval
  -- the two cross terms agree by a row swap
  have hswap : (tableOf C (M + 1) (rowU (M + 1)) (rowU (M + 1)) (rowB (M + 1))
      (rowA (M + 1))).permanent
      = (tableOf C (M + 1) (rowU (M + 1)) (rowU (M + 1)) (rowA (M + 1))
          (rowB (M + 1))).permanent := by
    have h1 : tableOf C (M + 1) (rowU (M + 1)) (rowU (M + 1)) (rowB (M + 1))
        (rowA (M + 1))
        = ((tableOf C (M + 1) (rowU (M + 1)) (rowU (M + 1)) (rowA (M + 1))
            (rowB (M + 1))).updateRow ⟨2, by omega⟩
              (rowB (M + 1))).updateRow ⟨3, by omega⟩ (rowA (M + 1)) := by
      rw [updateRow_tableOf_two, updateRow_tableOf_three]
    have h2 : tableOf C (M + 1) (rowU (M + 1)) (rowU (M + 1)) (rowA (M + 1))
        (rowB (M + 1))
        = ((tableOf C (M + 1) (rowU (M + 1)) (rowU (M + 1)) (rowA (M + 1))
            (rowB (M + 1))).updateRow ⟨2, by omega⟩
              (rowA (M + 1))).updateRow ⟨3, by omega⟩ (rowB (M + 1)) := by
      rw [updateRow_tableOf_two, updateRow_tableOf_three]
    rw [h1, permanent_updateRow_swap _ h23, ← h2]
  rw [step2, step3, step3, hAA, hBB, hswap]
  ring

/-- **Reduction of the surviving case.**  For `M ≡ 1 (mod 4)` the even
permanent equals `4 · perm (tableAB C M)`: the nonvanishing direction of the
A085805 conjecture is exactly the nonvanishing of the reduced core. -/
theorem permanent_dihedralTableEven_eq_four_mul (C : ℤ → R) (M : ℕ)
    (hC : ∀ (k : ℕ) (t : ℤ), C ((M : ℕ) * k - t) = (-1) ^ k * C t)
    (hM4 : M % 4 = 1) :
    (dihedralTableEven C M).permanent = 4 * (tableAB C M).permanent := by
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  have hexp := permanent_even_expansion C M'
  rw [permanent_tableWWVV_eq C M' hC] at hexp
  obtain ⟨a, ha⟩ : ∃ a, M' + 1 = 4 * a + 1 := ⟨(M' + 1) / 4, by omega⟩
  have hdiv : (M' + 2) * (M' + 1) / 2 = (2 * a + 1) * (4 * a + 1) :=
    Nat.div_eq_of_eq_mul_left (by norm_num)
      (by rw [show M' + 2 = 4 * a + 2 from by omega, ha]; ring)
  have hodd : Odd ((2 * a + 1) * (4 * a + 1)) := ⟨4 * a * a + 3 * a, by ring⟩
  have hsign : (-1 : R) ^ ((M' + 2) * (M' + 1) / 2 + 1) = 1 := by
    rw [pow_succ, hdiv, hodd.neg_one_pow]
    ring
  rw [hsign, one_mul, permanent_tableUUXX_eq_AB C M'] at hexp
  rw [hexp, tableAB]
  ring

/-- **Not proved here (A085805, nonvanishing direction).**  For every
`M ≡ 1 (mod 4)` the permanent of the real EXPLICIT dihedral table of order
`4M` is nonzero.  The values `8, -576, -13824, -14665728, 13177872384` are
the published terms of OEIS A086641 (Dekel 2003; a(6)-a(7) added by Sean A.
Irvine, Jul 11 2026), independently recomputed this session — exactly
(cyclotomic arithmetic) for `M ∈ {1, 5, 9}`, numerically (Ryser, float64)
for `M ∈ {13, 17}`; stated here as a `Prop`, not asserted.
Together with the vanishing theorems above it is equivalent to the full
OEIS A085805 conjecture (for the explicit table family): the permanent is
nonzero exactly at dihedral orders `≡ 4 (mod 16)`. -/
def NonvanishingConjecture : Prop :=
  ∀ M : ℕ, M % 4 = 1 → (dihedralTableEven (cosEntry M) M).permanent ≠ 0

end Certificates

/-! ## Certificate: dihedral order 20

`perm (dihedralTableEven (cosEntry 5) 5) = 4 · perm (tableAB (cosEntry 5) 5)`
by the reduction above; the reduced core has entries in `ℤ[√5]/2`, so its
doubled matrix `QA` lives in `ℤ√5` and its permanent is decided by kernel
computation.  The bridge `QA.map toReal = 2 • tableAB` is certified entry by
entry from the exact values `2cos(π/5) = (1+√5)/2`, `2cos(2π/5) = (√5-1)/2`
and the functional equation. -/

section OrderTwenty

/-- The doubled reduced core of the order-20 table over `ℤ√5`:
`QA = 2 • tableAB (cosEntry 5) 5` after identifying `1 + √5 = ⟨1,1⟩` etc.;
certified against the real table in `bridge_QA` below. -/
private def QA : Matrix (Fin 8) (Fin 8) (ℤ√5) :=
  !![⟨2,0⟩, ⟨2,0⟩, ⟨2,0⟩, ⟨2,0⟩, ⟨2,0⟩, ⟨2,0⟩, ⟨0,0⟩, ⟨0,0⟩;
     ⟨2,0⟩, ⟨2,0⟩, ⟨2,0⟩, ⟨2,0⟩, ⟨2,0⟩, ⟨2,0⟩, ⟨0,0⟩, ⟨0,0⟩;
     ⟨0,0⟩, ⟨0,0⟩, ⟨0,0⟩, ⟨0,0⟩, ⟨0,0⟩, ⟨0,0⟩, ⟨2,0⟩, ⟨0,0⟩;
     ⟨0,0⟩, ⟨0,0⟩, ⟨0,0⟩, ⟨0,0⟩, ⟨0,0⟩, ⟨0,0⟩, ⟨0,0⟩, ⟨2,0⟩;
     ⟨4,0⟩, ⟨1,1⟩, ⟨-1,1⟩, ⟨1,-1⟩, ⟨-1,-1⟩, ⟨-4,0⟩, ⟨0,0⟩, ⟨0,0⟩;
     ⟨4,0⟩, ⟨-1,1⟩, ⟨-1,-1⟩, ⟨-1,-1⟩, ⟨-1,1⟩, ⟨4,0⟩, ⟨0,0⟩, ⟨0,0⟩;
     ⟨4,0⟩, ⟨1,-1⟩, ⟨-1,-1⟩, ⟨1,1⟩, ⟨-1,1⟩, ⟨-4,0⟩, ⟨0,0⟩, ⟨0,0⟩;
     ⟨4,0⟩, ⟨-1,-1⟩, ⟨-1,1⟩, ⟨-1,1⟩, ⟨-1,-1⟩, ⟨4,0⟩, ⟨0,0⟩, ⟨0,0⟩]

set_option maxHeartbeats 1000000 in
/-- Kernel evaluation of the 8×8 permanent over `ℤ√5` (40320 monomials);
`decide +kernel` keeps the enlarged computation inside the kernel only. -/
private lemma permFin_QA : permFin 8 QA = (⟨-36864, 0⟩ : ℤ√5) := by
  decide +kernel

private lemma bridge_QA :
    QA.map (Zsqrtd.toReal (by norm_num : (0 : ℤ) ≤ 5))
      = (2 : ℝ) • tableAB (cosEntry 5) 5 := by
  have hm := cosEntry_master 5 (by norm_num)
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hC0 : cosEntry 5 (0 : ℤ) = 2 := by
    simp [cosEntry]
  have hC1 : cosEntry 5 (1 : ℤ) = (1 + Real.sqrt 5) / 2 := by
    simp only [cosEntry]
    rw [show (Real.pi * ((1 : ℤ) : ℝ) / ((5 : ℕ) : ℝ)) = Real.pi / 5 from by
      push_cast; ring]
    rw [Real.cos_pi_div_five]
    ring
  have hC2 : cosEntry 5 (2 : ℤ) = (Real.sqrt 5 - 1) / 2 := by
    simp only [cosEntry]
    rw [show (Real.pi * ((2 : ℤ) : ℝ) / ((5 : ℕ) : ℝ)) = 2 * (Real.pi / 5) from by
      push_cast; ring]
    rw [Real.cos_two_mul, Real.cos_pi_div_five]
    linear_combination h5 / 4
  have hC3 : cosEntry 5 (3 : ℤ) = -((Real.sqrt 5 - 1) / 2) := by
    have h := hm 1 2
    norm_num at h
    rw [h, hC2]
  have hC4 : cosEntry 5 (4 : ℤ) = -((1 + Real.sqrt 5) / 2) := by
    have h := hm 1 1
    norm_num at h
    rw [h, hC1]
  have hC5 : cosEntry 5 (5 : ℤ) = -2 := by
    have h := hm 1 0
    norm_num at h
    rw [h, hC0]
  have hC6 : cosEntry 5 (6 : ℤ) = -((1 + Real.sqrt 5) / 2) := by
    have h := hm 2 4
    norm_num at h
    rw [h, hC4]
  have hC8 : cosEntry 5 (8 : ℤ) = (Real.sqrt 5 - 1) / 2 := by
    have h := hm 2 2
    norm_num at h
    rw [h, hC2]
  have hC9 : cosEntry 5 (9 : ℤ) = (1 + Real.sqrt 5) / 2 := by
    have h := hm 2 1
    norm_num at h
    rw [h, hC1]
  have hC10 : cosEntry 5 (10 : ℤ) = 2 := by
    have h := hm 2 0
    norm_num at h
    rw [h, hC0]
  have hC12 : cosEntry 5 (12 : ℤ) = (Real.sqrt 5 - 1) / 2 := by
    have hneg : cosEntry 5 (-2 : ℤ) = cosEntry 5 (2 : ℤ) := by
      have h := hm 0 2
      norm_num at h
      exact h
    have h := hm 2 (-2)
    norm_num at h
    rw [h, hneg, hC2]
  have hC15 : cosEntry 5 (15 : ℤ) = -2 := by
    have h := hm 3 0
    norm_num at h
    rw [h, hC0]
  have hC16 : cosEntry 5 (16 : ℤ) = -((1 + Real.sqrt 5) / 2) := by
    have h := hm 4 4
    norm_num at h
    rw [h, hC4]
  have hC20 : cosEntry 5 (20 : ℤ) = 2 := by
    have h := hm 4 0
    norm_num at h
    rw [h, hC0]
  ext i j
  fin_cases i <;> fin_cases j <;>
    · norm_num [QA, tableAB, tableOf, rowU, rowA, rowB, rowChi,
        Matrix.map_apply, Matrix.smul_apply, Zsqrtd.toReal,
        Zsqrtd.lift_apply_apply, hC0, hC1, hC2, hC3, hC4, hC5, hC6, hC8,
        hC9, hC10, hC12, hC15, hC16, hC20]
      try ring

/-- The reduced core of the order-20 table has permanent `-144`. -/
theorem permanent_tableAB_five : (tableAB (cosEntry 5) 5).permanent = -144 := by
  have hQA : QA.permanent = (⟨-36864, 0⟩ : ℤ√5) := by
    rw [← permFin_eq_permanent]
    exact permFin_QA
  have hmap := permanent_map (Zsqrtd.toReal (by norm_num : (0 : ℤ) ≤ 5)) QA
  rw [bridge_QA, hQA, Matrix.permanent_smul] at hmap
  have hval : Zsqrtd.toReal (by norm_num : (0 : ℤ) ≤ 5) (⟨-36864, 0⟩ : ℤ√5)
      = -36864 := by
    simp [Zsqrtd.toReal, Zsqrtd.lift_apply_apply]
  rw [hval] at hmap
  norm_num at hmap
  linarith

/-- **Certificate, dihedral order 20**: the permanent of the real character
table of the dihedral group of order 20 is `-576 ≠ 0`.  Order
`20 ≡ 4 (mod 16)` is the second member of A085805; the value agrees with
the exact Sage computation. -/
theorem permanent_dihedralTable_order_twenty :
    (dihedralTableEven (cosEntry 5) 5).permanent = -576 := by
  rw [permanent_dihedralTableEven_eq_four_mul (cosEntry 5) 5
    (cosEntry_master 5 (by norm_num)) (by norm_num), permanent_tableAB_five]
  norm_num

/-- The order-20 permanent is nonzero: `20 ∈ A085805`. -/
example : (dihedralTableEven (cosEntry 5) 5).permanent ≠ 0 := by
  rw [permanent_dihedralTable_order_twenty]
  norm_num

end OrderTwenty

end DihedralPermanent
