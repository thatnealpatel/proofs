/-
  Vp2/BorderRank — polynomial-closure border rank of 3-tensors.

  This file supplies the polynomial-closure border-rank infrastructure that
  discharges the
  `SORRY[BorderRank]` definition in `Proofs.Vp2.Vp2`:

    · `RankLE T r`       — `T` is a sum of at most `r` rank-one tensors
                           (the honest rank-≤ r locus; no closure taken).
    · `BorderRankLE T r` — `entries T` lies in
                           `zeroLocus k (vanishingIdeal k (rankLocus k n r))`
                           (Mathlib's Nullstellensatz vocabulary,
                           `Mathlib.RingTheory.Nullstellensatz`): every
                           polynomial over `k` vanishing on all rank-≤ r
                           tensors vanishes at `T`.

  HONESTY NOTE (what this definition is and is not). Over every field,
  `BorderRankLE` is only the POLYNOMIAL-CLOSURE notion:
  "indistinguishable from rank ≤ r by polynomials over k". Relating this
  definition over `ℂ` to classical border rank requires a separate bridge
  through algebraic closedness, the Zariski closure of the Segre secant locus,
  and Euclidean closure. That bridge is not proved in this file, so no such
  equivalence is claimed here. The polynomial-closure property is precisely
  what `Distinguisher.vanishes` (Vp2.lean) consumes.

  Infrastructure proved here (all sorry-free):
    · `RankLE.borderRankLE`   rank ≤ r ⇒ polynomial-closure border rank ≤ r
    · `RankLE.mono`, `BorderRankLE.mono`                     (monotone in r)
    · `RankLE.rank_flattening_le`   a rank-≤ r tensor has flattening rank
      ≤ r — proved by factoring the flattening through `Fin r` as a matrix
      product and using `Matrix.rank_mul_le_left`
    · `det_submatrix_eq_zero_of_rank_le`   over a field, every
      (r+1)×(r+1) minor of a rank-≤ r matrix vanishes
    · `genericFlattening`, `det_genericFlattening_submatrix_ne_zero`
      the generic flattening minor on injective row/column picks is a
      NONZERO polynomial (transport `Matrix.det_mvPolynomialX_ne_zero`
      along an injective `MvPolynomial.rename`)
    · `eval_det_genericFlattening_submatrix`   evaluating the generic
      minor at `entries T` gives the same minor of `flattening T`
    · `det_genericFlattening_submatrix_mem_vanishingIdeal`,
      `BorderRankLE.eval_det_genericFlattening_submatrix_eq_zero`
      the generic minor lies in the vanishing ideal of the rank-≤ r
      locus, hence vanishes on every tensor of polynomial-closure border rank
      ≤ r.

  Together these feed the sorry-free
  `Vp2.exists_flattening_distinguisher` (Vp2.lean): flattening minors are
  genuine distinguishers for the polynomial-closure border-rank locus.

  The base objects `Tensor3`, `EntryIndex`, `entries`, `flattening` are
  moved here VERBATIM from Vp2.lean (§0, §2a) so that this file sits
  upstream of it.

  AI disclosure: produced with AI assistance (see Proofs/README).
-/
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.Nullstellensatz
import PolynomialClosure

set_option autoImplicit false

namespace Vp2

/-! ## 0. Base objects: tensors and their entry vectors

Moved verbatim from `Proofs.Vp2.Vp2` §0/§2a, which imports this file. -/

/-- A 3-tensor of side `n` over `k`: `T i j k` is the entry `c_{ijk}`.
This is the task-specified concrete shape `Fin n → Fin n → Fin n → k`,
the same object as a point of `kⁿ ⊗ kⁿ ⊗ kⁿ` in the standard basis. -/
abbrev Tensor3 (k : Type*) (n : ℕ) : Type _ := Fin n → Fin n → Fin n → k

/-- The index set of the `n³` tensor entries; these are the variables a
"distinguisher" polynomial `D(c_{ijk})` ranges over (FSV Defn 2.1:
`coeff(f)` ↦ the tensor entries). -/
abbrev EntryIndex (n : ℕ) : Type _ := Fin n × Fin n × Fin n

/-- The entry vector of a tensor, as the evaluation point for a
distinguisher `D : MvPolynomial (EntryIndex n) k`. -/
def entries {k : Type*} {n : ℕ} (T : Tensor3 k n) : EntryIndex n → k :=
  fun ijk => T ijk.1 ijk.2.1 ijk.2.2

/-- The `j`-flattening of `T` as an `n × (n × n)` matrix of entries:
row `i`, column `(j, l)` holds `c_{i j l}`. -/
def flattening {k : Type*} {n : ℕ} (T : Tensor3 k n) :
    Matrix (Fin n) (Fin n × Fin n) k :=
  fun i jl => T i jl.1 jl.2

/-! ## 1. The rank-≤ r locus -/

/-- `RankLE T r` : the tensor `T` is a sum of at most `r` rank-one
(simple) tensors — the honest, closure-free rank-≤ r condition. -/
def RankLE {k : Type*} [CommSemiring k] {n : ℕ} (T : Tensor3 k n) (r : ℕ) : Prop :=
  ∃ a b c : Fin r → Fin n → k,
    T = fun i j l => ∑ s, a s i * b s j * c s l

/-- The rank-≤ r locus: the set of entry vectors of tensors of rank at
most `r`, as a subset of the point space `EntryIndex n → k` that
`MvPolynomial.vanishingIdeal` consumes. -/
def rankLocus (k : Type*) [CommSemiring k] (n r : ℕ) : Set (EntryIndex n → k) :=
  {x | ∃ T : Tensor3 k n, RankLE T r ∧ x = entries T}

/-- Unfolding membership in the cubic ordinary rank-`≤ r` locus: a point
is the entry vector of a tensor with an `r`-term triad decomposition. -/
theorem mem_rankLocus {k : Type*} [CommSemiring k] {n r : ℕ} {x : EntryIndex n → k} :
    x ∈ rankLocus k n r ↔ ∃ T : Tensor3 k n, RankLE T r ∧ x = entries T :=
  Iff.rfl

/-- Rank is monotone in `r`: pad the decomposition with zero summands. -/
theorem RankLE.mono {k : Type*} [CommSemiring k] {n : ℕ} {T : Tensor3 k n} {r r' : ℕ}
    (h : RankLE T r) (hrr' : r ≤ r') : RankLE T r' := by
  obtain ⟨a, b, c, hT⟩ := h
  have key : RankLE T (r + (r' - r)) := by
    refine ⟨Fin.append a 0, Fin.append b 0, Fin.append c 0, ?_⟩
    subst hT
    funext i j l
    simp [Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  rwa [show r + (r' - r) = r' from by omega] at key

/-! ## 2. Polynomial-closure border rank -/

/-- `BorderRankLE T r` means that `T` has polynomial-closure border rank
at most `r`: `entries T` lies in the zero locus of the
vanishing ideal of the rank-≤ r locus. Equivalently (`borderRankLE_iff`)
every polynomial in the `n³` entry variables that vanishes on all
rank-≤ r tensors also vanishes at `T`. Over every field this is the
polynomial-closure notion. Equivalence over `ℂ` with classical border rank
requires a separate algebraic-geometric/topological bridge and is not proved
here. -/
def BorderRankLE {k : Type*} [Field k] {n : ℕ} (T : Tensor3 k n) (r : ℕ) : Prop :=
  entries T ∈ PolynomialClosure.closure k (rankLocus k n r)

/-- The defining property, unfolded: polynomial-closure border rank at most
`r` means every
polynomial vanishing on the rank-≤ r locus vanishes at `entries T`.
This is exactly the hypothesis `Distinguisher.vanishes` quantifies over. -/
theorem borderRankLE_iff {k : Type*} [Field k] {n : ℕ} {T : Tensor3 k n} {r : ℕ} :
    BorderRankLE T r ↔
      ∀ p ∈ MvPolynomial.vanishingIdeal k (rankLocus k n r),
        MvPolynomial.eval (entries T) p = 0 :=
  Iff.rfl

/-- Ordinary rank at most `r` implies polynomial-closure border rank at most
`r`: the locus is contained in the zero
locus of its own vanishing ideal (`zeroLocus_vanishingIdeal_le`). -/
theorem RankLE.borderRankLE {k : Type*} [Field k] {n : ℕ} {T : Tensor3 k n} {r : ℕ}
    (h : RankLE T r) : BorderRankLE T r :=
  MvPolynomial.zeroLocus_vanishingIdeal_le (rankLocus k n r) ⟨T, h, rfl⟩

/-- Polynomial-closure border rank is monotone in `r`: a larger locus has a
smaller
vanishing ideal, hence a larger zero locus. -/
theorem BorderRankLE.mono {k : Type*} [Field k] {n : ℕ} {T : Tensor3 k n} {r r' : ℕ}
    (h : BorderRankLE T r) (hrr' : r ≤ r') : BorderRankLE T r' := by
  have hlocus : rankLocus k n r ≤ rankLocus k n r' := by
    rintro x ⟨T', hT', rfl⟩
    exact ⟨T', hT'.mono hrr', rfl⟩
  exact MvPolynomial.zeroLocus_anti_mono
    (MvPolynomial.vanishingIdeal_anti_mono hlocus) h

/-! ## 3. Flattening rank bound

A rank-≤ r tensor has flattening rank ≤ r: the flattening factors as an
`n × r` times `r × n²` matrix product, so its rank is bounded by the
inner dimension. This avoids any rank-of-sum (Cardinal) bookkeeping. -/

/-- A tensor with ordinary rank at most `r` has flattening rank at most `r`:
the flattening factors through `Fin r` as an `n × r` matrix times an
`r × n²` matrix. -/
theorem RankLE.rank_flattening_le {k : Type*} [CommRing k] [Nontrivial k] {n : ℕ}
    {T : Tensor3 k n} {r : ℕ} (h : RankLE T r) : (flattening T).rank ≤ r := by
  obtain ⟨a, b, c, rfl⟩ := h
  have hfac : flattening (n := n) (fun i j l => ∑ s, a s i * b s j * c s l) =
      Matrix.of (fun i (s : Fin r) => a s i) *
        Matrix.of (fun (s : Fin r) jl => b s jl.1 * c s jl.2) := by
    ext i jl
    simp [flattening, Matrix.mul_apply, mul_assoc]
  rw [hfac]
  exact (Matrix.rank_mul_le_left _ _).trans
    ((Matrix.rank_le_card_width _).trans_eq (Fintype.card_fin r))

/-! ## 4. Minors of low-rank matrices vanish -/

/-- Over a field, every `(r+1) × (r+1)` minor of a matrix of rank ≤ r
vanishes — with NO injectivity assumption on the row/column picks (a
repeated pick only makes the submatrix more degenerate). A nonzero
determinant would make the submatrix invertible, forcing its rank to be
`r + 1`, contradicting `Matrix.rank_submatrix_le`. -/
theorem det_submatrix_eq_zero_of_rank_le {k : Type*} [Field k] {m m' : Type*}
    [Fintype m'] {r : ℕ} {M : Matrix m m' k} (hM : M.rank ≤ r)
    (ri : Fin (r + 1) → m) (ci : Fin (r + 1) → m') :
    (M.submatrix ri ci).det = 0 := by
  by_contra hdet
  have hunit : IsUnit (M.submatrix ri ci) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have h1 : (M.submatrix ri ci).rank = r + 1 :=
    (Matrix.rank_of_isUnit _ hunit).trans (Fintype.card_fin (r + 1))
  have h2 : (M.submatrix ri ci).rank ≤ M.rank := Matrix.rank_submatrix_le M ri ci
  omega

/-! ## 5. The generic flattening and its minors

The flattening of the GENERIC tensor: the `n × (n × n)` matrix whose
`(i, (j, l))` entry is the variable `X (i, j, l)`. Its `(r+1) × (r+1)`
minors are the degree-(r+1) determinantal polynomials in the tensor
entries; on injective row/column picks they are nonzero polynomials
(§5), and they vanish identically on the rank-≤ r locus (§6). -/

/-- The generic flattening: entry `(i, (j, l))` is the variable
`X (i, j, l)` of the polynomial ring in the `n³` tensor entries. -/
noncomputable def genericFlattening (k : Type*) [CommSemiring k] (n : ℕ) :
    Matrix (Fin n) (Fin n × Fin n) (MvPolynomial (EntryIndex n) k) :=
  Matrix.of fun i jl => MvPolynomial.X (i, jl.1, jl.2)

/-- A minor of the generic flattening is the image of the fully generic
determinant `det (Matrix.mvPolynomialX)` under the variable rename
`(s, t) ↦ (ri s, (ci t).1, (ci t).2)`. -/
theorem det_genericFlattening_submatrix_eq_rename {k : Type*} [CommRing k] {n m : ℕ}
    (ri : Fin m → Fin n) (ci : Fin m → Fin n × Fin n) :
    ((genericFlattening k n).submatrix ri ci).det =
      MvPolynomial.rename
        (fun st : Fin m × Fin m => ((ri st.1, (ci st.2).1, (ci st.2).2) : EntryIndex n))
        (Matrix.mvPolynomialX (Fin m) (Fin m) k).det := by
  rw [AlgHom.map_det]
  congr 1
  ext s t
  simp [genericFlattening, MvPolynomial.rename_X]

/-- On injective row/column picks the generic flattening minor is a
NONZERO polynomial: the rename map is injective on variables, and
renaming along an injection is injective on polynomials, so
`Matrix.det_mvPolynomialX_ne_zero` transports. -/
theorem det_genericFlattening_submatrix_ne_zero {k : Type*} [CommRing k] [Nontrivial k]
    {n m : ℕ} {ri : Fin m → Fin n} {ci : Fin m → Fin n × Fin n}
    (hri : Function.Injective ri) (hci : Function.Injective ci) :
    ((genericFlattening k n).submatrix ri ci).det ≠ 0 := by
  have hf : Function.Injective
      (fun st : Fin m × Fin m => ((ri st.1, (ci st.2).1, (ci st.2).2) : EntryIndex n)) := by
    rintro ⟨s, t⟩ ⟨s', t'⟩ hst
    have h1 : ri s = ri s' := congrArg Prod.fst hst
    have h2 : ci t = ci t' := congrArg Prod.snd hst
    rw [hri h1, hci h2]
  rw [det_genericFlattening_submatrix_eq_rename]
  intro h0
  exact Matrix.det_mvPolynomialX_ne_zero (Fin m) k
    (MvPolynomial.rename_injective _ hf (h0.trans (map_zero _).symm))

/-- Evaluation bridge: evaluating a generic flattening minor at the entry
vector of a concrete tensor `T` yields the corresponding minor of the
concrete flattening (determinant commutes with the evaluation ring
homomorphism). -/
theorem eval_det_genericFlattening_submatrix {k : Type*} [CommRing k] {n m : ℕ}
    (ri : Fin m → Fin n) (ci : Fin m → Fin n × Fin n) (T : Tensor3 k n) :
    MvPolynomial.eval (entries T) ((genericFlattening k n).submatrix ri ci).det =
      ((flattening T).submatrix ri ci).det := by
  rw [RingHom.map_det]
  congr 1
  ext s t
  simp [genericFlattening, flattening, entries]

/-! ## 6. Generic minors vanish on the polynomial-closure border-rank locus -/

/-- The generic flattening minor lies in the vanishing ideal of the
rank-≤ r locus: at every rank-≤ r point it evaluates to a minor of a
rank-≤ r matrix (§3), which vanishes (§4). -/
theorem det_genericFlattening_submatrix_mem_vanishingIdeal {k : Type*} [Field k]
    {n r : ℕ} (ri : Fin (r + 1) → Fin n) (ci : Fin (r + 1) → Fin n × Fin n) :
    ((genericFlattening k n).submatrix ri ci).det ∈
      MvPolynomial.vanishingIdeal k (rankLocus k n r) := by
  rw [MvPolynomial.mem_vanishingIdeal_iff]
  rintro x ⟨T, hT, rfl⟩
  simp only [MvPolynomial.aeval_eq_eval]
  rw [eval_det_genericFlattening_submatrix]
  exact det_submatrix_eq_zero_of_rank_le hT.rank_flattening_le ri ci

/-- Generic flattening minors vanish on every tensor of polynomial-closure
border rank at most `r`: they lie in the vanishing ideal of the ordinary
rank-`≤ r` locus, and polynomial-closure border rank at most `r` means by
construction that all such polynomials vanish at `T`. -/
theorem BorderRankLE.eval_det_genericFlattening_submatrix_eq_zero {k : Type*} [Field k]
    {n : ℕ} {T : Tensor3 k n} {r : ℕ} (h : BorderRankLE T r)
    (ri : Fin (r + 1) → Fin n) (ci : Fin (r + 1) → Fin n × Fin n) :
    MvPolynomial.eval (entries T) ((genericFlattening k n).submatrix ri ci).det = 0 :=
  borderRankLE_iff.mp h _ (det_genericFlattening_submatrix_mem_vanishingIdeal ri ci)

#check @mem_rankLocus
#check @RankLE.mono
#check @borderRankLE_iff
#check @RankLE.borderRankLE
#check @BorderRankLE.mono
#check @RankLE.rank_flattening_le
#check @det_submatrix_eq_zero_of_rank_le
#check @det_genericFlattening_submatrix_eq_rename
#check @det_genericFlattening_submatrix_ne_zero
#check @eval_det_genericFlattening_submatrix
#check @det_genericFlattening_submatrix_mem_vanishingIdeal
#check @BorderRankLE.eval_det_genericFlattening_submatrix_eq_zero

#print axioms mem_rankLocus
#print axioms RankLE.mono
#print axioms borderRankLE_iff
#print axioms RankLE.borderRankLE
#print axioms BorderRankLE.mono
#print axioms RankLE.rank_flattening_le
#print axioms det_submatrix_eq_zero_of_rank_le
#print axioms det_genericFlattening_submatrix_eq_rename
#print axioms det_genericFlattening_submatrix_ne_zero
#print axioms eval_det_genericFlattening_submatrix
#print axioms det_genericFlattening_submatrix_mem_vanishingIdeal
#print axioms BorderRankLE.eval_det_genericFlattening_submatrix_eq_zero

end Vp2
