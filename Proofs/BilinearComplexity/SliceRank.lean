/-
  BilinearComplexity/SliceRank — slice rank of rectangular 3-tensors:
  the definition layer and the elementary structural results.

  Slice rank is the hinge invariant of the barrier literature
  (BCCGU Corollary 2.11, arXiv:1712.02302): it is how that
  literature formally rules out group families as routes to ω = 2, and
  it is the prototype "leave the degree-2 paradigm" invariant. A slice
  is a tensor of the form (a vector in one mode) ⊗ (a matrix in the
  other two); the slice rank is the least number of slices summing to
  `T`. This file mirrors `Basic.lean`'s rank layer exactly (same `sInf`
  pattern, same order API), building on the `Tensor`/`RankLE`/`rank`
  API defined there.

    · `IsSlice1/2/3 T`    — `T` is a single slice supported on mode 1,
                            2, or 3 (`T i j l = f i * M j l`, and cyclic
                            variants).
    · `SliceRankLE T r`   — `T` is a sum of at most `r` slices, in the
                            "three parts" shape `r₁ + r₂ + r₃ ≤ r`
                            (`SliceRankLE.exists_parts` /
                            `sliceRankLE_of_parts` are the binding
                            destructor/constructor pair). Comes with
                            `SliceRankLE.mono` and the three mode
                            totalities `sliceRankLE_left/mid/right`.
    · `sliceRank T`       — the least such `r` (`sInf`; total by
                            `sliceRankLE_left`), with the order API
                            `sliceRankLE_sliceRank`,
                            `sliceRank_le_of_sliceRankLE`,
                            `sliceRankLE_of_sliceRank_le`,
                            `sliceRank_le_iff`, the min-over-modes bound
                            `sliceRank_le_left/mid/right`, and
                            `sliceRank_zero`/`sliceRank_eq_zero_iff`.
    · `RankLE.sliceRankLE` / `sliceRank_le_rank` — a triad is a mode-1
                            slice, so `sliceRank T ≤ rank T`.
    · `diag w`            — the diagonal tensor `⟨w⟩`, with the upper
                            bound `sliceRank_diag_le`: its slice rank is
                            at most the number of nonzero diagonal
                            entries. (The matching lower bound — Tao's
                            diagonal lemma over a field — is card Sr2.)
    · `SliceRankLE.comp` / `sliceRank_comp_le` — pullback-monotonicity
                            (the sub-tensor lemma): precomposing the
                            three modes with arbitrary index maps never
                            increases slice rank. Mirrors `RankLE.comp`
                            of MatMulMono; no injectivity is needed.

  Everything is over `CommSemiring k`; the diagonal-support lemmas take
  `[DecidableEq k]` so the support finset is genuinely decidable.

  AI disclosure: produced with AI assistance (see Proofs/README).
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Lattice.Nat
import Mathlib.LinearAlgebra.Matrix.Rank
import BilinearComplexity.Basic
import BilinearComplexity.RankCalculus

set_option autoImplicit false

namespace BilinearComplexity

section SliceRank

variable {k : Type*} [CommSemiring k] {a b c : ℕ}

/-! ## 1. Slice predicates -/

/-- `IsSlice1 T` : `T` is a single slice supported on mode 1, i.e. a
vector `f` in mode 1 times a matrix `M` in modes 2, 3. -/
def IsSlice1 (T : Tensor k a b c) : Prop :=
  ∃ (f : Fin a → k) (M : Fin b → Fin c → k), ∀ i j l, T i j l = f i * M j l

/-- `IsSlice2 T` : `T` is a single slice supported on mode 2. -/
def IsSlice2 (T : Tensor k a b c) : Prop :=
  ∃ (g : Fin b → k) (N : Fin a → Fin c → k), ∀ i j l, T i j l = g j * N i l

/-- `IsSlice3 T` : `T` is a single slice supported on mode 3. -/
def IsSlice3 (T : Tensor k a b c) : Prop :=
  ∃ (e : Fin c → k) (P : Fin a → Fin b → k), ∀ i j l, T i j l = e l * P i j

/-! ## 2. The slice-rank-≤ r predicate -/

/-- `SliceRankLE T r` : the tensor `T` is a sum of at most `r` slices —
`r₁` mode-1 slices, `r₂` mode-2 slices, `r₃` mode-3 slices, with
`r₁ + r₂ + r₃ ≤ r`. This "three parts" primitive is the shape of the
binding destructor `SliceRankLE.exists_parts`; monotonicity is
immediate from it. -/
def SliceRankLE (T : Tensor k a b c) (r : ℕ) : Prop :=
  ∃ (r₁ r₂ r₃ : ℕ), r₁ + r₂ + r₃ ≤ r ∧
    ∃ (f : Fin r₁ → Fin a → k) (M : Fin r₁ → Fin b → Fin c → k)
      (g : Fin r₂ → Fin b → k) (N : Fin r₂ → Fin a → Fin c → k)
      (e : Fin r₃ → Fin c → k) (P : Fin r₃ → Fin a → Fin b → k),
      ∀ i j l, T i j l =
        (∑ s, f s i * M s j l) + (∑ s, g s j * N s i l) + (∑ s, e s l * P s i j)

/-- Binding destructor (Sr2's interface): a slice-rank-≤ r decomposition
splits into `r₁` mode-1, `r₂` mode-2, `r₃` mode-3 slice families with
`r₁ + r₂ + r₃ ≤ r`. Definitional for the "three parts" primitive. -/
theorem SliceRankLE.exists_parts {T : Tensor k a b c} {r : ℕ}
    (h : SliceRankLE T r) :
    ∃ (r₁ r₂ r₃ : ℕ), r₁ + r₂ + r₃ ≤ r ∧
      ∃ (f : Fin r₁ → Fin a → k) (M : Fin r₁ → Fin b → Fin c → k)
        (g : Fin r₂ → Fin b → k) (N : Fin r₂ → Fin a → Fin c → k)
        (e : Fin r₃ → Fin c → k) (P : Fin r₃ → Fin a → Fin b → k),
        ∀ i j l, T i j l =
          (∑ s, f s i * M s j l) + (∑ s, g s j * N s i l) + (∑ s, e s l * P s i j) :=
  h

/-- Binding constructor (Sr2's interface): three slice families with
`r₁ + r₂ + r₃ ≤ r` assemble into a slice-rank-≤ r decomposition. -/
theorem sliceRankLE_of_parts {T : Tensor k a b c} {r r₁ r₂ r₃ : ℕ}
    (hr : r₁ + r₂ + r₃ ≤ r)
    (f : Fin r₁ → Fin a → k) (M : Fin r₁ → Fin b → Fin c → k)
    (g : Fin r₂ → Fin b → k) (N : Fin r₂ → Fin a → Fin c → k)
    (e : Fin r₃ → Fin c → k) (P : Fin r₃ → Fin a → Fin b → k)
    (hT : ∀ i j l, T i j l =
      (∑ s, f s i * M s j l) + (∑ s, g s j * N s i l) + (∑ s, e s l * P s i j)) :
    SliceRankLE T r :=
  ⟨r₁, r₂, r₃, hr, f, M, g, N, e, P, hT⟩

/-- Slice rank is monotone in `r`: the same parts still fit under a
larger budget. -/
theorem SliceRankLE.mono {T : Tensor k a b c} {r r' : ℕ} (h : SliceRankLE T r)
    (hrr' : r ≤ r') : SliceRankLE T r' := by
  obtain ⟨r₁, r₂, r₃, hr, rest⟩ := h
  exact ⟨r₁, r₂, r₃, le_trans hr hrr', rest⟩

/-- Mode-1 totality: every tensor is a sum of `a` mode-1 slices
`e_i ⊗ (T i · ·)`. -/
theorem sliceRankLE_left (T : Tensor k a b c) : SliceRankLE T a := by
  refine ⟨a, 0, 0, by omega, fun s i => if s = i then 1 else 0, fun s j l => T s j l,
    Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, ?_⟩
  intro i j l
  simp [ite_mul]

/-- Mode-2 totality: every tensor is a sum of `b` mode-2 slices. -/
theorem sliceRankLE_mid (T : Tensor k a b c) : SliceRankLE T b := by
  refine ⟨0, b, 0, by omega, Fin.elim0, Fin.elim0, fun s j => if s = j then 1 else 0,
    fun s i l => T i s l, Fin.elim0, Fin.elim0, ?_⟩
  intro i j l
  simp [ite_mul]

/-- Mode-3 totality: every tensor is a sum of `c` mode-3 slices. -/
theorem sliceRankLE_right (T : Tensor k a b c) : SliceRankLE T c := by
  refine ⟨0, 0, c, by omega, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0,
    fun s l => if s = l then 1 else 0, fun s i j => T i j s, ?_⟩
  intro i j l
  simp [ite_mul]

/-! ## 3. Slice rank -/

/-- The slice rank of a tensor: the least `r` admitting a slice-rank-≤ r
decomposition. The defining set is nonempty by `sliceRankLE_left`, so
the `sInf` is attained (`sliceRankLE_sliceRank`). -/
noncomputable def sliceRank (T : Tensor k a b c) : ℕ :=
  sInf {r | SliceRankLE T r}

/-- The slice rank is attained. -/
theorem sliceRankLE_sliceRank (T : Tensor k a b c) : SliceRankLE T (sliceRank T) :=
  Nat.sInf_mem (s := {r | SliceRankLE T r}) ⟨a, sliceRankLE_left T⟩

theorem sliceRank_le_of_sliceRankLE {T : Tensor k a b c} {r : ℕ}
    (h : SliceRankLE T r) : sliceRank T ≤ r :=
  Nat.sInf_le h

theorem sliceRankLE_of_sliceRank_le {T : Tensor k a b c} {r : ℕ}
    (h : sliceRank T ≤ r) : SliceRankLE T r :=
  (sliceRankLE_sliceRank T).mono h

theorem sliceRank_le_iff {T : Tensor k a b c} {r : ℕ} :
    sliceRank T ≤ r ↔ SliceRankLE T r :=
  ⟨sliceRankLE_of_sliceRank_le, sliceRank_le_of_sliceRankLE⟩

/-- Min-over-modes bound (mode 1): `sliceRank T ≤ a`. -/
theorem sliceRank_le_left (T : Tensor k a b c) : sliceRank T ≤ a :=
  sliceRank_le_of_sliceRankLE (sliceRankLE_left T)

/-- Min-over-modes bound (mode 2): `sliceRank T ≤ b`. -/
theorem sliceRank_le_mid (T : Tensor k a b c) : sliceRank T ≤ b :=
  sliceRank_le_of_sliceRankLE (sliceRankLE_mid T)

/-- Min-over-modes bound (mode 3): `sliceRank T ≤ c`. -/
theorem sliceRank_le_right (T : Tensor k a b c) : sliceRank T ≤ c :=
  sliceRank_le_of_sliceRankLE (sliceRankLE_right T)

/-- Slice rank ≤ 0 means the tensor is zero (the empty sum of slices). -/
theorem sliceRankLE_zero_iff {T : Tensor k a b c} : SliceRankLE T 0 ↔ T = 0 := by
  constructor
  · rintro ⟨r₁, r₂, r₃, hr, f, M, g, N, e, P, hT⟩
    obtain ⟨rfl, rfl, rfl⟩ : r₁ = 0 ∧ r₂ = 0 ∧ r₃ = 0 := by omega
    funext i j l
    simpa using hT i j l
  · rintro rfl
    exact ⟨0, 0, 0, by omega, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0,
      Fin.elim0, by intro i j l; simp⟩

theorem sliceRank_zero : sliceRank (0 : Tensor k a b c) = 0 :=
  Nat.le_zero.mp (sliceRank_le_of_sliceRankLE (sliceRankLE_zero_iff.mpr rfl))

theorem sliceRank_eq_zero_iff {T : Tensor k a b c} : sliceRank T = 0 ↔ T = 0 := by
  rw [← Nat.le_zero, sliceRank_le_iff, sliceRankLE_zero_iff]

/-! ## 4. Slice rank ≤ rank -/

/-- A rank-one triad `u ⊗ v ⊗ w` is a mode-1 slice (`f := u`,
`M := v ⊗ w`), so any `r`-triad decomposition is a slice-rank-≤ r
decomposition. -/
theorem RankLE.sliceRankLE {T : Tensor k a b c} {r : ℕ} (h : RankLE T r) :
    SliceRankLE T r := by
  obtain ⟨u, v, w, hT⟩ := h
  refine ⟨r, 0, 0, by omega, u, fun s j l => v s j * w s l,
    Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, ?_⟩
  intro i j l
  simp only [hT, Fin.sum_univ_zero, add_zero, mul_assoc]

/-- Renamed form of `RankLE.sliceRankLE`. -/
theorem sliceRankLE_of_rankLE {T : Tensor k a b c} {r : ℕ} (h : RankLE T r) :
    SliceRankLE T r :=
  h.sliceRankLE

/-- Slice rank never exceeds rank. -/
theorem sliceRank_le_rank (T : Tensor k a b c) : sliceRank T ≤ rank T :=
  sliceRank_le_of_sliceRankLE (rankLE_rank T).sliceRankLE

/-! ## 5. The diagonal tensor and its slice-rank upper bound -/

/-- The diagonal tensor `⟨w⟩` of shape `n × n × n`: `w i` on the main
diagonal `i = j = l`, zero elsewhere. -/
def diag {n : ℕ} (w : Fin n → k) : Tensor k n n n :=
  fun i j l => if i = j ∧ j = l then w i else 0

/-- Slice-rank upper bound for the diagonal tensor: `⟨w⟩` is a sum of
one mode-1 slice per nonzero diagonal entry, indexed by the support of
`w` reindexed through `Finset.equivFin`. Off-support diagonal entries
are zero, so the sum reproduces `⟨w⟩`. -/
theorem sliceRankLE_diag [DecidableEq k] {n : ℕ} (w : Fin n → k) :
    SliceRankLE (diag w) ((Finset.univ.filter fun i => w i ≠ 0).card) := by
  set s : Finset (Fin n) := Finset.univ.filter (fun i => w i ≠ 0) with hs
  refine ⟨s.card, 0, 0, by omega,
    fun t i => if (s.equivFin.symm t : Fin n) = i then (1 : k) else 0,
    fun t j l =>
      if (s.equivFin.symm t : Fin n) = j ∧ j = l then w (s.equivFin.symm t) else 0,
    Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, ?_⟩
  intro i j l
  rw [Fin.sum_univ_zero, Fin.sum_univ_zero, add_zero, add_zero]
  -- reindex the sum over `Fin s.card` back to a sum over the support `s`
  have ereindex :
      (∑ t : Fin s.card,
        (if (s.equivFin.symm t : Fin n) = i then (1 : k) else 0) *
          (if (s.equivFin.symm t : Fin n) = j ∧ j = l then w (s.equivFin.symm t) else 0))
        = ∑ x : {x // x ∈ s},
          (if (x : Fin n) = i then (1 : k) else 0) *
            (if (x : Fin n) = j ∧ j = l then w (x : Fin n) else 0) :=
    Equiv.sum_comp s.equivFin.symm
      (fun x : {x // x ∈ s} =>
        (if (x : Fin n) = i then (1 : k) else 0) *
          (if (x : Fin n) = j ∧ j = l then w (x : Fin n) else 0))
  rw [ereindex, Finset.sum_coe_sort s
    (fun x => (if x = i then (1 : k) else 0) * (if x = j ∧ j = l then w x else 0))]
  -- off-support terms vanish, so extend the sum to all of `Fin n`
  rw [Finset.sum_subset (Finset.subset_univ s)]
  · -- compute the diagonal sum over `Fin n`
    simp only [diag, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · intro x _ hx
    have hwx : w x = 0 := by
      by_contra hne
      exact hx (by rw [hs]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hne⟩)
    simp [hwx]

/-- Slice-rank upper bound for the diagonal tensor: `sliceRank ⟨w⟩` is
at most the number of nonzero diagonal entries. -/
theorem sliceRank_diag_le [DecidableEq k] {n : ℕ} (w : Fin n → k) :
    sliceRank (diag w) ≤ (Finset.univ.filter fun i => w i ≠ 0).card :=
  sliceRank_le_of_sliceRankLE (sliceRankLE_diag w)

/-! ## 6. Cyclic rotation -/

/-- Slice rank does not increase under cyclic rotation: a mode-1 slice
of `T` is a mode-3 slice of `cyc T`, a mode-2 slice a mode-1 slice, a
mode-3 slice a mode-2 slice — the three parts rotate. -/
theorem SliceRankLE.cyc {T : Tensor k a b c} {r : ℕ} (h : SliceRankLE T r) :
    SliceRankLE (cyc T) r := by
  obtain ⟨r₁, r₂, r₃, hr, f, M, g, N, e, P, hT⟩ := h
  refine ⟨r₂, r₃, r₁, by omega, g, fun s L I => N s I L, e, fun s J I => P s I J,
    f, fun s J L => M s J L, ?_⟩
  intro J L I
  dsimp only [cyc_apply]
  rw [hT I J L]
  ring

/-- Slice rank-≤ is invariant under cyclic rotation (rotate twice more
to come back around, using `cyc³ = id`). -/
theorem sliceRankLE_cyc_iff {T : Tensor k a b c} {r : ℕ} :
    SliceRankLE (cyc T) r ↔ SliceRankLE T r :=
  ⟨fun h => h.cyc.cyc, SliceRankLE.cyc⟩

/-- Slice rank is invariant under cyclic rotation. -/
@[simp] theorem sliceRank_cyc (T : Tensor k a b c) : sliceRank (cyc T) = sliceRank T :=
  le_antisymm (sliceRank_le_of_sliceRankLE (sliceRankLE_sliceRank T).cyc)
    (sliceRank_le_of_sliceRankLE ((sliceRankLE_sliceRank (cyc T)).cyc.cyc))

/-! ## 7. Pullback along index maps (the sub-tensor lemma) -/

/-- Slice decompositions pull back along arbitrary index maps: composing
every slice family with the maps turns a slice-rank-≤ r decomposition of
`T` into one of the sub-tensor `fun i j l => T (f i) (g j) (e l)` with
the same parts, so `SliceRankLE` is preserved. No injectivity is required
— this mirrors `RankLE.comp` (MatMulMono's generic sub-tensor lemma) at
the slice-rank level. (Existing `SliceRankLE.mono` is monotonicity in the
budget `r`; this is monotonicity in the tensor.) -/
theorem SliceRankLE.comp {a' b' c' : ℕ} {T : Tensor k a' b' c'} {r : ℕ}
    (h : SliceRankLE T r) (f : Fin a → Fin a') (g : Fin b → Fin b')
    (e : Fin c → Fin c') :
    SliceRankLE (fun i j l => T (f i) (g j) (e l)) r := by
  obtain ⟨r₁, r₂, r₃, hr, f₁, M, g₂, N, e₃, P, hT⟩ := h
  exact ⟨r₁, r₂, r₃, hr, fun s i => f₁ s (f i), fun s j l => M s (g j) (e l),
    fun s j => g₂ s (g j), fun s i l => N s (f i) (e l),
    fun s l => e₃ s (e l), fun s i j => P s (f i) (g j),
    fun i j l => hT (f i) (g j) (e l)⟩

/-- **Pullback-monotonicity of slice rank.** Slice rank never increases
when a tensor is pulled back along arbitrary index maps on each mode. -/
theorem sliceRank_comp_le {a' b' c' : ℕ} (T : Tensor k a' b' c')
    (f : Fin a → Fin a') (g : Fin b → Fin b') (e : Fin c → Fin c') :
    sliceRank (fun i j l => T (f i) (g j) (e l)) ≤ sliceRank T :=
  sliceRank_le_of_sliceRankLE ((sliceRankLE_sliceRank T).comp f g e)

/-- Ground/satisfiability check at a non-injective pullback: pulling the
`2×2×2` all-ones diagonal back along the constant maps `Fin 3 → Fin 2`
gives the all-ones `3×3×3` tensor within slice-rank budget 2 — a bound
the mode totalities of the pulled-back tensor alone (3) cannot see. -/
example : SliceRankLE
    (fun (_ _ _ : Fin 3) => diag (fun _ : Fin 2 => (1 : ℤ)) 0 0 0) 2 :=
  (sliceRankLE_left (diag fun _ : Fin 2 => (1 : ℤ))).comp
    (fun _ => 0) (fun _ => 0) (fun _ => 0)

end SliceRank

/-! ## 8. Tao's diagonal lemma: the slice-rank lower bound

The matching lower bound to `sliceRank_diag_le`: over a field, the slice rank of
the diagonal tensor `⟨w⟩` is *exactly* the number of nonzero diagonal entries
(Tao's diagonal lemma, the hinge of the slice-rank method). The proof contracts a
slice decomposition against a vector `v` in the joint kernel of the mode-1 slice
functionals; the contraction is a diagonal matrix `diag (v · w)` on one side and a
sum of `r₂ + r₃` rank-one matrices on the other, so `rank (diag (v · w)) ≤ r₂ + r₃`.
Choosing `v` with maximal support inside that kernel (the "large support" lemma
`exists_mem_support_card_ge`) forces `(support card) - r₁ ≤ r₂ + r₃`. -/

section TaoDiagonal

/-- **Large-support lemma.** A subspace `V ⊆ (ι → K)` over a field contains a
vector whose number of nonzero coordinates is at least `finrank K V`. Equivalently,
`V` cannot consist entirely of vectors with fewer than `finrank K V` nonzero
coordinates. This is what upgrades the diagonal contraction from "some `v`" to "a
`v` that sees the whole support". -/
theorem exists_mem_support_card_ge {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : Type*} [Field K] [DecidableEq K] (V : Submodule K (ι → K)) :
    ∃ v ∈ V, Module.finrank K V ≤ (Finset.univ.filter fun i => v i ≠ 0).card := by
  -- Take the element `ymax` of `V` with maximal support size `M`.
  set g : ↥V → ℕ := fun y => (Finset.univ.filter fun i => (y : ι → K) i ≠ 0).card with hg_def
  have hne : (Set.range g).Nonempty := Set.range_nonempty g
  have hbdd : BddAbove (Set.range g) := by
    use Fintype.card ι
    rintro _ ⟨y, rfl⟩
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans Finset.card_univ.le
  set M := sSup (Set.range g) with hM_def
  have hM_mem : M ∈ Set.range g := Nat.sSup_mem hne hbdd
  obtain ⟨ymax, hymax⟩ := hM_mem
  have hle : ∀ y, g y ≤ M := fun y => le_csSup hbdd (Set.mem_range_self y)
  -- It suffices to show `finrank K V ≤ M`.
  suffices hsuff : Module.finrank K V ≤ M by
    refine ⟨↑ymax, SetLike.coe_mem ymax, ?_⟩
    have : g ymax = (Finset.univ.filter fun i => (ymax : ι → K) i ≠ 0).card := rfl
    omega
  by_contra hlt
  push Not at hlt
  -- `T` is the support of `ymax`, with `T.card = M`.
  set T : Finset ι := Finset.univ.filter fun i => (ymax : ι → K) i ≠ 0 with hT_def
  have hTcard : T.card = M := hymax
  -- Restriction-to-`T` map; rank–nullity forces its kernel to be nonzero.
  set ρ : ↥V →ₗ[K] (↥T → K) :=
    (LinearMap.funLeft K K (Subtype.val : ↥T → ι)).comp V.subtype with hρ_def
  have hρ_range : Module.finrank K (LinearMap.range ρ) ≤ T.card := by
    calc Module.finrank K (LinearMap.range ρ)
        ≤ Module.finrank K (↥T → K) := Submodule.finrank_le _
      _ = Fintype.card ↥T := Module.finrank_pi _
      _ = T.card := Fintype.card_coe T
  have hrn := LinearMap.finrank_range_add_finrank_ker ρ
  have hker_pos : 0 < Module.finrank K (LinearMap.ker ρ) := by omega
  have hker_ne : LinearMap.ker ρ ≠ ⊥ := by
    intro heq
    rw [heq, finrank_bot] at hker_pos
    exact Nat.lt_irrefl 0 hker_pos
  -- a nonzero `b ∈ ker ρ`: its support avoids `T`, so we can enlarge `ymax`'s support.
  obtain ⟨b, hb_mem, hb_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker_ne
  have hρb : ρ b = 0 := LinearMap.mem_ker.mp hb_mem
  have hb_vanish : ∀ i : ι, i ∈ T → (b : ι → K) i = 0 := by
    intro i hi
    have := congr_fun hρb ⟨i, hi⟩
    simp [hρ_def, LinearMap.comp_apply, LinearMap.funLeft_apply, Submodule.subtype_apply] at this
    exact this
  have hb_ne_fun : (b : ι → K) ≠ 0 := by
    rwa [ne_eq, Submodule.coe_eq_zero]
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hb_ne_fun
  simp only [Pi.zero_apply] at hi₀
  have hi₀_not_mem : i₀ ∉ T := by
    intro hmem
    exact hi₀ (hb_vanish i₀ hmem)
  have hymax_i₀ : (ymax : ι → K) i₀ = 0 := by
    by_contra h'
    exact hi₀_not_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h'⟩)
  -- `ymax + b` has support ⊇ `insert i₀ T` (disjoint supports, no cancellation).
  have hinsert_sub : insert i₀ T ⊆ Finset.univ.filter fun i => (↑(ymax + b) : ι → K) i ≠ 0 := by
    intro i hi
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    simp only [Submodule.coe_add, Pi.add_apply]
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · rw [hymax_i₀, zero_add]
      exact hi₀
    · rw [hb_vanish i hi', add_zero]
      exact (Finset.mem_filter.mp hi').2
  have hg_big : M + 1 ≤ g (ymax + b) := by
    calc M + 1 = T.card + 1 := by omega
      _ = (insert i₀ T).card := (Finset.card_insert_of_notMem hi₀_not_mem).symm
      _ ≤ g (ymax + b) := Finset.card_le_card hinsert_sub
  have := hle (ymax + b)
  omega

variable {k : Type*} [Field k]

/-- Full-support case of Tao's diagonal lemma: if every diagonal entry is nonzero,
the slice rank of `⟨w⟩` is at least `n`. -/
theorem sliceRankLE_diag_full [DecidableEq k] {n : ℕ} (w : Fin n → k)
    (hw : ∀ i, w i ≠ 0) {r : ℕ} (h : SliceRankLE (diag w) r) : n ≤ r := by
  obtain ⟨r₁, r₂, r₃, hr, f, M, g, N, e, P, hT⟩ := h
  refine le_trans ?_ hr
  -- contraction against the mode-1 slice functionals, as a linear map `Φ`
  set Fmat : Matrix (Fin r₁) (Fin n) k := Matrix.of fun s i => f s i with hFmat
  set Φ : (Fin n → k) →ₗ[k] (Fin r₁ → k) := Fmat.mulVecLin with hΦ
  -- rank–nullity: `n ≤ r₁ + finrank (ker Φ)`
  have hnull : Module.finrank k (LinearMap.range Φ) + Module.finrank k (LinearMap.ker Φ) = n := by
    rw [LinearMap.finrank_range_add_finrank_ker Φ, Module.finrank_pi, Fintype.card_fin]
  have hrange : Module.finrank k (LinearMap.range Φ) ≤ r₁ := by
    refine le_trans (Submodule.finrank_le _) ?_
    rw [Module.finrank_pi, Fintype.card_fin]
  have hn_le : n ≤ r₁ + Module.finrank k (LinearMap.ker Φ) := by omega
  -- a maximal-support vector `v` in `ker Φ`
  obtain ⟨v, hvmem, hvcard⟩ := exists_mem_support_card_ge (LinearMap.ker Φ)
  have hker : ∀ s, ∑ i, f s i * v i = 0 := by
    intro s
    have h0 : Φ v = 0 := LinearMap.mem_ker.mp hvmem
    have := congrFun h0 s
    simpa [hΦ, hFmat, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.of_apply] using this
  -- the contraction of the diagonal against `v`
  have hdiagLHS : ∀ jj ll : Fin n,
      (∑ i, v i * diag w i jj ll) = if jj = ll then v jj * w jj else 0 := by
    intro jj ll
    simp only [diag]
    by_cases hjl : jj = ll
    · rw [if_pos hjl, Finset.sum_eq_single_of_mem jj (Finset.mem_univ jj)]
      · rw [if_pos (show jj = jj ∧ jj = ll from ⟨rfl, hjl⟩)]
      · intro i _ hij
        rw [if_neg (fun h => hij h.1), mul_zero]
    · rw [if_neg hjl]
      apply Finset.sum_eq_zero
      intro i _
      rw [if_neg (fun h => hjl h.2), mul_zero]
  -- contracting the slice decomposition kills the mode-1 part (`hker`)
  have contract : ∀ jj ll : Fin n, (∑ i, v i * diag w i jj ll)
      = (∑ s : Fin r₂, g s jj * ∑ i, v i * N s i ll)
        + ∑ s : Fin r₃, (∑ i, v i * P s i jj) * e s ll := by
    intro jj ll
    have step1 : (∑ i, v i * diag w i jj ll)
        = ((∑ s : Fin r₁, (∑ i, v i * f s i) * M s jj ll)
          + (∑ s : Fin r₂, g s jj * ∑ i, v i * N s i ll))
          + ∑ s : Fin r₃, (∑ i, v i * P s i jj) * e s ll := by
      simp only [hT, mul_add, Finset.sum_add_distrib]
      refine congr_arg₂ (· + ·) (congr_arg₂ (· + ·) ?_ ?_) ?_
      · simp only [Finset.mul_sum]; rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
      · simp only [Finset.mul_sum]; rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => by ring
      · simp only [Finset.mul_sum]; rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [step1]
    have hz : (∑ s : Fin r₁, (∑ i, v i * f s i) * M s jj ll) = 0 := by
      apply Finset.sum_eq_zero
      intro s _
      have : (∑ i, v i * f s i) = 0 := by
        rw [← hker s]; exact Finset.sum_congr rfl fun i _ => by ring
      rw [this, zero_mul]
    rw [hz, zero_add]
  -- the two contraction matrices `Hm`, `Vm`, so that `diag (v · w) = Hm * Vm`
  set Hm : Matrix (Fin n) (Fin r₂ ⊕ Fin r₃) k :=
    Matrix.of fun j x => Sum.elim (fun s => g s j) (fun s => ∑ i, v i * P s i j) x with hHm
  set Vm : Matrix (Fin r₂ ⊕ Fin r₃) (Fin n) k :=
    Matrix.of fun x l => Sum.elim (fun s => ∑ i, v i * N s i l) (fun s => e s l) x with hVm
  have hmateq : Matrix.diagonal (fun j => v j * w j) = Hm * Vm := by
    ext j l
    rw [Matrix.diagonal_apply, Matrix.mul_apply, Fintype.sum_sum_type]
    simp only [hHm, hVm, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr]
    rw [← hdiagLHS j l]
    exact contract j l
  -- `rank (diag (v · w)) ≤ r₂ + r₃`
  have hrankle : (Matrix.diagonal (fun j => v j * w j)).rank ≤ r₂ + r₃ := by
    rw [hmateq]
    calc (Hm * Vm).rank ≤ Hm.rank := Matrix.rank_mul_le_left Hm Vm
      _ ≤ Fintype.card (Fin r₂ ⊕ Fin r₃) := Matrix.rank_le_card_width Hm
      _ = r₂ + r₃ := by rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  -- `rank (diag (v · w)) = |support v|` (all diagonal entries of `w` nonzero)
  have hdiagrank : (Matrix.diagonal (fun j => v j * w j)).rank
      = (Finset.univ.filter fun i => v i ≠ 0).card := by
    rw [Matrix.rank_diagonal, Fintype.card_subtype]
    congr 1
    refine Finset.filter_congr fun i _ => ?_
    constructor
    · exact fun h => left_ne_zero_of_mul h
    · exact fun h => mul_ne_zero h (hw i)
  -- assemble
  have hfin : Module.finrank k (LinearMap.ker Φ) ≤ r₂ + r₃ :=
    le_trans hvcard (hdiagrank ▸ hrankle)
  omega

/-- Tao's diagonal lemma (lower bound form): every slice-rank-≤ r decomposition of
`⟨w⟩` over a field has `r` at least the number of nonzero diagonal entries. -/
theorem card_le_of_sliceRankLE_diag [DecidableEq k] {n : ℕ} (w : Fin n → k) {r : ℕ}
    (h : SliceRankLE (diag w) r) : (Finset.univ.filter fun i => w i ≠ 0).card ≤ r := by
  -- reindex the nonzero support `S` to `Fin S.card`, reducing to the full-support case
  set S : Finset (Fin n) := Finset.univ.filter fun i => w i ≠ 0 with hS
  set σ : Fin S.card → Fin n := fun t => (S.equivFin.symm t : Fin n) with hσdef
  have hσ : Function.Injective σ := fun a b hab =>
    S.equivFin.symm.injective (Subtype.val_injective hab)
  set w' : Fin S.card → k := fun t => w (σ t) with hw'def
  have hw' : ∀ t, w' t ≠ 0 := by
    intro t
    have hmem : σ t ∈ S := (S.equivFin.symm t).2
    rw [hS, Finset.mem_filter] at hmem
    exact hmem.2
  -- restrict every slice family through `σ`; the diagonal identity transports by injectivity
  have h' : SliceRankLE (diag w') r := by
    obtain ⟨r₁, r₂, r₃, hr, f, M, g, N, e, P, hT⟩ := h
    refine ⟨r₁, r₂, r₃, hr,
      fun s t => f s (σ t), fun s t₂ t₃ => M s (σ t₂) (σ t₃),
      fun s t => g s (σ t), fun s t t₃ => N s (σ t) (σ t₃),
      fun s t => e s (σ t), fun s t t₂ => P s (σ t) (σ t₂), ?_⟩
    intro t₁ t₂ t₃
    rw [show diag w' t₁ t₂ t₃ = diag w (σ t₁) (σ t₂) (σ t₃) by
      simp only [diag, hw'def, hσ.eq_iff]]
    exact hT (σ t₁) (σ t₂) (σ t₃)
  exact sliceRankLE_diag_full w' hw' h'

/-- **Tao's diagonal lemma.** Over a field, the slice rank of the diagonal tensor
`⟨w⟩` equals the number of nonzero diagonal entries. -/
theorem sliceRank_diag [DecidableEq k] {n : ℕ} (w : Fin n → k) :
    sliceRank (diag w) = (Finset.univ.filter fun i => w i ≠ 0).card :=
  le_antisymm (sliceRank_diag_le w)
    (card_le_of_sliceRankLE_diag w (sliceRankLE_sliceRank (diag w)))

end TaoDiagonal

/-! Axiom audit for the main declarations. -/

#print axioms sliceRank_le_rank
#print axioms sliceRank_cyc
#print axioms sliceRank_comp_le
#print axioms sliceRank_diag

end BilinearComplexity
