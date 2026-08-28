/-
  BilinearComplexity/Peeling — the list model of peeling for the min-peak
  lemma farm (Pl25/Sm1).

  A decomposition of a tensor `T` is a `List` of triads `(u, v, w)` whose
  sum equals `T`. The peeling trajectory subtracts triads one at a time and
  tracks the nonzero-entry count of each residual.

  KEY CONVENTION (load-bearing; j = 0 excluded).
  `peak T L` is the maximum of `nnz (residual T L j)` over `j ∈ [1, L.length]`.
  The initial `nnz T` (j = 0) is NOT counted. Under the alternative convention
  that includes j = 0, the corresponding value is `max (nnz T) (peak T L)`.

  The Bool layer (`peakB`, `isDecompB`) is computable via structural
  recursion on lists, all the way down to `native_decide`. Every definition
  is `abbrev` to ensure `native_decide` can unfold them.

  AI disclosure: produced with AI assistance (see Proofs/README).
-/
import BilinearComplexity.Support

namespace BilinearComplexity

/-! ## 1. Triads as data -/

variable {k : Type*} [DecidableEq k] {a b c : ℕ}

/-- A `TriadData` bundles the three vector components of a rank-one triad. -/
abbrev TriadData (k : Type*) (a b c : ℕ) : Type _ :=
  (Fin a → k) × (Fin b → k) × (Fin c → k)

/-- Evaluate a `TriadData` to its tensor `u ⊗ v ⊗ w`. -/
abbrev TriadData.eval [CommSemiring k] (t : TriadData k a b c) : Tensor k a b c :=
  triad t.1 t.2.1 t.2.2

/-! ## 2. Decompositions and the sum of a list of triads -/

/-- A decomposition is a `List` of `TriadData`. -/
abbrev Decomp (k : Type*) (a b c : ℕ) : Type _ := List (TriadData k a b c)

/-- The sum tensor of a list of triads: structural recursion on the list. -/
abbrev decompSum [CommSemiring k] : Decomp k a b c → Tensor k a b c
  | [] => 0
  | t :: ts => fun i j l => t.eval i j l + decompSum ts i j l

/-- `IsDecomp T L` : the sum of the triads in `L` equals `T`. -/
abbrev IsDecomp [CommSemiring k] (T : Tensor k a b c) (L : Decomp k a b c) : Prop :=
  decompSum L = T

/-! ## 3. Residuals -/

/-- `residual T L` = T minus the sum of the triads in `L`, computed by
peeling one triad at a time. Structural recursion on `L`. -/
abbrev residual [CommRing k] (T : Tensor k a b c) : Decomp k a b c → Tensor k a b c
  | [] => T
  | t :: ts =>
    residual (fun i j l => T i j l - t.eval i j l) ts

/-- Partial residual: peel only the first `j` triads. -/
abbrev residualAt [CommRing k] (T : Tensor k a b c) (L : Decomp k a b c) (j : ℕ) :
    Tensor k a b c :=
  residual T (L.take j)

omit [DecidableEq k] in
/-- The residual at j = 0 is the tensor itself. -/
theorem residualAt_zero [CommRing k] (T : Tensor k a b c) (L : Decomp k a b c) :
    residualAt T L 0 = T := rfl

/-! ## 4. Peak (j ≥ 1 convention) -/

/-- `nnzTrajectory T L` : the list of `nnz` values at each step of peeling.
`nnzTrajectory T [t₁, t₂, ..., tₙ]` = `[nnz(T - t₁), nnz(T - t₁ - t₂), ...]`.
The j = 0 value `nnz T` is NOT in this list. -/
abbrev nnzTrajectory [CommRing k] (T : Tensor k a b c) : Decomp k a b c → List ℕ
  | [] => []
  | t :: ts =>
    let T' := fun i j l => T i j l - t.eval i j l
    nnz T' :: nnzTrajectory T' ts

/-- `peak T L` = max over `j ∈ [1, L.length]` of `nnz (residualAt T L j)`.
The j = 0 case (nnz T itself) is **excluded** by design (see file header).
Implemented as the maximum of the nnz trajectory. -/
abbrev peak [CommRing k] (T : Tensor k a b c) (L : Decomp k a b c) : ℕ :=
  (nnzTrajectory T L).foldl max 0

/-! ## 5. Bool layer for native_decide -/

/-- Decidable equality check for tensors, entrywise. -/
abbrev tensorDecEq [CommSemiring k] (T T' : Tensor k a b c) : Bool :=
  (Finset.univ.filter fun p : Fin a × Fin b × Fin c =>
    T p.1 p.2.1 p.2.2 ≠ T' p.1 p.2.1 p.2.2).card == 0

/-- `isDecompB T L` : Bool test that the sum of triads equals `T`. -/
abbrev isDecompB [CommSemiring k] (T : Tensor k a b c) (L : Decomp k a b c) : Bool :=
  tensorDecEq (decompSum L) T

theorem isDecompB_iff [CommSemiring k] (T : Tensor k a b c) (L : Decomp k a b c) :
    isDecompB T L = true ↔ IsDecomp T L := by
  simp only [isDecompB, tensorDecEq, beq_iff_eq, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff, IsDecomp]
  constructor
  · intro h
    funext i j l
    by_contra hne
    have := h (Finset.mem_univ ⟨i, j, l⟩)
    exact hne (not_not.mp this)
  · intro h p _
    simp [h]

/-- `peakB T L` : computable peak, matching `peak`. -/
abbrev peakB [CommRing k] (T : Tensor k a b c) (L : Decomp k a b c) : ℕ :=
  peak T L

theorem peakB_eq_peak [CommRing k] (T : Tensor k a b c) (L : Decomp k a b c) :
    peakB T L = peak T L := rfl

/-! ## 6. minPeakOverPerms: brute-force over all orderings (small r only) -/

/-- Minimum of a list of natural numbers with a default. -/
abbrev listMin : List ℕ → ℕ → ℕ
  | [], d => d
  | x :: xs, d => listMin xs (min d x)

/-- The minimum peak over all permutations of a decomposition's triad list.
For small `r` only (r! orderings); do NOT use beyond r ≈ 8. -/
abbrev minPeakOverPerms [CommRing k] (T : Tensor k a b c) (L : Decomp k a b c) : ℕ :=
  listMin (L.permutations.map (peak T)) (peak T L)

private theorem listMin_le_default (xs : List ℕ) (d : ℕ) :
    listMin xs d ≤ d := by
  induction xs generalizing d with
  | nil => exact le_refl _
  | cons x xs ih =>
    simp only [listMin]
    exact le_trans (ih _) (min_le_left _ _)

theorem minPeakOverPerms_le_peak [CommRing k] (T : Tensor k a b c)
    (L : Decomp k a b c) :
    minPeakOverPerms T L ≤ peak T L :=
  listMin_le_default _ _

private theorem listMin_le_mem (xs : List ℕ) (d : ℕ) (x : ℕ) (hx : x ∈ xs) :
    listMin xs d ≤ x := by
  induction xs generalizing d with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [listMin]
    cases List.mem_cons.mp hx with
    | inl heq =>
      subst heq
      exact le_trans (listMin_le_default _ _) (min_le_right _ _)
    | inr hmem =>
      exact ih _ hmem

theorem minPeakOverPerms_le_peak_perm [CommRing k] (T : Tensor k a b c)
    (L L' : Decomp k a b c) (hperm : L' ∈ L.permutations) :
    minPeakOverPerms T L ≤ peak T L' := by
  exact listMin_le_mem _ _ _ (List.mem_map.mpr ⟨L', hperm, rfl⟩)

end BilinearComplexity
