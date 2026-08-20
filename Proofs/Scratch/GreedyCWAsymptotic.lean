/-
  Scratch/GreedyCWAsymptotic — the greedy Coppersmith–Winograd sequence
  (OEIS A172161): Greathouse's recurrence, proved, and McEachen's growth
  conjecture, proved.

  ## OEIS provenance (re-pulled 2026-08-20; `%F`/`%e` lines verbatim, the
  property phrasing is this file's disambiguation — see below)

  A172161 (Warren D. Smith, Jan 27 2010): start with `S = {0, 1}` and
  repeatedly adjoin the least new integer such that `S` keeps what the
  entry's comment names the Coppersmith–Winograd property.  The entry
  says only "three disjoint subsets"; this file reads that as *pairwise
  disjoint and nonempty* — a forced disambiguation, not a quote: the
  empty-allowed reading is false already at `{0, 1}`, and only the
  pairwise+nonempty reading reproduces the DATA (checked through a(15)).
  DATA: 0, 1, 2, 3, 4, 6, 9, 13, 20, 30, 45, 67, 101, … (offset 1).  The
  `%e` line rejects 5 via the triple `{5}, {1, 4}, {2, 3}`.

  Two `%F` lines, neither carrying a proof or reference in the entry;
  Greathouse's is asserted as a bare formula, only McEachen's is labeled
  "Conjecture":
  * `a(n) = floor((Sum_{i<n} a(i))/2) + 1 for n > 4`
    — Charles R Greathouse IV, Dec 02 2022.
  * `Conjecture: a(n) ~ k*(3/2)^n for some k.` — Bill McEachen, Dec 02 2022.
  A `%C` comment by McEachen (Dec 02 2022) generates the sequence from
  `b(0)=2, b(1)=2, b(2)=3, b(3)=5, b(4)=8`, `b(n) = floor(3*b(n-1)/2)`,
  with a(n) the first differences of b(n) — the A120134 tie-in (Warren D.
  Smith: "probably can be proved, but I haven't yet") that this file does
  not treat.

  ## What this file proves (both sorry-free)

  * `greedyA_recurrence` — Greathouse's recurrence, for the *greedy*
    definition (not for a recurrence-defined clone).  The proof splits into
    - safety (`cwProperty_insert_of_sum_lt`): any `m` with `Σ < 2m` keeps
      the CW property, because a violating triple using `m` would have its
      two `m`-free parts disjoint inside `S`, forcing `2t ≤ Σ < 2m ≤ 2t`;
    - minimality: every smaller candidate is rejected.  The engine is the
      invariant `PairRep S` — every pair of targets `u, v` with
      `u + v ≤ Σ` *outside four exceptional patterns* (`BadPair`:
      `(1,1)`, `(2,2)`, `(1, Σ-2)`, `(2, Σ-4)`, which are genuinely
      unrealizable because every representation of `1` uses the element
      `1` and every representation of `2` uses `2`) is realized by two
      *disjoint* subsets of `S`.  `PairRep` propagates through the greedy
      insertion `m = Σ/2 + 1` (`pairRep_insert`: lift, else peel `m` off
      the larger target — an overflowing total forces it past `Σ/2` — with
      a two-corner fallback peeling `m` off the smaller target), and at
      `u = v = m` it yields the violating triple `{m}, X, Y` for every
      candidate `m ≤ Σ/2` outside `S` (`not_cwProperty_insert_of_pairRep`;
      candidates `1, 2` are already members).  The base case is a
      decidable check on `{0, 1, 2, 3}`.
  * `mcEachen_growth` — the growth conjecture, derived from the recurrence:
    with `A n = Σ_{i<n} a(i)` the recurrence gives
    `3·A n < 2·A (n+1) ≤ 3·A n + 2`, so `(A n + 2)·(2/3)^n` is antitone
    with summable decrements, hence converges to a limit `L ≥ 224/243`,
    and `a(n)/(3/2)^n → L/2 > 0` by squeezing.

  ## Novelty and deviations

  * Both statements are proved here from the greedy definition alone.
    For Greathouse's recurrence we FOUND NO RECORD of a prior proof —
    corpora searched 2026-08-20: the A172161 entry and its links, the
    A120134 entry, and this repo's References corpus.  That is a
    found-no-record claim, not a priority, first-proof, or publication claim;
    mathematical publishability has not been assessed here.
  * The asymptotic carries NO novelty claim: given the recurrence it is a
    standard floor-recurrence convergence argument (the Odlyzko–Wilf 1991
    class, Prop. 1 shape), and the constant is already recorded on
    A120134 to 70+ digits (Kotesovec; `greedyLimit · 243/64` matches it).
    The mathematical content of this file is greedy ⟹ recurrence.
  * The sibling card `Candidates/A172161GreedyCW.lean` currently FAILS to
    build, for three reasons — the first a failed `decreasing_by` at its
    line 133, then its two 6-element `CWProperty` `decide` examples
    exceed the default `maxRecDepth` — so nothing is imported from it;
    the definitions below restate the same `CWProperty` shape and the
    statements mirror its `mcEachen_growth` / recurrence targets.
  * All kernel computation in this file is bounded: the largest `decide`
    is the `PairRep {0,1,2,3}` base case (≈ 7·7·16·16 subset checks).
    6-element `CWProperty` `decide`s are feasible with `maxRecDepth`
    raised (≈ 30 s each) but are not needed here.
-/
import Mathlib

set_option autoImplicit false

namespace GreedyCW

open Finset Filter

/-! ## The Coppersmith–Winograd property and the greedy sequence -/

/-- The **Coppersmith–Winograd property** for a finite set `S` of naturals:
no three pairwise disjoint **nonempty** subsets of `S` have equal sums.
Nonemptiness is load-bearing: with `0 ∈ S` and empty parts allowed,
`∅, ∅, {0}` would violate every version of the property. -/
def CWProperty (S : Finset ℕ) : Prop :=
  ∀ A ⊆ S, ∀ B ⊆ S, ∀ C ⊆ S, A.Nonempty → B.Nonempty → C.Nonempty →
    Disjoint A B → Disjoint A C → Disjoint B C →
    ¬(A.sum id = B.sum id ∧ B.sum id = C.sum id)

/-- `CWProperty` is decidable: the subset quantifiers range over a finite
powerset. -/
instance (S : Finset ℕ) : Decidable (CWProperty S) := by
  unfold CWProperty; infer_instance

/-- The next greedy element: the least `m ∉ S` such that `insert m S` still
has the CW property.  `sInf` is `Nat.sInf`; whenever `CWProperty S` holds the
candidate set is nonempty (`exists_greedyNext`), so no junk value occurs at
any use site in this file. -/
noncomputable def greedyNext (S : Finset ℕ) : ℕ :=
  sInf {m | m ∉ S ∧ CWProperty (insert m S)}

/-- The greedy Coppersmith–Winograd set after `n` adjunctions to `{0, 1}`. -/
noncomputable def greedySet : ℕ → Finset ℕ
  | 0 => {0, 1}
  | n + 1 => insert (greedyNext (greedySet n)) (greedySet n)

/-- A172161 with the OEIS offset: `greedyA 1 = 0`, `greedyA 2 = 1`, and
`greedyA (n + 3)` is the element adjoined to `greedySet n`.  `greedyA 0 = 0`
is unused junk (the offset is 1); it contributes `0` to all range sums. -/
noncomputable def greedyA : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | n + 3 => greedyNext (greedySet n)

/-- Unfolding lemma: the greedy construction starts at `{0, 1}`. -/
lemma greedySet_zero : greedySet 0 = {0, 1} := rfl

/-- Unfolding lemma: each step inserts the least valid new element. -/
lemma greedySet_succ (n : ℕ) :
    greedySet (n + 1) = insert (greedyNext (greedySet n)) (greedySet n) := rfl

/-- `greedyA 0` is the unused offset-0 junk value. -/
@[simp] lemma greedyA_zero : greedyA 0 = 0 := rfl

/-- OEIS DATA: `a(1) = 0`. -/
@[simp] lemma greedyA_one : greedyA 1 = 0 := rfl

/-- OEIS DATA: `a(2) = 1`. -/
@[simp] lemma greedyA_two : greedyA 2 = 1 := rfl

/-- Unfolding lemma: `greedyA (n + 3)` is the element adjoined to `greedySet n`. -/
lemma greedyA_add_three (n : ℕ) : greedyA (n + 3) = greedyNext (greedySet n) := rfl

/-- The partial sums `A n = Σ_{i < n} greedyA i` (OEIS `Sum_{i<n} a(i)`). -/
noncomputable def sumA (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, greedyA i

/-- The one-step unfolding of the partial sums. -/
lemma sumA_succ_eq (n : ℕ) : sumA (n + 1) = sumA n + greedyA n :=
  Finset.sum_range_succ _ _

/-! ## Safety: any `m` with `Σ < 2·m` preserves the CW property -/

/-- A subset of `insert m S` avoiding `m` is a subset of `S`. -/
lemma subset_of_subset_insert {m : ℕ} {X S : Finset ℕ}
    (hX : X ⊆ insert m S) (hm : m ∉ X) : X ⊆ S := by
  intro x hx
  rcases Finset.mem_insert.mp (hX hx) with rfl | hxS
  · exact absurd hx hm
  · exact hxS

/-- **Safety.**  If `S` has the CW property and `S.sum id < 2 * m`, then
`insert m S` has it too: in a violating triple the part containing `m` has
sum at least `m`, while the two `m`-free parts are disjoint subsets of `S`,
so twice the common sum is at most `Σ < 2m` — a contradiction.  This covers
both the greedy step `m = Σ/2 + 1` and the coarse witness `m = Σ + 1`. -/
theorem cwProperty_insert_of_sum_lt {S : Finset ℕ} {m : ℕ}
    (hS : CWProperty S) (hm : S.sum id < 2 * m) : CWProperty (insert m S) := by
  intro A hA B hB C hC hAne hBne hCne hAB hAC hBC h
  obtain ⟨h1, h2⟩ := h
  -- If two parts sit inside `S` and the third contains `m`, count sums.
  have key : ∀ P Q R : Finset ℕ, P ⊆ S → Q ⊆ S → Disjoint P Q → m ∈ R →
      P.sum id = R.sum id → Q.sum id = R.sum id → False := by
    intro P Q R hP hQ hPQ hmR hPR hQR
    have hmle : m ≤ R.sum id := by
      simpa using Finset.single_le_sum (f := id) (fun i _ => Nat.zero_le i) hmR
    have hsum : P.sum id + Q.sum id ≤ S.sum id := by
      rw [← Finset.sum_union hPQ]
      exact Finset.sum_le_sum_of_subset (Finset.union_subset hP hQ)
    omega
  by_cases hmA : m ∈ A
  · have hmB : m ∉ B := fun hmB => Finset.disjoint_left.mp hAB hmA hmB
    have hmC : m ∉ C := fun hmC => Finset.disjoint_left.mp hAC hmA hmC
    exact key B C A (subset_of_subset_insert hB hmB) (subset_of_subset_insert hC hmC)
      hBC hmA h1.symm (h1.trans h2).symm
  by_cases hmB : m ∈ B
  · have hmC : m ∉ C := fun hmC => Finset.disjoint_left.mp hBC hmB hmC
    exact key A C B (subset_of_subset_insert hA hmA) (subset_of_subset_insert hC hmC)
      hAC hmB h1 h2.symm
  by_cases hmC : m ∈ C
  · exact key A B C (subset_of_subset_insert hA hmA) (subset_of_subset_insert hB hmB)
      hAB hmC (h1.trans h2) h2
  · exact hS A (subset_of_subset_insert hA hmA) B (subset_of_subset_insert hB hmB)
      C (subset_of_subset_insert hC hmC) hAne hBne hCne hAB hAC hBC ⟨h1, h2⟩

/-- The candidate set for the greedy step is nonempty: `Σ + 1` is new and
safe.  This is Smith's "the sequence is clearly infinite" comment. -/
theorem exists_greedyNext {S : Finset ℕ} (hS : CWProperty S) :
    ∃ m, m ∉ S ∧ CWProperty (insert m S) := by
  refine ⟨S.sum id + 1, fun hmem => ?_, cwProperty_insert_of_sum_lt hS (by omega)⟩
  have h : S.sum id + 1 ≤ S.sum id := by
    simpa using Finset.single_le_sum (f := id) (fun i _ => Nat.zero_le i) hmem
  omega

/-- The greedy step lands in the candidate set. -/
theorem greedyNext_spec {S : Finset ℕ} (hS : CWProperty S) :
    greedyNext S ∉ S ∧ CWProperty (insert (greedyNext S) S) :=
  Nat.sInf_mem (exists_greedyNext hS)

/-- Every greedy prefix has the CW property. -/
theorem cwProperty_greedySet : ∀ n, CWProperty (greedySet n)
  | 0 => by decide
  | n + 1 => (greedyNext_spec (cwProperty_greedySet n)).2

/-- The adjoined element is always new. -/
theorem greedyNext_not_mem_greedySet (n : ℕ) :
    greedyNext (greedySet n) ∉ greedySet n :=
  (greedyNext_spec (cwProperty_greedySet n)).1

/-- The set sum of the greedy prefix is the range sum of the sequence. -/
theorem sum_greedySet : ∀ n, (greedySet n).sum id = sumA (n + 3)
  | 0 => by
    simp [greedySet_zero, sumA, Finset.sum_range_succ]
  | n + 1 => by
    have hidx : n + 1 + 3 = (n + 3) + 1 := rfl
    rw [greedySet_succ, Finset.sum_insert (greedyNext_not_mem_greedySet n), hidx,
      sumA_succ_eq, sum_greedySet n, greedyA_add_three]
    simp only [id_eq]
    omega

/-- If `m` is a member of the candidate set and everything below `m` is not,
then the greedy step picks `m`. -/
lemma greedyNext_eq_of_min {S : Finset ℕ} {m : ℕ}
    (hmem : m ∉ S ∧ CWProperty (insert m S))
    (hmin : ∀ k, k < m → k ∈ S ∨ ¬CWProperty (insert k S)) :
    greedyNext S = m := by
  have hle : greedyNext S ≤ m :=
    Nat.sInf_le (s := {m | m ∉ S ∧ CWProperty (insert m S)}) hmem
  have hinf : greedyNext S ∉ S ∧ CWProperty (insert (greedyNext S) S) :=
    Nat.sInf_mem (s := {m | m ∉ S ∧ CWProperty (insert m S)}) ⟨m, hmem⟩
  rcases Nat.lt_or_ge (greedyNext S) m with hlt | hge
  · rcases hmin _ hlt with hin | hnot
    · exact absurd hin hinf.1
    · exact absurd hinf.2 hnot
  · exact le_antisymm hle hge

/-! ## Minimality: guarded pair-representation completeness

`PairRep S` is the double-representation invariant that rejects every
candidate below `Σ/2 + 1`.  It cannot hold for *all* target pairs: in a
greedy prefix every subset summing to `1` contains the element `1` and
every subset summing to `2` contains `2`, so the pairs `(1,1)`, `(2,2)`
and their complement reflections `(1, Σ-2)`, `(2, Σ-4)` are never realized
by disjoint subsets.  Exactly these four patterns are excluded by
`BadPair`; the guarded invariant propagates along the greedy construction
by pure arithmetic and is checked on `{0,1,2,3}` by `decide`. -/

/-- The four exceptional target-pair patterns, symmetric in `u, v`:
`(1,1)`, `(2,2)`, `(1, s-2)`, `(2, s-4)` (written additively, so no
truncated subtraction occurs).  In every greedy prefix with total `s`
these pairs are genuinely unrealizable by disjoint subsets. -/
def BadPair (u v s : ℕ) : Prop :=
  (u = 1 ∧ v = 1) ∨ (u = 2 ∧ v = 2) ∨
  (u = 1 ∧ v + 2 = s) ∨ (v = 1 ∧ u + 2 = s) ∨
  (u = 2 ∧ v + 4 = s) ∨ (v = 2 ∧ u + 4 = s)

/-- `BadPair` is a decidable disjunction of ℕ equations. -/
instance (u v s : ℕ) : Decidable (BadPair u v s) := by
  unfold BadPair; infer_instance

/-- The exceptional patterns are symmetric in the two targets. -/
lemma badPair_comm {u v s : ℕ} (h : BadPair u v s) : BadPair v u s := by
  unfold BadPair at h ⊢
  tauto

/-- **Guarded pair-representation completeness**: every pair of targets
`u, v` with `u + v ≤ S.sum id` that avoids the four `BadPair` patterns is
realized by two disjoint subsets of `S`. -/
def PairRep (S : Finset ℕ) : Prop :=
  ∀ u v : ℕ, u + v ≤ S.sum id → ¬BadPair u v (S.sum id) →
    ∃ X ⊆ S, ∃ Y ⊆ S, Disjoint X Y ∧ X.sum id = u ∧ Y.sum id = v

/-- The `BadPair` guard is not an artifact: `{0,1,2,3}` has no two disjoint
subsets both summing to `2`, because every subset summing to `2`
contains the element `2`. -/
example : ¬∃ X ∈ ({0, 1, 2, 3} : Finset ℕ).powerset,
    ∃ Y ∈ ({0, 1, 2, 3} : Finset ℕ).powerset,
      Disjoint X Y ∧ X.sum id = 2 ∧ Y.sum id = 2 := by decide

/-- `PairRep` survives the greedy insertion of `m = Σ/2 + 1`.  Strategy:
lift a pair from `S` unchanged when the targets fit below `Σ` and avoid
the `BadPair` patterns at `Σ`; otherwise peel `m` off the larger target
(an overflowing total forces it past `Σ/2`); in the two residual corners
— where peeling the larger target lands on a `BadPair` pattern at `Σ` —
peel `m` off the *smaller* target instead.  The `hsok` hypothesis
excludes the sporadic totals `7, 8, 13, 14` at which the fallback would
collide with the excluded patterns; greedy totals run `6, 10, 16, 25, …`. -/
theorem pairRep_insert {S : Finset ℕ} (hP : PairRep S)
    (hm : S.sum id / 2 + 1 ∉ S)
    (hsok : S.sum id = 6 ∨ S.sum id = 10 ∨ 16 ≤ S.sum id) :
    PairRep (insert (S.sum id / 2 + 1) S) := by
  set m := S.sum id / 2 + 1 with hmdef
  have hsum : (insert m S).sum id = m + S.sum id := Finset.sum_insert hm
  have lift : ∀ {X : Finset ℕ}, X ⊆ S → X ⊆ insert m S :=
    fun hX => hX.trans (Finset.subset_insert m S)
  -- Realize `(u, v)` with `m` absorbed into the `v`-side representation.
  have peel : ∀ u v : ℕ, m ≤ v → u + (v - m) ≤ S.sum id →
      ¬BadPair u (v - m) (S.sum id) →
      ∃ X ⊆ insert m S, ∃ Y ⊆ insert m S,
        Disjoint X Y ∧ X.sum id = u ∧ Y.sum id = v := by
    intro u v hmv htot hgood
    obtain ⟨X, hX, Y₀, hY₀, hd, hu, hv₀⟩ := hP u (v - m) htot hgood
    have hmX : m ∉ X := fun h => hm (hX h)
    have hmY₀ : m ∉ Y₀ := fun h => hm (hY₀ h)
    refine ⟨X, lift hX, insert m Y₀, Finset.insert_subset_insert m hY₀, ?_, hu, ?_⟩
    · rw [Finset.disjoint_insert_right]
      exact ⟨hmX, hd⟩
    · rw [Finset.sum_insert hmY₀, hv₀, id_eq]
      omega
  have core : ∀ u v : ℕ, u ≤ v → u + v ≤ m + S.sum id →
      ¬BadPair u v (m + S.sum id) →
      ∃ X ⊆ insert m S, ∃ Y ⊆ insert m S,
        Disjoint X Y ∧ X.sum id = u ∧ Y.sum id = v := by
    intro u v huv htot hbad
    by_cases hD : u + v ≤ S.sum id ∧ ¬BadPair u v (S.sum id)
    · obtain ⟨X, hX, Y, hY, hd, hu, hv⟩ := hP u v hD.1 hD.2
      exact ⟨X, lift hX, Y, lift hY, hd, hu, hv⟩
    · by_cases hV : m ≤ v ∧ u + (v - m) ≤ S.sum id ∧
          ¬BadPair u (v - m) (S.sum id)
      · exact peel u v hV.1 hV.2.1 hV.2.2
      · -- Residual corners: the smaller side absorbs `m`.
        have hU : m ≤ u ∧ v + (u - m) ≤ S.sum id ∧
            ¬BadPair v (u - m) (S.sum id) := by
          unfold BadPair at hbad hD hV ⊢
          omega
        obtain ⟨X, hX, Y, hY, hd, hv', hu'⟩ := peel v u hU.1 hU.2.1 hU.2.2
        exact ⟨Y, hY, X, hX, hd.symm, hu', hv'⟩
  intro u v htot hbad
  rw [hsum] at htot hbad
  rcases le_total u v with h | h
  · exact core u v h htot hbad
  · have hbad' : ¬BadPair v u (m + S.sum id) := fun hb => hbad (badPair_comm hb)
    obtain ⟨X, hX, Y, hY, hd, hv, hu⟩ := core v u h (by omega) hbad'
    exact ⟨Y, hY, X, hX, hd.symm, hu, hv⟩

/-- **Minimality.**  If `S` has guarded pair-representation completeness,
then every new candidate `m ∉ {0, 1, 2}` with `2·m ≤ Σ` is rejected: two
disjoint subsets of `S` each sum to `m`, and together with `{m}` they
violate the CW property. -/
theorem not_cwProperty_insert_of_pairRep {S : Finset ℕ} {m : ℕ}
    (hP : PairRep S) (hm : m ∉ S) (hm0 : 0 < m) (hm1 : m ≠ 1) (hm2 : m ≠ 2)
    (h2m : 2 * m ≤ S.sum id) :
    ¬CWProperty (insert m S) := by
  have hbad : ¬BadPair m m (S.sum id) := by
    unfold BadPair
    omega
  obtain ⟨X, hX, Y, hY, hd, hXs, hYs⟩ := hP m m (by omega) hbad
  intro hCW
  have hXne : X.Nonempty := by
    rcases X.eq_empty_or_nonempty with rfl | h
    · rw [Finset.sum_empty] at hXs; omega
    · exact h
  have hYne : Y.Nonempty := by
    rcases Y.eq_empty_or_nonempty with rfl | h
    · rw [Finset.sum_empty] at hYs; omega
    · exact h
  have hmX : m ∉ X := fun h => hm (hX h)
  have hmY : m ∉ Y := fun h => hm (hY h)
  refine hCW {m} (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self m S))
    X (hX.trans (Finset.subset_insert m S))
    Y (hY.trans (Finset.subset_insert m S))
    (Finset.singleton_nonempty m) hXne hYne
    (Finset.disjoint_singleton_left.mpr hmX)
    (Finset.disjoint_singleton_left.mpr hmY)
    hd ⟨?_, ?_⟩
  · rw [Finset.sum_singleton, id_eq, hXs]
  · rw [hXs, hYs]

/-! ## The invariant bundle and the master step -/

/-- The full invariant carried along the greedy construction from
`{0, 1, 2, 3}` onward. -/
structure GoodState (S : Finset ℕ) : Prop where
  /-- The prefix has the CW property. -/
  cw : CWProperty S
  /-- Guarded pair-representation completeness — the minimality engine. -/
  pair : PairRep S
  /-- Every element is at most half the total (so the next greedy element
  exceeds all current ones). -/
  small : ∀ x ∈ S, 2 * x ≤ S.sum id
  /-- `0` is present (so candidate `0` is never "new"). -/
  zero_mem : 0 ∈ S
  /-- `1` is present (so candidate `1` is never "new"). -/
  one_mem : 1 ∈ S
  /-- `2` is present (so candidate `2` is never "new"). -/
  two_mem : 2 ∈ S
  /-- The total is `6`, `10`, or at least `16`; this excludes the sporadic
  totals `7, 8, 13, 14` needed by `pairRep_insert`. -/
  sum_ok : S.sum id = 6 ∨ S.sum id = 10 ∨ 16 ≤ S.sum id

/-- The greedy step value `Σ/2 + 1` is new. -/
theorem GoodState.next_not_mem {S : Finset ℕ} (h : GoodState S) :
    S.sum id / 2 + 1 ∉ S := by
  intro hmem
  have := h.small _ hmem
  omega

/-- **The greedy step, identified**: under the invariant, the least valid
new element is exactly `Σ/2 + 1`.  Safety gives membership; pair
representation rejects everything smaller. -/
theorem GoodState.greedyNext_eq {S : Finset ℕ} (h : GoodState S) :
    greedyNext S = S.sum id / 2 + 1 := by
  refine greedyNext_eq_of_min
    ⟨h.next_not_mem, cwProperty_insert_of_sum_lt h.cw (by omega)⟩ ?_
  intro k hk
  by_cases hk0 : k = 0
  · exact Or.inl (hk0 ▸ h.zero_mem)
  · by_cases hkS : k ∈ S
    · exact Or.inl hkS
    · have hk1 : k ≠ 1 := fun h1 => hkS (h1 ▸ h.one_mem)
      have hk2 : k ≠ 2 := fun h2 => hkS (h2 ▸ h.two_mem)
      exact Or.inr (not_cwProperty_insert_of_pairRep h.pair hkS
        (Nat.pos_of_ne_zero hk0) hk1 hk2 (by omega))

/-- The invariant propagates through the greedy step. -/
theorem GoodState.step {S : Finset ℕ} (h : GoodState S) :
    GoodState (insert (S.sum id / 2 + 1) S) := by
  have hnm : S.sum id / 2 + 1 ∉ S := h.next_not_mem
  have hsum : (insert (S.sum id / 2 + 1) S).sum id
      = S.sum id / 2 + 1 + S.sum id := Finset.sum_insert hnm
  have hsok := h.sum_ok
  refine ⟨cwProperty_insert_of_sum_lt h.cw (by omega),
    pairRep_insert h.pair hnm h.sum_ok, ?_,
    Finset.mem_insert_of_mem h.zero_mem,
    Finset.mem_insert_of_mem h.one_mem,
    Finset.mem_insert_of_mem h.two_mem, ?_⟩
  · intro x hx
    rw [hsum]
    rcases Finset.mem_insert.mp hx with rfl | hxS
    · omega
    · have := h.small x hxS
      omega
  · rw [hsum]
    omega

/-! ## Base case and the induction along greedy prefixes -/

set_option synthInstance.maxSize 1024 in
set_option synthInstance.maxHeartbeats 800000 in
/-- Guarded pair-representation completeness for the base prefix
`{0, 1, 2, 3}`, by a bounded decidable search over the powerset.  At total
`6` the `BadPair` patterns instantiate to `(1,1)`, `(2,2)`, `(1, 6-2) =
(1,4)` and `(2, 6-4) = (2,2)` — precisely the unrealizable pairs of this
prefix, so the guarded statement is decidably true.  The
`synthInstance` limits are raised because the decidability-instance term
for the bounded statement exceeds the default size cap. -/
lemma pairRep_base : PairRep ({0, 1, 2, 3} : Finset ℕ) := by
  have hsum : ({0, 1, 2, 3} : Finset ℕ).sum id = 6 := by decide
  intro u v htot hbad
  rw [hsum] at htot hbad
  have hdec : ∀ u' < 7, ∀ v' < 7, u' + v' ≤ 6 → ¬BadPair u' v' 6 →
      ∃ X ∈ ({0, 1, 2, 3} : Finset ℕ).powerset,
        ∃ Y ∈ ({0, 1, 2, 3} : Finset ℕ).powerset,
          Disjoint X Y ∧ X.sum id = u' ∧ Y.sum id = v' := by decide
  obtain ⟨X, hX, Y, hY, hd, hu, hv⟩ := hdec u (by omega) v (by omega) htot hbad
  exact ⟨X, Finset.mem_powerset.mp hX, Y, Finset.mem_powerset.mp hY, hd, hu, hv⟩

/-- The invariant at the base prefix `{0, 1, 2, 3}`. -/
lemma goodState_base : GoodState ({0, 1, 2, 3} : Finset ℕ) :=
  ⟨by decide, pairRep_base, by decide, by decide, by decide, by decide, by decide⟩

/-- Hand step (the master lemma needs `Σ ≥ 6`): after `{0, 1}` the greedy
choice is `2`. -/
lemma greedyNext_pair : greedyNext {0, 1} = 2 :=
  greedyNext_eq_of_min ⟨by decide, by decide⟩ (by decide)

/-- Hand step: after `{0, 1, 2}` the greedy choice is `3`. -/
lemma greedyNext_triple : greedyNext {0, 1, 2} = 3 :=
  greedyNext_eq_of_min ⟨by decide, by decide⟩ (by decide)

/-- The greedy prefix after one adjunction. -/
lemma greedySet_one : greedySet 1 = {0, 1, 2} := by
  rw [greedySet_succ, greedySet_zero, greedyNext_pair]
  decide

/-- The greedy prefix after two adjunctions — the induction base. -/
lemma greedySet_two : greedySet 2 = {0, 1, 2, 3} := by
  rw [greedySet_succ, greedySet_one, greedyNext_triple]
  decide

/-- The invariant holds along every greedy prefix from `{0,1,2,3}` on. -/
theorem goodState_greedySet (n : ℕ) : GoodState (greedySet (n + 2)) := by
  induction n with
  | zero => rw [greedySet_two]; exact goodState_base
  | succ n ih =>
    show GoodState (greedySet ((n + 2) + 1))
    rw [greedySet_succ, ih.greedyNext_eq]
    exact ih.step

/-- The next prefix, pinned: `a(6) = 6` enters after `{0,1,2,3,4}`. -/
lemma greedySet_three : greedySet 3 = {0, 1, 2, 3, 4} := by
  rw [greedySet_succ, (goodState_greedySet 0).greedyNext_eq, greedySet_two]; decide

/-- Joint satisfiability of `cwProperty_insert_of_sum_lt`'s hypotheses. -/
example : CWProperty (insert 2 ({0, 1} : Finset ℕ)) :=
  cwProperty_insert_of_sum_lt (by decide) (by decide)

/-- Joint satisfiability of `pairRep_insert`'s hypotheses. -/
example : PairRep (insert (({0, 1, 2, 3} : Finset ℕ).sum id / 2 + 1)
    ({0, 1, 2, 3} : Finset ℕ)) :=
  pairRep_insert pairRep_base (by decide) (by decide)

/-- Joint satisfiability of `not_cwProperty_insert_of_pairRep`'s six
hypotheses, at the first non-degenerate model: rejecting `5` from
`{0, 1, 2, 3, 4}`. -/
example : ¬CWProperty (insert 5 (greedySet 3)) :=
  not_cwProperty_insert_of_pairRep (goodState_greedySet 1).pair
    (by rw [greedySet_three]; decide) (by omega) (by omega) (by omega)
    (by rw [greedySet_three]; decide)

/-! ## Target 1: Greathouse's recurrence, proved -/

/-- **Greathouse's recurrence (A172161 `%F` line, Dec 02 2022), proved for
the greedy definition**: for `n > 4`,
`a(n) = ⌊(Σ_{i<n} a(i))/2⌋ + 1`.  The `%F` line carries no proof or
reference in the OEIS entry; for this derivation from the greedy definition
we found no record of a prior proof (corpora searched 2026-08-20: the
A172161 entry and links, A120134, the local References corpus).  This is a
found-no-record statement, not a priority or publication claim. -/
theorem greedyA_recurrence (n : ℕ) (hn : 4 < n) :
    greedyA n = (∑ i ∈ Finset.range n, greedyA i) / 2 + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  have h1 : greedyA (k + 5) = greedyNext (greedySet (k + 2)) := rfl
  rw [h1, (goodState_greedySet k).greedyNext_eq, sum_greedySet (k + 2),
    (by omega : k + 2 + 3 = k + 5)]
  rfl

/-- The recurrence, phrased through the partial-sum abbreviation. -/
lemma greedyA_eq_sumA (n : ℕ) (hn : 4 < n) : greedyA n = sumA n / 2 + 1 :=
  greedyA_recurrence n hn

/-- The partial sums satisfy `A(n+1) = A(n) + ⌊A(n)/2⌋ + 1` for `n ≥ 5`. -/
lemma sumA_succ_of_ge (n : ℕ) (hn : 5 ≤ n) :
    sumA (n + 1) = sumA n + sumA n / 2 + 1 := by
  rw [sumA_succ_eq, greedyA_eq_sumA n (by omega)]
  omega

/-! ## Ground truth against the OEIS DATA line -/

/-- OEIS DATA: `a(3) = 2`. -/
lemma greedyA_three : greedyA 3 = 2 := by
  rw [show greedyA 3 = greedyNext (greedySet 0) from rfl, greedySet_zero,
    greedyNext_pair]

/-- OEIS DATA: `a(4) = 3`. -/
lemma greedyA_four : greedyA 4 = 3 := by
  rw [show greedyA 4 = greedyNext (greedySet 1) from rfl, greedySet_one,
    greedyNext_triple]

/-- `S(5) = 0 + 0 + 1 + 2 + 3 = 6`. -/
lemma sumA_five : sumA 5 = 6 := by
  simp [sumA, Finset.sum_range_succ, greedyA_three, greedyA_four]

/-- OEIS DATA: `a(5) = 4`, the first value produced by the recurrence. -/
lemma greedyA_five : greedyA 5 = 4 := by
  rw [greedyA_eq_sumA 5 (by omega), sumA_five]

/-- `S(6) = 10`. -/
lemma sumA_six : sumA 6 = 10 := by
  rw [sumA_succ_eq, sumA_five, greedyA_five]

/-- OEIS DATA: `a(6) = 6` — the greedy step skips `5`. -/
lemma greedyA_six : greedyA 6 = 6 := by
  rw [greedyA_eq_sumA 6 (by omega), sumA_six]

/-- `S(7) = 16`. -/
lemma sumA_seven : sumA 7 = 16 := by
  rw [sumA_succ_eq, sumA_six, greedyA_six]

/-- DATA cross-check: the greedy definition reproduces the OEIS prefix
`0, 1, 2, 3, 4, 6, 9` (offset 1), including the skip of `5`. -/
lemma greedyA_seven : greedyA 7 = 9 := by
  rw [greedyA_eq_sumA 7 (by omega), sumA_seven]

/-- The explicit reason `5` is skipped: `{5}, {1,4}, {2,3}` all sum to 5. -/
example : ¬CWProperty {0, 1, 2, 3, 4, 5} := by
  intro h
  exact h {5} (by decide) {1, 4} (by decide) {2, 3} (by decide)
    ⟨5, by decide⟩ ⟨1, by decide⟩ ⟨2, by decide⟩
    (by decide) (by decide) (by decide) (by decide)

/-- The prefix-local half of Greathouse's completeness comment: every
target up to the *prefix total* is a subset sum of that prefix.  The full
comment ("every positive integer is the sum of a subset of its terms")
additionally needs the prefix totals to be unbounded, which is not proved
in this file. -/
theorem exists_subset_sum_eq (n : ℕ) {t : ℕ}
    (ht : t ≤ (greedySet (n + 2)).sum id) :
    ∃ X ⊆ greedySet (n + 2), X.sum id = t := by
  have hsok := (goodState_greedySet n).sum_ok
  have hbad : ¬BadPair t 0 ((greedySet (n + 2)).sum id) := by
    unfold BadPair
    omega
  obtain ⟨X, hX, Y, hY, hd, hu, hv⟩ :=
    (goodState_greedySet n).pair t 0 (by omega) hbad
  exact ⟨X, hX, hu⟩

/-! ## Target 2: McEachen's growth conjecture, proved

From the recurrence, `3·A n < 2·A (n+1) ≤ 3·A n + 2` for `n ≥ 5`, so
`ratio n = (A n + 2)·(2/3)^n` is antitone with geometrically summable
decrements; its limit `L` is at least `224/243`, and
`a(n)/(3/2)^n → L/2`. -/

/-- The normalized partial sums, `(A n + 2)·(2/3)^n`. -/
noncomputable def ratio (n : ℕ) : ℝ := ((sumA n : ℝ) + 2) * (2 / 3) ^ n

/-- Ground truth pinning `ratio`'s offset and base: `(6 + 2)·(2/3)^5`. -/
example : ratio 5 = 256 / 243 := by unfold ratio; rw [sumA_five]; norm_num

/-- The two-sided growth bound `3·A(n) < 2·A(n+1) ≤ 3·A(n) + 2` for `n ≥ 5`. -/
lemma sumA_bounds (n : ℕ) (hn : 5 ≤ n) :
    3 * sumA n < 2 * sumA (n + 1) ∧ 2 * sumA (n + 1) ≤ 3 * sumA n + 2 := by
  have h := sumA_succ_of_ge n hn
  omega

/-- The normalized partial sums are nonincreasing from index `5`. -/
lemma ratio_succ_le (n : ℕ) (hn : 5 ≤ n) : ratio (n + 1) ≤ ratio n := by
  obtain ⟨-, hub⟩ := sumA_bounds n hn
  have hub' : (2 : ℝ) * sumA (n + 1) ≤ 3 * sumA n + 2 := by exact_mod_cast hub
  have hpow : (0 : ℝ) ≤ (2 / 3) ^ n := by positivity
  unfold ratio
  rw [pow_succ]
  nlinarith [hpow]

/-- Each normalization step loses at most `(1/2)·(2/3)^(n+1)`. -/
lemma ratio_succ_ge (n : ℕ) (hn : 5 ≤ n) :
    ratio n - (2 / 3) ^ (n + 1) / 2 ≤ ratio (n + 1) := by
  obtain ⟨hlb, -⟩ := sumA_bounds n hn
  have hlb' : (3 : ℝ) * sumA n + 1 ≤ 2 * sumA (n + 1) := by exact_mod_cast hlb
  have hpow : (0 : ℝ) ≤ (2 / 3) ^ n := by positivity
  unfold ratio
  rw [pow_succ]
  nlinarith [hpow]

/-- The tail of `ratio`, shifted to start at index 5 where the recurrence
holds. -/
noncomputable def ratioTail (k : ℕ) : ℝ := ratio (k + 5)

/-- Ground truth pinning `ratioTail`'s shift: index 0 is `ratio 5`. -/
example : ratioTail 0 = 256 / 243 := by
  unfold ratioTail ratio; rw [sumA_five]; norm_num

/-- The shifted normalized sums are antitone. -/
lemma ratioTail_antitone : Antitone ratioTail :=
  antitone_nat_of_succ_le fun k => ratio_succ_le (k + 5) (by omega)

/-- Quantitative lower bound with the geometric-tail correction: each step
loses at most `(1/2)·(2/3)^(n+1)`, so the total decrement beyond index
`k + 5` is at most `(1/2)·3·(2/3)^(k+6) = (3/2)·(2/3)^(k+6)`, and the base
value is `ratio 5 = 256/243`. -/
lemma ratioTail_lower (k : ℕ) :
    224 / 243 + 3 / 2 * (2 / 3 : ℝ) ^ (k + 6) ≤ ratioTail k := by
  induction k with
  | zero =>
    show (224 : ℝ) / 243 + 3 / 2 * (2 / 3 : ℝ) ^ 6 ≤ ratio 5
    unfold ratio
    rw [sumA_five]
    norm_num
  | succ k ih =>
    have hstep := ratio_succ_ge (k + 5) (by omega)
    have hpow : ((2 / 3 : ℝ)) ^ (k + 1 + 6) = (2 / 3) ^ (k + 6) * (2 / 3) := by
      rw [show k + 1 + 6 = (k + 6) + 1 from by omega, pow_succ]
    have hshift : ((2 / 3 : ℝ)) ^ (k + 5 + 1) = (2 / 3) ^ (k + 6) := by
      norm_num
    show 224 / 243 + 3 / 2 * (2 / 3 : ℝ) ^ (k + 1 + 6) ≤ ratio (k + 1 + 5)
    have hidx : k + 1 + 5 = k + 5 + 1 := by omega
    rw [hidx, hpow]
    have htail : ratioTail k = ratio (k + 5) := rfl
    rw [htail] at ih
    rw [hshift] at hstep
    linarith

/-- The shifted normalized sums are bounded below by `224/243`. -/
lemma ratioTail_bddBelow : BddBelow (Set.range ratioTail) := by
  refine ⟨224 / 243, ?_⟩
  rintro x ⟨k, rfl⟩
  have h := ratioTail_lower k
  have hpow : (0 : ℝ) ≤ 3 / 2 * (2 / 3) ^ (k + 6) := by positivity
  linarith

/-- The limit of the normalized partial sums.  By `greedyLimit_lower_bound`
it is positive; numerically it is `≈ 1.0356`. -/
noncomputable def greedyLimit : ℝ := ⨅ k, ratioTail k

/-- Monotone convergence: the shifted normalized sums tend to their
infimum. -/
theorem tendsto_ratioTail : Tendsto ratioTail atTop (nhds greedyLimit) :=
  tendsto_atTop_ciInf ratioTail_antitone ratioTail_bddBelow

/-- The limit is at least `224/243`, in particular positive. -/
theorem greedyLimit_lower_bound : 224 / 243 ≤ greedyLimit := by
  refine le_ciInf fun k => ?_
  have h := ratioTail_lower k
  have hpow : (0 : ℝ) ≤ 3 / 2 * (2 / 3) ^ (k + 6) := by positivity
  linarith

/-- The unshifted normalized partial sums converge to `greedyLimit`. -/
theorem tendsto_ratio : Tendsto ratio atTop (nhds greedyLimit) :=
  (Filter.tendsto_add_atTop_iff_nat 5).mp tendsto_ratioTail

/-- Division by `(3/2)^n` is multiplication by `(2/3)^n`. -/
lemma div_three_half_pow (x : ℝ) (n : ℕ) :
    x / (3 / 2 : ℝ) ^ n = x * (2 / 3 : ℝ) ^ n := by
  rw [div_eq_mul_inv, ← inv_pow]
  norm_num

/-- **McEachen's growth conjecture (A172161 `%F` line, Dec 02 2022), proved,
with the constant identified**: `a(n)/(3/2)^n → greedyLimit/2`.  The greedy
terms satisfy `A n + 1 ≤ 2·a(n) ≤ A n + 2` for `n ≥ 5`, so the normalized
terms are squeezed between `(ratio n - (2/3)^n)/2` and `ratio n / 2`. -/
theorem tendsto_greedyA_div_pow :
    Tendsto (fun n : ℕ => (greedyA n : ℝ) / (3 / 2 : ℝ) ^ n) atTop
      (nhds (greedyLimit / 2)) := by
  have hpow23 : Tendsto (fun n : ℕ => ((2 : ℝ) / 3) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hlo : Tendsto (fun n : ℕ => (ratio n - (2 / 3 : ℝ) ^ n) / 2) atTop
      (nhds (greedyLimit / 2)) := by
    have := (tendsto_ratio.sub hpow23).div_const 2
    simpa using this
  have hhi : Tendsto (fun n : ℕ => ratio n / 2) atTop (nhds (greedyLimit / 2)) :=
    tendsto_ratio.div_const 2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [Filter.eventually_atTop.mpr ⟨5, fun n hn => hn⟩] with n hn
    have ha : greedyA n = sumA n / 2 + 1 := greedyA_eq_sumA n (by omega)
    have hbounds : sumA n + 1 ≤ 2 * greedyA n ∧ 2 * greedyA n ≤ sumA n + 2 := by
      omega
    have hlb : (sumA n : ℝ) + 1 ≤ 2 * (greedyA n : ℝ) := by
      exact_mod_cast hbounds.1
    have hpow : (0 : ℝ) ≤ (2 / 3) ^ n := by positivity
    rw [div_three_half_pow]
    unfold ratio
    nlinarith [hpow]
  · filter_upwards [Filter.eventually_atTop.mpr ⟨5, fun n hn => hn⟩] with n hn
    have ha : greedyA n = sumA n / 2 + 1 := greedyA_eq_sumA n (by omega)
    have hbounds : sumA n + 1 ≤ 2 * greedyA n ∧ 2 * greedyA n ≤ sumA n + 2 := by
      omega
    have hub : 2 * (greedyA n : ℝ) ≤ (sumA n : ℝ) + 2 := by
      exact_mod_cast hbounds.2
    have hpow : (0 : ℝ) ≤ (2 / 3) ^ n := by positivity
    rw [div_three_half_pow]
    unfold ratio
    nlinarith [hpow]

/-- The limit constant of `a(n)/(3/2)^n` is positive. -/
theorem greedyA_growth_constant_pos : 0 < greedyLimit / 2 := by
  have h := greedyLimit_lower_bound
  linarith

/-- **McEachen's conjecture in the OEIS existential form**: there is a
positive `k` with `a(n)/(3/2)^n → k`.  This is the statement
`mcEachen_growth` of the sibling candidate card, proved for the greedy
definition. -/
theorem mcEachen_growth :
    ∃ k : ℝ, 0 < k ∧
      Tendsto (fun n : ℕ => (greedyA n : ℝ) / (3 / 2 : ℝ) ^ n) atTop (nhds k) :=
  ⟨greedyLimit / 2, greedyA_growth_constant_pos, tendsto_greedyA_div_pow⟩

end GreedyCW
