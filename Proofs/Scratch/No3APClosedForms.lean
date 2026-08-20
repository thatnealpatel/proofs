import Enumerative.No3APGreedy

/-!
# OEIS A093682 rows 3–6: closed forms for greedy 3-AP-free sequences

**OEIS A093682**, "Array T(m,n) by antidiagonals: nonarithmetic-3-progression sequences
with simple closed forms."  Pinned verbatim from `oeis show A093682` (2026-08-19):

> The nonarithmetic-3-progression sequences starting with a(1)=1, a(2)=1+3^m or 1+2*3^m,
> m >= 0, seem to have especially simple 'closed' forms. None of these formulas have
> been proved, however.
>
> T(m,1)=1, T(m,2) = 1 + (1 + [m odd])*3^floor(m/2) = 1 + A038754(m), m >= 0, n > 0;
> T(m,n) is the least k such that no three terms of T(m,1), T(m,2), ..., T(m,n-1), k
> form an arithmetic progression.
>
> T(m, n) = (Sum_{k=1..n-1} (3^A007814(k) + 1)/2) + f(n), with f(n) a P-periodic
> function, where P <= 2^floor((m+3)/2) (conjectured and checked up to m=13, n=1000).

Per the `xrefs` field, rows 0–6 are A003278, A004793, A033157, A093678, A093679,
A093680, A093681.  Row 0 is settled in this repository
(`Proofs/Enumerative/StanleyDigits.lean`, A003278 — the classical
Szekeres/Stanley sequence).  Rows 1–2 (A004793, A033157) are NOT formalized
here; the OEIS credits them "proved by Lawrence Sze" (2004, via Ralf Stephan),
with no published write-up located.  **This file proves the closed forms of
rows 3–6** — A093678, A093679, A093680 carry the same OEIS "as proved by
Lawrence Sze" credit (again with no located write-up); only A093681 (row 6) is
marked "conjectured" in its entry — each pinned verbatim from its own entry
(2026-08-19):

* **A093678** (row 3, seed `1, 7`): "a(n) = (Sum_{k=1..n-1} (3^A007814(k) + 1)/2) + f(n),
  with f(n) an 8-periodic function with values {1, 6, 5, 6, 2, 6, 5, 7, ...}, as proved
  by Lawrence Sze."
* **A093679** (row 4, seed `1, 10`): same shape, 8-periodic values
  {1, 9, 8, 9, 5, 10, 10, 10, ...}, "as proved by Lawrence Sze."
* **A093680** (row 5, seed `1, 19`): same shape, 16-periodic values
  {1, 18, 17, 18, 14, 18, 17, 19, 5, 18, 17, 18, 14, 19, 19, 19, ...}, "as proved by
  Lawrence Sze."  **The printed list has a typo**: its 8th value must be `18`, not `19`
  — the entry's own `terms` field has `a(8) = 31 = 13 + 18` (with `Sum_{k=1..7} = 13`),
  and `f(8) = 19` would force the impossible `a(8) = 32 = a(9)`.  We prove the corrected
  list `{1, 18, 17, 18, 14, 18, 17, 18, 5, 18, 17, 18, 14, 19, 19, 19}`.
* **A093681** (row 6, seed `1, 28`): same shape, 16-periodic values
  {1, 27, 26, 27, 23, 27, 26, 27, 14, 28, 28, 28, 28, 28, 28, 28, ...},
  "(conjectured and checked up to n=1000)" — **no proof is claimed anywhere in the
  entry**; this row is the headline.

## Novelty assessment (researched 2026-08-19)

Subtracting 1 from every term, these rows are the classical Stanley sequences
S(0, 2·3) (row 3), S(0, 3²) (row 4), S(0, 2·3²) (row 5), S(0, 3³) (row 6).  The
ternary-digit *membership characterization* of S(0, 3^k) and S(0, 2·3^k) is stated as
Theorems 1–2 of Odlyzko–Stanley (*Some curious sequences constructed with the greedy
algorithm*, Bell Labs memorandum, 1978; proof described there as "routine though
tedious" and not written out; NB the memo's printed Theorem 2 lacks a clause
and is defective as printed — Rolnick's closed form (2) supplies it) and is
proved in published form by D. Rolnick, *On the classification of Stanley
sequences*, European J. Combin. 59 (2017) 51–70, Theorem 1.2 in the arXiv
numbering of 1408.1940 (monotone families; our block decomposition below is
the shape of Moy–Rolnick, *Novel structures in Stanley sequences*, Discrete
Math. 339 (2016), Theorem 2.4 in the arXiv numbering of 1502.06013: a modular
Stanley sequence mod N is a finite block plus N times the 0/1-ternary set).
The OEIS-specific sum-plus-periodic formulas were conjectured by Ralf Stephan
(2004); the OEIS credits Lawrence Sze with proofs for rows 1–5 (Stephan's
conjecture tracker dates them 2004-11-12); unlike other Sze entries in that
tracker no write-up is linked for these, and we located none.  For row 6 the
OEIS entry itself still says "conjectured".

So: **no new mathematics is claimed** — this is (as far as we can determine) the first
*formalization*, and for A093681 the first *written-out* proof of the exact OEIS
formula, resolving the entry's "conjectured" status; both are found-no-record rather
than priority claims.  The structure theorem it rests on is known.  The A093682 master
comment "None of these formulas have been proved" is outdated (Rolnick 2017), and the
A093680 formula list has the typo documented above.  The `19 → 18` correction is already
forced by the entry's eighth listed term; Lean proves the corrected periodic formula for
all indices but is not needed to detect that one-line inconsistency.  Repository issue
#37 is a correction report, not evidence that OEIS has accepted or applied the change.

## Contents and conventions

Everything is 0-indexed: `seedGreedy a b n = T(m, n+1)` for the row seeded `(a, b)`.
The greedy convention is pinned exactly as in `Proofs/Enumerative/StanleyDigits.lean`
(A003278) and `Proofs/Enumerative/No3APGreedy.lean` (A092482), both of which reproduce
their OEIS `terms` fields verbatim: each next term is the least `k` exceeding all
previous terms such that no three terms of prefix-plus-`k` form an arithmetic
progression (`IsGoodExt`/`nextTerm` are reused from `StanleyDigits.lean`).

The engine, generic over a modulus `M` and a sorted block list `bs` (all entries
`< M`):

* `BlockMem M bs x` — `x` lies in the block set `{M·s + b : s ∈ A005836-set, b ∈ bs}`;
* `threeAPFree_blockMem` — the block set is 3-AP-free, given finite (decidable)
  conditions on `bs`;
* `blockMem_blocking` — every `x` above the second seed and outside the block set
  completes an AP `p + x = 2q` with two smaller members: within the low block via a
  finite table of pairs, across blocks via the `keepOnes`/`capDigits` averaging
  witnesses of `StanleyDigits.lean`;
* `blockEnum M bs` — the increasing enumeration `n ↦ M · binToTernary (n / |bs|) +
  bs[n % |bs|]`;
* `seedGreedy_eq_of_blockLike` — the greedy bridge: the greedy sequence seeded with the
  two least elements equals any strictly monotone enumeration of a 3-AP-free,
  blocking-complete set;
* `binToTernary_pow_mul_add` — the digit-splitting identity
  `binToTernary (2^t·q + r) = 3^t·binToTernary q + binToTernary r` for `r < 2^t`,
  which converts the block form into the OEIS `binToTernary n + (periodic)` form; the
  `v₂`-sum shape then comes from `A092482.two_mul_binToTernary_eq_sum`
  (`Proofs/Enumerative/No3APGreedy.lean`).

Main theorems (all sorry-free, axioms ⊆ {propext, Classical.choice, Quot.sound}):
`a93678_closedForm`, `a93679_closedForm`, `a93680_closedForm`, `a93681_closedForm`,
each stated division-free by doubling, e.g. for row 6:

  `2 * a93681 n = (∑ k ∈ Finset.Icc 1 n, (3 ^ padicValNat 2 k + 1))
      + 2 * fs93681.getD (n % 16) 0`.
-/

set_option autoImplicit false

namespace A093682

/-! ## Arithmetic helpers for block decompositions

`ℕ`-linear facts about `M*u + β` decompositions.  `omega` cannot see through the
variable-times-variable products, so each helper isolates one `ring`-shaped step. -/

/-- Block comparison: a smaller block index wins regardless of the offsets, as long as
the low offset is a genuine offset (`β < M`). -/
theorem block_lt {M u v β γ : ℕ} (hβ : β < M) (huv : u < v) :
    M * u + β < M * v + γ :=
  calc M * u + β < M * u + M := Nat.add_lt_add_left hβ _
    _ = M * (u + 1) := by ring
    _ ≤ M * v := Nat.mul_le_mul_left M huv
    _ ≤ M * v + γ := Nat.le_add_right _ _

/-- Averaging two block elements, no carry: if the block indices average and the
offsets average, the elements average. -/
theorem pair_avg_zero {M u v s β γ c : ℕ} (h1 : u + s = 2 * v) (h2 : β + c = 2 * γ) :
    (M * u + β) + (M * s + c) = 2 * (M * v + γ) :=
  calc (M * u + β) + (M * s + c) = M * (u + s) + (β + c) := by ring
    _ = M * (2 * v) + 2 * γ := by rw [h1, h2]
    _ = 2 * (M * v + γ) := by ring

/-- Averaging two block elements with one carry: the block indices average up to `+1`
and the offsets average after borrowing one modulus. -/
theorem pair_avg_carry {M u v s β γ c : ℕ} (h1 : u + s = 2 * v + 1)
    (h2 : β + c + M = 2 * γ) :
    (M * u + β) + (M * s + c) = 2 * (M * v + γ) :=
  calc (M * u + β) + (M * s + c) = M * (u + s) + (β + c) := by ring
    _ = M * (2 * v + 1) + (β + c) := by rw [h1]
    _ = M * (2 * v) + (β + c + M) := by ring
    _ = M * (2 * v) + 2 * γ := by rw [h2]
    _ = 2 * (M * v + γ) := by ring

/-- Comparing two base-`M` decompositions whose "digits" are allowed to reach `2M`:
the quotients agree, or differ by exactly one carried modulus. -/
theorem carry_split {M A B C D : ℕ} (hC : C < 2 * M) (hD : D < 2 * M)
    (h : M * A + C = M * B + D) :
    (A = B ∧ C = D) ∨ (B = A + 1 ∧ C = D + M) ∨ (A = B + 1 ∧ D = C + M) := by
  rcases lt_trichotomy A B with hab | rfl | hab
  · -- A < B: the gap is exactly one, else the offsets overflow
    have hb2 : B ≤ A + 1 := by
      by_contra hb2
      have h2 : M * (A + 2) ≤ M * B := Nat.mul_le_mul_left M (by omega)
      have h3 : M * (A + 2) = M * A + 2 * M := by ring
      omega
    have hB : B = A + 1 := le_antisymm hb2 hab
    subst hB
    have h4 : M * (A + 1) = M * A + M := by ring
    exact Or.inr (Or.inl ⟨rfl, by omega⟩)
  · exact Or.inl ⟨rfl, by omega⟩
  · -- B < A: symmetric
    have ha2 : A ≤ B + 1 := by
      by_contra ha2
      have h2 : M * (B + 2) ≤ M * A := Nat.mul_le_mul_left M (by omega)
      have h3 : M * (B + 2) = M * B + 2 * M := by ring
      omega
    have hA : A = B + 1 := le_antisymm ha2 hab
    subst hA
    have h4 : M * (B + 1) = M * B + M := by ring
    exact Or.inr (Or.inr ⟨rfl, by omega⟩)

/-- Outside the 0/1-ternary set the two averaging witnesses are strictly ordered:
`keepOnes s < capDigits s`. -/
theorem keepOnes_lt_capDigits {s : ℕ} (hs : s ∉ Set.range binToTernary) :
    keepOnes s < capDigits s := by
  have havg : keepOnes s + s = 2 * capDigits s := keepOnes_add_self s
  have hlt : capDigits s < s := capDigits_lt_of_not_mem_range hs
  omega

/-! ## Block sets

The candidate term set of one row: low offset in the finite block `bs`, high part an
arbitrary 0/1-ternary number scaled by the modulus `M`. -/

/-- `x` belongs to the block set determined by modulus `M` and block list `bs`:
its residue mod `M` is a block offset and its quotient is a value of `binToTernary`
(equivalently, all base-3 digits of `x / M` are `0` or `1`, `mem_range_binToTernary`). -/
def BlockMem (M : ℕ) (bs : List ℕ) (x : ℕ) : Prop :=
  x % M ∈ bs ∧ x / M ∈ Set.range binToTernary

/-- Unfolding lemma for `BlockMem`. -/
theorem blockMem_def {M : ℕ} {bs : List ℕ} {x : ℕ} :
    BlockMem M bs x ↔ x % M ∈ bs ∧ x / M ∈ Set.range binToTernary :=
  Iff.rfl

/-- Constructor: an explicit decomposition `M * u + β` with `u` a 0/1-ternary value
and `β` a block offset lies in the block set. -/
theorem blockMem_mk {M : ℕ} {bs : List ℕ} {u β : ℕ} (hM : 0 < M)
    (hu : u ∈ Set.range binToTernary) (hβ : β ∈ bs) (hβM : β < M) :
    BlockMem M bs (M * u + β) := by
  refine ⟨?_, ?_⟩
  · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hβM]
    exact hβ
  · rw [Nat.mul_add_div hM, Nat.div_eq_of_lt hβM, Nat.add_zero]
    exact hu

/-- **3-AP-freeness of a block set.**  The finite hypothesis `hap` packages, for each
triple of offsets, the no-carry case (`b₁ + b₃ = 2b₂` forces `b₁ = b₂`) and the
impossibility of both carry cases; the high parts are handled by
`binToTernary_add_eq_two_mul` (no three distinct 0/1-ternary values average). -/
theorem threeAPFree_blockMem (M : ℕ) (bs : List ℕ) (hM : 0 < M)
    (hap : ∀ b₁ ∈ bs, ∀ b₂ ∈ bs, ∀ b₃ ∈ bs,
      (b₁ + b₃ = 2 * b₂ → b₁ = b₂) ∧ b₁ + b₃ + M ≠ 2 * b₂ ∧ b₁ + b₃ ≠ 2 * b₂ + M) :
    ThreeAPFree {x : ℕ | BlockMem M bs x} := by
  rintro x ⟨hxc, σx, hσx⟩ y ⟨hyc, σy, hσy⟩ z ⟨hzc, σz, hσz⟩ hxz
  have hx : M * (x / M) + x % M = x := Nat.div_add_mod x M
  have hy : M * (y / M) + y % M = y := Nat.div_add_mod y M
  have hz : M * (z / M) + z % M = z := Nat.div_add_mod z M
  have hcx : x % M < M := Nat.mod_lt _ hM
  have hcy : y % M < M := Nat.mod_lt _ hM
  have hcz : z % M < M := Nat.mod_lt _ hM
  have hkey : M * (x / M + z / M) + (x % M + z % M)
      = M * (2 * (y / M)) + (y % M + y % M) :=
    calc M * (x / M + z / M) + (x % M + z % M)
        = (M * (x / M) + x % M) + (M * (z / M) + z % M) := by ring
      _ = x + z := by rw [hx, hz]
      _ = y + y := hxz
      _ = (M * (y / M) + y % M) + (M * (y / M) + y % M) := by rw [hy]
      _ = M * (2 * (y / M)) + (y % M + y % M) := by ring
  have hap' := hap _ hxc _ hyc _ hzc
  rcases carry_split (by omega) (by omega) hkey with
    ⟨hA, hC⟩ | ⟨-, hC⟩ | ⟨-, hC⟩
  · -- no carry: offsets average and high parts average
    have hbc : x % M = y % M := hap'.1 (by omega)
    have hst : binToTernary σx + binToTernary σz = 2 * binToTernary σy := by
      rw [hσx, hσy, hσz]; omega
    obtain ⟨hσ1, -⟩ := binToTernary_add_eq_two_mul hst
    have hsx : x / M = y / M := by rw [← hσx, ← hσy, hσ1]
    rw [← hx, ← hy, hsx, hbc]
  · -- carry down: x%M + z%M = 2*(y%M) + M, excluded by the finite table
    exact absurd (by omega : x % M + z % M = 2 * (y % M) + M) hap'.2.2
  · -- carry up: x%M + z%M + M = 2*(y%M), excluded by the finite table
    exact absurd (by omega : x % M + z % M + M = 2 * (y % M)) hap'.2.1

/-- **Blocking completeness of a block set.**  Every `x` exceeding the second block
offset and outside the set completes an AP `p + x = 2q` with two strictly smaller
members.  Low-offset obstructions use the finite pair tables `hhi`/`hlo`; a base-3
digit `2` in the high part uses the `keepOnes`/`capDigits` averaging witnesses; the
genuinely cross-block cases (`c ≤ bs[1]`, high part 0/1-ternary) borrow one modulus
from the predecessor block via `hlo`'s carry pairs. -/
theorem blockMem_blocking (M : ℕ) (bs : List ℕ) (hM : 0 < M)
    (hlt : ∀ b ∈ bs, b < M) (_hlen : 1 < bs.length)
    (hhi : ∀ c < M, c ∉ bs → bs.getD 1 0 < c →
      ∃ p ∈ bs, ∃ q ∈ bs, p < q ∧ p + c = 2 * q)
    (hlo : ∀ c < M, c ∉ bs → c ≤ bs.getD 1 0 →
      (∃ p ∈ bs, ∃ q ∈ bs, q < p ∧ p + c = 2 * q) ∧
        (∃ p ∈ bs, ∃ q ∈ bs, p < q ∧ p + c + M = 2 * q))
    {x : ℕ} (hx : ¬BlockMem M bs x) (hxg : bs.getD 1 0 < x) :
    ∃ p q, BlockMem M bs p ∧ BlockMem M bs q ∧ p < q ∧ q < x ∧ p + x = 2 * q := by
  obtain ⟨s, c, hcM, rfl⟩ : ∃ s c, c < M ∧ M * s + c = x :=
    ⟨x / M, x % M, Nat.mod_lt _ hM, Nat.div_add_mod x M⟩
  have hmod : (M * s + c) % M = c := by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hcM]
  have hdiv : (M * s + c) / M = s := by
    rw [Nat.mul_add_div hM, Nat.div_eq_of_lt hcM, Nat.add_zero]
  rw [blockMem_def, hmod, hdiv] at hx
  by_cases hc : c ∈ bs
  · -- offset fine, so the high part has a digit 2: same-offset averaging witnesses
    have hs : s ∉ Set.range binToTernary := fun hmem => hx ⟨hc, hmem⟩
    have hko : keepOnes s < capDigits s := keepOnes_lt_capDigits hs
    have hcap : capDigits s < s := capDigits_lt_of_not_mem_range hs
    refine ⟨M * keepOnes s + c, M * capDigits s + c,
      blockMem_mk hM (keepOnes_mem_range s) hc (hlt _ hc),
      blockMem_mk hM (capDigits_mem_range s) hc (hlt _ hc),
      block_lt (hlt _ hc) hko, block_lt (hlt _ hc) hcap,
      pair_avg_zero (keepOnes_add_self s) (by ring)⟩
  · by_cases hcg : bs.getD 1 0 < c
    · -- in-block ascending pair from the finite table
      obtain ⟨β₁, hβ₁, β₂, hβ₂, hβlt, hβeq⟩ := hhi c hcM hc hcg
      by_cases hsr : s ∈ Set.range binToTernary
      · exact ⟨M * s + β₁, M * s + β₂,
          blockMem_mk hM hsr hβ₁ (hlt _ hβ₁), blockMem_mk hM hsr hβ₂ (hlt _ hβ₂),
          Nat.add_lt_add_left hβlt _, Nat.add_lt_add_left (by omega) _,
          pair_avg_zero (two_mul s).symm hβeq⟩
      · have hko : keepOnes s < capDigits s := keepOnes_lt_capDigits hsr
        have hcap : capDigits s < s := capDigits_lt_of_not_mem_range hsr
        exact ⟨M * keepOnes s + β₁, M * capDigits s + β₂,
          blockMem_mk hM (keepOnes_mem_range s) hβ₁ (hlt _ hβ₁),
          blockMem_mk hM (capDigits_mem_range s) hβ₂ (hlt _ hβ₂),
          block_lt (hlt _ hβ₁) hko, block_lt (hlt _ hβ₂) hcap,
          pair_avg_zero (keepOnes_add_self s) hβeq⟩
    · -- small offset: cross-block pairs
      have hcle : c ≤ bs.getD 1 0 := by omega
      obtain ⟨⟨δ₁, hδ₁, δ₂, hδ₂, hδlt, hδeq⟩, γ₁, hγ₁, γ₂, hγ₂, hγlt, hγeq⟩ :=
        hlo c hcM hc hcle
      have hs0 : s ≠ 0 := by
        rintro rfl
        rw [Nat.mul_zero, Nat.zero_add] at hxg
        omega
      by_cases hsr : s ∈ Set.range binToTernary
      · -- high part clean: borrow a modulus from block s − 1
        obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
        by_cases hs'r : s' ∈ Set.range binToTernary
        · exact ⟨M * s' + γ₁, M * s' + γ₂,
            blockMem_mk hM hs'r hγ₁ (hlt _ hγ₁), blockMem_mk hM hs'r hγ₂ (hlt _ hγ₂),
            Nat.add_lt_add_left hγlt _, block_lt (hlt _ hγ₂) (Nat.lt_succ_self s'),
            pair_avg_carry (by ring) hγeq⟩
        · have hko : keepOnes s' < capDigits s' := keepOnes_lt_capDigits hs'r
          have hcap : capDigits s' < s' := capDigits_lt_of_not_mem_range hs'r
          have havg : keepOnes s' + s' = 2 * capDigits s' := keepOnes_add_self s'
          exact ⟨M * keepOnes s' + γ₁, M * capDigits s' + γ₂,
            blockMem_mk hM (keepOnes_mem_range s') hγ₁ (hlt _ hγ₁),
            blockMem_mk hM (capDigits_mem_range s') hγ₂ (hlt _ hγ₂),
            block_lt (hlt _ hγ₁) hko, block_lt (hlt _ hγ₂) (by omega),
            pair_avg_carry (by omega) hγeq⟩
      · -- high part has a digit 2: averaging witnesses with the descending pair
        have hko : keepOnes s < capDigits s := keepOnes_lt_capDigits hsr
        have hcap : capDigits s < s := capDigits_lt_of_not_mem_range hsr
        exact ⟨M * keepOnes s + δ₁, M * capDigits s + δ₂,
          blockMem_mk hM (keepOnes_mem_range s) hδ₁ (hlt _ hδ₁),
          blockMem_mk hM (capDigits_mem_range s) hδ₂ (hlt _ hδ₂),
          block_lt (hlt _ hδ₁) hko, block_lt (hlt _ hδ₂) hcap,
          pair_avg_zero (keepOnes_add_self s) hδeq⟩

/-! ## The increasing enumeration of a block set -/

/-- The candidate closed form: element `n` sits in block `binToTernary (n / |bs|)` at
offset `bs[n % |bs|]`. -/
def blockEnum (M : ℕ) (bs : List ℕ) (n : ℕ) : ℕ :=
  M * binToTernary (n / bs.length) + bs.getD (n % bs.length) 0

/-- Indexed block offsets are members of the block list. -/
theorem getD_mem_of_lt {bs : List ℕ} {i : ℕ} (hi : i < bs.length) :
    bs.getD i 0 ∈ bs := by
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

/-- `blockEnum` is strictly monotone: within a block by sortedness of the offsets,
across blocks because `binToTernary` is strictly monotone and offsets stay below the
modulus. -/
theorem blockEnum_strictMono (M : ℕ) (bs : List ℕ)
    (hlt : ∀ b ∈ bs, b < M) (hsort : bs.Pairwise (· < ·)) (hlen : 0 < bs.length) :
    StrictMono (blockEnum M bs) := by
  intro m n hmn
  have hmL : m % bs.length < bs.length := Nat.mod_lt _ hlen
  have hnL : n % bs.length < bs.length := Nat.mod_lt _ hlen
  rcases eq_or_lt_of_le (Nat.div_le_div_right (c := bs.length) (Nat.le_of_lt hmn)) with
    hq | hq
  · -- same block: compare offsets
    have hmod : m % bs.length < n % bs.length := by
      have hm' := Nat.div_add_mod m bs.length
      have hn' := Nat.div_add_mod n bs.length
      rw [hq] at hm'
      have h5 : bs.length * (n / bs.length) + m % bs.length
          < bs.length * (n / bs.length) + n % bs.length := by
        rw [hm', hn']
        exact hmn
      exact Nat.lt_of_add_lt_add_left h5
    have hoff : bs.getD (m % bs.length) 0 < bs.getD (n % bs.length) 0 := by
      rw [List.getD_eq_getElem _ _ hmL, List.getD_eq_getElem _ _ hnL]
      exact List.pairwise_iff_getElem.mp hsort _ _ hmL hnL hmod
    show M * binToTernary (m / bs.length) + _ < M * binToTernary (n / bs.length) + _
    rw [hq]
    exact Nat.add_lt_add_left hoff _
  · -- later block: block gap dominates
    exact block_lt (hlt _ (getD_mem_of_lt hmL)) (binToTernary_strictMono hq)

/-- The range of `blockEnum` is exactly the block set. -/
theorem range_blockEnum (M : ℕ) (bs : List ℕ) (hM : 0 < M)
    (hlt : ∀ b ∈ bs, b < M) (hlen : 0 < bs.length) :
    Set.range (blockEnum M bs) = {x : ℕ | BlockMem M bs x} := by
  ext x
  constructor
  · rintro ⟨n, rfl⟩
    have hnL : n % bs.length < bs.length := Nat.mod_lt _ hlen
    exact blockMem_mk hM (Set.mem_range_self _) (getD_mem_of_lt hnL)
      (hlt _ (getD_mem_of_lt hnL))
  · rintro ⟨hc, σ, hσ⟩
    obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.mp hc
    refine ⟨bs.length * σ + i, ?_⟩
    have h1 : (bs.length * σ + i) / bs.length = σ := by
      rw [Nat.mul_add_div hlen, Nat.div_eq_of_lt hi, Nat.add_zero]
    have h2 : (bs.length * σ + i) % bs.length = i := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hi]
    rw [blockEnum, h1, h2, hσ, List.getD_eq_getElem _ _ hi, hie]
    exact Nat.div_add_mod x M

/-! ## The greedy sequence from a two-term seed

Reuses `IsGoodExt`, `nextTerm`, `exists_isGoodExt` from
`Proofs/Enumerative/StanleyDigits.lean`; only the base of the recursion differs from
the Stanley case (`{a, b}` instead of `{1}`). -/

/-- Any two-element subset of `ℕ` is 3-AP-free. -/
theorem threeAPFree_pair (a b : ℕ) : ThreeAPFree ({a, b} : Set ℕ) := by
  rintro x hx y hy z hz hxz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy hz
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;>
    omega

/-- Greedy prefix sets from the seed `{a, b}`, bundled with the 3-AP-free invariant:
`(seedAux a b n).1 = {T(1), …, T(n+2)}` in OEIS terms. -/
def seedAux (a b : ℕ) : ℕ → {s : Finset ℕ // ThreeAPFree (↑s : Set ℕ)}
  | 0 => ⟨{a, b}, by
      rw [Finset.coe_insert, Finset.coe_singleton]
      exact threeAPFree_pair a b⟩
  | n + 1 =>
    ⟨insert (nextTerm (seedAux a b n).1 (seedAux a b n).2) (seedAux a b n).1,
      (Nat.find_spec (exists_isGoodExt (seedAux a b n).2)).2⟩

/-- **The greedy 3-AP-free sequence with seed `(a, b)`** (0-indexed): terms `0` and `1`
are the seed; each later term is the least number exceeding all previous terms whose
insertion keeps the prefix 3-AP-free.  For `a < b` this is the OEIS rule "a(n) is the
least k such that no three terms of a(1), …, a(n-1), k form an arithmetic
progression". -/
def seedGreedy (a b : ℕ) : ℕ → ℕ
  | 0 => a
  | 1 => b
  | n + 2 => nextTerm (seedAux a b n).1 (seedAux a b n).2

/-- The seed values of `seedGreedy`. -/
theorem seedGreedy_zero (a b : ℕ) : seedGreedy a b 0 = a := rfl

/-- The seed values of `seedGreedy`. -/
theorem seedGreedy_one (a b : ℕ) : seedGreedy a b 1 = b := rfl

/-- **Greedy step on an enumerated prefix.**  If the prefix is the image of an initial
segment of a strictly monotone enumeration `e` whose range is 3-AP-free and
blocking-complete above `e 1`, the greedy choice is the next value of `e`.
Admissibility is 3-AP-freeness of the range; minimality shoots down every smaller
candidate with its blocking pair, which lands inside the prefix. -/
theorem nextTerm_eq_of_image (e : ℕ → ℕ) (he : StrictMono e)
    (hfree : ThreeAPFree (Set.range e))
    (hblock : ∀ x, x ∉ Set.range e → e 1 < x →
      ∃ p q, p ∈ Set.range e ∧ q ∈ Set.range e ∧ p < q ∧ q < x ∧ p + x = 2 * q)
    (n : ℕ) {s : Finset ℕ} (hs : ThreeAPFree (↑s : Set ℕ))
    (hset : s = (Finset.range (n + 2)).image e) :
    nextTerm s hs = e (n + 2) := by
  subst hset
  simp only [nextTerm]
  rw [Nat.find_eq_iff]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- every prefix element is smaller
    intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    exact he (Finset.mem_range.mp hi)
  · -- inserting e (n+2) stays 3-AP-free: everything lies in the range of e
    refine ThreeAPFree.mono ?_ hfree
    intro z hz
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe,
      Finset.mem_image] at hz
    rcases hz with rfl | ⟨i, -, rfl⟩
    · exact ⟨n + 2, rfl⟩
    · exact ⟨i, rfl⟩
  · -- minimality: any smaller good extension is blocked inside the prefix
    intro k hk hgood
    obtain ⟨hlt, hfree'⟩ := hgood
    have hmem_top : e (n + 1) ∈ (Finset.range (n + 2)).image e :=
      Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega))
    have h1 : e (n + 1) < k := hlt _ hmem_top
    have hknr : k ∉ Set.range e := by
      rintro ⟨j, rfl⟩
      have hj1 : n + 1 < j := he.lt_iff_lt.mp h1
      have hj2 : j < n + 2 := he.lt_iff_lt.mp hk
      omega
    have hek : e 1 < k := lt_of_le_of_lt (he.monotone (by omega : 1 ≤ n + 1)) h1
    obtain ⟨p, q, hp, hq, hpq, hqk, heq⟩ := hblock k hknr hek
    obtain ⟨jp, rfl⟩ := hp
    obtain ⟨jq, rfl⟩ := hq
    have hjq : jq < n + 2 := he.lt_iff_lt.mp (lt_trans hqk hk)
    have hjp : jp < n + 2 := he.lt_iff_lt.mp (lt_trans (lt_trans hpq hqk) hk)
    have hpmem : e jp ∈ (↑(insert k ((Finset.range (n + 2)).image e)) : Set ℕ) := by
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe]
      exact Or.inr (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hjp))
    have hqmem : e jq ∈ (↑(insert k ((Finset.range (n + 2)).image e)) : Set ℕ) := by
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe]
      exact Or.inr (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hjq))
    have hkmem : k ∈ (↑(insert k ((Finset.range (n + 2)).image e)) : Set ℕ) := by
      rw [Finset.coe_insert]
      exact Set.mem_insert _ _
    have hcontra : e jp = e jq := hfree' hpmem hqmem hkmem (by omega)
    omega

/-- The greedy prefix sets from seed `(e 0, e 1)` are the images of initial segments
of `e`. -/
theorem seedAux_eq_image (e : ℕ → ℕ) (he : StrictMono e)
    (hfree : ThreeAPFree (Set.range e))
    (hblock : ∀ x, x ∉ Set.range e → e 1 < x →
      ∃ p q, p ∈ Set.range e ∧ q ∈ Set.range e ∧ p < q ∧ q < x ∧ p + x = 2 * q) :
    ∀ n, (seedAux (e 0) (e 1) n).1 = (Finset.range (n + 2)).image e := by
  intro n
  induction n with
  | zero =>
    show ({e 0, e 1} : Finset ℕ) = _
    rw [Finset.range_add_one, Finset.range_one, Finset.image_insert,
      Finset.image_singleton, Finset.pair_comm]
  | succ n ih =>
    show insert (nextTerm (seedAux (e 0) (e 1) n).1 (seedAux (e 0) (e 1) n).2) _ = _
    rw [nextTerm_eq_of_image e he hfree hblock n (seedAux (e 0) (e 1) n).2 ih, ih]
    have hr : Finset.range (n + 1 + 2) = insert (n + 2) (Finset.range (n + 2)) := by
      rw [show n + 1 + 2 = (n + 2) + 1 by omega, Finset.range_add_one]
    rw [hr, Finset.image_insert]

/-- **The greedy bridge**: the greedy 3-AP-free sequence seeded with `(e 0, e 1)`
equals `e`, for any strictly monotone `e` whose range is 3-AP-free and
blocking-complete above `e 1`. -/
theorem seedGreedy_eq_of_blockLike (e : ℕ → ℕ) (he : StrictMono e)
    (hfree : ThreeAPFree (Set.range e))
    (hblock : ∀ x, x ∉ Set.range e → e 1 < x →
      ∃ p q, p ∈ Set.range e ∧ q ∈ Set.range e ∧ p < q ∧ q < x ∧ p + x = 2 * q) :
    seedGreedy (e 0) (e 1) = e := by
  funext n
  match n with
  | 0 => rfl
  | 1 => rfl
  | n + 2 =>
    exact nextTerm_eq_of_image e he hfree hblock n (seedAux (e 0) (e 1) n).2
      (seedAux_eq_image e he hfree hblock n)

/-! ## Digit splitting for the OEIS form -/

/-- **Digit splitting**: `binToTernary` turns a base-`2^t` split into a base-`3^t`
split, because it transports base-2 digit blocks to base-3 digit blocks. -/
theorem binToTernary_pow_mul_add (t : ℕ) : ∀ q r : ℕ, r < 2 ^ t →
    binToTernary (2 ^ t * q + r) = 3 ^ t * binToTernary q + binToTernary r := by
  induction t with
  | zero =>
    intro q r hr
    interval_cases r
    simp [binToTernary_zero]
  | succ t ih =>
    intro q r hr
    rw [pow_succ] at hr
    rcases Nat.even_or_odd r with ⟨r', rfl⟩ | ⟨r', rfl⟩
    · have h1 : 2 ^ (t + 1) * q + (r' + r') = 2 * (2 ^ t * q + r') := by ring
      have h2 : r' + r' = 2 * r' := by ring
      rw [h1, h2, binToTernary_two_mul, binToTernary_two_mul, ih q r' (by omega)]
      ring
    · have h1 : 2 ^ (t + 1) * q + (2 * r' + 1) = 2 * (2 ^ t * q + r') + 1 := by ring
      rw [h1, binToTernary_two_mul_add_one, binToTernary_two_mul_add_one,
        ih q r' (by omega)]
      ring

/-! ## Row 6: A093681, seed (1, 28) — the conjectured row

**OEIS A093681**, "Sequence contains no 3-term arithmetic progression, starting with
1, 28", terms pinned 2026-08-19:

> 1, 28, 29, 31, 32, 37, 38, 40, 41, 56, 58, 59, 64, 65, 67, 68, 82, 109, 110, 112, …

Formula (pinned verbatim): "a(n) = (Sum_{k=1..n-1} (3^A007814(k) + 1)/2) + f(n), with
f(n) a 16-periodic function with values {1, 27, 26, 27, 23, 27, 26, 27, 14, 28, 28,
28, 28, 28, 28, 28, ...}, n >= 1 (conjectured and checked up to n=1000)."  This
section proves that formula. -/

/-- The 16 block offsets of A093681: its first 16 terms, all below `81 = 3⁴`. -/
def bs93681 : List ℕ :=
  [1, 28, 29, 31, 32, 37, 38, 40, 41, 56, 58, 59, 64, 65, 67, 68]

/-- The 16-periodic residual of A093681, pinned verbatim from the entry's formula. -/
def fs93681 : List ℕ :=
  [1, 27, 26, 27, 23, 27, 26, 27, 14, 28, 28, 28, 28, 28, 28, 28]

/-- **OEIS A093681, 0-indexed** (`a93681 n = A093681(n+1)`): the greedy 3-AP-free
sequence seeded `1, 28`. -/
def a93681 : ℕ → ℕ := seedGreedy 1 28

/-- **The block closed form of A093681**: the greedy sequence seeded `(1, 28)`
is exactly the increasing enumeration of
`{81·s + b : s ∈ A005836-set, b ∈ bs93681}`.  This is Odlyzko–Stanley (1978)
Theorem 1 at `m = 3` (proof omitted there) and Rolnick (2017) closed form (1)
with `A = {0}`; the contribution here is the formalization. -/
theorem a93681_eq_blockEnum : a93681 = blockEnum 81 bs93681 := by
  have hM : 0 < 81 := by norm_num
  have hlt : ∀ b ∈ bs93681, b < 81 := by decide
  have hlen : 0 < bs93681.length := by decide
  have hmono : StrictMono (blockEnum 81 bs93681) :=
    blockEnum_strictMono 81 bs93681 hlt (by decide) hlen
  have hrange := range_blockEnum 81 bs93681 hM hlt hlen
  have hfree : ThreeAPFree (Set.range (blockEnum 81 bs93681)) := by
    rw [hrange]
    exact threeAPFree_blockMem 81 bs93681 hM (by decide)
  have hblock : ∀ x, x ∉ Set.range (blockEnum 81 bs93681) →
      blockEnum 81 bs93681 1 < x →
      ∃ p q, p ∈ Set.range (blockEnum 81 bs93681) ∧
        q ∈ Set.range (blockEnum 81 bs93681) ∧ p < q ∧ q < x ∧ p + x = 2 * q := by
    intro x hx hx1
    rw [hrange] at hx ⊢
    have h1 : blockEnum 81 bs93681 1 = bs93681.getD 1 0 := by
      norm_num [blockEnum, bs93681, binToTernary_zero]
    rw [h1] at hx1
    have hloA : ∀ c < 81, c ∉ bs93681 → c ≤ bs93681.getD 1 0 →
        ∃ p ∈ bs93681, ∃ q ∈ bs93681, q < p ∧ p + c = 2 * q := by decide
    have hloB : ∀ c < 81, c ∉ bs93681 → c ≤ bs93681.getD 1 0 →
        ∃ p ∈ bs93681, ∃ q ∈ bs93681, p < q ∧ p + c + 81 = 2 * q := by decide
    exact blockMem_blocking 81 bs93681 hM hlt (by decide) (by decide)
      (fun c hcM hc hle => ⟨hloA c hcM hc hle, hloB c hcM hc hle⟩) hx hx1
  have h0 : blockEnum 81 bs93681 0 = 1 := by
    norm_num [blockEnum, bs93681, binToTernary_zero]
  have h1 : blockEnum 81 bs93681 1 = 28 := by
    norm_num [blockEnum, bs93681, binToTernary_zero]
  calc a93681 = seedGreedy (blockEnum 81 bs93681 0) (blockEnum 81 bs93681 1) := by
        rw [h0, h1]; rfl
    _ = blockEnum 81 bs93681 :=
        seedGreedy_eq_of_blockLike _ hmono hfree hblock

/-- Pointwise block form of A093681. -/
theorem a93681_apply (n : ℕ) :
    a93681 n = 81 * binToTernary (n / 16) + bs93681.getD (n % 16) 0 := by
  rw [a93681_eq_blockEnum]
  rfl

/-- **The digit closed form of A093681**: `binToTernary` plus the 16-periodic
residual. -/
theorem a93681_eq_binToTernary_add (n : ℕ) :
    a93681 n = binToTernary n + fs93681.getD (n % 16) 0 := by
  have hsplit : binToTernary n = 81 * binToTernary (n / 16) + binToTernary (n % 16) := by
    have h := binToTernary_pow_mul_add 4 (n / 16) (n % 16)
      (Nat.mod_lt _ (by norm_num))
    rw [show (2 : ℕ) ^ 4 = 16 by norm_num, show (3 : ℕ) ^ 4 = 81 by norm_num,
      Nat.div_add_mod] at h
    exact h
  have hres : bs93681.getD (n % 16) 0
      = binToTernary (n % 16) + fs93681.getD (n % 16) 0 := by
    have hlt : n % 16 < 16 := Nat.mod_lt _ (by norm_num)
    interval_cases h : n % 16 <;>
      norm_num [bs93681, fs93681, binToTernary, Nat.ofDigits_cons, Nat.ofDigits_nil]
  rw [a93681_apply, hres, hsplit]
  ring

/-- **The OEIS closed form of A093681** (pinned formula, division-free by doubling;
the entry says "conjectured and checked up to n=1000" — as far as our search
reached, this is a found-no-record candidate for the first written-out
derivation of the exact periodic formula, not a priority claim; the structure
theorem it rests on is published, see header).  In OEIS
1-indexing this is `2·a(n) = Sum_{k=1..n-1} (3^A007814(k) + 1) + 2·f(n)` with `f`
16-periodic of values `fs93681`; here `a93681 n = a(n+1)`. -/
theorem a93681_closedForm (n : ℕ) :
    2 * a93681 n
      = (∑ k ∈ Finset.Icc 1 n, (3 ^ padicValNat 2 k + 1))
        + 2 * fs93681.getD (n % 16) 0 := by
  rw [a93681_eq_binToTernary_add, Nat.mul_add, A092482.two_mul_binToTernary_eq_sum]

/-- **Ground check** against the OEIS `terms` field of A093681 (pinned 2026-08-19):
the first 20 terms match verbatim. -/
theorem a93681_ground :
    (List.range 20).map a93681
      = [1, 28, 29, 31, 32, 37, 38, 40, 41, 56, 58, 59, 64, 65, 67, 68,
         82, 109, 110, 112] := by
  rw [a93681_eq_blockEnum]
  norm_num [blockEnum, bs93681, binToTernary, Nat.ofDigits_cons, Nat.ofDigits_nil,
    List.range_succ]

/-! ## Row 3: A093678, seed (1, 7)

**OEIS A093678**, "Sequence contains no 3-term arithmetic progression, starting with
1, 7", terms pinned 2026-08-19:

> 1, 7, 8, 10, 11, 16, 17, 20, 28, 34, 35, 37, 38, 43, 44, 47, 82, 88, 89, 91, …

Formula (pinned verbatim): "a(n) = (Sum_{k=1..n-1} (3^A007814(k) + 1)/2) + f(n), with
f(n) an 8-periodic function with values {1, 6, 5, 6, 2, 6, 5, 7, ...}, as proved by
Lawrence Sze."  The OEIS credits Sze with the proof (via Ralf Stephan, 2004);
no write-up is linked there and we located none; this section is, as far as we
can determine, the first formalization. -/

/-- The 8 block offsets of A093678: its first 8 terms, all below `27 = 3³`. -/
def bs93678 : List ℕ := [1, 7, 8, 10, 11, 16, 17, 20]

/-- The 8-periodic residual of A093678, pinned verbatim from the entry's formula. -/
def fs93678 : List ℕ := [1, 6, 5, 6, 2, 6, 5, 7]

/-- **OEIS A093678, 0-indexed** (`a93678 n = A093678(n+1)`): the greedy 3-AP-free
sequence seeded `1, 7`. -/
def a93678 : ℕ → ℕ := seedGreedy 1 7

/-- **The block closed form of A093678**: the greedy sequence seeded `(1, 7)` is the
increasing enumeration of `{27·s + b : s ∈ A005836-set, b ∈ bs93678}`. -/
theorem a93678_eq_blockEnum : a93678 = blockEnum 27 bs93678 := by
  have hM : 0 < 27 := by norm_num
  have hlt : ∀ b ∈ bs93678, b < 27 := by decide
  have hlen : 0 < bs93678.length := by decide
  have hmono : StrictMono (blockEnum 27 bs93678) :=
    blockEnum_strictMono 27 bs93678 hlt (by decide) hlen
  have hrange := range_blockEnum 27 bs93678 hM hlt hlen
  have hfree : ThreeAPFree (Set.range (blockEnum 27 bs93678)) := by
    rw [hrange]
    exact threeAPFree_blockMem 27 bs93678 hM (by decide)
  have hblock : ∀ x, x ∉ Set.range (blockEnum 27 bs93678) →
      blockEnum 27 bs93678 1 < x →
      ∃ p q, p ∈ Set.range (blockEnum 27 bs93678) ∧
        q ∈ Set.range (blockEnum 27 bs93678) ∧ p < q ∧ q < x ∧ p + x = 2 * q := by
    intro x hx hx1
    rw [hrange] at hx ⊢
    have h1 : blockEnum 27 bs93678 1 = bs93678.getD 1 0 := by
      norm_num [blockEnum, bs93678, binToTernary_zero]
    rw [h1] at hx1
    have hloA : ∀ c < 27, c ∉ bs93678 → c ≤ bs93678.getD 1 0 →
        ∃ p ∈ bs93678, ∃ q ∈ bs93678, q < p ∧ p + c = 2 * q := by decide
    have hloB : ∀ c < 27, c ∉ bs93678 → c ≤ bs93678.getD 1 0 →
        ∃ p ∈ bs93678, ∃ q ∈ bs93678, p < q ∧ p + c + 27 = 2 * q := by decide
    exact blockMem_blocking 27 bs93678 hM hlt (by decide) (by decide)
      (fun c hcM hc hle => ⟨hloA c hcM hc hle, hloB c hcM hc hle⟩) hx hx1
  have h0 : blockEnum 27 bs93678 0 = 1 := by
    norm_num [blockEnum, bs93678, binToTernary_zero]
  have h1 : blockEnum 27 bs93678 1 = 7 := by
    norm_num [blockEnum, bs93678, binToTernary_zero]
  calc a93678 = seedGreedy (blockEnum 27 bs93678 0) (blockEnum 27 bs93678 1) := by
        rw [h0, h1]; rfl
    _ = blockEnum 27 bs93678 :=
        seedGreedy_eq_of_blockLike _ hmono hfree hblock

/-- Pointwise block form of A093678. -/
theorem a93678_apply (n : ℕ) :
    a93678 n = 27 * binToTernary (n / 8) + bs93678.getD (n % 8) 0 := by
  rw [a93678_eq_blockEnum]
  rfl

/-- **The digit closed form of A093678**: `binToTernary` plus the 8-periodic
residual. -/
theorem a93678_eq_binToTernary_add (n : ℕ) :
    a93678 n = binToTernary n + fs93678.getD (n % 8) 0 := by
  have hsplit : binToTernary n = 27 * binToTernary (n / 8) + binToTernary (n % 8) := by
    have h := binToTernary_pow_mul_add 3 (n / 8) (n % 8)
      (Nat.mod_lt _ (by norm_num))
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num, show (3 : ℕ) ^ 3 = 27 by norm_num,
      Nat.div_add_mod] at h
    exact h
  have hres : bs93678.getD (n % 8) 0
      = binToTernary (n % 8) + fs93678.getD (n % 8) 0 := by
    have hlt : n % 8 < 8 := Nat.mod_lt _ (by norm_num)
    interval_cases h : n % 8 <;>
      norm_num [bs93678, fs93678, binToTernary, Nat.ofDigits_cons, Nat.ofDigits_nil]
  rw [a93678_apply, hres, hsplit]
  ring

/-- **The OEIS closed form of A093678** (pinned formula, division-free by doubling;
first formalization as far as we can determine — the OEIS credits the proof to
Lawrence Sze, with no located write-up).  In OEIS 1-indexing this is
`2·a(n) = Sum_{k=1..n-1} (3^A007814(k) + 1) + 2·f(n)` with `f` 8-periodic of values
`fs93678`; here `a93678 n = a(n+1)`. -/
theorem a93678_closedForm (n : ℕ) :
    2 * a93678 n
      = (∑ k ∈ Finset.Icc 1 n, (3 ^ padicValNat 2 k + 1))
        + 2 * fs93678.getD (n % 8) 0 := by
  rw [a93678_eq_binToTernary_add, Nat.mul_add, A092482.two_mul_binToTernary_eq_sum]

/-- **Ground check** against the OEIS `terms` field of A093678 (pinned 2026-08-19):
the first 20 terms match verbatim. -/
theorem a93678_ground :
    (List.range 20).map a93678
      = [1, 7, 8, 10, 11, 16, 17, 20, 28, 34, 35, 37, 38, 43, 44, 47,
         82, 88, 89, 91] := by
  rw [a93678_eq_blockEnum]
  norm_num [blockEnum, bs93678, binToTernary, Nat.ofDigits_cons, Nat.ofDigits_nil,
    List.range_succ]

/-! ## Row 4: A093679, seed (1, 10)

**OEIS A093679**, "Sequence contains no 3-term arithmetic progression, starting with
1, 10", terms pinned 2026-08-19:

> 1, 10, 11, 13, 14, 20, 22, 23, 28, 37, 38, 40, 41, 47, 49, 50, 82, 91, 92, 94, …

Formula (pinned verbatim): "a(n) = (Sum_{k=1..n-1} (3^A007814(k) + 1)/2) + f(n), with
f(n) an 8-periodic function with values {1, 9, 8, 9, 5, 10, 10, 10, ...}, n >= 1, as
proved by Lawrence Sze."  Same status as A093678: the proof was never published. -/

/-- The 8 block offsets of A093679: its first 8 terms, all below `27 = 3³`. -/
def bs93679 : List ℕ := [1, 10, 11, 13, 14, 20, 22, 23]

/-- The 8-periodic residual of A093679, pinned verbatim from the entry's formula. -/
def fs93679 : List ℕ := [1, 9, 8, 9, 5, 10, 10, 10]

/-- **OEIS A093679, 0-indexed** (`a93679 n = A093679(n+1)`): the greedy 3-AP-free
sequence seeded `1, 10`. -/
def a93679 : ℕ → ℕ := seedGreedy 1 10

/-- **The block closed form of A093679**: the greedy sequence seeded `(1, 10)` is the
increasing enumeration of `{27·s + b : s ∈ A005836-set, b ∈ bs93679}`. -/
theorem a93679_eq_blockEnum : a93679 = blockEnum 27 bs93679 := by
  have hM : 0 < 27 := by norm_num
  have hlt : ∀ b ∈ bs93679, b < 27 := by decide
  have hlen : 0 < bs93679.length := by decide
  have hmono : StrictMono (blockEnum 27 bs93679) :=
    blockEnum_strictMono 27 bs93679 hlt (by decide) hlen
  have hrange := range_blockEnum 27 bs93679 hM hlt hlen
  have hfree : ThreeAPFree (Set.range (blockEnum 27 bs93679)) := by
    rw [hrange]
    exact threeAPFree_blockMem 27 bs93679 hM (by decide)
  have hblock : ∀ x, x ∉ Set.range (blockEnum 27 bs93679) →
      blockEnum 27 bs93679 1 < x →
      ∃ p q, p ∈ Set.range (blockEnum 27 bs93679) ∧
        q ∈ Set.range (blockEnum 27 bs93679) ∧ p < q ∧ q < x ∧ p + x = 2 * q := by
    intro x hx hx1
    rw [hrange] at hx ⊢
    have h1 : blockEnum 27 bs93679 1 = bs93679.getD 1 0 := by
      norm_num [blockEnum, bs93679, binToTernary_zero]
    rw [h1] at hx1
    have hloA : ∀ c < 27, c ∉ bs93679 → c ≤ bs93679.getD 1 0 →
        ∃ p ∈ bs93679, ∃ q ∈ bs93679, q < p ∧ p + c = 2 * q := by decide
    have hloB : ∀ c < 27, c ∉ bs93679 → c ≤ bs93679.getD 1 0 →
        ∃ p ∈ bs93679, ∃ q ∈ bs93679, p < q ∧ p + c + 27 = 2 * q := by decide
    exact blockMem_blocking 27 bs93679 hM hlt (by decide) (by decide)
      (fun c hcM hc hle => ⟨hloA c hcM hc hle, hloB c hcM hc hle⟩) hx hx1
  have h0 : blockEnum 27 bs93679 0 = 1 := by
    norm_num [blockEnum, bs93679, binToTernary_zero]
  have h1 : blockEnum 27 bs93679 1 = 10 := by
    norm_num [blockEnum, bs93679, binToTernary_zero]
  calc a93679 = seedGreedy (blockEnum 27 bs93679 0) (blockEnum 27 bs93679 1) := by
        rw [h0, h1]; rfl
    _ = blockEnum 27 bs93679 :=
        seedGreedy_eq_of_blockLike _ hmono hfree hblock

/-- Pointwise block form of A093679. -/
theorem a93679_apply (n : ℕ) :
    a93679 n = 27 * binToTernary (n / 8) + bs93679.getD (n % 8) 0 := by
  rw [a93679_eq_blockEnum]
  rfl

/-- **The digit closed form of A093679**: `binToTernary` plus the 8-periodic
residual. -/
theorem a93679_eq_binToTernary_add (n : ℕ) :
    a93679 n = binToTernary n + fs93679.getD (n % 8) 0 := by
  have hsplit : binToTernary n = 27 * binToTernary (n / 8) + binToTernary (n % 8) := by
    have h := binToTernary_pow_mul_add 3 (n / 8) (n % 8)
      (Nat.mod_lt _ (by norm_num))
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num, show (3 : ℕ) ^ 3 = 27 by norm_num,
      Nat.div_add_mod] at h
    exact h
  have hres : bs93679.getD (n % 8) 0
      = binToTernary (n % 8) + fs93679.getD (n % 8) 0 := by
    have hlt : n % 8 < 8 := Nat.mod_lt _ (by norm_num)
    interval_cases h : n % 8 <;>
      norm_num [bs93679, fs93679, binToTernary, Nat.ofDigits_cons, Nat.ofDigits_nil]
  rw [a93679_apply, hres, hsplit]
  ring

/-- **The OEIS closed form of A093679** (pinned formula, division-free by doubling;
first formalization as far as we can determine — the OEIS credits the proof to
Lawrence Sze, with no located write-up).  In OEIS 1-indexing this is
`2·a(n) = Sum_{k=1..n-1} (3^A007814(k) + 1) + 2·f(n)` with `f` 8-periodic of values
`fs93679`; here `a93679 n = a(n+1)`. -/
theorem a93679_closedForm (n : ℕ) :
    2 * a93679 n
      = (∑ k ∈ Finset.Icc 1 n, (3 ^ padicValNat 2 k + 1))
        + 2 * fs93679.getD (n % 8) 0 := by
  rw [a93679_eq_binToTernary_add, Nat.mul_add, A092482.two_mul_binToTernary_eq_sum]

/-- **Ground check** against the OEIS `terms` field of A093679 (pinned 2026-08-19):
the first 20 terms match verbatim. -/
theorem a93679_ground :
    (List.range 20).map a93679
      = [1, 10, 11, 13, 14, 20, 22, 23, 28, 37, 38, 40, 41, 47, 49, 50,
         82, 91, 92, 94] := by
  rw [a93679_eq_blockEnum]
  norm_num [blockEnum, bs93679, binToTernary, Nat.ofDigits_cons, Nat.ofDigits_nil,
    List.range_succ]

/-! ## Row 5: A093680, seed (1, 19)

**OEIS A093680**, "Sequence contains no 3-term arithmetic progression, starting with
1, 19", terms pinned 2026-08-19:

> 1, 19, 20, 22, 23, 28, 29, 31, 32, 46, 47, 49, 50, 56, 58, 59, 82, 100, 101, 103, …

Formula (pinned verbatim): "a(n) = (Sum_{k=1..n-1} (3^A007814(k) + 1)/2) + f(n), with
f(n) a 16-periodic function with values {1, 18, 17, 18, 14, 18, 17, 19, 5, 18, 17, 18,
14, 19, 19, 19, ...}, as proved by Lawrence Sze."

**The printed residual list has a typo**: its 8th value must be `18`, not `19`.  The
entry's own `terms` field forces this: `a(8) = 31` and `Sum_{k=1..7} (3^v₂(k)+1)/2 =
binToTernary 7 = 13`, so `f(8) = 31 − 13 = 18`; the printed `19` would give
`a(8) = 32 = a(9)`, impossible for a strictly increasing sequence.  We prove the
corrected list (which also matches the terms to `n = 1024` computationally). -/

/-- The 16 block offsets of A093680: its first 16 terms, all below `81 = 3⁴`. -/
def bs93680 : List ℕ :=
  [1, 19, 20, 22, 23, 28, 29, 31, 32, 46, 47, 49, 50, 56, 58, 59]

/-- The 16-periodic residual of A093680 — the OEIS list with its 8th value corrected
from `19` to `18` (see the section header). -/
def fs93680 : List ℕ :=
  [1, 18, 17, 18, 14, 18, 17, 18, 5, 18, 17, 18, 14, 19, 19, 19]

/-- **OEIS A093680, 0-indexed** (`a93680 n = A093680(n+1)`): the greedy 3-AP-free
sequence seeded `1, 19`. -/
def a93680 : ℕ → ℕ := seedGreedy 1 19

/-- **The block closed form of A093680**: the greedy sequence seeded `(1, 19)` is the
increasing enumeration of `{81·s + b : s ∈ A005836-set, b ∈ bs93680}`. -/
theorem a93680_eq_blockEnum : a93680 = blockEnum 81 bs93680 := by
  have hM : 0 < 81 := by norm_num
  have hlt : ∀ b ∈ bs93680, b < 81 := by decide
  have hlen : 0 < bs93680.length := by decide
  have hmono : StrictMono (blockEnum 81 bs93680) :=
    blockEnum_strictMono 81 bs93680 hlt (by decide) hlen
  have hrange := range_blockEnum 81 bs93680 hM hlt hlen
  have hfree : ThreeAPFree (Set.range (blockEnum 81 bs93680)) := by
    rw [hrange]
    exact threeAPFree_blockMem 81 bs93680 hM (by decide)
  have hblock : ∀ x, x ∉ Set.range (blockEnum 81 bs93680) →
      blockEnum 81 bs93680 1 < x →
      ∃ p q, p ∈ Set.range (blockEnum 81 bs93680) ∧
        q ∈ Set.range (blockEnum 81 bs93680) ∧ p < q ∧ q < x ∧ p + x = 2 * q := by
    intro x hx hx1
    rw [hrange] at hx ⊢
    have h1 : blockEnum 81 bs93680 1 = bs93680.getD 1 0 := by
      norm_num [blockEnum, bs93680, binToTernary_zero]
    rw [h1] at hx1
    have hloA : ∀ c < 81, c ∉ bs93680 → c ≤ bs93680.getD 1 0 →
        ∃ p ∈ bs93680, ∃ q ∈ bs93680, q < p ∧ p + c = 2 * q := by decide
    have hloB : ∀ c < 81, c ∉ bs93680 → c ≤ bs93680.getD 1 0 →
        ∃ p ∈ bs93680, ∃ q ∈ bs93680, p < q ∧ p + c + 81 = 2 * q := by decide
    exact blockMem_blocking 81 bs93680 hM hlt (by decide) (by decide)
      (fun c hcM hc hle => ⟨hloA c hcM hc hle, hloB c hcM hc hle⟩) hx hx1
  have h0 : blockEnum 81 bs93680 0 = 1 := by
    norm_num [blockEnum, bs93680, binToTernary_zero]
  have h1 : blockEnum 81 bs93680 1 = 19 := by
    norm_num [blockEnum, bs93680, binToTernary_zero]
  calc a93680 = seedGreedy (blockEnum 81 bs93680 0) (blockEnum 81 bs93680 1) := by
        rw [h0, h1]; rfl
    _ = blockEnum 81 bs93680 :=
        seedGreedy_eq_of_blockLike _ hmono hfree hblock

/-- Pointwise block form of A093680. -/
theorem a93680_apply (n : ℕ) :
    a93680 n = 81 * binToTernary (n / 16) + bs93680.getD (n % 16) 0 := by
  rw [a93680_eq_blockEnum]
  rfl

/-- **The digit closed form of A093680**: `binToTernary` plus the 16-periodic
residual (typo-corrected, see the section header). -/
theorem a93680_eq_binToTernary_add (n : ℕ) :
    a93680 n = binToTernary n + fs93680.getD (n % 16) 0 := by
  have hsplit : binToTernary n = 81 * binToTernary (n / 16) + binToTernary (n % 16) := by
    have h := binToTernary_pow_mul_add 4 (n / 16) (n % 16)
      (Nat.mod_lt _ (by norm_num))
    rw [show (2 : ℕ) ^ 4 = 16 by norm_num, show (3 : ℕ) ^ 4 = 81 by norm_num,
      Nat.div_add_mod] at h
    exact h
  have hres : bs93680.getD (n % 16) 0
      = binToTernary (n % 16) + fs93680.getD (n % 16) 0 := by
    have hlt : n % 16 < 16 := Nat.mod_lt _ (by norm_num)
    interval_cases h : n % 16 <;>
      norm_num [bs93680, fs93680, binToTernary, Nat.ofDigits_cons, Nat.ofDigits_nil]
  rw [a93680_apply, hres, hsplit]
  ring

/-- **The OEIS closed form of A093680** (pinned formula with the 8th residual value
corrected from `19` to `18`, division-free by doubling; first formalization as far
as we can determine — the OEIS credits the proof to Lawrence Sze with no located
write-up, and the printed OEIS list contains the typo documented
above).  In OEIS 1-indexing this is `2·a(n) = Sum_{k=1..n-1} (3^A007814(k) + 1) +
2·f(n)` with `f` 16-periodic of values `fs93680`; here `a93680 n = a(n+1)`. -/
theorem a93680_closedForm (n : ℕ) :
    2 * a93680 n
      = (∑ k ∈ Finset.Icc 1 n, (3 ^ padicValNat 2 k + 1))
        + 2 * fs93680.getD (n % 16) 0 := by
  rw [a93680_eq_binToTernary_add, Nat.mul_add, A092482.two_mul_binToTernary_eq_sum]

/-- **Ground check** against the OEIS `terms` field of A093680 (pinned 2026-08-19):
the first 20 terms match verbatim — in particular `a(8) = 31`, confirming the residual
typo correction. -/
theorem a93680_ground :
    (List.range 20).map a93680
      = [1, 19, 20, 22, 23, 28, 29, 31, 32, 46, 47, 49, 50, 56, 58, 59,
         82, 100, 101, 103] := by
  rw [a93680_eq_blockEnum]
  norm_num [blockEnum, bs93680, binToTernary, Nat.ofDigits_cons, Nat.ofDigits_nil,
    List.range_succ]

/-! ## Verification

Satisfiability spot-checks for the engine's hypotheses (the four row instantiations
above already exercise every engine theorem jointly at concrete models), an
independent diagnostic run of the greedy definition itself, and the axiom audit. -/

/-- Satisfiability: a positive `BlockMem` witness, `28 = 27·1 + 1`. -/
example : BlockMem 27 bs93678 28 :=
  ⟨by decide, ⟨1, binToTernary_one⟩⟩

/-- Satisfiability: a negative `BlockMem` witness (`2` is not a term of A093678). -/
example : ¬ BlockMem 27 bs93678 2 := fun h => absurd h.1 (by decide)

/-- Satisfiability: the blocking conclusion is witnessed concretely — the non-term
`x = 9` of row 3 is blocked by the pair `(7, 8)`: `7 + 9 = 2·8`. -/
example : ∃ p q, BlockMem 27 bs93678 p ∧ BlockMem 27 bs93678 q ∧
    p < q ∧ q < 9 ∧ p + 9 = 2 * q :=
  ⟨7, 8, ⟨by decide, ⟨0, binToTernary_zero⟩⟩, ⟨by decide, ⟨0, binToTernary_zero⟩⟩,
    by norm_num, by norm_num, by norm_num⟩

/- **Independent cross-check of the greedy definition itself.**  The ground-check
theorems above route through the block closed forms; if `seedGreedy` had been
mis-formalized, both sides would be wrong together.  The `#eval`s below instead *run*
the greedy recursion — `Nat.find` over `IsGoodExt`, the literal OEIS rule, with no
reference to any closed form — and print the OEIS `terms` prefixes

  row 3: `[1, 7, 8, 10, 11, 16, 17, 20, 28, 34, 35, 37]`
  row 6: `[1, 28, 29, 31, 32, 37, 38, 40, 41, 56, 58, 59]`.

These are diagnostics, not proofs, and contribute no axioms. -/
#eval (List.range 12).map (seedGreedy 1 7)
#eval (List.range 12).map (seedGreedy 1 28)

#print axioms a93678_closedForm
#print axioms a93679_closedForm
#print axioms a93680_closedForm
#print axioms a93681_closedForm
#print axioms a93681_eq_blockEnum
#print axioms a93681_ground

end A093682
