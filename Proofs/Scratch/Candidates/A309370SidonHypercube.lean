/-
# A309370 — Sidon subsets of the hypercube

## OEIS source (re-pulled verbatim with `goof oeis show A309370`, 2026-08-05)

```
NAME:     Maximum size of a Sidon subset of {0,1}^n.
TERMS:    1,2,3,5,7,12,15
KEYWORDS: nonn,hard,more
COMMENTS:
  Define addition on {0,1}^n componentwise (ordinary addition, not addition
  modulo 2, so the result lies in {0,1,2}^n, not necessarily {0,1}^n). We say a
  subset of {0,1}^n is Sidon iff the only solutions to a + b = c + d, with
  a,b,c,d in the set, are the trivial ones: a = c, b = d or a = d, b = c.
  a(7) >= 23, a(8) >= 32, a(9) >= 45, a(10) >= 63, a(11) >= 87, a(12) >= 120,
  a(13) >= 169, a(14) >= 237, a(15) >= 334, a(16) >= 472, a(17) >= 662,
  a(18) >= 864.
  Conjecture: a(n) is asymptotic to 2^(n/2+1).
  a(7) >= 24. - _Christian Sievers_, Sep 17 2025
  a(16) >= 503, a(17) >= 712, a(18) >= 1010, a(19) >= 1397, a(20) >= 1941,
  a(21) >= 2694, a(22) >= 3770 (see Blair Link). - _William Blair_, Jun 02 2026
  a(8) >= 33, a(9) >= 46, a(10) >= 66 (verified Sidon sets attaining these
  sizes; see Blair Link). - _William Blair_, Jun 03 2026
  a(9) >= 47, a(11) >= 92, a(12) >= 133, a(13) >= 185, a(14) >= 257,
  a(15) >= 364, a(16) >= 505, a(19) >= 1435, a(20) >= 1989 (verified Sidon sets
  attaining these sizes; see Blair Link). - _William Blair_, Jun 05 2026
  a(23) >= 5179, a(24) >= 7179 (verified Sidon sets attaining these sizes; see
  Blair Link). - _William Blair_, Jun 05 2026
```

Raw-pull lines that `goof oeis show` strips
(`curl "https://oeis.org/search?q=id:A309370&fmt=text"`):
```
%O A309370 0,2
%A A309370 _Asier Calbet Rípodas_, Aug 02 2019
%F A309370 Theorem 2 from Lindström (1969) implies that a(n) > 2^(k*n) for any
           k < 1/2 and large enough n. - _Charles R Greathouse IV_, Oct 03 2025
%F A309370 Cohen, Litsyn, and Zémor prove that a(n) < 2^(0.57526*n) for large
           enough n. - _Charles R Greathouse IV_, Oct 03 2025
```

## Offset correction

The earlier candidate sweep says "exact values 1, 2, 3, 5, 7, 12, 15 for `n ≤ 7`".
That is **off by one**: there are 7 terms and the first `a(7)` line is a *lower
bound* (`a(7) ≥ 23`), so the offset is `0` and the exact values run `n = 0..6`:
`a(0) = 1, a(1) = 2, a(2) = 3, a(3) = 5, a(4) = 7, a(5) = 12, a(6) = 15`.
Sanity: `a(0) = 1` because `{0,1}^0` is a single point; `a(2) = 3` because the
full square fails (`00 + 11 = 01 + 10`) while any three of its points work.

## Status

Open.  Lindström (1969) gives the lower bound, Cohen–Litsyn–Zémor the upper
bound `2^{0.57526 n}`; the conjectured truth `2^{n/2 + 1}` sits strictly below
the known upper bound, so the conjecture is *not* implied by current results.
The entry is under active revision (Blair's records are dated June 2026).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A309370

/-! ## Definition layer

`leandoc` findings: **Mathlib has no Sidon sets.**
`grep -rn "Sidon" .lake/packages/mathlib/Mathlib/` returns nothing, and
`leandoc "Sidon set"` is pure noise.  The repo has none either
(`grep -rn "Sidon" /home/neal/p/proofs/` is empty).  So the predicate is
defined fresh, and it is written to be reusable by `A390813SidonSquares.lean`
in this directory — hence the general `AddCommMonoid` version alongside the
hypercube specialization.

What *is* available and relevant:
* `ThreeAPFree` (`Mathlib/Combinatorics/Additive/AP/Three/Defs.lean`) — the
  `x + z = 2y` analogue.  Sidon is the `a + b = c + d` analogue and is *not* a
  special case, so it cannot be reduced to it.
* `Finset.card`, `Finset.filter`, `Fintype.card` — STYLE.md forbids mixing
  cardinality APIs, so everything below uses `Finset.card` and the maximum is
  taken with `Finset.max'`/`IsGreatest`, never `Nat.card`.
* `Asymptotics.IsLittleO`, `Filter.Tendsto`, `Real.rpow` — for the asymptotic.
  `2^(n/2+1)` has a half-integer exponent, so it must live in `ℝ` via
  `Real.rpow`; `(2 : ℕ) ^ (n / 2 + 1)` with `ℕ` division would be a *different
  and wrong* quantity (it truncates at odd `n`).  That is the main type trap in
  this card. -/

/-- A general Sidon predicate over an additive commutative monoid: the only
solutions of `a + b = c + d` inside `S` are the trivial ones. -/
def IsSidon {α : Type*} [AddCommMonoid α] [DecidableEq α] (S : Finset α) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- The hypercube point `v` as an `ℕ`-valued vector, so that addition is the
componentwise **ordinary** addition the OEIS comment specifies (landing in
`{0,1,2}^n`), not addition mod `2`. -/
def emb {n : ℕ} (v : Fin n → Bool) : Fin n → ℕ := fun i => if v i then 1 else 0

/-- A subset of the Boolean hypercube is Sidon when its image under `emb` is. -/
def IsSidonCube {n : ℕ} (S : Finset (Fin n → Bool)) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
    emb a + emb b = emb c + emb d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

instance {n : ℕ} (S : Finset (Fin n → Bool)) : Decidable (IsSidonCube S) := by
  unfold IsSidonCube; infer_instance

/-- A309370: the maximum size of a Sidon subset of `{0,1}^n`.  Offset `0`. -/
noncomputable def a309370 (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ S : Finset (Fin n → Bool), IsSidonCube S ∧ S.card = k}

/-! ## The conjecture -/

/-- **The A309370 asymptotic conjecture.**

Verbatim (entry comment): "Conjecture: a(n) is asymptotic to 2^(n/2+1)."

"Asymptotic to" means the ratio tends to `1`.  The exponent `n/2 + 1` is a
*half-integer*, so the right-hand side must be `(2 : ℝ) ^ ((n : ℝ) / 2 + 1)` via
`Real.rpow`; writing `(2 : ℕ) ^ (n / 2 + 1)` would silently truncate at odd `n`
and state a different (false) claim.  This is the type trap flagged above.

**Mathlib primitives available.**  `Filter.Tendsto`, `Filter.atTop`,
`Real.rpow`, `Real.rpow_natCast`, `Real.rpow_add`, `Asymptotics.IsBigO`,
`Asymptotics.IsLittleO`, `Asymptotics.isEquivalent` (`~[atTop]`, which is
literally "asymptotic to" and is the Mathlib-normal spelling —
`Asymptotics.IsEquivalent f g ↔ (f - g) =o[l] g`).  The repo's asymptotics
toolbox (see `reference_lean_basic_asymptotics_toolbox`) applies.

**Sketch of the known bounds.**
* *Lower* (Lindström 1969): a Sidon set in `{0,1}^n` of size `≍ 2^{n/2}` comes
  from a Sidon set in `ℤ/2^n` via binary expansion — the "B₂ set" construction.
  Constructive and formalizable, though not small.
* *Upper*: counting pairs gives `binom(|S|,2) ≤ 3^n` (the sumset lives in
  `{0,1,2}^n`), i.e. `|S| ≲ 3^{n/2} = 2^{0.7925n}`.  **This trivial bound is
  provable today and is the right first target**; the Cohen–Litsyn–Zémor
  refinement to `2^{0.57526 n}` is a Fourier/linear-programming argument.
* The conjecture `2^{n/2+1}` is *below* the CLZ upper bound, so proving it needs
  a new upper-bound technique, not just bookkeeping.

**Tactic families.**  `decide` for `n ≤ 3` (`|{0,1}^n| ≤ 8`, so
`2^8 = 256` subsets); `native_decide` for `n = 4, 5` (`2^16`, `2^32` subsets —
`n = 5` needs a smarter search than brute subset enumeration);
`Finset.card_le_card_of_injOn` for the counting upper bound;
`Real.rpow` simp set plus `Filter.Tendsto.div` for the asymptotic;
`Asymptotics.IsEquivalent.trans` for chaining.

**Related work in this repo.**  `Proofs/Erdos/Erdos880/` (restricted sumsets),
`Proofs/BilinearComplexity/Capset.lean` and `CapsetSliceRank.lean` (the
`x + z = 2y` problem in `𝔽_3^n`).  **The slice-rank method does not transfer**:
it needs a tensor with a group-algebra structure that `a + b = c + d` over
`{0,1}^n` (with *ordinary*, not modular, addition) does not have.  Adjacent
card: `A390813SidonSquares.lean`, which reuses `IsSidon` above. -/
theorem a309370_asymptotic :
    Filter.Tendsto (fun n : ℕ => (a309370 n : ℝ) / (2 : ℝ) ^ ((n : ℝ) / 2 + 1))
      Filter.atTop (nhds 1) := by
  sorry

/-- The trivial counting upper bound, **provable today**: the sumset of a Sidon
set in `{0,1}^n` lives in `{0,1,2}^n`, and distinct unordered pairs have
distinct sums, so `binom(|S|, 2) ≤ 3^n`. -/
theorem a309370_trivial_upper (n : ℕ) : a309370 n * (a309370 n - 1) ≤ 2 * 3 ^ n := by
  sorry

/-! ## Sanity layer -/

-- PROVABLE: the exact values, `n = 0..6`, matching the DATA line
-- `1, 2, 3, 5, 7, 12, 15` with offset `0`.
example : a309370 0 = 1 := by sorry
example : a309370 1 = 2 := by sorry
example : a309370 2 = 3 := by sorry
example : a309370 3 = 5 := by sorry

-- PROVABLE: the offset pin.  The full square `{0,1}^2` is *not* Sidon because
-- `(0,0) + (1,1) = (0,1) + (1,0)`, which is why `a(2) = 3 < 4`.  This single
-- check separates the correct offset from the candidates document's `n ≤ 7`.
example : ¬ IsSidonCube (Finset.univ : Finset (Fin 2 → Bool)) := by decide

-- PROVABLE: and three of the four points *are* Sidon, so `a(2) = 3` is attained.
example : IsSidonCube ({![false, false], ![false, true], ![true, false]} :
    Finset (Fin 2 → Bool)) := by decide

-- PROVABLE: satisfiability — `IsSidonCube` is nonvacuous and the singleton and
-- empty cases behave.
example : IsSidonCube (∅ : Finset (Fin 3 → Bool)) := by decide
example : IsSidonCube (Finset.univ : Finset (Fin 1 → Bool)) := by decide

-- PROVABLE: `emb` ground truth — the embedding really lands in `{0,1}` and
-- addition really is ordinary (so `1 + 1 = 2`, not `0`).
example : emb ![true] + emb ![true] = ![2] := by decide

-- PROVABLE: the `sSup` is over a nonempty bounded set, so `a309370 n` is not
-- the `sSup ∅ = 0` junk value.  `∅` is always a Sidon subset of card `0`, and
-- cards are bounded by `2^n`.
theorem a309370_bddAbove (n : ℕ) :
    BddAbove {k : ℕ | ∃ S : Finset (Fin n → Bool), IsSidonCube S ∧ S.card = k} := by
  sorry

/-! ## Notes for a follow-up card

1. `a309370_bddAbove` and the `n ≤ 3` exact values — free-ish, and they make
   every other statement about a well-defined quantity.
2. `a309370_trivial_upper` — the `binom(|S|,2) ≤ 3^n` bound.  Provable today,
   maybe 60 lines, and it is a real (if weak) theorem about the sequence.
3. Lindström's lower bound `2^{n/2} ≲ a(n)` — a construction, so formalizable,
   and it turns the conjecture into a two-sided question.
4. The conjecture itself — open, and not implied by the known upper bound.

References: Lindström, *Determination of two vectors from the sum*,
J. Combin. Theory 6 (1969) 402–407; Cohen, Litsyn, Zémor, *Binary B₂-sequences:
a new upper bound*, J. Combin. Theory Ser. A 94 (2001) 152–155. -/

/-!
## Adversarial review verdict — **PASS-WITH-NOTES** (no defects)

Independent re-pull of A309370 by a source-fidelity reviewer, 2026-08-05.

Confirmed:
* `%O A309370 0,2` — **offset `0`**, so the candidates document's
  "exact values … for `n ≤ 7`" is indeed off by one; the exact range is
  `n = 0..6`.
* `a(2) = 3`: the full square fails because `(0,0)+(1,1) = (0,1)+(1,0)`, and any
  3-subset is Sidon.
* **The type trap is real**: at `n = 5`, `(2:ℕ)^(5/2+1) = 2^3 = 8` while
  `(2:ℝ)^(3.5) = 11.314…`.  `Real.rpow` is mandatory.
* `emb` lands in `ℕ`-vectors, so addition is ordinary (`1 + 1 = 2`), matching
  the OEIS's "not addition modulo 2".
* Mathlib has no Sidon predicate; neither did the repo before these two cards.
* `a309370_trivial_upper`: the `binom(|S|,2) ≤ 3^n` counting is valid, and the
  `ℕ` subtraction `a309370 n - 1` cannot truncate harmfully (at `a = 0` both
  sides are `0`; and `a ≥ 1` always, since singletons are Sidon).

Two notes, neither a defect:
* **A.**  The bound could be tightened to `|S|(|S|+1) ≤ 2·3^n` by counting
  diagonal pairs `a + a` as well; the stated form is valid but weaker for the
  same proof cost.
* **B.**  The two Greathouse `%F` lines were originally discussed only in prose.
  **FIXED**: they are now quoted verbatim in the header, along with `%O` and
  `%A`, since `goof oeis show` strips those fields.
-/

end Candidates.A309370
