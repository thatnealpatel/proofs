/-
# A351243 — Selfridge–Lacampagne counterexamples and the `3^m + 4` family

## OEIS source (re-pulled verbatim 2026-08-05)

`goof oeis show A351243`:
```
NAME:     Counterexamples to a conjecture of Selfridge and Lacampagne.
TERMS:    247,277,967,977,1211,1219,1895,1937,1951,1961,2183,2191,2911,2921,
          3029,3641,3649
KEYWORDS: nonn,base,more
COMMENTS:
  The conjecture was that every natural number k not divisible by 3 can be
  written as the quotient of two terms chosen from A147991.
  For every specific k, the problem of representing k as the quotient of two
  terms of A147991 can be decided by using a queue-based breadth-first search
  algorithm on the transition diagram of a finite automaton that on input j in
  base 3 computes j*k and checks to see if both j and j*k are in A147991.
  It is not known if there are infinitely many counterexamples to the
  conjecture, but perhaps 3^m+4, for m >= 5 and odd, are.
XREFS:
  Cf. A147991.
```

`goof oeis show A147991`:
```
NAME:     Sequence S such that 1 is in S and if x is in S, then 3x-1 and 3x+1
          are in S.
TERMS:    1,2,4,5,7,11,13,14,16,20,22,32,34,38,40,41,43,47,49,59,61,65,67,95,97,
          101,103,113,115,119,121,122,124,128,130,140,142,146,148,176,178,182,
          184,194,196,200,202,284,286,290,292,302,304,308,310,338,340,344,346
KEYWORDS: nonn
COMMENTS:
  Positive numbers that can be written in balanced ternary without a 0 trit.
  - _J. Hufford_, Jun 30 2015
  Let S be the set of terms. Define c: Z -> P(R) so that c(m) is the translated
  Cantor ternary set spanning [m-0.5, m+0.5], and let C be the union of c(m) for
  all m in S U {0} U -S. C is the closure of the translated Cantor ternary set
  spanning [-0.5, 0.5] under multiplication by 3. - _Peter Munn_, Jan 31 2022
```

## Balanced-ternary correction

The earlier candidate sweep says of A147991: *"Needs a def for A147991 membership
(base-3 digits in {0,1} — trivial)"*.  **That is wrong.**  A147991 is
*balanced ternary with no `0` trit*, i.e. digits in `{−1, +1}`, per Hufford's
comment above.  Ordinary base-3 digits in `{0,1}` is A005836 (the Stanley
sequence / Cantor set integers), a *different* sequence — `3` is in A005836
(digits `10`) but not in A147991.  A card built on the document's reading would
formalize the wrong sequence entirely.

The balanced-ternary reading was verified computationally before writing this
card: enumerating `Σ εᵢ 3ⁱ` with `εᵢ ∈ {−1, +1}` over all trit-lengths `≤ 14`
and keeping the positive values reproduces the A147991 DATA line exactly
(first 20 terms `1, 2, 4, 5, 7, 11, 13, 14, 16, 20, 22, 32, 34, 38, 40, 41, 43,
47, 49, 59`).

## Status

The **original** Selfridge–Lacampagne conjecture is **disproved** — A351243 is
precisely the list of known counterexamples.  What is **open** is whether there
are infinitely many, and specifically whether `3^m + 4` (`m ≥ 5` odd) is an
infinite family of counterexamples.

Data check on the `3^m + 4` speculation: `3^5 + 4 = 247` (the first term) and
`3^7 + 4 = 2191` (also a term).  `3^9 + 4 = 19687` is beyond the listed range,
so the DATA neither confirms nor refutes it.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A351243

/-! ## Definition layer

`leandoc` findings: nothing in Mathlib for balanced ternary.
`leandoc "balanced ternary"` and `leandoc Nat.balancedTernary` are misses.
`Nat.digits` exists but is the ordinary (non-balanced) expansion, so it is the
*wrong* tool here — using it would reintroduce exactly the error the candidates
document made.

Two encodings of A147991 are given:

* `btVal : List Bool → ℤ` + `MemA147991` — the balanced-ternary characterization
  (Hufford's comment).  This is the one all statements use; it is finitary,
  decidable given a length bound, and it is what was verified against the DATA
  line.
* `GenA147991` — the *generative* definition from the OEIS NAME (`1 ∈ S`, and
  `x ∈ S → 3x−1 ∈ S ∧ 3x+1 ∈ S`).  Recorded because the NAME is the official
  definition and the balanced-ternary form is "only" a comment; their
  equivalence is a PROVABLE obligation, not something to assume.

The generative form uses `3 * x - 1` with `ℕ` subtraction.  Truncation never
fires (every member is `≥ 1`, so `3x − 1 ≥ 2`), but STYLE.md wants the guard
visible, so `GenA147991` is stated over `ℤ` with an explicit positivity
invariant rather than over `ℕ` with a silent truncation. -/

/-- Value of a balanced-ternary trit string, little-endian, `true ↦ +1`,
`false ↦ −1`.  No `0` trit is representable, which is the point. -/
def btVal : List Bool → ℤ
  | [] => 0
  | b :: t => (if b then 1 else -1) + 3 * btVal t

/-- Membership in A147991 (balanced-ternary characterization): `n` is a positive
integer writable in balanced ternary with no `0` trit. -/
def MemA147991 (n : ℕ) : Prop := ∃ L : List Bool, L ≠ [] ∧ btVal L = (n : ℤ)

/-- Membership in A147991 (generative characterization, the OEIS NAME).  Stated
over `ℤ` so that `3x − 1` is honest subtraction; positivity of every member is
then a lemma (`genA147991_pos`) rather than an implicit assumption. -/
inductive GenA147991 : ℤ → Prop
  | one : GenA147991 1
  | lo {x : ℤ} : GenA147991 x → GenA147991 (3 * x - 1)
  | hi {x : ℤ} : GenA147991 x → GenA147991 (3 * x + 1)

/-- `k` is a Selfridge–Lacampagne **counterexample**: `k` is a positive integer
not divisible by `3` that is *not* the quotient of two A147991 terms.  Note the
quotient is stated multiplicatively (`a = k * b`), so no division appears. -/
def IsSLCounterexample (k : ℕ) : Prop :=
  0 < k ∧ ¬ (3 ∣ k) ∧ ¬ ∃ a b : ℕ, MemA147991 a ∧ MemA147991 b ∧ a = k * b

/-! ## The statements -/

/-- **The original Selfridge–Lacampagne conjecture — DISPROVED.**

Verbatim: "The conjecture was that every natural number k not divisible by 3 can
be written as the quotient of two terms chosen from A147991."

Stated as a `theorem … : ¬ (…)` because the source says it is *false*; stating
it positively would archive a known falsehood.  A card that discharges this
`sorry` proves the refutation, whose content is exactly `247` being a
counterexample.  Shallit et al. resolved the original conjecture negatively
(see the entry's automaton comment, which describes their decision procedure).

**Mathlib primitives available.**  `Nat.digits` (wrong tool here — see the
definition layer), `List`, `Finset.filter`, `Decidable` machinery.  The
decision procedure the OEIS describes is a **finite automaton** on base-3
digits; Mathlib has `Computability.DFA` (`DFA`, `DFA.accepts`,
`DFA.evalFrom`) and `Language`, so the automaton could in principle be built
and its emptiness decided.  That is the honest route to a *proof* of
counterexample-hood; the bounded search below is only a certificate for a
bounded range.

**Sketch of the refutation.**  For fixed `k`, the pairs `(b, kb)` with both in
A147991 are recognized by a DFA reading `b` in base `3` least-significant-digit
first, with state = carry ∈ a finite window (`|carry| ≤ k`) together with the
"is a valid trit" flags for both `b` and `kb`.  Emptiness of the accepted
language is decidable by reachability.  For `k = 247` the language is empty.
Formalizing this is genuinely feasible: `DFA` + `Finset` reachability + `decide`.

**Tactic families.** `decide` on the bounded search; `DFA.mem_accepts`;
`Finset.card_eq_zero`; `omega` for the carry arithmetic; `induction` on the
inductive `GenA147991` for the equivalence proof.

**Related work in this repo.** `Enumerative.StanleyDigits` uses `Nat.digits 3`
and `Nat.ofDigits 3` for the A005836/A003278 pair — structurally similar digit
predicates, but on the *ordinary* ternary expansion.  The two must not be
confused (that confusion is what this card's header corrects). -/
theorem selfridgeLacampagne_false :
    ¬ ∀ k : ℕ, 0 < k → ¬ (3 ∣ k) → ∃ a b : ℕ, MemA147991 a ∧ MemA147991 b ∧ a = k * b := by
  sorry

/-- `247` is a counterexample — the first term of A351243, and the content of the
refutation.  Not open: this is a finite (automaton-decidable) fact. -/
theorem isSLCounterexample_247 : IsSLCounterexample 247 := by
  sorry

/-- **The open question (A351243).**

Verbatim: "It is not known if there are infinitely many counterexamples to the
conjecture, but perhaps 3^m+4, for m >= 5 and odd, are."

Part one: infinitude of the counterexample set. -/
theorem slCounterexamples_infinite : {k : ℕ | IsSLCounterexample k}.Infinite := by
  sorry

/-- **The open question, part two: the `3^m + 4` family.**

Verbatim: "…but perhaps 3^m+4, for m >= 5 and odd, are."

Note the source's hedge ("perhaps") — this is a *speculation* recorded in the
entry, not an asserted conjecture, and the card should not upgrade it.  Data
support: `3^5 + 4 = 247` ✓ (first term) and `3^7 + 4 = 2191` ✓ (a term);
`3^9 + 4 = 19687` is past the end of the DATA line, so untested.

This statement implies `slCounterexamples_infinite`. -/
theorem slCounterexample_three_pow_add_four (m : ℕ) (hm : 5 ≤ m) (hodd : Odd m) :
    IsSLCounterexample (3 ^ m + 4) := by
  sorry

/-! ## Sanity layer -/

-- PROVABLE: the two characterizations of A147991 agree.  This is the
-- definitional audit that the balanced-ternary reading is the right one.
theorem memA147991_iff_gen (n : ℕ) (hn : 0 < n) :
    MemA147991 n ↔ GenA147991 (n : ℤ) := by
  sorry

-- PROVABLE: every member of the generative set is positive, so the `ℕ`-level
-- `3x − 1` in the OEIS NAME never truncates.
theorem genA147991_pos {x : ℤ} (h : GenA147991 x) : 0 < x := by
  sorry

-- PROVABLE: the head of the A147991 DATA line, via `btVal`.
--   1 = [T], 2 = [F,T], 4 = [T,T], 5 = [F,F,T], 7 = [T,F,T], 11 = [F,T,T],
--   13 = [T,T,T], 14 = [F,F,F,T]
example : btVal [true] = 1 := by decide
example : btVal [false, true] = 2 := by decide
example : btVal [true, true] = 4 := by decide
example : btVal [false, false, true] = 5 := by decide
example : btVal [true, false, true] = 7 := by decide
example : btVal [false, true, true] = 11 := by decide
example : btVal [true, true, true] = 13 := by decide
example : btVal [false, false, false, true] = 14 := by decide

-- PROVABLE: `3` is **not** in A147991, which is the discriminating case against
-- the "base-3 digits in {0,1}" misreading (`3 = 10₃` *is* in A005836).
-- Search bound: `|btVal L| ≥ (3^len − 1)/2 · 0 + …` — concretely,
-- `btVal L ≥ 3^(len−1) − (3^(len−1) − 1)/2 > 3` once `len ≥ 3`, and lengths
-- `1, 2` give only `±1, ±2, ±4`.  So a length-`≤ 3` enumeration suffices.
theorem three_not_memA147991 : ¬ MemA147991 3 := by
  sorry

-- PROVABLE: `247` and `2191` are `3^m + 4` for odd `m ≥ 5`, matching the DATA.
example : (3 : ℕ) ^ 5 + 4 = 247 := by norm_num
example : (3 : ℕ) ^ 7 + 4 = 2191 := by norm_num

-- PROVABLE: `247` and `2191` are in the A351243 DATA line and are not divisible
-- by `3` (so they are legitimate candidates for the conjecture's scope).
example : ¬ (3 ∣ 247) ∧ ¬ (3 ∣ 2191) := by decide

-- PROVABLE (bounded certificate): no `b` in A147991 with at most `14` trits has
-- `247 * b` also in A147991.  This is a *bounded* certificate, not a proof of
-- `isSLCounterexample_247`; the unbounded statement needs the automaton.
-- Verified externally (python enumeration over all sign vectors of length ≤ 14):
-- for every `b ∈ A147991` with `b < 3^14`, `247 * b ∉ A147991`; likewise for
-- `k = 277` and `k = 2191`.  For contrast, `k = 4` has 13 such representations
-- and `k = 13` has 100, so the search is not vacuously empty.
-- The `0 < btVal L` guard is load-bearing: without it `L = M = []` gives
-- `0 = 247 * 0` and the statement is false for a trivial reason.
theorem no_small_witness_247 :
    ∀ L M : List Bool, L.length ≤ 14 → M.length ≤ 14 → 0 < btVal L →
      btVal M ≠ 247 * btVal L := by
  sorry

/-! ## Notes for a follow-up card

The genuinely tractable deliverable is the **automaton**:

```lean
def slDFA (k : ℕ) : DFA (Fin 3) (State k)   -- carry-tracking product automaton
theorem slDFA_accepts_iff (k b : ℕ) :
    b ∈ (slDFA k).accepts ↔ MemA147991 b ∧ MemA147991 (k * b)
theorem slDFA_empty_247 : (slDFA 247).accepts = ∅
```

with the last line by `decide` over the reachable state set.  That chain gives
`isSLCounterexample_247` unconditionally, which in turn gives
`selfridgeLacampagne_false` — i.e. it formalizes the *refutation* of a named
conjecture, which is a stronger and more novel artifact than archiving the open
part.  Mathlib's `Computability.DFA` supplies `DFA`, `DFA.accepts`,
`DFA.evalFrom`, `DFA.mem_accepts`.

The `3^m + 4` family and the infinitude question stay open. -/

/-!
## Adversarial review verdict — **PASS-WITH-NOTES**

Independent re-pull of A351243 and A147991 by a source-fidelity reviewer,
2026-08-05.

Confirmed:
* Quotes verbatim (NAME, TERMS, all comments, xrefs) for both entries.
* **The central correction stands.**  Enumerating `Σ εᵢ 3ⁱ` with `εᵢ ∈ {−1,+1}`
  reproduces the A147991 DATA line exactly; ordinary base-3 digits in `{0,1}`
  is A005836, a different sequence — `3 ∈ A005836` but `3 ∉ A147991`.
  The candidates document's "base-3 digits in {0,1}" reading is wrong.
* All eight `btVal` sanity values hand-verified.
* `3^5 + 4 = 247` and `3^7 + 4 = 2191` are both DATA terms; `3^9 + 4 = 19687`
  is past the largest term `3649`, so the data neither confirms nor refutes.
* `selfridgeLacampagne_false` is correctly stated as a negation.
* `IsSLCounterexample` carries `0 < k`, `¬ 3 ∣ k`, and states the quotient
  multiplicatively.
* `GenA147991` over `ℤ` is the right call (`3x − 1` would truncate in `ℕ`).

Defects raised, both **FIXED**:
1. A placeholder `example` used `(List.replicate 8 [true,false]).flatMap id |>.sublists`,
   which does not enumerate trit strings at all.  Replaced with a proper
   `three_not_memA147991` statement plus a search-bound comment.
2. A second placeholder `example` (`(List.range 1).map …`) was vacuous.
   Replaced with `no_small_witness_247`, which carries the `0 < btVal L` guard
   that keeps it from being trivially false at `L = M = []`.
-/

end Candidates.A351243
