/-
# A174865 / A083207 — Noe's odd-Zumkeller biconditional

## OEIS source (re-pulled verbatim 2026-08-05)

`goof oeis show A174865`:
```
NAME:     Odd abundant numbers whose abundance is even.
TERMS:    945,1575,2205,2835,3465,4095,4725,5355,5775,5985,6435,6615,6825,7245,
          7425,7875,8085,8415,8505,8925,9135,9555,9765,10395,11655,12285,12705,
          12915,13545,14175,14805,15015,15435,16065,16695,17325,17955,18585
KEYWORDS: nonn
COMMENTS:
  This is a subsequence of the odd abundant numbers, A005231. The first term in
  A005231 but not in this sequence is 11025.
XREFS:
  Cf. A156942 (Odd abundant numbers whose abundance is odd).
  Cf. A005231, A033880.
```

**Provenance correction.** The earlier candidate sweep
document attributes the two Noe comments to A174865.  They are *not* there —
A174865 carries exactly one comment, quoted above.  Both Noe lines live in
**A083207** (Zumkeller numbers).  `goof oeis show A083207`:
```
NAME:     Zumkeller or integer-perfect numbers: numbers n whose divisors can be
          partitioned into two disjoint sets with equal sum.
COMMENTS:
  The 229026 Zumkeller numbers less than 10^6 have a maximum difference of 12.
  This leads to the conjecture that any 12 consecutive numbers include at least
  one Zumkeller number. There are 1989 odd Zumkeller numbers less than 10^6;
  they are exactly the odd abundant numbers that have even abundance, A174865.
  - _T. D. Noe_, Mar 31 2010
  ...
  All 205283 odd abundant numbers less than 10^8 that have even abundance
  (see A174865) are Zumkeller numbers. - _T. D. Noe_, Nov 14 2010
```

Note the two Noe comments differ in strength: the 2010-03 line asserts a
*biconditional* (verified below `10^6`), the 2010-11 line asserts only the
*hard direction* (verified below `10^8`).  Both are stated separately below.

## Status

Open.  Phrased empirically in both comments; no later "proved by" comment
appears in either entry.

## Repo adjacency

Strongest in the batch.  `IsZumkeller` and its decidability instance already
live in `Proofs/Enumerative/IsZumkeller.lean`, and the easy direction routes
through `IsZumkeller.two_dvd_sum_divisors` plus
`isZumkeller_iff_two_mul_sum_eq_sum_divisors`, both already proved there.
-/
import Mathlib
import Enumerative.IsZumkeller
import Enumerative.ZumkellerSigmaHalf

set_option autoImplicit false

namespace Candidates.A174865

open Finset

/-! ## Definition layer

Existing repo definitions reused verbatim (nothing re-defined):

* `IsZumkeller (n : ℕ) : Prop := 0 < n ∧ ∃ A ∈ n.divisors.powerset,
    ∑ a ∈ A, a = ∑ d ∈ n.divisors \ A, d`
  — `Proofs/Enumerative/IsZumkeller.lean`, with `instance : DecidablePred IsZumkeller`.

Mathlib definitions found by `leandoc` (all `mode:"exact"`):

* `Nat.Abundant (n : ℕ) : Prop := n < ∑ i ∈ properDivisors n, i`
  (`mathlib/Mathlib/NumberTheory/FactorisationProperties.lean:60`), with
  `deriving Decidable`.
* `Nat.abundant_iff_sum_divisors : Abundant n ↔ 2 * n < ∑ i ∈ n.divisors, i`
  — the bridge from `properDivisors` to `divisors`, needed because
  `IsZumkeller` is phrased over `n.divisors`.  STYLE.md forbids mixing
  cardinality APIs; the same discipline applies to divisor-sum APIs, so every
  statement below is phrased over `n.divisors` and this lemma is the only
  crossing point.
* `Odd (n : α) : Prop` and `Even (n : α) : Prop` — Mathlib normal form,
  preferred to `n % 2 = 1`.

**Fresh definition: "even abundance".**  A033880 is `abundance(n) = σ(n) - 2n`,
an *integer* (negative for deficient `n`).  STYLE.md forbids `↑(a - b)` on `ℕ`,
so the literal reading casts first.  But `2 * n` is always even, so
`Even (σ(n) - 2n)` over `ℤ` is equivalent to `Even (σ(n))` over `ℕ`; the
`ℕ`-level form is the one that plays with the existing Zumkeller API
(`IsZumkeller.two_dvd_sum_divisors`).  Both are given, and their equivalence is
in the PROVABLE sanity layer so the reader can audit the translation. -/

/-- Abundance of `n` as an integer: `σ(n) - 2n` (A033880).  Cast before
subtracting, per STYLE.md. -/
def abundance (n : ℕ) : ℤ := (∑ d ∈ n.divisors, (d : ℤ)) - 2 * (n : ℤ)

/-- Membership in A174865: odd, abundant, and with even abundance.
Phrased with the literal `Even (abundance n)`; `evenAbundance_iff_even_sigma`
below reduces it to `Even (∑ d ∈ n.divisors, d)`. -/
def MemA174865 (n : ℕ) : Prop :=
  Odd n ∧ n.Abundant ∧ Even (abundance n)

instance : DecidablePred MemA174865 := fun n => by
  unfold MemA174865 abundance; infer_instance

/-! ## The conjectures -/

/-- **Noe's biconditional (A083207, T. D. Noe, Mar 31 2010).**

Verbatim: "There are 1989 odd Zumkeller numbers less than 10^6; they are exactly
the odd abundant numbers that have even abundance, A174865."

Formalized: for odd `n`, `n` is Zumkeller iff `n` is abundant with even
abundance.  The oddness hypothesis is *load-bearing*: `MemA174865` bakes `Odd n`
in, so without it the right-hand side is simply false for every even `n` while
the left-hand side is true for infinitely many (`6, 12, 20, 24, …`).  The
oddness restriction is therefore not decoration — it is what makes the
biconditional a claim rather than a falsehood.  The `native_decide` witness
`¬ MemA174865 24 ∧ IsZumkeller 24` in the sanity layer pins this down.

**Mathlib primitives available.** `Nat.Abundant`, `Nat.abundant_iff_sum_divisors`,
`Nat.sum_divisors_eq_sum_properDivisors_add_self`, `Nat.Coprime.sum_divisors_mul`
(multiplicativity of `σ`), `ArithmeticFunction.sigma_one_apply`,
`ArithmeticFunction.isMultiplicative_sigma`, `ArithmeticFunction.sigma_apply`.
For the partition side: `Finset.powerset`, `Finset.sum_sdiff`,
`Finset.sum_add_sum_compl`.

**Sketch of the easy direction (`IsZumkeller n → MemA174865 n`, for odd `n`).**
This one is *not* open and should be proved, not `sorry`d, in a follow-up:
1. `isZumkeller_iff_two_mul_sum_eq_sum_divisors` (already in the repo) gives
   `2 * (∑ a ∈ A, a) = ∑ d ∈ n.divisors, d` for the witnessing `A`, hence
   `Even (∑ d ∈ n.divisors, d)`, hence `Even (abundance n)`.
2. For abundance we need `2 * n < σ(n)`, i.e. `n` is abundant *or perfect*.
   Zumkeller forces `σ(n) ≥ 2n` (each half of the partition contains a subset
   summing to `σ(n)/2 ≥ n`, since `n ∣ n` puts `n` in one half).  Equality
   `σ(n) = 2n` means `n` is perfect; every perfect number `< 10^300` is even
   (open in general!), so **the easy direction is only easy modulo the
   nonexistence of odd perfect numbers**.  This is a genuine subtlety the
   candidates document missed: for odd `n`, `IsZumkeller n → n.Abundant`
   requires ruling out odd perfect numbers, itself a famous open problem.
   The correct honest statement of the easy direction therefore concludes
   `n.Abundant ∨ n.Perfect`; see `noe_easy_direction'` below.

**Sketch of the hard direction (the open content).**  Given odd abundant `n`
with `σ(n)` even, produce a subset of `n.divisors` summing to `σ(n)/2`.  This is
a subset-sum feasibility claim.  The known general tool is the "complete
sequence" criterion: if the divisors `1 = d_1 < ... < d_k = n` satisfy
`d_{i+1} ≤ 1 + ∑_{j ≤ i} d_j` then every value up to `σ(n)` is a subset sum
(this is the Practical/Stewart machinery already in
`Proofs/Enumerative/StewartCriterion.lean`).  Odd abundant numbers need not be
practical (no odd number `> 1` is practical — `Practical.two_dvd`), so the
criterion does not apply directly; the open content is exactly the gap.

**Tactic families.** `decide` (the `Decidable` instances make small cases
mechanical), `native_decide` for the `n ≤ 10^4` sweep, `Finset.sum_congr` /
`Finset.sum_sdiff` for partition manipulation, `omega` for the parity leaves,
`Nat.Coprime.sum_divisors_mul` for multiplicative reductions.

**Related work in this repo.** `Enumerative.IsZumkeller`,
`Enumerative.ZumkellerSigmaHalf` (`Practical.isZumkeller`,
`infinite_setOf_isZumkeller`), `Enumerative.ZumkellerTauSigma`
(`isZumkeller_of_six_dvd_of_not_nine_dvd`),
`Enumerative.MultiperfectZumkeller` (`Perfect.isZumkeller`). -/
theorem noe_odd_zumkeller_iff (n : ℕ) (hodd : Odd n) :
    IsZumkeller n ↔ MemA174865 n := by
  sorry

/-- **Noe's hard direction alone (A083207, T. D. Noe, Nov 14 2010).**

Verbatim: "All 205283 odd abundant numbers less than 10^8 that have even
abundance (see A174865) are Zumkeller numbers."

This is the direction with open content and the larger verification range
(`10^8` vs `10^6`).  Stated separately because it is strictly weaker than
`noe_odd_zumkeller_iff` and is the honest target. -/
theorem noe_hard_direction (n : ℕ) (h : MemA174865 n) : IsZumkeller n := by
  sorry

/-- The easy direction, stated *honestly*: Zumkeller odd numbers are abundant
**or perfect**, with even divisor sum.  Upgrading `∨ n.Perfect` to `n.Abundant`
is equivalent to "there is no odd perfect Zumkeller number", which is implied by
(and, restricted to Zumkeller numbers, essentially equivalent to) the
nonexistence of odd perfect numbers.  This is a genuine theorem, not a
conjecture, and should be discharged rather than archived. -/
theorem noe_easy_direction' (n : ℕ) (hodd : Odd n) (hz : IsZumkeller n) :
    (n.Abundant ∨ n.Perfect) ∧ Even (∑ d ∈ n.divisors, d) := by
  sorry

/-! ## Sanity layer -/

-- PROVABLE: the two readings of "even abundance" agree.  This is the
-- translation audit for `abundance`.
theorem evenAbundance_iff_even_sigma (n : ℕ) :
    Even (abundance n) ↔ Even (∑ d ∈ n.divisors, d) := by
  sorry

-- PROVABLE: `945` is the first term of A174865 and is Zumkeller.
-- σ(945) = 1920, abundance = 1920 - 1890 = 30 (even), 945 odd, abundant.
example : MemA174865 945 := by native_decide

-- PROVABLE: satisfiability — `noe_hard_direction`'s hypothesis is instantiable,
-- so the theorem is not vacuous.
example : IsZumkeller 945 := by native_decide

-- PROVABLE: `11025 = 3^2 * 5^2 * 7^2` is the documented separator ("The first
-- term in A005231 but not in this sequence is 11025"): odd, abundant, but with
-- *odd* abundance — σ(11025) = 13 * 31 * 57 = 22971 is odd, so
-- abundance = 22971 - 22050 = 921.
example : Odd 11025 ∧ Nat.Abundant 11025 ∧ ¬ Even (abundance 11025) := by
  native_decide

-- PROVABLE: and, consistently with Noe, `11025` is not Zumkeller.
example : ¬ IsZumkeller 11025 := by native_decide

-- PROVABLE: the oddness hypothesis in `noe_odd_zumkeller_iff` is load-bearing.
-- `24` is Zumkeller but not in A174865 (it is even), so dropping `Odd n` from
-- `noe_odd_zumkeller_iff` turns a conjecture into a refuted statement.
example : IsZumkeller 24 ∧ ¬ MemA174865 24 := by native_decide

-- PROVABLE (window check): the biconditional holds for every odd `n ≤ 20000`.
-- This is the `native_decide` sweep the candidates document proposed, at a size
-- the evaluator can actually finish; raise the bound only after timing it.
example : ∀ n ∈ Finset.range 20001, Odd n → (IsZumkeller n ↔ MemA174865 n) := by
  native_decide

/-! ## Notes for a follow-up card

Two separable deliverables, in increasing difficulty:

1. `noe_easy_direction'` — genuinely provable today from the existing repo API
   (`isZumkeller_iff_two_mul_sum_eq_sum_divisors` gives the parity;
   `n ∈ n.divisors` plus the partition gives `σ(n) ≥ 2n`).  Roughly 40 lines.
2. `noe_hard_direction` — open.  A partial result within reach: every odd
   abundant `n` with even `σ(n)` *and* `n` divisible by a "sufficiently
   practical" odd part is Zumkeller, via a Stewart-style completeness argument
   on the divisor list.  `Proofs/Enumerative/StewartCriterion.lean` has the
   machinery; the missing piece is an odd analogue of
   `practical_iff_forall_le_sum_divisors`. -/

/-!
## Adversarial review verdict — **PASS-WITH-NOTES**

Independent re-pull of A174865 and A083207, plus `sympy` verification of every
arithmetic claim, by a source-fidelity reviewer, 2026-08-05.

Confirmed:
* The provenance correction is right — A174865 carries exactly one comment, and
  both Noe lines live in A083207.
* `σ(945) = 1920`, `σ(11025) = 13·31·57 = 22971` (odd),
  `abundance(11025) = 921`, `abundance(945) = 30`.
* `Nat.Abundant`, `Nat.abundant_iff_sum_divisors`,
  `ArithmeticFunction.sigma_one_apply`,
  `isZumkeller_iff_two_mul_sum_eq_sum_divisors`,
  `IsZumkeller.two_dvd_sum_divisors` all exist with the cited signatures.
* **The odd-perfect-number subtlety is correct**: Zumkeller forces
  `σ(n) ≥ 2n`, and upgrading `≥` to `>` for odd `n` requires ruling out odd
  perfect numbers.  `noe_easy_direction'` correctly concludes
  `n.Abundant ∨ n.Perfect`.

One cosmetic defect: a prose comment wrote `Practical.two_dvd` where the
declaration is `Nat.Practical.two_dvd`.  Not in code; left as is.
-/

end Candidates.A174865
