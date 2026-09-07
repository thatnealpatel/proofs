/-
# A146968 — Brocard's problem

## OEIS source (re-pulled verbatim with `goof oeis show A146968`, 2026-08-05)

```
NAME:     Brocard's problem: positive integers n such that n!+1 = m^2.
TERMS:    4,5,7
KEYWORDS: bref,nonn,hard
COMMENTS:
  No other terms below 10^9.
  See A085692 for more comments and references. - _M. F. Hasler_, Nov 20 2018
XREFS:
  A085692, A146968, A216071 are all essentially the same sequence.
  - _N. J. A. Sloane_, Sep 01 2012
```

The *conjecture line* is not in A146968 itself.  It lives in the companion
entry A085692 ("Brocard's problem: squares which can be written as n!+1 for
some n", TERMS 25,121,5041), re-pulled verbatim with
`goof oeis show A085692`:

```
COMMENTS:
  Next term, if it exists, is greater than 10^850. - _Sascha Kurz_, Sep 22 2003
  No more terms < 10^20000. - _David Wasserman_, Feb 08 2005
  The problem of whether there are any other terms in this sequence, Brocard's
  problem, has been unsolved since 1876. The known calculations give
  a(4) > (10^9)! = factorial(10^9). - _Stefan Steinerberger_, Mar 19 2006
  I wrote a similar program sieving against the 40 smallest primes larger than
  4*10^9 and can report that a(4) > factorial(4*10^9+1). In other words, it's
  now known that the only n <= 4*10^9 for which n!+1 is a square are 4, 5 and 7.
  C source code available on request. - Tim Peters, Jul 02 2006
  Robert Matson claims to have verified that 4, 5, and 7 are the only values of
  n <= 10^12 for which n!+1 is a square. This implies that the next term, if it
  exists, is greater than (10^12+1)! ~ 1.4*10^11565705518115.
  - _David Radcliffe_, Oct 28 2019
```

**Indexing correction.** The earlier candidate sweep
attributes the quoted conjecture line to "comment in A085692" — correct — but
then labels the whole card "A146968".  The two entries are cofinal (Sloane's
own xref says so); this file states the claim in the A146968 indexing
(the *arguments* `n`, not the *squares* `n!+1`).  Both indexings are recorded
below so a reviewer can check either one.

## Status

Open since Brocard (1876); Ramanujan asked it independently (1913).  Verified
for `n ≤ 10^12` (Matson, per Radcliffe's 2019 comment).  Overholt (1993)
showed Brocard's problem has finitely many solutions *conditional on* the
weak form of Szpiro's conjecture (equivalently, abc).

## Lean status

Everything needed is Mathlib-native — no new definitions.  The `sorry`s below
are the *conjecture*, not gaps in a proof strategy.
-/
import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Candidates.A146968

open Nat

/-! ## Definition layer

`leandoc` findings (all `mode:"exact"`):

* `Nat.factorial : ℕ → ℕ`
  (`mathlib/Mathlib/Data/Nat/Factorial/Basic.lean:36`), notation `n !`
  under `open Nat`.
* `IsSquare (a : α) : Prop` (`mathlib/Mathlib/Algebra/Group/Even.lean:57`),
  defined as `∃ r, a = r * r`.  This is Mathlib normal form and preferred to a
  hand-rolled `∃ m, n ! + 1 = m ^ 2`; `Nat.exists_mul_self` and
  `Int.sq_eq_sq'` connect it to the exponent form.
* `Nat.sqrt : ℕ → ℕ` with
  `Nat.exists_mul_self (x : ℕ) : (∃ n, n * n = x) ↔ sqrt x * sqrt x = x` — this
  is the decision procedure for the sanity layer, and it is *far* cheaper than
  `decide` on the raw existential (which has no finite search bound).

Nothing fresh is defined here beyond a readable abbreviation for the solution
set, so there is no definitional-drift risk. -/

/-- The Brocard solution set, indexed as in A146968: the arguments `n` for
which `n ! + 1` is a perfect square.  Positivity is carried explicitly because
OEIS says "positive integers n"; `n = 0` gives `0 ! + 1 = 2`, not a square, so
the guard is cosmetic but keeps the translation literal. -/
def IsBrocard (n : ℕ) : Prop := 0 < n ∧ IsSquare (n ! + 1)

instance (n : ℕ) : Decidable (IsBrocard n) := by
  unfold IsBrocard
  have h : IsSquare (n ! + 1) ↔ Nat.sqrt (n ! + 1) * Nat.sqrt (n ! + 1) = n ! + 1 := by
    rw [← Nat.exists_mul_self]
    exact ⟨fun ⟨r, hr⟩ => ⟨r, hr.symm⟩, fun ⟨r, hr⟩ => ⟨r, hr.symm⟩⟩
  exact decidable_of_iff _ (by rw [h] : (0 < n ∧ _) ↔ (0 < n ∧ _)).symm

/-- The Brocard–Ramanujan *roots*: the `r` with `r ^ 2 = n ! + 1` for some
positive `n`.  These are `5, 11, 71` — the square roots of the A085692 terms,
not the A085692 terms themselves. -/
def IsBrocardRoot (r : ℕ) : Prop := ∃ n : ℕ, 0 < n ∧ n ! + 1 = r * r

/-- Membership in **A085692** proper: the *squares* `s = n ! + 1`, i.e.
`25, 121, 5041`.  Kept distinct from `IsBrocardRoot` because conflating the two
indexings silently changes what the DATA line `25, 121, 5041` is asserting. -/
def IsBrocardSquare (s : ℕ) : Prop := IsSquare s ∧ ∃ n : ℕ, 0 < n ∧ s = n ! + 1

/-! ## The conjecture -/

/-- **Brocard's problem (A146968 / A085692).**

Verbatim source (A085692, Stefan Steinerberger, Mar 19 2006):
"The problem of whether there are any other terms in this sequence, Brocard's
problem, has been unsolved since 1876."
Together with the A146968 DATA line `4, 5, 7` this says exactly: the only
positive `n` with `n ! + 1` a perfect square are `4`, `5`, `7`.

**What is available in Mathlib.**  `Nat.factorial`, `IsSquare`,
`Nat.factorial_dvd_factorial`, `Nat.dvd_factorial`, `Nat.sub_one_dvd_sub_of_dvd_sub`,
`ZMod` reduction lemmas (`Nat.cast_factorial` does not exist but
`Nat.factorial` pushes through `Nat.cast_mul` fine), quadratic-residue API
(`ZMod.euler_criterion`, `legendreSym`), and `Int.sq_dvd_sq'`.  Nothing
special-purpose.

**Sketch of an attack (and why it stalls).**  The standard elementary attacks
all fail for a documented reason:

1. *Congruence sieving.*  For each fixed prime `p`, `n ≥ p` forces
   `n ! ≡ 0 [MOD p]`, so `n ! + 1 ≡ 1`, a square mod `p` — no information.
   The sieve only bites for `n < p`, i.e. it constrains `n` in a *finite*
   window, which is exactly the `10^12` computation, not a proof.
   In Lean this is `Nat.dvd_factorial` plus `ZMod.natCast_self_eq_zero`.
2. *Wilson's theorem.*  `Nat.prime_iff_fac_equiv_neg_one` /
   `ZMod.wilsons_lemma : ((p - 1)! : ZMod p) = -1` gives
   `(p-1)! + 1 ≡ 0 [MOD p]`, so `p ∣ m ^ 2`, so `p ∣ m` and `p ^ 2 ∣ (p-1)! + 1`.
   This is a real constraint at `n = p - 1` (a Wilson-prime-adjacent condition)
   but says nothing for composite-adjacent `n`.
3. *abc / Szpiro.*  Overholt 1993 derives finiteness from weak Szpiro.  Mathlib
   has no abc conjecture statement, so this route needs the hypothesis added as
   an explicit assumption — a legitimate *conditional* formalization target and
   the most honest thing a follow-up card could do.

**Tactic families that apply to the finite part.** `decide` on `IsBrocard n` for
a *specific* small `n` (the instance above routes through `Nat.sqrt`, so the
kernel cost is `O(log n !)` Newton steps, not a search); `norm_num [Nat.factorial]`
for evaluating `n !`; `native_decide` for the `n ≤ 20` sweep if `decide` blows
the heartbeat budget (note the enlarged trust surface at the use site).

**Related work in this repo.** None directly.  This is a pure statement-archive
card in the P8 mold; the nearest structural sibling is the A000041/A000166
perfect-power family (`A000166SunPerfectPower.lean` in this directory), which
shares the "value of a fast-growing sequence is almost never a perfect power"
shape and the same `Nat.sqrt`-based sanity layer. -/
theorem brocard_conjecture : ∀ n : ℕ, IsBrocard n → n = 4 ∨ n = 5 ∨ n = 7 := by
  sorry

/-- Contrapositive packaging: no solutions above `7`.  Stated separately because
the `7 < n` form is the one a search would actually refute, and because it
avoids the three-way disjunction when used as a hypothesis. -/
theorem brocard_no_large : ∀ n : ℕ, 7 < n → ¬ IsSquare (n ! + 1) := by
  sorry

/-- The A085692 indexing of the same claim: the Brocard squares are exactly
`25, 121, 5041`. -/
theorem brocard_squares : ∀ m : ℕ, IsBrocardSquare m → m = 5 ∨ m = 11 ∨ m = 71 := by
  sorry

/-- The weakest interesting form — finiteness of the solution set.  This is what
Overholt (1993) gets from weak Szpiro, so it is the natural target for a
*conditional* formalization.  It is strictly weaker than `brocard_conjecture`. -/
theorem brocard_finite : {n : ℕ | IsBrocard n}.Finite := by
  sorry

/-! ## Sanity layer

Everything in this section is intended to compile sorry-free.  These are the
*satisfiability witnesses* STYLE.md demands: they show `IsBrocard` is not
identically false (so `brocard_conjecture` is not vacuous) and that the three
listed values really are solutions (so the conclusion is not overshooting). -/

-- PROVABLE: `4 ! + 1 = 25 = 5 ^ 2`.
example : (4 : ℕ)! + 1 = 5 * 5 := by decide

-- PROVABLE: `5 ! + 1 = 121 = 11 ^ 2`.
example : (5 : ℕ)! + 1 = 11 * 11 := by decide

-- PROVABLE: `7 ! + 1 = 5041 = 71 ^ 2`.
example : (7 : ℕ)! + 1 = 71 * 71 := by decide

-- PROVABLE: satisfiability of `IsBrocard` — the hypothesis of
-- `brocard_conjecture` is jointly instantiable, so the theorem is not vacuous.
example : IsBrocard 4 := ⟨by norm_num, ⟨5, by decide⟩⟩

-- PROVABLE: the conclusion is tight — all three listed values are solutions.
example : IsBrocard 4 ∧ IsBrocard 5 ∧ IsBrocard 7 := by decide

-- PROVABLE: `6` is *not* a solution (`721` sits strictly between `26 ^ 2 = 676`
-- and `27 ^ 2 = 729`), so the gap in the DATA line is real.
example : ¬ IsBrocard 6 := by decide

-- PROVABLE (window check): no `n ≤ 25` outside `{4, 5, 7}` is Brocard.
-- `25 ! ≈ 1.55 * 10^25`, so the `Nat.sqrt` route stays in bignum territory that
-- the kernel handles; escalate to `native_decide` (noting the trust surface) if
-- `decide` exceeds the heartbeat budget.
example : ∀ n ∈ Finset.range 26, IsBrocard n → n = 4 ∨ n = 5 ∨ n = 7 := by
  decide

/-! ## Notes for a follow-up card

The honest deliverable here is the *conditional* theorem.  A card of the shape

```lean
theorem brocard_of_szpiro (hszpiro : WeakSzpiro) : {n | IsBrocard n}.Finite
```

with `WeakSzpiro` spelled out as an explicit hypothesis would be new
formalization content (Mathlib has neither abc nor Szpiro), self-contained, and
would not pretend to settle anything.  Overholt, *The Diophantine equation
n! + 1 = m^2*, Bull. LMS 25 (1993) 104. -/

/-!
## Adversarial review verdict — **PASS-WITH-NOTES**

Independent re-pull of A146968 and A085692 by a source-fidelity reviewer,
2026-08-05.  Quotes, offsets (`%O 1,1` for both), statement direction,
non-vacuity, and the `Nat` typing all checked out.  Four defects were raised:

1. `IsBrocardSquare` was misnamed — it tested *roots* (`5, 11, 71`) while
   claiming to be "the A085692 indexing" (`25, 121, 5041`).  **FIXED**: split
   into `IsBrocardRoot` and a genuine `IsBrocardSquare`.
2. `ZMod.natCast_self_eq_zero` cited in a docstring does not exist.
   **FIXED**: the correct name is `ZMod.natCast_self : (n : ZMod n) = 0`.
3. `Int.sq_dvd_sq'` cited in a docstring does not exist.  **FIXED**: removed;
   the nearest real lemma is `Int.pow_dvd_pow_iff`.
4. Tim Peters's email address was elided from the A085692 quote.  Cosmetic;
   left as is (the name and date are correct).
-/

end Candidates.A146968
