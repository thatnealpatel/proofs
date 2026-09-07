import Mathlib

set_option autoImplicit false

/-!
# Rebert's step-doubling walk equals the Chandah-sutra count (OEIS A014701)

`A014701 n` is the number of multiplications used by the Chandah-sutra method
(left-to-right binary exponentiation) to compute `x ^ n`; classically
`A014701 n = ⌊log₂ n⌋ + (binary weight of n) - 1` for `1 ≤ n`.

Jean-Marc Rebert conjectured (OEIS A014701, 2025-05-15):

> `a(n+1)` is the minimal number of steps to go from `0` to `n`, by choosing
> before each step, after the first step, whether to keep the same step length
> or double it. The initial step length is `1`.

This file proves the characterization for positive destinations `1 ≤ n`. The
boundary case `n = 0`, where `a(1) = 0` corresponds to the empty walk, is not
represented by `Reach`.

## Literature status (bounded sweep 2026-08-21)

The closed-form count `A014701 n = ⌊log₂ n⌋ + popcount n − 1` is classical
(Knuth, TAOCP Vol. 2, §4.6.3), and the max-Hamming-weight decomposition identity
is due to Gruber–Holzer (MFCS 2021, Lemma 8). A bounded search of the OEIS entry
and its linked neighborhood, cited primary sources, targeted web results,
limited SeqFan material, and `sequencelib` found no earlier proof of Rebert's
keep-or-double characterization. This records the scope of that search, not an
unrestricted priority claim.

## Main statements

* `NumberComplexity.Reach` — inductive reachability of
  `(position, current step length)` states of the walk;
  `NumberComplexity.Reachable n k` says `n` is reached in `k` steps.
* `NumberComplexity.rebert_conjecture` — for `1 ≤ n`, `k` is the least number of
  steps reaching `n` iff `k + 2 = (Nat.bits (n+1)).length + popCount (n+1)`.
* `NumberComplexity.existsUnique_shortest_decisionWord` — for `1 ≤ n`, exactly
  one data-level keep/double word reaches `n` with minimum total walk length.
* `NumberComplexity.rebert_conjecture_iInf` — the same minimum-step count, phrased with a
  subtype-indexed infimum over the (provably nonempty) set of step counts.

## Implementation notes

The classical count is carried **additively** as `binCost n = A014701 n + 2`:
`binCost n = (Nat.bits n).length + popCount n`.  Since `(Nat.bits n).length`
is `⌊log₂ n⌋ + 1` for `1 ≤ n`, this is the classical formula shifted so that no
`Nat` subtraction ever appears in a statement.  `popCount` is defined here;
Mathlib has `Nat.bits` but no popcount.

The proof runs both ways through the same decomposition
`binCost (q * 2 ^ u + r) = u + binCost q + popCount r` (for `q ≠ 0`, `r < 2 ^ u`):

* lower bound: the invariant of a `k`-step walk standing at `p` with step length
  `2 ^ t` is `2 ^ (t+1) ≤ p + 1` and `binCost (p + 1) ≤ k + 2`, preserved because
  `binCost (P + 2 ^ u) ≤ binCost P + 1` whenever `2 ^ u ≤ P`;
* upper bound: the binary expansion `n + 1 = 2 ^ (t+1) + R` is realised by a walk
  of `t + 1 + popCount R` steps (doublings are shifts, keeps are the `1`-bits).

Route note: the initially considered
interval-with-congruence reachable-set family was not needed — the scalar
potential `binCost` with the single exchange lemma above is already an inductive
invariant of the `Reach` derivation, collapsing the optimality direction to one
induction.
-/

namespace NumberComplexity

/-! ## The binary-exponentiation cost, additively -/

/-- Number of `1` digits in the binary expansion of `n` (the Hamming weight,
OEIS A000120).  Mathlib provides `Nat.bits` but no popcount. -/
def popCount (n : ℕ) : ℕ := (Nat.bits n).count true

/-- `binCost n` is the Chandah-sutra multiplication count `A014701 n` shifted by
two: `binCost n = (Nat.bits n).length + popCount n`, so `binCost n = A014701 n + 2`
for `1 ≤ n`.  The shift keeps every statement free of `Nat` subtraction. -/
def binCost (n : ℕ) : ℕ := (Nat.bits n).length + popCount n

/-- Unfolding lemma for `binCost`. -/
theorem binCost_def (n : ℕ) : binCost n = (Nat.bits n).length + popCount n := rfl

/-- Zero has no `1` bits. -/
@[simp] theorem popCount_zero : popCount 0 = 0 := by simp [popCount, Nat.zero_bits]

/-- One has a single `1` bit. -/
@[simp] theorem popCount_one : popCount 1 = 1 := by decide

/-- Appending a `0` bit does not change the binary weight. -/
@[simp] theorem popCount_two_mul (n : ℕ) : popCount (2 * n) = popCount n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp [popCount, Nat.bit0_bits n hn]

/-- Appending a `1` bit raises the binary weight by one. -/
@[simp] theorem popCount_two_mul_add_one (n : ℕ) :
    popCount (2 * n + 1) = popCount n + 1 := by
  simp [popCount]

/-- Appending a `0` bit to a nonzero number lengthens its binary expansion by one. -/
theorem bits_length_two_mul {n : ℕ} (hn : n ≠ 0) :
    (Nat.bits (2 * n)).length = (Nat.bits n).length + 1 := by
  simp [Nat.bit0_bits n hn]

/-- Appending a `1` bit lengthens the binary expansion by one. -/
theorem bits_length_two_mul_add_one (n : ℕ) :
    (Nat.bits (2 * n + 1)).length = (Nat.bits n).length + 1 := by
  simp

/-- A squaring step of the Chandah-sutra method costs one multiplication. -/
theorem binCost_two_mul {n : ℕ} (hn : n ≠ 0) : binCost (2 * n) = binCost n + 1 := by
  simp only [binCost_def, bits_length_two_mul hn, popCount_two_mul]
  omega

/-- A squaring step followed by a multiplication by `x` costs two multiplications. -/
theorem binCost_two_mul_add_one (n : ℕ) : binCost (2 * n + 1) = binCost n + 2 := by
  simp only [binCost_def, bits_length_two_mul_add_one, popCount_two_mul_add_one]
  omega

/-! ## Splitting a number at a power of two -/

/-- Popcount is additive along the split `q * 2 ^ u + r` with `r < 2 ^ u`. -/
theorem popCount_mul_pow_add (u q r : ℕ) (hr : r < 2 ^ u) :
    popCount (q * 2 ^ u + r) = popCount q + popCount r := by
  induction u generalizing r with
  | zero =>
    have hr0 : r = 0 := by simpa using hr
    subst hr0
    simp
  | succ u ih =>
    have hpow : (2 : ℕ) ^ (u + 1) = 2 * 2 ^ u := by ring
    rcases Nat.even_or_odd r with ⟨r', hr'⟩ | ⟨r', hr'⟩
    · subst hr'
      have hlt : r' < 2 ^ u := by omega
      have hsplit : q * 2 ^ (u + 1) + (r' + r') = 2 * (q * 2 ^ u + r') := by ring
      have hdouble : r' + r' = 2 * r' := by ring
      rw [hsplit, popCount_two_mul, ih r' hlt, hdouble, popCount_two_mul]
    · subst hr'
      have hlt : r' < 2 ^ u := by omega
      have hsplit : q * 2 ^ (u + 1) + (2 * r' + 1) = 2 * (q * 2 ^ u + r') + 1 := by ring
      rw [hsplit, popCount_two_mul_add_one, ih r' hlt, popCount_two_mul_add_one]
      omega

/-- Bit length along the split `q * 2 ^ u + r` with `r < 2 ^ u` and `q ≠ 0`. -/
theorem bits_length_mul_pow_add (u q r : ℕ) (hq : q ≠ 0) (hr : r < 2 ^ u) :
    (Nat.bits (q * 2 ^ u + r)).length = u + (Nat.bits q).length := by
  induction u generalizing r with
  | zero =>
    have hr0 : r = 0 := by simpa using hr
    subst hr0
    simp
  | succ u ih =>
    have hpow : (2 : ℕ) ^ (u + 1) = 2 * 2 ^ u := by ring
    have hqpos : 0 < q * 2 ^ u :=
      Nat.mul_pos (Nat.pos_of_ne_zero hq) (pow_pos (by norm_num) u)
    rcases Nat.even_or_odd r with ⟨r', hr'⟩ | ⟨r', hr'⟩
    · subst hr'
      have hlt : r' < 2 ^ u := by omega
      have hne : q * 2 ^ u + r' ≠ 0 := by omega
      have hsplit : q * 2 ^ (u + 1) + (r' + r') = 2 * (q * 2 ^ u + r') := by ring
      rw [hsplit, bits_length_two_mul hne, ih r' hlt]
      omega
    · subst hr'
      have hlt : r' < 2 ^ u := by omega
      have hsplit : q * 2 ^ (u + 1) + (2 * r' + 1) = 2 * (q * 2 ^ u + r') + 1 := by ring
      rw [hsplit, bits_length_two_mul_add_one, ih r' hlt]
      omega

/-- The decomposition that drives both directions of the main theorem. -/
theorem binCost_mul_pow_add (u q r : ℕ) (hq : q ≠ 0) (hr : r < 2 ^ u) :
    binCost (q * 2 ^ u + r) = u + binCost q + popCount r := by
  simp only [binCost_def, bits_length_mul_pow_add u q r hq hr,
    popCount_mul_pow_add u q r hr]
  omega

/-! ## Two monotonicity facts about `binCost` -/

/-- `A014701` increases by at most one at each step: `binCost (q+1) ≤ binCost q + 1`. -/
theorem binCost_succ_le (q : ℕ) (hq : 1 ≤ q) : binCost (q + 1) ≤ binCost q + 1 := by
  revert hq
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro hq
    rcases Nat.even_or_odd q with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- `q = 2 * m` with `m ≠ 0`: appending a `1` bit costs exactly one more.
      subst hm
      have hm0 : m ≠ 0 := by omega
      have hdouble : m + m = 2 * m := by ring
      rw [hdouble, binCost_two_mul hm0, binCost_two_mul_add_one m]
    · -- `q = 2 * m + 1`: the carry into `2 * (m + 1)` is paid by the inductive step.
      subst hm
      rcases Nat.eq_zero_or_pos m with rfl | hmpos
      · decide
      · have hcarry : 2 * m + 1 + 1 = 2 * (m + 1) := by ring
        have hne : m + 1 ≠ 0 := by omega
        have hstep : binCost (m + 1) ≤ binCost m + 1 := ih m (by omega) hmpos
        rw [hcarry, binCost_two_mul hne, binCost_two_mul_add_one m]
        omega

/-- Adding a power of two no larger than `P` costs at most one extra unit of
`binCost`.  This is the exchange step behind optimality of the binary walk. -/
theorem binCost_add_pow_le {P u : ℕ} (h : 2 ^ u ≤ P) :
    binCost (P + 2 ^ u) ≤ binCost P + 1 := by
  have hpow : 0 < 2 ^ u := pow_pos (by norm_num) u
  obtain ⟨q, r, hq, hr, rfl⟩ : ∃ q r, 1 ≤ q ∧ r < 2 ^ u ∧ P = q * 2 ^ u + r :=
    ⟨P / 2 ^ u, P % 2 ^ u, (Nat.one_le_div_iff hpow).2 h, Nat.mod_lt _ hpow,
      (Nat.div_add_mod' P (2 ^ u)).symm⟩
  have hshift : q * 2 ^ u + r + 2 ^ u = (q + 1) * 2 ^ u + r := by ring
  have elow : binCost (q * 2 ^ u + r) = u + binCost q + popCount r :=
    binCost_mul_pow_add u q r (by omega) hr
  have ehigh : binCost ((q + 1) * 2 ^ u + r) = u + binCost (q + 1) + popCount r :=
    binCost_mul_pow_add u (q + 1) r (by omega) hr
  have estep : binCost (q + 1) ≤ binCost q + 1 := binCost_succ_le q hq
  rw [hshift, ehigh, elow]
  omega

/-! ## The walk -/

/-- `Reach k p s` : after `k` steps the walker started at `0` stands at position
`p`, and the step just taken had length `s` — so the next step has length `s`
(keep) or `2 * s` (double).  The first step has length `1`. -/
inductive Reach : ℕ → ℕ → ℕ → Prop
  | one : Reach 1 1 1
  | keep {k p s : ℕ} : Reach k p s → Reach (k + 1) (p + s) s
  | double {k p s : ℕ} : Reach k p s → Reach (k + 1) (p + 2 * s) (2 * s)

/-- `Reachable n k` : the walker can stand at `n` after exactly `k` steps. -/
def Reachable (n k : ℕ) : Prop := ∃ s, Reach k n s

/-- Every walk has taken at least one step, so it stands at a positive position with a
positive current step length. -/
theorem Reach.pos {k p s : ℕ} (h : Reach k p s) : 1 ≤ p ∧ 1 ≤ k ∧ 1 ≤ s := by
  induction h with
  | one => omega
  | keep _ ih => omega
  | double _ ih => omega

/-- Positions strictly increase, so the walk never returns to `0`; this is the
boundary case `A014701 1 = 0` (the empty walk) that the theorem below excludes by
assuming `1 ≤ n`. -/
theorem not_reachable_zero (k : ℕ) : ¬ Reachable 0 k := by
  rintro ⟨s, h⟩
  have hpos := h.pos
  omega

/-! ## Lower bound: no walk beats the binary method -/

/-- The invariant of the walk.  After `k` steps at position `p` with step length
`s`, the length is a power `2 ^ t`, the position satisfies `2 ^ (t+1) ≤ p + 1`,
and the binary-method cost of `p + 1` is at most `k + 2`. -/
theorem Reach.bound {k p s : ℕ} (h : Reach k p s) :
    ∃ t : ℕ, s = 2 ^ t ∧ 2 ^ (t + 1) ≤ p + 1 ∧ binCost (p + 1) ≤ k + 2 := by
  induction h with
  | one => exact ⟨0, by norm_num, by norm_num, by decide⟩
  | @keep k p s _ ih =>
    obtain ⟨t, rfl, hlo, hcost⟩ := ih
    have hpow : (2 : ℕ) ^ (t + 1) = 2 * 2 ^ t := by ring
    have hle : 2 ^ t ≤ p + 1 := by omega
    have hkey : binCost (p + 1 + 2 ^ t) ≤ binCost (p + 1) + 1 := binCost_add_pow_le hle
    have heq : p + 2 ^ t + 1 = p + 1 + 2 ^ t := by ring
    refine ⟨t, rfl, by omega, ?_⟩
    rw [heq]
    omega
  | @double k p s _ ih =>
    obtain ⟨t, rfl, hlo, hcost⟩ := ih
    have hpow : (2 : ℕ) ^ (t + 1) = 2 * 2 ^ t := by ring
    have hpow2 : (2 : ℕ) ^ (t + 1 + 1) = 2 * 2 ^ (t + 1) := by ring
    have hkey : binCost (p + 1 + 2 ^ (t + 1)) ≤ binCost (p + 1) + 1 :=
      binCost_add_pow_le hlo
    have heq : p + 2 * 2 ^ t + 1 = p + 1 + 2 ^ (t + 1) := by ring
    refine ⟨t + 1, by ring, by omega, ?_⟩
    rw [heq]
    omega

/-- **Optimality.** No walk reaching `n` is shorter than the binary method:
`A014701 (n+1) ≤ k` for every achievable step count `k`. -/
theorem binCost_le_of_reachable {n k : ℕ} (h : Reachable n k) :
    binCost (n + 1) ≤ k + 2 := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨t, -, -, hcost⟩ := hs.bound
  exact hcost

/-! ## Upper bound: the binary expansion is a walk -/

/-- The walk realising the binary expansion `p + 1 = 2 ^ (t+1) + R`: it uses
one initial step, `t` doubling transitions, and `popCount R` extra keeps, and
ends with step length `2 ^ t`. -/
theorem reach_of_binary (t : ℕ) : ∀ R p : ℕ, R < 2 ^ (t + 1) → p + 1 = 2 ^ (t + 1) + R →
    Reach (t + 1 + popCount R) p (2 ^ t) := by
  induction t with
  | zero =>
    intro R p hR hp
    simp only [zero_add, pow_one, pow_zero] at hR hp ⊢
    interval_cases R
    · have hp1 : p = 1 := by omega
      subst hp1
      simpa using Reach.one
    · have hp2 : p = 2 := by omega
      subst hp2
      have hwalk : Reach 2 2 1 := Reach.one.keep
      simpa using hwalk
  | succ t ih =>
    intro R p hR hp
    have hpow0 : (2 : ℕ) ^ (t + 1) = 2 * 2 ^ t := by ring
    have hpow1 : (2 : ℕ) ^ (t + 1 + 1) = 2 * 2 ^ (t + 1) := by ring
    rcases lt_or_ge R (2 ^ (t + 1)) with hb | hb
    · -- The `t+1`-st bit of `R` is `0`: one doubling finishes the walk.
      obtain ⟨p', hp'⟩ : ∃ p', p = p' + 2 ^ (t + 1) := ⟨p - 2 ^ (t + 1), by omega⟩
      have hrec : Reach (t + 1 + popCount R) p' (2 ^ t) := ih R p' hb (by omega)
      have hwalk : Reach (t + 1 + popCount R + 1) (p' + 2 * 2 ^ t) (2 * 2 ^ t) := hrec.double
      have epos : p' + 2 * 2 ^ t = p := by omega
      have elen : (2 : ℕ) * 2 ^ t = 2 ^ (t + 1) := hpow0.symm
      have estep : t + 1 + popCount R + 1 = t + 1 + 1 + popCount R := by omega
      rw [epos, elen, estep] at hwalk
      exact hwalk
    · -- The `t+1`-st bit of `R` is `1`: one doubling and one extra keep.
      obtain ⟨R', rfl⟩ : ∃ R', R = 2 ^ (t + 1) + R' := ⟨R - 2 ^ (t + 1), by omega⟩
      have hR'lt : R' < 2 ^ (t + 1) := by omega
      have hmul : (1 : ℕ) * 2 ^ (t + 1) + R' = 2 ^ (t + 1) + R' := by ring
      have hpc : popCount (2 ^ (t + 1) + R') = popCount R' + 1 := by
        rw [← hmul, popCount_mul_pow_add (t + 1) 1 R' hR'lt, popCount_one]
        omega
      obtain ⟨p', hp'⟩ : ∃ p', p = p' + 2 * 2 ^ (t + 1) := ⟨p - 2 * 2 ^ (t + 1), by omega⟩
      have hrec : Reach (t + 1 + popCount R') p' (2 ^ t) := ih R' p' hR'lt (by omega)
      have hwalk : Reach (t + 1 + popCount R' + 1 + 1) (p' + 2 * 2 ^ t + 2 * 2 ^ t)
          (2 * 2 ^ t) := hrec.double.keep
      have epos : p' + 2 * 2 ^ t + 2 * 2 ^ t = p := by omega
      have elen : (2 : ℕ) * 2 ^ t = 2 ^ (t + 1) := hpow0.symm
      have estep : t + 1 + popCount R' + 1 + 1
          = t + 1 + 1 + popCount (2 ^ (t + 1) + R') := by rw [hpc]; omega
      rw [epos, elen, estep] at hwalk
      exact hwalk

/-- Every `N ≥ 2` splits as a leading power of two plus a strictly smaller remainder,
with the leading exponent at least `1`. -/
theorem exists_pow_decomp {N : ℕ} (hN : 2 ≤ N) :
    ∃ t R : ℕ, R < 2 ^ (t + 1) ∧ N = 2 ^ (t + 1) + R := by
  have hlogpos : 0 < Nat.log 2 N := Nat.log_pos (by norm_num) hN
  obtain ⟨t, ht⟩ : ∃ t, Nat.log 2 N = t + 1 := ⟨Nat.log 2 N - 1, by omega⟩
  have hle : 2 ^ (t + 1) ≤ N := by
    have hself := Nat.pow_log_le_self 2 (show N ≠ 0 by omega)
    rwa [ht] at hself
  have hlt : N < 2 ^ (t + 1 + 1) := by
    have hsucc := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) N
    rwa [ht] at hsucc
  have hpow : (2 : ℕ) ^ (t + 1 + 1) = 2 * 2 ^ (t + 1) := by ring
  exact ⟨t, N - 2 ^ (t + 1), by omega, by omega⟩

/-- The binary walk exists and its length is exactly `binCost (n+1) - 2`, and no walk
is shorter: the least step count is `A014701 (n+1)`. -/
theorem exists_isLeast_reachable {n : ℕ} (hn : 1 ≤ n) :
    ∃ k, k + 2 = binCost (n + 1) ∧ IsLeast {j : ℕ | Reachable n j} k := by
  obtain ⟨t, R, hR, hN⟩ := exists_pow_decomp (show 2 ≤ n + 1 by omega)
  have hb1 : binCost 1 = 2 := by decide
  have hmul : (1 : ℕ) * 2 ^ (t + 1) + R = 2 ^ (t + 1) + R := by ring
  have hsplit := binCost_mul_pow_add (t + 1) 1 R (by norm_num) hR
  rw [hmul, hb1] at hsplit
  refine ⟨t + 1 + popCount R, by rw [hN, hsplit]; omega,
    ⟨⟨2 ^ t, reach_of_binary t R n hR hN⟩, ?_⟩⟩
  intro j hj
  have hjb : binCost (n + 1) ≤ j + 2 := binCost_le_of_reachable hj
  rw [hN, hsplit] at hjb
  omega

/-! ## Rebert's conjecture -/

/-- **Rebert's conjecture** (OEIS A014701, 2025-05-15).  For `1 ≤ n`, a step count
`k` is the *minimum* number of steps of a walk from `0` to `n` — first step of
length `1`, each later step either keeping or doubling the current length — if and
only if `k + 2 = (Nat.bits (n+1)).length + popCount (n+1)`, i.e. iff
`k = A014701 (n+1)`. -/
theorem rebert_conjecture (n k : ℕ) (hn : 1 ≤ n) :
    IsLeast {j : ℕ | Reachable n j} k ↔
      k + 2 = (Nat.bits (n + 1)).length + popCount (n + 1) := by
  obtain ⟨k₀, hk₀, hleast⟩ := exists_isLeast_reachable hn
  constructor
  · intro hk
    have hkk : k = k₀ := hk.unique hleast
    rw [hkk, ← binCost_def]
    exact hk₀
  · intro hk
    rw [← binCost_def] at hk
    have hkk : k = k₀ := by omega
    rw [hkk]
    exact hleast

/-! ## Uniqueness of the shortest decision word

`Reach` is `Prop`-valued, so equality of two `Reach` proofs follows from proof
irrelevance and does not express path uniqueness.  The data-level words below
record each keep/double decision after the mandatory first step.  The evaluator
is equivalent to `Reach`, and its list data makes genuine path uniqueness
stateable.
-/

/-- A keep-or-double choice made after the mandatory first step. -/
inductive WalkDecision where
  | keep
  | double
  deriving DecidableEq, Repr

/-- Final position encoded by a chronological word of decisions after the first step. -/
def decisionPosition : List WalkDecision → ℕ
  | [] => 1
  | WalkDecision.keep :: w => decisionPosition w + 1
  | WalkDecision.double :: w => 2 * decisionPosition w + 1

/-- Final step length encoded by a chronological word of decisions after the first step. -/
def decisionStep : List WalkDecision → ℕ
  | [] => 1
  | WalkDecision.keep :: w => decisionStep w
  | WalkDecision.double :: w => 2 * decisionStep w

example : decisionPosition [] = 1 := rfl
example : decisionPosition [WalkDecision.keep, WalkDecision.double, WalkDecision.keep] = 6 := rfl
example : decisionStep [WalkDecision.keep, WalkDecision.double, WalkDecision.keep] = 2 := rfl

/-- Every decision word has a positive terminal position. -/
@[simp] theorem decisionPosition_pos (w : List WalkDecision) : 1 ≤ decisionPosition w := by
  induction w with
  | nil => simp [decisionPosition]
  | cons a w ih => cases a <;> simp [decisionPosition]

/-- Every decision word has a positive terminal step length. -/
@[simp] theorem decisionStep_pos (w : List WalkDecision) : 1 ≤ decisionStep w := by
  induction w with
  | nil => simp [decisionStep]
  | cons a w ih => cases a <;> simp only [decisionStep] <;> omega

/-- Appending a keep advances the position by the current terminal step length. -/
@[simp] theorem decisionPosition_append_keep (w : List WalkDecision) :
    decisionPosition (w ++ [WalkDecision.keep]) = decisionPosition w + decisionStep w := by
  induction w with
  | nil => simp [decisionPosition, decisionStep]
  | cons a w ih =>
    cases a <;> simp only [List.cons_append, decisionPosition, decisionStep, ih] <;> omega

/-- Appending a keep preserves the terminal step length. -/
@[simp] theorem decisionStep_append_keep (w : List WalkDecision) :
    decisionStep (w ++ [WalkDecision.keep]) = decisionStep w := by
  induction w with
  | nil => simp [decisionStep]
  | cons a w ih => cases a <;> simp [decisionStep, ih]

/-- Appending a double advances the position by twice the terminal step length. -/
@[simp] theorem decisionPosition_append_double (w : List WalkDecision) :
    decisionPosition (w ++ [WalkDecision.double]) = decisionPosition w + 2 * decisionStep w := by
  induction w with
  | nil => simp [decisionPosition, decisionStep]
  | cons a w ih =>
    cases a <;> simp only [List.cons_append, decisionPosition, decisionStep, ih] <;> omega

/-- Appending a double doubles the terminal step length. -/
@[simp] theorem decisionStep_append_double (w : List WalkDecision) :
    decisionStep (w ++ [WalkDecision.double]) = 2 * decisionStep w := by
  induction w with
  | nil => simp [decisionStep]
  | cons a w ih => cases a <;> simp [decisionStep, ih]

/-- Every data-level decision word gives a derivation of the original `Reach` relation. -/
theorem reach_decisionWord (w : List WalkDecision) :
    Reach (w.length + 1) (decisionPosition w) (decisionStep w) := by
  induction w using List.reverseRecOn with
  | nil => simpa [decisionPosition, decisionStep] using Reach.one
  | append_singleton w a ih =>
    cases a with
    | keep => simpa [Nat.add_assoc] using ih.keep
    | double => simpa [Nat.add_assoc] using ih.double

/-- Every `Reach` witness is represented by a data-level keep-or-double word. -/
theorem Reach.exists_decisionWord {k p s : ℕ} (h : Reach k p s) :
    ∃ w : List WalkDecision,
      w.length + 1 = k ∧ decisionPosition w = p ∧ decisionStep w = s := by
  induction h with
  | one => exact ⟨[], by simp, rfl, rfl⟩
  | @keep k p s h ih =>
    obtain ⟨w, hk, hp, hs⟩ := ih
    refine ⟨w ++ [WalkDecision.keep], ?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_singleton]
      omega
    · simp only [decisionPosition_append_keep, hp, hs]
    · simp only [decisionStep_append_keep, hs]
  | @double k p s h ih =>
    obtain ⟨w, hk, hp, hs⟩ := ih
    refine ⟨w ++ [WalkDecision.double], ?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_singleton]
      omega
    · simp only [decisionPosition_append_double, hp, hs]
    · simp only [decisionStep_append_double, hs]

/-- A word is binary-normal when it has no two consecutive keep decisions. -/
def DecisionNormal : List WalkDecision → Prop
  | [] => True
  | WalkDecision.keep :: WalkDecision.keep :: _ => False
  | _ :: w => DecisionNormal w

example : DecisionNormal [] := by simp [DecisionNormal]
example : DecisionNormal [WalkDecision.keep, WalkDecision.double, WalkDecision.keep] := by
  simp [DecisionNormal]
example : ¬ DecisionNormal [WalkDecision.keep, WalkDecision.keep] := by simp [DecisionNormal]

/-- The binary cost of a word's endpoint is at most the word's number of walk
steps, with the same additive shift as `binCost_le_of_reachable`. -/
theorem binCost_decisionPosition_le (w : List WalkDecision) :
    binCost (decisionPosition w + 1) ≤ w.length + 3 := by
  induction w with
  | nil => decide
  | cons a w ih =>
    cases a with
    | keep =>
      have hadd : binCost (decisionPosition w + 1 + 1) ≤
          binCost (decisionPosition w + 1) + 1 :=
        binCost_add_pow_le (u := 0) (by simp)
      simp only [decisionPosition, List.length_cons]
      omega
    | double =>
      have hne : decisionPosition w + 1 ≠ 0 := by omega
      have hcost : binCost (2 * (decisionPosition w + 1)) =
          binCost (decisionPosition w + 1) + 1 := binCost_two_mul hne
      simp only [decisionPosition, List.length_cons]
      rw [show 2 * decisionPosition w + 1 + 1 = 2 * (decisionPosition w + 1) by ring, hcost]
      omega

private theorem binCost_cons_keep_lt {w : List WalkDecision}
    (h : binCost (decisionPosition w + 1) < w.length + 3) :
    binCost (decisionPosition (WalkDecision.keep :: w) + 1) <
      (WalkDecision.keep :: w).length + 3 := by
  have hadd : binCost (decisionPosition w + 1 + 1) ≤
      binCost (decisionPosition w + 1) + 1 :=
    binCost_add_pow_le (u := 0) (by simp)
  simp only [decisionPosition, List.length_cons]
  omega

private theorem binCost_cons_double_lt {w : List WalkDecision}
    (h : binCost (decisionPosition w + 1) < w.length + 3) :
    binCost (decisionPosition (WalkDecision.double :: w) + 1) <
      (WalkDecision.double :: w).length + 3 := by
  have hne : decisionPosition w + 1 ≠ 0 := by omega
  have hcost : binCost (2 * (decisionPosition w + 1)) =
      binCost (decisionPosition w + 1) + 1 := binCost_two_mul hne
  simp only [decisionPosition, List.length_cons]
  rw [show 2 * decisionPosition w + 1 + 1 = 2 * (decisionPosition w + 1) by ring, hcost]
  omega

/-- Any non-normal word is strictly longer than the binary cost of its endpoint. -/
theorem binCost_decisionPosition_lt_of_not_normal (w : List WalkDecision)
    (h : ¬ DecisionNormal w) :
    binCost (decisionPosition w + 1) < w.length + 3 := by
  induction w with
  | nil => simp [DecisionNormal] at h
  | cons a w ih =>
    cases a with
    | double =>
      apply binCost_cons_double_lt
      exact ih (by simpa [DecisionNormal] using h)
    | keep =>
      cases w with
      | nil => simp [DecisionNormal] at h
      | cons b w =>
        cases b with
        | double =>
          apply binCost_cons_keep_lt
          exact ih (by simpa [DecisionNormal] using h)
        | keep =>
          have hbase : binCost (decisionPosition w + 1 + 2) ≤
              binCost (decisionPosition w + 1) + 1 := by
            have hpow : (2 : ℕ) ^ 1 ≤ decisionPosition w + 1 := by
              have hpos := decisionPosition_pos w
              norm_num
              omega
            simpa [pow_one, Nat.add_assoc] using
              (binCost_add_pow_le (P := decisionPosition w + 1) (u := 1) hpow)
          have htail := binCost_decisionPosition_le w
          have heq : decisionPosition
              (WalkDecision.keep :: WalkDecision.keep :: w) + 1 =
              decisionPosition w + 1 + 2 := by
            simp [decisionPosition]
          rw [heq]
          simp only [List.length_cons]
          omega

/-- Optimal decision words are in binary normal form: no scale is kept twice. -/
theorem decisionNormal_of_optimal {n : ℕ} {w : List WalkDecision}
    (hreaches : decisionPosition w = n)
    (hoptimal : w.length + 3 = binCost (n + 1)) : DecisionNormal w := by
  by_contra hnormal
  have hstrict := binCost_decisionPosition_lt_of_not_normal w hnormal
  rw [hreaches, ← hoptimal] at hstrict
  omega

/-- Binary-normal decision words are determined by their terminal position. -/
theorem decisionPosition_injective_of_normal {w₁ w₂ : List WalkDecision}
    (h₁ : DecisionNormal w₁) (h₂ : DecisionNormal w₂)
    (hpos : decisionPosition w₁ = decisionPosition w₂) : w₁ = w₂ := by
  cases w₁ with
  | nil =>
    cases w₂ with
    | nil => rfl
    | cons b w₂ =>
      have hw₂pos := decisionPosition_pos w₂
      cases b <;> simp only [decisionPosition] at hpos <;> omega
  | cons a w₁ =>
    cases a with
    | double =>
      cases w₂ with
      | nil =>
        have hw₁pos := decisionPosition_pos w₁
        simp only [decisionPosition] at hpos
        omega
      | cons b w₂ =>
        cases b with
        | double =>
          simp only [decisionPosition] at hpos
          have htail : decisionPosition w₁ = decisionPosition w₂ := by omega
          have hw : w₁ = w₂ := decisionPosition_injective_of_normal
            (by simpa [DecisionNormal] using h₁)
            (by simpa [DecisionNormal] using h₂) htail
          rw [hw]
        | keep =>
          cases w₂ with
          | nil =>
            have hw₁pos := decisionPosition_pos w₁
            simp only [decisionPosition] at hpos
            omega
          | cons b w₂ =>
            cases b with
            | keep => simp [DecisionNormal] at h₂
            | double =>
              have hw₁pos := decisionPosition_pos w₁
              simp only [decisionPosition] at hpos
              omega
    | keep =>
      cases w₁ with
      | nil =>
        cases w₂ with
        | nil => simp [decisionPosition] at hpos
        | cons b w₂ =>
          cases b with
          | double =>
            have hw₂pos := decisionPosition_pos w₂
            simp only [decisionPosition] at hpos
            omega
          | keep =>
            cases w₂ with
            | nil => rfl
            | cons b w₂ =>
              cases b with
              | keep => simp [DecisionNormal] at h₂
              | double =>
                have hw₂pos := decisionPosition_pos w₂
                simp only [decisionPosition] at hpos
                omega
      | cons b w₁ =>
        cases b with
        | keep => simp [DecisionNormal] at h₁
        | double =>
          cases w₂ with
          | nil =>
            have hw₁pos := decisionPosition_pos w₁
            simp only [decisionPosition] at hpos
            omega
          | cons b w₂ =>
            cases b with
            | double =>
              have hw₁pos := decisionPosition_pos w₁
              have hw₂pos := decisionPosition_pos w₂
              simp only [decisionPosition] at hpos
              omega
            | keep =>
              cases w₂ with
              | nil =>
                have hw₁pos := decisionPosition_pos w₁
                simp only [decisionPosition] at hpos
                omega
              | cons b w₂ =>
                cases b with
                | keep => simp [DecisionNormal] at h₂
                | double =>
                  simp only [decisionPosition] at hpos
                  have htail : decisionPosition w₁ = decisionPosition w₂ := by omega
                  have hw : w₁ = w₂ := decisionPosition_injective_of_normal
                    (by simpa [DecisionNormal] using h₁)
                    (by simpa [DecisionNormal] using h₂) htail
                  rw [hw]
termination_by w₁.length

/-- For every positive target, exactly one keep-or-double decision word follows
its mandatory first step and has shortest possible total walk length. -/
theorem existsUnique_shortest_decisionWord (n : ℕ) (hn : 1 ≤ n) :
    ∃! w : List WalkDecision,
      decisionPosition w = n ∧
        IsLeast {j : ℕ | Reachable n j} (w.length + 1) := by
  obtain ⟨k, hk, hleast⟩ := exists_isLeast_reachable hn
  obtain ⟨s, hs⟩ := hleast.1
  obtain ⟨w, hwlen, hwpos, -⟩ := hs.exists_decisionWord
  have hwoptimal : w.length + 3 = binCost (n + 1) := by omega
  refine ⟨w, ⟨hwpos, ?_⟩, ?_⟩
  · rwa [hwlen]
  · intro v hv
    have hvoptimal : v.length + 3 = binCost (n + 1) := by
      have hvcount := (rebert_conjecture n (v.length + 1) hn).1 hv.2
      rw [← binCost_def] at hvcount
      omega
    apply decisionPosition_injective_of_normal
    · exact decisionNormal_of_optimal hv.1 hvoptimal
    · exact decisionNormal_of_optimal hwpos hwoptimal
    · exact hv.1.trans hwpos.symm

/-- The set of admissible step counts for `1 ≤ n` is nonempty, so the infimum below
is a genuine minimum rather than the junk value `sInf ∅ = 0`. -/
theorem nonempty_reachable {n : ℕ} (hn : 1 ≤ n) : Nonempty {j : ℕ // Reachable n j} := by
  obtain ⟨k₀, -, hleast⟩ := exists_isLeast_reachable hn
  exact ⟨⟨k₀, hleast.1⟩⟩

/-- Rebert's conjecture as an identity about the minimal step count, phrased with a
subtype-indexed infimum over the set of achievable step counts — nonempty, with
its least element supplied by `exists_isLeast_reachable`, which is what computes
the infimum below.  The `1 ≤ n` guard is load-bearing: at `n = 0` the index
subtype is empty and the collapsed infimum satisfies the identity only by
numerical coincidence. -/
theorem rebert_conjecture_iInf (n : ℕ) (hn : 1 ≤ n) :
    (⨅ j : {j : ℕ // Reachable n j}, (j : ℕ)) + 2
      = (Nat.bits (n + 1)).length + popCount (n + 1) := by
  obtain ⟨k₀, hk₀, hleast⟩ := exists_isLeast_reachable hn
  have hrange : (⨅ j : {j : ℕ // Reachable n j}, (j : ℕ)) = sInf {j : ℕ | Reachable n j} := by
    rw [← sInf_range, Subtype.range_coe_subtype]
  rw [hrange, hleast.csInf_eq, ← binCost_def]
  exact hk₀

/-! ## Ground checks against OEIS A014701

The OEIS terms are `a(1..8) = 0, 1, 2, 2, 3, 3, 4, 3`, `a(15) = 6`, `a(16) = 4`,
`a(31) = 8`, `a(32) = 5`, `a(64) = 6`, `a(86) = 9`; `binCost n` must equal `a(n) + 2`.
-/

example : popCount 0 = 0 := by decide
example : popCount 1 = 1 := by decide
example : popCount 7 = 3 := by decide
example : popCount 8 = 1 := by decide
example : popCount 86 = 4 := by decide

example : (Nat.bits 86).length = 7 := by decide

example : binCost 1 = 0 + 2 := by decide
example : binCost 2 = 1 + 2 := by decide
example : binCost 3 = 2 + 2 := by decide
example : binCost 4 = 2 + 2 := by decide
example : binCost 5 = 3 + 2 := by decide
example : binCost 6 = 3 + 2 := by decide
example : binCost 7 = 4 + 2 := by decide
example : binCost 8 = 3 + 2 := by decide
example : binCost 15 = 6 + 2 := by decide
example : binCost 16 = 4 + 2 := by decide
example : binCost 31 = 8 + 2 := by decide
example : binCost 32 = 5 + 2 := by decide
example : binCost 64 = 6 + 2 := by decide
example : binCost 86 = 9 + 2 := by decide

/-! ### The walk itself, at `n = 6`

`0 →1→ 1 →1→ 2 →2→ 4 →2→ 6` uses four steps; `A014701 7 = 4`. -/

example : Reachable 6 4 := ⟨2, Reach.one.keep.double.keep⟩

/-- Six unit steps also reach `6`, so the set of admissible step counts is not a
singleton and the minimality asserted by `rebert_conjecture` has content. -/
example : Reachable 6 6 := ⟨1, Reach.one.keep.keep.keep.keep.keep⟩

/-- Three steps do not suffice: the reachable positions after three steps are
`{3, 4, 5, 7}`. -/
example : ¬ Reachable 6 3 := by
  intro h
  have hb := binCost_le_of_reachable h
  revert hb
  decide

/-- The `n = 6` instance built from scratch — an explicit four-step walk plus the
optimality invariant — independently of `rebert_conjecture`. -/
example : IsLeast {j : ℕ | Reachable 6 j} 4 :=
  ⟨⟨2, Reach.one.keep.double.keep⟩, by
    intro j hj
    have hcost : binCost (6 + 1) = 6 := by decide
    have hb := binCost_le_of_reachable hj
    omega⟩

/-! ### Satisfiability: every hypothesis of `rebert_conjecture` instantiated jointly -/

example : IsLeast {j : ℕ | Reachable 1 j} 1 := (rebert_conjecture 1 1 (by norm_num)).2 (by decide)
example : IsLeast {j : ℕ | Reachable 2 j} 2 := (rebert_conjecture 2 2 (by norm_num)).2 (by decide)
example : IsLeast {j : ℕ | Reachable 3 j} 2 := (rebert_conjecture 3 2 (by norm_num)).2 (by decide)
example : IsLeast {j : ℕ | Reachable 6 j} 4 := (rebert_conjecture 6 4 (by norm_num)).2 (by decide)
example : IsLeast {j : ℕ | Reachable 7 j} 3 := (rebert_conjecture 7 3 (by norm_num)).2 (by decide)
example : IsLeast {j : ℕ | Reachable 15 j} 4 := (rebert_conjecture 15 4 (by norm_num)).2 (by decide)
example : IsLeast {j : ℕ | Reachable 31 j} 5 := (rebert_conjecture 31 5 (by norm_num)).2 (by decide)
example : IsLeast {j : ℕ | Reachable 63 j} 6 := (rebert_conjecture 63 6 (by norm_num)).2 (by decide)
example : IsLeast {j : ℕ | Reachable 85 j} 9 := (rebert_conjecture 85 9 (by norm_num)).2 (by decide)

/-- The shortest decision word to `6` is genuinely unique as list data. -/
example : ∃! w : List WalkDecision,
    decisionPosition w = 6 ∧
      IsLeast {j : ℕ | Reachable 6 j} (w.length + 1) :=
  existsUnique_shortest_decisionWord 6 (by norm_num)

/-- The conjectured value is *forced*: no other `k` is the minimum at `n = 6`. -/
example : ¬ IsLeast {j : ℕ | Reachable 6 j} 5 := by
  intro h
  have hk := (rebert_conjecture 6 5 (by norm_num)).1 h
  revert hk
  decide

#check @rebert_conjecture
#check @existsUnique_shortest_decisionWord
#check @rebert_conjecture_iInf

#print axioms rebert_conjecture
#print axioms existsUnique_shortest_decisionWord
#print axioms rebert_conjecture_iInf
#print axioms nonempty_reachable

end NumberComplexity
