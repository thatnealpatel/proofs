/-
  Scratch/GiugaDerivative — the provable half of Lava's conjecture (OEIS A007850):
  every solution of the arithmetic-derivative equation `n' = n + 1` is a Giuga
  number.

  ## Sources (re-pulled verbatim via `oeis show`, 2026-08-20)

  * A003415 (arithmetic derivative): "a(n) = n' = arithmetic derivative of n:
    a(0) = a(1) = 0, a(prime) = 1, a(m*n) = m*a(n) + n*a(m)."  Formula:
    "If n = Product p_i^e_i, a(n) = n * Sum (e_i/p_i)"; equivalently
    n' = Sum_{p | n} v_p(n) * (n/p), the shape used for `ad` below.
  * A007850 (Giuga numbers): "composite numbers n such that p divides n/p - 1
    for every prime divisor p of n."  Terms: 30, 858, 1722, 66198, ...
  * The conjecture (A007850 comment): "Conjecture: Giuga numbers are the
    solution of the differential equation n' = n + 1, where n' is the
    arithmetic derivative of n. - _Paolo P. Lava_, Nov 16 2009".

  ## What is proved here and what is genuinely open

  `isGiuga_of_ad_eq_succ` (sorry-free): `ad n = n + 1 → IsGiuga n`.  Route:
  (a) the equation itself forces `1 < n` (`ad 0 = 0 ≠ 1`, `ad 1 = 0 ≠ 2`);
  (b) solutions are squarefree — `p² ∣ n` gives `p ∣ ad n = n + 1` and `p ∣ n`,
      hence `p ∣ 1`;
  (c) solutions are not prime — `ad p = 1 ≠ p + 1`;
  (d) for squarefree `n`, `ad n = Σ_{p ∣ n} n/p`; modulo a fixed prime `p ∣ n`
      every summand `n/q` with `q ≠ p` is divisible by `p`, so
      `n/p ≡ ad n = n + 1 ≡ 1 (mod p)` — the Giuga condition.

  `ad_eq_succ_of_isGiuga` (archived, the ONE intended sorry): the converse is
  the open content of the conjecture.

  ## Novelty caveat (literature check, 2026-08-20)

  The sorry-free direction is NOT new mathematics: J. M. Grau and
  A. M. Oller-Marcén, "Giuga Numbers and the arithmetic derivative",
  arXiv:1103.2298 (J. Integer Seq. 15 (2012), Article 12.4.1), prove
  "n is a Giuga number if and only if n' = a·n + 1 for some a ∈ ℕ" (their
  ℕ excludes 0 — read `a > 0`); the direction proved here is their `a = 1`
  special case.  This file therefore contributes a first *formalization*,
  not a first proof: Mathlib has no arithmetic derivative and no Giuga
  numbers (`grep -ri` over `.lake/packages`, 2026-08-20), and
  google-deepmind/formal-conjectures states the Giuga-number condition
  (`isWeakGiuga_iff_prime_dvd`, sorry'd) with no arithmetic derivative —
  we found no record of a formalization elsewhere.  The open half is
  exactly "the `a` is always 1": per Grau–Oller-Marcén, refuting it needs a
  Giuga number with `Σ 1/p − 1/n > 1`, known to require more than 59 prime
  factors (they cite Borwein–Wong 1997 for the bound).  Lava's equation
  holds for every KNOWN Giuga number: Schneider's exhaustive search reports
  "There are no other Giuga numbers with 8 or fewer prime factors" (A007850
  comment, Jul 04 2006), and Grau–Oller-Marcén confirm "the thirteen known
  Giuga Numbers satisfy n' = n+1".  (Ufnarovski–Åhlander 2003, the other
  arithmetic-derivative reference, never discusses Giuga numbers or
  `n' = n + 1`, though their Corollary 2 — n squarefree iff gcd(n, n') = 1 —
  is the squarefreeness step Grau–Oller-Marcén cite.)

  ## Certification notes

  Kernel `decide` cannot evaluate `Nat.primeFactors` — `Nat.primeFactorsList`
  is defined by well-founded recursion, on which kernel reduction gets stuck —
  so the ground-truth layer is algebraic: numerals are split into explicit
  prime products and pushed through `ad_prime` / `ad_prime_pow` /
  `ad_mul_coprime` / `Nat.primeFactors_mul`.  The only `decide` uses are on
  explicit finset literals and numeral modular arithmetic.  No `native_decide`,
  no range sweeps.
-/
import Mathlib

set_option autoImplicit false

namespace GiugaDerivative

/-! ## The arithmetic derivative (A003415) -/

/-- The **arithmetic derivative** (A003415): `ad n = Σ_{p ∣ n} (n/p) · v_p(n)`,
so `ad 0 = ad 1 = 0`, `ad p = 1` on primes, and the Leibniz rule holds — the
coprime case is what is proved below (`ad_mul_coprime`); the general case is
true but not formalized here.  The `ℕ`-division `n / p` is exact, never a
junk value: `p ∈ n.primeFactors` forces `p ∣ n`.  Mathlib has no arithmetic
derivative (`grep -ri` over `.lake/packages`, 2026-08-20); fresh minimal
reusable infrastructure, definition shape shared with
`Scratch/Candidates/A007850LavaGiuga.lean`. -/
def ad (n : ℕ) : ℕ := ∑ p ∈ n.primeFactors, n / p * n.factorization p

/-- `ad 0 = 0`, matching A003415's `a(0) = 0`. -/
theorem ad_zero : ad 0 = 0 := by simp [ad]

/-- `ad 1 = 0`, matching A003415's `a(1) = 0`. -/
theorem ad_one : ad 1 = 0 := by simp [ad]

/-- `ad p = 1` on primes, matching A003415's `a(prime) = 1`. -/
theorem ad_prime {p : ℕ} (hp : p.Prime) : ad p = 1 := by
  unfold ad
  rw [hp.primeFactors, Finset.sum_singleton, Nat.div_self hp.pos,
    hp.factorization_self, one_mul]

/-- Power rule on prime powers: `ad (p ^ k) = k · p ^ (k - 1)` for `k ≠ 0`. -/
theorem ad_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    ad (p ^ k) = k * p ^ (k - 1) := by
  have hdiv : p ^ k / p = p ^ (k - 1) := by
    conv_lhs => rw [show k = k - 1 + 1 by omega]
    rw [pow_succ, Nat.mul_div_cancel _ hp.pos]
  unfold ad
  rw [Nat.primeFactors_pow p hk, hp.primeFactors, Finset.sum_singleton,
    hp.factorization_pow, Finsupp.single_eq_same, hdiv, mul_comm]

/-- **Leibniz rule** on coprime factors: `ad (m·n) = ad m · n + m · ad n`.
Together with `ad_prime` and `ad_prime_pow` this pins `ad` on every explicitly
factored numeral, which is how the ground-truth layer below is certified
(kernel `decide` cannot unfold `Nat.primeFactors`). -/
theorem ad_mul_coprime {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (h : Nat.Coprime m n) :
    ad (m * n) = ad m * n + m * ad n := by
  have key : ∀ a b : ℕ, a ≠ 0 → b ≠ 0 → Nat.Coprime a b →
      ∀ p ∈ a.primeFactors,
        a * b / p * (a * b).factorization p = a / p * a.factorization p * b := by
    intro a b ha hb hab p hp
    have hpa : p ∣ a := Nat.dvd_of_mem_primeFactors hp
    have hbf : b.factorization p = 0 := by
      have hpb : p ∉ b.primeFactors :=
        Finset.disjoint_left.mp hab.disjoint_primeFactors hp
      rw [← Nat.support_factorization] at hpb
      exact Finsupp.notMem_support_iff.mp hpb
    simp only [Nat.factorization_mul ha hb, Finsupp.add_apply, hbf, add_zero]
    rw [mul_comm a b, Nat.mul_div_assoc b hpa]
    ring
  unfold ad
  rw [Nat.primeFactors_mul hm hn, Finset.sum_union h.disjoint_primeFactors,
    Finset.sum_mul, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun p hp => key m n hm hn h p hp
  · refine Finset.sum_congr rfl fun p hp => ?_
    have hswap := key n m hn hm h.symm p hp
    rw [mul_comm n m] at hswap
    rw [hswap]
    ring

/-! ## Giuga numbers (A007850) -/

/-- `n` is a **Giuga number** (A007850): composite — `¬ n.Prime ∧ 1 < n` — and
`p ∣ n/p − 1` for every prime `p ∣ n`, spelled `n / p ≡ 1 [MOD p]` to avoid
`ℕ`-subtraction.  The spellings agree: `p ∈ n.primeFactors` gives `p ∣ n`, so
`n / p` is an exact quotient with `1 ≤ n / p`. -/
def IsGiuga (n : ℕ) : Prop :=
  ¬n.Prime ∧ 1 < n ∧ ∀ p ∈ n.primeFactors, n / p ≡ 1 [MOD p]

/-- `IsGiuga` is decidable in principle; kernel `decide` CANNOT use this
instance — `Nat.primeFactorsList` is well-founded recursion and does not
reduce (it works via `#eval`/compiler only).  Do not reach for
`native_decide`; rewrite `primeFactors` to a literal first, as the
certificates below do. -/
instance : DecidablePred IsGiuga := fun n => by unfold IsGiuga; infer_instance

/-! ## The provable half: `ad n = n + 1 → IsGiuga n` -/

/-- A prime `p ∣ n` also divides the exact quotient `n / q` for any other
prime `q ∣ n`. -/
theorem prime_dvd_div {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (hpn : p ∣ n) (hqn : q ∣ n) : p ∣ n / q := by
  have hdvd : p ∣ n / q * q := by
    rw [Nat.div_mul_cancel hqn]
    exact hpn
  rcases hp.dvd_mul.mp hdvd with hd | hd
  · exact hd
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp hq).mp hd) hne

/-- If `p² ∣ n` then `p` divides every summand of `ad n`, hence `p ∣ ad n`:
the `q = p` summand contains `n/p` (divisible by `p` since `p² ∣ n`), and every
`q ≠ p` summand contains `n/q` (divisible by `p` by `prime_dvd_div`). -/
theorem dvd_ad_of_sq_dvd {p n : ℕ} (hp : p.Prime) (hsq : p * p ∣ n) :
    p ∣ ad n := by
  have hpn : p ∣ n := (dvd_mul_right p p).trans hsq
  refine Finset.dvd_sum fun q hq => ?_
  have hqn : q ∣ n := Nat.dvd_of_mem_primeFactors hq
  rcases eq_or_ne p q with rfl | hne
  · exact dvd_mul_of_dvd_left ((Nat.dvd_div_iff_mul_dvd hqn).mpr hsq) _
  · exact dvd_mul_of_dvd_left
      (prime_dvd_div hp (Nat.prime_of_mem_primeFactors hq) hne hpn hqn) _

/-- Solutions of `ad n = n + 1` are squarefree: `p² ∣ n` would give
`p ∣ ad n = n + 1` alongside `p ∣ n`, hence `p ∣ 1`. -/
theorem squarefree_of_ad_eq_succ {n : ℕ} (h : ad n = n + 1) : Squarefree n := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hsq
  have hpn : p ∣ n := (dvd_mul_right p p).trans hsq
  have hpsucc : p ∣ n + 1 := h ▸ dvd_ad_of_sq_dvd hp hsq
  have hp1 : p ∣ 1 := by
    have hd : p ∣ n + 1 - n := Nat.dvd_sub hpsucc hpn
    simpa using hd
  exact hp.ne_one (Nat.dvd_one.mp hp1)

/-- On squarefree `n` the arithmetic derivative collapses to `Σ_{p ∣ n} n/p`:
every exponent `v_p(n)` is exactly `1`. -/
theorem ad_eq_sum_div_of_squarefree {n : ℕ} (hsf : Squarefree n) :
    ad n = ∑ p ∈ n.primeFactors, n / p := by
  unfold ad
  refine Finset.sum_congr rfl fun p hp => ?_
  have hle : n.factorization p ≤ 1 :=
    (Nat.squarefree_iff_factorization_le_one hsf.ne_zero).mp hsf p
  have hpos : 0 < n.factorization p :=
    (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hsf.ne_zero
      (Nat.dvd_of_mem_primeFactors hp)
  have hone : n.factorization p = 1 := le_antisymm hle hpos
  rw [hone, mul_one]

/-- **The provable half of Lava's conjecture (A007850) — sorry-free.**
Every solution of the arithmetic-derivative equation `n' = n + 1` is a Giuga
number.  No side conditions: `n = 0`, `n = 1`, and primes are excluded by the
equation itself.

Proved as the `a = 1` case of "Giuga ⟺ `n' = a·n + 1`" by Grau and
Oller-Marcén (arXiv:1103.2298); to our knowledge this is its first
formalization. -/
theorem isGiuga_of_ad_eq_succ {n : ℕ} (h : ad n = n + 1) : IsGiuga n := by
  have hn : 1 < n := by
    by_contra hle
    have hle' : n ≤ 1 := Nat.le_of_not_lt hle
    interval_cases n
    · rw [ad_zero] at h
      omega
    · rw [ad_one] at h
      omega
  have hsf : Squarefree n := squarefree_of_ad_eq_succ h
  have hnp : ¬n.Prime := by
    intro hp
    rw [ad_prime hp] at h
    omega
  refine ⟨hnp, hn, fun p hp => ?_⟩
  have hpP : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  have hsum : n / p + ∑ q ∈ n.primeFactors.erase p, n / q = n + 1 := by
    rw [Finset.add_sum_erase _ _ hp, ← ad_eq_sum_div_of_squarefree hsf]
    exact h
  have hSdvd : p ∣ ∑ q ∈ n.primeFactors.erase p, n / q :=
    Finset.dvd_sum fun q hq =>
      prime_dvd_div hpP
        (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hq))
        (Finset.ne_of_mem_erase hq).symm hpn
        (Nat.dvd_of_mem_primeFactors (Finset.mem_of_mem_erase hq))
  have hmod : n / p + ∑ q ∈ n.primeFactors.erase p, n / q ≡ n / p + 0 [MOD p] :=
    Nat.ModEq.add_left _ (Nat.modEq_zero_iff_dvd.mpr hSdvd)
  have hmod' : n + 1 ≡ 0 + 1 [MOD p] :=
    Nat.ModEq.add_right _ (Nat.modEq_zero_iff_dvd.mpr hpn)
  calc n / p = n / p + 0 := (add_zero _).symm
    _ ≡ n / p + ∑ q ∈ n.primeFactors.erase p, n / q [MOD p] := hmod.symm
    _ = n + 1 := hsum
    _ ≡ 0 + 1 [MOD p] := hmod'
    _ = 1 := zero_add 1

/-! ## The open half, archived -/

/-- **The open half of Lava's conjecture (A007850) — the ONE intended sorry.**

Verbatim conjecture: "Giuga numbers are the solution of the differential
equation n' = n + 1" (Paolo P. Lava, Nov 16 2009).  This direction — every
Giuga number satisfies `n' = n + 1` — is the open content.  Grau–Oller-Marcén
(arXiv:1103.2298) prove `IsGiuga n ↔ ∃ a > 0, ad n = a·n + 1`; what is open is
that the multiplier `a` is always `1`, equivalently that every Giuga number
satisfies `Σ_{p ∣ n} 1/p − 1/n = 1`.  A counterexample must have more than 59
prime factors (Grau–Oller-Marcén, citing Borwein–Wong 1997).  The statement
holds for every Giuga number with at most 8 prime factors: Schneider's
exhaustive search reports "There are no other Giuga numbers with 8 or fewer
prime factors" (A007850 comment, Jul 04 2006), and Grau–Oller-Marcén confirm
the thirteen known Giuga numbers satisfy `n' = n + 1`.  Archived, not
attempted. -/
theorem ad_eq_succ_of_isGiuga {n : ℕ} (h : IsGiuga n) : ad n = n + 1 := by
  sorry

/-- **Lava's conjecture (A007850), stated as the biconditional the OEIS
comment asserts.**  The `←` direction is the sorry-free
`isGiuga_of_ad_eq_succ`; the `→` direction is the archived open half, so this
statement's axiom report includes `sorryAx` by design — it is the conjecture,
not a result.  No `1 < n` guard is needed: for `n ∈ {0, 1}` both sides are
false (`IsGiuga` requires `1 < n`; `ad 0 = 0 ≠ 1` and `ad 1 = 0 ≠ 2`). -/
theorem lava_conjecture (n : ℕ) : IsGiuga n ↔ ad n = n + 1 :=
  ⟨ad_eq_succ_of_isGiuga, isGiuga_of_ad_eq_succ⟩

/-! ## Ground truth for `ad` (STYLE.md def-check layer)

A003415 head: `a(0..12) = 0, 0, 1, 1, 4, 1, 5, 1, 12, 6, 7, 1, 16`.
All certified algebraically — see the header's certification notes. -/

example : ad 0 = 0 := ad_zero
example : ad 1 = 0 := ad_one
example : ad 2 = 1 := ad_prime (by norm_num)
example : ad 3 = 1 := ad_prime (by norm_num)
example : ad 5 = 1 := ad_prime (by norm_num)
example : ad 7 = 1 := ad_prime (by norm_num)
example : ad 11 = 1 := ad_prime (by norm_num)

example : ad 4 = 4 := by
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ad_prime_pow (by norm_num) (by norm_num)]
  norm_num

example : ad 8 = 12 := by
  rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ad_prime_pow (by norm_num) (by norm_num)]
  norm_num

example : ad 9 = 6 := by
  rw [show (9 : ℕ) = 3 ^ 2 by norm_num, ad_prime_pow (by norm_num) (by norm_num)]
  norm_num

example : ad 6 = 5 := by
  rw [show (6 : ℕ) = 2 * 3 by norm_num,
    ad_mul_coprime (by norm_num) (by norm_num) (by norm_num),
    ad_prime (by norm_num), ad_prime (by norm_num)]

example : ad 10 = 7 := by
  rw [show (10 : ℕ) = 2 * 5 by norm_num,
    ad_mul_coprime (by norm_num) (by norm_num) (by norm_num),
    ad_prime (by norm_num), ad_prime (by norm_num)]

example : ad 12 = 16 := by
  rw [show (12 : ℕ) = 4 * 3 by norm_num,
    ad_mul_coprime (by norm_num) (by norm_num) (by norm_num),
    show (4 : ℕ) = 2 ^ 2 by norm_num, ad_prime_pow (by norm_num) (by norm_num),
    ad_prime (by norm_num)]
  norm_num

/-! ## Witness layer: 30, 858, 1722 satisfy both predicates -/

/-- `ad 30 = 31`: the first Giuga number solves `n' = n + 1` (A007850 head). -/
theorem ad_30 : ad 30 = 31 := by
  have h15 : ad 15 = 8 := by
    rw [show (15 : ℕ) = 3 * 5 by norm_num,
      ad_mul_coprime (by norm_num) (by norm_num) (by norm_num),
      ad_prime (by norm_num), ad_prime (by norm_num)]
  rw [show (30 : ℕ) = 2 * 15 by norm_num,
    ad_mul_coprime (by norm_num) (by norm_num) (by norm_num),
    ad_prime (by norm_num), h15]

/-- `ad 858 = 859`: the second Giuga number solves `n' = n + 1`. -/
theorem ad_858 : ad 858 = 859 := by
  have h143 : ad 143 = 24 := by
    rw [show (143 : ℕ) = 11 * 13 by norm_num,
      ad_mul_coprime (by norm_num) (by norm_num) (by norm_num),
      ad_prime (by norm_num), ad_prime (by norm_num)]
  have h429 : ad 429 = 215 := by
    rw [show (429 : ℕ) = 3 * 143 by norm_num,
      ad_mul_coprime (by norm_num) (by norm_num) (by norm_num),
      ad_prime (by norm_num), h143]
  rw [show (858 : ℕ) = 2 * 429 by norm_num,
    ad_mul_coprime (by norm_num) (by norm_num) (by norm_num),
    ad_prime (by norm_num), h429]

/-- `ad 1722 = 1723`: the third Giuga number solves `n' = n + 1`. -/
theorem ad_1722 : ad 1722 = 1723 := by
  have h287 : ad 287 = 48 := by
    rw [show (287 : ℕ) = 7 * 41 by norm_num,
      ad_mul_coprime (by norm_num) (by norm_num) (by norm_num),
      ad_prime (by norm_num), ad_prime (by norm_num)]
  have h861 : ad 861 = 431 := by
    rw [show (861 : ℕ) = 3 * 287 by norm_num,
      ad_mul_coprime (by norm_num) (by norm_num) (by norm_num),
      ad_prime (by norm_num), h287]
  rw [show (1722 : ℕ) = 2 * 861 by norm_num,
    ad_mul_coprime (by norm_num) (by norm_num) (by norm_num),
    ad_prime (by norm_num), h861]

/-- `30 = 2·3·5` is a Giuga number: direct certificate from the definition. -/
theorem isGiuga_30 : IsGiuga 30 := by
  have h2 : Nat.Prime 2 := by norm_num
  have h3 : Nat.Prime 3 := by norm_num
  have h5 : Nat.Prime 5 := by norm_num
  have hpf : (30 : ℕ).primeFactors = {2, 3, 5} := by
    rw [show (30 : ℕ) = 2 * 3 * 5 by norm_num,
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      h2.primeFactors, h3.primeFactors, h5.primeFactors]
    decide
  refine ⟨by norm_num, by norm_num, ?_⟩
  rw [hpf]
  decide

/-- `858 = 2·3·11·13` is a Giuga number: direct certificate. -/
theorem isGiuga_858 : IsGiuga 858 := by
  have h2 : Nat.Prime 2 := by norm_num
  have h3 : Nat.Prime 3 := by norm_num
  have h11 : Nat.Prime 11 := by norm_num
  have h13 : Nat.Prime 13 := by norm_num
  have hpf : (858 : ℕ).primeFactors = {2, 3, 11, 13} := by
    rw [show (858 : ℕ) = 2 * 3 * 11 * 13 by norm_num,
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      h2.primeFactors, h3.primeFactors, h11.primeFactors, h13.primeFactors]
    decide
  refine ⟨by norm_num, by norm_num, ?_⟩
  rw [hpf]
  decide

/-- `1722 = 2·3·7·41` is a Giuga number: direct certificate. -/
theorem isGiuga_1722 : IsGiuga 1722 := by
  have h2 : Nat.Prime 2 := by norm_num
  have h3 : Nat.Prime 3 := by norm_num
  have h7 : Nat.Prime 7 := by norm_num
  have h41 : Nat.Prime 41 := by norm_num
  have hpf : (1722 : ℕ).primeFactors = {2, 3, 7, 41} := by
    rw [show (1722 : ℕ) = 2 * 3 * 7 * 41 by norm_num,
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      h2.primeFactors, h3.primeFactors, h7.primeFactors, h41.primeFactors]
    decide
  refine ⟨by norm_num, by norm_num, ?_⟩
  rw [hpf]
  decide

/-! ## Satisfiability of the main theorem's hypothesis (STYLE.md)

The two certification routes agree: pushing the `ad`-side witnesses through
`isGiuga_of_ad_eq_succ` reproduces the direct `IsGiuga` certificates, so the
hypothesis `ad n = n + 1` is jointly instantiated at three concrete models and
the theorem is not vacuous. -/

example : IsGiuga 30 := isGiuga_of_ad_eq_succ ad_30
example : IsGiuga 858 := isGiuga_of_ad_eq_succ ad_858
example : IsGiuga 1722 := isGiuga_of_ad_eq_succ ad_1722

/-! ## Axiom audit

Expected: the sorry-free layer reports at most
`{propext, Classical.choice, Quot.sound}`; `lava_conjecture` and
`ad_eq_succ_of_isGiuga` additionally report `sorryAx` — they carry the
archived open half by design. -/

#print axioms isGiuga_of_ad_eq_succ
#print axioms ad_mul_coprime
#print axioms isGiuga_30
#print axioms lava_conjecture

end GiugaDerivative
