/-
# A007850 — Lava: Giuga numbers solve the "differential equation" `n' = n + 1`

## OEIS source (re-pulled verbatim with `goof oeis show A007850`, 2026-08-05)

```
NAME:     Giuga numbers: composite numbers n such that p divides n/p - 1 for
          every prime divisor p of n.
TERMS:    30,858,1722,66198,2214408306,24423128562,432749205173838,
          14737133470010574,550843391309130318,244197000982499715087866346,
          554079914617070801288578559178,
          1910667181420507984555759916338506
KEYWORDS: nonn,nice,hard,more
COMMENTS (the conjecture and the two comments that bound it):
  Conjecture: Giuga numbers are the solution of the differential equation
  n' = n + 1, where n' is the arithmetic derivative of n.
  - _Paolo P. Lava_, Nov 16 2009
  n is a Giuga number if and only if n' = a*n + 1 for some integer a > 0 (see
  our preprint in arXiv:1103.2298). - _José María Grau Ribas_, Mar 19 2011
  A composite number n is a Giuga number if and only if Sum_{prime p|n} 1/p =
  1/n + an integer. (In fact, all known Giuga numbers n satisfy
  Sum_{prime p|n} 1/p = 1/n + 1.) - _Jonathan Sondow_, Jan 08 2014
  There are no other Giuga numbers with 8 or fewer prime factors. I did an
  exhaustive search using a PARI script which implemented Borwein and
  Girgensohn's method for finding n factor solutions given n - 2 factors.
  - _Fred Schneider_, Jul 04 2006
XREFS:
  Cf. A054377, A216823, A216824, A235137, A235138, A235140, A235363, A236434,
  A326690.
```

## What the conjecture actually is — **one direction, not two**

The candidates document says "one direction (Giuga implies n' = n+1) may be
provable from the definition".  **That is backwards.**  Working it out:

* Giuga ⟹ squarefree.  If `p² ∣ n` then `p ∣ n/p`, so `p ∣ n/p − 1` forces
  `p ∣ 1`.  Contradiction.
* For squarefree `n = p₁⋯p_k`, `n' = Σᵢ n/pᵢ`.  Modulo `pᵢ`, every term with
  `j ≠ i` vanishes, so `n' − 1 ≡ n/pᵢ − 1 (mod pᵢ)`.  Hence
  **`n` Giuga ⟺ `n ∣ n' − 1`**, i.e. `n' = a·n + 1` for some `a ≥ 0`.
  That is exactly Grau Ribas's *proved* comment.
* Conversely, `n' = n + 1` ⟹ `n` squarefree (if `p² ∣ n` then `p ∣ n'` and
  `p ∣ n`, so `p ∣ 1`) ⟹ `n ∣ n' − 1 = n` ⟹ Giuga, and `n` is composite because
  `p' = 1 ≠ p + 1` and `1' = 0 ≠ 2`.

So **`n' = n + 1 ⟹ Giuga` is provable**, and the *open* content is the other
direction: that the `a` in Grau Ribas's `n' = a·n + 1` is always `1`.  Sondow's
parenthetical says the same thing ("all *known* Giuga numbers satisfy
`Σ 1/p = 1/n + 1`").  The card is written to make that asymmetry visible.

## Verification performed before writing this card

`n' = n + 1` and "is a Giuga number" were computed independently for all
`n < 200000`; the two predicates agree everywhere, and both hold exactly on
`{30, 858, 1722, 66198}` — the head of the DATA line.  `n' (30) = 31`,
`n' (858) = 859`, `n' (1722) = 1723`, `n' (66198) = 66199`.

## Status

Open (the `a = 1` direction).  Holds for every KNOWN Giuga number: Schneider's
comment reports the Giuga list complete through 8 prime factors (a completeness
claim about the list, not a verification over composites), and Grau–Oller-Marcén
(arXiv:1103.2298) confirm the thirteen known Giuga numbers satisfy `n' = n + 1`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A007850

/-! ## Definition layer

`leandoc` findings:

* `leandoc "arithmetic derivative"` returns only `ArithmeticFunction` noise —
  **Mathlib has no arithmetic derivative** (A003415).  It is defined fresh here,
  and it is genuinely reusable infrastructure for future cards.
* `Nat.primeFactors (n : ℕ) : Finset ℕ` (`mathlib/Mathlib/Data/Nat/PrimeFin.lean:37`).
* `Nat.factorization (n : ℕ) : ℕ →₀ ℕ` (`mathlib/Mathlib/Data/Nat/Factorization/Defs.lean`).
* `Nat.Squarefree`, `Nat.squarefree_iff_factorization_le_one`.
* `Nat.ord_proj_dvd`, `Nat.ord_compl`, `Nat.factorization_def`.

**Division discipline.**  `ad n = Σ_{p ∈ n.primeFactors} (n / p) * v_p(n)` uses
`ℕ` division, but `p ∈ n.primeFactors → p ∣ n`, so the division is *exact* and
never lands on a junk value.  STYLE.md still wants that visible, so
`ad_eq_sum_of_dvd` (PROVABLE) records the exactness, and an equivalent
division-free characterization `n * ad' n = …` is given for anyone who prefers
to avoid `/` entirely.

Ground truth for the fresh definition (STYLE.md requires it):
`ad 1 = 0`, `ad p = 1` for prime `p`, `ad 4 = 4`, `ad 6 = 5`, `ad 30 = 31`. -/

/-- The **arithmetic derivative** (A003415):
`n' = n · Σ_{p^a ‖ n} a/p = Σ_{p ∣ n} (n/p)·v_p(n)`.
Fresh definition — Mathlib has none. -/
def ad (n : ℕ) : ℕ := ∑ p ∈ n.primeFactors, (n / p) * n.factorization p

/-- `n` is a **Giuga number**: composite, and `p ∣ n/p − 1` for every prime
`p ∣ n`.  The `ℕ` subtraction `n/p − 1` is guarded: `p ∈ n.primeFactors` and
`n` composite force `n/p ≥ 1`, so no truncation.  Stated as `n/p ≡ 1 [MOD p]`
to sidestep the subtraction entirely, which is the Mathlib-normal spelling. -/
def IsGiuga (n : ℕ) : Prop :=
  ¬ n.Prime ∧ 1 < n ∧ ∀ p ∈ n.primeFactors, n / p ≡ 1 [MOD p]

instance : DecidablePred IsGiuga := fun n => by unfold IsGiuga; infer_instance

/-! ## The conjecture -/

/-- **Lava's conjecture (A007850, Paolo P. Lava, Nov 16 2009).**

Verbatim: "Conjecture: Giuga numbers are the solution of the differential
equation n' = n + 1, where n' is the arithmetic derivative of n."

Formalized as the biconditional the wording asserts.  Per the header analysis,
`←` is provable and `→` is the open half; both are also stated separately so a
follow-up card can discharge the provable one without touching the other.

**Mathlib primitives available.**  `Nat.primeFactors`, `Nat.factorization`,
`Nat.Squarefree`, `Nat.squarefree_iff_prime_squarefree`,
`Nat.Coprime.isMultiplicative`-style multiplicativity,
`Nat.sum_primeFactors_...`, `Nat.ModEq` and its API
(`Nat.ModEq.add`, `Nat.modCast` simp set), `Finset.sum_congr`,
`Finset.sum_eq_zero_iff`.

**Sketch of an attack on the open half.**  Giuga ⟹ `n' = a·n + 1` with
`a = Σ_{p ∣ n} 1/p − 1/n` (Sondow's comment, restated).  So `a = 1` iff
`Σ_{p ∣ n} 1/p = 1 + 1/n`.  With `k` prime factors, `Σ 1/p < 1 + 1/n` requires
the primes to be small, and `Σ 1/p > 1 + 1/n` requires them to be large; the
known Giuga numbers all sit exactly on the boundary.  Schneider's exhaustive
search (Borwein–Girgensohn's method) shows the Giuga LIST is complete for
`k ≤ 8`; checking `n' = n + 1` on that finite list (Grau–Oller-Marcén) then
gives `a = 1` for `k ≤ 8`.
A proof for all `k` would need an upper bound on `Σ_{p ∣ n} 1/p` for Giuga `n`,
which is precisely the hard part of the Giuga-conjecture circle.
Concretely: `a ≥ 2` would need `Σ 1/p ≥ 2 + 1/n`, forcing `n` to have at least
`2·3·7·43·1807…` structure (Sylvester's sequence), and ruling that out is open.

**Tactic families.** `decide`/`native_decide` for ground checks (both predicates
are decidable); `Nat.ModEq` lemmas and `omega` for the congruence bookkeeping;
`Finset.sum_congr`/`Finset.sum_eq_single` for the modular collapse of `ad`;
`Nat.Squarefree` API for the squarefree step; `interval_cases` for small `k`.

**Related work in this repo.** None — `ad` is new infrastructure.  It is
immediately reusable for A003415 itself and for the `n' = a·n + b` families
(A099304 and relatives).  The nearest structural sibling in this directory is
`A046094AgohGiuga.lean` (the *other* Giuga conjecture, via Bernoulli numbers). -/
theorem lava_giuga_iff (n : ℕ) (hn : 1 < n) : IsGiuga n ↔ ad n = n + 1 := by
  sorry

/-- The **provable** half: `n' = n + 1` implies `n` is a Giuga number.
This should be discharged, not archived — see the header derivation. -/
theorem isGiuga_of_ad_eq_succ (n : ℕ) (hn : 1 < n) (h : ad n = n + 1) : IsGiuga n := by
  sorry

/-- The **open** half: every Giuga number satisfies `n' = n + 1` exactly (i.e.
the `a` in Grau Ribas's `n' = a·n + 1` is always `1`). -/
theorem ad_eq_succ_of_isGiuga (n : ℕ) (h : IsGiuga n) : ad n = n + 1 := by
  sorry

/-- **Grau Ribas's proved characterization** (arXiv:1103.2298), recorded because
it isolates exactly what is open: the `a` is not pinned.
Verbatim: "n is a Giuga number if and only if n' = a*n + 1 for some integer
a > 0". -/
theorem grauRibas_isGiuga_iff (n : ℕ) (hn : 1 < n) :
    IsGiuga n ↔ ∃ a : ℕ, 0 < a ∧ ad n = a * n + 1 := by
  sorry

/-! ## Sanity layer

STYLE.md requires ground-truth checks on every fresh `def`.  `ad` gets them. -/

-- PROVABLE: `ad` ground truth, A003415 head `0, 0, 1, 1, 4, 1, 5, 1, 12, 6, 7`
-- for `n = 0..10`.
example : ad 0 = 0 := by decide
example : ad 1 = 0 := by decide
example : ad 2 = 1 := by decide
example : ad 3 = 1 := by decide
example : ad 4 = 4 := by decide
example : ad 5 = 1 := by decide
example : ad 6 = 5 := by decide
example : ad 8 = 12 := by decide
example : ad 9 = 6 := by decide
example : ad 10 = 7 := by decide

-- PROVABLE: `ad` is a derivation on primes — `ad p = 1` for every prime `p`.
theorem ad_prime {p : ℕ} (hp : p.Prime) : ad p = 1 := by
  sorry

-- PROVABLE: the Leibniz rule on coprime factors, which is the structural fact
-- that makes `ad` a "derivative" and the engine of every proof below.
theorem ad_mul_coprime {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (h : Nat.Coprime m n) :
    ad (m * n) = ad m * n + m * ad n := by
  sorry

-- PROVABLE: exactness of the division in `ad` — every `p ∈ n.primeFactors`
-- divides `n`, so `n / p` is not a junk value.
theorem ad_eq_sum_of_dvd (n : ℕ) :
    ∀ p ∈ n.primeFactors, p ∣ n := by
  intro p hp
  exact Nat.dvd_of_mem_primeFactors hp

-- PROVABLE: satisfiability — `30` is a Giuga number and `ad 30 = 31`, so
-- `lava_giuga_iff` is not vacuous on either side.
example : IsGiuga 30 := by decide
example : ad 30 = 31 := by decide

-- PROVABLE: the next two DATA terms.  `ad 858 = 859`, `ad 1722 = 1723`.
example : ad 858 = 859 := by native_decide
example : ad 1722 = 1723 := by native_decide
example : IsGiuga 858 ∧ IsGiuga 1722 := by native_decide

-- PROVABLE: Giuga numbers are squarefree — the first step of both directions.
theorem isGiuga_squarefree {n : ℕ} (h : IsGiuga n) : Squarefree n := by
  sorry

-- PROVABLE (window check): `IsGiuga n ↔ ad n = n + 1` for every `n < 200000`,
-- and both hold exactly on `{30, 858, 1722, 66198}`.  Externally verified in
-- python (sympy `factorint`) before this file was written.
--
-- FEASIBILITY WARNING: `IsGiuga` unfolds `Nat.primeFactors`, which goes through
-- `Nat.factors`/trial division, once per `n`; `200000` iterations of that inside
-- `native_decide` may exhaust memory or time.  Start at `Finset.Ico 2 20000`
-- and raise only after timing it.  The claim is true at either bound.
example : ∀ n ∈ Finset.Ico 2 20000, (IsGiuga n ↔ ad n = n + 1) := by native_decide

example : ∀ n ∈ Finset.Ico 2 20000, ad n = n + 1 → n ∈ ({30, 858, 1722} : Finset ℕ) := by
  native_decide

/-! ## Notes for a follow-up card

Order of attack:

1. `ad_prime`, `ad_mul_coprime` — the derivation axioms.  Provable today; these
   turn `ad` from a definition into a usable API and are the prerequisite for
   everything else.
2. `isGiuga_squarefree` — three lines from `p² ∣ n → p ∣ n/p`.
3. `isGiuga_of_ad_eq_succ` — the provable half of Lava's conjecture.  Perhaps
   80 lines given (1) and (2).  **This is the deliverable**: it converts half of
   a named open conjecture into a theorem.
4. `grauRibas_isGiuga_iff` — proved in the literature (arXiv:1103.2298),
   formalizable, and it isolates the remaining open content as "`a = 1`".
5. `ad_eq_succ_of_isGiuga` — open; archive only.

Reference: Grau, Oller-Marcén, *Giuga numbers and the arithmetic derivative*,
arXiv:1103.2298. -/

/-!
## Adversarial review verdict — **PASS-WITH-NOTES**

Independent re-pull of A007850 and A003415, plus `sympy` recomputation of every
numeric claim, 2026-08-05.

Confirmed:
* Lava (Nov 16 2009), Grau Ribas (Mar 19 2011), Sondow (Jan 08 2014) comments
  quoted verbatim with correct attributions.
* **The directionality reversal is CORRECT.**  Every step of the header
  derivation was checked: Giuga ⟹ squarefree; `n' = Σ n/p` for squarefree `n`;
  `n' − 1 ≡ n/pᵢ − 1 (mod pᵢ)`; hence Giuga ⟺ `n ∣ n' − 1` (Grau Ribas);
  and `n' = n + 1 ⟹ squarefree ⟹ Giuga ∧ composite`.  So the candidates
  document has the provable direction backwards, as the header says.
* `ad` reproduces A003415 exactly for `n = 0..16`
  (`0,0,1,1,4,1,5,1,12,6,7,1,16,1,9,8,32`), including the `n = 0, 1` edge cases.
* All thirteen ground-truth examples correct.
* `IsGiuga n ↔ ad n = n + 1` holds for every `n < 200000`, and both hold exactly
  on `{30, 858, 1722, 66198}`; `66198` is a DATA term.
* Mathlib has **no** arithmetic derivative (`leandoc` miss; grep for
  `arithmeticDeriv` empty).
* `n / p ≡ 1 [MOD p]` faithfully renders "p divides n/p − 1" with no `n/p = 0`
  degeneracy (for composite `n` with `p ∈ n.primeFactors`, `n/p ≥ 2`), and
  `¬ n.Prime ∧ 1 < n` is exactly "composite".

Defects raised, both **FIXED**:
1. The Schneider comment was elided with "…" while the header claimed a verbatim
   pull.  Now quoted in full.
2. The `native_decide` sweep over `Finset.Ico 2 200000` calls
   `Nat.primeFactors` 200 000 times and may exhaust the evaluator.  Lowered to
   `20000` with an explicit feasibility warning; the claim is true at either
   bound.
-/

end Candidates.A007850
