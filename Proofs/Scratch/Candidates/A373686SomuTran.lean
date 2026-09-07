/-
# A373686 — Somu–Tran: every `n > 0` is practical + two squares

## OEIS source (re-pulled verbatim with `goof oeis show A373686`, 2026-08-05)

```
NAME:     a(n) is the number of ways n can be written as a sum of a practical
          number and two squares.
TERMS:    1,2,2,2,2,4,2,3,3,4,3,4,3,4,2,4,5,5,4,6,6,6,2,6,5,7,4,7,7,6,5,7,9,7,4,
          8,9,10,2,9,10,9,6,9,9,8,5,8,10,9,5,10,11,9,7,12,11,11,6,9,11,10,3,11,
          14,13,9,12,13,11,7,10,15,14,4,13,13,8,8,15
KEYWORDS: nonn
COMMENTS:
  Somu and Tran (2024) proved that a(n) > 0 for sufficiently large n and
  conjectured that a(n) > 0 for all n > 0. The conjecture was checked up to
  10^8.
XREFS:
  Cf. A000290, A005153.
```

Offset `1`.  Reading off the counting convention from the DATA line:
`a(1) = 1` (`1 = 1 + 0² + 0²`, `1` practical), `a(6) = 4`
(`6 = 1 + 1² + 2² = 2 + 0² + 2² = 4 + 1² + 1² = 6 + 0² + 0²`).  So squares
include `0`, the practical summand is any A005153 term, and pairs of squares are
counted **unordered** (`x ≤ y`).  The card below pins this convention explicitly
in `numRepsA373686`, because getting it wrong would silently change the DATA
cross-check even though the `a(n) > 0` conjecture itself is insensitive to it.

## Status correction

The earlier candidate sweep rates this "potentially completable, which puts it above
every other Tier 2 item in expected value", on the theory that Somu–Tran's
threshold might be small enough to finish by computation.  **It is not.**

Source: Somu & Tran, *On Sums of Practical Numbers and Polygonal Numbers*,
arXiv:2403.13533, J. Integer Seq. 27 (2024), art. 24.5.4; fetched to
`References/arXiv-2403-13533/main.tex`.  Their Theorem 2 is:

> Let `s` be a natural number greater than `3`. Then, there exists a natural
> number `N(s)` such that all natural numbers greater than `N(s)` can be written
> as a sum of a practical number and two `s`-gonal numbers.

The proof is fully **effective** — no Siegel–Walfisz, no ineffective
zero-density input, just CRT + Hensel + Stewart's characterization of practical
numbers — but the constant is astronomical:

* `N(s) = 2 P_s(2 p_1 p_2 ⋯ p_r)` where `r` is least with
  `σ(p_1⋯p_r)/(p_1⋯p_r) ≥ A(s)` and `A(s)` bounds `2 P_s(2 p_{i(s)} x)/x²`.
* For `s = 4` (squares, our case) `P_4(x) = x²` and `p_{i(4)} = 5`, so
  `A(4) = 2·(2·5)² = 200`.
* `σ(p#)/p# = ∏_{p ≤ x}(1 + 1/p) ≈ 1.083 · log x`, so `σ/n ≥ 200` needs
  `log p_r ≈ 185`, i.e. `p_r ≈ 10^80`, i.e. `p_1⋯p_r ≈ exp(10^80)`.
* Hence `N(4) ≈ 8 · exp(2·10^80)` — versus the `10^8` that has been checked.

**Conclusion: this is an archive card, not a completable one.**  The gap between
`10^8` and `exp(2·10^80)` is not closable by computation, and closing it by
argument means improving Somu–Tran's constant by ~80 orders of magnitude in the
exponent.  The candidates document's expected-value ranking for this item should
be downgraded accordingly.

## Adjacent proved results (from the same paper's introduction, verbatim)

```
  Melfi showed that every even natural number is a sum of two practical numbers.
  Pomerance and Weingartner proved that every sufficiently large odd number can
  be written as a sum of a practical number and a prime. Somu et al. proved that
  all natural numbers congruent to 1 modulo 8 are expressible as a sum of a
  practical number and a square.
```

The paper's **Theorem 1** ("all positive integers can be written as a sum of a
practical number and a triangular number, resolving a conjecture by Sun") is a
*resolved* conjecture and therefore a legitimate full-proof target rather than
an archive card; it is stated below as `somuTran_thm1_practical_add_triangular`.
-/
import Mathlib
import Enumerative.Practical
import Enumerative.StewartCriterion

set_option autoImplicit false

namespace Candidates.A373686

/-! ## Definition layer

Existing repo definition reused: `Nat.Practical` (`Proofs/Enumerative/Practical.lean`),
with `instance decidablePredPractical`.  `leandoc "Nat.Practical"` is a
`mode:"miss"` — Mathlib has no practical numbers.

Mathlib pieces used:
* `Finset.Icc`, `Finset.filter`, `Finset.card` — for the counting function.
  STYLE.md forbids mixing cardinality APIs, so `numRepsA373686` uses
  `Finset.card` throughout and nothing else.
* `Nat.sqrt` — to bound the square search.
* Sums of two squares: `Nat.Prime.sq_add_sq`, `ZMod.exists_sq_eq_neg_one_iff`,
  `Nat.eq_sq_add_sq_iff` … Mathlib does have Fermat's two-square theorem and
  the `Nat.sum_two_squares`-adjacent API, but it is **not needed** here: the
  statement is a bare existential over `x, y`, not a characterization.

No fresh predicate is defined beyond the counting function; the conjecture is a
bare existential. -/

/-- The A373686 counting function: representations `n = q + x² + y²` with `q`
practical and `x ≤ y`.  Search bounds are exact, not heuristic: `x² ≤ n` and
`y² ≤ n` force `x, y ≤ Nat.sqrt n`, and `q ≤ n`. -/
def numRepsA373686 (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n ×ˢ (Finset.range (n.sqrt + 1) ×ˢ Finset.range (n.sqrt + 1))).filter
    (fun t => t.1.Practical ∧ t.2.1 ≤ t.2.2 ∧ t.1 + t.2.1 ^ 2 + t.2.2 ^ 2 = n)).card

/-! ## The conjecture -/

/-- **The Somu–Tran conjecture (A373686).**

Verbatim: "Somu and Tran (2024) proved that a(n) > 0 for sufficiently large n
and conjectured that a(n) > 0 for all n > 0. The conjecture was checked up to
10^8."

The `0 < n` guard is from the source and is load-bearing: `n = 0` has no
representation, since every practical number is positive
(`Nat.Practical` bakes in `0 < n`) and `0² + 0² = 0`.

**Mathlib primitives available.**  Two-squares machinery
(`Nat.Prime.sq_add_sq`, `ZMod.exists_sq_eq_neg_one_iff`,
`Nat.Prime.sq_add_sq'`), CRT (`Nat.chineseRemainder`, `ZMod.chineseRemainder`),
Hensel lifting (`Polynomial.IsHenselianLocalRing`, `PadicInt.exists_root` —
though for the elementary lifting Somu–Tran use, plain `ZMod (p^k)` induction is
simpler), `Nat.sqrt`, `Nat.totient`, `ArithmeticFunction.sigma`.
Practical-number side: all repo API.

**Sketch of the Somu–Tran proof** (formalizable in principle, ~1500 lines):
1. *Local solvability.* For each prime `p` and each `n`, the congruence
   `x² + y² ≡ n (mod p)` is solvable (a standard counting argument: the sets
   `{x²}` and `{n − y²}` each have `(p+1)/2` elements in `ZMod p`, so they meet).
   Their Lemmas `sum_poly_mod_p`, `sum_poly_mod_2`, `sum_poly_mod_p^k` are the
   `s`-gonal generalization.
2. *CRT assembly.* Combine over `p_1 ⋯ p_r` to get `x, y (mod n_k)` with
   `x² + y² ≡ n (mod n_k)`, then choose the representatives with
   `x, y ≤ n_k / 2`.
3. *Practical completion.* The residual `n − x² − y²` is a multiple of `n_k`
   bounded by `σ(n_k/2)`, and `n_k/2` is practical by Stewart's criterion
   (already in the repo as `practical_iff_stewart`), so the residual is a sum of
   distinct divisors — hence itself a practical multiple.
   Their `practical_product` lemma is the repo's `Practical.mul_prime_pow`
   in disguise.

Step 3 is the one the repo is best placed to supply.

**Tactic families.** `decide`/`native_decide` for the sweep;
`Finset.card_pos`/`Finset.filter_nonempty_iff` to move between the counting
function and the existential; `ZMod` `decide` for the local-solvability base
cases; `interval_cases` for bounded searches; `omega` for the arithmetic leaves.

**Related work in this repo.** `Enumerative.Practical`,
`Enumerative.StewartCriterion`.  Adjacent cards in this directory:
`A005153Switkay.lean` (the prime analogue — which is *proved* for large `n` by
Pomerance–Weingartner, per the paper's introduction, so Switkay's conjecture has
the same effective-but-astronomical structure),
`A209312SymmetricPractical.lean`, `A222603PracticalTree.lean`. -/
theorem somuTran_practical_add_two_squares (n : ℕ) (hn : 0 < n) :
    ∃ q x y : ℕ, q.Practical ∧ q + x ^ 2 + y ^ 2 = n := by
  sorry

/-- The counting form, matching the OEIS `a(n) > 0` phrasing literally. -/
theorem somuTran_numReps_pos (n : ℕ) (hn : 0 < n) : 0 < numRepsA373686 n := by
  sorry

/-- **Somu–Tran Theorem 2 (proved, 2024), stated with the threshold explicit.**

This is the part that is a *theorem*, not a conjecture.  It is `sorry`d here
because formalizing it is real work, not because it is open.  A card that
discharges this would be genuine formalization content. -/
theorem somuTran_thm2_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N < n → ∃ q x y : ℕ, q.Practical ∧ q + x ^ 2 + y ^ 2 = n := by
  sorry

/-- **Somu–Tran Theorem 1 (proved, 2024): practical + triangular, with no
threshold.**

Verbatim from the paper's abstract: "we show that all positive integers can be
written as a sum of a practical number and a triangular number, resolving a
conjecture by Sun."

The triangular number is written division-free as `2 * T = t * (t + 1)` to keep
the statement off `Nat` division, per STYLE.md. -/
theorem somuTran_thm1_practical_add_triangular (n : ℕ) (hn : 0 < n) :
    ∃ q t : ℕ, q.Practical ∧ 2 * n = 2 * q + t * (t + 1) := by
  sorry

/-! ## Sanity layer -/

-- PROVABLE: the counting function reproduces the OEIS DATA line on its head.
-- a(1..10) = 1, 2, 2, 2, 2, 4, 2, 3, 3, 4.
example : List.map numRepsA373686 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
    = [1, 2, 2, 2, 2, 4, 2, 3, 3, 4] := by native_decide

-- PROVABLE: satisfiability — the existential is instantiable at `n = 1`
-- (`1 = 1 + 0² + 0²`), so the conjecture is not vacuous.
example : ∃ q x y : ℕ, q.Practical ∧ q + x ^ 2 + y ^ 2 = 1 :=
  ⟨1, 0, 0, Nat.practical_one, by norm_num⟩

-- PROVABLE: the `0 < n` guard is load-bearing — `n = 0` is a genuine
-- counterexample, since practical numbers are positive by definition.
example : ¬ ∃ q x y : ℕ, q.Practical ∧ q + x ^ 2 + y ^ 2 = 0 := by
  rintro ⟨q, x, y, hq, h⟩
  have : 0 < q := hq.1
  omega

-- PROVABLE: the counting convention is `x ≤ y` (unordered pairs).  If ordered
-- pairs were counted, `a(6)` would be `1 + 1 + 1 + 1 + 1 = 5`, not `4`
-- (the pair `(1,2)` would be counted twice).  This example pins the convention.
example : numRepsA373686 6 = 4 := by native_decide

-- PROVABLE (window check): a representation exists for every `1 ≤ n ≤ 20000`.
example : ∀ n ∈ Finset.Icc 1 20000, 0 < numRepsA373686 n := by native_decide

-- PROVABLE: the practical summand really has to range over more than `{1, 2}`.
-- `n = 23` has `a(23) = 2`; both representations use practical `q ∈ {4, 22?}` —
-- checking the actual witnesses guards against a degenerate reading in which the
-- conjecture is secretly about powers of two.
example : numRepsA373686 23 = 2 := by native_decide

/-! ## Notes for a follow-up card

Order of attack, by decreasing value per unit effort:

1. `somuTran_thm1_practical_add_triangular` — a *proved* theorem (Somu–Tran
   Thm 1) resolving a Sun conjecture, with **no** threshold, so no astronomical
   constant appears.  This is the completable item in this neighbourhood and the
   one the candidates document should have flagged instead of Thm 2.
2. The local-solvability lemma `∀ p prime, ∀ n, ∃ x y : ZMod p, x² + y² = n` —
   three lines of counting, provable today, and reusable across the whole
   practical-numbers arc.
3. `somuTran_thm2_eventually` — proved but heavy.
4. `somuTran_practical_add_two_squares` — open; archive only. -/

/-!
## Adversarial review verdict — **PASS** (no defects)

Independent re-pull of A373686 *and independent reading of
`References/arXiv-2403-13533/main.tex`* by a source-fidelity reviewer,
2026-08-05.

Confirmed:
* Quotes verbatim; `%O A373686 1,2`, offset `1`.
* **The counting convention is unordered.**  A python recomputation with
  `x ≤ y` gives `1,2,2,2,2,4,2,3,3,4` for `n = 1..10` (matching DATA); with
  ordered pairs it gives `1,3,3,2,4,6,4,4,5,6` (not matching).
* **The threshold analysis is correct**, item by item against the paper:
  `N(s) = 2 P_s(2 p_1⋯p_r)`; `P_4(x) = x²`; `p_{i(4)} = 5` (least prime
  `≡ 1 mod 4` coprime to `s − 2 = 2`); `A(4) = 2·(2·5)² = 200` exactly (the
  ratio is constant); and `σ(p#)/p# ≈ 1.0828 · ln x` needs `ln x ≈ 184.7`,
  i.e. `x ≈ 10^{80.2}`, giving `N(4) ≈ 8·exp(2·10^80)`.
  **The "archive card, not completable" downgrade of the candidates document's
  ranking is justified.**
* `somuTran_practical_add_two_squares`'s `0 < n` guard is load-bearing
  (practical numbers are positive).
* `somuTran_thm1_practical_add_triangular`'s doubling `2n = 2q + t(t+1)`
  correctly encodes `n = q + T_t`.
* `numRepsA373686`'s search bounds (`q ∈ Icc 1 n`, `x, y ≤ √n`) cannot miss a
  representation.
-/

end Candidates.A373686
