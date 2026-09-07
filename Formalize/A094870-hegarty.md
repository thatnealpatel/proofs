seq:     A094870
claim:   hegarty-density
status:  hard-blocked
stmt:    M
proof:   hard
module:  Proofs/Enumerative/HegartyPermutation.lean
source:  OEIS A094870 comment (P. Hegarty conjecture)

CLAIM
  a(1) = 1; a(n) = minimal positive integer t not yet
  used such that no three of the chosen values form an
  arithmetic progression in order of choice (greedy
  injective no-3AP-in-sequence variant; pin exact
  condition from entry — the constraint involves
  t - a(n-i) vs a(n-i) - a(n-2i)). Known:
  3/8 <= a(n)/n < 3/2. Conjecture (Hegarty):
  a(n)/n -> 1 in OEIS's one-indexed convention. With Lean's zero-indexed
  `a`, the exact residual denominator is `n+1`.

LEAN
  `Proofs/Enumerative/HegartyPermutation.lean` defines the greedy permutation
  and proves permutation, AP-avoidance, and upper-bound infrastructure.
  Accepted main `ce7ab453d8530cbfdd65c41eeb8ea71072f3fc94` publishes
  Proofs/Enumerative/HegartyThreeEighths.lean with
  `A094870.hegarty_three_eighths : ∀ n, 3 * (n + 1) ≤ 8 * A094870.a n`.

ROUTE
  The evidence-backed `3/8` lower bound is complete. The sole residual in
  `Proofs/Enumerative/HegartyPermutation.lean` is exactly
  `A094870.conj_3_2 : Filter.Tendsto (fun n : ℕ => (A094870.a n : ℝ) /
  ((n : ℝ) + 1)) Filter.atTop (nhds 1)`.
EVIDENCE
  Numerics consistent with density 1 in-entry.
