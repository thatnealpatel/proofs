seq:     A161682
claim:   infinitude
status:  open
stmt:    S
proof:   hard
module:  Proofs/Enumerative/PrimesNotCubeMinusSquare.lean
source:  OEIS A161682 comment (unattributed
         conjecture); search bound Daniel
         Starodubtsev, 2020-01-22

CLAIM
  Infinitely many primes are not of the form
  x^3 - y^2 (x, y nonnegative integers per entry
  convention — pin signs/domain from entry when
  writing Lean).

LEAN
  Pure Diophantine vocabulary: Nat.Prime, existential
  over x y. Set.Infinite {p | p.Prime ∧ ¬ exists x y,
  x^3 - y^2 = p} (integer subtraction — use ℤ).

ROUTE
  Open; related to Hall's conjecture and integral
  points on Mordell curves. Per-prime NON-membership
  is even hard to certify (unbounded search), so this
  is statement-archive; no near-term burndown or
  witness activity.

EVIDENCE
  Listed primes have no representation with
  x < 2.2 * 10^9.
