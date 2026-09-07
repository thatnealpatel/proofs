seq:     A323653
claim:   karttunen-1-2-3-4
status:  open
stmt:    M
proof:   hard
module:  Proofs/Enumerative/MultiperfectCongruence.lean
source:  OEIS A323653 comments, Antti Karttunen,
         2021-03-20 and 2022-02-18

CLAIM
  A323653 = multiperfect numbers m such that sigma(m)
  is also multiperfect (m ∣ sigma(m) and
  sigma(m) ∣ sigma(sigma(m))). Four conjectures:
  1c. For every term m > 1, sigma(m)/m equals the
      least prime NOT dividing m.
  2.  The sequence is finite.
  3.  A323653 = A007691 ∩ A351458.
  4.  A323653 ⊆ A349745.

LEAN
  Defs needed: IsMultiplyPerfect (one line), the
  A323653 predicate (one line from it), Nat.minFac of
  the complement for 1c: least prime not dividing m is
  Nat.minFac applied to nothing standard — define
    leastNonFactorPrime m := sInf {p | p.Prime ∧
      ¬ p ∣ m}
  Conjectures 3 and 4 additionally need the A351458 /
  A349745 defining predicates pulled from OEIS before
  formalization (not captured in this sweep — fetch
  before writing the Lean file).

ROUTE
  None; conjecture 2 (finiteness) is adjacent to
  odd-perfect-number territory. 1c is checkable per
  known term. Treat as statement-archive, not
  burndown.

EVIDENCE
  Holds for all known terms (few; multiperfects are
  scarce).
