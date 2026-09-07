seq:     A000001
claim:   cdo-gnu-iteration
status:  open
stmt:    M
proof:   hard
module:  Proofs/GroupCount/CdoIteration.lean
source:  OEIS A000001 comment recorded by Muniru A
         Asiru, 2017-11-19; conjecture from Conway-
         Dietrich-O'Brien 2008

CLAIM
  gnu(n) = number of isomorphism classes of groups of
  order n. Conjecture: for every n, the iteration
  n -> gnu(n) -> gnu(gnu(n)) -> ... eventually
  reaches 1 (and stays).

LEAN
  gnu is definable WITHOUT classification (this
  corrects an L rating): group structures on Fin n
  form a Fintype; isomorphism between two structures
  is decidable by finite search; so
    gnu n := Nat.card (Quotient (isoSetoid n))
  is a computable M-sized definition. Statement then:
    forall n > 0, exists k, gnu^[k] n = 1.

ROUTE
  Open (depends on gnu values at prime powers, where
  gnu explodes). Adjacent provable substance for the
  def's sanity suite: gnu p = 1 for prime p (every
  group of prime order is cyclic — Mathlib has
  isCyclic_of_prime_card), gnu(p^2) = 2, gnu(15) = 1.
  These small evaluations are native_decide-hard
  (n! search) — expect to prove them structurally,
  which is exactly the classical classification
  content and is novel in Lean.

EVIDENCE
  Holds for all n within GAP SmallGroups coverage.
