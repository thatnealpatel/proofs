seq:     A003313
claim:   knuth-stolarsky-lower-bound
status:  open
stmt:    M
proof:   hard
module:  Proofs/NumberComplexity/AdditionChain.lean
source:  OEIS A003313 comment recorded by Achim
         Flammenkamp, 2016-10-26; conjecture due to
         D. E. Knuth, K. Stolarsky et al.

CLAIM
  l(n) = length of a shortest addition chain for n
  (chain 1 = a_0, a_1, ..., a_r = n, each a_i a sum
  of two earlier — not necessarily distinct — terms;
  l(n) = minimal r). v(n) = binary weight of n
  (A000120). Conjecture:
    floor(log2 n) + ceil(log2 v(n)) <= l(n).

LEAN
  `Proofs/NumberComplexity/AdditionChain.lean` now provides
  `NumberComplexity.IsAddChain`, the subtype `NumberComplexity.AdditionChain n`,
  and the shortest-length function `NumberComplexity.l`. Its `l` is the
  minimum `chainSteps` over `AdditionChain n`; `l_eq_lAsc` reconciles the
  permissive predicate with ascending chains. The target can therefore be
  stated directly against this API; no `Nat.addChainLength` exists.

ROUTE
  Known partial results: l(n) >= log2 n + log2 v(n) -
  2.13 (Schonhage) — a Lean proof of the weaker
  classical bound l(n) >= ceil(log2 n) is the natural
  first theorem for the new def (each step at most
  doubles). The full conjecture is open mathematics.

EVIDENCE
  Verified by exhaustive computation for very large
  ranges (Flammenkamp/Clift chain tables).
