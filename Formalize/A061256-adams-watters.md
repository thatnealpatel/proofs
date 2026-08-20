seq:     A061256
claim:   commuting-pairs-euler-transform
status:  PROVED IN FULL 2026-08-20 (sorry-free,
         Proofs/Scratch/CommutingPairsEuler.lean,
         uncommitted; full reviewer trio passed).
         STATUS CORRECTION: the annotation was NEVER
         open — it is the genus-1 case of
         Liskovets–Mednykh 2009 (stated as A061256 on
         p. 49/53 of Mednykh's slides, linked from the
         entry) and a one-step Burnside corollary of
         Britnell.  Only the OEIS comment is stale.
         Contribution = independent machine-checked
         proof; KNOWN tier, no first-proof claim.
stmt:    M
proof:   M-L
module:  Proofs/Scratch/CommutingPairsEuler.lean
source:  OEIS A061256 comment ("it appears").
         ATTRIBUTION CORRECTION 2026-08-20: the PAIRS
         claim is a blog comment by "Allan" (Secret
         Blogging Seminar link in entry), NOT
         Adams-Watters; Adams-Watters conjectured the
         TRIPLES statement, proved by Britnell 2012.
         NB `oeis show` drops %H links — the White and
         Mednykh links that settle the status are
         invisible to it; pin from oeis.org.

CLAIM
  A061256 = Euler transform of sigma(n). Open part:
  a(n) equals the number of conjugacy classes of
  commuting ordered pairs in S_n, i.e. orbits of
  {(g,h) : gh = hg} under simultaneous conjugation.

LEAN
  Define the conjugation action of S_n on pairs
  (one line); Burnside IS in Mathlib:
  MulAction.sum_card_fixedBy_eq_card_orbits_mul_
  card_group (GroupTheory.GroupAction.Quotient).
  Euler transform side: define via the sigma product
  formula (ArithmeticFunction.sigma exists) or as the
  coefficient identity — pick the cleanest.

ROUTE
  Burnside: #orbits = (1/n!) sum_g #{commuting pairs
  fixed by g}. Fixed pairs under conjugation by g =
  commuting pairs in C(g) x C(g) intersected
  suitably; centralizers in S_n are wreath-type
  products with known structure; cycle-index
  bookkeeping should land on the Euler transform of
  sigma. Real but bounded combinatorics; medium
  confidence. Would settle the OEIS "it appears"
  outright — the cleanest possible instance of the
  project's novel-formalization-to-novel-proof bet.

EVIDENCE
  Terms match as far as computed in-entry; triples
  analogue is a proved theorem (Britnell), a strong
  plausibility signal.
