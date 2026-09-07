seq:     A000670
claim:   bala-egf-family-periodicity
status:  open
stmt:    L
proof:   hard
module:  Proofs/Enumerative/Fubini.lean (special case)
source:  OEIS A000670 comment, Peter Bala, 2022-07-08

CLAIM
  Generalization of the completed Fubini periodicity theorem in
  `Proofs/Enumerative/FubiniMod.lean`: for every
  integral power series G(x), the integer sequence
  with exponential generating function G(exp(x) - 1)
  is, for every k >= 1, eventually periodic mod k with
  period dividing phi(k). A000670 is G(x) = 1/(1-x);
  Bell numbers are G(x) = exp(x).

LEAN
  Mathlib has PowerSeries (RingTheory.PowerSeries) but
  no EGF API: no coefficient-extraction-with-n!
  framework, no composition G(exp(x)-1) toolkit aimed
  at integer sequences. Stating this faithfully needs
  that layer built first — that is the L.

ROUTE
  None with current machinery. If attacked, do the
  single-sequence cases (A000670, Bell mod k — the
  Bell case is Touchard congruence territory) first
  and let the general statement emerge from the shared
  proof shape.

EVIDENCE
  Instances asserted by Bala at A000670, A002050,
  A354242; Touchard's congruence is the proved Bell
  prototype.
