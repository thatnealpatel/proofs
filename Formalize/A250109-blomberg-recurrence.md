seq:     A250109
claim:   blomberg-empirical-recurrence
status:  open
stmt:    L
proof:   unknown
dependency: no dedicated formal model of straight-line multiplicative
         complexity; the bilinear-rank modules do not imply this claim
source:  OEIS A250109: Lars Blomberg empirical
         formulas and order-12 recurrence, 2016-12-04;
         Colin Barker empirical g.f., 2016-12-04;
         entry states "no recurrence is known"

CLAIM
  A250109 arises from the multiplicative complexity
  of symmetric functions over a field of
  characteristic p (exact functional per entry).
  Conjectures: a(n) satisfies piecewise-cubic closed
  forms in n mod 4 and the recurrence
    a(n) = 3a(n-4) - 3a(n-8) + a(n-12) - 64  (n > 12)
  with a rational generating function.

LEAN
  L because the OBJECT needs a circuit model:
  multiplicative complexity = min number of AND gates
  in an XOR/AND circuit computing a Boolean/GF(p)
  function. No circuit-complexity formalization exists
  in Mathlib or packages (audited 2026-07-23; Std.Sat
  AIG is a solver internal, not a complexity measure).
  Building the model is the first formalization obligation.

ROUTE
  Only via building the circuit layer. Park unless the
  circuit model is wanted for its own sake (it is
  adjacent in spirit to the concrete track's addition-
  count ledger, but formally unrelated).

EVIDENCE
  Empirical fit over the computed range in-entry.
