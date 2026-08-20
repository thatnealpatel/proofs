seq:     A135908, A135909
claim:   barker-commuting-clique-recurrences
status:  LANDED 2026-08-20 (sorry-free,
         Proofs/Scratch/CommutingCliqueRecurrence.lean,
         uncommitted; full reviewer trio passed).
         A135908 recurrence PROVED unconditionally
         (bridge a135908 n + 1 = A000792 n,
         Bercov–Moser).  A135909: recurrence proved
         for n > 9 conditional on AltStructure (max
         abelian order of A_n = gAlt; verified n ≤ 11
         by computation, n ≤ 60 structurally; NO
         published general A_n determination found —
         Bercov–Moser is S_n only), and Barker's
         claimed range n > 6 REFUTED (fails at n = 8,
         9; contradicts his own g.f. in the same %F
         clause) — issue thatnealpatel/proofs#36.
         Vertex convention: three conventions in the
         literature; file uses G∖{1} (data-pinned).
stmt:    S
proof:   L
module:  Proofs/GroupTPP/CommProbBound.lean,
         HigherCommProb.lean (commuting structure)
source:  OEIS A135908 and A135909 formulas, Colin
         Barker, 2013-07-26

CLAIM
  a(n) = clique number of the commuting graph of S_n
  (A135908) resp. A_n (A135909): vertices = group
  elements, edges = commuting pairs; clique number =
  largest set of pairwise-commuting elements = largest
  abelian subgroup order (a pairwise-commuting set
  generates an abelian subgroup). Conjectures:
    S_n: a(n) = a(n-1) + 3a(n-3) - 3a(n-4)  (n > 7)
    A_n: same recurrence                     (n > 6)
  with explicit rational generating functions
  in-entry.

LEAN
  SimpleGraph.cliqueNum exists; commuting graph is a
  one-line SimpleGraph def (novel in Lean). Statement
  S.

ROUTE
  Reduces to: maximal abelian subgroups of S_n are
  (up to the boundary cases) direct products of
  3-cycle groups on disjoint supports, giving
  b(n) = max(b(n-1), 3*b(n-3)) and hence the linear
  recurrence and g.f. The underlying max-abelian-
  subgroup theorem (Bercov-Moser flavor) is real
  mathematics — L — but crisp, self-contained, and
  novel in Lean; the recurrence then falls out
  mechanically. Do small n by decide-style
  computation to anchor.

EVIDENCE
  Recurrence fits all computed terms in-entry.
