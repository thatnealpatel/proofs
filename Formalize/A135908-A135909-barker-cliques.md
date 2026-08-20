seq:     A135908, A135909
claim:   barker-commuting-clique-recurrences
status:  LANDED 2026-08-20 (base file in f061efe
         and subsequently extended; the unconditional
         A135909 proof passed independent review).
         A135908 recurrence PROVED unconditionally
         (bridge a135908 n + 1 = A000792 n,
         Bercov–Moser); no prior written proof was found,
         which is not a priority claim. A135909 is now
         PROVED unconditionally for the corrected range
         n > 9: `maxAbelianOrder_alternating_fin` proves
         the exact `gAlt` formula by explicit lower
         constructions and orbit induction, and
         `a135909_recurrence` derives the recurrence for
         the actual A_n clique numbers. The general
         alternating-group extremal problem was treated
         by E. P. Vdovin, "Maximal orders of Abelian
         subgroups in finite simple groups," Algebra and
         Logic 38 (1999), 67–83; the contribution here is
         an elementary Lean formalization and the Barker
         consequence. Barker's claimed range n > 6 is
         REFUTED numerically and unconditionally from
         the entry's own terms (fails at n = 8, 9 and
         contradicts his own g.f. in the same %F clause).
         Issue thatnealpatel/proofs#36 is a correction
         report, not evidence that OEIS has accepted or
         applied the correction.
         Vertex convention: three conventions occur in
         the literature. When the center is trivial,
         G∖Z(G) and G∖{1} agree, while the graph on all
         of G has clique number one larger. The file uses
         G∖{1} (data-pinned).
stmt:    S
proof:   L
module:  Proofs/GroupTPP/CommProbBound.lean,
         HigherCommProb.lean (commuting structure)
source:  OEIS A135908 and A135909 formulas, Colin
         Barker, 2013-07-26

CLAIM
  a(n) = clique number of the commuting graph of S_n
  (A135908) resp. A_n (A135909), using nonidentity
  elements as vertices. Its clique number plus one is
  the maximum abelian subgroup order: adjoining the
  identity to a pairwise-commuting set preserves
  commutativity, and such a set generates an abelian
  subgroup. Barker's original conjectures were:
    S_n: a(n) = a(n-1) + 3a(n-3) - 3a(n-4)  (n > 7)
    A_n: same recurrence                     (n > 6)
  with explicit rational generating functions
  in-entry.

LEAN
  `maxAbelianOrder_alternating_fin` proves the exact
  maximum order `gAlt n` unconditionally. The proof
  combines explicit abelian subgroups with a strong
  induction on orbits; a separate parity argument
  handles two-point orbits. `a135909_recurrence` then
  proves Barker's corrected recurrence directly for the
  actual alternating-group clique numbers when n > 9.

ROUTE
  The symmetric-group side proves the Bercov–Moser
  maximum-order theorem by orbit induction and explicit
  disjoint-support products. The alternating-group side
  sharpens this argument: the ordinary orbit branch
  restricts an even point stabilizer to the complement,
  while the exceptional two-point branch injects the
  whole subgroup into the symmetric group on the
  complement using parity. Explicit C3, V4, C5, and
  product witnesses attain the upper bound.

EVIDENCE
  The file compiles sorry-free. Axiom audits of the
  headline theorems report only `propext`,
  `Classical.choice`, and `Quot.sound`; independent
  correctness, vacuity, and foundations reviews passed.
