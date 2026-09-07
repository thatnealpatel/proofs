# Border apolarity, Hilbert schemes, Slip, and search completeness

- **Mathematical status:** published border-apolarity criteria and algorithms, only narrowly formalized.
- **Work status:** hard-blocked.
- **Remaining target:** formalize the full Buczyńska–Buczyński / Conner–Harper–Landsberg border-apolarity criterion, including multigraded Hilbert functions, the relevant Hilbert scheme and `Slip` component/smoothability membership, Borel-fixed reduction, and completeness/soundness of the finite search algorithm over its stated field hypotheses.
- **Completed narrow scope:** `Proofs/AlgComplexity/Vp2/Apolarity.lean` proves the polynomial-closure soundness of a weaker modeled `(111)` kernel test over an infinite field. That is not the full `Slip`-membership theorem, does not model smoothability or the cactus gap, and passing the test gives no border-rank upper bound.
- **Source digest:** `Documents/BorderApolarity.md` consolidates arXiv:1910.01944 and arXiv:1911.07981 while preserving their different objects, field hypotheses, and theorem-number corrections. The deleted cactus-barrier note arXiv:2602.11309 is also covered by this residual boundary: its barrier consequences do not supply the missing Hilbert/Slip formalization.
- **Next obligation:** define multigraded Hilbert functors/schemes and the smoothable component sufficiently to state `Slip` membership; prove the degeneration/properness argument; only then connect Borel-fixed enumeration and algorithmic rejection/acceptance certificates.
- **Claim boundary:** finite `(111)` linear algebra, bounded candidates, polynomial closure, and Borel-fixedness as an isolated reduction are not completion of the published criterion or algorithm.
