# A391599 — intersecting-family lower bounds

- **Mathematical status:** the source's former `3n+O(1)` premise is refuted; the classical and improved lower bounds are known theorems.
- **Work status:** unstarted for the substantive lower-bound mathematics.
- **Remaining target:** formalize the Erdős–Lovász lower bound (and ultimately Sivashankar's improvement) for the minimum size of the relevant maximal intersecting uniform family.
- **Existing correction:** `Proofs/Erdos/ErdosLovasz.lean` records the obsolete asymptotic as a proposition and proves it incompatible with Sivashankar's theorem. Sivashankar gives `g(r)≥((41-√19)/12-ε)r`, whose coefficient is about `3.0534`, so `g(r)-3r→∞`.
- **Next obligation:** define the covering/transversal-number formulation without ambiguity and formalize the actual lower-bound argument. Recording the refutation is not a proof of either lower bound.
- **Attribution:** the `g(5)=13` and `g(6)≤18` results are by J. Barát alone, not Barát–Wanless.
