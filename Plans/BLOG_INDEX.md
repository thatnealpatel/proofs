# BLOG_INDEX

An index of landed results considered for blog posts, restricted to two
clusters: settled OEIS conjectures, and the perfect-number reductions.
Each entry is a content summary with pointers, not a narrative — grouping,
ordering, and framing are deliberately left for the reader to derive.

**Provenance discipline.** Entries are compiled from
`Manuscripts/Drafts/first-proofs-and-opn-reduction.md` (whose pointers and
novelty grades were last verified there 2026-07-31) and its ledger. File
existence was checked against the git tree 2026-08-02; the per-result
claims below (sorry-free status, axiom surface, novelty grades) are
**repeated from the sheet, not independently re-verified here**. Per repo
policy, ledger rows and index files — including this one — are unverified
summaries: re-fetch the artifact (build the file, re-run the axiom sweep,
re-sweep the novelty claim) before repeating any claim publicly.

Novelty grades used below, from the sheet's convention:
- **NRF** = no reference found (first-proof candidate; a claim about a
  sweep, not about the world).
- **LK** = likely known (first *recorded* proof is the ceiling).
- **KC** = known classical (no novelty claim; contribution is the
  formalization).

---

## Cluster A — OEIS conjectures settled by formalization

Statements taken from live OEIS entries where they appear as unproved
comments ("Conjecture", "It appears that ...", empirical observations),
proved sorry-free in Lean 4.

### A354741 — almost every Boolean matrix has full row rank
- **Statement proved:** the fraction of n×n matrices over the Boolean
  semiring ({0,1}, ∨, ∧) with full Boolean row rank tends to 1.
  Source: unattributed A354741 comment, hedged as "it appears from some
  empirical computations."
- **File:** `Proofs/BilinearComplexity/BooleanRankGeneric.lean`
  (commit `3ec26ec`), main theorem `fullRowRankFraction_tendsto_one`.
- **Mechanism:** rows that are nonzero and pairwise incomparable under
  domination span freely; a union bound gives ≤ n²(3/4)ⁿ bad fraction.
- **Grade:** NRF (sweep `.tasks/main/docs/novelty-BooleanRankGeneric.md`).
  Ingredients individually standard; the combination and the machine
  check are the contribution.
- **Contrast worth recording:** over 𝔽₂ the same fraction tends to
  ∏(1 − 2⁻ⁱ) ≈ 0.2888 (A048651). Divergence is concrete at n = 3:
  A354741 row `1, 49, 306, 156` vs A286331 row `1, 49, 294, 168`, both
  computed in-kernel over the same 512 matrices. Checked neighbours that
  do **not** subsume it: Komlós 1967 / Kahn–Komlós–Szemerédi 1995 (real
  rank), Pourmoradnasseri–Theis 2017 (Schein rank),
  Izhakian–Janson–Rhodes 2015 (triangular rank).

### A000670 — Bala's totient-period conjecture (a 1988 theorem)
- **Statement proved:** for every k ≥ 1 the residues `fubini n % k` are
  eventually periodic with period dividing φ(k). Source: Peter Bala's
  A000670 comment (2022-07-08), still labelled "Conjecture" on the entry
  as of 2026-07-31.
- **File:** `Proofs/Enumerative/FubiniMod.lean` (commit `c37e31e`), main
  theorem `fubini_mod_eventuallyPeriodic_conjecture`. No `native_decide`.
- **Grade:** LK, and the sheet is emphatic: the mathematics is
  **Poonen 1988** (Fibonacci Quarterly 26, Theorems 2 and 6; verified
  against `References/poonen/paper.txt`) and independently Barsky ~1982.
  The honest contribution is (a) the Bala ⟸ Poonen connection, recorded
  nowhere on the entries; (b) an elementary self-contained proof;
  (c) the machine check.
- **Scope caution (previously misstated in-repo):** this settles **one
  entry, half of one comment** — not A354242 or A002050, which are
  instances of Bala's *general* `G(exp(x) − 1)` conjecture. That general
  statement is open, covered by neither Poonen nor Barsky, and is the
  interesting question this work does not answer.

### A114976 — parity of mean-divisor subsets detects squares
- **Statement proved:** `a(n)` (nonempty divisor subsets of n containing
  their own arithmetic mean) satisfies `Odd (a n) ↔ IsSquare n`; sharper
  `a(n) ≡ τ(n) (mod 2)`; also `a(n) = 2 ↔ n prime`. Source: A114976
  unattributed "It appears that..." observations.
- **File:** `Proofs/Enumerative/MeanDivisors.lean` (commit `6677024`).
- **Mechanism:** mean-toggle involution. Note: the involution suggested
  by the OEIS entry's own route is provably wrong — a documented
  deviation.
- **Grade:** NRF (sweep inlined in the sheet §1.3, 2026-07-29). The
  sheet calls it the campaign's strongest first-proof candidate among
  the classical-statement results.

### A014701 — Rebert's keep-or-double walk
- **Statement proved:** minimal step count 0 → n is
  ⌊log₂(n+1)⌋ + popcount(n+1) − 1, with load-bearing guard `1 ≤ n`
  (the n = 0 junk coincidence is documented in-file). Source: A014701,
  Jean-Marc Rebert 2025-05-15, labelled "Conjecture" in-entry.
- **File:** `Proofs/NumberComplexity/StepWalk.lean` (commit `fa83e94`),
  main theorem `rebert_conjecture`.
- **Mechanism:** scalar potential (`binCost`) + exchange lemma for the
  lower bound; binary expansion realizes the upper bound.
- **Grade:** NRF (`novelty-StepWalk.md`). Explicitly UNCHECKED corpus:
  SeqFan archives. A056792's add-1-or-double walk is structurally
  distinct (worth distinguishing if written up).
- **Audit note:** the vacuity audit BFS'd three rival readings of
  Rebert's prose to pin the intended model; 86/86 published terms
  kernel-checked.

### A051293 — Cloitre's asymptotic, general M
- **Statement proved:** Cloitre's asymptotic expansion of A051293 with
  Fubini-number coefficients at *general* M
  (`Counting.lean:cloitre_conjecture`), with the DeepMind AlphaProof
  paper's `target_theorem_0` (M = 5 only, arXiv:2605.22763) derived as a
  corollary in `Proofs/Enumerative/A051293/Cloitre.lean`.
- **Also recorded:** Cloitre's general-m phrasing on the entry is false
  as written (o-term placement forces `fubini(m+1) = 0`); the M = 5
  instance shows the intended reading. In-tree definition pinned to OEIS
  terms 1..10 by kernel `decide`.
- **Grade:** related-work upgrade (machine-checked result strictly
  subsumes the cited published theorem), not a novelty claim.

### Smaller settled or cleaned-up entries (ledger tier)
Statements are easy or de-facto known; value is retiring stale labels
and having recorded proofs. Grades per `.tasks/main/docs/` sweeps.
- **A348262** — {1,+,^} master equality + pow-subadditivity.
  `Proofs/NumberComplexity/HamiltonBallinger.lean` (`f499c59`). NRF
  (modest: entry/norm unstudied, statements easy).
- **A005520** — record iff `a(n) = n ⟺ n ≤ 5`.
  `Proofs/NumberComplexity/ComplexityPatterns.lean` (`3559616`). NRF
  (small).
- **A064097** — log₂ lower bound; entry still says "Conjecture".
  `Proofs/NumberComplexity/Quasilog.lean` (`67b13d1`). LK.
- **A076142** — `l ≤ quasilog`.
  `Proofs/NumberComplexity/QuasilogChainGap.lean` (`bf57463`). LK.
- **A267632** — odd-row palindromicity.
  `Proofs/Enumerative/PalindromeRows.lean` (`5976abf`). LK.
- **A003278 / A191107 / A055246** — identities; stale "Conjecture"
  labels. `Proofs/Enumerative/StanleyDigits.lean` (`1b6db2c`). LK.
- **A003313** — low-range doubling law.
  `Proofs/NumberComplexity/SlizkovDoubling.lean` (`cb84c0f`). KC.
- **A000001** — coprime submultiplicativity (Lopes).
  `Proofs/GroupCount/Submult.lean` (`559c2f0`). LK folklore.
- **A046057** — minimality pins a(1)=1, a(2)=4.
  `Proofs/GroupCount/DennisSurjectivity.lean` (`24c754e`). LK (possibly
  first rigorous proofs of any entries of this sequence).
- **A060938** — Schmidt submultiplicativity.
  `Proofs/GroupTPP/MaxIrrepDegree.lean` (`3d513bd`). LK.

---

## Cluster B — reductions and bridges around perfect numbers

Distinct character from Cluster A: the products here are mostly
**conditional reductions** (theorems of the form open-conjecture ⟹
constraint) and **bridges** between OEIS-recorded notions. Several are
vacuously true if no odd perfect number exists; every file discloses
this at the declaration site, and any write-up must too.

### A083207 ⟹ an odd-perfect constraint
- **Statement proved:** the verbatim Ianakiev conjecture (A083207,
  2020-04-24; OPEN, the file's one disclosed sorry) implies: no odd
  perfect N — with τ(N) = 2w, w odd, forced by Euler parity — has w·N a
  perfect square. Conditional twice over (assumes the open conjecture;
  vacuous if no OPN exists) — the same genre as published OPN
  constraint theorems.
- **File:** `Proofs/Enumerative/ZumkellerTauSigma.lean` (`8eef184`).
  Supporting layer (unconditional, sorry-free) includes Neder's
  criterion and σ-parity lemmas.
- **Grade:** NRF on three counts (`novelty-ZumkellerTauSigma.md`,
  2026-07-30): the constraint itself, the A083207↔OPN connection, and
  the hedged hardness claim. UNCHECKED (low risk): Guy UPINT B1,
  Dickson vol. I, SeqFan.
- **Audit:** vacuity review SOUND; perfection/oddness proved
  load-bearing by counter-probes. Sieve to 10⁷: 103 qualifying d, all
  conjecture-consistent.

### Practical numbers: Stewart's criterion and the Coleman reduction
- **Statements proved:** Stewart's structure theorem as a full iff
  (`Proofs/Enumerative/StewartCriterion.lean`, `55a8a97`; math is
  Stewart 1954 / Sierpiński 1955, KC); the practical-number layer with
  Stewart step (`Proofs/Enumerative/Practical.lean`, `6b4d720`); weak
  Coleman (even perfect ⟹ practical) and the machine-checked
  **Coleman ⟹ no-odd-perfect** reduction (`d84bcbc`, conditional,
  same genre as A083207 above; graded NRF-connection, thinner — one
  step from folklore evenness).
- **Retraction on record (do not repeat the dead claim):** "first
  formalization of practical numbers in any proof assistant" was
  **retracted 2026-07-31** — google-deepmind/formal-conjectures has had
  `Nat.IsPractical` since 2026-03-15 and a proved
  `factorial_isPractical` since 2026-04-13. **Surviving claims:** first
  formalization of Stewart's criterion (both directions), the
  σ-characterization layer, weak Coleman, the Coleman archive, and the
  OPN-hardness reduction. Upstream's definition lacks a positivity
  guard (`IsPractical 0` holds); agreement for `0 < n` is
  machine-checked — a documented upstream-PR hook.

### The σ-parity bridge and multiperfect ordering
- **Statements proved:** practical ⟹ (Zumkeller iff 2 ∣ σ) — equal to
  Bhaskara Rao–Peng 2013 Prop. `proppraczu`, **cite them, no novelty
  claim**; Perfect ⟹ Zumkeller unconditionally (including the
  hypothetical odd case); Coleman ⟹ A007691 ⊆ A083207 for n > 1
  (conditional); nine instance certificates; Ianakiev's σ-half
  conjecture archived as a statement.
- **Files:** `Proofs/Enumerative/ZumkellerSigmaHalf.lean`,
  `Proofs/Enumerative/MultiperfectZumkeller.lean` (working tree
  2026-07-31 per the sheet — confirm commit before citing).
- **Grade:** KC consolidation. The Coleman ⟹ A007691-Zumkeller
  *ordering* composes three OEIS-recorded facts and appears unrecorded
  as such — one-sentence remark, not a result.

---

## Shared context a future reader should know

- **Toolchain/repro:** `leanprover/lean4:v4.33.0-rc1` + Mathlib pinned
  by `lakefile.toml` / `lean-toolchain`; full build green 2026-07-30
  (8826 jobs). Axiom surface for cited sorry-free theorems: exactly
  `{propext, Classical.choice, Quot.sound}`; the A083207 file carries
  its one disclosed open-conjecture sorry. No `native_decide` in any
  result file (per the sheet's 2026-07-30 re-verification).
- **Claim-discipline record:** nine prior-art or fact claims in this
  project were believed and later falsified — every one caught by
  retrieving an artifact, never by reasoning or a second search. Two
  are directly relevant here (the A000670 scope error and the
  practical-numbers retraction, both detailed above). Treat every
  grade in this file the same way: a claim about a sweep on a date,
  falsifiable by one fetch.
- **Sweep docs** live under `.tasks/main/docs/` (untracked — copy out
  before they age away). OEIS ground truth was checked against live
  entries on the dates noted; entries drift.
- Deliberately out of scope for this index: the covering-systems arc
  (`Manuscripts/Drafts/covering-criterion.md`,
  `covering-certificates.md`), the matrix-multiplication/ω program
  (`four-way-chain.md`, `abelian-factor-refutation.md`,
  `exotic-groups-for-mm.md`), and all in-tree material with no
  manuscript coverage (`Proofs/ShearEC/*`, `Proofs/CHILO/*`,
  `Proofs/Erdos/Erdos*` outside `Covering/`).
