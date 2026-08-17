# PLAN — campaign dispatch plan

This file is the forward dispatch plan for ALL active arcs. It supersedes
its previous covering-arc-only scope and re-absorbs the dispatchable
remainder of `Formalize/INDEX`'s burndown queue. `INDEX` stays the ledger
of landed work and card metadata but is NO LONGER the dispatch state of
record — it is stale (chore X2); trust git and the tree over both
documents.

Correction history is in `git log -p PLAN.md`, not in this file. Several
claims here have been wrong before; when one moves, move it and let the
commit record why.


## PROTOCOL — deltas of 2026-08-05

  Lanes    `prover` = Fable 5 xhigh: scarce-by-cost; holds only the item
           with the largest gap between "stated" and any known formal
           route. `postdoc` = Opus 5 Max: throughput; literature-
           following routes, grindy lanes, statement archives.
  Review   Orchestrator-dispatched ONLY, after a writer lane halts:
           parallel vacuity-cop + reviewer, orchestrator applies fixes,
           one commit per lane, writers never commit. Lanes MUST NOT
           self-audit (prover/postdoc agent files carry the MUST NOT); a
           lane-relayed PASS is an unverified claim — re-audit it.
  Cop      vacuity-cop rung 5 (new): source-fidelity — hunt LLM
           mis-translation, hallucinated conjectures, and prose-to-
           formal divergence against PRIMARY sources (`oeis show`,
           fetched papers), never against the `Formalize/` card, which
           is itself an LLM relay.
  Writers  STYLE.md first; `flock .lake/agent.lock lake build`;
           systemd-run memory fence; `oeis show` ground truth before any
           Lean statement; halt-never-weaken.


## CHORES — cross-cutting, start before or alongside wave 1

  X1  Adopt `leanprover-community/axiom-audit` (allowlist-subset check,
      runs over `.olean`, catches transitive deps, community-maintained)
      and retire the five stale hand-rolled sweeps under
      `Proofs/Scratch/` (Ad1AxiomSweep, Aw1AxiomAudit, Le1AxiomAudit,
      Secp256k1AxiomAudit, ShearReviewAudit) with `goof rm` — only
      after parity is demonstrated by planting both a native_decide
      proof and a `sorry` and watching the new tool fire. Measured facts
      behind this are under AXIOM HYGIENE below.
  X2  Refresh `Formalize/INDEX`: record the landed-but-unrecorded files
      — FixedDivisor/Sierpinski/Riesel/Erdos1950Instance (9d873d7,
      5157ca8), RankOfApparition (3c7d4ef), ZumkellerSigmaHalf +
      MultiperfectZumkeller + nine A083207 instances (3e593ab), the
      NederGap stub state, and the ShearEC arc — CORRECTED 2026-08-05:
      T1–T4 are fully covered and sorry-free (T1 =
      TotalDegreeAeval + ShearCircuit, T2 = ShearInversionLB +
      Secp256k1Prime, T3 = ShearQuadraticRank + ShearAddition, T4 =
      ShearAdditionEC + ShortCurveScaling + VariableChangePointEquiv),
      but `ShearAdditionChains.lean` (T5) is a THREE-LINE EMPTY STUB —
      the min-shears-for-x^n = l(n) bridge does not exist; it joins the
      A003313 lane (P8) as the natural sibling. Strike the STATEMENTS
      rows that landed; mark queue items 2–5 follow-ons accurately
      (Sierpinski/Riesel follow-on is DONE). Two spec files INDEX
      cites do not exist anywhere (review-vacuity-SlizkovDoubling.md,
      review-vacuity-ErdosLovasz.md) — note the citations as dead.


## WAVE 1 — dispatched 2026-08-05

  P1  prover   SliceRank pullback-monotonicity + CLP bound.   [DONE]
               16e7e2b (Task A), edc443d (Task B).
               `sliceRank_comp_le` (arbitrary maps, not just injective)
               in SliceRank.lean § 7. CLP sorry discharged via Tao's
               symmetric route in CapsetSliceRank.lean § 5;
               `ellenberg_gijswijt` now clean. `peebles_conjecture`
               untouched (intended sorry).
  P2  postdoc  Neder gap ≤ 12.                                [DONE]
               9859682. `nth_isZumkeller_succ_le_add_twelve` +
               `exists_isZumkeller_mem_Ico` (settles Noe 2010).
               Reused in-tree 3·2^k and coprime-closure proofs.
               CORRECTION: the brief's Noe framing was wrong — Noe's
               conjecture is WEAKER than Neder's, not stronger.
  P3  postdoc  AdditionChain permissive ≡ ascending.           [DONE]
               24bb900. `l_eq_lAsc`. Brief's sort+dedup sketch was
               wrong (chains can overshoot n); fixed via filter-first
               `ascNormalize`. Ground checks n ≤ 8, n = 15.
  P4  postdoc  ErdosLovasz g(3) = 6.                          [DONE]
               3a4110c. `tripathi_six_le_erdosLovaszNum_three`
               discharged via double-counting (not Fin 15 search).
               `tripathi_erdosLovaszNum_three` now sorry-free.
               Attribution corrected: priority is FOT96, not Tr14.

## WAVE 2 — into freed lanes as wave 1 drains

  P5  postdoc  Erdős–Rado sunflower bound (r−1)^k · k! + 1, extending
               `Erdos/Erdos20/Sunflower.lean` (verified 2026-08-05:
               sorry-free, `IsSunflowerWith`/`HasSunflower` defs +
               compression machinery in place; the headline bound is
               absent — SpreadLemma.lean says so in a comment). Model:
               AFP `Sunflowers` (René Thiemann) — it IS Erdős–Rado
               (#20), not Naslund–Sawin; see PRIOR ART. Note A332077's
               formula section pins the bound family verbatim.
  P6  postdoc  A061256 via Burnside/cycle index. PREMISE CORRECTED
               2026-08-05: the Adams-Watters comment (triples of
               commuting permutations / n!) was conjectured Jan 2006
               and PROVED by J. R. Britnell in 2012 — the OEIS note is
               NOT open. The lane is a first-FORMALIZATION of a proved
               identity, not a settlement; frame the file header
               accordingly. Burnside is
               `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`
               (verified live, GroupTheory/GroupAction/Quotient.lean) —
               pin it, do not let the lane reprove it.
  P7  postdoc  A092482/A093682 per-row closed forms. Verified
               2026-08-05: every formula on both entries is explicitly
               unproved ("conjectured and checked up to n=512" /
               "None of these formulas have been proved") — genuine
               open targets. Row 0 of A093682 IS A003278, already
               formalized in `Enumerative/StanleyDigits.lean` — start
               from that layer; rows are A003278, A004793, A033157,
               A093678–A093681.
  P8  postdoc  Statement-archive batch, one dedicated lane, sequential,
               one file/commit each, claims pinned 2026-08-05 (quote
               them verbatim in file headers from `oeis show`):
               A003313 (ascending convention per Hasler Nov 2025;
               Knuth-Stolarsky: floor(log2 n) + ceil(log2 v(n)) <= a(n),
               v = A000120; after P3) →
               A000670-muljadi ("primes > 3 in this sequence are of
               the form 4n+1", Jan 28 2011; Bala labels still live) →
               A000041-sun ("No a(n) has the form x^m, m>1, x>1",
               Dec 02 2013) →
               A161682 (WARNING: the TERMS are conjectural, search
               radius artifacts — archive the predicate "prime not of
               the form x^3 − y^2" + the infinitude conjecture, never
               the term list) →
               A002804 (formula proved for n <= 471600000
               Kubina-Wunderlich 1990; Mahler: finitely many
               exceptions; archive the all-n conjecture) →
               A046098 (entry has NO explicit finiteness conjecture,
               only Noe's "No other n < 10^8" — archive that bound
               honestly; note `Erdos175/NotSquarefree.lean` core is
               sorry-free but `witness_cert` uses native_decide, and
               its n is centralBinom's n: A046098 terms are 2n) →
               A332077 (conjecture verbatim: Sun(m,n) <= (n*O(1))^m;
               O(1) needs care — archive via ∃ C) →
               A094870 (Hegarty: 3n/8 <= a(n) < 3n/2 and
               lim a(n)/n = 1; permutation property is PROVED in
               Hegarty's paper — a provable sub-target) →
               A005432 (Pyber: c^(n^2(1+o(1))) <= a(n) <=
               d^(n^2(1+o(1))), c = 2^(1/16), d = 24^(1/6); lower
               bound conjectured tight) →
               A323653 (def layer is HEAVY: needs A276086 primorial-
               base exp and A003961 prime-shift; pinned defs in the
               2026-08-05 sweep; conjecture = A351458 ∩ A007691 =
               A323653; cost is L, not M — do last) →
               A273929 (rank-free point-existence form ONLY per USER
               ruling; CARD DRIFT found: OEIS says subset of
               PRIMITIVE congruent numbers A006991 with A062695 the
               complementary piece — state the subset claim, not the
               card's "characterization" framing).


## WAVE 3 — dispatched 2026-08-05

  P9  postdoc  Melfi 1996: even = practical + practical.  [DONE]
               2e5b1ab. `even_eq_practical_add_practical` (sorry-free).
               Proof uses two-modulus covering (2^k, 2·3^j), NOT
               Melfi's twin-practical sequence — L risk avoided.
               Discharges `melfi` sorry in three sketch files.
  P10 postdoc  Kummer carry layer (#376).                 [DONE]
               626822b. `carry` def + bridge to Mathlib's
               `padicValNat_choose'`. Kummer proper already in
               Mathlib; file builds the missing carry function.
               Unlocks #376 + #406 (not five problems as briefed).
  P11 postdoc  Erdős #1063 Selfridge defect.              [DONE]
               8efac26. `erdos_selfridge_defect_pos` (sorry-free).
               Proved under k ≤ n (stronger than source's 2k ≤ n).
               CORRECTION: brief gloss described #377, not #1063.
               Certifies n₂=4, n₃=6, n₄=9, n₅=12 (A389360).
  P12 postdoc  Erdős #535 gcd-sunflower bound.            [DONE]
               0238c07. `card_le_of_isAlmostPrime` (sorry-free).
               Ω-layer bound (r-1)^k·k! via prime-power encoding
               of Erdős–Rado. Sharp at k=1. N-form proved but
               weaker than trivial (brief's premise was false).
  P13 postdoc  Covering arc C1: base-b generalisation.    [DONE]
               37e5f2e. `IsFixedDivisorSystemBase` + base-b
               Sierpiński/Riesel with three concrete witnesses.
               51 new declarations, zero existing broken.
               n ≥ 1 convention forced (n=0 gives primes).
  P14 postdoc  ‖2^n‖ = 2n archive (Guy F26).             [DONE]
               d657720. One intended sorry. Cube bound certifies
               a ≤ 9 analytically (decide window unreachable).
               Bonus: ‖3^b‖ = 3b proved for all b ≥ 1.


## COVERING ARC — adopted lanes (previous PLAN, renumbered)

### STATE

  Basic.lean                f2cd3df  Covers, IsCoveringSystem (distinct
                                     moduli > 1), covers_iff_forall_range
  NotTwoPowerPlusPrime      add6611  Erdos 1950 in full
  ErdosMinus2k / ErdosRows  7520b62  A039669 archive + 10^9 window;
                                     A089654 bridge (1 intended sorry)
  FixedDivisor.lean         9d873d7  THE GENERAL CRITERION
  Sierpinski / Riesel       9d873d7  78557, 509203, both infinitudes
  Erdos1950Instance.lean    9d873d7  Erdos 1950 from the criterion
  RankOfApparition.lean     3c7d4ef  alpha(p) and Fibonacci-like zero
                                     sets — the alpha-layer lane C6 needs

Sorry-free except the archived A039669 conjecture. Axioms within
{propext, Classical.choice, Quot.sound}. No native_decide.

### Lanes

  C1  (was A') Base-b parameterisation                 [S]  DONE (P13, 37e5f2e)
      postdoc. `2` → `b` throughout FixedDivisor; order bridge becomes
      `(b:Z)^d = 1 [ZMOD p]`; per-class step unchanged. Decidability
      survives — `b^d % p = 1 % p` stays a ground check. Reaches base-b
      Sierpinski/Riesel (cf. A273987). Mechanical; highest value per
      line in the arc.

  C2  (was A) Abstract sequence-level layer            [S]
      postdoc, piggyback on the C1 lane. ~15 lines: the shared statement
      both families instantiate (Fibonacci-like half landed at 3c7d4ef).
      Buys STATEMENT reuse only — the `decide` pipeline stays in
      per-family bridges. The shared hypothesis is NOT decidable as
      stated; families satisfy it by different mechanisms (ord_p(2) vs
      alpha(p)).

  C3  (was B) Brier numbers                            [S]  SWEEP FIRST
      postdoc. Simultaneously Sierpinski and Riesel;
      k = 3316923598096294713661 (Clavier), all four fields checked both
      sides, zero uncovered residues, all divisors prime:
        Sierpinski (p | k*2^a + 1), L = 48, 7 triples, max 108 bits
          {(1,2,3),(2,4,5),(4,12,13),(0,8,17),(36,48,97),
           (20,24,241),(12,48,673)}
        Riesel (p | k*2^a - 1), L = 180, 13 triples, max 109 bits
          {(0,2,3),(0,3,7),(9,10,11),(11,18,19),(1,5,31),(23,36,37),
           (7,20,41),(10,60,61),(8,9,73),(5,36,109),(13,15,151),
           (25,30,331),(37,60,1321)}
      Shape: TWO INDEPENDENT `IsFixedDivisorSystem` instances — the
      sides share only the prime 3 and the modulus 2. Loads 336 and 2340
      vs Selfridge's 252, far inside the measured ceiling. BOTH
      CERTIFICATES INDEPENDENTLY RE-VERIFIED 2026-08-05 (coverage,
      divisibility + ord, primality — all PASS; python3/sympy, sage
      absent in the probe environment). Warn: the record k is also the
      smallest — no cheaper fallback witness; do not source covering
      sets from primepuzzles.net without re-verifying (Wesolowski's
      entry fails Riesel coverage). NOVELTY SWEEP DONE 2026-08-05:
      ACL2 HAS mechanically verified Brier numbers — Cowles–Gamboa,
      "Verifying Sierpinski and Riesel Numbers in ACL2" (2011,
      arXiv:1110.4671), Appendix A: five k values with both covers
      checked by verify-sierpinski/verify-riesel macros (smallest
      143665583045350793098657; the word "Brier" never appears but
      the concept is explicit). No Lean/Isabelle/Coq/Mizar/HOL/Agda
      hit. Value framing: first LEAN formalization + the RECORD
      (smallest known) Brier k — Clavier's k is ~10^21, far below
      ACL2's five. Cite Cowles–Gamboa; claim no more.
      Adjacent: formal-conjectures issue #644 tracks Sierpinski/
      Riesel as absent upstream — our landed Sierpinski.lean/
      Riesel.lean already exceed it; possible upstreaming hook.

  C4  (was D) Mirsky–Newman theorem                    [M]
      postdoc. No disjoint distinct covering system exists (conjectured
      Erdos 1950; proved Mirsky–Newman, indep. Davenport–Rado; special
      case of Herzog–Schonheim). Root-of-unity argument, stated directly
      on the committed `IsCoveringSystem`. Strongest classical target in
      reach. GATE RESOLVED 2026-08-05: upstream `ErdosProblems/274.lean`
      was READ — it states Erdős #274 / Herzog–Schönheim over GROUP
      cosets (all three theorems sorry'd; the abelian variant is tagged
      "solved" pointing to an external proof by Jostamon, body still
      sorry). It does NOT state integer Mirsky–Newman — the
      integer-AP statement on our `IsCoveringSystem` is not taken
      upstream. NOVELTY SWEEP DONE 2026-08-05: NO Mirsky–Newman /
      Davenport–Rado proof found in any assistant (GitHub, mathlib4,
      Zulip, erdosproblems threads, AFP-adjacent, arXiv — all
      searched). First-formalization candidate. UNRESOLVED THREAD:
      274.lean's abelian-variant tag reportedly points to an external
      proof by "Jostamon", but the sweep found no such artifact — the
      lane MUST resolve that pointer from the file itself before any
      novelty claim. Paper trail: abelian case is Sun 2004; the
      integer theorem is Mirsky–Newman via the root-of-unity /
      Davenport–Rado argument.

  C5  (was E) Erdős-problem targets                    [S each]
      Measured against the formal-conjectures tree (recursive, API),
      509 files; covering-systems tag = 22 entries.
      PRESENT upstream, do NOT duplicate:
        7, 203, 204, 273, 274, 275, 276, 277, 279, 280, 281, 1113
        (7 and 274 present, 278/1188/1189 absent — re-verified
        against the live tree 2026-08-05)
      Unclaimed AND open (statuses re-pulled from erdosproblems
      2026-08-05):
        #278   fixed-modulus-set covered density. NOT a mere archive —
               the MINIMUM question is SETTLED (minimum at all a_i
               equal; Rogers via Halberstam–Roth *Sequences* (1983)
               5.3 per JonahKlein comment 2026-03-03, three years
               before Simpson [Si86]; Tao writeup 2026-01-19,
               terrytao.wordpress.com "Rogers' theorem on sieving").
               The MAXIMUM question stays open. Provable target:
               postdoc formalizes the Rogers/Simpson minimum
               (inclusion-exclusion over lcms).
        #1188  count of minimal distinct covering systems F(x). Open.
               CAVEAT (Woett/Bloom thread, Apr 2026): the site's
               statement is Bloom's reinterpretation — Erdős's [Er80]
               original asks about moduli distinct ACROSS systems,
               where Hough bounds F(x) uniformly. Archive the site's
               form and say which one it is. Woett's elementary
               F(x) >= floor(log_12 x) is a provable fragment.
        #1189  irreducible covering sets. Open; final sub-question
               settled by Sun 2007 (divisors of 2^(p-1)·p form an
               irreducible covering set — an explicit certificate our
               layer can check); Simpson [Si85]: n_k <= 2^(k-1).
               Archive + the Sun instance as the settled fragment.
      #7 upstream is `erdos_7` over `StrictCoveringSystem Z` (sorry'd,
      Ideal moduli, not decidable) — a decidable restatement is a
      defensible separate contribution, but say so explicitly.

  C6  (was H) Wilf primefree sequence A083216          [M]  PROBE FIRST
      Fibonacci-like, every term composite, consecutive coprime.
      a(0) = 20615674205555510, a(1) = 3794765361567513. Alpha-layer
      LANDED (3c7d4ef) and API CONFIRMED READY 2026-08-05: the
      per-class step is `IsFibonacciLike.forall_mod_eq_dvd`
      (needs only 0 < m, alpha(m) ∣ d, one base divisibility — the
      exact analogue of FixedDivisor's order bridge); non-degeneracy
      discharges from `not_dvd_zero_and_one_of_isCoprime`, which is
      A083216's coprime initial pair. `IsFibonacciLike` is pinned to
      s(n+2) = s(n+1) + s(n) — fine here, but do not promise general
      two-term recurrences. alpha(p), not the Pisano period, plays
      ord_p(2)'s role. `decide` load L*|T| = 8640*18 = 155520, ~600x Selfridge —
      AT the measured practical limit, not inside it: GATE dispatch on a
      scaled decide probe first. Terms are unevaluable (a(8640) ~
      10^1805) — the bridge MUST live entirely in `ZMod p`; a naive port
      of the existing certificate shape will not terminate. Warn: the
      18-triple certificate (L = 8640, coverage verified, gcd(a0,a1)=1)
      was reconstructed computationally from A083216, NOT read off a
      paper — Vsemirnov's 17 published quadruples are for a DIFFERENT
      sequence. Re-derive independently before committing.
      Src: Graham, Math. Mag. 37 (1964) 322–324; Wilf, Math. Mag. 63
      (1990) 284; Vsemirnov, JIS 7 (2004) 04.3.7.

  C7  NEW micro-lane: drop `1 ≤ k` from erdos_1950
      MECHANICS PINNED 2026-08-05. The `1 ≤ k` sits INSIDE the negated
      existential of `erdos_1950_not_two_pow_add_prime` (`¬ ∃ k p,
      1 ≤ k ∧ ...`), so removing it STRENGTHENS the theorem. The k = 0
      case is already paid for: the covering class 0 (mod 2) with
      p = 3 gives 3 ∣ m − 2^0 (docstring on
      `exists_mem_erdosPrimes1950_dvd` says so explicitly), and the
      general-criterion rederivation
      `not_prime_sub_two_pow_of_general` ALREADY dropped the
      hypothesis. Only the bespoke `not_prime_sub_two_pow` + the final
      packaging still carry it. Genuinely small; do it regardless of
      USER decision 3 — it makes the flagship match A006285's k ≥ 0
      convention.


## AXIOM HYGIENE — measured facts (keep until X1 lands)

The five hand-listed sweeps under `Proofs/Scratch` state their criterion
as "no `Lean.ofReduceBool`". That name is never emitted on this
toolchain, so those five detect nothing. Measured on v4.33.0-rc1: a
native_decide proof yields `<decl>._native.native_decide.ax_1_1`.

This is documented upstream behaviour, not a discovery — RFC #12216 /
PR #12217, shipped in Lean v4.29.0 (2026-03-27), moved native
computation to one axiom per computation; `ofReduceBool` was deprecated
2026-02-01. Only an allowlist-SUBSET test works. `RankOfApparition`
section 10 does it that way and `throwError`s, verified to fire by
planting both a native_decide proof and a `sorry`. It cannot close two
limits from inside: `example`s contribute no constant and escape any
such sweep, and the sweep is positional. Mathlib solves the same problem
with a syntactic linter plus periodic lean4checker, and explicitly notes
name-checking is "not airtight".


## PRIOR ART, as enumerated

Recorded here because the canonical grading document
(`.tasks/main/docs/novelty-ErdosCovering.md`) is outside version control.
Each absence names the enumeration it was checked against.

  alpha(p) / Pisano   Absent from Mathlib rev 3edb3c0 (`grep -ric
                      apparition|pisano` over Mathlib/ = zero files).
                      Absent from AFP (63 NT entries enumerated) and
                      from Coq/Rocq sources checked. agda-unimath DOES
                      have `elementary-number-theory.pisano-periods` —
                      closest prior art anywhere; it defines the period
                      but not the entry point, and does not prove the
                      zero-set theorem. The mathematics is routine
                      (Vajda 1989 p. 73); first-formalization at most,
                      never new mathematics.
  Naslund-Sawin       No prior formalization found. formal-conjectures
                      `ErdosProblems/857.lean` exists but is a stub —
                      `answer(sorry)`, body `sorry`, 0 lines proved.
                      Mathlib has zero sunflower/slice-rank content. AFP
                      `Sunflowers` is Erdos-Rado, i.e. #20, a different
                      problem. Lean 3 `lean-forward/cap_set_problem` is
                      Ellenberg-Gijswijt, method-adjacent but not this.
                      `SproutSeeds/sunflower-lean` is structural, not
                      the tensor bound.
  Covering in Lean    NOT clear ground. erdosproblems.com links
                      per-problem Lean artifacts in personal repos: #16
                      is "disproved (Lean)" via D. Chin 2026-02-25,
                      building two covered APs from the SAME
                      {3,5,7,13,17,241}/period-24 system as
                      NotTwoPowerPlusPrime. Sweep each entry's comment
                      thread before any novelty claim, not just the
                      formal-conjectures tree.

  LIMIT on all three: GitHub code search does not index every repo and
  was unauthenticated for the alpha sweep; the Rocq opam index (584
  packages) and the Mizar MML (~1300 articles) were not enumerated
  exhaustively. "None found in the corpora named" is the claim; "does
  not exist" is not.


## AXED

  * Old lane C (more Sierpinski/Riesel instantiations, A076336/A101036):
    no firsts anywhere (ACL2 covers several), and framework reusability
    is already evidenced by THREE landed instantiations (Sierpinski,
    Riesel, Erdos1950Instance). Value per line ~zero.
  * The five hand-rolled axiom sweeps — on X1 landing, not before.
  * Old lane I (A006285 note) as a lane — demoted to micro-lane C7 plus,
    at most, a formalization link on the entry. Formally still USER
    decision 3; recommendation is drop the note, keep C7.
  * A062733 (GL(3,2) char table): "bounded" but almost certainly a
    kernel-decide grind, not proving. Stays a card in INDEX, not a lane.


## GATED / DEFERRED

  * Hough–Nielsen 2019 (was F) [XL]: every distinct covering system has
    a modulus divisible by 2 or 3. An ITP paper on its own. GATED on
    USER decision 2.
  * Hough 2015 minimum-modulus (was G) [XXL]: recorded for completeness,
    not dispatch.
  * Barker cliques (A135908/09) [S/L]: the max-abelian-subgroup-of-S_n
    theorem underneath is the one queued item where a lane may stall.
    Dispatch to prover only after P5 lands and the S_n machinery has
    been felt out.
  * A000670-egf-family: needs an EGF layer designed first (Mathlib
    gap) — infrastructure arc of its own, not a lane here.


## NON-GOALS — state these explicitly in any writeup

  * Izotov (1995): certain fourth powers are Sierpinski WITHOUT a
    covering set, via the aurifeuillean factorization
      t^4*2^(4m+2) + 1 = (t^2*2^(2m+1) + t*2^(m+1) + 1)
                       * (t^2*2^(2m+1) - t*2^(m+1) + 1).
    Our framework provably cannot reach these. "Covering systems
    characterize Sierpinski numbers" is FALSE and easy to imply by
    accident. Whether Sierpinski numbers with no finite covering set
    exist is itself Erdos #1113 (open) — cite it as the anchor.
  * The Sierpinski problem (is 78557 least?) is a search question no
    covering argument touches. PrimeGrid is down to k = 21181, 22699,
    24737, 55459, 67607.
  * Pushing the A039669 window past 2^44 to discharge DeepMind's
    sorry'd `mientka_weitzenkamp` needs q = 37 and ~60x the current
    sweep; memory-bound on this box. Not a lane until that changes.
  * Attack on HOLD archives stays on hold: A064097 2.5·log upper,
    A267632 2^j case, A000001 non-coprime submultiplicativity, A250109
    (circuit model). Shelved by ruling: A031507, A060748 (no MW layer).


## USER DECISIONS PENDING

  1. Does the covering arc seed a SEPARATE ITP/CPP paper, or join
     `Manuscripts/Drafts/first-proofs-and-opn-reduction.md` as a fourth
     result? My read: separate — it is a formalization-infrastructure
     paper, not an OEIS-first-proof paper.
  2. Scope Hough–Nielsen yes/no.
  3. A006285 note yes/no (recommendation: no; C7 covers the substance).
  4. Whether to upstream `Basic` + `FixedDivisor` to Mathlib. Mathlib
     has ZERO covering-system content; impact is real and durable,
     review latency is long, and the API would need reshaping first.
  5. Whether `Manuscripts/` and `.tasks/` stay outside version control.
     Six drafts, 17 novelty sweeps and the triage sheet are untracked,
     including the file this plan cites as canonical for novelty
     grading.
