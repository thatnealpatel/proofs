# VERIFIED

Session-verified claims, one `##` entry per result. Unlike `BLOG_INDEX.md`
and the manuscript sheets — which are unverified summaries — every claim in
an entry here is either (a) tagged with the retrieval that established it
(command, URL, date) or (b) explicitly marked as a judgment of the editor.
Entries are drafted by an assistant from session artifacts and then
**heavily edited and signed by the editor**; an unsigned entry is a draft.

Floor vocabulary (from the 2026-08-02 session):
- **F0** — statement's status on the live primary source, fetched dated.
- **F1** — Lean artifact exists: named theorem, no stray `sorry`.
- **F2** — cold kernel re-check (`lake env lean`, not cache replay) + axiom
  surface, dated.
- **F3** — novelty/significance. Never grantable by search alone; the
  strongest truthful form is "no reference found by *this* enumeration on
  *this* date."

Workflow: **all work in this file happens in interactive Socratic
sessions** (`claude --append-system-prompt
"$(cat .claude/prompts/socratic_system.md)"`), with the editor present.
Within a session the agent runs floors and sweeps and drafts the entry;
the editor resolves every `<!-- EDIT ME -->` (they are HTML comments —
read the raw file, not rendered markdown) and signs. **An unsigned entry
is a draft; agents extend the evidence, never resolve the judgments.
No item below is a work order for an autonomous or background agent —
if the editor is not in the loop, do not start.** Every sweep here has
ended in a determination only the editor could make; autonomous
completion of these items is how manufactured claims happen.

## Open work queue (2026-08-02)

**Ready for the next Socratic session (agent retrieves, editor judges):**
- [x] A354741 F3 sweep — run 2026-08-02/03, entry drafted below.
  Fidelity signed by the editor 2026-08-03; verdict line, framing
  tier, and two follow-ups (Bollobás 1986, A355333 check) still open.
- [x] Verify the manuscript §1.2 claim that "the OEIS ROUTE's
  reflection involution is provably wrong" against
  `Proofs/Enumerative/MeanDivisors.lean` — done 2026-08-03; the
  claim **failed** verification (misattributed and not in-file; see
  the rewritten bullet in the A114976 entry).
- [x] Add an in-file axiom audit section to `MeanDivisors.lean` —
  done 2026-08-03, modeled on `BooleanRankGeneric.lean`'s; cold
  check green (see the updated F2 bullet in the A114976 entry).

**Editor-only (blocked on the editor):**
- [ ] A114976 entry: verdict line, ledger numbering (claims 10/11),
  footnote decision, editor's statement — all `EDIT ME` slots; then
  sign.
- [ ] A014701: framing tier for the blog post (headline vs.
  supporting); upstream OEIS contribution decisions for both entries.
- [ ] **A083207 (not yet an entry):** parked pending the editor's
  targeted reading on non-vacuity and the untrusted
  `novelty-ZumkellerTauSigma.md`. F0 established 2026-08-02 (Ianakiev
  conjecture live on the entry, verbatim in session record); F1 as
  designed (one disclosed open-hypothesis `sorry` at
  `ZumkellerTauSigma.lean:450`). No F3 work should start before the
  editor's read.

---

## A114976 — a true parity theorem inside a manufactured conjecture

**Verdict (editor's, 2026-08-02):** <!-- EDIT ME: your signed one-liner.
Assistant's raw material, marked as such: "the proof is real, the
mathematics is true, and the story built around it was manufactured by the
mining pipeline — the strongest surviving claim is the meta-observation." -->

### The mathematics (established, F0–F2)

- **Theorem (machine-checked):** for `a(n)` = number of nonempty subsets of
  `{1,…,n}` whose arithmetic mean is an integer dividing `n`:
  `Odd (a n) ↔ IsSquare n` (and `a(n) ≡ τ(n) (mod 2)`; `a(n) = 2 ↔ n`
  prime). `Proofs/Enumerative/MeanDivisors.lean:318`
  (`A114976.odd_a_iff_isSquare`), commit `6677024`.
- **F2, dated:** cold `flock .lake/agent.lock lake env lean` re-elaboration,
  exit 0, 2026-08-02. Axiom probe (separate file, after full
  `lake build Enumerative.MeanDivisors`, 8694 jobs green):
  `A114976.odd_a_iff_isSquare` depends on exactly
  `[propext, Classical.choice, Quot.sound]`. No `native_decide`.
  Hygiene gap **closed 2026-08-03**: in-file axiom audit section
  added (modeled on `BooleanRankGeneric.lean`'s), covering all 22
  named declarations including the two private lemmas and the
  `Decidable` instance. Cold re-check same day: `flock
  .lake/agent.lock lake env lean Proofs/Enumerative/MeanDivisors.lean`,
  exit 0; every declaration ⊆ `[propext, Classical.choice,
  Quot.sound]` (`IsMeanDiv` only `[propext, Quot.sound]`); no
  `native_decide`, no `sorryAx` in the log (session scratchpad
  `meandivisors-cold.log`).
- **Ground truth:** in-kernel `decide` checks of `a(1..10)` against the
  published terms (`MeanDivisors.lean:91-108`), including the
  discriminating values `a(4) = 5`, `a(10) = 80`. These ran in today's
  cold check.
- **F0, dated:** live entry fetched 2026-08-02 twice (`oeis show A114976`
  and `curl 'https://oeis.org/search?q=id:A114976&fmt=text'`, byte-identical
  comments; saved to session scratchpad). The parity observation is on the
  entry, hedged: unattributed comment, "at least for the very first terms,
  a(n)=odd iff n is a square: these observations **might suggest
  conjectures** on a deeper relationship with A000005." Entry authored by
  Reinhard Zumkeller, 2006-02-22; last edit #20, 2023-04-25; no `%F`
  formula lines, no `%D` references.

### The refutation chain (established 2026-08-02)

The repo's grade for this result was NRF, "the campaign's strongest
first-proof candidate" (`Manuscripts/Drafts/first-proofs-and-opn-reduction.md:114-121`,
§1.3, sweep dated 2026-07-29). It died in three retrievals:

1. **Putnam 2002 Problem A3** states the parity of the unrestricted count
   (A051293): "Let n ≥ 2 … T_n be the number of nonempty subsets S of
   {1,2,3,…,n} with the property that the average of the elements of S is
   an integer. Prove that T_n − n is always even."
   Retrieved: https://kskedlaya.org/putnam-archive/2002.pdf (verbatim).
   Print citation: Mathematics Magazine 76 (2003), 76–80,
   https://www.jstor.org/stable/3219137.
2. **The published solution is the repo's "mechanism."** Kedlaya–Ng,
   https://kskedlaya.org/putnam-archive/2002s.pdf, A3, verbatim: "for each
   set S with integer average m that does not contain m, S ∪ {m} also has
   average m, while for each set T of more than one element with integer
   average m that contains m, T \ {m} also has average m." This is the
   "mean-toggle involution" of manuscript §1.2. Consequence: each
   mean-class contributes an odd count, so restricting allowed means to
   any set M gives count ≡ |M| (mod 2). Putnam A3 is M = {1,…,n}; the
   repo's theorem is M = divisors of n. Same argument, different M.
3. **The sweep's own corpus contained the refutation.** §1.3 claims
   "nothing in … the A051293 … entries … states them." The live A051293
   entry carries a `%H` link titled "63rd Annual William Lowell Putnam
   Mathematical Competition, Problem A3" — one hop deep. Confirmed absent
   from the repo's awareness: `grep -rn Putnam Proofs/ Manuscripts/
   BLOG_INDEX.md PLAN.md YAH.md BRAINSTORM.md` → zero hits (2026-08-02).

### The drift chain (in-repo claims falsified this session)

Ledger candidates ten and eleven, pattern identical to the previous nine:
world-facing claims, caught only by retrieval. <!-- EDIT ME: confirm you
want these numbered into the nine-claim ledger -->

- **Wrong object, twice.** `BLOG_INDEX.md:73-75` and the manuscript
  (§1 header, :91-95) describe `a(n)` as "nonempty divisor subsets of n
  containing their own arithmetic mean." Wrong ground set (subsets of
  `{1,…,n}`, not of divisors — `a(10) = 80 > 2^τ(10)` makes this
  impossible) and wrong condition (counted subsets needn't contain their
  mean: `{1,3}` counts for n = 4). The Lean file is correct; only the
  prose drifted.
- **Fabricated quotation.** Both sheets cite the source as A114976
  unattributed "It appears that…" observations. That phrase appears
  nowhere on A114976; it lives on A354741. Quotation marks around words
  transplanted from a different entry.
- **Manufactured status.** §1.3: the claims are "framed as open conjecture
  by OEIS." False — the entry says "might suggest conjectures." Escalation
  chain as it actually ran: hedged observation → misquote → "framed as
  open conjecture" → "OEIS conjectures settled" (BLOG_INDEX cluster A
  title) → nearly a blog headline.

### What survives

- The theorem, its kernel check, and the extension from "the very first
  terms" to all `n` — F0–F2 above. The proof was never wrong; the kernel
  never certified a false statement. Every falsified claim was about the
  world.
- The specific statement `a(n) ≡ τ(n) (mod 2)` appears unrecorded as of
  2026-08-02: web probe on "A114976" surfaced no citing papers (only
  A051293's cross-reference); entry has no formula lines. This is a
  null-search over {general web search, OEIS entry, A051293 neighborhood,
  Putnam archive}, **not** an enumeration — the strongest truthful wording
  is "we found no record," and given the one-line derivation from a
  published Putnam solution, <!-- EDIT ME: decide whether this is worth
  even a footnote --> .
- ~~The documented deviation~~ — **verified 2026-08-03 and the claim
  fails on two counts.** (a) Misattribution: "ROUTE" is a section of
  the repo's own work card (`Formalize/A114976-parity-square.md:37-44`,
  read this session), whose generic heuristic proposed "reflection
  x ↦ n+1-x"; OEIS suggested no involution (live entry: no formula
  lines, hedged comment only). Drift chain across artifacts: card
  "ROUTE" → PLAN.md `0d98351` "Card's reflection involution is
  provably wrong" → `Formalize/INDEX` (at `9ce3a87`) "the ROUTE's
  reflection involution was wrong" → manuscript §1.2 "the OEIS
  ROUTE's" — internal jargon drifting toward a reader-facing OEIS
  attribution. (b) "Recorded in-file" is false: greps this session
  (`reflection|wrong|deviat|route|counterexample|complement` over
  `MeanDivisors.lean`) → zero hits; the deviation is documented only
  in `Formalize/INDEX` and retired PLAN.md, and "provably wrong" is
  proved nowhere in the corpus. Assistant's derivation (this
  session, unverified formally): for n > 1 the only reflection-fixed
  mean class is (n+1)/2, and (n+1)/2 ∣ n forces n = 1, so the
  proposed involution would make a(n) even for all n > 1 —
  contradicting kernel-checked a(4) = 5; reflection also fails to
  preserve the mean-divides-n condition (n = 4: mean 2 ↦ mean 3,
  3 ∤ 4). <!-- EDIT ME: manuscript §1.2's deviation remark, if kept,
  needs rewriting as "our own card's suggested route was wrong" —
  and ledger-candidate decision: is the OEIS-attribution drift
  claim twelve? -->

### Editor's statement

<!-- EDIT ME: your established / refuted / open statement, in your words,
signed and dated. From the session, unedited, yours to rewrite or discard:
"the strongest thing I would sign is the meta-observations about how LLMs
can fail to mine and then spin doing pointless proofs that look good." -->

### Open

- ~~A354741 and A014701 F3 sweeps not yet run~~ — A014701 swept
  2026-08-02 and **survived** (see its entry below). A354741 remains.
- OEIS contribution decision: the parity fact is provable and unrecorded
  on the entry; a comment citing Putnam 2002 A3 would retire the hedge.
  <!-- EDIT ME: whether to contribute upstream -->

---

## A014701 — Rebert's keep-or-double walk: the surviving first-proof candidate

**Verdict (editor's, 2026-08-02, verbatim):** "Yeah, I am satisfied. This
is a real result. … This is a real novel proof." Recorded after the editor
personally reviewed the model-fidelity seams (below). Public wording
constraint: "novel" here means **no reference found by the enumerations
named in this entry, on this date** — the strongest truthful form.

### The mathematics (established, F0–F2, all dated 2026-08-02)

- **Source (F0, live, verbatim):** OEIS A014701 comment — "Conjecture:
  a(n+1) is the minimal number of steps to go from 0 to n, by choosing
  before each step, after the first step, whether to keep the same step
  length or double it. The initial step length is 1. - _Jean-Marc
  Rebert_, May 15 2025." Fetched twice (`oeis show A014701` and
  `curl 'https://oeis.org/search?q=id:A014701&fmt=text'`, identical).
  The only headline candidate whose live entry uses the word
  "Conjecture," attributed and dated. Entry last modified per `%I`:
  edit #20-era; full internal text in session scratchpad.
- **Theorem (F1/F2):** `Proofs/NumberComplexity/StepWalk.lean:368`
  (commit `fa83e94`), cold-checked (`flock .lake/agent.lock lake env
  lean`, exit 0), axioms exactly `[propext, Classical.choice,
  Quot.sound]` for `rebert_conjecture` and `rebert_conjecture_iInf`;
  no `sorry`, no `native_decide`. Statement as printed by the cold check:
  `∀ (n k : ℕ), 1 ≤ n → (IsLeast {j | Reachable n j} k ↔
  k + 2 = (n + 1).bits.length + popCount (n + 1))`.
- **Model:** `Reach` inductive at `StepWalk.lean:219-225` — `one : Reach
  1 1 1`; `keep : (p+s, s)`; `double : (p+2s, 2s)` (length changes
  before the step). Guard `1 ≤ n` documented at `:235-241` (a(1) = 0
  counts the empty walk; no walk returns to 0).

### Fidelity checks (what "faithful to Rebert's sentence" rests on)

Two layers, deliberately distinguished: the kernel certifies the formal
statement is a theorem (layer 1, mechanical, closed above); it cannot
certify the formal statement *is* Rebert's sentence (layer 2, human).
Layer-2 evidence assembled 2026-08-02:

- **Formula bridge (arithmetic, closed):** the theorem's RHS equals the
  entry's own `%F` line (Forgues 2012: `a(n) = floor(log_2 n) + wt(n)
  − 1` at `n+1`) and is shape-identical to Branicky's program line
  (2026-03-19: `bit_count + bit_length − 2`). Kernel spot-check:
  `(Nat.bits m).length = ⌊log₂ m⌋ + 1` and `bits.count true =
  popcount` for m = 1..12.
- **Brute-force eval (closed):** enumeration mirroring the `Reach`
  constructors verbatim gives min-steps = a(n+1) for all n = 1..30,
  with optimal walks matching the prose reading, e.g. n = 7: steps
  `[1,2,4]`, positions 1 → 3 → 7; n = 12: `[1,1,2,4,4]`. (Scratch
  eval `WalkEval.lean`; a transcription of `Reach`, not the theorem —
  the all-n guarantee is the theorem itself.)
- **In-file ground checks:** kernel checks against published terms
  (`StepWalk.lean:440` region; ran in the cold pass).
- **Editor's read (closed 2026-08-02):** the editor reviewed Rebert's
  sentence against the `Reach` constructors and the guard, and signed
  the verdict above.

### The novelty sweep (F3), corpora named, run 2026-08-02

The formula is classical — novelty lives **only** in the walk-model
equivalence. No record of that equivalence found in:

1. **The live entry, one hop deep** (per law 9): all `%F`/`%H` content.
   Four independent proved characterizations of a(n) exist (Forgues;
   `A056792 − 1` add-1-or-double minimality; Gruber–Holzer MFCS 2021
   Lemma 8 max-form, doi:10.4230/LIPIcs.MFCS.2021.52; Cunningham 2024
   bijective base-2 digit sum) — none is the keep-or-double walk.
2. **RSOS 2026 assembly-theory paper** (doi:10.1098/rsos.260082, the
   entry's only post-conjecture reference; full text grepped from the
   editor's copy, 4,728 lines): uses A014701 solely as the classical
   "depth index" bound; no Rebert, no walk model.
3. **Web citation probe** on "A014701": nothing addressing the comment.
4. **SeqFan:** old pipermail host dead (connection refused, verified);
   last Wayback index snapshot 2024-06-19 **predates the conjecture**,
   so the old archives cannot discuss it. Current list = Google Groups
   (per OEIS wiki, rev. 2026-07-20); site-scoped searches for A014701
   and Rebert: null. Caveat: Google Groups search indexing is spotty —
   this corpus is probed, not enumerated.
5. **sequencelib** (provables.org; arXiv:2601.11757; 25,905 `.lean`
   files): cloned in full and grepped — zero hits for A014701 (or any
   campaign A-number). Their theorems are ground-value checks, not
   conjecture proofs. Re-run: `git clone --depth 1
   https://github.com/provables/sequencelib && grep -rl A014701`.

**Bounded residuals, disclosed:** (a) pre-2024 SeqFan archives are
unreachable except via bulk Wayback download — they predate the
conjecture but could contain the walk model arising independently;
(b) an assistant derivation (unverified, assistant's) reduces the walk
to bijective base-2 digit sums one step from Cunningham's on-entry
comment — suggesting the proof is exercise-adjacent. Nobody appears to
have done the exercise; the editor's framing call on "small labeled
conjecture, first to close it" vs. headline is still open for the post.

### Open

- Framing tier for the blog post (headline vs. supporting) — editor's.
- Whether to contribute the proof reference to the OEIS entry,
  retiring the "Conjecture" label.

---

## A354741 — almost every Boolean matrix has full row rank

> [!NOTE]
> I actually need to walk through and verify the
> theorem defs but the agent was being useless so
> I had it dump the present context.

**Verdict (editor's):** <!-- EDIT ME: your signed one-liner. The
assistant's raw material, marked as such, post-correction: "the
theorem is real, kernel-checked, and editor-verified faithful; the
exact-fullness dichotomy (limit 1 over the Boolean semiring vs 0.2888
over GF(2)) is the phenomenon, it is precisely the part prior art
does not contain, and no record of it was found by any enumeration
below — first recorded proof of the comment, supporting-to-headline
tier." -->

### The mathematics (established, F0–F2, all dated 2026-08-02)

- **Source (F0, live, verbatim):** OEIS A354741 (Geoffrey Critzer,
  2022-06-12; last edit #44, 2022-07-14, row 5 from Pontus von
  Brömssen) comment, unattributed and hedged: "Compare to A286331
  which counts n X n matrices over the field GF(2). … Here, it appears
  (from some empirical computations) that the limiting probability
  that a Boolean matrix has rank n is 1." Fetched twice (`oeis show
  A354741` and `curl 'https://oeis.org/search?q=id:A354741&fmt=text'`,
  saved to session scratchpad). No `%D` references; one `%H` link
  (Wikipedia "Boolean matrix"). This is the entry whose "it appears"
  phrasing the A114976 sheets misquoted. Modality: an empirical
  observation, not labeled "Conjecture" (unlike A014701).
  Provenance wrinkle, retrieved: the A-number was recycled — a
  P. Lipski submission held A354741 and was deleted ("rifo A354423",
  OeisWiki Deleted sequences/2022, fetched 2026-08-02); irrelevant to
  the live entry, but it pollutes web probes on the A-number.
- **Theorem (F1/F2):**
  `Proofs/BilinearComplexity/BooleanRankGeneric.lean:562`
  (`fullRowRankFraction_tendsto_one`, commit `3ec26ec`):
  `Tendsto fullRowRankFraction atTop (nhds 1)` where
  `fullRowRankFraction n = fullRowRankCount n / 2^(n·n)` counts
  matrices with `boolRowRank = n`. Cold check 2026-08-02:
  `flock .lake/agent.lock sh -c 'lake build
  BilinearComplexity.BooleanRank && lake env lean
  Proofs/BilinearComplexity/BooleanRankGeneric.lean'`, exit 0. In-file
  axiom audit (all 33 named declarations): 31 depend on exactly
  `[propext, Classical.choice, Quot.sound]`, 2 defs axiom-free; no
  `sorry`, no `native_decide` anywhere in the cold log.
- **Fidelity (layer 2) — closed by the editor, 2026-08-03.** The
  editor evaluated five verbatim source↔Lean pairs side by side and
  signed off, verbatim: **"Those all look good to me."** The pairs
  (session record, 2026-08-03): (1) `%N` "row rank" ↔ `boolRowRank`
  docstring; (2) the `%t` Mathematica program (`bospan` = or-span,
  minimal spanning row subset) ↔ `rowsSum`/`rowSpan`/`BoolRowRankLE`
  (`BooleanRankGeneric.lean:103,124,147`), with four named
  discrepancies judged immaterial — Clip-vs-or, empty-subset
  inclusion, zero-row deletion, and `Select[...][[1]]` relying on
  Mathematica's `Subsets` size-ordering (the weakest link, external
  semantics not independently verified; covered empirically by the
  diagonal checks); (3) the `%C` limit sentence ↔
  `fullRowRankFraction_tendsto_one`, reading "rank" as the `%N`
  title's row rank, "probability" as uniform counting measure,
  "limiting" as `Tendsto atTop`; (4) the comment's GF(2) contrast ↔
  the in-file 𝔽₂ block (`:590-598`, 156 vs 168 =
  (2³−1)(2³−2)(2³−4) over the same 512 matrices, ruling out xor
  leakage); (5) published terms ↔ in-kernel `decide` checks
  T(1,1)=1, T(2,2)=6 (`:464-469`), T(3,3)=156 (`:590`). Diagonals
  n = 4, 5 are not kernel-checked (2¹⁶, 2²⁵ matrices).

### The novelty sweep (F3), corpora classified, run 2026-08-02/03

No record found of the statement "P(Boolean row rank = n) → 1" (or a
proof of the comment) in:

1. **Enumerated — the live entry one hop deep:** the single `%H` link
   (Wikipedia "Boolean matrix", a 19-line stub, zero mentions of rank
   or randomness; via `wiki article`), all `%F` lines (exact
   small-rank counts only), and every `%Y` crossref read this session
   (A000012, A060867, A002416, A048651, A064230, A286331, A355333).
   None states the row-rank limit. A064230 (rational rank analogue)
   carries the Komlós/KKS "almost all invertible" comment — the
   real-rank neighbour is already recorded one hop away, for a
   different rank.
2. **Enumerated — sequencelib:** fresh shallow clone 2026-08-02,
   25,905 `.lean` files, `grep -rl A354741` → zero. Re-run:
   `git clone --depth 1 https://github.com/provables/sequencelib &&
   grep -rl A354741 sequencelib`.
3. **Enumerated (vacuously) — SeqFan 2008-10…2012-07:** the Wayback
   copy of `list.seqfan.eu/anumref/` (snapshot 2023-02-07; its
   by-month index ends 2012-July) enumerates A-number references in
   old posts; A354741 absent and the coverage predates the entry.
4. **Probed — web citation on "A354741":** only OEIS mirrors, the
   crossref entries, and the recycled-number deletion note. No citing
   paper.
5. **Probed — SeqFan current era:** Google Groups site-scoped
   searches, null; indexing spotty. **Unreachable:** pipermail
   2022-06 → 2024-06 (dead host; the window that could discuss the
   entry) — bulk Wayback download would be needed.
6. **Retrieved literature (the `.tasks/` neighbours, re-fetched
   fresh):**
   - Pourmoradnasseri–Theis, EJC 24(2) #P2.37 (2017), full text read
     (session scratchpad `pt2017.txt`). Corollary 6.1, verbatim: "In
     the range 1/n ≪ p ⩽ 1/2, we have χ(G^{n,p}) = (1 − o(1))n" —
     and χ(G(M)) = rc(M), the rectangle covering number. Cover
     (Schein-type) rank, asymptotically full, not exactly full.
     Body grep 2026-08-03 (same full text, 2,328 lines): zero
     occurrences of "row rank", "antichain", "incomparable";
     "Sperner" only as bibliography item [13] (Froncek–Jerebic–
     Klavžar–Kovár, CPC 16 (2007) 271–275), cited in PT's intro
     solely as a deterministic application of rectangle covers to
     strong isometric dimension. Neither the exact-fullness
     statement nor the antichain mechanism appears in PT's text.
   - Izhakian–Janson–Rhodes, arXiv:1109.5503
     (`References/arXiv-1109-5503/paper.tex`), Theorem 1:
     triangular/superboolean rank `/ log_Q n → 2+√2` in probability.
     Different rank, Θ(log n).
   - Komlós 1967/1968/1981 / Kahn–Komlós–Szemerédi 1995: rational/±1
     rank. Upgraded from probe to a read textbook statement —
     Bollobás, *Random Graphs* 2nd ed., §14.2 p. 394, read visually
     from scan 2026-08-03, verbatim: "Komlós (1967, 1968) proved that
     this probability tends to 1 as n → ∞" (the probability that a
     random 0–1 matrix of order n is non-singular over ℝ).
     Corroborated by the A064230 comment (live, 2026-08-02).
   - arXiv:2601.13900 (2026 survey of Boolean/binary rank,
     `References/arXiv-2601-13900/survey.tex`), post-dating the
     repo's sweep: grepped — no random-matrix rank theorem at all.
7. **Textbook sweep for the mechanism** (is "a random family of
   subsets is an antichain a.a.s." a recorded statement?), run
   2026-08-02/03:
   - **Enumerated (full-text grep), null:** Jukna, *Extremal
     Combinatorics* draft, 301 pp
     (mathematik.uni-muenchen.de/~kpanagio/draft.pdf) — nearest
     object is the Erdős–Füredi 1983 lemma (his Lemma 20.5): the
     same (3/4)ⁿ computation for a *triple* condition
     A∩B ⊆ C ⊆ A∪B, not pairwise domination. Alon–Spencer, *The
     Probabilistic Method* 4th ed. 2015 (editor-supplied PDF,
     lib.ysu.am) — only antichain content is the LYM/Sperner
     Probabilistic Lens (p. 237 region), a deterministic bound; zero
     hits for incomparable / (3/4) / containment-a.a.s.
   - **Index-enumerated + targeted read, null:** Bollobás, *Random
     Graphs* 2nd ed. 2001 (djvu scan, no text layer; full A–Z index
     read visually, §14.2 "Random Matrices" pp. 394–395 read) — that
     section is entirely rational-rank (Komlós; Littlewood–Offord
     with Sperner's lemma as a tool; "strong rank" defined by linear
     independence over ℚ).
   - **Unreached, TODO:** Bollobás, *Combinatorics: Set Systems,
     Hypergraphs, Families of Vectors and Combinatorial Probability*,
     CUP 1986, xii+177 pp — the likeliest home of the statement;
     lending copy at https://archive.org/details/combinatorics00bela.
     <!-- EDIT ME/TODO: borrow, check the Sperner chapters, close -->

**Where the novelty lives (corrected 2026-08-03; supersedes the
assistant's earlier "the phenomenon is one line from published work"
framing, which conflated two statements — correction prompted by the
editor's question).** Composing PT Cor. 6.1 with the file's bridge
`boolRank ≤ boolRowRank` (`BooleanRankGeneric.lean:267`) yields only
the **contrast-free weakening** "row rank ≥ (1−o(1))n a.a.s." —
contrast-free because the same asymptotic holds over GF(2): by the
classical rank-count formula (rank-r n×n matrices over 𝔽_q number
(∏_{i<r}(qⁿ−qⁱ))² / ∏_{i<r}(qʳ−qⁱ)), at n = 30 over GF(2),
P(rank ≥ n−3) ≈ 0.999953 while P(rank = n) ≈ 0.288788 (sage,
2026-08-03, session record). The comment's phenomenon — the
**exact-fullness dichotomy**, limit 1 over the Boolean semiring vs
∏(1−2⁻ⁱ) ≈ 0.2888 over the field — lives entirely at exactness,
which PT does not address and which no enumeration above found
recorded anywhere. PT remains the nearest recorded neighbour and
must be cited in any writeup; it is not subsuming prior art.
Sharpening, **checked 2026-08-03**: A355333 fetched live
(`oeis show A355333`; published through n = 5, keyword `more`).
Full-Schein-rank diagonal fractions T(n,n)/2^(n²) = 0.5, 0.375,
0.3047, 0.2457, 0.1914 for n = 1..5 — strictly decreasing at every
published step (row-splitting validated: each row sums to 2^(n²)).
On published data, exactness fails at PT's own rank statistic; the
dichotomy is specific to row rank. Prose caveat: five data points —
"decreasing over the published rows (n ≤ 5)" is the strongest
truthful form; behavior beyond n = 5 is open.
<!-- EDIT ME: keep/strike is yours; assistant recommends keep -->

**Bounded residuals, disclosed:** (a) SeqFan 2022-06→2024-06 and
current Google Groups — probed/unreachable, see 5; (b) Sherstov's
communication-complexity lecture notes (PT's pointer for the p = 1/2
chromatic number) not retrieved — same rc object as PT, two hops out;
(c) Bollobás *Combinatorics* 1986 — unreached, see 7; (d) Komlós/KKS
read at the textbook-statement level (Bollobás §14.2), not from the
original papers; (e) PT's reference [13] (Sperner's theorem ×
biclique coverings, CPC 2007) — unread, two hops out; title suggests
deterministic, checked only via PT's citing sentence (2026-08-03).

### Session record (editor's words, verbatim, dated)

- 2026-08-03, on the five fidelity pairs: "Those all look good to
  me." (Recorded above as the layer-2 sign-off.)
- 2026-08-03, the question that forced the novelty correction:
  "You're saying prior art is actually better and more complete?" —
  answered no, after the sage GF(2) computation; see the corrected
  paragraph above.
- 2026-08-03, the editor's novelty challenge, verbatim: "Well it
  sounds like they already new this proof or deemed it trivial"
  [sic]. Prompted the PT body grep (corpus 6: neither statement nor
  mechanism present) and a live A354741 re-fetch (comment verbatim
  unchanged; no proof or limit formula on the entry). "Already knew"
  unsupported as far as the two primary artifacts reach; "deemed it
  trivial" unfalsifiable and undisputed — F3 claims recordedness,
  not difficulty. The depth-vs-priority question it raised is
  pending the editor's answer.
- 2026-08-03, on the framing tier, verbatim: "A354741 - framing
  decision remains my own since all of the required research
  materials should be captured it its section" [sic]. The verdict
  line, framing tier, and the manuscript §6 ranking therefore stay
  open as editor-only items; the A014701 contrast lives in the
  novelty-wording and framing bullets below, the depth-vs-priority
  question in this record. Bollobás 1986 dropped from session scope
  the same day (editor: tracked in their own work queue); it remains
  residual (c).

### Editor's statement

<!-- EDIT ME: your established / refuted / open statement, signed and
dated. Raw material, the assistant's: established — the theorem, its
kernel check, its faithfulness (your five-pair read); the absence of
any record of the exact-fullness dichotomy across the enumerations
named above. Open — Bollobás 1986, the A355333 empirical claim, the
SeqFan 2022-24 window. -->

### Open (draft points for the editor)

- **Verdict line** (top of entry) and **editor's statement** — yours.
- **Novelty wording for public prose** — the strongest truthful form:
  "no record found by the enumerations named in this entry, as of
  2026-08-03; nearest recorded neighbour PT 2017 (cited), which
  addresses cover rank and not exact fullness." "Settles an OEIS
  conjecture" is unavailable — the source is a hedged, unattributed
  observation, never labeled Conjecture (contrast A014701).
  <!-- EDIT ME: adopt / rewrite -->
- **Framing tier** (headline vs. supporting, vs. A014701) — the
  corrected adjacency analysis cuts both ways: mathematics closer to
  published work than A014701's, but the dichotomy framing
  (1 vs 0.2888) is sharper and the sweep broader. <!-- EDIT ME -->
- **TODO — Bollobás *Combinatorics* 1986** (archive.org lending copy,
  pointer in 7): the last named corpus for the mechanism sweep.
- ~~TODO — A355333 check~~ — run 2026-08-03, see the sharpening
  paragraph above; keep/strike decision pending editor.
- **OEIS contribution decision:** the comment is provable and the
  entry records no proof; a comment or link would retire the hedge.
  <!-- EDIT ME -->
- **Law-5 nit, both sheets:** BLOG_INDEX.md:36-37 and manuscript
  §6 quote the comment as "it appears from some empirical
  computations" — the entry has "it appears (from some empirical
  computations)"; words verbatim, parentheses silently dropped
  inside quotation marks. Fix when the sheets are next touched.
- Manuscript §6 and BLOG_INDEX prose otherwise checked against the
  Lean statement 2026-08-02: correct object, correct pointers, PT
  characterization accurate — no A114976-style drift found. The §6
  line "strongest first-proof claim in the corpus" is a ranking the
  corrected adjacency analysis may revise. <!-- EDIT ME -->
