# OEIS Conjecture Candidates — Mining Sweep 2026-08-05

## methodology

Six parallel `goof oeis search` sweeps over the repo's topic
clusters (extremal combinatorics, addition chains and number
complexity, covering systems, arithmetic functions, enumerative
and algebraic counting) plus one orthogonal conjecture-marker
sweep ("no proof is known", "it appears that", "remains open",
keyword `hard`). Every promising hit was pulled in full via
`goof oeis show`; all conjecture quotes below are verbatim from
those live pulls, not model memory.

Candidates were deduplicated against three exclusion sets:
the 87 A-numbers mentioned in `Formalize/` cards, the 61
A-numbers in `Proofs/`, and everything queued in `PLAN.md`
(wave 2, P8 statement-archive batch, covering arc C1-C7,
gated items). Sequences that appear in the repo but carry a
*different, uncarded* conjecture are included with the overlap
noted — the adjacency is an asset, not a duplicate.

Confidence discipline: "open" below means the subagent found
no "proved by" comment in the entry and the entry carries
open-problem markers. Where openness or provability is
uncertain, it is flagged inline.

## candidates

### Tier 1 — low-hanging fruit (statable today, adjacent to existing infra)

#### A146968 — Brocard's problem (n! + 1 = m^2)
- **Conjecture**: "The problem of whether there are any other terms in this sequence, Brocard's problem, has been unsolved since 1876." (comment in A085692, Stefan Steinerberger, Mar 19 2006). Known terms: 4, 5, 7.
- **Attribution**: Brocard 1876; Ramanujan asked it independently.
- **Status**: open. Verified to n <= 10^12 (Matson 2019). Keywords `bref, nonn, hard`.
- **Repo adjacency**: none direct; pure `Nat.factorial` + `IsSquare`, both Mathlib-native. Fits the statement-archive pattern of P8.
- **Lean feasibility**: high. Statement: `∀ n, (∃ m, n ! + 1 = m * m) → n ∈ ({4, 5, 7} : Finset ℕ)`. No new defs.
- **Sanity layer**: `native_decide` that 4, 5, 7 satisfy the predicate; exhaustive check that no other n <= 100 does (factorials grow fast, so the window check is cheap; squares testable via `Nat.sqrt`).

#### A174865 — Noe: odd abundant with even abundance is Zumkeller
- **Conjecture**: "There are 1989 odd Zumkeller numbers less than 10^6; they are exactly the odd abundant numbers that have even abundance, A174865." (T. D. Noe, Mar 31 2010); "All 205283 odd abundant numbers less than 10^8 that have even abundance (see A174865) are Zumkeller numbers." (T. D. Noe, Nov 14 2010)
- **Attribution**: T. D. Noe, 2010.
- **Status**: open. Phrased empirically; no later proof comment.
- **Repo adjacency**: strongest in the batch. `IsZumkeller` lives in `Proofs/Enumerative`; the easy direction (Zumkeller implies abundant-or-perfect with even sigma) is nearly free from the existing sigma-half bridge. A083207 is heavily carded but this specific Noe biconditional is not.
- **Lean feasibility**: high. Both directions statable today. The hard direction (odd + abundant + even abundance implies Zumkeller) is the open content.
- **Sanity layer**: `native_decide` sweep over odd n <= 10^4 checking the biconditional, reusing the existing decidable Zumkeller instance.

#### A000166 — Sun: derangement numbers are never perfect powers (except D(4) = 9)
- **Conjecture**: "Conjecture: a(n) with n > 2 is a perfect power only for n = 4 with a(4) = 3^2. This has been verified for n <= 1000." (Zhi-Wei Sun, Jan 09 2025)
- **Attribution**: Zhi-Wei Sun, Jan 2025.
- **Status**: open, and very fresh (2025).
- **Repo adjacency**: sibling of the carded A000041 Sun perfect-power conjecture — same statement shape, same sanity-layer machinery, so the two cards can share a `IsPerfectPower` helper. Mathlib has `Equiv.Derangements` and the recurrence D(n) = (n-1)(D(n-1) + D(n-2)).
- **Lean feasibility**: high for statement + archive. Full proof is Diophantine-hard, like its A000041 sibling.
- **Sanity layer**: `native_decide` for n <= 60 via the recurrence; perfect-power test is decidable.

#### A005153 — Switkay: every odd number >= 3 is prime + practical
- **Conjecture**: "Conjecture: every odd number, beginning with 3, is the sum of a prime number and a practical number. Note that this conjecture occupies the space between the unproven Goldbach conjecture and the theorem that every even number, beginning with 2, is the sum of two practical numbers (Melfi's 1996 proof of Margenstern's conjecture)." (Hal M. Switkay, Jan 28 2023)
- **Attribution**: Hal M. Switkay, Jan 2023.
- **Status**: open. A005153 itself is all over the repo, but this conjecture is uncarded.
- **Repo adjacency**: `Nat.Practical` and Stewart's criterion already exist in `Proofs/Enumerative`. Statement cost is near zero.
- **Lean feasibility**: high for the archive card; the full claim is Goldbach-adjacent, honestly out of reach. Ideal intended-sorry target.
- **Sanity layer**: `native_decide` for odd n in [3, 5000] using the existing practical-number decidability.

#### A244743 — unboundedness of the integer-complexity defect ||n-1|| - ||n||
- **Conjecture**: "It is conjectured that ||n-1||-||n|| is not bounded. But there is no proof that the sequence is infinite or is well defined." (comment in A244743; ||n|| = A005245)
- **Attribution**: implicit in the entry; no named author on the conjecture line.
- **Status**: open. Known terms a(0)=6 through a(8)=612360000.
- **Repo adjacency**: `complexity` (A005245) is already defined and proved-about in `Proofs/NumberComplexity`. The statement `∀ k, ∃ n, complexity (n-1) - complexity n = k` (with the usual cast guards) is cheap given existing defs.
- **Lean feasibility**: high for statement; the sequence's well-definedness *is* the conjecture, which makes it a clean archive card. Proof out of reach.
- **Sanity layer**: witness certificates for k <= 5: verify `complexity` values at 6, 12, 24, 108, 720, 1440 against the existing evaluation machinery.

#### A192787 / A073101 — Erdős–Straus: 4/n = 1/x + 1/y + 1/z
- **Conjecture**: "In 1948 Erdős and Straus conjectured that for any positive integer n >= 2 the equation 4/n = 1/x + 1/y + 1/z has a solution with positive integers x, y and z" (A073101 comment); "The Erdős-Straus conjecture is that a(n) > 0 for n > 1. Swett verified the conjecture for n < 10^14." (A192787 comment)
- **Attribution**: Erdős and Straus, 1948.
- **Status**: open. Famous.
- **Repo adjacency**: fits the Erdős-problem arc (`Proofs/Erdos`) organizationally; no def reuse, but the cleared-denominator form needs only `Nat` arithmetic.
- **Lean feasibility**: high for statement via `4 * x * y * z = n * (y*z + x*z + x*y)`, avoiding rationals entirely. STYLE.md-clean (no subtraction, no division).
- **Sanity layer**: `native_decide` existence check for n <= 500 with the bound x <= n (since 4/n <= 3/x forces x <= 3n/4).

### Tier 2 — medium effort (needs modest new definitions)

#### A373686 — Somu–Tran: every n is practical + two squares
- **Conjecture**: "Somu and Tran (2024) proved that a(n) > 0 for sufficiently large n and conjectured that a(n) > 0 for all n > 0. The conjecture was checked up to 10^8." (entry comment)
- **Attribution**: Somu and Tran, 2024.
- **Status**: open for all n, proved for sufficiently large n. The threshold N(4) ≈ 8·exp(2·10^80) (derived from Somu–Tran's effective Theorem 2) is far beyond any computational reach — **archive only**, not completable. However, the paper's Theorem 1 (every positive integer is practical + triangular, resolving a Sun conjecture) has **no threshold** and IS a completable full-proof target.
- **Repo adjacency**: `Nat.Practical` exists. Sum-of-two-squares is Mathlib-supported (`Nat.sum_two_squares`-adjacent lemmas exist; the existential itself is elementary).
- **Lean feasibility**: high for statement; archive only for the two-squares conjecture. The completable item in this neighbourhood is Theorem 1 (practical + triangular).
- **Sanity layer**: `native_decide` for n <= 10^4.

#### A351243 — Selfridge–Lacampagne counterexamples and the 3^m + 4 pattern
- **Conjecture**: "The conjecture was that every natural number k not divisible by 3 can be written as the quotient of two terms chosen from A147991." ... "It is not known if there are infinitely many counterexamples to the conjecture, but perhaps 3^m+4, for m >= 5 and odd, are." (entry comments)
- **Attribution**: Selfridge and Lacampagne (original); the counterexample-family speculation is from the entry (Shallit et al. resolved the original conjecture negatively).
- **Status**: original conjecture disproved; infinitude of counterexamples open.
- **Repo adjacency**: digit predicates via `Nat.digits 3` mirror the `stanleyDigits` work on A003278/A005836 in `Proofs/Enumerative`.
- **Lean feasibility**: medium. Needs a def for A147991 membership (balanced ternary with no 0 trit, i.e. trits in {−1,+1} — *not* base-3 digits in {0,1}, which is A005836) and a bounded-quotient search argument to certify a counterexample; the bounding lemma is real but modest work.
- **Sanity layer**: certify 247 is a counterexample by exhaustive search with a proved search bound.

#### A131646 — Sloane: numbers writable in bases 2..18 with digits 0..9 only
- **Conjecture**: "It is a plausible conjecture that there are no more terms, but this has not been proved." (N. J. A. Sloane, Nov 17 2017). 20 known terms, checked to 2^20356.
- **Attribution**: N. J. A. Sloane, 2017.
- **Status**: open.
- **Repo adjacency**: none direct; `Nat.digits` makes the predicate one line. Only bases 11..18 matter (digits in bases <= 10 are automatically <= 9) — a cute first lemma.
- **Lean feasibility**: medium-high. Finiteness claim is the intended sorry; the digit predicate and the 20-member certificate are easy.
- **Sanity layer**: `native_decide` membership for all 20 terms (the two 19-digit terms may need `Nat.digits` evaluation care) plus completeness below 10^6.

#### A141386 — Sun: exceptions for x^2 + y^2 + 5*triangular
- **Conjecture**: "Conjectured to be complete list of numbers not of the form x^2 + y^2 + 5*triangular number." (sequence name). Terms: 3, 11, 12, 27, 129, 138, 273.
- **Attribution**: Zhi-Wei Sun (part of his representability program).
- **Status**: open. Low risk of mislabeling but worth a literature check — several Sun representability conjectures from that era have since been proved.
- **Repo adjacency**: none direct; elementary quadratic-form statement.
- **Lean feasibility**: medium. Representability for fixed n is a bounded search (x, y <= sqrt n, z bounded); the completeness claim is the sorry.
- **Sanity layer**: prove non-representability of the 7 exceptions by `decide` over the bounded search space; prove representability for all other n <= 300.

#### A007850 — Lava: Giuga numbers solve n' = n + 1
- **Conjecture**: "Conjecture: Giuga numbers are the solution of the differential equation n' = n + 1, where n' is the arithmetic derivative of n." (Paolo P. Lava, Nov 16 2009)
- **Attribution**: Paolo P. Lava, 2009.
- **Status**: open (holds for every known Giuga number; Schneider's A007850 comment reports the Giuga list complete through 8 prime factors — a completeness claim about the list, not a verification over composites). LANDED 2026-08-20 in f061efe as `Proofs/Scratch/GiugaDerivative.lean` (reviewer trio passed): the forward direction and reusable arithmetic-derivative layer are sorry-free and formalize Grau–Oller-Marcén's known `a = 1` case (arXiv:1103.2298, JIS 12.4.1); the converse is the one intended `sorry`, so the file as a whole and `lava_conjecture` are not completed proofs. Any first-formalization language is found-no-record, not priority.
- **Repo adjacency**: none direct; needs an arithmetic-derivative def (A003415), a genuinely reusable piece of infrastructure for future cards.
- **Lean feasibility**: medium. Both predicates decidable; one direction (n' = n+1 implies Giuga) is provable from the definition via squarefreeness and the p | n/p - 1 condition — worth attempting, not just archiving. The other direction (Giuga implies n' = n+1, i.e. the multiplier a in Grau Ribas's n' = a·n + 1 is always 1) is the open content.
- **Sanity layer**: verify 30, 858, 1722 satisfy both predicates by `native_decide`.

#### A045652 — Schur numbers, exact small values
- **Conjecture**: not a single conjecture but an open frontier: "The best known lower bounds for the next terms are due to Fredricksen and Sweet (see links): a(6) >= 536 and a(7) >= 1680. - Dmitry Kamenetsky, Oct 23 2019"; "A partition showing that a(7) >= 1696 was demonstrated in 2021 - Fred Rowley, Mar 01 2023". Known exactly: 1, 4, 13, 44, 160.
- **Attribution**: Schur 1916 (definition); a(5) = 160 is Heule's 2017 SAT result.
- **Status**: a(6) onward open; a(1)..a(4) proved classically, a(5) proved via SAT (2 PB of proof — not importable).
- **Repo adjacency**: sum-free colorings sit next to the restricted-sumset work in `Erdos880/`; Mathlib has Schur-like machinery in `Combinatorics.Schnirelmann`-adjacent files, worth a `/leandoc` check.
- **Lean feasibility**: medium. Formalize the def, prove a(2) = 4 and a(3) = 13 by witness + `decide` exhaustion; archive a(4) = 44 (search space ~3^44 is too big for decide, needs a cleverer certificate).
- **Sanity layer**: the witness colorings for lower bounds are tiny and checkable by `decide`.

#### A349044 — non-Brauer gap: can l*(n) - l(n) exceed 1?
- **Conjecture**: "For entries at least through 41506, these numbers satisfy l*(n) = A003313(n) + 1. It seems likely that larger differences between l*(n) and A003313(n) occur for later entries in this sequence, but it is unclear whether any n with a larger difference have been found." (entry comment)
- **Attribution**: entry comment, unattributed.
- **Status**: open question (both directions: no proof the gap is bounded, no example of gap >= 2).
- **Repo adjacency**: `IsAddChain` and `l` exist in `Proofs/NumberComplexity`; needs a Brauer-chain (star-chain) variant def — a natural extension of existing infra, echoing the permissive/ascending equivalence just landed for A003313.
- **Lean feasibility**: medium. Defs cheap given existing chain machinery; certifying l*(12509) = l(12509) + 1 requires exhaustive chain search, expensive but bounded.
- **Sanity layer**: l and l* agree on all n <= 100 (both computable by bounded search for small n).

#### A293771 — Whitney: reads are never needed in the cache-memory machine
- **Conjecture**: "Conjecture: reading from memory (operation 2) is never needed to get to a number in the minimal number of steps." Also: "Conjecture II: For each n, there is a minimal-length program for n that stores numbers in memory in increasing order." and "Conjecture III: ... difference between successive numbers stored in memory is strictly increasing." "All three conjectures are empirically verified for all programs of length 23 or less, and all values of n up to 2326." (Glen Whitney, Oct 12 2021)
- **Attribution**: Glen Whitney, 2021.
- **Status**: open. Note the entry's caveat: with a *fixed* memory sequence the claim fails, so quantifier order matters — a statement-soundness trap the card must get right.
- **Repo adjacency**: operational-semantics flavor matches the `Expr`/chain minimization style of `Proofs/NumberComplexity`; a third computation model alongside complexity and chains.
- **Lean feasibility**: medium. Small-step semantics def (~30 lines), then conjecture I as `∀ n, ∃ minimal read-free program`. Proof genuinely open but the finite structure invites partial results.
- **Sanity layer**: enumerate programs of length <= 10 and check read-freeness of some minimal program per reachable n, via `native_decide`.

#### A080210 — multiplicity lower bound for disjoint covering systems
- **Conjecture**: formula `a(n) = floor(Lpf(n) * phi(n) / n) + 1` stated as fact in the entry with no proof reference.
- **Attribution**: entry author; provenance unclear — flagged low confidence, likely folklore-proved in the DCS literature (Znám-era results). Verify before carding.
- **Status**: likely proved-but-unformalized.
- **Repo adjacency**: direct fit for the covering arc (`Proofs/Erdos/Covering`, C1-C5 lanes); `Nat.totient` in Mathlib, **largest** prime factor (A006530) from `Nat.primeFactors` — note that "Lpf" in the OEIS formula means *largest* prime factor, not least, despite the lowercase "l".
- **Lean feasibility**: medium-high, but the entry is **not proof-ready**: it lacks a definition of "multiplicity" for a DCS, and the formula is stated as fact with no proof reference. The Zamojski survey linked from the entry must be consulted before carding. This is NOT the only completable-in-full candidate in the covering cluster without that groundwork.
- **Sanity layer**: compute both sides for n <= 1000.

### Tier 3 — heavy lift (needs significant new infrastructure)

#### A309370 — Sidon subsets of the hypercube
- **Conjecture**: "Conjecture: a(n) is asymptotic to 2^(n/2+1)." (entry formula section). Bracketing bounds: Lindström (1969) lower, Cohen–Litsyn–Zémor 2^(0.57526 n) upper.
- **Attribution**: entry author (unattributed line); active area (lower-bound records through n = 24 as of 2026).
- **Status**: open.
- **Lean feasibility**: the asymptotic needs `IsBigO` over atTop plus a Sidon-in-`(ZMod 2)^n` def; exact small values are decidable. The Sidon def itself is reusable for A390813.
- **Sanity layer**: exact values 1, 2, 3, 5, 7, 12, 15 for n = 0..6 (offset 0, so n ≤ 6) by exhaustive `native_decide`.

#### A390813 — Erdős: Sidon subsets of the squares
- **Conjecture**: "Erdős asks if a(n) is n^(1-o(1))" (entry comment, referencing the Erdős problems site).
- **Attribution**: Erdős.
- **Status**: open.
- **Lean feasibility**: heavy — the o(1) exponent form needs careful asymptotic phrasing (the repo's `IsLittleO` toolbox from the asymptotics work applies). Statement-archive only.
- **Sanity layer**: exact a(n) for n <= 15 by exhaustive search.

#### A265262 — Erdős–Turán additive basis conjecture via the hemitropic tree
- **Conjecture**: "Erdős and Turán conjectured that the profile of a basis is always unbounded (see the Erdős and Turán link). The conjecture is, up till now, still undecided." (entry comment)
- **Attribution**: Erdős and Turán, 1941.
- **Status**: open, famous.
- **Lean feasibility**: heavy. The representation-function def is easy; the value here is the entry's tree reformulation (conjecture iff no infinite bounded zero-free branch), which is a König's-lemma-shaped statement Lean handles well. A card formalizing the *equivalence* would be novel and self-contained.
- **Sanity layer**: verify the first tree levels against listed terms.

#### A046094 — Agoh–Giuga congruence
- **Conjecture**: "a(n) is conjectured to be 1 iff n is prime" (sequence name), where a(n) = -n*Bernoulli(n-1) mod n.
- **Attribution**: Agoh (equivalence with Giuga's 1950 conjecture is a known theorem).
- **Status**: open.
- **Lean feasibility**: heavy. Mathlib has `Polynomial.bernoulli`, but the mod-n congruence for rational Bernoulli numbers needs von Staudt–Clausen-grade plumbing (denominator control) before the statement is even sound. The forward direction (prime implies 1) is a provable warm-up.
- **Sanity layer**: verify a(n) for n <= 30 once the congruence is defined computably.

#### A209312 — Sun-style symmetric prime/practical offsets
- **Conjecture**: "Conjecture: a(n)>0 for all n>2." (a(n) counts practical p < n with n-p, n+p both prime or both practical); "This has been verified for n up to 10^7." (entry comments)
- **Attribution**: uncredited in the pull; style strongly suggests Zhi-Wei Sun — verify before carding.
- **Status**: open.
- **Lean feasibility**: statement is cheap given `Nat.Practical`, but the even/odd case split makes the card fiddly; proof hopeless. Lower priority than Switkay's cleaner statement in Tier 1.
- **Sanity layer**: `native_decide` for n <= 2000.

#### A222603 — the practical-number successor graph is a tree
- **Conjecture**: "Conjecture: The graph H constructed above is connected and hence it is a tree." (entry comment; H joins each practical p to the least practical q > p with 2(p+1) - q practical)
- **Attribution**: uncredited; likely Zhi-Wei Sun.
- **Status**: open.
- **Lean feasibility**: heavy — infinite-graph connectivity over a def with an embedded least-witness; needs `SimpleGraph` scaffolding plus well-definedness of the successor (itself conjectural-ish). Statement-archive only, and an awkward one.
- **Sanity layer**: connectivity of the restriction to practicals <= 10^4.

#### A005153 — Sun: a(n)^(1/n) strictly decreasing
- **Conjecture**: "Conjecture: The sequence a(n)^(1/n) (n=3,4,...) is strictly decreasing to the limit 1." (Zhi-Wei Sun, Jan 12 2013)
- **Attribution**: Zhi-Wei Sun, 2013.
- **Status**: open (limit 1 follows from Weingartner's asymptotic; strict monotonicity is the open part).
- **Lean feasibility**: heavy. Real-power comparisons of consecutive terms of an enumeration; needs the practical-number counting function. The repo's asymptotics toolbox helps with the limit half only.
- **Sanity layer**: `a(n)^(n+1) > a(n+1)^n` (integer form) for n <= 200.

#### A003135 — factorial products of smaller factorials
- **Conjecture**: "It is conjectured that the list is complete." (sequence name; terms 9, 10, 16); "There are no other terms < 10^5. - Jud McCranie, Jun 15 2005"
- **Attribution**: classical (Guy, UPINT B23 territory); entry-level attribution thin.
- **Status**: open.
- **Lean feasibility**: heavy-ish for its size: the nontriviality condition (largest factor x! with x < n-1) over multisets of factorials is awkward to state cleanly. Doable, but the statement audit cost is high relative to payoff.
- **Sanity layer**: verify 9! = 7!*3!*3!*2!, 10! = 7!*6!, 16! = 14!*5!*2! by `rfl`/`decide`; completeness below 100 by bounded search.

#### A172161 — greedy Coppersmith–Winograd sequence growth
- **Conjecture**: "Conjecture: a(n) ~ k*(3 / 2)^n for some k. - Bill McEachen, Dec 02 2022"
- **Attribution**: Bill McEachen, 2022.
- **Status**: PROVED IN FULL 2026-08-20 in f061efe (`Proofs/Scratch/GreedyCWAsymptotic.lean`, reviewer trio passed): both the recurrence and asymptotic, from the greedy definition. CORRECTION: Greathouse did not supply a proof of the recurrence — his `%F` line is a bare formula with no proof or reference; the greedy-to-recurrence induction (four-bad-pair double-representation invariant) is the real content. The search found no prior proof, but that is not a priority, first-proof, publication, or publishability claim. The asymptotic given the recurrence is Odlyzko–Wilf-class, with no novelty claim.
- **Lean feasibility**: recurrence layer easy; the ratio-limit argument needs real analysis over a floor recurrence, medium-heavy in practice.
- **Sanity layer**: verify the recurrence for the first 40 listed terms.

#### A000041 — Sun: additive representation by p(k) + 2
- **Conjecture**: "Conjecture: Each integer n > 2 different from 6 can be written as a sum of finitely many numbers of the form a(k) + 2 (k > 0) with no summand dividing another. This has been verified for n <= 7140." (Zhi-Wei Sun, May 16 2023)
- **Attribution**: Zhi-Wei Sun, 2023.
- **Status**: open. Distinct from the carded A000041 perfect-power conjecture.
- **Lean feasibility**: statement needs multiset summand encoding with an antichain condition — moderately awkward; search-based sanity layer does not reduce to a clean `native_decide`.
- **Sanity layer**: marginal; witness certificates for n <= 50.

## already covered (skipped)

Found again by the sweep but already in `Formalize/` cards,
`Proofs/`, or `PLAN.md` lanes: A039669 (archived card),
A089654, A332077 (sunflower card + P5/P8), A236397 (Peebles
card), A090245 (capset, BilinearComplexity), A003313
(Knuth–Stolarsky card + P3/P8), A002804 / A174420 (Kubina–
Wunderlich card, P8), A005520 (record-values card), A064097
(quasilog card), A005245 / A348262 (Hamilton–Ballinger card),
A230528, A014701, A000670 (Bala periodicity proved; Muljadi
and EGF-family cards exist — the general G(exp(x)-1)
conjecture is the already-carded A000670-egf-family),
A000041 perfect-power (Sun card), A000001 (Lopes and CDO
cards), A083207 Ianakiev tau-sigma and sigma-half (cards),
A007691 multiperfect-Zumkeller (card), A005153-as-sequence
(practical infra in Proofs; only *new* conjectures on it are
listed above), A076335 Brier (covering arc C3), A101036
Riesel covering sets (covering arc), A160559 / Hough–Nielsen
(gated per PLAN), A161682, A046098, A094870, A005432,
A323653, A273929 (all P8 batch).

Two sweep hits were dropped as non-candidates rather than
duplicates: A389975 (no conjecture in the entry, just a hard
definition) and A122251 (unattributed Hankel-determinant
closed form; determinant-of-rationals infrastructure cost is
out of proportion to the entry's weight).
