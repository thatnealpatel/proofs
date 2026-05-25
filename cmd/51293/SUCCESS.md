# A051293 Proof Retrospective

Closed the final sorry in a ~1000-line Lean 4 formalization of
Cloitre's conjecture on subsets with integer average, proving
the full asymptotic expansion with Fubini number coefficients.

## What went well

**Go programs as intuition scaffolding.** Before writing any Lean,
a 70-line Go program (`tailbound.go`) verified three things:
(1) the bound `4*fubini(i)*n^i/2^n` is tight at `n=1`,
(2) the identity `sum C(i,m)*fubini(m) = 2*fubini(i)` holds
exactly, and (3) the decomposition
`sum_{m<i} = fubini(i)` + `C(i,i)*fubini(i) = fubini(i)`
follows directly from the recurrence. This killed a dead-end
approach (binomial expansion of `(n+k)^i`) before any Lean was
written, and surfaced the much simpler `n+k <= n*(k+1)` route.
Total Go time: ~5 minutes. Lean time saved: potentially hours.

**Extracting the sorry into its own lemma.** The inline proof
inside `polylog_partial_error_isLittleO` caused deterministic
timeouts at 1.6M heartbeats. Moving it to a top-level
`polylog_tail_bound` lemma compiled in 3.9s. Same proof text,
zero code changes. The elaborator chokes on large proof contexts,
not on individual steps.

**`set f : N -> R` killed a type inference disaster.** Without
the explicit `N -> R` annotation, Lean inferred tsum indices as
`R` instead of `N`, silently producing `sum' (j : R), ...`
which broke every downstream `linarith`. One annotation fixed
all of it. This is a pattern worth remembering for any proof
involving tsums over cast sequences.

**Lint-first, prove-second.** Clearing the four lint warnings
before touching the sorry ensured the codebase was clean and
that no warning noise masked real errors during proof iteration.

## What went poorly

**Lemma discovery is the bottleneck, not proving.** Seven grep
invocations were needed to find `tsum_le_tsum` (it only exists
for ENNReal; the real-valued version is `Summable.tsum_le_tsum`,
a dot-notation method). Five more to find `pow_le_pow_left0`
(the `0` suffix) and confirm `tsum_mul_left` is an equality,
not a function. Each grep cycle costs a build round-trip. The
appendix in `notes.txt` documents even worse cases from earlier
sessions -- eight consecutive empty grep results trying to find
`HasSum.add`.

A `/leandoc` skill (analogous to `/godoc` for Go) backed by
doc-gen4 would collapse these multi-grep chains into one call.
The data exists; the tooling to query it does not.

**`convert ... using 1` with `field_simp` created opaque cast
terms.** The first attempt at `shifted_polylog_summable` used
`convert` to bridge between `(k+1)^i / 2^k` and
`2 * ((k+1)^i / 2^{k+1})`. The `field_simp` inside `convert`
generated intermediate terms that caused downstream `isDefEq`
timeouts. Replacing it with explicit `ext k; rw [smul_eq_mul,
pow_succ]; field_simp` fixed it, but diagnosing the cause took
three build cycles.

**Heartbeat timeouts give zero locality.** The error reports the
line where the `lemma` keyword is, not the tactic that's stuck.
With a 40-line proof, this means binary-searching for the slow
step via sorry-insertion. The actual fix (extract to top-level
lemma) was trivial once the cause was found; finding it was not.

**`tsum_mul_left` is an equality, not a function.** Writing
`tsum_mul_left _ _` fails because it's not a function taking
arguments -- it's a proof of `sum' x, c * f x = c * sum' x, f x`.
The correct usage is `tsum_mul_left ..` (term-mode) or
`exact tsum_mul_left` or using it as a rewrite. This API shape
is surprising and cost a build cycle.

## What I wish I knew

**`set f : T := ...` is not optional for tsum proofs.** Without
an explicit type annotation, Lean's bidirectional type inference
for `sum' j, ...` resolves `j` to whatever makes the body
well-typed, which is often `R` when casts are present. Every
tsum proof over `N`-indexed cast sequences should start with
`set f : N -> R := ...`.

**The multiplicative/additive `to_additive` naming split.** The
"real" tsum ordering lemma is generated via `@[to_additive]`
from a multiplicative version in `NatInt.lean`. Grepping for the
additive name finds nothing; you need to grep for the
multiplicative name (`Multipliable.prod_mul_tprod_nat_add`) and
infer the additive counterpart (`Summable.sum_add_tsum_nat_add`).
This naming indirection is invisible without knowing the pattern.

**`Summable.mul_left` exists and is the right idiom.** Not
`Summable.const_smul` (which fights with `SMul` instances), not
`Summable.of_nonneg_of_le` (wrong direction). Just `.mul_left`.
This took three attempts to discover.

**The `n + k <= n * (k + 1)` trick.** For bounding shifted sums
`sum_{j>=n} f(j)`, the inequality `n + k <= n*(k+1)` (from
`k <= n*k` when `n >= 1`) is strictly simpler than a binomial
expansion of `(n+k)^i`. The Go program revealed this by showing
the binomial approach requires `sum C(i,m)*fubini(m) = 2*fubini(i)`,
which IS true and elegant, but unnecessary -- the cruder
per-term bound `(n+k)^i <= (n*(k+1))^i = n^i * (k+1)^i` gives
the same result with half the Lean code. Computation identified
both paths; choosing the simpler one saved significant effort.

## Open questions for the future

**Should we build a `/leandoc` skill?** The `doc-gen4` project
generates browsable HTML documentation from Lean/Mathlib source.
A local index (like the OEIS/Wikipedia indexes in `/maths`) would
let us query "what lemmas mention `tsum` and `Summable`?" without
grepping 350K lines of Mathlib. The main questions: (1) does
doc-gen4's JSON output contain enough type information for
signature-level search? (2) can we build a BM25 index over it
the way `goof oeis` works? (3) would `exact?`/`apply?` with
higher heartbeats be good enough instead?

**Can we detect the `set f : T` anti-pattern automatically?**
A pre-build hook that scans for `tsum` or `sum'` without an
explicit index type annotation could warn before the 3-minute
build cycle. The pattern is: if `tsum` appears in a goal and
the index variable has a metavariable type, flag it.

**Is there a systematic way to find `@[to_additive]` pairs?**
When a grep for `sum_add_tsum_nat_add` returns nothing, the
current workflow is to guess that it's generated from a
multiplicative version and search for `prod_mul_tprod`. A tool
that maps additive names to their multiplicative sources (or
vice versa) would eliminate this guesswork.

**What's the right heartbeat budget for proof development?**
The default 200K is too low for proofs involving tsum
comparisons with cast arithmetic. But 1.6M masks real infinite
loops. A per-tactic heartbeat profile (like Go's `pprof`) would
let us identify which step is expensive without binary-searching
with sorry.

**How do we scale this to the next proof?** The A051293 proof
took ~1000 lines across 4 sections. The process bottleneck was
always lemma discovery, never mathematical insight. If we solve
the search problem (via doc-gen4, better `exact?`, or a custom
index), the next formalization should be significantly faster.
The Go-for-intuition pattern and the extract-to-top-level
pattern both transferred cleanly and should be standard practice.

## Appendix A: Go/Lean co-evaluation

Three Go programs exist in `cmd/51293/`; only `tailbound.go`
was written during the sorry-closing session. `terms.go` and
`convergence.go` predate it (validating OEIS terms and
asymptotic convergence respectively).

### Where `tailbound.go` directly helped

1. **Killed the binomial expansion approach.** Output showed
   `sum C(i,m)*fubini(m) = 2*fubini(i)` is exact, revealing
   the Fubini recurrence one-liner. But it also showed the
   identity was unnecessary — the ratio column proved the crude
   `n+k <= n*(k+1)` bound was already tight at `n=1` for all
   `i`, making the binomial path dead weight. The Lean proof
   uses the crude bound. The `binomial_fubini_*` lemmas (lines
   687-709) compile and are correct but are unused — a
   discipline failure, not a tooling one.

2. **Confirmed the constant 4 is tight.** Every `i` shows
   `ratio=1.0000` at `n=1`. This prevented wasting time trying
   to simplify the sorry statement.

### Where a Go program would have helped but wasn't written

1. **The `shifted_polylog_summable` factoring.** The Lean proof
   needs `(k+1)^i / 2^k = 2 * (k+1)^i / 2^{k+1}`. This step
   caused three build failures (the `convert`/`const_smul`/
   `field_simp` chain). A Go program printing `f(k) / g(k)` for
   both representations would have confirmed they're equal and
   shown the exact algebraic identity, making it obvious that
   `smul_eq_mul` + `pow_succ` was the right rewrite chain.
   Cost: 5 lines of Go. Savings: 2 build cycles (~8 min).

2. **The `tsum_geometric_two` form mismatch.** The `i=0` case
   of `shifted_polylog_le` needed `sum 1/2^k = 2`. Lean's
   `tsum_geometric_two` gives `sum (1/2)^k = 2`. A Go program
   computing `1.0/math.Pow(2,k)` vs `math.Pow(0.5,k)` would
   have made the representation gap visible instantly, showing
   that `inv_pow` + `one_div` is the bridge. Instead this was
   discovered via a type mismatch error.

3. **The `set f : N -> R` requirement.** The type inference
   disaster (Lean inferring `j : R` for tsum indices) could not
   have been caught by Go directly. But a Go program computing
   the tail `sum_{j>=n} j^i/2^j` step-by-step as
   `sum over k of f(k+n)` would have forced thinking in terms
   of `f : N -> R` with explicit index types, making the `set f`
   annotation more natural when translating to Lean.

### Where Go would NOT have helped

- **Lemma discovery.** `tsum_le_tsum` vs
  `Summable.tsum_le_tsum`, `pow_le_pow_left0` (the `0` suffix),
  `div_le_div_of_nonneg_right`. These are Lean namespace
  problems, not mathematical ones.
- **Heartbeat timeout from inline vs extracted lemma.** This is
  an elaborator implementation detail.
- **`tsum_mul_left` is an equality, not a function.** This is
  Lean API design.

### Verdict

`tailbound.go` earned its keep — it prevented at least one wrong
approach and confirmed the bound. But it was written too late
(after analysis, not before) and too narrow (only tested the
final bound, not the intermediate algebraic steps).

The ideal workflow: write a Go program that computes the *full
decomposition chain* (tail -> factored form -> shifted polylog
-> bound), printing each intermediate value. Translate each
printed line into a Lean `have` statement. Fill in the proofs.
This is "write the calc chain in Go first, then transcribe to
Lean." The current `tailbound.go` only validated endpoints, not
intermediate steps. The two build failures in
`shifted_polylog_summable` and `shifted_polylog_le` (zero case)
were both intermediate-step issues that a more detailed Go
program would have pre-empted.

## Appendix B: Proof structure and wider applications

> NOTE: Each wider application below is speculative. They must be
> verified against existing literature and tested computationally
> before being formalized into skills or memories.

### Theorem statement

For `a(n) = #{S ⊆ {1,...,n} : S != empty, mean(S) in Z}`:

    a(n) = (2^{n+1}/n) * sum_{k=0}^M fubini(k)/n^k + o(2^n/n^{M+1})

for every truncation order M, where fubini(k) are the ordered
Bell numbers (A000670).

### Proof steps

1. **d=1 dominance.** The divisor-sum `b(k) = (1/k) sum_{d|k,
   d odd} 2^{k/d} phi(d)` is dominated by `d=1` (contributing
   `2^k/k`). Error from `d >= 3` is `O(2^{n/3})`, negligible.

2. **Coefficient identity.** `sum_{j>=0} j^m/2^j = 2*fubini(m)`.
   By strong induction via binomial telescoping against geometric
   weights, closed by the Fubini recurrence.

3. **Discrete Laplace expansion.** Reindex `S(n) = 2^n *
   sum_{j<n} 1/(2^j(n-j))`. Geometric expansion of `1/(n-j)` to
   order M produces coefficients `(1/n^{m+1}) sum_j j^m/2^j`
   which converge to `2*fubini(m)/n^{m+1}` by Step 2.

4. **Tail bound.** `|partial - tsum| <= 4*fubini(i)*n^i/2^n`.
   Key inequality: `n+k <= n*(k+1)` for `n >= 1`, giving
   `(n+k)^i <= n^i*(k+1)^i`. Combined with shifted polylog
   bound `sum (k+1)^i/2^k <= 4*fubini(i)`.

### Core components (reusable)

- `fubini_polylog`: the series identity (why Fubini numbers
  appear in any problem with `1/(2-e^x)` generating functions)
- `polylog_shift_tsum`: `sum (j+1)^m/2^j = 2*sum j^m/2^j`
  (bridges induction in Step 2 and tail bound in Step 4)
- `polylog_tail_bound`: quantitative convergence rate for
  truncated polylogarithms `Li_{-i}(1/2)`
- `n+k <= n*(k+1)`: trivial but powerful factoring trick for
  shifted-index tail bounds

### Potential wider applications (unverified)

1. **Discrete Laplace method as a template.** Steps 1+3 are
   generic: any sum `sum f(k)/k` where `f` is exponentially
   dominated by one term admits the same reindexing and geometric
   expansion. Candidate sequences: A006218 (divisor summatory),
   A000041 (partitions via Hardy-Ramanujan), any OEIS entry with
   "asymptotic expansion" in comments and a dominant exponential
   term. Needs verification that the error structure matches.

2. **Fubini number identities for related sequences.** The
   `binomial_fubini_nat` identity and `fubini_polylog` series
   apply wherever the EGF `1/(2-e^x)` appears. Known
   connections: A000670 (surjections), A052856 (ascent
   sequences), weak compositions counted by preference orders.
   Needs verification of which specific conjectures these close.

3. **Polylog tail bounds for numerical algorithms.** The
   `polylog_tail_bound` gives `|Li_{-i}(1/2) - partial_n| <=
   4*fubini(i)*n^i/2^n`. This is relevant for error analysis in
   algorithms computing polylogarithms at half-integer points
   (e.g., in statistical mechanics partition functions). Needs
   verification against existing numerical analysis literature.

4. **Subset-sum statistics in combinatorics/coding theory.** The
   full expansion gives precise asymptotics for integer-average
   subsets beyond the leading `2^{n+1}/n`. This could improve
   bounds in additive combinatorics (zero-sum problems over Z/nZ)
   or inform algorithm design for subset-sum enumeration. Needs
   verification of whether existing results (Erdos-Ginzburg-Ziv
   and descendants) use this specific count.
