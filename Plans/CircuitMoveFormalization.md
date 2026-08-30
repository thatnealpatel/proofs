# Circuit Move Formalization

## Purpose

Own the `~/p/proofs` side of the research bridge

$$
\text{binary circuit}
\longrightarrow
\text{valid KM/Arai executable path with controlled altitude}.
$$

This campaign covers source fidelity, mathematical definitions, theorem
boundaries, and Lean proofs. Exploration and counterexample search under
`~/x/tensor` belong to the collaborating tensor track and are immutable inputs
to this campaign.

The relation-algebra statement from
`Plans/SymbolicCompletenessTheorem.md` is retained only as a short derived
proposition. It is not the mathematical centerpiece of this campaign.

## Campaign status

The foundational tranche closed on 2026-06-17. Its durable source audit is
`Documents/CircuitMoveSourceContract.md`, and its verified Lean boundary is
`Proofs/BilinearComplexity/BinaryCircuit.lean`.

The closed tranche proves the abstract finite-set circuit decomposition, a
specifically constructed path with path-specific vertices, target-fiber
preservation, and the altitude bound $|D\cup E|$. It deliberately does not
claim compilation into KM/Arai moves. The parity-to-box equivalence, weighted
quotient, and Graver projection remain deferred with explicit prerequisites.

The collaborating tensor track has now discharged the two computational inputs
that were pending when the tranche closed. Code committed at tensor `89c0a84`
reproducibly generates circuit report schema 4, which classifies the complete
support-at-most-five factor-dimension-two census against the audited local KM
and Arai formulas. Code committed at tensor `fc3baea` reproducibly generates
dimension-three report schema 1, which exhaustively treats all disjoint exact
$2\leftrightarrow3$ relations in the 343-term normalized carrier with a
bounded-memory, per-fiber computation. Here local altitude three means that the
maximum represented local-state cardinality is three; adjoining an admissible
context $C$ would instead give full-scheme altitude $|C|+3$. These reports
promote one precise *candidate* for formalization: a factor-dimension-three path
theorem of local altitude three and length at most three in the explicitly
generated raw relation described below. They do not prove that candidate, lift
it to larger factor dimensions or full schemes, establish Arai connectivity, or
alter the closed status of the abstract circuit tranche.

## Ownership

This campaign exclusively owns changes under `~/p/proofs`, including plans,
Lean files, and supporting Go packages. It does not modify `~/x/tensor`, its
exploration program, production moves, search policy, trajectories, codecs,
telemetry, stored schemes, or data.

Reports from `~/x/tensor` are computational evidence. They may generate,
sharpen, or refute candidate statements, but they are not proofs.

`Documents/DeformationTheory.md` is outside the autonomous update scope.

## Shared mathematical contract

Let `P` be a finite configuration of nonzero pure tensors over
$\mathbb F_2$. For a target $m$, define

$$
X_m=\left\{D\subseteq P:\sum_{t\in D}t=m\right\}.
$$

A binary cycle is a finite subset $Z\subseteq P$ with
$\sum_{t\in Z}t=0$. A circuit is an inclusion-minimal nonempty binary cycle.
Its abstract move is the toggle

$$
D\longmapsto D\mathbin{\triangle}C.
$$

Every concrete move system must be named. Relevant systems include:

- full Kauers--Moosbauer moves;
- Arai--Ichikawa--Hukushima moves including Plus;
- any separately audited executable move family.

For a named move system $\mathcal M$, a path is a nonempty finite sequence
$(D_0,\ldots,D_k)$ whose adjacent pairs are $\mathcal M$-moves; it includes
both endpoints, and the length-zero path $(D)$ is allowed. Define the
bottleneck distance in $\mathbb N\cup\{\infty\}$ by

$$
\lambda_{\mathcal M}(D,E)
=
\min_{\pi:D\leadsto E}
\max_{D'\in\pi}|D'|,
$$

where the value is $\infty$ if no path exists. In particular,
$\lambda_{\mathcal M}(D,D)=|D|$. No unqualified $\lambda(D,E)$ will be used.
The definitions allow $X_m=\varnothing$; endpoint statements always assume
that the displayed schemes belong to $X_m$.

## Checkpoint 1: primary-source contract

Audit the primary texts and record exact definitions, hypotheses, theorem
statements, and page pointers for:

1. Kauers--Moosbauer reductions and flips;
2. their weak-connectivity theorem and coordinate-splitting proof;
3. any source result that classifies or connects two-term relations;
4. Arai--Ichikawa--Hukushima Split, Flip, Plus, and connectivity;
5. the literal source relationship
   $$
   \mathrm{Plus}=\mathrm{Split};\mathrm{Flip}.
   $$

The Arai audit must check:

- nonzero-factor requirements;
- inequalities and distinctness assumptions;
- avoidance and treatment of duplicate terms;
- whether schemes are sets, multisets, or ordered lists at each proof step;
- availability of partner terms during repeated Plus operations;
- elimination of surplus coordinate terms;
- whether the construction supplies an explicit rank, altitude, path-length,
  or Plus-count bound.

Every resulting claim must be classified as one of:

1. proved in the cited source;
2. a routine consequence with an explicit derivation;
3. unresolved or conjectural;
4. consistent with an executable implementation only after a separate audit.

The source contract will be delivered to the tensor track before its schema
recognizers are treated as source-faithful.

## Formal campaign boundary

### Short derived proposition

For a finite connected move graph, singleton edge relations and singleton
identity tests generate every relation under composition and finite union.
Thus the proposed

$$
Q_n=\operatorname{Rel}(X_n)
$$

is infrastructure once the relevant connectivity theorem has been
instantiated. It will not be presented as a new tensor theorem or as an
algorithmic efficiency result.

### Substantive formal objects

The formal development should instead expose:

- finite-set schemes in a binary target fiber;
- binary cycles and circuits;
- typed abstract move systems;
- paths under a named move system;
- path length and maximum altitude;
- $\lambda_{\mathcal M}$;
- compilation of one move family into another;
- equivariance under tensor and scheme symmetries;
- orbit paths and concrete certificate lifting;
- preservation of bottleneck altitude under a weighted quotient.

The quotient layer is deliberately deferred until the concrete move semantics
are fixed. It will require a specified group action preserving the target,
cardinality, and named move relation; a quotient path semantics; and a lifting
theorem showing that quotient paths admit concrete lifts with the same
sequence of vertex altitudes. Reachability or ordinary shortest-depth
preservation alone will not establish preservation of
$\lambda_{\mathcal M}$.

## Carrier decision

The intended first model consists of finite sets of nonzero pure tensors over
$\mathbb F_2$. It has no duplicate occurrences, no zero terms, and no
nontrivial scalar refactorizations.

The existing generic `TriadData`/multiset scaffold admits duplicate
occurrences, zero terms, and general-field scalar behavior. It must not be
silently identified with $X_m$.

Before theorem implementation, choose one of two sound boundaries:

1. specialize the carrier and normalize explicitly to the finite-set
   $\mathbb F_2$ model; or
2. prove an abstract theorem under hypotheses strong enough to instantiate
   that model, while keeping the generic multiset development separate.

No support-five classification theorem will be attempted on the current
unnormalized carrier.

## Foundational lemmas

The first small formal layer should establish:

1. If $D,E\in X_m$, then
   $$
   \sum_{t\in D\triangle E}t=0.
   $$
2. Every finite binary cycle is a disjoint union of circuits.
3. If
   $$
   D\triangle E=C_1\sqcup\cdots\sqcup C_k,
   $$
   then successive circuit toggles form a path from $D$ to $E$ in $X_m$.
4. Every intermediate scheme lies in $D\cup E$, so the abstract circuit path
   has altitude at most
   $$
   |D\cup E|\le |D|+|E|.
   $$
5. Fix binary coordinate vectors for the columns of $P$ and the target
   $m\in\mathbb F_2^d$, and let $A\in\{0,1\}^{d\times N}$ be the resulting
   integer incidence matrix. The map
   $$
   x\longmapsto\left(x,\frac{Ax-m}{2}\right)
   $$
   is a bijection from
   $$
   \{x\in\{0,1\}^N:Ax\equiv m\pmod 2\}
   $$
   to the explicitly box-constrained integer fiber
   $$
   \left\{(x,z)\in\mathbb Z^{N+d}:
   [A\mid-2I](x,z)=m,
   \ 0\le x_j\le1,
   \ 0\le z_i\le\left\lfloor\frac N2\right\rfloor
   \right\}.
   $$
   Here $m$ on the right is its canonical $0$--$1$ integer representative.

The box constraints are essential because the matrix has negative columns.
The target is not to be called an ordinary finite nonnegative toric fiber.

The elementary circuit development is primary. A Graver interpretation will
be formalized only if it yields an additional precise theorem. In particular,
this campaign makes no unsupported claim that every Graver element of
$[A\mid-2I]$ applicable to binary endpoints projects exactly to a circuit;
slack-coordinate conformality must be analyzed before any such statement.

Lean constructs a restricted abstract circuit-toggle path from $D$ to $E$
whose vertices stay in $D\cup E$ and whose altitude is therefore at most
$|D\cup E|$. This gives an existential bottleneck bound; arbitrary abstract
`CircuitPath`s may detour outside the endpoint union. No such bound applies to
KM/Arai paths unless a controlled compilation theorem is proved.

## Candidate theorem generation

The tensor track will report symmetry classes of bounded-support circuits and
compilation experiments. This campaign will convert only stable observations
into precise candidate theorems, such as:

- classifications of low-support binary circuits;
- sufficient and necessary conditions for a circuit orientation to be a
  Split, Reduction, Flip, or Plus;
- local and uniform compilation into a named move system;
- bounds on compilation path length and maximum intermediate arity;
- obstructions caused by zero or duplicate intermediate terms;
- counterexamples to overly broad support-five claims.

### Post-adversarial theorem ladder

The evidence generated by tensor commits `89c0a84` and `fc3baea` supports the
following ordered work items; dependencies are stated within the items. None is
an inferred theorem.

1. Define normalized finite carriers
   $$
   L_d=(\mathbb F_2^d\setminus\{0\})^3
   $$
   as factor triples evaluated as pure tensors in
   $(\mathbb F_2^d)^{\otimes3}$, with immediate instances $L_2$ and $L_3$.
   This local-factor notation is separate from the matrix-size configuration
   notation $P_4$ in the non-goals, where each factor space has dimension 16.
   Prove the normalization and evaluation facts needed to identify the factor
   triples with distinct nonzero pure tensors: 27 for $L_2$ and 343 for $L_3$.
2. Define and name `GeneratedKMLocalWeak` as a symmetric edge relation on
   finite local states: legality-checked implementation identities based on KM's
   prose Split, reversible source Flips, and the symmetric closure of directed
   source Reductions. The checked Split identity is not a formally source-defined
   relation, and a converse Reduction is only weak traversal. Separately define
   `BoundedGeneratedKMGraph d` as its induced graph on squarefree $L_d$ states
   of arity one through three in the union of pair-containing evaluation fibers.
   This bounded graph, not the unrestricted edge relation, is the exact graph
   searched by the dimension-three census. Keep Arai Flip and Plus on an
   occurrence-aware multiset carrier.
3. Prove evaluation preservation, nonzero outputs, collision freedom, and the
   precise cardinality change for each finite-set relation. Separately prove the
   Arai formulas with multiplicity and the Plus-as-Split-then-Flip identity.
4. Prove a context-lifting lemma. For a chosen local path $p$, require
   factorwise injective ambient maps and injectivity/cardinality preservation of
   the induced tensor map; require a context $C$ such that adjoining it to the
   embedded local source is an actual matrix-multiplication scheme; and require
   $C$ to avoid the image of the union of **all** vertices of $p$, not merely
   the endpoints. Prove that every named edge remains legal after adjoining
   $C$, every vertex remains in the matrix-multiplication target fiber, length
   is preserved, and altitude changes from local $h$ to $|C|+h$. State a
   separate multiset-addition lemma for Arai. The aggregate dimension-three
   report emits no per-relation path or context certificate.
5. Prove local covariance under factor-space linear automorphisms and factor
   permutations for evaluation, each named relation with its direction, path
   length, and local altitude. Prove symmetry and path reversal for
   `GeneratedKMLocalWeak` before using representatives whose converses were
   identified. A full-scheme result must either transport the target, embedding,
   and context with the local certificate or restrict to a target-preserving
   subgroup; arbitrary local automorphisms do not preserve a fixed
   matrix-multiplication target.
6. Certify the finite $L_2$ theorem: every disjoint support-five circuit
   orientation of type $2\leftrightarrow3$ has a path in
   `BoundedGeneratedKMGraph 2` of length at most three and local altitude three,
   hence also a `GeneratedKMLocalWeak` path. A full-scheme corollary must retain
   all hypotheses from item 4, including target completion and avoidance of the
   chosen path-vertex union.
7. Certify the finite $L_3$ candidate: for disjoint $D,E\subseteq L_3$ with
   $|D|=2$, $|E|=3$, and equal evaluation, $D\triangle E$ is a circuit and
   there is a path in `BoundedGeneratedKMGraph 3` from $D$ to $E$ of length at
   most three and local altitude exactly three. This implies a path in the
   unrestricted `GeneratedKMLocalWeak` relation. A proof may use a verified
   finite decision procedure, a structural classification, or both; the
   reproducible JSON output itself is not a proof.
8. Prove a generic dependent path-substitution theorem. For an abstract edge
   $E=D\triangle C_0$, require a local compiler with endpoints exactly
   $D\cap C_0$ and $C_0\setminus D$, and consume item 4 using the unchanged
   context $D\setminus C_0$ and vertex lift
   $$
   X\longmapsto (D\setminus C_0)\cup X.
   $$
   Prove the endpoint equations
   $$
   (D\setminus C_0)\cup(D\cap C_0)=D,
   \qquad
   (D\setminus C_0)\cup(C_0\setminus D)=D\triangle C_0=E.
   $$
   The compiler must also expose target-fiber legality of every lifted vertex,
   avoidance of every introduced term by the unchanged context, and
   length/altitude costs that compose under concatenation. The present abstract
   decomposition includes circuits of arbitrary support, while the reports
   compile only the displayed $2\leftrightarrow3$ subclass, so they do not
   instantiate this theorem globally.
9. In parallel, investigate missing outside-span mask 7 as a nonblocking
   structural conjecture: every enumerated relation has some factor position in
   which all three right factors lie in the span of the two left factors. This
   is not yet a local-span theorem and does not lift the $L_3$ result to
   arbitrary ambient factor dimensions.

Meaningful comparisons between two globally connecting move systems concern
primitive edges, support, locality, path length, altitude, uniform
representability, and behavior on other parity fibers. Their equivalence
closures on a fixed connected $X_m$ are both the universal relation and are
not a distinguishing invariant.

## Coordination checkpoints

### Checkpoint 1: source contract

This campaign supplies exact KM/Arai definitions and an unresolved-condition
ledger. The tensor track uses that contract to implement authoritative source
recognizers.

### Checkpoint 2: support-five census

The tensor track supplies the complete support-at-most-five
factor-dimension-two circuit and compilation report. Both tracks decide which
observations merit theorem statements. No large Lean proof begins at this
checkpoint.

### Checkpoint 3: adversarial expansion

The tensor track tests candidate statements in factor dimension three and
searches for counterexamples or hidden span-growth phenomena. This campaign
repairs hypotheses and theorem boundaries.

### Checkpoint 4: formalization

Only statements that survive source audit and adversarial computation are
formalized. This campaign owns the Lean proofs; the tensor track retains
executable witnesses and regression examples.

## Expected tensor-track input

For each class, the deterministic report should contain:

- factor dimension;
- support size;
- canonical circuit;
- orientation $L\leftrightarrow R$;
- orbit size;
- direct matches against each named schema;
- shortest known compilation word;
- minimum known intermediate arity;
- all intermediate fragments;
- zero, duplicate, or bounded-search obstruction details.

Absence of a path in a bounded computation is not a proof of impossibility.

## Non-goals

This campaign does not initially attempt to:

- materialize the normalized carrier $P_4$ for $4\times4$
  matrix-multiplication factor spaces, whose size is
  $$
  (2^{16}-1)^3;
  $$
- construct a full Graver basis for the matrix-multiplication configuration;
- claim bounded-rank connectivity from unbounded weak connectivity;
- treat border-rank or characteristic-zero deformation results as exact
  $\mathbb F_2$ move theorems;
- prove the existing `SupportFiveClassificationGoal` before normalizing its
  carrier and move families;
- modify production search behavior in `~/x/tensor`;
- treat computational census results as formal proofs.

## Review ledger

| ID | Reviewer axis | Status | Disposition |
|---|---|---|---|
| CMF-001 | Novelty | accepted | Demote $Q_n=\operatorname{Rel}(X_n)$ to a derived proposition. |
| CMF-002 | Source fidelity | accepted with gaps | Exact KM/Arai contract is recorded in `Documents/CircuitMoveSourceContract.md`; source proof gaps remain explicit. |
| CMF-003 | Carrier semantics | accepted | `BinaryCircuit.lean` is a separate abstract finite-set `ZMod 2`-module boundary. |
| CMF-004 | Graver terminology | accepted | Use box-constrained fiber language; keep circuits primary. |
| CMF-005 | Graver projection | blocked | Make no circuit-projection claim until slack conformality is proved. |
| CMF-006 | Move comparison | accepted | Compare local edges and costs, not universal equivalence closures. |
| CMF-007 | Altitude | accepted | The specifically constructed restricted abstract path has vertices in $D\cup E$ and altitude at most $|D\cup E|$; arbitrary abstract paths may detour and no compiled bound is claimed. |
| CMF-008 | Implementation fidelity | accepted with conditions | Tensor `89c0a84` implements, tests, and replays the audited local schemas; tensor `fc3baea` adds complete disjoint exact $2\leftrightarrow3$ slice differential agreement for KM Reduction and Arai Plus. Applicability still requires the reported embedding, target-completion, and context-avoidance hypotheses. |
| CMF-009 | Computational provenance | accepted | Treat tensor reports as conjecture-forming evidence only. |
| CMF-010 | Weighted quotient | deferred | Address after concrete move semantics and bottleneck paths are fixed. |
| CMF-011 | Adversarial expansion | accepted as evidence | Code at tensor `fc3baea` reproducibly supports the bounded local $L_3$ candidate; it is not a formal proof or a dimension-lift theorem. |
| CMF-012 | Full-scheme lifting | blocked | Prove target completion, induced-map/cardinality preservation, edge legality, and path-union context avoidance before adjoining an ambient KM context. |
| CMF-013 | Arai compilation | deferred | Direct Plus matches are classified, but no Arai Reduction or path/connectivity result is inferred. |

## Completion criteria

The campaign reaches its first stable milestone when:

1. the KM/Arai source contract and audit ledger are complete;
2. the binary finite-set carrier has an explicit formal boundary;
3. the four elementary circuit/path/altitude lemmas are type-checked;
4. the parity-to-box statement is either type-checked with explicit bounds or
   deliberately deferred with its exact missing prerequisites recorded;
5. the factor-dimension-two report has been reviewed without promoting
   unsupported generalizations;
6. candidate compilation theorems have survived factor-dimension-three
   adversarial testing before substantial formalization begins.

### Milestone disposition

1. **Complete:** the primary-source contract and unresolved-condition ledger are
   in `Documents/CircuitMoveSourceContract.md`.
2. **Complete:** the binary carrier is a separate abstract `Finset` boundary;
   no generic multiset identification is made.
3. **Complete:** the cycle, recursive disjoint decomposition, concrete toggle
   path, target-fiber preservation, and path-specific altitude results build
   without `sorry` in `BinaryCircuit.lean`.
4. **Deliberately deferred:** the parity-to-box equivalence awaits the explicit
   coordinate enumeration, subset/indicator equivalence, bit hypotheses, and
   integer quotient/bound lemmas listed in the source contract.
5. **Complete as reviewed computational evidence:** code at tensor `89c0a84`
   reproducibly generates circuit report schema 4, retaining the complete
   support-at-most-five dimension-two census and classifying all 14 orientation
   representatives against independently named source schemas. The six
   $2\leftrightarrow3$ classes have conditional witnesses in
   `BoundedGeneratedKMGraph 2` of length at most three and local altitude three.
   The detailed directional classification is recorded in
   `Documents/CircuitMoveSourceContract.md`.
6. **Complete as adversarial computational evidence, open as a theorem:** code
   at tensor `fc3baea` reproducibly generates dimension-three report schema 1,
   enumerating 1,265,670 disjoint exact $2\leftrightarrow3$ relations. All pass
   the inclusion-minimality test, and all are connected at local altitude three
   with exact BFS distance at most three **inside
   `BoundedGeneratedKMGraph 3`**, the generated raw, unquotiented,
   arity-at-most-three graph. The report supplies aggregate
   counts but no per-relation path/context certificates and proves no
   dimension-lift or full-scheme statement.

The evidence gate for the post-adversarial theorem ladder is therefore open.
The next Lean work is the normalized pure-tensor carrier, typed local relations,
their legality/preservation lemmas, and the finite $L_2$ then $L_3$ candidates.
The abstract circuit theorem remains the upstream decomposition layer; it does
not become a KM/Arai theorem merely because this bounded census succeeded.
