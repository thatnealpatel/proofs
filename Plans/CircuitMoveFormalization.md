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
concrete path with path-specific vertices, target-fiber preservation, and the
altitude bound $|D\cup E|$. It deliberately does not claim compilation into
KM/Arai moves. The parity-to-box equivalence, weighted quotient, Graver
projection, and KM/Arai compilation remain deferred with explicit prerequisites.
At tensor commit `65f82da`, the dimension-two report still omits
source-schema classification but now includes bounded path certificates for all
six $2\leftrightarrow3$ classes under provisional algebraic moves. Exploratory
dimension-three evidence is also available, but no deterministic report or
source-faithful compilation statement has yet stabilized; no compilation
conjecture was promoted.

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

The bound $|D\cup E|$ applies to the abstract circuit-toggle graph. It does not
bound KM/Arai paths unless a controlled compilation theorem is proved.

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

The tensor track supplies the complete factor-dimension-two circuit and
compilation report. Both tracks decide which observations merit theorem
statements. No large Lean proof begins at this checkpoint.

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

- materialize $P_4$, whose size is
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
| CMF-007 | Altitude | accepted | Concrete abstract-circuit paths have path-specific vertices and altitude at most $|D\cup E|$; no compiled bound is claimed. |
| CMF-008 | Implementation fidelity | handed off | The source contract is complete; the tensor track must still audit and rename its recognizers before they are KM/Arai operations. |
| CMF-009 | Computational provenance | accepted | Treat tensor reports as conjecture-forming evidence only. |
| CMF-010 | Weighted quotient | deferred | Address after concrete move semantics and bottleneck paths are fixed. |

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
5. **Partially available and reviewed:** the dimension-two version-3 report
   preserves the circuit census and records bounded provisional algebraic paths
   for all six $2\leftrightarrow3$ classes, of length two or three and altitude
   three. Its metadata still explicitly omits source-schema classification.
6. **Exploratory evidence available:** the tensor track reports that a temporary
   dimension-three computation tested 1,265,670 disjoint support-five
   $2\leftrightarrow3$ relations and found provisional paths of length two or
   three and altitude three for all of them. A deterministic committed report
   and source-faithful move classification remain pending. This affects only the
   next compilation campaign, not the closed elementary circuit tranche.

The first stable deliverable is therefore closed at the elementary circuit
boundary. The tensor track can now continue with source-faithful KM/Arai
recognizers and a durable dimension-three report; Lean compilation work should
resume only after that produces a precise statement.
