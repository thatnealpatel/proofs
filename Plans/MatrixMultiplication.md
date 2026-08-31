# Matrix Multiplication Research Frontier

## Purpose

This is the canonical plan for the exact matrix-multiplication and binary-circuit
research program. It replaces the former circuit-move, symbolic-completeness,
and rank-47 plans. The immediate objective is not a large architecture or a
headline connectivity theorem. The dimension-free pair-to-triple span theorem
has now landed; the next objective is the shortest dependency chain from that
theorem and the existing formal circuit layer to a complete pruned local
candidate generator, typed local moves, and replayable finite certificates.

The executable exploration repository at `/home/exedev/x/tensor` is a
read-only evidence source for this plan. Its computations generate candidate
theorems and finite certificates; they are not proofs. A completed prior-art
and feasibility review now supports a minimal-factor-carrier pivot for the
relation-level theorem. The first implementation work remains the normalized
carrier and automatic five-circuit layer; the eventual certificate should
reduce each relation to its exact factor spans rather than replay the full
343-term dimension-three carrier.

`Documents/CircuitMoveSourceContract.md` remains the authority for what the
Kauers--Moosbauer and Arai--Ichikawa--Hukushima sources actually define or
prove.

## Status vocabulary

Every claim in this plan has one of the following statuses.

- **Repository-proved:** checked by Lean in a committed file in this repository.
- **Experimental Lean checkpoint:** elaborated successfully in the current
  worktree but intentionally excluded from the present plan/document commit;
  it is not part of the repository-proved boundary.
- **Deterministic computational evidence:** reproducible finite computation,
  with the tested carrier and bounds stated explicitly.
- **Source assertion:** attributed to a primary source and subject to the
  source-contract qualifications.
- **Conjecture:** a falsifiable mathematical claim not yet proved.
- **Blocked target:** a desired theorem whose named prerequisites are absent.

A checked report is still computational evidence. A source theorem is not a
Lean theorem. A bounded raw-graph path is not an unrestricted or full-scheme
connectivity result.

## Current proved and audited boundary

### Repository-proved

- `Proofs/BilinearComplexity/BinaryCircuit.lean` proves the abstract
  finite-set binary-cycle decomposition, the constructed circuit-toggle path,
  target-fiber preservation, and the path-specific altitude bound
  $|D\cup E|$. It does not compile a circuit toggle into KM or Arai moves.
- `Proofs/BilinearComplexity/ParityBox.lean` proves the selected-entry
  parity-to-bounded-integer-box equivalence with explicit slack and indicator
  data. It does not establish a Graver projection theorem.
- `Proofs/BilinearComplexity/PairTripleSpan.lean` proves the dimension-free
  binary pair-to-triple span-drop theorem `pair_triple_span_drop`: for five
  injectively represented nonzero pure tensors satisfying a two-equals-three
  relation, all three factors on the triple side lie in the original pair span
  in at least one mode. Its target-independent restriction is not yet connected
  to the normalized finite-set carrier, an executable candidate generator, a
  legal local move, or an ordered full scheme.
- The existing `BilinearComplexity.Scheme` development is an ordered concrete
  matrix-multiplication representation. It is not definitionally the finite-set
  KM carrier or the occurrence-aware Arai carrier.

### Audited source boundary

The exact carrier assumptions, directionality, legality gaps, and move formulas
are recorded in `Documents/CircuitMoveSourceContract.md`. In particular:

- KM schemes are finite sets of nonzero rank-one tensors;
- KM Reduction is directed and rank-decreasing in general, not intrinsically a
  $3\to2$ operation;
- KM's prose Split does not supply a complete formal executable relation;
- reversing a Reduction is weak traversal, not a directed Reduction;
- Arai moves use occurrence-sensitive multiset semantics;
- generated Split identities and Arai Split/Plus must not be identified merely
  because their displayed tensors look similar.

## Governing carrier split

The local normalized carrier in factor dimensions $(a,b,c)$ should be

$$
L_{a,b,c}=(\mathbb F_2^a\setminus\{0\})\times
          (\mathbb F_2^b\setminus\{0\})\times
          (\mathbb F_2^c\setminus\{0\}),
$$

with coordinate evaluation into the corresponding tensor array. Write $L_d$
for $L_{d,d,d}$. Over $\mathbb F_2$ there is no nontrivial scalar
refactorization, so the intended carrier theorem is that normalized triples
evaluate injectively to distinct nonzero pure tensors. The first homogeneous
instances must prove

$$
|L_2|=27,
\qquad
|L_3|=343.
$$

The minimal carriers for five-term circuits also require the heterogeneous
instances

$$
|L_{2,2,1}|=9,\quad |L_{4,1,1}|=15,\quad
|L_{3,2,1}|=21,\quad |L_{2,2,2}|=27.
$$

The following representations remain physically and semantically separate.

1. Local KM-style states: `Finset` subsets of the normalized carrier,
   instantiated through `BilinearComplexity.BinaryCircuit.Scheme`. No concrete
   `BilinearComplexity.CircuitMove.State` declaration currently exists.
2. Arai states: occurrence-aware multisets with their own move relations.
3. Existing `BilinearComplexity.Scheme`: ordered full
   matrix-multiplication schemes.

An explicit multiplicity-one embedding from a finite set to a multiset is
harmless. What is forbidden is an implicit carrier identification or automatic
transfer of a move theorem across that embedding.

The first carrier implementation should use coordinate evaluation. Do not
force a coordinate-array/`TensorProduct` equivalence into the carrier layer
unless the structural proof actually needs both models.

## Immediate local-search tranche

The structural span theorem is complete, and a diagnostic minimal-carrier
path search has passed, but neither fact is yet a repository theorem about
concrete carriers or typed moves. Keep the next production tranche limited to
**Carrier**, **FiveCircuit**, and **PrunedPairTriple**. Do not create the
previously proposed large file tree or begin the full-scheme bridge before the
local generator has a precise completeness theorem and the typed local move
checker has stabilized.

### 1. Carrier

Prove, in dependency order:

1. normalization and decidable equality for nonzero factor triples;
2. coordinate evaluation and its compatibility with addition;
3. nonzeroness and injectivity of evaluation over $\mathbb F_2$;
4. the counts 27 and 343;
5. the instantiation of `BinaryCircuit` by evaluated carrier terms.

No full $4\times4$ pure-tensor carrier should be materialized: it would have
$(2^{16}-1)^3$ normalized triples.

### 2. Automatic five-circuit lemma

For disjoint sides $D,E$ with $|D|=2$, $|E|=3$, five pairwise distinct nonzero
binary vectors, and equal evaluations, prove that $D\cup E$ is automatically a
circuit.

The intended short proof is independent of tensor structure. The five terms
sum to zero. If a proper nonempty subrelation summed to zero, its complement
would also sum to zero, so one of the two zero subsets would have cardinality
at most two. A singleton cannot sum to zero because its term is nonzero. Two
distinct vectors cannot sum to zero over $\mathbb F_2$. Thus no additional
inclusion-minimality hypothesis should be needed.

Pairwise distinctness is expected to suffice, but this remains a target until
its Lean statement lands.

### 3. Complete pruned pair-to-triple generator

For a fixed ordered pair of normalized pure tensors, define the three candidate
loci in which every replacement factor in one chosen mode belongs to the span
of that pair's factors. Define the pruned candidate space as their union,
retaining all nonzero, distinctness, disjointness, and equal-evaluation checks.

Prove that every collision-free binary two-to-three relation from the pair is
present in that union by applying `pair_triple_span_drop`. This is a local
completeness theorem only: it does not establish move legality, context
transport, or a global matrix-multiplication search reduction.

Then compare the complete generator with unrestricted exhaustive enumeration
in dimensions two and three. Record raw candidate and surviving-relation
counts. Record orbit reductions only after specifying and verifying the acting
group and coverage map; the existing dimension-three report does not contain
an orbit-coverage certificate.

### 4. Exact minimal-factor profiles

For a collision-free binary $2\leftrightarrow3$ relation, the automatic
five-circuit lemma gives tensor-span dimension four. The Lovitz--Petrov
Splitting Theorem is a **source theorem**, not yet formalized here; its
five-circuit specialization gives

$$
\sum_i(r_i-1)\le 3,
$$

where $r_i$ is the factor-span dimension. Together with
$4\le r_1r_2r_3$, elementary enumeration leaves, up to mode permutation,

$$
(2,2,1),\quad(3,2,1),\quad(2,2,2),\quad(4,1,1).
$$

All four occur over $\mathbb F_2$. The $9$-term $(2,2,1)$ carrier is
mandatory. Let $e_1,e_2$ be the standard basis of $\mathbb F_2^2$, fix the
unique nonzero $w\in\mathbb F_2^1$, and set

$$
E_{ij}=e_i\otimes e_j\otimes w,
\qquad
J=(e_1+e_2)\otimes(e_1+e_2)\otimes w.
$$

The derived relation

$$
E_{11}+E_{22}=E_{12}+E_{21}+J
$$

is a collision-free five-circuit and no pair within either side shares two
factors. Thus pruning based only on within-side pair reductions does not remove
it. In ambient factor dimension three, $(4,1,1)$ is impossible, so the exact
minimal carriers have sizes $9$, $21$, and $27$.

The formal target is a disjoint exact-span partition: every ambient relation
is represented uniquely by its ordered profile, a tuple of canonical factor
subspaces, and an internal relation whose factor projections span those
subspaces exactly. Certificates for the four displayed representatives cover
all ordered profiles only after an explicit tensor-mode permutation transport
theorem; factorwise maps alone do not permute modes. Enumerating arbitrary
subsets of a larger carrier is not a substitute, because it duplicates
lower-profile relations.

### 5. Passed diagnostic gate

The exact diagnostic generator and output are preserved as campaign artifacts
at `/home/exedev/x/matrix-prior-art/profilepaths.go` and `profilepaths.out`.
They are reproduced by
`go run /home/exedev/x/matrix-prior-art/profilepaths.go`; their SHA-256 hashes
are respectively
`1f126bb8dea51d36ad9bc8f0f1074b3e337d9863aad9fac0439e78cd967eb2f3`
and
`81a45a9ffe1951f19bcc5faa7d321c09b977af95858615b54ca38aa6e8f49e3e`.
The generic finite computation enumerates every arity-one-through-three
squarefree state in the four minimal carriers and uses only
implementation-generated one-factor Split, its pair Reduction inverse, and
ordinary Flip, with nonzero and collision checks. Every one of the $5{,}490$
exact-span ordered relations has a path confined to its minimal carrier at
local altitude three:

| profile | exact circuits | ordered relations | shortest path lengths |
|---|---:|---:|---|
| $(2,2,1)$ | 9 | 90 | all 90 have length 2 |
| $(4,1,1)$ | 168 | 1,680 | all 1,680 have length 3 |
| $(3,2,1)$ | 210 | 2,100 | 1,512 have length 2; 588 have length 3 |
| $(2,2,2)$ | 162 | 1,620 | 1,296 have length 2; 324 have length 3 |

This is reproducible deterministic computational evidence, not a checked
certificate: the aggregate program does not retain explicit path witnesses or
supply an independent replay format. It justifies building the small typed
semantics and replay checker; it does not justify assuming the resulting
theorem or altitude bound before replay is formalized. Generated Split must
remain labeled as an implementation relation, not a source-defined KM Split.

## Typed move layer

Only after the structural tranche stabilizes, define the concrete local move
relations.

### KM finite-set semantics

- Define directed KM Reduction for every legal rank-decreasing instance.
- Define an explicitly **implementation-generated Split** relation with all
  nonzero, distinctness, collision, and finite-set legality checks.
- Define ordinary source Flip separately.
- Define `GeneratedKMLocalWeak` as the weak symmetrization needed for traversal,
  including reverse traversal of directed Reduction.
- Prove evaluation preservation, endpoint cardinalities, collision freedom,
  and directionality for every relation.

Do not call generated Split a formally source-defined KM Split.

### Arai multiset semantics

Define Arai Split, Flip, and Plus on the separate occurrence-aware carrier.
Prove the literal Plus-as-Split-then-Flip identity with multiplicities and all
source preconditions. The KM compilation chain must not depend on an Arai
connectivity theorem.

### Existing ordered schemes

Bridge to ordered `Scheme` only through explicit enumeration and replacement
data. Changing cardinalities require coherent order data across adjacent
vertices; “enumerate each finite set” is not enough for a path theorem.

## Finite evidence and certification targets

### Dimension two

Tensor commit `89c0a84` is deterministic computational evidence for the
complete support-at-most-five census in the 27-term normalized carrier. It
classifies six $2\leftrightarrow3$ orientation classes and records conditional
local KM weak paths of lengths $1,3,1,2,2,2$, all with local altitude three.

The first finite formal target is a typed theorem for this exact carrier and
bounded graph. It should be proved either by structural reduction or by a
small replayable certificate checked inside Lean.

### Dimension three

Tensor commit `fc3baea` is deterministic computational evidence for the
343-term normalized carrier. It enumerates:

- 58,653 pair states in 43,561 evaluation fibers;
- 1,282,134 matching triple states;
- 1,265,670 disjoint exact oriented $2\leftrightarrow3$ relations;
- 126,567 underlying support-five circuits.

All enumerated relations pass the computational minimality test and are
connected at local altitude three in the raw arity-at-most-three graph, with
reported distances one through three. No mask-7 example occurs.

Independent exact computation reproduces the underlying circuit count through
the minimal-profile partition:

$$
126{,}567=
3\cdot7^3\cdot9+6\cdot7^2\cdot210+7^3\cdot162,
$$

The displayed sum is $126{,}567$; multiplying by the ten choices of the
two-term side reproduces the $1{,}265{,}670$ oriented relation count. Here $7$
is each relevant Gaussian subspace count in $\mathbb F_2^3$. This factorization
is the intended certificate theorem, but it remains computational evidence
until the exact-span lift bijection and reduced counts are checked in Lean.

The raw report does **not** emit orbit-coverage certificates or a path for each
relation. A formal relation-level dimension-three theorem should use the
minimal-profile partition and reduced replay rather than raw 343-term replay.
Raw or joint ambient certificates remain necessary for predicates depending on
relative embeddings of several relations, shared tensors, or unchanged global
context.

### Trust boundary

Certificate files are untrusted data. A repository theorem may depend on a
small typed checker that reconstructs carrier elements, replays every named
edge, checks endpoints and evaluations, and verifies the stated altitude and
length. “Verified” JSON, unchecked hashes, aggregate counts, and successful
external BFS are not proof terms.

`BoundedGeneratedKMGraph d` must mean the induced raw graph on squarefree
arity-one-through-three states in the union of pair-containing evaluation
fibers. It is distinct from:

- unrestricted `GeneratedKMLocalWeak`;
- the KM symmetry quotient;
- an Arai move graph;
- a full matrix-multiplication target fiber.

## Context and full-scheme bridge

A local path can be lifted only after proving rule-specific context transport
for every named edge. A predicate such as

$$
\operatorname{Disjoint}(C,\operatorname{pathSupport}(p))
$$

is necessary but not sufficient by itself.

A valid lift must provide:

1. factorwise injective maps into ambient matrix spaces;
2. injectivity and cardinality preservation of the induced tensor map;
3. a context $C$ completing the embedded local source to the exact
   matrix-multiplication target;
4. avoidance by $C$ of the union of **all** path vertices, not only endpoints;
5. legality of each named move after adjoining $C$;
6. coherent ordered enumeration/replacement data when producing `Scheme`s.

If the local path has altitude three, the lifted full-scheme altitude is

$$
|C|+3,
$$

not three. Arbitrary local linear automorphisms do not preserve a fixed
matrix-multiplication target; covariance must transport the target, embedding,
and context, or restrict to a target-preserving subgroup.

After this bridge, prove generic dependent path substitution for one abstract
circuit toggle. Global compilation still requires a compiler for every circuit
class produced by the abstract decomposition; support-five evidence alone does
not provide that.

## Conditional symbolic consequence

For a finite move graph already proved connected, singleton edge relations and
singleton identity tests generate every relation under composition and finite
union. Hence a statement of the form

$$
Q_n=\operatorname{Rel}(X_n)
$$

is routine relation-algebra infrastructure conditional on a proved named-move
connectivity theorem. It is not a headline matrix-multiplication theorem, does
not imply an efficient symbolic representation, and should not be developed
before the connectivity and carrier semantics exist.

Weighted relations, quotient paths, Kleene structure, or bottleneck semantics
are later infrastructure. Any quotient theorem must lift concrete paths while
preserving the entire altitude sequence; ordinary reachability preservation is
insufficient. The former coarse $r n^4$ altitude claim is discarded.

## Rank-47 conjectural frontier

The following independent M4 questions remain conjectures. They are retained
because each is directly falsifiable on a newly discovered full-span rank-47
scheme; none is evidence for the local support-five compilation theorem.

1. **Infinitesimal rigidity.** Every full-span rank-47 decomposition over
   $\mathbb F_2$ has Brent-Jacobian kernel equal to the 139-dimensional tangent
   space generated by term rescalings and infinitesimal sandwich action.
2. **Restriction ladder.** Every such decomposition admits an intrinsic
   compatible rank-2 idempotent restriction with exactly seven surviving terms
   and a rank-3 restriction with at most 24 surviving terms.
3. **Native irredundancy.** Every such decomposition has 47 distinct
   projective factors in each leg and full rank 47 in each complementary
   Khatri--Rao family.
4. **Original-class rank-48 barrier.** No two of AlphaTensor,
   Kauers--Moosbauer, and c680 are connected by a certified composite path of
   maximum rank 48, modulo term permutations, tensor orientations, and sandwich
   equivalence.

Tests must construct exact witnesses: tangent generators and Jacobian kernels,
all compatible idempotent triples, factor/Khatri--Rao ranks, or persisted
parent-and-move certificates. Failed random search is not evidence for a
barrier.

## Explicitly rejected directions and nonclaims

- Do not create the speculative 20-file architecture before structural and
  move APIs stabilize.
- Do not claim a profile classification or dimension-free compilation theorem
  before proving it.
- Do not use nonexistent dimension-three orbit certificates.
- Do not identify abstract circuit toggles, generated KM weak paths, Arai
  multiset moves, bounded raw graphs, or context-lifted full schemes.
- Do not infer Arai connectivity from direct Plus classifications.
- Do not infer a full-scheme theorem from local altitude-three evidence.
- Do not claim bounded-rank connectivity from source-stated unbounded weak
  connectivity.
- Do not assert a Graver projection without a slack-conformality proof.
- Do not materialize the full relation algebra or the M4 pure-tensor carrier.
- Do not force coordinate tensors and `TensorProduct` into one carrier API
  without a proof-driven need.

## Dependency-ordered next work

1. Land and review the heterogeneous normalized coordinate carrier, including
   nonzero/injective evaluation, homogeneous counts 27 and 343, and the
   `BinaryCircuit` instantiation.
2. Land the automatic five-circuit theorem.
3. Define the three span-constrained pair-to-triple loci and their union as an
   executable local candidate generator.
4. Prove generator completeness from `pair_triple_span_drop`, with explicit
   nonzero, injectivity, disjointness, and equal-evaluation hypotheses.
5. Prove the specialized five-circuit profile table and define exact-span
   internal relations. Attribute the structural inequality to
   Lovitz--Petrov; do not import Ballico wholesale when the elementary integer
   deduction suffices.
6. Define typed finite-set pair Reduction, implementation-generated Split, and
   source Flip, with directionality and all legality/preservation laws.
7. Specify a small typed certificate format and replay the four reduced
   representative carriers at altitude three. Require every intermediate to
   remain in the minimal factor spans; do not claim all ordered profiles before
   proving tensor-mode permutation transport.
8. Prove factorwise injective-map equivariance, tensor-mode permutation
   equivariance for carriers, moves, and paths, and the canonical RREF subspace
   lift bijection. Derive the dimension-three count from the exact-profile
   partition as a corollary.
9. Prove rule-specific context transport, then the ordered full-scheme bridge
   with coherent `Fin` enumeration/replacement data and dependent path
   substitution.
10. Develop relation-algebra or quotient infrastructure only when a proved
    named-move connectivity result needs it.

A fresh session should begin at item 1 or 2. It should not begin by designing
later graph, quotient, or full-scheme APIs, and it should not treat the proved
local span restriction as an implemented global search reduction.
