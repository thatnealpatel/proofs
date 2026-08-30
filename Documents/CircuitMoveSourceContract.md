# Circuit Move Source Contract

## Scope and status

This document is the source-fidelity boundary for the circuit-move program in
`Plans/MatrixMultiplication.md`. It separates statements in the primary
sources from routine consequences, gaps in those arguments, and results proved
in this repository.

The status labels are:

- **source-stated/proved**: stated, and when applicable argued, in the cited
  primary source;
- **routine consequence**: follows by a short explicit argument, but is not a
  separately stated source theorem;
- **unresolved**: absent, false as written, or dependent on a missing legality
  or invariant argument;
- **implementation obligation**: required before an executable recognizer or
  path can be called source-faithful.

A theorem being source-stated does not make an incomplete source proof into a
formal proof. Conversely, a source proof gap does not establish that the
claimed theorem is false.

## Kauers--Moosbauer

The primary source is Kauers and Moosbauer, *Flip Graphs for Matrix
Multiplication*, arXiv:2212.01175, also published at ISSAC 2023, pp. 381--388,
DOI `10.1145/3597066.3597120`. Page references below use the 12-page arXiv PDF.

### Carrier and elementary moves

- **Scheme** — Definition 1, p. 2: a scheme is a **finite set** of nonzero
  rank-one tensors summing to the matrix-multiplication tensor. Its rank is its
  set cardinality. Duplicate tensor occurrences are therefore excluded.
  The displayed factor space for the third factor contains a `p × m` typo; the
  ambient tensor space and the later split use `p × n`.
- **Reduction** — Definition 2 and Proposition 3, p. 3: a nonempty family with
  one factor span of dimension one and another factor family linearly dependent
  can be redistributed after choosing one dependent term, decreasing rank by
  one. The redistribution identity is source-proved. The proof does not check
  that every new term is nonzero or distinct from the other new and unchanged
  terms. Those checks are implementation obligations under Definition 1's
  finite-set carrier.
- **Flip** — Definition 4, p. 4: two terms with a literally common factor are
  replaced by one of the displayed two-versus-two identities, with analogous
  definitions after permuting tensor factors. Reversibility is explicitly
  proved. The premise that the output is another scheme of the same rank
  implicitly enforces nonzero and collision-free outputs; it is not an
  executable precondition test.
- **Split** — prose on p. 6: replace
  $A\otimes B\otimes\Gamma$ by
  $A\otimes B\otimes(\Gamma-\Gamma')$ and
  $A\otimes B\otimes\Gamma'$. Sum preservation and reduction back to the
  original term are routine consequences when both outputs are nonzero,
  distinct, and absent from the unchanged set. The source does not define a
  formal Split relation, and its phrase “arbitrary $\Gamma'$” does not supply
  all of these legality conditions.

The source uses equality of displayed common factors, not merely proportional
factors. An implementation using unnormalized factor triples must separately
specify how literal factor equality relates to equality of rank-one tensors.

### Two-term results

- Lemma 5, pp. 4--5, proves uniqueness of a two-term presentation when all
  three left factor pairs are independent.
- Lemma 6, p. 5, identifies the two relevant factor spans in a two-by-two
  equality under its independence and nonzero hypotheses.
- Theorem 7, p. 5, shows that a nontrivial two-by-two equality with two
  independent factor pairs has a one-dimensional span in the remaining factor
  and equal spans in the two independent factors.
- Corollary 10, pp. 6--7, states the actual two-term flip classification:
  over $\mathbb F_2$, two irreducible schemes of the same rank that differ in
  exactly two set elements are related by a flip.

Corollary 10 is not an arbitrary-field classification, is not a statement
about reducible schemes, and does not classify every relation of total support
at most five.

### Connectivity and quantitative limits

Definition 8, p. 6, takes vertices to be symmetry orbits of schemes. Flip edges
are reversible and reduction edges point to lower rank. Theorem 9, p. 6,
asserts that this directed graph is **weakly connected**: reduction edges are
regarded as undirected for connectivity.

The proof reduces to an irreducible scheme, repeatedly splits coordinates,
combines terms by reductions, and arrives at the standard algorithm. It is a
constructive outline, but it does not provide a complete executable invariant
showing at every split that new terms are nonzero and collision-free. It also
does not provide a bound on:

- path length;
- number of splits, flips, or reductions;
- maximum intermediate rank or altitude.

Accordingly, Theorem 9 may be cited as the source's weak-connectivity result,
but it does not imply bounded-level connectivity or a controlled-altitude
compilation theorem.

## Arai--Ichikawa--Hukushima

The primary source is Arai--Ichikawa--Hukushima, arXiv:2312.16960. Page
references below use the seven-page arXiv PDF; definition and theorem numbering
is the source's numbering.

### Carrier, Flip, and Plus

- **Scheme** — Definition 2.4, p. 2: a scheme is a **finite multiset** of
  rank-one tensors. Multiplicity and duplicate tensors are allowed. The source
  occasionally orders multiset occurrences during its proof, but does not
  replace the carrier by an ordered list or a finite set.
- **Flip** — Definition 2.5, p. 2: the displayed two-versus-two operation acts
  on two terms sharing one factor, with analogous operations after factor
  permutations. The definition supplies no explicit output-nonzero tests.
- **Plus** — Definition 4.1, p. 3: selected terms must satisfy the three literal
  factor inequalities
  $\alpha_i\ne\alpha_j$, $\beta_i\ne\beta_j$, and
  $\gamma_i\ne\gamma_j$. It replaces two occurrences by the displayed three
  occurrences and may be applied after permuting factors.

Over $\mathbb F_2$, assuming input rank-one terms have nonzero factors, those
three inequalities make the displayed new factors nonzero. The analogous
claim is false over a general field without an additional condition such as
$\beta_i+\beta_j\ne0$. No global duplicate-avoidance condition belongs to this
source carrier.

### Plus is Split followed by Flip

The displayed first arrow in Definition 4.1 splits the $j$-term by
$\alpha_i$:

$$
\alpha_j\otimes\beta_j\otimes\gamma_j
\longmapsto
\alpha_i\otimes\beta_j\otimes\gamma_j
+ (\alpha_j-\alpha_i)\otimes\beta_j\otimes\gamma_j.
$$

The second arrow applies Definition 2.5 Flip to the original $i$-term and the
first split term. The split interpretation is also stated in the prose on
p. 4 immediately before Theorem 5.2. Thus

$$
\mathrm{Plus}=\mathrm{Split}_{j\text{ by }\alpha_i};\mathrm{Flip}
$$

is a routine algebraic consequence explicitly supported by the source. It is
not a separately named theorem, and it does not by itself prove that every
Split and Flip intermediate is legal in a different carrier.

### Connectivity proof audit

Lemma 5.1, pp. 4--5, proves that the displayed $\alpha$-factors span their
entire coordinate space; the $\beta$ and $\gamma$ versions are analogous. It
proves span membership, not reachability by legal Plus operations.

Theorem 5.2, pp. 4--5, states that adding Plus edges makes the flip graph over
$\mathbb F_2$ connected. Its proof orders occurrences, pads the smaller
scheme with Plus operations, tries to match each target factor successively,
standardizes surplus factors, and removes the surplus by reductions.

The following are unresolved in that proof:

1. Span membership does not ensure that a term carrying the desired split
   factor is available as a legal Plus partner.
2. Definition 4.1 also requires inequality in the other two factors; the proof
   supplies no partner-selection lemma maintaining all three conditions.
3. No invariant shows that repeated Plus operations preserve an already
   matched prefix of ordered multiset occurrences.
4. “Arbitrary” padding Plus operations are not shown always to exist.
5. The final phrase about reducing “any pairs” is too broad. A conditional
   repair is available only after proving the surplus consists of standard
   basis triples with total sum zero: characteristic two and basis
   independence then give even multiplicity, so identical pairs can be
   reduced.

Theorem 5.2 and its finite-transition corollary are therefore source
assertions, but the cited argument is not promoted here to a proved
constructive connectivity theorem. The source gives local cardinality changes
(Plus $2\to3$, Flip $2\to2$, and the displayed Reduction decrease), but no
operation-count, path-length, maximum-rank, or altitude bound.

## Carrier separation

The two sources do not share one carrier:

| Layer | Carrier | Duplicate policy |
|---|---|---|
| Kauers--Moosbauer | finite set of nonzero rank-one tensors | forbidden |
| Arai--Ichikawa--Hukushima | finite multiset of rank-one tensors | allowed |
| `SchemeMoveAlgebra.lean` | generic multiset of factor triples | allowed; zero and refactorized terms possible |
| `BinaryCircuit.lean` | abstract `Finset α` evaluated in a `ZMod 2`-module | duplicate carrier elements forbidden |

`BinaryCircuit.lean` is intentionally more abstract than a pure-tensor
configuration: it does not assume `value` injective or nonzero. The intended
literal configuration is obtained by taking `α` to be the subtype of a finite
set of distinct nonzero pure tensors and `value` to be subtype coercion. The
file does not identify this carrier with either source's operational carrier
or with the existing multiset scaffold.

## Repository-proved boundary

`Proofs/BilinearComplexity/BinaryCircuit.lean` type-checks, without `sorry`, the
following abstract finite-set results:

1. equal-target schemes have a zero-sum symmetric difference;
2. every finite binary cycle has a recursive certificate as a disjoint union
   of circuit leaves, including the empty decomposition;
3. toggling those leaves constructs a concrete circuit path between the
   endpoints;
4. every actual vertex of that specific path remains in the target fiber and
   in the endpoint union;
5. the path altitude satisfies
   $$
   \operatorname{altitude}(p)\le |D\cup E|\le |D|+|E|;
   $$
6. singleton paths have zero edges, one vertex, and altitude $|D|$.

This is an abstract **circuit-toggle** theorem only. It proves no compilation
into KM Reduction/Flip/Split or Arai Plus, no KM/Arai altitude bound, no
support-five classification, and no weighted-quotient lifting theorem.

## Parity-to-box proved boundary

`Proofs/BilinearComplexity/ParityBox.lean` type-checks, without `sorry`, a
standalone selected-entry parity-to-box theorem. Given finite carrier and row
types, `ZMod 2` coefficients and targets, integer lifts with the required cast
compatibility, and literal-bit hypotheses on selected entries and targets, it
proves:

1. equality modulo two is equivalent to an integer equation with even slack;
2. selected parity equations are equivalent to rowwise integer equations;
3. each slack is uniquely determined and lies between zero and half the
   selected-set cardinality;
4. the integer membership indicator lies in the box $[0,1]$ and converts a
   selected sum to a full-carrier sum; and
5. the selected parity equations are equivalent to the full-carrier bounded
   formulation with $x$ explicitly equal to that membership indicator and
   slack bounded by half the ambient carrier cardinality.

Thus the proved codomain is the box-constrained integer fiber

$$
[A\mid-2I](x,z)=m,
\qquad 0\le x_j\le1,
\qquad 0\le z_i\le\left\lfloor\frac N2\right\rfloor.
$$

The file does not yet construct a normalized tensor carrier, its coordinate
enumeration, or the concrete incidence matrix for matrix multiplication; those
are instantiation obligations for the carrier tranche. The displayed fiber is
not an unrestricted nonnegative toric fiber. No claim is made that an
applicable Graver element of this signed matrix projects to a binary circuit;
that would require a separate slack-coordinate conformality theorem.

## Computational evidence reviewed

The source contract above was committed at proofs commit `6e3a9e5`. The tensor
track subsequently implemented independent source-schema recognizers against
that fixed contract. Code and assertions committed at tensor `89c0a84` and
`fc3baea` reproducibly generate the evidence below with, respectively,

```text
go run ./cmd/localrelation circuits
go run ./cmd/localrelation dimension-three
```

The generated JSON is not a tracked artifact, and the absolute `contract_path`
in its metadata is machine-local; `contract_commit=6e3a9e5` is the durable
contract provenance. These deterministic finite computations are evidence, not
proofs in this repository.

### Factor dimension two

Code at tensor commit `89c0a84` reproducibly generates
`tensor.localrelation.circuits` schema version 4 for the 27 normalized nonzero
pure tensors in $(\mathbb F_2^2)^{\otimes3}$. Here factor dimension two means
three abstract local factor spaces $\mathbb F_2^2$, not $2\times2$
matrix-multiplication spaces. The report retains the exhaustive squarefree
circuit census through support five:

- raw circuit counts by supports 1 through 5: $0,0,27,81,243$;
- symmetry-orbit counts: $0,0,1,1,2$;
- 14 orientation orbits after identifying converse;
- six $2\leftrightarrow3$ classes `O009`--`O014`.

The report now has `schema_classification_included=true`. It uses independently
named KM finite-set and Arai multiset states, applies and replays each recognized
formula, and preserves the carrier distinction. Commit `89c0a84` implements,
tests, and replays those audited schemas; `fc3baea` later adds differential
agreement over the complete embedded factor-dimension-two disjoint exact
$2\leftrightarrow3$ slice for direct KM Reduction and Arai Plus. Its direct
classification of the six $2\leftrightarrow3$ representatives is:

- `O009` and `O011`: direct KM Reduction from the three-term side to the
  two-term side; the displayed converse is only weak reverse-Reduction
  traversal;
- `O014`: direct Arai Plus from the two-term side to the three-term side;
- `O010`, `O012`, and `O013`: no direct audited source-formula match.

All six have conditional local KM weak-edge path certificates of local altitude
three—maximum represented local-set cardinality three—and respective lengths
$1,3,1,2,2,2$. Except for the forced one-edge cases, these are replayed
witnesses rather than globally shortest-path claims. Each KM certificate emits
the union of its path terms as forbidden ambient terms. A full-scheme reading
still requires the report's injective factor-space embedding and one omitted
context that both completes the embedded local source to an actual
matrix-multiplication scheme and avoids that entire forbidden set. Subject to
those hypotheses, a lifted path has full-scheme altitude $|C|+3$, not three.
The provisional `algebraic_*` and `current_z2_squarefree_projection_*` systems
remain separately labeled and are not promoted.

### Factor dimension three

Code at tensor commit `fc3baea` reproducibly generates
`tensor.localrelation.dimension_three` schema version 1 for the 343 normalized
nonzero pure tensors in $(\mathbb F_2^3)^{\otimes3}$. Here factor dimension
three means three abstract local factor spaces $\mathbb F_2^3$, not
$3\times3$ matrix-multiplication spaces. It exhaustively enumerates every
two-term set, every three-term set in a pair-containing evaluation fiber, and
every disjoint exact $2\leftrightarrow3$ pairing. The report records:

- 58,653 pair states in 43,561 evaluation fibers;
- 1,282,134 matching triple states;
- 1,265,670 disjoint exact oriented relations;
- all 1,265,670 passing the explicit inclusion-minimality test;
- 126,567 underlying support-five circuits, with ten $2\leftrightarrow3$
  orientations per circuit.

Direct conditional local formulas cover only part of the census:

- KM Reduction: 203,742 relations and 222,264 descriptors, directed from triple
  to pair; the converse is only weak traversal;
- Arai Plus: 222,264 relations and 444,528 descriptors, directed from pair to
  triple;
- overlap between those direct classes: zero;
- neither direct formula: 839,664 relations.

The report also constructs the exact raw, unquotiented, arity-at-most-three
local KM weak graph over the union of pair-containing evaluation fibers. In the
Plan's proposed terminology this finite induced graph is
`BoundedGeneratedKMGraph 3`, distinct from the unrestricted
`GeneratedKMLocalWeak` edge relation. Its 1,341,130 nodes and 2,478,861 unique
weak edges are processed one fiber at a time, with maximum fiber size 130.
Every enumerated relation is reachable at local altitude three, meaning maximum
raw-state arity three. Exact BFS distances **inside this bounded raw graph** are
203,742 at length one, 777,924 at length two, and 284,004 at length three.
These are not distances in KM's symmetry quotient and not globally shortest
paths in an unbounded or full-scheme graph.
Split transitions in this graph are implementation-generated legality-checked
identities based on KM's prose, not edges of a formally source-defined Split
relation.

The outside-pair-factor-span census has no mask-7 example: every enumerated
relation has some factor position in which all three right factors lie in the
span of the two left factors. This absence is finite-carrier evidence only. It
proves neither structural impossibility of mask 7 nor a lift to larger factor
dimensions.

Unlike the dimension-two class report, the dimension-three aggregate report
emits no per-relation path and no ambient context certificate. Full-scheme KM
applicability remains conditional on an injective embedding and one context
that completes the embedded local source to an actual matrix-multiplication
scheme while avoiding every vertex term on the selected path. Only direct Arai
Plus is classified; no Arai Reduction, path, or connectivity conclusion is
present.

### Relation to the repository-proved boundary

For an inclusion-minimal disjoint equality $D\leftrightarrow E$, the abstract
`CircuitMove` layer regards $D\triangle E$ as one circuit and hence the endpoint
change as one abstract toggle. The tensor reports study a different question:
whether that one abstract edge can be replaced by legal local KM/Arai edges,
possibly through tensors outside $D\cup E$.

Thus the dimension-three result is evidence for compilation of a finite subclass
of abstract circuit edges, not new evidence for the already proved circuit
decomposition theorem. The specifically constructed same-fiber restricted path
in `BinaryCircuit.lean` has bound $|D\cup E|$ because its vertices stay in the
endpoint union; an arbitrary abstract `CircuitPath` need not. A compiled KM path
needs a separate context-lifting theorem based on the union of its own path
vertices. Until the normalized pure-tensor carrier, typed local move relations,
finite compilation theorem, and context-lifting lemma are proved, no KM/Arai
claim follows from the abstract Lean theorem.
