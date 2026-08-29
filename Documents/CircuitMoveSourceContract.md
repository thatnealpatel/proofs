# Circuit Move Source Contract

## Scope and status

This document is the source-fidelity boundary for the circuit-move campaign in
`Plans/CircuitMoveFormalization.md`. It separates statements in the primary
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

## Parity-to-box technical deferral

The arithmetic statement remains mathematically supported but is not included
in the present Lean tranche. A faithful formal theorem requires the following
explicit data and bridges:

1. finite row and column index types and an integer matrix
   $A:\operatorname{Fin}(d)\to\operatorname{Fin}(N)\to\mathbb Z$;
2. predicates proving every $A_{ij}$ and target representative $m_i$ is
   exactly `0` or `1`;
3. an enumeration of the finite tensor configuration and a coordinate
   equivalence to $\mathbb F_2^d$;
4. an equivalence between finite subsets and binary indicator vectors;
5. a proof that subset evaluation corresponds to $Ax\equiv m\pmod 2$;
6. integer divisibility lemmas defining
   $z_i=((Ax)_i-m_i)/2$ and proving
   $0\le z_i\le\lfloor N/2\rfloor$.

Once fixed, the intended codomain is the box-constrained integer fiber

$$
[A\mid-2I](x,z)=m,
\qquad 0\le x_j\le1,
\qquad 0\le z_i\le\left\lfloor\frac N2\right\rfloor.
$$

It is not an unrestricted nonnegative toric fiber. No claim is made that an
applicable Graver element of this signed matrix projects to a binary circuit;
that would require a separate slack-coordinate conformality theorem.

## Computational evidence reviewed

The read-only factor-dimension-two report under `~/x/tensor` exhaustively
enumerates squarefree nonempty circuits through support five in its 27-element
carrier. It reports:

- raw circuit counts by supports $1$ through $5$: $0,0,27,81,243$;
- symmetry-orbit counts: $0,0,1,1,2$;
- 14 orientation orbits after identifying converse.

The report's own metadata says
`schema_classification_included=false` and
`path_compilation_included=false`. It therefore supplies circuit-census
evidence, not a source-schema classification or a circuit-to-KM/Arai
compilation theorem. No factor-dimension-three adversarial report was available
for this campaign, so no compilation conjecture was promoted to a formal
statement.
