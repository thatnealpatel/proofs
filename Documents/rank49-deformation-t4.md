# Rank-49 deformation T4: accepted computational tranche

## Status and scope

This document integrates the four deterministic T4 acceptance artifacts for the
fixed binary length-49 presentation.  It is a **scoped computational research
result, not a declaration that the whole T4 card is complete**.  The accepted
claims are:

1. a field-valued-point theorem for the stabilizer of the fixed presentation,
   with finite `F2`/`F4` witnesses and an independent replayer;
2. an exhaustive census of all five-slot restricted first-order systems;
3. exact generic Jacobian, connected-action, orbit-sweep, and binary quadratic
   calculations; and
4. the field-valued parameter correspondence for the displayed `G_m` family,
   including direct `F2` and `F4` fiber checks.

Scheme equality for the stabilizer, representability of its quotient, the
scheme structure of the parameter correspondence, component assertions, and
minimal-rank assertions remain outside the accepted result.  The terms
“proved” and “exact” below mean deterministic exact arithmetic plus the stated
finite or polynomial certificate; they do not mean that the numerical
certificates have been formalized in Lean.

## Prominent correction to the T4 card

> **The card's outer-action sentence is false.**  Rotations permute the three
> scalar sandwich coordinates, but every reflection both permutes **and
> inverts** them.  Consequently the diagonal `G_m` is normalized and is fixed
> by rotations, but a reflection sends `t` to `t^-1`; it is not central under
> all six outer actions.  The subgroup scheme fixed by all six monomial actions
> is the diagonal `mu_2`, with Laurent equalizer ideal
> `(p-q, q-r, p^2-1)`.  In characteristic two it has one geometric point but is
> nonreduced and may have nonidentity points over nonreduced algebras.

This corrected monomial calculation does **not** close the scheme-theoretic
stabilizer problem.  Equality of the proposed stabilizer scheme with the
three-torus, equality on arbitrary (especially nonreduced or disconnected)
test algebras, and representability or point formulas for
`Stab_wit,x / C_x` are unproved.  No naive quotient of point groups is used.

Two other card statements are stale relative to the accepted v2 parameter
artifact.  That artifact now checks all 49 evaluated summands for nonzeroness
and pairwise distinctness on all `G_m` fibers, and it proves pointwise `F4`
separation within its full declared sandwich/gauge/permutation/six-orientation
action.  These improvements are still fiberwise/field-point results, not a
scheme-structure theorem or a count of all ambient decompositions.

## 1. Fixed object, conventions, and meanings

### 1.1 Authenticated presentation

The sole numerical runtime input is the vendored fixture

```text
Programs/BilinearComplexity/rank49_t4/fixtures/4x4x4_m49_c680_iteration65_Z2.txt
SHA-256 5fc92a6bf83fc29d9527ab100bad5d72d769178b616b31a36c3c0c0b8ad9d09d
bytes 4716; header 4 4 4 49; four lines
```

The original locator
`/home/exedev/x/tensor/data/z2/4x4x4_m49_c680_iteration65_Z2.txt` is retained
as historical provenance only. No producer or checker opens it. The vendored
fixture has the same authenticated bytes and makes the bundle relocatable.

It gives ordered triples `x_l=(U_l,V_l,W_l)`, `0 <= l < 49`.  Each factor is a
`4 x 4` binary matrix represented by a 16-bit word, with bit `4*i+j` equal to
entry `(i,j)`.  Tensor coordinate `(i,j,k)` has bit index `256*i+16*j+k`.
All three factor lists contain 49 nonzero, pairwise distinct matrices.  The
artifact-level digest of the decoded 49 triples is
`6268c06eb811567c77a5e0f75222e8bf7ec6f8bf6f2ebf841ea0bb559353df7e`.
The source represents the `4 x 4` matrix-multiplication tensor: all 4096 Brent
coordinates are checked exactly.

All lane artifacts record generation base Git revision
`6866f8be63692dc918e26d75db9414325b03b78c`. This revision authenticates the
repository base used to generate the artifacts. The integration checker
requires that commit object to exist and uses `git merge-base --is-ancestor` to
require it as an ancestor of current `HEAD`; later commits are allowed because
every delivered bundle file is still checked by byte count and SHA-256.

### 1.2 Deformation maps

A variation is

```text
d = ((u_l,v_l,w_l))_(l=0)^48 in F_2^(49*3*16) = F_2^2352.
```

For the sum of rank-one terms, the linear and quadratic coefficients are

```text
J(d) = sum_l (u_l⊗V_l⊗W_l + U_l⊗v_l⊗W_l + U_l⊗V_l⊗w_l),
Q(d) = sum_l (u_l⊗v_l⊗W_l + u_l⊗V_l⊗w_l + U_l⊗v_l⊗w_l).
```

The mixed polarization `B(d,e)` is the sum of the six terms obtained by putting
one variation from `d` and one from `e` into two different factor positions.
In characteristic two,
`Q(d+e)=Q(d)+Q(e)+B(d,e)`.  The second-order lifting equation is
`J(d_2)+Q(d_1)=0`.

The connected action differential `dH` has 146 displayed generators: two
term-scaling generators for each of 49 terms and 48 elementary sandwich
variations.  Its image lies in `ker J`; overlap among the raw generators must
be computed rather than subtracted by counting.

For a five-slot support `S`, the raw restricted domain has `48|S|=240`
columns.  Each selected nonzero term has exactly its two-dimensional local
scaling kernel.  The census uses an authenticated direct-complement reduction
which deletes those ten directions, leaving five 46-column blocks and 230
reduced columns.  Its “normal dimension” is the dimension of the restricted
kernel after comparison with the ambient connected-action image.  It is a
linear quotient dimension, not a local geometric slice.

A **factor three-circuit** is a minimal linear dependence among three matrices
in one factor list.  A **derivative block circuit** is a minimal dependence
among the five reduced 46-column derivative blocks: the five-block system is
independent after omitting any block, but dependent using all five.  These
notions coincide on the accepted exceptional supports only through an explicit
paired-circuit certificate; neither is the definition of the other.

`Scheme.Valid` means exactly: the 49 evaluated rank-one tensors sum to the
target tensor, every evaluated term is nonzero, and the slot-to-evaluated-term
map is injective.  A valid length-49 presentation proves rank at most 49; it
does not prove that tensor rank is 49.

### 1.3 Equivalence witnesses and fields

For an oriented source triple `(U_l^sigma,V_l^sigma,W_l^sigma)`, a witness over
a field `K/F2` consists of `P,Q,R in GL_4(K)`, one common term permutation
`pi`, and nonzero term scalars satisfying

```text
P U_l^sigma Q^-1 = lambda_l U_pi(l),
Q V_l^sigma R^-1 = mu_l V_pi(l),
R W_l^sigma P^-1 = nu_l W_pi(l),
lambda_l*mu_l*nu_l = 1.
```

The JSON replayer uses inverse multipliers as replay-side gauges.  A physical
outer orientation is not a term permutation and is not, by itself, a return
map to the fixed presentation.

The following are kept separate throughout:

* `F2`-rational points, `F4`-rational points, and points over arbitrary field
  extensions or an algebraic closure;
* equality of sets of field-valued points and equality of schemes;
* the witness point group, the proposed quotient group scheme, and the direct
  effective image on decomposition data;
* a support-restricted statement and a global-coordinate statement.

## 2. Stabilizer of the fixed presentation

### 2.1 Exhaustive field-point argument

The six physical orientations are

| name | oriented factors |
|---|---|
| `id` | `(U,V,W)` |
| `cyc` | `(V,W,U)` |
| `cyc2` | `(W,U,V)` |
| `rev` | `(W^T,V^T,U^T)` |
| `rev_cyc` | `(U^T,W^T,V^T)` |
| `rev_cyc2` | `(V^T,U^T,W^T)` |

The three projective factor-circuit hypergraphs are defined over `F2`, so their
ranks and incidence data are unchanged after every scalar extension.  Their
circuit counts at the target are `(29,29,27)`.  Four nonidentity orientations
are rejected immediately by the ordered counts.  `rev_cyc2` has the same
counts but is rejected by the incidence-degree histogram: degree triple
`(1,2,1)` occurs eight times in the oriented data and six times in the target.
Thus all five nonidentity branches are proved impossible over every field
extension; there is no timeout, solver cap, or heuristic negative branch.

In the identity branch, invariant color refinement has 16, then 46, then 49
colors.  The final colors are singleton, so the only compatible term
permutation is `pi=id` over every extension.  Projective frame systems then
force

```text
P=p I_4,  Q=q I_4,  R=r I_4
```

with `p,q,r` nonzero; the factor equations uniquely force the uniform gauges.
An independent, explicitly `F2`-only colored-pair and 48-variable linear
calculation is retained as a crosscheck, not promoted to the geometric proof.

Define the scalar witness functor

```text
C_x = G_m^3,
(p,q,r) |-> (pI_4,qI_4,rI_4; replay gauges q/p,r/q,p/r; pi=id; sigma=id).
```

It fixes each raw factor triple exactly.  The accepted field-point theorem is

```text
Stab_wit,x(K) = C_x(K)
```

for every field extension `K/F2`, within the explicitly displayed witness
parametrization.  Its direct effective image on the decomposition data is
trivial.  Hence it acts trivially on terms, supports, `ker J`, `image(dH)`, the
normal tangent quotient, and `coker J`.  This is an assertion about the direct
field-point image, not a representation of an unconstructed quotient scheme.

Finite checks give:

| field | `|C_x(K)| = |K^x|^3` | replayed witnesses | direct effective image |
|---|---:|---:|---:|
| `F2` | 1 | 1, with 147 factor equations | 1 |
| `F4` | 27 | 27, with 3969 factor equations | 1 |

The 146-column connected differential has rank 143 and three-dimensional
kernel, exactly the three scalar-sandwich/compensating-gauge tangent vectors.
Its elimination-basis digest is
`cf9b3e5e362660280ce4d7a029b98bb87a5aea8040f7cfb84dbcea9f5e346990`.
This is not the 2352-column Brent Jacobian calculation.

### 2.2 Correct outer conjugation action

With conjugation convention `sigma S(P,Q,R) sigma^-1`, the exact action is:

| orientation | `(p,q,r)` under conjugation | inversion? |
|---|---|---|
| `id` | `(p,q,r)` | no |
| `cyc` | `(q,r,p)` | no |
| `cyc2` | `(r,p,q)` | no |
| `rev` | `(p^-1,r^-1,q^-1)` | yes |
| `rev_cyc` | `(q^-1,p^-1,r^-1)` | yes |
| `rev_cyc2` | `(r^-1,q^-1,p^-1)` | yes |

All six maps are replayed on all 27 points of `C_x(F4)`, for 23,814 mapped
factor conjugation equations.  Their `F4` fixed-point counts are respectively
`27,3,3,3,3,3`, giving seven orbits of **torus coordinates under outer
conjugation** by Burnside.  This number seven is not a family-decomposition
orbit count.

Individual fixed subgroup schemes of the abstract monomial action are:

| action | fixed subgroup |
|---|---|
| `id` | `G_m^3` |
| `cyc`, `cyc2` | diagonal `G_m` |
| `rev` | `mu_2 x G_m`, equations `p^2=1`, `qr=1` |
| `rev_cyc` | `G_m x mu_2`, equations `pq=1`, `r^2=1` |
| `rev_cyc2` | `G_m x mu_2`, equations `pr=1`, `q^2=1` |
| all six | diagonal `mu_2` |

The artifact's key spelling `F2[p+-1,q+-1,r+-1]` is only an informal rendering
of the Laurent ring `F2[p^{±1},q^{±1},r^{±1}]`.

### 2.3 Scheme boundary

The candidate ambient witness functor is
`H_wit=(GL_4^3 x D) semidirect (S_49 x S_3)`, where
`D={(g_l^U,g_l^V,g_l^W):g_l^U g_l^V g_l^W=1}`.  The stabilizer is intended as
the equalizer of the displayed factor equations.  The artifact lists a
standard conditional route from geometric points plus the tangent calculation
to scheme equality, but it deliberately does not promote that route because
the following machine-checked coordinate-ring premises are absent:

* representability/finite type and closedness for the displayed functors;
* a replayed closed immersion `C_x -> Stab_wit,x` and normality calculation;
* identification of the emitted differential with the scheme's Zariski
  tangent map.

Therefore `Stab_wit,x(A)=C_x(A)` for arbitrary `F2`-algebras `A`, scheme
equality, and `Stab_wit,x/C_x` representability or `A`-points are unknown.

## 3. Exhaustive support-five census

### 3.1 Coverage and elimination logic

The v4 checker iterates, in lexicographic `itertools.combinations` order, every
one of

```text
binom(49,5) = 1,906,884
```

five-slot supports.  It does not sample and does not quotient before checking.
For each support it constructs the exact five-block reduced derivative,
computes rank, the restricted kernel, intersection with the ambient sandwich
image, factor three-circuits, and the derivative block-circuit signature.
Every record is written as a singleton orbit because the certified `F2` direct
effective action is the identity.  The stabilizer theorem additionally shows
that the direct effective field-point image stays trivial after every field
extension, but no quotient-scheme orbit statement is inferred.

The complete rank table is:

| reduced rank | reduced kernel / normal dimension | derivative-block kind | supports |
|---:|---|---|---:|
| 230 | 0 / 0 | independent | 1,906,821 |
| 229 | 1 / 1 | minimal dependent; every four-block rank 184 | 63 |

For every support the quotient-sandwich intersection dimension is zero in the
reduced model.  In raw coordinates the exceptional systems have kernel
11 = 10 local-scaling directions + 1 normal direction.  The full binary model
has Jacobian shape `4096 x 2352`, rank 2155, kernel dimension 197; after removing
98 local-scaling coordinates it has shape `4096 x 2254`, the same rank, and
kernel dimension 99.  The quotient sandwich rank is 45, giving ambient normal
tangent dimension `99-45=54` (equivalently `197-143=54`).

Factor-list circuit counts are `U:29`, `V:29`, `W:27`.  The paired-T3 generator
finds 252 ordered witnesses but 63 unique five-slot supports.  The census and
paired-T3 support sets agree exactly: there is no non-T3 rank-229 support and no
paired-T3 support outside the rank-229 list.

| orientation mask | orientations represented | supports | canonical section already T3 | gauge-corrected |
|---:|---|---:|---:|---:|
| 9 | `abc`, `acb` | 21 | 10 | 11 |
| 20 | `cab`, `cba` | 21 | 0 | 21 |
| 34 | `bca`, `bac` | 21 | 14 | 7 |
| **total** | | **63** | **24** | **39** |

Here an orientation mask records all available paired-circuit orientations;
the artifact stores a deterministic canonical witness separately.

### 3.2 Rational and geometric directions

Every positive support has normal dimension one.  Thus its projectivized normal
direction space is `P^0`, containing exactly one point over `F2` and exactly one
geometric point after scalar extension.  Every other support has normal
dimension zero.  Since matrix rank is unchanged under extension of the binary
coefficient matrices, this is simultaneously a complete `F2` and algebraic-
closure classification of five-support normal first-order directions.  It does
not identify point sets merely from equal dimensions: the reason no new
geometric direction appears is specifically that every positive space is
one-dimensional and already has a nonzero `F2` vector.

This census concerns five-slot leading variations.  It is not a search for
distant finite decompositions or finite replacements.  The prior statement
that all supports of size at most four are gauge is an imported audited boundary
fact, not regenerated by this five-support checker.

### 3.3 Obstructions, representative corrections, and exact families

For each of the 63 `P^0` directions the artifact emits the deterministic normal
section representative, its full quadratic residual, and two separately
checked membership witnesses:

| test | accepted result on all 63 directions | meaning |
|---|---|---|
| same-support obstruction class | `vanishes` | a stored preimage of `Q(d)` exists under the same five-support restricted Jacobian |
| full-coordinate obstruction class | `vanishes` | a stored preimage of `Q(d)` exists under the full 2352-column Jacobian |
| same-support lift | exact paired-T3 normal-class family | an all-order five-support family exists after the stored gauge correction |
| full-coordinate lift | same exact family | the same family is also a full-coordinate lift |

The same-support and full-coordinate preimage vectors are both stored; they are
not silently identified, and in several records their weights differ.  This is
stronger than a basis-only obstruction test because each normal projective
space is `P^0`.  It would not by itself solve a higher-dimensional projective
quadratic locus, but no such support occurs here.

For 24 supports the deterministic section equals a canonical T3 tangent.  For
39 it does not.  Each mismatch record stores five local-scaling correction
coefficients and an integrated product-one gauge path.  With `q=1+tau`, the
three exponent sums are zero termwise, so composing the paired-T3 family with
that gauge path gives the displayed section's **normal class**.  The report
therefore claims exact integrability of the normal class, not literal equality
of an uncorrected section with the canonical tangent.

Every canonical witness expands the local tensor difference as

```text
Delta = s*A + t*B + s*t*C,       A=B=C,
(1+s)(1+t)=1.
```

In characteristic two this relation is `s+t+s*t=0`, hence `Delta=0` in all 4096
coordinates.  Taking `b=1+t` gives `t=tau`,
`s=tau/(1+tau)=1+b^-1`, so the family is exact over every characteristic-two
field and formally over `Fbar_2[[tau]]`.  This is an all-order identity, not an
inference from a finite Hasse truncation.

The 63 supports, grouped by orientation mask, are:

* mask 9:
  `{0,7,32,39,45}`; `{0,23,35,39,45}`; `{1,8,26,37,42}`;
  `{1,14,29,37,42}`; `{2,15,22,36,44}`; `{2,15,22,43,48}`;
  `{2,36,43,44,48}`; `{3,4,10,38,46}`; `{3,4,21,25,38}`;
  `{5,6,9,11,31}`; `{5,6,19,31,33}`; `{5,9,11,19,33}`;
  `{7,23,32,35,45}`; `{8,14,26,29,42}`; `{10,21,25,38,46}`;
  `{12,16,17,30,41}`; `{12,16,28,34,41}`; `{13,18,20,27,47}`;
  `{13,20,24,27,40}`; `{17,28,30,34,41}`; `{18,24,27,40,47}`.
* mask 20:
  `{0,7,23,32,45}`; `{0,32,35,39,45}`; `{1,8,14,37,42}`;
  `{1,8,26,29,42}`; `{2,15,22,36,43}`; `{2,15,43,44,48}`;
  `{2,22,36,44,48}`; `{3,4,21,38,46}`; `{3,10,25,38,46}`;
  `{4,10,21,25,38}`; `{5,6,9,31,33}`; `{5,6,11,19,33}`;
  `{5,9,11,19,31}`; `{7,23,35,39,45}`; `{12,16,17,28,41}`;
  `{12,17,30,34,41}`; `{13,18,24,27,47}`; `{13,20,27,40,47}`;
  `{14,26,29,37,42}`; `{16,28,30,34,41}`; `{18,20,24,27,40}`.
* mask 34:
  `{0,7,23,39,45}`; `{0,23,32,35,45}`; `{1,8,14,29,42}`;
  `{1,26,29,37,42}`; `{2,15,22,44,48}`; `{2,15,36,43,44}`;
  `{2,22,36,43,48}`; `{3,4,10,25,38}`; `{3,21,25,38,46}`;
  `{4,10,21,38,46}`; `{5,6,9,11,33}`; `{5,6,11,19,31}`;
  `{5,9,19,31,33}`; `{7,32,35,39,45}`; `{8,14,26,37,42}`;
  `{12,16,30,34,41}`; `{12,17,28,34,41}`; `{13,18,20,24,27}`;
  `{13,24,27,40,47}`; `{16,17,28,30,41}`; `{18,20,27,40,47}`.

### 3.4 Census coverage certificates

The 1,906,884 JSONL records are in combinadic IDs `0..1906883`, first support
`{0,1,2,3,4}`, last support `{44,45,46,47,48}`.  The deterministic gzip uses
level 9, empty filename, and `mtime=0`.

| certificate | SHA-256 |
|---|---|
| support order | `392c99d7617a113ca1efcc0a2b513d6ef9bcd03bd6a24b0fdc41e8031f18eaa7` |
| rank/gauge/normal stream | `00aa6f5b01c852220af5f4311014cfe0daad60100c0f5e4b93f01f86be295eae` |
| complete classification | `b43f6322519111a5ffca80635e310baf49004160b045067aba486000793a8107` |
| non-self-referential census content | `4e9844bb140031dee4396a6327915ce37757dd8f5e8005df4832f851ba28c017` |
| uncompressed JSONL (1,585,377,651 bytes) | `f84fbef87ed0854f4677c0e38b9788eb483531023ff7d62dd04d6892a20ffad5` |
| compressed JSONL | `99ea851b7dec758b3e302f306f93220969df7ef26073cfc4afa384d60c71bf7b` |
| length-prefixed body stream | `b4595515af48c2776e0c33ca7fd0a0a7705b093f60804cb2945256d182af0966` |
| cross-digest | `7dc16f181bf98e1ef435cd4560940ef8958b2e27a2ca6cde54535a50abaf6948` |

These are coverage/integrity certificates.  A hash is not used as a substitute
for equality of supports or equations; full check mode reconstructs and
compares the semantic census and streams all records.

## 4. Generic germ and binary quadratic map

### 4.1 The certified family

The distinguished support is `{1,14,29,37,42}`.  Put

```text
t = 1+b,   s = 1+b^-1,   b in G_m.
```

The `s` updates add mask `0500` to the `U` factors of terms 1, 37, and 42.
The `t` updates add `0070` to `W_14`, `9990` to `U_29`, `7707` to `W_37`,
and `0070` to `W_42`.  All other factors are fixed.  Laurent replay proves the
sum tensor is constant; `b=1` is the binary source.  Neither `b=0` nor
`b=infinity` is a fiber.

### 4.2 Exact polynomial rank certificates

The generic checker works over `F2(b)`.  It clears Laurent denominators into
`F2[b]` and evaluates every element of `GF(2^9)`, with modulus
`x^9+x^4+1`.  This is not probabilistic sampling: each claimed polynomial has
a proved degree below 512, so agreement or vanishing at all 512 field elements
is a polynomial identity.  Lower-rank minors are explicit monomials in `b` and
therefore nonzero on `G_m`.

| matrix | exact rank on `G_m` | lower determinant | degree bound used for upper certificate | conclusion |
|---|---:|---|---:|---|
| fixed 44-term Jacobian block, `4096 x 2112` | 1958 | constant echelon certificate | — | fixed rank 1958 |
| 240 moving columns modulo fixed block | 197 | selected 197-minor `b^208` (unscaled `b^11`) | every 198-minor degree <=396 | quotient rank 197 |
| full Jacobian, `4096 x 2352` | 2155 | sum of preceding ranks | preceding upper bound | kernel dimension 197 |
| connected `dH`, 146 columns | 143 | selected minor `b^143` | every 144-minor degree <=288 | rank 143 |
| connected orbit plus family tangent, 147 columns | 144 | selected minor `b^288` | selected-minor degree <=431 | family tangent is outside orbit tangent |

There is no Jacobian or connected-action rank jump on `G_m`.  The complete
finite-field rank evaluation digests and the selected rows/columns are stored
in `generic_germ.json`.  The generic Jacobian result is notably **not** kernel
144: its kernel is 197, leaving a 54-dimensional tangent quotient by the
143-dimensional connected orbit.  The orbit-plus-family differential has rank
144, so 53 tangent directions remain beyond that displayed sweep.

These ranks do not determine a component dimension.  In particular, rank 144
of the sweep proves that the family direction is independent of the orbit
direction; it does not prove smoothness, reducedness, local dimension 144, or
that the sweep is an irreducible component.

### 4.3 Full binary quadratic vanishing

At the binary base point the checker constructs a deterministic vector-space
direct sum

```text
ker J = image(dH) direct_sum N,
dim ker J=197, dim image(dH)=143, dim N=54.
```

`N` is a linear complement, not a normal, local, or formal slice.  The cokernel
has dimension `4096-2155=1941`; it is used as an obstruction container, not
claimed to be a miniversal obstruction space.

The checker reduces every coefficient of the quadratic map on a deterministic
197-vector kernel basis:

| coefficients reduced modulo `image J` | count | nonzero remainders |
|---|---:|---:|
| diagonal `Q(e_i)` | 197 | 0 |
| mixed `B(e_i,e_j)`, `i<j` | 19,306 | 0 |
| **total binary quadratic coefficients** | **19,503** | **0** |

It also recomputes the decomposition-sensitive pieces:

| piece | count | nonzero remainders |
|---|---:|---:|
| gauge diagonal | 143 | 0 |
| gauge-gauge mixed | 10,153 | 0 |
| complement diagonal | 54 | 0 |
| complement-complement mixed | 1,431 | 0 |
| complement-gauge mixed | 7,722 | 0 |

Thus the full quadratic obstruction map `ker J -> coker J` is zero and remains
zero after every scalar extension of `F2`.  In particular every binary
first-order tangent has an **unrestricted full-coordinate second-order lift**.
The mixed calculations prove representative independence at quadratic order:
for `h in image(dH)`, `Q(d+h)-Q(d)` lies in `image J`.

This result does not give same-support lifts for arbitrary tangent directions;
the same-support preimages in Section 3 are a separate 63-direction
calculation.  It also says nothing about third and higher obstructions, equation
syzygies, formal smoothness, a miniversal base, or global integrability.

## 5. Pointwise parameter correspondence

### 5.1 Complete declared action and negative branches

For every field extension `K/F2`, define

```text
R(K) = {(b,b') in K^x x K^x : a declared equivalence witness exists over K}.
```

The declared action includes sandwiching, one common term permutation,
product-one term gauges, and all six orientations.  It is exactly the action in
Section 1.3; no smaller permutation-only relation is substituted.

The checker splits `G_m` into `b=1` and `b!=0,1`.  It computes symbolic factor
ranks and all directed pair-product ranks.  There are 882 factor records and
43,218 directed-edge records (`49*49*3` per orientation, six orientations).
Stable colored-graph refinement compares 24 stratum/orientation cells.  Its
negative graph and anchor filters deliberately allow transformations in a
superclass (arbitrary nonzero projective factor gauges and arbitrary `GL_16`
factor maps), so a mismatch is also a valid rejection for the narrower declared
action.  Twenty-two cells are rejected by exact stable-histogram mismatch.  Only
same-stratum `abc` cells survive, and each has 49 singleton stable colors,
forcing the identity term permutation.

The 44 unchanged `U` factors then give a `704 x 300` projective-anchor system of
rank 299.  Its emitted determinant-one minor leaves only the scalar identity
line, over every field extension.  Finally

```text
U_42(b) = U_b + b^-1 U_d,
U_b=9990, U_d=0500,
```

where `U_b,U_d` have rank two as a pair.  Projective equality
`U_42(b')=mu U_42(b)` yields, after clearing nonzero denominators,

```text
mu+1=0,  b+mu*b'=0,
b+b' = (b+mu*b') + b'*(mu+1).
```

Therefore `b'=b`.  Conversely `P=Q=R=I_4`, `pi=id`, `abc`, and all gauges one
is a witness over `F2(b)`.  The exact accepted result is

```text
R(K) = {(b,b): b in K^x}
```

for every field extension `K/F2`, within the declared action.  In particular
there is no `b -> b^-1` branch.  An unequal pair cannot become equivalent after
a further field extension; positive diagonal witnesses already descend to
`F2`.

### 5.2 All-`G_m` validity and finite family orbit counts

On both symbolic strata, all 147 factor matrices are nonzero, all 49 evaluated
rank-one tensors are nonzero, and the stable graph colors are singleton.  The
sum identity holds in all 4096 coordinates.  Hence every field-valued fiber
satisfies the three properties equivalent to `Scheme.Valid`.  This is an exact
computational, fiberwise certificate; `formal_lean_theorem_claimed=false`.

The `F2` and `F4=F2[z2]/(z2^2+z2+1)` fibers are also directly evaluated:

| field | nonzero parameters | direct checks per fiber | family orbit count |
|---|---|---|---:|
| `F2` | `1` | 4096 sum coordinates; 49 nonzero, 49 distinct terms | 1 |
| `F4` | `1,z2,z2+1` | same checks for each parameter | 3 |

The orbit count is `q-1` because `R(F_q)` is diagonal.  These are the orbits
represented by this parameterized family, not all length-49 decompositions of
the matrix-multiplication tensor.  They are also distinct from the seven
`C_x(F4)` outer-conjugation orbits in Section 2.2.

After base change to an algebraic closure, the **set** of geometric parameter
pairs with witnesses is diagonal.  The scheme-theoretic correspondence,
possible nilpotents, and equivalence over arbitrary nonreduced base algebras
are not computed.

## 6. Artifacts, commands, hashes, and authentication

`check_all.py` derives the repository root as
`Path(__file__).resolve().parents[3]` and executes each acceptance argv with
that derived root as its working directory. No particular checkout location is
required. Acceptance commands are read-only with respect to checked artifacts;
generation modes are not run.

| lane | artifact schema | exact acceptance command |
|---|---|---|
| support census | `rank49-t4-support5-census-v4`; stream `rank49-t4-support5-singleton-orbits-v3` | `python3 Programs/BilinearComplexity/rank49_t4/support5_census.py --check --quiet` |
| stabilizer | `proofs.rank49_t4.stabilizer.v2` | `python3 Programs/BilinearComplexity/rank49_t4/stabilizer.py --check` |
| generic germ | `BilinearComplexity.rank49_t4.generic_germ.v3` | `python3 Programs/BilinearComplexity/rank49_t4/generic_germ.py --check` |
| parameter correspondence | `rank49-t4-parameter-orbits-v2` | `sage Programs/BilinearComplexity/rank49_t4/parameter_orbits.sage -- --check` |

The stabilizer acceptance command recomputes the producer artifact byte for
byte and invokes `stabilizer_replay.py` as an independent JSON consumer and
witness replayer.

| path | bytes | SHA-256 |
|---|---:|---|
| `fixtures/4x4x4_m49_c680_iteration65_Z2.txt` | 4,716 | `5fc92a6bf83fc29d9527ab100bad5d72d769178b616b31a36c3c0c0b8ad9d09d` |
| `support5_census.py` | 93,348 | `3af318d568bd76fabea18dcaa77fc12aaad9f2bf776ff48f0235c57756a23a2f` |
| `artifacts/support5_census.json` | 2,171,403 | `1afc16b7db176e4a480fb3c06a5b6cfe104be974bef0c5af3f48ac4d0a4c78de` |
| `artifacts/support5_orbits-99ea851b7dec758b3e302f306f93220969df7ef26073cfc4afa384d60c71bf7b.jsonl.gz` | 16,890,516 | `99ea851b7dec758b3e302f306f93220969df7ef26073cfc4afa384d60c71bf7b` |
| `stabilizer.py` | 74,597 | `d7b5c51498d84d5645d17db8e1def4296716760aaf39fbef27cc1add7ea74995` |
| `stabilizer_replay.py` | 40,627 | `e6caaec294fe2d17aaf85fe2efb7f07ec5cbb057e9c5a90d9180aea8943b2528` |
| `artifacts/stabilizer.json` | 2,891,566 | `0501d01822991a8d1177783fcd4600c6e93cf8c844b10b2264278f42eac3facf` |
| `generic_germ.py` | 52,098 | `4165af7a47cfba2dffe88c6501372fdadccc2d520dba4954f79f60e3bac91425` |
| `artifacts/generic_germ.json` | 195,551 | `fb2ed08df59a07c8b22df9481433cd4939ad9828e038ef3952198e62bb9e9d52` |
| `parameter_orbits.sage` | 51,008 | `e76291a3fb578ccf505c14cf7485483612b5b3b0c47e27b8932b33fd22ce8aa4` |
| `artifacts/parameter_orbits.json` | 453,886 | `b50b6d6c4854095d6001edd3605d7cd9d51eaa096319b4126042ff1ac7ddcb88` |

Top-level payload/content certificates include stabilizer
`da0561aa76c9e037fc9af0168e9d83d2b82377b35050c02eb8fa26bc4586fe3a`,
generic germ
`4d13dffb0be4d4207cab4857fd1015f67d2fff992c0f65e3b3ab417d6b23a79d`,
and support census
`4e9844bb140031dee4396a6327915ce37757dd8f5e8005df4832f851ba28c017`.
The support provenance policy is `fixed generation base; verified present and
ancestor of generation/check HEAD`; the generic-germ policy is `must exist and
be an ancestor of current HEAD`. Both preserve the fixed generation base while
permitting authenticated descendant commits.
The parameter artifact is authenticated by its outer file hash and exact
recomputation. Its provenance fields `t3_lean_provenance` and
`t3_lean_provenance_sha256` are both bound through manifest inventory ID
`paired_circuit_lean` to `Proofs/BilinearComplexity/PairedCircuit.lean` and its
digest `2589a379ec7d9aaf1dbf8972cac0833bc39cc34ba28de1f477165981789001fa`.
That Lean file is authenticated provenance, not a runtime input to Sage.

Artifact generation is deterministic for the authenticated fixture, code,
generation base revision, its enforced ancestor policy, and declared default
limits; dynamic run measurements are emitted on stdout rather than placed in
authenticated content. Each JSON producer writes
a same-directory temporary, flushes and fsyncs it, atomically replaces the
destination, and fsyncs the parent directory. The support stream is
deterministic gzip (level 9, empty header filename, `mtime=0`), fsynced and made
read-only before publication without overwrite under
`support5_orbits-<sha256>.jsonl.gz`; an existing target is reused only after its
size and digest match. Stream and census publication is ordered but not a
two-file transaction: interruption may leave an unreferenced immutable stream,
but a new census is published only after its referenced stream is durable.

`manifest.json` cross-hashes every lane script/artifact, the vendored fixture,
the cards/provenance inputs, and the integration files. It declares no
randomness (empty seed list) and gives enforced wall/RSS limits and expected
`PASS` for each checker. `check_all.py --quick` performs trusted-local integrity
and cross-authentication: it checks canonical manifest encoding and its
self-contained payload hash, that the generation base revision exists and is an
ancestor of current `HEAD`, every file byte count/hash, final schemas, fixture/script/base-policy cross-references, the
content-addressed stream path
and digest, internal payload digests, and the parameter-to-Lean path-and-digest
binding. It neither decompresses the support stream nor executes a lane. The
manifest payload hash is not a signature or external trust anchor; the bundle
assumes the local checker and manifest named here are trusted inputs.

`check_all.py --full` first performs the same checks, then runs the four fixed
commands. Each process and descendant inherits a hard address-space limit; the
wrapper additionally samples aggregate same-process-group RSS, retains the
process group until empty, and terminates it at the wall deadline or an observed
RSS excess. This is effective enforcement for trusted lane programs, not a
cgroup/security boundary against a child that deliberately escapes its process
group. Each lane and the overall summary uses `PASS`, `TIMEOUT`,
`RESOURCE_EXCEEDED`, or `FAIL`.

## 7. Exact conclusions and residual unknowns

### Accepted conclusions

* The direct effective stabilizer **field-point** image of the fixed
  presentation is trivial over every field extension of `F2`; `F2` has one
  torus witness and `F4` has 27, all acting trivially.
* Reflections invert as well as permute torus coordinates.  The all-outer fixed
  subgroup of the abstract monomial `C_x` action is diagonal `mu_2`, not
  diagonal `G_m`.
* Every one of the 1,906,884 five-support derivative systems was checked.
  Exactly 63 have reduced rank 229 and one-dimensional normal quotient; all
  others have rank 230 and no normal direction.
* Those 63 `P^0` directions, rational and geometric, coincide exactly with the
  paired-T3 supports.  Their same-support and full-coordinate quadratic
  obstruction classes vanish; explicit preimages are stored for both
  Jacobians.  Every normal class has an exact characteristic-two `G_m` family
  with explicit representative gauge correction when necessary.
* Along the distinguished family, `rank J=2155`, `dim ker J=197`, connected
  orbit tangent rank is 143, and orbit-plus-family rank is 144 everywhere on
  `G_m`; the exact degree certificates show no rank jump there.
* At the binary point the complete quadratic map from `ker J` to `coker J` is
  zero, including all mixed terms, so every tangent has an unrestricted
  second-order lift and the quadratic class is gauge-independent.
* Within the declared full point action, `R(K)` is diagonal for every field
  extension.  Every `G_m` fiber satisfies the computational equivalent of
  `Scheme.Valid`; the declared family has one `F2` orbit and three `F4` orbits.

### Unknown or explicitly not claimed

1. **Stabilizer schemes:** no machine-replayed affine/Hopf-algebra construction,
   no proved closed immersion/normality of `C_x`, no equality on arbitrary test
   algebras, and no represented quotient `Stab_wit,x/C_x` or formula for its
   points.
2. **Parameter schemes:** only field-valued-point correspondences are known;
   scheme-theoretic diagonal equality, nilpotents, and nonreduced test-algebra
   behavior are unknown.
3. **Components:** tangent dimensions are not component dimensions.  Smoothness,
   reducedness, local/global component dimensions, component incidence, and
   whether the orbit sweep is a component are unknown.
4. **Obstruction theory:** the 1941-dimensional Jacobian cokernel is not proved
   miniversal; third and higher obstruction maps and syzygies are unknown.
   Full quadratic lifting is not all-order integrability.
5. **Support versus global geometry:** the census classifies five-slot leading
   normal directions.  It does not exclude larger-support arcs, distant finite
   points, finite replacements, or global equivalences outside the declared
   action.
6. **Compactification:** `b=0` and `b=infinity` are poles, not fibers.  No DVR
   limit, stable endpoint, or rank-47 boundary decomposition is proved.
7. **Length versus rank:** all accepted objects are length-49 presentations.
   There is no rank reduction and no proof that matrix-multiplication tensor
   rank is minimally 49.
8. **Formalization:** the numerical artifacts and their external search are not
   Lean theorems.  They are structured for later replay through the T1-T3
   semantics, and the parameter validity statement is presently only the
   exact computational equivalent of `Scheme.Valid`.
