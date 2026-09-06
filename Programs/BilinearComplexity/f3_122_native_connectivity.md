# F3 profile (1,2,2), altitude-4 native-connectivity census

## Scope and outcome

This is a finite computation for semantic atom sets in
`F3^1 ⊗ F3^2 ⊗ F3^2`. It is not a Lean theorem, does not concern the
stopped `(1,3,2)` branch, and says nothing about unbounded F3-LG.

The exact altitude-4 graph is **not connected within every endpoint fiber**:
the empty state is isolated, while the two-atom state

```text
{ (0,0,0,1), (0,0,0,2) }
```

also evaluates to zero. In the artifact encoding this smallest separated pair
is `00000000` versus `00000003`. There is no nonempty obstruction in this
profile and bound: every nonempty fiber is connected through states of
cardinality at most four. All 80 separated pairs of distinct, equal-evaluation
endpoints of cardinality at most three consist of the empty state and a
nonempty zero-sum endpoint.

## Source contract and exhaustive generator

The census follows the accepted revision
`318734eb6daa04fa0d960de42c36aa041efb5908`:

- semantic `Atom` equality and Finset `State` occupancy are in
  `FieldRankOne.lean:131-196`;
- coefficient absorption and gauge preservation are in
  `FieldRankOne.lean:65-127`;
- `FieldNativeMoves.atom` and its surjectivity are in
  `FieldNativeMoves.lean:59-84`;
- the three `SplitFormula` constructors are in
  `FieldNativeMoves.lean:110-150`;
- the ordered shear and six `FlipFormula` orientations are in
  `FieldNativeMoves.lean:152-287`;
- the exact `NativeReplacement` and contextual `NativeStep` fields are in
  `FieldNativeMoves.lean:289-405`.

There are 2, 8, and 8 nonzero raw vectors in the three modes. The program
first enumerates all 256 coefficient-bearing tuples `(q,u,v,w)`, then
quotients by their four tensor coordinates. This gives 32 semantic atoms,
with eight coefficient-bearing representatives per atom. After absorbing the
coefficient into the first factor, there are 128 presentations, four per
atom. Thus the formula generator retains every coefficient and gauge rather
than relying on one canonical factorization.

For every raw presentation the program instantiates all three Split modes and
all six ordered Flip orientations, applies the exact nonzero and semantic
finite-set distinctness guards, and deduplicates only after semantic atom
encoding. A second, source-driven enumerator starts from all four absorbed
presentations of each semantic source atom and reproduces every
orientation-specific local relation exactly.

Every local relation is contextualized with every atom set disjoint from both
the local source and target that keeps both endpoints at altitude at most
four. This is complete because in a `NativeStep D E` the context is uniquely
`D \ source`; `source_subset`, `target_fresh`, and `result_eq` say exactly
that the two endpoints are `context ∪ source` and `context ∪ target`.

## Carrier and generator coverage

The state carrier has

| cardinality | 0 | 1 | 2 | 3 | 4 | total |
|---:|---:|---:|---:|---:|---:|---:|
| vertices | 1 | 32 | 496 | 4,960 | 35,960 | **41,449** |

Raw formula coverage before semantic deduplication is:

| constructor orientation | parameter tuples | nonzero output guards | semantic pair-distinct witnesses | unique directed local relations |
|---|---:|---:|---:|---:|
| Split first | 256 | 128 | 0 | 0 |
| Split second | 1,024 | 896 | 768 | 96 |
| Split third | 1,024 | 896 | 768 | 96 |
| Flip firstSecond | 2,048 | 896 | 896 | 208 |
| Flip secondFirst | 2,048 | 896 | 896 | 208 |
| Flip firstThird | 2,048 | 896 | 896 | 208 |
| Flip thirdFirst | 2,048 | 896 | 896 | 208 |
| Flip secondThird | 8,192 | 6,272 | 6,272 | 1,552 |
| Flip thirdSecond | 8,192 | 6,272 | 6,272 | 1,552 |

After cross-orientation deduplication there are 192 directed local Splits,
192 inverse Reductions, and 1,552 directed local Flips. The Flip count includes
16 valid local self-relations. Source order, subtraction over F3, all six mode
assignments, and target/source semantic collisions are handled before this
deduplication.

## Edge census

Counts below distinguish directed native relations, ordinary non-strict loops,
and the strict simple graph used for connectivity.

| edge count convention | Split | Reduction | Flip | union |
|---|---:|---:|---:|---:|
| directed contextual relations | 83,712 | 83,712 | 632,488 | 799,912 |
| undirected endpoint pairs | 83,712 for Split/Reduction together | — | 319,912 | 403,624 |
| strict undirected endpoint pairs | 83,712 | — | 312,576 | **396,288** |

The strict Split/Reduction edges have endpoint-cardinality distribution
`1↔2: 192`, `2↔3: 5,568`, `3↔4: 77,952`. The strict Flip edges have
`2↔2: 768`, `3↔3: 21,504`, `4↔4: 290,304`.

There are 7,336 states carrying a witnessed non-strict Flip loop: 16 of
cardinality two, 480 of cardinality three, and 6,840 of cardinality four.
Counting distinct local self-source occurrences rather than endpoint pairs
gives 7,456; a four-atom state can contain two opposite pairs. Loops do not
alter connectivity and are omitted only from the strict adjacency relation.

Every generated contextual edge is checked coordinatewise for equal tensor
evaluation. Every endpoint is checked to be a legal semantic atom set of
cardinality at most four. Directed Flip reverse closure and exact
Split/Reduction reverse closure are also asserted.

## Fibers, components, and endpoint distances

The 81 evaluation fibers have the following complete signatures:

| evaluation rank | number of fibers | vertices by cardinality `0,1,2,3,4` | components | strict edges per nontrivial fiber |
|---|---:|---|---|---:|
| zero | 1 | `1,0,16,64,456` | sizes `1,536` | 5,184 in the nonempty component |
| rank one | 32 | `0,1,6,63,448` | one of size 518 | 5,004 |
| rank two | 48 | `0,0,6,60,441` | one of size 507 | 4,812 |

Thus the graph has 82 components. The JSON records all 81 fibers separately,
not only these rank-aggregated signatures.

There are 5,489 endpoint vertices of cardinality at most three and 183,480
unordered distinct endpoint pairs with equal evaluation. Their complete
connectivity census is:

| result / distance | pair count |
|---|---:|
| separated | **80** |
| connected, distance 1 | 28,032 |
| connected, distance 2 | 107,712 |
| connected, distance 3 | 45,600 |
| connected, distance 4 | 2,056 |
| connected total | **183,400** |

The maximum finite distance is four. One exact path, with a native formula
witness and context recorded for every edge in the JSON, is

```text
00000003 -> 0000002a -> 00000024 -> 00808020 -> 0001c000.
```

The isolated-empty certificate is independent of BFS: every
`NativeReplacement` source is a singleton or a distinct pair, so
`NativeStep.source_subset` makes a step from the empty state impossible. The
census additionally proves that the other 536 zero-evaluation vertices form
one component. The JSON lists every one of the 80 separated endpoint pairs.

## Reproduction and checks

The dedicated artifact consists only of:

- `f3_122_native_connectivity.py`, the finite enumerator and checker;
- `f3_122_native_connectivity.json`, its deterministic result.

Run from the repository root:

```bash
python3 Programs/BilinearComplexity/f3_122_native_connectivity.py \
  --verify Programs/BilinearComplexity/f3_122_native_connectivity.json
```

The program imposes a 180-second alarm and a 4 GiB process address-space
limit. The final full generation run on the campaign host took 9.67 seconds wall time
and 608,392 KiB maximum RSS. There is no randomness.

Final file hashes:

```text
6711cdb05f43d7838c3991febbc9c255ca9c89823a0b7dcc280cc9fba72a0627  Programs/BilinearComplexity/f3_122_native_connectivity.py
3d85884ad62033a5053a7f618e3a98159c6688eb3f0d276676e7a19b53af7067  Programs/BilinearComplexity/f3_122_native_connectivity.json
```

The JSON also publishes hashes for the canonical atom list, vertex list, local
Split and Flip relations, each directed contextual move kind, the complete
undirected graph including loops, state evaluations, component assignment,
and the 80 separated endpoint pairs. These hashes authenticate deterministic
census records; they do not turn the computation into a formal proof.
