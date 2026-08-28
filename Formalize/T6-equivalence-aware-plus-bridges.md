# T6 — equivalence-aware Plus bridges between c659 and c680

**Status.** Exact certificate and formalization card. The first deliverable is a
finite proof-producing comparison over `F_2`; Lean should replay the definitions
and positive witnesses or the final finite partition, not implement the search
policy.

**Goal.** Decide whether one exact Plus move from the authenticated c659 and
c680 rank-47 schemes can reach equivalent rank-48 presentations, and whether a
Plus child of c680 has a non-generating inverse-Plus exit to a rank-47
presentation equivalent to c659.

A positive result is a certified `47 -> 48 -> 47` bridge between the two root
classes. It is not a shortening and does not prove anything about minimal tensor
rank.

## Authenticated roots

Use exactly these binary `<4,4,4>` presentations:

- c659: `4x4x4_m47_c659_iteration5551_Z2.txt`, raw SHA-256
  `25f47b5f37d2b7351dd5a2c5da65ff8ef5ba80ce53239d46cdfdef37e6eef403`;
- c680: `4x4x4_m47_c680_iteration4356_Z2.txt`, raw SHA-256
  `7e65a2fa888fcd9f32d9d68fd21ab8cdafeb4a39300cc77882def8e0115483e8`.

Both roots must be authenticated before any comparison. Every generated child
and reconstructed parent must independently satisfy all Brent equations and the
nonzero/distinct-term conditions declared by the certificate.

## Established boundary

Commit `8ea0c37` and `cmd/c659-c680-cc1-cert` completely regenerate the frozen
variant-0 one-Plus frontiers:

- 12,972 ordered descriptors per root;
- six orientations for every ordered pair of distinct source slots;
- 6,486 exact term-permutation-canonical children per root;
- two forward aliases per canonical child;
- zero common 296-byte canonical child payloads.

This proves that the two frontiers have no literally equal child after removing
term order. It does **not** compare children under sandwich transformations,
outer orientations, or scalar gauges, and it says nothing about longer paths.

The fixed-child and all-child inverse-Plus certificates for c659 establish
inverse rigidity only on the declared c659 children. They do not classify the
c680 frontier.

## Standard equivalence over `F_2`

Two ordered rank-48 presentations are standard-equivalent when one can be
carried to the other by:

1. a permutation of the 48 terms;
2. invertible `4 x 4` sandwich matrices `P`, `Q`, and `R` acting as
   `(U,V,W) -> (PUQ^-1, QVR^-1, RWP^-1)`;
3. one of the six factor-permutation/transposition outer orientations.

Termwise gauges should remain explicit in the general definition. Over `F_2`
they are trivial because the only nonzero scalar is one. Equivalence after
extension to a larger field is a separate problem and is not part of the first
certificate.

## Part A: equivalence-aware common Plus child

Determine whether any child in the complete c659 variant-0 frontier is
standard-equivalent over `F_2` to any child in the complete c680 variant-0
frontier.

Use exact invariants to reject pairs before solving, for example:

- per-term factor-rank colors;
- factor matroids and circuit data;
- pair and pencil ranks;
- complementary Khatri--Rao ranks;
- cyclic-product similarity invariants;
- incidence data preserved by the declared action.

An invariant mismatch is a valid rejection certificate. Matching invariants are
only candidates and never prove equivalence.

A positive witness must contain:

- both authenticated root descriptors;
- both Plus descriptors and exact rank-48 children;
- the outer orientation;
- `P`, `Q`, `R` and their verified inverses;
- the complete 48-term permutation;
- all factor equations after orientation and sandwiching;
- exact replay showing both children still represent the matrix-multiplication
  tensor.

A negative result must provide a finite partition of all candidate pairs and an
independent checker showing that every pair is either rejected by a verified
invariant mismatch or decided negatively by a complete equivalence solver.
Timeouts, branch limits, and unresolved solver cases must remain explicitly
unresolved and cannot support a negative theorem.

## Part B: inverse-Plus exit from the c680 frontier

For a 48-term child `R`, a leg order `(i,j,k)`, and distinct slots `(x,y,z)`, an
inverse-Plus tripod has the factor relations

`f_i(x) = f_i(z)`,

`f_j(y) = f_j(z)`,

`f_k(x) + f_k(y) + f_k(z) = 0`,

with the two nonalias conditions

`f_i(y) != f_i(z)` and `f_j(x) != f_j(z)`.

In leg order `(i,j,k)`, reconstruct the two parent terms

`P = f_i(z) * (f_j(x) + f_j(z)) * f_k(x)`,

`Q = (f_i(y) + f_i(z)) * f_j(z) * f_k(y)`.

The notation `*` here denotes the rank-one tensor product of the three displayed
factors. The implementation must verify directly that

`r_x + r_y + r_z = P + Q`

and then replay the complete 47-term parent.

For every canonical c680 variant-0 child, exhaust all typed tripod incidences,
all six leg orders, and every inverse-Plus formula variant admitted by the
constructor. Retain the complete forward lineage so that the generating parent
is recognized rather than reported as a discovery.

For every exact non-generating parent:

1. require 47 nonzero, pairwise-distinct terms;
2. replay every Brent equation;
3. compare inexpensive exact invariants with c659;
4. invoke the complete standard-equivalence solver only when those invariants
   do not reject the parent;
5. retain a full equivalence witness for every positive result.

The strongest intended positive result is a c680 Plus child with a second
inverse-Plus tripod whose parent is standard-equivalent to c659. Record the
intersection size of the generating and alternate tripod supports; overlap in
exactly one slot is a useful structured subcase, not part of the basic bridge
definition.

## Formalization targets

### 1. Plus and inverse-Plus identities

Reuse the exact Plus and inverse-Plus constructors already represented by
`internal/tensor` and the corresponding Lean tensor algebra. Prove that the
tripod equations imply the local identity above, with orientation and formula
variant explicit.

### 2. Standard-equivalence relation

Package term permutation, sandwiching, and all six outer orientations as one
relation on valid schemes. Prove reflexivity, symmetry, and transitivity, and
prove that the relation preserves the represented tensor and presentation
length.

Keep equality of ordered schemes, equality up to term permutation, and full
standard equivalence as distinct predicates.

### 3. Witness replay

Define a small witness format whose checker verifies every matrix inverse,
factor equation, orientation, term permutation, and source/target hash. The
checker must establish equivalence from the witness without trusting the search
that found it.

### 4. Finite negative interface

If the computation finds no bridge, import only a manifest that partitions the
complete declared domain. Lean need not reproduce the expensive search, but it
must be able to check the exact rejection certificates used by the final
partition. Any unclassified case prevents a complete negative theorem.

## Outcomes

Report exactly one of:

- `bridge`: an independently replayable equivalence witness exists;
- `complete_no_bridge`: every case in the frozen finite domain has a checked
  negative certificate;
- `incomplete`: at least one case remains unresolved.

The word `complete` is reserved for the frozen variant-0 forward domain and the
explicit inverse-tripod domain above. It must not be read as closure of the
rank-48 flip graph or of all Plus variants and paths.

## Acceptance criteria

- Both roots and every external corpus are authenticated before parsing.
- The forward domain exactly matches the committed 12,972-descriptor-per-root
  variant-0 contract.
- Complete canonical bytes, not hashes alone, decide literal equality.
- Every positive equivalence claim has a full independently replayable witness.
- Every complete negative has a checked partition with no omitted or unresolved
  cases.
- The c659 all-child inverse result is not silently reused as a c680 result.
- `47 -> 48 -> 47` is described as a same-length bridge, not a rank reduction.
- No result is promoted to tensor-rank minimality, a moat theorem, or global
  move-graph connectivity.

## Non-goals

Do not enumerate the full rank-48 ordinary-flip component. Do not include Plus
variants 1 or 2 in the forward frontier unless a new card freezes and certifies
that larger domain. Do not claim equivalence over scalar extensions from an
`F_2` computation. Do not treat invariant agreement as an equivalence witness.
