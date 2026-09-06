# Normalized binary contextual certificates

## Trust boundary

The four `NormalizedBinaryContextual{221,411,321,222}.lean` modules contain
literals emitted from an external contextual search. The external program is a
candidate generator only: its search results and census are not assumptions of
the Lean development. For every emitted leaf, Lean independently checks the
native fixed-move replay and endpoint equation. It also checks the compact
present/absent guard, structural full coverage
`ContextualDecisionTree.Valid ∅ ∅`, the compiled dependent path endpoints, and
the constructed path length. The length parameter records the prescribed
length of the generated witness; it makes no shortest-path or distance claim.

The generated one- or two-bit guards belong to the selected decision trees.
They do not assert that every contextual witness is controlled by those bits.

## Reconstruction

The candidate artifacts used for these modules are maintained outside the
repository in
`/home/exedev/x/auto-research/binary-five-circuit/artifacts/contextual/`.
With that directory bound to `CTX`, the successful candidate-generation command is:

```sh
"$CTX/generate.py" > "$CTX/all.json" 2> "$CTX/generate-all.log"
```

The four production modules are emitted independently, so their private local
instance names remain distinct:

```sh
"$CTX/emit_lean.py" "$CTX/all.json" \
  Proofs/BilinearComplexity/NormalizedBinaryContextual221.lean --profiles 221
"$CTX/emit_lean.py" "$CTX/all.json" \
  Proofs/BilinearComplexity/NormalizedBinaryContextual411.lean --profiles 411
"$CTX/emit_lean.py" "$CTX/all.json" \
  Proofs/BilinearComplexity/NormalizedBinaryContextual321.lean --profiles 321
"$CTX/emit_lean.py" "$CTX/all.json" \
  Proofs/BilinearComplexity/NormalizedBinaryContextual222.lean --profiles 222
```

`$CTX/SHA256SUMS` preserves the original manifest for the generator, emitter,
JSON candidates, production sources, and stable build logs. After campaign
consolidation, use `$CTX/SHA256SUMS.relocated` to verify those same hashes at
their new locations. Its entry for this document checks the byte-preserved
pre-relocation version; the present revision changes reconstruction paths only.
The campaign's `migration-map.json` records all original and relocated paths.
The external provenance record distinguishes the isolated successful invocation
from a later archived failed invocation which incorrectly supplied unsupported
`--all --output` arguments.

## Mask-coordinate convention

The generator JSON and the older contextual-evidence bundle identify a factor
mask by the same nonnegative integer. Integer identity must not be confused
with literal identity of displayed coordinate vectors. In the older evidence,
a two-coordinate mask was displayed most-significant-bit first, so mask `1`
appears as `(0,1)`. Lean decodes with `Nat.testBit` in increasing bit-index
order, so the same integer mask `1` is the little-endian vector `![1,0]`.
Applying coordinate reversal separately in each factor relates these two
display conventions.

This observation explains the representation boundary only. The two displayed
vectors are not literally equal, and no unchecked theorem identifying them is
imported into Lean. The preserved old contextual-evidence bundle is left
unchanged; these new generated certificates use integer mask literals whose
meaning is checked by the production Lean definitions.
