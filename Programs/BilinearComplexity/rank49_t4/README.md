# Rank-49 T4 acceptance bundle

This directory contains the deterministic acceptance material for the repaired
T4 computational tranche. The research synthesis is
[`Documents/rank49-deformation-t4.md`](../../../Documents/rank49-deformation-t4.md).
The tranche is intentionally scoped: it does not claim that every deliverable
in the original T4 card is scheme-theoretically complete.

## Critical correction

The outer action on the scalar witness torus `C_x ≅ G_m^3` is not merely a
permutation action. Rotations permute `(p,q,r)`, while reflections permute and
invert the coordinates. Therefore diagonal `G_m` is not central under all six
orientations; the all-outer fixed subgroup scheme is diagonal `mu_2`. Equality
of the stabilizer scheme with `C_x` and representability of
`Stab_wit,x / C_x` remain unproved.

## Contents

All numerical lanes open the authenticated vendored fixture
`fixtures/4x4x4_m49_c680_iteration65_Z2.txt`, not its historical external
locator. The four acceptance lanes are:

| lane | checker | artifact(s) |
|---|---|---|
| exhaustive support-five census | `support5_census.py` | `artifacts/support5_census.json`, `artifacts/support5_orbits-99ea851b7dec758b3e302f306f93220969df7ef26073cfc4afa384d60c71bf7b.jsonl.gz` |
| fixed-point stabilizer | `stabilizer.py` (invokes `stabilizer_replay.py`) | `artifacts/stabilizer.json` |
| generic germ and binary quadratic map | `generic_germ.py` | `artifacts/generic_germ.json` |
| parameter correspondence | `parameter_orbits.sage` | `artifacts/parameter_orbits.json` |

`manifest.json` records every fixture, script, artifact, integration file, and
report/provenance input by repository-relative path, byte count, and SHA-256.
It also records the generation base revision and current-HEAD ancestry policy,
final schemas, exact checker argv, absence of randomness, resource limits, and
expected completion. The parameter lane's
`t3_lean_provenance` path and digest are explicitly cross-bound to inventory ID
`paired_circuit_lean` (`Proofs/BilinearComplexity/PairedCircuit.lean`).

## Authentication modes

The checker derives the repository root from its own resolved location, so it
may be invoked from any current directory and no particular checkout path is
required:

```bash
python3 Programs/BilinearComplexity/rank49_t4/check_all.py --quick
```

Quick mode does **not** recompute artifacts. Under a trusted-local-files model,
it verifies canonical manifest encoding and its self-contained payload digest,
that the recorded generation base exists and is an ancestor of current `HEAD`,
and all listed file sizes and SHA-256 values. Later unrelated commits are
allowed because every delivered bundle file remains content-authenticated. It
also verifies the vendored
fixture, final artifact schemas, the digest-named support stream path and
metadata, script/fixture/base-policy cross-references, the parameter-to-Lean
path-and-digest binding, and available payload certificates. It does not
decompress or semantically replay the 1.585 GB support stream. The manifest
digest is an integrity/cross-consistency check, not a digital signature or
external trust anchor.

For complete deterministic replay:

```bash
python3 Programs/BilinearComplexity/rank49_t4/check_all.py --full
```

Full mode performs quick authentication first and then executes the four exact
commands fixed jointly by `check_all.py` and the manifest. It never invokes a
generation mode. Every checker process and descendant inherits a hard
per-process address-space limit. The wrapper also samples aggregate RSS for the
same process group, keeps monitoring until that group is empty, and terminates
the group at the wall deadline or an observed aggregate excess. This is an
enforced boundary for the trusted lane programs, but not a cgroup/security
boundary against hostile code that deliberately creates a new session. The
stabilizer checker itself invokes its independent replayer. Full replay is
dominated by the exhaustive 1,906,884-support census and validation of the
1.585 GB uncompressed singleton stream.

Each lane receives one first-class status:

* `PASS`: checker exited zero within both limits;
* `TIMEOUT`: the enforced wall limit expired;
* `RESOURCE_EXCEEDED`: sampled aggregate group RSS exceeded the allowance, or
  checker output/termination supplied recognized resource-limit evidence;
* `FAIL`: authentication, launch, checker, or other non-resource failure.

A non-`PASS` lane makes full mode exit nonzero, but the wrapper continues to run
and report the remaining lanes. Complete checker stdout and stderr are
preserved.

## Determinism and publication

Artifact generation is deterministic for the authenticated fixture, code,
generation base revision, its required ancestor policy, and declared default
limits. Elapsed time and other run measurements are emitted only on stdout and
are not authenticated artifact content. Each
JSON producer writes a same-directory temporary file, flushes and fsyncs it,
atomically replaces the destination, and fsyncs the parent directory. The
support stream is deterministic gzip (level 9, empty header filename,
`mtime=0`): its temporary is fsynced, made read-only, and published without
overwrite by hard link at `support5_orbits-<sha256>.jsonl.gz`; an existing target
is reused only after its size and digest match.

Publication of the stream and census JSON is ordered but is not a two-file
transaction. Interruption may leave an unreferenced content-addressed stream,
but cannot make the previously published census refer to a partial stream; a
new census is published only after its referenced stream is durable.

## Scope of accepted results

The bundle authenticates, among other detailed certificates:

* all `binom(49,5)=1,906,884` supports, with exactly 63 rank-229,
  one-dimensional normal `P^0` cases, exactly the paired-T3 supports;
* separate same-support and full-coordinate quadratic preimages and exact
  normal-class families for all 63 directions, including 39 stored gauge
  corrections;
* generic Jacobian rank 2155, kernel dimension 197, connected-action rank 143,
  sweep rank 144, exact degree bounds, and complete binary quadratic-cokernel
  vanishing;
* a diagonal field-valued parameter relation over every extension of `F2`,
  all-`G_m` fiberwise `Scheme.Valid`-equivalent certificates, and family orbit
  counts `F2:1`, `F4:3`;
* a trivial direct effective stabilizer field-point image, with one `F2` and 27
  `F4` scalar-torus witnesses.

It does not establish component dimension, a geometric/formal normal slice,
miniversal obstruction theory, all-order lifting, larger-support or global
rigidity, a scheme-theoretic parameter diagonal, quotient-group-scheme points,
behavior at `b=0` or `b=infinity`, a rank reduction, or minimal tensor rank 49.
