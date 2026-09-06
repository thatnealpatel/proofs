# F3 five-to-four closeout archive — 2026-09-06

**Archival experiments, not an approved production proof suite.** This directory
preserves all 38 Scratch files left staged by the bounded F3 closeout of session
`01a074d2-6dfc-7eaa-abbd-e71a43dc1b5b`. The files include checked experiments,
intermediate copies of implementation work, inspection probes, and failed drafts.
Their inclusion in Git is preservation, not a claim that every file compiles.

The approved partial production infrastructure is in
[`Proofs/BilinearComplexity`](../../BilinearComplexity/), committed separately as
`4c99ffbe8d659288be4fcd093cc3f3e3077ad03b`. Production review approval does not
extend to these archived proofs. The archival commit adds no production theorem,
compiler coverage, rank bound, or completion claim.

## Status at closeout

The following distinctions govern interpretation of this archive. Historical
comments, checkpoint notes, apparent theorem declarations, or older success
reports inside the preserved files do not override these qualifications.

| Material | Supported status |
| --- | --- |
| `FieldFiveToFourRegressionContextWIP.lean` | The final pre-move Scratch source checked with `TRUE_EXIT=0` in `first01-partial-final-scratch-01.log`. It includes `first01ResidualAbsent` of length 2, `first01PacketAbsent` of length 3, and present-context/request endpoint infrastructure. It does **not** contain a completed q-present packet. |
| Canonical residual path and trace experiments | `canonical-traces-04.log` records kernel-checked equalities for a two-Split residual path, its three-vertex forward trace, local endpoints, and reversed trace/restoration. These are **symbolic equalities**, not `#eval` runs or a completed full public composition-packet execution suite. |
| `FieldFiveToFourRegressionContextFullDraft.lean` | An unsuccessful broader draft. Apparent q-present packet material is **not checked success**. |
| `ExecCompose*Diagnosis92c366f.lean`, `Scanner*92c366f.lean`, inspection probes, and other implementation drafts | Preserved diagnostics and intermediate work. No individual passing-build claim is made here. Some earlier execution-build reports masked timeouts and were retracted; their presence is not evidence of success. |
| `*.md` and `*.txt` | Historical working notes and source fragments, not authoritative final status or production declarations. |

The checked q-absent packet is Scratch-only. Its complete public packet
state/edge/reversal/restoration regression was **not** completed. The canonical
residual trace checks above must not be confused with that missing full-packet
regression. The production `execCompose` API still consumes a supplied checked
residual path; it is not residual-path synthesis or a full F3 compiler.

**Goal 2 and the combined campaign remain incomplete.** Remaining work includes
the q-present packet, other canonical placements, full execution coverage,
general contextual height/carrier guarantees, residual four-circuit compilation
and coverage, and unrestricted ambient optimality. No obstruction or lower bound
follows from a failed proof, timeout, or the early close. Further F3 expansion was
deferred pending the successor's semantic-comparison gate, not silently waived.

## Byte preservation and paths

Every archived source was moved byte-for-byte from
`Proofs/Scratch/<basename>` to this directory. `SHA256SUMS` lists exactly those
38 basenames and hashes; the README and hash manifest are new archive metadata.
The hashes agree with the predecessor's final repaired-source manifest. Verify
from the repository root with:

```sh
(cd Proofs/Scratch/FieldFiveToFourCloseout20260906 && sha256sum -c SHA256SUMS)
```

No Lean declarations, imports, proof bodies, embedded paths, or historical
comments were repaired during relocation. In particular, `TraceTest.lean` retains
its old `Proofs.Scratch.FieldFiveToFourRegressionContextWIP` import. The original
paths and line references in the external logs refer to the pre-move layout.
Replaying selected experiments may therefore require restoring that layout in
a disposable worktree and checking the appropriate historical dependencies.
The hash check establishes preservation, **not Lean elaboration**.

This is not a self-contained buildable package. `Scratch` is not a default Lake
target, and this archive does not add imports or change Lake configuration.
Do not bulk-build the archive as a production acceptance test, or import its
implementation copies into production. Any future promotion requires a new
scoped proof review and current-source verification.

## Evidence and provenance

The canonical local campaign root is:

`~/x/auto-research/binary-five-circuit/`

The evidence paths below are relative to that root. They are **external local
artifacts**, not files bundled by this archival commit; a repository clone alone
does not contain those logs. This README records their scope rather than claiming
to package a fully reproducible certificate bundle.

- `64-bounded-consolidation-early-close-handoff.md`: final predecessor handoff,
  including the precise public API, incomplete obligations, and early-close
  outcome. Its staged/uncommitted Scratch status describes the predecessor's
  snapshot, before this separately authorized archival relocation and commit.
- `artifacts/field/early-close-2026-09-06/repair-manifest.json` and
  `repaired-sources.sha256`: original-path hashes of all 45 reviewed files,
  including the 38 preserved here and the seven production modules.
- `artifacts/field/early-close-2026-09-06/final-checkpoint.json`: exact predecessor
  commit/index membership and evidence hashes. SHA-256:
  `1a1780ac26ddcdbb54d6e3ab88a702e8a51e3a67322f6aec90423b3930bee1e1`.
- `artifacts/field/early-close-2026-09-06/archival-scratch-staged.patch` and
  `freeze/` in that same directory: pre-move archive preservation.
- `artifacts/field/early-close-2026-09-06/review-*.md`: original production
  reviews and their documentation-only repair reviews. Scratch was assessed
  as archival material, not approved production proof code.
- `artifacts/field/five-to-four-build/first01-partial-final-scratch-01.log`:
  final checked Scratch WIP described above.
- `artifacts/field/five-to-four-build/canonical-traces-04.log`: the separate
  canonical residual trace checks.

The last failed q-present path insertion was reconstructed separately from
immutable transcript event 1849. It is **not substituted into the checked WIP**
in this directory. The external reconstruction is
`artifacts/field/early-close-2026-09-06/FieldFiveToFourRegressionContextWIP-present-paths-failed-01.lean`,
with SHA-256
`ffa4679a74f4d1fbfaeafa3e860bd19f8550d0dc9f41bd44a3a6fccc612985cb`.
Its recovery metadata and failure log remain external.

The predecessor closed at 18:03:21 UTC on 2026-09-06. This archival packaging
neither restarts its proof campaign nor activates `.yah/system_rider_next.tmpl`.
The successor rider and separate Go artifacts are excluded.
