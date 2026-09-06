# FieldFiveToFourContext second-tranche checkpoint

## Production status
- Created and promoted `Proofs/BilinearComplexity/FieldFiveToFourContext.lean`.
- `context-production-01.log`: original six-branch contextual composition builds, warnings only.
- Refactored composition through private `composeWithLength`; public `compose` name/signature unchanged.
- Added endpoint transport helpers, height weakening helper, and public `length_compose`.
- `context-production-03.log`: current production file builds, warnings only.
- Parent/integrator was notified immediately of promoted import/API.

## Upstream canonical residual API
Production `FieldFiveToFour.lean` now provides `CertifiedFiveToFour.signedResidual`, `signedResidualAtom`, `qSignedIndex`, `signedResidualSource`, `signedResidualTarget`, etc. `residualShape` correctly maps opposite to `.twoTwo`.

## New maintainer requirement
The existing context/schedule/request/compose are explicitly noncomputable proof-side infrastructure and must not be presented as an effective splice. Need add ordinary computable F3 state operations and computable schedule/request/path operations, with proved correspondence to existing semantic definitions. Runtime API must return actual `StrictNativePath` plus computed states, not labels/counts. Need public executions for q present/absent and all placements.

## Next actions
1. Prove current `residualSource` and `residualTarget` equal canonical `B.signedResidualSource/Target`, by cases on `B.normalized` and finite indices.
2. Add public reverse length and height max(H,C.card+3); endpoint-card bounds and residual-context disjointness.
3. Define computable F3 `effectiveStateUnion`, `effectiveStateDifference`, singleton/pair/triple and correspondence theorems. Define computable outer endpoints, schedule, requests and actual path append/snoc/reverse.
4. Construct computable outer strict-step functions and six-branch `effectiveCompose`, avoiding every noncomputable helper in executable data. Prove correspondence and test all six placement/occupancy branches.
5. Locked build and message parent exact actual effective API.

## Third-tranche executable status (externalized before recharge)
- `FieldNativeExecutablePath.lean` is now imported. Added namespace `CertifiedFiveToFour.Executable` with genuinely computed F3 definitions: `sourceState`, `targetState`, `outerSource`, `outerTarget`, `fullStart`, `fullFinish`, `schedule`, `requestStart`, `requestFinish`, and `displayedCarrier`; all have proof-side specification theorems and these portions elaborated in `context-exec-04.log`.
- Added ordinary executable `castPath` and computed-state `outerStep`; `outerStep` stores computed local endpoints and computed difference/union output rather than proof-side noncomputable states.
- Drafted `outerStepTo` by constructing the reverse-direction computed step and applying `FieldNativeExecutablePath.reverseStep`; the only immediate error there is line 722 calling nonexistent `native.reverse`. Exact fix: use theorem `NativeReplacement.symm` (`exact native.symm`), confirmed at `FieldNativeMoves.lean:305`.
- Drafted public `execCompose : ... -> FieldNativeExecutablePath.Packet F3 a b c`. It branches on computed schedule, constructs actual computed outer edge, casts only indices of supplied computed residual path, and uses executable `snoc`. Its requested residual path indices are computed `Executable.requestStart/requestFinish`, and packet endpoints are computed `fullStart/fullFinish`.
- Four schedule implication helpers now elaborate after explicit placement cases. Remaining `execCompose` elaboration in `context-exec-04.log` times out at lines 813/821/827 (proof transport from computed states to old freshness/subset helpers); no logical goal was reported, just 200k heartbeat timeouts. Exact next action after `.symm`: wrap `execCompose` in `set_option maxHeartbeats 1000000 in` and rebuild. If still slow, replace `rw` chains for `hsource`/`hfresh` with separately proved small transport lemmas so each caches elaboration.
- Production currently does NOT build because of the above one invalid field and three timeouts; last fully building source predates executable additions (`context-production-03.log`). Do not present `execCompose` as completed until a locked build succeeds.
- Canonical residual equality scratch remains unsolved and is secondary to closing executable build. Height card lemmas were attempted but removed after expensive `Finset` instance elaboration.
- Existing constraints remain satisfied: no sorry/axioms/native_decide/noncomputable executable definitions; only owned production/scratch files edited.
