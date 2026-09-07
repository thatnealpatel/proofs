# A005245 — Hamilton–Ballinger finiteness

- **Mathematical status:** open conjecture from an OEIS A005245 comment (Gordon Hamilton and Brad Ballinger, 2022-05-23).
- **Work status:** hard-blocked.
- **Remaining target:** prove that only finitely many `n` satisfy `integerComplexity n < powerComplexity n`, where the second complexity uses addition and exponentiation rather than addition and multiplication.
- **Proved prerequisites:** `Proofs/NumberComplexity/HamiltonBallinger.lean` defines both measures and proves their intended optimization characterizations.
- **Next obligation:** establish a comparative eventual bound strong enough to imply `Set.Finite {n | integerComplexity n < powerComplexity n}`; no such growth argument is presently formalized.
- **Correction:** the older claim `c(p)=c(p-1)+1` for every prime is refuted (least counterexample `353942783`) and is not this target.
