# Cohn–Kleinberg–Szegedy–Umans STPP and wreath residual

- **Mathematical status:** published asymptotic inequalities, only partially formalized.
- **Work status:** hard-blocked.
- **Remaining target:** prove the central CKSU simultaneous-TPP capacity inequality and its wreath-product specialization, then obtain the commutative specialization without relying on `sorry`.
- **Current boundary:** `Proofs/GroupTPP/STPPWreath.lean` contains substantial sorry-free definitions, direct-product closure, wreath embeddings, character-degree bounds, and asymptotic witness families, but `stpp_capacity_le` and `stpp_capacity_le_of_wreath` deliberately use `sorry`; `stpp_capacity_le_comm` factors through those obligations. Therefore the surrounding STPP/wreath/asymptotic story is not complete.
- **Sources consolidated:** arXiv:math/0511460, only the central simultaneous-TPP capacity and wreath-specialization portions. The chart-USP/`ω<2.41` portion is a separate residual in `GroupTPP-Barriers-Lie-ChartUSP.md`; no unrelated source results are claimed here.
- **Next obligation:** formalize the tensor-rank/Schönhage asymptotic sum inequality needed by `stpp_capacity_le`, then discharge the multinomial/wreath asymptotics in `stpp_capacity_le_of_wreath` and audit all downstream theorems for `sorryAx`.
- **Claim boundary:** proved constructions or a convergence statement downstream of the skeleton do not establish the central inequalities independently.
