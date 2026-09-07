# Exact matrix-multiplication border-rank residual

- **Source:** arXiv:1112.6007, Landsberg–Ottaviani.
- **Mathematical status:** published exact border-rank lower bound for rectangular matrix multiplication, not fully formalized.
- **Work status:** hard-blocked.
- **Remaining target:** formalize the exact theorem and corollary, with their rectangular dimensions, flattening/submatrix hypotheses, and border-rank conclusion. The generic flattening vanishing API in `Proofs/AlgComplexity/Vp2/BorderRank.lean` is only an ingredient.
- **Next obligation:** connect the matrix-multiplication tensor to the source's chosen flattening and prove the dimension-indexed determinant/rank estimate without weakening the statement to a generic necessary condition.
