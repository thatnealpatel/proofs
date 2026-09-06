import BilinearComplexity.FieldFiveToFourRegression
set_option autoImplicit false
namespace BilinearComplexity.FieldFiveToFourRegression
#eval (bridgeFirst01.normalized.leftIndex.val, bridgeFirst01.normalized.rightIndex.val,
  (List.ofFn bridgeFirst01.normalized.residualReindex).map Fin.val,
  bridgeFirst01.qSignedIndex.val)
#eval (bridgeFirst23.normalized.leftIndex.val, bridgeFirst23.normalized.rightIndex.val,
  (List.ofFn bridgeFirst23.normalized.residualReindex).map Fin.val,
  bridgeFirst23.qSignedIndex.val)
#eval (bridgeFirst02.normalized.leftIndex.val, bridgeFirst02.normalized.rightIndex.val,
  (List.ofFn bridgeFirst02.normalized.residualReindex).map Fin.val,
  bridgeFirst02.qSignedIndex.val)
#eval (bridgeFirst12.normalized.leftIndex.val, bridgeFirst12.normalized.rightIndex.val,
  (List.ofFn bridgeFirst12.normalized.residualReindex).map Fin.val,
  bridgeFirst12.qSignedIndex.val)
end BilinearComplexity.FieldFiveToFourRegression
