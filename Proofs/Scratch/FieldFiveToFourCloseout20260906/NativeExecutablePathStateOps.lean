import BilinearComplexity.FieldNativeExecutablePath

set_option autoImplicit false

namespace BilinearComplexity.FieldNativeExecutablePath.Execution

#eval
  let all := ComputedState.union sourceState targetState
  let withoutSource := ComputedState.difference all sourceState
  ((decide (sourceAtom ∈ all), decide (leftAtom ∈ all), decide (rightAtom ∈ all)),
   (decide (sourceAtom ∈ withoutSource), decide (leftAtom ∈ withoutSource),
    decide (rightAtom ∈ withoutSource)))

end BilinearComplexity.FieldNativeExecutablePath.Execution
