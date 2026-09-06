import BilinearComplexity.FieldFiveToFourRegression
import BilinearComplexity.FieldFiveToFourContext
import BilinearComplexity.FieldThreeProductCircuit

set_option autoImplicit false

namespace BilinearComplexity
namespace TestResidualMath
open FieldCircuitContraction

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- A one/three signed residual has its first term equal to the other three. -/
theorem oneThree_relation (S : SignedMinimalFour k V) (hshape : S.shape = .oneThree) :
    S.term 1 + (S.term 2 + S.term 3) = S.term 0 := by
  have h := S.signed_relation
  rw [hshape] at h
  norm_num [IsLinearRelation, signedFourCoefficients, Fin.sum_univ_succ] at h
  rw [eq_neg_of_add_eq_zero_left h]
  abel

/-- Distinct signed residual indices carry distinct terms. -/
theorem term_ne_term (S : SignedMinimalFour k V) {i j : Fin 4} (hij : i ≠ j) :
    S.term i ≠ S.term j := S.injective.ne hij

#check @oneThree_relation
#print axioms oneThree_relation

end TestResidualMath
end BilinearComplexity
