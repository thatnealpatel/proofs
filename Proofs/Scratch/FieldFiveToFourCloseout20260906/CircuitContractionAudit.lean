import BilinearComplexity.FieldCircuitContraction

set_option autoImplicit false

open BilinearComplexity
open BilinearComplexity.FieldCircuitContraction

#check @ContractionData
#check @ContractionData.residual_relation
#check @ContractionData.q_ne_zero
#check @ContractionData.q_not_proportional
#check @ContractionData.q_ne_original
#check @ContractionData.residual_everyDeletionIndependent
#check @ContractionData.residual_isMinimalFourCircuit
#check @ContractionData.signedMinimalFour
#check @ContractionData.result
#check @minimalFive_vanishingRelation
#check @minimalFive_properSubfamily
#check @SignedMinimalFour.pair_linearIndependent

#print axioms ContractionData.residual_relation
#print axioms ContractionData.q_ne_zero
#print axioms ContractionData.q_not_proportional
#print axioms ContractionData.residual_isMinimalFourCircuit
#print axioms ContractionData.signedMinimalFour
#print axioms ContractionData.result
#print axioms minimalFive_vanishingRelation
#print axioms minimalFive_properSubfamily
