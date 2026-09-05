import BilinearComplexity.BinaryAmbientNormalization
import BilinearComplexity.BinaryAmbientFiveCircuitSharpness
import BilinearComplexity.NormalizedBinaryOrbitClassification

set_option autoImplicit false

/-!
# Coordinate models of ambient binary circuits

This module separates coordinate tensor arrays from genuine nested tensor
products while proving that they detect the same finite-state relations and
circuits.  It also constructs a choice-free identity presentation of every
exact normalized relation and packages the selected profile-411 relation as an
abstract tensor-product circuit together with its independently certified
intrinsic move sharpness.
-/

namespace BilinearComplexity.BinaryAmbientCircuitModels

open scoped TensorProduct BigOperators
open BinaryCircuit
open NormalizedBinaryCarrier
open NormalizedBinaryFiveCircuitCertificate
open NormalizedBinaryRelationEnumeration
open BinaryAmbientNormalization

/-- The executable identity coordinate frame in dimension `d`. -/
def coordinateIdentity (d : ℕ) :
    BinaryAmbientTensorCoordinates.Coord d ≃ₗ[F2]
      BinaryAmbientTensorCoordinates.Coord d :=
  LinearEquiv.refl F2 _

example : coordinateIdentity 0 (0 : CoordinateVector 0) = 0 := rfl

private theorem normalizeTerm_coordinateIdentity {a b c : ℕ}
    (t : Carrier (BinaryAmbientTensorCoordinates.coordinateProfile a b c)) :
    BinaryAmbientTensorCoordinates.normalizeTerm
      (coordinateIdentity a) (coordinateIdentity b)
      (coordinateIdentity c) t = t := by
  rfl

private theorem tensorCoordinateEquiv_coordinate_tensorEvaluation
    {a b c : ℕ}
    (t : Carrier (BinaryAmbientTensorCoordinates.coordinateProfile a b c)) :
    BinaryAmbientTensorCoordinates.tensorCoordinateEquiv
        (BinaryAmbientTensorCoordinates.basisOfCoordinates
          (coordinateIdentity a))
        (BinaryAmbientTensorCoordinates.basisOfCoordinates
          (coordinateIdentity b))
        (BinaryAmbientTensorCoordinates.basisOfCoordinates
          (coordinateIdentity c))
        (BinaryAmbientCarrier.tensorEvaluation t) = tensorEvaluation t := by
  unfold BinaryAmbientTensorCoordinates.coordinateProfile at t ⊢
  rw [BinaryAmbientTensorCoordinates.tensorCoordinateEquiv_tensorEvaluation]
  rfl

private theorem circuit_iff_of_injective_covariance
    {α V W : Type*} [DecidableEq α]
    [AddCommGroup V] [Module F2 V] [AddCommGroup W] [Module F2 W]
    (valueV : α → V) (valueW : α → W) (f : V →+ W)
    (hf : Function.Injective f) (hvalue : ∀ x, f (valueV x) = valueW x)
    (C : BinaryCircuit.Scheme α) : Circuit valueV C ↔ Circuit valueW C := by
  have hevaluation (D : BinaryCircuit.Scheme α) :
      f (evaluation valueV D) = evaluation valueW D := by
    simp only [evaluation, map_sum, hvalue]
  have hcycle (D : BinaryCircuit.Scheme α) : BinaryCycle valueV D ↔ BinaryCycle valueW D := by
    constructor
    · intro h
      unfold BinaryCycle at h ⊢
      rw [← hevaluation, h, map_zero]
    · intro h
      unfold BinaryCycle at h ⊢
      apply hf
      rw [hevaluation, h, map_zero]
  unfold Circuit
  constructor
  · rintro ⟨hC, hnonempty, hminimal⟩
    refine ⟨(hcycle C).mp hC, hnonempty, ?_⟩
    intro Z hZ hZnonempty
    simpa only [hcycle Z] using hminimal Z hZ hZnonempty
  · rintro ⟨hC, hnonempty, hminimal⟩
    refine ⟨(hcycle C).mpr hC, hnonempty, ?_⟩
    intro Z hZ hZnonempty
    simpa only [hcycle Z] using hminimal Z hZ hZnonempty

/-- Identity-frame normalization fixes every finite coordinate state. -/
@[simp] theorem normalizeState_coordinateIdentity {a b c : ℕ}
    (D : State (BinaryAmbientTensorCoordinates.coordinateProfile a b c)) :
    BinaryAmbientTensorCoordinates.normalizeState
      (coordinateIdentity a) (coordinateIdentity b)
      (coordinateIdentity c) D = D := by
  unfold BinaryAmbientTensorCoordinates.normalizeState
  have hEmbedding :
      (BinaryAmbientTensorCoordinates.carrierEquiv
        (coordinateIdentity a) (coordinateIdentity b)
        (coordinateIdentity c)).symm.toEmbedding =
      Function.Embedding.refl _ := by
    exact Function.Embedding.ext fun t =>
      normalizeTerm_coordinateIdentity t
  rw [hEmbedding]
  exact Finset.map_refl

private theorem coordinate_stateEvaluation_eq_iff_ambientStateEvaluation_aux
    {a b c : ℕ}
    (D E : State (BinaryAmbientTensorCoordinates.coordinateProfile a b c)) :
    stateEvaluation D = stateEvaluation E ↔
      BinaryAmbientCarrier.stateEvaluation D =
        BinaryAmbientCarrier.stateEvaluation E := by
  unfold BinaryAmbientTensorCoordinates.coordinateProfile at D E ⊢
  rw [← BinaryAmbientTensorCoordinates.normalized_stateEvaluation_eq_iff
    (coordinateIdentity a) (coordinateIdentity b)
    (coordinateIdentity c)]
  have hD := normalizeState_coordinateIdentity (a := a) (b := b) (c := c) D
  have hE := normalizeState_coordinateIdentity (a := a) (b := b) (c := c) E
  unfold BinaryAmbientTensorCoordinates.coordinateProfile at hD hE
  rw [hD, hE]
  rfl

/-- Equality of finite-state coordinate tensor arrays is equivalent to equality
of their evaluations in the genuine nested tensor product. -/
theorem coordinate_stateEvaluation_eq_iff_ambientStateEvaluation
    {p : Profile} (D E : State p) :
    stateEvaluation D = stateEvaluation E ↔
      BinaryAmbientCarrier.stateEvaluation D =
        BinaryAmbientCarrier.stateEvaluation E := by
  rcases p with ⟨a, b, c⟩
  exact coordinate_stateEvaluation_eq_iff_ambientStateEvaluation_aux D E

/-- On the coordinate carrier of every profile, circuit minimality computed
in coordinate arrays is equivalent to circuit minimality in the genuine
nested tensor product of the three coordinate spaces. -/
theorem coordinateCircuit_iff_ambientCircuit (p : Profile) (C : State p) :
    Circuit (@tensorEvaluation p) C ↔
      Circuit (@BinaryAmbientCarrier.tensorEvaluation
        (CoordinateVector p.first) (CoordinateVector p.second)
        (CoordinateVector p.third) _ _ _ _ _ _) C := by
  rcases p with ⟨a, b, c⟩
  refine (circuit_iff_of_injective_covariance
    (@BinaryAmbientCarrier.tensorEvaluation
      (CoordinateVector a) (CoordinateVector b)
      (CoordinateVector c) _ _ _ _ _ _)
    (@tensorEvaluation (BinaryAmbientTensorCoordinates.coordinateProfile a b c))
    (BinaryAmbientTensorCoordinates.tensorCoordinateEquiv
      (BinaryAmbientTensorCoordinates.basisOfCoordinates
        (coordinateIdentity a))
      (BinaryAmbientTensorCoordinates.basisOfCoordinates
        (coordinateIdentity b))
      (BinaryAmbientTensorCoordinates.basisOfCoordinates
        (coordinateIdentity c))).toAddMonoidHom
    ?_ ?_ C).symm
  · exact (BinaryAmbientTensorCoordinates.tensorCoordinateEquiv
      (BinaryAmbientTensorCoordinates.basisOfCoordinates
        (coordinateIdentity a))
      (BinaryAmbientTensorCoordinates.basisOfCoordinates
        (coordinateIdentity b))
      (BinaryAmbientTensorCoordinates.basisOfCoordinates
        (coordinateIdentity c))).injective
  · exact tensorCoordinateEquiv_coordinate_tensorEvaluation

/-- For coordinate states, the ambient first-factor span is exactly the
normalized first-factor span. -/
theorem coordinate_firstSpan_eq_firstFactorSpan {p : Profile} (D : State p) :
    BinaryAmbientCarrier.firstSpan D = firstFactorSpan D := by
  unfold BinaryAmbientCarrier.firstSpan firstFactorSpan
  congr 2
  ext x
  simp

/-- For coordinate states, the ambient second-factor span is exactly the
normalized second-factor span. -/
theorem coordinate_secondSpan_eq_secondFactorSpan {p : Profile} (D : State p) :
    BinaryAmbientCarrier.secondSpan D = secondFactorSpan D := by
  unfold BinaryAmbientCarrier.secondSpan secondFactorSpan
  congr 2
  ext x
  simp

/-- For coordinate states, the ambient third-factor span is exactly the
normalized third-factor span. -/
theorem coordinate_thirdSpan_eq_thirdFactorSpan {p : Profile} (D : State p) :
    BinaryAmbientCarrier.thirdSpan D = thirdFactorSpan D := by
  unfold BinaryAmbientCarrier.thirdSpan thirdFactorSpan
  congr 2
  ext x
  simp

private def coordinatesToTopSpan {d : ℕ} (P : Submodule F2 (CoordinateVector d))
    (hP : P = ⊤) : CoordinateVector d ≃ₗ[F2] P :=
  ((LinearEquiv.ofEq P ⊤ hP).trans Submodule.topEquiv).symm

/-- The ambient first-factor span of the endpoints of an exact coordinate
relation is the entire coordinate factor space. -/
theorem ExactRelation.coordinate_firstSpan_eq_top {p : Profile}
    (target : ExactRelation p) :
    BinaryAmbientCarrier.firstSpan (target.1.left ∪ target.1.right) = ⊤ := by
  rw [coordinate_firstSpan_eq_firstFactorSpan]
  exact target.2.2.2.2.2.1

/-- The ambient second-factor span of the endpoints of an exact coordinate
relation is the entire coordinate factor space. -/
theorem ExactRelation.coordinate_secondSpan_eq_top {p : Profile}
    (target : ExactRelation p) :
    BinaryAmbientCarrier.secondSpan (target.1.left ∪ target.1.right) = ⊤ := by
  rw [coordinate_secondSpan_eq_secondFactorSpan]
  exact target.2.2.2.2.2.2.1

/-- The ambient third-factor span of the endpoints of an exact coordinate
relation is the entire coordinate factor space. -/
theorem ExactRelation.coordinate_thirdSpan_eq_top {p : Profile}
    (target : ExactRelation p) :
    BinaryAmbientCarrier.thirdSpan (target.1.left ∪ target.1.right) = ⊤ := by
  rw [coordinate_thirdSpan_eq_thirdFactorSpan]
  exact target.2.2.2.2.2.2.2

/-- Every exact normalized relation has an executable exact-span presentation
in its own coordinate spaces.  Each coordinate map is the identity followed
by attachment to the full exact span; no basis is selected. -/
def coordinateExactSpanPresentation {p : Profile} (target : ExactRelation p) :
    ExactSpanPresentation target.1.left target.1.right where
  profile := p
  firstCoordinates := coordinatesToTopSpan _
    (ExactRelation.coordinate_firstSpan_eq_top target)
  secondCoordinates := coordinatesToTopSpan _
    (ExactRelation.coordinate_secondSpan_eq_top target)
  thirdCoordinates := coordinatesToTopSpan _
    (ExactRelation.coordinate_thirdSpan_eq_top target)

/-- The first coordinate map in the identity exact-span presentation preserves
the underlying coordinate vector. -/
@[simp] theorem coordinateExactSpanPresentation_firstCoordinates_val
    {p : Profile} (target : ExactRelation p) (x : CoordinateVector p.first) :
    ((coordinateExactSpanPresentation target).firstCoordinates x).1 = x := by
  rfl

/-- The second coordinate map in the identity exact-span presentation preserves
the underlying coordinate vector. -/
@[simp] theorem coordinateExactSpanPresentation_secondCoordinates_val
    {p : Profile} (target : ExactRelation p) (x : CoordinateVector p.second) :
    ((coordinateExactSpanPresentation target).secondCoordinates x).1 = x := by
  rfl

/-- The third coordinate map in the identity exact-span presentation preserves
the underlying coordinate vector. -/
@[simp] theorem coordinateExactSpanPresentation_thirdCoordinates_val
    {p : Profile} (target : ExactRelation p) (x : CoordinateVector p.third) :
    ((coordinateExactSpanPresentation target).thirdCoordinates x).1 = x := by
  rfl

private theorem coordinatePresentation_normalize_restrictTerm {p : Profile}
    (target : ExactRelation p) (t : Carrier p)
    (ht : t ∈ target.1.left ∪ target.1.right) :
    BinaryAmbientTensorCoordinates.normalizeTerm
      (coordinateExactSpanPresentation target).firstCoordinates
      (coordinateExactSpanPresentation target).secondCoordinates
      (coordinateExactSpanPresentation target).thirdCoordinates
      (restrictTerm (target.1.left ∪ target.1.right) t ht) = t := by
  apply Prod.ext
  · apply Subtype.ext
    rfl
  · apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      rfl

/-- The identity exact-span presentation normalizes the left endpoint back to
the original coordinate state. -/
@[simp] theorem normalizedLeft_coordinateExactSpanPresentation {p : Profile}
    (target : ExactRelation p) :
    normalizedLeft (coordinateExactSpanPresentation target) = target.1.left := by
  unfold normalizedLeft normalizeSubstate
  unfold BinaryAmbientTensorCoordinates.normalizeState restrictState
  rw [Finset.map_map]
  have hEmbedding :
      ({ toFun := fun t => restrictTerm
            (target.1.left ∪ target.1.right) t.1
            (Finset.subset_union_left t.2)
         inj' := by
           intro s t hst
           apply Subtype.ext
           simpa using congrArg
             (includeTerm (target.1.left ∪ target.1.right)) hst } :
        {t // t ∈ target.1.left} ↪
          BinaryAmbientCarrier.Carrier
            (BinaryAmbientCarrier.firstSpan
              (target.1.left ∪ target.1.right))
            (BinaryAmbientCarrier.secondSpan
              (target.1.left ∪ target.1.right))
            (BinaryAmbientCarrier.thirdSpan
              (target.1.left ∪ target.1.right))).trans
          (BinaryAmbientTensorCoordinates.carrierEquiv
            (coordinateExactSpanPresentation target).firstCoordinates
            (coordinateExactSpanPresentation target).secondCoordinates
            (coordinateExactSpanPresentation target).thirdCoordinates).symm.toEmbedding =
        Function.Embedding.subtype _ := by
    apply Function.Embedding.ext
    intro t
    exact coordinatePresentation_normalize_restrictTerm target t.1
      (Finset.mem_union_left _ t.2)
  rw [hEmbedding]
  exact Finset.attach_map_val
/-- The identity exact-span presentation normalizes the right endpoint back to
the original coordinate state. -/
@[simp] theorem normalizedRight_coordinateExactSpanPresentation {p : Profile}
    (target : ExactRelation p) :
    normalizedRight (coordinateExactSpanPresentation target) = target.1.right := by
  unfold normalizedRight normalizeSubstate
  unfold BinaryAmbientTensorCoordinates.normalizeState restrictState
  rw [Finset.map_map]
  have hEmbedding :
      ({ toFun := fun t => restrictTerm
            (target.1.left ∪ target.1.right) t.1
            (Finset.subset_union_right t.2)
         inj' := by
           intro s t hst
           apply Subtype.ext
           simpa using congrArg
             (includeTerm (target.1.left ∪ target.1.right)) hst } :
        {t // t ∈ target.1.right} ↪
          BinaryAmbientCarrier.Carrier
            (BinaryAmbientCarrier.firstSpan
              (target.1.left ∪ target.1.right))
            (BinaryAmbientCarrier.secondSpan
              (target.1.left ∪ target.1.right))
            (BinaryAmbientCarrier.thirdSpan
              (target.1.left ∪ target.1.right))).trans
          (BinaryAmbientTensorCoordinates.carrierEquiv
            (coordinateExactSpanPresentation target).firstCoordinates
            (coordinateExactSpanPresentation target).secondCoordinates
            (coordinateExactSpanPresentation target).thirdCoordinates).symm.toEmbedding =
        Function.Embedding.subtype _ := by
    apply Function.Embedding.ext
    intro t
    exact coordinatePresentation_normalize_restrictTerm target t.1
      (Finset.mem_union_right _ t.2)
  rw [hEmbedding]
  exact Finset.attach_map_val

/-- Normalizing an exact coordinate relation through its identity exact-span
presentation reconstructs that proof-bearing relation. -/
theorem normalizedExactRelation_coordinateExactSpanPresentation {p : Profile}
    (target : ExactRelation p) :
    let hEvaluation : BinaryAmbientCarrier.stateEvaluation target.1.left =
        BinaryAmbientCarrier.stateEvaluation target.1.right :=
      (coordinate_stateEvaluation_eq_iff_ambientStateEvaluation
        target.1.left target.1.right).mp target.2.2.2.2.1
    normalizedExactRelation (coordinateExactSpanPresentation target)
      target.2.1 target.2.2.1 target.2.2.2.1 hEvaluation = target := by
  dsimp only
  apply Subtype.ext
  rw [normalizedExactRelation_value]
  apply congrArg₂ (fun left right =>
    ({ left := left, right := right } :
      NormalizedBinaryFiniteAction.RelationEndpoints p))
  · exact normalizedLeft_coordinateExactSpanPresentation target
  · exact normalizedRight_coordinateExactSpanPresentation target

/-- A proof-bearing two-versus-three circuit evaluated in the genuine nested
tensor product of its three coordinate factor spaces. -/
structure AbstractFiveCircuitModel (p : Profile) where
  /-- The two-term endpoint. -/
  left : State p
  /-- The three-term endpoint. -/
  right : State p
  /-- The left endpoint has two terms. -/
  card_left : left.card = 2
  /-- The right endpoint has three terms. -/
  card_right : right.card = 3
  /-- The endpoints are disjoint finite sets. -/
  disjoint : Disjoint left right
  /-- The endpoints evaluate equally in an actual nested tensor product. -/
  abstract_tensor_eq :
    BinaryAmbientCarrier.stateEvaluation left =
      BinaryAmbientCarrier.stateEvaluation right
  /-- Their five-term union is minimal for actual tensor-product evaluation. -/
  abstract_circuit :
    Circuit (@BinaryAmbientCarrier.tensorEvaluation
      (CoordinateVector p.first) (CoordinateVector p.second)
      (CoordinateVector p.third) _ _ _ _ _ _) (left ∪ right)

/-- Every proof-bearing exact coordinate relation canonically supplies a
circuit model in a genuine nested tensor product. -/
def exactRelationAbstractModel {p : Profile} (target : ExactRelation p) :
    AbstractFiveCircuitModel p where
  left := target.1.left
  right := target.1.right
  card_left := target.2.1
  card_right := target.2.2.1
  disjoint := target.2.2.2.1
  abstract_tensor_eq :=
    (coordinate_stateEvaluation_eq_iff_ambientStateEvaluation
      target.1.left target.1.right).mp target.2.2.2.2.1
  abstract_circuit :=
    (coordinateCircuit_iff_ambientCircuit p
      (target.1.left ∪ target.1.right)).mp target.2.circuit

/-- The selected row `411-01`, as a proof-bearing exact normalized relation. -/
def row41101ExactRelation : ExactRelation profile411 := by
  let endpoints : NormalizedBinaryFiniteAction.RelationEndpoints profile411 :=
    { left := NormalizedBinaryFiveCircuitRows.row41101Start
      right := NormalizedBinaryFiveCircuitRows.row41101Finish }
  have hCardLeft : endpoints.left.card = 2 :=
    NormalizedBinaryFiveCircuitRows.row41101_card_start
  have hCardRight : endpoints.right.card = 3 :=
    NormalizedBinaryFiveCircuitRows.row41101_card_finish
  have hDisjoint : Disjoint endpoints.left endpoints.right :=
    NormalizedBinaryFiveCircuitRows.row41101_disjoint
  have hEvaluation : stateEvaluation endpoints.left =
      stateEvaluation endpoints.right :=
    (NormalizedBinaryAllModeMove.allModeMovePath_preserves_evaluation
      NormalizedBinaryFiveCircuitRows.row41101ForwardPath).symm
  have hProfile :=
    NormalizedBinaryFiveCircuitRows.row41101_exactFactorProfile
  refine ⟨endpoints, ?_⟩
  constructor
  · exact hCardLeft
  constructor
  · exact hCardRight
  constructor
  · exact hDisjoint
  constructor
  · exact hEvaluation
  · exact hProfile

/-- The genuine abstract tensor-product circuit model carried by row `411-01`. -/
def row41101AbstractModel : AbstractFiveCircuitModel profile411 :=
  exactRelationAbstractModel row41101ExactRelation

/-- The row-411 abstract model has actual `2/3` disjoint endpoints, equal
nested-tensor evaluations, and a five-term circuit, while the same endpoints
have intrinsic directed distance exactly three in both directions with
altitude at most four. -/
theorem row41101_abstract_model_and_intrinsic_sharpness :
    row41101AbstractModel.left =
        NormalizedBinaryFiveCircuitRows.row41101Start ∧
      row41101AbstractModel.right =
        NormalizedBinaryFiveCircuitRows.row41101Finish ∧
      row41101AbstractModel.left.card = 2 ∧
      row41101AbstractModel.right.card = 3 ∧
      Disjoint row41101AbstractModel.left row41101AbstractModel.right ∧
      BinaryAmbientCarrier.stateEvaluation row41101AbstractModel.left =
        BinaryAmbientCarrier.stateEvaluation row41101AbstractModel.right ∧
      Circuit (@BinaryAmbientCarrier.tensorEvaluation
        (CoordinateVector profile411.first)
        (CoordinateVector profile411.second)
        (CoordinateVector profile411.third) _ _ _ _ _ _)
        (row41101AbstractModel.left ∪ row41101AbstractModel.right) ∧
      BinaryAmbientFiveCircuitSharpness.row41101AmbientForwardPath.length = 3 ∧
      BinaryAmbientFiveCircuitSharpness.row41101AmbientReversePath.length = 3 ∧
      BinaryAmbientFiveCircuitSharpness.row41101AmbientForwardPath.altitude ≤ 4 ∧
      BinaryAmbientFiveCircuitSharpness.row41101AmbientReversePath.altitude ≤ 4 ∧
      (∀ path : MovePath BinaryAmbientMoves.AllModeMove
        NormalizedBinaryFiveCircuitRows.row41101Start
        NormalizedBinaryFiveCircuitRows.row41101Finish,
        ¬ path.length ≤ 2) ∧
      (∀ path : MovePath BinaryAmbientMoves.AllModeMove
        NormalizedBinaryFiveCircuitRows.row41101Finish
        NormalizedBinaryFiveCircuitRows.row41101Start,
        ¬ path.length ≤ 2) := by
  have hIntrinsic := BilinearComplexity.BinaryAmbientFiveCircuitSharpness.row41101_intrinsic_ambient_exact_directed_length_three
  have hForwardLength := hIntrinsic.1
  have hReverseLength := hIntrinsic.2.1
  have hForwardAltitude := hIntrinsic.2.2.1
  have hReverseAltitude := hIntrinsic.2.2.2.1
  have hForwardLowerBound := hIntrinsic.2.2.2.2.1
  have hReverseLowerBound := hIntrinsic.2.2.2.2.2
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · exact row41101AbstractModel.card_left
  constructor
  · exact row41101AbstractModel.card_right
  constructor
  · exact row41101AbstractModel.disjoint
  constructor
  · exact row41101AbstractModel.abstract_tensor_eq
  constructor
  · exact row41101AbstractModel.abstract_circuit
  constructor
  · exact hForwardLength
  constructor
  · exact hReverseLength
  constructor
  · exact hForwardAltitude
  constructor
  · exact hReverseAltitude
  constructor
  · exact hForwardLowerBound
  · exact hReverseLowerBound

/-- Every selected orbit label has a choice-free identity exact-span
presentation in its own coordinate spaces. -/
def _root_.BilinearComplexity.NormalizedBinaryOrbitClassification.OrbitLabel.selectedCoordinatePresentation
    (label : _root_.BilinearComplexity.NormalizedBinaryOrbitClassification.OrbitLabel) :
    ExactSpanPresentation label.selectedExactRelation.1.left
      label.selectedExactRelation.1.right :=
  coordinateExactSpanPresentation label.selectedExactRelation

/-- Every selected orbit label has a genuine abstract tensor-product circuit
model, rather than merely a syntactic label witness. -/
def _root_.BilinearComplexity.NormalizedBinaryOrbitClassification.OrbitLabel.selectedAbstractModel
    (label : _root_.BilinearComplexity.NormalizedBinaryOrbitClassification.OrbitLabel) :
    AbstractFiveCircuitModel label.1.profile :=
  exactRelationAbstractModel label.selectedExactRelation

/-- The selected identity presentation recovers both selected coordinate
endpoints for every one of the thirteen labels. -/
theorem selectedCoordinatePresentation_normalizedEndpoints
    (label : BilinearComplexity.NormalizedBinaryOrbitClassification.OrbitLabel) :
    normalizedLeft label.selectedCoordinatePresentation =
        label.selectedExactRelation.1.left ∧
      normalizedRight label.selectedCoordinatePresentation =
        label.selectedExactRelation.1.right :=
  ⟨normalizedLeft_coordinateExactSpanPresentation label.selectedExactRelation,
    normalizedRight_coordinateExactSpanPresentation label.selectedExactRelation⟩

/-- The generic abstract model retains the exact relation's ordered endpoint
data definitionally. -/
@[simp] theorem exactRelationAbstractModel_endpoints {p : Profile}
    (target : ExactRelation p) :
    (exactRelationAbstractModel target).left = target.1.left ∧
      (exactRelationAbstractModel target).right = target.1.right :=
  ⟨rfl, rfl⟩

example : Nonempty (AbstractFiveCircuitModel profile411) :=
  ⟨row41101AbstractModel⟩

example : normalizedLeft
    (coordinateExactSpanPresentation row41101ExactRelation) =
      NormalizedBinaryFiveCircuitRows.row41101Start := by
  exact normalizedLeft_coordinateExactSpanPresentation row41101ExactRelation

#check @coordinateIdentity
#check @normalizeState_coordinateIdentity
#check @coordinate_stateEvaluation_eq_iff_ambientStateEvaluation
#check @coordinateCircuit_iff_ambientCircuit
#check @coordinate_firstSpan_eq_firstFactorSpan
#check @coordinate_secondSpan_eq_secondFactorSpan
#check @coordinate_thirdSpan_eq_thirdFactorSpan
#check @coordinateExactSpanPresentation
#check @normalizedLeft_coordinateExactSpanPresentation
#check @normalizedRight_coordinateExactSpanPresentation
#check @normalizedExactRelation_coordinateExactSpanPresentation
#check @exactRelationAbstractModel
#check @row41101AbstractModel
#check @row41101_abstract_model_and_intrinsic_sharpness
#check @selectedCoordinatePresentation_normalizedEndpoints

#print axioms coordinate_stateEvaluation_eq_iff_ambientStateEvaluation
#print axioms coordinateCircuit_iff_ambientCircuit
#print axioms normalizedExactRelation_coordinateExactSpanPresentation
#print axioms row41101_abstract_model_and_intrinsic_sharpness
#print axioms selectedCoordinatePresentation_normalizedEndpoints

end BilinearComplexity.BinaryAmbientCircuitModels
