import BilinearComplexity.BinaryFiveCircuitCompiler
import BilinearComplexity.BinaryAmbientCircuitModels

set_option autoImplicit false

/-!
# Ambient binary five-circuit theorem

This module combines the presentation-explicit compiler with genuine nested
binary tensor-product models. It records all thirteen realizations and global
sharpness of the uniform path-length bound.

AI disclosure: produced with AI assistance (see `README`).
-/

namespace BilinearComplexity.BinaryFiveCircuitTheorem

open BinaryCircuit
open BinaryAmbientCarrier
open BinaryAmbientNormalization
open BinaryAmbientCircuitModels
open BinaryFiveCircuitCompiler
open NormalizedBinaryCarrier
open NormalizedBinaryFiniteAction
open NormalizedBinaryOrbitClassification
open NormalizedBinaryRelationEnumeration

/-- Compiling an exact coordinate relation through its identity exact-span
presentation returns exactly the label of direct normalized compilation. -/
theorem coordinateCompiler_label {p : Profile} (target : ExactRelation p) :
    (compileBinaryFiveCircuit (coordinateExactSpanPresentation target)
      target.2.1 target.2.2.1 target.2.2.2.1
      ((coordinate_stateEvaluation_eq_iff_ambientStateEvaluation
        target.1.left target.1.right).mp target.2.2.2.2.1)).label =
      (compileClassified target).label := by
  change (compileClassified (normalizedExactRelation
    (coordinateExactSpanPresentation target) target.2.1 target.2.2.1
    target.2.2.2.1
    ((coordinate_stateEvaluation_eq_iff_ambientStateEvaluation
      target.1.left target.1.right).mp target.2.2.2.2.1))).label =
      (compileClassified target).label
  exact congrArg
    (fun relation : ExactRelation p => (compileClassified relation).label)
    (normalizedExactRelation_coordinateExactSpanPresentation target)

/-- The identity-presentation ambient compiler returns a selected label when
run on that label's chosen exact coordinate relation. -/
theorem selectedCoordinateCompiler_label (label : OrbitLabel) :
    (compileBinaryFiveCircuit label.selectedCoordinatePresentation
      label.selectedExactRelation.2.1 label.selectedExactRelation.2.2.1
      label.selectedExactRelation.2.2.2.1
      ((coordinate_stateEvaluation_eq_iff_ambientStateEvaluation
        label.selectedExactRelation.1.left
        label.selectedExactRelation.1.right).mp
        label.selectedExactRelation.2.2.2.2.1)).label = label := by
  exact (coordinateCompiler_label label.selectedExactRelation).trans
    (compileClassified_selectedExactRelation_label label)

/-- The concrete identity-presentation ambient compilation selected for an
orbit label. -/
def selectedAmbientCompilation (label : OrbitLabel) :=
  compileBinaryFiveCircuit label.selectedCoordinatePresentation
    label.selectedExactRelation.2.1 label.selectedExactRelation.2.2.1
    label.selectedExactRelation.2.2.2.1
    ((coordinate_stateEvaluation_eq_iff_ambientStateEvaluation
      label.selectedExactRelation.1.left
      label.selectedExactRelation.1.right).mp
      label.selectedExactRelation.2.2.2.2.1)

example (label : OrbitLabel) :
    (selectedAmbientCompilation label).label = label :=
  selectedCoordinateCompiler_label label

/-- Every orbit label has a genuine nested tensor-product circuit model
whose endpoints lie in that unique semantic orbit, and the selected compiler's
actual paths satisfy the uniform metric and exact-span-confinement bounds. -/
theorem everyOrbitLabel_has_genuine_ambient_realization (label : OrbitLabel) :
    Circuit (@BinaryAmbientCarrier.tensorEvaluation
      (CoordinateVector label.1.profile.first)
      (CoordinateVector label.1.profile.second)
      (CoordinateVector label.1.profile.third) _ _ _ _ _ _)
      (label.selectedAbstractModel.left ∪ label.selectedAbstractModel.right) ∧
    AmbientInOrbit label label.selectedAbstractModel.left
      label.selectedAbstractModel.right ∧
    (∀ candidate : OrbitLabel,
      AmbientInOrbit candidate label.selectedAbstractModel.left
        label.selectedAbstractModel.right → candidate = label) ∧
    (selectedAmbientCompilation label).label = label ∧
    (selectedAmbientCompilation label).forward.length ≤ 3 ∧
    (selectedAmbientCompilation label).reverse.length ≤ 3 ∧
    (selectedAmbientCompilation label).forward.altitude ≤ 4 ∧
    (selectedAmbientCompilation label).reverse.altitude ≤ 4 ∧
    AmbientPathFactorSpanConfined
      (selectedAmbientCompilation label).forward
      (label.selectedAbstractModel.left ∪ label.selectedAbstractModel.right) ∧
    AmbientPathFactorSpanConfined
      (selectedAmbientCompilation label).reverse
      (label.selectedAbstractModel.left ∪ label.selectedAbstractModel.right) ∧
    AmbientFiveCircuitConclusion label.selectedAbstractModel.left
      label.selectedAbstractModel.right := by
  let model := label.selectedAbstractModel
  have horbit : AmbientInOrbit label model.left model.right := by
    refine ⟨label.selectedCoordinatePresentation, ?_⟩
    obtain ⟨hleft, hright⟩ :=
      selectedCoordinatePresentation_normalizedEndpoints label
    change InOrbit label
      ⟨normalizedLeft label.selectedCoordinatePresentation,
        normalizedRight label.selectedCoordinatePresentation⟩
    rw [hleft, hright]
    exact selectedExactRelation_inOrbit label
  have hunique : ∀ candidate : OrbitLabel,
      AmbientInOrbit candidate model.left model.right → candidate = label := by
    intro candidate hcandidate
    exact ambientInOrbit_label_unique hcandidate horbit
  refine ⟨model.abstract_circuit, horbit, hunique,
    selectedCoordinateCompiler_label label,
    (selectedAmbientCompilation label).forward_length_le,
    (selectedAmbientCompilation label).reverse_length_le,
    (selectedAmbientCompilation label).forward_altitude_le,
    (selectedAmbientCompilation label).reverse_altitude_le,
    (selectedAmbientCompilation label).forward_confined,
    (selectedAmbientCompilation label).reverse_confined, ?_⟩
  exact exists_ambientFiveCircuitConclusion model.card_left model.card_right
    model.disjoint model.abstract_tensor_eq

/-- There are exactly thirteen labels, and every label's genuine ambient
circuit realization has a unique semantic label and concrete bounded,
exact-span-confined compiler paths in both directions. -/
theorem all_thirteen_ambient_orbits_realized :
    Fintype.card OrbitLabel = 13 ∧
      ∀ label : OrbitLabel,
        Circuit (@BinaryAmbientCarrier.tensorEvaluation
          (CoordinateVector label.1.profile.first)
          (CoordinateVector label.1.profile.second)
          (CoordinateVector label.1.profile.third) _ _ _ _ _ _)
          (label.selectedAbstractModel.left ∪ label.selectedAbstractModel.right) ∧
        AmbientInOrbit label label.selectedAbstractModel.left
          label.selectedAbstractModel.right ∧
        (∀ candidate : OrbitLabel,
          AmbientInOrbit candidate label.selectedAbstractModel.left
            label.selectedAbstractModel.right → candidate = label) ∧
        (selectedAmbientCompilation label).label = label ∧
        (selectedAmbientCompilation label).forward.length ≤ 3 ∧
        (selectedAmbientCompilation label).reverse.length ≤ 3 ∧
        (selectedAmbientCompilation label).forward.altitude ≤ 4 ∧
        (selectedAmbientCompilation label).reverse.altitude ≤ 4 ∧
        AmbientPathFactorSpanConfined
          (selectedAmbientCompilation label).forward
          (label.selectedAbstractModel.left ∪ label.selectedAbstractModel.right) ∧
        AmbientPathFactorSpanConfined
          (selectedAmbientCompilation label).reverse
          (label.selectedAbstractModel.left ∪ label.selectedAbstractModel.right) ∧
        AmbientFiveCircuitConclusion label.selectedAbstractModel.left
          label.selectedAbstractModel.right :=
  ⟨orbitLabel_card, everyOrbitLabel_has_genuine_ambient_realization⟩

/-- The unique profile-411 selected orbit label. -/
def row41101OrbitLabel : OrbitLabel := ⟨.family411, (0 : Fin 1)⟩

example : row41101OrbitLabel.1 = .family411 := rfl

example : row41101ExactRelation = row41101OrbitLabel.selectedExactRelation := by
  rfl

/-- The actual identity-presentation compiler run on the concrete profile-411
row relation. -/
def row41101SelectedCompilation :=
  compileBinaryFiveCircuit
    (coordinateExactSpanPresentation row41101ExactRelation)
    row41101ExactRelation.2.1 row41101ExactRelation.2.2.1
    row41101ExactRelation.2.2.2.1
    ((coordinate_stateEvaluation_eq_iff_ambientStateEvaluation
      row41101ExactRelation.1.left row41101ExactRelation.1.right).mp
      row41101ExactRelation.2.2.2.2.1)

/-- The concrete row-411 compiler returns the unique profile-411 orbit label. -/
theorem row41101SelectedCompilation_label :
    row41101SelectedCompilation.label = row41101OrbitLabel := by
  calc
    row41101SelectedCompilation.label =
        (compileClassified row41101ExactRelation).label :=
      coordinateCompiler_label row41101ExactRelation
    _ = row41101OrbitLabel := by
      rw [show row41101ExactRelation =
        row41101OrbitLabel.selectedExactRelation by rfl]
      exact compileClassified_selectedExactRelation_label row41101OrbitLabel

example : row41101SelectedCompilation.label = row41101OrbitLabel :=
  row41101SelectedCompilation_label

/-- On the genuine profile-411 circuit model, the compiler's two actual paths
both have exact length three; they obey the uniform altitude and confinement
bounds, and no intrinsic ambient path of length at most two exists in either
direction. -/
theorem row41101_genuine_compiler_joint_sharpness :
    Circuit (@BinaryAmbientCarrier.tensorEvaluation
      (CoordinateVector profile411.first)
      (CoordinateVector profile411.second)
      (CoordinateVector profile411.third) _ _ _ _ _ _)
      (row41101AbstractModel.left ∪ row41101AbstractModel.right) ∧
    row41101SelectedCompilation.label = row41101OrbitLabel ∧
    row41101SelectedCompilation.forward.length = 3 ∧
    row41101SelectedCompilation.reverse.length = 3 ∧
    row41101SelectedCompilation.forward.altitude ≤ 4 ∧
    row41101SelectedCompilation.reverse.altitude ≤ 4 ∧
    AmbientPathFactorSpanConfined row41101SelectedCompilation.forward
      (row41101AbstractModel.left ∪ row41101AbstractModel.right) ∧
    AmbientPathFactorSpanConfined row41101SelectedCompilation.reverse
      (row41101AbstractModel.left ∪ row41101AbstractModel.right) ∧
    (∀ path : MovePath BinaryAmbientMoves.AllModeMove
      row41101AbstractModel.left row41101AbstractModel.right,
      ¬ path.length ≤ 2) ∧
    (∀ path : MovePath BinaryAmbientMoves.AllModeMove
      row41101AbstractModel.right row41101AbstractModel.left,
      ¬ path.length ≤ 2) := by
  have hcircuit : Circuit (@BinaryAmbientCarrier.tensorEvaluation
      (CoordinateVector profile411.first)
      (CoordinateVector profile411.second)
      (CoordinateVector profile411.third) _ _ _ _ _ _)
      (row41101AbstractModel.left ∪ row41101AbstractModel.right) :=
    row41101AbstractModel.abstract_circuit
  have hnoForward : ∀ path : MovePath BinaryAmbientMoves.AllModeMove
      row41101AbstractModel.left row41101AbstractModel.right,
      ¬ path.length ≤ 2 := by
    intro path
    exact BinaryAmbientFiveCircuitSharpness.row41101_no_ambient_forward_path_length_le_two
      path
  have hnoReverse : ∀ path : MovePath BinaryAmbientMoves.AllModeMove
      row41101AbstractModel.right row41101AbstractModel.left,
      ¬ path.length ≤ 2 := by
    intro path
    exact BinaryAmbientFiveCircuitSharpness.row41101_no_ambient_reverse_path_length_le_two
      path
  have hforward : row41101SelectedCompilation.forward.length = 3 := by
    have hle : row41101SelectedCompilation.forward.length ≤ 3 :=
      row41101SelectedCompilation.forward_length_le
    have hnot : ¬ row41101SelectedCompilation.forward.length ≤ 2 :=
      hnoForward row41101SelectedCompilation.forward
    omega
  have hreverse : row41101SelectedCompilation.reverse.length = 3 := by
    have hle : row41101SelectedCompilation.reverse.length ≤ 3 :=
      row41101SelectedCompilation.reverse_length_le
    have hnot : ¬ row41101SelectedCompilation.reverse.length ≤ 2 :=
      hnoReverse row41101SelectedCompilation.reverse
    omega
  exact ⟨hcircuit, row41101SelectedCompilation_label,
    hforward, hreverse, row41101SelectedCompilation.forward_altitude_le,
    row41101SelectedCompilation.reverse_altitude_le,
    row41101SelectedCompilation.forward_confined,
    row41101SelectedCompilation.reverse_confined, hnoForward, hnoReverse⟩

/-- Every finite-dimensional ambient disjoint `2/3` equal-evaluation relation
has one and only one semantic orbit label and has explicit compiler paths in
both directions, of length at most three and altitude at most four, confined
factorwise to the spans generated by its five input tensors. No separate
circuit hypothesis is needed: the `2/3`, disjointness, and equal-evaluation
contract is the stronger input used to construct the classified exact
relation. -/
theorem finiteDimensional_ambient_fiveCircuit_classification
    {U V W : Type*}
    [AddCommGroup U] [Module F2 U]
    [AddCommGroup V] [Module F2 V]
    [AddCommGroup W] [Module F2 W]
    [DecidableEq U] [DecidableEq V] [DecidableEq W]
    [FiniteDimensional F2 U] [FiniteDimensional F2 V]
    [FiniteDimensional F2 W]
    {A B : State U V W}
    (hA : A.card = 2) (hB : B.card = 3) (hDisjoint : Disjoint A B)
    (hEvaluation : stateEvaluation A = stateEvaluation B) :
    (∃! label : OrbitLabel, AmbientInOrbit label A B) ∧
      ∃ forward : MovePath
          (BinaryAmbientMoves.AllModeMove (U := U) (V := V) (W := W)) A B,
        ∃ reverse : MovePath
            (BinaryAmbientMoves.AllModeMove (U := U) (V := V) (W := W)) B A,
          forward.length ≤ 3 ∧ reverse.length ≤ 3 ∧
          forward.altitude ≤ 4 ∧ reverse.altitude ≤ 4 ∧
          AmbientPathFactorSpanConfined forward (A ∪ B) ∧
          AmbientPathFactorSpanConfined reverse (A ∪ B) := by
  rcases exists_ambientFiveCircuitConclusion hA hB hDisjoint hEvaluation with
    ⟨label, hmembership, forward, reverse, hpaths⟩
  refine ⟨⟨label, hmembership, ?_⟩, forward, reverse, hpaths⟩
  intro candidate hcandidate
  exact ambientInOrbit_label_unique hcandidate hmembership

#check @coordinateCompiler_label
#check @everyOrbitLabel_has_genuine_ambient_realization
#check @all_thirteen_ambient_orbits_realized
#check @row41101_genuine_compiler_joint_sharpness
#check @finiteDimensional_ambient_fiveCircuit_classification

#print axioms coordinateCompiler_label
#print axioms all_thirteen_ambient_orbits_realized
#print axioms row41101_genuine_compiler_joint_sharpness
#print axioms finiteDimensional_ambient_fiveCircuit_classification

end BilinearComplexity.BinaryFiveCircuitTheorem
