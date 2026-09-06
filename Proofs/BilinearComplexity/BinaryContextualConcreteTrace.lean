import BilinearComplexity.BinaryContextualFiveCircuitOptimality
import BilinearComplexity.BinaryContextualTrace

/-!
# Concrete compilation of contextual traces

This module closes the abstract compiler parameter in `BinaryContextualTrace`.
Every proof-bearing contextual jump is classified and compiled by
`compileContextualBinaryFiveCircuit`; its direction selects the actual forward
or reverse ambient path, and the global optimality theorems certify the
`MacroCompilation.shortest` field.  Thus the public trace compiler takes only
a trace: there is no run-time path, lower-bound callback, basis choice, or
requested distance.

The dependent endpoint equalities stored in each jump are used only to
transport the compiler's exact `context ∪ endpoint` path indices.  Transport
preserves length and altitude, so concatenating macros introduces no
accumulative overhead beyond the existing one-term altitude bound.
-/

set_option autoImplicit false

namespace BilinearComplexity.BinaryContextualConcreteTrace

open BinaryCircuit
open BinaryAmbientCarrier
open BinaryAmbientMoves
open BinaryAmbientNormalization
open BinaryAmbientContextTransport
open BinaryAmbientCircuitModels
open BinaryFiveCircuitCompiler
open BinaryContextBorrowing221
open BinaryContextualTrace
open BinaryContextualFiveCircuitCompiler
open BinaryContextualNormalizedCompiler
open NormalizedBinaryCarrier
open NormalizedBinaryOrbitClassification
open NormalizedBinaryRelationEnumeration
open NormalizedBinaryContextualCompiler

universe u v w

variable {U : Type u} {V : Type v} {W : Type w}
variable [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
variable [Module F2 U] [Module F2 V] [Module F2 W]
variable [DecidableEq U] [DecidableEq V] [DecidableEq W]

/-- Compile one proof-bearing contextual five-circuit jump to the actual
ambient path selected by its direction, with semantic orbit metadata and a
global shortestness certificate. -/
def compileContextualJump
    {D E : BinaryContextualTrace.AmbientState U V W}
    (jump : ContextualFiveCircuitJump D E) : MacroCompilation jump := by
  let actual := compileContextualBinaryFiveCircuit jump.presentation
    jump.left_card jump.right_card jump.endpoints_disjoint
    jump.endpoint_evaluation jump.context jump.context_disjoint
  cases hDirection : jump.direction with
  | forward =>
      have hStart : D = jump.context ∪ jump.left := by
        simpa only [hDirection, MacroDirection.source] using jump.start_eq
      have hFinish : E = jump.context ∪ jump.right := by
        simpa only [hDirection, MacroDirection.target] using jump.finish_eq
      refine {
        orbit := actual.label
        distance := orbitDistance actual.label
        distance_two_or_three := actual.distance_two_or_three
        path := castMovePathEndpoints actual.forward hStart.symm hFinish.symm
        path_length := ?_
        altitude_le := ?_
        shortest := ?_ }
      · rw [castMovePathEndpoints_length, actual.forward_length]
      · rw [castMovePathEndpoints_altitude]
        exact actual.forward_altitude_le
      · intro competitor
        let localCompetitor :=
          castMovePathEndpoints competitor hStart hFinish
        calc
          orbitDistance actual.label = actual.forward.length := actual.forward_length.symm
          _ ≤ localCompetitor.length := actual.forward_shortest localCompetitor
          _ = competitor.length :=
            castMovePathEndpoints_length competitor hStart hFinish
  | reverse =>
      have hStart : D = jump.context ∪ jump.right := by
        simpa only [hDirection, MacroDirection.source] using jump.start_eq
      have hFinish : E = jump.context ∪ jump.left := by
        simpa only [hDirection, MacroDirection.target] using jump.finish_eq
      refine {
        orbit := actual.label
        distance := orbitDistance actual.label
        distance_two_or_three := actual.distance_two_or_three
        path := castMovePathEndpoints actual.reverse hStart.symm hFinish.symm
        path_length := ?_
        altitude_le := ?_
        shortest := ?_ }
      · rw [castMovePathEndpoints_length, actual.reverse_length]
      · rw [castMovePathEndpoints_altitude]
        exact actual.reverse_altitude_le
      · intro competitor
        let localCompetitor :=
          castMovePathEndpoints competitor hStart hFinish
        calc
          orbitDistance actual.label = actual.reverse.length := actual.reverse_length.symm
          _ ≤ localCompetitor.length := actual.reverse_shortest localCompetitor
          _ = competitor.length :=
            castMovePathEndpoints_length competitor hStart hFinish

private theorem compileContextualJump_orbit_eq
    {D E : BinaryContextualTrace.AmbientState U V W}
    (jump : ContextualFiveCircuitJump D E) :
    (compileContextualJump jump).orbit =
      (compileContextualBinaryFiveCircuit jump.presentation jump.left_card
        jump.right_card jump.endpoints_disjoint jump.endpoint_evaluation
        jump.context jump.context_disjoint).label := by
  rcases jump with ⟨context, left, right, direction, leftCard, rightCard,
    endpointsDisjoint, contextDisjoint, endpointEvaluation, supportCircuit,
    presentation, startEq, finishEq⟩
  cases direction <;> rfl

private theorem compileContextualJump_distance_eq
    {D E : BinaryContextualTrace.AmbientState U V W}
    (jump : ContextualFiveCircuitJump D E) :
    (compileContextualJump jump).distance =
      orbitDistance (compileContextualBinaryFiveCircuit jump.presentation
        jump.left_card jump.right_card jump.endpoints_disjoint
        jump.endpoint_evaluation jump.context jump.context_disjoint).label := by
  rcases jump with ⟨context, left, right, direction, leftCard, rightCard,
    endpointsDisjoint, contextDisjoint, endpointEvaluation, supportCircuit,
    presentation, startEq, finishEq⟩
  cases direction <;> rfl

/-- The concrete macro's label is semantically the orbit of the jump's actual
local endpoint pair; it is not merely unverified metadata. -/
theorem compileContextualJump_ambient_membership
    {D E : BinaryContextualTrace.AmbientState U V W}
    (jump : ContextualFiveCircuitJump D E) :
    AmbientInOrbit (compileContextualJump jump).orbit jump.left jump.right := by
  let actual := compileContextualBinaryFiveCircuit jump.presentation
    jump.left_card jump.right_card jump.endpoints_disjoint
    jump.endpoint_evaluation jump.context jump.context_disjoint
  rw [compileContextualJump_orbit_eq jump]
  exact actual.ambient_membership

/-- The concrete macro distance is definitionally tied to its certified orbit
label and is therefore always the canonical value two or three. -/
@[simp] theorem compileContextualJump_distance
    {D E : BinaryContextualTrace.AmbientState U V W}
    (jump : ContextualFiveCircuitJump D E) :
    (compileContextualJump jump).distance =
      orbitDistance (compileContextualJump jump).orbit := by
  rw [compileContextualJump_orbit_eq jump]
  exact compileContextualJump_distance_eq jump

/-- Every vertex of the adapted concrete macro agrees with the supplied
context outside the endpoint-generated local box. -/
theorem compileContextualJump_outside
    {D E : BinaryContextualTrace.AmbientState U V W}
    (jump : ContextualFiveCircuitJump D E) :
    ∀ Y ∈ (compileContextualJump jump).path.vertices,
      Y \ localBox jump.presentation =
        jump.context \ localBox jump.presentation := by
  rcases jump with ⟨context, left, right, direction, leftCard, rightCard,
    endpointsDisjoint, contextDisjoint, endpointEvaluation, supportCircuit,
    presentation, startEq, finishEq⟩
  let actual := compileContextualBinaryFiveCircuit presentation leftCard
    rightCard endpointsDisjoint endpointEvaluation context contextDisjoint
  cases direction with
  | forward =>
      intro Y hY
      have hYActual : PathVertex actual.forward Y := by
        rw [PathVertex]
        simpa only [compileContextualJump, castMovePathEndpoints_vertices] using hY
      simpa only [outsideContext] using actual.forward_outside hYActual
  | reverse =>
      intro Y hY
      have hYActual : PathVertex actual.reverse Y := by
        rw [PathVertex]
        simpa only [compileContextualJump, castMovePathEndpoints_vertices] using hY
      simpa only [outsideContext] using actual.reverse_outside hYActual

/-- The concrete local compiler used by public trace compilation. -/
def concreteEffectiveLocalCompiler : EffectiveLocalCompiler U V W :=
  fun jump => compileContextualJump jump

example {D E : BinaryContextualTrace.AmbientState U V W}
    (jump : ContextualFiveCircuitJump D E) :
    concreteEffectiveLocalCompiler jump = compileContextualJump jump := rfl

namespace ContextualTrace

/-- The sum of canonical orbit distances of all contextual macros in a trace. -/
def concreteMacroDistanceSum {D E : BinaryContextualTrace.AmbientState U V W}
    (trace : ContextualTrace D E) : ℕ :=
  trace.macroDistanceSum concreteEffectiveLocalCompiler

/-- Compile a contextual trace to native ambient Split, Flip, and directed
Reduction moves using the concrete callback-free local compiler. -/
def compileConcrete {D E : BinaryContextualTrace.AmbientState U V W}
    (trace : ContextualTrace D E) : MovePath AllModeMove D E :=
  trace.compile concreteEffectiveLocalCompiler

example (X : BinaryContextualTrace.AmbientState U V W) :
    concreteMacroDistanceSum (ContextualTrace.singleton X) = 0 := by
  simp only [concreteMacroDistanceSum,
    BinaryContextualTrace.ContextualTrace.macroDistanceSum]

example (X : BinaryContextualTrace.AmbientState U V W) :
    compileConcrete (ContextualTrace.singleton X) = MovePath.singleton X := by
  simp only [compileConcrete, BinaryContextualTrace.ContextualTrace.compile]

/-- Concrete trace compilation has exactly one edge per primitive jump plus
the sum of the canonical orbit distances of its contextual jumps. -/
@[simp] theorem compileConcrete_length
    {D E : BinaryContextualTrace.AmbientState U V W}
    (trace : ContextualTrace D E) :
    (compileConcrete trace).length =
      trace.primitiveCount + concreteMacroDistanceSum trace := by
  simpa only [compileConcrete, concreteMacroDistanceSum,
    BinaryContextualTrace.ContextualTrace.constructedLength]
    using trace.compile_length concreteEffectiveLocalCompiler

/-- Every concrete macro costs at most three primitive edges, so concrete
compilation satisfies the exact global edge-count budget. -/
theorem compileConcrete_length_le
    {D E : BinaryContextualTrace.AmbientState U V W}
    (trace : ContextualTrace D E) :
    (compileConcrete trace).length ≤
      3 * trace.macroCount + trace.primitiveCount := by
  exact trace.compile_length_le concreteEffectiveLocalCompiler

/-- Concrete compilation rises at most one term above the largest explicit
trace boundary, independently of how many macros are concatenated. -/
theorem compileConcrete_altitude_le
    {D E : BinaryContextualTrace.AmbientState U V W}
    (trace : ContextualTrace D E) :
    (compileConcrete trace).altitude ≤ trace.maxStateCard + 1 := by
  exact trace.compile_altitude_le concreteEffectiveLocalCompiler

end ContextualTrace

private abbrev groundLabel221 : OrbitLabel :=
  ⟨.family221, (0 : Fin 3)⟩

private abbrev groundTarget221 : ExactRelation profile221 :=
  groundLabel221.selectedExactRelation

private def groundPresentation221 :
    ExactSpanPresentation groundTarget221.1.left groundTarget221.1.right :=
  coordinateExactSpanPresentation groundTarget221

example : normalizedLeft groundPresentation221 = groundTarget221.1.left := by
  exact normalizedLeft_coordinateExactSpanPresentation groundTarget221

private abbrev groundModel221 : AbstractFiveCircuitModel profile221 :=
  exactRelationAbstractModel groundTarget221

private theorem groundContextDisjoint221 :
    Disjoint contextC (groundTarget221.1.left ∪ groundTarget221.1.right) := by
  decide

/-- A collision-bearing profile-`221` contextual jump in the forward direction,
using the same four-term borrowing context as the contextual row regression. -/
def collisionJump221Forward : ContextualFiveCircuitJump
    (contextC ∪ groundTarget221.1.left)
    (contextC ∪ groundTarget221.1.right) where
  context := contextC
  left := groundTarget221.1.left
  right := groundTarget221.1.right
  direction := .forward
  left_card := groundTarget221.2.1
  right_card := groundTarget221.2.2.1
  endpoints_disjoint := groundTarget221.2.2.2.1
  context_disjoint := groundContextDisjoint221
  endpoint_evaluation := groundModel221.abstract_tensor_eq
  support_circuit := groundModel221.abstract_circuit
  presentation := groundPresentation221
  start_eq := rfl
  finish_eq := rfl

example : collisionJump221Forward.direction = .forward := rfl

/-- The same collision-bearing profile-`221` contextual jump traversed in the
reverse native direction. -/
def collisionJump221Reverse : ContextualFiveCircuitJump
    (contextC ∪ groundTarget221.1.right)
    (contextC ∪ groundTarget221.1.left) where
  context := contextC
  left := groundTarget221.1.left
  right := groundTarget221.1.right
  direction := .reverse
  left_card := groundTarget221.2.1
  right_card := groundTarget221.2.2.1
  endpoints_disjoint := groundTarget221.2.2.2.1
  context_disjoint := groundContextDisjoint221
  endpoint_evaluation := groundModel221.abstract_tensor_eq
  support_circuit := groundModel221.abstract_circuit
  presentation := groundPresentation221
  start_eq := rfl
  finish_eq := rfl

example : collisionJump221Reverse.direction = .reverse := rfl

/-- A one-macro collision-bearing trace through the profile-`221` relation in
the forward direction. -/
def collisionTrace221Forward : ContextualTrace
    (contextC ∪ groundTarget221.1.left)
    (contextC ∪ groundTarget221.1.right) :=
  .contextual (.singleton _) collisionJump221Forward

example : collisionTrace221Forward.macroCount = 1 := rfl

/-- A one-macro collision-bearing trace through the same profile-`221` relation
and context in the reverse direction. -/
def collisionTrace221Reverse : ContextualTrace
    (contextC ∪ groundTarget221.1.right)
    (contextC ∪ groundTarget221.1.left) :=
  .contextual (.singleton _) collisionJump221Reverse

example : collisionTrace221Reverse.macroCount = 1 := rfl

/-- The two collision-bearing profile-`221` macros compose in opposite native
directions to form a genuine round trip through the same context. -/
def collisionRoundtripTrace221 : ContextualTrace
    (contextC ∪ groundTarget221.1.left)
    (contextC ∪ groundTarget221.1.left) :=
  .contextual
    (.contextual (.singleton _) collisionJump221Forward)
    collisionJump221Reverse

example : collisionRoundtripTrace221.macroCount = 2 := rfl

example : collisionRoundtripTrace221.primitiveCount = 0 := rfl

example :
    (ContextualTrace.compileConcrete collisionRoundtripTrace221).length =
      collisionRoundtripTrace221.primitiveCount +
        ContextualTrace.concreteMacroDistanceSum collisionRoundtripTrace221 := by
  exact ContextualTrace.compileConcrete_length collisionRoundtripTrace221

example :
    (ContextualTrace.compileConcrete collisionRoundtripTrace221).length ≤
      3 * collisionRoundtripTrace221.macroCount +
        collisionRoundtripTrace221.primitiveCount := by
  exact ContextualTrace.compileConcrete_length_le collisionRoundtripTrace221

example :
    (ContextualTrace.compileConcrete collisionRoundtripTrace221).altitude ≤
      collisionRoundtripTrace221.maxStateCard + 1 := by
  exact ContextualTrace.compileConcrete_altitude_le collisionRoundtripTrace221

private theorem groundPrimitiveMove221 :
    AllModeMove NormalizedBinaryReplay221.S0 NormalizedBinaryReplay221.S1 := by
  apply BinaryAmbientMoves.Coordinate.allModeMove_iff_normalized.mpr
  exact NormalizedBinaryAllModeMove.allModeMove_of_move
    (.generatedFirstSplit NormalizedBinaryReplay221.forwardSplit)

private theorem groundPrimitiveEvaluation221 :
    BinaryAmbientCarrier.stateEvaluation NormalizedBinaryReplay221.S0 =
      BinaryAmbientCarrier.stateEvaluation NormalizedBinaryReplay221.S1 := by
  apply (coordinate_stateEvaluation_eq_iff_ambientStateEvaluation
    NormalizedBinaryReplay221.S0 NormalizedBinaryReplay221.S1).mp
  exact (NormalizedBinaryAllModeMove.AllModeMove.preserves_evaluation
    (NormalizedBinaryAllModeMove.allModeMove_of_move
      (.generatedFirstSplit NormalizedBinaryReplay221.forwardSplit))).symm

private theorem groundPrimitiveJump221 : PrimitiveJump
    NormalizedBinaryReplay221.S0 NormalizedBinaryReplay221.S1 :=
  ⟨groundPrimitiveMove221, groundPrimitiveEvaluation221⟩

example : groundPrimitiveJump221.move = groundPrimitiveMove221 := rfl

private def groundPrimitiveTrace221 : ContextualTrace
    NormalizedBinaryReplay221.S0 NormalizedBinaryReplay221.S1 :=
  .primitive (.singleton _) groundPrimitiveJump221

example : ContextualTrace.compileConcrete groundPrimitiveTrace221 =
    MovePath.one groundPrimitiveMove221 := by
  simp only [ContextualTrace.compileConcrete, groundPrimitiveTrace221,
    BinaryContextualTrace.ContextualTrace.compile]
  exact congrArg MovePath.one (Subsingleton.elim _ _)

example : (ContextualTrace.compileConcrete groundPrimitiveTrace221).length = 1 := by
  simp only [ContextualTrace.compileConcrete, groundPrimitiveTrace221,
    BinaryContextualTrace.ContextualTrace.compile, MovePath.length]

-- Executable end-to-end regression. Both directions use the same collision-
-- bearing context; expected output is `([6, 6, 7], 2, [7, 6, 6], 2)`.
#eval ((ContextualTrace.compileConcrete collisionTrace221Forward).vertices.map Finset.card,
  (ContextualTrace.compileConcrete collisionTrace221Forward).length,
  (ContextualTrace.compileConcrete collisionTrace221Reverse).vertices.map Finset.card,
  (ContextualTrace.compileConcrete collisionTrace221Reverse).length)

-- Executable compositional regression; expected output is
-- `([6, 6, 7, 6, 6], 4, 2, 0, 7, 7)`.
#eval ((ContextualTrace.compileConcrete collisionRoundtripTrace221).vertices.map Finset.card,
  (ContextualTrace.compileConcrete collisionRoundtripTrace221).length,
  collisionRoundtripTrace221.macroCount,
  collisionRoundtripTrace221.primitiveCount,
  collisionRoundtripTrace221.maxStateCard,
  (ContextualTrace.compileConcrete collisionRoundtripTrace221).altitude)

#check @compileContextualJump
#check @compileContextualJump_ambient_membership
#check @compileContextualJump_outside
#check @concreteEffectiveLocalCompiler
#check @ContextualTrace.compileConcrete
#check @ContextualTrace.compileConcrete_length
#check @ContextualTrace.compileConcrete_length_le
#check @ContextualTrace.compileConcrete_altitude_le

#print axioms compileContextualJump
#print axioms compileContextualJump_ambient_membership
#print axioms compileContextualJump_outside
#print axioms ContextualTrace.compileConcrete_length
#print axioms ContextualTrace.compileConcrete_length_le
#print axioms ContextualTrace.compileConcrete_altitude_le

end BilinearComplexity.BinaryContextualConcreteTrace
