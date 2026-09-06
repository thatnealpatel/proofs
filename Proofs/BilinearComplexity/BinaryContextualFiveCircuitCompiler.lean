import BilinearComplexity.BinaryContextualNormalizedCompiler
import BilinearComplexity.BinaryContextBorrowing221
import BilinearComplexity.BinaryAmbientContextTransport
import BilinearComplexity.BinaryFiveCircuitCompiler
import BilinearComplexity.NormalizedBinaryContextualCompiler

set_option autoImplicit false

/-!
# Effective contextual binary five-circuit compiler

This module classifies an explicitly coordinated ambient five-circuit, invokes
the uniform checked contextual row tables in both native directions, and
restores an arbitrary disjoint ambient context. The upper compiler is total,
contains no path callback or run-time basis choice, and returns concrete paths
with exact constructed length, controlled altitude, and exact outside-box
restoration.

`orbitDistance` denotes the length constructed here. The downstream module
`BinaryContextualFiveCircuitOptimality` identifies it with global ambient
shortest-path distance for these same compiler results, and
`BinaryContextualConcreteTrace` supplies the concrete trace compiler.
-/

namespace BilinearComplexity.BinaryContextualFiveCircuitCompiler

open BinaryCircuit
open BinaryAmbientCarrier
open BinaryAmbientMoves
open BinaryAmbientNormalization
open BinaryAmbientMoveTransport
open BinaryAmbientContextTransport
open BinaryAmbientCircuitModels
open BinaryContextBorrowing221
open BinaryFiveCircuitCompiler
open NormalizedBinaryCarrier
open NormalizedBinaryAllModeMove
open NormalizedBinaryOrbitClassification
open NormalizedBinaryRelationEnumeration
open BinaryContextualNormalizedCompiler
open NormalizedBinaryContextualCompiler

universe u v w

variable {U : Type u} {V : Type v} {W : Type w}
variable [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
variable [Module F2 U] [Module F2 V] [Module F2 W]
variable [DecidableEq U] [DecidableEq V] [DecidableEq W]

/-- Disjointness of an ambient context from the local support descends to the
executable normalized local context. -/
theorem normalizeLocalContext_disjoint
    {A B : BinaryAmbientCarrier.State U V W}
    (P : ExactSpanPresentation A B) (C : BinaryAmbientCarrier.State U V W)
    (hC : Disjoint C (A ∪ B)) :
    Disjoint (normalizeLocalContext P C)
      (normalizedLeft P ∪ normalizedRight P) := by
  rw [Finset.disjoint_left]
  intro t htC htEndpoints
  have hmapC : mapTerm (exactSpanCoordinateEmbedding P) t ∈ C := by
    have hmapped : mapTerm (exactSpanCoordinateEmbedding P) t ∈
        mapState (exactSpanCoordinateEmbedding P) (normalizeLocalContext P C) :=
      (mapState_mem _).2 htC
    rw [mapState_normalizeLocalContext] at hmapped
    exact (Finset.mem_inter.mp hmapped).1
  have hmapEndpoints : mapTerm (exactSpanCoordinateEmbedding P) t ∈ A ∪ B := by
    have hmapped : mapTerm (exactSpanCoordinateEmbedding P) t ∈
        mapState (exactSpanCoordinateEmbedding P)
          (normalizedLeft P ∪ normalizedRight P) :=
      (mapState_mem _).2 htEndpoints
    rw [mapState_union, mapState_normalizedLeft, mapState_normalizedRight] at hmapped
    exact hmapped
  exact Finset.disjoint_left.mp hC hmapC hmapEndpoints

/-- The outside/local split preserves the exact cardinality of the supplied
ambient context. -/
theorem outsideContext_card_add_normalizeLocalContext_card
    {A B : BinaryAmbientCarrier.State U V W}
    (P : ExactSpanPresentation A B) (C : BinaryAmbientCarrier.State U V W) :
    (outsideContext P C).card + (normalizeLocalContext P C).card = C.card := by
  rw [← mapState_card (exactSpanCoordinateEmbedding P) (normalizeLocalContext P C)]
  rw [← Finset.card_union_of_disjoint (outsideContext_disjoint_mapped P C _)]
  rw [outsideContext_union_local]

/-- The exact normalized relation associated to the supplied ambient endpoints
and explicit exact-span presentation. -/
abbrev normalizedTarget {A B : BinaryAmbientCarrier.State U V W}
    (P : ExactSpanPresentation A B)
    (hA : A.card = 2) (hB : B.card = 3) (hAB : Disjoint A B)
    (hEval : stateEvaluation A = stateEvaluation B) : ExactRelation P.profile :=
  normalizedExactRelation P hA hB hAB hEval

/-- Disjointness specialized to the endpoint projection of the exact normalized
relation used by the compiler. -/
theorem normalizedTarget_context_disjoint
    {A B : BinaryAmbientCarrier.State U V W}
    (P : ExactSpanPresentation A B)
    (hA : A.card = 2) (hB : B.card = 3) (hAB : Disjoint A B)
    (hEval : stateEvaluation A = stateEvaluation B)
    (C : BinaryAmbientCarrier.State U V W) (hC : Disjoint C (A ∪ B)) :
    Disjoint (normalizeLocalContext P C)
      ((normalizedTarget P hA hB hAB hEval).1.left ∪
        (normalizedTarget P hA hB hAB hEval).1.right) := by
  exact normalizeLocalContext_disjoint P C hC

/-- Minimal data owned by upper compilation: the classified normalized
relation.  All paths and metadata below are deterministic projections. -/
structure ContextualBinaryFiveCircuitCompilation
    {A B : BinaryAmbientCarrier.State U V W}
    (P : ExactSpanPresentation A B)
    (hA : A.card = 2) (hB : B.card = 3) (hAB : Disjoint A B)
    (hEval : stateEvaluation A = stateEvaluation B)
    (C : BinaryAmbientCarrier.State U V W) (hC : Disjoint C (A ∪ B)) where
  /-- The normalized relation together with its uniquely classified orbit. -/
  classified : ClassifiedCompilation (normalizedTarget P hA hB hAB hEval)

/-- Run the callback-free upper compiler using only explicit coordinate and
proof-bearing endpoint data. -/
def compileContextualBinaryFiveCircuit
    {A B : BinaryAmbientCarrier.State U V W}
    (P : ExactSpanPresentation A B)
    (hA : A.card = 2) (hB : B.card = 3) (hAB : Disjoint A B)
    (hEval : stateEvaluation A = stateEvaluation B)
    (C : BinaryAmbientCarrier.State U V W) (hC : Disjoint C (A ∪ B)) :
    ContextualBinaryFiveCircuitCompilation P hA hB hAB hEval C hC :=
  ⟨compileClassified (normalizedTarget P hA hB hAB hEval)⟩

/-- The semantic orbit label computed by contextual compilation. -/
abbrev ContextualBinaryFiveCircuitCompilation.label
    {A B : BinaryAmbientCarrier.State U V W}
    {P : ExactSpanPresentation A B}
    {hA : A.card = 2} {hB : B.card = 3} {hAB : Disjoint A B}
    {hEval : stateEvaluation A = stateEvaluation B}
    {C : BinaryAmbientCarrier.State U V W} {hC : Disjoint C (A ∪ B)}
    (result : ContextualBinaryFiveCircuitCompilation P hA hB hAB hEval C hC) :
    OrbitLabel :=
  result.classified.label

/-- The concrete uniform two-direction provider derived from the checked row
tables.  It is internal compiler data, not a caller-supplied callback. -/
def orbitLabelContextPathProvider (label : OrbitLabel) :
    SelectedContextPathProvider label :=
  fun K hK =>
    (orbitLabelForwardPath label K hK, orbitLabelReversePath label K hK)

/-- The forward normalized path at the recovered local context. -/
def ContextualBinaryFiveCircuitCompilation.normalizedForward
    {A B : BinaryAmbientCarrier.State U V W}
    {P : ExactSpanPresentation A B}
    {hA : A.card = 2} {hB : B.card = 3} {hAB : Disjoint A B}
    {hEval : stateEvaluation A = stateEvaluation B}
    {C : BinaryAmbientCarrier.State U V W} {hC : Disjoint C (A ∪ B)}
    (result : ContextualBinaryFiveCircuitCompilation P hA hB hAB hEval C hC) :
    MovePath (@NormalizedBinaryAllModeMove.AllModeMove P.profile)
      (normalizeLocalContext P C ∪ normalizedLeft P)
      (normalizeLocalContext P C ∪ normalizedRight P) :=
  compileOriginalContextForwardPath result.classified
    (normalizeLocalContext P C)
    (normalizedTarget_context_disjoint P hA hB hAB hEval C hC)
    (orbitLabelContextPathProvider result.classified.label)

/-- The reverse normalized path is separately compiled in its native directed
move relation. -/
def ContextualBinaryFiveCircuitCompilation.normalizedReverse
    {A B : BinaryAmbientCarrier.State U V W}
    {P : ExactSpanPresentation A B}
    {hA : A.card = 2} {hB : B.card = 3} {hAB : Disjoint A B}
    {hEval : stateEvaluation A = stateEvaluation B}
    {C : BinaryAmbientCarrier.State U V W} {hC : Disjoint C (A ∪ B)}
    (result : ContextualBinaryFiveCircuitCompilation P hA hB hAB hEval C hC) :
    MovePath (@NormalizedBinaryAllModeMove.AllModeMove P.profile)
      (normalizeLocalContext P C ∪ normalizedRight P)
      (normalizeLocalContext P C ∪ normalizedLeft P) :=
  compileOriginalContextReversePath result.classified
    (normalizeLocalContext P C)
    (normalizedTarget_context_disjoint P hA hB hAB hEval C hC)
    (orbitLabelContextPathProvider result.classified.label)

/-- Restore the ambient context around the compiled forward path. -/
def ContextualBinaryFiveCircuitCompilation.forward
    {A B : BinaryAmbientCarrier.State U V W}
    {P : ExactSpanPresentation A B}
    {hA : A.card = 2} {hB : B.card = 3} {hAB : Disjoint A B}
    {hEval : stateEvaluation A = stateEvaluation B}
    {C : BinaryAmbientCarrier.State U V W} {hC : Disjoint C (A ∪ B)}
    (result : ContextualBinaryFiveCircuitCompilation P hA hB hAB hEval C hC) :
    MovePath (BinaryAmbientMoves.AllModeMove (U := U) (V := V) (W := W))
      (C ∪ A) (C ∪ B) :=
  mapPathInContextEndpoints P C result.normalizedForward rfl rfl

/-- Restore the ambient context around the separately compiled reverse path. -/
def ContextualBinaryFiveCircuitCompilation.reverse
    {A B : BinaryAmbientCarrier.State U V W}
    {P : ExactSpanPresentation A B}
    {hA : A.card = 2} {hB : B.card = 3} {hAB : Disjoint A B}
    {hEval : stateEvaluation A = stateEvaluation B}
    {C : BinaryAmbientCarrier.State U V W} {hC : Disjoint C (A ∪ B)}
    (result : ContextualBinaryFiveCircuitCompilation P hA hB hAB hEval C hC) :
    MovePath (BinaryAmbientMoves.AllModeMove (U := U) (V := V) (W := W))
      (C ∪ B) (C ∪ A) :=
  mapPathInContextEndpointsReverse P C result.normalizedReverse rfl rfl

/-- The computed label semantically contains the original ambient endpoint
pair, independently of the context. -/
theorem ContextualBinaryFiveCircuitCompilation.ambient_membership
    {A B : BinaryAmbientCarrier.State U V W}
    {P : ExactSpanPresentation A B}
    {hA : A.card = 2} {hB : B.card = 3} {hAB : Disjoint A B}
    {hEval : stateEvaluation A = stateEvaluation B}
    {C : BinaryAmbientCarrier.State U V W} {hC : Disjoint C (A ∪ B)}
    (result : ContextualBinaryFiveCircuitCompilation P hA hB hAB hEval C hC) :
    AmbientInOrbit result.label A B := by
  exact ⟨P, result.classified.membership⟩

/-- The normalized forward path has exactly the canonical constructed length. -/
@[simp] theorem ContextualBinaryFiveCircuitCompilation.normalizedForward_length
    {A B : BinaryAmbientCarrier.State U V W}
    {P : ExactSpanPresentation A B}
    {hA : A.card = 2} {hB : B.card = 3} {hAB : Disjoint A B}
    {hEval : stateEvaluation A = stateEvaluation B}
    {C : BinaryAmbientCarrier.State U V W} {hC : Disjoint C (A ∪ B)}
    (result : ContextualBinaryFiveCircuitCompilation P hA hB hAB hEval C hC) :
    result.normalizedForward.length = orbitDistance result.label := by
  have hpreservation := compileOriginalContextForwardPath_length result.classified
    (normalizeLocalContext P C)
    (normalizedTarget_context_disjoint P hA hB hAB hEval C hC)
    (orbitLabelContextPathProvider result.classified.label)
  calc
    result.normalizedForward.length =
        (selectedLocalForwardPath result.classified (normalizeLocalContext P C)
          (normalizedTarget_context_disjoint P hA hB hAB hEval C hC)
          (orbitLabelContextPathProvider result.classified.label)).length := by
      convert hpreservation using 1
      rfl
    _ = orbitDistance result.label := by
      convert orbitLabelForwardPath_length result.classified.label
        (compilationLocalContext result.classified (normalizeLocalContext P C))
        (compilationLocalContext_disjoint result.classified
          (normalizedTarget_context_disjoint P hA hB hAB hEval C hC)) using 1; rfl

/-- The normalized reverse path has exactly the canonical constructed length. -/
@[simp] theorem ContextualBinaryFiveCircuitCompilation.normalizedReverse_length
    {A B : BinaryAmbientCarrier.State U V W}
    {P : ExactSpanPresentation A B}
    {hA : A.card = 2} {hB : B.card = 3} {hAB : Disjoint A B}
    {hEval : stateEvaluation A = stateEvaluation B}
    {C : BinaryAmbientCarrier.State U V W} {hC : Disjoint C (A ∪ B)}
    (result : ContextualBinaryFiveCircuitCompilation P hA hB hAB hEval C hC) :
    result.normalizedReverse.length = orbitDistance result.label := by
  have hpreservation := compileOriginalContextReversePath_length result.classified
    (normalizeLocalContext P C)
    (normalizedTarget_context_disjoint P hA hB hAB hEval C hC)
    (orbitLabelContextPathProvider result.classified.label)
  calc
    result.normalizedReverse.length =
        (selectedLocalReversePath result.classified (normalizeLocalContext P C)
          (normalizedTarget_context_disjoint P hA hB hAB hEval C hC)
          (orbitLabelContextPathProvider result.classified.label)).length := by
      convert hpreservation using 1
      rfl
    _ = orbitDistance result.label := by
      convert orbitLabelReversePath_length result.classified.label
        (compilationLocalContext result.classified (normalizeLocalContext P C))
        (compilationLocalContext_disjoint result.classified
          (normalizedTarget_context_disjoint P hA hB hAB hEval C hC)) using 1; rfl

/-- The normalized forward path rises by at most four terms above its recovered
local context. -/
theorem ContextualBinaryFiveCircuitCompilation.normalizedForward_altitude_le
    {A B : BinaryAmbientCarrier.State U V W}
    {P : ExactSpanPresentation A B}
    {hA : A.card = 2} {hB : B.card = 3} {hAB : Disjoint A B}
    {hEval : stateEvaluation A = stateEvaluation B}
    {C : BinaryAmbientCarrier.State U V W} {hC : Disjoint C (A ∪ B)}
    (result : ContextualBinaryFiveCircuitCompilation P hA hB hAB hEval C hC) :
    result.normalizedForward.altitude ≤ (normalizeLocalContext P C).card + 4 := by
  have hpreservation := compileOriginalContextForwardPath_altitude result.classified
    (normalizeLocalContext P C)
    (normalizedTarget_context_disjoint P hA hB hAB hEval C hC)
    (orbitLabelContextPathProvider result.classified.label)
  calc
    result.normalizedForward.altitude =
        (selectedLocalForwardPath result.classified (normalizeLocalContext P C)
          (normalizedTarget_context_disjoint P hA hB hAB hEval C hC)
          (orbitLabelContextPathProvider result.classified.label)).altitude := by
      convert hpreservation using 1
      rfl
    _ ≤ (normalizeLocalContext P C).card + 4 := by
      have haltitude :=
        orbitLabelForwardPath_altitude_le result.classified.label
          (compilationLocalContext result.classified (normalizeLocalContext P C))
          (compilationLocalContext_disjoint result.classified
            (normalizedTarget_context_disjoint P hA hB hAB hEval C hC))
      convert haltitude using 1 <;>
        first | rfl | exact (compilationLocalContext_card result.classified
          (normalizeLocalContext P C)) | exact (congrArg (fun n => n + 4)
          (compilationLocalContext_card result.classified
            (normalizeLocalContext P C)).symm)

/-- The normalized reverse path rises by at most four terms above its recovered
local context. -/
theorem ContextualBinaryFiveCircuitCompilation.normalizedReverse_altitude_le
    {A B : BinaryAmbientCarrier.State U V W}
    {P : ExactSpanPresentation A B}
    {hA : A.card = 2} {hB : B.card = 3} {hAB : Disjoint A B}
    {hEval : stateEvaluation A = stateEvaluation B}
    {C : BinaryAmbientCarrier.State U V W} {hC : Disjoint C (A ∪ B)}
    (result : ContextualBinaryFiveCircuitCompilation P hA hB hAB hEval C hC) :
    result.normalizedReverse.altitude ≤ (normalizeLocalContext P C).card + 4 := by
  have hpreservation := compileOriginalContextReversePath_altitude result.classified
    (normalizeLocalContext P C)
    (normalizedTarget_context_disjoint P hA hB hAB hEval C hC)
    (orbitLabelContextPathProvider result.classified.label)
  calc
    result.normalizedReverse.altitude =
        (selectedLocalReversePath result.classified (normalizeLocalContext P C)
          (normalizedTarget_context_disjoint P hA hB hAB hEval C hC)
          (orbitLabelContextPathProvider result.classified.label)).altitude := by
      convert hpreservation using 1
      rfl
    _ ≤ (normalizeLocalContext P C).card + 4 := by
      have haltitude :=
        orbitLabelReversePath_altitude_le result.classified.label
          (compilationLocalContext result.classified (normalizeLocalContext P C))
          (compilationLocalContext_disjoint result.classified
            (normalizedTarget_context_disjoint P hA hB hAB hEval C hC))
      convert haltitude using 1 <;>
        first | rfl | exact (compilationLocalContext_card result.classified
          (normalizeLocalContext P C)) | exact (congrArg (fun n => n + 4)
          (compilationLocalContext_card result.classified
            (normalizeLocalContext P C)).symm)

/-- The restored ambient forward path has exactly the canonical constructed length. -/
@[simp] theorem ContextualBinaryFiveCircuitCompilation.forward_length
    {A B : BinaryAmbientCarrier.State U V W}
    {P : ExactSpanPresentation A B}
    {hA : A.card = 2} {hB : B.card = 3} {hAB : Disjoint A B}
    {hEval : stateEvaluation A = stateEvaluation B}
    {C : BinaryAmbientCarrier.State U V W} {hC : Disjoint C (A ∪ B)}
    (result : ContextualBinaryFiveCircuitCompilation P hA hB hAB hEval C hC) :
    result.forward.length = orbitDistance result.label := by
  rw [ContextualBinaryFiveCircuitCompilation.forward,
    mapPathInContextEndpoints_length, result.normalizedForward_length]

/-- The restored ambient reverse path has exactly the canonical constructed length. -/
@[simp] theorem ContextualBinaryFiveCircuitCompilation.reverse_length
    {A B : BinaryAmbientCarrier.State U V W}
    {P : ExactSpanPresentation A B}
    {hA : A.card = 2} {hB : B.card = 3} {hAB : Disjoint A B}
    {hEval : stateEvaluation A = stateEvaluation B}
    {C : BinaryAmbientCarrier.State U V W} {hC : Disjoint C (A ∪ B)}
    (result : ContextualBinaryFiveCircuitCompilation P hA hB hAB hEval C hC) :
    result.reverse.length = orbitDistance result.label := by
  rw [ContextualBinaryFiveCircuitCompilation.reverse,
    mapPathInContextEndpointsReverse_length, result.normalizedReverse_length]

/-- The restored ambient forward path has altitude at most the full ambient
context size plus four. -/
theorem ContextualBinaryFiveCircuitCompilation.forward_altitude_le
    {A B : BinaryAmbientCarrier.State U V W}
    {P : ExactSpanPresentation A B}
    {hA : A.card = 2} {hB : B.card = 3} {hAB : Disjoint A B}
    {hEval : stateEvaluation A = stateEvaluation B}
    {C : BinaryAmbientCarrier.State U V W} {hC : Disjoint C (A ∪ B)}
    (result : ContextualBinaryFiveCircuitCompilation P hA hB hAB hEval C hC) :
    result.forward.altitude ≤ C.card + 4 := by
  rw [ContextualBinaryFiveCircuitCompilation.forward,
    mapPathInContextEndpoints_altitude]
  have hlocal := result.normalizedForward_altitude_le
  have hcard := outsideContext_card_add_normalizeLocalContext_card P C
  omega

/-- The restored ambient reverse path has altitude at most the full ambient
context size plus four. -/
theorem ContextualBinaryFiveCircuitCompilation.reverse_altitude_le
    {A B : BinaryAmbientCarrier.State U V W}
    {P : ExactSpanPresentation A B}
    {hA : A.card = 2} {hB : B.card = 3} {hAB : Disjoint A B}
    {hEval : stateEvaluation A = stateEvaluation B}
    {C : BinaryAmbientCarrier.State U V W} {hC : Disjoint C (A ∪ B)}
    (result : ContextualBinaryFiveCircuitCompilation P hA hB hAB hEval C hC) :
    result.reverse.altitude ≤ C.card + 4 := by
  rw [ContextualBinaryFiveCircuitCompilation.reverse,
    mapPathInContextEndpointsReverse_altitude]
  have hlocal := result.normalizedReverse_altitude_le
  have hcard := outsideContext_card_add_normalizeLocalContext_card P C
  omega

/-- Every forward path vertex restores exactly the supplied context outside the
endpoint-generated coordinate box. -/
theorem ContextualBinaryFiveCircuitCompilation.forward_outside
    {A B : BinaryAmbientCarrier.State U V W}
    {P : ExactSpanPresentation A B}
    {hA : A.card = 2} {hB : B.card = 3} {hAB : Disjoint A B}
    {hEval : stateEvaluation A = stateEvaluation B}
    {C : BinaryAmbientCarrier.State U V W} {hC : Disjoint C (A ∪ B)}
    (result : ContextualBinaryFiveCircuitCompilation P hA hB hAB hEval C hC)
    {Y : BinaryAmbientCarrier.State U V W} (hY : PathVertex result.forward Y) :
    Y \ localBox P = outsideContext P C := by
  exact mapPathInContextEndpoints_outside P C result.normalizedForward rfl rfl hY

/-- Every reverse path vertex restores exactly the supplied context outside the
endpoint-generated coordinate box. -/
theorem ContextualBinaryFiveCircuitCompilation.reverse_outside
    {A B : BinaryAmbientCarrier.State U V W}
    {P : ExactSpanPresentation A B}
    {hA : A.card = 2} {hB : B.card = 3} {hAB : Disjoint A B}
    {hEval : stateEvaluation A = stateEvaluation B}
    {C : BinaryAmbientCarrier.State U V W} {hC : Disjoint C (A ∪ B)}
    (result : ContextualBinaryFiveCircuitCompilation P hA hB hAB hEval C hC)
    {Y : BinaryAmbientCarrier.State U V W} (hY : PathVertex result.reverse Y) :
    Y \ localBox P = outsideContext P C := by
  exact mapPathInContextEndpointsReverse_outside P C result.normalizedReverse rfl rfl hY

/-- The compiler-owned constructed length is always exactly two or exactly three. -/
theorem ContextualBinaryFiveCircuitCompilation.distance_two_or_three
    {A B : BinaryAmbientCarrier.State U V W}
    {P : ExactSpanPresentation A B}
    {hA : A.card = 2} {hB : B.card = 3} {hAB : Disjoint A B}
    {hEval : stateEvaluation A = stateEvaluation B}
    {C : BinaryAmbientCarrier.State U V W} {hC : Disjoint C (A ∪ B)}
    (result : ContextualBinaryFiveCircuitCompilation P hA hB hAB hEval C hC) :
    orbitDistance result.label = 2 ∨ orbitDistance result.label = 3 :=
  orbitDistance_two_or_three result.label

/-- The selected profile-`221` label used by the end-to-end collision
regression. -/
private abbrev groundLabel221 : OrbitLabel :=
  ⟨.family221, (0 : Fin 3)⟩

/-- The exact normalized relation selected by the ground label. -/
private abbrev groundTarget221 : ExactRelation profile221 :=
  groundLabel221.selectedExactRelation

/-- A choice-free identity presentation of the ground relation in its finite
coordinate spaces. -/
private def groundPresentation221 :
    ExactSpanPresentation groundTarget221.1.left groundTarget221.1.right :=
  coordinateExactSpanPresentation groundTarget221

/-- The ground presentation normalizes its left endpoint to the original
finite coordinate endpoint. -/
example : normalizedLeft groundPresentation221 = groundTarget221.1.left := by
  exact normalizedLeft_coordinateExactSpanPresentation groundTarget221

/-- The normalized equality of evaluations is also an equality for the
intrinsic ambient tensor evaluation. -/
private theorem groundEvaluation221 :
    BinaryAmbientCarrier.stateEvaluation groundTarget221.1.left =
      BinaryAmbientCarrier.stateEvaluation groundTarget221.1.right := by
  exact (coordinate_stateEvaluation_eq_iff_ambientStateEvaluation
    groundTarget221.1.left groundTarget221.1.right).mp
      groundTarget221.2.2.2.2.1

/-- The finite borrowing context is jointly disjoint from both ground
endpoints. -/
private theorem groundContextDisjoint221 :
    Disjoint contextC (groundTarget221.1.left ∪ groundTarget221.1.right) := by
  decide

/-- The end-to-end ground execution calls the public contextual compiler with
an explicit choice-free presentation and the collision-bearing finite context. -/
private def groundCompilation221 :=
  compileContextualBinaryFiveCircuit groundPresentation221
    groundTarget221.2.1 groundTarget221.2.2.1
    groundTarget221.2.2.2.1 groundEvaluation221 contextC
    groundContextDisjoint221

/-- The ground forward result has the exact ambient source and target indices. -/
example :
    MovePath BinaryAmbientMoves.AllModeMove
      (contextC ∪ groundTarget221.1.left)
      (contextC ∪ groundTarget221.1.right) :=
  groundCompilation221.forward

/-- The separately compiled ground reverse result has reversed exact ambient
source and target indices. -/
example :
    MovePath BinaryAmbientMoves.AllModeMove
      (contextC ∪ groundTarget221.1.right)
      (contextC ∪ groundTarget221.1.left) :=
  groundCompilation221.reverse

/-- The end-to-end ambient forward path has exact constructed length two. -/
private theorem groundCompilation221_forward_length :
    groundCompilation221.forward.length = 2 := by
  rw [ContextualBinaryFiveCircuitCompilation.forward_length]
  decide

/-- The independently compiled ambient reverse path has exact constructed
length two. -/
private theorem groundCompilation221_reverse_length :
    groundCompilation221.reverse.length = 2 := by
  rw [ContextualBinaryFiveCircuitCompilation.reverse_length]
  decide

-- End-to-end runtime regression. The public compiler performs classification,
-- local-context recovery, separate directed path compilation, and ambient
-- context restoration. The output consists of forward vertex cardinalities
-- and length followed by reverse vertex cardinalities and length:
-- `([6, 6, 7], 2, [7, 6, 6], 2)`.
#eval (groundCompilation221.forward.vertices.map Finset.card,
  groundCompilation221.forward.length,
  groundCompilation221.reverse.vertices.map Finset.card,
  groundCompilation221.reverse.length)

#check @compileContextualBinaryFiveCircuit
#check @ContextualBinaryFiveCircuitCompilation.forward
#check @ContextualBinaryFiveCircuitCompilation.reverse

#print axioms groundCompilation221_forward_length
#print axioms groundCompilation221_reverse_length
#print axioms compileContextualBinaryFiveCircuit
#print axioms ContextualBinaryFiveCircuitCompilation.ambient_membership
#print axioms ContextualBinaryFiveCircuitCompilation.forward_length
#print axioms ContextualBinaryFiveCircuitCompilation.reverse_length
#print axioms ContextualBinaryFiveCircuitCompilation.forward_altitude_le
#print axioms ContextualBinaryFiveCircuitCompilation.reverse_altitude_le
#print axioms ContextualBinaryFiveCircuitCompilation.forward_outside
#print axioms ContextualBinaryFiveCircuitCompilation.reverse_outside
#print axioms ContextualBinaryFiveCircuitCompilation.distance_two_or_three

end BilinearComplexity.BinaryContextualFiveCircuitCompiler
