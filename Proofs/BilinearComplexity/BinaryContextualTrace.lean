import BilinearComplexity.BinaryAmbientCircuitModels

set_option autoImplicit false

/-!
# Contextual traces for intrinsic binary ambient moves

This module defines data-bearing traces whose primitive steps retain native
`BinaryAmbientMoves.AllModeMove` witnesses and whose contextual steps retain
the complete local five-circuit payload. A separate `EffectiveLocalCompiler`
parameter turns each contextual jump into an exact intrinsic path.

The local compilation result owns its computed distance; a caller cannot
request or prescribe a distance. Its orbit-label field is compiler-supplied,
unverified metadata at this generic interface: no field relates that label to
the jump's endpoints or presentation. The concrete adapter in
`BinaryContextualConcreteTrace` separately certifies orbit identity and supplies
a total local compiler. Consequently `ContextualTrace.macroDistanceSum` here
depends on the supplied compiler. This module proves the generic path length,
altitude, and endpoint-evaluation contracts; the concrete module exports the
callback-free specialization.

AI disclosure: produced with AI assistance (see `README`).
-/

namespace BilinearComplexity.BinaryContextualTrace

open BinaryCircuit
open BinaryAmbientCarrier
open BinaryAmbientMoves
open BinaryAmbientNormalization
open NormalizedBinaryCarrier (F2)
open NormalizedBinaryOrbitClassification

universe u v w

variable {U : Type u} {V : Type v} {W : Type w}
variable [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
variable [Module F2 U] [Module F2 V] [Module F2 W]
variable [DecidableEq U] [DecidableEq V] [DecidableEq W]

/-- An intrinsic ambient state, abbreviated for contextual-trace signatures. -/
abbrev AmbientState (U : Type u) (V : Type v) (W : Type w)
    [Zero U] [Zero V] [Zero W] := BinaryAmbientCarrier.State U V W

/-- The orientation in which a two-versus-three five-circuit macro is used. -/
inductive MacroDirection
  | forward
  | reverse
  deriving DecidableEq

namespace MacroDirection

/-- Select the source endpoint according to a macro direction. -/
def source (direction : MacroDirection) (A B : AmbientState U V W) : AmbientState U V W :=
  match direction with
  | .forward => A
  | .reverse => B

/-- Select the target endpoint according to a macro direction. -/
def target (direction : MacroDirection) (A B : AmbientState U V W) : AmbientState U V W :=
  match direction with
  | .forward => B
  | .reverse => A

example (A B : AmbientState U V W) : MacroDirection.forward.source A B = A := rfl

example (A B : AmbientState U V W) : MacroDirection.reverse.source A B = B := rfl

example (A B : AmbientState U V W) : MacroDirection.forward.target A B = B := rfl

example (A B : AmbientState U V W) : MacroDirection.reverse.target A B = A := rfl

end MacroDirection

/-- A directed contextual five-circuit jump with exact context-restored
boundaries and all proof-bearing data needed by a later effective compiler. -/
structure ContextualFiveCircuitJump (D E : AmbientState U V W) where
  /-- The unchanged surrounding state. -/
  context : AmbientState U V W
  /-- The two-term local endpoint. -/
  left : AmbientState U V W
  /-- The three-term local endpoint. -/
  right : AmbientState U V W
  /-- The direction in which the local relation is traversed. -/
  direction : MacroDirection
  /-- The left local endpoint has two terms. -/
  left_card : left.card = 2
  /-- The right local endpoint has three terms. -/
  right_card : right.card = 3
  /-- The local endpoints are disjoint. -/
  endpoints_disjoint : Disjoint left right
  /-- The context is disjoint from the entire local support. -/
  context_disjoint : Disjoint context (left ∪ right)
  /-- The local endpoints have equal ambient tensor evaluation. -/
  endpoint_evaluation : stateEvaluation left = stateEvaluation right
  /-- The five-term local support is a circuit. -/
  support_circuit : Circuit tensorEvaluation (left ∪ right)
  /-- Effective exact-span coordinates for the local endpoints. -/
  presentation : ExactSpanPresentation left right
  /-- The trace source is exactly the context union the directed source. -/
  start_eq : D = context ∪ direction.source left right
  /-- The trace target is exactly the context union the directed target. -/
  finish_eq : E = context ∪ direction.target left right

/-! The selected normalized row below jointly witnesses satisfiability of every
field of `ContextualFiveCircuitJump`; in particular, its circuit and exact-span
presentation are independent proof-bearing data rather than assumptions made
by this module. -/

example : Nonempty (ContextualFiveCircuitJump
    BinaryAmbientCircuitModels.row41101AbstractModel.left
    BinaryAmbientCircuitModels.row41101AbstractModel.right) := by
  refine ⟨{
    context := ∅
    left := BinaryAmbientCircuitModels.row41101AbstractModel.left
    right := BinaryAmbientCircuitModels.row41101AbstractModel.right
    direction := .forward
    left_card := BinaryAmbientCircuitModels.row41101AbstractModel.card_left
    right_card := BinaryAmbientCircuitModels.row41101AbstractModel.card_right
    endpoints_disjoint := BinaryAmbientCircuitModels.row41101AbstractModel.disjoint
    context_disjoint := Finset.disjoint_empty_left _
    endpoint_evaluation :=
      BinaryAmbientCircuitModels.row41101AbstractModel.abstract_tensor_eq
    support_circuit :=
      BinaryAmbientCircuitModels.row41101AbstractModel.abstract_circuit
    presentation := ?_
    start_eq := by simp only [MacroDirection.source, Finset.empty_union]
    finish_eq := by simp only [MacroDirection.target, Finset.empty_union] }⟩
  simpa only [BinaryAmbientCircuitModels.row41101AbstractModel,
      BinaryAmbientCircuitModels.exactRelationAbstractModel] using
    BinaryAmbientCircuitModels.coordinateExactSpanPresentation
      BinaryAmbientCircuitModels.row41101ExactRelation

namespace ContextualFiveCircuitJump

/-- The larger exact boundary contains the context and all three terms of
the larger local endpoint. -/
theorem context_card_add_three_le_boundaryMax {D E : AmbientState U V W}
    (jump : ContextualFiveCircuitJump D E) :
    jump.context.card + 3 ≤ max D.card E.card := by
  have hContextRight : Disjoint jump.context jump.right :=
    Disjoint.mono_right Finset.subset_union_right jump.context_disjoint
  cases hDirection : jump.direction with
  | forward =>
      have hEndpointCard : E.card = (jump.context ∪ jump.right).card := by
        simpa only [hDirection, MacroDirection.target] using
          congrArg Finset.card jump.finish_eq
      have hECard : E.card = jump.context.card + 3 := by
        calc
          E.card = (jump.context ∪ jump.right).card := hEndpointCard
          _ = jump.context.card + jump.right.card :=
            Finset.card_union_of_disjoint hContextRight
          _ = jump.context.card + 3 := by rw [jump.right_card]
      rw [← hECard]
      exact Nat.le_max_right _ _
  | reverse =>
      have hEndpointCard : D.card = (jump.context ∪ jump.right).card := by
        simpa only [hDirection, MacroDirection.source] using
          congrArg Finset.card jump.start_eq
      have hDCard : D.card = jump.context.card + 3 := by
        calc
          D.card = (jump.context ∪ jump.right).card := hEndpointCard
          _ = jump.context.card + jump.right.card :=
            Finset.card_union_of_disjoint hContextRight
          _ = jump.context.card + 3 := by rw [jump.right_card]
      rw [← hDCard]
      exact Nat.le_max_left _ _

/-- A raw contextual jump restores its supplied context and preserves ambient
evaluation at its exact macro boundary. -/
theorem preserves_evaluation {D E : AmbientState U V W}
    (jump : ContextualFiveCircuitJump D E) :
    stateEvaluation D = stateEvaluation E := by
  have hStart : stateEvaluation D = stateEvaluation
      (jump.context ∪ jump.direction.source jump.left jump.right) :=
    congrArg stateEvaluation jump.start_eq
  have hFinish : stateEvaluation
      (jump.context ∪ jump.direction.target jump.left jump.right) =
      stateEvaluation E :=
    (congrArg stateEvaluation jump.finish_eq).symm
  have hContextLeft : Disjoint jump.context jump.left :=
    Disjoint.mono_right Finset.subset_union_left jump.context_disjoint
  have hContextRight : Disjoint jump.context jump.right :=
    Disjoint.mono_right Finset.subset_union_right jump.context_disjoint
  calc
    stateEvaluation D = stateEvaluation
        (jump.context ∪ jump.direction.source jump.left jump.right) := hStart
    _ = stateEvaluation
        (jump.context ∪ jump.direction.target jump.left jump.right) := by
      cases jump.direction <;>
        simp only [MacroDirection.source, MacroDirection.target,
          stateEvaluation_union hContextLeft,
          stateEvaluation_union hContextRight, jump.endpoint_evaluation]
    _ = stateEvaluation E := hFinish

end ContextualFiveCircuitJump

/-- A primitive trace step retaining its native intrinsic move witness and
its endpoint-evaluation certificate. -/
structure PrimitiveJump (D E : AmbientState U V W) where
  /-- The native intrinsic ambient move. -/
  move : BinaryAmbientMoves.AllModeMove D E
  /-- The primitive move's endpoint-evaluation certificate. -/
  endpoint_evaluation : stateEvaluation D = stateEvaluation E

/-- The result owned by a local macro compiler: unverified orbit-label metadata,
a computed two-or-three intrinsic distance, an exact path, its altitude bound,
and local shortestness. No requested distance is an input to this structure.
The path and shortestness fields certify distance, but do not certify the
orbit-label metadata against the jump. -/
structure MacroCompilation {D E : AmbientState U V W}
    (jump : ContextualFiveCircuitJump D E) where
  /-- Compiler-supplied orbit-label metadata, not related to the jump by this
  generic structure. A concrete compiler must separately prove its identity. -/
  orbit : OrbitLabel
  /-- The compiler-computed local intrinsic distance. -/
  distance : ℕ
  /-- The computed distance is exactly two or three. -/
  distance_two_or_three : distance = 2 ∨ distance = 3
  /-- The exact-endpoint intrinsic ambient path produced by compilation. -/
  path : MovePath BinaryAmbientMoves.AllModeMove D E
  /-- The produced path realizes the computed distance exactly. -/
  path_length : path.length = distance
  /-- The local path rises at most one term above the three-term boundary. -/
  altitude_le : path.altitude ≤ jump.context.card + 4
  /-- No intrinsic ambient competitor is shorter than the computed distance. -/
  shortest : ∀ competitor : MovePath BinaryAmbientMoves.AllModeMove D E,
    distance ≤ competitor.length

namespace MacroCompilation

/-- The local macro altitude is at most one above its larger boundary. -/
theorem altitude_le_boundaryMax_add_one {D E : AmbientState U V W}
    {jump : ContextualFiveCircuitJump D E} (compilation : MacroCompilation jump) :
    compilation.path.altitude ≤ max D.card E.card + 1 := by
  have hBoundary := jump.context_card_add_three_le_boundaryMax
  have hAltitude := compilation.altitude_le
  omega

end MacroCompilation

/-- A total effective local compiler for every proof-bearing contextual
five-circuit jump. This parameter is intentionally not constructed here. -/
abbrev EffectiveLocalCompiler (U : Type u) (V : Type v) (W : Type w)
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    [DecidableEq U] [DecidableEq V] [DecidableEq W] :=
  ∀ {D E : AmbientState U V W} (jump : ContextualFiveCircuitJump D E),
    MacroCompilation jump

/-- A finite trace from one ambient state to another, built from primitive
intrinsic moves and proof-bearing contextual five-circuit jumps. -/
inductive ContextualTrace : AmbientState U V W → AmbientState U V W → Type (max u v w)
  /-- The zero-step trace at one state. -/
  | singleton (D : AmbientState U V W) : ContextualTrace D D
  /-- Append one native intrinsic primitive move. -/
  | primitive {D E F : AmbientState U V W} : ContextualTrace D E →
      PrimitiveJump E F → ContextualTrace D F
  /-- Append one proof-bearing contextual five-circuit macro. -/
  | contextual {D E F : AmbientState U V W} : ContextualTrace D E →
      ContextualFiveCircuitJump E F → ContextualTrace D F

namespace ContextualTrace

/-- Count the primitive steps in a contextual trace. -/
def primitiveCount {D E : AmbientState U V W} : ContextualTrace D E → ℕ
  | .singleton _ => 0
  | .primitive trace _ => trace.primitiveCount + 1
  | .contextual trace _ => trace.primitiveCount

/-- Count the contextual macro steps in a contextual trace. -/
def macroCount {D E : AmbientState U V W} : ContextualTrace D E → ℕ
  | .singleton _ => 0
  | .primitive trace _ => trace.macroCount
  | .contextual trace _ => trace.macroCount + 1

/-- The maximum cardinality among all explicit boundary states of a trace. -/
def maxStateCard : {D E : AmbientState U V W} → ContextualTrace D E → ℕ
  | _, _, .singleton X => X.card
  | _, F, .primitive trace _ => max trace.maxStateCard F.card
  | _, F, .contextual trace _ => max trace.maxStateCard F.card

/-- Sum the compiler-owned computed distances of all contextual macro steps.
This quantity is compiler-dependent and takes no caller-requested distance. -/
def macroDistanceSum (compiler : EffectiveLocalCompiler U V W) :
    {D E : AmbientState U V W} → ContextualTrace D E → ℕ
  | _, _, .singleton _ => 0
  | _, _, .primitive trace _ => trace.macroDistanceSum compiler
  | _, _, .contextual trace jump =>
      trace.macroDistanceSum compiler + (compiler jump).distance

/-- The exact intended compiled length: primitive count plus the sum of
compiler-owned macro distances. -/
def constructedLength (compiler : EffectiveLocalCompiler U V W)
    {D E : AmbientState U V W} (trace : ContextualTrace D E) : ℕ :=
  trace.primitiveCount + trace.macroDistanceSum compiler

/-- Compile a contextual trace by retaining primitive edges and concatenating
the exact paths returned by the supplied total local compiler. -/
def compile (compiler : EffectiveLocalCompiler U V W) :
    {D E : AmbientState U V W} → ContextualTrace D E →
      MovePath BinaryAmbientMoves.AllModeMove D E
  | _, _, .singleton X => .singleton X
  | _, _, .primitive trace jump => .snoc (compile compiler trace) jump.move
  | _, _, .contextual trace jump =>
      (compile compiler trace).trans (compiler jump).path

example (X : AmbientState U V W) :
    (ContextualTrace.singleton X).primitiveCount = 0 := rfl

example (X : AmbientState U V W) :
    (ContextualTrace.singleton X).macroCount = 0 := rfl

example :
    (ContextualTrace.singleton (∅ : AmbientState U V W)).maxStateCard = 0 := by
  simp only [maxStateCard, Finset.card_empty]

example (compiler : EffectiveLocalCompiler U V W) (X : AmbientState U V W) :
    (ContextualTrace.singleton X).macroDistanceSum compiler = 0 := by
  simp only [macroDistanceSum]

example (compiler : EffectiveLocalCompiler U V W) (X : AmbientState U V W) :
    (ContextualTrace.singleton X).constructedLength compiler = 0 := by
  simp only [constructedLength, primitiveCount, macroDistanceSum]

example (compiler : EffectiveLocalCompiler U V W) (X : AmbientState U V W) :
    (ContextualTrace.singleton X).compile compiler = MovePath.singleton X := by
  simp only [compile]

example {D E : AmbientState U V W} (jump : PrimitiveJump D E) :
    (ContextualTrace.primitive (ContextualTrace.singleton D) jump).primitiveCount = 1 := rfl

example {D E : AmbientState U V W} (jump : PrimitiveJump D E) :
    (ContextualTrace.primitive (ContextualTrace.singleton D) jump).macroCount = 0 := rfl

example {D E : AmbientState U V W} (compiler : EffectiveLocalCompiler U V W)
    (jump : PrimitiveJump D E) :
    (ContextualTrace.primitive (ContextualTrace.singleton D) jump).compile compiler =
      MovePath.snoc (MovePath.singleton D) jump.move := by
  simp only [compile]

end ContextualTrace

namespace MovePath

omit [Module F2 U] [Module F2 V] [Module F2 W]
    [DecidableEq U] [DecidableEq V] [DecidableEq W] in
/-- Every move path's final-state cardinality is bounded by its altitude. -/
theorem end_card_le_altitude {R : AmbientState U V W → AmbientState U V W → Prop} {D E : AmbientState U V W}
    (path : MovePath R D E) : E.card ≤ path.altitude := by
  cases path with
  | singleton =>
      simp only [MovePath.altitude]
      apply Nat.le_refl
  | snoc path edge =>
      simp only [MovePath.altitude]
      apply Nat.le_max_right

omit [Module F2 U] [Module F2 V] [Module F2 W]
    [DecidableEq U] [DecidableEq V] [DecidableEq W] in
/-- Concatenating move paths adds their edge lengths. -/
theorem trans_length {R : AmbientState U V W → AmbientState U V W → Prop} {D E F : AmbientState U V W}
    (path : MovePath R D E) (tail : MovePath R E F) :
    (path.trans tail).length = path.length + tail.length := by
  induction tail with
  | singleton => simp only [MovePath.trans, MovePath.length, Nat.add_zero]
  | snoc tail _ ih =>
      simp only [MovePath.trans, MovePath.length]
      rw [ih, Nat.add_assoc]

omit [Module F2 U] [Module F2 V] [Module F2 W]
    [DecidableEq U] [DecidableEq V] [DecidableEq W] in
/-- Concatenating move paths takes the maximum of their altitudes. -/
theorem trans_altitude {R : AmbientState U V W → AmbientState U V W → Prop} {D E F : AmbientState U V W}
    (path : MovePath R D E) (tail : MovePath R E F) :
    (path.trans tail).altitude = max path.altitude tail.altitude := by
  induction tail with
  | singleton =>
      simp only [MovePath.trans, MovePath.altitude]
      exact (Nat.max_eq_left (end_card_le_altitude path)).symm
  | snoc tail edge ih =>
      simp only [MovePath.trans, MovePath.altitude, ih, Nat.max_assoc]

end MovePath

namespace ContextualTrace

/-- The initial boundary cardinality is bounded by the trace boundary maximum. -/
theorem start_card_le_maxStateCard {D E : AmbientState U V W}
    (trace : ContextualTrace D E) : D.card ≤ trace.maxStateCard := by
  induction trace with
  | singleton =>
      simp only [maxStateCard]
      apply Nat.le_refl
  | primitive trace jump ih =>
      simp only [maxStateCard]
      exact ih.trans (Nat.le_max_left _ _)
  | contextual trace jump ih =>
      simp only [maxStateCard]
      exact ih.trans (Nat.le_max_left _ _)

/-- The final boundary cardinality is bounded by the trace boundary maximum. -/
theorem end_card_le_maxStateCard {D E : AmbientState U V W}
    (trace : ContextualTrace D E) : E.card ≤ trace.maxStateCard := by
  cases trace with
  | singleton =>
      simp only [maxStateCard]
      apply Nat.le_refl
  | primitive trace jump =>
      simp only [maxStateCard]
      exact Nat.le_max_right _ _
  | contextual trace jump =>
      simp only [maxStateCard]
      exact Nat.le_max_right _ _

/-- Compilation has exact length equal to the primitive count plus the sum
of compiler-owned macro distances. -/
theorem compile_length (compiler : EffectiveLocalCompiler U V W) {D E : AmbientState U V W}
    (trace : ContextualTrace D E) :
    (trace.compile compiler).length = trace.constructedLength compiler := by
  induction trace with
  | singleton =>
      simp only [compile, MovePath.length, constructedLength, primitiveCount,
        macroDistanceSum]
  | primitive trace jump ih =>
      simp only [compile, MovePath.length, constructedLength, primitiveCount,
        macroDistanceSum, ih]
      omega
  | contextual trace jump ih =>
      rw [compile, MovePath.trans_length, (compiler jump).path_length, ih]
      simp only [constructedLength, primitiveCount, macroDistanceSum]
      omega

/-- The compiler-owned macro-distance sum is at most three times the number
of contextual macros. -/
theorem macroDistanceSum_le_three_mul_macroCount
    (compiler : EffectiveLocalCompiler U V W) {D E : AmbientState U V W}
    (trace : ContextualTrace D E) :
    trace.macroDistanceSum compiler ≤ 3 * trace.macroCount := by
  induction trace with
  | singleton =>
      simp only [macroDistanceSum, macroCount, Nat.mul_zero]
      apply Nat.le_refl
  | primitive trace jump ih =>
      simpa only [macroDistanceSum, macroCount] using ih
  | contextual trace jump ih =>
      simp only [macroDistanceSum, macroCount]
      rcases (compiler jump).distance_two_or_three with h | h <;> rw [h] <;> omega

/-- A compiled trace has length at most three times its macro count plus
its primitive count. -/
theorem compile_length_le (compiler : EffectiveLocalCompiler U V W) {D E : AmbientState U V W}
    (trace : ContextualTrace D E) :
    (trace.compile compiler).length ≤ 3 * trace.macroCount + trace.primitiveCount := by
  rw [compile_length, constructedLength]
  have h := macroDistanceSum_le_three_mul_macroCount compiler trace
  omega

/-- A compiled trace rises at most one term above its largest explicit
trace boundary. -/
theorem compile_altitude_le (compiler : EffectiveLocalCompiler U V W) {D E : AmbientState U V W}
    (trace : ContextualTrace D E) :
    (trace.compile compiler).altitude ≤ trace.maxStateCard + 1 := by
  induction trace with
  | singleton =>
      simp only [compile, MovePath.altitude, maxStateCard]
      omega
  | primitive trace jump ih =>
      simp only [compile, MovePath.altitude, maxStateCard]
      exact Nat.max_le.mpr ⟨ih.trans (Nat.add_le_add_right (Nat.le_max_left _ _) 1),
        (Nat.le_max_right _ _).trans (Nat.le_add_right _ _)⟩
  | @contextual X Y trace jump ih =>
      rw [compile, MovePath.trans_altitude]
      simp only [maxStateCard]
      apply Nat.max_le.mpr
      constructor
      · exact ih.trans (Nat.add_le_add_right (Nat.le_max_left _ _) 1)
      · have hBoundaryMax : max X.card Y.card ≤ max trace.maxStateCard Y.card :=
          Nat.max_le.mpr ⟨
            (end_card_le_maxStateCard trace).trans (Nat.le_max_left _ _),
            Nat.le_max_right _ _⟩
        exact (compiler jump).altitude_le_boundaryMax_add_one.trans
          (Nat.add_le_add_right hBoundaryMax 1)

/-- Every contextual trace preserves ambient tensor evaluation between its
exact endpoints. -/
theorem endpoint_evaluation {D E : AmbientState U V W}
    (trace : ContextualTrace D E) : stateEvaluation D = stateEvaluation E := by
  induction trace with
  | singleton => rfl
  | primitive trace jump ih => exact ih.trans jump.endpoint_evaluation
  | contextual trace jump ih => exact ih.trans jump.preserves_evaluation

end ContextualTrace

#check @ContextualFiveCircuitJump
#check @MacroCompilation
#check @EffectiveLocalCompiler
#check @ContextualTrace.compile
#check @ContextualTrace.compile_length
#check @ContextualTrace.compile_length_le
#check @ContextualTrace.compile_altitude_le
#check @ContextualTrace.endpoint_evaluation

#print axioms ContextualFiveCircuitJump.preserves_evaluation
#print axioms MacroCompilation.altitude_le_boundaryMax_add_one
#print axioms ContextualTrace.compile_length
#print axioms ContextualTrace.macroDistanceSum_le_three_mul_macroCount
#print axioms ContextualTrace.compile_length_le
#print axioms ContextualTrace.compile_altitude_le
#print axioms ContextualTrace.endpoint_evaluation

end BilinearComplexity.BinaryContextualTrace
