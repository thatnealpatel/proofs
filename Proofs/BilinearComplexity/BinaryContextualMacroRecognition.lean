import BilinearComplexity.BinaryEffectiveExactSpanPresentation
import BilinearComplexity.BinaryContextualFiveCircuitOptimality

set_option autoImplicit false

/-!
# Automatic recognition of contextual binary five-circuit macros

This module exhaustively enumerates the two-versus-three endpoint pairs in a
supplied finite binary full frame.  Forward and reverse source tests are
independent.  Every accepted key recovers its unchanged context, constructs an
effective exact-span presentation, and invokes the existing contextual
compiler.  Bounds are tested on the actual expanded native path.
-/

namespace BilinearComplexity.BinaryContextualMacroRecognition

open BinaryCircuit
open BinaryAmbientCarrier
open BinaryAmbientMoves
open BinaryAmbientTensorCoordinates
open BinaryAmbientNormalization
open BinaryContextualFiveCircuitCompiler
open BinaryContextualFiveCircuitOptimality
open BinaryFiveCircuitCompiler
open NormalizedBinaryCarrier (F2)

universe u v w

variable {U : Type u} {V : Type v} {W : Type w}
variable [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
variable [Module F2 U] [Module F2 V] [Module F2 W]
variable [DecidableEq U] [DecidableEq V] [DecidableEq W]
variable {a b c : ℕ}

/-- The two directed uses of one ordered two-versus-three relation. -/
inductive MacroDirection
  | forward
  | reverse
  deriving DecidableEq, Repr

/-- An endpoint pair together with the direction whose source must occur in the
current state. -/
structure MacroKey where
  direction : MacroDirection
  left : State U V W
  right : State U V W
  deriving DecidableEq

/-- Every ambient rank-one term represented by the supplied full frames. -/
def ambientTerms (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W) : State U V W :=
  denormalizeState eU eV eW
    (Finset.univ : NormalizedBinaryCarrier.State (coordinateProfile a b c))

/-- The full-frame carrier really contains every ambient rank-one term. -/
theorem mem_ambientTerms (eU : Coord a ≃ₗ[F2] U)
    (eV : Coord b ≃ₗ[F2] V) (eW : Coord c ≃ₗ[F2] W)
    (t : Carrier U V W) : t ∈ ambientTerms eU eV eW := by
  rw [ambientTerms, denormalizeState, Finset.mem_map]
  exact ⟨normalizeTerm eU eV eW t, Finset.mem_univ _,
    denormalizeTerm_normalizeTerm eU eV eW t⟩

private def keyEmbedding (direction : MacroDirection) :
    (State U V W × State U V W) ↪ MacroKey (U := U) (V := V) (W := W) where
  toFun pair := ⟨direction, pair.1, pair.2⟩
  inj' := by
    intro x y h
    cases x
    cases y
    cases h
    rfl

/-- Forward keys enumerate the two-term source inside `D` and every ambient
three-term target, without redundant duplicate elimination. No ambient
`DecidableEq` instances are needed by this embedding-based implementation. -/
def forwardKeys (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W) (D : State U V W) : Finset (MacroKey (U := U) (V := V) (W := W)) :=
  ((D.powersetCard 2).product ((ambientTerms eU eV eW).powersetCard 3)).map
    (keyEmbedding .forward)

/-- The embedding-based forward loop enumerates exactly the original image. -/
theorem forwardKeys_eq_image (eU : Coord a ≃ₗ[F2] U)
    (eV : Coord b ≃ₗ[F2] V) (eW : Coord c ≃ₗ[F2] W) (D : State U V W) :
    forwardKeys eU eV eW D =
      ((D.powersetCard 2).product ((ambientTerms eU eV eW).powersetCard 3)).image
        (fun pair => ⟨.forward, pair.1, pair.2⟩) := by
  rw [forwardKeys, Finset.map_eq_image]
  rfl

/-- Reverse keys independently enumerate the three-term source inside `D` and
every ambient two-term target, without redundant duplicate elimination. No
ambient `DecidableEq` instances are needed by this embedding-based implementation. -/
def reverseKeys (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W) (D : State U V W) : Finset (MacroKey (U := U) (V := V) (W := W)) :=
  (((ambientTerms eU eV eW).powersetCard 2).product (D.powersetCard 3)).map
    (keyEmbedding .reverse)

/-- The embedding-based reverse loop enumerates exactly the original image. -/
theorem reverseKeys_eq_image (eU : Coord a ≃ₗ[F2] U)
    (eV : Coord b ≃ₗ[F2] V) (eW : Coord c ≃ₗ[F2] W) (D : State U V W) :
    reverseKeys eU eV eW D =
      (((ambientTerms eU eV eW).powersetCard 2).product (D.powersetCard 3)).image
        (fun pair => ⟨.reverse, pair.1, pair.2⟩) := by
  rw [reverseKeys, Finset.map_eq_image]
  rfl

private theorem forwardKeys_disjoint_reverseKeys (eU : Coord a ≃ₗ[F2] U)
    (eV : Coord b ≃ₗ[F2] V) (eW : Coord c ≃ₗ[F2] W) (D : State U V W) :
    Disjoint (forwardKeys eU eV eW D) (reverseKeys eU eV eW D) := by
  apply Finset.disjoint_left.mpr
  intro key hforward hreverse
  obtain ⟨p, _, hp⟩ := Finset.mem_map.mp hforward
  obtain ⟨q, _, hq⟩ := Finset.mem_map.mp hreverse
  have hdirection := congrArg MacroKey.direction (hp.trans hq.symm)
  cases hdirection

/-- Both directed endpoint loops.  They are deliberately separate: the reverse
source is the three-term endpoint. Their distinct direction tags make the
union disjoint, so no runtime duplicate check is needed. -/
def rawKeys (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W) (D : State U V W) : Finset (MacroKey (U := U) (V := V) (W := W)) :=
  (forwardKeys eU eV eW D).disjUnion (reverseKeys eU eV eW D)
    (forwardKeys_disjoint_reverseKeys eU eV eW D)

/-- The disjoint-union implementation preserves the original raw-key union. -/
theorem rawKeys_eq_union (eU : Coord a ≃ₗ[F2] U)
    (eV : Coord b ≃ₗ[F2] V) (eW : Coord c ≃ₗ[F2] W) (D : State U V W) :
    rawKeys eU eV eW D = forwardKeys eU eV eW D ∪ reverseKeys eU eV eW D := by
  exact Finset.disjUnion_eq_union _ _ _

/-- Applicability is checked in finite coordinates.  The tensor comparison is
therefore a decidable equality of coordinate functions, not equality in an
abstract tensor product. -/
def Applicable (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W) (D : State U V W)
    (key : MacroKey (U := U) (V := V) (W := W)) : Prop :=
  key.left.card = 2 ∧
    key.right.card = 3 ∧
    Disjoint key.left key.right ∧
    NormalizedBinaryCarrier.stateEvaluation
        (normalizeState eU eV eW key.left) =
      NormalizedBinaryCarrier.stateEvaluation
        (normalizeState eU eV eW key.right) ∧
    match key.direction with
    | .forward =>
        key.left ⊆ D ∧ Disjoint (D \ key.left) (key.left ∪ key.right)
    | .reverse =>
        key.right ⊆ D ∧ Disjoint (D \ key.right) (key.left ∪ key.right)

instance instDecidableApplicable (eU : Coord a ≃ₗ[F2] U)
    (eV : Coord b ≃ₗ[F2] V) (eW : Coord c ≃ₗ[F2] W)
    (D : State U V W) (key : MacroKey (U := U) (V := V) (W := W)) :
    Decidable (Applicable eU eV eW D key) := by
  let p := coordinateProfile a b c
  letI : DecidableEq (Fin p.third → F2) := Fintype.decidablePiFintype
  letI : DecidableEq (Fin p.second → Fin p.third → F2) :=
    Fintype.decidablePiFintype
  letI : DecidableEq (Tensor F2 p.first p.second p.third) :=
    Fintype.decidablePiFintype
  unfold Applicable
  cases key.direction <;> infer_instance

/-- A proof-bearing automatically recognized macro before global budget
filtering.  Its exact-span coordinates and compiler result are deterministic
projections defined below. -/
structure RecognizedMacro (eU : Coord a ≃ₗ[F2] U)
    (eV : Coord b ≃ₗ[F2] V) (eW : Coord c ≃ₗ[F2] W)
    (D : State U V W) where
  key : MacroKey (U := U) (V := V) (W := W)
  applicable : Applicable eU eV eW D key

/-- The two-term endpoint of a recognized result. -/
abbrev RecognizedMacro.left
    {eU : Coord a ≃ₗ[F2] U} {eV : Coord b ≃ₗ[F2] V}
    {eW : Coord c ≃ₗ[F2] W} {D : State U V W}
    (result : RecognizedMacro eU eV eW D) : State U V W := result.key.left

/-- The three-term endpoint of a recognized result. -/
abbrev RecognizedMacro.right
    {eU : Coord a ≃ₗ[F2] U} {eV : Coord b ≃ₗ[F2] V}
    {eW : Coord c ≃ₗ[F2] W} {D : State U V W}
    (result : RecognizedMacro eU eV eW D) : State U V W := result.key.right

/-- Recover the unchanged context by subtracting the direction's source
endpoint from the complete current state. -/
def RecognizedMacro.context
    {eU : Coord a ≃ₗ[F2] U} {eV : Coord b ≃ₗ[F2] V}
    {eW : Coord c ≃ₗ[F2] W} {D : State U V W}
    (result : RecognizedMacro eU eV eW D) : State U V W :=
  match result.key.direction with
  | .forward => D \ result.left
  | .reverse => D \ result.right

/-- Coordinate equality used by recognition implies the abstract ambient
tensor equality required by the contextual compiler. -/
theorem RecognizedMacro.evaluation_eq
    {eU : Coord a ≃ₗ[F2] U} {eV : Coord b ≃ₗ[F2] V}
    {eW : Coord c ≃ₗ[F2] W} {D : State U V W}
    (result : RecognizedMacro eU eV eW D) :
    stateEvaluation result.left = stateEvaluation result.right := by
  exact (normalized_stateEvaluation_eq_iff eU eV eW result.left result.right).mp
    result.applicable.2.2.2.1

/-- Effective exact-span coordinates reconstructed directly from the recognized
ambient endpoints and the supplied full frames. -/
def RecognizedMacro.presentation
    {eU : Coord a ≃ₗ[F2] U} {eV : Coord b ≃ₗ[F2] V}
    {eW : Coord c ≃ₗ[F2] W} {D : State U V W}
    (result : RecognizedMacro eU eV eW D) :
    ExactSpanPresentation result.left result.right :=
  BinaryEffectiveExactSpanPresentation.effectiveExactSpanPresentation
    eU eV eW result.left result.right

/-- The recovered context is disjoint from the complete endpoint union. -/
theorem RecognizedMacro.context_disjoint
    {eU : Coord a ≃ₗ[F2] U} {eV : Coord b ≃ₗ[F2] V}
    {eW : Coord c ≃ₗ[F2] W} {D : State U V W}
    (result : RecognizedMacro eU eV eW D) :
    Disjoint result.context (result.left ∪ result.right) := by
  cases hdirection : result.key.direction with
  | forward =>
      have hrest := result.applicable.2.2.2.2
      rw [hdirection] at hrest
      simpa only [RecognizedMacro.context, hdirection] using hrest.2
  | reverse =>
      have hrest := result.applicable.2.2.2.2
      rw [hdirection] at hrest
      simpa only [RecognizedMacro.context, hdirection] using hrest.2

/-- The source endpoint together with the recovered context reconstructs the
whole current state. -/
theorem RecognizedMacro.source_eq
    {eU : Coord a ≃ₗ[F2] U} {eV : Coord b ≃ₗ[F2] V}
    {eW : Coord c ≃ₗ[F2] W} {D : State U V W}
    (result : RecognizedMacro eU eV eW D) :
    match result.key.direction with
    | .forward => result.context ∪ result.left = D
    | .reverse => result.context ∪ result.right = D := by
  cases hdirection : result.key.direction with
  | forward =>
      have hrest := result.applicable.2.2.2.2
      rw [hdirection] at hrest
      simpa only [RecognizedMacro.context, hdirection] using
        Finset.sdiff_union_of_subset hrest.1
  | reverse =>
      have hrest := result.applicable.2.2.2.2
      rw [hdirection] at hrest
      simpa only [RecognizedMacro.context, hdirection] using
        Finset.sdiff_union_of_subset hrest.1

/-- The existing total contextual compiler instantiated with the automatically
recovered effective presentation and context. -/
def RecognizedMacro.compilation
    {eU : Coord a ≃ₗ[F2] U} {eV : Coord b ≃ₗ[F2] V}
    {eW : Coord c ≃ₗ[F2] W} {D : State U V W}
    (result : RecognizedMacro eU eV eW D) :=
  compileContextualBinaryFiveCircuit result.presentation
    result.applicable.1 result.applicable.2.1 result.applicable.2.2.1
    result.evaluation_eq result.context result.context_disjoint

/-- The actual endpoint obtained after replacing the recognized source. -/
def RecognizedMacro.finish
    {eU : Coord a ≃ₗ[F2] U} {eV : Coord b ≃ₗ[F2] V}
    {eW : Coord c ≃ₗ[F2] W} {D : State U V W}
    (result : RecognizedMacro eU eV eW D) : State U V W :=
  match result.key.direction with
  | .forward => result.context ∪ result.right
  | .reverse => result.context ∪ result.left

private def castPathStart {α : Type*} [DecidableEq α]
    {R : Finset α → Finset α → Prop} {D D' E : Finset α}
    (h : D = D') (path : MovePath R D E) : MovePath R D' E := h ▸ path

private def castPathFinish {α : Type*} [DecidableEq α]
    {R : Finset α → Finset α → Prop} {D E E' : Finset α}
    (h : E = E') (path : MovePath R D E) : MovePath R D E' := h ▸ path

private def castPathEndpoints {α : Type*} [DecidableEq α]
    {R : Finset α → Finset α → Prop} {D D' E E' : Finset α}
    (hD : D = D') (hE : E = E') (path : MovePath R D E) :
    MovePath R D' E' :=
  castPathFinish hE (castPathStart hD path)

private theorem castPathStart_length {α : Type*} [DecidableEq α]
    {R : Finset α → Finset α → Prop} {D D' E : Finset α}
    (h : D = D') (path : MovePath R D E) :
    (castPathStart h path).length = path.length := by
  cases h
  rfl

private theorem castPathFinish_length {α : Type*} [DecidableEq α]
    {R : Finset α → Finset α → Prop} {D E E' : Finset α}
    (h : E = E') (path : MovePath R D E) :
    (castPathFinish h path).length = path.length := by
  cases h
  rfl

private theorem castPathEndpoints_length {α : Type*} [DecidableEq α]
    {R : Finset α → Finset α → Prop} {D D' E E' : Finset α}
    (hD : D = D') (hE : E = E') (path : MovePath R D E) :
    (castPathEndpoints hD hE path).length = path.length := by
  rw [castPathEndpoints, castPathFinish_length, castPathStart_length]

private theorem castPathStart_altitude {α : Type*} [DecidableEq α]
    {R : Finset α → Finset α → Prop} {D D' E : Finset α}
    (h : D = D') (path : MovePath R D E) :
    (castPathStart h path).altitude = path.altitude := by
  cases h
  rfl

private theorem castPathFinish_altitude {α : Type*} [DecidableEq α]
    {R : Finset α → Finset α → Prop} {D E E' : Finset α}
    (h : E = E') (path : MovePath R D E) :
    (castPathFinish h path).altitude = path.altitude := by
  cases h
  rfl

private theorem castPathEndpoints_altitude {α : Type*} [DecidableEq α]
    {R : Finset α → Finset α → Prop} {D D' E E' : Finset α}
    (hD : D = D') (hE : E = E') (path : MovePath R D E) :
    (castPathEndpoints hD hE path).altitude = path.altitude := by
  rw [castPathEndpoints, castPathFinish_altitude, castPathStart_altitude]

private theorem direction_eq_reverse_of_ne_forward {d : MacroDirection}
    (h : d ≠ .forward) : d = .reverse := by
  cases d with
  | forward => exact (h rfl).elim
  | reverse => rfl

private theorem RecognizedMacro.source_forward
    {eU : Coord a ≃ₗ[F2] U} {eV : Coord b ≃ₗ[F2] V}
    {eW : Coord c ≃ₗ[F2] W} {D : State U V W}
    (result : RecognizedMacro eU eV eW D)
    (h : result.key.direction = .forward) :
    result.context ∪ result.left = D := by
  simpa only [h] using result.source_eq

private theorem RecognizedMacro.source_reverse
    {eU : Coord a ≃ₗ[F2] U} {eV : Coord b ≃ₗ[F2] V}
    {eW : Coord c ≃ₗ[F2] W} {D : State U V W}
    (result : RecognizedMacro eU eV eW D)
    (h : result.key.direction = .reverse) :
    result.context ∪ result.right = D := by
  simpa only [h] using result.source_eq

private theorem RecognizedMacro.finish_forward
    {eU : Coord a ≃ₗ[F2] U} {eV : Coord b ≃ₗ[F2] V}
    {eW : Coord c ≃ₗ[F2] W} {D : State U V W}
    (result : RecognizedMacro eU eV eW D)
    (h : result.key.direction = .forward) :
    result.context ∪ result.right = result.finish := by
  simp only [RecognizedMacro.finish, h]

private theorem RecognizedMacro.finish_reverse
    {eU : Coord a ≃ₗ[F2] U} {eV : Coord b ≃ₗ[F2] V}
    {eW : Coord c ≃ₗ[F2] W} {D : State U V W}
    (result : RecognizedMacro eU eV eW D)
    (h : result.key.direction = .reverse) :
    result.context ∪ result.left = result.finish := by
  simp only [RecognizedMacro.finish, h]

private def RecognizedMacro.forwardPath
    {eU : Coord a ≃ₗ[F2] U} {eV : Coord b ≃ₗ[F2] V}
    {eW : Coord c ≃ₗ[F2] W} {D : State U V W}
    (result : RecognizedMacro eU eV eW D)
    (h : result.key.direction = .forward) :
    MovePath (AllModeMove (U := U) (V := V) (W := W)) D result.finish :=
  castPathEndpoints (result.source_forward h) (result.finish_forward h)
    result.compilation.forward

private def RecognizedMacro.reversePath
    {eU : Coord a ≃ₗ[F2] U} {eV : Coord b ≃ₗ[F2] V}
    {eW : Coord c ≃ₗ[F2] W} {D : State U V W}
    (result : RecognizedMacro eU eV eW D)
    (h : result.key.direction = .reverse) :
    MovePath (AllModeMove (U := U) (V := V) (W := W)) D result.finish :=
  castPathEndpoints (result.source_reverse h) (result.finish_reverse h)
    result.compilation.reverse

/-- The actual expanded native path selected by the existing compiler. -/
def RecognizedMacro.path
    {eU : Coord a ≃ₗ[F2] U} {eV : Coord b ≃ₗ[F2] V}
    {eW : Coord c ≃ₗ[F2] W} {D : State U V W}
    (result : RecognizedMacro eU eV eW D) :
    MovePath (AllModeMove (U := U) (V := V) (W := W)) D result.finish :=
  if h : result.key.direction = .forward then result.forwardPath h
  else result.reversePath (direction_eq_reverse_of_ne_forward h)

private theorem RecognizedMacro.path_length_forward
    {eU : Coord a ≃ₗ[F2] U} {eV : Coord b ≃ₗ[F2] V}
    {eW : Coord c ≃ₗ[F2] W} {D : State U V W}
    (result : RecognizedMacro eU eV eW D)
    (h : result.key.direction = .forward) :
    result.path.length = result.compilation.forward.length := by
  rw [RecognizedMacro.path, dif_pos h, RecognizedMacro.forwardPath,
    castPathEndpoints_length]

private theorem RecognizedMacro.path_length_reverse
    {eU : Coord a ≃ₗ[F2] U} {eV : Coord b ≃ₗ[F2] V}
    {eW : Coord c ≃ₗ[F2] W} {D : State U V W}
    (result : RecognizedMacro eU eV eW D)
    (h : result.key.direction = .reverse) :
    result.path.length = result.compilation.reverse.length := by
  have hn : result.key.direction ≠ .forward := by
    intro hf
    exact MacroDirection.noConfusion (h.symm.trans hf)
  rw [RecognizedMacro.path, dif_neg hn, RecognizedMacro.reversePath,
    castPathEndpoints_length]


/-- The compiler's semantic orbit certificate remains attached to every
recognized result. -/
theorem RecognizedMacro.semantic_orbit
    {eU : Coord a ≃ₗ[F2] U} {eV : Coord b ≃ₗ[F2] V}
    {eW : Coord c ≃ₗ[F2] W} {D : State U V W}
    (result : RecognizedMacro eU eV eW D) :
    AmbientInOrbit
      result.compilation.label result.left result.right :=
  result.compilation.ambient_membership

/-- Every recognized result has exact primitive length two or three. -/
theorem RecognizedMacro.length_two_or_three
    {eU : Coord a ≃ₗ[F2] U} {eV : Coord b ≃ₗ[F2] V}
    {eW : Coord c ≃ₗ[F2] W} {D : State U V W}
    (result : RecognizedMacro eU eV eW D) :
    result.path.length = 2 ∨ result.path.length = 3 := by
  by_cases h : result.key.direction = .forward
  · rw [result.path_length_forward h, result.compilation.forward_length]
    exact result.compilation.distance_two_or_three
  · let hr := direction_eq_reverse_of_ne_forward h
    rw [result.path_length_reverse hr, result.compilation.reverse_length]
    exact result.compilation.distance_two_or_three

/-- Actual primitive result cost is strictly positive. -/
theorem RecognizedMacro.length_pos
    {eU : Coord a ≃ₗ[F2] U} {eV : Coord b ≃ₗ[F2] V}
    {eW : Coord c ≃ₗ[F2] W} {D : State U V W}
    (result : RecognizedMacro eU eV eW D) : 0 < result.path.length := by
  rcases result.length_two_or_three with h | h <;> omega

/-- The compiled result is shortest among all ambient native paths with its
actual contextual endpoints. -/
theorem RecognizedMacro.path_shortest
    {eU : Coord a ≃ₗ[F2] U} {eV : Coord b ≃ₗ[F2] V}
    {eW : Coord c ≃ₗ[F2] W} {D : State U V W}
    (result : RecognizedMacro eU eV eW D)
    (competitor : MovePath (AllModeMove (U := U) (V := V) (W := W))
      D result.finish) : result.path.length ≤ competitor.length := by
  by_cases h : result.key.direction = .forward
  · let contextualCompetitor : MovePath
        (AllModeMove (U := U) (V := V) (W := W))
        (result.context ∪ result.left) (result.context ∪ result.right) :=
      castPathEndpoints (result.source_forward h).symm
        (result.finish_forward h).symm competitor
    calc
      result.path.length = result.compilation.forward.length :=
        result.path_length_forward h
      _ ≤ contextualCompetitor.length :=
        result.compilation.forward_shortest contextualCompetitor
      _ = competitor.length := by
        exact castPathEndpoints_length _ _ competitor
  · let hr := direction_eq_reverse_of_ne_forward h
    let contextualCompetitor : MovePath
        (AllModeMove (U := U) (V := V) (W := W))
        (result.context ∪ result.right) (result.context ∪ result.left) :=
      castPathEndpoints (result.source_reverse hr).symm
        (result.finish_reverse hr).symm competitor
    calc
      result.path.length = result.compilation.reverse.length :=
        result.path_length_reverse hr
      _ ≤ contextualCompetitor.length :=
        result.compilation.reverse_shortest contextualCompetitor
      _ = competitor.length := by
        exact castPathEndpoints_length _ _ competitor

/-- A recognized result exposes the existing semantic-orbit and ambient
shortestness certificates together with its exact positive primitive cost. -/
theorem RecognizedMacro.certified
    {eU : Coord a ≃ₗ[F2] U} {eV : Coord b ≃ₗ[F2] V}
    {eW : Coord c ≃ₗ[F2] W} {D : State U V W}
    (result : RecognizedMacro eU eV eW D) :
    AmbientInOrbit
        result.compilation.label result.left result.right ∧
      (result.path.length = 2 ∨ result.path.length = 3) ∧
      0 < result.path.length ∧
      ∀ competitor : MovePath (AllModeMove (U := U) (V := V) (W := W))
        D result.finish, result.path.length ≤ competitor.length := by
  exact ⟨result.semantic_orbit, result.length_two_or_three, result.length_pos,
    result.path_shortest⟩

/-- Convert an applicable enumerated key into its proof-bearing compiler
instance. -/
def compileApplicable (eU : Coord a ≃ₗ[F2] U)
    (eV : Coord b ≃ₗ[F2] V) (eW : Coord c ≃ₗ[F2] W)
    (D : State U V W) (key : MacroKey (U := U) (V := V) (W := W))
    (h : Applicable eU eV eW D key) : RecognizedMacro eU eV eW D :=
  ⟨key, h⟩

/-- Exact `(k,H)` admission predicate, evaluated on the complete compiled
primitive path and hence on every internal vertex through `MovePath.altitude`. -/
def PassesBounds (eU : Coord a ≃ₗ[F2] U)
    (eV : Coord b ≃ₗ[F2] V) (eW : Coord c ≃ₗ[F2] W)
    (D : State U V W) (k H : ℕ)
    (key : MacroKey (U := U) (V := V) (W := W)) : Prop :=
  if h : Applicable eU eV eW D key then
    (compileApplicable eU eV eW D key h).path.length ≤ k ∧
      (compileApplicable eU eV eW D key h).path.altitude ≤ H
  else False

/-- Decide admission using constructive applicability and actual native-path bounds. -/
instance instDecidablePassesBounds (eU : Coord a ≃ₗ[F2] U)
    (eV : Coord b ≃ₗ[F2] V) (eW : Coord c ≃ₗ[F2] W)
    (D : State U V W) (k H : ℕ)
    (key : MacroKey (U := U) (V := V) (W := W)) :
    Decidable (PassesBounds eU eV eW D k H key) := by
  unfold PassesBounds
  split <;> infer_instance

/-- Automatically recognized, actually budget-admissible result keys. -/
def recognizeMacroKeys (eU : Coord a ≃ₗ[F2] U)
    (eV : Coord b ≃ₗ[F2] V) (eW : Coord c ≃ₗ[F2] W)
    (D : State U V W) (k H : ℕ) : Finset (MacroKey (U := U) (V := V) (W := W)) :=
  (rawKeys eU eV eW D).filter (PassesBounds eU eV eW D k H)

/-- Extract the proof-bearing compiler object from a recognized finite key.
The only case split is the executable applicability decision; no choice of a
presentation, label, or path is made. -/
def compileRecognized (eU : Coord a ≃ₗ[F2] U)
    (eV : Coord b ≃ₗ[F2] V) (eW : Coord c ≃ₗ[F2] W)
    (D : State U V W) (k H : ℕ)
    (key : MacroKey (U := U) (V := V) (W := W))
    (hkey : key ∈ recognizeMacroKeys eU eV eW D k H) :
    RecognizedMacro eU eV eW D := by
  by_cases hApplicable : Applicable eU eV eW D key
  · exact compileApplicable eU eV eW D key hApplicable
  · have hkey' := hkey
    rw [recognizeMacroKeys, Finset.mem_filter] at hkey'
    have hpasses := hkey'.2
    simp only [PassesBounds, dif_neg hApplicable] at hpasses

/-- Forward applicability expands to the full two-source/context predicate. -/
theorem applicable_forward_iff (eU : Coord a ≃ₗ[F2] U)
    (eV : Coord b ≃ₗ[F2] V) (eW : Coord c ≃ₗ[F2] W)
    (D A B : State U V W) :
    Applicable eU eV eW D ⟨.forward, A, B⟩ ↔
      A.card = 2 ∧ B.card = 3 ∧ Disjoint A B ∧
      NormalizedBinaryCarrier.stateEvaluation (normalizeState eU eV eW A) =
        NormalizedBinaryCarrier.stateEvaluation (normalizeState eU eV eW B) ∧
      A ⊆ D ∧ Disjoint (D \ A) (A ∪ B) := Iff.rfl

/-- Reverse applicability independently uses the three-term endpoint as the
source and recovers its own context. -/
theorem applicable_reverse_iff (eU : Coord a ≃ₗ[F2] U)
    (eV : Coord b ≃ₗ[F2] V) (eW : Coord c ≃ₗ[F2] W)
    (D A B : State U V W) :
    Applicable eU eV eW D ⟨.reverse, A, B⟩ ↔
      A.card = 2 ∧ B.card = 3 ∧ Disjoint A B ∧
      NormalizedBinaryCarrier.stateEvaluation (normalizeState eU eV eW A) =
        NormalizedBinaryCarrier.stateEvaluation (normalizeState eU eV eW B) ∧
      B ⊆ D ∧ Disjoint (D \ B) (A ∪ B) := Iff.rfl

/-- Applicability alone guarantees occurrence in the correct independent raw
endpoint loop. -/
theorem rawKeys_mem_of_applicable (eU : Coord a ≃ₗ[F2] U)
    (eV : Coord b ≃ₗ[F2] V) (eW : Coord c ≃ₗ[F2] W)
    (D : State U V W) (key : MacroKey (U := U) (V := V) (W := W))
    (h : Applicable eU eV eW D key) : key ∈ rawKeys eU eV eW D := by
  rcases h with ⟨hleftCard, hrightCard, _hdisjoint, _hevaluation, hsource⟩
  rcases key with ⟨direction, left, right⟩
  cases direction with
  | forward =>
      rw [rawKeys_eq_union, Finset.mem_union]
      apply Or.inl
      rw [forwardKeys_eq_image, Finset.mem_image]
      refine ⟨(left, right), ?_, rfl⟩
      apply Finset.mem_product.mpr
      rw [Finset.mem_powersetCard, Finset.mem_powersetCard]
      exact ⟨⟨hsource.1, hleftCard⟩,
        ⟨fun t _ => mem_ambientTerms eU eV eW t, hrightCard⟩⟩
  | reverse =>
      rw [rawKeys_eq_union, Finset.mem_union]
      apply Or.inr
      rw [reverseKeys_eq_image, Finset.mem_image]
      refine ⟨(left, right), ?_, rfl⟩
      apply Finset.mem_product.mpr
      rw [Finset.mem_powersetCard, Finset.mem_powersetCard]
      exact ⟨⟨fun t _ => mem_ambientTerms eU eV eW t, hleftCard⟩,
        ⟨hsource.1, hrightCard⟩⟩

/-- Membership is exactly applicability plus the actual expanded-path budget
and altitude tests.  In particular this is complete in both source directions;
no caller supplies a pair, context, presentation, classifier, or coverage
oracle. -/
theorem mem_recognizeMacroKeys_iff (eU : Coord a ≃ₗ[F2] U)
    (eV : Coord b ≃ₗ[F2] V) (eW : Coord c ≃ₗ[F2] W)
    (D : State U V W) (k H : ℕ)
    (key : MacroKey (U := U) (V := V) (W := W)) :
    key ∈ recognizeMacroKeys eU eV eW D k H ↔
      ∃ h : Applicable eU eV eW D key,
        (compileApplicable eU eV eW D key h).path.length ≤ k ∧
          (compileApplicable eU eV eW D key h).path.altitude ≤ H := by
  rw [recognizeMacroKeys, Finset.mem_filter]
  constructor
  · rintro ⟨_hraw, hbounds⟩
    rw [PassesBounds] at hbounds
    split at hbounds
    next hApplicable => exact ⟨hApplicable, hbounds⟩
    next => exact False.elim hbounds
  · rintro ⟨hApplicable, hbounds⟩
    refine ⟨rawKeys_mem_of_applicable eU eV eW D key hApplicable, ?_⟩
    rw [PassesBounds]
    split
    next hApplicable' => simpa only [Subsingleton.elim hApplicable' hApplicable] using hbounds
    next hnot => exact False.elim (hnot hApplicable)

/-- Forward recognition covers exactly the applicable two-term sources whose
compiled expansion meets the public bounds. -/
theorem mem_recognizeMacroKeys_forward_iff (eU : Coord a ≃ₗ[F2] U)
    (eV : Coord b ≃ₗ[F2] V) (eW : Coord c ≃ₗ[F2] W)
    (D A B : State U V W) (k H : ℕ) :
    (⟨.forward, A, B⟩ : MacroKey) ∈ recognizeMacroKeys eU eV eW D k H ↔
      ∃ h : Applicable eU eV eW D ⟨.forward, A, B⟩,
        (compileApplicable eU eV eW D ⟨.forward, A, B⟩ h).path.length ≤ k ∧
          (compileApplicable eU eV eW D ⟨.forward, A, B⟩ h).path.altitude ≤ H :=
  mem_recognizeMacroKeys_iff eU eV eW D k H ⟨.forward, A, B⟩

/-- Reverse recognition independently covers applicable three-term sources;
it does not require that the two-term target be contained in the input. -/
theorem mem_recognizeMacroKeys_reverse_iff (eU : Coord a ≃ₗ[F2] U)
    (eV : Coord b ≃ₗ[F2] V) (eW : Coord c ≃ₗ[F2] W)
    (D A B : State U V W) (k H : ℕ) :
    (⟨.reverse, A, B⟩ : MacroKey) ∈ recognizeMacroKeys eU eV eW D k H ↔
      ∃ h : Applicable eU eV eW D ⟨.reverse, A, B⟩,
        (compileApplicable eU eV eW D ⟨.reverse, A, B⟩ h).path.length ≤ k ∧
          (compileApplicable eU eV eW D ⟨.reverse, A, B⟩ h).path.altitude ≤ H :=
  mem_recognizeMacroKeys_iff eU eV eW D k H ⟨.reverse, A, B⟩

/-- No five-circuit macro is admitted below its minimum two-primitive cost. -/
theorem recognizeMacroKeys_eq_empty_of_lt_two (eU : Coord a ≃ₗ[F2] U)
    (eV : Coord b ≃ₗ[F2] V) (eW : Coord c ≃ₗ[F2] W)
    (D : State U V W) (k H : ℕ) (hk : k < 2) :
    recognizeMacroKeys eU eV eW D k H = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro key hkey
  obtain ⟨h, hlength, _⟩ :=
    (mem_recognizeMacroKeys_iff eU eV eW D k H key).mp hkey
  have hd := (compileApplicable eU eV eW D key h).length_two_or_three
  have htwo : 2 ≤ (compileApplicable eU eV eW D key h).path.length :=
    hd.elim (fun heq => heq ▸ Nat.le_refl 2) (fun heq => heq ▸ (by decide : 2 ≤ 3))
  exact (Nat.not_le_of_lt hk) (htwo.trans hlength)

/-- Every enumerated key compiles to a genuine native path satisfying the exact
public bounds, with recovered full context and effective presentation. -/
theorem recognizedMacro_sound (eU : Coord a ≃ₗ[F2] U)
    (eV : Coord b ≃ₗ[F2] V) (eW : Coord c ≃ₗ[F2] W)
    (D : State U V W) (k H : ℕ)
    (key : MacroKey (U := U) (V := V) (W := W))
    (hkey : key ∈ recognizeMacroKeys eU eV eW D k H) :
    let result := compileRecognized eU eV eW D k H key hkey
    result.path.length ≤ k ∧ result.path.altitude ≤ H ∧
      Disjoint result.context (result.left ∪ result.right) ∧
      (match result.key.direction with
       | .forward => result.context ∪ result.left = D
       | .reverse => result.context ∪ result.right = D) ∧
      AmbientInOrbit
        result.compilation.label result.left result.right := by
  dsimp only
  by_cases hApplicable : Applicable eU eV eW D key
  · rcases (mem_recognizeMacroKeys_iff eU eV eW D k H key).mp hkey with
      ⟨hApplicable', hbounds⟩
    have hproof : hApplicable' = hApplicable := Subsingleton.elim _ _
    subst hApplicable'
    let result := compileApplicable eU eV eW D key hApplicable
    have hresult : result.path.length ≤ k ∧ result.path.altitude ≤ H ∧
        Disjoint result.context (result.left ∪ result.right) ∧
        (match result.key.direction with
         | .forward => result.context ∪ result.left = D
         | .reverse => result.context ∪ result.right = D) ∧
        AmbientInOrbit result.compilation.label result.left result.right :=
      ⟨hbounds.1, hbounds.2, result.context_disjoint, result.source_eq,
        result.semantic_orbit⟩
    have heq : compileRecognized eU eV eW D k H key hkey = result := by
      unfold compileRecognized
      split
      · rfl
      · next hnot => exact False.elim (hnot hApplicable)
    rw [heq]
    exact hresult
  · rcases (mem_recognizeMacroKeys_iff eU eV eW D k H key).mp hkey with
      ⟨hApplicable', _⟩
    exact False.elim (hApplicable hApplicable')

#check @recognizeMacroKeys
#check @mem_recognizeMacroKeys_iff
#check @recognizedMacro_sound
#check @RecognizedMacro.certified

#print axioms forwardKeys_eq_image
#print axioms reverseKeys_eq_image
#print axioms rawKeys_eq_union
#print axioms mem_recognizeMacroKeys_iff
#print axioms mem_recognizeMacroKeys_forward_iff
#print axioms mem_recognizeMacroKeys_reverse_iff
#print axioms recognizeMacroKeys_eq_empty_of_lt_two
#print axioms recognizedMacro_sound
#print axioms RecognizedMacro.certified

end BilinearComplexity.BinaryContextualMacroRecognition
