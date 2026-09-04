import BilinearComplexity.NormalizedBinaryReplay221
import BilinearComplexity.SchemeAction

set_option autoImplicit false

/-!
# Mode-permutation transport for the designated normalized binary replay

This module transports normalized binary carrier terms, finite-set states, and
one designated profile-`221` replay through the six explicit tensor-mode
orientations in `BilinearComplexity.Scheme.Action`.  Its three named target
legality predicates are exact relational images of specifically tagged source
moves: target terms, relabeled modes, and endpoint states are explicit inputs
constrained by permutation equalities.  They are not independent
coordinate-native move semantics, and the module does not assert that the
ordered predicates in `NormalizedBinaryReplay221.Move` are invariant under
mode permutation.

AI disclosure: produced with AI assistance (see `README`).
-/

namespace BilinearComplexity.NormalizedBinaryModePermutation

open NormalizedBinaryCarrier
open NormalizedBinaryReplay221
open BinaryCircuit
open Scheme.Action
open scoped BigOperators

/-- Reorder a normalized binary profile by one of the six explicit tensor-mode
orientations. -/
abbrev permProfile (o : Orientation) (p : Profile) : Profile :=
  ⟨o.firstDim p.first p.second p.third,
    o.secondDim p.first p.second p.third,
    o.thirdDim p.first p.second p.third⟩

example : permProfile .bca ⟨2, 3, 5⟩ = ⟨3, 5, 2⟩ := rfl

/-- The identity orientation leaves a normalized profile unchanged. -/
@[simp] theorem permProfile_abc (p : Profile) : permProfile .abc p = p := by
  rcases p with ⟨a, b, c⟩
  rfl

/-- Reorder the three factors of a normalized carrier term by one of the six
explicit tensor-mode orientations. -/
def permuteTerm {p : Profile} (o : Orientation) (t : Carrier p) :
    Carrier (permProfile o p) :=
  match o with
  | .abc => (t.1, t.2.1, t.2.2)
  | .bca => (t.2.1, t.2.2, t.1)
  | .cab => (t.2.2, t.1, t.2.1)
  | .acb => (t.1, t.2.2, t.2.1)
  | .cba => (t.2.2, t.2.1, t.1)
  | .bac => (t.2.1, t.1, t.2.2)

example {p : Profile} (t : Carrier p) :
    permuteTerm .cab t = (t.2.2, t.1, t.2.1) := rfl

/-- Map a finite-set state by the explicit carrier-term permutation. -/
def permuteState {p : Profile} (o : Orientation) (D : State p) :
    State (permProfile o p) :=
  D.image (permuteTerm o)

example {p : Profile} : permuteState .abc (∅ : State p) = ∅ := rfl

/-- `orientationMode o m` is the output position of original mode `m` under
`o`.  Thus generated Split and directed narrow Reduction use
`orientationMode o 0`; source third Flip shares `orientationMode o 2`, while
its ordered shear roles originating in modes `0` and `1` occur at
`orientationMode o 0` and `orientationMode o 1`. -/
def orientationMode (o : Orientation) : Fin 3 → Fin 3 :=
  match o with
  | .abc => ![0, 1, 2]
  | .bca => ![2, 0, 1]
  | .cab => ![1, 2, 0]
  | .acb => ![0, 2, 1]
  | .cba => ![2, 1, 0]
  | .bac => ![1, 0, 2]

example : orientationMode .bca 0 = 2 ∧ orientationMode .bca 2 = 1 := by decide

/-- The explicit output-mode table is a permutation for each orientation. -/
theorem orientationMode_injective (o : Orientation) :
    Function.Injective (orientationMode o) := by
  cases o <;> decide

/-- The carrier-term permutation is injective. -/
theorem permuteTerm_injective {p : Profile} (o : Orientation) :
    Function.Injective (@permuteTerm p o) := by
  intro s t hst
  cases o <;>
    rcases s with ⟨s₁, s₂, s₃⟩ <;>
    rcases t with ⟨t₁, t₂, t₃⟩ <;>
    simp only [permuteTerm] at hst ⊢
  all_goals
    injection hst with h₁ h₂₃
    injection h₂₃ with h₂ h₃
    subst_vars
    rfl

/-- Permuting finite-set states commutes with union. -/
@[simp] theorem permuteState_union {p : Profile} (o : Orientation)
    (D E : State p) :
    permuteState o (D ∪ E) = permuteState o D ∪ permuteState o E := by
  exact Finset.image_union D E

/-- A permuted source term belongs to a permuted state exactly when the source
term belongs to the source state. -/
@[simp] theorem permuteState_mem {p : Profile} (o : Orientation)
    {t : Carrier p} {D : State p} :
    permuteTerm o t ∈ permuteState o D ↔ t ∈ D := by
  constructor
  · intro hmem
    obtain ⟨s, hs, hst⟩ := Finset.mem_image.mp hmem
    have heq : s = t := permuteTerm_injective o hst
    simpa only [heq] using hs
  · intro hmem
    exact Finset.mem_image.mpr ⟨t, hmem, rfl⟩

/-- Permuting a state preserves its exact finite-set cardinality. -/
@[simp] theorem permuteState_card {p : Profile} (o : Orientation)
    (D : State p) :
    (permuteState o D).card = D.card := by
  exact Finset.card_image_of_injective D (permuteTerm_injective o)

/-- Permuting a state commutes exactly with erasing a source term. -/
@[simp] theorem permuteState_erase {p : Profile} (o : Orientation)
    (D : State p) (t : Carrier p) :
    permuteState o (D.erase t) =
      (permuteState o D).erase (permuteTerm o t) := by
  exact Finset.image_erase (permuteTerm_injective o) D t

/-- Permuting a state commutes exactly with inserting a source term. -/
@[simp] theorem permuteState_insert {p : Profile} (o : Orientation)
    (D : State p) (t : Carrier p) :
    permuteState o (insert t D) =
      insert (permuteTerm o t) (permuteState o D) := by
  exact Finset.image_insert (permuteTerm o) t D

/-- The identity orientation leaves every carrier term unchanged. -/
@[simp] theorem permuteTerm_abc {p : Profile} (t : Carrier p) :
    permuteTerm .abc t = t := rfl

/-- The identity orientation leaves every finite-set state unchanged. -/
@[simp] theorem permuteState_abc {p : Profile} (D : State p) :
    permuteState .abc D = D := by
  rcases p with ⟨a, b, c⟩
  change D.image id = D
  exact Finset.image_id

/-- Permuting a normalized term and then evaluating it agrees with the
corresponding tensor argument permutation. -/
theorem tensorEvaluation_permuteTerm {p : Profile} (o : Orientation)
    (t : Carrier p) :
    tensorEvaluation (permuteTerm o t) =
      orientTensor o (tensorEvaluation t) := by
  cases o <;> funext i j k <;>
    simp only [tensorEvaluation, permuteTerm, orientTensor] <;> ring

private theorem orientTensor_zero {p : Profile} (o : Orientation) :
    orientTensor o (0 : Tensor F2 p.first p.second p.third) = 0 := by
  cases o <;> funext i j k <;> rfl

private theorem orientTensor_add {p : Profile} (o : Orientation)
    (T U : Tensor F2 p.first p.second p.third) :
    orientTensor o (T + U) = orientTensor o T + orientTensor o U := by
  cases o <;> funext i j k <;> rfl

private theorem stateEvaluation_empty (p : Profile) :
    stateEvaluation (∅ : State p) = 0 := by
  simp only [stateEvaluation_eq_sum, Finset.sum_empty]

private theorem stateEvaluation_insert {p : Profile} {t : Carrier p}
    {D : State p} (ht : t ∉ D) :
    stateEvaluation (insert t D) = tensorEvaluation t + stateEvaluation D := by
  simp only [stateEvaluation_eq_sum, Finset.sum_insert ht]

/-- Evaluation of a permuted finite-set state is the corresponding permutation
of its source tensor evaluation. -/
theorem stateEvaluation_permuteState {p : Profile} (o : Orientation)
    (D : State p) :
    stateEvaluation (permuteState o D) =
      orientTensor o (stateEvaluation D) := by
  induction D using Finset.induction_on with
  | empty =>
      rw [permuteState, Finset.image_empty, stateEvaluation_empty,
        stateEvaluation_empty, orientTensor_zero]
  | @insert t D ht ih =>
      have hpermute : permuteTerm o t ∉ permuteState o D := by
        intro hmem
        exact ht ((permuteState_mem o).mp hmem)
      calc
        stateEvaluation (permuteState o (insert t D)) =
            stateEvaluation (insert (permuteTerm o t) (permuteState o D)) := by
          rw [permuteState_insert]
        _ = tensorEvaluation (permuteTerm o t) +
            stateEvaluation (permuteState o D) := stateEvaluation_insert hpermute
        _ = orientTensor o (tensorEvaluation t) +
            stateEvaluation (permuteState o D) := by
          exact congrArg (fun T => T + stateEvaluation (permuteState o D))
            (tensorEvaluation_permuteTerm o t)
        _ = orientTensor o (tensorEvaluation t) +
            orientTensor o (stateEvaluation D) := by
          exact congrArg (fun T => orientTensor o (tensorEvaluation t) + T) ih
        _ = orientTensor o (tensorEvaluation t + stateEvaluation D) :=
          (orientTensor_add o _ _).symm
        _ = orientTensor o (stateEvaluation (insert t D)) := by
          exact congrArg (orientTensor o) (stateEvaluation_insert ht).symm

/-- Exact transported target legality for a generated first-mode Split.
This is the relational image of a specifically tagged `GeneratedFirstSplit`
witness: the target terms, output mode, and endpoint states are inputs to the
predicate and are fixed by the displayed permutation equalities.  It is not an
independent coordinate-native Split predicate. -/
def OrientationGeneratedSplit {p : Profile} (o : Orientation)
    (splitMode : Fin 3)
    (source' outputLeft' outputRight' : Carrier (permProfile o p))
    (D' E' : State (permProfile o p)) : Prop :=
  ∃ (source outputLeft outputRight : Carrier p) (sourceState targetState : State p),
    GeneratedFirstSplit source outputLeft outputRight sourceState targetState ∧
    source' = permuteTerm o source ∧
    outputLeft' = permuteTerm o outputLeft ∧
    outputRight' = permuteTerm o outputRight ∧
    splitMode = orientationMode o 0 ∧
    D' = permuteState o sourceState ∧
    E' = permuteState o targetState

/-- A tagged source Split constructs its exact transported target legality
predicate. -/
theorem orientationGeneratedSplit_of_source {p : Profile} (o : Orientation)
    {source outputLeft outputRight : Carrier p} {D E : State p}
    (h : GeneratedFirstSplit source outputLeft outputRight D E) :
    OrientationGeneratedSplit o (orientationMode o 0)
      (permuteTerm o source) (permuteTerm o outputLeft)
      (permuteTerm o outputRight) (permuteState o D) (permuteState o E) := by
  exact ⟨source, outputLeft, outputRight, D, E, h, rfl, rfl, rfl, rfl,
    rfl, rfl⟩

/-- Exact transported target legality for a source third-mode Flip.  It is the
relational image of a specifically tagged `SourceThirdFlip`; all four target
terms, all three relabeled output modes, and both endpoint states are inputs to
this predicate and are constrained by exact permutation equalities. -/
def OrientationSourceFlip {p : Profile} (o : Orientation)
    (sharedMode firstShearMode secondShearMode : Fin 3)
    (sourceLeft' sourceRight' targetLeft' targetRight' :
      Carrier (permProfile o p))
    (D' E' : State (permProfile o p)) : Prop :=
  ∃ (sourceLeft sourceRight targetLeft targetRight : Carrier p)
      (sourceState targetState : State p),
    SourceThirdFlip sourceLeft sourceRight targetLeft targetRight
      sourceState targetState ∧
    sourceLeft' = permuteTerm o sourceLeft ∧
    sourceRight' = permuteTerm o sourceRight ∧
    targetLeft' = permuteTerm o targetLeft ∧
    targetRight' = permuteTerm o targetRight ∧
    sharedMode = orientationMode o 2 ∧
    firstShearMode = orientationMode o 0 ∧
    secondShearMode = orientationMode o 1 ∧
    D' = permuteState o sourceState ∧
    E' = permuteState o targetState

/-- A tagged source Flip constructs its exact transported target legality
predicate. -/
theorem orientationSourceFlip_of_source {p : Profile} (o : Orientation)
    {sourceLeft sourceRight targetLeft targetRight : Carrier p} {D E : State p}
    (h : SourceThirdFlip sourceLeft sourceRight targetLeft targetRight D E) :
    OrientationSourceFlip o (orientationMode o 2) (orientationMode o 0)
      (orientationMode o 1) (permuteTerm o sourceLeft)
      (permuteTerm o sourceRight) (permuteTerm o targetLeft)
      (permuteTerm o targetRight) (permuteState o D) (permuteState o E) := by
  exact ⟨sourceLeft, sourceRight, targetLeft, targetRight, D, E, h,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Exact transported target legality for a directed narrow first-mode
Reduction.  It is the relational image of a specifically tagged
`DirectedNarrowPairReduction`; the three target terms, relabeled output mode,
and endpoint states are inputs constrained by exact permutation equalities. -/
def OrientationNarrowReduction {p : Profile} (o : Orientation)
    (reductionMode : Fin 3)
    (sourceLeft' sourceRight' target' : Carrier (permProfile o p))
    (D' E' : State (permProfile o p)) : Prop :=
  ∃ (sourceLeft sourceRight target : Carrier p) (sourceState targetState : State p),
    DirectedNarrowPairReduction sourceLeft sourceRight target
      sourceState targetState ∧
    sourceLeft' = permuteTerm o sourceLeft ∧
    sourceRight' = permuteTerm o sourceRight ∧
    target' = permuteTerm o target ∧
    reductionMode = orientationMode o 0 ∧
    D' = permuteState o sourceState ∧
    E' = permuteState o targetState

/-- A tagged source Reduction constructs its exact transported target legality
predicate. -/
theorem orientationNarrowReduction_of_source {p : Profile} (o : Orientation)
    {sourceLeft sourceRight target : Carrier p} {D E : State p}
    (h : DirectedNarrowPairReduction sourceLeft sourceRight target D E) :
    OrientationNarrowReduction o (orientationMode o 0)
      (permuteTerm o sourceLeft) (permuteTerm o sourceRight)
      (permuteTerm o target) (permuteState o D) (permuteState o E) := by
  exact ⟨sourceLeft, sourceRight, target, D, E, h, rfl, rfl, rfl, rfl,
    rfl, rfl⟩

/-- A move relation generated by the three exact transported target legality
predicates.  The term and mode parameters are existential constructor data,
but every constructor requires the named target-side law that constrains them;
this remains relational-image semantics rather than coordinate-native moves. -/
inductive OrientationMove {p : Profile} (o : Orientation) :
    State (permProfile o p) → State (permProfile o p) → Prop
  /-- A move certified by exact transported generated-Split legality. -/
  | generatedSplit
      {source' outputLeft' outputRight' : Carrier (permProfile o p)}
      {D' E' : State (permProfile o p)} {splitMode : Fin 3} :
      OrientationGeneratedSplit o splitMode source' outputLeft' outputRight'
        D' E' →
      OrientationMove o D' E'
  /-- A move certified by exact transported source-Flip legality. -/
  | sourceThirdFlip
      {sourceLeft' sourceRight' targetLeft' targetRight' :
        Carrier (permProfile o p)}
      {D' E' : State (permProfile o p)}
      {sharedMode firstShearMode secondShearMode : Fin 3} :
      OrientationSourceFlip o sharedMode firstShearMode secondShearMode
        sourceLeft' sourceRight' targetLeft' targetRight' D' E' →
      OrientationMove o D' E'
  /-- A move certified by exact transported narrow-Reduction legality. -/
  | directedNarrowReduction
      {sourceLeft' sourceRight' target' : Carrier (permProfile o p)}
      {D' E' : State (permProfile o p)} {reductionMode : Fin 3} :
      OrientationNarrowReduction o reductionMode sourceLeft' sourceRight'
        target' D' E' →
      OrientationMove o D' E'

/-- A generated first-factor Split produces its exact transported target
legality law and hence a relabeled Split edge in output mode
`orientationMode o 0`. -/
theorem transportGeneratedFirstSplit {p : Profile} (o : Orientation)
    {source outputLeft outputRight : Carrier p} {D E : State p}
    (h : GeneratedFirstSplit source outputLeft outputRight D E) :
    OrientationMove o (permuteState o D) (permuteState o E) := by
  exact .generatedSplit (orientationGeneratedSplit_of_source o h)

/-- A source third-factor Flip produces its exact transported target legality
law and hence a relabeled Flip sharing `orientationMode o 2`, with ordered
shear modes `orientationMode o 0` and `orientationMode o 1`. -/
theorem transportSourceThirdFlip {p : Profile} (o : Orientation)
    {sourceLeft sourceRight targetLeft targetRight : Carrier p} {D E : State p}
    (h : SourceThirdFlip sourceLeft sourceRight targetLeft targetRight D E) :
    OrientationMove o (permuteState o D) (permuteState o E) := by
  exact .sourceThirdFlip (orientationSourceFlip_of_source o h)

/-- A directed narrow first-mode Reduction produces its exact transported
target legality law and hence a relabeled Reduction edge whose varying mode is
`orientationMode o 0`. -/
theorem transportDirectedNarrowPairReduction {p : Profile} (o : Orientation)
    {sourceLeft sourceRight target : Carrier p} {D E : State p}
    (h : DirectedNarrowPairReduction sourceLeft sourceRight target D E) :
    OrientationMove o (permuteState o D) (permuteState o E) := by
  exact .directedNarrowReduction (orientationNarrowReduction_of_source o h)

/-- Transport one old ordered move to its explicitly relabeled orientation
move, without claiming invariance of `Move`. -/
theorem permuteMove {p : Profile} (o : Orientation) {D E : State p}
    (h : @Move p D E) :
    OrientationMove o (permuteState o D) (permuteState o E) := by
  cases h with
  | generatedFirstSplit hsplit => exact transportGeneratedFirstSplit o hsplit
  | sourceThirdFlip hflip => exact transportSourceThirdFlip o hflip
  | directedNarrowPairReduction hreduction =>
      exact transportDirectedNarrowPairReduction o hreduction

/-- Every orientation move carries an old source move and exact endpoint-image
provenance. -/
theorem OrientationMove.provenance {p : Profile} {o : Orientation}
    {D E : State (permProfile o p)} (h : @OrientationMove p o D E) :
    ∃ D₀ E₀ : State p,
      @Move p D₀ E₀ ∧ D = permuteState o D₀ ∧ E = permuteState o E₀ := by
  cases h with
  | generatedSplit legality =>
      rcases legality with
        ⟨_, _, _, D₀, E₀, sourceWitness, _, _, _, _, sourceState_eq,
          targetState_eq⟩
      exact ⟨D₀, E₀, .generatedFirstSplit sourceWitness,
        sourceState_eq, targetState_eq⟩
  | sourceThirdFlip legality =>
      rcases legality with
        ⟨_, _, _, _, D₀, E₀, sourceWitness, _, _, _, _, _, _, _,
          sourceState_eq, targetState_eq⟩
      exact ⟨D₀, E₀, .sourceThirdFlip sourceWitness,
        sourceState_eq, targetState_eq⟩
  | directedNarrowReduction legality =>
      rcases legality with
        ⟨_, _, _, D₀, E₀, sourceWitness, _, _, _, _, sourceState_eq,
          targetState_eq⟩
      exact ⟨D₀, E₀, .directedNarrowPairReduction sourceWitness,
        sourceState_eq, targetState_eq⟩

/-- Every explicitly relabeled orientation move preserves target-profile state
evaluation. -/
theorem OrientationMove.preserves_evaluation {p : Profile} {o : Orientation}
    {D E : State (permProfile o p)} (h : @OrientationMove p o D E) :
    stateEvaluation E = stateEvaluation D := by
  obtain ⟨D₀, E₀, hmove, rfl, rfl⟩ := h.provenance
  rw [stateEvaluation_permuteState, stateEvaluation_permuteState]
  exact congrArg (orientTensor o) hmove.preserves_evaluation

/-- At the identity orientation, every relabeled move recovers a genuine old
ordered `Move`. -/
theorem orientationMove_abc_to_move {p : Profile} {D E : State p}
    (h : @OrientationMove p .abc D E) : @Move p D E := by
  obtain ⟨D₀, E₀, hmove, hD, hE⟩ := h.provenance
  rw [permuteState_abc] at hD hE
  subst D
  subst E
  exact hmove

/-- At the identity orientation, old ordered moves and relabeled orientation
moves are equivalent. -/
theorem orientationMove_abc_iff {p : Profile} {D E : State p} :
    @OrientationMove p .abc D E ↔ @Move p D E := by
  constructor
  · exact orientationMove_abc_to_move
  · intro h
    simpa only [permuteState_abc] using permuteMove .abc h

/-- Recursively transport actual old `MovePath` data to actual relabeled
`OrientationMove` path data. -/
def permuteMovePath {p : Profile} (o : Orientation) :
    {D E : State p} → MovePath (@Move p) D E →
      MovePath (@OrientationMove p o) (permuteState o D) (permuteState o E)
  | _, _, .singleton D => .singleton (permuteState o D)
  | _, _, .snoc path h => .snoc (permuteMovePath o path) (permuteMove o h)

example {p : Profile} (o : Orientation) (D : State p) :
    permuteMovePath o (.singleton D : MovePath (@Move p) D D) =
      (.singleton (permuteState o D) :
        MovePath (@OrientationMove p o) (permuteState o D) (permuteState o D)) := by
  simp only [permuteMovePath]

/-- Transport maps the ordered vertex list pointwise by `permuteState`. -/
theorem permuteMovePath_vertices {p : Profile} (o : Orientation)
    {D E : State p} (path : MovePath (@Move p) D E) :
    (permuteMovePath o path).vertices = path.vertices.map (permuteState o) := by
  induction path with
  | singleton =>
      simp only [permuteMovePath, MovePath.vertices, List.map_singleton]
  | snoc path _ ih =>
      simp only [permuteMovePath, MovePath.vertices, ih, List.map_append,
        List.map_singleton]

/-- Transport preserves the exact number of path edges. -/
@[simp] theorem permuteMovePath_length {p : Profile} (o : Orientation)
    {D E : State p} (path : MovePath (@Move p) D E) :
    (permuteMovePath o path).length = path.length := by
  induction path with
  | singleton => simp only [permuteMovePath, MovePath.length]
  | snoc path _ ih => simp only [permuteMovePath, MovePath.length, ih]

/-- Transport preserves exact path altitude because the carrier permutation is
injective on every finite-set vertex. -/
@[simp] theorem permuteMovePath_altitude {p : Profile} (o : Orientation)
    {D E : State p} (path : MovePath (@Move p) D E) :
    (permuteMovePath o path).altitude = path.altitude := by
  induction path with
  | singleton => simp only [permuteMovePath, MovePath.altitude, permuteState_card]
  | snoc path _ ih =>
      simp only [permuteMovePath, MovePath.altitude, ih, permuteState_card]

/-- A target state is a transported path vertex exactly when it is the image of
an actual source path vertex. -/
theorem permuteMovePath_pathVertex_iff {p : Profile} (o : Orientation)
    {D E : State p} (path : MovePath (@Move p) D E)
    (Y : State (permProfile o p)) :
    PathVertex (permuteMovePath o path) Y ↔
      ∃ X, PathVertex path X ∧ permuteState o X = Y := by
  simp only [PathVertex, permuteMovePath_vertices, List.mem_map]

/-- Every actual source vertex gives its corresponding transported target
vertex. -/
theorem permuteMovePath_pathVertex {p : Profile} (o : Orientation)
    {D E X : State p} {path : MovePath (@Move p) D E}
    (hX : PathVertex path X) :
    PathVertex (permuteMovePath o path) (permuteState o X) := by
  rw [PathVertex, permuteMovePath_vertices]
  exact List.mem_map.mpr ⟨X, hX, rfl⟩

/-- A source image-boundary confinement proof transports to the corresponding
finite-set image boundary. -/
theorem permuteMovePath_confined {p : Profile} (o : Orientation)
    {D E B : State p} (path : MovePath (@Move p) D E)
    (hconfined : ∀ X, PathVertex path X → X ⊆ B) :
    ∀ Y, PathVertex (permuteMovePath o path) Y → Y ⊆ permuteState o B := by
  intro Y hY
  obtain ⟨X, hX, hXY⟩ := (permuteMovePath_pathVertex_iff o path Y).mp hY
  rw [← hXY]
  exact Finset.image_mono (permuteTerm o) (hconfined X hX)

/-- Every transported path preserves endpoint evaluation. -/
theorem permuteMovePath_preserves_evaluation {p : Profile} (o : Orientation)
    {D E : State p} (path : MovePath (@Move p) D E) :
    stateEvaluation (permuteState o E) =
      stateEvaluation (permuteState o D) := by
  induction path with
  | singleton => rfl
  | snoc _ h ih => exact (permuteMove o h).preserves_evaluation.trans ih

/-- The designated forward profile-`221` replay after mode permutation, as
actual `OrientationMove` path data. -/
def permuteForwardPath (o : Orientation) :
    MovePath (@OrientationMove profile221 o)
      (permuteState o S0) (permuteState o S2) :=
  permuteMovePath o forwardPath

example (o : Orientation) :
    permuteForwardPath o = permuteMovePath o forwardPath := rfl

/-- The designated reverse profile-`221` replay after mode permutation, as
actual `OrientationMove` path data. -/
def permuteReversePath (o : Orientation) :
    MovePath (@OrientationMove profile221 o)
      (permuteState o S2) (permuteState o S0) :=
  permuteMovePath o reversePath

example (o : Orientation) :
    permuteReversePath o = permuteMovePath o reversePath := rfl

/-- The permuted forward replay has exactly the three pointwise-mapped source
vertices. -/
theorem permuteForwardPath_vertices (o : Orientation) :
    (permuteForwardPath o).vertices =
      [permuteState o S0, permuteState o S1, permuteState o S2] := by
  rw [permuteForwardPath, permuteMovePath_vertices, forwardPath_vertices]
  rfl

/-- The permuted reverse replay has exactly the three pointwise-mapped source
vertices in reverse order. -/
theorem permuteReversePath_vertices (o : Orientation) :
    (permuteReversePath o).vertices =
      [permuteState o S2, permuteState o S1, permuteState o S0] := by
  rw [permuteReversePath, permuteMovePath_vertices, reversePath_vertices]
  rfl

/-- A state is a vertex of the designated permuted forward replay exactly when
it is one of the three displayed mapped states. -/
theorem permuteForwardPath_pathVertex_iff (o : Orientation)
    (Y : State (permProfile o profile221)) :
    PathVertex (permuteForwardPath o) Y ↔
      Y = permuteState o S0 ∨ Y = permuteState o S1 ∨
        Y = permuteState o S2 := by
  simp only [PathVertex, permuteForwardPath_vertices, List.mem_cons,
    List.not_mem_nil, or_false]

/-- A state is a vertex of the designated permuted reverse replay exactly when
it is one of the three displayed mapped states in reverse order. -/
theorem permuteReversePath_pathVertex_iff (o : Orientation)
    (Y : State (permProfile o profile221)) :
    PathVertex (permuteReversePath o) Y ↔
      Y = permuteState o S2 ∨ Y = permuteState o S1 ∨
        Y = permuteState o S0 := by
  simp only [PathVertex, permuteReversePath_vertices, List.mem_cons,
    List.not_mem_nil, or_false]

/-- Both designated permuted paths retain exact length two and exact altitude
three. -/
theorem permuted_path_metrics (o : Orientation) :
    (permuteForwardPath o).length = 2 ∧
    (permuteReversePath o).length = 2 ∧
    (permuteForwardPath o).altitude = 3 ∧
    (permuteReversePath o).altitude = 3 := by
  constructor
  · rw [permuteForwardPath, permuteMovePath_length]
    exact path_metrics.1
  constructor
  · rw [permuteReversePath, permuteMovePath_length]
    exact path_metrics.2.1
  constructor
  · rw [permuteForwardPath, permuteMovePath_altitude]
    exact path_metrics.2.2.1
  · rw [permuteReversePath, permuteMovePath_altitude]
    exact path_metrics.2.2.2

/-- Every vertex of either designated permuted path is contained in the image
of the explicit six-term source boundary. -/
theorem permuted_paths_confined (o : Orientation) :
    (∀ Y, PathVertex (permuteForwardPath o) Y →
      Y ⊆ permuteState o boundary) ∧
    (∀ Y, PathVertex (permuteReversePath o) Y →
      Y ⊆ permuteState o boundary) := by
  constructor
  · simpa only [permuteForwardPath] using
      permuteMovePath_confined o forwardPath paths_confined.1
  · simpa only [permuteReversePath] using
      permuteMovePath_confined o reversePath paths_confined.2.1

/-- The permuted designated endpoints have exact cardinalities two and three. -/
theorem permuted_endpoint_cardinalities (o : Orientation) :
    (permuteState o S0).card = 2 ∧ (permuteState o S2).card = 3 := by
  exact ⟨(permuteState_card o S0).trans state_cardinalities.1,
    (permuteState_card o S2).trans state_cardinalities.2.2⟩

/-- The permuted designated endpoints remain disjoint finite sets. -/
theorem permuted_endpoints_disjoint (o : Orientation) :
    Disjoint (permuteState o S0) (permuteState o S2) := by
  exact (Finset.disjoint_image (permuteTerm_injective o)).mpr
    designated_endpoint_exact_profile_221.1

/-- The image of the designated source endpoint union is exactly the union of
the two permuted endpoints. -/
theorem permuted_endpoint_union (o : Orientation) :
    permuteState o (S0 ∪ S2) = permuteState o S0 ∪ permuteState o S2 := by
  exact permuteState_union o S0 S2

/-- The union of the permuted designated endpoints has exactly five terms. -/
theorem permuted_endpoint_union_card (o : Orientation) :
    (permuteState o S0 ∪ permuteState o S2).card = 5 := by
  calc
    (permuteState o S0 ∪ permuteState o S2).card =
        (permuteState o (S0 ∪ S2)).card :=
      congrArg Finset.card (permuted_endpoint_union o).symm
    _ = (S0 ∪ S2).card := permuteState_card o (S0 ∪ S2)
    _ = 5 := designated_endpoint_exact_profile_221.2.1

/-- The permuted forward and reverse paths prove both orientations of the
endpoint evaluation equality. -/
theorem permuted_endpoint_evaluations (o : Orientation) :
    stateEvaluation (permuteState o S2) =
        stateEvaluation (permuteState o S0) ∧
      stateEvaluation (permuteState o S0) =
        stateEvaluation (permuteState o S2) := by
  exact ⟨permuteMovePath_preserves_evaluation o forwardPath,
    permuteMovePath_preserves_evaluation o reversePath⟩

/-- The union of the permuted designated endpoints is a genuine circuit at
the permuted profile. -/
theorem permuted_endpoint_circuit (o : Orientation) :
    Circuit (@tensorEvaluation (permProfile o profile221))
      (permuteState o S0 ∪ permuteState o S2) := by
  apply tensorEvaluation_circuit_union_of_disjoint_card_two_card_three
    (permuted_endpoints_disjoint o)
  · exact (permuted_endpoint_cardinalities o).1
  · exact (permuted_endpoint_cardinalities o).2
  · exact (permuted_endpoint_evaluations o).2

private theorem source_endpoint_first_span_eq_top :
    Submodule.span F2
      (((S0 ∪ S2).image (fun t => t.1.1) : Finset (CoordinateVector 2)) :
        Set (CoordinateVector 2)) = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [designated_endpoint_exact_profile_221.2.2.2.1,
    Module.finrank_fin_fun]

private theorem source_endpoint_second_span_eq_top :
    Submodule.span F2
      (((S0 ∪ S2).image (fun t => t.2.1.1) : Finset (CoordinateVector 2)) :
        Set (CoordinateVector 2)) = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [designated_endpoint_exact_profile_221.2.2.2.2.1,
    Module.finrank_fin_fun]

private theorem source_endpoint_third_span_eq_top :
    Submodule.span F2
      (((S0 ∪ S2).image (fun t => t.2.2.1) : Finset (CoordinateVector 1)) :
        Set (CoordinateVector 1)) = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [designated_endpoint_exact_profile_221.2.2.2.2.2.1,
    Module.finrank_fin_fun]

private theorem source_endpoint_first_span_eq_top_at_profile :
    Submodule.span F2
      (((S0 ∪ S2).image (fun t => t.1.1) :
        Finset (CoordinateVector profile221.first)) :
        Set (CoordinateVector profile221.first)) = ⊤ := by
  change Submodule.span F2
    (((S0 ∪ S2).image (fun t => t.1.1) : Finset (CoordinateVector 2)) :
      Set (CoordinateVector 2)) = ⊤
  exact source_endpoint_first_span_eq_top

private theorem source_endpoint_second_span_eq_top_at_profile :
    Submodule.span F2
      (((S0 ∪ S2).image (fun t => t.2.1.1) :
        Finset (CoordinateVector profile221.second)) :
        Set (CoordinateVector profile221.second)) = ⊤ := by
  change Submodule.span F2
    (((S0 ∪ S2).image (fun t => t.2.1.1) : Finset (CoordinateVector 2)) :
      Set (CoordinateVector 2)) = ⊤
  exact source_endpoint_second_span_eq_top

private theorem source_endpoint_third_span_eq_top_at_profile :
    Submodule.span F2
      (((S0 ∪ S2).image (fun t => t.2.2.1) :
        Finset (CoordinateVector profile221.third)) :
        Set (CoordinateVector profile221.third)) = ⊤ := by
  change Submodule.span F2
    (((S0 ∪ S2).image (fun t => t.2.2.1) : Finset (CoordinateVector 1)) :
      Set (CoordinateVector 1)) = ⊤
  exact source_endpoint_third_span_eq_top

private theorem span_eq_top_of_finset_eq {n : ℕ}
    {s t : Finset (CoordinateVector n)} (hst : s = t)
    (htop : Submodule.span F2 (t : Set (CoordinateVector n)) = ⊤) :
    Submodule.span F2 (s : Set (CoordinateVector n)) = ⊤ := by
  rw [hst]
  exact htop

/-- The first-factor projection of the permuted designated endpoint union spans
the full first output factor. -/
theorem permuted_endpoint_first_span_eq_top (o : Orientation) :
    Submodule.span F2
      (((permuteState o S0 ∪ permuteState o S2).image (fun t => t.1.1) :
        Finset (CoordinateVector (o.firstDim 2 2 1))) :
        Set (CoordinateVector (o.firstDim 2 2 1))) = ⊤ := by
  rw [← permuted_endpoint_union]
  cases o
  · change Submodule.span F2
      (↑(((S0 ∪ S2).image (permuteTerm .abc)).image (fun t => t.1.1)) :
        Set (CoordinateVector (permProfile .abc profile221).first)) = ⊤
    have hprojection :
        ((S0 ∪ S2).image (permuteTerm .abc)).image (fun t => t.1.1) =
          (S0 ∪ S2).image (fun t => t.1.1) := by
      rw [Finset.image_image]
      apply Finset.image_congr
      intro t _
      rfl
    rw [hprojection]
    change Submodule.span F2
      (((S0 ∪ S2).image (fun t => t.1.1) : Finset (CoordinateVector 2)) :
        Set (CoordinateVector 2)) = ⊤
    exact source_endpoint_first_span_eq_top
  · change Submodule.span F2
      (↑(((S0 ∪ S2).image (permuteTerm .bca)).image (fun t => t.1.1)) :
        Set (CoordinateVector (permProfile .bca profile221).first)) = ⊤
    have hprojection :
        ((S0 ∪ S2).image (permuteTerm .bca)).image (fun t => t.1.1) =
          (S0 ∪ S2).image (fun t => t.2.1.1) := by
      rw [Finset.image_image]
      apply Finset.image_congr
      intro t _
      rfl
    rw [hprojection]
    change Submodule.span F2
      (((S0 ∪ S2).image (fun t => t.2.1.1) : Finset (CoordinateVector 2)) :
        Set (CoordinateVector 2)) = ⊤
    exact source_endpoint_second_span_eq_top
  · change Submodule.span F2
      (↑(((S0 ∪ S2).image (permuteTerm .cab)).image (fun t => t.1.1)) :
        Set (CoordinateVector (permProfile .cab profile221).first)) = ⊤
    have hprojection :
        ((S0 ∪ S2).image (permuteTerm .cab)).image (fun t => t.1.1) =
          (S0 ∪ S2).image (fun t => t.2.2.1) := by
      rw [Finset.image_image]
      apply Finset.image_congr
      intro t _
      rfl
    rw [hprojection]
    change Submodule.span F2
      (((S0 ∪ S2).image (fun t => t.2.2.1) : Finset (CoordinateVector 1)) :
        Set (CoordinateVector 1)) = ⊤
    exact source_endpoint_third_span_eq_top
  · change Submodule.span F2
      (↑(((S0 ∪ S2).image (permuteTerm .acb)).image (fun t => t.1.1)) :
        Set (CoordinateVector (permProfile .acb profile221).first)) = ⊤
    have hprojection :
        ((S0 ∪ S2).image (permuteTerm .acb)).image (fun t => t.1.1) =
          (S0 ∪ S2).image (fun t => t.1.1) := by
      rw [Finset.image_image]
      apply Finset.image_congr
      intro t _
      rfl
    rw [hprojection]
    change Submodule.span F2
      (((S0 ∪ S2).image (fun t => t.1.1) : Finset (CoordinateVector 2)) :
        Set (CoordinateVector 2)) = ⊤
    exact source_endpoint_first_span_eq_top
  · change Submodule.span F2
      (↑(((S0 ∪ S2).image (permuteTerm .cba)).image (fun t => t.1.1)) :
        Set (CoordinateVector (permProfile .cba profile221).first)) = ⊤
    have hprojection :
        ((S0 ∪ S2).image (permuteTerm .cba)).image (fun t => t.1.1) =
          (S0 ∪ S2).image (fun t => t.2.2.1) := by
      rw [Finset.image_image]
      apply Finset.image_congr
      intro t _
      rfl
    rw [hprojection]
    change Submodule.span F2
      (((S0 ∪ S2).image (fun t => t.2.2.1) : Finset (CoordinateVector 1)) :
        Set (CoordinateVector 1)) = ⊤
    exact source_endpoint_third_span_eq_top
  · change Submodule.span F2
      (↑(((S0 ∪ S2).image (permuteTerm .bac)).image (fun t => t.1.1)) :
        Set (CoordinateVector (permProfile .bac profile221).first)) = ⊤
    have hprojection :
        ((S0 ∪ S2).image (permuteTerm .bac)).image (fun t => t.1.1) =
          (S0 ∪ S2).image (fun t => t.2.1.1) := by
      rw [Finset.image_image]
      apply Finset.image_congr
      intro t _
      rfl
    rw [hprojection]
    change Submodule.span F2
      (((S0 ∪ S2).image (fun t => t.2.1.1) : Finset (CoordinateVector 2)) :
        Set (CoordinateVector 2)) = ⊤
    exact source_endpoint_second_span_eq_top

/-- The second-factor projection of the permuted designated endpoint union
spans the full second output factor. -/
theorem permuted_endpoint_second_span_eq_top (o : Orientation) :
    Submodule.span F2
      (((permuteState o S0 ∪ permuteState o S2).image (fun t => t.2.1.1) :
        Finset (CoordinateVector (o.secondDim 2 2 1))) :
        Set (CoordinateVector (o.secondDim 2 2 1))) = ⊤ := by
  rw [← permuted_endpoint_union]
  cases o
  · change Submodule.span F2
      (↑(((S0 ∪ S2).image (permuteTerm .abc)).image (fun t => t.2.1.1)) :
        Set (CoordinateVector (permProfile .abc profile221).second)) = ⊤
    apply span_eq_top_of_finset_eq ?_ source_endpoint_second_span_eq_top_at_profile
    rw [Finset.image_image]
    apply Finset.image_congr
    intro t _
    rfl
  · change Submodule.span F2
      (↑(((S0 ∪ S2).image (permuteTerm .bca)).image (fun t => t.2.1.1)) :
        Set (CoordinateVector (permProfile .bca profile221).second)) = ⊤
    apply span_eq_top_of_finset_eq ?_ source_endpoint_third_span_eq_top_at_profile
    rw [Finset.image_image]
    apply Finset.image_congr
    intro t _
    rfl
  · change Submodule.span F2
      (↑(((S0 ∪ S2).image (permuteTerm .cab)).image (fun t => t.2.1.1)) :
        Set (CoordinateVector (permProfile .cab profile221).second)) = ⊤
    apply span_eq_top_of_finset_eq ?_ source_endpoint_first_span_eq_top_at_profile
    rw [Finset.image_image]
    apply Finset.image_congr
    intro t _
    rfl
  · change Submodule.span F2
      (↑(((S0 ∪ S2).image (permuteTerm .acb)).image (fun t => t.2.1.1)) :
        Set (CoordinateVector (permProfile .acb profile221).second)) = ⊤
    apply span_eq_top_of_finset_eq ?_ source_endpoint_third_span_eq_top_at_profile
    rw [Finset.image_image]
    apply Finset.image_congr
    intro t _
    rfl
  · change Submodule.span F2
      (↑(((S0 ∪ S2).image (permuteTerm .cba)).image (fun t => t.2.1.1)) :
        Set (CoordinateVector (permProfile .cba profile221).second)) = ⊤
    apply span_eq_top_of_finset_eq ?_ source_endpoint_second_span_eq_top_at_profile
    rw [Finset.image_image]
    apply Finset.image_congr
    intro t _
    rfl
  · change Submodule.span F2
      (↑(((S0 ∪ S2).image (permuteTerm .bac)).image (fun t => t.2.1.1)) :
        Set (CoordinateVector (permProfile .bac profile221).second)) = ⊤
    apply span_eq_top_of_finset_eq ?_ source_endpoint_first_span_eq_top_at_profile
    rw [Finset.image_image]
    apply Finset.image_congr
    intro t _
    rfl

/-- The third-factor projection of the permuted designated endpoint union spans
the full third output factor. -/
theorem permuted_endpoint_third_span_eq_top (o : Orientation) :
    Submodule.span F2
      (((permuteState o S0 ∪ permuteState o S2).image (fun t => t.2.2.1) :
        Finset (CoordinateVector (o.thirdDim 2 2 1))) :
        Set (CoordinateVector (o.thirdDim 2 2 1))) = ⊤ := by
  rw [← permuted_endpoint_union]
  cases o
  · change Submodule.span F2
      (↑(((S0 ∪ S2).image (permuteTerm .abc)).image (fun t => t.2.2.1)) :
        Set (CoordinateVector (permProfile .abc profile221).third)) = ⊤
    apply span_eq_top_of_finset_eq ?_ source_endpoint_third_span_eq_top_at_profile
    rw [Finset.image_image]
    apply Finset.image_congr
    intro t _
    rfl
  · change Submodule.span F2
      (↑(((S0 ∪ S2).image (permuteTerm .bca)).image (fun t => t.2.2.1)) :
        Set (CoordinateVector (permProfile .bca profile221).third)) = ⊤
    apply span_eq_top_of_finset_eq ?_ source_endpoint_first_span_eq_top_at_profile
    rw [Finset.image_image]
    apply Finset.image_congr
    intro t _
    rfl
  · change Submodule.span F2
      (↑(((S0 ∪ S2).image (permuteTerm .cab)).image (fun t => t.2.2.1)) :
        Set (CoordinateVector (permProfile .cab profile221).third)) = ⊤
    apply span_eq_top_of_finset_eq ?_ source_endpoint_second_span_eq_top_at_profile
    rw [Finset.image_image]
    apply Finset.image_congr
    intro t _
    rfl
  · change Submodule.span F2
      (↑(((S0 ∪ S2).image (permuteTerm .acb)).image (fun t => t.2.2.1)) :
        Set (CoordinateVector (permProfile .acb profile221).third)) = ⊤
    apply span_eq_top_of_finset_eq ?_ source_endpoint_second_span_eq_top_at_profile
    rw [Finset.image_image]
    apply Finset.image_congr
    intro t _
    rfl
  · change Submodule.span F2
      (↑(((S0 ∪ S2).image (permuteTerm .cba)).image (fun t => t.2.2.1)) :
        Set (CoordinateVector (permProfile .cba profile221).third)) = ⊤
    apply span_eq_top_of_finset_eq ?_ source_endpoint_first_span_eq_top_at_profile
    rw [Finset.image_image]
    apply Finset.image_congr
    intro t _
    rfl
  · change Submodule.span F2
      (↑(((S0 ∪ S2).image (permuteTerm .bac)).image (fun t => t.2.2.1)) :
        Set (CoordinateVector (permProfile .bac profile221).third)) = ⊤
    apply span_eq_top_of_finset_eq ?_ source_endpoint_third_span_eq_top_at_profile
    rw [Finset.image_image]
    apply Finset.image_congr
    intro t _
    rfl

/-- The first projected span of the permuted designated endpoint union has
exactly the first permuted profile dimension. -/
theorem permuted_endpoint_first_finrank (o : Orientation) :
    Module.finrank F2
      (Submodule.span F2
        (((permuteState o S0 ∪ permuteState o S2).image (fun t => t.1.1) :
          Finset (CoordinateVector (o.firstDim 2 2 1))) :
          Set (CoordinateVector (o.firstDim 2 2 1)))) =
      o.firstDim 2 2 1 := by
  rw [permuted_endpoint_first_span_eq_top, finrank_top,
    Module.finrank_fin_fun]

/-- The second projected span of the permuted designated endpoint union has
exactly the second permuted profile dimension. -/
theorem permuted_endpoint_second_finrank (o : Orientation) :
    Module.finrank F2
      (Submodule.span F2
        (((permuteState o S0 ∪ permuteState o S2).image (fun t => t.2.1.1) :
          Finset (CoordinateVector (o.secondDim 2 2 1))) :
          Set (CoordinateVector (o.secondDim 2 2 1)))) =
      o.secondDim 2 2 1 := by
  rw [permuted_endpoint_second_span_eq_top, finrank_top,
    Module.finrank_fin_fun]

/-- The third projected span of the permuted designated endpoint union has
exactly the third permuted profile dimension. -/
theorem permuted_endpoint_third_finrank (o : Orientation) :
    Module.finrank F2
      (Submodule.span F2
        (((permuteState o S0 ∪ permuteState o S2).image (fun t => t.2.2.1) :
          Finset (CoordinateVector (o.thirdDim 2 2 1))) :
          Set (CoordinateVector (o.thirdDim 2 2 1)))) =
      o.thirdDim 2 2 1 := by
  rw [permuted_endpoint_third_span_eq_top, finrank_top,
    Module.finrank_fin_fun]

/-- Narrow designated profile-`221` checkpoint after any of the six explicit
mode permutations.  It packages only the transported named endpoints and
named replay paths: no orbit coverage or arbitrary-circuit normalization is
asserted. -/
theorem permuted_designated_endpoint_exact_profile_221 (o : Orientation) :
    (Disjoint (permuteState o S0) (permuteState o S2) ∧
      permuteState o (S0 ∪ S2) = permuteState o S0 ∪ permuteState o S2 ∧
      (permuteState o S0).card = 2 ∧
      (permuteState o S2).card = 3 ∧
      (permuteState o S0 ∪ permuteState o S2).card = 5 ∧
      Circuit (@tensorEvaluation (permProfile o profile221))
        (permuteState o S0 ∪ permuteState o S2)) ∧
    (stateEvaluation (permuteState o S2) = stateEvaluation (permuteState o S0) ∧
      stateEvaluation (permuteState o S0) = stateEvaluation (permuteState o S2)) ∧
    (Module.finrank F2
          (Submodule.span F2
            (((permuteState o S0 ∪ permuteState o S2).image
              (fun t => t.1.1) :
              Finset (CoordinateVector (o.firstDim 2 2 1))) :
              Set (CoordinateVector (o.firstDim 2 2 1)))) =
        o.firstDim 2 2 1 ∧
      Module.finrank F2
          (Submodule.span F2
            (((permuteState o S0 ∪ permuteState o S2).image
              (fun t => t.2.1.1) :
              Finset (CoordinateVector (o.secondDim 2 2 1))) :
              Set (CoordinateVector (o.secondDim 2 2 1)))) =
        o.secondDim 2 2 1 ∧
      Module.finrank F2
          (Submodule.span F2
            (((permuteState o S0 ∪ permuteState o S2).image
              (fun t => t.2.2.1) :
              Finset (CoordinateVector (o.thirdDim 2 2 1))) :
              Set (CoordinateVector (o.thirdDim 2 2 1)))) =
        o.thirdDim 2 2 1) ∧
    ((permuteForwardPath o).length = 2 ∧
      (permuteReversePath o).length = 2 ∧
      (permuteForwardPath o).altitude = 3 ∧
      (permuteReversePath o).altitude = 3) ∧
    ((∀ Y, PathVertex (permuteForwardPath o) Y →
        Y ⊆ permuteState o boundary) ∧
      (∀ Y, PathVertex (permuteReversePath o) Y →
        Y ⊆ permuteState o boundary)) := by
  have hcards := permuted_endpoint_cardinalities o
  have hendpoints :
      Disjoint (permuteState o S0) (permuteState o S2) ∧
        permuteState o (S0 ∪ S2) = permuteState o S0 ∪ permuteState o S2 ∧
        (permuteState o S0).card = 2 ∧
        (permuteState o S2).card = 3 ∧
        (permuteState o S0 ∪ permuteState o S2).card = 5 ∧
        Circuit (@tensorEvaluation (permProfile o profile221))
          (permuteState o S0 ∪ permuteState o S2) := by
    constructor
    · exact permuted_endpoints_disjoint o
    constructor
    · exact permuted_endpoint_union o
    constructor
    · exact hcards.1
    constructor
    · exact hcards.2
    constructor
    · exact permuted_endpoint_union_card o
    · exact permuted_endpoint_circuit o
  have hspans := And.intro (permuted_endpoint_first_finrank o)
    (And.intro (permuted_endpoint_second_finrank o)
      (permuted_endpoint_third_finrank o))
  exact And.intro hendpoints
    (And.intro (permuted_endpoint_evaluations o)
      (And.intro hspans
        (And.intro (permuted_path_metrics o) (permuted_paths_confined o))))

#check @permProfile
#check @orientationMode
#check @tensorEvaluation_permuteTerm
#check @stateEvaluation_permuteState
#check @OrientationGeneratedSplit
#check @OrientationSourceFlip
#check @OrientationNarrowReduction
#check @OrientationMove.generatedSplit
#check @OrientationMove.sourceThirdFlip
#check @OrientationMove.directedNarrowReduction
#check @OrientationMove
#check @permuteMovePath
#check @permuteForwardPath
#check @permuteReversePath
#check @permuted_designated_endpoint_exact_profile_221
#print axioms tensorEvaluation_permuteTerm
#print axioms stateEvaluation_permuteState
#print axioms permuteMove
#print axioms permuteMovePath
#print axioms permuted_endpoint_circuit
#print axioms permuted_designated_endpoint_exact_profile_221

end BilinearComplexity.NormalizedBinaryModePermutation
