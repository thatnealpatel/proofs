import BilinearComplexity.NormalizedBinaryModePermutation

set_option autoImplicit false

/-!
# Fixed-profile all-mode normalized binary moves

This module defines a proof-facing, fixed-profile existential union of the exact
orientation relational images from `NormalizedBinaryModePermutation`.  Each
edge independently selects an orientation and a source profile whose permuted
profile is the fixed target profile.  The selected `OrientationMove` witness
retains the operation tag and direction.

This is not an executable completeness statement, a coordinate-native move
semantics, or an invariance claim for the old ordered `Move` relation.

AI disclosure: produced with AI assistance (see `README`).
-/

namespace BilinearComplexity.NormalizedBinaryAllModeMove

open BinaryCircuit
open NormalizedBinaryCarrier
open NormalizedBinaryReplay221
open NormalizedBinaryModePermutation
open Scheme.Action

/-- At a fixed target profile, an edge may use any exact orientation relational
image.  The source profile and orientation are selected independently for each
edge, and the target states are pulled back along the displayed profile
equality. -/
def AllModeMove {q : Profile} (D E : State q) : Prop :=
  ∃ (p : Profile) (o : Orientation) (h : permProfile o p = q),
    @OrientationMove p o
      (cast (congrArg State h.symm) D)
      (cast (congrArg State h.symm) E)

example {q : Profile} (D E : State q) :
    AllModeMove D E ↔
      ∃ (p : Profile) (o : Orientation) (h : permProfile o p = q),
        @OrientationMove p o
          (cast (congrArg State h.symm) D)
          (cast (congrArg State h.symm) E) :=
  Iff.rfl

/-- An exact orientation edge enters the all-mode union at its target profile.
The orientation-move witness, including its operation tag and direction, is
unchanged. -/
theorem allModeMove_of_orientationMove {p : Profile} {o : Orientation}
    {D E : State (permProfile o p)} (h : @OrientationMove p o D E) :
    @AllModeMove (permProfile o p) D E := by
  exact ⟨p, o, rfl, h⟩

/-- An old ordered move enters the all-mode union through the identity
orientation.  This is only an inclusion and supplies no converse or
mode-permutation invariance theorem for `Move`. -/
theorem allModeMove_of_move {q : Profile} {D E : State q}
    (h : @Move q D E) : @AllModeMove q D E := by
  rcases q with ⟨a, b, c⟩
  exact ⟨_, .abc, rfl, orientationMove_abc_iff.mpr h⟩

/-- Every all-mode edge preserves normalized state evaluation because its
selected exact orientation edge does. -/
theorem AllModeMove.preserves_evaluation {q : Profile} {D E : State q}
    (h : @AllModeMove q D E) : stateEvaluation E = stateEvaluation D := by
  rcases h with ⟨p, o, rfl, hmove⟩
  exact hmove.preserves_evaluation

/-- Every all-mode edge retains an old ordered move together with its exact
orientation, source profile, and transported endpoints. -/
theorem AllModeMove.provenance {q : Profile} {D E : State q}
    (h : @AllModeMove q D E) :
    ∃ (p : Profile) (o : Orientation) (hp : permProfile o p = q)
        (D₀ E₀ : State p),
      @Move p D₀ E₀ ∧
      D = cast (congrArg State hp) (permuteState o D₀) ∧
      E = cast (congrArg State hp) (permuteState o E₀) := by
  rcases h with ⟨p, o, rfl, hmove⟩
  obtain ⟨D₀, E₀, hold, hD, hE⟩ := hmove.provenance
  exact ⟨p, o, rfl, D₀, E₀, hold, hD, hE⟩

/-- The selected operation tag gives exactly one of the three possible
cardinality changes: Split increases by one, Flip preserves cardinality, and
Reduction decreases by one. -/
theorem AllModeMove.card_change {q : Profile} {D E : State q}
    (h : @AllModeMove q D E) :
    E.card = D.card + 1 ∨ E.card = D.card ∨ E.card + 1 = D.card := by
  rcases h with ⟨p, o, rfl, hmove⟩
  obtain ⟨D₀, E₀, hold, rfl, rfl⟩ := hmove.provenance
  simp only [permuteState_card]
  cases hold with
  | generatedFirstSplit hsplit =>
      exact Or.inl hsplit.card_eq
  | sourceThirdFlip hflip =>
      exact Or.inr (Or.inl hflip.card_eq)
  | directedNarrowPairReduction hreduction =>
      exact Or.inr (Or.inr hreduction.card_add_one_eq)

/-- Every concrete path whose edges independently select all-mode witnesses
preserves endpoint evaluation. -/
theorem allModeMovePath_preserves_evaluation {q : Profile} {D E : State q}
    (path : MovePath (@AllModeMove q) D E) :
    stateEvaluation E = stateEvaluation D := by
  induction path with
  | singleton => rfl
  | snoc path h ih => exact h.preserves_evaluation.trans ih

/-- Forget the common orientation of an existing orientation-move path.  This
changes only the edge relation and leaves every state vertex unchanged. -/
def orientationMovePathToAllModeMovePath {p : Profile} {o : Orientation}
    {D E : State (permProfile o p)}
    (path : MovePath (@OrientationMove p o) D E) :
    MovePath (@AllModeMove (permProfile o p)) D E :=
  path.mono fun h => allModeMove_of_orientationMove h

example {p : Profile} {o : Orientation}
    (D : State (permProfile o p)) :
    orientationMovePathToAllModeMovePath
        (.singleton D : MovePath (@OrientationMove p o) D D) =
      (.singleton D : MovePath (@AllModeMove (permProfile o p)) D D) := by
  simp only [orientationMovePathToAllModeMovePath, MovePath.mono]

/-- Forgetting a path's common orientation leaves its ordered vertex list
exactly unchanged. -/
@[simp] theorem orientationMovePathToAllModeMovePath_vertices
    {p : Profile} {o : Orientation} {D E : State (permProfile o p)}
    (path : MovePath (@OrientationMove p o) D E) :
    (orientationMovePathToAllModeMovePath path).vertices = path.vertices := by
  induction path with
  | singleton =>
      simp only [orientationMovePathToAllModeMovePath, MovePath.mono,
        MovePath.vertices]
  | snoc path h ih =>
      simp only [orientationMovePathToAllModeMovePath, MovePath.mono,
        MovePath.vertices]
      change (orientationMovePathToAllModeMovePath path).vertices ++ [_] =
        path.vertices ++ [_]
      rw [ih]

/-- Forgetting a path's common orientation preserves its exact number of
edges. -/
@[simp] theorem orientationMovePathToAllModeMovePath_length
    {p : Profile} {o : Orientation} {D E : State (permProfile o p)}
    (path : MovePath (@OrientationMove p o) D E) :
    (orientationMovePathToAllModeMovePath path).length = path.length := by
  induction path with
  | singleton =>
      simp only [orientationMovePathToAllModeMovePath, MovePath.mono,
        MovePath.length]
  | snoc path h ih =>
      simp only [orientationMovePathToAllModeMovePath, MovePath.mono,
        MovePath.length]
      change (orientationMovePathToAllModeMovePath path).length + 1 =
        path.length + 1
      rw [ih]

/-- Forgetting a path's common orientation preserves its exact altitude. -/
@[simp] theorem orientationMovePathToAllModeMovePath_altitude
    {p : Profile} {o : Orientation} {D E : State (permProfile o p)}
    (path : MovePath (@OrientationMove p o) D E) :
    (orientationMovePathToAllModeMovePath path).altitude = path.altitude := by
  induction path with
  | singleton =>
      simp only [orientationMovePathToAllModeMovePath, MovePath.mono,
        MovePath.altitude]
  | snoc path h ih =>
      simp only [orientationMovePathToAllModeMovePath, MovePath.mono,
        MovePath.altitude]
      change max (orientationMovePathToAllModeMovePath path).altitude _ =
        max path.altitude _
      rw [ih]

/-- Forgetting a path's common orientation preserves the predicate of being an
actual path vertex. -/
theorem orientationMovePathToAllModeMovePath_pathVertex_iff
    {p : Profile} {o : Orientation} {D E X : State (permProfile o p)}
    (path : MovePath (@OrientationMove p o) D E) :
    PathVertex (orientationMovePathToAllModeMovePath path) X ↔
      PathVertex path X := by
  simp only [PathVertex, orientationMovePathToAllModeMovePath_vertices]

/-- Any boundary confinement proof transfers unchanged when a common path
orientation is forgotten. -/
theorem orientationMovePathToAllModeMovePath_confined
    {p : Profile} {o : Orientation} {D E B : State (permProfile o p)}
    (path : MovePath (@OrientationMove p o) D E)
    (hconfined : ∀ X, PathVertex path X → X ⊆ B) :
    ∀ X, PathVertex (orientationMovePathToAllModeMovePath path) X → X ⊆ B := by
  intro X hX
  exact hconfined X
    ((orientationMovePathToAllModeMovePath_pathVertex_iff path).mp hX)

/-- Permute an old ordered path into an exact orientation path and then forget
the common orientation into the fixed-profile all-mode edge relation. -/
def permuteAllModeMovePath {p : Profile} (o : Orientation) {D E : State p}
    (path : MovePath (@Move p) D E) :
    MovePath (@AllModeMove (permProfile o p))
      (permuteState o D) (permuteState o E) :=
  orientationMovePathToAllModeMovePath (permuteMovePath o path)

example {p : Profile} (o : Orientation) (D : State p) :
    permuteAllModeMovePath o (.singleton D : MovePath (@Move p) D D) =
      (.singleton (permuteState o D) :
        MovePath (@AllModeMove (permProfile o p))
          (permuteState o D) (permuteState o D)) := by
  simp only [permuteAllModeMovePath, permuteMovePath,
    orientationMovePathToAllModeMovePath, MovePath.mono]

/-- Permuting an old path into the all-mode relation maps its ordered vertex
list pointwise by `permuteState`. -/
theorem permuteAllModeMovePath_vertices {p : Profile} (o : Orientation)
    {D E : State p} (path : MovePath (@Move p) D E) :
    (permuteAllModeMovePath o path).vertices =
      path.vertices.map (permuteState o) := by
  calc
    (permuteAllModeMovePath o path).vertices =
        (permuteMovePath o path).vertices :=
      orientationMovePathToAllModeMovePath_vertices (permuteMovePath o path)
    _ = path.vertices.map (permuteState o) := permuteMovePath_vertices o path

/-- Permuting an old path into the all-mode relation preserves its exact number
of edges. -/
@[simp] theorem permuteAllModeMovePath_length {p : Profile} (o : Orientation)
    {D E : State p} (path : MovePath (@Move p) D E) :
    (permuteAllModeMovePath o path).length = path.length := by
  calc
    (permuteAllModeMovePath o path).length =
        (permuteMovePath o path).length :=
      orientationMovePathToAllModeMovePath_length (permuteMovePath o path)
    _ = path.length := permuteMovePath_length o path

/-- Permuting an old path into the all-mode relation preserves its exact
altitude. -/
@[simp] theorem permuteAllModeMovePath_altitude {p : Profile} (o : Orientation)
    {D E : State p} (path : MovePath (@Move p) D E) :
    (permuteAllModeMovePath o path).altitude = path.altitude := by
  calc
    (permuteAllModeMovePath o path).altitude =
        (permuteMovePath o path).altitude :=
      orientationMovePathToAllModeMovePath_altitude (permuteMovePath o path)
    _ = path.altitude := permuteMovePath_altitude o path

/-- Image-boundary confinement transfers from an old path to its permuted
all-mode path. -/
theorem permuteAllModeMovePath_confined {p : Profile} (o : Orientation)
    {D E B : State p} (path : MovePath (@Move p) D E)
    (hconfined : ∀ X, PathVertex path X → X ⊆ B) :
    ∀ Y, PathVertex (permuteAllModeMovePath o path) Y →
      Y ⊆ permuteState o B := by
  intro Y hY
  exact permuteMovePath_confined o path hconfined Y
    ((orientationMovePathToAllModeMovePath_pathVertex_iff
      (permuteMovePath o path)).mp hY)

/-- The designated forward profile-`221` replay, permuted by any orientation
and viewed as a path in the fixed target-profile all-mode relation. -/
def allModeForwardPath (o : Orientation) :
    MovePath (@AllModeMove (permProfile o profile221))
      (permuteState o S0) (permuteState o S2) :=
  permuteAllModeMovePath o forwardPath

example (o : Orientation) :
    allModeForwardPath o = permuteAllModeMovePath o forwardPath := rfl

/-- The designated reverse profile-`221` replay, permuted by any orientation
and viewed as a path in the fixed target-profile all-mode relation. -/
def allModeReversePath (o : Orientation) :
    MovePath (@AllModeMove (permProfile o profile221))
      (permuteState o S2) (permuteState o S0) :=
  permuteAllModeMovePath o reversePath

example (o : Orientation) :
    allModeReversePath o = permuteAllModeMovePath o reversePath := rfl

/-- The designated all-mode forward replay has exactly the three pointwise
permuted source vertices. -/
theorem allModeForwardPath_vertices (o : Orientation) :
    (allModeForwardPath o).vertices =
      [permuteState o S0, permuteState o S1, permuteState o S2] := by
  rw [allModeForwardPath, permuteAllModeMovePath_vertices,
    forwardPath_vertices]
  rfl

/-- The designated all-mode reverse replay has exactly the three pointwise
permuted source vertices in reverse order. -/
theorem allModeReversePath_vertices (o : Orientation) :
    (allModeReversePath o).vertices =
      [permuteState o S2, permuteState o S1, permuteState o S0] := by
  rw [allModeReversePath, permuteAllModeMovePath_vertices,
    reversePath_vertices]
  rfl

/-- Both designated all-mode paths retain exact length two and exact altitude
three after every orientation. -/
theorem allMode_path_metrics (o : Orientation) :
    (allModeForwardPath o).length = 2 ∧
    (allModeReversePath o).length = 2 ∧
    (allModeForwardPath o).altitude = 3 ∧
    (allModeReversePath o).altitude = 3 := by
  constructor
  · rw [allModeForwardPath, permuteAllModeMovePath_length]
    exact path_metrics.1
  constructor
  · rw [allModeReversePath, permuteAllModeMovePath_length]
    exact path_metrics.2.1
  constructor
  · rw [allModeForwardPath, permuteAllModeMovePath_altitude]
    exact path_metrics.2.2.1
  · rw [allModeReversePath, permuteAllModeMovePath_altitude]
    exact path_metrics.2.2.2

/-- Every vertex of either designated all-mode path is contained in the
permuted image of the explicit six-term source boundary. -/
theorem allMode_paths_confined (o : Orientation) :
    (∀ Y, PathVertex (allModeForwardPath o) Y →
      Y ⊆ permuteState o boundary) ∧
    (∀ Y, PathVertex (allModeReversePath o) Y →
      Y ⊆ permuteState o boundary) := by
  constructor
  · simpa only [allModeForwardPath] using
      permuteAllModeMovePath_confined o forwardPath paths_confined.1
  · simpa only [allModeReversePath] using
      permuteAllModeMovePath_confined o reversePath paths_confined.2.1

/-- The all-mode relation is nonempty at the identity orientation: the first
designated profile-`221` Split is an edge. -/
theorem allModeMove_identity_nonempty :
    @AllModeMove profile221 S0 S1 :=
  allModeMove_of_move (.generatedFirstSplit forwardSplit)

/-- The all-mode relation is also nonempty at a nonidentity orientation: the
first designated Split transported by `bca` remains an exact tagged edge. -/
theorem allModeMove_bca_nonempty :
    @AllModeMove (permProfile .bca profile221)
      (permuteState .bca S0) (permuteState .bca S1) :=
  allModeMove_of_orientationMove
    (permuteMove .bca (.generatedFirstSplit forwardSplit))

#check @AllModeMove
#check @allModeMove_of_orientationMove
#check @allModeMove_of_move
#check @AllModeMove.preserves_evaluation
#check @AllModeMove.provenance
#check @AllModeMove.card_change
#check @allModeMovePath_preserves_evaluation
#check @orientationMovePathToAllModeMovePath
#check @permuteAllModeMovePath
#check @allModeForwardPath
#check @allModeReversePath
#check @allModeMove_identity_nonempty
#check @allModeMove_bca_nonempty
#print axioms AllModeMove.preserves_evaluation
#print axioms AllModeMove.card_change
#print axioms allModeMovePath_preserves_evaluation
#print axioms permuteAllModeMovePath_confined
#print axioms allMode_paths_confined
#print axioms allModeMove_bca_nonempty

end BilinearComplexity.NormalizedBinaryAllModeMove
