import BilinearComplexity.BinaryContextualNormalizedCompiler

set_option autoImplicit false

/-!
# Reflection of normalized contextual competitors through orbit actions

A checked finite profile action already transports native normalized
`AllModeMove` edges forward. Because normalized state space is finite and the
action is injective, its induced self-map on the subtype of valid edges is
surjective; consequently it also reflects the edge relation. This avoids
constructing an explicit inverse general-linear action.

The data-bearing path pullback below is executable: every vertex is obtained
with the existing finite-filter `pullbackState`; finite choice occurs only in
the erased proof that each pulled-back edge is valid. The classified transport
first orients an arbitrary contextual competitor, then pulls it through the
compiler-selected action to the selected replay row. Exact length, altitude,
and endpoint-disjoint context are preserved, allowing selected-row lower
bounds to transfer to every classified normalized relation.

This module does not provide the finite selected-row lower bounds themselves or
assemble the final ambient contextual compiler.

AI disclosure: produced with AI assistance (see `README`).
-/

namespace BilinearComplexity.BinaryContextualOrbitReflection

open BinaryCircuit
open NormalizedBinaryCarrier
open NormalizedBinaryAllModeMove
open NormalizedBinaryAllModePermutation
open NormalizedBinaryFiniteAction
open NormalizedBinaryOrbitClassification
open NormalizedBinaryProfileOrientation
open NormalizedBinaryRelationEnumeration
open BilinearComplexity.BinaryContextualOrbitTransport
open BilinearComplexity.BinaryContextualNormalizedCompiler

/-- A bijective finite profile action reflects the native normalized move relation. -/
theorem reflectActionAllModeMove {p : Profile} (action : ProfileAction p)
    {D E : State p}
    (move : @AllModeMove p (action.actState D) (action.actState E)) :
    @AllModeMove p D E := by
  let Edge := {edge : State p × State p //
    @AllModeMove p edge.1 edge.2}
  let actEdge : Edge → Edge := fun edge =>
    ⟨(action.actState edge.1.1, action.actState edge.1.2),
      transportActionAllModeMove action edge.2⟩
  have hStateInjective : Function.Injective action.actState :=
    Function.LeftInverse.injective (pullbackState_actState action)
  have hEdgeInjective : Function.Injective actEdge := by
    intro first second heq
    have hpair :
        (action.actState first.1.1, action.actState first.1.2) =
          (action.actState second.1.1, action.actState second.1.2) := by
      simpa only [actEdge] using congrArg (fun edge : Edge => edge.1) heq
    apply Subtype.ext
    exact Prod.ext
      (hStateInjective (congrArg Prod.fst hpair))
      (hStateInjective (congrArg Prod.snd hpair))
  have hEdgeSurjective : Function.Surjective actEdge :=
    Finite.surjective_of_injective hEdgeInjective
  obtain ⟨source, hsource⟩ :=
    hEdgeSurjective ⟨(action.actState D, action.actState E), move⟩
  have hpair :
      (action.actState source.1.1, action.actState source.1.2) =
        (action.actState D, action.actState E) := by
    simpa only [actEdge] using congrArg (fun edge : Edge => edge.1) hsource
  have hleft : source.1.1 = D :=
    hStateInjective (congrArg Prod.fst hpair)
  have hright : source.1.2 = E :=
    hStateInjective (congrArg Prod.snd hpair)
  simpa only [hleft, hright] using source.2

/-! A concrete normalized split and any checked identity action jointly witness
that the reflected-move theorem's hypotheses are satisfiable. -/

example : ∃ action : ProfileAction profile221,
    @AllModeMove profile221
      (action.actState NormalizedBinaryReplay221.S0)
      (action.actState NormalizedBinaryReplay221.S1) := by
  let action : ProfileAction profile221 :=
    { first := 1
      second := 1
      third := 1
      orientation := .abc
      profile_eq := rfl }
  let move : @AllModeMove profile221
      NormalizedBinaryReplay221.S0 NormalizedBinaryReplay221.S1 :=
    allModeMove_of_move (.generatedFirstSplit
      NormalizedBinaryReplay221.forwardSplit)
  exact ⟨action, transportActionAllModeMove action move⟩

/-- Pull every vertex and edge of a native normalized path back through a checked action. -/
def pullbackPath {p : Profile} (action : ProfileAction p) :
    {D E : State p} → MovePath (@AllModeMove p) D E →
      MovePath (@AllModeMove p) (pullbackState action D) (pullbackState action E)
  | _, _, .singleton D => .singleton (pullbackState action D)
  | _, _, .snoc path move =>
      .snoc (pullbackPath action path)
        (reflectActionAllModeMove action (by
          simpa only [actState_pullbackState] using move))

/-- Pulling a path back preserves its exact edge count. -/
@[simp] theorem pullbackPath_length {p : Profile} (action : ProfileAction p)
    {D E : State p} (path : MovePath (@AllModeMove p) D E) :
    (pullbackPath action path).length = path.length := by
  induction path with
  | singleton => simp only [pullbackPath, MovePath.length]
  | snoc path move ih => simp only [pullbackPath, MovePath.length, ih]

/-- Pulling a path back preserves its exact altitude. -/
@[simp] theorem pullbackPath_altitude {p : Profile} (action : ProfileAction p)
    {D E : State p} (path : MovePath (@AllModeMove p) D E) :
    (pullbackPath action path).altitude = path.altitude := by
  induction path with
  | singleton =>
      simp only [pullbackPath, MovePath.altitude, pullbackState_card]
  | snoc path move ih =>
      simp only [pullbackPath, MovePath.altitude, ih, pullbackState_card]

/-- Pulling a path back maps its concrete vertex list pointwise by executable state pullback. -/
theorem pullbackPath_vertices {p : Profile} (action : ProfileAction p)
    {D E : State p} (path : MovePath (@AllModeMove p) D E) :
    (pullbackPath action path).vertices =
      path.vertices.map (pullbackState action) := by
  induction path with
  | singleton =>
      simp only [pullbackPath, MovePath.vertices, List.map_singleton]
  | snoc path move ih =>
      simp only [pullbackPath, MovePath.vertices, ih, List.map_append,
        List.map_singleton]

/-- Orient every vertex and native edge of a normalized path into its selected canonical profile. -/
def orientPath {p : Profile} (choice : ProfileOrientation p)
    {D E : State p} (path : MovePath (@AllModeMove p) D E) :
    MovePath (@AllModeMove choice.family.profile)
      (choice.orientState D) (choice.orientState E) :=
  castAllModePathProfile choice.profile_eq
    (permuteAllModePath choice.orientation path)

/-- Orienting a normalized path preserves its exact edge count. -/
@[simp] theorem orientPath_length {p : Profile} (choice : ProfileOrientation p)
    {D E : State p} (path : MovePath (@AllModeMove p) D E) :
    (orientPath choice path).length = path.length := by
  unfold orientPath
  calc
    (castAllModePathProfile choice.profile_eq
      (permuteAllModePath choice.orientation path)).length =
        (permuteAllModePath choice.orientation path).length :=
      castAllModePathProfile_length choice.profile_eq _
    _ = path.length := permuteAllModePath_length choice.orientation path

/-- Orienting a normalized path preserves its exact altitude. -/
@[simp] theorem orientPath_altitude {p : Profile} (choice : ProfileOrientation p)
    {D E : State p} (path : MovePath (@AllModeMove p) D E) :
    (orientPath choice path).altitude = path.altitude := by
  unfold orientPath
  calc
    (castAllModePathProfile choice.profile_eq
      (permuteAllModePath choice.orientation path)).altitude =
        (permuteAllModePath choice.orientation path).altitude :=
      castAllModePathProfile_altitude choice.profile_eq _
    _ = path.altitude := permuteAllModePath_altitude choice.orientation path

private theorem orientedContextLeft {p : Profile} {target : ExactRelation p}
    (compiled : ClassifiedCompilation target) (K : State p) :
    compiled.compilation.choice.orientState (K ∪ target.1.left) =
      compiled.compilation.choice.orientState K ∪
        compiled.compilation.oriented.1.left := by
  rw [compiled.compilation.choice.orientState_union,
    ← compiled.compilation.oriented_left]

private theorem orientedContextRight {p : Profile} {target : ExactRelation p}
    (compiled : ClassifiedCompilation target) (K : State p) :
    compiled.compilation.choice.orientState (K ∪ target.1.right) =
      compiled.compilation.choice.orientState K ∪
        compiled.compilation.oriented.1.right := by
  rw [compiled.compilation.choice.orientState_union,
    ← compiled.compilation.oriented_right]

/-- Orient a competitor at a classified relation while exposing its oriented contextual endpoints. -/
def orientClassifiedContextPath {p : Profile} {target : ExactRelation p}
    (compiled : ClassifiedCompilation target) (K : State p)
    (path : MovePath (@AllModeMove p)
      (K ∪ target.1.left) (K ∪ target.1.right)) :
    MovePath (@AllModeMove compiled.compilation.choice.family.profile)
      (compiled.compilation.choice.orientState K ∪
        compiled.compilation.oriented.1.left)
      (compiled.compilation.choice.orientState K ∪
        compiled.compilation.oriented.1.right) :=
  castPathEndpoints (orientedContextLeft compiled K)
    (orientedContextRight compiled K)
    (orientPath compiled.compilation.choice path)

/-- Exposing the oriented contextual endpoints preserves exact path length. -/
@[simp] theorem orientClassifiedContextPath_length {p : Profile}
    {target : ExactRelation p} (compiled : ClassifiedCompilation target)
    (K : State p) (path : MovePath (@AllModeMove p)
      (K ∪ target.1.left) (K ∪ target.1.right)) :
    (orientClassifiedContextPath compiled K path).length = path.length := by
  simp only [orientClassifiedContextPath, castPathEndpoints_length,
    orientPath_length]

/-- Exposing the oriented contextual endpoints preserves exact altitude. -/
@[simp] theorem orientClassifiedContextPath_altitude {p : Profile}
    {target : ExactRelation p} (compiled : ClassifiedCompilation target)
    (K : State p) (path : MovePath (@AllModeMove p)
      (K ∪ target.1.left) (K ∪ target.1.right)) :
    (orientClassifiedContextPath compiled K path).altitude = path.altitude := by
  simp only [orientClassifiedContextPath, castPathEndpoints_altitude,
    orientPath_altitude]

private theorem pullbackOrientedLeft {p : Profile} {target : ExactRelation p}
    (compiled : ClassifiedCompilation target) (K : State p) :
    pullbackState (selectedActionWitness compiled).action
      (compiled.compilation.choice.orientState K ∪
        compiled.compilation.oriented.1.left) =
      compilationLocalContext compiled K ∪
        compiled.label.selectedEndpoints.left := by
  change pullbackState (selectedActionWitness compiled).action
      (compiled.compilation.choice.orientState K ∪
        compiled.compilation.oriented.1.left) =
    pullbackState (selectedActionWitness compiled).action
        (compiled.compilation.choice.orientState K) ∪
      compiled.label.selectedEndpoints.left
  calc
    pullbackState (selectedActionWitness compiled).action
        (compiled.compilation.choice.orientState K ∪
          compiled.compilation.oriented.1.left) =
      pullbackState (selectedActionWitness compiled).action
          (compiled.compilation.choice.orientState K) ∪
        pullbackState (selectedActionWitness compiled).action
          compiled.compilation.oriented.1.left :=
      pullbackState_union _ _ _
    _ = pullbackState (selectedActionWitness compiled).action
          (compiled.compilation.choice.orientState K) ∪
        pullbackState (selectedActionWitness compiled).action
          (ProfileAction.actState (selectedActionWitness compiled).action
            compiled.label.selectedEndpoints.left) := by
      rw [(selectedActionWitness compiled).left_image]
    _ = pullbackState (selectedActionWitness compiled).action
          (compiled.compilation.choice.orientState K) ∪
        compiled.label.selectedEndpoints.left := by
      rw [pullbackState_actState]

private theorem pullbackOrientedRight {p : Profile} {target : ExactRelation p}
    (compiled : ClassifiedCompilation target) (K : State p) :
    pullbackState (selectedActionWitness compiled).action
      (compiled.compilation.choice.orientState K ∪
        compiled.compilation.oriented.1.right) =
      compilationLocalContext compiled K ∪
        compiled.label.selectedEndpoints.right := by
  change pullbackState (selectedActionWitness compiled).action
      (compiled.compilation.choice.orientState K ∪
        compiled.compilation.oriented.1.right) =
    pullbackState (selectedActionWitness compiled).action
        (compiled.compilation.choice.orientState K) ∪
      compiled.label.selectedEndpoints.right
  calc
    pullbackState (selectedActionWitness compiled).action
        (compiled.compilation.choice.orientState K ∪
          compiled.compilation.oriented.1.right) =
      pullbackState (selectedActionWitness compiled).action
          (compiled.compilation.choice.orientState K) ∪
        pullbackState (selectedActionWitness compiled).action
          compiled.compilation.oriented.1.right :=
      pullbackState_union _ _ _
    _ = pullbackState (selectedActionWitness compiled).action
          (compiled.compilation.choice.orientState K) ∪
        pullbackState (selectedActionWitness compiled).action
          (ProfileAction.actState (selectedActionWitness compiled).action
            compiled.label.selectedEndpoints.right) := by
      rw [(selectedActionWitness compiled).right_image]
    _ = pullbackState (selectedActionWitness compiled).action
          (compiled.compilation.choice.orientState K) ∪
        compiled.label.selectedEndpoints.right := by
      rw [pullbackState_actState]

/-- Reflect an arbitrary contextual competitor at a classified normalized relation to the compiler-selected row. -/
def reflectClassifiedContextPath {p : Profile} {target : ExactRelation p}
    (compiled : ClassifiedCompilation target) (K : State p)
    (path : MovePath (@AllModeMove p)
      (K ∪ target.1.left) (K ∪ target.1.right)) :
    MovePath (@AllModeMove compiled.compilation.choice.family.profile)
      (compilationLocalContext compiled K ∪
        compiled.label.selectedEndpoints.left)
      (compilationLocalContext compiled K ∪
        compiled.label.selectedEndpoints.right) :=
  castPathEndpoints (pullbackOrientedLeft compiled K)
    (pullbackOrientedRight compiled K)
    (pullbackPath (selectedActionWitness compiled).action
      (orientClassifiedContextPath compiled K path))

/-- Classified competitor reflection preserves exact edge count. -/
@[simp] theorem reflectClassifiedContextPath_length {p : Profile}
    {target : ExactRelation p} (compiled : ClassifiedCompilation target)
    (K : State p) (path : MovePath (@AllModeMove p)
      (K ∪ target.1.left) (K ∪ target.1.right)) :
    (reflectClassifiedContextPath compiled K path).length = path.length := by
  unfold reflectClassifiedContextPath
  calc
    (castPathEndpoints (pullbackOrientedLeft compiled K)
      (pullbackOrientedRight compiled K)
      (pullbackPath (selectedActionWitness compiled).action
        (orientClassifiedContextPath compiled K path))).length =
        (pullbackPath (selectedActionWitness compiled).action
          (orientClassifiedContextPath compiled K path)).length :=
      castPathEndpoints_length _ _ _
    _ = (orientClassifiedContextPath compiled K path).length :=
      pullbackPath_length _ _
    _ = path.length := orientClassifiedContextPath_length compiled K path

/-- Classified competitor reflection preserves exact altitude. -/
@[simp] theorem reflectClassifiedContextPath_altitude {p : Profile}
    {target : ExactRelation p} (compiled : ClassifiedCompilation target)
    (K : State p) (path : MovePath (@AllModeMove p)
      (K ∪ target.1.left) (K ∪ target.1.right)) :
    (reflectClassifiedContextPath compiled K path).altitude = path.altitude := by
  unfold reflectClassifiedContextPath
  calc
    (castPathEndpoints (pullbackOrientedLeft compiled K)
      (pullbackOrientedRight compiled K)
      (pullbackPath (selectedActionWitness compiled).action
        (orientClassifiedContextPath compiled K path))).altitude =
        (pullbackPath (selectedActionWitness compiled).action
          (orientClassifiedContextPath compiled K path)).altitude :=
      castPathEndpoints_altitude _ _ _
    _ = (orientClassifiedContextPath compiled K path).altitude :=
      pullbackPath_altitude _ _
    _ = path.altitude := orientClassifiedContextPath_altitude compiled K path

/-- Endpoint-disjointness at the arbitrary target supplies endpoint-disjointness for the reflected selected-row context. -/
theorem reflectionContext_disjoint {p : Profile} {target : ExactRelation p}
    (compiled : ClassifiedCompilation target) {K : State p}
    (hK : Disjoint K (target.1.left ∪ target.1.right)) :
    Disjoint (compilationLocalContext compiled K)
      (compiled.label.selectedEndpoints.left ∪
        compiled.label.selectedEndpoints.right) := by
  exact compilationLocalContext_disjoint compiled hK

/-- A selected-row contextual path lower bound transfers to every classified normalized relation. -/
theorem classifiedContextPath_length_lower_bound {p : Profile}
    {target : ExactRelation p} (compiled : ClassifiedCompilation target)
    (n : ℕ)
    (hselected : ∀ (K : State compiled.compilation.choice.family.profile),
      Disjoint K (compiled.label.selectedEndpoints.left ∪
        compiled.label.selectedEndpoints.right) →
      ∀ path : MovePath (@AllModeMove compiled.compilation.choice.family.profile)
        (K ∪ compiled.label.selectedEndpoints.left)
        (K ∪ compiled.label.selectedEndpoints.right),
        n ≤ path.length)
    (K : State p) (hK : Disjoint K (target.1.left ∪ target.1.right))
    (path : MovePath (@AllModeMove p)
      (K ∪ target.1.left) (K ∪ target.1.right)) :
    n ≤ path.length := by
  let reflected := reflectClassifiedContextPath compiled K path
  have hLocalDisjoint := reflectionContext_disjoint compiled hK
  have hbound : n ≤ reflected.length :=
    hselected (compilationLocalContext compiled K) hLocalDisjoint reflected
  rw [reflectClassifiedContextPath_length] at hbound
  exact hbound

#check @reflectActionAllModeMove
#check @pullbackPath
#check @pullbackPath_length
#check @pullbackPath_altitude
#check @reflectClassifiedContextPath
#check @reflectClassifiedContextPath_length
#check @reflectClassifiedContextPath_altitude
#check @classifiedContextPath_length_lower_bound

#print axioms reflectActionAllModeMove
#print axioms pullbackPath_length
#print axioms reflectClassifiedContextPath_length
#print axioms classifiedContextPath_length_lower_bound

end BilinearComplexity.BinaryContextualOrbitReflection
