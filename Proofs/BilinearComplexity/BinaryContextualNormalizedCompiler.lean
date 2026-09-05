import BilinearComplexity.BinaryContextualOrbitTransport

set_option autoImplicit false

/-!
# Callback-driven contextual compiler with target unorientation

This module completes the normalized contextual transport pipeline after orbit
classification. It orients an arbitrary endpoint-disjoint context together
with the classified target, pulls that context back to the compiler-selected
row, invokes an abstract provider of actual forward and reverse contextual
paths, transports those paths through the selected action, and explicitly
undoes the profile orientation.

All output paths use the native directed `AllModeMove` relation. The compiler
preserves the supplied selected path's exact length and altitude, and its local
context has the original context's exact cardinality. This remains an
intermediate abstraction: it contains no finite row certificates, coverage
proof, or optimality assertion.
-/

namespace BilinearComplexity.BinaryContextualNormalizedCompiler

open BinaryCircuit
open NormalizedBinaryCarrier
open NormalizedBinaryModePermutation
open NormalizedBinaryProfileOrientation
open NormalizedBinaryAllModeMove
open NormalizedBinaryAllModePermutation
open NormalizedBinaryFiniteAction
open NormalizedBinaryOrbitClassification
open NormalizedBinaryRelationEnumeration
open Scheme.Action

/-- Invert a concrete checked profile orientation equality. -/
theorem inverseProfileEqOf {p q : Profile} (o : Orientation)
    (h : permProfile o p = q) :
    permProfile (orientationInverse o) q = p := by
  calc
    permProfile (orientationInverse o) q =
        permProfile (orientationInverse o) (permProfile o p) := by rw [h]
    _ = p := permProfile_inverse_left o p

/-- The inverse profile equality determined by a checked profile orientation. -/
theorem inverseProfileEq {p : Profile} (choice : ProfileOrientation p) :
    permProfile (orientationInverse choice.orientation)
      choice.family.profile = p :=
  inverseProfileEqOf choice.orientation choice.profile_eq

/-- Executably undo a checked profile orientation on a normalized state. -/
def unorientState {p : Profile}
    (choice : ProfileOrientation p) (D : State choice.family.profile) : State p :=
  cast (congrArg State (inverseProfileEq choice))
    (permuteState (orientationInverse choice.orientation) D)

private theorem unorientStateOfProfileEq {p q : Profile} (o : Orientation)
    (h : permProfile o p = q) (D : State p) :
    cast (congrArg State (inverseProfileEqOf o h))
      (permuteState (orientationInverse o)
        (cast (congrArg State h) (permuteState o D))) = D := by
  cases h
  simp

/-- Undoing the checked orientation of a state recovers that state. -/
@[simp] theorem unorientState_orientState {p : Profile}
    (choice : ProfileOrientation p) (D : State p) :
    unorientState choice (choice.orientState D) = D := by
  exact unorientStateOfProfileEq choice.orientation choice.profile_eq D

private theorem castStateUnion {p q : Profile} (h : p = q)
    (D E : State p) :
    cast (congrArg State h) (D ∪ E) =
      cast (congrArg State h) D ∪ cast (congrArg State h) E := by
  subst q
  rfl

private theorem castStateCard {p q : Profile} (h : p = q) (D : State p) :
    (cast (congrArg State h) D).card = D.card := by
  subst q
  rfl

/-- Unorientation commutes with finite-state union. -/
@[simp] theorem unorientState_union {p : Profile}
    (choice : ProfileOrientation p) (D E : State choice.family.profile) :
    unorientState choice (D ∪ E) =
      unorientState choice D ∪ unorientState choice E := by
  unfold unorientState
  rw [permuteState_union]
  exact castStateUnion (inverseProfileEq choice) _ _

/-- Unorientation preserves exact finite-state cardinality. -/
@[simp] theorem unorientState_card {p : Profile}
    (choice : ProfileOrientation p) (D : State choice.family.profile) :
    (unorientState choice D).card = D.card := by
  unfold unorientState
  exact (castStateCard (inverseProfileEq choice)
    (permuteState (orientationInverse choice.orientation) D)).trans
      (permuteState_card _ _)

/-- Cast a native all-mode path through a profile equality. -/
def castAllModePathProfile {p q : Profile} (h : p = q)
    {D E : State p} (path : MovePath (@AllModeMove p) D E) :
    MovePath (@AllModeMove q)
      (cast (congrArg State h) D) (cast (congrArg State h) E) := by
  subst q
  exact path

/-- Profile casting preserves exact path length. -/
@[simp] theorem castAllModePathProfile_length {p q : Profile} (h : p = q)
    {D E : State p} (path : MovePath (@AllModeMove p) D E) :
    (castAllModePathProfile h path).length = path.length := by
  subst q
  rfl

/-- Profile casting preserves exact path altitude. -/
@[simp] theorem castAllModePathProfile_altitude {p q : Profile} (h : p = q)
    {D E : State p} (path : MovePath (@AllModeMove p) D E) :
    (castAllModePathProfile h path).altitude = path.altitude := by
  subst q
  rfl

/-- Executably undo a checked profile orientation on an actual native path. -/
def unorientPath {p : Profile}
    (choice : ProfileOrientation p) {D E : State choice.family.profile}
    (path : MovePath (@AllModeMove choice.family.profile) D E) :
    MovePath (@AllModeMove p)
      (unorientState choice D) (unorientState choice E) :=
  castAllModePathProfile (inverseProfileEq choice)
    (permuteAllModePath (orientationInverse choice.orientation) path)

/-- Path unorientation preserves exact edge count. -/
@[simp] theorem unorientPath_length {p : Profile}
    (choice : ProfileOrientation p) {D E : State choice.family.profile}
    (path : MovePath (@AllModeMove choice.family.profile) D E) :
    (unorientPath choice path).length = path.length := by
  exact (castAllModePathProfile_length (inverseProfileEq choice)
    (permuteAllModePath (orientationInverse choice.orientation) path)).trans
      (permuteAllModePath_length _ path)

/-- Path unorientation preserves exact altitude. -/
@[simp] theorem unorientPath_altitude {p : Profile}
    (choice : ProfileOrientation p) {D E : State choice.family.profile}
    (path : MovePath (@AllModeMove choice.family.profile) D E) :
    (unorientPath choice path).altitude = path.altitude := by
  exact (castAllModePathProfile_altitude (inverseProfileEq choice)
    (permuteAllModePath (orientationInverse choice.orientation) path)).trans
      (permuteAllModePath_altitude _ path)

/-- Transport an actual selected-row reverse contextual path through an endpoint witness. -/
def transportContextReversePath {p : Profile}
    {source target : RelationEndpoints p}
    (witness : ActionWitness source target) (K : State p)
    (path : MovePath (@AllModeMove p)
      (BinaryContextualOrbitTransport.contextPullback witness K ∪ source.right)
      (BinaryContextualOrbitTransport.contextPullback witness K ∪ source.left)) :
    MovePath (@AllModeMove p)
      (K ∪ target.right) (K ∪ target.left) :=
  BinaryContextualOrbitTransport.castPathEndpoints
    (BinaryContextualOrbitTransport.contextPullback_right_union_image witness K)
    (BinaryContextualOrbitTransport.contextPullback_left_union_image witness K)
    (BinaryContextualOrbitTransport.actPath witness.action path)

/-- Reverse contextual action transport preserves exact edge count. -/
@[simp] theorem transportContextReversePath_length {p : Profile}
    {source target : RelationEndpoints p}
    (witness : ActionWitness source target) (K : State p)
    (path : MovePath (@AllModeMove p)
      (BinaryContextualOrbitTransport.contextPullback witness K ∪ source.right)
      (BinaryContextualOrbitTransport.contextPullback witness K ∪ source.left)) :
    (transportContextReversePath witness K path).length = path.length := by
  simp only [transportContextReversePath,
    BinaryContextualOrbitTransport.castPathEndpoints_length,
    BinaryContextualOrbitTransport.actPath_length]

/-- Reverse contextual action transport preserves exact altitude. -/
@[simp] theorem transportContextReversePath_altitude {p : Profile}
    {source target : RelationEndpoints p}
    (witness : ActionWitness source target) (K : State p)
    (path : MovePath (@AllModeMove p)
      (BinaryContextualOrbitTransport.contextPullback witness K ∪ source.right)
      (BinaryContextualOrbitTransport.contextPullback witness K ∪ source.left)) :
    (transportContextReversePath witness K path).altitude = path.altitude := by
  simp only [transportContextReversePath,
    BinaryContextualOrbitTransport.castPathEndpoints_altitude,
    BinaryContextualOrbitTransport.actPath_altitude]

/-- Transport an actual reverse path for the compiler-selected row to the oriented target. -/
def transportSelectedContextReversePath {p : Profile}
    {target : ExactRelation p} (compiled : ClassifiedCompilation target)
    (K : State compiled.compilation.choice.family.profile)
    (path : MovePath
      (@AllModeMove compiled.compilation.choice.family.profile)
      (BinaryContextualOrbitTransport.selectedContextPullback compiled K ∪
        compiled.label.selectedEndpoints.right)
      (BinaryContextualOrbitTransport.selectedContextPullback compiled K ∪
        compiled.label.selectedEndpoints.left)) :
    MovePath (@AllModeMove compiled.compilation.choice.family.profile)
      (K ∪ compiled.compilation.oriented.1.right)
      (K ∪ compiled.compilation.oriented.1.left) :=
  transportContextReversePath
    (BinaryContextualOrbitTransport.selectedActionWitness compiled) K path

/-- Selected-row reverse transport preserves exact edge count. -/
@[simp] theorem transportSelectedContextReversePath_length {p : Profile}
    {target : ExactRelation p} (compiled : ClassifiedCompilation target)
    (K : State compiled.compilation.choice.family.profile)
    (path : MovePath
      (@AllModeMove compiled.compilation.choice.family.profile)
      (BinaryContextualOrbitTransport.selectedContextPullback compiled K ∪
        compiled.label.selectedEndpoints.right)
      (BinaryContextualOrbitTransport.selectedContextPullback compiled K ∪
        compiled.label.selectedEndpoints.left)) :
    (transportSelectedContextReversePath compiled K path).length = path.length := by
  exact transportContextReversePath_length
    (BinaryContextualOrbitTransport.selectedActionWitness compiled) K path

/-- Selected-row reverse transport preserves exact altitude. -/
@[simp] theorem transportSelectedContextReversePath_altitude {p : Profile}
    {target : ExactRelation p} (compiled : ClassifiedCompilation target)
    (K : State compiled.compilation.choice.family.profile)
    (path : MovePath
      (@AllModeMove compiled.compilation.choice.family.profile)
      (BinaryContextualOrbitTransport.selectedContextPullback compiled K ∪
        compiled.label.selectedEndpoints.right)
      (BinaryContextualOrbitTransport.selectedContextPullback compiled K ∪
        compiled.label.selectedEndpoints.left)) :
    (transportSelectedContextReversePath compiled K path).altitude = path.altitude := by
  exact transportContextReversePath_altitude
    (BinaryContextualOrbitTransport.selectedActionWitness compiled) K path

/-- Unorient the contextual left endpoint produced by the oriented compiler. -/
theorem unorientCompiledLeftContext {p : Profile}
    {target : ExactRelation p} (compiled : ClassifiedCompilation target)
    (K : State p) :
    unorientState compiled.compilation.choice
      (compiled.compilation.choice.orientState K ∪
        compiled.compilation.oriented.1.left) =
      K ∪ target.1.left := by
  rw [compiled.compilation.oriented_left,
    ← compiled.compilation.choice.orientState_union,
    unorientState_orientState]

/-- Unorient the contextual right endpoint produced by the oriented compiler. -/
theorem unorientCompiledRightContext {p : Profile}
    {target : ExactRelation p} (compiled : ClassifiedCompilation target)
    (K : State p) :
    unorientState compiled.compilation.choice
      (compiled.compilation.choice.orientState K ∪
        compiled.compilation.oriented.1.right) =
      K ∪ target.1.right := by
  rw [compiled.compilation.oriented_right,
    ← compiled.compilation.choice.orientState_union,
    unorientState_orientState]

/-- Unorient an actual oriented contextual path to the original target endpoints. -/
def unorientCompiledContextPath {p : Profile}
    {target : ExactRelation p} (compiled : ClassifiedCompilation target)
    (K : State p)
    (path : MovePath (@AllModeMove compiled.compilation.choice.family.profile)
      (compiled.compilation.choice.orientState K ∪
        compiled.compilation.oriented.1.left)
      (compiled.compilation.choice.orientState K ∪
        compiled.compilation.oriented.1.right)) :
    MovePath (@AllModeMove p)
      (K ∪ target.1.left) (K ∪ target.1.right) :=
  BinaryContextualOrbitTransport.castPathEndpoints
    (unorientCompiledLeftContext compiled K)
    (unorientCompiledRightContext compiled K)
    (unorientPath compiled.compilation.choice path)

/-- Unorienting an oriented contextual path preserves exact edge count. -/
@[simp] theorem unorientCompiledContextPath_length {p : Profile}
    {target : ExactRelation p} (compiled : ClassifiedCompilation target)
    (K : State p)
    (path : MovePath (@AllModeMove compiled.compilation.choice.family.profile)
      (compiled.compilation.choice.orientState K ∪
        compiled.compilation.oriented.1.left)
      (compiled.compilation.choice.orientState K ∪
        compiled.compilation.oriented.1.right)) :
    (unorientCompiledContextPath compiled K path).length = path.length := by
  simp only [unorientCompiledContextPath,
    BinaryContextualOrbitTransport.castPathEndpoints_length,
    unorientPath_length]

/-- Unorienting an oriented contextual path preserves exact altitude. -/
@[simp] theorem unorientCompiledContextPath_altitude {p : Profile}
    {target : ExactRelation p} (compiled : ClassifiedCompilation target)
    (K : State p)
    (path : MovePath (@AllModeMove compiled.compilation.choice.family.profile)
      (compiled.compilation.choice.orientState K ∪
        compiled.compilation.oriented.1.left)
      (compiled.compilation.choice.orientState K ∪
        compiled.compilation.oriented.1.right)) :
    (unorientCompiledContextPath compiled K path).altitude = path.altitude := by
  simp only [unorientCompiledContextPath,
    BinaryContextualOrbitTransport.castPathEndpoints_altitude,
    unorientPath_altitude]

/-- Unorient an actual reverse oriented contextual path to the original reversed endpoints. -/
def unorientCompiledContextReversePath {p : Profile}
    {target : ExactRelation p} (compiled : ClassifiedCompilation target)
    (K : State p)
    (path : MovePath (@AllModeMove compiled.compilation.choice.family.profile)
      (compiled.compilation.choice.orientState K ∪
        compiled.compilation.oriented.1.right)
      (compiled.compilation.choice.orientState K ∪
        compiled.compilation.oriented.1.left)) :
    MovePath (@AllModeMove p)
      (K ∪ target.1.right) (K ∪ target.1.left) :=
  BinaryContextualOrbitTransport.castPathEndpoints
    (unorientCompiledRightContext compiled K)
    (unorientCompiledLeftContext compiled K)
    (unorientPath compiled.compilation.choice path)

/-- Reverse contextual unorientation preserves exact edge count. -/
@[simp] theorem unorientCompiledContextReversePath_length {p : Profile}
    {target : ExactRelation p} (compiled : ClassifiedCompilation target)
    (K : State p)
    (path : MovePath (@AllModeMove compiled.compilation.choice.family.profile)
      (compiled.compilation.choice.orientState K ∪
        compiled.compilation.oriented.1.right)
      (compiled.compilation.choice.orientState K ∪
        compiled.compilation.oriented.1.left)) :
    (unorientCompiledContextReversePath compiled K path).length = path.length := by
  simp only [unorientCompiledContextReversePath,
    BinaryContextualOrbitTransport.castPathEndpoints_length,
    unorientPath_length]

/-- Reverse contextual unorientation preserves exact altitude. -/
@[simp] theorem unorientCompiledContextReversePath_altitude {p : Profile}
    {target : ExactRelation p} (compiled : ClassifiedCompilation target)
    (K : State p)
    (path : MovePath (@AllModeMove compiled.compilation.choice.family.profile)
      (compiled.compilation.choice.orientState K ∪
        compiled.compilation.oriented.1.right)
      (compiled.compilation.choice.orientState K ∪
        compiled.compilation.oriented.1.left)) :
    (unorientCompiledContextReversePath compiled K path).altitude = path.altitude := by
  simp only [unorientCompiledContextReversePath,
    BinaryContextualOrbitTransport.castPathEndpoints_altitude,
    unorientPath_altitude]

/-- A certificate-agnostic callback supplying both directed contextual paths for one selected orbit label at every endpoint-disjoint local context. -/
def SelectedContextPathProvider (label : OrbitLabel) : Type :=
  (K : State label.1.profile) →
    Disjoint K
      (label.selectedEndpoints.left ∪ label.selectedEndpoints.right) →
    (MovePath (@AllModeMove label.1.profile)
      (K ∪ label.selectedEndpoints.left)
      (K ∪ label.selectedEndpoints.right)) ×
    (MovePath (@AllModeMove label.1.profile)
      (K ∪ label.selectedEndpoints.right)
      (K ∪ label.selectedEndpoints.left))

/-- A provider application is exactly its exposed forward and reverse path pair. -/
theorem selectedContextPathProvider_apply {label : OrbitLabel}
    (provider : SelectedContextPathProvider label)
    (K : State label.1.profile)
    (hK : Disjoint K
      (label.selectedEndpoints.left ∪ label.selectedEndpoints.right)) :
    provider K hK = ((provider K hK).1, (provider K hK).2) := by
  exact (provider K hK).eta.symm

/-- The local context at which the selected-label callback must be invoked. -/
def compilationLocalContext {p : Profile} {target : ExactRelation p}
    (compiled : ClassifiedCompilation target) (K : State p) :
    State compiled.compilation.choice.family.profile :=
  BinaryContextualOrbitTransport.selectedContextPullback compiled
    (compiled.compilation.choice.orientState K)

/-- The selected local context has exactly the cardinality of the original context. -/
@[simp] theorem compilationLocalContext_card {p : Profile}
    {target : ExactRelation p} (compiled : ClassifiedCompilation target)
    (K : State p) :
    (compilationLocalContext compiled K).card = K.card := by
  calc
    (compilationLocalContext compiled K).card =
        (compiled.compilation.choice.orientState K).card :=
      BinaryContextualOrbitTransport.selectedContextPullback_card _ _
    _ = K.card := compiled.compilation.choice.orientState_card K

/-- Original endpoint disjointness supplies the selected callback's local disjointness premise. -/
theorem compilationLocalContext_disjoint {p : Profile}
    {target : ExactRelation p} (compiled : ClassifiedCompilation target)
    {K : State p} (hK : Disjoint K (target.1.left ∪ target.1.right)) :
    Disjoint (compilationLocalContext compiled K)
      (compiled.label.selectedEndpoints.left ∪
        compiled.label.selectedEndpoints.right) := by
  have hOriented := compiled.compilation.choice.orientState_disjoint hK
  rw [compiled.compilation.choice.orientState_union,
    ← compiled.compilation.oriented_left,
    ← compiled.compilation.oriented_right] at hOriented
  exact BinaryContextualOrbitTransport.selectedContextPullback_disjoint
    compiled hOriented

/-- Obtain the callback's concrete selected-row forward path at the computed local context. -/
def selectedLocalForwardPath {p : Profile} {target : ExactRelation p}
    (compiled : ClassifiedCompilation target) (K : State p)
    (hK : Disjoint K (target.1.left ∪ target.1.right))
    (provider : SelectedContextPathProvider compiled.label) :
    MovePath (@AllModeMove compiled.compilation.choice.family.profile)
      (compilationLocalContext compiled K ∪
        compiled.label.selectedEndpoints.left)
      (compilationLocalContext compiled K ∪
        compiled.label.selectedEndpoints.right) :=
  (provider (compilationLocalContext compiled K)
    (compilationLocalContext_disjoint compiled hK)).1

/-- Obtain the callback's concrete selected-row reverse path at the computed local context. -/
def selectedLocalReversePath {p : Profile} {target : ExactRelation p}
    (compiled : ClassifiedCompilation target) (K : State p)
    (hK : Disjoint K (target.1.left ∪ target.1.right))
    (provider : SelectedContextPathProvider compiled.label) :
    MovePath (@AllModeMove compiled.compilation.choice.family.profile)
      (compilationLocalContext compiled K ∪
        compiled.label.selectedEndpoints.right)
      (compilationLocalContext compiled K ∪
        compiled.label.selectedEndpoints.left) :=
  (provider (compilationLocalContext compiled K)
    (compilationLocalContext_disjoint compiled hK)).2

/-- Use a selected-label callback to produce an actual forward path at the original target and context. -/
def compileOriginalContextForwardPath {p : Profile}
    {target : ExactRelation p} (compiled : ClassifiedCompilation target)
    (K : State p) (hK : Disjoint K (target.1.left ∪ target.1.right))
    (provider : SelectedContextPathProvider compiled.label) :
    MovePath (@AllModeMove p)
      (K ∪ target.1.left) (K ∪ target.1.right) :=
  unorientCompiledContextPath compiled K
    (BinaryContextualOrbitTransport.transportSelectedContextPath compiled
      (compiled.compilation.choice.orientState K)
      (selectedLocalForwardPath compiled K hK provider))

/-- Callback-driven forward compilation preserves the selected path's exact edge count. -/
@[simp] theorem compileOriginalContextForwardPath_length {p : Profile}
    {target : ExactRelation p} (compiled : ClassifiedCompilation target)
    (K : State p) (hK : Disjoint K (target.1.left ∪ target.1.right))
    (provider : SelectedContextPathProvider compiled.label) :
    (compileOriginalContextForwardPath compiled K hK provider).length =
      (selectedLocalForwardPath compiled K hK provider).length := by
  calc
    (compileOriginalContextForwardPath compiled K hK provider).length =
        (BinaryContextualOrbitTransport.transportSelectedContextPath compiled
          (compiled.compilation.choice.orientState K)
          (selectedLocalForwardPath compiled K hK provider)).length :=
      unorientCompiledContextPath_length _ _ _
    _ = (selectedLocalForwardPath compiled K hK provider).length :=
      BinaryContextualOrbitTransport.transportSelectedContextPath_length _ _ _

/-- Callback-driven forward compilation preserves the selected path's exact altitude. -/
@[simp] theorem compileOriginalContextForwardPath_altitude {p : Profile}
    {target : ExactRelation p} (compiled : ClassifiedCompilation target)
    (K : State p) (hK : Disjoint K (target.1.left ∪ target.1.right))
    (provider : SelectedContextPathProvider compiled.label) :
    (compileOriginalContextForwardPath compiled K hK provider).altitude =
      (selectedLocalForwardPath compiled K hK provider).altitude := by
  calc
    (compileOriginalContextForwardPath compiled K hK provider).altitude =
        (BinaryContextualOrbitTransport.transportSelectedContextPath compiled
          (compiled.compilation.choice.orientState K)
          (selectedLocalForwardPath compiled K hK provider)).altitude :=
      unorientCompiledContextPath_altitude _ _ _
    _ = (selectedLocalForwardPath compiled K hK provider).altitude :=
      BinaryContextualOrbitTransport.transportSelectedContextPath_altitude _ _ _

/-- Use the same selected-label callback to produce an actual reverse path at the original target and context. -/
def compileOriginalContextReversePath {p : Profile}
    {target : ExactRelation p} (compiled : ClassifiedCompilation target)
    (K : State p) (hK : Disjoint K (target.1.left ∪ target.1.right))
    (provider : SelectedContextPathProvider compiled.label) :
    MovePath (@AllModeMove p)
      (K ∪ target.1.right) (K ∪ target.1.left) :=
  unorientCompiledContextReversePath compiled K
    (transportSelectedContextReversePath compiled
      (compiled.compilation.choice.orientState K)
      (selectedLocalReversePath compiled K hK provider))

/-- Callback-driven reverse compilation preserves the selected path's exact edge count. -/
@[simp] theorem compileOriginalContextReversePath_length {p : Profile}
    {target : ExactRelation p} (compiled : ClassifiedCompilation target)
    (K : State p) (hK : Disjoint K (target.1.left ∪ target.1.right))
    (provider : SelectedContextPathProvider compiled.label) :
    (compileOriginalContextReversePath compiled K hK provider).length =
      (selectedLocalReversePath compiled K hK provider).length := by
  calc
    (compileOriginalContextReversePath compiled K hK provider).length =
        (transportSelectedContextReversePath compiled
          (compiled.compilation.choice.orientState K)
          (selectedLocalReversePath compiled K hK provider)).length :=
      unorientCompiledContextReversePath_length _ _ _
    _ = (selectedLocalReversePath compiled K hK provider).length :=
      transportSelectedContextReversePath_length _ _ _

/-- Callback-driven reverse compilation preserves the selected path's exact altitude. -/
@[simp] theorem compileOriginalContextReversePath_altitude {p : Profile}
    {target : ExactRelation p} (compiled : ClassifiedCompilation target)
    (K : State p) (hK : Disjoint K (target.1.left ∪ target.1.right))
    (provider : SelectedContextPathProvider compiled.label) :
    (compileOriginalContextReversePath compiled K hK provider).altitude =
      (selectedLocalReversePath compiled K hK provider).altitude := by
  calc
    (compileOriginalContextReversePath compiled K hK provider).altitude =
        (transportSelectedContextReversePath compiled
          (compiled.compilation.choice.orientState K)
          (selectedLocalReversePath compiled K hK provider)).altitude :=
      unorientCompiledContextReversePath_altitude _ _ _
    _ = (selectedLocalReversePath compiled K hK provider).altitude :=
      transportSelectedContextReversePath_altitude _ _ _

end BilinearComplexity.BinaryContextualNormalizedCompiler

#print axioms BilinearComplexity.BinaryContextualNormalizedCompiler.compileOriginalContextForwardPath_length
#print axioms BilinearComplexity.BinaryContextualNormalizedCompiler.compileOriginalContextReversePath_altitude
