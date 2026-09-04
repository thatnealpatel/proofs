import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import BilinearComplexity.NormalizedBinaryModePermutation
import BilinearComplexity.NormalizedBinaryMoveTransport

set_option autoImplicit false

/-!
# Finite checker for normalized binary profile actions

This module is an action checker only.  A raw candidate contains three forward
binary matrices and a tensor-mode orientation.  The checker turns it into
proof-carrying action data exactly when all matrices are invertible and the
orientation preserves the ordered profile, and a second checker returns an
endpoint witness exactly when both ordered endpoint images agree.

The external-compatible convention is fixed as follows.  A factor vector is a
column, a Lean matrix is indexed by `(row, column)`, and each forward factor
map is `y = Mx` via `Matrix.mulVec`.  The three matrices act in their source
factor modes first.  The existing `Orientation` then permutes the resulting
modes, and only then does an explicit proof cast the permuted profile back to
the source profile.  Endpoint left and right slots are acted on separately;
in particular, ordered `2 | 3` sides are never exchanged.

No group composition or inverse laws, orbit relation, enumeration, action
size, census, coverage or separation result, certificate/path mode transport,
compiler claim, or external artifact is defined here.

AI disclosure: produced with AI assistance (see `README`).
-/

namespace BilinearComplexity.NormalizedBinaryFiniteAction

open NormalizedBinaryCarrier
open NormalizedBinaryModePermutation
open NormalizedBinaryMoveTransport
open NormalizedBinaryReplay221
open Scheme.Action

/-- A square matrix over `F2` acting on a dimension-`d` coordinate column. -/
abbrev BinarySquareMatrix (d : ℕ) : Type := Matrix (Fin d) (Fin d) F2

/-- An intrinsic general-linear-group element represented by a binary square
matrix. -/
abbrev BinaryGeneralLinear (d : ℕ) : Type :=
  Matrix.GeneralLinearGroup (Fin d) F2

example : (0 : BinarySquareMatrix 1) (0 : Fin 1) (0 : Fin 1) = 0 := rfl
example : Nonempty (BinaryGeneralLinear 1) := ⟨1⟩

/-- Forget a binary matrix GL element to its additive forward map, through the
canonical `toLin → toLinearEquiv → toAddEquiv → toAddMonoidHom` chain. -/
def binaryGeneralLinearToAddMonoidHom {d : ℕ} (g : BinaryGeneralLinear d) :
    CoordinateVector d →+ CoordinateVector d :=
  (Matrix.GeneralLinearGroup.toLin g).toLinearEquiv.toAddEquiv.toAddMonoidHom

/-- The forgotten additive map applies the represented matrix to a column
vector by row-column multiplication. -/
@[simp] theorem binaryGeneralLinearToAddMonoidHom_apply {d : ℕ}
    (g : BinaryGeneralLinear d) (x : CoordinateVector d) :
    binaryGeneralLinearToAddMonoidHom g x =
      (g : BinarySquareMatrix d).mulVec x := by
  rfl

/-- The additive map underlying an intrinsic binary GL element is injective. -/
theorem binaryGeneralLinearToAddMonoidHom_injective {d : ℕ}
    (g : BinaryGeneralLinear d) :
    Function.Injective (binaryGeneralLinearToAddMonoidHom g) := by
  exact (Matrix.GeneralLinearGroup.toLin g).toLinearEquiv.injective

example (x : CoordinateVector 2) :
    binaryGeneralLinearToAddMonoidHom (1 : BinaryGeneralLinear 2) x = x := by
  rw [binaryGeneralLinearToAddMonoidHom_apply]
  exact Matrix.one_mulVec x

/-- An unchecked profile-action candidate.  Its three matrices are forward
maps in the three ordered source factors; the orientation is applied only
after all three matrix maps. -/
structure RawProfileAction (p : Profile) where
  /-- The forward matrix in the source first factor. -/
  first : BinarySquareMatrix p.first
  /-- The forward matrix in the source second factor. -/
  second : BinarySquareMatrix p.second
  /-- The forward matrix in the source third factor. -/
  third : BinarySquareMatrix p.third
  /-- The subsequent permutation of the three already-mapped factor modes. -/
  orientation : Orientation

namespace RawProfileAction

/-- A raw profile action is valid when all three source-factor matrices have
nonzero determinant and its orientation preserves the ordered profile. -/
def Valid {p : Profile} (raw : RawProfileAction p) : Prop :=
  Matrix.det raw.first ≠ 0 ∧
    Matrix.det raw.second ≠ 0 ∧
    Matrix.det raw.third ≠ 0 ∧
    permProfile raw.orientation p = p

/-- Raw profile-action validity is constructively decidable. -/
instance {p : Profile} (raw : RawProfileAction p) : Decidable raw.Valid := by
  unfold Valid
  infer_instance

end RawProfileAction

example :
    RawProfileAction.Valid
      ({ first := 1, second := 1, third := 1, orientation := .abc } :
        RawProfileAction profile221) := by
  decide

/-- A checked profile action: three intrinsic source-factor GL elements,
followed by an orientation with a proof that the ordered profile is unchanged. -/
structure ProfileAction (p : Profile) where
  /-- The checked forward GL element in the source first factor. -/
  first : BinaryGeneralLinear p.first
  /-- The checked forward GL element in the source second factor. -/
  second : BinaryGeneralLinear p.second
  /-- The checked forward GL element in the source third factor. -/
  third : BinaryGeneralLinear p.third
  /-- The mode permutation applied after the three forward GL maps. -/
  orientation : Orientation
  /-- The explicit equality used to cast the permuted profile back to `p`. -/
  profile_eq : permProfile orientation p = p

namespace RawProfileAction

/-- Convert a valid raw action into intrinsic GL elements and its proved
profile-preserving orientation. -/
def toProfileAction {p : Profile} (raw : RawProfileAction p) (h : raw.Valid) :
    ProfileAction p where
  first := Matrix.GeneralLinearGroup.mkOfDetNeZero raw.first h.1
  second := Matrix.GeneralLinearGroup.mkOfDetNeZero raw.second h.2.1
  third := Matrix.GeneralLinearGroup.mkOfDetNeZero raw.third h.2.2.1
  orientation := raw.orientation
  profile_eq := h.2.2.2

/-- Conversion preserves the exact raw first-factor matrix. -/
@[simp] theorem toProfileAction_first_coe {p : Profile}
    (raw : RawProfileAction p) (h : raw.Valid) :
    ((raw.toProfileAction h).first : BinarySquareMatrix p.first) = raw.first := by
  rfl

/-- Conversion preserves the exact raw second-factor matrix. -/
@[simp] theorem toProfileAction_second_coe {p : Profile}
    (raw : RawProfileAction p) (h : raw.Valid) :
    ((raw.toProfileAction h).second : BinarySquareMatrix p.second) =
      raw.second := by
  rfl

/-- Conversion preserves the exact raw third-factor matrix. -/
@[simp] theorem toProfileAction_third_coe {p : Profile}
    (raw : RawProfileAction p) (h : raw.Valid) :
    ((raw.toProfileAction h).third : BinarySquareMatrix p.third) = raw.third := by
  rfl

end RawProfileAction

namespace ProfileAction

/-- Package the three checked GL maps as the existing ordered
`FactorwiseAdditiveInjection p p`. -/
def factorwiseInjection {p : Profile} (action : ProfileAction p) :
    FactorwiseAdditiveInjection p p where
  first := binaryGeneralLinearToAddMonoidHom action.first
  second := binaryGeneralLinearToAddMonoidHom action.second
  third := binaryGeneralLinearToAddMonoidHom action.third
  first_injective := binaryGeneralLinearToAddMonoidHom_injective action.first
  second_injective := binaryGeneralLinearToAddMonoidHom_injective action.second
  third_injective := binaryGeneralLinearToAddMonoidHom_injective action.third

/-- The packaged first factor is exact forward matrix-column multiplication. -/
@[simp] theorem factorwiseInjection_first_apply {p : Profile}
    (action : ProfileAction p) (x : CoordinateVector p.first) :
    action.factorwiseInjection.first x =
      (action.first : BinarySquareMatrix p.first).mulVec x := by
  rfl

/-- The packaged second factor is exact forward matrix-column multiplication. -/
@[simp] theorem factorwiseInjection_second_apply {p : Profile}
    (action : ProfileAction p) (x : CoordinateVector p.second) :
    action.factorwiseInjection.second x =
      (action.second : BinarySquareMatrix p.second).mulVec x := by
  rfl

/-- The packaged third factor is exact forward matrix-column multiplication. -/
@[simp] theorem factorwiseInjection_third_apply {p : Profile}
    (action : ProfileAction p) (x : CoordinateVector p.third) :
    action.factorwiseInjection.third x =
      (action.third : BinarySquareMatrix p.third).mulVec x := by
  rfl

/-- All three components of the packaged existing factorwise map are
injective. -/
theorem factorwiseInjection_components_injective {p : Profile}
    (action : ProfileAction p) :
    Function.Injective action.factorwiseInjection.first ∧
      Function.Injective action.factorwiseInjection.second ∧
      Function.Injective action.factorwiseInjection.third := by
  exact ⟨action.factorwiseInjection.first_injective,
    action.factorwiseInjection.second_injective,
    action.factorwiseInjection.third_injective⟩

end ProfileAction

namespace RawProfileAction

/-- A converted action's first additive factor map applies the exact raw
first matrix as a forward matrix-column product. -/
@[simp] theorem toProfileAction_first_map_apply {p : Profile}
    (raw : RawProfileAction p) (h : raw.Valid)
    (x : CoordinateVector p.first) :
    (raw.toProfileAction h).factorwiseInjection.first x =
      raw.first.mulVec x := by
  rfl

/-- A converted action's second additive factor map applies the exact raw
second matrix as a forward matrix-column product. -/
@[simp] theorem toProfileAction_second_map_apply {p : Profile}
    (raw : RawProfileAction p) (h : raw.Valid)
    (x : CoordinateVector p.second) :
    (raw.toProfileAction h).factorwiseInjection.second x =
      raw.second.mulVec x := by
  rfl

/-- A converted action's third additive factor map applies the exact raw
third matrix as a forward matrix-column product. -/
@[simp] theorem toProfileAction_third_map_apply {p : Profile}
    (raw : RawProfileAction p) (h : raw.Valid)
    (x : CoordinateVector p.third) :
    (raw.toProfileAction h).factorwiseInjection.third x =
      raw.third.mulVec x := by
  rfl

end RawProfileAction

namespace ProfileAction

/-- Act on one carrier term using the fixed external convention: apply the
three source-factor forward matrices, apply the existing mode permutation,
then cast along the explicit profile equality. -/
def actTerm {p : Profile} (action : ProfileAction p) (t : Carrier p) :
    Carrier p :=
  Equiv.cast (congrArg Carrier action.profile_eq)
    (permuteTerm action.orientation (mapTerm action.factorwiseInjection t))

/-- Act on a finite-set state by the same ordered factor maps, subsequent mode
permutation, and final explicit profile cast. -/
def actState {p : Profile} (action : ProfileAction p) (D : State p) : State p :=
  Equiv.cast (congrArg State action.profile_eq)
    (permuteState action.orientation
      (mapState action.factorwiseInjection D))

private theorem castState_eq_image_castCarrier {p q : Profile} (h : p = q)
    (D : State p) :
    Equiv.cast (congrArg State h) D =
      D.image (Equiv.cast (congrArg Carrier h)) := by
  subst q
  change D = D.image id
  exact Finset.image_id.symm

/-- State action is exactly the finite-set image of the corresponding term
action. -/
@[simp] theorem actState_eq_image {p : Profile} (action : ProfileAction p)
    (D : State p) : action.actState D = D.image action.actTerm := by
  rw [actState, castState_eq_image_castCarrier]
  · simp only [permuteState, mapState, Finset.image_image]
    apply Finset.image_congr
    intro t _
    rfl
  · exact action.profile_eq

/-- A checked profile action is injective on normalized carrier terms. -/
theorem actTerm_injective {p : Profile} (action : ProfileAction p) :
    Function.Injective action.actTerm := by
  intro s t hst
  have hpermuted :
      permuteTerm action.orientation
          (mapTerm action.factorwiseInjection s) =
        permuteTerm action.orientation
          (mapTerm action.factorwiseInjection t) :=
    (Equiv.cast (congrArg Carrier action.profile_eq)).injective hst
  exact mapTerm_injective action.factorwiseInjection
    (permuteTerm_injective action.orientation hpermuted)

/-- A checked profile action preserves exact finite-set state cardinality. -/
@[simp] theorem actState_card {p : Profile} (action : ProfileAction p)
    (D : State p) : (action.actState D).card = D.card := by
  rw [actState_eq_image]
  exact Finset.card_image_of_injective D action.actTerm_injective

end ProfileAction

/-- Two ordered relation endpoints.  The left slot and right slot remain
separate under actions; client-side `2 | 3` cardinality information does not
permit or trigger a side swap. -/
structure RelationEndpoints (p : Profile) where
  /-- The ordered left endpoint state. -/
  left : State p
  /-- The ordered right endpoint state. -/
  right : State p
  deriving DecidableEq

namespace ProfileAction

/-- Act on both ordered endpoints without exchanging their left/right slots. -/
def actEndpoints {p : Profile} (action : ProfileAction p)
    (endpoints : RelationEndpoints p) : RelationEndpoints p :=
  ⟨action.actState endpoints.left, action.actState endpoints.right⟩

/-- Endpoint action projects to state action in the ordered left slot. -/
@[simp] theorem actEndpoints_left {p : Profile} (action : ProfileAction p)
    (endpoints : RelationEndpoints p) :
    (action.actEndpoints endpoints).left =
      action.actState endpoints.left := by
  rfl

/-- Endpoint action projects to state action in the ordered right slot. -/
@[simp] theorem actEndpoints_right {p : Profile} (action : ProfileAction p)
    (endpoints : RelationEndpoints p) :
    (action.actEndpoints endpoints).right =
      action.actState endpoints.right := by
  rfl

end ProfileAction

/-- Proof-producing evidence that one checked profile action maps a specified
ordered source endpoint pair to a specified ordered target endpoint pair. -/
structure ActionWitness {p : Profile}
    (source target : RelationEndpoints p) where
  /-- The actual checked action data. -/
  action : ProfileAction p
  /-- Exact simultaneous equality of both ordered endpoint images. -/
  maps_endpoints : action.actEndpoints source = target

namespace ActionWitness

/-- An action witness gives the exact left-endpoint image equality. -/
@[simp] theorem left_image {p : Profile}
    {source target : RelationEndpoints p}
    (witness : ActionWitness source target) :
    witness.action.actState source.left = target.left := by
  exact congrArg RelationEndpoints.left witness.maps_endpoints

/-- An action witness gives the exact right-endpoint image equality. -/
@[simp] theorem right_image {p : Profile}
    {source target : RelationEndpoints p}
    (witness : ActionWitness source target) :
    witness.action.actState source.right = target.right := by
  exact congrArg RelationEndpoints.right witness.maps_endpoints

end ActionWitness

namespace RawProfileAction

/-- Check raw validity and return the resulting proof-carrying profile action;
invalid raw matrices or a profile-changing orientation return `none`. -/
def check {p : Profile} (raw : RawProfileAction p) : Option (ProfileAction p) :=
  if h : raw.Valid then some (raw.toProfileAction h) else none

/-- Every proof of raw validity identifies the exact checked action emitted by
the raw checker. -/
@[simp] theorem check_eq_some_of_valid {p : Profile}
    (raw : RawProfileAction p) (h : raw.Valid) :
    raw.check = some (raw.toProfileAction h) := by
  simp only [check, h, dite_true]

/-- The raw checker emits data exactly when its three determinant and profile
conditions hold. -/
@[simp] theorem check_isSome_iff {p : Profile} (raw : RawProfileAction p) :
    raw.check.isSome = true ↔ raw.Valid := by
  by_cases h : raw.Valid
  · simp [check, h]
  · simp [check, h]

/-- Any action emitted by the raw checker certifies that the raw candidate is
valid. -/
theorem valid_of_check_eq_some {p : Profile} (raw : RawProfileAction p)
    (action : ProfileAction p) (hcheck : raw.check = some action) : raw.Valid := by
  apply (check_isSome_iff raw).mp
  rw [hcheck]
  rfl

end RawProfileAction

/-- Run the raw checker, compare the two ordered endpoint images exactly, and
return the actual proof-carrying witness on success. -/
def checkActionWitness {p : Profile} (raw : RawProfileAction p)
    (source target : RelationEndpoints p) :
    Option (ActionWitness source target) :=
  match raw.check with
  | none => none
  | some action =>
      if h : action.actEndpoints source = target then
        some ⟨action, h⟩
      else none

/-- If a particular action is emitted and maps the endpoints exactly, the
endpoint checker returns that action together with the equality proof. -/
theorem checkActionWitness_eq_some_of {p : Profile}
    (raw : RawProfileAction p) (source target : RelationEndpoints p)
    (action : ProfileAction p) (hcheck : raw.check = some action)
    (hmap : action.actEndpoints source = target) :
    checkActionWitness raw source target = some ⟨action, hmap⟩ := by
  simp only [checkActionWitness, hcheck, hmap, dite_true]

/-- A witness returned by the endpoint checker contains exactly an action
emitted by the raw checker and its exact ordered endpoint equality. -/
theorem checkActionWitness_sound {p : Profile}
    (raw : RawProfileAction p) (source target : RelationEndpoints p)
    (witness : ActionWitness source target)
    (hcheck : checkActionWitness raw source target = some witness) :
    raw.check = some witness.action ∧
      witness.action.actEndpoints source = target := by
  constructor
  · cases hraw : raw.check with
    | none =>
        have himpossible : (none : Option (ActionWitness source target)) =
            some witness := by
          simpa only [checkActionWitness, hraw] using hcheck
        exact False.elim ((Option.some_ne_none witness) himpossible.symm)
    | some action =>
        by_cases hmap : action.actEndpoints source = target
        · simp only [checkActionWitness, hraw, hmap, dite_true,
            Option.some.injEq] at hcheck
          subst witness
          rfl
        · have himpossible : (none : Option (ActionWitness source target)) =
              some witness := by
            simpa only [checkActionWitness, hraw, hmap, dite_false] using hcheck
          exact False.elim ((Option.some_ne_none witness) himpossible.symm)
  · exact witness.maps_endpoints

/-- The endpoint checker succeeds if and only if an action actually emitted by
this raw checker maps the ordered source endpoints to the ordered target
endpoints. -/
@[simp] theorem checkActionWitness_isSome_iff {p : Profile}
    (raw : RawProfileAction p) (source target : RelationEndpoints p) :
    (checkActionWitness raw source target).isSome = true ↔
      ∃ action,
        raw.check = some action ∧ action.actEndpoints source = target := by
  cases hcheck : raw.check with
  | none =>
      simp only [checkActionWitness, hcheck, Option.isSome_none,
        Bool.false_eq_true, false_iff]
      rintro ⟨action, haction, _⟩
      exact (Option.some_ne_none action) haction.symm
  | some emitted =>
      by_cases hmap : emitted.actEndpoints source = target
      · simp only [checkActionWitness, hcheck, hmap, dite_true,
          Option.isSome_some]
        constructor
        · intro _
          exact ⟨emitted, rfl, hmap⟩
        · intro _
          exact True.intro
      · simp only [checkActionWitness, hcheck, hmap, dite_false,
          Option.isSome_none, Bool.false_eq_true, false_iff]
        rintro ⟨action, haction, hmaps⟩
        have haction_eq : emitted = action := Option.some.inj haction
        subst action
        exact hmap hmaps

namespace Regression

/-- The serialized profile-`221` regression raw action: swap the first factor,
use identity matrices in the second and third factors, then use orientation
`.abc`. -/
def profile221SwapRaw : RawProfileAction profile221 where
  first := !![0, 1; 1, 0]
  second := 1
  third := 1
  orientation := .abc

/-- The regression raw fields agree exactly with the intended serialized
matrix and orientation tuple. -/
theorem profile221SwapRaw_serialization :
    profile221SwapRaw.first = !![0, 1; 1, 0] ∧
      profile221SwapRaw.second = 1 ∧
      profile221SwapRaw.third = 1 ∧
      profile221SwapRaw.orientation = .abc := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The serialized profile-`221` swap candidate is valid. -/
theorem profile221SwapRaw_valid : profile221SwapRaw.Valid := by
  decide

/-- The regression's first-factor swap matrix is not the identity matrix. -/
theorem profile221SwapRaw_first_ne_one : profile221SwapRaw.first ≠ 1 := by
  decide

/-- The literal ordered source endpoint singletons are left `{E11}` and right
`{E12}`. -/
def profile221SwapSource : RelationEndpoints profile221 :=
  ⟨{E11}, {E12}⟩

/-- The literal ordered target endpoint singletons are left `{E21}` and right
`{E22}`; this target is not defined by applying the action. -/
def profile221SwapTarget : RelationEndpoints profile221 :=
  ⟨{E21}, {E22}⟩

/-- The actual checked action constructed from the valid serialized raw
profile-`221` swap. -/
def profile221SwapAction : ProfileAction profile221 :=
  profile221SwapRaw.toProfileAction profile221SwapRaw_valid

/-- The raw checker returns the exact checked profile-`221` swap action. -/
theorem profile221SwapRaw_check_success :
    profile221SwapRaw.check = some profile221SwapAction := by
  exact RawProfileAction.check_eq_some_of_valid
    profile221SwapRaw profile221SwapRaw_valid

/-- The nonidentity checked swap maps the two literal ordered source
singletons exactly to the two literal ordered target singletons. -/
theorem profile221Swap_exact_endpoint_image :
    profile221SwapAction.actEndpoints profile221SwapSource =
      profile221SwapTarget := by
  let action := profile221SwapRaw.toProfileAction profile221SwapRaw_valid
  have hcastState (D : State profile221) :
      Equiv.cast (congrArg State action.profile_eq) D = D := by
    have heq : congrArg State action.profile_eq =
        (rfl : State profile221 = State profile221) := Subsingleton.elim _ _
    rw [heq]
    rfl
  have hactState (D : State profile221) :
      action.actState D =
        permuteState action.orientation
          (mapState action.factorwiseInjection D) := by
    exact hcastState _
  have hE11 : mapTerm action.factorwiseInjection E11 = E21 := by
    apply Prod.ext
    · apply Subtype.ext
      change (!![0, 1; 1, 0] : BinarySquareMatrix 2).mulVec e1.1 = e2.1
      decide
    · apply Prod.ext
      · apply Subtype.ext
        change (1 : BinarySquareMatrix 2).mulVec e1.1 = e1.1
        decide
      · apply Subtype.ext
        change (1 : BinarySquareMatrix 1).mulVec w.1 = w.1
        decide
  have hE12 : mapTerm action.factorwiseInjection E12 = E22 := by
    apply Prod.ext
    · apply Subtype.ext
      change (!![0, 1; 1, 0] : BinarySquareMatrix 2).mulVec e1.1 = e2.1
      decide
    · apply Prod.ext
      · apply Subtype.ext
        change (1 : BinarySquareMatrix 2).mulVec e2.1 = e2.1
        decide
      · apply Subtype.ext
        change (1 : BinarySquareMatrix 1).mulVec w.1 = w.1
        decide
  change action.actEndpoints profile221SwapSource = profile221SwapTarget
  unfold ProfileAction.actEndpoints
  rw [hactState, hactState]
  change
    ⟨permuteState .abc (mapState action.factorwiseInjection {E11}),
      permuteState .abc (mapState action.factorwiseInjection {E12})⟩ =
        profile221SwapTarget
  rw [permuteState_abc, permuteState_abc]
  simp only [mapState, Finset.image_singleton, hE11, hE12,
    profile221SwapTarget]

/-- The actual type-valued witness for the exact profile-`221` endpoint image. -/
def profile221SwapWitness :
    ActionWitness profile221SwapSource profile221SwapTarget where
  action := profile221SwapAction
  maps_endpoints := profile221Swap_exact_endpoint_image

/-- The endpoint checker succeeds exactly with the concrete profile-`221`
swap witness data. -/
theorem profile221Swap_endpoint_check_success :
    checkActionWitness profile221SwapRaw profile221SwapSource
      profile221SwapTarget = some profile221SwapWitness := by
  exact checkActionWitness_eq_some_of profile221SwapRaw profile221SwapSource
    profile221SwapTarget profile221SwapAction profile221SwapRaw_check_success
    profile221Swap_exact_endpoint_image

end Regression

#check @BinarySquareMatrix
#check @BinaryGeneralLinear
#check @RawProfileAction.Valid
#check @RawProfileAction.toProfileAction
#check @ProfileAction.factorwiseInjection
#check @ProfileAction.actTerm
#check @ProfileAction.actState
#check @ProfileAction.actEndpoints
#check @RelationEndpoints
#check @ActionWitness
#check @RawProfileAction.check
#check @checkActionWitness
#check @checkActionWitness_isSome_iff
#check @Regression.profile221SwapWitness

#print axioms RawProfileAction.toProfileAction_first_coe
#print axioms ProfileAction.actTerm_injective
#print axioms ProfileAction.actState_card
#print axioms checkActionWitness_isSome_iff
#print axioms Regression.profile221Swap_endpoint_check_success

end BilinearComplexity.NormalizedBinaryFiniteAction
