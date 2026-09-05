import BilinearComplexity.NormalizedBinaryFiveCircuitCertificate
import BilinearComplexity.NormalizedBinaryFiniteAction

set_option autoImplicit false

/-!
# Global mode permutation for mixed normalized binary paths

This module closes the proof-facing `AllModeMove` relation under an arbitrary
single permutation of all three tensor modes.  It provides the six-orientation
composition and inverse tables, recursively maps concrete mixed paths while
preserving their vertices, length, altitude, and factor-span confinement, and
transports `FiveCircuitCertificate` values.  The final action-witness adapter
uses the checked convention: factor maps first, mode permutation second,
profile cast third, and literal endpoint rewrites last.

The construction preserves each directed Split, Flip, or Reduction through
its existing edge provenance; it does not symmetrize the relation.  It proves
transport of already supplied certificates only.  It does not prove finite
coverage, normalization, orbit classification, compiler totality, or any
Scheme/Arai representation bridge.

AI disclosure: produced with AI assistance (see `README`).
-/

namespace BilinearComplexity.NormalizedBinaryAllModePermutation

open BinaryCircuit
open NormalizedBinaryCarrier
open NormalizedBinaryReplay221
open NormalizedBinaryModePermutation
open NormalizedBinaryAllModeMove
open NormalizedBinaryMoveTransport
open NormalizedBinaryAllModeMoveTransport
open NormalizedBinaryFiveCircuitCertificate
open NormalizedBinaryFiniteAction
open Scheme.Action

/-- Compose an inner orientation followed by an outer orientation. -/
def orientationCompose (outer inner : Orientation) : Orientation :=
  match outer, inner with
  | .abc, x => x
  | .bca, .abc => .bca
  | .bca, .bca => .cab
  | .bca, .cab => .abc
  | .bca, .acb => .cba
  | .bca, .cba => .bac
  | .bca, .bac => .acb
  | .cab, .abc => .cab
  | .cab, .bca => .abc
  | .cab, .cab => .bca
  | .cab, .acb => .bac
  | .cab, .cba => .acb
  | .cab, .bac => .cba
  | .acb, .abc => .acb
  | .acb, .bca => .bac
  | .acb, .cab => .cba
  | .acb, .acb => .abc
  | .acb, .cba => .cab
  | .acb, .bac => .bca
  | .cba, .abc => .cba
  | .cba, .bca => .acb
  | .cba, .cab => .bac
  | .cba, .acb => .bca
  | .cba, .cba => .abc
  | .cba, .bac => .cab
  | .bac, .abc => .bac
  | .bac, .bca => .cba
  | .bac, .cab => .acb
  | .bac, .acb => .cab
  | .bac, .cba => .bca
  | .bac, .bac => .abc

/-- Invert an orientation. -/
def orientationInverse (o : Orientation) : Orientation :=
  match o with
  | .abc => .abc
  | .bca => .cab
  | .cab => .bca
  | .acb => .acb
  | .cba => .cba
  | .bac => .bac

example : orientationCompose .bca .acb = .cba := rfl
example : orientationInverse .bca = .cab := rfl


/-- The identity orientation is a left identity for composition. -/
@[simp] theorem orientationCompose_abc_left (o : Orientation) :
    orientationCompose .abc o = o := by
  rfl

/-- The identity orientation is a right identity for composition. -/
@[simp] theorem orientationCompose_abc_right (o : Orientation) :
    orientationCompose o .abc = o := by
  cases o <;> rfl

/-- Explicit orientation composition is associative. -/
theorem orientationCompose_assoc (outer middle inner : Orientation) :
    orientationCompose outer (orientationCompose middle inner) =
      orientationCompose (orientationCompose outer middle) inner := by
  cases outer <;> cases middle <;> cases inner <;> rfl

/-- Inverting an orientation twice restores it. -/
@[simp] theorem orientationInverse_involutive (o : Orientation) :
    orientationInverse (orientationInverse o) = o := by
  cases o <;> rfl

/-- Reordering a profile successively agrees with the explicit orientation
composition table. -/
@[simp] theorem permProfile_compose (outer inner : Orientation) (p : Profile) :
    permProfile outer (permProfile inner p) =
      permProfile (orientationCompose outer inner) p := by
  cases outer <;> cases inner <;> cases p <;> rfl

/-- Composing an orientation inverse on the left gives the identity
orientation. -/
@[simp] theorem orientationCompose_inverse_left (o : Orientation) :
    orientationCompose (orientationInverse o) o = .abc := by
  cases o <;> rfl

/-- Composing an orientation inverse on the right gives the identity
orientation. -/
@[simp] theorem orientationCompose_inverse_right (o : Orientation) :
    orientationCompose o (orientationInverse o) = .abc := by
  cases o <;> rfl

/-- Applying an orientation and then its inverse restores the source
profile. -/
@[simp] theorem permProfile_inverse_left (o : Orientation) (p : Profile) :
    permProfile (orientationInverse o) (permProfile o p) = p := by
  cases o <;> cases p <;> rfl

/-- Applying an inverse orientation and then the orientation restores the
source profile. -/
@[simp] theorem permProfile_inverse_right (o : Orientation) (p : Profile) :
    permProfile o (permProfile (orientationInverse o) p) = p := by
  cases o <;> cases p <;> rfl

/-- Relabeling a mode successively agrees with the explicit orientation
composition table. -/
@[simp] theorem orientationMode_compose (outer inner : Orientation) (m : Fin 3) :
    orientationMode (orientationCompose outer inner) m =
      orientationMode outer (orientationMode inner m) := by
  cases outer <;> cases inner <;> fin_cases m <;> rfl

/-- Successive term permutations agree, after the profile cast, with the
explicit orientation composition. -/
@[simp] theorem permuteTerm_compose {p : Profile} (outer inner : Orientation)
    (t : Carrier p) :
    cast (congrArg Carrier (permProfile_compose outer inner p))
        (permuteTerm outer (permuteTerm inner t)) =
      permuteTerm (orientationCompose outer inner) t := by
  cases outer <;> cases inner <;> cases p <;> rfl

/-- Successive state permutations agree, after the profile cast, with the
explicit orientation composition. -/
@[simp] theorem permuteState_compose {p : Profile} (outer inner : Orientation)
    (D : State p) :
    cast (congrArg State (permProfile_compose outer inner p))
        (permuteState outer (permuteState inner D)) =
      permuteState (orientationCompose outer inner) D := by
  cases outer <;> cases inner <;> cases p <;>
    simp only [permuteState, Finset.image_image]
  all_goals
    apply Finset.image_congr
    intro t _
    rfl

/-- Permuting a term and then applying the inverse restores the term after
the profile cast. -/
@[simp] theorem permuteTerm_inverse_left {p : Profile} (o : Orientation)
    (t : Carrier p) :
    cast (congrArg Carrier (permProfile_inverse_left o p))
        (permuteTerm (orientationInverse o) (permuteTerm o t)) = t := by
  cases o <;> cases p <;> rfl

/-- Permuting a state and then applying the inverse restores the state after
the profile cast. -/
@[simp] theorem permuteState_inverse_left {p : Profile} (o : Orientation)
    (D : State p) :
    cast (congrArg State (permProfile_inverse_left o p))
        (permuteState (orientationInverse o) (permuteState o D)) = D := by
  cases o <;> cases p <;>
    simp only [permuteState, Finset.image_image]
  all_goals
    exact Finset.image_id


/-- Applying an inverse permutation to a term and then the original
permutation restores the term after the profile cast. -/
@[simp] theorem permuteTerm_inverse_right {p : Profile} (o : Orientation)
    (t : Carrier p) :
    cast (congrArg Carrier (permProfile_inverse_right o p))
        (permuteTerm o (permuteTerm (orientationInverse o) t)) = t := by
  cases o <;> cases p <;> rfl

/-- Applying an inverse permutation to a state and then the original
permutation restores the state after the profile cast. -/
@[simp] theorem permuteState_inverse_right {p : Profile} (o : Orientation)
    (D : State p) :
    cast (congrArg State (permProfile_inverse_right o p))
        (permuteState o (permuteState (orientationInverse o) D)) = D := by
  cases o <;> cases p <;>
    simp only [permuteState, Finset.image_image]
  all_goals
    exact Finset.image_id

/-- A global mode permutation carries any mixed all-mode edge to another
mixed all-mode edge. -/
theorem permuteAllModeMove {q : Profile} (global : Orientation)
    {D E : State q} (h : @AllModeMove q D E) :
    @AllModeMove (permProfile global q)
      (permuteState global D) (permuteState global E) := by
  rcases h with ⟨p, inner, rfl, hinner⟩
  have hinner' : @OrientationMove p inner D E := by
    simpa using hinner
  obtain ⟨D₀, E₀, hold, hD, hE⟩ := hinner'.provenance
  rw [hD, hE]
  let combined := orientationCompose global inner
  have hp : permProfile combined p =
      permProfile global (permProfile inner p) :=
    (permProfile_compose global inner p).symm
  refine ⟨p, combined, hp, ?_⟩
  change @OrientationMove p combined
    (cast (congrArg State hp.symm)
      (permuteState global (permuteState inner D₀)))
    (cast (congrArg State hp.symm)
      (permuteState global (permuteState inner E₀)))
  rw [permuteState_compose, permuteState_compose]
  exact permuteMove combined hold

/-- Recursively permute every vertex and every independently oriented edge of
a mixed all-mode path. -/
def permuteAllModePath {q : Profile} (o : Orientation) :
    {D E : State q} → MovePath (@AllModeMove q) D E →
      MovePath (@AllModeMove (permProfile o q))
        (permuteState o D) (permuteState o E)
  | _, _, .singleton D => .singleton (permuteState o D)
  | _, _, .snoc path h =>
      .snoc (permuteAllModePath o path) (permuteAllModeMove o h)

example {q : Profile} (o : Orientation) (D : State q) :
    permuteAllModePath o (.singleton D : MovePath (@AllModeMove q) D D) =
      (.singleton (permuteState o D) :
        MovePath (@AllModeMove (permProfile o q))
          (permuteState o D) (permuteState o D)) := by
  simp only [permuteAllModePath]

/-- A globally permuted mixed path has the pointwise permuted vertex list. -/
theorem permuteAllModePath_vertices {q : Profile} (o : Orientation)
    {D E : State q} (path : MovePath (@AllModeMove q) D E) :
    (permuteAllModePath o path).vertices =
      path.vertices.map (permuteState o) := by
  induction path with
  | singleton =>
      simp only [permuteAllModePath, MovePath.vertices, List.map_singleton]
  | snoc path _ ih =>
      simp only [permuteAllModePath, MovePath.vertices, ih, List.map_append,
        List.map_singleton]

/-- Global mode permutation preserves mixed-path length. -/
@[simp] theorem permuteAllModePath_length {q : Profile} (o : Orientation)
    {D E : State q} (path : MovePath (@AllModeMove q) D E) :
    (permuteAllModePath o path).length = path.length := by
  induction path with
  | singleton => simp only [permuteAllModePath, MovePath.length]
  | snoc path _ ih => simp only [permuteAllModePath, MovePath.length, ih]

/-- Global mode permutation preserves mixed-path altitude. -/
@[simp] theorem permuteAllModePath_altitude {q : Profile} (o : Orientation)
    {D E : State q} (path : MovePath (@AllModeMove q) D E) :
    (permuteAllModePath o path).altitude = path.altitude := by
  induction path with
  | singleton => simp only [permuteAllModePath, MovePath.altitude, permuteState_card]
  | snoc path _ ih =>
      simp only [permuteAllModePath, MovePath.altitude, ih, permuteState_card]

/-- Vertices of a globally permuted mixed path are exactly images of source
vertices. -/
theorem permuteAllModePath_pathVertex_iff {q : Profile} (o : Orientation)
    {D E : State q} (path : MovePath (@AllModeMove q) D E)
    (Y : State (permProfile o q)) :
    PathVertex (permuteAllModePath o path) Y ↔
      ∃ X, PathVertex path X ∧ permuteState o X = Y := by
  simp only [PathVertex, permuteAllModePath_vertices, List.mem_map]



/-- Finite term-set confinement is preserved when every vertex of a mixed path
is globally mode-permuted. -/
theorem permuteAllModePath_confined {p : Profile} (o : Orientation)
    {D E K : State p} (path : MovePath (@AllModeMove p) D E)
    (h : ∀ X, PathVertex path X → X ⊆ K) :
    ∀ Y, PathVertex (permuteAllModePath o path) Y →
      Y ⊆ permuteState o K := by
  intro Y hY
  obtain ⟨X, hX, hXY⟩ :=
    (permuteAllModePath_pathVertex_iff o path Y).mp hY
  rw [← hXY]
  exact Finset.image_mono (permuteTerm o) (h X hX)

private theorem firstFactorSpan_permuteState_abc {p : Profile} (D : State p) :
    firstFactorSpan (permuteState .abc D) = firstFactorSpan D := by
  rw [permuteState_abc]
  rfl

private theorem secondFactorSpan_permuteState_abc {p : Profile} (D : State p) :
    secondFactorSpan (permuteState .abc D) = secondFactorSpan D := by
  rw [permuteState_abc]
  rfl

private theorem thirdFactorSpan_permuteState_abc {p : Profile} (D : State p) :
    thirdFactorSpan (permuteState .abc D) = thirdFactorSpan D := by
  rw [permuteState_abc]
  rfl

private theorem firstFactorSpan_permuteState_bca {p : Profile} (D : State p) :
    firstFactorSpan (permuteState .bca D) = secondFactorSpan D := by
  unfold firstFactorSpan secondFactorSpan permuteState
  rw [Finset.image_image]
  congr 2

private theorem secondFactorSpan_permuteState_bca {p : Profile} (D : State p) :
    secondFactorSpan (permuteState .bca D) = thirdFactorSpan D := by
  unfold secondFactorSpan thirdFactorSpan permuteState
  rw [Finset.image_image]
  congr 2

private theorem thirdFactorSpan_permuteState_bca {p : Profile} (D : State p) :
    thirdFactorSpan (permuteState .bca D) = firstFactorSpan D := by
  unfold thirdFactorSpan firstFactorSpan permuteState
  rw [Finset.image_image]
  congr 2

private theorem firstFactorSpan_permuteState_cab {p : Profile} (D : State p) :
    firstFactorSpan (permuteState .cab D) = thirdFactorSpan D := by
  unfold firstFactorSpan thirdFactorSpan permuteState
  rw [Finset.image_image]
  congr 2

private theorem secondFactorSpan_permuteState_cab {p : Profile} (D : State p) :
    secondFactorSpan (permuteState .cab D) = firstFactorSpan D := by
  unfold secondFactorSpan firstFactorSpan permuteState
  rw [Finset.image_image]
  congr 2

private theorem thirdFactorSpan_permuteState_cab {p : Profile} (D : State p) :
    thirdFactorSpan (permuteState .cab D) = secondFactorSpan D := by
  unfold thirdFactorSpan secondFactorSpan permuteState
  rw [Finset.image_image]
  congr 2

private theorem firstFactorSpan_permuteState_acb {p : Profile} (D : State p) :
    firstFactorSpan (permuteState .acb D) = firstFactorSpan D := by
  unfold firstFactorSpan permuteState
  rw [Finset.image_image]
  congr 2

private theorem secondFactorSpan_permuteState_acb {p : Profile} (D : State p) :
    secondFactorSpan (permuteState .acb D) = thirdFactorSpan D := by
  unfold secondFactorSpan thirdFactorSpan permuteState
  rw [Finset.image_image]
  congr 2

private theorem thirdFactorSpan_permuteState_acb {p : Profile} (D : State p) :
    thirdFactorSpan (permuteState .acb D) = secondFactorSpan D := by
  unfold thirdFactorSpan secondFactorSpan permuteState
  rw [Finset.image_image]
  congr 2

private theorem firstFactorSpan_permuteState_cba {p : Profile} (D : State p) :
    firstFactorSpan (permuteState .cba D) = thirdFactorSpan D := by
  unfold firstFactorSpan thirdFactorSpan permuteState
  rw [Finset.image_image]
  congr 2

private theorem secondFactorSpan_permuteState_cba {p : Profile} (D : State p) :
    secondFactorSpan (permuteState .cba D) = secondFactorSpan D := by
  unfold secondFactorSpan permuteState
  rw [Finset.image_image]
  congr 2

private theorem thirdFactorSpan_permuteState_cba {p : Profile} (D : State p) :
    thirdFactorSpan (permuteState .cba D) = firstFactorSpan D := by
  unfold thirdFactorSpan firstFactorSpan permuteState
  rw [Finset.image_image]
  congr 2

private theorem firstFactorSpan_permuteState_bac {p : Profile} (D : State p) :
    firstFactorSpan (permuteState .bac D) = secondFactorSpan D := by
  unfold firstFactorSpan secondFactorSpan permuteState
  rw [Finset.image_image]
  congr 2

private theorem secondFactorSpan_permuteState_bac {p : Profile} (D : State p) :
    secondFactorSpan (permuteState .bac D) = firstFactorSpan D := by
  unfold secondFactorSpan firstFactorSpan permuteState
  rw [Finset.image_image]
  congr 2

private theorem thirdFactorSpan_permuteState_bac {p : Profile} (D : State p) :
    thirdFactorSpan (permuteState .bac D) = thirdFactorSpan D := by
  unfold thirdFactorSpan permuteState
  rw [Finset.image_image]
  congr 2

/-- Global mode permutation reorders all three factor-span confinement
inequalities without weakening any of them. -/
theorem factorSpanConfined_permute {p : Profile} (o : Orientation)
    {K X : State p} (h : FactorSpanConfined K X) :
    FactorSpanConfined (permuteState o K) (permuteState o X) := by
  cases o with
  | abc =>
      rw [FactorSpanConfined, firstFactorSpan_permuteState_abc,
        firstFactorSpan_permuteState_abc, secondFactorSpan_permuteState_abc,
        secondFactorSpan_permuteState_abc, thirdFactorSpan_permuteState_abc,
        thirdFactorSpan_permuteState_abc]
      exact h
  | bca =>
      rw [FactorSpanConfined, firstFactorSpan_permuteState_bca,
        firstFactorSpan_permuteState_bca, secondFactorSpan_permuteState_bca,
        secondFactorSpan_permuteState_bca, thirdFactorSpan_permuteState_bca,
        thirdFactorSpan_permuteState_bca]
      exact ⟨h.2.1, h.2.2, h.1⟩
  | cab =>
      rw [FactorSpanConfined, firstFactorSpan_permuteState_cab,
        firstFactorSpan_permuteState_cab, secondFactorSpan_permuteState_cab,
        secondFactorSpan_permuteState_cab, thirdFactorSpan_permuteState_cab,
        thirdFactorSpan_permuteState_cab]
      exact ⟨h.2.2, h.1, h.2.1⟩
  | acb =>
      rw [FactorSpanConfined, firstFactorSpan_permuteState_acb,
        firstFactorSpan_permuteState_acb, secondFactorSpan_permuteState_acb,
        secondFactorSpan_permuteState_acb, thirdFactorSpan_permuteState_acb,
        thirdFactorSpan_permuteState_acb]
      exact ⟨h.1, h.2.2, h.2.1⟩
  | cba =>
      rw [FactorSpanConfined, firstFactorSpan_permuteState_cba,
        firstFactorSpan_permuteState_cba, secondFactorSpan_permuteState_cba,
        secondFactorSpan_permuteState_cba, thirdFactorSpan_permuteState_cba,
        thirdFactorSpan_permuteState_cba]
      exact ⟨h.2.2, h.2.1, h.1⟩
  | bac =>
      rw [FactorSpanConfined, firstFactorSpan_permuteState_bac,
        firstFactorSpan_permuteState_bac, secondFactorSpan_permuteState_bac,
        secondFactorSpan_permuteState_bac, thirdFactorSpan_permuteState_bac,
        thirdFactorSpan_permuteState_bac]
      exact ⟨h.2.1, h.1, h.2.2⟩

/-- Factor-span confinement of every mixed-path vertex survives a global mode
permutation, with the endpoint boundary permuted in the same way. -/
theorem pathFactorSpanConfined_permute {p : Profile} (o : Orientation)
    {D E K : State p} (path : MovePath (@AllModeMove p) D E)
    (h : PathFactorSpanConfined path K) :
    PathFactorSpanConfined (permuteAllModePath o path) (permuteState o K) := by
  intro Y hY
  obtain ⟨X, hX, hXY⟩ :=
    (permuteAllModePath_pathVertex_iff o path Y).mp hY
  rw [← hXY]
  exact factorSpanConfined_permute o (h X hX)


#check @orientationCompose
#check @orientationInverse
#check @permuteAllModeMove
#check @permuteAllModePath
#check @permuteAllModePath_vertices
#check @permuteAllModePath_length
#check @permuteAllModePath_altitude
#check @permuteAllModePath_confined
#check @factorSpanConfined_permute
#check @pathFactorSpanConfined_permute
#print axioms pathFactorSpanConfined_permute

end BilinearComplexity.NormalizedBinaryAllModePermutation


namespace BilinearComplexity.NormalizedBinaryFiveCircuitCertificate

open NormalizedBinaryCarrier
open NormalizedBinaryReplay221
open NormalizedBinaryModePermutation
open NormalizedBinaryAllModeMove
open NormalizedBinaryAllModePermutation
open Scheme.Action

/-- Globally permute both mixed paths and all three confinement modes of a
five-circuit certificate.  The ordered left and right endpoints are not
exchanged. -/
def FiveCircuitCertificate.permute {p : Profile} {A B : State p}
    (cert : FiveCircuitCertificate p A B) (o : Orientation) :
    FiveCircuitCertificate (permProfile o p)
      (permuteState o A) (permuteState o B) where
  disjoint := (Finset.disjoint_image (permuteTerm_injective o)).mpr cert.disjoint
  card_left := (permuteState_card o A).trans cert.card_left
  card_right := (permuteState_card o B).trans cert.card_right
  forward := permuteAllModePath o cert.forward
  reverse := permuteAllModePath o cert.reverse
  forward_length_le := by
    rw [permuteAllModePath_length]
    exact cert.forward_length_le
  reverse_length_le := by
    rw [permuteAllModePath_length]
    exact cert.reverse_length_le
  forward_altitude_le := by
    rw [permuteAllModePath_altitude]
    exact cert.forward_altitude_le
  reverse_altitude_le := by
    rw [permuteAllModePath_altitude]
    exact cert.reverse_altitude_le
  forward_confined := by
    simpa only [permuteState_union] using
      pathFactorSpanConfined_permute o cert.forward cert.forward_confined
  reverse_confined := by
    simpa only [permuteState_union] using
      pathFactorSpanConfined_permute o cert.reverse cert.reverse_confined

example :
    FiveCircuitCertificate (permProfile .bca profile221)
      (permuteState .bca S0) (permuteState .bca S2) :=
  designatedReplay221Certificate.permute .bca

/-- Reindex a certificate along an equality of profiles, casting both endpoint
states and all stored proof-bearing path data. -/
def FiveCircuitCertificate.castProfile {p q : Profile} (h : p = q)
    {A B : State p} (cert : FiveCircuitCertificate p A B) :
    FiveCircuitCertificate q
      (cast (congrArg State h) A) (cast (congrArg State h) B) := by
  subst q
  simpa using cert

example {p : Profile} {A B : State p} (cert : FiveCircuitCertificate p A B) :
    cert.castProfile rfl = cert := by
  rfl

#check @FiveCircuitCertificate.permute
#check @FiveCircuitCertificate.castProfile
#print axioms FiveCircuitCertificate.permute
#print axioms FiveCircuitCertificate.castProfile

end BilinearComplexity.NormalizedBinaryFiveCircuitCertificate

namespace BilinearComplexity.NormalizedBinaryFiniteAction

open NormalizedBinaryCarrier
open NormalizedBinaryReplay221
open NormalizedBinaryModePermutation
open NormalizedBinaryMoveTransport
open NormalizedBinaryFiveCircuitCertificate
open Scheme.Action

/-- Transport a source certificate through the exact checked action witness:
first apply its three factor maps, then its global mode orientation, cast back
along the stored profile equality, and finally rewrite to the literal target
endpoints. -/
def ActionWitness.transportCertificate {p : Profile}
    {source target : RelationEndpoints p}
    (witness : ActionWitness source target)
    (cert : FiveCircuitCertificate p source.left source.right) :
    FiveCircuitCertificate p target.left target.right := by
  let factorCert := cert.map witness.action.factorwiseInjection
  let modeCert := factorCert.permute witness.action.orientation
  let actionCert := modeCert.castProfile witness.action.profile_eq
  rw [← witness.left_image, ← witness.right_image]
  exact actionCert


example :
    ∃ target : RelationEndpoints profile221,
      ∃ witness : ActionWitness
          (⟨S0, S2⟩ : RelationEndpoints profile221) target,
        witness.action.orientation = .bac ∧
          Nonempty (FiveCircuitCertificate profile221 target.left target.right) := by
  let action : ProfileAction profile221 :=
    { first := 1
      second := 1
      third := 1
      orientation := .bac
      profile_eq := rfl }
  let source : RelationEndpoints profile221 := ⟨S0, S2⟩
  let target : RelationEndpoints profile221 := action.actEndpoints source
  let witness : ActionWitness source target :=
    { action := action
      maps_endpoints := rfl }
  refine ⟨target, witness, rfl, ?_⟩
  exact ⟨witness.transportCertificate designatedReplay221Certificate⟩

#check @ActionWitness.transportCertificate
#print axioms ActionWitness.transportCertificate

end BilinearComplexity.NormalizedBinaryFiniteAction
