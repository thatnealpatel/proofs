import BilinearComplexity.BinaryAmbientTensorCoordinates
import BilinearComplexity.NormalizedBinaryOrbitClassification
import BilinearComplexity.NormalizedBinaryOrbitInvariants

set_option autoImplicit false

/-!
# Basis independence of normalized ambient orbit coordinates

A supplied coordinate frame normalizes finite states in three ambient binary
vector spaces.  Changing all three frames carries the old normalized state to
the new normalized state by factorwise additive injections.  Consequently the
semantic pair-count invariant, and hence the unique thirteen-orbit label, is
independent of those supplied frames.

This bridge concerns coordinate changes only.  It neither reconstructs matrix
GL actions nor asserts invariance under circuit moves.
-/

namespace BilinearComplexity.BinaryAmbientOrbitCoordinates

open BinaryAmbientCarrier
open BinaryAmbientTensorCoordinates
open NormalizedBinaryCarrier
open NormalizedBinaryCoverage
open NormalizedBinaryFiniteAction
open NormalizedBinaryMoveTransport
open NormalizedBinaryOrbitClassification
open NormalizedBinaryOrbitInvariants
open NormalizedBinaryRelationEnumeration

universe u v w

/-- The ordered factorwise coordinate change from an old supplied frame to a
new supplied frame on the same three ambient spaces. -/
def coordinateChangeInjection
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    {a b c a' b' c' : ℕ}
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W)
    (fU : Coord a' ≃ₗ[F2] U) (fV : Coord b' ≃ₗ[F2] V)
    (fW : Coord c' ≃ₗ[F2] W) :
    FactorwiseAdditiveInjection (coordinateProfile a b c)
      (coordinateProfile a' b' c') where
  first := (eU.trans fU.symm).toLinearMap.toAddMonoidHom
  second := (eV.trans fV.symm).toLinearMap.toAddMonoidHom
  third := (eW.trans fW.symm).toLinearMap.toAddMonoidHom
  first_injective := (eU.trans fU.symm).injective
  second_injective := (eV.trans fV.symm).injective
  third_injective := (eW.trans fW.symm).injective

example (a b c : ℕ) (x : Coord a) :
    (coordinateChangeInjection
      (LinearEquiv.refl F2 (Coord a)) (LinearEquiv.refl F2 (Coord b))
      (LinearEquiv.refl F2 (Coord c)) (LinearEquiv.refl F2 (Coord a))
      (LinearEquiv.refl F2 (Coord b)) (LinearEquiv.refl F2 (Coord c))).first x = x :=
  rfl

/-- Coordinate change sends an old-frame normalized ambient term exactly to
its normalization in the new frame. -/
theorem mapTerm_normalizeTerm
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    {a b c a' b' c' : ℕ}
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W)
    (fU : Coord a' ≃ₗ[F2] U) (fV : Coord b' ≃ₗ[F2] V)
    (fW : Coord c' ≃ₗ[F2] W)
    (t : BinaryAmbientCarrier.Carrier U V W) :
    mapTerm (coordinateChangeInjection eU eV eW fU fV fW)
      (normalizeTerm eU eV eW t) = normalizeTerm fU fV fW t := by
  apply Prod.ext
  · apply Subtype.ext
    change fU.symm (eU (eU.symm t.1.1)) = fU.symm t.1.1
    rw [eU.apply_symm_apply]
  · apply Prod.ext
    · apply Subtype.ext
      change fV.symm (eV (eV.symm t.2.1.1)) = fV.symm t.2.1.1
      rw [eV.apply_symm_apply]
    · apply Subtype.ext
      change fW.symm (eW (eW.symm t.2.2.1)) = fW.symm t.2.2.1
      rw [eW.apply_symm_apply]

/-- Coordinate change sends every old-frame normalized finite ambient state
exactly to its normalization in the new frame. -/
theorem mapState_normalizeState
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    {a b c a' b' c' : ℕ}
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W)
    (fU : Coord a' ≃ₗ[F2] U) (fV : Coord b' ≃ₗ[F2] V)
    (fW : Coord c' ≃ₗ[F2] W)
    (D : BinaryAmbientCarrier.State U V W) :
    mapState (coordinateChangeInjection eU eV eW fU fV fW)
        (normalizeState eU eV eW D) = normalizeState fU fV fW D := by
  unfold mapState normalizeState
  rw [Finset.map_eq_image, Finset.map_eq_image, Finset.image_image]
  apply Finset.image_congr
  intro t ht
  exact mapTerm_normalizeTerm eU eV eW fU fV fW t

example (a b c : ℕ) :
    mapState (coordinateChangeInjection
      (LinearEquiv.refl F2 (Coord a)) (LinearEquiv.refl F2 (Coord b))
      (LinearEquiv.refl F2 (Coord c)) (LinearEquiv.refl F2 (Coord a))
      (LinearEquiv.refl F2 (Coord b)) (LinearEquiv.refl F2 (Coord c)))
      (normalizeState (LinearEquiv.refl F2 (Coord a))
        (LinearEquiv.refl F2 (Coord b)) (LinearEquiv.refl F2 (Coord c)) ∅) =
      normalizeState (LinearEquiv.refl F2 (Coord a))
        (LinearEquiv.refl F2 (Coord b)) (LinearEquiv.refl F2 (Coord c)) ∅ := by
  apply mapState_normalizeState

/-- The semantic ordered pair-count invariant of two normalized ambient
endpoints is independent of all three supplied coordinate frames. -/
theorem relationInvariant_normalizeState_independent
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    {a b c a' b' c' : ℕ}
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W)
    (fU : Coord a' ≃ₗ[F2] U) (fV : Coord b' ≃ₗ[F2] V)
    (fW : Coord c' ≃ₗ[F2] W)
    (A B : BinaryAmbientCarrier.State U V W) :
    relationInvariant
        (⟨normalizeState eU eV eW A, normalizeState eU eV eW B⟩ :
          RelationEndpoints (coordinateProfile a b c)) =
      relationInvariant
        (⟨normalizeState fU fV fW A, normalizeState fU fV fW B⟩ :
          RelationEndpoints (coordinateProfile a' b' c')) := by
  let change := coordinateChangeInjection eU eV eW fU fV fW
  let oldEndpoints : RelationEndpoints (coordinateProfile a b c) :=
    ⟨normalizeState eU eV eW A, normalizeState eU eV eW B⟩
  calc
    relationInvariant oldEndpoints =
        relationInvariant
          (⟨mapState change oldEndpoints.left,
            mapState change oldEndpoints.right⟩ :
            RelationEndpoints (coordinateProfile a' b' c')) :=
      (relationInvariant_map change oldEndpoints).symm
    _ = relationInvariant
        (⟨normalizeState fU fV fW A, normalizeState fU fV fW B⟩ :
          RelationEndpoints (coordinateProfile a' b' c')) := by
      rw [mapState_normalizeState, mapState_normalizeState]

/-- Two finite coordinate frames onto the same binary vector space necessarily
have equal displayed dimensions. -/
theorem coordinateDimension_eq
    {U : Type u} [AddCommGroup U] [Module F2 U]
    {a a' : ℕ} (e : Coord a ≃ₗ[F2] U) (f : Coord a' ≃ₗ[F2] U) :
    a = a' := by
  have hfinrank : Module.finrank F2 (Coord a) =
      Module.finrank F2 (Coord a') := e.finrank_eq.trans f.finrank_eq.symm
  simpa only [Coord, Module.finrank_fin_fun] using hfinrank

example (a : ℕ) : coordinateDimension_eq
    (LinearEquiv.refl F2 (Coord a)) (LinearEquiv.refl F2 (Coord a)) = rfl :=
  rfl

/-- Three supplied frames onto the same ordered ambient factors have identical
normalized profiles. -/
theorem coordinateProfile_eq
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    {a b c a' b' c' : ℕ}
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W)
    (fU : Coord a' ≃ₗ[F2] U) (fV : Coord b' ≃ₗ[F2] V)
    (fW : Coord c' ≃ₗ[F2] W) :
    coordinateProfile a b c = coordinateProfile a' b' c' := by
  rw [coordinateDimension_eq eU fU, coordinateDimension_eq eV fV,
    coordinateDimension_eq eW fW]

/-- At one normalized profile, semantic membership in possibly different
endpoint relations still determines the same canonical profile family. -/
theorem inOrbit_family_eq_of_sameProfile {p : Profile}
    {first second : OrbitLabel} {R S : RelationEndpoints p}
    (hfirst : InOrbit first R) (hsecond : InOrbit second S) :
    first.1 = second.1 := by
  rcases hfirst with ⟨firstChoice, hfirstFamily, _⟩
  rcases hsecond with ⟨secondChoice, hsecondFamily, _⟩
  exact hfirstFamily.trans
    ((profileOrientation_family_unique firstChoice secondChoice).trans
      hsecondFamily.symm)

/-- Semantic orbit labels of the same ambient endpoint pair are independent of
which three supplied coordinate frames are used.  No exactness or coverage
hypothesis is required beyond the two semantic membership witnesses. -/
theorem inOrbit_label_eq_of_normalizeState
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    {a b c a' b' c' : ℕ}
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W)
    (fU : Coord a' ≃ₗ[F2] U) (fV : Coord b' ≃ₗ[F2] V)
    (fW : Coord c' ≃ₗ[F2] W)
    (A B : BinaryAmbientCarrier.State U V W)
    (first second : OrbitLabel)
    (hfirst : InOrbit first
      (⟨normalizeState eU eV eW A, normalizeState eU eV eW B⟩ :
        RelationEndpoints (coordinateProfile a b c)))
    (hsecond : InOrbit second
      (⟨normalizeState fU fV fW A, normalizeState fU fV fW B⟩ :
        RelationEndpoints (coordinateProfile a' b' c'))) :
    first = second := by
  have ha : a = a' := coordinateDimension_eq eU fU
  have hb : b = b' := coordinateDimension_eq eV fV
  have hc : c = c' := coordinateDimension_eq eW fW
  subst a'
  subst b'
  subst c'
  rcases first with ⟨firstFamily, firstIndex⟩
  rcases second with ⟨secondFamily, secondIndex⟩
  have hfamily : firstFamily = secondFamily :=
    inOrbit_family_eq_of_sameProfile hfirst hsecond
  subst secondFamily
  have hfirstInvariant := selectedInvariant_eq_of_inOrbit
    ⟨firstFamily, firstIndex⟩ _ hfirst
  have hsecondInvariant := selectedInvariant_eq_of_inOrbit
    ⟨firstFamily, secondIndex⟩ _ hsecond
  have hnormalized := relationInvariant_normalizeState_independent
    eU eV eW fU fV fW A B
  have hindex : firstIndex = secondIndex :=
    selectedRowInvariant_injective firstFamily
      (hfirstInvariant.trans (hnormalized.trans hsecondInvariant.symm))
  subst secondIndex
  rfl

/-- Consequently, whenever both frame normalizations of an ambient endpoint
pair satisfy the exact-relation hypotheses, their classified compiler outputs
carry the same semantic orbit label. -/
theorem compileClassified_label_normalizeState_eq
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    {a b c a' b' c' : ℕ}
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W)
    (fU : Coord a' ≃ₗ[F2] U) (fV : Coord b' ≃ₗ[F2] V)
    (fW : Coord c' ≃ₗ[F2] W)
    (A B : BinaryAmbientCarrier.State U V W)
    (hold : IsExactRelation
      (⟨normalizeState eU eV eW A, normalizeState eU eV eW B⟩ :
        RelationEndpoints (coordinateProfile a b c)))
    (hnew : IsExactRelation
      (⟨normalizeState fU fV fW A, normalizeState fU fV fW B⟩ :
        RelationEndpoints (coordinateProfile a' b' c'))) :
    (compileClassified ⟨_, hold⟩).label =
      (compileClassified ⟨_, hnew⟩).label := by
  apply inOrbit_label_eq_of_normalizeState eU eV eW fU fV fW A B
  · exact (compileClassified ⟨_, hold⟩).membership
  · exact (compileClassified ⟨_, hnew⟩).membership

#check @coordinateChangeInjection
#check @mapTerm_normalizeTerm
#check @mapState_normalizeState
#check @relationInvariant_normalizeState_independent
#check @coordinateDimension_eq
#check @coordinateProfile_eq
#check @inOrbit_family_eq_of_sameProfile
#check @inOrbit_label_eq_of_normalizeState
#check @compileClassified_label_normalizeState_eq

#print axioms mapState_normalizeState
#print axioms relationInvariant_normalizeState_independent
#print axioms coordinateDimension_eq
#print axioms inOrbit_label_eq_of_normalizeState
#print axioms compileClassified_label_normalizeState_eq

end BilinearComplexity.BinaryAmbientOrbitCoordinates
