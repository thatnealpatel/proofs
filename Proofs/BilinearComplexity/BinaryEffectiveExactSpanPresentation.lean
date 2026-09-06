import BilinearComplexity.BinaryEffectiveSpanCoordinates
import BilinearComplexity.BinaryContextualFiveCircuitCompiler

set_option autoImplicit false

/-!
# Effective exact-span presentations in supplied full frames

Finite endpoint factors are pulled back through three explicit full-coordinate
frames.  The effective span constructor is run independently in each factor,
and the resulting coordinate spans are transported back to the ambient exact
factor spans.  No ambient basis or inverse is selected at runtime.
-/

namespace BilinearComplexity.BinaryEffectiveExactSpanPresentation

open NormalizedBinaryCarrier (F2)
open BinaryAmbientTensorCoordinates (Coord)
open BinaryAmbientNormalization

universe u v w

/-- First-factor endpoint generators expressed in a supplied full coordinate
frame. -/
def firstCoordinateGenerators
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    [DecidableEq (AmbientCarrier U V W)] {a : ℕ}
    (eU : Coord a ≃ₗ[F2] U) (K : AmbientState U V W) : Finset (Coord a) :=
  K.image fun t => eU.symm t.1.1

/-- Second-factor endpoint generators expressed in a supplied full coordinate
frame. -/
def secondCoordinateGenerators
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    [DecidableEq (AmbientCarrier U V W)] {b : ℕ}
    (eV : Coord b ≃ₗ[F2] V) (K : AmbientState U V W) : Finset (Coord b) :=
  K.image fun t => eV.symm t.2.1.1

/-- Third-factor endpoint generators expressed in a supplied full coordinate
frame. -/
def thirdCoordinateGenerators
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    [DecidableEq (AmbientCarrier U V W)] {c : ℕ}
    (eW : Coord c ≃ₗ[F2] W) (K : AmbientState U V W) : Finset (Coord c) :=
  K.image fun t => eW.symm t.2.2.1

private theorem map_firstCoordinateGenerators_span
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    [DecidableEq (AmbientCarrier U V W)] {a : ℕ}
    (eU : Coord a ≃ₗ[F2] U) (K : AmbientState U V W) :
    (Submodule.span F2
      (firstCoordinateGenerators eU K : Set (Coord a))).map eU.toLinearMap =
      BinaryAmbientCarrier.firstSpan K := by
  rw [Submodule.map_span]
  unfold firstCoordinateGenerators BinaryAmbientCarrier.firstSpan
  congr 1
  ext x
  simp

private theorem map_secondCoordinateGenerators_span
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    [DecidableEq (AmbientCarrier U V W)] {b : ℕ}
    (eV : Coord b ≃ₗ[F2] V) (K : AmbientState U V W) :
    (Submodule.span F2
      (secondCoordinateGenerators eV K : Set (Coord b))).map eV.toLinearMap =
      BinaryAmbientCarrier.secondSpan K := by
  rw [Submodule.map_span]
  unfold secondCoordinateGenerators BinaryAmbientCarrier.secondSpan
  congr 1
  ext x
  simp

private theorem map_thirdCoordinateGenerators_span
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    [DecidableEq (AmbientCarrier U V W)] {c : ℕ}
    (eW : Coord c ≃ₗ[F2] W) (K : AmbientState U V W) :
    (Submodule.span F2
      (thirdCoordinateGenerators eW K : Set (Coord c))).map eW.toLinearMap =
      BinaryAmbientCarrier.thirdSpan K := by
  rw [Submodule.map_span]
  unfold thirdCoordinateGenerators BinaryAmbientCarrier.thirdSpan
  congr 1
  ext x
  simp

/-- Construct exact endpoint-span coordinates effectively from finite endpoints
and explicit coordinate frames for all three ambient factor spaces. -/
def effectiveExactSpanPresentation
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    [DecidableEq (AmbientCarrier U V W)] {a b c : ℕ}
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W) (A B : AmbientState U V W) :
    ExactSpanPresentation A B := by
  let SU := firstCoordinateGenerators eU (A ∪ B)
  let SV := secondCoordinateGenerators eV (A ∪ B)
  let SW := thirdCoordinateGenerators eW (A ∪ B)
  let PU := BinaryEffectiveSpanCoordinates.effectiveSpanCoordinates SU
  let PV := BinaryEffectiveSpanCoordinates.effectiveSpanCoordinates SV
  let PW := BinaryEffectiveSpanCoordinates.effectiveSpanCoordinates SW
  let hU : (Submodule.span F2 (SU : Set (Coord a))).map eU.toLinearMap =
      BinaryAmbientCarrier.firstSpan (A ∪ B) :=
    map_firstCoordinateGenerators_span eU (A ∪ B)
  let hV : (Submodule.span F2 (SV : Set (Coord b))).map eV.toLinearMap =
      BinaryAmbientCarrier.secondSpan (A ∪ B) :=
    map_secondCoordinateGenerators_span eV (A ∪ B)
  let hW : (Submodule.span F2 (SW : Set (Coord c))).map eW.toLinearMap =
      BinaryAmbientCarrier.thirdSpan (A ∪ B) :=
    map_thirdCoordinateGenerators_span eW (A ∪ B)
  exact {
    profile := ⟨PU.r, PV.r, PW.r⟩
    firstCoordinates := PU.equiv.trans
      ((eU.submoduleMap _).trans (LinearEquiv.ofEq _ _ hU))
    secondCoordinates := PV.equiv.trans
      ((eV.submoduleMap _).trans (LinearEquiv.ofEq _ _ hV))
    thirdCoordinates := PW.equiv.trans
      ((eW.submoduleMap _).trans (LinearEquiv.ofEq _ _ hW)) }

/-! ## End-to-end computed-presentation regression -/

open NormalizedBinaryCarrier
open BinaryCircuit
open NormalizedBinaryFiveCircuitRows
open BinaryAmbientTensorCoordinates
open BinaryContextualFiveCircuitCompiler

private def effectiveRow22101Presentation :
    ExactSpanPresentation row22101Start row22101Finish :=
  effectiveExactSpanPresentation
    (LinearEquiv.refl F2 (Coord profile221.first))
    (LinearEquiv.refl F2 (Coord profile221.second))
    (LinearEquiv.refl F2 (Coord profile221.third))
    row22101Start row22101Finish

private theorem row22101_empty_context_disjoint :
    Disjoint
      (∅ : BinaryAmbientCarrier.State (Coord profile221.first)
        (Coord profile221.second) (Coord profile221.third))
      (row22101Start ∪ row22101Finish) :=
  Finset.disjoint_empty_left (row22101Start ∪ row22101Finish)

private def effectiveRow22101Compilation :=
  compileContextualBinaryFiveCircuit effectiveRow22101Presentation
    row22101_card_start row22101_card_finish row22101_disjoint
    row22101_ambient_evaluation_eq ∅ row22101_empty_context_disjoint

/-- The actual compiler instantiated with computed coordinates produces a
forward path between the original five-circuit endpoints. -/
example :
    MovePath BinaryAmbientMoves.AllModeMove row22101Start row22101Finish :=
  effectiveRow22101Compilation.forward

/-- The same computed presentation independently produces the reverse path. -/
example :
    MovePath BinaryAmbientMoves.AllModeMove row22101Finish row22101Start :=
  effectiveRow22101Compilation.reverse

/-- The computed-presentation forward compilation obeys the certified uniform
three-edge bound. -/
example : effectiveRow22101Compilation.forward.length ≤ 3 := by
  rw [ContextualBinaryFiveCircuitCompilation.forward_length]
  exact NormalizedBinaryContextualCompiler.orbitDistance_le_three
    effectiveRow22101Compilation.label

/-- The computed-presentation reverse compilation obeys the certified uniform
three-edge bound. -/
example : effectiveRow22101Compilation.reverse.length ≤ 3 := by
  rw [ContextualBinaryFiveCircuitCompilation.reverse_length]
  exact NormalizedBinaryContextualCompiler.orbitDistance_le_three
    effectiveRow22101Compilation.label

-- The executable result traverses the computed presentation in both
-- directions.  Its value is `([2, 3, 3], 2, [3, 3, 2], 2)`.
#eval (effectiveRow22101Compilation.forward.vertices.map Finset.card,
  effectiveRow22101Compilation.forward.length,
  effectiveRow22101Compilation.reverse.vertices.map Finset.card,
  effectiveRow22101Compilation.reverse.length)

#check @effectiveExactSpanPresentation

end BilinearComplexity.BinaryEffectiveExactSpanPresentation
