import BilinearComplexity.BinaryAmbientCarrier
import Mathlib.LinearAlgebra.Basis.Submodule
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace

set_option autoImplicit false

/-!
# Coordinates for ambient binary tensors

Supplied linear equivalences give executable conversions between ambient and
coordinate carrier states.  Separately, tensor-product bases identify abstract
ambient tensors with the coordinate tensors used by the normalized compiler.
The final section proves that inclusion of exact-span tensor products reflects
equality by constructing an explicit proof-side left inverse.
-/

namespace BilinearComplexity.BinaryAmbientTensorCoordinates

open scoped TensorProduct BigOperators

universe u v w

open NormalizedBinaryCarrier (F2)

/-- Coordinate vectors over the shared binary field. -/
abbrev Coord (d : ℕ) := Fin d → F2

/-- The normalized profile associated to three displayed coordinate dimensions. -/
def coordinateProfile (a b c : ℕ) : NormalizedBinaryCarrier.Profile := ⟨a, b, c⟩

/-- Restrict a linear equivalence to an equivalence of nonzero-vector subtypes. -/
def nonzeroEquiv
    {U : Type u} [AddCommGroup U] [Module F2 U] {a : ℕ}
    (e : Coord a ≃ₗ[F2] U) :
    NormalizedBinaryCarrier.NonzeroVector a ≃
      BinaryAmbientCarrier.NonzeroVector U where
  toFun x := ⟨e x.1, fun hx => x.2 (e.injective (hx.trans e.map_zero.symm))⟩
  invFun x := ⟨e.symm x.1, fun hx => x.2 (e.symm.injective (hx.trans e.symm.map_zero.symm))⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.1)
  right_inv x := Subtype.ext (e.apply_symm_apply x.1)

/-- The carrier equivalence induced by three supplied coordinate equivalences. -/
def carrierEquiv
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    {a b c : ℕ}
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W) :
    NormalizedBinaryCarrier.Carrier (coordinateProfile a b c) ≃
      BinaryAmbientCarrier.Carrier U V W :=
  (nonzeroEquiv eU).prodCongr ((nonzeroEquiv eV).prodCongr (nonzeroEquiv eW))

/-- Convert one ambient carrier term to normalized coordinates. -/
def normalizeTerm
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    {a b c : ℕ}
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W) :
    BinaryAmbientCarrier.Carrier U V W →
      NormalizedBinaryCarrier.Carrier (coordinateProfile a b c) :=
  (carrierEquiv eU eV eW).symm

/-- Convert one normalized coordinate term to its ambient realization. -/
def denormalizeTerm
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    {a b c : ℕ}
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W) :
    NormalizedBinaryCarrier.Carrier (coordinateProfile a b c) →
      BinaryAmbientCarrier.Carrier U V W :=
  carrierEquiv eU eV eW

/-- Normalize a finite ambient state using only supplied coordinate data. -/
def normalizeState
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    {a b c : ℕ}
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W)
    (D : BinaryAmbientCarrier.State U V W) :
    NormalizedBinaryCarrier.State (coordinateProfile a b c) :=
  D.map (carrierEquiv eU eV eW).symm.toEmbedding

/-- Realize a finite normalized state in the supplied ambient coordinates. -/
def denormalizeState
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    {a b c : ℕ}
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W)
    (D : NormalizedBinaryCarrier.State (coordinateProfile a b c)) :
    BinaryAmbientCarrier.State U V W :=
  D.map (carrierEquiv eU eV eW).toEmbedding

/-- Normalizing the ambient realization of a coordinate term returns the
original normalized term. -/
@[simp] theorem normalizeTerm_denormalizeTerm
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    {a b c : ℕ}
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W)
    (t : NormalizedBinaryCarrier.Carrier (coordinateProfile a b c)) :
    normalizeTerm eU eV eW (denormalizeTerm eU eV eW t) = t :=
  (carrierEquiv eU eV eW).symm_apply_apply t

/-- Realizing an ambient term after normalization returns the original
ambient term. -/
@[simp] theorem denormalizeTerm_normalizeTerm
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    {a b c : ℕ}
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W)
    (t : BinaryAmbientCarrier.Carrier U V W) :
    denormalizeTerm eU eV eW (normalizeTerm eU eV eW t) = t :=
  (carrierEquiv eU eV eW).apply_symm_apply t

/-- Normalizing a realized coordinate state reconstructs the original finite
normalized state, without requiring ambient decidable equality. -/
@[simp] theorem normalizeState_denormalizeState
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    {a b c : ℕ}
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W)
    (D : NormalizedBinaryCarrier.State (coordinateProfile a b c)) :
    normalizeState eU eV eW (denormalizeState eU eV eW D) = D := by
  unfold normalizeState denormalizeState
  rw [Finset.map_map]
  have hEmbedding :
      (carrierEquiv eU eV eW).toEmbedding.trans
          (carrierEquiv eU eV eW).symm.toEmbedding =
        Function.Embedding.refl _ := by
    exact Function.Embedding.ext fun t =>
      (carrierEquiv eU eV eW).symm_apply_apply t
  rw [hEmbedding, Finset.map_refl]

/-- Realizing a normalized ambient state reconstructs the original finite
ambient state, without selecting a decidable-equality instance. -/
@[simp] theorem denormalizeState_normalizeState
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    {a b c : ℕ}
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W)
    (D : BinaryAmbientCarrier.State U V W) :
    denormalizeState eU eV eW (normalizeState eU eV eW D) = D := by
  unfold normalizeState denormalizeState
  rw [Finset.map_map]
  have hEmbedding :
      (carrierEquiv eU eV eW).symm.toEmbedding.trans
          (carrierEquiv eU eV eW).toEmbedding =
        Function.Embedding.refl _ := by
    exact Function.Embedding.ext fun t =>
      (carrierEquiv eU eV eW).apply_symm_apply t
  rw [hEmbedding, Finset.map_refl]

/-- Normalization through an injective carrier equivalence preserves the
number of terms in a finite ambient state. -/
@[simp] theorem normalizeState_card
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    {a b c : ℕ}
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W)
    (D : BinaryAmbientCarrier.State U V W) :
    (normalizeState eU eV eW D).card = D.card := by
  simp [normalizeState]

/-- Ambient realization through an injective carrier equivalence preserves
the number of terms in a finite normalized state. -/
@[simp] theorem denormalizeState_card
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    {a b c : ℕ}
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W)
    (D : NormalizedBinaryCarrier.State (coordinateProfile a b c)) :
    (denormalizeState eU eV eW D).card = D.card := by
  simp [denormalizeState]

/-- Normalization reflects and preserves disjointness of finite states. -/
@[simp] theorem normalizeState_disjoint_iff
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    {a b c : ℕ}
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W)
    (D E : BinaryAmbientCarrier.State U V W) :
    Disjoint (normalizeState eU eV eW D) (normalizeState eU eV eW E) ↔
      Disjoint D E := by
  exact Finset.disjoint_map (carrierEquiv eU eV eW).symm.toEmbedding

/-- Ambient realization reflects and preserves disjointness of finite states. -/
@[simp] theorem denormalizeState_disjoint_iff
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    {a b c : ℕ}
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W)
    (D E : NormalizedBinaryCarrier.State (coordinateProfile a b c)) :
    Disjoint (denormalizeState eU eV eW D)
        (denormalizeState eU eV eW E) ↔ Disjoint D E := by
  exact Finset.disjoint_map (carrierEquiv eU eV eW).toEmbedding

/-- A basis obtained by transporting the standard function basis. -/
noncomputable def basisOfCoordinates
    {U : Type u} [AddCommGroup U] [Module F2 U] {a : ℕ}
    (e : Coord a ≃ₗ[F2] U) : Module.Basis (Fin a) F2 U :=
  (Pi.basisFun F2 (Fin a)).map e

/-- Coordinates in the transported basis are exactly the inverse images
under the supplied linear equivalence. -/
@[simp] theorem basisOfCoordinates_equivFun
    {U : Type u} [AddCommGroup U] [Module F2 U] {a : ℕ}
    (e : Coord a ≃ₗ[F2] U) (u : U) :
    (basisOfCoordinates e).equivFun u = e.symm u := by
  ext i
  simp [basisOfCoordinates]

/-- Basis coordinates identify a nested abstract tensor product with the
coordinate tensor representation used by the normalized compiler. -/
noncomputable def tensorCoordinateEquiv
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    {a b c : ℕ}
    (bU : Module.Basis (Fin a) F2 U)
    (bV : Module.Basis (Fin b) F2 V)
    (bW : Module.Basis (Fin c) F2 W) :
    U ⊗[F2] (V ⊗[F2] W) ≃ₗ[F2]
      Tensor F2 a b c :=
  ((bU.tensorProduct (bV.tensorProduct bW)).equivFun).trans
    ((LinearEquiv.curry F2 F2 (Fin a) (Fin b × Fin c)).trans
      (LinearEquiv.piCongrRight fun _ : Fin a =>
        LinearEquiv.curry F2 F2 (Fin b) (Fin c)))

/-- The transported tensor-coordinate equivalence evaluates a nested pure
tensor entrywise as the product of its three basis coordinates. -/
@[simp] theorem tensorCoordinateEquiv_tmul_apply
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    {a b c : ℕ}
    (bU : Module.Basis (Fin a) F2 U)
    (bV : Module.Basis (Fin b) F2 V)
    (bW : Module.Basis (Fin c) F2 W)
    (u : U) (v : V) (w : W) (i : Fin a) (j : Fin b) (k : Fin c) :
    tensorCoordinateEquiv bU bV bW (u ⊗ₜ (v ⊗ₜ w)) i j k =
      bU.equivFun u i * bV.equivFun v j * bW.equivFun w k := by
  simp [tensorCoordinateEquiv,
    Module.Basis.tensorProduct_repr_tmul_apply, mul_comm, mul_assoc]

/-- Pure tensors become the project's coordinate `triad` under supplied
factor-coordinate equivalences. -/
@[simp] theorem tensorCoordinateEquiv_tmul
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    {a b c : ℕ}
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W)
    (u : U) (v : V) (w : W) :
    tensorCoordinateEquiv (basisOfCoordinates eU) (basisOfCoordinates eV)
        (basisOfCoordinates eW) (u ⊗ₜ (v ⊗ₜ w)) =
      triad (eU.symm u) (eV.symm v) (eW.symm w) := by
  funext i j k
  rw [tensorCoordinateEquiv_tmul_apply]
  simp only [basisOfCoordinates_equivFun, triad]

/-- Coordinate tensor evaluation of an ambient term agrees with normalized
carrier evaluation. -/
@[simp] theorem tensorCoordinateEquiv_tensorEvaluation
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    {a b c : ℕ}
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W)
    (t : BinaryAmbientCarrier.Carrier U V W) :
    tensorCoordinateEquiv (basisOfCoordinates eU) (basisOfCoordinates eV)
        (basisOfCoordinates eW) (BinaryAmbientCarrier.tensorEvaluation t) =
      NormalizedBinaryCarrier.tensorEvaluation (normalizeTerm eU eV eW t) := by
  apply tensorCoordinateEquiv_tmul

/-- Coordinate conversion commutes with finite-state tensor evaluation. -/
@[simp] theorem tensorCoordinateEquiv_stateEvaluation
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    {a b c : ℕ}
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W)
    (D : BinaryAmbientCarrier.State U V W) :
    tensorCoordinateEquiv (basisOfCoordinates eU) (basisOfCoordinates eV)
        (basisOfCoordinates eW) (BinaryAmbientCarrier.stateEvaluation D) =
      NormalizedBinaryCarrier.stateEvaluation (normalizeState eU eV eW D) := by
  rw [BinaryAmbientCarrier.stateEvaluation,
    NormalizedBinaryCarrier.stateEvaluation_eq_sum, map_sum]
  unfold normalizeState
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro t _ht
  exact tensorCoordinateEquiv_tensorEvaluation eU eV eW t

/-- Normalized finite-state evaluation equality is equivalent to the original
ambient tensor equality. -/
theorem normalized_stateEvaluation_eq_iff
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    {a b c : ℕ}
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W)
    (D E : BinaryAmbientCarrier.State U V W) :
    NormalizedBinaryCarrier.stateEvaluation (normalizeState eU eV eW D) =
        NormalizedBinaryCarrier.stateEvaluation (normalizeState eU eV eW E) ↔
      BinaryAmbientCarrier.stateEvaluation D =
        BinaryAmbientCarrier.stateEvaluation E := by
  rw [← tensorCoordinateEquiv_stateEvaluation eU eV eW D,
    ← tensorCoordinateEquiv_stateEvaluation eU eV eW E]
  exact (tensorCoordinateEquiv (basisOfCoordinates eU)
    (basisOfCoordinates eV) (basisOfCoordinates eW)).injective.eq_iff

/-- A noncomputable coordinate equivalence onto a finite-dimensional exact
span.  This is proof infrastructure, not executable compiler input. -/
noncomputable def exactSpanCoordinates
    {U : Type u} [AddCommGroup U] [Module F2 U] [FiniteDimensional F2 U]
    (P : Submodule F2 U) :
    Coord (Module.finrank F2 P) ≃ₗ[F2] P :=
  (Module.finBasis F2 P).equivFun.symm

section ExactSpanReflection

variable {U : Type u} {V : Type v} {W : Type w}
  [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
  [Module F2 U] [Module F2 V] [Module F2 W]

/-- Inclusion of three exact spans, nested in the tensor convention used here. -/
def exactSpanTensorMap
    (PU : Submodule F2 U) (PV : Submodule F2 V) (PW : Submodule F2 W) :
    PU ⊗[F2] (PV ⊗[F2] PW) →ₗ[F2] U ⊗[F2] (V ⊗[F2] W) :=
  TensorProduct.map PU.subtype (TensorProduct.map PV.subtype PW.subtype)

/-- A proof-side left inverse to exact-span tensor inclusion. -/
noncomputable def exactSpanTensorLeftInverse
    (PU : Submodule F2 U) (PV : Submodule F2 V) (PW : Submodule F2 W) :
    U ⊗[F2] (V ⊗[F2] W) →ₗ[F2] PU ⊗[F2] (PV ⊗[F2] PW) :=
  TensorProduct.map PU.subtype.leftInverse
    (TensorProduct.map PV.subtype.leftInverse PW.subtype.leftInverse)

private theorem subtype_leftInverse_apply
    {X : Type*} [AddCommGroup X] [Module F2 X]
    (P : Submodule F2 X) (x : P) :
    P.subtype.leftInverse (P.subtype x) = x := by
  apply LinearMap.leftInverse_apply_of_inj
  exact LinearMap.ker_eq_bot.mpr Subtype.val_injective

private theorem inner_exactSpan_leftInverse_apply
    (PV : Submodule F2 V) (PW : Submodule F2 W)
    (x : PV ⊗[F2] PW) :
    TensorProduct.map PV.subtype.leftInverse PW.subtype.leftInverse
        (TensorProduct.map PV.subtype PW.subtype x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v w =>
      simp only [TensorProduct.map_tmul]
      rw [subtype_leftInverse_apply, subtype_leftInverse_apply]
  | add x y hx hy => simp [hx, hy]

/-- The constructed map is genuinely a left inverse on every exact-span tensor. -/
@[simp] theorem exactSpanTensorLeftInverse_apply
    (PU : Submodule F2 U) (PV : Submodule F2 V) (PW : Submodule F2 W)
    (x : PU ⊗[F2] (PV ⊗[F2] PW)) :
    exactSpanTensorLeftInverse PU PV PW (exactSpanTensorMap PU PV PW x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp [exactSpanTensorLeftInverse, exactSpanTensorMap]
  | tmul u x =>
      simp only [exactSpanTensorLeftInverse, exactSpanTensorMap,
        TensorProduct.map_tmul]
      rw [subtype_leftInverse_apply, inner_exactSpan_leftInverse_apply]
  | add x y hx hy => simp [hx, hy]

/-- Tensor inclusion from three exact spans is injective. -/
theorem exactSpanTensorMap_injective
    (PU : Submodule F2 U) (PV : Submodule F2 V) (PW : Submodule F2 W) :
    Function.Injective (exactSpanTensorMap PU PV PW) := by
  intro x y hxy
  rw [← exactSpanTensorLeftInverse_apply PU PV PW x,
    ← exactSpanTensorLeftInverse_apply PU PV PW y, hxy]

/-- Equality after inclusion into the original ambient tensor product reflects
exactly to equality in the tensor product of exact spans. -/
theorem exactSpanTensorMap_eq_iff
    (PU : Submodule F2 U) (PV : Submodule F2 V) (PW : Submodule F2 W)
    (x y : PU ⊗[F2] (PV ⊗[F2] PW)) :
    exactSpanTensorMap PU PV PW x = exactSpanTensorMap PU PV PW y ↔ x = y :=
  (exactSpanTensorMap_injective PU PV PW).eq_iff

end ExactSpanReflection

end BilinearComplexity.BinaryAmbientTensorCoordinates
