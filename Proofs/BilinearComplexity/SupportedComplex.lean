import BilinearComplexity.SchemeGauge

set_option autoImplicit false

/-!
# Supported three-term deformation complexes

This module packages a caller-supplied linear map certified to land in the scheme Jacobian
kernel, pulls it back to an arbitrary submodule of allowed variations, and restricts the
Jacobian to that scope. For compatibility with the established gauge API, the structure and
some maps retain infinitesimal-action terminology; that terminology does not assert that an
action, orbit map, or differentiation procedure is encoded. The construction is linear and
makes no claim that kernel vectors integrate or extend to higher-order deformations.
-/

namespace BilinearComplexity
namespace Scheme
namespace Deformation

variable {k : Type*} {a b c r : ℕ}

/-- A caller-supplied linear map with a certificate that its range lies in the scheme
Jacobian kernel. The name supports the intended gauge examples, but this structure encodes no
action, orbit map, provenance from differentiation, or integrability assertion. -/
structure InfinitesimalAction [CommRing k] (S : Scheme k a b c r)
    (H : Type*) [AddCommGroup H] [Module k H] where
  /-- The certified linear map; the field name does not by itself certify differentiation. -/
  derivative : H →ₗ[k] Variation k a b c r
  /-- Every vector in the linear map's range is killed by the Jacobian. -/
  range_le_ker : LinearMap.range derivative ≤ LinearMap.ker (jacobian S)

namespace InfinitesimalAction

variable {H : Type*} [CommRing k] [AddCommGroup H] [Module k H]
variable {S : Scheme k a b c r}

/-- The Jacobian kills every direction produced by the certified linear map. -/
@[simp] theorem jacobian_derivative (A : InfinitesimalAction S H) (x : H) :
    jacobian S (A.derivative x) = 0 := by
  exact A.range_le_ker ⟨x, rfl⟩

/-- The ambient Jacobian composed with the certified linear map is the zero map. -/
theorem jacobian_comp_derivative (A : InfinitesimalAction S H) :
    (jacobian S).comp A.derivative = 0 := by
  apply LinearMap.ext
  intro x
  change jacobian S (A.derivative x) = 0
  exact A.jacobian_derivative x

/-- Package any caller-supplied linear map with a pointwise Jacobian-kernel proof.
This constructor supplies no evidence that the map arises by differentiating an action. -/
def ofLinearMap (d : H →ₗ[k] Variation k a b c r)
    (hd : ∀ x, jacobian S (d x) = 0) : InfinitesimalAction S H where
  derivative := d
  range_le_ker := by
    rintro _ ⟨x, rfl⟩
    exact hd x

/-- The package built from a certified linear map retains exactly that map. -/
@[simp] theorem ofLinearMap_derivative (d : H →ₗ[k] Variation k a b c r)
    (hd : ∀ x, jacobian S (d x) = 0) :
    (ofLinearMap d hd).derivative = d := rfl

/-- The certified package whose linear map is zero. -/
def zero (S : Scheme k a b c r) (H : Type*) [AddCommGroup H] [Module k H] :
    InfinitesimalAction S H where
  derivative := 0
  range_le_ker := by
    rintro _ ⟨x, rfl⟩
    change jacobian S (0 : Variation k a b c r) = 0
    exact LinearMap.map_zero (jacobian S)

/-- The linear map in the zero package is zero. -/
@[simp] theorem zero_derivative (S : Scheme k a b c r) (H : Type*)
    [AddCommGroup H] [Module k H] : (zero S H).derivative = 0 := rfl

/-- Termwise product-one scaling parameters give a certified kernel map for every scheme. -/
def termScaling (S : Scheme k a b c r) :
    InfinitesimalAction S (Fin r → k × k) :=
  ofLinearMap (termScalingDerivative S) (jacobian_termScalingDerivative S)

/-- The term-scaling package uses the existing term-scaling derivative. -/
@[simp] theorem termScaling_derivative (S : Scheme k a b c r) :
    (termScaling S).derivative = termScalingDerivative S := rfl

/-- At a Brent scheme, package the existing combined term-scaling and sandwich derivative. -/
def gauge {n₁ n₂ n₃ : ℕ} (S : MatrixScheme k n₁ n₂ n₃ r) (hS : S.Brent) :
    InfinitesimalAction S (GaugeParameters k n₁ n₂ n₃ r) :=
  ofLinearMap (gaugeDerivative S) (gaugeDerivative_mem_ker S hS)

/-- The Brent gauge package uses the existing combined gauge derivative. -/
@[simp] theorem gauge_derivative {n₁ n₂ n₃ : ℕ}
    (S : MatrixScheme k n₁ n₂ n₃ r) (hS : S.Brent) :
    (gauge S hS).derivative = gaugeDerivative S := rfl

end InfinitesimalAction

/-- A supported three-term complex is a certified Jacobian-kernel map together with an
arbitrary submodule of variations in which deformations are allowed. -/
structure SupportedComplex {H : Type*} [CommRing k] [AddCommGroup H] [Module k H]
    {S : Scheme k a b c r} (A : InfinitesimalAction S H) where
  /-- The allowed variation scope. -/
  scope : Submodule k (Variation k a b c r)

namespace SupportedComplex

variable {H : Type*} [CommRing k] [AddCommGroup H] [Module k H]
variable {S : Scheme k a b c r} {A : InfinitesimalAction S H}

/-- The parameters whose images under the certified map lie in the selected scope. -/
def supportedParameters (C : SupportedComplex A) : Submodule k H :=
  C.scope.comap A.derivative

/-- A parameter is supported exactly when its image under the certified map lies in scope. -/
@[simp] theorem mem_supportedParameters_iff (C : SupportedComplex A) (x : H) :
    x ∈ C.supportedParameters ↔ A.derivative x ∈ C.scope :=
  Submodule.mem_comap

/-- The certified linear map restricted from supported parameters to scoped variations.
The declaration name is retained for API compatibility and does not encode an action. -/
def supportedAction (C : SupportedComplex A) :
    C.supportedParameters →ₗ[k] C.scope where
  toFun x := ⟨A.derivative x.1, x.2⟩
  map_add' x y := by
    apply Subtype.ext
    exact A.derivative.map_add x.1 y.1
  map_smul' t x := by
    apply Subtype.ext
    exact A.derivative.map_smul t x.1

/-- Forgetting support from the restricted map recovers the certified linear map. -/
@[simp] theorem coe_supportedAction (C : SupportedComplex A)
    (x : C.supportedParameters) :
    (C.supportedAction x : Variation k a b c r) = A.derivative x.1 := rfl

/-- The Jacobian restricted to the selected variation scope. -/
def restrictedJacobian (C : SupportedComplex A) :
    C.scope →ₗ[k] Tensor k a b c :=
  (jacobian S).comp C.scope.subtype

/-- The restricted Jacobian is the ambient Jacobian on the underlying variation. -/
@[simp] theorem restrictedJacobian_apply (C : SupportedComplex A) (d : C.scope) :
    C.restrictedJacobian d = jacobian S d.1 := rfl

/-- The two differentials of the supported three-term complex compose to zero. -/
theorem restrictedJacobian_comp_supportedAction (C : SupportedComplex A) :
    C.restrictedJacobian.comp C.supportedAction = 0 := by
  apply LinearMap.ext
  intro x
  change jacobian S (A.derivative x.1) = 0
  exact A.jacobian_derivative x.1

/-- The parameter kernel of the restricted certified map. The traditional name `stabilizer`
is purely linear-algebraic here and does not assert an encoded group action or group stabilizer. -/
def stabilizer (C : SupportedComplex A) : Submodule k C.supportedParameters :=
  LinearMap.ker C.supportedAction

/-- Membership in the algebraic parameter kernel is exactly vanishing of the restricted map. -/
@[simp] theorem mem_stabilizer_iff (C : SupportedComplex A)
    (x : C.supportedParameters) :
    x ∈ C.stabilizer ↔ C.supportedAction x = 0 :=
  LinearMap.mem_ker

/-- The scoped cycles are the kernel of the restricted Jacobian. -/
def cycles (C : SupportedComplex A) : Submodule k C.scope :=
  LinearMap.ker C.restrictedJacobian

/-- Cycle membership is exactly vanishing under the restricted Jacobian. -/
@[simp] theorem mem_cycles_iff (C : SupportedComplex A) (d : C.scope) :
    d ∈ C.cycles ↔ C.restrictedJacobian d = 0 :=
  LinearMap.mem_ker

/-- The restricted certified map with codomain narrowed to scoped Jacobian cycles. -/
def actionInCycles (C : SupportedComplex A) :
    C.supportedParameters →ₗ[k] C.cycles :=
  LinearMap.codRestrict C.cycles C.supportedAction (fun x => by
    rw [mem_cycles_iff]
    exact A.jacobian_derivative x.1)

/-- Forgetting the cycle certificate recovers the restricted certified map. -/
@[simp] theorem coe_actionInCycles (C : SupportedComplex A)
    (x : C.supportedParameters) :
    (C.actionInCycles x : C.scope) = C.supportedAction x := rfl

/-- Images of the restricted certified map inside the scoped Jacobian cycles. -/
def boundaries (C : SupportedComplex A) : Submodule k C.cycles :=
  LinearMap.range C.actionInCycles

/-- A cycle is a boundary exactly when represented by a supported source parameter. -/
@[simp] theorem mem_boundaries_iff (C : SupportedComplex A) (d : C.cycles) :
    d ∈ C.boundaries ↔ ∃ x, C.actionInCycles x = d :=
  LinearMap.mem_range

/-- The normal module is the scoped Jacobian kernel modulo the certified map's image. -/
abbrev Normal (C : SupportedComplex A) :=
  ↥C.cycles ⧸ C.boundaries.toAddSubgroup

/-- Scalar multiplication on the normal module descends from scalar multiplication on cycles. -/
instance normalSMul (C : SupportedComplex A) : SMul k C.Normal where
  smul t := Quotient.map' (t • ·) (by
    intro x y hxy
    rw [QuotientAddGroup.leftRel_apply] at hxy ⊢
    change -(t • x) + t • y ∈ C.boundaries
    simpa only [smul_neg, smul_add] using C.boundaries.smul_mem t hxy)

/-- The normal quotient carries the module structure descended from the cycle module. -/
instance normalModule (C : SupportedComplex A) : Module k C.Normal := by
  let q : C.cycles →+ C.Normal :=
    { toFun := fun d => Quotient.mk'' d
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hq : Function.Surjective q := by
    intro z
    refine Quotient.inductionOn' z ?_
    intro d
    exact ⟨d, rfl⟩
  exact Function.Surjective.module k q hq (fun _ _ => rfl)

/-- The residual module is the target tensor module modulo the restricted Jacobian image. -/
abbrev Residual (C : SupportedComplex A) :=
  Tensor k a b c ⧸ LinearMap.range C.restrictedJacobian

/-- Send a scoped cycle to its normal class. -/
def normalClass (C : SupportedComplex A) : C.cycles →ₗ[k] C.Normal where
  toFun := fun d => Quotient.mk'' d
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

/-- A normal class is represented by the supplied scoped cycle. -/
@[simp] theorem normalClass_apply (C : SupportedComplex A) (d : C.cycles) :
    C.normalClass d = Quotient.mk'' d := rfl

/-- Send a target tensor to its residual class modulo the scoped Jacobian image. -/
def residualClass (C : SupportedComplex A) : Tensor k a b c →ₗ[k] C.Residual :=
  (LinearMap.range C.restrictedJacobian).mkQ

/-- A tensor has zero residual class exactly when it lies in the restricted Jacobian image. -/
@[simp] theorem residualClass_eq_zero_iff (C : SupportedComplex A)
    (t : Tensor k a b c) :
    C.residualClass t = 0 ↔ t ∈ LinearMap.range C.restrictedJacobian :=
  Submodule.Quotient.mk_eq_zero _

/-- Inclusion of supported parameters induced by an inclusion of variation scopes. -/
def supportedParametersInclusion {C D : SupportedComplex A} (h : C.scope ≤ D.scope) :
    C.supportedParameters →ₗ[k] D.supportedParameters :=
  Submodule.inclusion (fun _x hx => h hx)

/-- Inclusion of variation scopes. -/
def scopeInclusion {C D : SupportedComplex A} (h : C.scope ≤ D.scope) :
    C.scope →ₗ[k] D.scope :=
  Submodule.inclusion h

/-- Supported parameter spaces are monotone under inclusion of variation scopes. -/
theorem supportedParameters_mono {C D : SupportedComplex A} (h : C.scope ≤ D.scope) :
    C.supportedParameters ≤ D.supportedParameters := by
  intro x hx
  exact h hx

/-- Restriction of the certified map commutes with inclusion of variation scopes. -/
theorem supportedAction_natural {C D : SupportedComplex A} (h : C.scope ≤ D.scope)
    (x : C.supportedParameters) :
    D.supportedAction (supportedParametersInclusion h x) =
      scopeInclusion h (C.supportedAction x) := rfl

/-- Restricting the Jacobian commutes with inclusion of variation scopes. -/
theorem restrictedJacobian_natural {C D : SupportedComplex A} (h : C.scope ≤ D.scope)
    (d : C.scope) :
    D.restrictedJacobian (scopeInclusion h d) = C.restrictedJacobian d := rfl

/-- A scope inclusion sends vectors in the algebraic parameter kernel to such vectors. -/
def stabilizerMap {C D : SupportedComplex A} (h : C.scope ≤ D.scope) :
    C.stabilizer →ₗ[k] D.stabilizer :=
  LinearMap.codRestrict D.stabilizer
    ((supportedParametersInclusion h).comp C.stabilizer.subtype) (fun x => by
      rw [mem_stabilizer_iff]
      change D.supportedAction (supportedParametersInclusion h x.1) = 0
      rw [supportedAction_natural h]
      have hx : C.supportedAction x.1 = 0 := (mem_stabilizer_iff C x.1).mp x.2
      rw [hx, map_zero])

/-- A scope inclusion sends restricted Jacobian cycles to restricted Jacobian cycles. -/
def cyclesMap {C D : SupportedComplex A} (h : C.scope ≤ D.scope) :
    C.cycles →ₗ[k] D.cycles :=
  LinearMap.codRestrict D.cycles
    ((scopeInclusion h).comp C.cycles.subtype) (fun d => by
      rw [mem_cycles_iff]
      change D.restrictedJacobian (scopeInclusion h d.1) = 0
      rw [restrictedJacobian_natural h]
      exact (mem_cycles_iff C d.1).mp d.2)

/-- The algebraic parameter-kernel map for the identity scope inclusion is the identity. -/
@[simp] theorem stabilizerMap_id (C : SupportedComplex A) :
    stabilizerMap (le_refl C.scope) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rfl

/-- The cycle map for the identity scope inclusion is the identity. -/
@[simp] theorem cyclesMap_id (C : SupportedComplex A) :
    cyclesMap (le_refl C.scope) = LinearMap.id := by
  apply LinearMap.ext
  intro d
  apply Subtype.ext
  rfl

/-- Algebraic parameter-kernel maps compose along nested scope inclusions. -/
theorem stabilizerMap_comp {C D E : SupportedComplex A}
    (hCD : C.scope ≤ D.scope) (hDE : D.scope ≤ E.scope) :
    stabilizerMap (hCD.trans hDE) = (stabilizerMap hDE).comp (stabilizerMap hCD) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rfl

/-- Cycle maps compose along nested scope inclusions. -/
theorem cyclesMap_comp {C D E : SupportedComplex A}
    (hCD : C.scope ≤ D.scope) (hDE : D.scope ≤ E.scope) :
    cyclesMap (hCD.trans hDE) = (cyclesMap hDE).comp (cyclesMap hCD) := by
  apply LinearMap.ext
  intro d
  apply Subtype.ext
  rfl

/-- The cycle map carries images of the certified map into such images. -/
theorem cyclesMap_range_le {C D : SupportedComplex A} (h : C.scope ≤ D.scope) :
    C.boundaries ≤ D.boundaries.comap (cyclesMap h) := by
  rintro _ ⟨x, rfl⟩
  refine ⟨supportedParametersInclusion h x, ?_⟩
  apply Subtype.ext
  rfl

/-- Inclusion of scopes induces the covariant map on normal modules. -/
def normalMap {C D : SupportedComplex A} (h : C.scope ≤ D.scope) :
    C.Normal →ₗ[k] D.Normal where
  toFun := Quotient.map' (cyclesMap h) (by
    intro x y hxy
    rw [QuotientAddGroup.leftRel_apply] at hxy ⊢
    change -(cyclesMap h x) + cyclesMap h y ∈ D.boundaries
    have himage := cyclesMap_range_le h hxy
    change cyclesMap h (-x + y) ∈ D.boundaries at himage
    rw [(cyclesMap h).map_add] at himage
    have hnegmap : cyclesMap h (-x) = -(cyclesMap h x) := by
      apply Subtype.ext
      rfl
    rw [hnegmap] at himage
    exact himage)
  map_add' x y := by
    refine Quotient.inductionOn₂' x y ?_
    intro d e
    rfl
  map_smul' t x := by
    refine Quotient.inductionOn' x ?_
    intro d
    rfl

/-- The normal map sends a represented cycle to the class of its included cycle. -/
@[simp] theorem normalMap_normalClass {C D : SupportedComplex A}
    (h : C.scope ≤ D.scope) (d : C.cycles) :
    normalMap h (C.normalClass d) = D.normalClass (cyclesMap h d) := rfl

/-- The normal map for the identity scope inclusion is the identity. -/
@[simp] theorem normalMap_id (C : SupportedComplex A) :
    normalMap (le_refl C.scope) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  refine Quotient.inductionOn' z ?_
  intro d
  change normalMap (le_refl C.scope) (C.normalClass d) = C.normalClass d
  rw [normalMap_normalClass]
  congr 1

/-- Normal maps compose along nested scope inclusions. -/
theorem normalMap_comp {C D E : SupportedComplex A}
    (hCD : C.scope ≤ D.scope) (hDE : D.scope ≤ E.scope) :
    normalMap (hCD.trans hDE) = (normalMap hDE).comp (normalMap hCD) := by
  apply LinearMap.ext
  intro z
  refine Quotient.inductionOn' z ?_
  intro d
  change normalMap (hCD.trans hDE) (C.normalClass d) =
    normalMap hDE (normalMap hCD (C.normalClass d))
  rw [normalMap_normalClass, normalMap_normalClass, normalMap_normalClass]
  congr 1

/-- Enlarging a scope enlarges the restricted Jacobian range. -/
theorem restrictedJacobian_range_mono {C D : SupportedComplex A}
    (h : C.scope ≤ D.scope) :
    LinearMap.range C.restrictedJacobian ≤ LinearMap.range D.restrictedJacobian := by
  rintro _ ⟨d, rfl⟩
  exact ⟨scopeInclusion h d, (restrictedJacobian_natural h d).symm⟩

/-- Inclusion of scopes induces the covariant map on residual modules. -/
def residualMap {C D : SupportedComplex A} (h : C.scope ≤ D.scope) :
    C.Residual →ₗ[k] D.Residual :=
  (LinearMap.range C.restrictedJacobian).mapQ
    (LinearMap.range D.restrictedJacobian) LinearMap.id (by
      intro t ht
      exact restrictedJacobian_range_mono h ht)

/-- The residual map sends a represented tensor to the same tensor in the larger quotient. -/
@[simp] theorem residualMap_residualClass {C D : SupportedComplex A}
    (h : C.scope ≤ D.scope) (t : Tensor k a b c) :
    residualMap h (C.residualClass t) = D.residualClass t := by
  exact Submodule.mapQ_apply _ _ _ t

/-- The residual map for the identity scope inclusion is the identity. -/
@[simp] theorem residualMap_id (C : SupportedComplex A) :
    residualMap (le_refl C.scope) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  refine Quotient.inductionOn' z ?_
  intro t
  change residualMap (le_refl C.scope) (C.residualClass t) = C.residualClass t
  rw [residualMap_residualClass]

/-- Residual maps compose along nested scope inclusions. -/
theorem residualMap_comp {C D E : SupportedComplex A}
    (hCD : C.scope ≤ D.scope) (hDE : D.scope ≤ E.scope) :
    residualMap (hCD.trans hDE) = (residualMap hDE).comp (residualMap hCD) := by
  apply LinearMap.ext
  intro z
  refine Quotient.inductionOn' z ?_
  intro t
  change residualMap (hCD.trans hDE) (C.residualClass t) =
    residualMap hDE (residualMap hCD (C.residualClass t))
  rw [residualMap_residualClass, residualMap_residualClass, residualMap_residualClass]

/-- Build the supported complex associated with an existing coordinate mask. -/
def ofMask (A : InfinitesimalAction S H) (M : VariationMask a b c r) :
    SupportedComplex A where
  scope := M.allowed

/-- The scope of the mask-supported complex is the existing allowed-variation submodule. -/
@[simp] theorem ofMask_scope (A : InfinitesimalAction S H)
    (M : VariationMask a b c r) :
    (ofMask A M).scope = M.allowed := rfl

/-- The generic restricted Jacobian specializes to the existing mask-restricted Jacobian. -/
theorem ofMask_restrictedJacobian (A : InfinitesimalAction S H)
    (M : VariationMask a b c r) :
    (ofMask A M).restrictedJacobian = M.restrictedJacobian S := rfl

/-- The generic scoped cycles specialize to the existing restricted kernel. -/
theorem ofMask_cycles (A : InfinitesimalAction S H) (M : VariationMask a b c r) :
    (ofMask A M).cycles = restrictedKernel S M := rfl

/-- The generic residual module specializes to the existing restricted Jacobian cokernel. -/
theorem ofMask_residual (A : InfinitesimalAction S H) (M : VariationMask a b c r) :
    (ofMask A M).Residual = RestrictedJacobianCokernel S M := rfl

/-- For the packaged Brent gauge derivative, generic boundaries are the existing restricted gauge. -/
theorem gauge_ofMask_boundaries {n₁ n₂ n₃ : ℕ}
    (S : MatrixScheme k n₁ n₂ n₃ r) (hS : S.Brent)
    (M : VariationMask (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) r) :
    (ofMask (InfinitesimalAction.gauge S hS) M).boundaries = restrictedGauge S M := by
  ext d
  constructor
  · rintro ⟨x, hx⟩
    change M.inclusion d.1 ∈ gaugeSpace S
    refine ⟨x.1, ?_⟩
    have hvalue := congrArg
      (fun e => ((e : (ofMask (InfinitesimalAction.gauge S hS) M).cycles).1.1 :
        Variation k (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) r)) hx
    exact hvalue
  · intro hd
    change M.inclusion d.1 ∈ gaugeSpace S at hd
    rcases hd with ⟨x, hx⟩
    have hsupp : gaugeDerivative S x ∈ M.allowed := by
      rw [hx]
      exact d.1.2
    let supported : (ofMask (InfinitesimalAction.gauge S hS) M).supportedParameters :=
      ⟨x, hsupp⟩
    refine ⟨supported, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hx

/-- A concrete nonempty complex jointly instantiates the certified map, scope, and chain law. -/
example :
    let S : Scheme (ZMod 2) 1 1 1 1 := ⟨fun _ => (![1], ![1], ![1])⟩
    let A := InfinitesimalAction.zero S (ZMod 2)
    let C : SupportedComplex A := ⟨⊤⟩
    C.restrictedJacobian.comp C.supportedAction = 0 := by
  exact restrictedJacobian_comp_supportedAction _

/-- The concrete normal quotient has the descended module structure. -/
example :
    let S : Scheme (ZMod 2) 1 1 1 1 := ⟨fun _ => (![1], ![1], ![1])⟩
    let A := InfinitesimalAction.zero S (ZMod 2)
    let C : SupportedComplex A := ⟨⊤⟩
    Module (ZMod 2) C.Normal := by
  exact normalModule _

/-- The concrete residual quotient has the standard quotient-module structure. -/
example :
    let S : Scheme (ZMod 2) 1 1 1 1 := ⟨fun _ => (![1], ![1], ![1])⟩
    let A := InfinitesimalAction.zero S (ZMod 2)
    let C : SupportedComplex A := ⟨⊤⟩
    Module (ZMod 2) C.Residual := by
  infer_instance

end SupportedComplex

end Deformation
end Scheme
end BilinearComplexity
