import BilinearComplexity.SchemeAction
import BilinearComplexity.SchemeReplacement
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.LinearCombination

/-!
# Paired-circuit five-term deformation

This module formalizes a sufficient normalized five-term construction. It deliberately does not
classify paired circuits, encode the remaining 44 terms of the cited length-49 presentation, claim
that length 49 is minimal tensor rank, or make a Jacobian/derivative rank census. The factor-matroid
circuits below are not derivative circuits. No integrability, global-rigidity, or nontrivial binary
endpoint claim is made; indeed the binary torus is proved to contain only its origin.
-/

set_option autoImplicit false

namespace BilinearComplexity
namespace Scheme
namespace PairedCircuit

variable {k : Type*} {a b c r n : ℕ}

/-- In characteristic two, the multiplicative torus equation is exactly the normalized
quadratic cancellation equation. -/
theorem torus_iff_scalarCancellation [CommRing k] [CharP k 2] (s t : k) :
    (1 + s) * (1 + t) = 1 ↔ s + t + s * t = 0 := by
  constructor
  · intro h
    ring_nf at h ⊢
    linear_combination h
  · intro h
    ring_nf at h ⊢
    linear_combination h

/-- Equal module coefficients cancel whenever their three scalar weights sum to zero. -/
theorem additiveCancellation [CommRing k] {M : Type*} [AddCommGroup M] [Module k M]
    (A B C : M) (s t : k) (hB : B = A) (hC : C = A)
    (hscalar : s + t + s * t = 0) :
    s • A + t • B + (s * t) • C = 0 := by
  rw [hB, hC, ← add_smul, ← add_smul, hscalar, zero_smul]

/-- An explicit unit `b = 1 + t` gives the unique characteristic-two solution
`s = t * b⁻¹` of the torus equation. -/
theorem eq_mul_inv_iff [CommRing k] [CharP k 2] (s t : k) (unit : kˣ)
    (hunit : (unit : k) = 1 + t) :
    (1 + s) * (1 + t) = 1 ↔ s = t * (unit⁻¹ : kˣ) := by
  let x : k := (unit⁻¹ : kˣ)
  have htxSub : t * x = 1 - x := by
    apply (eq_sub_iff_add_eq).2
    calc
      t * x + x = (1 + t) * x := by ring
      _ = (unit : k) * (unit⁻¹ : kˣ) := by rw [hunit]
      _ = 1 := by simp
  have htx : t * x = x - 1 := by
    calc
      t * x = 1 - x := htxSub
      _ = 1 + x := by rw [sub_eq_add_neg, CharTwo.neg_eq]
      _ = x + 1 := add_comm 1 x
      _ = x - 1 := by rw [sub_eq_add_neg, CharTwo.neg_eq]
  constructor
  · intro h
    have hsOne : 1 + s = x := by
      calc
        1 + s = (1 + s) * 1 := by rw [mul_one]
        _ = (1 + s) * ((unit : k) * (unit⁻¹ : kˣ)) := by simp
        _ = ((1 + s) * (1 + t)) * x := by rw [hunit, mul_assoc]
        _ = x := by rw [h, one_mul]
    change s = t * x
    calc
      s = (1 + s) - 1 := by ring
      _ = x - 1 := by rw [hsOne]
      _ = t * x := htx.symm
  · intro hs
    change s = t * x at hs
    have hsOne : 1 + s = x := by
      rw [hs, htx]
      ring
    calc
      (1 + s) * (1 + t) = x * (unit : k) := by rw [hsOne, hunit]
      _ = 1 := by
        dsimp only [x]
        simp

/-- Over a field, if `1+t` is nonzero then the torus equation is equivalent to the canonical
formula `s=t*(1+t)⁻¹`. -/
theorem eq_field_inv_iff [Field k] [CharP k 2] (s t : k) (ht : 1 + t ≠ 0) :
    (1 + s) * (1 + t) = 1 ↔ s = t * (1 + t)⁻¹ := by
  simpa [Units.mk0] using
    (eq_mul_inv_iff s t (Units.mk0 (1 + t) ht) rfl)

/-- If `1 + t` is a unit, its chosen inverse gives exactly the unique solution of the
characteristic-two torus equation. -/
theorem eq_isUnit_inv_iff [CommRing k] [CharP k 2] (s t : k)
    (ht : IsUnit (1 + t)) :
    (1 + s) * (1 + t) = 1 ↔ s = t * (ht.unit⁻¹ : kˣ) :=
  eq_mul_inv_iff s t ht.unit ht.unit_spec

/-- If `1 + t` is a unit, the characteristic-two torus equation has the displayed unique
solution. -/
theorem existsUnique_solution [CommRing k] [CharP k 2] (t : k)
    (ht : IsUnit (1 + t)) :
    ∃! s : k, (1 + s) * (1 + t) = 1 := by
  refine ⟨t * (ht.unit⁻¹ : kˣ), ?_, ?_⟩
  · exact (eq_mul_inv_iff _ _ ht.unit ht.unit_spec).mpr rfl
  · intro s hs
    exact (eq_mul_inv_iff s t ht.unit ht.unit_spec).mp hs

/-- Solutions of `(1+s)(1+t)=1` over a commutative ring are equivalent to units, with
`b = 1+t` and `1+s = b⁻¹`. -/
def solutionEquivUnits [CommRing k] :
    {p : k × k // (1 + p.1) * (1 + p.2) = 1} ≃ kˣ where
  toFun p :=
    { val := 1 + p.1.2
      inv := 1 + p.1.1
      val_inv := by simpa only [mul_comm] using p.2
      inv_val := p.2 }
  invFun unit :=
    ⟨((unit⁻¹ : kˣ) - 1, (unit : k) - 1), by simp⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> simp
  right_inv unit := by
    apply Units.ext
    simp

/-- Under `solutionEquivUnits`, the unit value is `b = 1+t`. -/
@[simp] theorem solutionEquivUnits_apply_val [CommRing k]
    (p : {p : k × k // (1 + p.1) * (1 + p.2) = 1}) :
    ((solutionEquivUnits p : kˣ) : k) = 1 + p.1.2 := rfl

/-- Under `solutionEquivUnits`, the inverse unit value is `b⁻¹ = 1+s`. -/
@[simp] theorem solutionEquivUnits_apply_inv_val [CommRing k]
    (p : {p : k × k // (1 + p.1) * (1 + p.2) = 1}) :
    (((solutionEquivUnits p : kˣ)⁻¹ : kˣ) : k) = 1 + p.1.1 := rfl

/-- The inverse unit parametrization reconstructs `s` with `1+s=b⁻¹`. -/
@[simp] theorem solutionEquivUnits_symm_fst [CommRing k] (unit : kˣ) :
    1 + (solutionEquivUnits.symm unit).1.1 = ((unit⁻¹ : kˣ) : k) := by
  simp [solutionEquivUnits]

/-- The inverse unit parametrization reconstructs `t` with `1+t=b`. -/
@[simp] theorem solutionEquivUnits_symm_snd [CommRing k] (unit : kˣ) :
    1 + (solutionEquivUnits.symm unit).1.2 = (unit : k) := by
  simp [solutionEquivUnits]

/-- Every unit of `ZMod 2` is one. -/
theorem zmodTwo_unit_eq_one (unit : (ZMod 2)ˣ) : unit = 1 := by
  apply Units.ext
  have hunit : (unit : ZMod 2) ≠ 0 := Units.ne_zero unit
  generalize hx : (unit : ZMod 2) = x at hunit ⊢
  fin_cases x
  · exact (hunit rfl).elim
  · rfl

/-- The unit group of `ZMod 2` has exactly one element. -/
instance zmodTwoUnitsUnique : Unique (ZMod 2)ˣ where
  default := 1
  uniq := zmodTwo_unit_eq_one

/-- The unit group of `ZMod 2` is subsingleton. -/
theorem zmodTwo_units_subsingleton : Subsingleton (ZMod 2)ˣ :=
  ⟨fun u v => (zmodTwo_unit_eq_one u).trans (zmodTwo_unit_eq_one v).symm⟩

/-- A coefficient-explicit three-element factor-matroid circuit: all relation coefficients
are nonzero and every two-element subfamily is linearly independent. This is not a
Jacobian or derivative circuit. -/
structure ThreeCircuit [Field k] (x y z : Fin n → k) where
  /-- The coefficient of the first factor in the relation. -/
  firstCoefficient : k
  /-- The coefficient of the second factor in the relation. -/
  secondCoefficient : k
  /-- The coefficient of the third factor in the relation. -/
  thirdCoefficient : k
  /-- The first relation coefficient is nonzero. -/
  firstCoefficient_ne_zero : firstCoefficient ≠ 0
  /-- The second relation coefficient is nonzero. -/
  secondCoefficient_ne_zero : secondCoefficient ≠ 0
  /-- The third relation coefficient is nonzero. -/
  thirdCoefficient_ne_zero : thirdCoefficient ≠ 0
  /-- The displayed coefficients give a linear relation among the three factors. -/
  relation : firstCoefficient • x + secondCoefficient • y + thirdCoefficient • z = 0
  /-- The first and second factors are linearly independent. -/
  firstSecond_independent : LinearIndependent k ![x, y]
  /-- The first and third factors are linearly independent. -/
  firstThird_independent : LinearIndependent k ![x, z]
  /-- The second and third factors are linearly independent. -/
  secondThird_independent : LinearIndependent k ![y, z]

/-- An invertible linear map preserves relation coefficients and three-circuit minimality. -/
def ThreeCircuit.map [Field k] {m : ℕ} {x y z : Fin n → k} (h : ThreeCircuit x y z)
    (equiv : (Fin n → k) ≃ₗ[k] (Fin m → k)) :
    ThreeCircuit (equiv x) (equiv y) (equiv z) where
  firstCoefficient := h.firstCoefficient
  secondCoefficient := h.secondCoefficient
  thirdCoefficient := h.thirdCoefficient
  firstCoefficient_ne_zero := h.firstCoefficient_ne_zero
  secondCoefficient_ne_zero := h.secondCoefficient_ne_zero
  thirdCoefficient_ne_zero := h.thirdCoefficient_ne_zero
  relation := by
    calc
      h.firstCoefficient • equiv x + h.secondCoefficient • equiv y +
          h.thirdCoefficient • equiv z =
          equiv (h.firstCoefficient • x + h.secondCoefficient • y +
            h.thirdCoefficient • z) := by
        rw [equiv.map_add, equiv.map_add, equiv.map_smul, equiv.map_smul, equiv.map_smul]
      _ = equiv 0 := congrArg equiv h.relation
      _ = 0 := equiv.map_zero
  firstSecond_independent := by
    rw [LinearIndependent.pair_iff]
    intro s t hzero
    apply (LinearIndependent.pair_iff.mp h.firstSecond_independent) s t
    apply equiv.injective
    simpa only [equiv.map_add, equiv.map_smul, equiv.map_zero] using hzero
  firstThird_independent := by
    rw [LinearIndependent.pair_iff]
    intro s t hzero
    apply (LinearIndependent.pair_iff.mp h.firstThird_independent) s t
    apply equiv.injective
    simpa only [equiv.map_add, equiv.map_smul, equiv.map_zero] using hzero
  secondThird_independent := by
    rw [LinearIndependent.pair_iff]
    intro s t hzero
    apply (LinearIndependent.pair_iff.mp h.secondThird_independent) s t
    apply equiv.injective
    simpa only [equiv.map_add, equiv.map_smul, equiv.map_zero] using hzero

/-- Nonvanishing of a rank-one triad implies nonvanishing of each of its three factors. -/
theorem factors_ne_zero_of_triad_ne_zero [Field k]
    (u : Fin a → k) (v : Fin b → k) (w : Fin c → k)
    (h : triad u v w ≠ 0) : u ≠ 0 ∧ v ≠ 0 ∧ w ≠ 0 := by
  constructor
  · intro hu
    apply h
    funext i j l
    simp only [triad, hu, Pi.zero_apply, zero_mul]
  · constructor
    · intro hv
      apply h
      funext i j l
      simp only [triad, hv, Pi.zero_apply, mul_zero, zero_mul]
    · intro hw
      apply h
      funext i j l
      simp only [triad, hw, Pi.zero_apply, mul_zero]

/-- Three nonzero factors evaluate to a nonzero rank-one triad over a field. -/
theorem triad_ne_zero_of_factors [Field k]
    (u : Fin a → k) (v : Fin b → k) (w : Fin c → k)
    (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) : triad u v w ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hu
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
  obtain ⟨l, hl⟩ := Function.ne_iff.mp hw
  intro hzero
  have hvalue := congrFun (congrFun (congrFun hzero i) j) l
  simp only [triad, Pi.zero_apply] at hvalue
  exact mul_ne_zero (mul_ne_zero hi hj) hl hvalue

/-- Independent linear equivalences preserve nonvanishing of a rank-one triad. -/
theorem triad_map_ne_zero [Field k] {a' b' c' : ℕ}
    (u : Fin a → k) (v : Fin b → k) (w : Fin c → k)
    (eU : (Fin a → k) ≃ₗ[k] (Fin a' → k))
    (eV : (Fin b → k) ≃ₗ[k] (Fin b' → k))
    (eW : (Fin c → k) ≃ₗ[k] (Fin c' → k))
    (h : triad u v w ≠ 0) : triad (eU u) (eV v) (eW w) ≠ 0 := by
  have hfactors := factors_ne_zero_of_triad_ne_zero u v w h
  exact triad_ne_zero_of_factors _ _ _
    ((LinearEquiv.map_ne_zero_iff eU).2 hfactors.1)
    ((LinearEquiv.map_ne_zero_iff eV).2 hfactors.2.1)
    ((LinearEquiv.map_ne_zero_iff eW).2 hfactors.2.2)

/-- The five ordered triples of factors used by the paired-circuit construction. -/
structure FiveFactorData (k : Type*) (a b c : ℕ) where
  /-- The first-leg factors in slots `a,b,c,d,e`. -/
  U : Fin 5 → Fin a → k
  /-- The fixed second-leg factors in slots `a,b,c,d,e`. -/
  V : Fin 5 → Fin b → k
  /-- The third-leg factors in slots `a,b,c,d,e`. -/
  W : Fin 5 → Fin c → k

namespace FiveFactorData

variable [CommRing k]

/-- Read five distinct labelled source slots from a scheme; the two circuit supports may still
overlap at their shared label `e`. -/
def ofScheme (S : Scheme k a b c r) (slots : Fin 5 ↪ Fin r) :
    FiveFactorData k a b c where
  U q := (S.term (slots q)).1
  V q := (S.term (slots q)).2.1
  W q := (S.term (slots q)).2.2

/-- The sum of the five original rank-one tensors. -/
def baseTensor (D : FiveFactorData k a b c) : Tensor k a b c :=
  ∑ q, triad (D.U q) (D.V q) (D.W q)

/-- The exact normalized two-parameter factor updates on slots `a,b,c,d,e`. -/
def familyData (D : FiveFactorData k a b c) (s t : k) : FiveFactorData k a b c where
  U := ![D.U 0 + s • D.U 3, D.U 1, D.U 2 + t • D.U 1,
    D.U 3 + s • D.U 3, D.U 4 + s • D.U 3]
  V := D.V
  W := ![D.W 0, D.W 1 + t • D.W 2, D.W 2,
    D.W 3 + t • (D.W 0 + D.W 3), D.W 4 + t • D.W 2]

/-- The family definition exposes exactly the seven designated normalized update positions,
while the second leg remains fixed. -/
theorem familyData_spec (D : FiveFactorData k a b c) (s t : k) :
    (D.familyData s t).U 0 = D.U 0 + s • D.U 3 ∧
    (D.familyData s t).W 1 = D.W 1 + t • D.W 2 ∧
    (D.familyData s t).U 2 = D.U 2 + t • D.U 1 ∧
    (D.familyData s t).U 3 = D.U 3 + s • D.U 3 ∧
    (D.familyData s t).W 3 = D.W 3 + t • (D.W 0 + D.W 3) ∧
    (D.familyData s t).U 4 = D.U 4 + s • D.U 3 ∧
    (D.familyData s t).W 4 = D.W 4 + t • D.W 2 ∧
    (D.familyData s t).V = D.V := by
  simp [familyData]

/-- The tensor represented by the five updated terms. -/
def familyTensor (D : FiveFactorData k a b c) (s t : k) : Tensor k a b c :=
  (D.familyData s t).baseTensor

/-- The coefficient of `s` in the exact five-term tensor difference. -/
def coefficientA (D : FiveFactorData k a b c) : Tensor k a b c :=
  triad (D.U 3) (D.V 0) (D.W 0) +
    triad (D.U 3) (D.V 3) (D.W 3) +
    triad (D.U 3) (D.V 4) (D.W 4)

/-- The coefficient of `t` in the exact five-term tensor difference. -/
def coefficientB (D : FiveFactorData k a b c) : Tensor k a b c :=
  triad (D.U 1) (D.V 1) (D.W 2) +
    triad (D.U 1) (D.V 2) (D.W 2) +
    triad (D.U 3) (D.V 3) (D.W 0 + D.W 3) +
    triad (D.U 4) (D.V 4) (D.W 2)

/-- The coefficient of `s*t` in the exact five-term tensor difference. -/
def coefficientC (D : FiveFactorData k a b c) : Tensor k a b c :=
  triad (D.U 3) (D.V 3) (D.W 0 + D.W 3) +
    triad (D.U 3) (D.V 4) (D.W 2)

/-- The updated-minus-original tensor expands exactly as `s A + t B + s*t C`. -/
theorem exact_expansion (D : FiveFactorData k a b c) (s t : k) :
    D.familyTensor s t - D.baseTensor =
      s • D.coefficientA + t • D.coefficientB + (s * t) • D.coefficientC := by
  funext i j l
  simp only [familyTensor, baseTensor, familyData, Fin.isValue, smul_add,
    Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Pi.sub_apply, Pi.add_apply, triad, Pi.smul_apply, smul_eq_mul, coefficientA,
    coefficientB, coefficientC]
  ring

/-- The first normalized `V` circuit and the `W` closure imply `A=C`. -/
theorem coefficientA_eq_coefficientC [CharP k 2] (D : FiveFactorData k a b c)
    (hCircuit : D.V 0 + D.V 3 + D.V 4 = 0)
    (hClosure : D.W 0 + D.W 2 + D.W 4 = 0) :
    D.coefficientA = D.coefficientC := by
  funext i j l
  have hv := congrFun hCircuit j
  have hw := congrFun hClosure l
  simp only [Pi.add_apply, Pi.zero_apply] at hv hw
  simp only [coefficientA, coefficientC, triad, Pi.add_apply]
  have htwo : (2 : k) = 0 := CharP.cast_eq_zero k 2
  have hneg (x : k) : -x = x := by
    apply neg_eq_of_add_eq_zero_right
    calc
      x + x = (2 : k) * x := by ring
      _ = 0 := by rw [htwo, zero_mul]
  have hv' : D.V 0 j = D.V 3 j + D.V 4 j := by
    have hsum : D.V 0 j + (D.V 3 j + D.V 4 j) = 0 := by
      linear_combination hv
    exact (eq_neg_of_add_eq_zero_left hsum).trans (hneg _)
  have hw' : D.W 4 l = D.W 0 l + D.W 2 l := by
    have hsum : (D.W 0 l + D.W 2 l) + D.W 4 l = 0 := by
      linear_combination hw
    exact (eq_neg_of_add_eq_zero_right hsum).trans (hneg _)
  rw [hv', hw']
  ring_nf
  simp only [htwo, mul_zero, add_zero]

/-- The second normalized `V` circuit and the `U` closure imply `B=C`. -/
theorem coefficientB_eq_coefficientC [CharP k 2] (D : FiveFactorData k a b c)
    (hCircuit : D.V 1 + D.V 2 + D.V 4 = 0)
    (hClosure : D.U 1 + D.U 3 + D.U 4 = 0) :
    D.coefficientB = D.coefficientC := by
  funext i j l
  have hv := congrFun hCircuit j
  have hu := congrFun hClosure i
  simp only [Pi.add_apply, Pi.zero_apply] at hv hu
  simp only [coefficientB, coefficientC, triad, Pi.add_apply]
  have htwo : (2 : k) = 0 := CharP.cast_eq_zero k 2
  have hneg (x : k) : -x = x := by
    apply neg_eq_of_add_eq_zero_right
    calc
      x + x = (2 : k) * x := by ring
      _ = 0 := by rw [htwo, zero_mul]
  have hv' : D.V 1 j + D.V 2 j = D.V 4 j := by
    have hsum : (D.V 1 j + D.V 2 j) + D.V 4 j = 0 := by
      linear_combination hv
    exact (eq_neg_of_add_eq_zero_left hsum).trans (hneg _)
  have hu' : D.U 1 i + D.U 4 i = D.U 3 i := by
    have hsum : (D.U 1 i + D.U 4 i) + D.U 3 i = 0 := by
      linear_combination hu
    exact (eq_neg_of_add_eq_zero_left hsum).trans (hneg _)
  rw [← hv', ← hu']
  ring_nf

end FiveFactorData

/-- A scheme contains the overlapping normalized five-slot paired-circuit pattern. The shared
slot `e` occurs in both minimal circuits; this is a sufficient construction, not a
classification. -/
structure Witness [Field k] [CharP k 2] (S : Scheme k a b c r) where
  /-- The source-labelled first outer coordinate domain is nonempty. -/
  sourceU_nonempty : Nonempty (Fin a)
  /-- The source-labelled third outer coordinate domain is nonempty. -/
  sourceW_nonempty : Nonempty (Fin c)
  /-- An injective placement of the five labels `a,b,c,d,e` into source terms. -/
  slots : Fin 5 ↪ Fin r
  /-- Every selected rank-one source term evaluates to a nonzero tensor. -/
  selectedTerm_eval_ne_zero : ∀ q : Fin 5, (S.term (slots q)).eval ≠ 0
  /-- The `V_a,V_d,V_e` factor-matroid circuit with explicit nonzero coefficients. -/
  firstFactorCircuit : ThreeCircuit
    (S.term (slots 0)).2.1 (S.term (slots 3)).2.1 (S.term (slots 4)).2.1
  /-- The `V_b,V_c,V_e` factor-matroid circuit sharing slot `e`. -/
  secondFactorCircuit : ThreeCircuit
    (S.term (slots 1)).2.1 (S.term (slots 2)).2.1 (S.term (slots 4)).2.1
  /-- The first circuit has the normalized all-one relation. -/
  firstCircuit_normalized :
    (S.term (slots 0)).2.1 + (S.term (slots 3)).2.1 + (S.term (slots 4)).2.1 = 0
  /-- The second circuit has the normalized all-one relation. -/
  secondCircuit_normalized :
    (S.term (slots 1)).2.1 + (S.term (slots 2)).2.1 + (S.term (slots 4)).2.1 = 0
  /-- The complementary first-leg closure is `U_b+U_d+U_e=0`. -/
  firstClosure :
    (S.term (slots 1)).1 + (S.term (slots 3)).1 + (S.term (slots 4)).1 = 0
  /-- The complementary third-leg closure is `W_a+W_c+W_e=0`. -/
  thirdClosure :
    (S.term (slots 0)).2.2 + (S.term (slots 2)).2.2 + (S.term (slots 4)).2.2 = 0

namespace Witness

variable [Field k] [CharP k 2] {S : Scheme k a b c r}

/-- Extract the five labelled factor triples from a scheme witness. -/
def factors (h : Witness S) : FiveFactorData k a b c :=
  FiveFactorData.ofScheme S h.slots

/-- The four normalized factor equalities imply the independently checkable tensor equalities
`A=C` and `B=C`. -/
theorem coefficient_equalities (h : Witness S) :
    h.factors.coefficientA = h.factors.coefficientC ∧
      h.factors.coefficientB = h.factors.coefficientC := by
  exact ⟨FiveFactorData.coefficientA_eq_coefficientC _ h.firstCircuit_normalized h.thirdClosure,
    FiveFactorData.coefficientB_eq_coefficientC _ h.secondCircuit_normalized h.firstClosure⟩

/-- The two tensor checks expose the intended chain `A=B=C`. -/
theorem coefficients_all_equal (h : Witness S) :
    h.factors.coefficientA = h.factors.coefficientB ∧
    h.factors.coefficientB = h.factors.coefficientC ∧
    h.factors.coefficientA = h.factors.coefficientC := by
  have hcoefficients := h.coefficient_equalities
  exact ⟨hcoefficients.1.trans hcoefficients.2.symm, hcoefficients.2, hcoefficients.1⟩

/-- The complete normalized certificate exposes all four factor equalities together with the
resulting tensor-coefficient chain `A=B=C`. -/
theorem normalized_certificate (h : Witness S) :
    ((S.term (h.slots 0)).2.1 + (S.term (h.slots 3)).2.1 +
        (S.term (h.slots 4)).2.1 = 0) ∧
    ((S.term (h.slots 1)).2.1 + (S.term (h.slots 2)).2.1 +
        (S.term (h.slots 4)).2.1 = 0) ∧
    ((S.term (h.slots 1)).1 + (S.term (h.slots 3)).1 +
        (S.term (h.slots 4)).1 = 0) ∧
    ((S.term (h.slots 0)).2.2 + (S.term (h.slots 2)).2.2 +
        (S.term (h.slots 4)).2.2 = 0) ∧
    h.factors.coefficientA = h.factors.coefficientB ∧
    h.factors.coefficientB = h.factors.coefficientC := by
  have hcoefficients := h.coefficients_all_equal
  exact ⟨h.firstCircuit_normalized, h.secondCircuit_normalized, h.firstClosure,
    h.thirdClosure, hcoefficients.1, hcoefficients.2.1⟩

/-- On `(1+s)(1+t)=1`, the normalized five-term family represents exactly its original local
tensor, in every characteristic-two field. -/
theorem exact_family (h : Witness S) (s t : k)
    (hst : (1 + s) * (1 + t) = 1) :
    h.factors.familyTensor s t = h.factors.baseTensor := by
  apply sub_eq_zero.mp
  rw [FiveFactorData.exact_expansion]
  have hcoefficients := h.coefficient_equalities
  exact additiveCancellation _ _ _ s t (hcoefficients.2.trans hcoefficients.1.symm)
    hcoefficients.1.symm (torus_iff_scalarCancellation s t |>.mp hst)

/-- Exact term reordering transports the five embedded slots and every circuit, minimality, and
closure field of the witness. -/
def reorder (h : Witness S) (equiv : Fin r ≃ Fin r) : Witness (Action.reorder S equiv) where
  sourceU_nonempty := h.sourceU_nonempty
  sourceW_nonempty := h.sourceW_nonempty
  slots := h.slots.trans equiv.toEmbedding
  selectedTerm_eval_ne_zero := by
    intro q
    simpa only [Action.reorder, Scheme.permute, Function.Embedding.trans_apply,
      Equiv.coe_toEmbedding, Equiv.symm_apply_apply] using h.selectedTerm_eval_ne_zero q
  firstFactorCircuit := by
    simpa only [Action.reorder, Scheme.permute, Function.Embedding.trans_apply,
      Equiv.coe_toEmbedding, Equiv.symm_apply_apply] using h.firstFactorCircuit
  secondFactorCircuit := by
    simpa only [Action.reorder, Scheme.permute, Function.Embedding.trans_apply,
      Equiv.coe_toEmbedding, Equiv.symm_apply_apply] using h.secondFactorCircuit
  firstCircuit_normalized := by
    simpa only [Action.reorder, Scheme.permute, Function.Embedding.trans_apply,
      Equiv.coe_toEmbedding, Equiv.symm_apply_apply] using h.firstCircuit_normalized
  secondCircuit_normalized := by
    simpa only [Action.reorder, Scheme.permute, Function.Embedding.trans_apply,
      Equiv.coe_toEmbedding, Equiv.symm_apply_apply] using h.secondCircuit_normalized
  firstClosure := by
    simpa only [Action.reorder, Scheme.permute, Function.Embedding.trans_apply,
      Equiv.coe_toEmbedding, Equiv.symm_apply_apply] using h.firstClosure
  thirdClosure := by
    simpa only [Action.reorder, Scheme.permute, Function.Embedding.trans_apply,
      Equiv.coe_toEmbedding, Equiv.symm_apply_apply] using h.thirdClosure

end Witness

namespace BinaryFiveMask

/-- The binary field used by the compact five-mask source certificate. -/
abbrev F := ZMod 2

/-- Decode a natural-number bit mask as a sixteen-coordinate binary factor, with bit
`4*row+column` represented by the corresponding little-endian coordinate. -/
def mask (value : ℕ) : Fin 16 → F := fun i => if value.testBit i then 1 else 0

/-- The SHA-256 digest of the external 49-term source file from which the five terms were
selected. No full 49-term table or rank assertion is imported. -/
def sourceSHA256 : String :=
  "5fc92a6bf83fc29d9527ab100bad5d72d769178b616b31a36c3c0c0b8ad9d09d"

/-- The five zero-based term identifiers in source order `a,b,c,d,e`. -/
def sourceTermId : Fin 5 → ℕ := ![1, 14, 29, 37, 42]

/-- The fifteen hexadecimal source masks, grouped as `(U,V,W)` for `a,b,c,d,e`. -/
def sourceMasks : Fin 5 → ℕ × ℕ × ℕ :=
  ![(0x5050, 0x0aa0, 0x8808), (0x9990, 0xbbb0, 0x00f0),
    (0x9090, 0xa000, 0x0070), (0x0500, 0x1110, 0xff0f),
    (0x9c90, 0x1bb0, 0x8878)]

/-- The compact five source terms decoded from the fifteen masks. -/
def factors : FiveFactorData F 16 16 16 where
  U := ![mask 0x5050, mask 0x9990, mask 0x9090, mask 0x0500, mask 0x9c90]
  V := ![mask 0x0aa0, mask 0xbbb0, mask 0xa000, mask 0x1110, mask 0x1bb0]
  W := ![mask 0x8808, mask 0x00f0, mask 0x0070, mask 0xff0f, mask 0x8878]

/-- Every concrete factor is decoded from the corresponding entry of the public fifteen-mask
table, so the metadata cannot drift from the replayed source terms. -/
theorem factors_decode_sourceMasks (q : Fin 5) :
    factors.U q = mask (sourceMasks q).1 ∧
    factors.V q = mask (sourceMasks q).2.1 ∧
    factors.W q = mask (sourceMasks q).2.2 := by
  fin_cases q <;> exact ⟨rfl, rfl, rfl⟩

/-- The five decoded source terms as a rank-five local scheme. -/
def scheme : Scheme F 16 16 16 5 :=
  ⟨fun q => (factors.U q, factors.V q, factors.W q)⟩

/-- The first binary `V` circuit has all coefficients one and every proper pair independent. -/
def firstCircuit : ThreeCircuit (factors.V 0) (factors.V 3) (factors.V 4) where
  firstCoefficient := 1
  secondCoefficient := 1
  thirdCoefficient := 1
  firstCoefficient_ne_zero := by decide
  secondCoefficient_ne_zero := by decide
  thirdCoefficient_ne_zero := by decide
  relation := by decide
  firstSecond_independent := by
    rw [LinearIndependent.pair_iff]
    decide
  firstThird_independent := by
    rw [LinearIndependent.pair_iff]
    decide
  secondThird_independent := by
    rw [LinearIndependent.pair_iff]
    decide

/-- The second binary `V` circuit has all coefficients one and every proper pair independent. -/
def secondCircuit : ThreeCircuit (factors.V 1) (factors.V 2) (factors.V 4) where
  firstCoefficient := 1
  secondCoefficient := 1
  thirdCoefficient := 1
  firstCoefficient_ne_zero := by decide
  secondCoefficient_ne_zero := by decide
  thirdCoefficient_ne_zero := by decide
  relation := by decide
  firstSecond_independent := by
    rw [LinearIndependent.pair_iff]
    decide
  firstThird_independent := by
    rw [LinearIndependent.pair_iff]
    decide
  secondThird_independent := by
    rw [LinearIndependent.pair_iff]
    decide

/-- The compact data have exactly the four normalized closure equations used by the proof. -/
theorem normalized_relations :
    factors.V 0 + factors.V 3 + factors.V 4 = 0 ∧
    factors.V 1 + factors.V 2 + factors.V 4 = 0 ∧
    factors.U 1 + factors.U 3 + factors.U 4 = 0 ∧
    factors.W 0 + factors.W 2 + factors.W 4 = 0 := by
  decide

/-- The normalized relation coefficients in both binary circuits are explicitly all one. -/
theorem normalized_coefficients :
    firstCircuit.firstCoefficient = 1 ∧ firstCircuit.secondCoefficient = 1 ∧
      firstCircuit.thirdCoefficient = 1 ∧ secondCircuit.firstCoefficient = 1 ∧
      secondCircuit.secondCoefficient = 1 ∧ secondCircuit.thirdCoefficient = 1 := by
  decide

/-- The two concrete circuits overlap exactly in factor `V_e`, and each is genuinely minimal
through its three pair-independence fields. -/
theorem genuine_minimality :
    LinearIndependent F ![factors.V 0, factors.V 3] ∧
    LinearIndependent F ![factors.V 0, factors.V 4] ∧
    LinearIndependent F ![factors.V 3, factors.V 4] ∧
    LinearIndependent F ![factors.V 1, factors.V 2] ∧
    LinearIndependent F ![factors.V 1, factors.V 4] ∧
    LinearIndependent F ![factors.V 2, factors.V 4] :=
  ⟨firstCircuit.firstSecond_independent, firstCircuit.firstThird_independent,
    firstCircuit.secondThird_independent, secondCircuit.firstSecond_independent,
    secondCircuit.firstThird_independent, secondCircuit.secondThird_independent⟩

/-- The source identifiers are pairwise distinct, so the five-term slice has no repeated slot. -/
theorem sourceTermId_injective : Function.Injective sourceTermId := by decide

/-- All five concrete binary source terms have nonzero rank-one evaluations. -/
theorem sourceTerms_eval_ne_zero : ∀ q : Fin 5, (scheme.term q).eval ≠ 0 := by
  decide

/-- The public five-slot witness assembles both overlapping circuits and both complementary
closures from independently decoded source masks. -/
def witness : Witness scheme where
  sourceU_nonempty := inferInstance
  sourceW_nonempty := inferInstance
  slots := Function.Embedding.refl (Fin 5)
  selectedTerm_eval_ne_zero := sourceTerms_eval_ne_zero
  firstFactorCircuit := by simpa [scheme] using firstCircuit
  secondFactorCircuit := by simpa [scheme] using secondCircuit
  firstCircuit_normalized := normalized_relations.1
  secondCircuit_normalized := normalized_relations.2.1
  firstClosure := normalized_relations.2.2.1
  thirdClosure := normalized_relations.2.2.2

/-- The concrete source masks yield `A=C` and `B=C`. -/
theorem coefficient_equalities :
    witness.factors.coefficientA = witness.factors.coefficientC ∧
      witness.factors.coefficientB = witness.factors.coefficientC :=
  witness.coefficient_equalities

/-- Every binary torus point gives an exact five-term local tensor presentation. -/
theorem exact_family (s t : F) (hst : (1 + s) * (1 + t) = 1) :
    witness.factors.familyTensor s t = witness.factors.baseTensor :=
  witness.exact_family s t hst

/-- The binary torus has only the origin, so the binary specialization is honest but has no
nontrivial parameter endpoint. -/
theorem torus_point_eq_origin (s t : F) (hst : (1 + s) * (1 + t) = 1) :
    (s, t) = (0, 0) := by
  have hunitOne : solutionEquivUnits ⟨(s, t), hst⟩ = 1 :=
    zmodTwo_unit_eq_one _
  have ht : 1 + t = 1 := by
    rw [← solutionEquivUnits_apply_val ⟨(s, t), hst⟩, hunitOne]
    rfl
  have hs : 1 + s = 1 := by
    rw [← solutionEquivUnits_apply_inv_val ⟨(s, t), hst⟩, hunitOne]
    rfl
  apply Prod.ext
  · exact add_left_cancel (by simpa only [add_zero] using hs)
  · exact add_left_cancel (by simpa only [add_zero] using ht)

/-- The independently recorded first-leg updates in the `s` direction, keyed by source term. -/
def sourceSFirstLegUpdates : List (ℕ × ℕ) :=
  [(1, 0x0500), (37, 0x0500), (42, 0x0500)]

/-- The independently recorded first-leg update in the `t` direction, keyed by source term. -/
def sourceTFirstLegUpdates : List (ℕ × ℕ) := [(29, 0x9990)]

/-- The independently recorded third-leg updates in the `t` direction, keyed by source term. -/
def sourceTThirdLegUpdates : List (ℕ × ℕ) :=
  [(14, 0x0070), (37, 0x7707), (42, 0x0070)]

/-- The normalized update masks agree with the independently listed first-order POC masks. -/
theorem update_masks :
    factors.U 3 = mask 0x0500 ∧
    factors.U 1 = mask 0x9990 ∧
    factors.W 2 = mask 0x0070 ∧
    factors.W 0 + factors.W 3 = mask 0x7707 := by
  decide

/-- The compact metadata, source masks, and independently recorded update lists equal the
stated recorded values. This theorem checks internal consistency, not external-file authentication. -/
theorem source_groundTruth :
    sourceSHA256 = "5fc92a6bf83fc29d9527ab100bad5d72d769178b616b31a36c3c0c0b8ad9d09d" ∧
    sourceTermId = ![1, 14, 29, 37, 42] ∧
    sourceMasks = ![(0x5050, 0x0aa0, 0x8808), (0x9990, 0xbbb0, 0x00f0),
      (0x9090, 0xa000, 0x0070), (0x0500, 0x1110, 0xff0f),
      (0x9c90, 0x1bb0, 0x8878)] ∧
    sourceSFirstLegUpdates = [(1, 0x0500), (37, 0x0500), (42, 0x0500)] ∧
    sourceTFirstLegUpdates = [(29, 0x9990)] ∧
    sourceTThirdLegUpdates = [(14, 0x0070), (37, 0x7707), (42, 0x0070)] := by
  decide

/-- Decoding checks both the zero boundary and little-endian least-significant bit. -/
theorem mask_groundTruth :
    mask 0 = 0 ∧ mask 1 0 = 1 ∧ mask 1 1 = 0 := by
  decide

end BinaryFiveMask

namespace LocalReplay

open Replacement

variable {k : Type*} {a b c : ℕ}

/-- The updated rank-one term in one of the five normalized positions. -/
def familyTerm [Field k] [CharP k 2] {S : Scheme k a b c 5}
    (h : Witness S) (s t : k) (q : Fin 5) : TriadData k a b c :=
  ((h.factors.familyData s t).U q, (h.factors.familyData s t).V q,
    (h.factors.familyData s t).W q)

/-- The ordered rank-five scheme formed by the five updated terms. -/
def familyScheme [Field k] [CharP k 2] {S : Scheme k a b c 5}
    (h : Witness S) (s t : k) : Scheme k a b c 5 :=
  ⟨familyTerm h s t⟩

/-- The ordered insertion list formed by the five updated terms. -/
def familyList [Field k] [CharP k 2] {S : Scheme k a b c 5}
    (h : Witness S) (s t : k) : List (TriadData k a b c) :=
  [familyTerm h s t 0, familyTerm h s t 1, familyTerm h s t 2,
    familyTerm h s t 3, familyTerm h s t 4]

/-- For a rank-five source, summing every source term is the witness base tensor even when the
five labels are embedded in a nontrivial order. -/
theorem source_sum_eq_base [Field k] [CharP k 2]
    {S : Scheme k a b c 5} (h : Witness S) :
    (∑ q, (S.term q).eval) = h.factors.baseTensor := by
  rw [FiveFactorData.baseTensor]
  change (∑ q, (S.term q).eval) = ∑ q, (S.term (h.slots q)).eval
  let equiv : Fin 5 ≃ Fin 5 := h.slots.equivOfFiniteSelfEmbedding
  calc
    (∑ q, (S.term q).eval) = ∑ q, (S.term (equiv q)).eval :=
      (Equiv.sum_comp equiv (fun q => (S.term q).eval)).symm
    _ = ∑ q, (S.term (h.slots q)).eval := by
      apply Finset.sum_congr rfl
      intro q _hq
      congr 2

/-- Summing the ordered updated scheme is definitionally the five-term family tensor. -/
theorem family_sum_eq [Field k] [CharP k 2]
    {S : Scheme k a b c 5} (h : Witness S) (s t : k) :
    (∑ q, ((familyScheme h s t).term q).eval) =
      h.factors.familyTensor s t := by
  rfl

/-- A replayable exact replacement removes the five source slots and inserts the five normalized
updated terms, using only the torus equation and paired-circuit witness. -/
def certificate [Field k] [CharP k 2] {S : Scheme k a b c 5}
    (h : Witness S) (s t : k) (hst : (1 + s) * (1 + t) = 1) :
    Replacement.Certificate S where
  removed := Finset.univ
  inserted := familyList h s t
  local_eq := by
    calc
      selectedTensor S Finset.univ = h.factors.baseTensor := by
        simpa [selectedTensor] using source_sum_eq_base h
      _ = h.factors.familyTensor s t := (h.exact_family s t hst).symm
      _ = insertedTensor (familyList h s t) := by
        rw [← family_sum_eq h s t]
        simp only [Fin.sum_univ_five, familyScheme, familyList, insertedTensor,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        ac_rfl

/-- The replay certificate removes exactly five slots and inserts exactly five terms. -/
theorem certificate_exactly_five [Field k] [CharP k 2]
    {S : Scheme k a b c 5} (h : Witness S) (s t : k)
    (hst : (1 + s) * (1 + t) = 1) :
    (certificate h s t hst).removed.card = 5 ∧
      (certificate h s t hst).inserted.length = 5 := by
  simp only [certificate, Finset.card_univ, Fintype.card_fin, familyList,
    List.length_cons, List.length_nil, and_self]

/-- Every deterministic inserted output slot contains its corresponding normalized family term. -/
theorem certificate_inserted_output [Field k] [CharP k 2]
    {S : Scheme k a b c 5} (h : Witness S) (s t : k)
    (hst : (1 + s) * (1 + t) = 1) (q : Fin 5) :
    (certificate h s t hst).output.term
      ((certificate h s t hst).insertedSlot q) =
        (familyScheme h s t).term q := by
  fin_cases q <;> rfl

/-- The deterministic replacement output is exactly the ordered normalized family scheme. -/
theorem certificate_output_eq_family [Field k] [CharP k 2]
    {S : Scheme k a b c 5} (h : Witness S) (s t : k)
    (hst : (1 + s) * (1 + t) = 1) :
    (certificate h s t hst).output = familyScheme h s t := by
  apply congrArg
    (fun f : Fin 5 → TriadData k a b c => (⟨f⟩ : Scheme k a b c 5))
  funext q
  fin_cases q <;> rfl

/-- Replaying the five-for-five certificate preserves the complete source tensor. -/
theorem certificate_sumTensor_eq [Field k] [CharP k 2]
    {S : Scheme k a b c 5} (h : Witness S) (s t : k)
    (hst : (1 + s) * (1 + t) = 1) :
    (certificate h s t hst).output.sumTensor = S.sumTensor :=
  (certificate h s t hst).sumTensor_eq

/-- Rebuild the replay certificate after an exact T1 term permutation. -/
def reorderedCertificate [Field k] [CharP k 2]
    {S : Scheme k a b c 5} (h : Witness S) (equiv : Fin 5 ≃ Fin 5) (s t : k)
    (hst : (1 + s) * (1 + t) = 1) :
    Replacement.Certificate (Action.reorder S equiv) :=
  certificate (h.reorder equiv) s t hst

/-- Reordering source slots transports the witness labels, so the five inserted terms remain in
exactly the same normalized label order. -/
theorem reordered_inserted_terms [Field k] [CharP k 2]
    {S : Scheme k a b c 5} (h : Witness S) (equiv : Fin 5 ≃ Fin 5) (s t : k)
    (hst : (1 + s) * (1 + t) = 1) :
    (reorderedCertificate h equiv s t hst).inserted =
      (certificate h s t hst).inserted := by
  have hfactors : (h.reorder equiv).factors = h.factors := by
    change
      FiveFactorData.ofScheme (Action.reorder S equiv)
          (h.slots.trans equiv.toEmbedding) =
        FiveFactorData.ofScheme S h.slots
    unfold FiveFactorData.ofScheme
    rw [FiveFactorData.mk.injEq]
    refine ⟨?_, ?_, ?_⟩ <;>
      funext q x <;>
      simp only [Action.reorder, Scheme.permute,
        Function.Embedding.trans_apply, Equiv.coe_toEmbedding,
        Equiv.symm_apply_apply]
  change familyList (h.reorder equiv) s t = familyList h s t
  simp only [familyList, familyTerm]
  rw [hfactors]

/-- Transport the replayable local equality through any additive triad symmetry. -/
def symmetryCertificate [Field k] [CharP k 2]
    {S : Scheme k a b c 5} {a' b' c' : ℕ} (h : Witness S) (s t : k)
    (hst : (1 + s) * (1 + t) = 1)
    (equiv : Replacement.TriadSymmetry k a b c a' b' c') :
    Replacement.Certificate (equiv.mapScheme S) :=
  (certificate h s t hst).transport equiv

/-- Symmetry transport maps each inserted term by the supplied triad equivalence. -/
theorem symmetry_inserted_terms [Field k] [CharP k 2]
    {S : Scheme k a b c 5} {a' b' c' : ℕ} (h : Witness S) (s t : k)
    (hst : (1 + s) * (1 + t) = 1)
    (equiv : Replacement.TriadSymmetry k a b c a' b' c') :
    (symmetryCertificate h s t hst equiv).inserted =
      equiv.mapInserted (certificate h s t hst).inserted := by
  rfl

/-- The concrete binary five-mask witness yields a kernel-replayable five-for-five certificate. -/
def binaryCertificate : Replacement.Certificate BinaryFiveMask.scheme :=
  certificate BinaryFiveMask.witness 0 0 (by decide)

/-- The concrete binary replay removes and inserts five terms and preserves its source tensor. -/
theorem binaryCertificate_fixture :
    binaryCertificate.removed.card = 5 ∧
    binaryCertificate.inserted.length = 5 ∧
    binaryCertificate.output.sumTensor = BinaryFiveMask.scheme.sumTensor := by
  exact ⟨(certificate_exactly_five BinaryFiveMask.witness 0 0 (by decide)).1,
    (certificate_exactly_five BinaryFiveMask.witness 0 0 (by decide)).2,
    binaryCertificate.sumTensor_eq⟩

end LocalReplay

namespace BinaryFiveMaskRatFunc

noncomputable section

/-- The rational-function scalar extension of the binary five-mask field. -/
abbrev K := RatFunc BinaryFiveMask.F

/-- The scalar-extension field has exact characteristic two. -/
theorem ringChar_eq_two : ringChar K = 2 :=
  ringChar.eq K 2

/-- Canonically extend a binary coordinate factor to the rational-function field. -/
def liftFactor (v : Fin 16 → BinaryFiveMask.F) : Fin 16 → K :=
  fun i => algebraMap BinaryFiveMask.F K (v i)

/-- Canonical scalar extension is coordinatewise the algebra map. -/
@[simp] theorem liftFactor_apply (v : Fin 16 → BinaryFiveMask.F) (i : Fin 16) :
    liftFactor v i = algebraMap BinaryFiveMask.F K (v i) := rfl

/-- Canonical scalar extension is injective on coordinate factors. -/
theorem liftFactor_injective : Function.Injective liftFactor := by
  intro v w h
  funext i
  exact (algebraMap BinaryFiveMask.F K).injective (congrFun h i)

/-- A nonzero binary coordinate factor remains nonzero after canonical scalar extension. -/
theorem liftFactor_ne_zero {v : Fin 16 → BinaryFiveMask.F} (hv : v ≠ 0) :
    liftFactor v ≠ 0 := by
  intro hzero
  apply hv
  apply liftFactor_injective
  rw [hzero]
  funext i
  simp only [liftFactor, Pi.zero_apply, map_zero]

/-- Two coordinate evaluations with a nonzero determinant certify pairwise linear independence. -/
theorem pair_linearIndependent_of_det (x y : Fin 16 → K) (i j : Fin 16)
    (hdet : x i * y j - x j * y i ≠ 0) : LinearIndependent K ![x, y] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have hi := congrFun hab i
  have hj := congrFun hab j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi hj
  have ha : a * (x i * y j - x j * y i) = 0 := by
    linear_combination y j * hi - y i * hj
  have hb : b * (x i * y j - x j * y i) = 0 := by
    linear_combination x i * hj - x j * hi
  exact ⟨(mul_eq_zero.mp ha).resolve_right hdet,
    (mul_eq_zero.mp hb).resolve_right hdet⟩

/-- The same fifteen `BinaryFiveMask` factors, canonically extended from `ZMod 2`. -/
def factors : FiveFactorData K 16 16 16 where
  U q := liftFactor (BinaryFiveMask.factors.U q)
  V q := liftFactor (BinaryFiveMask.factors.V q)
  W q := liftFactor (BinaryFiveMask.factors.W q)

/-- Every extended factor is decoded from exactly the existing binary source-mask table. -/
theorem factors_decode_sourceMasks (q : Fin 5) :
    factors.U q = liftFactor (BinaryFiveMask.mask (BinaryFiveMask.sourceMasks q).1) ∧
    factors.V q = liftFactor (BinaryFiveMask.mask (BinaryFiveMask.sourceMasks q).2.1) ∧
    factors.W q = liftFactor (BinaryFiveMask.mask (BinaryFiveMask.sourceMasks q).2.2) := by
  have h := BinaryFiveMask.factors_decode_sourceMasks q
  exact ⟨congrArg liftFactor h.1, congrArg liftFactor h.2.1,
    congrArg liftFactor h.2.2⟩

/-- The five canonically extended source terms as a rank-five local scheme. -/
def scheme : Scheme K 16 16 16 5 :=
  ⟨fun q => (factors.U q, factors.V q, factors.W q)⟩

/-- The extended scheme uses exactly the lifted factor triple in every slot. -/
theorem scheme_term (q : Fin 5) :
    scheme.term q = (factors.U q, factors.V q, factors.W q) := rfl

/-- Every canonically extended source term retains its nonzero rank-one evaluation. -/
theorem sourceTerms_eval_ne_zero : ∀ q : Fin 5, (scheme.term q).eval ≠ 0 := by
  intro q
  have hbinary := factors_ne_zero_of_triad_ne_zero
    (BinaryFiveMask.factors.U q) (BinaryFiveMask.factors.V q)
    (BinaryFiveMask.factors.W q) (BinaryFiveMask.sourceTerms_eval_ne_zero q)
  change triad (liftFactor (BinaryFiveMask.factors.U q))
    (liftFactor (BinaryFiveMask.factors.V q))
    (liftFactor (BinaryFiveMask.factors.W q)) ≠ 0
  exact triad_ne_zero_of_factors _ _ _ (liftFactor_ne_zero hbinary.1)
    (liftFactor_ne_zero hbinary.2.1) (liftFactor_ne_zero hbinary.2.2)

/-- The four normalized binary relations survive canonical scalar extension. -/
theorem normalized_relations :
    factors.V 0 + factors.V 3 + factors.V 4 = 0 ∧
    factors.V 1 + factors.V 2 + factors.V 4 = 0 ∧
    factors.U 1 + factors.U 3 + factors.U 4 = 0 ∧
    factors.W 0 + factors.W 2 + factors.W 4 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext i
    have hi := congrFun BinaryFiveMask.normalized_relations.1 i
    simpa only [factors, liftFactor, Pi.add_apply, Pi.zero_apply, map_add, map_zero]
      using congrArg (algebraMap BinaryFiveMask.F K) hi
  · funext i
    have hi := congrFun BinaryFiveMask.normalized_relations.2.1 i
    simpa only [factors, liftFactor, Pi.add_apply, Pi.zero_apply, map_add, map_zero]
      using congrArg (algebraMap BinaryFiveMask.F K) hi
  · funext i
    have hi := congrFun BinaryFiveMask.normalized_relations.2.2.1 i
    simpa only [factors, liftFactor, Pi.add_apply, Pi.zero_apply, map_add, map_zero]
      using congrArg (algebraMap BinaryFiveMask.F K) hi
  · funext i
    have hi := congrFun BinaryFiveMask.normalized_relations.2.2.2 i
    simpa only [factors, liftFactor, Pi.add_apply, Pi.zero_apply, map_add, map_zero]
      using congrArg (algebraMap BinaryFiveMask.F K) hi

/-- The lifted circuit coordinates used below are the canonical images of the same mask bits. -/
theorem circuit_coordinate_groundTruth :
    factors.V 0 5 = 1 ∧ factors.V 0 4 = 0 ∧
    factors.V 3 5 = 0 ∧ factors.V 3 4 = 1 ∧
    factors.V 4 5 = 1 ∧ factors.V 4 4 = 1 ∧
    factors.V 1 4 = 1 ∧ factors.V 1 13 = 1 ∧
    factors.V 2 4 = 0 ∧ factors.V 2 13 = 1 ∧
    factors.V 4 13 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change algebraMap BinaryFiveMask.F K (BinaryFiveMask.factors.V 0 5) = 1
    rw [show BinaryFiveMask.factors.V 0 5 = 1 by decide, map_one]
  · change algebraMap BinaryFiveMask.F K (BinaryFiveMask.factors.V 0 4) = 0
    rw [show BinaryFiveMask.factors.V 0 4 = 0 by decide, map_zero]
  · change algebraMap BinaryFiveMask.F K (BinaryFiveMask.factors.V 3 5) = 0
    rw [show BinaryFiveMask.factors.V 3 5 = 0 by decide, map_zero]
  · change algebraMap BinaryFiveMask.F K (BinaryFiveMask.factors.V 3 4) = 1
    rw [show BinaryFiveMask.factors.V 3 4 = 1 by decide, map_one]
  · change algebraMap BinaryFiveMask.F K (BinaryFiveMask.factors.V 4 5) = 1
    rw [show BinaryFiveMask.factors.V 4 5 = 1 by decide, map_one]
  · change algebraMap BinaryFiveMask.F K (BinaryFiveMask.factors.V 4 4) = 1
    rw [show BinaryFiveMask.factors.V 4 4 = 1 by decide, map_one]
  · change algebraMap BinaryFiveMask.F K (BinaryFiveMask.factors.V 1 4) = 1
    rw [show BinaryFiveMask.factors.V 1 4 = 1 by decide, map_one]
  · change algebraMap BinaryFiveMask.F K (BinaryFiveMask.factors.V 1 13) = 1
    rw [show BinaryFiveMask.factors.V 1 13 = 1 by decide, map_one]
  · change algebraMap BinaryFiveMask.F K (BinaryFiveMask.factors.V 2 4) = 0
    rw [show BinaryFiveMask.factors.V 2 4 = 0 by decide, map_zero]
  · change algebraMap BinaryFiveMask.F K (BinaryFiveMask.factors.V 2 13) = 1
    rw [show BinaryFiveMask.factors.V 2 13 = 1 by decide, map_one]
  · change algebraMap BinaryFiveMask.F K (BinaryFiveMask.factors.V 4 13) = 0
    rw [show BinaryFiveMask.factors.V 4 13 = 0 by decide, map_zero]

/-- The first extended `V` circuit is the base change of the first binary circuit. -/
def firstCircuit : ThreeCircuit (factors.V 0) (factors.V 3) (factors.V 4) where
  firstCoefficient := 1
  secondCoefficient := 1
  thirdCoefficient := 1
  firstCoefficient_ne_zero := one_ne_zero
  secondCoefficient_ne_zero := one_ne_zero
  thirdCoefficient_ne_zero := one_ne_zero
  relation := by simpa only [one_smul] using normalized_relations.1
  firstSecond_independent := by
    apply pair_linearIndependent_of_det _ _ 5 4
    rcases circuit_coordinate_groundTruth with
      ⟨h05, h04, h35, h34, _h45, _h44, _h14, _h113, _h24, _h213, _h413⟩
    simpa only [h05, h34, h04, h35, one_mul, zero_mul, mul_zero, sub_zero] using
      (one_ne_zero : (1 : K) ≠ 0)
  firstThird_independent := by
    apply pair_linearIndependent_of_det _ _ 5 4
    rcases circuit_coordinate_groundTruth with
      ⟨h05, h04, _h35, _h34, h45, h44, _h14, _h113, _h24, _h213, _h413⟩
    simpa only [h05, h44, h04, h45, one_mul, zero_mul, mul_zero, sub_zero] using
      (one_ne_zero : (1 : K) ≠ 0)
  secondThird_independent := by
    apply pair_linearIndependent_of_det _ _ 4 5
    rcases circuit_coordinate_groundTruth with
      ⟨_h05, _h04, h35, h34, h45, h44, _h14, _h113, _h24, _h213, _h413⟩
    simpa only [h34, h45, h35, h44, one_mul, zero_mul, mul_zero, sub_zero] using
      (one_ne_zero : (1 : K) ≠ 0)

/-- The second extended `V` circuit is the base change of the second binary circuit. -/
def secondCircuit : ThreeCircuit (factors.V 1) (factors.V 2) (factors.V 4) where
  firstCoefficient := 1
  secondCoefficient := 1
  thirdCoefficient := 1
  firstCoefficient_ne_zero := one_ne_zero
  secondCoefficient_ne_zero := one_ne_zero
  thirdCoefficient_ne_zero := one_ne_zero
  relation := by simpa only [one_smul] using normalized_relations.2.1
  firstSecond_independent := by
    apply pair_linearIndependent_of_det _ _ 4 13
    rcases circuit_coordinate_groundTruth with
      ⟨_h05, _h04, _h35, _h34, _h45, _h44, h14, h113, h24, h213, _h413⟩
    simpa only [h14, h213, h113, h24, one_mul, zero_mul, mul_zero, sub_zero] using
      (one_ne_zero : (1 : K) ≠ 0)
  firstThird_independent := by
    apply pair_linearIndependent_of_det _ _ 13 4
    rcases circuit_coordinate_groundTruth with
      ⟨_h05, _h04, _h35, _h34, _h45, h44, h14, h113, _h24, _h213, h413⟩
    simpa only [h113, h44, h14, h413, one_mul, zero_mul, mul_zero, sub_zero] using
      (one_ne_zero : (1 : K) ≠ 0)
  secondThird_independent := by
    apply pair_linearIndependent_of_det _ _ 13 4
    rcases circuit_coordinate_groundTruth with
      ⟨_h05, _h04, _h35, _h34, _h45, h44, _h14, _h113, h24, h213, h413⟩
    simpa only [h213, h44, h24, h413, one_mul, zero_mul, mul_zero, sub_zero] using
      (one_ne_zero : (1 : K) ≠ 0)

/-- The lifted circuits retain all-one coefficients and all six proper-pair checks. -/
theorem circuit_groundTruth :
    firstCircuit.firstCoefficient = 1 ∧ firstCircuit.secondCoefficient = 1 ∧
    firstCircuit.thirdCoefficient = 1 ∧ secondCircuit.firstCoefficient = 1 ∧
    secondCircuit.secondCoefficient = 1 ∧ secondCircuit.thirdCoefficient = 1 ∧
    LinearIndependent K ![factors.V 0, factors.V 3] ∧
    LinearIndependent K ![factors.V 0, factors.V 4] ∧
    LinearIndependent K ![factors.V 3, factors.V 4] ∧
    LinearIndependent K ![factors.V 1, factors.V 2] ∧
    LinearIndependent K ![factors.V 1, factors.V 4] ∧
    LinearIndependent K ![factors.V 2, factors.V 4] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl,
    firstCircuit.firstSecond_independent, firstCircuit.firstThird_independent,
    firstCircuit.secondThird_independent, secondCircuit.firstSecond_independent,
    secondCircuit.firstThird_independent, secondCircuit.secondThird_independent⟩

/-- The same five masks give a paired-circuit witness over the scalar-extension field. -/
def witness : Witness scheme where
  sourceU_nonempty := inferInstance
  sourceW_nonempty := inferInstance
  slots := Function.Embedding.refl (Fin 5)
  selectedTerm_eval_ne_zero := sourceTerms_eval_ne_zero
  firstFactorCircuit := by simpa [scheme] using firstCircuit
  secondFactorCircuit := by simpa [scheme] using secondCircuit
  firstCircuit_normalized := normalized_relations.1
  secondCircuit_normalized := normalized_relations.2.1
  firstClosure := normalized_relations.2.2.1
  thirdClosure := normalized_relations.2.2.2

/-- Extracting the witness factors returns the canonically extended mask data. -/
@[simp] theorem witness_factors : witness.factors = factors := rfl

/-- The explicit nonconstant torus parameter in the second direction. -/
def torusT : K := RatFunc.X

/-- The corresponding first torus parameter `t * (1+t)⁻¹`. -/
def torusS : K := torusT * (1 + torusT)⁻¹

/-- The rational function `1 + X` is nonzero. -/
theorem one_add_torusT_ne_zero : 1 + torusT ≠ 0 := by
  simpa only [torusT, map_add, RatFunc.algebraMap_X, RatFunc.algebraMap_C,
    map_one, add_comm] using
    (RatFunc.algebraMap_ne_zero (Polynomial.X_add_C_ne_zero (1 : BinaryFiveMask.F)))

/-- The second torus parameter is genuinely nonzero. -/
theorem torusT_ne_zero : torusT ≠ 0 := by
  exact RatFunc.X_ne_zero

/-- The first torus parameter is genuinely nonzero as well. -/
theorem torusS_ne_zero : torusS ≠ 0 := by
  exact mul_ne_zero torusT_ne_zero (inv_ne_zero one_add_torusT_ne_zero)

/-- The explicit rational-function parameters satisfy the torus equation. -/
theorem torus_equation : (1 + torusS) * (1 + torusT) = 1 := by
  exact (eq_field_inv_iff torusS torusT one_add_torusT_ne_zero).2 rfl

/-- The lifted update direction `W_c` is nonzero. -/
theorem factorWTwo_ne_zero : factors.W 2 ≠ 0 := by
  intro hzero
  have hLift : liftFactor (BinaryFiveMask.factors.W 2) = liftFactor 0 := by
    rw [← show factors.W 2 = liftFactor (BinaryFiveMask.factors.W 2) from rfl]
    rw [hzero]
    funext i
    simp only [liftFactor, Pi.zero_apply, map_zero]
  have hBinary : BinaryFiveMask.factors.W 2 = 0 := liftFactor_injective hLift
  have hNonzero : BinaryFiveMask.factors.W 2 ≠ 0 := by decide
  exact hNonzero hBinary

/-- The designated slot-`b` third-leg update genuinely changes at the explicit torus point. -/
theorem designated_updated_factor_changes :
    (witness.factors.familyData torusS torusT).W 1 ≠ witness.factors.W 1 := by
  have hupdate := (FiveFactorData.familyData_spec witness.factors torusS torusT).2.1
  rw [hupdate]
  intro heq
  have hzero : torusT • witness.factors.W 2 = 0 := by
    apply add_left_cancel (a := witness.factors.W 1)
    simpa only [add_zero] using heq
  have hw : witness.factors.W 2 ≠ 0 := by
    simpa only [witness_factors] using factorWTwo_ne_zero
  exact (smul_ne_zero torusT_ne_zero hw) hzero

/-- The explicit nontrivial family point preserves the five-term tensor. -/
theorem exact_family :
    witness.factors.familyTensor torusS torusT = witness.factors.baseTensor :=
  witness.exact_family torusS torusT torus_equation

/-- The explicit nontrivial scalar-extension replacement certificate. -/
def certificate : Replacement.Certificate scheme :=
  LocalReplay.certificate witness torusS torusT torus_equation

/-- The designated changed factor occurs in the corresponding deterministic certificate output slot. -/
theorem certificate_updated_factor_changes :
    ((LocalReplay.certificate witness torusS torusT torus_equation).output.term
      ((LocalReplay.certificate witness torusS torusT torus_equation).insertedSlot
        (1 : Fin 5))).2.2 ≠ (scheme.term 1).2.2 := by
  rw [LocalReplay.certificate_inserted_output witness torusS torusT torus_equation 1]
  change (witness.factors.familyData torusS torusT).W 1 ≠ factors.W 1
  simpa only [witness_factors] using designated_updated_factor_changes

/-- The certificate is five-for-five and kernel-checks complete tensor preservation. -/
theorem certificate_fixture :
    certificate.removed.card = 5 ∧
    certificate.inserted.length = 5 ∧
    certificate.output.sumTensor = scheme.sumTensor := by
  exact ⟨(LocalReplay.certificate_exactly_five witness torusS torusT torus_equation).1,
    (LocalReplay.certificate_exactly_five witness torusS torusT torus_equation).2,
    certificate.sumTensor_eq⟩

/-- The certificate combines exact characteristic, a nonzero torus point, a genuine factor
change, and tensor preservation without asserting a second binary point or action inequivalence. -/
theorem nontrivial_replacement_certificate :
    ringChar K = 2 ∧
    torusS ≠ 0 ∧ torusT ≠ 0 ∧
    (1 + torusS) * (1 + torusT) = 1 ∧
    (witness.factors.familyData torusS torusT).W 1 ≠ witness.factors.W 1 ∧
    certificate.output.sumTensor = scheme.sumTensor := by
  exact ⟨ringChar_eq_two, torusS_ne_zero, torusT_ne_zero, torus_equation,
    designated_updated_factor_changes, certificate_fixture.2.2⟩

/-- One joint fixture traces every extended factor to the binary masks, keeps all five source
terms genuine, and records the nontrivial five-for-five tensor-preserving replacement. -/
theorem sameMasks_nontrivial_replacement_fixture :
    (∀ q : Fin 5,
      factors.U q = liftFactor (BinaryFiveMask.mask (BinaryFiveMask.sourceMasks q).1) ∧
      factors.V q = liftFactor (BinaryFiveMask.mask (BinaryFiveMask.sourceMasks q).2.1) ∧
      factors.W q = liftFactor (BinaryFiveMask.mask (BinaryFiveMask.sourceMasks q).2.2)) ∧
    (∀ q : Fin 5, (scheme.term q).eval ≠ 0) ∧
    ringChar K = 2 ∧ torusS ≠ 0 ∧ torusT ≠ 0 ∧
    (1 + torusS) * (1 + torusT) = 1 ∧
    (witness.factors.familyData torusS torusT).W 1 ≠ witness.factors.W 1 ∧
    certificate.removed.card = 5 ∧ certificate.inserted.length = 5 ∧
    certificate.output.sumTensor = scheme.sumTensor := by
  exact ⟨factors_decode_sourceMasks, sourceTerms_eval_ne_zero, ringChar_eq_two,
    torusS_ne_zero, torusT_ne_zero, torus_equation, designated_updated_factor_changes,
    certificate_fixture.1, certificate_fixture.2.1, certificate_fixture.2.2⟩

end

end BinaryFiveMaskRatFunc

namespace ActionTransport

open Action

variable {k : Type*} {a b c r n₁ n₂ n₃ : ℕ}

/-- Complete paired-circuit and closure evidence for five source-labelled factor triples. Keeping
source labels separate from physical output legs prevents odd outer orientations from silently
changing which leg contains the fixed `V` circuits. -/
structure Evidence [Field k] [CharP k 2] (D : FiveFactorData k a b c) where
  /-- The source-labelled first outer coordinate domain is nonempty. -/
  sourceU_nonempty : Nonempty (Fin a)
  /-- The source-labelled third outer coordinate domain is nonempty. -/
  sourceW_nonempty : Nonempty (Fin c)
  /-- Every source-labelled rank-one triad evaluates to a nonzero tensor. -/
  triad_ne_zero : ∀ q : Fin 5, triad (D.U q) (D.V q) (D.W q) ≠ 0
  /-- The complete minimal circuit on source factors `V_a,V_d,V_e`. -/
  firstFactorCircuit : ThreeCircuit (D.V 0) (D.V 3) (D.V 4)
  /-- The complete minimal circuit on source factors `V_b,V_c,V_e`. -/
  secondFactorCircuit : ThreeCircuit (D.V 1) (D.V 2) (D.V 4)
  /-- The normalized first source-`V` relation. -/
  firstCircuit_normalized : D.V 0 + D.V 3 + D.V 4 = 0
  /-- The normalized second source-`V` relation. -/
  secondCircuit_normalized : D.V 1 + D.V 2 + D.V 4 = 0
  /-- The normalized source-`U` closure. -/
  firstClosure : D.U 1 + D.U 3 + D.U 4 = 0
  /-- The normalized source-`W` closure. -/
  thirdClosure : D.W 0 + D.W 2 + D.W 4 = 0

/-- Apply independent linear equivalences to the three source-labelled factor families. -/
def mapData [Field k] {a' b' c' : ℕ} (D : FiveFactorData k a b c)
    (eU : (Fin a → k) ≃ₗ[k] (Fin a' → k))
    (eV : (Fin b → k) ≃ₗ[k] (Fin b' → k))
    (eW : (Fin c → k) ≃ₗ[k] (Fin c' → k)) : FiveFactorData k a' b' c' where
  U q := eU (D.U q)
  V q := eV (D.V q)
  W q := eW (D.W q)

/-- Identity factor equivalences leave all source-labelled five-factor data unchanged. -/
theorem mapData_refl [Field k] (D : FiveFactorData k a b c) :
    mapData D (LinearEquiv.refl k _) (LinearEquiv.refl k _) (LinearEquiv.refl k _) = D := by
  rfl

/-- A linear equivalence between coordinate-function spaces transfers nonemptiness of the
source coordinate domain to the target coordinate domain. -/
theorem target_nonempty_of_linearEquiv [Field k] {m n : ℕ} (hm : Nonempty (Fin m))
    (equiv : (Fin m → k) ≃ₗ[k] (Fin n → k)) : Nonempty (Fin n) := by
  classical
  let one : Fin m → k := fun _ => 1
  have hone : one ≠ 0 := by
    obtain ⟨i⟩ := hm
    intro hz
    have hi := congrFun hz i
    change (1 : k) = 0 at hi
    exact one_ne_zero hi
  have heone : equiv one ≠ 0 := by
    intro hz
    apply hone
    apply equiv.injective
    simpa only [map_zero] using hz
  by_contra hn
  apply heone
  funext i
  exact (hn ⟨i⟩).elim

namespace Evidence

/-- Independent linear equivalences preserve both complete three-circuits and both closures. -/
def map [Field k] [CharP k 2] {a' b' c' : ℕ} {D : FiveFactorData k a b c}
    (h : Evidence D)
    (eU : (Fin a → k) ≃ₗ[k] (Fin a' → k))
    (eV : (Fin b → k) ≃ₗ[k] (Fin b' → k))
    (eW : (Fin c → k) ≃ₗ[k] (Fin c' → k)) : Evidence (mapData D eU eV eW) where
  sourceU_nonempty := target_nonempty_of_linearEquiv h.sourceU_nonempty eU
  sourceW_nonempty := target_nonempty_of_linearEquiv h.sourceW_nonempty eW
  triad_ne_zero := by
    intro q
    exact PairedCircuit.triad_map_ne_zero (D.U q) (D.V q) (D.W q) eU eV eW
      (h.triad_ne_zero q)
  firstFactorCircuit := h.firstFactorCircuit.map eV
  secondFactorCircuit := h.secondFactorCircuit.map eV
  firstCircuit_normalized := by
    simpa only [mapData, map_add, map_zero] using congrArg eV h.firstCircuit_normalized
  secondCircuit_normalized := by
    simpa only [mapData, map_add, map_zero] using congrArg eV h.secondCircuit_normalized
  firstClosure := by
    simpa only [mapData, map_add, map_zero] using congrArg eU h.firstClosure
  thirdClosure := by
    simpa only [mapData, map_add, map_zero] using congrArg eW h.thirdClosure

/-- Complete action evidence implies the two tensor coefficient equalities `A=C` and `B=C`. -/
theorem coefficient_equalities [Field k] [CharP k 2] {D : FiveFactorData k a b c}
    (h : Evidence D) :
    D.coefficientA = D.coefficientC ∧ D.coefficientB = D.coefficientC :=
  ⟨FiveFactorData.coefficientA_eq_coefficientC D h.firstCircuit_normalized h.thirdClosure,
    FiveFactorData.coefficientB_eq_coefficientC D h.secondCircuit_normalized h.firstClosure⟩

/-- Complete action evidence proves exact normalized family constancy on the torus. -/
theorem exact_family [Field k] [CharP k 2] {D : FiveFactorData k a b c}
    (h : Evidence D) (s t : k) (hst : (1 + s) * (1 + t) = 1) :
    D.familyTensor s t = D.baseTensor := by
  apply sub_eq_zero.mp
  rw [FiveFactorData.exact_expansion]
  have hcoefficients := h.coefficient_equalities
  exact additiveCancellation _ _ _ s t (hcoefficients.2.trans hcoefficients.1.symm)
    hcoefficients.1.symm (torus_iff_scalarCancellation s t |>.mp hst)

end Evidence

/-- A scheme witness whose complete evidence is factored through its five selected terms. -/
structure SchemeWitness [Field k] [CharP k 2] (S : Scheme k a b c r) where
  /-- The embedded source positions labelled `a,b,c,d,e`. -/
  slots : Fin 5 ↪ Fin r
  /-- All circuit, minimality, and closure data on the selected factors. -/
  evidence : Evidence (FiveFactorData.ofScheme S slots)

namespace SchemeWitness

/-- Package an ordinary fixed-second-leg witness as source-labelled action evidence. -/
def ofWitness [Field k] [CharP k 2] {S : Scheme k a b c r} (h : Witness S) :
    SchemeWitness S where
  slots := h.slots
  evidence :=
    { sourceU_nonempty := h.sourceU_nonempty
      sourceW_nonempty := h.sourceW_nonempty
      triad_ne_zero := h.selectedTerm_eval_ne_zero
      firstFactorCircuit := h.firstFactorCircuit
      secondFactorCircuit := h.secondFactorCircuit
      firstCircuit_normalized := h.firstCircuit_normalized
      secondCircuit_normalized := h.secondCircuit_normalized
      firstClosure := h.firstClosure
      thirdClosure := h.thirdClosure }

/-- Recover an ordinary fixed-second-leg witness from source-labelled evidence before any leg
permutation. -/
def toWitness [Field k] [CharP k 2] {S : Scheme k a b c r} (h : SchemeWitness S) :
    Witness S where
  sourceU_nonempty := h.evidence.sourceU_nonempty
  sourceW_nonempty := h.evidence.sourceW_nonempty
  slots := h.slots
  selectedTerm_eval_ne_zero := h.evidence.triad_ne_zero
  firstFactorCircuit := h.evidence.firstFactorCircuit
  secondFactorCircuit := h.evidence.secondFactorCircuit
  firstCircuit_normalized := h.evidence.firstCircuit_normalized
  secondCircuit_normalized := h.evidence.secondCircuit_normalized
  firstClosure := h.evidence.firstClosure
  thirdClosure := h.evidence.thirdClosure

/-- Source-labelled scheme evidence proves its exact five-term family theorem. -/
theorem exact_family [Field k] [CharP k 2] {S : Scheme k a b c r}
    (h : SchemeWitness S) (s t : k) (hst : (1 + s) * (1 + t) = 1) :
    h.toWitness.factors.familyTensor s t = h.toWitness.factors.baseTensor :=
  h.toWitness.exact_family s t hst

/-- Exact T1 term reordering transports selected slots and every paired-circuit field. -/
def reorder [Field k] [CharP k 2] {S : Scheme k a b c r} (h : SchemeWitness S)
    (equiv : Fin r ≃ Fin r) : SchemeWitness (Action.reorder S equiv) where
  slots := h.slots.trans equiv.toEmbedding
  evidence := by
    simpa only [FiveFactorData.ofScheme, Action.reorder, Scheme.permute,
      Function.Embedding.trans_apply, Equiv.coe_toEmbedding, Equiv.symm_apply_apply]
      using h.evidence

end SchemeWitness

/-- Row-major two-sided matrix multiplication `U ↦ L*U*RInv` as a linear equivalence of
flattened factors, with inverse `U ↦ LInv*U*R`. -/
def matrixSandwichEquiv [Field k] (L LInv : Matrix (Fin a) (Fin a) k)
    (R RInv : Matrix (Fin b) (Fin b) k) (hLInvL : LInv * L = 1)
    (hLLInv : L * LInv = 1) (hRInvR : RInv * R = 1) (hRRInv : R * RInv = 1) :
    (Fin (a * b) → k) ≃ₗ[k] (Fin (a * b) → k) where
  toFun u := flattenMatrix (L * reshapeVector u * RInv)
  invFun u := flattenMatrix (LInv * reshapeVector u * R)
  left_inv u := by
    change flattenMatrix (LInv * reshapeVector (flattenMatrix
      (L * reshapeVector u * RInv)) * R) = u
    rw [show reshapeVector (flattenMatrix (L * reshapeVector u * RInv)) =
      L * reshapeVector u * RInv by
        exact (matrixVectorEquiv k a b).symm_apply_apply _]
    rw [show LInv * (L * reshapeVector u * RInv) * R =
      (LInv * L) * reshapeVector u * (RInv * R) by simp only [Matrix.mul_assoc]]
    rw [hLInvL, hRInvR, Matrix.one_mul, Matrix.mul_one]
    exact (matrixVectorEquiv k a b).apply_symm_apply u
  right_inv u := by
    change flattenMatrix (L * reshapeVector (flattenMatrix
      (LInv * reshapeVector u * R)) * RInv) = u
    rw [show reshapeVector (flattenMatrix (LInv * reshapeVector u * R)) =
      LInv * reshapeVector u * R by
        exact (matrixVectorEquiv k a b).symm_apply_apply _]
    rw [show L * (LInv * reshapeVector u * R) * RInv =
      (L * LInv) * reshapeVector u * (R * RInv) by simp only [Matrix.mul_assoc]]
    rw [hLLInv, hRRInv, Matrix.one_mul, Matrix.mul_one]
    exact (matrixVectorEquiv k a b).apply_symm_apply u
  map_add' u v := by
    change flattenMatrix (L * reshapeVector (u + v) * RInv) =
      flattenMatrix (L * reshapeVector u * RInv) +
        flattenMatrix (L * reshapeVector v * RInv)
    rw [show reshapeVector (u + v) = reshapeVector u + reshapeVector v by rfl]
    rw [Matrix.mul_add, Matrix.add_mul]
    rfl
  map_smul' s u := by
    change flattenMatrix (L * reshapeVector (s • u) * RInv) =
      s • flattenMatrix (L * reshapeVector u * RInv)
    rw [show reshapeVector (s • u) = s • reshapeVector u by rfl]
    rw [Matrix.mul_smul, Matrix.smul_mul]
    rfl

/-- A transpose is a linear equivalence between the two row-major rectangular shapes. -/
def transposeEquiv [Field k] (a b : ℕ) :
    (Fin (a * b) → k) ≃ₗ[k] (Fin (b * a) → k) where
  toFun := transposeFactor
  invFun := transposeFactor
  left_inv u := by
    apply (matrixVectorEquiv k a b).symm.injective
    ext i j
    simp only [reshapeVector, matrixVectorEquiv, transposeFactor, flattenMatrix,
      Matrix.transpose_apply, Equiv.symm_apply_apply]
  right_inv u := by
    apply (matrixVectorEquiv k b a).symm.injective
    ext i j
    simp only [reshapeVector, matrixVectorEquiv, transposeFactor, flattenMatrix,
      Matrix.transpose_apply, Equiv.symm_apply_apply]
  map_add' u v := rfl
  map_smul' s u := rfl

namespace SchemeWitness

/-- A T1 matrix sandwich transports all source-labelled circuit, minimality, and closure
evidence through its three invertible factor maps. -/
def sandwich [Field k] [CharP k 2] {S : MatrixScheme k n₁ n₂ n₃ r}
    (h : SchemeWitness S) (data : Sandwich k n₁ n₂ n₃) :
    SchemeWitness (Action.sandwich S data) where
  slots := h.slots
  evidence := by
    let eU := matrixSandwichEquiv data.P data.PInv data.Q data.QInv data.PInv_mul_P
      data.P_mul_PInv data.QInv_mul_Q data.Q_mul_QInv
    let eV := matrixSandwichEquiv data.Q data.QInv data.R data.RInv data.QInv_mul_Q
      data.Q_mul_QInv data.RInv_mul_R data.R_mul_RInv
    let eW := matrixSandwichEquiv data.R data.RInv data.P data.PInv data.RInv_mul_R
      data.R_mul_RInv data.PInv_mul_P data.P_mul_PInv
    change Evidence (mapData (FiveFactorData.ofScheme S h.slots) eU eV eW)
    exact h.evidence.map eU eV eW

end SchemeWitness

/-- The physical output leg occupied by a fixed source-labelled factor after orientation. -/
inductive OutputLeg where
  /-- The first physical output factor. -/
  | first
  /-- The second physical output factor. -/
  | second
  /-- The third physical output factor. -/
  | third
  deriving DecidableEq

/-- Track the fixed source `V` factor through each of the six outer orientations. -/
def sourceVLeg (orientation : Orientation) : OutputLeg :=
  match orientation with
  | .abc | .acb => .second
  | .bca | .cba => .first
  | .cab | .bac => .third

/-- The dimension of the source `U` factor after any transpose required by orientation. -/
def sourceUDim (orientation : Orientation) (n₁ n₂ : ℕ) : ℕ :=
  match orientation with
  | .abc | .bca | .cab => n₁ * n₂
  | .acb | .cba | .bac => n₂ * n₁

/-- The dimension of the source `V` factor after any transpose required by orientation. -/
def sourceVDim (orientation : Orientation) (n₂ n₃ : ℕ) : ℕ :=
  match orientation with
  | .abc | .bca | .cab => n₂ * n₃
  | .acb | .cba | .bac => n₃ * n₂

/-- The dimension of the source `W` factor after any transpose required by orientation. -/
def sourceWDim (orientation : Orientation) (n₃ n₁ : ℕ) : ℕ :=
  match orientation with
  | .abc | .bca | .cab => n₃ * n₁
  | .acb | .cba | .bac => n₁ * n₃

/-- Extract oriented factors in fixed source `U,V,W` labels rather than physical output order. -/
def orientedData (orientation : Orientation) (S : MatrixScheme k n₁ n₂ n₃ r)
    (slots : Fin 5 ↪ Fin r) :
    FiveFactorData k (sourceUDim orientation n₁ n₂) (sourceVDim orientation n₂ n₃)
      (sourceWDim orientation n₃ n₁) :=
  match orientation with
  | .abc => FiveFactorData.ofScheme (Action.orientMatrix .abc S) slots
  | .bca =>
      { U := fun q => ((Action.orientMatrix .bca S).term (slots q)).2.2
        V := fun q => ((Action.orientMatrix .bca S).term (slots q)).1
        W := fun q => ((Action.orientMatrix .bca S).term (slots q)).2.1 }
  | .cab =>
      { U := fun q => ((Action.orientMatrix .cab S).term (slots q)).2.1
        V := fun q => ((Action.orientMatrix .cab S).term (slots q)).2.2
        W := fun q => ((Action.orientMatrix .cab S).term (slots q)).1 }
  | .acb =>
      { U := fun q => ((Action.orientMatrix .acb S).term (slots q)).2.2
        V := fun q => ((Action.orientMatrix .acb S).term (slots q)).2.1
        W := fun q => ((Action.orientMatrix .acb S).term (slots q)).1 }
  | .cba =>
      { U := fun q => ((Action.orientMatrix .cba S).term (slots q)).2.1
        V := fun q => ((Action.orientMatrix .cba S).term (slots q)).1
        W := fun q => ((Action.orientMatrix .cba S).term (slots q)).2.2 }
  | .bac =>
      { U := fun q => ((Action.orientMatrix .bac S).term (slots q)).1
        V := fun q => ((Action.orientMatrix .bac S).term (slots q)).2.2
        W := fun q => ((Action.orientMatrix .bac S).term (slots q)).2.1 }

/-- The source-labelled dimensions for a representative odd orientation are the expected
transposed rectangular products. -/
theorem sourceDimensions_groundTruth :
    (sourceUDim .cba 2 3, sourceVDim .cba 3 5, sourceWDim .cba 5 2) =
      (6, 15, 10) := by
  rfl

/-- In orientation `cba`, the first physical output factor is precisely the transposed source
`V` factor. -/
theorem orientedData_cba_sourceV
    (S : MatrixScheme k n₁ n₂ n₃ r) (slots : Fin 5 ↪ Fin r) (q : Fin 5) :
    (orientedData .cba S slots).V q = transposeFactor (S.term (slots q)).2.1 := by
  rfl

/-- Complete evidence on an oriented T1 target, retained under fixed source factor labels. -/
structure OrientedWitness [Field k] [CharP k 2]
    (S : MatrixScheme k n₁ n₂ n₃ r) (orientation : Orientation) where
  /-- The five unchanged term positions in the oriented scheme. -/
  slots : Fin 5 ↪ Fin r
  /-- Every circuit, minimality, and closure fact in source-labelled oriented coordinates. -/
  evidence : Evidence (orientedData orientation S slots)

namespace SchemeWitness

/-- All six T1 matrix orientations transport complete evidence while explicitly tracking which
physical output leg contains the fixed source-`V` circuits. -/
def orientMatrix [Field k] [CharP k 2] {S : MatrixScheme k n₁ n₂ n₃ r}
    (h : SchemeWitness S) (orientation : Orientation) : OrientedWitness S orientation where
  slots := h.slots
  evidence := by
    cases orientation with
    | abc => exact h.evidence
    | bca => exact h.evidence
    | cab => exact h.evidence
    | acb =>
        exact h.evidence.map (transposeEquiv n₁ n₂) (transposeEquiv n₂ n₃)
          (transposeEquiv n₃ n₁)
    | cba =>
        exact h.evidence.map (transposeEquiv n₁ n₂) (transposeEquiv n₂ n₃)
          (transposeEquiv n₃ n₁)
    | bac =>
        exact h.evidence.map (transposeEquiv n₁ n₂) (transposeEquiv n₂ n₃)
          (transposeEquiv n₃ n₁)

end SchemeWitness

namespace OrientedWitness

/-- An oriented witness proves exact family constancy in fixed source labels for every one of the
six outer orientations. -/
theorem exact_family [Field k] [CharP k 2] {S : MatrixScheme k n₁ n₂ n₃ r}
    {orientation : Orientation} (h : OrientedWitness S orientation) (s t : k)
    (hst : (1 + s) * (1 + t) = 1) :
    (orientedData orientation S h.slots).familyTensor s t =
      (orientedData orientation S h.slots).baseTensor :=
  h.evidence.exact_family s t hst

end OrientedWitness

/-- The fixed source `V` circuit occupies the stated physical leg in all six orientations. -/
theorem sourceVLeg_allSix :
    ([sourceVLeg .abc, sourceVLeg .bca, sourceVLeg .cab,
      sourceVLeg .acb, sourceVLeg .cba, sourceVLeg .bac] : List OutputLeg) =
      [.second, .first, .third, .second, .first, .third] := by
  rfl

/-- The identity two-sided factor equivalence fixes every flattened factor. -/
theorem matrixSandwichEquiv_one [Field k] (u : Fin (a * b) → k) :
    matrixSandwichEquiv (1 : Matrix (Fin a) (Fin a) k) 1
      (1 : Matrix (Fin b) (Fin b) k) 1 (by simp only [Matrix.one_mul])
      (by simp only [Matrix.one_mul]) (by simp only [Matrix.one_mul])
      (by simp only [Matrix.one_mul]) u = u := by
  simp only [matrixSandwichEquiv, Matrix.one_mul, Matrix.mul_one]
  exact (matrixVectorEquiv k a b).apply_symm_apply u

/-- The binary five-mask source gives a concrete matrix-scheme action witness at shape `4×4×4`. -/
def binarySchemeWitness : SchemeWitness
    (show MatrixScheme BinaryFiveMask.F 4 4 4 5 from BinaryFiveMask.scheme) :=
  SchemeWitness.ofWitness BinaryFiveMask.witness

/-- The concrete binary witness transports through the identity T1 sandwich. -/
def binarySandwichWitness : SchemeWitness
    (Action.sandwich (show MatrixScheme BinaryFiveMask.F 4 4 4 5 from BinaryFiveMask.scheme)
      (Sandwich.one BinaryFiveMask.F 4 4 4)) :=
  binarySchemeWitness.sandwich (Sandwich.one BinaryFiveMask.F 4 4 4)

/-- The concrete binary witness transports through any of the six T1 outer orientations. -/
def binaryOrientedWitness (orientation : Orientation) : OrientedWitness
    (show MatrixScheme BinaryFiveMask.F 4 4 4 5 from BinaryFiveMask.scheme) orientation :=
  binarySchemeWitness.orientMatrix orientation

/-- All six concrete outer-orientation transports are jointly inhabited, including the three odd
orientations that transpose every source-labelled factor. -/
theorem binary_allSix_inhabited :
    Nonempty (OrientedWitness
      (show MatrixScheme BinaryFiveMask.F 4 4 4 5 from BinaryFiveMask.scheme) .abc) ∧
    Nonempty (OrientedWitness
      (show MatrixScheme BinaryFiveMask.F 4 4 4 5 from BinaryFiveMask.scheme) .bca) ∧
    Nonempty (OrientedWitness
      (show MatrixScheme BinaryFiveMask.F 4 4 4 5 from BinaryFiveMask.scheme) .cab) ∧
    Nonempty (OrientedWitness
      (show MatrixScheme BinaryFiveMask.F 4 4 4 5 from BinaryFiveMask.scheme) .acb) ∧
    Nonempty (OrientedWitness
      (show MatrixScheme BinaryFiveMask.F 4 4 4 5 from BinaryFiveMask.scheme) .cba) ∧
    Nonempty (OrientedWitness
      (show MatrixScheme BinaryFiveMask.F 4 4 4 5 from BinaryFiveMask.scheme) .bac) :=
  ⟨⟨binaryOrientedWitness .abc⟩, ⟨binaryOrientedWitness .bca⟩,
    ⟨binaryOrientedWitness .cab⟩, ⟨binaryOrientedWitness .acb⟩,
    ⟨binaryOrientedWitness .cba⟩, ⟨binaryOrientedWitness .bac⟩⟩

namespace PhysicalReplay

open Action Replacement

variable {k : Type*} {a b c n₁ n₂ n₃ : ℕ}

/-- Regard five source-labelled factor triples as a rank-five scheme in label order. -/
def sourceScheme (D : FiveFactorData k a b c) : Scheme k a b c 5 :=
  ⟨fun q => (D.U q, D.V q, D.W q)⟩

/-- The source-labelled scheme reads back the original factor data. -/
theorem sourceScheme_factors [CommRing k] (D : FiveFactorData k a b c) :
    FiveFactorData.ofScheme (sourceScheme D) (Function.Embedding.refl (Fin 5)) = D := by
  rfl

/-- Package source-labelled evidence as an ordinary witness on its rank-five scheme. -/
def evidenceSourceWitness [Field k] [CharP k 2] {D : FiveFactorData k a b c}
    (h : Evidence D) : Witness (sourceScheme D) where
  sourceU_nonempty := h.sourceU_nonempty
  sourceW_nonempty := h.sourceW_nonempty
  slots := Function.Embedding.refl (Fin 5)
  selectedTerm_eval_ne_zero := h.triad_ne_zero
  firstFactorCircuit := h.firstFactorCircuit
  secondFactorCircuit := h.secondFactorCircuit
  firstCircuit_normalized := h.firstCircuit_normalized
  secondCircuit_normalized := h.secondCircuit_normalized
  firstClosure := h.firstClosure
  thirdClosure := h.thirdClosure

/-- The packaged witness retains exactly the supplied source-labelled factor data. -/
theorem evidenceSourceWitness_factors [Field k] [CharP k 2]
    {D : FiveFactorData k a b c} (h : Evidence D) :
    (evidenceSourceWitness h).factors = D := by
  rfl

/-- Place source-labelled oriented factors into the physical output legs for all six vertex
orientations. The odd cases permute factors already transposed by `orientedData`. -/
def physicalSourceScheme [Field k] [CharP k 2]
    {S : MatrixScheme k n₁ n₂ n₃ 5} {orientation : Orientation}
    (h : OrientedWitness S orientation) :
    MatrixScheme k (orientation.firstDim n₁ n₂ n₃) (orientation.secondDim n₁ n₂ n₃)
      (orientation.thirdDim n₁ n₂ n₃) 5 :=
  match orientation with
  | .abc => sourceScheme (orientedData .abc S h.slots)
  | .bca => Action.orient .bca (sourceScheme (orientedData .bca S h.slots))
  | .cab => Action.orient .cab (sourceScheme (orientedData .cab S h.slots))
  | .acb => Action.orient .cba (sourceScheme (orientedData .acb S h.slots))
  | .cba => Action.orient .bac (sourceScheme (orientedData .cba S h.slots))
  | .bac => Action.orient .acb (sourceScheme (orientedData .bac S h.slots))

/-- Every physically placed source term is the corresponding selected term of the actual
`Action.orientMatrix` target; this statement checks all three projections in all six cases. -/
theorem physicalSourceScheme_term_eq [Field k] [CharP k 2]
    {S : MatrixScheme k n₁ n₂ n₃ 5} {orientation : Orientation}
    (h : OrientedWitness S orientation) (q : Fin 5) :
    (physicalSourceScheme h).term q =
      (Action.orientMatrix orientation S).term (h.slots q) := by
  cases orientation <;> rfl

/-- Every physically placed selected source term remains a nonzero rank-one tensor in all six
orientations. -/
theorem physicalSourceScheme_term_eval_ne_zero [Field k] [CharP k 2]
    {S : MatrixScheme k n₁ n₂ n₃ 5} {orientation : Orientation}
    (h : OrientedWitness S orientation) (q : Fin 5) :
    ((physicalSourceScheme h).term q).eval ≠ 0 := by
  have hfactors := factors_ne_zero_of_triad_ne_zero
    ((orientedData orientation S h.slots).U q)
    ((orientedData orientation S h.slots).V q)
    ((orientedData orientation S h.slots).W q)
    (h.evidence.triad_ne_zero q)
  cases orientation with
  | abc => exact triad_ne_zero_of_factors _ _ _ hfactors.1 hfactors.2.1 hfactors.2.2
  | bca => exact triad_ne_zero_of_factors _ _ _ hfactors.2.1 hfactors.2.2 hfactors.1
  | cab => exact triad_ne_zero_of_factors _ _ _ hfactors.2.2 hfactors.1 hfactors.2.1
  | acb => exact triad_ne_zero_of_factors _ _ _ hfactors.2.2 hfactors.2.1 hfactors.1
  | cba => exact triad_ne_zero_of_factors _ _ _ hfactors.2.1 hfactors.1 hfactors.2.2
  | bac => exact triad_ne_zero_of_factors _ _ _ hfactors.1 hfactors.2.2 hfactors.2.1

/-- The odd `acb` physical source term is `(Wᵀ,Vᵀ,Uᵀ)`. -/
theorem physicalSourceScheme_acb_term [Field k] [CharP k 2]
    {S : MatrixScheme k n₁ n₂ n₃ 5} (h : OrientedWitness S .acb) (q : Fin 5) :
    (physicalSourceScheme h).term q =
      (transposeFactor (S.term (h.slots q)).2.2,
        transposeFactor (S.term (h.slots q)).2.1,
        transposeFactor (S.term (h.slots q)).1) := by
  rfl

/-- The odd `cba` physical source term is `(Vᵀ,Uᵀ,Wᵀ)`. -/
theorem physicalSourceScheme_cba_term [Field k] [CharP k 2]
    {S : MatrixScheme k n₁ n₂ n₃ 5} (h : OrientedWitness S .cba) (q : Fin 5) :
    (physicalSourceScheme h).term q =
      (transposeFactor (S.term (h.slots q)).2.1,
        transposeFactor (S.term (h.slots q)).1,
        transposeFactor (S.term (h.slots q)).2.2) := by
  rfl

/-- The odd `bac` physical source term is `(Uᵀ,Wᵀ,Vᵀ)`. -/
theorem physicalSourceScheme_bac_term [Field k] [CharP k 2]
    {S : MatrixScheme k n₁ n₂ n₃ 5} (h : OrientedWitness S .bac) (q : Fin 5) :
    (physicalSourceScheme h).term q =
      (transposeFactor (S.term (h.slots q)).1,
        transposeFactor (S.term (h.slots q)).2.2,
        transposeFactor (S.term (h.slots q)).2.1) := by
  rfl

/-- Apply the normalized source-labelled five-term update and then place its factors in the
physical output legs selected by the vertex orientation. -/
def physicalFamilyScheme [Field k] [CharP k 2]
    {S : MatrixScheme k n₁ n₂ n₃ 5} {orientation : Orientation}
    (h : OrientedWitness S orientation) (s t : k) :
    MatrixScheme k (orientation.firstDim n₁ n₂ n₃) (orientation.secondDim n₁ n₂ n₃)
      (orientation.thirdDim n₁ n₂ n₃) 5 :=
  match orientation with
  | .abc => LocalReplay.familyScheme (evidenceSourceWitness h.evidence) s t
  | .bca => Action.orient .bca (LocalReplay.familyScheme (evidenceSourceWitness h.evidence) s t)
  | .cab => Action.orient .cab (LocalReplay.familyScheme (evidenceSourceWitness h.evidence) s t)
  | .acb => Action.orient .cba (LocalReplay.familyScheme (evidenceSourceWitness h.evidence) s t)
  | .cba => Action.orient .bac (LocalReplay.familyScheme (evidenceSourceWitness h.evidence) s t)
  | .bac => Action.orient .acb (LocalReplay.familyScheme (evidenceSourceWitness h.evidence) s t)

/-- The physically placed source-labelled scheme is the actual matrix-oriented source with its
five terms reordered into exact label order `a,b,c,d,e`. -/
theorem physicalSourceScheme_eq_reorder [Field k] [CharP k 2]
    {S : MatrixScheme k n₁ n₂ n₃ 5} {orientation : Orientation}
    (h : OrientedWitness S orientation) :
    physicalSourceScheme h =
      Action.reorder (Action.orientMatrix orientation S)
        (h.slots.equivOfFiniteSelfEmbedding.symm) := by
  cases orientation <;>
    apply congrArg (fun term => (⟨term⟩ : Scheme k _ _ _ 5)) <;>
    funext q <;>
    change (Action.orientMatrix _ S).term (h.slots q) =
      (Action.orientMatrix _ S).term (h.slots.equivOfFiniteSelfEmbedding q) <;>
    congr 2

/-- The physically placed source-labelled scheme has exactly the tensor of the actual physical
matrix orientation; source term labels affect order but not the represented tensor. -/
theorem physicalSourceScheme_sumTensor_eq [Field k] [CharP k 2]
    {S : MatrixScheme k n₁ n₂ n₃ 5} {orientation : Orientation}
    (h : OrientedWitness S orientation) :
    (physicalSourceScheme h).sumTensor = (Action.orientMatrix orientation S).sumTensor := by
  rw [physicalSourceScheme_eq_reorder h, Action.sumTensor_reorder]

/-- A rank-five scheme tensor is the finite sum of its evaluated stored terms. -/
theorem sumTensor_eq_sum_eval [CommSemiring k] (R : Scheme k a b c 5) :
    R.sumTensor = ∑ q, (R.term q).eval := by
  funext i j l
  simp only [sumTensor, Finset.sum_apply]

/-- The source-labelled normalized update scheme has the same tensor as its source-labelled
rank-five scheme. -/
theorem sourceFamilyScheme_sumTensor_eq [Field k] [CharP k 2]
    {D : FiveFactorData k a b c} (h : Evidence D) (s t : k)
    (hst : (1 + s) * (1 + t) = 1) :
    (LocalReplay.familyScheme (evidenceSourceWitness h) s t).sumTensor =
      (sourceScheme D).sumTensor := by
  calc
    (LocalReplay.familyScheme (evidenceSourceWitness h) s t).sumTensor =
        ∑ q, ((LocalReplay.familyScheme (evidenceSourceWitness h) s t).term q).eval :=
      sumTensor_eq_sum_eval _
    _ = D.familyTensor s t := by
      simpa only [evidenceSourceWitness_factors] using
        LocalReplay.family_sum_eq (evidenceSourceWitness h) s t
    _ = D.baseTensor := h.exact_family s t hst
    _ = ∑ q, ((sourceScheme D).term q).eval := by
      simpa only [evidenceSourceWitness_factors] using
        (LocalReplay.source_sum_eq_base (evidenceSourceWitness h)).symm
    _ = (sourceScheme D).sumTensor := (sumTensor_eq_sum_eval _).symm

/-- Applying the same abstract leg permutation to tensor-equal schemes preserves equality. -/
theorem orient_sumTensor_eq [Field k] {R T : Scheme k a b c 5}
    (orientation : Orientation) (hRT : R.sumTensor = T.sumTensor) :
    (Action.orient orientation R).sumTensor = (Action.orient orientation T).sumTensor := by
  rw [Action.sumTensor_orient, Action.sumTensor_orient, hRT]

/-- For every orientation, the normalized update in physical leg order has exactly the tensor of
the physically placed source-labelled terms. The proof checks all six factor permutations. -/
theorem physicalFamilyScheme_sumTensor_eq_physicalSource [Field k] [CharP k 2]
    {S : MatrixScheme k n₁ n₂ n₃ 5} {orientation : Orientation}
    (h : OrientedWitness S orientation) (s t : k)
    (hst : (1 + s) * (1 + t) = 1) :
    (physicalFamilyScheme h s t).sumTensor = (physicalSourceScheme h).sumTensor := by
  cases orientation with
  | abc =>
      exact sourceFamilyScheme_sumTensor_eq h.evidence s t hst
  | bca =>
      exact orient_sumTensor_eq .bca
        (sourceFamilyScheme_sumTensor_eq h.evidence s t hst)
  | cab =>
      exact orient_sumTensor_eq .cab
        (sourceFamilyScheme_sumTensor_eq h.evidence s t hst)
  | acb =>
      exact orient_sumTensor_eq .cba
        (sourceFamilyScheme_sumTensor_eq h.evidence s t hst)
  | cba =>
      exact orient_sumTensor_eq .bac
        (sourceFamilyScheme_sumTensor_eq h.evidence s t hst)
  | bac =>
      exact orient_sumTensor_eq .acb
        (sourceFamilyScheme_sumTensor_eq h.evidence s t hst)

/-- The physically ordered updated rank-five scheme represents the actual physical
`Action.orientMatrix` source tensor, not merely a source-order family tensor. -/
theorem physicalFamilyScheme_sumTensor_eq [Field k] [CharP k 2]
    {S : MatrixScheme k n₁ n₂ n₃ 5} {orientation : Orientation}
    (h : OrientedWitness S orientation) (s t : k)
    (hst : (1 + s) * (1 + t) = 1) :
    (physicalFamilyScheme h s t).sumTensor =
      (Action.orientMatrix orientation S).sumTensor :=
  (physicalFamilyScheme_sumTensor_eq_physicalSource h s t hst).trans
    (physicalSourceScheme_sumTensor_eq h)

/-- The insertion list records the five physically ordered updated terms in exact source-label
order `a,b,c,d,e`. -/
def physicalFamilyList [Field k] [CharP k 2]
    {S : MatrixScheme k n₁ n₂ n₃ 5} {orientation : Orientation}
    (h : OrientedWitness S orientation) (s t : k) :
    List (TriadData k ((orientation.firstDim n₁ n₂ n₃) *
        (orientation.secondDim n₁ n₂ n₃))
      ((orientation.secondDim n₁ n₂ n₃) * (orientation.thirdDim n₁ n₂ n₃))
      ((orientation.thirdDim n₁ n₂ n₃) * (orientation.firstDim n₁ n₂ n₃))) :=
  [(physicalFamilyScheme h s t).term 0, (physicalFamilyScheme h s t).term 1,
    (physicalFamilyScheme h s t).term 2, (physicalFamilyScheme h s t).term 3,
    (physicalFamilyScheme h s t).term 4]

/-- The physical insertion list contains exactly five source-labelled terms. -/
theorem physicalFamilyList_length [Field k] [CharP k 2]
    {S : MatrixScheme k n₁ n₂ n₃ 5} {orientation : Orientation}
    (h : OrientedWitness S orientation) (s t : k) :
    (physicalFamilyList h s t).length = 5 := by
  rfl

/-- The insertion-list tensor is exactly the tensor of the physically ordered family scheme. -/
theorem insertedTensor_physicalFamilyList [Field k] [CharP k 2]
    {S : MatrixScheme k n₁ n₂ n₃ 5} {orientation : Orientation}
    (h : OrientedWitness S orientation) (s t : k) :
    insertedTensor (physicalFamilyList h s t) = (physicalFamilyScheme h s t).sumTensor := by
  funext i j l
  simp only [physicalFamilyList, insertedTensor, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, sumTensor, Fin.sum_univ_five, Pi.add_apply]
  ac_rfl

/-- Selecting all slots of a rank-five scheme recovers its represented tensor. -/
theorem selectedTensor_univ_eq_sumTensor [CommSemiring k] (R : Scheme k a b c 5) :
    selectedTensor R Finset.univ = R.sumTensor := by
  funext i j l
  simp [selectedTensor, sumTensor]

/-- A replayable rank-five certificate removes the actual physical oriented source and inserts
the five normalized updated terms in physical factor order and exact source-label order. -/
def certificate [Field k] [CharP k 2]
    {S : MatrixScheme k n₁ n₂ n₃ 5} {orientation : Orientation}
    (h : OrientedWitness S orientation) (s t : k)
    (hst : (1 + s) * (1 + t) = 1) :
    Replacement.Certificate (Action.orientMatrix orientation S) where
  removed := Finset.univ
  inserted := physicalFamilyList h s t
  local_eq := by
    calc
      selectedTensor (Action.orientMatrix orientation S) Finset.univ =
          (Action.orientMatrix orientation S).sumTensor :=
        selectedTensor_univ_eq_sumTensor _
      _ = (physicalFamilyScheme h s t).sumTensor :=
        (physicalFamilyScheme_sumTensor_eq h s t hst).symm
      _ = insertedTensor (physicalFamilyList h s t) :=
        (insertedTensor_physicalFamilyList h s t).symm

/-- The physical replay certificate removes and inserts exactly five terms and therefore has
result rank five. -/
theorem certificate_rank_five [Field k] [CharP k 2]
    {S : MatrixScheme k n₁ n₂ n₃ 5} {orientation : Orientation}
    (h : OrientedWitness S orientation) (s t : k)
    (hst : (1 + s) * (1 + t) = 1) :
    (certificate h s t hst).removed.card = 5 ∧
      (certificate h s t hst).inserted.length = 5 ∧
      (certificate h s t hst).resultRank = 5 := by
  simp [certificate, physicalFamilyList, Replacement.Certificate.resultRank]

/-- The deterministic certificate output is the physically ordered normalized family scheme. -/
theorem certificate_output_eq_physicalFamilyScheme [Field k] [CharP k 2]
    {S : MatrixScheme k n₁ n₂ n₃ 5} {orientation : Orientation}
    (h : OrientedWitness S orientation) (s t : k)
    (hst : (1 + s) * (1 + t) = 1) :
    (certificate h s t hst).output = physicalFamilyScheme h s t := by
  apply congrArg
    (fun term => (⟨term⟩ : MatrixScheme k (orientation.firstDim n₁ n₂ n₃)
      (orientation.secondDim n₁ n₂ n₃) (orientation.thirdDim n₁ n₂ n₃) 5))
  funext q
  fin_cases q <;> rfl

/-- Certificate replay proves that its physically ordered output represents the actual physical
matrix-oriented source tensor. -/
theorem certificate_output_sumTensor_eq [Field k] [CharP k 2]
    {S : MatrixScheme k n₁ n₂ n₃ 5} {orientation : Orientation}
    (h : OrientedWitness S orientation) (s t : k)
    (hst : (1 + s) * (1 + t) = 1) :
    (certificate h s t hst).output.sumTensor =
      (Action.orientMatrix orientation S).sumTensor :=
  (certificate h s t hst).sumTensor_eq

/-- The concrete binary fixture jointly inhabits physical replay certificates for all six
orientations. -/
theorem binary_allSix_certificates :
    Nonempty (Replacement.Certificate (Action.orientMatrix .abc
      (show MatrixScheme BinaryFiveMask.F 4 4 4 5 from BinaryFiveMask.scheme))) ∧
    Nonempty (Replacement.Certificate (Action.orientMatrix .bca
      (show MatrixScheme BinaryFiveMask.F 4 4 4 5 from BinaryFiveMask.scheme))) ∧
    Nonempty (Replacement.Certificate (Action.orientMatrix .cab
      (show MatrixScheme BinaryFiveMask.F 4 4 4 5 from BinaryFiveMask.scheme))) ∧
    Nonempty (Replacement.Certificate (Action.orientMatrix .acb
      (show MatrixScheme BinaryFiveMask.F 4 4 4 5 from BinaryFiveMask.scheme))) ∧
    Nonempty (Replacement.Certificate (Action.orientMatrix .cba
      (show MatrixScheme BinaryFiveMask.F 4 4 4 5 from BinaryFiveMask.scheme))) ∧
    Nonempty (Replacement.Certificate (Action.orientMatrix .bac
      (show MatrixScheme BinaryFiveMask.F 4 4 4 5 from BinaryFiveMask.scheme))) := by
  exact ⟨⟨certificate (binaryOrientedWitness .abc) 0 0 (by decide)⟩,
    ⟨certificate (binaryOrientedWitness .bca) 0 0 (by decide)⟩,
    ⟨certificate (binaryOrientedWitness .cab) 0 0 (by decide)⟩,
    ⟨certificate (binaryOrientedWitness .acb) 0 0 (by decide)⟩,
    ⟨certificate (binaryOrientedWitness .cba) 0 0 (by decide)⟩,
    ⟨certificate (binaryOrientedWitness .bac) 0 0 (by decide)⟩⟩

/-- The concrete binary fixture satisfies the physical tensor theorem in all six orientations. -/
theorem binary_allSix_physical_sumTensor :
    (physicalFamilyScheme (binaryOrientedWitness .abc) 0 0).sumTensor =
        (Action.orientMatrix .abc
          (show MatrixScheme BinaryFiveMask.F 4 4 4 5 from BinaryFiveMask.scheme)).sumTensor ∧
    (physicalFamilyScheme (binaryOrientedWitness .bca) 0 0).sumTensor =
        (Action.orientMatrix .bca
          (show MatrixScheme BinaryFiveMask.F 4 4 4 5 from BinaryFiveMask.scheme)).sumTensor ∧
    (physicalFamilyScheme (binaryOrientedWitness .cab) 0 0).sumTensor =
        (Action.orientMatrix .cab
          (show MatrixScheme BinaryFiveMask.F 4 4 4 5 from BinaryFiveMask.scheme)).sumTensor ∧
    (physicalFamilyScheme (binaryOrientedWitness .acb) 0 0).sumTensor =
        (Action.orientMatrix .acb
          (show MatrixScheme BinaryFiveMask.F 4 4 4 5 from BinaryFiveMask.scheme)).sumTensor ∧
    (physicalFamilyScheme (binaryOrientedWitness .cba) 0 0).sumTensor =
        (Action.orientMatrix .cba
          (show MatrixScheme BinaryFiveMask.F 4 4 4 5 from BinaryFiveMask.scheme)).sumTensor ∧
    (physicalFamilyScheme (binaryOrientedWitness .bac) 0 0).sumTensor =
        (Action.orientMatrix .bac
          (show MatrixScheme BinaryFiveMask.F 4 4 4 5 from BinaryFiveMask.scheme)).sumTensor := by
  exact ⟨physicalFamilyScheme_sumTensor_eq (binaryOrientedWitness .abc) 0 0 (by decide),
    physicalFamilyScheme_sumTensor_eq (binaryOrientedWitness .bca) 0 0 (by decide),
    physicalFamilyScheme_sumTensor_eq (binaryOrientedWitness .cab) 0 0 (by decide),
    physicalFamilyScheme_sumTensor_eq (binaryOrientedWitness .acb) 0 0 (by decide),
    physicalFamilyScheme_sumTensor_eq (binaryOrientedWitness .cba) 0 0 (by decide),
    physicalFamilyScheme_sumTensor_eq (binaryOrientedWitness .bac) 0 0 (by decide)⟩

/-- Every selected concrete physical source term is nonzero jointly in all six orientations. -/
theorem binary_allSix_physical_supported (q : Fin 5) :
    ((physicalSourceScheme (binaryOrientedWitness .abc)).term q).eval ≠ 0 ∧
    ((physicalSourceScheme (binaryOrientedWitness .bca)).term q).eval ≠ 0 ∧
    ((physicalSourceScheme (binaryOrientedWitness .cab)).term q).eval ≠ 0 ∧
    ((physicalSourceScheme (binaryOrientedWitness .acb)).term q).eval ≠ 0 ∧
    ((physicalSourceScheme (binaryOrientedWitness .cba)).term q).eval ≠ 0 ∧
    ((physicalSourceScheme (binaryOrientedWitness .bac)).term q).eval ≠ 0 := by
  exact ⟨physicalSourceScheme_term_eval_ne_zero (binaryOrientedWitness .abc) q,
    physicalSourceScheme_term_eval_ne_zero (binaryOrientedWitness .bca) q,
    physicalSourceScheme_term_eval_ne_zero (binaryOrientedWitness .cab) q,
    physicalSourceScheme_term_eval_ne_zero (binaryOrientedWitness .acb) q,
    physicalSourceScheme_term_eval_ne_zero (binaryOrientedWitness .cba) q,
    physicalSourceScheme_term_eval_ne_zero (binaryOrientedWitness .bac) q⟩

end PhysicalReplay

end ActionTransport

example : ((1 + 0) * (1 + 0) : ZMod 2) = 1 := by
  norm_num

#check @ThreeCircuit
#check @factors_ne_zero_of_triad_ne_zero
#check @triad_ne_zero_of_factors
#check @triad_map_ne_zero
#check @Witness
#check @Witness.exact_family
#check @Witness.reorder
#check @LocalReplay.certificate
#check @LocalReplay.certificate_output_eq_family
#check @LocalReplay.binaryCertificate
#check @ActionTransport.Evidence.map
#check @ActionTransport.SchemeWitness.sandwich
#check @ActionTransport.SchemeWitness.orientMatrix
#check @ActionTransport.sourceVLeg_allSix
#check @ActionTransport.PhysicalReplay.physicalSourceScheme_term_eq
#check @ActionTransport.PhysicalReplay.physicalSourceScheme_term_eval_ne_zero
#check @ActionTransport.PhysicalReplay.physicalSourceScheme_eq_reorder
#check @ActionTransport.PhysicalReplay.physicalFamilyScheme_sumTensor_eq
#check @ActionTransport.PhysicalReplay.certificate
#check @ActionTransport.PhysicalReplay.certificate_output_sumTensor_eq
#check @ActionTransport.PhysicalReplay.binary_allSix_certificates
#check @ActionTransport.PhysicalReplay.binary_allSix_physical_supported
#check @BinaryFiveMask.witness
#check @BinaryFiveMask.sourceTerms_eval_ne_zero
#check @BinaryFiveMaskRatFunc.factors_decode_sourceMasks
#check @BinaryFiveMaskRatFunc.sourceTerms_eval_ne_zero
#check @BinaryFiveMaskRatFunc.nontrivial_replacement_certificate
#check @BinaryFiveMaskRatFunc.sameMasks_nontrivial_replacement_fixture

#print axioms torus_iff_scalarCancellation
#print axioms eq_field_inv_iff
#print axioms solutionEquivUnits
#print axioms ThreeCircuit.map
#print axioms triad_map_ne_zero
#print axioms FiveFactorData.exact_expansion
#print axioms Witness.normalized_certificate
#print axioms Witness.exact_family
#print axioms BinaryFiveMask.genuine_minimality
#print axioms BinaryFiveMask.sourceTerms_eval_ne_zero
#print axioms BinaryFiveMask.exact_family
#print axioms LocalReplay.binaryCertificate_fixture
#print axioms LocalReplay.symmetryCertificate
#print axioms BinaryFiveMaskRatFunc.sameMasks_nontrivial_replacement_fixture
#print axioms ActionTransport.Evidence.map
#print axioms ActionTransport.matrixSandwichEquiv
#print axioms ActionTransport.SchemeWitness.sandwich
#print axioms ActionTransport.SchemeWitness.orientMatrix
#print axioms ActionTransport.binary_allSix_inhabited
#print axioms ActionTransport.target_nonempty_of_linearEquiv
#print axioms ActionTransport.PhysicalReplay.physicalSourceScheme_term_eq
#print axioms ActionTransport.PhysicalReplay.physicalSourceScheme_term_eval_ne_zero
#print axioms ActionTransport.PhysicalReplay.physicalSourceScheme_eq_reorder
#print axioms ActionTransport.PhysicalReplay.physicalFamilyScheme_sumTensor_eq
#print axioms ActionTransport.PhysicalReplay.certificate
#print axioms ActionTransport.PhysicalReplay.certificate_output_sumTensor_eq
#print axioms ActionTransport.PhysicalReplay.binary_allSix_certificates
#print axioms ActionTransport.PhysicalReplay.binary_allSix_physical_sumTensor
#print axioms ActionTransport.PhysicalReplay.binary_allSix_physical_supported

end PairedCircuit
end Scheme
end BilinearComplexity
