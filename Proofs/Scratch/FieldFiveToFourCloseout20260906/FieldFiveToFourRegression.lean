import BilinearComplexity.FieldFiveToFour
import BilinearComplexity.FieldNativeExecutablePath
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators

namespace BilinearComplexity
namespace FieldFiveToFourRegressionScratch

open FieldRankOne FieldContextual FieldNativeMoves FieldNativePath
open FieldFiveCircuitProfile FieldCircuitContraction FieldNativePairBridge
open FieldFiveToFour

abbrev F3 := FieldFiveToFour.F3

/-- One of the first four coordinate vectors in the five-dimensional ambient space. -/
def basisVector (i : Fin 4) : Fin 5 → F3 := fun j => if j.val = i.val then 1 else 0

/-- Four coordinate vectors followed by a full-support vector with prescribed first four entries. -/
def varyingFamily (r : Fin 4 → F3) : Fin 5 → Fin 5 → F3 :=
  ![basisVector 0, basisVector 1, basisVector 2, basisVector 3,
    ![r 0, r 1, r 2, r 3, 0]]

/-- The constant nonzero one-dimensional factor family. -/
def oneFamily : Fin 5 → Fin 1 → F3 := fun _ _ => 1

example : varyingFamily ![(1 : F3), 1, -1, -1] 4 0 = 1 := rfl
example : oneFamily 0 0 = 1 := rfl

/-- Every first factor is nonzero when the four entries of the fifth are nonzero. -/
theorem varyingFamily_ne (r : Fin 4 → F3) (hr : ∀ i, r i ≠ 0) :
    ∀ i, varyingFamily r i ≠ 0 := by
  intro i hi
  fin_cases i
  · have h := congrFun hi 0
    norm_num [varyingFamily, basisVector] at h
  · have h := congrFun hi 1
    norm_num [varyingFamily, basisVector] at h
  · have h := congrFun hi 2
    norm_num [varyingFamily, basisVector] at h
  · have h := congrFun hi 3
    norm_num [varyingFamily, basisVector] at h
  · exact hr 0 (by simpa [varyingFamily] using congrFun hi 0)

/-- Every constant one-dimensional factor is nonzero. -/
theorem oneFamily_ne : ∀ i, oneFamily i ≠ 0 := by
  intro i hi
  have h := congrFun hi 0
  norm_num [oneFamily] at h

/-- A product term in this fixture evaluates to its varying first factor. -/
@[simp] theorem productFamily_varying_apply (r : Fin 4 → F3)
    (i : Fin 5) (p : Fin 5) (q s : Fin 1) :
    productFamily (varyingFamily r) oneFamily oneFamily i p q s = varyingFamily r i p := by
  simp [productFamily, evalFactors, oneFamily]

/-- The four coordinate equations forced by a relation among the five fixture terms. -/
theorem relation_coordinates (r : Fin 4 → F3) (u : Fin 5 → F3)
    (h : IsProductRelation (varyingFamily r) oneFamily oneFamily u) :
    u 0 + u 4 * r 0 = 0 ∧ u 1 + u 4 * r 1 = 0 ∧
      u 2 + u 4 * r 2 = 0 ∧ u 3 + u 4 * r 3 = 0 := by
  unfold IsProductRelation at h
  have h0 := congrFun (congrFun (congrFun h 0) 0) 0
  have h1 := congrFun (congrFun (congrFun h 1) 0) 0
  have h2 := congrFun (congrFun (congrFun h 2) 0) 0
  have h3 := congrFun (congrFun (congrFun h 3) 0) 0
  simp [productFamily, evalFactors, varyingFamily, basisVector, oneFamily,
    Fin.sum_univ_succ] at h0 h1 h2 h3
  exact ⟨h0, h1, h2, h3⟩

/-- These five terms form a minimal circuit whenever the fifth vector has four nonzero entries. -/
theorem fixture_minimal (r : Fin 4 → F3) (hr : ∀ i, r i ≠ 0) :
    IsMinimalFiveProductCircuit (varyingFamily r) oneFamily oneFamily := by
  constructor
  · let u : Fin 5 → F3 := ![-r 0, -r 1, -r 2, -r 3, 1]
    refine ⟨u, ?_, ?_⟩
    · intro hu
      have h : (1 : F3) = 0 := by simpa [u] using congrFun hu 4
      exact one_ne_zero h
    · unfold IsProductRelation
      funext p q s
      fin_cases p <;> fin_cases q <;> fin_cases s <;>
        simp [u, productFamily, evalFactors, varyingFamily, basisVector, oneFamily,
          Fin.sum_univ_succ]
  · intro u hrel hz
    obtain ⟨h0, h1, h2, h3⟩ := relation_coordinates r u hrel
    obtain ⟨i, hi⟩ := hz
    have h4 : u 4 = 0 := by
      fin_cases i
      · have hi0 : u 0 = 0 := by simpa using hi
        have hp := h0
        rw [hi0, zero_add] at hp
        exact (mul_eq_zero.mp hp).resolve_right (hr 0)
      · have hi1 : u 1 = 0 := by simpa using hi
        have hp := h1
        rw [hi1, zero_add] at hp
        exact (mul_eq_zero.mp hp).resolve_right (hr 1)
      · have hi2 : u 2 = 0 := by simpa using hi
        have hp := h2
        rw [hi2, zero_add] at hp
        exact (mul_eq_zero.mp hp).resolve_right (hr 2)
      · have hi3 : u 3 = 0 := by simpa using hi
        have hp := h3
        rw [hi3, zero_add] at hp
        exact (mul_eq_zero.mp hp).resolve_right (hr 3)
      · exact hi
    funext j
    fin_cases j
    · simpa [h4] using h0
    · simpa [h4] using h1
    · simpa [h4] using h2
    · simpa [h4] using h3
    · exact h4


/-- Row for source slots zero and one. -/
def row01 : Fin 4 → F3 := ![1, 1, -1, -1]

/-- Row for source slots two and three. -/
def row23 : Fin 4 → F3 := ![-1, -1, 1, 1]

/-- Row for source slots zero and two. -/
def row02 : Fin 4 → F3 := ![1, -1, 1, -1]

/-- Row for source slots one and two. -/
def row12 : Fin 4 → F3 := ![-1, 1, 1, -1]

/-- Every declared fifth-vector coordinate is nonzero. -/
theorem row_ne :
    (∀ i, row01 i ≠ 0) ∧ (∀ i, row23 i ≠ 0) ∧
      (∀ i, row02 i ≠ 0) ∧ (∀ i, row12 i ≠ 0) := by
  constructor
  · intro i
    fin_cases i <;> decide
  constructor
  · intro i
    fin_cases i <;> decide
  constructor <;> intro i <;> fin_cases i <;> decide

/-- Display slots for source subset `{0,1}`. -/
def slots01 : Fin 2 ⊕ Fin 3 ≃ Fin 5 := finSumFinEquiv

/-- Display slots for source subset `{2,3}`. -/
def slots23 : Fin 2 ⊕ Fin 3 ≃ Fin 5 := finSumFinEquiv.trans {
  toFun := ![2, 3, 0, 1, 4]
  invFun := ![2, 3, 0, 1, 4]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl }

/-- Display slots for source subset `{0,2}`. -/
def slots02 : Fin 2 ⊕ Fin 3 ≃ Fin 5 := finSumFinEquiv.trans {
  toFun := ![0, 2, 1, 3, 4]
  invFun := ![0, 2, 1, 3, 4]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl }

/-- Display slots for source subset `{1,2}`. -/
def slots12 : Fin 2 ⊕ Fin 3 ≃ Fin 5 := finSumFinEquiv.trans {
  toFun := ![1, 2, 0, 3, 4]
  invFun := ![2, 0, 1, 3, 4]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl }

/-- The four concrete rows and slot maps satisfy their displayed endpoint equality. -/
theorem vector_balances :
    (∑ i : Fin 2, varyingFamily row01 (slots01 (.inl i))) =
        ∑ j : Fin 3, varyingFamily row01 (slots01 (.inr j)) ∧
    (∑ i : Fin 2, varyingFamily row23 (slots23 (.inl i))) =
        ∑ j : Fin 3, varyingFamily row23 (slots23 (.inr j)) ∧
    (∑ i : Fin 2, varyingFamily row02 (slots02 (.inl i))) =
        ∑ j : Fin 3, varyingFamily row02 (slots02 (.inr j)) ∧
    (∑ i : Fin 2, varyingFamily row12 (slots12 (.inl i))) =
        ∑ j : Fin 3, varyingFamily row12 (slots12 (.inr j)) := by
  constructor
  · funext p
    fin_cases p <;>
      decide +kernel
  constructor
  · funext p
    fin_cases p <;>
      decide +kernel
  constructor <;> funext p <;> fin_cases p <;> decide +kernel

/-- A vector endpoint equality gives the corresponding tensor endpoint equality when the first
factor varies. -/
theorem first_eval_eq (r : Fin 4 → F3) (slots : Fin 2 ⊕ Fin 3 ≃ Fin 5)
    (h : (∑ i : Fin 2, varyingFamily r (slots (.inl i))) =
      ∑ j : Fin 3, varyingFamily r (slots (.inr j))) :
    (∑ i : Fin 2, productFamily (varyingFamily r) oneFamily oneFamily (slots (.inl i))) =
      ∑ j : Fin 3, productFamily (varyingFamily r) oneFamily oneFamily (slots (.inr j)) := by
  funext p q s
  simpa only [Finset.sum_apply, productFamily_varying_apply] using congrFun h p

/-- A vector endpoint equality gives the corresponding tensor endpoint equality when the second
factor varies. -/
theorem second_eval_eq (r : Fin 4 → F3) (slots : Fin 2 ⊕ Fin 3 ≃ Fin 5)
    (h : (∑ i : Fin 2, varyingFamily r (slots (.inl i))) =
      ∑ j : Fin 3, varyingFamily r (slots (.inr j))) :
    (∑ i : Fin 2, productFamily oneFamily (varyingFamily r) oneFamily (slots (.inl i))) =
      ∑ j : Fin 3, productFamily oneFamily (varyingFamily r) oneFamily (slots (.inr j)) := by
  funext p q s
  simpa only [productFamily, evalFactors, oneFamily, one_mul, mul_one, Finset.sum_apply] using
    congrFun h q

/-- A vector endpoint equality gives the corresponding tensor endpoint equality when the third
factor varies. -/
theorem third_eval_eq (r : Fin 4 → F3) (slots : Fin 2 ⊕ Fin 3 ≃ Fin 5)
    (h : (∑ i : Fin 2, varyingFamily r (slots (.inl i))) =
      ∑ j : Fin 3, varyingFamily r (slots (.inr j))) :
    (∑ i : Fin 2, productFamily oneFamily oneFamily (varyingFamily r) (slots (.inl i))) =
      ∑ j : Fin 3, productFamily oneFamily oneFamily (varyingFamily r) (slots (.inr j)) := by
  funext p q s
  simpa only [productFamily, evalFactors, oneFamily, one_mul, Finset.sum_apply] using congrFun h s

/-- Moving the varying family from the first to the second mode preserves exactly the
coefficient relations. -/
theorem relation_first_second_iff (r : Fin 4 → F3) (u : Fin 5 → F3) :
    IsProductRelation (varyingFamily r) oneFamily oneFamily u ↔
      IsProductRelation oneFamily (varyingFamily r) oneFamily u := by
  constructor
  · intro h
    unfold IsProductRelation at h ⊢
    funext p q s
    have hc := congrFun (congrFun (congrFun h q) p) s
    simpa [evalFactors, oneFamily] using hc
  · intro h
    unfold IsProductRelation at h ⊢
    funext p q s
    have hc := congrFun (congrFun (congrFun h q) p) s
    simpa [evalFactors, oneFamily] using hc

/-- Moving the varying family from the first to the third mode preserves exactly the
coefficient relations. -/
theorem relation_first_third_iff (r : Fin 4 → F3) (u : Fin 5 → F3) :
    IsProductRelation (varyingFamily r) oneFamily oneFamily u ↔
      IsProductRelation oneFamily oneFamily (varyingFamily r) u := by
  constructor
  · intro h
    unfold IsProductRelation at h ⊢
    funext p q s
    have hc := congrFun (congrFun (congrFun h s) p) q
    simpa [evalFactors, oneFamily] using hc
  · intro h
    unfold IsProductRelation at h ⊢
    funext p q s
    have hc := congrFun (congrFun (congrFun h q) s) p
    simpa [evalFactors, oneFamily] using hc

/-- Minimality is invariant under moving this fixture's varying family to the second mode. -/
theorem fixture_minimal_second (r : Fin 4 → F3) (hr : ∀ i, r i ≠ 0) :
    IsMinimalFiveProductCircuit oneFamily (varyingFamily r) oneFamily := by
  obtain ⟨hexists, hvanish⟩ := fixture_minimal r hr
  constructor
  · obtain ⟨u, hune, hrel⟩ := hexists
    exact ⟨u, hune, (relation_first_second_iff r u).mp hrel⟩
  · intro u hrel hz
    exact hvanish u ((relation_first_second_iff r u).mpr hrel) hz

/-- Minimality is invariant under moving this fixture's varying family to the third mode. -/
theorem fixture_minimal_third (r : Fin 4 → F3) (hr : ∀ i, r i ≠ 0) :
    IsMinimalFiveProductCircuit oneFamily oneFamily (varyingFamily r) := by
  obtain ⟨hexists, hvanish⟩ := fixture_minimal r hr
  constructor
  · obtain ⟨u, hune, hrel⟩ := hexists
    exact ⟨u, hune, (relation_first_third_iff r u).mp hrel⟩
  · intro u hrel hz
    exact hvanish u ((relation_first_third_iff r u).mpr hrel) hz

/-- Build one first-mode-varying displayed fixture from checked row data. -/
def firstFixture (r : Fin 4 → F3) (slots : Fin 2 ⊕ Fin 3 ≃ Fin 5)
    (hr : ∀ i, r i ≠ 0)
    (h : (∑ i : Fin 2, varyingFamily r (slots (.inl i))) =
      ∑ j : Fin 3, varyingFamily r (slots (.inr j))) :
    DisplayedF3PairTriple 5 1 1 where
  x := varyingFamily r
  y := oneFamily
  z := oneFamily
  x_ne := varyingFamily_ne r hr
  y_ne := oneFamily_ne
  z_ne := oneFamily_ne
  slots := slots
  eval_eq := first_eval_eq r slots h
  minimal := fixture_minimal r hr

/-- Build the same displayed fixture with its varying family in the second mode. -/
def secondFixture (r : Fin 4 → F3) (slots : Fin 2 ⊕ Fin 3 ≃ Fin 5)
    (hr : ∀ i, r i ≠ 0)
    (h : (∑ i : Fin 2, varyingFamily r (slots (.inl i))) =
      ∑ j : Fin 3, varyingFamily r (slots (.inr j))) :
    DisplayedF3PairTriple 1 5 1 where
  x := oneFamily
  y := varyingFamily r
  z := oneFamily
  x_ne := oneFamily_ne
  y_ne := varyingFamily_ne r hr
  z_ne := oneFamily_ne
  slots := slots
  eval_eq := second_eval_eq r slots h
  minimal := fixture_minimal_second r hr

/-- Build the same displayed fixture with its varying family in the third mode. -/
def thirdFixture (r : Fin 4 → F3) (slots : Fin 2 ⊕ Fin 3 ≃ Fin 5)
    (hr : ∀ i, r i ≠ 0)
    (h : (∑ i : Fin 2, varyingFamily r (slots (.inl i))) =
      ∑ j : Fin 3, varyingFamily r (slots (.inr j))) :
    DisplayedF3PairTriple 1 1 5 where
  x := oneFamily
  y := oneFamily
  z := varyingFamily r
  x_ne := oneFamily_ne
  y_ne := oneFamily_ne
  z_ne := varyingFamily_ne r hr
  slots := slots
  eval_eq := third_eval_eq r slots h
  minimal := fixture_minimal_third r hr


/-- First-mode source/source fixture in ambient dimensions `(5,1,1)`. -/
def first01 : DisplayedF3PairTriple 5 1 1 :=
  firstFixture row01 slots01 row_ne.1 vector_balances.1

/-- First-mode target/target fixture in ambient dimensions `(5,1,1)`. -/
def first23 : DisplayedF3PairTriple 5 1 1 :=
  firstFixture row23 slots23 row_ne.2.1 vector_balances.2.1

/-- First-mode forward-opposite fixture in ambient dimensions `(5,1,1)`. -/
def first02 : DisplayedF3PairTriple 5 1 1 :=
  firstFixture row02 slots02 row_ne.2.2.1 vector_balances.2.2.1

/-- First-mode reverse-opposite fixture in ambient dimensions `(5,1,1)`. -/
def first12 : DisplayedF3PairTriple 5 1 1 :=
  firstFixture row12 slots12 row_ne.2.2.2 vector_balances.2.2.2

/-- Second-mode source/source fixture in ambient dimensions `(1,5,1)`. -/
def second01 : DisplayedF3PairTriple 1 5 1 :=
  secondFixture row01 slots01 row_ne.1 vector_balances.1

/-- Second-mode target/target fixture in ambient dimensions `(1,5,1)`. -/
def second23 : DisplayedF3PairTriple 1 5 1 :=
  secondFixture row23 slots23 row_ne.2.1 vector_balances.2.1

/-- Second-mode forward-opposite fixture in ambient dimensions `(1,5,1)`. -/
def second02 : DisplayedF3PairTriple 1 5 1 :=
  secondFixture row02 slots02 row_ne.2.2.1 vector_balances.2.2.1

/-- Second-mode reverse-opposite fixture in ambient dimensions `(1,5,1)`. -/
def second12 : DisplayedF3PairTriple 1 5 1 :=
  secondFixture row12 slots12 row_ne.2.2.2 vector_balances.2.2.2

/-- Third-mode source/source fixture in ambient dimensions `(1,1,5)`. -/
def third01 : DisplayedF3PairTriple 1 1 5 :=
  thirdFixture row01 slots01 row_ne.1 vector_balances.1

/-- Third-mode target/target fixture in ambient dimensions `(1,1,5)`. -/
def third23 : DisplayedF3PairTriple 1 1 5 :=
  thirdFixture row23 slots23 row_ne.2.1 vector_balances.2.1

/-- Third-mode forward-opposite fixture in ambient dimensions `(1,1,5)`. -/
def third02 : DisplayedF3PairTriple 1 1 5 :=
  thirdFixture row02 slots02 row_ne.2.2.1 vector_balances.2.2.1

/-- Third-mode reverse-opposite fixture in ambient dimensions `(1,1,5)`. -/
def third12 : DisplayedF3PairTriple 1 1 5 :=
  thirdFixture row12 slots12 row_ne.2.2.2 vector_balances.2.2.2

/-- Total bridges for the four first-mode placement fixtures. -/
def bridgeFirst01 := certifiedFiveToFour first01

def bridgeFirst23 := certifiedFiveToFour first23

def bridgeFirst02 := certifiedFiveToFour first02

def bridgeFirst12 := certifiedFiveToFour first12

example : bridgeFirst01.normalized.placement = .sourceSource := by decide
example : bridgeFirst23.normalized.placement = .targetTarget := by decide
example : bridgeFirst02.normalized.placement = .opposite := by decide
example : bridgeFirst12.normalized.placement = .opposite := by decide

example : bridgeFirst01.normalized.residualShape = .oneThree := by decide
example : bridgeFirst23.normalized.residualShape = .twoTwo := by decide
example : bridgeFirst02.normalized.residualShape = .twoTwo := by decide
example : bridgeFirst12.normalized.residualShape = .twoTwo := by decide

#eval (bridgeFirst01.normalized.leftIndex.val, bridgeFirst01.normalized.rightIndex.val,
  (List.ofFn bridgeFirst01.normalized.residualReindex).map Fin.val,
  bridgeFirst01.qSignedIndex.val)
#eval (bridgeFirst23.normalized.leftIndex.val, bridgeFirst23.normalized.rightIndex.val,
  (List.ofFn bridgeFirst23.normalized.residualReindex).map Fin.val,
  bridgeFirst23.qSignedIndex.val)
#eval (bridgeFirst02.normalized.leftIndex.val, bridgeFirst02.normalized.rightIndex.val,
  (List.ofFn bridgeFirst02.normalized.residualReindex).map Fin.val,
  bridgeFirst02.qSignedIndex.val)
#eval (bridgeFirst12.normalized.leftIndex.val, bridgeFirst12.normalized.rightIndex.val,
  (List.ofFn bridgeFirst12.normalized.residualReindex).map Fin.val,
  bridgeFirst12.qSignedIndex.val)

#eval (List.ofFn fun i : Fin 4 =>
  ((List.ofFn fun j : Fin 5 => decide (bridgeFirst01.signedResidualAtom i = first01.atomAt j)),
    decide (bridgeFirst01.signedResidualAtom i = bridgeFirst01.q)))
#eval (List.ofFn fun i : Fin 4 =>
  ((List.ofFn fun j : Fin 5 => decide (bridgeFirst23.signedResidualAtom i = first23.atomAt j)),
    decide (bridgeFirst23.signedResidualAtom i = bridgeFirst23.q)))
#eval (List.ofFn fun i : Fin 4 =>
  ((List.ofFn fun j : Fin 5 => decide (bridgeFirst02.signedResidualAtom i = first02.atomAt j)),
    decide (bridgeFirst02.signedResidualAtom i = bridgeFirst02.q)))
#eval (List.ofFn fun i : Fin 4 =>
  ((List.ofFn fun j : Fin 5 => decide (bridgeFirst12.signedResidualAtom i = first12.atomAt j)),
    decide (bridgeFirst12.signedResidualAtom i = bridgeFirst12.q)))

end FieldFiveToFourRegressionScratch
end BilinearComplexity
