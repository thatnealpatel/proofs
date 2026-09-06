import BilinearComplexity.FieldFiveToFourContext
import BilinearComplexity.FieldThreeProductCircuit
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators

namespace BilinearComplexity
namespace FieldFiveToFourRegression

open FieldRankOne FieldContextual FieldNativeMoves FieldNativePath
open FieldFiveCircuitProfile FieldCircuitContraction FieldNativePairBridge
open FieldFiveToFour FieldNativeExecutablePath FieldThreeProductCircuit
open FieldTernaryFiveCircuitPair

/-- The ternary field used throughout the public bridge regressions. -/
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

/-- Total bridge for the first-mode source/source fixture. -/
def bridgeFirst01 := certifiedFiveToFour first01

/-- Total bridge for the first-mode target/target fixture. -/
def bridgeFirst23 := certifiedFiveToFour first23

/-- Total bridge for the first-mode forward-opposite fixture. -/
def bridgeFirst02 := certifiedFiveToFour first02

/-- Total bridge for the first-mode reverse-opposite fixture. -/
def bridgeFirst12 := certifiedFiveToFour first12

/-- A locally transparent decision procedure for candidate validity. -/
def transparentCandidateValidDecidable {a b c : ℕ} (candidate : Candidate)
    (x : Fin 5 → Fin a → F3) (y : Fin 5 → Fin b → F3)
    (z : Fin 5 → Fin c → F3) : Decidable (candidate.Valid x y z) := by
  unfold Candidate.Valid
  cases candidate.orientation <;> infer_instance

/-- The same total scanner with its validity decision procedure exposed transparently. -/
def transparentScan {a b c : ℕ} (x : Fin 5 → Fin a → F3)
    (y : Fin 5 → Fin b → F3) (z : Fin 5 → Fin c → F3) : Option Candidate :=
  candidates.find? fun candidate =>
    @decide (candidate.Valid x y z) (transparentCandidateValidDecidable candidate x y z)

/-- The public total scanner agrees with the transparently executable scanner. -/
theorem scan_eq_transparentScan {a b c : ℕ} (x : Fin 5 → Fin a → F3)
    (y : Fin 5 → Fin b → F3) (z : Fin 5 → Fin c → F3) :
    scan x y z = transparentScan x y z := by
  unfold scan transparentScan
  congr 1

/-- Kernel-checked execution of the total scanner on the first source/source fixture. -/
theorem first01_scan_execution : scan first01.x first01.y first01.z =
    some ⟨0, 1, .yz, 1, 1⟩ := by
  rw [scan_eq_transparentScan]
  decide

/-- The certified bridge stores the candidate returned by the actual total scanner. -/
theorem bridgeFirst01_candidate : bridgeFirst01.scan.candidate = ⟨0, 1, .yz, 1, 1⟩ := by
  unfold bridgeFirst01 certifiedFiveToFour FieldNativePairBridge.certifiedScanGauge
  simp only [FieldTernaryFiveCircuitPair.certifiedScan, first01_scan_execution,
    Option.get_some]

/-- Context containing the already-present source/source contraction atom. -/
def first01PresentContext : State F3 5 1 1 := ComputedState.singleton bridgeFirst01.q

macro "first01_decide" : tactic =>
  `(tactic|
    (unfold bridgeFirst01 certifiedFiveToFour FieldNativePairBridge.certifiedScanGauge
     simp only [FieldTernaryFiveCircuitPair.certifiedScan, first01_scan_execution,
       Option.get_some]
     decide))

/-- In a one/three signed residual, the first term is the sum of the other three. -/
theorem oneThree_signed_relation {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (S : SignedMinimalFour k V) (hshape : S.shape = .oneThree) :
    S.term 1 + (S.term 2 + S.term 3) = S.term 0 := by
  have h := S.signed_relation
  rw [hshape] at h
  norm_num [IsLinearRelation, signedFourCoefficients, Fin.sum_univ_succ] at h
  rw [eq_neg_of_add_eq_zero_left h]
  abel

/-- The unit factor used to turn concrete coordinate vectors into first-mode atoms. -/
def unitFactor : Factor F3 1 := ⟨fun _ => 1, by
  intro h
  have h0 := congrFun h 0
  norm_num at h0⟩

/-- Turn a nonzero five-coordinate vector into an atom varying in the first factor. -/
def firstVectorAtom (u : Fin 5 → F3) (hu : u ≠ 0) : Atom F3 5 1 1 :=
  FieldNativeMoves.atom ⟨u, hu⟩ unitFactor unitFactor

example : (firstVectorAtom ![1, 1, 0, 0, 0] (by decide)).val 0 0 0 = 1 := by decide

/-- Apply an actual native replacement to a computed F3 state. The stored terminal state is
computed by executable union and difference rather than by a specification-level index. -/
def actualStrictStep {a b c : ℕ} (D S T : State F3 a b c)
    (native : NativeReplacement S T) (hendpoints : Disjoint S T)
    (hsource : S ⊆ D) (hfresh : Disjoint T (ComputedState.difference D S))
    (hne : D ≠ ComputedState.union (ComputedState.difference D S) T) :
    StrictNativeStep D (ComputedState.union (ComputedState.difference D S) T) where
  step := {
    source := S
    target := T
    native := native
    source_subset := hsource
    target_fresh := by
      rw [ComputedState.difference_eq_spec] at hfresh
      exact hfresh
    result_eq := by
      rw [ComputedState.union_eq_spec, ComputedState.difference_eq_spec] }
  endpoints_disjoint := hendpoints
  ne := hne

/-- Compose two actual computed native steps and transport only the checked final index. -/
def actualTwoStepPath {a b c : ℕ} (D E S₀ T₀ S₁ T₁ : State F3 a b c)
    (native₀ : NativeReplacement S₀ T₀) (native₁ : NativeReplacement S₁ T₁)
    (hendpoints₀ : Disjoint S₀ T₀) (hendpoints₁ : Disjoint S₁ T₁)
    (hsource₀ : S₀ ⊆ D)
    (hfresh₀ : Disjoint T₀ (ComputedState.difference D S₀))
    (hne₀ : D ≠ ComputedState.union (ComputedState.difference D S₀) T₀)
    (hsource₁ : S₁ ⊆ ComputedState.union (ComputedState.difference D S₀) T₀)
    (hfresh₁ : Disjoint T₁ (ComputedState.difference
      (ComputedState.union (ComputedState.difference D S₀) T₀) S₁))
    (hne₁ : ComputedState.union (ComputedState.difference D S₀) T₀ ≠
      ComputedState.union (ComputedState.difference
        (ComputedState.union (ComputedState.difference D S₀) T₀) S₁) T₁)
    (hfinish : ComputedState.union (ComputedState.difference
      (ComputedState.union (ComputedState.difference D S₀) T₀) S₁) T₁ = E) :
    StrictNativePath D E := by
  let D₁ := ComputedState.union (ComputedState.difference D S₀) T₀
  let D₂ := ComputedState.union (ComputedState.difference D₁ S₁) T₁
  let first : StrictNativeStep D D₁ :=
    actualStrictStep D S₀ T₀ native₀ hendpoints₀ hsource₀ hfresh₀ hne₀
  let second : StrictNativeStep D₁ D₂ :=
    actualStrictStep D₁ S₁ T₁ native₁ hendpoints₁ hsource₁ hfresh₁ hne₁
  let path : StrictNativePath D D₂ := .cons first (.cons second (.nil D₂))
  exact FieldFiveToFourContext.CertifiedFiveToFour.Executable.castPath rfl hfinish path

/-- Explicit pure intermediate for the source/source residual path. -/
def first01Middle : Atom F3 5 1 1 :=
  firstVectorAtom
    (fun p => (bridgeFirst01.signedResidualAtom 2).val p 0 0 +
      (bridgeFirst01.signedResidualAtom 3).val p 0 0)
    (by
      intro hvector
      have hsum : (bridgeFirst01.signedResidualAtom 2).val +
          (bridgeFirst01.signedResidualAtom 3).val = 0 := by
        funext p j l
        rw [show j = 0 by exact Subsingleton.elim _ _,
          show l = 0 by exact Subsingleton.elim _ _]
        have hp := congrFun hvector p
        simpa only [Pi.add_apply, Pi.zero_apply] using hp
      have hterms : bridgeFirst01.signedResidual.term 2 +
          bridgeFirst01.signedResidual.term 3 = 0 := by
        simpa only [CertifiedFiveToFour.signedResidualAtom_val] using hsum
      have hprop : bridgeFirst01.signedResidual.term 2 =
          (-1 : F3) • bridgeFirst01.signedResidual.term 3 := by
        rw [eq_neg_of_add_eq_zero_left hterms]
        simp only [neg_one_smul]
      exact (bridgeFirst01.signedResidual.nonproportional 2 3 (by decide)) (-1) hprop)

/-- The explicit middle evaluates to the sum of the final two residual terms. -/
theorem first01Middle_val : first01Middle.val =
    (bridgeFirst01.signedResidualAtom 2).val +
      (bridgeFirst01.signedResidualAtom 3).val := by
  funext p j l
  rw [show j = 0 by exact Subsingleton.elim _ _,
    show l = 0 by exact Subsingleton.elim _ _]
  simp only [first01Middle, firstVectorAtom, FieldNativeMoves.atom_val, evalFactors,
    unitFactor, Pi.add_apply, one_mul, mul_one]

/-- The first fixture has one/three residual shape. -/
theorem first01_shape : bridgeFirst01.signedResidual.shape = .oneThree := by
  rw [CertifiedFiveToFour.signedResidual_shape]
  first01_decide

/-- Distinct canonical signed indices give distinct semantic residual atoms. -/
theorem first01ResidualAtom_ne {i j : Fin 4} (hij : i ≠ j) :
    bridgeFirst01.signedResidualAtom i ≠ bridgeFirst01.signedResidualAtom j := by
  intro hatom
  apply hij
  apply bridgeFirst01.signedResidual.injective
  simpa only [CertifiedFiveToFour.signedResidualAtom_val] using
    congrArg (fun x : Atom F3 5 1 1 => x.val) hatom

/-- The explicit middle differs from residual term two. -/
theorem first01Middle_ne_two : first01Middle ≠ bridgeFirst01.signedResidualAtom 2 := by
  intro hatom
  have hval : bridgeFirst01.signedResidual.term 2 +
      bridgeFirst01.signedResidual.term 3 = bridgeFirst01.signedResidual.term 2 := by
    rw [← CertifiedFiveToFour.signedResidualAtom_val,
      ← CertifiedFiveToFour.signedResidualAtom_val]
    rw [← first01Middle_val, hatom]
  apply bridgeFirst01.signedResidual.term_ne_zero 3
  apply add_left_cancel (a := bridgeFirst01.signedResidual.term 2)
  simpa only [add_zero] using hval

/-- The explicit middle differs from residual term three. -/
theorem first01Middle_ne_three : first01Middle ≠ bridgeFirst01.signedResidualAtom 3 := by
  intro hatom
  have hval : bridgeFirst01.signedResidual.term 2 +
      bridgeFirst01.signedResidual.term 3 = bridgeFirst01.signedResidual.term 3 := by
    rw [← CertifiedFiveToFour.signedResidualAtom_val,
      ← CertifiedFiveToFour.signedResidualAtom_val]
    rw [← first01Middle_val, hatom]
  apply bridgeFirst01.signedResidual.term_ne_zero 2
  apply add_right_cancel (b := bridgeFirst01.signedResidual.term 3)
  simpa only [zero_add] using hval

/-- The explicit middle differs from the residual source term. -/
theorem first01Middle_ne_zero : first01Middle ≠ bridgeFirst01.signedResidualAtom 0 := by
  intro hatom
  have hmiddle : bridgeFirst01.signedResidual.term 2 +
      bridgeFirst01.signedResidual.term 3 = bridgeFirst01.signedResidual.term 0 := by
    calc
      _ = first01Middle.val := by
        rw [first01Middle_val, CertifiedFiveToFour.signedResidualAtom_val,
          CertifiedFiveToFour.signedResidualAtom_val]
      _ = (bridgeFirst01.signedResidualAtom 0).val := by rw [hatom]
      _ = _ := CertifiedFiveToFour.signedResidualAtom_val _ _
  have hrelation := oneThree_signed_relation bridgeFirst01.signedResidual first01_shape
  rw [hmiddle] at hrelation
  apply bridgeFirst01.signedResidual.term_ne_zero 1
  apply add_right_cancel (b := bridgeFirst01.signedResidual.term 0)
  simpa only [zero_add] using hrelation

/-- The explicit middle differs from residual term one. -/
theorem first01Middle_ne_one : first01Middle ≠ bridgeFirst01.signedResidualAtom 1 := by
  intro hatom
  have hmiddle : bridgeFirst01.signedResidual.term 2 +
      bridgeFirst01.signedResidual.term 3 = bridgeFirst01.signedResidual.term 1 := by
    calc
      _ = first01Middle.val := by
        rw [first01Middle_val, CertifiedFiveToFour.signedResidualAtom_val,
          CertifiedFiveToFour.signedResidualAtom_val]
      _ = (bridgeFirst01.signedResidualAtom 1).val := by rw [hatom]
      _ = _ := CertifiedFiveToFour.signedResidualAtom_val _ _
  have hrelation := oneThree_signed_relation bridgeFirst01.signedResidual first01_shape
  rw [hmiddle] at hrelation
  have hprop : bridgeFirst01.signedResidual.term 0 =
      (2 : F3) • bridgeFirst01.signedResidual.term 1 := by
    rw [← hrelation]
    norm_num [two_smul]
  exact (bridgeFirst01.signedResidual.nonproportional 0 1 (by decide)) 2 hprop

/-- First split in the source/source residual path. -/
theorem first01Split₀ : SplitFormula (bridgeFirst01.signedResidualAtom 0)
    (bridgeFirst01.signedResidualAtom 1) first01Middle := by
  apply FieldThreeProductCircuit.splitFormula_of_val_add_eq
  rw [first01Middle_val]
  simpa only [CertifiedFiveToFour.signedResidualAtom_val] using
    oneThree_signed_relation bridgeFirst01.signedResidual first01_shape

/-- Second split in the source/source residual path. -/
theorem first01Split₁ : SplitFormula first01Middle
    (bridgeFirst01.signedResidualAtom 2) (bridgeFirst01.signedResidualAtom 3) := by
  apply FieldThreeProductCircuit.splitFormula_of_val_add_eq
  exact first01Middle_val.symm

/-- Actual two-Split residual path with the contraction atom absent from the context. -/
def first01ResidualAbsent : StrictNativePath
    (FieldFiveToFourContext.CertifiedFiveToFour.Executable.requestStart bridgeFirst01
      ComputedState.empty)
    (FieldFiveToFourContext.CertifiedFiveToFour.Executable.requestFinish bridgeFirst01
      ComputedState.empty) := by
  let D := FieldFiveToFourContext.CertifiedFiveToFour.Executable.requestStart bridgeFirst01
    ComputedState.empty
  let E := FieldFiveToFourContext.CertifiedFiveToFour.Executable.requestFinish bridgeFirst01
    ComputedState.empty
  let S₀ := ComputedState.singleton (bridgeFirst01.signedResidualAtom 0)
  let T₀ := ComputedState.pair (bridgeFirst01.signedResidualAtom 1) first01Middle
  let S₁ := ComputedState.singleton first01Middle
  let T₁ := ComputedState.pair (bridgeFirst01.signedResidualAtom 2)
    (bridgeFirst01.signedResidualAtom 3)
  have native₀ : NativeReplacement S₀ T₀ := by
    simpa only [S₀, T₀, ComputedState.singleton_eq_spec, ComputedState.pair_eq_spec] using
      NativeReplacement.split first01Split₀ (by first01_decide)
  have native₁ : NativeReplacement S₁ T₁ := by
    simpa only [S₁, T₁, ComputedState.singleton_eq_spec, ComputedState.pair_eq_spec] using
      NativeReplacement.split first01Split₁ (by first01_decide)
  exact actualTwoStepPath D E S₀ T₀ S₁ T₁ native₀ native₁
    (by dsimp only [D, E, S₀, T₀, S₁, T₁]; first01_decide)
    (by dsimp only [D, E, S₀, T₀, S₁, T₁]; first01_decide)
    (by dsimp only [D, E, S₀, T₀, S₁, T₁]; first01_decide)
    (by dsimp only [D, E, S₀, T₀, S₁, T₁]; first01_decide)
    (by dsimp only [D, E, S₀, T₀, S₁, T₁]; first01_decide)
    (by dsimp only [D, E, S₀, T₀, S₁, T₁]; first01_decide)
    (by dsimp only [D, E, S₀, T₀, S₁, T₁]; first01_decide)
    (by dsimp only [D, E, S₀, T₀, S₁, T₁]; first01_decide)
    (by dsimp only [D, E, S₀, T₀, S₁, T₁]; first01_decide)

/-- Actual two-Split residual path with the contraction atom present in the context. -/
def first01ResidualPresent : StrictNativePath
    (FieldFiveToFourContext.CertifiedFiveToFour.Executable.requestStart bridgeFirst01
      first01PresentContext)
    (FieldFiveToFourContext.CertifiedFiveToFour.Executable.requestFinish bridgeFirst01
      first01PresentContext) := by
  let D := FieldFiveToFourContext.CertifiedFiveToFour.Executable.requestStart bridgeFirst01
    first01PresentContext
  let E := FieldFiveToFourContext.CertifiedFiveToFour.Executable.requestFinish bridgeFirst01
    first01PresentContext
  let S₀ := ComputedState.singleton (bridgeFirst01.signedResidualAtom 0)
  let T₀ := ComputedState.pair (bridgeFirst01.signedResidualAtom 1) first01Middle
  let S₁ := ComputedState.singleton first01Middle
  let T₁ := ComputedState.pair (bridgeFirst01.signedResidualAtom 2)
    (bridgeFirst01.signedResidualAtom 3)
  have native₀ : NativeReplacement S₀ T₀ := by
    simpa only [S₀, T₀, ComputedState.singleton_eq_spec, ComputedState.pair_eq_spec] using
      NativeReplacement.split first01Split₀ (by first01_decide)
  have native₁ : NativeReplacement S₁ T₁ := by
    simpa only [S₁, T₁, ComputedState.singleton_eq_spec, ComputedState.pair_eq_spec] using
      NativeReplacement.split first01Split₁ (by first01_decide)
  exact actualTwoStepPath D E S₀ T₀ S₁ T₁ native₀ native₁
    (by dsimp only [D, E, S₀, T₀, S₁, T₁]; first01_decide)
    (by dsimp only [D, E, S₀, T₀, S₁, T₁]; first01_decide)
    (by dsimp only [D, E, S₀, T₀, S₁, T₁]; first01_decide)
    (by dsimp only [D, E, S₀, T₀, S₁, T₁]; first01_decide)
    (by dsimp only [D, E, S₀, T₀, S₁, T₁]; first01_decide)
    (by dsimp only [D, E, S₀, T₀, S₁, T₁]; first01_decide)
    (by dsimp only [D, E, S₀, T₀, S₁, T₁]; first01_decide)
    (by dsimp only [D, E, S₀, T₀, S₁, T₁]; first01_decide)
    (by dsimp only [D, E, S₀, T₀, S₁, T₁]; first01_decide)


/-- Full executable source/source splice with the contraction atom absent initially. -/
def first01PacketAbsent : FieldNativeExecutablePath.Packet F3 5 1 1 :=
  FieldFiveToFourContext.CertifiedFiveToFour.Executable.execCompose bridgeFirst01
    ComputedState.empty (by decide) first01ResidualAbsent

/-- Full executable source/source splice with the contraction atom present initially. -/
def first01PacketPresent : FieldNativeExecutablePath.Packet F3 5 1 1 :=
  FieldFiveToFourContext.CertifiedFiveToFour.Executable.execCompose bridgeFirst01
    first01PresentContext (by
      simp only [first01PresentContext]
      first01_decide) first01ResidualPresent

macro "first01_packet_decide" : tactic =>
  `(tactic|
    (simp only [first01PacketAbsent, first01PacketPresent,
       first01ResidualAbsent, first01ResidualPresent, first01PresentContext]
     first01_decide))

example : FieldNativePairBridge.Path.length first01ResidualAbsent = 2 := rfl
example : FieldNativePairBridge.Path.length first01ResidualPresent = 2 := rfl

example : FieldNativePairBridge.Path.length first01PacketAbsent.path = 3 := by
  rw [first01PacketAbsent,
    FieldFiveToFourContext.CertifiedFiveToFour.Executable.length_execCompose]
  rfl

example : FieldNativePairBridge.Path.length first01PacketPresent.path = 3 := by
  rw [first01PacketPresent,
    FieldFiveToFourContext.CertifiedFiveToFour.Executable.length_execCompose]
  rfl

example : first01PacketAbsent.start =
    FieldFiveToFourContext.CertifiedFiveToFour.Executable.fullStart
      (I := first01) ComputedState.empty ∧
    first01PacketAbsent.finish =
      FieldFiveToFourContext.CertifiedFiveToFour.Executable.fullFinish
        (I := first01) ComputedState.empty := by first01_packet_decide

example : first01PacketPresent.start =
    FieldFiveToFourContext.CertifiedFiveToFour.Executable.fullStart
      (I := first01) first01PresentContext ∧
    first01PacketPresent.finish =
      FieldFiveToFourContext.CertifiedFiveToFour.Executable.fullFinish
        (I := first01) first01PresentContext := by first01_packet_decide

example : first01PacketAbsent.localEndpointTrace = [
    (FieldFiveToFourContext.CertifiedFiveToFour.Executable.outerSource bridgeFirst01,
      FieldFiveToFourContext.CertifiedFiveToFour.Executable.outerTarget bridgeFirst01),
    (ComputedState.singleton (bridgeFirst01.signedResidualAtom 0),
      ComputedState.pair (bridgeFirst01.signedResidualAtom 1) first01Middle),
    (ComputedState.singleton first01Middle,
      ComputedState.pair (bridgeFirst01.signedResidualAtom 2)
        (bridgeFirst01.signedResidualAtom 3))] := by first01_packet_decide

example : first01PacketPresent.localEndpointTrace = [
    (ComputedState.singleton (bridgeFirst01.signedResidualAtom 0),
      ComputedState.pair (bridgeFirst01.signedResidualAtom 1) first01Middle),
    (ComputedState.singleton first01Middle,
      ComputedState.pair (bridgeFirst01.signedResidualAtom 2)
        (bridgeFirst01.signedResidualAtom 3)),
    (FieldFiveToFourContext.CertifiedFiveToFour.Executable.outerSource bridgeFirst01,
      FieldFiveToFourContext.CertifiedFiveToFour.Executable.outerTarget bridgeFirst01)] := by first01_packet_decide

example : first01PacketAbsent.localEndpointTrace.map
    (fun edge => (edge.1.card, edge.2.card)) = [(2, 1), (1, 2), (1, 2)] := by first01_packet_decide

example : first01PacketPresent.localEndpointTrace.map
    (fun edge => (edge.1.card, edge.2.card)) = [(1, 2), (1, 2), (2, 1)] := by first01_packet_decide

example : first01PacketAbsent.stateTrace = [
    FieldFiveToFourContext.CertifiedFiveToFour.Executable.fullStart
      (I := first01) ComputedState.empty,
    FieldFiveToFourContext.CertifiedFiveToFour.Executable.requestStart bridgeFirst01
      ComputedState.empty,
    ComputedState.union
      (ComputedState.difference
        (FieldFiveToFourContext.CertifiedFiveToFour.Executable.requestStart bridgeFirst01
          ComputedState.empty)
        (ComputedState.singleton (bridgeFirst01.signedResidualAtom 0)))
      (ComputedState.pair (bridgeFirst01.signedResidualAtom 1) first01Middle),
    FieldFiveToFourContext.CertifiedFiveToFour.Executable.fullFinish
      (I := first01) ComputedState.empty] := by first01_packet_decide

example : first01PacketPresent.stateTrace = [
    FieldFiveToFourContext.CertifiedFiveToFour.Executable.fullStart
      (I := first01) first01PresentContext,
    ComputedState.union
      (ComputedState.difference
        (FieldFiveToFourContext.CertifiedFiveToFour.Executable.requestStart bridgeFirst01
          first01PresentContext)
        (ComputedState.singleton (bridgeFirst01.signedResidualAtom 0)))
      (ComputedState.pair (bridgeFirst01.signedResidualAtom 1) first01Middle),
    FieldFiveToFourContext.CertifiedFiveToFour.Executable.requestFinish bridgeFirst01
      first01PresentContext,
    FieldFiveToFourContext.CertifiedFiveToFour.Executable.fullFinish
      (I := first01) first01PresentContext] := by first01_packet_decide

example : first01PacketAbsent.edgeTrace =
    List.zip first01PacketAbsent.stateTrace first01PacketAbsent.stateTrace.tail := by first01_packet_decide

example : first01PacketPresent.edgeTrace =
    List.zip first01PacketPresent.stateTrace first01PacketPresent.stateTrace.tail := by first01_packet_decide

example : bridgeFirst01.normalized.placement = .sourceSource := by first01_decide


end FieldFiveToFourRegression
end BilinearComplexity
