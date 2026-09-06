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

/-- The actual vertex trace of the generic computed two-step constructor. -/
theorem stateTrace_actualTwoStepPath {a b c : ℕ}
    (D E S₀ T₀ S₁ T₁ : State F3 a b c)
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
    FieldNativeExecutablePath.stateTrace D
      (actualTwoStepPath D E S₀ T₀ S₁ T₁ native₀ native₁ hendpoints₀ hendpoints₁
        hsource₀ hfresh₀ hne₀ hsource₁ hfresh₁ hne₁ hfinish) =
      [D, ComputedState.union (ComputedState.difference D S₀) T₀, E] := by
  subst E
  rfl

/-- The local endpoint trace of the generic computed two-step constructor. -/
theorem localEndpointTrace_actualTwoStepPath {a b c : ℕ}
    (D E S₀ T₀ S₁ T₁ : State F3 a b c)
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
    FieldNativeExecutablePath.localEndpointTrace
      (actualTwoStepPath D E S₀ T₀ S₁ T₁ native₀ native₁ hendpoints₀ hendpoints₁
        hsource₀ hfresh₀ hne₀ hsource₁ hfresh₁ hne₁ hfinish) =
      [(S₀, T₀), (S₁, T₁)] := by
  subst E
  rfl

/-- Reversal of the generic computed two-step constructor restores its actual start state. -/
theorem reverseStateTrace_actualTwoStepPath {a b c : ℕ}
    (D E S₀ T₀ S₁ T₁ : State F3 a b c)
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
    FieldNativeExecutablePath.stateTrace E
      (FieldNativeExecutablePath.reverse
        (actualTwoStepPath D E S₀ T₀ S₁ T₁ native₀ native₁ hendpoints₀ hendpoints₁
          hsource₀ hfresh₀ hne₀ hsource₁ hfresh₁ hne₁ hfinish)) =
      [E, ComputedState.union (ComputedState.difference D S₀) T₀, D] := by
  subst E
  rfl

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

/- Actual two-Split residual path on the canonical one/three residual endpoints. -/
def first01CanonicalPath : StrictNativePath
    (ComputedState.singleton (bridgeFirst01.signedResidualAtom 0))
    (ComputedState.union (ComputedState.singleton (bridgeFirst01.signedResidualAtom 1))
      (ComputedState.pair (bridgeFirst01.signedResidualAtom 2)
        (bridgeFirst01.signedResidualAtom 3))) := by
  let D := ComputedState.singleton (bridgeFirst01.signedResidualAtom 0)
  let E := ComputedState.union
    (ComputedState.singleton (bridgeFirst01.signedResidualAtom 1))
    (ComputedState.pair (bridgeFirst01.signedResidualAtom 2)
      (bridgeFirst01.signedResidualAtom 3))
  let S₀ := ComputedState.singleton (bridgeFirst01.signedResidualAtom 0)
  let T₀ := ComputedState.pair (bridgeFirst01.signedResidualAtom 1) first01Middle
  let S₁ := ComputedState.singleton first01Middle
  let T₁ := ComputedState.pair (bridgeFirst01.signedResidualAtom 2)
    (bridgeFirst01.signedResidualAtom 3)
  have native₀ : NativeReplacement S₀ T₀ := by
    simpa only [S₀, T₀, ComputedState.singleton_eq_spec, ComputedState.pair_eq_spec] using
      NativeReplacement.split first01Split₀ first01Middle_ne_one.symm
  have native₁ : NativeReplacement S₁ T₁ := by
    simpa only [S₁, T₁, ComputedState.singleton_eq_spec, ComputedState.pair_eq_spec] using
      NativeReplacement.split first01Split₁
        (first01ResidualAtom_ne (by decide))
  exact actualTwoStepPath D E S₀ T₀ S₁ T₁ native₀ native₁
    (by
      rw [Finset.disjoint_left]
      intro x hxS hxT
      simp only [S₀, ComputedState.singleton, Finset.mem_singleton] at hxS
      simp only [T₀, ComputedState.pair, Finset.mem_insert, Finset.mem_singleton] at hxT
      subst x
      rcases hxT with h | h
      · exact first01ResidualAtom_ne (by decide) h
      · exact first01Middle_ne_zero h.symm)
    (by
      rw [Finset.disjoint_left]
      intro x hxS hxT
      simp only [S₁, ComputedState.singleton, Finset.mem_singleton] at hxS
      simp only [T₁, ComputedState.pair, Finset.mem_insert, Finset.mem_singleton] at hxT
      subst x
      rcases hxT with h | h
      · exact first01Middle_ne_two h
      · exact first01Middle_ne_three h)
    (by exact Finset.Subset.rfl)
    (by
      simp only [D, S₀, T₀, ComputedState.difference, ComputedState.singleton,
        Finset.sdiff_self, ComputedState.union, Finset.empty_union,
        Finset.disjoint_empty_right])
    (by
      intro h
      have hmem : bridgeFirst01.signedResidualAtom 0 ∈ D := by
        simp only [D, ComputedState.singleton, Finset.mem_singleton]
      rw [h] at hmem
      simp only [D, S₀, ComputedState.difference, ComputedState.singleton,
        Finset.sdiff_self, ComputedState.union, Finset.empty_union] at hmem
      simp only [T₀, ComputedState.pair, Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h
      · exact first01ResidualAtom_ne (by decide) h
      · exact first01Middle_ne_zero h.symm)
    (by
      simp only [D, S₀, T₀, S₁, ComputedState.difference, ComputedState.singleton,
        Finset.sdiff_self, ComputedState.union, Finset.empty_union,
        ComputedState.pair, Finset.singleton_subset_iff, Finset.mem_insert,
        Finset.mem_singleton]
      exact Or.inr True.intro)
    (by
      rw [Finset.disjoint_left]
      intro x hxT hxRest
      simp only [T₁, ComputedState.pair, Finset.mem_insert, Finset.mem_singleton] at hxT
      simp only [D, S₀, T₀, S₁, ComputedState.difference, ComputedState.singleton,
        Finset.sdiff_self, ComputedState.union, Finset.empty_union,
        ComputedState.pair, Finset.mem_sdiff, Finset.mem_insert,
        Finset.mem_singleton] at hxRest
      rcases hxT with rfl | rfl
      · rcases hxRest.1 with h | h
        · exact first01ResidualAtom_ne (by decide) h
        · exact hxRest.2 h
      · rcases hxRest.1 with h | h
        · exact first01ResidualAtom_ne (by decide) h
        · exact hxRest.2 h)
    (by
      intro h
      have hmem : bridgeFirst01.signedResidualAtom 2 ∈
          ComputedState.union
            (ComputedState.difference
              (ComputedState.union (ComputedState.difference D S₀) T₀) S₁) T₁ := by
        simp only [T₁, ComputedState.union, ComputedState.pair, Finset.mem_union,
          Finset.mem_insert, true_or, Finset.mem_singleton, or_true]
      rw [← h] at hmem
      simp only [D, S₀, T₀, ComputedState.difference, ComputedState.singleton,
        Finset.sdiff_self, ComputedState.union, Finset.empty_union,
        ComputedState.pair, Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h
      · exact first01ResidualAtom_ne (by decide) h.symm
      · exact first01Middle_ne_two h.symm)
    (by
      ext x
      simp only [D, E, S₀, T₀, S₁, T₁, ComputedState.difference,
        ComputedState.singleton, Finset.sdiff_self, ComputedState.union,
        Finset.empty_union, ComputedState.pair, Finset.mem_union,
        Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      have h1m : bridgeFirst01.signedResidualAtom 1 ≠ first01Middle :=
        first01Middle_ne_one.symm
      have h12 : bridgeFirst01.signedResidualAtom 1 ≠
          bridgeFirst01.signedResidualAtom 2 := first01ResidualAtom_ne (by decide)
      have h13 : bridgeFirst01.signedResidualAtom 1 ≠
          bridgeFirst01.signedResidualAtom 3 := first01ResidualAtom_ne (by decide)
      aesop)

example : FieldNativePairBridge.Path.length first01CanonicalPath = 2 := by
  unfold first01CanonicalPath actualTwoStepPath
  rw [FieldFiveToFourContext.CertifiedFiveToFour.Executable.length_castPath]
  rfl

private def first01CanonicalPacket : Packet F3 5 1 1 where
  start := ComputedState.singleton (bridgeFirst01.signedResidualAtom 0)
  finish := ComputedState.union
    (ComputedState.singleton (bridgeFirst01.signedResidualAtom 1))
    (ComputedState.pair (bridgeFirst01.signedResidualAtom 2)
      (bridgeFirst01.signedResidualAtom 3))
  path := first01CanonicalPath

example : first01CanonicalPacket.stateTrace.length = 3 := by
  rw [Packet.stateTrace_length]
  unfold first01CanonicalPacket first01CanonicalPath actualTwoStepPath
  rw [FieldFiveToFourContext.CertifiedFiveToFour.Executable.length_castPath]
  rfl

example : first01CanonicalPacket.localEndpointTrace.length = 2 := by
  change (FieldNativeExecutablePath.localEndpointTrace first01CanonicalPath).length = 2
  rw [FieldNativeExecutablePath.localEndpointTrace_length]
  unfold first01CanonicalPath actualTwoStepPath
  rw [FieldFiveToFourContext.CertifiedFiveToFour.Executable.length_castPath]
  rfl

example : FieldNativePairBridge.Path.length
    (FieldNativeExecutablePath.reverse first01CanonicalPath) = 2 := by
  rw [FieldNativeExecutablePath.length_reverse]
  unfold first01CanonicalPath actualTwoStepPath
  rw [FieldFiveToFourContext.CertifiedFiveToFour.Executable.length_castPath]
  rfl

example : (FieldNativeExecutablePath.stateTrace
    (ComputedState.union
      (ComputedState.singleton (bridgeFirst01.signedResidualAtom 1))
      (ComputedState.pair (bridgeFirst01.signedResidualAtom 2)
        (bridgeFirst01.signedResidualAtom 3)))
    (FieldNativeExecutablePath.reverse first01CanonicalPath)).length = 3 := by
  rw [FieldNativeExecutablePath.stateTrace_length,
    FieldNativeExecutablePath.length_reverse]
  unfold first01CanonicalPath actualTwoStepPath
  rw [FieldFiveToFourContext.CertifiedFiveToFour.Executable.length_castPath]
  rfl

example : first01CanonicalPacket.stateTrace =
    [ComputedState.singleton (bridgeFirst01.signedResidualAtom 0),
      ComputedState.pair (bridgeFirst01.signedResidualAtom 1) first01Middle,
      ComputedState.union
        (ComputedState.singleton (bridgeFirst01.signedResidualAtom 1))
        (ComputedState.pair (bridgeFirst01.signedResidualAtom 2)
          (bridgeFirst01.signedResidualAtom 3))] := by
  unfold first01CanonicalPacket Packet.stateTrace first01CanonicalPath
  rw [stateTrace_actualTwoStepPath]
  simp only [ComputedState.difference, ComputedState.singleton, Finset.sdiff_self,
    ComputedState.union, Finset.empty_union]

example : first01CanonicalPacket.localEndpointTrace =
    [(ComputedState.singleton (bridgeFirst01.signedResidualAtom 0),
      ComputedState.pair (bridgeFirst01.signedResidualAtom 1) first01Middle),
      (ComputedState.singleton first01Middle,
        ComputedState.pair (bridgeFirst01.signedResidualAtom 2)
          (bridgeFirst01.signedResidualAtom 3))] := by
  unfold first01CanonicalPacket Packet.localEndpointTrace first01CanonicalPath
  rw [localEndpointTrace_actualTwoStepPath]

example : FieldNativeExecutablePath.stateTrace
    (ComputedState.union
      (ComputedState.singleton (bridgeFirst01.signedResidualAtom 1))
      (ComputedState.pair (bridgeFirst01.signedResidualAtom 2)
        (bridgeFirst01.signedResidualAtom 3)))
    (FieldNativeExecutablePath.reverse first01CanonicalPath) =
    [ComputedState.union
      (ComputedState.singleton (bridgeFirst01.signedResidualAtom 1))
      (ComputedState.pair (bridgeFirst01.signedResidualAtom 2)
        (bridgeFirst01.signedResidualAtom 3)),
      ComputedState.pair (bridgeFirst01.signedResidualAtom 1) first01Middle,
      ComputedState.singleton (bridgeFirst01.signedResidualAtom 0)] := by
  unfold first01CanonicalPath
  rw [reverseStateTrace_actualTwoStepPath]
  simp only [ComputedState.difference, ComputedState.singleton, Finset.sdiff_self,
    ComputedState.union, Finset.empty_union]

/-- The scanned first fixture is in source/source placement, derived from its residual shape. -/
theorem first01_placement : bridgeFirst01.normalized.placement = .sourceSource := by
  have hshape : bridgeFirst01.normalized.residualShape = .oneThree := by
    simpa only [CertifiedFiveToFour.signedResidual_shape] using first01_shape
  cases hplace : bridgeFirst01.normalized.placement with
  | sourceSource => exact hplace
  | targetTarget =>
      simp only [EffectiveDisplayedF3PairTriple.residualShape, hplace] at hshape
      contradiction
  | opposite =>
      simp only [EffectiveDisplayedF3PairTriple.residualShape, hplace] at hshape
      contradiction

/-- The computed canonical singleton is the signed residual source of the first fixture. -/
theorem first01CanonicalStart_eq_signedResidualSource :
    ComputedState.singleton (bridgeFirst01.signedResidualAtom 0) =
      bridgeFirst01.signedResidualSource := by
  have hshape : bridgeFirst01.normalized.residualShape = .oneThree := by
    simpa only [CertifiedFiveToFour.signedResidual_shape] using first01_shape
  simp only [CertifiedFiveToFour.signedResidualSource,
    CertifiedFiveToFour.signedResidualAtom,
    EffectiveDisplayedF3PairTriple.signedResidualSource, hshape,
    ComputedState.singleton_eq_spec]

/-- The computed canonical triple is the signed residual target of the first fixture. -/
theorem first01CanonicalFinish_eq_signedResidualTarget :
    ComputedState.union
      (ComputedState.singleton (bridgeFirst01.signedResidualAtom 1))
      (ComputedState.pair (bridgeFirst01.signedResidualAtom 2)
        (bridgeFirst01.signedResidualAtom 3)) = bridgeFirst01.signedResidualTarget := by
  have hshape : bridgeFirst01.normalized.residualShape = .oneThree := by
    simpa only [CertifiedFiveToFour.signedResidual_shape] using first01_shape
  simp only [CertifiedFiveToFour.signedResidualTarget,
    CertifiedFiveToFour.signedResidualAtom,
    EffectiveDisplayedF3PairTriple.signedResidualTarget, hshape,
    ComputedState.union_eq_spec, ComputedState.singleton_eq_spec,
    ComputedState.pair_eq_spec]
  ext x
  simp only [stateUnion, singletonState, pairState, tripleState,
    Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]

/-- With empty outside context, the executable residual request starts at the canonical singleton. -/
theorem first01CanonicalStart_eq_requestStart_empty :
    ComputedState.singleton (bridgeFirst01.signedResidualAtom 0) =
      FieldFiveToFourContext.CertifiedFiveToFour.Executable.requestStart bridgeFirst01
        ComputedState.empty := by
  have hs : FieldFiveToFourContext.CertifiedFiveToFour.schedule bridgeFirst01
      ComputedState.empty = .beforeResidual := by
    simp [FieldFiveToFourContext.CertifiedFiveToFour.schedule,
      first01_placement, ComputedState.empty]
  have hrequest : FieldFiveToFourContext.CertifiedFiveToFour.requestStart bridgeFirst01
      ComputedState.empty = singletonState bridgeFirst01.q := by
    simp only [FieldFiveToFourContext.CertifiedFiveToFour.requestStart, hs,
      FieldFiveToFourContext.CertifiedFiveToFour.outerSource_eq_sourceState_of_sourceSource
        bridgeFirst01 first01_placement,
      FieldFiveToFourContext.CertifiedFiveToFour.outerTarget_eq_singletonState_of_sourceSource
        bridgeFirst01 first01_placement]
    ext x
    simp [ComputedState.empty, stateUnion, stateDifference, singletonState]
  calc
    _ = bridgeFirst01.signedResidualSource :=
      first01CanonicalStart_eq_signedResidualSource
    _ = singletonState bridgeFirst01.q :=
      FieldFiveToFourContext.CertifiedFiveToFour.signedResidualSource_eq_singletonState_of_sourceSource
        bridgeFirst01 first01_placement
    _ = FieldFiveToFourContext.CertifiedFiveToFour.requestStart bridgeFirst01
        ComputedState.empty := hrequest.symm
    _ = FieldFiveToFourContext.CertifiedFiveToFour.Executable.requestStart bridgeFirst01
        ComputedState.empty :=
      (FieldFiveToFourContext.CertifiedFiveToFour.Executable.requestStart_eq_spec
        bridgeFirst01 ComputedState.empty).symm

/-- With empty outside context, the executable residual request finishes at the canonical triple. -/
theorem first01CanonicalFinish_eq_requestFinish_empty :
    ComputedState.union
      (ComputedState.singleton (bridgeFirst01.signedResidualAtom 1))
      (ComputedState.pair (bridgeFirst01.signedResidualAtom 2)
        (bridgeFirst01.signedResidualAtom 3)) =
      FieldFiveToFourContext.CertifiedFiveToFour.Executable.requestFinish bridgeFirst01
        ComputedState.empty := by
  have hs : FieldFiveToFourContext.CertifiedFiveToFour.schedule bridgeFirst01
      ComputedState.empty = .beforeResidual := by
    simp [FieldFiveToFourContext.CertifiedFiveToFour.schedule,
      first01_placement, ComputedState.empty]
  have hrequest : FieldFiveToFourContext.CertifiedFiveToFour.requestFinish bridgeFirst01
      ComputedState.empty = first01.targetState := by
    simp only [FieldFiveToFourContext.CertifiedFiveToFour.requestFinish, hs]
    ext x
    simp [ComputedState.empty, stateUnion]
  calc
    _ = bridgeFirst01.signedResidualTarget :=
      first01CanonicalFinish_eq_signedResidualTarget
    _ = first01.targetState :=
      FieldFiveToFourContext.CertifiedFiveToFour.signedResidualTarget_eq_targetState_of_sourceSource
        bridgeFirst01 first01_placement
    _ = FieldFiveToFourContext.CertifiedFiveToFour.requestFinish bridgeFirst01
        ComputedState.empty := hrequest.symm
    _ = FieldFiveToFourContext.CertifiedFiveToFour.Executable.requestFinish bridgeFirst01
        ComputedState.empty :=
      (FieldFiveToFourContext.CertifiedFiveToFour.Executable.requestFinish_eq_spec
        bridgeFirst01 ComputedState.empty).symm

/-- Actual canonical residual execution for the first scanned fixture with empty outside context. -/
def first01ResidualAbsent : StrictNativePath
    (FieldFiveToFourContext.CertifiedFiveToFour.Executable.requestStart bridgeFirst01
      ComputedState.empty)
    (FieldFiveToFourContext.CertifiedFiveToFour.Executable.requestFinish bridgeFirst01
      ComputedState.empty) :=
  FieldFiveToFourContext.CertifiedFiveToFour.Executable.castPath
    first01CanonicalStart_eq_requestStart_empty
    first01CanonicalFinish_eq_requestFinish_empty first01CanonicalPath

/-- Full executable source/source packet for the first scanned fixture with empty context. -/
def first01PacketAbsent : Packet F3 5 1 1 :=
  FieldFiveToFourContext.CertifiedFiveToFour.Executable.execCompose bridgeFirst01
    ComputedState.empty (by
      rw [Finset.disjoint_left]
      intro x hx
      simp [ComputedState.empty] at hx)
    first01ResidualAbsent

example : FieldNativePairBridge.Path.length first01ResidualAbsent = 2 := by
  unfold first01ResidualAbsent
  rw [FieldFiveToFourContext.CertifiedFiveToFour.Executable.length_castPath]
  unfold first01CanonicalPath actualTwoStepPath
  rw [FieldFiveToFourContext.CertifiedFiveToFour.Executable.length_castPath]
  rfl

example : FieldNativePairBridge.Path.length first01PacketAbsent.path = 3 := by
  rw [first01PacketAbsent,
    FieldFiveToFourContext.CertifiedFiveToFour.Executable.length_execCompose]
  change FieldNativePairBridge.Path.length first01ResidualAbsent + 1 = 3
  unfold first01ResidualAbsent
  rw [FieldFiveToFourContext.CertifiedFiveToFour.Executable.length_castPath]
  unfold first01CanonicalPath actualTwoStepPath
  rw [FieldFiveToFourContext.CertifiedFiveToFour.Executable.length_castPath]
  rfl

/-- Computed retained residual context for the occupied source/source schedule. -/
def first01RetainedContext : State F3 5 1 1 :=
  FieldFiveToFourContext.CertifiedFiveToFour.Executable.sourceState first01

/-- The contraction atom is present in the occupied external context. -/
theorem first01_q_mem_present : bridgeFirst01.q ∈ first01PresentContext := by
  simp [first01PresentContext, ComputedState.singleton]

/-- The occupied external context is disjoint from the computed displayed carrier. -/
theorem first01PresentContext_disjoint_displayedCarrier :
    Disjoint first01PresentContext
      (FieldFiveToFourContext.CertifiedFiveToFour.Executable.displayedCarrier first01) := by
  rw [FieldFiveToFourContext.CertifiedFiveToFour.Executable.displayedCarrier_eq_spec]
  rw [Finset.disjoint_left]
  intro x hxC hxDisplayed
  simp only [first01PresentContext, ComputedState.singleton,
    Finset.mem_singleton] at hxC
  subst x
  simp only [stateUnion, Finset.mem_union] at hxDisplayed
  exact hxDisplayed.elim
    (FieldFiveToFourContext.CertifiedFiveToFour.q_not_mem_sourceState bridgeFirst01)
    (FieldFiveToFourContext.CertifiedFiveToFour.q_not_mem_targetState bridgeFirst01)

/-- The retained computed context is the displayed source state. -/
theorem first01RetainedContext_eq_sourceState :
    first01RetainedContext = first01.sourceState := by
  unfold first01RetainedContext
  exact FieldFiveToFourContext.CertifiedFiveToFour.Executable.sourceState_eq_spec first01

/-- Residual atom zero is absent from the retained context. -/
theorem first01ResidualZero_not_mem_retained :
    bridgeFirst01.signedResidualAtom 0 ∉ first01RetainedContext := by
  rw [first01RetainedContext_eq_sourceState]
  have h0q : bridgeFirst01.signedResidualAtom 0 = bridgeFirst01.q := by
    have hs : ComputedState.singleton (bridgeFirst01.signedResidualAtom 0) =
        singletonState bridgeFirst01.q :=
      first01CanonicalStart_eq_signedResidualSource.trans
        (FieldFiveToFourContext.CertifiedFiveToFour.signedResidualSource_eq_singletonState_of_sourceSource
          bridgeFirst01 first01_placement)
    have hmem : bridgeFirst01.q ∈
        ComputedState.singleton (bridgeFirst01.signedResidualAtom 0) := by
      rw [hs]
      simp [singletonState]
    have hq0 : bridgeFirst01.q = bridgeFirst01.signedResidualAtom 0 := by
      simpa [ComputedState.singleton] using hmem
    exact hq0.symm
  rw [h0q]
  exact FieldFiveToFourContext.CertifiedFiveToFour.q_not_mem_sourceState bridgeFirst01

/-- Residual atom one is absent from the retained context. -/
theorem first01ResidualOne_not_mem_retained :
    bridgeFirst01.signedResidualAtom 1 ∉ first01RetainedContext := by
  rw [first01RetainedContext_eq_sourceState]
  intro hsource
  apply Finset.disjoint_left.mp first01.source_target_disjoint hsource
  rw [← FieldFiveToFourContext.CertifiedFiveToFour.signedResidualTarget_eq_targetState_of_sourceSource
      bridgeFirst01 first01_placement,
    ← first01CanonicalFinish_eq_signedResidualTarget]
  simp [ComputedState.union, ComputedState.singleton, ComputedState.pair]

/-- Residual atom two is absent from the retained context. -/
theorem first01ResidualTwo_not_mem_retained :
    bridgeFirst01.signedResidualAtom 2 ∉ first01RetainedContext := by
  rw [first01RetainedContext_eq_sourceState]
  intro hsource
  apply Finset.disjoint_left.mp first01.source_target_disjoint hsource
  rw [← FieldFiveToFourContext.CertifiedFiveToFour.signedResidualTarget_eq_targetState_of_sourceSource
      bridgeFirst01 first01_placement,
    ← first01CanonicalFinish_eq_signedResidualTarget]
  simp [ComputedState.union, ComputedState.singleton, ComputedState.pair]

/-- Residual atom three is absent from the retained context. -/
theorem first01ResidualThree_not_mem_retained :
    bridgeFirst01.signedResidualAtom 3 ∉ first01RetainedContext := by
  rw [first01RetainedContext_eq_sourceState]
  intro hsource
  apply Finset.disjoint_left.mp first01.source_target_disjoint hsource
  rw [← FieldFiveToFourContext.CertifiedFiveToFour.signedResidualTarget_eq_targetState_of_sourceSource
      bridgeFirst01 first01_placement,
    ← first01CanonicalFinish_eq_signedResidualTarget]
  simp [ComputedState.union, ComputedState.singleton, ComputedState.pair]

/-- The occupied computed start request is retained context union the canonical singleton. -/
theorem first01PresentStart_eq_requestStart :
    ComputedState.union first01RetainedContext
      (ComputedState.singleton (bridgeFirst01.signedResidualAtom 0)) =
      FieldFiveToFourContext.CertifiedFiveToFour.Executable.requestStart bridgeFirst01
        first01PresentContext := by
  have hspec : Disjoint first01PresentContext
      (stateUnion first01.sourceState first01.targetState) := by
    rw [← FieldFiveToFourContext.CertifiedFiveToFour.Executable.displayedCarrier_eq_spec]
    exact first01PresentContext_disjoint_displayedCarrier
  calc
    _ = stateUnion first01.sourceState bridgeFirst01.signedResidualSource := by
      unfold first01RetainedContext
      rw [ComputedState.union_eq_spec,
        FieldFiveToFourContext.CertifiedFiveToFour.Executable.sourceState_eq_spec,
        first01CanonicalStart_eq_signedResidualSource]
    _ = stateUnion
        (FieldFiveToFourContext.CertifiedFiveToFour.residualContext bridgeFirst01
          first01PresentContext) bridgeFirst01.signedResidualSource := by
      rw [FieldFiveToFourContext.CertifiedFiveToFour.residualContext_eq_of_sourceSource_q_mem
        bridgeFirst01 first01PresentContext first01_placement first01_q_mem_present]
      ext x
      simp [first01PresentContext, ComputedState.singleton_eq_spec,
        stateDifference, singletonState, stateUnion]
    _ = FieldFiveToFourContext.CertifiedFiveToFour.requestStart bridgeFirst01
        first01PresentContext :=
      (FieldFiveToFourContext.CertifiedFiveToFour.requestStart_eq_residualContext_union_signedResidualSource_of_sourceSource_q_mem
        bridgeFirst01 first01PresentContext first01_placement first01_q_mem_present).symm
    _ = FieldFiveToFourContext.CertifiedFiveToFour.Executable.requestStart bridgeFirst01
        first01PresentContext :=
      (FieldFiveToFourContext.CertifiedFiveToFour.Executable.requestStart_eq_spec
        bridgeFirst01 first01PresentContext).symm

/-- The occupied computed finish request is retained context union the canonical triple. -/
theorem first01PresentFinish_eq_requestFinish :
    ComputedState.union first01RetainedContext
      (ComputedState.union
        (ComputedState.singleton (bridgeFirst01.signedResidualAtom 1))
        (ComputedState.pair (bridgeFirst01.signedResidualAtom 2)
          (bridgeFirst01.signedResidualAtom 3))) =
      FieldFiveToFourContext.CertifiedFiveToFour.Executable.requestFinish bridgeFirst01
        first01PresentContext := by
  have hspec : Disjoint first01PresentContext
      (stateUnion first01.sourceState first01.targetState) := by
    rw [← FieldFiveToFourContext.CertifiedFiveToFour.Executable.displayedCarrier_eq_spec]
    exact first01PresentContext_disjoint_displayedCarrier
  calc
    _ = stateUnion first01.sourceState bridgeFirst01.signedResidualTarget := by
      unfold first01RetainedContext
      rw [ComputedState.union_eq_spec,
        FieldFiveToFourContext.CertifiedFiveToFour.Executable.sourceState_eq_spec,
        first01CanonicalFinish_eq_signedResidualTarget]
    _ = stateUnion
        (FieldFiveToFourContext.CertifiedFiveToFour.residualContext bridgeFirst01
          first01PresentContext) bridgeFirst01.signedResidualTarget := by
      rw [FieldFiveToFourContext.CertifiedFiveToFour.residualContext_eq_of_sourceSource_q_mem
        bridgeFirst01 first01PresentContext first01_placement first01_q_mem_present]
      ext x
      simp [first01PresentContext, ComputedState.singleton_eq_spec,
        stateDifference, singletonState, stateUnion]
    _ = FieldFiveToFourContext.CertifiedFiveToFour.requestFinish bridgeFirst01
        first01PresentContext :=
      (FieldFiveToFourContext.CertifiedFiveToFour.requestFinish_eq_residualContext_union_signedResidualTarget_of_sourceSource_q_mem
        bridgeFirst01 first01PresentContext first01_placement first01_q_mem_present).symm
    _ = FieldFiveToFourContext.CertifiedFiveToFour.Executable.requestFinish bridgeFirst01
        first01PresentContext :=
      (FieldFiveToFourContext.CertifiedFiveToFour.Executable.requestFinish_eq_spec
        bridgeFirst01 first01PresentContext).symm

end FieldFiveToFourRegression
end BilinearComplexity
