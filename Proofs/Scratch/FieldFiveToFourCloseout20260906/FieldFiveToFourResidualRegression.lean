import BilinearComplexity.FieldFiveToFourRegression

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace BilinearComplexity
namespace FieldFiveToFourResidualRegression

/-- The unambiguous ternary scalar type used by the residual execution fixtures. -/
abbrev RF3 := FieldFiveToFour.F3

open FieldRankOne FieldContextual FieldNativeMoves FieldNativePath
open FieldFiveToFour FieldFiveToFourRegression
open FieldNativeExecutablePath FieldThreeProductCircuit

/-- The common one-dimensional factor used by the concrete residual intermediates. -/
def unitFactor : Factor RF3 1 := ⟨![1], by decide⟩

/-- Construct an atom whose first factor is a concrete five-coordinate vector. -/
def firstVectorAtom (u : Fin 5 → RF3) (hu : u ≠ 0) : Atom RF3 5 1 1 :=
  FieldNativeMoves.atom ⟨u, hu⟩ unitFactor unitFactor

/-- Construct an atom whose second factor is a concrete five-coordinate vector. -/
def secondVectorAtom (u : Fin 5 → RF3) (hu : u ≠ 0) : Atom RF3 1 5 1 :=
  FieldNativeMoves.atom unitFactor ⟨u, hu⟩ unitFactor

/-- Construct an atom whose third factor is a concrete five-coordinate vector. -/
def thirdVectorAtom (u : Fin 5 → RF3) (hu : u ≠ 0) : Atom RF3 1 1 5 :=
  FieldNativeMoves.atom unitFactor unitFactor ⟨u, hu⟩

example : (firstVectorAtom ![1, 0, 0, 0, 0] (by decide)).val 0 0 0 = 1 := by decide
example : (secondVectorAtom ![0, 1, 0, 0, 0] (by decide)).val 0 1 0 = 1 := by decide
example : (thirdVectorAtom ![0, 0, 1, 0, 0] (by decide)).val 0 0 2 = 1 := by decide

/-- Apply a local native replacement to an actual computed state. -/
def actualStrictStep {a b c : ℕ} (D S T : State RF3 a b c)
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

/-- Compose two actual native steps whose states are computed by union and difference. -/
def actualTwoStepPath {a b c : ℕ} (D E S₀ T₀ S₁ T₁ : State RF3 a b c)
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
  exact FieldNativeExecutablePath.castPath rfl hfinish path

/-- Computed source of a canonical one/three residual. -/
def oneThreeStart {a b c : ℕ} {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) : State RF3 a b c :=
  ComputedState.singleton (B.signedResidualAtom 0)

/-- Computed target of a canonical one/three residual. -/
def oneThreeFinish {a b c : ℕ} {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) : State RF3 a b c :=
  ComputedState.union (ComputedState.singleton (B.signedResidualAtom 1))
    (ComputedState.pair (B.signedResidualAtom 2) (B.signedResidualAtom 3))

/-- Build a checked two-Split realization of a canonical one/three residual. -/
def oneThreePath {a b c : ℕ} {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) (middle : Atom RF3 a b c)
    (formula₀ : SplitFormula (B.signedResidualAtom 0) (B.signedResidualAtom 1) middle)
    (formula₁ : SplitFormula middle (B.signedResidualAtom 2) (B.signedResidualAtom 3))
    (hchecks :
      let D := oneThreeStart B
      let E := oneThreeFinish B
      let S₀ := ComputedState.singleton (B.signedResidualAtom 0)
      let T₀ := ComputedState.pair (B.signedResidualAtom 1) middle
      let S₁ := ComputedState.singleton middle
      let T₁ := ComputedState.pair (B.signedResidualAtom 2) (B.signedResidualAtom 3)
      B.signedResidualAtom 1 ≠ middle ∧
      B.signedResidualAtom 2 ≠ B.signedResidualAtom 3 ∧
      Disjoint S₀ T₀ ∧ Disjoint S₁ T₁ ∧ S₀ ⊆ D ∧
      Disjoint T₀ (ComputedState.difference D S₀) ∧
      D ≠ ComputedState.union (ComputedState.difference D S₀) T₀ ∧
      S₁ ⊆ ComputedState.union (ComputedState.difference D S₀) T₀ ∧
      Disjoint T₁ (ComputedState.difference
        (ComputedState.union (ComputedState.difference D S₀) T₀) S₁) ∧
      ComputedState.union (ComputedState.difference D S₀) T₀ ≠
        ComputedState.union (ComputedState.difference
          (ComputedState.union (ComputedState.difference D S₀) T₀) S₁) T₁ ∧
      ComputedState.union (ComputedState.difference
        (ComputedState.union (ComputedState.difference D S₀) T₀) S₁) T₁ = E) :
    StrictNativePath (oneThreeStart B) (oneThreeFinish B) := by
  dsimp only at hchecks
  rcases hchecks with ⟨hne₀, hne₁, hend₀, hend₁, hsource₀, hfresh₀, hstep₀,
    hsource₁, hfresh₁, hstep₁, hfinish⟩
  let S₀ := ComputedState.singleton (B.signedResidualAtom 0)
  let T₀ := ComputedState.pair (B.signedResidualAtom 1) middle
  let S₁ := ComputedState.singleton middle
  let T₁ := ComputedState.pair (B.signedResidualAtom 2) (B.signedResidualAtom 3)
  have native₀ : NativeReplacement S₀ T₀ := by
    simpa only [S₀, T₀, ComputedState.singleton_eq_spec, ComputedState.pair_eq_spec] using
      NativeReplacement.split formula₀ hne₀
  have native₁ : NativeReplacement S₁ T₁ := by
    simpa only [S₁, T₁, ComputedState.singleton_eq_spec, ComputedState.pair_eq_spec] using
      NativeReplacement.split formula₁ hne₁
  exact actualTwoStepPath (oneThreeStart B) (oneThreeFinish B) S₀ T₀ S₁ T₁
    native₀ native₁ hend₀ hend₁ hsource₀ hfresh₀ hstep₀ hsource₁ hfresh₁ hstep₁ hfinish

/-- Computed source of a canonical two/two residual. -/
def twoTwoStart {a b c : ℕ} {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) : State RF3 a b c :=
  ComputedState.pair (B.signedResidualAtom 0) (B.signedResidualAtom 1)

/-- Computed target of a canonical two/two residual. -/
def twoTwoFinish {a b c : ℕ} {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) : State RF3 a b c :=
  ComputedState.pair (B.signedResidualAtom 2) (B.signedResidualAtom 3)

/-- Build a checked Split-then-Reduction realization of a canonical two/two residual. -/
def twoTwoPath {a b c : ℕ} {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) (middle : Atom RF3 a b c)
    (formula₀ : SplitFormula (B.signedResidualAtom 0) (B.signedResidualAtom 2) middle)
    (formula₁ : SplitFormula (B.signedResidualAtom 3) middle (B.signedResidualAtom 1))
    (hchecks :
      let D := twoTwoStart B
      let E := twoTwoFinish B
      let S₀ := ComputedState.singleton (B.signedResidualAtom 0)
      let T₀ := ComputedState.pair (B.signedResidualAtom 2) middle
      let S₁ := ComputedState.pair middle (B.signedResidualAtom 1)
      let T₁ := ComputedState.singleton (B.signedResidualAtom 3)
      B.signedResidualAtom 2 ≠ middle ∧ middle ≠ B.signedResidualAtom 1 ∧
      Disjoint S₀ T₀ ∧ Disjoint S₁ T₁ ∧ S₀ ⊆ D ∧
      Disjoint T₀ (ComputedState.difference D S₀) ∧
      D ≠ ComputedState.union (ComputedState.difference D S₀) T₀ ∧
      S₁ ⊆ ComputedState.union (ComputedState.difference D S₀) T₀ ∧
      Disjoint T₁ (ComputedState.difference
        (ComputedState.union (ComputedState.difference D S₀) T₀) S₁) ∧
      ComputedState.union (ComputedState.difference D S₀) T₀ ≠
        ComputedState.union (ComputedState.difference
          (ComputedState.union (ComputedState.difference D S₀) T₀) S₁) T₁ ∧
      ComputedState.union (ComputedState.difference
        (ComputedState.union (ComputedState.difference D S₀) T₀) S₁) T₁ = E) :
    StrictNativePath (twoTwoStart B) (twoTwoFinish B) := by
  dsimp only at hchecks
  rcases hchecks with ⟨hne₀, hne₁, hend₀, hend₁, hsource₀, hfresh₀, hstep₀,
    hsource₁, hfresh₁, hstep₁, hfinish⟩
  let S₀ := ComputedState.singleton (B.signedResidualAtom 0)
  let T₀ := ComputedState.pair (B.signedResidualAtom 2) middle
  let S₁ := ComputedState.pair middle (B.signedResidualAtom 1)
  let T₁ := ComputedState.singleton (B.signedResidualAtom 3)
  have native₀ : NativeReplacement S₀ T₀ := by
    simpa only [S₀, T₀, ComputedState.singleton_eq_spec, ComputedState.pair_eq_spec] using
      NativeReplacement.split formula₀ hne₀
  have native₁ : NativeReplacement S₁ T₁ := by
    simpa only [S₁, T₁, ComputedState.pair_eq_spec, ComputedState.singleton_eq_spec] using
      NativeReplacement.reduction formula₁ hne₁
  exact actualTwoStepPath (twoTwoStart B) (twoTwoFinish B) S₀ T₀ S₁ T₁
    native₀ native₁ hend₀ hend₁ hsource₀ hfresh₀ hstep₀ hsource₁ hfresh₁ hstep₁ hfinish

/-- Total second-mode source/source bridge. -/
def bridgeSecond01 := certifiedFiveToFour second01
/-- Total second-mode target/target bridge. -/
def bridgeSecond23 := certifiedFiveToFour second23
/-- Total second-mode forward-opposite bridge. -/
def bridgeSecond02 := certifiedFiveToFour second02
/-- Total second-mode reverse-opposite bridge. -/
def bridgeSecond12 := certifiedFiveToFour second12
/-- Total third-mode source/source bridge. -/
def bridgeThird01 := certifiedFiveToFour third01
/-- Total third-mode target/target bridge. -/
def bridgeThird23 := certifiedFiveToFour third23
/-- Total third-mode forward-opposite bridge. -/
def bridgeThird02 := certifiedFiveToFour third02
/-- Total third-mode reverse-opposite bridge. -/
def bridgeThird12 := certifiedFiveToFour third12

/-- First-mode one/three intermediate. -/
def middleFirst01 : Atom RF3 5 1 1 :=
  firstVectorAtom (fun p => (bridgeFirst01.signedResidualAtom 2).val p 0 0 +
    (bridgeFirst01.signedResidualAtom 3).val p 0 0) (by decide)

/-- First-mode target/target intermediate. -/
def middleFirst23 : Atom RF3 5 1 1 :=
  firstVectorAtom (fun p => (bridgeFirst23.signedResidualAtom 0).val p 0 0 -
    (bridgeFirst23.signedResidualAtom 2).val p 0 0) (by decide)

/-- First-mode forward-opposite intermediate. -/
def middleFirst02 : Atom RF3 5 1 1 :=
  firstVectorAtom (fun p => (bridgeFirst02.signedResidualAtom 0).val p 0 0 -
    (bridgeFirst02.signedResidualAtom 2).val p 0 0) (by decide)

/-- First-mode reverse-opposite intermediate. -/
def middleFirst12 : Atom RF3 5 1 1 :=
  firstVectorAtom (fun p => (bridgeFirst12.signedResidualAtom 0).val p 0 0 -
    (bridgeFirst12.signedResidualAtom 2).val p 0 0) (by decide)

/-- Second-mode one/three intermediate. -/
def middleSecond01 : Atom RF3 1 5 1 :=
  secondVectorAtom (fun q => (bridgeSecond01.signedResidualAtom 2).val 0 q 0 +
    (bridgeSecond01.signedResidualAtom 3).val 0 q 0) (by decide)

/-- Second-mode target/target intermediate. -/
def middleSecond23 : Atom RF3 1 5 1 :=
  secondVectorAtom (fun q => (bridgeSecond23.signedResidualAtom 0).val 0 q 0 -
    (bridgeSecond23.signedResidualAtom 2).val 0 q 0) (by decide)

/-- Second-mode forward-opposite intermediate. -/
def middleSecond02 : Atom RF3 1 5 1 :=
  secondVectorAtom (fun q => (bridgeSecond02.signedResidualAtom 0).val 0 q 0 -
    (bridgeSecond02.signedResidualAtom 2).val 0 q 0) (by decide)

/-- Second-mode reverse-opposite intermediate. -/
def middleSecond12 : Atom RF3 1 5 1 :=
  secondVectorAtom (fun q => (bridgeSecond12.signedResidualAtom 0).val 0 q 0 -
    (bridgeSecond12.signedResidualAtom 2).val 0 q 0) (by decide)

/-- Third-mode one/three intermediate. -/
def middleThird01 : Atom RF3 1 1 5 :=
  thirdVectorAtom (fun s => (bridgeThird01.signedResidualAtom 2).val 0 0 s +
    (bridgeThird01.signedResidualAtom 3).val 0 0 s) (by decide)

/-- Third-mode target/target intermediate. -/
def middleThird23 : Atom RF3 1 1 5 :=
  thirdVectorAtom (fun s => (bridgeThird23.signedResidualAtom 0).val 0 0 s -
    (bridgeThird23.signedResidualAtom 2).val 0 0 s) (by decide)

/-- Third-mode forward-opposite intermediate. -/
def middleThird02 : Atom RF3 1 1 5 :=
  thirdVectorAtom (fun s => (bridgeThird02.signedResidualAtom 0).val 0 0 s -
    (bridgeThird02.signedResidualAtom 2).val 0 0 s) (by decide)

/-- Third-mode reverse-opposite intermediate. -/
def middleThird12 : Atom RF3 1 1 5 :=
  thirdVectorAtom (fun s => (bridgeThird12.signedResidualAtom 0).val 0 0 s -
    (bridgeThird12.signedResidualAtom 2).val 0 0 s) (by decide)

/-- Actual first-mode one/three path. -/
def pathFirst01 := oneThreePath bridgeFirst01 middleFirst01
  (splitFormula_of_val_add_eq _ _ _ (by decide))
  (splitFormula_of_val_add_eq _ _ _ (by decide)) (by decide)

/-- Actual first-mode target/target path. -/
def pathFirst23 := twoTwoPath bridgeFirst23 middleFirst23
  (splitFormula_of_val_add_eq _ _ _ (by decide))
  (splitFormula_of_val_add_eq _ _ _ (by decide)) (by decide)

/-- Actual first-mode forward-opposite path. -/
def pathFirst02 := twoTwoPath bridgeFirst02 middleFirst02
  (splitFormula_of_val_add_eq _ _ _ (by decide))
  (splitFormula_of_val_add_eq _ _ _ (by decide)) (by decide)

/-- Actual first-mode reverse-opposite path. -/
def pathFirst12 := twoTwoPath bridgeFirst12 middleFirst12
  (splitFormula_of_val_add_eq _ _ _ (by decide))
  (splitFormula_of_val_add_eq _ _ _ (by decide)) (by decide)

/-- Actual second-mode one/three path. -/
def pathSecond01 := oneThreePath bridgeSecond01 middleSecond01
  (splitFormula_of_val_add_eq _ _ _ (by decide))
  (splitFormula_of_val_add_eq _ _ _ (by decide)) (by decide)

/-- Actual second-mode target/target path. -/
def pathSecond23 := twoTwoPath bridgeSecond23 middleSecond23
  (splitFormula_of_val_add_eq _ _ _ (by decide))
  (splitFormula_of_val_add_eq _ _ _ (by decide)) (by decide)

/-- Actual second-mode forward-opposite path. -/
def pathSecond02 := twoTwoPath bridgeSecond02 middleSecond02
  (splitFormula_of_val_add_eq _ _ _ (by decide))
  (splitFormula_of_val_add_eq _ _ _ (by decide)) (by decide)

/-- Actual second-mode reverse-opposite path. -/
def pathSecond12 := twoTwoPath bridgeSecond12 middleSecond12
  (splitFormula_of_val_add_eq _ _ _ (by decide))
  (splitFormula_of_val_add_eq _ _ _ (by decide)) (by decide)

/-- Actual third-mode one/three path. -/
def pathThird01 := oneThreePath bridgeThird01 middleThird01
  (splitFormula_of_val_add_eq _ _ _ (by decide))
  (splitFormula_of_val_add_eq _ _ _ (by decide)) (by decide)

/-- Actual third-mode target/target path. -/
def pathThird23 := twoTwoPath bridgeThird23 middleThird23
  (splitFormula_of_val_add_eq _ _ _ (by decide))
  (splitFormula_of_val_add_eq _ _ _ (by decide)) (by decide)

/-- Actual third-mode forward-opposite path. -/
def pathThird02 := twoTwoPath bridgeThird02 middleThird02
  (splitFormula_of_val_add_eq _ _ _ (by decide))
  (splitFormula_of_val_add_eq _ _ _ (by decide)) (by decide)

/-- Actual third-mode reverse-opposite path. -/
def pathThird12 := twoTwoPath bridgeThird12 middleThird12
  (splitFormula_of_val_add_eq _ _ _ (by decide))
  (splitFormula_of_val_add_eq _ _ _ (by decide)) (by decide)

example : FieldNativePairBridge.Path.length pathFirst01 = 2 := rfl
example : FieldNativePairBridge.Path.length pathFirst23 = 2 := rfl
example : FieldNativePairBridge.Path.length pathFirst02 = 2 := rfl
example : FieldNativePairBridge.Path.length pathFirst12 = 2 := rfl
example : FieldNativePairBridge.Path.length pathSecond01 = 2 := rfl
example : FieldNativePairBridge.Path.length pathSecond23 = 2 := rfl
example : FieldNativePairBridge.Path.length pathSecond02 = 2 := rfl
example : FieldNativePairBridge.Path.length pathSecond12 = 2 := rfl
example : FieldNativePairBridge.Path.length pathThird01 = 2 := rfl
example : FieldNativePairBridge.Path.length pathThird23 = 2 := rfl
example : FieldNativePairBridge.Path.length pathThird02 = 2 := rfl
example : FieldNativePairBridge.Path.length pathThird12 = 2 := rfl

/-- Executable packet exposing the source/source path states and local native endpoints. -/
def packetFirst01 : FieldNativeExecutablePath.Packet RF3 5 1 1 :=
  ⟨oneThreeStart bridgeFirst01, oneThreeFinish bridgeFirst01, pathFirst01⟩

/-- Executable packet exposing the target/target path states and local native endpoints. -/
def packetFirst23 : FieldNativeExecutablePath.Packet RF3 5 1 1 :=
  ⟨twoTwoStart bridgeFirst23, twoTwoFinish bridgeFirst23, pathFirst23⟩

example : packetFirst01.stateTrace = [oneThreeStart bridgeFirst01,
    ComputedState.pair (bridgeFirst01.signedResidualAtom 1) middleFirst01,
    oneThreeFinish bridgeFirst01] := by decide

example : packetFirst01.localEndpointTrace = [
    (ComputedState.singleton (bridgeFirst01.signedResidualAtom 0),
      ComputedState.pair (bridgeFirst01.signedResidualAtom 1) middleFirst01),
    (ComputedState.singleton middleFirst01,
      ComputedState.pair (bridgeFirst01.signedResidualAtom 2)
        (bridgeFirst01.signedResidualAtom 3))] := by decide

example : packetFirst23.stateTrace = [twoTwoStart bridgeFirst23,
    ComputedState.union
      (ComputedState.singleton (bridgeFirst23.signedResidualAtom 1))
      (ComputedState.pair (bridgeFirst23.signedResidualAtom 2) middleFirst23),
    twoTwoFinish bridgeFirst23] := by decide

example : packetFirst23.localEndpointTrace = [
    (ComputedState.singleton (bridgeFirst23.signedResidualAtom 0),
      ComputedState.pair (bridgeFirst23.signedResidualAtom 2) middleFirst23),
    (ComputedState.pair middleFirst23 (bridgeFirst23.signedResidualAtom 1),
      ComputedState.singleton (bridgeFirst23.signedResidualAtom 3))] := by decide

example : packetFirst01.localEndpointTrace.map (fun edge => (edge.1.card, edge.2.card)) =
    [(1, 2), (1, 2)] := by decide

example : packetFirst23.localEndpointTrace.map (fun edge => (edge.1.card, edge.2.card)) =
    [(1, 2), (2, 1)] := by decide

end FieldFiveToFourResidualRegression
end BilinearComplexity
