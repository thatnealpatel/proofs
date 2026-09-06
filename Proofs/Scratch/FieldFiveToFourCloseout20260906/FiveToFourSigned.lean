import BilinearComplexity.FieldFiveToFour
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace BilinearComplexity
namespace FieldFiveToFour

open FieldRankOne FieldContextual FieldNativeMoves FieldNativePath
open FieldFiveCircuitProfile FieldCircuitContraction FieldNativePairBridge

variable {a b c : ℕ}

/-- A computable permutation moving two distinct residual positions to positions zero and one. -/
def pairFrontPerm4 (i j : Fin 4) : Equiv.Perm (Fin 4) :=
  (Equiv.swap 1 ((Equiv.swap 0 i) j)).trans (Equiv.swap 0 i)

/-- Canonical residual reindexing for the target/target placement. -/
def targetTargetResidualReindex (u v : Fin 3) : Equiv.Perm (Fin 4) :=
  if u = 0 then
    if v = 1 then pairFrontPerm4 1 2 else pairFrontPerm4 1 3
  else if u = 1 then
    if v = 0 then pairFrontPerm4 1 2 else pairFrontPerm4 2 3
  else if v = 0 then pairFrontPerm4 1 3 else pairFrontPerm4 2 3

/-- Reindex the actual contraction residual into its signed endpoint order. -/
def EffectiveDisplayedF3PairTriple.residualReindex
    {I : DisplayedF3PairTriple a b c}
    {scan : ScannedPairGauge I.x I.y I.z I.x_ne I.y_ne I.z_ne}
    (P : EffectiveDisplayedF3PairTriple I scan) : Equiv.Perm (Fin 4) :=
  match P with
  | .sourceSource .. => Equiv.refl _
  | .targetTarget u v .. => targetTargetResidualReindex u v
  | .oppositeForward _ v .. => Equiv.swap 1 v.succ
  | .oppositeReverse _ v .. => Equiv.swap 1 v.succ

/-- The endpoint shape of the normalized contraction. -/
def EffectiveDisplayedF3PairTriple.residualShape
    {I : DisplayedF3PairTriple a b c}
    {scan : ScannedPairGauge I.x I.y I.z I.x_ne I.y_ne I.z_ne}
    (P : EffectiveDisplayedF3PairTriple I scan) : FourFamilyShape :=
  match P.placement with
  | .sourceSource => .oneThree
  | .targetTarget | .opposite => .twoTwo

/-- The signed coefficient attached to one logical displayed endpoint slot. -/
def logicalCoefficient : Fin 2 ⊕ Fin 3 → F3
  | .inl _ => 1
  | .inr _ => -1

/-- The logical endpoint slot occupying `z` after bringing `x,y` to the contraction front. -/
def logicalSlotAfterPairFront (x y z : Fin 2 ⊕ Fin 3) : Fin 2 ⊕ Fin 3 :=
  finSumFinEquiv.symm (pairFrontSplit (finSumFinEquiv x) (finSumFinEquiv y) z)

/-- Displayed coefficients reduce to their logical endpoint sign. -/
@[simp] theorem DisplayedF3PairTriple.coefficient_slots
    (I : DisplayedF3PairTriple a b c) (x : Fin 2 ⊕ Fin 3) :
    I.coefficient (I.slots x) = logicalCoefficient x := by
  cases x <;> simp [DisplayedF3PairTriple.coefficient, logicalCoefficient]

/-- A normalized split can be evaluated through logical endpoint coordinates without reducing
constructor equality proofs. -/
theorem EffectiveDisplayedF3PairTriple.coefficient_normalizedSplit_of_indices
    {I : DisplayedF3PairTriple a b c}
    {scan : ScannedPairGauge I.x I.y I.z I.x_ne I.y_ne I.z_ne}
    (P : EffectiveDisplayedF3PairTriple I scan)
    {x y : Fin 2 ⊕ Fin 3}
    (hleft : P.leftIndex = I.slots x)
    (hright : P.rightIndex = I.slots y)
    (z : Fin 2 ⊕ Fin 3) :
    I.coefficient (P.normalizedSplit z) =
      logicalCoefficient (logicalSlotAfterPairFront x y z) := by
  unfold EffectiveDisplayedF3PairTriple.normalizedSplit
    DisplayedF3PairTriple.logicalSlots logicalSlotAfterPairFront
  simp only [Equiv.trans_apply, hleft, hright, Equiv.symm_apply_apply,
    DisplayedF3PairTriple.coefficient_slots]

/-- Contraction residual coefficients can be computed entirely in logical endpoint coordinates. -/
theorem EffectiveDisplayedF3PairTriple.contraction_residualCoefficients_of_indices
    {I : DisplayedF3PairTriple a b c}
    {scan : ScannedPairGauge I.x I.y I.z I.x_ne I.y_ne I.z_ne}
    (P : EffectiveDisplayedF3PairTriple I scan)
    {x y : Fin 2 ⊕ Fin 3}
    (hleft : P.leftIndex = I.slots x)
    (hright : P.rightIndex = I.slots y)
    (i : Fin 4) :
    P.contraction.residualCoefficients i =
      Fin.cases (logicalCoefficient x)
        (fun j => logicalCoefficient (logicalSlotAfterPairFront x y (.inr j))) i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [EffectiveDisplayedF3PairTriple.contraction_residualCoefficients_zero,
      hleft, DisplayedF3PairTriple.coefficient_slots]
    rfl
  · rw [EffectiveDisplayedF3PairTriple.contraction_residualCoefficients_succ]
    exact P.coefficient_normalizedSplit_of_indices hleft hright (.inr j)

/-- Actual contraction coefficients agree with the canonical signed coefficients after the
explicit endpoint-aware residual permutation. -/
theorem EffectiveDisplayedF3PairTriple.residual_coefficients_reindex
    {I : DisplayedF3PairTriple a b c}
    {scan : ScannedPairGauge I.x I.y I.z I.x_ne I.y_ne I.z_ne}
    (P : EffectiveDisplayedF3PairTriple I scan) (i : Fin 4) :
    P.contraction.residualCoefficients (P.residualReindex i) =
      signedFourCoefficients (k := F3) P.residualShape i := by
  cases P with
  | sourceSource u v huv hfirst hsecond pair =>
      let P : EffectiveDisplayedF3PairTriple I scan :=
        .sourceSource u v huv hfirst hsecond pair
      change P.contraction.residualCoefficients (P.residualReindex i) =
        signedFourCoefficients P.residualShape i
      have hleft : P.leftIndex = I.slots (.inl u) := by
        change scan.candidate.first = I.slots (.inl u)
        exact hfirst
      have hright : P.rightIndex = I.slots (.inl v) := by
        change scan.candidate.second = I.slots (.inl v)
        exact hsecond
      rw [P.contraction_residualCoefficients_of_indices hleft hright]
      dsimp [P, EffectiveDisplayedF3PairTriple.residualReindex,
        EffectiveDisplayedF3PairTriple.residualShape,
        EffectiveDisplayedF3PairTriple.placement]
      fin_cases u <;> fin_cases v <;> fin_cases i <;>
        first | omega | decide
  | targetTarget u v huv hfirst hsecond pair =>
      let P : EffectiveDisplayedF3PairTriple I scan :=
        .targetTarget u v huv hfirst hsecond pair
      change P.contraction.residualCoefficients (P.residualReindex i) =
        signedFourCoefficients P.residualShape i
      have hleft : P.leftIndex = I.slots (.inr u) := by
        change scan.candidate.first = I.slots (.inr u)
        exact hfirst
      have hright : P.rightIndex = I.slots (.inr v) := by
        change scan.candidate.second = I.slots (.inr v)
        exact hsecond
      rw [P.contraction_residualCoefficients_of_indices hleft hright]
      dsimp [P, EffectiveDisplayedF3PairTriple.residualReindex,
        EffectiveDisplayedF3PairTriple.residualShape,
        EffectiveDisplayedF3PairTriple.placement]
      fin_cases u <;> fin_cases v <;> fin_cases i <;>
        first | omega | decide
  | oppositeForward u v hfirst hsecond pair =>
      let P : EffectiveDisplayedF3PairTriple I scan :=
        .oppositeForward u v hfirst hsecond pair
      change P.contraction.residualCoefficients (P.residualReindex i) =
        signedFourCoefficients P.residualShape i
      have hleft : P.leftIndex = I.slots (.inl u) := by
        change scan.candidate.first = I.slots (.inl u)
        exact hfirst
      have hright : P.rightIndex = I.slots (.inr v) := by
        change scan.candidate.second = I.slots (.inr v)
        exact hsecond
      rw [P.contraction_residualCoefficients_of_indices hleft hright]
      dsimp [P, EffectiveDisplayedF3PairTriple.residualReindex,
        EffectiveDisplayedF3PairTriple.residualShape,
        EffectiveDisplayedF3PairTriple.placement]
      fin_cases u <;> fin_cases v <;> fin_cases i <;>
        first | omega | decide
  | oppositeReverse u v hfirst hsecond pair =>
      let P : EffectiveDisplayedF3PairTriple I scan :=
        .oppositeReverse u v hfirst hsecond pair
      change P.contraction.residualCoefficients (P.residualReindex i) =
        signedFourCoefficients P.residualShape i
      have hleft : P.leftIndex = I.slots (.inl u) := by
        change scan.candidate.second = I.slots (.inl u)
        exact hsecond
      have hright : P.rightIndex = I.slots (.inr v) := by
        change scan.candidate.first = I.slots (.inr v)
        exact hfirst
      rw [P.contraction_residualCoefficients_of_indices hleft hright]
      dsimp [P, EffectiveDisplayedF3PairTriple.residualReindex,
        EffectiveDisplayedF3PairTriple.residualShape,
        EffectiveDisplayedF3PairTriple.placement]
      fin_cases u <;> fin_cases v <;> fin_cases i <;>
        first | omega | decide

/-- The coefficient-correct residual in canonical one/three or two/two endpoint order. -/
def EffectiveDisplayedF3PairTriple.signedResidual
    {I : DisplayedF3PairTriple a b c}
    {scan : ScannedPairGauge I.x I.y I.z I.x_ne I.y_ne I.z_ne}
    (P : EffectiveDisplayedF3PairTriple I scan) :
    SignedMinimalFour F3 (Tensor F3 a b c) :=
  P.contraction.signedMinimalFour
    (minimalFive_vanishingRelation I.x I.y I.z I.minimal)
    P.residualReindex P.residualShape P.residual_coefficients_reindex

end FieldFiveToFour
end BilinearComplexity
