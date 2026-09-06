import BilinearComplexity.FieldFiveToFourRegression
import BilinearComplexity.FieldFiveToFourContext
import BilinearComplexity.FieldThreeProductCircuit

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace BilinearComplexity
namespace TestFirst01ScanRewrite

open FieldRankOne FieldContextual FieldNativeMoves FieldNativePath
open FieldFiveCircuitProfile FieldCircuitContraction FieldNativePairBridge
open FieldFiveToFour FieldNativeExecutablePath FieldThreeProductCircuit
open FieldTernaryFiveCircuitPair
open FieldFiveToFourRegression

abbrev F3 := FieldFiveToFour.F3

def transparentCandidateValidDecidable {a b c : ℕ} (candidate : Candidate)
    (x : Fin 5 → Fin a → F3) (y : Fin 5 → Fin b → F3)
    (z : Fin 5 → Fin c → F3) : Decidable (candidate.Valid x y z) := by
  unfold Candidate.Valid
  cases candidate.orientation <;> infer_instance

def transparentScan {a b c : ℕ} (x : Fin 5 → Fin a → F3)
    (y : Fin 5 → Fin b → F3) (z : Fin 5 → Fin c → F3) : Option Candidate :=
  candidates.find? fun candidate =>
    @decide (candidate.Valid x y z) (transparentCandidateValidDecidable candidate x y z)

theorem scan_eq_transparentScan {a b c : ℕ} (x : Fin 5 → Fin a → F3)
    (y : Fin 5 → Fin b → F3) (z : Fin 5 → Fin c → F3) :
    scan x y z = transparentScan x y z := by
  unfold scan transparentScan
  congr 1

theorem first01_scan_execution : scan first01.x first01.y first01.z =
    some ⟨0, 1, .yz, 1, 1⟩ := by
  rw [scan_eq_transparentScan]
  decide

theorem bridgeFirst01_candidate : bridgeFirst01.scan.candidate = ⟨0, 1, .yz, 1, 1⟩ := by
  unfold bridgeFirst01 certifiedFiveToFour FieldNativePairBridge.certifiedScanGauge
  simp only [FieldTernaryFiveCircuitPair.certifiedScan, first01_scan_execution,
    Option.get_some]

example : bridgeFirst01.normalized.placement = .sourceSource := by
  unfold bridgeFirst01 certifiedFiveToFour FieldNativePairBridge.certifiedScanGauge
  simp only [FieldTernaryFiveCircuitPair.certifiedScan, first01_scan_execution,
    Option.get_some]
  decide

example : bridgeFirst01.normalized.leftIndex = 0 := by
  unfold bridgeFirst01 certifiedFiveToFour FieldNativePairBridge.certifiedScanGauge
  simp only [FieldTernaryFiveCircuitPair.certifiedScan, first01_scan_execution,
    Option.get_some]
  decide

example : bridgeFirst01.normalized.rightIndex = 1 := by
  unfold bridgeFirst01 certifiedFiveToFour FieldNativePairBridge.certifiedScanGauge
  simp only [FieldTernaryFiveCircuitPair.certifiedScan, first01_scan_execution,
    Option.get_some]
  decide

end TestFirst01ScanRewrite
end BilinearComplexity
