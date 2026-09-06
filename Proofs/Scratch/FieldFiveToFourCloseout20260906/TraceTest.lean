import Proofs.Scratch.FieldFiveToFourRegressionContextWIP

set_option autoImplicit false

namespace BilinearComplexity.FieldFiveToFourRegression
open FieldNativeMoves FieldNativePairBridge FieldNativeExecutablePath

private abbrev A (i : Fin 4) := bridgeFirst01.signedResidualAtom i
private abbrev M := first01Middle
private abbrev D : State F3 5 1 1 := ComputedState.singleton (A 0)
private abbrev D₁ : State F3 5 1 1 := ComputedState.pair (A 1) M
private abbrev E : State F3 5 1 1 :=
  ComputedState.union (ComputedState.singleton (A 1))
    (ComputedState.pair (A 2) (A 3))

def canonPacket : Packet F3 5 1 1 where
  start := D
  finish := E
  path := first01CanonicalPath

example : (canonPacket.stateTrace).length = 3 := by
  rw [Packet.stateTrace_length]
  exact Nat.succ.inj (by
    unfold first01CanonicalPath actualTwoStepPath
    rw [FieldFiveToFourContext.CertifiedFiveToFour.Executable.length_castPath]
    rfl)

example : (canonPacket.localEndpointTrace).length = 2 := by
  rw [Packet.localEndpointTrace_length]
  unfold first01CanonicalPath actualTwoStepPath
  rw [FieldFiveToFourContext.CertifiedFiveToFour.Executable.length_castPath]
  rfl

example : FieldNativePairBridge.Path.length
    (FieldNativeExecutablePath.reverse first01CanonicalPath) = 2 := by
  rw [FieldNativeExecutablePath.length_reverse]
  unfold first01CanonicalPath actualTwoStepPath
  rw [FieldFiveToFourContext.CertifiedFiveToFour.Executable.length_castPath]
  rfl

example : (FieldNativeExecutablePath.stateTrace E
    (FieldNativeExecutablePath.reverse first01CanonicalPath)).length = 3 := by
  rw [FieldNativeExecutablePath.stateTrace_length,
    FieldNativeExecutablePath.length_reverse]
  unfold first01CanonicalPath actualTwoStepPath
  rw [FieldFiveToFourContext.CertifiedFiveToFour.Executable.length_castPath]
  rfl

example : canonPacket.stateTrace = [D, D₁, E] := by
  unfold canonPacket Packet.stateTrace first01CanonicalPath actualTwoStepPath
  simp only [FieldFiveToFourContext.CertifiedFiveToFour.Executable.castPath]
  rfl

example : canonPacket.localEndpointTrace =
    [(ComputedState.singleton (A 0), ComputedState.pair (A 1) M),
      (ComputedState.singleton M, ComputedState.pair (A 2) (A 3))] := by
  unfold canonPacket Packet.localEndpointTrace first01CanonicalPath actualTwoStepPath
  simp only [FieldFiveToFourContext.CertifiedFiveToFour.Executable.castPath]
  rfl

example : FieldNativeExecutablePath.stateTrace E
    (FieldNativeExecutablePath.reverse first01CanonicalPath) = [E, D₁, D] := by
  unfold first01CanonicalPath actualTwoStepPath
  simp only [FieldFiveToFourContext.CertifiedFiveToFour.Executable.castPath]
  rfl

end BilinearComplexity.FieldFiveToFourRegression
