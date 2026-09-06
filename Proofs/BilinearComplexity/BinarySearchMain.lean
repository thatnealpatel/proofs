import BilinearComplexity.NormalizedBinarySearchRegression
import BilinearComplexity.BinaryMatMulRankCertificate

set_option autoImplicit false

open BilinearComplexity
open NormalizedBinaryCarrier

local instance : FinEnum F2 := FinEnum.ofList [0, 1] (by decide)

/-- Serialize a normalized binary term in increasing coordinate-index order. -/
def binaryTermJSON {p : Profile} (t : Carrier p) : Lean.Json :=
  Lean.toJson [List.ofFn fun i => (t.1.1 i).val,
    List.ofFn fun j => (t.2.1.1 j).val,
    List.ofFn fun l => (t.2.2.1 l).val]

/-- Serialize the actual coordinate triples in constructive finite-carrier order.
Enumeration avoids a noncomputable choice of ordering for the finite set. -/
def binaryStateJSON {p : Profile} (D : State p) : Lean.Json :=
  Lean.Json.arr (((FinEnum.toList (Carrier p)).filter fun t => t ∈ D).map
    binaryTermJSON).toArray

/-- Execute the complete successor API on the baseline profile-221 state.
The count includes duplicate presentations and is not a rank optimum. -/
def runSuccessors : IO Unit :=
  IO.println (Lean.Json.mkObj [
    ("case", Lean.toJson "native-successors-221"),
    ("successor_presentations", Lean.toJson
      (NormalizedBinaryNativeSuccessors.successors NormalizedBinaryReplay221.S0).length)]).compress

/-- Execute the independently certified seven-term binary Strassen state check. -/
def runRankCertificate : IO Unit :=
  IO.println (Lean.Json.mkObj [
    ("case", Lean.toJson "binary-matmul-222-rank-certificate"),
    ("card", Lean.toJson BinaryMatMulRankCertificate.strassenState.card),
    ("evaluation_matches", Lean.toJson
      BinaryMatMulRankCertificate.strassenStateEvaluationMatches)]).compress

/-- Run the frozen rectangular multiplication input through the public bounded
optimizer and print every actual path vertex and its primitive-budget data. -/
def runSB1 (k H : ℕ) : IO Unit := do
  let D := NormalizedBinarySearchRegression.suppliedState
  if hD : D.card ≤ H then
    let result := NormalizedBinaryBoundedSearch.optimize D k H hD
    IO.println (Lean.Json.mkObj [
      ("case", Lean.toJson "S-B1"),
      ("k", Lean.toJson k), ("H", Lean.toJson H),
      ("initial", binaryStateJSON D),
      ("finish", binaryStateJSON result.finish),
      ("card", Lean.toJson result.finish.card),
      ("length", Lean.toJson result.path.length),
      ("altitude", Lean.toJson result.path.altitude),
      ("vertex_cards", Lean.toJson (result.path.vertices.map Finset.card)),
      ("vertices", Lean.Json.arr (result.path.vertices.map binaryStateJSON).toArray)]).compress
  else
    throw (IO.userError "invalid ceiling: H must be at least the initial cardinality")

/-- Standalone public-API driver. Individual runs admit separate resource limits;
the default executes the successor, rank, and priority S-B1 checks. -/
def main (args : List String) : IO Unit := do
  match args with
  | [] =>
      runSuccessors
      runRankCertificate
      runSB1 0 3
      runSB1 1 3
  | ["successors"] => runSuccessors
  | ["rank"] => runRankCertificate
  | ["sb1", k, H] =>
      match k.toNat?, H.toNat? with
      | some k, some H => runSB1 k H
      | _, _ => throw (IO.userError "k and H must be natural numbers")
  | _ => throw (IO.userError "usage: binary-search [successors|rank|sb1 k H]")

example : binaryStateJSON (∅ : State ⟨0, 0, 0⟩) = Lean.Json.arr #[] := by
  simp [binaryStateJSON]

#check @binaryTermJSON
#check @binaryStateJSON
#print axioms runSB1
