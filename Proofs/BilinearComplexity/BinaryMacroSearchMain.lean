import BilinearComplexity.BinaryMacroBoundedSearch
import BilinearComplexity.NormalizedBinarySearchRegression
import BilinearComplexity.BinaryContextBorrowing221

set_option autoImplicit false

/-!
# Native primitive/macro comparison driver

The two optimizing modes share the frozen S-B1 input, identity full frames,
primitive budget, ceiling, and minimum endpoint-cardinality objective. The
activated mode only enumerates automatically admitted one-block macro traces;
it makes no endpoint-optimality assertion. No closed borrowing search result is
constructed at module initialization.

JSON coordinates use increasing `Fin` indices inside a term, and effective
`FinEnum` carrier order between terms. Runtime replay checks use the complete
public primitive successor API; they are additional execution evidence, not
proofs of optimality. The imported optimizer and trace-factorization theorems
supply the kernel-checked contracts.
-/

namespace BilinearComplexity.BinaryMacroSearchMain

open BinaryCircuit NormalizedBinaryCarrier
open BinaryAmbientTensorCoordinates
open BinaryContextualMacroRecognition
open NormalizedBinaryOrbitClassification

local instance : FinEnum F2 := FinEnum.ofList [0, 1] (by decide)
local instance : DecidableEq (State profile221) :=
  @Finset.decidableEq (Carrier profile221) inferInstance

/-- The common effective identity frame on the first two-dimensional factor. -/
abbrev firstFrame := LinearEquiv.refl F2 (Coord 2)

/-- The common effective identity frame on the second two-dimensional factor. -/
abbrev secondFrame := LinearEquiv.refl F2 (Coord 2)

/-- The common effective identity frame on the third one-dimensional factor. -/
abbrev thirdFrame := LinearEquiv.refl F2 (Coord 1)

example (x : Coord 2) : firstFrame x = x := rfl
example (x : Coord 2) : secondFrame x = x := rfl
example (x : Coord 1) : thirdFrame x = x := rfl

/-- Serialize the three nonzero factor vectors in increasing coordinate order. -/
def termJSON {p : Profile} (t : Carrier p) : Lean.Json :=
  Lean.toJson [List.ofFn fun i => (t.1.1 i).val,
    List.ofFn fun j => (t.2.1.1 j).val,
    List.ofFn fun l => (t.2.2.1 l).val]

example : termJSON NormalizedBinaryReplay221.E11 =
    Lean.toJson ([[1, 0], [1, 0], [1]] : List (List ℕ)) := rfl

/-- Serialize exactly the occupied terms, ordered by constructive carrier
enumeration rather than a choice-backed ordering of the finite set. -/
def stateJSON {p : Profile} (D : State p) : Lean.Json :=
  Lean.Json.arr (((FinEnum.toList (Carrier p)).filter fun t => t ∈ D).map
    termJSON).toArray

example : stateJSON (∅ : State profile221) = Lean.Json.arr #[] := by
  simp [stateJSON]

/-- Serialize all four tensor coordinates of a profile-221 state, with axis
order first, second, third and increasing coordinate indices on each axis. -/
def evaluationJSON (D : State profile221) : Lean.Json :=
  Lean.toJson (List.ofFn fun i => List.ofFn fun j => List.ofFn fun l =>
    (stateEvaluation D i j l).val)

example : evaluationJSON ∅ =
    Lean.toJson ([[[0], [0]], [[0], [0]]] : List (List (List ℕ))) := rfl

/-- Reconstruct a state from the constructive carrier enumeration. This
computable scan replaces function-valued representatives by canonical carrier
representatives while preserving the finite set exactly. -/
def canonicalReplayState {p : Profile} (D : State p) : State p :=
  ((FinEnum.toList (Carrier p)).filter fun t => t ∈ D).toFinset

example : canonicalReplayState (∅ : State profile221) = ∅ := by
  simp [canonicalReplayState]

/-- Canonical replay reconstruction is pointwise the identity on every
normalized binary state. -/
theorem canonicalReplayState_eq {p : Profile} (D : State p) :
    canonicalReplayState D = D := by
  ext t
  simp only [canonicalReplayState, List.mem_toFinset, List.mem_filter,
    decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨FinEnum.mem_toList t, h⟩⟩

/-- Independently replay each consecutive vertex pair by membership in the
public complete six-orientation primitive successor enumeration. Canonical
state reconstruction changes representatives only, not this membership test. -/
def edgeReplay (vertices : List (State profile221)) : List Bool :=
  (vertices.zip vertices.tail).map fun pair =>
    decide (canonicalReplayState pair.2 ∈
      NormalizedBinaryNativeSuccessors.successors (canonicalReplayState pair.1))

/-- Canonical replay produces literally the same Boolean list as direct
membership in the unchanged complete native successor enumeration. -/
theorem edgeReplay_eq_direct (vertices : List (State profile221)) :
    edgeReplay vertices =
      (vertices.zip vertices.tail).map fun pair =>
        decide (pair.2 ∈ NormalizedBinaryNativeSuccessors.successors pair.1) := by
  simp only [edgeReplay, canonicalReplayState_eq]

example : edgeReplay [NormalizedBinarySearchRegression.suppliedState] = [] := rfl

/-- Common actual path data and executable coordinate-evaluation, primitive
replay, endpoint, and budget checks. No optimum is inferred from these checks. -/
def pathFields {D E : State profile221}
    (path : MovePath (BinaryAmbientMoves.AllModeMove
      (U := Coord 2) (V := Coord 2) (W := Coord 1)) D E)
    (k H : ℕ) : List (String × Lean.Json) :=
  let vertices : List (State profile221) := path.vertices
  let replay := edgeReplay vertices
  [("initial", stateJSON D), ("finish", stateJSON E),
    ("initial_card", Lean.toJson D.card), ("card", Lean.toJson E.card),
    ("length", Lean.toJson path.length), ("altitude", Lean.toJson path.altitude),
    ("vertex_cards", Lean.toJson (vertices.map Finset.card)),
    ("vertices", Lean.Json.arr (vertices.map stateJSON).toArray),
    ("initial_evaluation", evaluationJSON D), ("finish_evaluation", evaluationJSON E),
    ("checks", Lean.Json.mkObj [
      ("length_le_k", Lean.toJson (decide (path.length ≤ k))),
      ("altitude_le_H", Lean.toJson (decide (path.altitude ≤ H))),
      ("vertices_length", Lean.toJson (decide (vertices.length = path.length + 1))),
      ("endpoints", Lean.toJson (decide (vertices.head? = some D ∧ vertices.getLast? = some E))),
      ("evaluation_preserved", Lean.toJson (decide (stateEvaluation E = stateEvaluation D))),
      ("all_vertex_evaluations", Lean.toJson (vertices.all fun X =>
        decide (stateEvaluation X = stateEvaluation D))),
      ("edge_replay", Lean.toJson replay),
      ("all_edges_replay", Lean.toJson (replay.all id))])]

example : (pathFields (MovePath.singleton (∅ : State profile221)) 0 0).head? =
    some ("initial", Lean.Json.arr #[]) := by
  simp [pathFields, stateJSON]

/-- A public semantic orbit identifier: canonical family and zero-based replay
row. This is computed from the recognized compiler object, not supplied by CLI. -/
def orbitFields (label : OrbitLabel) : List (String × Lean.Json) :=
  let familyRow : String × ℕ := match label with
    | ⟨.family221, row⟩ => ("221", row.val)
    | ⟨.family411, row⟩ => ("411", row.val)
    | ⟨.family321, row⟩ => ("321", row.val)
    | ⟨.family222, row⟩ => ("222", row.val)
  [("family", Lean.toJson familyRow.1), ("row", Lean.toJson familyRow.2)]

example : orbitFields ⟨.family221, (0 : Fin 3)⟩ =
    [("family", Lean.toJson "221"), ("row", Lean.toJson (0 : ℕ))] := rfl

/-- Serialize an admitted cached macro at its dependent intermediate source,
including recovered endpoints/context, compiler orbit/distance, retained path,
and a check that its vertices form a segment of the selected native path. -/
def macroFields {D : State profile221}
    (cached : BinaryMacroBoundedSearch.CachedMacro firstFrame secondFrame thirdFrame D)
    (wholeVertices : List (State profile221)) (k H : ℕ) : List (String × Lean.Json) :=
  let result := cached.result
  let path := cached.path
  let macroVertices : List (State profile221) := path.vertices
  let label := result.compilation.label
  let direction := match result.key.direction with
    | .forward => "forward"
    | .reverse => "reverse"
  [("source", stateJSON D), ("direction", Lean.toJson direction),
    ("left", stateJSON (p := profile221) result.left),
    ("right", stateJSON (p := profile221) result.right),
    ("context", stateJSON (p := profile221) result.context),
    ("context_card", Lean.toJson result.context.card),
    ("distance", Lean.toJson (NormalizedBinaryContextualCompiler.orbitDistance label)),
    ("vertices_occur_in_selected_path", Lean.toJson
      ((List.range (wholeVertices.length + 1)).any fun offset =>
        decide ((wholeVertices.drop offset).take macroVertices.length = macroVertices)))] ++
    orbitFields label ++ pathFields path k H

example {D : State profile221}
    (cached : BinaryMacroBoundedSearch.CachedMacro firstFrame secondFrame thirdFrame D)
    (vertices : List (State profile221)) (k H : ℕ) :
    (macroFields cached vertices k H).head? = some ("source", stateJSON D) := rfl

/-- Serialize the actual cached candidate path and retained per-macro paths.
`Candidate.expands`, `Trace.cachedMacros_results`, and
`Trace.cached_macro_factorization` connect the serialized data to the existing
semantic macro trace, while `Candidate.cached_macro_factorization` gives literal
segments of the returned native path without recomputing macro paths. -/
def candidateFields {D : State profile221} {k H : ℕ}
    (candidate : BinaryMacroBoundedSearch.Candidate firstFrame secondFrame thirdFrame k H D) :
    List (String × Lean.Json) :=
  let path := candidate.path firstFrame secondFrame thirdFrame
  let macros := candidate.trace.cachedMacros firstFrame secondFrame thirdFrame
  pathFields path k H ++ [("macro_count", Lean.toJson macros.length),
    ("macros", Lean.Json.arr (macros.map fun entry =>
      Lean.Json.mkObj (macroFields entry.2 path.vertices k H)).toArray)]

example : candidateFields (BinaryMacroBoundedSearch.Candidate.root
    firstFrame secondFrame thirdFrame 0 0 (∅ : State profile221)) =
    pathFields (MovePath.singleton (∅ : State profile221)) 0 0 ++
      [("macro_count", Lean.toJson (0 : ℕ)), ("macros", Lean.Json.arr #[])] := rfl

/-- Shared benchmark input and objective metadata, with no search execution. -/
def runFields (mode fixture : String) (k H : ℕ) : List (String × Lean.Json) :=
  [("schema", Lean.toJson "binary-native-macro-v1"),
    ("mode", Lean.toJson mode), ("case", Lean.toJson fixture),
    ("field", Lean.toJson (2 : ℕ)),
    ("factor_dimensions", Lean.toJson ([2, 2, 1] : List ℕ)),
    ("frames", Lean.toJson "identity"),
    ("coordinate_order", Lean.toJson "FinEnum carrier; increasing Fin indices within factors"),
    ("k", Lean.toJson k), ("H", Lean.toJson H)]

example : (runFields "primitive" "S-B1" 0 3).head? =
    some ("schema", Lean.toJson "binary-native-macro-v1") := rfl

/-- Run one primitive-only optimum on the unchanged frozen input, rejecting
ceilings below its cardinality before calling the public ambient optimizer. -/
def runPrimitive (k H : ℕ) : IO Unit := do
  let D := NormalizedBinarySearchRegression.suppliedState
  if hD : D.card ≤ H then
    let result := BinaryAmbientBoundedSearch.optimize firstFrame secondFrame thirdFrame D k H hD
    IO.println (Lean.Json.mkObj (runFields "primitive" "S-B1" k H ++
      [("claim", Lean.toJson "bounded endpoint-cardinality optimum"),
        ("macro_count", Lean.toJson (0 : ℕ)), ("macros", Lean.Json.arr #[])] ++
      pathFields result.path k H)).compress
  else
    throw (IO.userError "invalid ceiling: H must be at least the initial cardinality")

/-- Run the oracle-free macro-assisted optimum on exactly the same initial
state and frames as primitive mode, preserving the actual selected trace. -/
def runMacro (k H : ℕ) : IO Unit := do
  let D := NormalizedBinarySearchRegression.suppliedState
  if hD : D.card ≤ H then
    let result := BinaryMacroBoundedSearch.optimize firstFrame secondFrame thirdFrame D k H hD
    IO.println (Lean.Json.mkObj (runFields "macro" "S-B1" k H ++
      [("claim", Lean.toJson "bounded endpoint-cardinality optimum")] ++
      candidateFields result.toCandidate)).compress
  else
    throw (IO.userError "invalid ceiling: H must be at least the initial cardinality")

/-- Automatically recognize macros on the declared borrowing fixture and
extend a typed root by each returned step. Empty admission is an error. No key,
presentation, compiler path, or closed candidate constant is supplied. -/
def runActivated (k H : ℕ) : IO Unit := do
  let D := BinaryContextBorrowing221.contextualStart
  if D.card ≤ H then
    let steps := BinaryMacroBoundedSearch.macroSteps firstFrame secondFrame thirdFrame D k H
    let root := BinaryMacroBoundedSearch.Candidate.root firstFrame secondFrame thirdFrame k H D
    let candidates := steps.map (root.extend firstFrame secondFrame thirdFrame)
    if candidates.isEmpty then
      throw (IO.userError "activated: no automatically admitted macro steps")
    else
      IO.println (Lean.Json.mkObj (runFields "activated" "borrowing-activation" k H ++
        [("claim", Lean.toJson "automatic one-block macro activation; not an endpoint optimum"),
          ("initial", stateJSON D), ("initial_card", Lean.toJson D.card),
          ("admitted_count", Lean.toJson candidates.length),
          ("candidates", Lean.Json.arr (candidates.map fun candidate =>
            Lean.Json.mkObj (candidateFields candidate)).toArray)])).compress
  else
    throw (IO.userError "invalid ceiling: H must be at least the initial cardinality")

example : runPrimitive 0 2 =
    throw (IO.userError "invalid ceiling: H must be at least the initial cardinality") := rfl
example : runMacro 0 2 =
    throw (IO.userError "invalid ceiling: H must be at least the initial cardinality") := rfl
example : runActivated 0 0 =
    throw (IO.userError "invalid ceiling: H must be at least the initial cardinality") := rfl

example : NormalizedBinarySearchRegression.suppliedState.card ≤ 3 ∧
    BinaryContextBorrowing221.contextualStart.card ≤ 7 := by decide
example : Nonempty (Carrier profile221) := ⟨NormalizedBinaryReplay221.E11⟩
example : Nonempty (Fin 2) ∧ Nonempty (Fin 1) := ⟨⟨0⟩, ⟨0⟩⟩

#check @canonicalReplayState
#check @canonicalReplayState_eq
#check @edgeReplay_eq_direct
#print axioms canonicalReplayState_eq
#print axioms edgeReplay_eq_direct
#check @macroFields
#check @candidateFields
#check @BinaryMacroBoundedSearch.Candidate.cached_macro_factorization
#print axioms BinaryMacroBoundedSearch.Candidate.cached_macro_factorization
#check @BinaryMacroBoundedSearch.Trace.cachedMacros_results
#check @BinaryMacroBoundedSearch.Trace.cached_macro_factorization
#print axioms BinaryMacroBoundedSearch.Trace.cachedMacros_results
#print axioms BinaryMacroBoundedSearch.Trace.cached_macro_factorization
#check @BinaryMacroBoundedSearch.Result.macro_factorization
#check @BinaryMacroBoundedSearch.optimize_card_eq_primitive
#print axioms runPrimitive
#print axioms runMacro
#print axioms runActivated
#print axioms BinaryMacroBoundedSearch.Result.macro_factorization
#print axioms BinaryMacroBoundedSearch.optimize_card_eq_primitive

end BilinearComplexity.BinaryMacroSearchMain

/-- One explicitly requested run per process; successful execution emits exactly
one JSON object. Budgets must be natural numbers and ceilings must admit the root. -/
def main (args : List String) : IO Unit := do
  match args with
  | [mode, k, H] =>
      let run := match mode with
        | "primitive" => BilinearComplexity.BinaryMacroSearchMain.runPrimitive
        | "macro" => BilinearComplexity.BinaryMacroSearchMain.runMacro
        | "activated" => BilinearComplexity.BinaryMacroSearchMain.runActivated
        | _ => fun _ _ => throw (IO.userError "usage: binary-macro-search (primitive|macro|activated) k H")
      match k.toNat?, H.toNat? with
      | some k, some H => run k H
      | _, _ => throw (IO.userError "k and H must be natural numbers")
  | _ => throw (IO.userError "usage: binary-macro-search (primitive|macro|activated) k H")

example : main [] =
    throw (IO.userError "usage: binary-macro-search (primitive|macro|activated) k H") := rfl

#check @main
#print axioms main
