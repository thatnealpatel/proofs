import BilinearComplexity.NormalizedBinaryBoundedSearch
import BilinearComplexity.Basic

set_option autoImplicit false

/-!
# Frozen S-B1 bounded-search regression

This module transcribes the exact S-B1 artifact with SHA-256
`63bbfb5be99d49fee8686431b77f1a99f1a7fee777dfaf478b4be29a05a29ffa`.
It checks that exhaustive bounded search reduces its supplied three-term
normalized `𝔽₂` decomposition of the `⟨1,2,1⟩` tensor to two terms at budget
one. A separately proved reduction is used only as an optimality competitor;
it is not supplied to the optimizer.

AI disclosure: produced with AI assistance (see `Proofs/README`).
-/

namespace BilinearComplexity.NormalizedBinarySearchRegression

open BinaryCircuit
open NormalizedBinaryCarrier
open NormalizedBinaryReplay221
open NormalizedBinaryAllModeMove

/-- Exact contents of the externally frozen S-B1 JSON artifact, apart from its
terminal newline. -/
def fixtureJSON : String :=
  "{\"id\":\"S-B1\",\"field\":2,\"matmul_dimensions\":[1,2,1],\"factor_dimensions\":[2,2,1],\"coordinate_convention\":\"arrays in increasing Fin index; matmul third index packs (output-column,output-row)\",\"initial_terms\":[[[1,0],[1,0],[1]],[[1,0],[0,1],[1]],[[1,1],[0,1],[1]]],\"primary_budget\":{\"k\":1,\"H\":3},\"additional_budgets\":[{\"k\":0,\"H\":3},{\"k\":2,\"H\":3},{\"k\":3,\"H\":3},{\"k\":1,\"H\":4},{\"k\":2,\"H\":4},{\"k\":3,\"H\":4}],\"objective\":\"minimum endpoint finite-set cardinality over ALL native paths within budget\",\"native_moves\":[\"Split\",\"Flip\",\"directed Reduction\"],\"orientations\":\"all six\",\"pruning\":\"none except proved actual primitive length and intermediate cardinality checks\",\"execution_timeout_seconds\":60,\"execution_memory_limit_GiB\":4}"

example : fixtureJSON =
    "{\"id\":\"S-B1\",\"field\":2,\"matmul_dimensions\":[1,2,1],\"factor_dimensions\":[2,2,1],\"coordinate_convention\":\"arrays in increasing Fin index; matmul third index packs (output-column,output-row)\",\"initial_terms\":[[[1,0],[1,0],[1]],[[1,0],[0,1],[1]],[[1,1],[0,1],[1]]],\"primary_budget\":{\"k\":1,\"H\":3},\"additional_budgets\":[{\"k\":0,\"H\":3},{\"k\":2,\"H\":3},{\"k\":3,\"H\":3},{\"k\":1,\"H\":4},{\"k\":2,\"H\":4},{\"k\":3,\"H\":4}],\"objective\":\"minimum endpoint finite-set cardinality over ALL native paths within budget\",\"native_moves\":[\"Split\",\"Flip\",\"directed Reduction\"],\"orientations\":\"all six\",\"pruning\":\"none except proved actual primitive length and intermediate cardinality checks\",\"execution_timeout_seconds\":60,\"execution_memory_limit_GiB\":4}" := rfl

/-- Requested compiled-run matrix, extending the artifact's budgets by the
harmless zero-budget ceiling-four boundary case. -/
def declaredRuns : List (ℕ × ℕ) :=
  [(0, 3), (1, 3), (2, 3), (3, 3), (0, 4), (1, 4), (2, 4), (3, 4)]

example : declaredRuns.length = 8 := by decide
example : (1, 3) ∈ declaredRuns ∧ (3, 4) ∈ declaredRuns := by decide

/-- The artifact's third normalized term `([1,1],[0,1],[1])`. -/
def frozenThirdTerm : Term := (ep, e2, w)

example : frozenThirdTerm = (ep, e2, w) := rfl

/-- Exact normalized finite-set state transcribed from `initial_terms` in the
frozen S-B1 artifact. -/
def suppliedState : State221 := {E11, E12, frozenThirdTerm}

example : suppliedState = {E11, E12, (ep, e2, w)} := rfl

/-- The exact frozen supplied state has three distinct normalized terms. -/
theorem suppliedState_card : suppliedState.card = 3 := by decide

/-- The frozen supplied state evaluates to the `⟨1,2,1⟩`
matrix-multiplication tensor. -/
theorem suppliedState_evaluation :
    stateEvaluation suppliedState = matMulTensor F2 1 2 1 := by
  funext i j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;> decide

/-- The comparison state has two distinct normalized terms. -/
theorem comparisonState_card : S0.card = 2 := by decide

/-- The comparison state evaluates to the same target tensor. -/
theorem comparisonState_evaluation :
    stateEvaluation S0 = matMulTensor F2 1 2 1 := by
  funext i j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;> decide

/-- The artifact's last two terms share their second factor and legally reduce
to `E22`, leaving exactly the two-term comparison state. -/
theorem suppliedReduction :
    DirectedNarrowPairReduction E12 frozenThirdTerm E22 suppliedState S0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide

/-- A path of at most one all-mode edge from a three-term scheme cannot finish
with fewer than two terms. -/
theorem two_le_endpoint_card_of_length_le_one {p : Profile} {D E : State p}
    (path : MovePath (@AllModeMove p) D E)
    (hD : D.card = 3) (hlength : path.length ≤ 1) : 2 ≤ E.card := by
  cases path with
  | singleton => omega
  | snoc priorPath edge =>
      cases priorPath with
      | singleton =>
          rcases edge.card_change with h | h | h <;> omega
      | snoc priorPath priorEdge =>
          simp only [MovePath.length] at hlength
          omega

/-- A bounded path from cardinality three to cardinality two uses exactly one edge. -/
theorem path_length_eq_one_of_card_three_two {p : Profile} {D E : State p}
    (path : MovePath (@AllModeMove p) D E)
    (hD : D.card = 3) (hE : E.card = 2) (hlength : path.length ≤ 1) :
    path.length = 1 := by
  cases path with
  | singleton => omega
  | snoc priorPath edge =>
      simp only [MovePath.length] at hlength ⊢
      omega

/-- Every one-edge dependent path records exactly its source and target vertices. -/
theorem path_vertices_eq_pair_of_length_one {p : Profile} {D E : State p}
    (path : MovePath (@AllModeMove p) D E) (hlength : path.length = 1) :
    path.vertices = [D, E] := by
  cases path with
  | singleton =>
      simp only [MovePath.length] at hlength
      omega
  | snoc priorPath edge =>
      have hprior : priorPath.length = 0 := by
        simp only [MovePath.length] at hlength
        omega
      cases priorPath with
      | singleton => simp [MovePath.vertices]
      | snoc priorPath priorEdge =>
          simp only [MovePath.length] at hprior
          omega

/-- A zero-edge dependent path records only its source vertex. -/
theorem path_vertices_eq_singleton_of_length_zero {p : Profile} {D E : State p}
    (path : MovePath (@AllModeMove p) D E) (hlength : path.length = 0) :
    path.vertices = [D] := by
  cases path with
  | singleton => simp only [MovePath.vertices]
  | snoc priorPath edge =>
      simp only [MovePath.length] at hlength
      omega

/-- The independently proved legal reduction gives an optimality competitor;
it is not an input to executable search. -/
def comparisonPath : MovePath (@AllModeMove profile221) suppliedState S0 :=
  MovePath.one (allModeMove_of_move (.directedNarrowPairReduction suppliedReduction))

/-- The comparison path has one primitive edge. -/
theorem comparisonPath_length : comparisonPath.length = 1 := by
  simp only [comparisonPath, MovePath.one, MovePath.length]

/-- The comparison path records the exact supplied and comparison schemes. -/
theorem comparisonPath_vertices : comparisonPath.vertices = [suppliedState, S0] := by
  simp only [comparisonPath, MovePath.one, MovePath.vertices, List.singleton_append]

/-- The comparison path stays within ceiling three. -/
theorem comparisonPath_altitude : comparisonPath.altitude = 3 := by
  simp only [comparisonPath, MovePath.one, MovePath.altitude]
  rw [suppliedState_card, comparisonState_card]
  decide

/-- Executable exact-fixture result at budget zero and ceiling three. -/
def result0 : NormalizedBinaryBoundedSearch.Result suppliedState 0 3 :=
  NormalizedBinaryBoundedSearch.optimize suppliedState 0 3 (by decide)

/-- The zero-budget run returns the exact frozen supplied state. -/
theorem result0_finish : result0.finish = suppliedState := by
  exact NormalizedBinaryBoundedSearch.optimize_zero_finish suppliedState 3 (by decide)

/-- The zero-budget result has three terms. -/
theorem result0_card : result0.finish.card = 3 := by
  rw [result0_finish]
  exact suppliedState_card

/-- The zero-budget result records no edges and only its root vertex. -/
theorem result0_path_data :
    result0.path.length = 0 ∧ result0.path.vertices = [suppliedState] := by
  have hlength : result0.path.length = 0 := Nat.le_zero.mp result0.length_le
  exact ⟨hlength, path_vertices_eq_singleton_of_length_zero result0.path hlength⟩

/-- Executable exact-fixture result at budget one and ceiling three. -/
def result1 : NormalizedBinaryBoundedSearch.Result suppliedState 1 3 :=
  NormalizedBinaryBoundedSearch.optimize suppliedState 1 3 (by decide)

/-- The checked one-edge optimizer output has exactly two terms. -/
theorem result1_card : result1.finish.card = 2 := by
  apply Nat.le_antisymm
  · have hoptimal := result1.optimal comparisonPath
        comparisonPath_length.le comparisonPath_altitude.le
    simpa only [comparisonState_card] using hoptimal
  · exact two_le_endpoint_card_of_length_le_one result1.path
      suppliedState_card result1.length_le

/-- The selected exact-fixture path has one edge and records both endpoints. -/
theorem result1_path_data :
    result1.path.length = 1 ∧
      result1.path.vertices = [suppliedState, result1.finish] := by
  have hlength : result1.path.length = 1 :=
    path_length_eq_one_of_card_three_two result1.path suppliedState_card
      result1_card result1.length_le
  exact ⟨hlength, path_vertices_eq_pair_of_length_one result1.path hlength⟩

/-- The discovered two-term scheme evaluates to the frozen target tensor. -/
theorem result1_evaluation :
    stateEvaluation result1.finish = matMulTensor F2 1 2 1 := by
  rw [NormalizedBinaryBoundedSearch.Result.preserves_evaluation result1]
  exact suppliedState_evaluation

/-- The `(1,1,1)` profile used for the tight-ceiling boundary regression. -/
def unitProfile : Profile := ⟨1, 1, 1⟩

example : unitProfile = Profile.homogeneous 1 := rfl

/-- The unique normalized carrier term at the `(1,1,1)` profile. -/
def unitTerm : Carrier unitProfile := (w, w, w)

example : unitTerm = (w, w, w) := rfl

/-- The singleton state at the `(1,1,1)` profile. -/
def unitState : State unitProfile := {unitTerm}

example : unitState.card = 1 := by decide

/-- Deliberately malformed split data whose two proposed outputs are equal. -/
def duplicateOutputSplitData :
    NormalizedBinaryAllModeMoveData.SourceMoveData unitProfile :=
  .split unitTerm unitTerm unitTerm

/-- The exact legality checker rejects equal split outputs at the distinctness guard. -/
theorem duplicateOutputSplitData_rejected :
    duplicateOutputSplitData.step? unitState = none := by
  have hillegal : ¬ duplicateOutputSplitData.Legal unitState := by
    intro hlegal
    exact hlegal.2.1 rfl
  simp only [NormalizedBinaryAllModeMoveData.SourceMoveData.step?, hillegal,
    ↓reduceIte]

/-- A state in which `E21`, one proposed split output, remains occupied after
removing the source `E11`. -/
def occupiedFreshSplitState : State221 := {E11, E21}

example : occupiedFreshSplitState = {E11, E21} := rfl

/-- Structurally valid split data `E11 ↦ E21 + E31` whose left output collides
with an existing term. -/
def occupiedFreshSplitData :
    NormalizedBinaryAllModeMoveData.SourceMoveData profile221 :=
  .split E11 E21 E31

/-- The source and both proposed outputs have nonzero factors, as guaranteed by
the normalized carrier but recorded explicitly for this regression. -/
theorem occupiedFreshSplit_nonzero :
    E11.1.1 ≠ 0 ∧ E11.2.1.1 ≠ 0 ∧ E11.2.2.1 ≠ 0 ∧
    E21.1.1 ≠ 0 ∧ E21.2.1.1 ≠ 0 ∧ E21.2.2.1 ≠ 0 ∧
    E31.1.1 ≠ 0 ∧ E31.2.1.1 ≠ 0 ∧ E31.2.2.1 ≠ 0 := by
  exact ⟨E11.1.2, E11.2.1.2, E11.2.2.2,
    E21.1.2, E21.2.1.2, E21.2.2.2,
    E31.1.2, E31.2.1.2, E31.2.2.2⟩

/-- Apart from freshness, the proposed split has a present source, distinct
outputs, the correct first-factor sum, and the required shared factors. -/
theorem occupiedFreshSplit_structural_guards :
    E11 ∈ occupiedFreshSplitState ∧
    E21 ≠ E31 ∧
    E11.1.1 = E21.1.1 + E31.1.1 ∧
    E21.2.1.1 = E11.2.1.1 ∧ E31.2.1.1 = E11.2.1.1 ∧
    E21.2.2.1 = E11.2.2.1 ∧ E31.2.2.1 = E11.2.2.1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide

/-- `E21` survives erasing the distinct source, while the other output `E31`
is genuinely fresh. -/
theorem occupiedFreshSplit_collision :
    E21 ∈ occupiedFreshSplitState.erase E11 ∧
    E31 ∉ occupiedFreshSplitState.erase E11 := by
  constructor <;> decide

/-- The exact legality checker rejects the otherwise valid split specifically
because the occupied output `E21` violates its freshness guard. -/
theorem occupiedFreshSplitData_rejected :
    occupiedFreshSplitData.step? occupiedFreshSplitState = none := by
  have hillegal : ¬ occupiedFreshSplitData.Legal occupiedFreshSplitState := by
    intro hlegal
    exact hlegal.2.2.1 occupiedFreshSplit_collision.1
  simp only [NormalizedBinaryAllModeMoveData.SourceMoveData.step?, hillegal,
    ↓reduceIte]

/-- Tight-ceiling one-edge search at profile `(1,1,1)`; its ground evaluation
below checks that the singleton root is retained with a zero-edge path. -/
def unitResult : NormalizedBinaryBoundedSearch.Result unitState 1 1 :=
  NormalizedBinaryBoundedSearch.optimize unitState 1 1 (by decide)

#eval fixtureJSON
#eval suppliedState
#eval
  (result0.finish.card, result0.path.length, result0.path.vertices.map Finset.card)
#eval
  (result1.finish.card, result1.path.length, result1.path.vertices.map Finset.card)
#eval result1.finish
#eval (unitResult.finish.card, unitResult.path.length)

#check @suppliedState
#check @result0
#check @result1
#check @result1_card
#check @result1_path_data
#check @result1_evaluation
#print axioms suppliedState_evaluation
#print axioms suppliedReduction
#print axioms result0_finish
#print axioms result1_card
#print axioms result1_path_data
#print axioms result1_evaluation
#print axioms duplicateOutputSplitData_rejected
#print axioms occupiedFreshSplit_nonzero
#print axioms occupiedFreshSplit_structural_guards
#print axioms occupiedFreshSplit_collision
#print axioms occupiedFreshSplitData_rejected

end BilinearComplexity.NormalizedBinarySearchRegression
