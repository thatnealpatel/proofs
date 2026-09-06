import BilinearComplexity.NormalizedBinaryContextual221
import BilinearComplexity.NormalizedBinaryContextual411
import BilinearComplexity.NormalizedBinaryContextual321
import BilinearComplexity.NormalizedBinaryContextual222
import BilinearComplexity.NormalizedBinaryOrbitClassification

set_option autoImplicit false

/-!
# Uniform contextual compiler for the thirteen normalized binary rows

This module packages the four generated profile modules behind the semantic
`OrbitLabel` API.  Its paths retain the original production row endpoints by
definitional reduction, work in every endpoint-disjoint finite context, and
have the canonical constructed lengths and local altitude bound.  The length
table is not identified with shortest-path distance in this module.
-/

namespace BilinearComplexity.NormalizedBinaryContextualCompiler

open BinaryCircuit
open NormalizedBinaryAllModeMove
open NormalizedBinaryCarrier
open NormalizedBinaryContextualCertificates
open NormalizedBinaryFiveCircuitRows
open NormalizedBinaryOrbitClassification

/-- The canonical orbit-distance table for normalized labels.
This module establishes constructed witness lengths; the downstream module
`BinaryContextualFiveCircuitOptimality` proves their global shortestness. -/
def orbitDistance : OrbitLabel → Nat
  | ⟨.family221, _⟩ => 2
  | ⟨.family411, _⟩ => 3
  | ⟨.family321, index⟩ => if index.1 < 3 then 3 else 2
  | ⟨.family222, index⟩ => if index.1 = 0 then 3 else 2

example : orbitDistance (⟨.family221, (0 : Fin 3)⟩ : OrbitLabel) = 2 := rfl
example : orbitDistance (⟨.family411, (0 : Fin 1)⟩ : OrbitLabel) = 3 := rfl
example : orbitDistance (⟨.family321, (2 : Fin 6)⟩ : OrbitLabel) = 3 := by decide
example : orbitDistance (⟨.family321, (3 : Fin 6)⟩ : OrbitLabel) = 2 := by decide
example : orbitDistance (⟨.family222, (0 : Fin 3)⟩ : OrbitLabel) = 3 := by decide
example : orbitDistance (⟨.family222, (1 : Fin 3)⟩ : OrbitLabel) = 2 := by decide

/-- Every canonical constructed length is at most three. -/
theorem orbitDistance_le_three (label : OrbitLabel) : orbitDistance label ≤ 3 := by
  rcases label with ⟨family, index⟩
  cases family <;> fin_cases index <;> decide

/-- Every canonical constructed length is either two or three. -/
theorem orbitDistance_two_or_three (label : OrbitLabel) :
    orbitDistance label = 2 ∨ orbitDistance label = 3 := by
  rcases label with ⟨family, index⟩
  cases family <;> fin_cases index <;> decide


/-- The actual forward path used by the packaged compiler. -/
private def orbitLabelForwardActualPath (label : OrbitLabel)
    (K : State label.1.profile)
    (hK : Disjoint K
      (label.selectedEndpoints.left ∪ label.selectedEndpoints.right)) :
    MovePath (@AllModeMove label.1.profile)
      (K ∪ label.selectedEndpoints.left)
      (K ∪ label.selectedEndpoints.right) := by
  rcases label with ⟨family, index⟩
  cases family with
  | family221 =>
      change Fin 3 at index
      revert K
      refine Fin.cases ?_ ?_ index
      · exact row22101ForwardContextualPath
      · intro index
        refine Fin.cases ?_ ?_ index
        · exact row22102ForwardContextualPath
        · intro index
          refine Fin.cases ?_ ?_ index
          · exact row22103ForwardContextualPath
          · intro index
            exact Fin.elim0 index
  | family411 =>
      change Fin 1 at index
      revert K
      refine Fin.cases ?_ ?_ index
      · exact row41101ForwardContextualPath
      · intro index
        exact Fin.elim0 index
  | family321 =>
      change Fin 6 at index
      revert K
      refine Fin.cases ?_ ?_ index
      · exact row32101ForwardContextualPath
      · intro index
        refine Fin.cases ?_ ?_ index
        · exact row32102ForwardContextualPath
        · intro index
          refine Fin.cases ?_ ?_ index
          · exact row32103ForwardContextualPath
          · intro index
            refine Fin.cases ?_ ?_ index
            · exact row32104ForwardContextualPath
            · intro index
              refine Fin.cases ?_ ?_ index
              · exact row32105ForwardContextualPath
              · intro index
                refine Fin.cases ?_ ?_ index
                · exact row32106ForwardContextualPath
                · intro index
                  exact Fin.elim0 index
  | family222 =>
      change Fin 3 at index
      revert K
      refine Fin.cases ?_ ?_ index
      · exact row22201ForwardContextualPath
      · intro index
        refine Fin.cases ?_ ?_ index
        · exact row22202ForwardContextualPath
        · intro index
          refine Fin.cases ?_ ?_ index
          · exact row22203ForwardContextualPath
          · intro index
            exact Fin.elim0 index

/-- The actual reverse path used by the packaged compiler. -/
private def orbitLabelReverseActualPath (label : OrbitLabel)
    (K : State label.1.profile)
    (hK : Disjoint K
      (label.selectedEndpoints.left ∪ label.selectedEndpoints.right)) :
    MovePath (@AllModeMove label.1.profile)
      (K ∪ label.selectedEndpoints.right)
      (K ∪ label.selectedEndpoints.left) := by
  rw [Finset.union_comm] at hK
  rcases label with ⟨family, index⟩
  cases family with
  | family221 =>
      change Fin 3 at index
      revert K
      refine Fin.cases ?_ ?_ index
      · exact row22101ReverseContextualPath
      · intro index
        refine Fin.cases ?_ ?_ index
        · exact row22102ReverseContextualPath
        · intro index
          refine Fin.cases ?_ ?_ index
          · exact row22103ReverseContextualPath
          · intro index
            exact Fin.elim0 index
  | family411 =>
      change Fin 1 at index
      revert K
      refine Fin.cases ?_ ?_ index
      · exact row41101ReverseContextualPath
      · intro index
        exact Fin.elim0 index
  | family321 =>
      change Fin 6 at index
      revert K
      refine Fin.cases ?_ ?_ index
      · exact row32101ReverseContextualPath
      · intro index
        refine Fin.cases ?_ ?_ index
        · exact row32102ReverseContextualPath
        · intro index
          refine Fin.cases ?_ ?_ index
          · exact row32103ReverseContextualPath
          · intro index
            refine Fin.cases ?_ ?_ index
            · exact row32104ReverseContextualPath
            · intro index
              refine Fin.cases ?_ ?_ index
              · exact row32105ReverseContextualPath
              · intro index
                refine Fin.cases ?_ ?_ index
                · exact row32106ReverseContextualPath
                · intro index
                  exact Fin.elim0 index
  | family222 =>
      change Fin 3 at index
      revert K
      refine Fin.cases ?_ ?_ index
      · exact row22201ReverseContextualPath
      · intro index
        refine Fin.cases ?_ ?_ index
        · exact row22202ReverseContextualPath
        · intro index
          refine Fin.cases ?_ ?_ index
          · exact row22203ReverseContextualPath
          · intro index
            exact Fin.elim0 index

/-- The actual forward dispatch has the tabled constructed length. -/
private theorem orbitLabelForwardActualPath_length (label : OrbitLabel)
    (K : State label.1.profile)
    (hK : Disjoint K
      (label.selectedEndpoints.left ∪ label.selectedEndpoints.right)) :
    (orbitLabelForwardActualPath label K hK).length = orbitDistance label := by
  rcases label with ⟨family, index⟩
  cases family with
  | family221 =>
      change Fin 3 at index
      revert K
      refine Fin.cases ?_ ?_ index
      · intro K hK
        change (row22101ForwardContextualPath K hK).length = 2
        exact row22101ForwardContextualPath_length K hK
      · intro index
        refine Fin.cases ?_ ?_ index
        · intro K hK
          change (row22102ForwardContextualPath K hK).length = 2
          exact row22102ForwardContextualPath_length K hK
        · intro index
          refine Fin.cases ?_ ?_ index
          · intro K hK
            change (row22103ForwardContextualPath K hK).length = 2
            exact row22103ForwardContextualPath_length K hK
          · intro index
            exact Fin.elim0 index
  | family411 =>
      change Fin 1 at index
      revert K
      refine Fin.cases ?_ ?_ index
      · intro K hK
        change (row41101ForwardContextualPath K hK).length = 3
        exact row41101ForwardContextualPath_length K hK
      · intro index
        exact Fin.elim0 index
  | family321 =>
      change Fin 6 at index
      revert K
      refine Fin.cases ?_ ?_ index
      · intro K hK
        change (row32101ForwardContextualPath K hK).length = 3
        exact row32101ForwardContextualPath_length K hK
      · intro index
        refine Fin.cases ?_ ?_ index
        · intro K hK
          change (row32102ForwardContextualPath K hK).length = 3
          exact row32102ForwardContextualPath_length K hK
        · intro index
          refine Fin.cases ?_ ?_ index
          · intro K hK
            change (row32103ForwardContextualPath K hK).length = 3
            exact row32103ForwardContextualPath_length K hK
          · intro index
            refine Fin.cases ?_ ?_ index
            · intro K hK
              change (row32104ForwardContextualPath K hK).length = 2
              exact row32104ForwardContextualPath_length K hK
            · intro index
              refine Fin.cases ?_ ?_ index
              · intro K hK
                change (row32105ForwardContextualPath K hK).length = 2
                exact row32105ForwardContextualPath_length K hK
              · intro index
                refine Fin.cases ?_ ?_ index
                · intro K hK
                  change (row32106ForwardContextualPath K hK).length = 2
                  exact row32106ForwardContextualPath_length K hK
                · intro index
                  exact Fin.elim0 index
  | family222 =>
      change Fin 3 at index
      revert K
      refine Fin.cases ?_ ?_ index
      · intro K hK
        change (row22201ForwardContextualPath K hK).length = 3
        exact row22201ForwardContextualPath_length K hK
      · intro index
        refine Fin.cases ?_ ?_ index
        · intro K hK
          change (row22202ForwardContextualPath K hK).length = 2
          exact row22202ForwardContextualPath_length K hK
        · intro index
          refine Fin.cases ?_ ?_ index
          · intro K hK
            change (row22203ForwardContextualPath K hK).length = 2
            exact row22203ForwardContextualPath_length K hK
          · intro index
            exact Fin.elim0 index

/-- The actual reverse dispatch has the tabled constructed length. -/
private theorem orbitLabelReverseActualPath_length (label : OrbitLabel)
    (K : State label.1.profile)
    (hK : Disjoint K
      (label.selectedEndpoints.left ∪ label.selectedEndpoints.right)) :
    (orbitLabelReverseActualPath label K hK).length = orbitDistance label := by
  rcases label with ⟨family, index⟩
  cases family with
  | family221 =>
      change Fin 3 at index
      revert K
      refine Fin.cases ?_ ?_ index
      · intro K hK
        rw [Finset.union_comm] at hK
        change (row22101ReverseContextualPath K hK).length = 2
        exact row22101ReverseContextualPath_length K hK
      · intro index
        refine Fin.cases ?_ ?_ index
        · intro K hK
          rw [Finset.union_comm] at hK
          change (row22102ReverseContextualPath K hK).length = 2
          exact row22102ReverseContextualPath_length K hK
        · intro index
          refine Fin.cases ?_ ?_ index
          · intro K hK
            rw [Finset.union_comm] at hK
            change (row22103ReverseContextualPath K hK).length = 2
            exact row22103ReverseContextualPath_length K hK
          · intro index
            exact Fin.elim0 index
  | family411 =>
      change Fin 1 at index
      revert K
      refine Fin.cases ?_ ?_ index
      · intro K hK
        rw [Finset.union_comm] at hK
        change (row41101ReverseContextualPath K hK).length = 3
        exact row41101ReverseContextualPath_length K hK
      · intro index
        exact Fin.elim0 index
  | family321 =>
      change Fin 6 at index
      revert K
      refine Fin.cases ?_ ?_ index
      · intro K hK
        rw [Finset.union_comm] at hK
        change (row32101ReverseContextualPath K hK).length = 3
        exact row32101ReverseContextualPath_length K hK
      · intro index
        refine Fin.cases ?_ ?_ index
        · intro K hK
          rw [Finset.union_comm] at hK
          change (row32102ReverseContextualPath K hK).length = 3
          exact row32102ReverseContextualPath_length K hK
        · intro index
          refine Fin.cases ?_ ?_ index
          · intro K hK
            rw [Finset.union_comm] at hK
            change (row32103ReverseContextualPath K hK).length = 3
            exact row32103ReverseContextualPath_length K hK
          · intro index
            refine Fin.cases ?_ ?_ index
            · intro K hK
              rw [Finset.union_comm] at hK
              change (row32104ReverseContextualPath K hK).length = 2
              exact row32104ReverseContextualPath_length K hK
            · intro index
              refine Fin.cases ?_ ?_ index
              · intro K hK
                rw [Finset.union_comm] at hK
                change (row32105ReverseContextualPath K hK).length = 2
                exact row32105ReverseContextualPath_length K hK
              · intro index
                refine Fin.cases ?_ ?_ index
                · intro K hK
                  rw [Finset.union_comm] at hK
                  change (row32106ReverseContextualPath K hK).length = 2
                  exact row32106ReverseContextualPath_length K hK
                · intro index
                  exact Fin.elim0 index
  | family222 =>
      change Fin 3 at index
      revert K
      refine Fin.cases ?_ ?_ index
      · intro K hK
        rw [Finset.union_comm] at hK
        change (row22201ReverseContextualPath K hK).length = 3
        exact row22201ReverseContextualPath_length K hK
      · intro index
        refine Fin.cases ?_ ?_ index
        · intro K hK
          rw [Finset.union_comm] at hK
          change (row22202ReverseContextualPath K hK).length = 2
          exact row22202ReverseContextualPath_length K hK
        · intro index
          refine Fin.cases ?_ ?_ index
          · intro K hK
            rw [Finset.union_comm] at hK
            change (row22203ReverseContextualPath K hK).length = 2
            exact row22203ReverseContextualPath_length K hK
          · intro index
            exact Fin.elim0 index

/-- Package the actual forward path together with its canonical constructed length. -/
private def orbitLabelForwardPathCertificate (label : OrbitLabel)
    (K : State label.1.profile)
    (hK : Disjoint K
      (label.selectedEndpoints.left ∪ label.selectedEndpoints.right)) :
    { path : MovePath (@AllModeMove label.1.profile)
        (K ∪ label.selectedEndpoints.left)
        (K ∪ label.selectedEndpoints.right) //
      path.length = orbitDistance label } :=
  ⟨orbitLabelForwardActualPath label K hK,
    orbitLabelForwardActualPath_length label K hK⟩

/-- Package the actual reverse path together with its canonical constructed length. -/
private def orbitLabelReversePathCertificate (label : OrbitLabel)
    (K : State label.1.profile)
    (hK : Disjoint K
      (label.selectedEndpoints.left ∪ label.selectedEndpoints.right)) :
    { path : MovePath (@AllModeMove label.1.profile)
        (K ∪ label.selectedEndpoints.right)
        (K ∪ label.selectedEndpoints.left) //
      path.length = orbitDistance label } :=
  ⟨orbitLabelReverseActualPath label K hK,
    orbitLabelReverseActualPath_length label K hK⟩

/-- Compile the forward direction of any normalized orbit label in an arbitrary
context disjoint from the two original production endpoints. -/
def orbitLabelForwardPath (label : OrbitLabel)
    (K : State label.1.profile)
    (hK : Disjoint K
      (label.selectedEndpoints.left ∪ label.selectedEndpoints.right)) :
    MovePath (@AllModeMove label.1.profile)
      (K ∪ label.selectedEndpoints.left)
      (K ∪ label.selectedEndpoints.right) :=
  (orbitLabelForwardPathCertificate label K hK).1

/-- Compile the reverse direction of any normalized orbit label in an arbitrary
context disjoint from the two original production endpoints. -/
def orbitLabelReversePath (label : OrbitLabel)
    (K : State label.1.profile)
    (hK : Disjoint K
      (label.selectedEndpoints.left ∪ label.selectedEndpoints.right)) :
    MovePath (@AllModeMove label.1.profile)
      (K ∪ label.selectedEndpoints.right)
      (K ∪ label.selectedEndpoints.left) :=
  (orbitLabelReversePathCertificate label K hK).1

/-- The uniformly compiled forward path has exactly the canonical constructed
length. This theorem does not assert shortestness. -/
@[simp] theorem orbitLabelForwardPath_length (label : OrbitLabel)
    (K : State label.1.profile)
    (hK : Disjoint K
      (label.selectedEndpoints.left ∪ label.selectedEndpoints.right)) :
    (orbitLabelForwardPath label K hK).length = orbitDistance label :=
  (orbitLabelForwardPathCertificate label K hK).2

/-- The uniformly compiled reverse path has exactly the canonical constructed
length. This theorem does not assert shortestness. -/
@[simp] theorem orbitLabelReversePath_length (label : OrbitLabel)
    (K : State label.1.profile)
    (hK : Disjoint K
      (label.selectedEndpoints.left ∪ label.selectedEndpoints.right)) :
    (orbitLabelReversePath label K hK).length = orbitDistance label :=
  (orbitLabelReversePathCertificate label K hK).2

/-- A path of at most three all-mode edges whose endpoints have cardinality at
most `n` has altitude at most `n + 1`. -/
theorem allModeMovePath_altitude_le_add_one {q : Profile} {D E : State q}
    (path : MovePath (@AllModeMove q) D E) (n : Nat)
    (hD : D.card ≤ n) (hE : E.card ≤ n) (hlen : path.length ≤ 3) :
    path.altitude ≤ n + 1 := by
  cases path with
  | singleton =>
      simp only [MovePath.altitude]
      omega
  | snoc path hlast =>
      cases path with
      | singleton =>
          have hbLast := AllModeMove.card_bounds hlast
          simp only [MovePath.altitude, max_le_iff]
          omega
      | snoc path hmiddle =>
          cases path with
          | singleton =>
              have hbMiddle := AllModeMove.card_bounds hmiddle
              have hbLast := AllModeMove.card_bounds hlast
              simp only [MovePath.altitude, max_le_iff]
              omega
          | snoc path hfirst =>
              cases path with
              | singleton =>
                  have hbFirst := AllModeMove.card_bounds hfirst
                  have hbMiddle := AllModeMove.card_bounds hmiddle
                  have hbLast := AllModeMove.card_bounds hlast
                  simp only [MovePath.altitude, max_le_iff]
                  omega
              | snoc path htooMany =>
                  simp only [MovePath.length] at hlen
                  omega

private theorem contextualEndpoint_card_bounds (label : OrbitLabel)
    (K : State label.1.profile)
    (hK : Disjoint K
      (label.selectedEndpoints.left ∪ label.selectedEndpoints.right)) :
    (K ∪ label.selectedEndpoints.left).card ≤ K.card + 3 ∧
      (K ∪ label.selectedEndpoints.right).card ≤ K.card + 3 := by
  have hExact := selectedEndpoints_isExactRelation label
  have hKLeft : Disjoint K label.selectedEndpoints.left :=
    Disjoint.mono_right Finset.subset_union_left hK
  have hKRight : Disjoint K label.selectedEndpoints.right :=
    Disjoint.mono_right Finset.subset_union_right hK
  rw [Finset.card_union_of_disjoint hKLeft,
    Finset.card_union_of_disjoint hKRight, hExact.1, hExact.2.1]
  omega

/-- The uniformly compiled forward path never exceeds the context cardinality
plus four. -/
theorem orbitLabelForwardPath_altitude_le (label : OrbitLabel)
    (K : State label.1.profile)
    (hK : Disjoint K
      (label.selectedEndpoints.left ∪ label.selectedEndpoints.right)) :
    (orbitLabelForwardPath label K hK).altitude ≤ K.card + 4 := by
  have hcards := contextualEndpoint_card_bounds label K hK
  apply allModeMovePath_altitude_le_add_one
    (orbitLabelForwardPath label K hK) (K.card + 3) hcards.1 hcards.2
  rw [orbitLabelForwardPath_length]
  exact orbitDistance_le_three label

/-- The uniformly compiled reverse path never exceeds the context cardinality
plus four. -/
theorem orbitLabelReversePath_altitude_le (label : OrbitLabel)
    (K : State label.1.profile)
    (hK : Disjoint K
      (label.selectedEndpoints.left ∪ label.selectedEndpoints.right)) :
    (orbitLabelReversePath label K hK).altitude ≤ K.card + 4 := by
  have hcards := contextualEndpoint_card_bounds label K hK
  apply allModeMovePath_altitude_le_add_one
    (orbitLabelReversePath label K hK) (K.card + 3) hcards.2 hcards.1
  rw [orbitLabelReversePath_length]
  exact orbitDistance_le_three label

/-- At label `221-01`, the uniform forward path has the original production
row endpoints without a cast or replacement relation. -/
example (K : State profile221)
    (hK : Disjoint K (row22101Start ∪ row22101Finish)) :
    MovePath (@AllModeMove profile221) (K ∪ row22101Start)
      (K ∪ row22101Finish) :=
  orbitLabelForwardPath (⟨.family221, (0 : Fin 3)⟩ : OrbitLabel) K hK

/-- At label `221-01`, the uniform reverse path has the original production
row endpoints without a cast or replacement relation. -/
example (K : State profile221)
    (hK : Disjoint K (row22101Start ∪ row22101Finish)) :
    MovePath (@AllModeMove profile221) (K ∪ row22101Finish)
      (K ∪ row22101Start) :=
  orbitLabelReversePath (⟨.family221, (0 : Fin 3)⟩ : OrbitLabel) K hK

/-- The public disjointness hypothesis is jointly satisfiable in the empty
context. -/
example : Disjoint (∅ : State profile411) (row41101Start ∪ row41101Finish) := by
  simp

/-- At label `411-01`, the empty-context forward compilation has exact length
three. -/
example :
    (orbitLabelForwardPath (⟨.family411, (0 : Fin 1)⟩ : OrbitLabel)
      (∅ : State profile411) (Finset.disjoint_empty_left _)).length = 3 := by
  simpa only [orbitDistance] using orbitLabelForwardPath_length
    (⟨.family411, (0 : Fin 1)⟩ : OrbitLabel) (∅ : State profile411)
    (Finset.disjoint_empty_left _)

/-- At label `411-01`, the empty-context reverse compilation has exact length
three. -/
example :
    (orbitLabelReversePath (⟨.family411, (0 : Fin 1)⟩ : OrbitLabel)
      (∅ : State profile411) (Finset.disjoint_empty_left _)).length = 3 := by
  simpa only [orbitDistance] using orbitLabelReversePath_length
    (⟨.family411, (0 : Fin 1)⟩ : OrbitLabel) (∅ : State profile411)
    (Finset.disjoint_empty_left _)

/-- At label `411-01`, the empty-context forward altitude is at most four. -/
example :
    (orbitLabelForwardPath (⟨.family411, (0 : Fin 1)⟩ : OrbitLabel)
      (∅ : State profile411) (Finset.disjoint_empty_left _)).altitude ≤ 4 := by
  simpa using orbitLabelForwardPath_altitude_le
    (⟨.family411, (0 : Fin 1)⟩ : OrbitLabel) (∅ : State profile411)
    (Finset.disjoint_empty_left _)

#check @orbitDistance
#check @orbitDistance_two_or_three
#check @orbitLabelForwardPath
#check @orbitLabelReversePath
#check @orbitLabelForwardPath_length
#check @orbitLabelReversePath_length
#check @orbitLabelForwardPath_altitude_le
#check @orbitLabelReversePath_altitude_le

#print axioms orbitDistance_two_or_three
#print axioms allModeMovePath_altitude_le_add_one
#print axioms orbitLabelForwardPath_length
#print axioms orbitLabelReversePath_length
#print axioms orbitLabelForwardPath_altitude_le
#print axioms orbitLabelReversePath_altitude_le

end BilinearComplexity.NormalizedBinaryContextualCompiler
