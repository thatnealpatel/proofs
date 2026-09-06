import BilinearComplexity.BinaryContextualFiveCircuitCompiler
import BilinearComplexity.BinaryContextualNativeExclusion
import BilinearComplexity.BinaryContextualOrbitReflection
import BilinearComplexity.BinaryAmbientContextDistance

set_option autoImplicit false

/-!
# Global optimality of the contextual binary five-circuit compiler

The thirteen classified orbit rows are assigned their exact two- or three-edge
lower bounds using the same `orbitDistance` table as the callback-free upper
compiler. Reflection transfers these bounds to every classified normalized
relation, and ambient context normalization transfers them to arbitrary native
competitors without any freshness hypothesis.

Consequently the actual `forward` path and the independently compiled native
`reverse` path returned by `compileContextualBinaryFiveCircuit` are globally
shortest. The final certificate theorem binds both paths, their shared semantic
orbit label and distance, their altitude bounds, and both universal optimality
properties to one compiler result. The orbit-distance stability theorem additionally
shows that this certified distance is independent of both the supplied exact
span presentation and the disjoint borrowing context for fixed endpoints.

AI disclosure: produced with AI assistance (see `README`).
-/

open scoped symmDiff

namespace BilinearComplexity.BinaryContextualFiveCircuitOptimality

open BinaryCircuit
open BinaryAmbientCarrier
open BinaryAmbientMoves
open BinaryAmbientNormalization
open BinaryAmbientContextOptimality
open BinaryAmbientContextDistance
open NormalizedBinaryCarrier
open NormalizedBinaryAllModeMove
open NormalizedBinaryOrbitClassification
open NormalizedBinaryRelationEnumeration
open NormalizedBinaryContextualCompiler
open BinaryContextualNativeExclusion
open BinaryContextualOrbitReflection
open BinaryContextualFiveCircuitCompiler

universe u v w

variable {U : Type u} {V : Type v} {W : Type w}
variable [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
variable [Module F2 U] [Module F2 V] [Module F2 W]
variable [DecidableEq U] [DecidableEq V] [DecidableEq W]

private theorem movePath_mono_length {α : Type*}
    {R S : Finset α → Finset α → Prop}
    (hRS : ∀ {X Y}, R X Y → S X Y) {D E : Finset α}
    (path : MovePath R D E) :
    (path.mono hRS).length = path.length := by
  induction path with
  | singleton => simp only [MovePath.mono, MovePath.length]
  | snoc path move ih => simp only [MovePath.mono, MovePath.length, ih]

private def toAmbientPath {p : Profile} {D E : State p}
    (path : MovePath (@NormalizedBinaryAllModeMove.AllModeMove p) D E) :
    MovePath
      (BinaryAmbientMoves.AllModeMove
        (U := CoordinateVector p.first)
        (V := CoordinateVector p.second)
        (W := CoordinateVector p.third)) D E :=
  path.mono (fun {X Y} hmove =>
    (@BinaryAmbientMoves.Coordinate.allModeMove_iff_normalized p X Y).mpr hmove)

@[simp] private theorem toAmbientPath_length {p : Profile} {D E : State p}
    (path : MovePath (@NormalizedBinaryAllModeMove.AllModeMove p) D E) :
    (toAmbientPath path).length = path.length := by
  unfold toAmbientPath
  exact movePath_mono_length
    (fun {X Y} hmove =>
      (@BinaryAmbientMoves.Coordinate.allModeMove_iff_normalized p X Y).mpr hmove)
    path


private theorem normalized_context_path_length_two_le {p : Profile}
    {A B K : State p}
    (hKA : Disjoint K A) (hKB : Disjoint K B) (hAB : Disjoint A B)
    (hA : A.card = 2) (hB : B.card = 3)
    (path : MovePath (@NormalizedBinaryAllModeMove.AllModeMove p)
      (K ∪ A) (K ∪ B)) :
    2 ≤ path.length := by
  let ambientPath := toAmbientPath path
  have hlower := intrinsic_allModeMovePath_length_two_le
    hKA hKB hAB hA hB ambientPath
  simpa only [ambientPath, toAmbientPath_length] using hlower

/-- Every selected normalized row has the contextual lower bound prescribed by
`orbitDistance` in the forward direction. -/
theorem selected_forward_context_path_length_lower_bound
    (label : OrbitLabel)
    (K : State label.1.profile)
    (hK : Disjoint K
      (label.selectedEndpoints.left ∪ label.selectedEndpoints.right))
    (path : MovePath (@NormalizedBinaryAllModeMove.AllModeMove label.1.profile)
      (K ∪ label.selectedEndpoints.left)
      (K ∪ label.selectedEndpoints.right)) :
    orbitDistance label ≤ path.length := by
  rcases label with ⟨family, index⟩
  cases family with
  | family221 =>
      fin_cases index <;>
        exact normalized_context_path_length_two_le
          (hK.mono_right Finset.subset_union_left)
          (hK.mono_right Finset.subset_union_right)
          (selectedEndpoints_isExactRelation _).2.2.1
          (selectedEndpoints_isExactRelation _).1
          (selectedEndpoints_isExactRelation _).2.1 path
  | family411 =>
      fin_cases index
      have hlower := row41101_forward_contextual_length_three_le K hK
        (toAmbientPath path)
      have hlength := toAmbientPath_length path
      have hthree : 3 ≤ path.length := hlower.trans_eq hlength
      simpa [orbitDistance] using hthree
  | family321 =>
      fin_cases index
      · have hlower := row32101_forward_contextual_length_three_le K hK
          (toAmbientPath path)
        have hlength := toAmbientPath_length path
        have hthree : 3 ≤ path.length := hlower.trans_eq hlength
        simpa [orbitDistance] using hthree
      · have hlower := row32102_forward_contextual_length_three_le K hK
          (toAmbientPath path)
        have hlength := toAmbientPath_length path
        have hthree : 3 ≤ path.length := hlower.trans_eq hlength
        simpa [orbitDistance] using hthree
      · have hlower := row32103_forward_contextual_length_three_le K hK
          (toAmbientPath path)
        have hlength := toAmbientPath_length path
        have hthree : 3 ≤ path.length := hlower.trans_eq hlength
        simpa [orbitDistance] using hthree
      · exact normalized_context_path_length_two_le
          (hK.mono_right Finset.subset_union_left)
          (hK.mono_right Finset.subset_union_right)
          (selectedEndpoints_isExactRelation _).2.2.1
          (selectedEndpoints_isExactRelation _).1
          (selectedEndpoints_isExactRelation _).2.1 path
      · exact normalized_context_path_length_two_le
          (hK.mono_right Finset.subset_union_left)
          (hK.mono_right Finset.subset_union_right)
          (selectedEndpoints_isExactRelation _).2.2.1
          (selectedEndpoints_isExactRelation _).1
          (selectedEndpoints_isExactRelation _).2.1 path
      · exact normalized_context_path_length_two_le
          (hK.mono_right Finset.subset_union_left)
          (hK.mono_right Finset.subset_union_right)
          (selectedEndpoints_isExactRelation _).2.2.1
          (selectedEndpoints_isExactRelation _).1
          (selectedEndpoints_isExactRelation _).2.1 path
  | family222 =>
      fin_cases index
      · have hlower := row22201_forward_contextual_length_three_le K hK
          (toAmbientPath path)
        have hlength := toAmbientPath_length path
        have hthree : 3 ≤ path.length := hlower.trans_eq hlength
        simpa [orbitDistance] using hthree
      · exact normalized_context_path_length_two_le
          (hK.mono_right Finset.subset_union_left)
          (hK.mono_right Finset.subset_union_right)
          (selectedEndpoints_isExactRelation _).2.2.1
          (selectedEndpoints_isExactRelation _).1
          (selectedEndpoints_isExactRelation _).2.1 path
      · exact normalized_context_path_length_two_le
          (hK.mono_right Finset.subset_union_left)
          (hK.mono_right Finset.subset_union_right)
          (selectedEndpoints_isExactRelation _).2.2.1
          (selectedEndpoints_isExactRelation _).1
          (selectedEndpoints_isExactRelation _).2.1 path

private theorem normalized_reverse_context_path_length_two_le {p : Profile}
    {A B K : State p}
    (hKA : Disjoint K A) (hKB : Disjoint K B) (hAB : Disjoint A B)
    (hA : A.card = 2) (hB : B.card = 3)
    (path : MovePath (@NormalizedBinaryAllModeMove.AllModeMove p)
      (K ∪ B) (K ∪ A)) :
    2 ≤ path.length := by
  by_contra hnot
  have hlength : path.length < 2 := Nat.lt_of_not_ge hnot
  rcases movePath_length_lt_two_cases path hlength with hzero | hone
  · have hstartCard : (K ∪ B).card = K.card + 3 := by
      rw [Finset.card_union_of_disjoint hKB, hB]
    have hfinishCard : (K ∪ A).card = K.card + 2 := by
      rw [Finset.card_union_of_disjoint hKA, hA]
    have hcards := congrArg Finset.card hzero
    omega
  · have hEndpoint : (K ∪ B) ∆ (K ∪ A) = B ∪ A :=
      symmDiff_context_union hKB hKA hAB.symm
    have hEndpointCard : (B ∪ A).card = 5 := by
      rw [Finset.card_union_of_disjoint hAB.symm, hB, hA]
    have hsupport := BinaryAmbientMoveSupport.AllModeMove.support_card
      ((@BinaryAmbientMoves.Coordinate.allModeMove_iff_normalized p _ _).mpr hone)
    rcases hsupport with hsupport | hsupport <;>
      rw [hEndpoint, hEndpointCard] at hsupport <;> omega

/-- Every selected normalized row has the contextual lower bound prescribed by
`orbitDistance` in the reverse direction. -/
theorem selected_reverse_context_path_length_lower_bound
    (label : OrbitLabel)
    (K : State label.1.profile)
    (hK : Disjoint K
      (label.selectedEndpoints.left ∪ label.selectedEndpoints.right))
    (path : MovePath (@NormalizedBinaryAllModeMove.AllModeMove label.1.profile)
      (K ∪ label.selectedEndpoints.right)
      (K ∪ label.selectedEndpoints.left)) :
    orbitDistance label ≤ path.length := by
  rcases label with ⟨family, index⟩
  cases family with
  | family221 =>
      fin_cases index <;>
        exact normalized_reverse_context_path_length_two_le
          (hK.mono_right Finset.subset_union_left)
          (hK.mono_right Finset.subset_union_right)
          (selectedEndpoints_isExactRelation _).2.2.1
          (selectedEndpoints_isExactRelation _).1
          (selectedEndpoints_isExactRelation _).2.1 path
  | family411 =>
      fin_cases index
      have hlower := row41101_reverse_contextual_length_three_le K hK
        (toAmbientPath path)
      have hlength := toAmbientPath_length path
      have hthree : 3 ≤ path.length := hlower.trans_eq hlength
      simpa [orbitDistance] using hthree
  | family321 =>
      fin_cases index
      · have hlower := row32101_reverse_contextual_length_three_le K hK
          (toAmbientPath path)
        have hlength := toAmbientPath_length path
        have hthree : 3 ≤ path.length := hlower.trans_eq hlength
        simpa [orbitDistance] using hthree
      · have hlower := row32102_reverse_contextual_length_three_le K hK
          (toAmbientPath path)
        have hlength := toAmbientPath_length path
        have hthree : 3 ≤ path.length := hlower.trans_eq hlength
        simpa [orbitDistance] using hthree
      · have hlower := row32103_reverse_contextual_length_three_le K hK
          (toAmbientPath path)
        have hlength := toAmbientPath_length path
        have hthree : 3 ≤ path.length := hlower.trans_eq hlength
        simpa [orbitDistance] using hthree
      · exact normalized_reverse_context_path_length_two_le
          (hK.mono_right Finset.subset_union_left)
          (hK.mono_right Finset.subset_union_right)
          (selectedEndpoints_isExactRelation _).2.2.1
          (selectedEndpoints_isExactRelation _).1
          (selectedEndpoints_isExactRelation _).2.1 path
      · exact normalized_reverse_context_path_length_two_le
          (hK.mono_right Finset.subset_union_left)
          (hK.mono_right Finset.subset_union_right)
          (selectedEndpoints_isExactRelation _).2.2.1
          (selectedEndpoints_isExactRelation _).1
          (selectedEndpoints_isExactRelation _).2.1 path
      · exact normalized_reverse_context_path_length_two_le
          (hK.mono_right Finset.subset_union_left)
          (hK.mono_right Finset.subset_union_right)
          (selectedEndpoints_isExactRelation _).2.2.1
          (selectedEndpoints_isExactRelation _).1
          (selectedEndpoints_isExactRelation _).2.1 path
  | family222 =>
      fin_cases index
      · have hlower := row22201_reverse_contextual_length_three_le K hK
          (toAmbientPath path)
        have hlength := toAmbientPath_length path
        have hthree : 3 ≤ path.length := hlower.trans_eq hlength
        simpa [orbitDistance] using hthree
      · exact normalized_reverse_context_path_length_two_le
          (hK.mono_right Finset.subset_union_left)
          (hK.mono_right Finset.subset_union_right)
          (selectedEndpoints_isExactRelation _).2.2.1
          (selectedEndpoints_isExactRelation _).1
          (selectedEndpoints_isExactRelation _).2.1 path
      · exact normalized_reverse_context_path_length_two_le
          (hK.mono_right Finset.subset_union_left)
          (hK.mono_right Finset.subset_union_right)
          (selectedEndpoints_isExactRelation _).2.2.1
          (selectedEndpoints_isExactRelation _).1
          (selectedEndpoints_isExactRelation _).2.1 path

/-- Reflection transports the selected forward lower-bound table to every
classified normalized exact relation. -/
theorem classified_forward_context_path_length_lower_bound {p : Profile}
    {target : ExactRelation p} (compiled : ClassifiedCompilation target)
    (K : State p) (hK : Disjoint K (target.1.left ∪ target.1.right))
    (path : MovePath (@NormalizedBinaryAllModeMove.AllModeMove p)
      (K ∪ target.1.left) (K ∪ target.1.right)) :
    orbitDistance compiled.label ≤ path.length := by
  exact classifiedContextPath_length_lower_bound compiled
    (orbitDistance compiled.label)
    (selected_forward_context_path_length_lower_bound compiled.label) K hK path

private theorem normalizedAllModeMove_reverse {p : Profile} {D E : State p}
    (hmove : @NormalizedBinaryAllModeMove.AllModeMove p D E) :
    @NormalizedBinaryAllModeMove.AllModeMove p E D := by
  apply (@BinaryAmbientMoves.Coordinate.allModeMove_iff_normalized p E D).mp
  exact BinaryAmbientMoveSupport.AllModeMove.reverse
    ((@BinaryAmbientMoves.Coordinate.allModeMove_iff_normalized p D E).mpr hmove)

private def reverseNormalizedPath {p : Profile} :
    {D E : State p} →
      MovePath (@NormalizedBinaryAllModeMove.AllModeMove p) D E →
      MovePath (@NormalizedBinaryAllModeMove.AllModeMove p) E D
  | _, _, .singleton D => .singleton D
  | _, _, .snoc path hmove =>
      (MovePath.one (normalizedAllModeMove_reverse hmove)).trans
        (reverseNormalizedPath path)

private theorem movePath_trans_length' {α : Type*} [DecidableEq α]
    {R : Finset α → Finset α → Prop} {X Y Z : Finset α}
    (first : MovePath R X Y) (second : MovePath R Y Z) :
    (first.trans second).length = first.length + second.length := by
  induction second with
  | singleton => simp only [MovePath.trans, MovePath.length, Nat.add_zero]
  | snoc second hmove ih =>
      simp only [MovePath.trans, MovePath.length, ih, Nat.add_assoc]

@[simp] private theorem reverseNormalizedPath_length {p : Profile}
    {D E : State p}
    (path : MovePath (@NormalizedBinaryAllModeMove.AllModeMove p) D E) :
    (reverseNormalizedPath path).length = path.length := by
  induction path with
  | singleton => simp only [reverseNormalizedPath, MovePath.length]
  | snoc path hmove ih =>
      rw [reverseNormalizedPath, movePath_trans_length', ih]
      simp only [MovePath.one, MovePath.length]
      omega

/-- Reflection transports the selected reverse lower-bound table to every
classified normalized exact relation. -/
theorem classified_reverse_context_path_length_lower_bound {p : Profile}
    {target : ExactRelation p} (compiled : ClassifiedCompilation target)
    (K : State p) (hK : Disjoint K (target.1.left ∪ target.1.right))
    (path : MovePath (@NormalizedBinaryAllModeMove.AllModeMove p)
      (K ∪ target.1.right) (K ∪ target.1.left)) :
    orbitDistance compiled.label ≤ path.length := by
  have hlower := classified_forward_context_path_length_lower_bound
    compiled K hK (reverseNormalizedPath path)
  exact hlower.trans_eq (reverseNormalizedPath_length path)

end BilinearComplexity.BinaryContextualFiveCircuitOptimality

namespace BilinearComplexity.BinaryContextualFiveCircuitCompiler.ContextualBinaryFiveCircuitCompilation

open BinaryCircuit
open BinaryAmbientCarrier
open BinaryAmbientMoves
open BinaryAmbientNormalization
open BinaryAmbientContextDistance
open BinaryFiveCircuitCompiler
open BinaryContextBorrowing221
open BinaryAmbientCircuitModels
open NormalizedBinaryCarrier
open NormalizedBinaryOrbitClassification
open NormalizedBinaryProfileOrientation
open NormalizedBinaryRelationEnumeration
open NormalizedBinaryContextualCompiler
open BilinearComplexity.BinaryContextualFiveCircuitOptimality

universe u v w

variable {U : Type u} {V : Type v} {W : Type w}
variable [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
variable [Module F2 U] [Module F2 V] [Module F2 W]
variable [DecidableEq U] [DecidableEq V] [DecidableEq W]

/-- Every ambient native forward competitor has length at least the orbit
length computed by the actual contextual compiler. -/
theorem forward_path_length_ge
    {A B : BinaryAmbientCarrier.State U V W}
    {P : ExactSpanPresentation A B}
    {hA : A.card = 2} {hB : B.card = 3} {hAB : Disjoint A B}
    {hEval : stateEvaluation A = stateEvaluation B}
    {C : BinaryAmbientCarrier.State U V W} {hC : Disjoint C (A ∪ B)}
    (result : ContextualBinaryFiveCircuitCompilation P hA hB hAB hEval C hC)
    (path : MovePath (BinaryAmbientMoves.AllModeMove (U := U) (V := V) (W := W))
      (C ∪ A) (C ∪ B)) :
    orbitDistance result.label ≤ path.length := by
  apply forward_path_length_ge_of_normalized_context_lower P
    (hC.mono_right Finset.subset_union_left)
    (hC.mono_right Finset.subset_union_right) hAB hA hB
    (orbitDistance result.label) result.distance_two_or_three
  · intro K hKLeft hKRight normalizedPath
    exact classified_forward_context_path_length_lower_bound
      result.classified K
      (Finset.disjoint_union_right.mpr ⟨hKLeft, hKRight⟩)
      normalizedPath

/-- Every ambient native reverse competitor has length at least the orbit
length computed by the actual contextual compiler. -/
theorem reverse_path_length_ge
    {A B : BinaryAmbientCarrier.State U V W}
    {P : ExactSpanPresentation A B}
    {hA : A.card = 2} {hB : B.card = 3} {hAB : Disjoint A B}
    {hEval : stateEvaluation A = stateEvaluation B}
    {C : BinaryAmbientCarrier.State U V W} {hC : Disjoint C (A ∪ B)}
    (result : ContextualBinaryFiveCircuitCompilation P hA hB hAB hEval C hC)
    (path : MovePath (BinaryAmbientMoves.AllModeMove (U := U) (V := V) (W := W))
      (C ∪ B) (C ∪ A)) :
    orbitDistance result.label ≤ path.length := by
  apply reverse_path_length_ge_of_normalized_context_lower P
    (hC.mono_right Finset.subset_union_left)
    (hC.mono_right Finset.subset_union_right) hAB hA hB
    (orbitDistance result.label) result.distance_two_or_three
  · intro K hKLeft hKRight normalizedPath
    exact classified_reverse_context_path_length_lower_bound
      result.classified K
      (Finset.disjoint_union_right.mpr ⟨hKLeft, hKRight⟩)
      normalizedPath

/-- The actual contextual compiler's forward path is globally shortest among
all ambient native paths with the same contextual endpoints. -/
theorem forward_shortest
    {A B : BinaryAmbientCarrier.State U V W}
    {P : ExactSpanPresentation A B}
    {hA : A.card = 2} {hB : B.card = 3} {hAB : Disjoint A B}
    {hEval : stateEvaluation A = stateEvaluation B}
    {C : BinaryAmbientCarrier.State U V W} {hC : Disjoint C (A ∪ B)}
    (result : ContextualBinaryFiveCircuitCompilation P hA hB hAB hEval C hC)
    (path : MovePath (BinaryAmbientMoves.AllModeMove (U := U) (V := V) (W := W))
      (C ∪ A) (C ∪ B)) :
    result.forward.length ≤ path.length := by
  calc
    result.forward.length = orbitDistance result.label := result.forward_length
    _ ≤ path.length := result.forward_path_length_ge path

/-- The actual contextual compiler's separately constructed reverse path is
globally shortest among all ambient native reverse paths with the same
contextual endpoints. -/
theorem reverse_shortest
    {A B : BinaryAmbientCarrier.State U V W}
    {P : ExactSpanPresentation A B}
    {hA : A.card = 2} {hB : B.card = 3} {hAB : Disjoint A B}
    {hEval : stateEvaluation A = stateEvaluation B}
    {C : BinaryAmbientCarrier.State U V W} {hC : Disjoint C (A ∪ B)}
    (result : ContextualBinaryFiveCircuitCompilation P hA hB hAB hEval C hC)
    (path : MovePath (BinaryAmbientMoves.AllModeMove (U := U) (V := V) (W := W))
      (C ∪ B) (C ∪ A)) :
    result.reverse.length ≤ path.length := by
  calc
    result.reverse.length = orbitDistance result.label := result.reverse_length
    _ ≤ path.length := result.reverse_path_length_ge path

/-- One theorem certifies that a single runtime compiler result carries its
semantic orbit, exact common distance, both concrete directed paths, their
altitude bounds, and global optimality against every ambient native competitor. -/
theorem certified_optimality
    {A B : BinaryAmbientCarrier.State U V W}
    {P : ExactSpanPresentation A B}
    {hA : A.card = 2} {hB : B.card = 3} {hAB : Disjoint A B}
    {hEval : stateEvaluation A = stateEvaluation B}
    {C : BinaryAmbientCarrier.State U V W} {hC : Disjoint C (A ∪ B)}
    (result : ContextualBinaryFiveCircuitCompilation P hA hB hAB hEval C hC) :
    AmbientInOrbit result.label A B ∧
      (orbitDistance result.label = 2 ∨ orbitDistance result.label = 3) ∧
      result.forward.length = orbitDistance result.label ∧
      result.reverse.length = orbitDistance result.label ∧
      result.forward.altitude ≤ C.card + 4 ∧
      result.reverse.altitude ≤ C.card + 4 ∧
      (∀ path : MovePath
        (BinaryAmbientMoves.AllModeMove (U := U) (V := V) (W := W))
        (C ∪ A) (C ∪ B), result.forward.length ≤ path.length) ∧
      (∀ path : MovePath
        (BinaryAmbientMoves.AllModeMove (U := U) (V := V) (W := W))
        (C ∪ B) (C ∪ A), result.reverse.length ≤ path.length) := by
  have hmembership : AmbientInOrbit result.label A B := result.ambient_membership
  have hdistance :
      orbitDistance result.label = 2 ∨ orbitDistance result.label = 3 :=
    result.distance_two_or_three
  have hforwardLength :
      result.forward.length = orbitDistance result.label := result.forward_length
  have hreverseLength :
      result.reverse.length = orbitDistance result.label := result.reverse_length
  have hforwardAltitude : result.forward.altitude ≤ C.card + 4 :=
    result.forward_altitude_le
  have hreverseAltitude : result.reverse.altitude ≤ C.card + 4 :=
    result.reverse_altitude_le
  have hforwardShortest : ∀ path : MovePath
      (BinaryAmbientMoves.AllModeMove (U := U) (V := V) (W := W))
      (C ∪ A) (C ∪ B), result.forward.length ≤ path.length :=
    fun path => result.forward_shortest path
  have hreverseShortest : ∀ path : MovePath
      (BinaryAmbientMoves.AllModeMove (U := U) (V := V) (W := W))
      (C ∪ B) (C ∪ A), result.reverse.length ≤ path.length :=
    fun path => result.reverse_shortest path
  exact ⟨hmembership, hdistance, hforwardLength, hreverseLength,
    hforwardAltitude, hreverseAltitude, hforwardShortest, hreverseShortest⟩

/-- For fixed ambient endpoints, the compiler's classified distance is
independent of both the supplied effective exact-span presentation and the
disjoint borrowing context. -/
theorem orbitDistance_compileContextualBinaryFiveCircuit_eq
    {A B : BinaryAmbientCarrier.State U V W}
    (P₁ P₂ : ExactSpanPresentation A B)
    (hA : A.card = 2) (hB : B.card = 3) (hAB : Disjoint A B)
    (hEval : stateEvaluation A = stateEvaluation B)
    (C₁ C₂ : BinaryAmbientCarrier.State U V W)
    (hC₁ : Disjoint C₁ (A ∪ B)) (hC₂ : Disjoint C₂ (A ∪ B)) :
    orbitDistance
        (compileContextualBinaryFiveCircuit P₁ hA hB hAB hEval C₁ hC₁).label =
      orbitDistance
        (compileContextualBinaryFiveCircuit P₂ hA hB hAB hEval C₂ hC₂).label := by
  have hEmpty : Disjoint (∅ : BinaryAmbientCarrier.State U V W) (A ∪ B) :=
    Finset.disjoint_empty_left (A ∪ B)
  let result₁ :=
    compileContextualBinaryFiveCircuit P₁ hA hB hAB hEval ∅ hEmpty
  let result₂ :=
    compileContextualBinaryFiveCircuit P₂ hA hB hAB hEval ∅ hEmpty
  have h₁₂ : orbitDistance result₁.label ≤ orbitDistance result₂.label := by
    calc
      orbitDistance result₁.label ≤ result₂.forward.length :=
        result₁.forward_path_length_ge result₂.forward
      _ = orbitDistance result₂.label := result₂.forward_length
  have h₂₁ : orbitDistance result₂.label ≤ orbitDistance result₁.label := by
    calc
      orbitDistance result₂.label ≤ result₁.forward.length :=
        result₂.forward_path_length_ge result₁.forward
      _ = orbitDistance result₁.label := result₁.forward_length
  have hResult : orbitDistance result₁.label = orbitDistance result₂.label :=
    Nat.le_antisymm h₁₂ h₂₁
  exact hResult

/-- The collision regression's semantic orbit label. -/
private abbrev optimalityGroundLabel221 : OrbitLabel :=
  ⟨.family221, (0 : Fin 3)⟩

/-- The collision regression's exact normalized relation. -/
private abbrev optimalityGroundTarget221 : ExactRelation profile221 :=
  optimalityGroundLabel221.selectedExactRelation

/-- A concrete choice-free coordinate presentation for the collision regression. -/
private def optimalityGroundPresentation221 : ExactSpanPresentation
    optimalityGroundTarget221.1.left optimalityGroundTarget221.1.right :=
  coordinateExactSpanPresentation optimalityGroundTarget221

example : normalizedLeft optimalityGroundPresentation221 =
    optimalityGroundTarget221.1.left := by
  exact normalizedLeft_coordinateExactSpanPresentation optimalityGroundTarget221

private theorem optimalityGroundEvaluation221 :
    BinaryAmbientCarrier.stateEvaluation optimalityGroundTarget221.1.left =
      BinaryAmbientCarrier.stateEvaluation optimalityGroundTarget221.1.right := by
  exact (coordinate_stateEvaluation_eq_iff_ambientStateEvaluation
    optimalityGroundTarget221.1.left optimalityGroundTarget221.1.right).mp
      optimalityGroundTarget221.2.2.2.2.1

private theorem optimalityGroundContextDisjoint221 :
    Disjoint contextC
      (optimalityGroundTarget221.1.left ∪ optimalityGroundTarget221.1.right) := by
  decide

private theorem optimalityGroundEmptyDisjoint221 :
    Disjoint (∅ : NormalizedBinaryCarrier.State profile221)
      (optimalityGroundTarget221.1.left ∪ optimalityGroundTarget221.1.right) :=
  Finset.disjoint_empty_left _

/-- The actual public compiler run in the collision-bearing `221-01` context. -/
private def optimalityGroundCompilation221 :=
  compileContextualBinaryFiveCircuit optimalityGroundPresentation221
    optimalityGroundTarget221.2.1 optimalityGroundTarget221.2.2.1
    optimalityGroundTarget221.2.2.2.1 optimalityGroundEvaluation221 contextC
    optimalityGroundContextDisjoint221

example :
    orbitDistance optimalityGroundCompilation221.label =
      orbitDistance
        (compileContextualBinaryFiveCircuit optimalityGroundPresentation221
          optimalityGroundTarget221.2.1 optimalityGroundTarget221.2.2.1
          optimalityGroundTarget221.2.2.2.1 optimalityGroundEvaluation221 ∅
          optimalityGroundEmptyDisjoint221).label := by
  exact orbitDistance_compileContextualBinaryFiveCircuit_eq
    optimalityGroundPresentation221 optimalityGroundPresentation221
    optimalityGroundTarget221.2.1 optimalityGroundTarget221.2.2.1
    optimalityGroundTarget221.2.2.2.1 optimalityGroundEvaluation221 contextC ∅
    optimalityGroundContextDisjoint221 optimalityGroundEmptyDisjoint221

example : optimalityGroundCompilation221.forward.length = 2 := by
  rw [ContextualBinaryFiveCircuitCompilation.forward_length]
  decide

example : optimalityGroundCompilation221.reverse.length = 2 := by
  rw [ContextualBinaryFiveCircuitCompilation.reverse_length]
  decide

example (path : MovePath BinaryAmbientMoves.AllModeMove
    (contextC ∪ optimalityGroundTarget221.1.left)
    (contextC ∪ optimalityGroundTarget221.1.right)) :
    optimalityGroundCompilation221.forward.length ≤ path.length :=
  optimalityGroundCompilation221.forward_shortest path

example (path : MovePath BinaryAmbientMoves.AllModeMove
    (contextC ∪ optimalityGroundTarget221.1.right)
    (contextC ∪ optimalityGroundTarget221.1.left)) :
    optimalityGroundCompilation221.reverse.length ≤ path.length :=
  optimalityGroundCompilation221.reverse_shortest path

-- Runtime collision regression for both actual directed outputs. It evaluates
-- to `([6, 6, 7], 2, [7, 6, 6], 2)`.
#eval (optimalityGroundCompilation221.forward.vertices.map Finset.card,
  optimalityGroundCompilation221.forward.length,
  optimalityGroundCompilation221.reverse.vertices.map Finset.card,
  optimalityGroundCompilation221.reverse.length)

#check @forward_path_length_ge
#check @reverse_path_length_ge
#check @forward_shortest
#check @reverse_shortest
#check @certified_optimality
#check @orbitDistance_compileContextualBinaryFiveCircuit_eq

#print axioms BilinearComplexity.BinaryContextualFiveCircuitOptimality.selected_forward_context_path_length_lower_bound
#print axioms BilinearComplexity.BinaryContextualFiveCircuitOptimality.selected_reverse_context_path_length_lower_bound
#print axioms BilinearComplexity.BinaryContextualFiveCircuitOptimality.classified_forward_context_path_length_lower_bound
#print axioms BilinearComplexity.BinaryContextualFiveCircuitOptimality.classified_reverse_context_path_length_lower_bound
#print axioms forward_path_length_ge
#print axioms reverse_path_length_ge
#print axioms forward_shortest
#print axioms reverse_shortest
#print axioms certified_optimality
#print axioms orbitDistance_compileContextualBinaryFiveCircuit_eq

end BilinearComplexity.BinaryContextualFiveCircuitCompiler.ContextualBinaryFiveCircuitCompilation
