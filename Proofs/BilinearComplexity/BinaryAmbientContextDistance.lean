import BilinearComplexity.BinaryAmbientContextOptimality
import BilinearComplexity.BinaryAmbientContextReflection

/-!
# Ambient contextual distance reflection

This module localizes every hypothetical ambient path of length below three
between contextual two- and three-term endpoints.  The native three-point
support geometry places the unique auxiliary term found by finite-set
localization in the exact endpoint factor box.  Consequently both ambient
edge supports lie in that box and reflect to an actual normalized two-edge
competitor.  Abstract every-context normalized lower bounds therefore lift to
arbitrary ambient paths; no locality or context-persistence condition is
imposed on those paths.
-/

set_option autoImplicit false

namespace BilinearComplexity.BinaryAmbientContextDistance

open scoped symmDiff
open BinaryCircuit
open BinaryAmbientCarrier
open BinaryAmbientMoves
open BinaryAmbientMoveSupport
open BinaryAmbientMoveTransport
open BinaryAmbientNormalization
open BinaryFiveCircuitCompiler
open BinaryAmbientContextTransport
open BinaryAmbientContextReflection
open BinaryAmbientContextOptimality
open NormalizedBinaryCarrier
open NormalizedBinaryFiveCircuitRows

universe u v w

variable {U : Type u} {V : Type v} {W : Type w}
variable [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
variable [Module F2 U] [Module F2 V] [Module F2 W]
variable [DecidableEq U] [DecidableEq V] [DecidableEq W]

private theorem movePath_mono_length
    {α : Type*} [DecidableEq α]
    {R S : Finset α → Finset α → Prop} {X Y : Finset α}
    (f : ∀ {D E}, R D E → S D E) (path : MovePath R X Y) :
    (path.mono f).length = path.length := by
  induction path with
  | singleton => simp only [MovePath.mono, MovePath.length]
  | snoc path h ih => simp only [MovePath.mono, MovePath.length, ih]

/-- The concrete `221-01` replay jointly realizes the disjointness,
cardinality, exact-presentation, and short native-path hypotheses used below. -/
example : ∃
    (_P : ExactSpanPresentation row22101Start row22101Finish)
    (path : MovePath (fun X Y => AllModeMove X Y)
      row22101Start row22101Finish),
    Disjoint (∅ : BinaryAmbientCarrier.State _ _ _) row22101Start ∧
    Disjoint (∅ : BinaryAmbientCarrier.State _ _ _) row22101Finish ∧
    Disjoint row22101Start row22101Finish ∧
    row22101Start.card = 2 ∧ row22101Finish.card = 3 ∧ path.length < 3 := by
  obtain ⟨P⟩ := exists_exactSpanPresentation row22101Start row22101Finish
  let path := row22101Certificate.forward.mono
    (fun h => BinaryAmbientMoves.Coordinate.allModeMove_iff_normalized.mpr h)
  refine ⟨P, path, by simp, by simp, row22101Certificate.disjoint,
    row22101Certificate.card_left, row22101Certificate.card_right, ?_⟩
  rw [movePath_mono_length]
  change row22101ForwardPath.length < 3
  rw [row22101ForwardPath_length]
  omega

private theorem short_forward_path_local_supports
    {A B C : BinaryAmbientCarrier.State U V W}
    (P : ExactSpanPresentation A B)
    (hCA : Disjoint C A) (hCB : Disjoint C B) (hAB : Disjoint A B)
    (hA : A.card = 2) (hB : B.card = 3)
    (path : MovePath
      (fun X Y : BinaryAmbientCarrier.State U V W => AllModeMove X Y)
      (C ∪ A) (C ∪ B))
    (hlength : path.length < 3) :
    ∃ D,
      AllModeMove (C ∪ A) D ∧ AllModeMove D (C ∪ B) ∧
      (C ∪ A) ∆ D ⊆ localBox P ∧ D ∆ (C ∪ B) ⊆ localBox P := by
  obtain ⟨D, t, hfirst, hsecond, htEndpoint, htInter, htUnion,
      hfirstErase, hsecondErase, hcards⟩ :=
    short_path_two_support_localization hCA hCB hAB hA hB
      (fun h => AllModeMove.support_card h) path hlength
  have htFirst : t ∈ (C ∪ A) ∆ D := by
    have htFirstIntersection : t ∈ ((C ∪ A) ∆ D) ∩ (D ∆ (C ∪ B)) := by
      rw [htInter]
      exact Finset.mem_singleton_self t
    exact (Finset.mem_inter.mp htFirstIntersection).1
  have htSecond : t ∈ D ∆ (C ∪ B) := by
    have htSecondIntersection : t ∈ ((C ∪ A) ∆ D) ∩ (D ∆ (C ∪ B)) := by
      rw [htInter]
      exact Finset.mem_singleton_self t
    exact (Finset.mem_inter.mp htSecondIntersection).2
  have htFactors :
      t.1.1 ∈ firstSpan (A ∪ B) ∧
      t.2.1.1 ∈ secondSpan (A ∪ B) ∧
      t.2.2.1 ∈ thirdSpan (A ∪ B) := by
    rcases hcards with hcards | hcards
    · exact factors_mem_endpoint_spans_of_support_erase_subset hfirstErase
        (AllModeMove.support_three_factors_mem_spans
          hfirst hcards.1 htFirst).1
        (AllModeMove.support_three_factors_mem_spans
          hfirst hcards.1 htFirst).2.1
        (AllModeMove.support_three_factors_mem_spans
          hfirst hcards.1 htFirst).2.2
    · exact factors_mem_endpoint_spans_of_support_erase_subset hsecondErase
        (AllModeMove.support_three_factors_mem_spans
          hsecond hcards.2 htSecond).1
        (AllModeMove.support_three_factors_mem_spans
          hsecond hcards.2 htSecond).2.1
        (AllModeMove.support_three_factors_mem_spans
          hsecond hcards.2 htSecond).2.2
  have hUnionFactors : ∀ x ∈ ((C ∪ A) ∆ D) ∪ (D ∆ (C ∪ B)),
      x.1.1 ∈ firstSpan (A ∪ B) ∧
      x.2.1.1 ∈ secondSpan (A ∪ B) ∧
      x.2.2.1 ∈ thirdSpan (A ∪ B) :=
    support_union_factors_mem_endpoint_spans htUnion htFactors
  refine ⟨D, hfirst, hsecond, ?_, ?_⟩
  · intro x hx
    exact (mem_localBox_iff P x).mpr
      (hUnionFactors x (Finset.mem_union_left _ hx))
  · intro x hx
    exact (mem_localBox_iff P x).mpr
      (hUnionFactors x (Finset.mem_union_right _ hx))

/-- Every ambient path of length below three from a contextual two-term
endpoint to a contextual three-term endpoint reflects to an actual normalized
two-edge competitor over the normalized local context. -/
theorem short_forward_path_reflects_two_edges
    {A B C : BinaryAmbientCarrier.State U V W}
    (P : ExactSpanPresentation A B)
    (hCA : Disjoint C A) (hCB : Disjoint C B) (hAB : Disjoint A B)
    (hA : A.card = 2) (hB : B.card = 3)
    (path : MovePath
      (fun X Y : BinaryAmbientCarrier.State U V W => AllModeMove X Y)
      (C ∪ A) (C ∪ B))
    (hlength : path.length < 3) :
    ∃ D : NormalizedBinaryCarrier.State P.profile,
      @NormalizedBinaryAllModeMove.AllModeMove P.profile
        (normalizeLocalContext P C ∪ normalizedLeft P) D ∧
      @NormalizedBinaryAllModeMove.AllModeMove P.profile
        D (normalizeLocalContext P C ∪ normalizedRight P) := by
  obtain ⟨D, hfirst, hsecond, hfirstLocal, hsecondLocal⟩ :=
    short_forward_path_local_supports P hCA hCB hAB hA hB path hlength
  let D₀ := normalizeLocalContext P D
  have hfirst₀ := allModeMove_normalizeLocalContext P hfirst hfirstLocal
  have hsecond₀ := allModeMove_normalizeLocalContext P hsecond hsecondLocal
  refine ⟨D₀, ?_, ?_⟩
  · simpa only [normalizeLocalContext_union_left] using hfirst₀
  · simpa only [normalizeLocalContext_union_right] using hsecond₀

private def reverseAmbientPath :
    {X Y : BinaryAmbientCarrier.State U V W} →
      MovePath (fun D E : BinaryAmbientCarrier.State U V W => AllModeMove D E) X Y →
      MovePath (fun D E : BinaryAmbientCarrier.State U V W => AllModeMove D E) Y X
  | _, _, .singleton X => .singleton X
  | _, _, .snoc path h =>
      (MovePath.one (AllModeMove.reverse h)).trans (reverseAmbientPath path)

private theorem movePath_trans_length
    {α : Type*} [DecidableEq α]
    {R : Finset α → Finset α → Prop} {X Y Z : Finset α}
    (p : MovePath R X Y) (q : MovePath R Y Z) :
    (p.trans q).length = p.length + q.length := by
  induction q with
  | singleton => simp only [MovePath.trans, MovePath.length, Nat.add_zero]
  | snoc q h ih => simp only [MovePath.trans, MovePath.length, ih, Nat.add_assoc]

private theorem reverseAmbientPath_length
    {X Y : BinaryAmbientCarrier.State U V W}
    (path : MovePath
      (fun D E : BinaryAmbientCarrier.State U V W => AllModeMove D E) X Y) :
    (reverseAmbientPath path).length = path.length := by
  induction path with
  | singleton => simp only [reverseAmbientPath, MovePath.length]
  | snoc path h ih =>
      rw [reverseAmbientPath, movePath_trans_length, ih]
      simp only [MovePath.one, MovePath.length]
      omega

private theorem normalizedAllModeMove_reverse {p : Profile}
    {X Y : NormalizedBinaryCarrier.State p}
    (h : @NormalizedBinaryAllModeMove.AllModeMove p X Y) :
    @NormalizedBinaryAllModeMove.AllModeMove p Y X := by
  apply BinaryAmbientMoves.Coordinate.allModeMove_iff_normalized.mp
  exact AllModeMove.reverse
    (BinaryAmbientMoves.Coordinate.allModeMove_iff_normalized.mpr h)

/-- Every ambient path of length below three in the reverse endpoint direction
reflects to an actual normalized two-edge competitor in that same direction. -/
theorem short_reverse_path_reflects_two_edges
    {A B C : BinaryAmbientCarrier.State U V W}
    (P : ExactSpanPresentation A B)
    (hCA : Disjoint C A) (hCB : Disjoint C B) (hAB : Disjoint A B)
    (hA : A.card = 2) (hB : B.card = 3)
    (path : MovePath
      (fun X Y : BinaryAmbientCarrier.State U V W => AllModeMove X Y)
      (C ∪ B) (C ∪ A))
    (hlength : path.length < 3) :
    ∃ D : NormalizedBinaryCarrier.State P.profile,
      @NormalizedBinaryAllModeMove.AllModeMove P.profile
        (normalizeLocalContext P C ∪ normalizedRight P) D ∧
      @NormalizedBinaryAllModeMove.AllModeMove P.profile
        D (normalizeLocalContext P C ∪ normalizedLeft P) := by
  have hreverseLength : (reverseAmbientPath path).length < 3 := by
    rw [reverseAmbientPath_length]
    exact hlength
  obtain ⟨D, hfirst, hsecond⟩ := short_forward_path_reflects_two_edges P
    hCA hCB hAB hA hB (reverseAmbientPath path) hreverseLength
  exact ⟨D, normalizedAllModeMove_reverse hsecond,
    normalizedAllModeMove_reverse hfirst⟩

private theorem normalizedContext_disjoint_left
    {A B C : BinaryAmbientCarrier.State U V W}
    (P : ExactSpanPresentation A B) (hCA : Disjoint C A) :
    Disjoint (normalizeLocalContext P C) (normalizedLeft P) := by
  apply Finset.disjoint_left.mpr
  intro s hsC hsA
  have hmC : mapTerm (exactSpanCoordinateEmbedding P) s ∈ C := by
    have hm : mapTerm (exactSpanCoordinateEmbedding P) s ∈
        mapState (exactSpanCoordinateEmbedding P) (normalizeLocalContext P C) :=
      Finset.mem_image.mpr ⟨s, hsC, rfl⟩
    rw [mapState_normalizeLocalContext] at hm
    exact (Finset.mem_inter.mp hm).1
  have hmA : mapTerm (exactSpanCoordinateEmbedding P) s ∈ A := by
    have hm : mapTerm (exactSpanCoordinateEmbedding P) s ∈
        mapState (exactSpanCoordinateEmbedding P) (normalizedLeft P) :=
      Finset.mem_image.mpr ⟨s, hsA, rfl⟩
    rwa [mapState_normalizedLeft] at hm
  exact Finset.disjoint_left.mp hCA hmC hmA

private theorem normalizedContext_disjoint_right
    {A B C : BinaryAmbientCarrier.State U V W}
    (P : ExactSpanPresentation A B) (hCB : Disjoint C B) :
    Disjoint (normalizeLocalContext P C) (normalizedRight P) := by
  apply Finset.disjoint_left.mpr
  intro s hsC hsB
  have hmC : mapTerm (exactSpanCoordinateEmbedding P) s ∈ C := by
    have hm : mapTerm (exactSpanCoordinateEmbedding P) s ∈
        mapState (exactSpanCoordinateEmbedding P) (normalizeLocalContext P C) :=
      Finset.mem_image.mpr ⟨s, hsC, rfl⟩
    rw [mapState_normalizeLocalContext] at hm
    exact (Finset.mem_inter.mp hm).1
  have hmB : mapTerm (exactSpanCoordinateEmbedding P) s ∈ B := by
    have hm : mapTerm (exactSpanCoordinateEmbedding P) s ∈
        mapState (exactSpanCoordinateEmbedding P) (normalizedRight P) :=
      Finset.mem_image.mpr ⟨s, hsB, rfl⟩
    rwa [mapState_normalizedRight] at hm
  exact Finset.disjoint_left.mp hCB hmC hmB

/-- A normalized every-context lower bound of value two or three lifts to all
ambient paths in the forward endpoint direction, without a locality premise. -/
theorem forward_path_length_ge_of_normalized_context_lower
    {A B C : BinaryAmbientCarrier.State U V W}
    (P : ExactSpanPresentation A B)
    (hCA : Disjoint C A) (hCB : Disjoint C B) (hAB : Disjoint A B)
    (hA : A.card = 2) (hB : B.card = 3)
    (d : ℕ) (hd : d = 2 ∨ d = 3)
    (hnormalized : ∀ K : NormalizedBinaryCarrier.State P.profile,
      Disjoint K (normalizedLeft P) → Disjoint K (normalizedRight P) →
      ∀ q : MovePath (@NormalizedBinaryAllModeMove.AllModeMove P.profile)
        (K ∪ normalizedLeft P) (K ∪ normalizedRight P), d ≤ q.length)
    (path : MovePath
      (fun X Y : BinaryAmbientCarrier.State U V W => AllModeMove X Y)
      (C ∪ A) (C ∪ B)) :
    d ≤ path.length := by
  rcases hd with rfl | rfl
  · exact intrinsic_allModeMovePath_length_two_le hCA hCB hAB hA hB path
  · by_contra hnot
    have hlength : path.length < 3 := Nat.lt_of_not_ge hnot
    obtain ⟨D, hfirst, hsecond⟩ := short_forward_path_reflects_two_edges P
      hCA hCB hAB hA hB path hlength
    let q : MovePath (@NormalizedBinaryAllModeMove.AllModeMove P.profile)
        (normalizeLocalContext P C ∪ normalizedLeft P)
        (normalizeLocalContext P C ∪ normalizedRight P) :=
      .snoc (.one hfirst) hsecond
    have hlower := hnormalized (normalizeLocalContext P C)
      (normalizedContext_disjoint_left P hCA)
      (normalizedContext_disjoint_right P hCB) q
    have hq : q.length = 2 := by
      simp only [q, MovePath.one, MovePath.length]
    omega

/-- A normalized every-context lower bound of value two or three lifts to all
ambient paths in the reverse endpoint direction, without a locality premise. -/
theorem reverse_path_length_ge_of_normalized_context_lower
    {A B C : BinaryAmbientCarrier.State U V W}
    (P : ExactSpanPresentation A B)
    (hCA : Disjoint C A) (hCB : Disjoint C B) (hAB : Disjoint A B)
    (hA : A.card = 2) (hB : B.card = 3)
    (d : ℕ) (hd : d = 2 ∨ d = 3)
    (hnormalized : ∀ K : NormalizedBinaryCarrier.State P.profile,
      Disjoint K (normalizedLeft P) → Disjoint K (normalizedRight P) →
      ∀ q : MovePath (@NormalizedBinaryAllModeMove.AllModeMove P.profile)
        (K ∪ normalizedRight P) (K ∪ normalizedLeft P), d ≤ q.length)
    (path : MovePath
      (fun X Y : BinaryAmbientCarrier.State U V W => AllModeMove X Y)
      (C ∪ B) (C ∪ A)) :
    d ≤ path.length := by
  rcases hd with rfl | rfl
  · have hlower := intrinsic_allModeMovePath_length_two_le hCA hCB hAB hA hB
      (reverseAmbientPath path)
    rwa [reverseAmbientPath_length] at hlower
  · by_contra hnot
    have hlength : path.length < 3 := Nat.lt_of_not_ge hnot
    obtain ⟨D, hfirst, hsecond⟩ := short_reverse_path_reflects_two_edges P
      hCA hCB hAB hA hB path hlength
    let q : MovePath (@NormalizedBinaryAllModeMove.AllModeMove P.profile)
        (normalizeLocalContext P C ∪ normalizedRight P)
        (normalizeLocalContext P C ∪ normalizedLeft P) :=
      .snoc (.one hfirst) hsecond
    have hlower := hnormalized (normalizeLocalContext P C)
      (normalizedContext_disjoint_left P hCA)
      (normalizedContext_disjoint_right P hCB) q
    have hq : q.length = 2 := by
      simp only [q, MovePath.one, MovePath.length]
    omega

#check @short_forward_path_reflects_two_edges
#check @short_reverse_path_reflects_two_edges
#check @forward_path_length_ge_of_normalized_context_lower
#check @reverse_path_length_ge_of_normalized_context_lower

#print axioms short_forward_path_reflects_two_edges
#print axioms short_reverse_path_reflects_two_edges
#print axioms forward_path_length_ge_of_normalized_context_lower
#print axioms reverse_path_length_ge_of_normalized_context_lower

end BilinearComplexity.BinaryAmbientContextDistance
