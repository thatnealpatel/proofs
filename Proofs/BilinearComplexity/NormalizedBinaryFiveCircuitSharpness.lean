import BilinearComplexity.NormalizedBinaryFiveCircuitRows

set_option autoImplicit false

/-!
# Symbolic length-three sharpness for normalized profile 411

Every source orientation of an all-mode move at target profile `(4,1,1)` has
a one-dimensional binary factor in at least one of the two Flip shear modes.
A Flip would therefore create a zero factor, which is excluded by the
normalized carrier. Consequently every legal edge changes cardinality by
exactly one.

This module also handles the otherwise omitted one-edge case. A Split from a
two-term state, or a Reduction from a three-term state, leaves one source term
untouched, so it cannot connect disjoint endpoints. These facts prove that the
certified length-three paths for selected row `411-01` are sharp in both
actual directed `AllModeMove` relations.

AI disclosure: produced with AI assistance (see `README`).
-/

namespace BilinearComplexity.NormalizedBinaryFiveCircuitSharpness

open BinaryCircuit
open NormalizedBinaryCarrier
open NormalizedBinaryReplay221
open NormalizedBinaryModePermutation
open NormalizedBinaryAllModeMove
open NormalizedBinaryFiveCircuitCertificate
open NormalizedBinaryFiveCircuitRows
open Scheme.Action

private theorem nonzeroVector_one_eq (u v : NonzeroVector 1) : u = v := by
  obtain ⟨x, hx⟩ := Fintype.card_eq_one_iff.mp card_nonzeroVector_one
  exact (hx u).trans (hx v).symm

private theorem sourceThirdFlip_false_of_first_eq_one {p : Profile}
    (hp : p.first = 1)
    {sourceLeft sourceRight targetLeft targetRight : Carrier p}
    {D E : State p}
    (h : SourceThirdFlip sourceLeft sourceRight targetLeft targetRight D E) :
    False := by
  rcases p with ⟨a, b, c⟩
  simp only at hp
  subst a
  rcases h with ⟨_, _, _, _, _, _, _, htargetLeftFirst, _⟩
  have heq : sourceLeft.1.1 = sourceRight.1.1 :=
    congrArg Subtype.val
      (nonzeroVector_one_eq sourceLeft.1 sourceRight.1)
  apply targetLeft.1.2
  rw [htargetLeftFirst, heq]
  exact CharTwo.add_self_eq_zero _

private theorem sourceThirdFlip_false_of_second_eq_one {p : Profile}
    (hp : p.second = 1)
    {sourceLeft sourceRight targetLeft targetRight : Carrier p}
    {D E : State p}
    (h : SourceThirdFlip sourceLeft sourceRight targetLeft targetRight D E) :
    False := by
  rcases p with ⟨a, b, c⟩
  simp only at hp
  subst b
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _,
    htargetRightSecond, _⟩
  have heq : sourceRight.2.1.1 = sourceLeft.2.1.1 :=
    congrArg Subtype.val
      (nonzeroVector_one_eq sourceRight.2.1 sourceLeft.2.1)
  apply targetRight.2.1.2
  rw [htargetRightSecond, heq]
  exact sub_self _

/-- No actual source-coordinate Flip can underlie an all-mode edge whose
permuted target profile is `(4,1,1)`, for any of the six orientations. -/
theorem sourceThirdFlip_false_of_permProfile_eq_profile411
    {p : Profile} {o : Orientation}
    (hp : permProfile o p = profile411)
    {sourceLeft sourceRight targetLeft targetRight : Carrier p}
    {D E : State p}
    (h : SourceThirdFlip sourceLeft sourceRight targetLeft targetRight D E) :
    False := by
  rcases p with ⟨a, b, c⟩
  cases o <;>
    simp only [permProfile, profile411, Orientation.firstDim,
      Orientation.secondDim, Orientation.thirdDim, Profile.mk.injEq] at hp
  all_goals
    rcases hp with ⟨h1, h2, h3⟩
  case abc => exact sourceThirdFlip_false_of_second_eq_one h2 h
  case bca => exact sourceThirdFlip_false_of_first_eq_one h3 h
  case cab => exact sourceThirdFlip_false_of_first_eq_one h2 h
  case acb => exact sourceThirdFlip_false_of_second_eq_one h3 h
  case cba => exact sourceThirdFlip_false_of_first_eq_one h3 h
  case bac => exact sourceThirdFlip_false_of_first_eq_one h2 h

private theorem cast_state_card {p q : Profile} (hp : p = q)
    (D : State p) :
    (cast (congrArg State hp) D).card = D.card := by
  subst q
  rfl

private theorem card_eq_of_permute_cast {p q : Profile} (o : Orientation)
    (hp : permProfile o p = q) (D : State q) (D₀ : State p)
    (hD : D = cast (congrArg State hp) (permuteState o D₀)) :
    D.card = D₀.card := by
  calc
    D.card = (cast (congrArg State hp) (permuteState o D₀)).card :=
      congrArg Finset.card hD
    _ = (permuteState o D₀).card := cast_state_card hp _
    _ = D₀.card := permuteState_card o D₀

private theorem allModeMove_profile411_card_ne {D E : State profile411}
    (h : AllModeMove D E) : D.card ≠ E.card := by
  intro hcard
  obtain ⟨p, o, hp, D₀, E₀, hmove, hD, hE⟩ := h.provenance
  have hDcard : D.card = D₀.card :=
    card_eq_of_permute_cast o hp D D₀ hD
  have hEcard : E.card = E₀.card :=
    card_eq_of_permute_cast o hp E E₀ hE
  cases hmove with
  | generatedFirstSplit hsplit =>
      have hchange := hsplit.card_eq
      omega
  | sourceThirdFlip hflip =>
      exact sourceThirdFlip_false_of_permProfile_eq_profile411 hp hflip
  | directedNarrowPairReduction hreduction =>
      have hchange := hreduction.card_add_one_eq
      omega

/-- Every actual directed all-mode edge in the normalized `(4,1,1)` carrier
changes finite-set cardinality by exactly one; the preserving Flip case is
impossible. -/
theorem allModeMove_profile411_card_strict_change {D E : State profile411}
    (h : AllModeMove D E) :
    E.card = D.card + 1 ∨ E.card + 1 = D.card := by
  rcases h.card_change with hsplit | hflip | hreduction
  · exact Or.inl hsplit
  · exact False.elim (allModeMove_profile411_card_ne h hflip.symm)
  · exact Or.inr hreduction

private theorem disjoint_source_of_permute_cast {p q : Profile}
    (o : Orientation) (hp : permProfile o p = q)
    (D E : State q) (D₀ E₀ : State p)
    (hD : D = cast (congrArg State hp) (permuteState o D₀))
    (hE : E = cast (congrArg State hp) (permuteState o E₀))
    (hdisjoint : Disjoint D E) : Disjoint D₀ E₀ := by
  rw [hD, hE] at hdisjoint
  subst q
  exact (Finset.disjoint_image (permuteTerm_injective o)).mp hdisjoint

private theorem generatedFirstSplit_not_disjoint_of_one_lt_card
    {p : Profile}
    {source outputLeft outputRight : Carrier p} {D E : State p}
    (h : GeneratedFirstSplit source outputLeft outputRight D E)
    (hcard : 1 < D.card) : ¬ Disjoint D E := by
  rcases h with ⟨hsource, _, _, _, _, _, _, _, _, htarget⟩
  have heraseCard := Finset.card_erase_add_one hsource
  have herasePos : 0 < (D.erase source).card := by omega
  obtain ⟨survivor, hsurvivorErase⟩ := Finset.card_pos.mp herasePos
  have hsurvivorD : survivor ∈ D :=
    (Finset.mem_erase.mp hsurvivorErase).2
  have hsurvivorE : survivor ∈ E := by
    rw [htarget]
    exact Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem hsurvivorErase)
  intro hdisjoint
  exact (Finset.disjoint_left.mp hdisjoint) hsurvivorD hsurvivorE

private theorem directedNarrowPairReduction_not_disjoint_of_two_lt_card
    {p : Profile}
    {sourceLeft sourceRight target : Carrier p} {D E : State p}
    (h : DirectedNarrowPairReduction sourceLeft sourceRight target D E)
    (hcard : 2 < D.card) : ¬ Disjoint D E := by
  rcases h with ⟨hleft, hright, hsources, _, _, _, _, _, _, htarget⟩
  have hrightErase : sourceRight ∈ D.erase sourceLeft :=
    Finset.mem_erase.mpr ⟨hsources.symm, hright⟩
  have heraseLeftCard := Finset.card_erase_add_one hleft
  have heraseRightCard := Finset.card_erase_add_one hrightErase
  have herasePos : 0 < ((D.erase sourceLeft).erase sourceRight).card := by
    omega
  obtain ⟨survivor, hsurvivorErase⟩ := Finset.card_pos.mp herasePos
  have hsurvivorD : survivor ∈ D :=
    (Finset.mem_erase.mp (Finset.mem_erase.mp hsurvivorErase).2).2
  have hsurvivorE : survivor ∈ E := by
    rw [htarget]
    exact Finset.mem_insert_of_mem hsurvivorErase
  intro hdisjoint
  exact (Finset.disjoint_left.mp hdisjoint) hsurvivorD hsurvivorE

private theorem no_one_move_of_disjoint_card_two_three
    {D E : State profile411}
    (hdisjoint : Disjoint D E) (hDcard : D.card = 2)
    (hEcard : E.card = 3) : ¬ AllModeMove D E := by
  intro h
  obtain ⟨p, o, hp, D₀, E₀, hmove, hD, hE⟩ := h.provenance
  have hD₀card : D.card = D₀.card :=
    card_eq_of_permute_cast o hp D D₀ hD
  have hE₀card : E.card = E₀.card :=
    card_eq_of_permute_cast o hp E E₀ hE
  have hsourceDisjoint : Disjoint D₀ E₀ :=
    disjoint_source_of_permute_cast o hp D E D₀ E₀ hD hE hdisjoint
  cases hmove with
  | generatedFirstSplit hsplit =>
      exact generatedFirstSplit_not_disjoint_of_one_lt_card hsplit
        (by omega) hsourceDisjoint
  | sourceThirdFlip hflip =>
      exact sourceThirdFlip_false_of_permProfile_eq_profile411 hp hflip
  | directedNarrowPairReduction hreduction =>
      have hchange := hreduction.card_add_one_eq
      omega

private theorem no_one_move_of_disjoint_card_three_two
    {D E : State profile411}
    (hdisjoint : Disjoint D E) (hDcard : D.card = 3)
    (hEcard : E.card = 2) : ¬ AllModeMove D E := by
  intro h
  obtain ⟨p, o, hp, D₀, E₀, hmove, hD, hE⟩ := h.provenance
  have hD₀card : D.card = D₀.card :=
    card_eq_of_permute_cast o hp D D₀ hD
  have hE₀card : E.card = E₀.card :=
    card_eq_of_permute_cast o hp E E₀ hE
  have hsourceDisjoint : Disjoint D₀ E₀ :=
    disjoint_source_of_permute_cast o hp D E D₀ E₀ hD hE hdisjoint
  cases hmove with
  | generatedFirstSplit hsplit =>
      have hchange := hsplit.card_eq
      omega
  | sourceThirdFlip hflip =>
      exact sourceThirdFlip_false_of_permProfile_eq_profile411 hp hflip
  | directedNarrowPairReduction hreduction =>
      exact directedNarrowPairReduction_not_disjoint_of_two_lt_card
        hreduction (by omega) hsourceDisjoint

private theorem no_path_le_two_of_disjoint_card_two_three
    {D E : State profile411}
    (hdisjoint : Disjoint D E) (hDcard : D.card = 2)
    (hEcard : E.card = 3)
    (path : MovePath (@AllModeMove profile411) D E) :
    ¬ path.length ≤ 2 := by
  intro hlength
  cases path with
  | singleton => omega
  | snoc path hlast =>
      cases path with
      | singleton =>
          exact no_one_move_of_disjoint_card_two_three hdisjoint hDcard
            hEcard hlast
      | snoc path hfirst =>
          cases path with
          | singleton =>
              rcases allModeMove_profile411_card_strict_change hfirst with
                  hfirst | hfirst <;>
                rcases allModeMove_profile411_card_strict_change hlast with
                  hlast | hlast <;>
                omega
          | snoc path _ =>
              simp only [MovePath.length] at hlength
              omega

private theorem no_path_le_two_of_disjoint_card_three_two
    {D E : State profile411}
    (hdisjoint : Disjoint D E) (hDcard : D.card = 3)
    (hEcard : E.card = 2)
    (path : MovePath (@AllModeMove profile411) D E) :
    ¬ path.length ≤ 2 := by
  intro hlength
  cases path with
  | singleton => omega
  | snoc path hlast =>
      cases path with
      | singleton =>
          exact no_one_move_of_disjoint_card_three_two hdisjoint hDcard
            hEcard hlast
      | snoc path hfirst =>
          cases path with
          | singleton =>
              rcases allModeMove_profile411_card_strict_change hfirst with
                  hfirst | hfirst <;>
                rcases allModeMove_profile411_card_strict_change hlast with
                  hlast | hlast <;>
                omega
          | snoc path _ =>
              simp only [MovePath.length] at hlength
              omega

/-- No actual directed all-mode path from the selected row-`411-01` two-term
endpoint to its three-term endpoint has at most two edges. -/
theorem row41101_no_forward_path_length_le_two
    (path : MovePath (@AllModeMove profile411)
      row41101Start row41101Finish) :
    ¬ path.length ≤ 2 :=
  no_path_le_two_of_disjoint_card_two_three row41101_disjoint
    row41101_card_start row41101_card_finish path

/-- No actual directed all-mode path from the selected row-`411-01` three-term
endpoint to its two-term endpoint has at most two edges. -/
theorem row41101_no_reverse_path_length_le_two
    (path : MovePath (@AllModeMove profile411)
      row41101Finish row41101Start) :
    ¬ path.length ≤ 2 :=
  no_path_le_two_of_disjoint_card_three_two row41101_disjoint.symm
    row41101_card_finish row41101_card_start path

/-- The selected row-`411-01` hypotheses are jointly satisfiable, witnessed by
its kernel-replayed certificate from the thirteen-row data module. -/
theorem row41101_certificate_nonempty :
    Nonempty (FiveCircuitCertificate profile411
      row41101Start row41101Finish) :=
  ⟨certified41101.certificate⟩

/-- The certified forward and reverse paths for selected row `411-01` both
have exact length three, and every actual directed path between the ordered
endpoints in either direction has length greater than two. -/
theorem row41101_exact_directed_length_three :
    row41101ForwardPath.length = 3 ∧
      row41101ReversePath.length = 3 ∧
      (∀ path : MovePath (@AllModeMove profile411)
        row41101Start row41101Finish, ¬ path.length ≤ 2) ∧
      (∀ path : MovePath (@AllModeMove profile411)
        row41101Finish row41101Start, ¬ path.length ≤ 2) := by
  exact ⟨row41101ForwardPath_length, row41101ReversePath_length,
    row41101_no_forward_path_length_le_two,
    row41101_no_reverse_path_length_le_two⟩

#check @sourceThirdFlip_false_of_permProfile_eq_profile411
#check @allModeMove_profile411_card_strict_change
#check @row41101_no_forward_path_length_le_two
#check @row41101_no_reverse_path_length_le_two
#check @row41101_certificate_nonempty
#check @row41101_exact_directed_length_three

#print axioms sourceThirdFlip_false_of_permProfile_eq_profile411
#print axioms allModeMove_profile411_card_strict_change
#print axioms row41101_no_forward_path_length_le_two
#print axioms row41101_no_reverse_path_length_le_two
#print axioms row41101_certificate_nonempty
#print axioms row41101_exact_directed_length_three

end BilinearComplexity.NormalizedBinaryFiveCircuitSharpness
