import BilinearComplexity.FieldFiveToFourContext

set_option autoImplicit false
namespace BilinearComplexity.FieldFiveToFourContext.CertifiedFiveToFour
open FieldRankOne FieldContextual FieldNativeMoves FieldNativePath
open FieldNativePairBridge FieldFiveToFour
abbrev F3 := FieldFiveToFour.F3
variable {a b c : ℕ}

example {I : DisplayedF3PairTriple a b c} (B : CertifiedFiveToFour I)
    (hp : B.normalized.placement = .sourceSource) :
    B.signedResidualTarget = I.targetState := by
  classical
  cases P : B.normalized with
  | sourceSource u v huv hfirst hsecond pair =>
      have hL : B.normalized.leftIndex = I.slots (.inl u) := by
        simpa [P, EffectiveDisplayedF3PairTriple.leftIndex] using hfirst
      have hR : B.normalized.rightIndex = I.slots (.inl v) := by
        simpa [P, EffectiveDisplayedF3PairTriple.rightIndex] using hsecond
      have h0 : B.normalized.normalizedSplit (.inl 0) = I.slots (.inl u) :=
        B.normalized.normalizedSplit_left_zero.trans hL
      have h1 : B.normalized.normalizedSplit (.inl 1) = I.slots (.inl v) :=
        B.normalized.normalizedSplit_left_one.trans hR
      have hcover (i : Fin 2) : i = u ∨ i = v := by
        fin_cases u <;> fin_cases v <;> fin_cases i <;>
          first | omega | simp
      have hleft :
          Set.range (fun i : Fin 2 => B.normalized.normalizedSplit (.inl i)) =
            Set.range (fun i : Fin 2 => I.slots (.inl i)) := by
        ext k
        constructor
        · rintro ⟨i, rfl⟩
          fin_cases i
          · exact ⟨u, h0.symm⟩
          · exact ⟨v, h1.symm⟩
        · rintro ⟨i, rfl⟩
          rcases hcover i with rfl | rfl
          · exact ⟨0, h0⟩
          · exact ⟨1, h1⟩
      have hright := range_comp_inr_eq_of_range_inl_eq
        B.normalized.normalizedSplit I.slots I.atomAt hleft
      have hfin :
          Finset.univ.image (fun j : Fin 3 =>
              I.atomAt (B.normalized.normalizedSplit (.inr j))) =
            Finset.univ.image (fun j : Fin 3 => I.atomAt (I.slots (.inr j))) := by
        ext x
        simpa only [Finset.mem_image, Finset.mem_univ, true_and,
          Set.ext_iff, Set.mem_range] using Set.ext_iff.mp hright x
      rw [DisplayedF3PairTriple.targetState, ← hfin]
      ext x
      simp only [P, FieldFiveToFour.CertifiedFiveToFour.signedResidualTarget,
        EffectiveDisplayedF3PairTriple.signedResidualTarget,
        EffectiveDisplayedF3PairTriple.residualShape,
        EffectiveDisplayedF3PairTriple.placement,
        FieldFiveToFour.CertifiedFiveToFour.signedResidualAtom,
        EffectiveDisplayedF3PairTriple.signedResidualAtom,
        EffectiveDisplayedF3PairTriple.residualReindex,
        EffectiveDisplayedF3PairTriple.residualAtomFamily, tripleState,
        Finset.mem_insert, Finset.mem_singleton, Finset.mem_image,
        Finset.mem_univ, true_and]
      constructor
      · rintro (hx | hx | hx)
        · exact ⟨0, hx.symm⟩
        · exact ⟨1, hx.symm⟩
        · exact ⟨2, hx.symm⟩
      · rintro ⟨j, hx⟩
        fin_cases j
        · exact Or.inl hx.symm
        · exact Or.inr (Or.inl hx.symm)
        · exact Or.inr (Or.inr hx.symm)
  | targetTarget u v huv hfirst hsecond pair =>
      simp [P, EffectiveDisplayedF3PairTriple.placement] at hp
  | oppositeForward u v hfirst hsecond pair =>
      simp [P, EffectiveDisplayedF3PairTriple.placement] at hp
  | oppositeReverse u v hfirst hsecond pair =>
      simp [P, EffectiveDisplayedF3PairTriple.placement] at hp

end BilinearComplexity.FieldFiveToFourContext.CertifiedFiveToFour
