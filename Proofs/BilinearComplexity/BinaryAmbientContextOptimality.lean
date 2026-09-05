import BilinearComplexity.BinaryAmbientMoveSupport

set_option autoImplicit false

/-!
# Ambient optimality for contextual binary five-circuits

This module isolates the finite-set argument behind two-edge ambient
localization.  If two primitive supports of cardinality three or four toggle a
five-element endpoint difference, then one support has size three, the other
has size four, and they meet in a unique auxiliary term.  Every other support
term is an endpoint term.  The final span lemma is the bridge used after native
three-support line geometry has placed the auxiliary factors in the spans of
the other support terms.
-/

namespace BilinearComplexity.BinaryAmbientContextOptimality

open scoped symmDiff
open BinaryAmbientCarrier
open NormalizedBinaryCarrier (F2)

universe u v w

/-- The symmetric-difference cardinality plus twice the intersection
cardinality is the sum of the two cardinalities. -/
theorem card_symmDiff_add_twice_card_inter
    {α : Type*} [DecidableEq α] (S T : Finset α) :
    (S ∆ T).card + 2 * (S ∩ T).card = S.card + T.card := by
  rw [Finset.symmDiff_def,
    Finset.card_union_of_disjoint (Finset.sdiff_disjoint.mono_right Finset.sdiff_subset)]
  rw [Finset.card_sdiff, Finset.card_sdiff, Finset.inter_comm T S]
  have hleft : (S ∩ T).card ≤ S.card :=
    Finset.card_le_card Finset.inter_subset_left
  have hright : (S ∩ T).card ≤ T.card :=
    Finset.card_le_card Finset.inter_subset_right
  omega

/-- Symmetric differences of the consecutive edges of a two-edge chain
telescope to the symmetric difference of its endpoints. -/
theorem symmDiff_chain
    {α : Type*} [DecidableEq α] (D E F : Finset α) :
    (D ∆ E) ∆ (E ∆ F) = D ∆ F := by
  ext x
  simp only [Finset.mem_symmDiff]
  tauto

/-- Adding the same disjoint context to two disjoint endpoint pieces
cancels from their symmetric difference. -/
theorem symmDiff_context_union
    {α : Type*} [DecidableEq α] {C A B : Finset α}
    (hCA : Disjoint C A) (hCB : Disjoint C B) (hAB : Disjoint A B) :
    (C ∪ A) ∆ (C ∪ B) = A ∪ B := by
  ext x
  simp only [Finset.mem_symmDiff, Finset.mem_union]
  have hca : ¬(x ∈ C ∧ x ∈ A) := by
    intro hx
    exact Finset.disjoint_left.mp hCA hx.1 hx.2
  have hcb : ¬(x ∈ C ∧ x ∈ B) := by
    intro hx
    exact Finset.disjoint_left.mp hCB hx.1 hx.2
  have hab : ¬(x ∈ A ∧ x ∈ B) := by
    intro hx
    exact Finset.disjoint_left.mp hAB hx.1 hx.2
  tauto

/-- The common part of two finite sets is disjoint from their symmetric
difference. -/
theorem inter_disjoint_symmDiff
    {α : Type*} [DecidableEq α] (S T : Finset α) :
    Disjoint (S ∩ T) (S ∆ T) := by
  apply Finset.disjoint_left.mpr
  intro x hxI hxD
  simp only [Finset.mem_inter] at hxI
  simp only [Finset.mem_symmDiff] at hxD
  tauto

/-- The union of two finite sets is the union of their common part and
their symmetric difference. -/
theorem union_eq_inter_union_symmDiff
    {α : Type*} [DecidableEq α] (S T : Finset α) :
    S ∪ T = (S ∩ T) ∪ (S ∆ T) := by
  ext x
  simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_symmDiff]
  tauto

/-- Two sets of size three or four whose symmetric difference has size
five have opposite sizes and a one-element intersection. -/
theorem three_four_supports_of_five
    {α : Type*} [DecidableEq α] {S T Z : Finset α}
    (hST : S ∆ T = Z) (hZ : Z.card = 5)
    (hS : S.card = 3 ∨ S.card = 4)
    (hT : T.card = 3 ∨ T.card = 4) :
    ((S.card = 3 ∧ T.card = 4) ∨ (S.card = 4 ∧ T.card = 3)) ∧
      (S ∩ T).card = 1 := by
  have hcard := card_symmDiff_add_twice_card_inter S T
  rw [hST, hZ] at hcard
  rcases hS with hS | hS <;> rcases hT with hT | hT <;>
    omega

/-- If two primitive-sized supports have a five-element symmetric
difference, they share one auxiliary outside it and all other terms belong to
the symmetric difference. -/
theorem two_support_localization
    {α : Type*} [DecidableEq α] {S T Z : Finset α}
    (hST : S ∆ T = Z) (hZ : Z.card = 5)
    (hS : S.card = 3 ∨ S.card = 4)
    (hT : T.card = 3 ∨ T.card = 4) :
    ∃ t : α,
      t ∉ Z ∧
      S ∩ T = {t} ∧
      S ∪ T = insert t Z ∧
      S.erase t ⊆ Z ∧
      T.erase t ⊆ Z ∧
      ((S.card = 3 ∧ T.card = 4) ∨ (S.card = 4 ∧ T.card = 3)) := by
  have hclassification := three_four_supports_of_five hST hZ hS hT
  obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hclassification.2
  have htNotZ : t ∉ Z := by
    have hdisjoint : Disjoint (S ∩ T) Z := by
      rw [← hST]
      exact inter_disjoint_symmDiff S T
    exact Finset.disjoint_left.mp hdisjoint (by simp only [ht, Finset.mem_singleton])
  have hunion : S ∪ T = insert t Z := by
    rw [union_eq_inter_union_symmDiff S T, ht, hST, Finset.singleton_union]
  have hSerase : S.erase t ⊆ Z := by
    intro x hx
    have hxS : x ∈ S := (Finset.mem_erase.mp hx).2
    have hxt : x ≠ t := (Finset.mem_erase.mp hx).1
    have hxUnion : x ∈ insert t Z := by
      rw [← hunion]
      exact Finset.mem_union_left T hxS
    simpa only [Finset.mem_insert, hxt, false_or] using hxUnion
  have hTerase : T.erase t ⊆ Z := by
    intro x hx
    have hxT : x ∈ T := (Finset.mem_erase.mp hx).2
    have hxt : x ≠ t := (Finset.mem_erase.mp hx).1
    have hxUnion : x ∈ insert t Z := by
      rw [← hunion]
      exact Finset.mem_union_right S hxT
    simpa only [Finset.mem_insert, hxt, false_or] using hxUnion
  exact ⟨t, htNotZ, ht, hunion, hSerase, hTerase, hclassification.1⟩

/-- For a two-edge chain between a contextual two-term endpoint and a
contextual three-term endpoint, primitive-sized supports share exactly one
non-endpoint auxiliary and otherwise consist only of endpoint terms. -/
theorem endpoint_support_localization
    {α : Type*} [DecidableEq α]
    {C A B D : Finset α}
    (hCA : Disjoint C A) (hCB : Disjoint C B) (hAB : Disjoint A B)
    (hA : A.card = 2) (hB : B.card = 3)
    (hFirst : ((C ∪ A) ∆ D).card = 3 ∨ ((C ∪ A) ∆ D).card = 4)
    (hSecond : (D ∆ (C ∪ B)).card = 3 ∨ (D ∆ (C ∪ B)).card = 4) :
    ∃ t : α,
      t ∉ A ∪ B ∧
      ((C ∪ A) ∆ D) ∩ (D ∆ (C ∪ B)) = {t} ∧
      ((C ∪ A) ∆ D) ∪ (D ∆ (C ∪ B)) = insert t (A ∪ B) ∧
      (((C ∪ A) ∆ D).erase t ⊆ A ∪ B) ∧
      ((D ∆ (C ∪ B)).erase t ⊆ A ∪ B) ∧
      (((C ∪ A) ∆ D).card = 3 ∧ (D ∆ (C ∪ B)).card = 4 ∨
        ((C ∪ A) ∆ D).card = 4 ∧ (D ∆ (C ∪ B)).card = 3) := by
  have hEndpoint : (C ∪ A) ∆ (C ∪ B) = A ∪ B :=
    symmDiff_context_union hCA hCB hAB
  have hSupport : ((C ∪ A) ∆ D) ∆ (D ∆ (C ∪ B)) = A ∪ B := by
    rw [symmDiff_chain, hEndpoint]
  have hABcard : (A ∪ B).card = 5 := by
    rw [Finset.card_union_of_disjoint hAB, hA, hB]
  exact two_support_localization hSupport hABcard hFirst hSecond

/-- Every finite path of length less than three has zero, one, or two
edges, with the corresponding endpoint relation data exposed. -/
theorem movePath_length_lt_three_cases
    {α : Type*} [DecidableEq α]
    {R : Finset α → Finset α → Prop} {D F : Finset α}
    (path : BinaryCircuit.MovePath R D F) (hlength : path.length < 3) :
    D = F ∨ R D F ∨ ∃ E : Finset α, R D E ∧ R E F := by
  cases path with
  | singleton => exact Or.inl rfl
  | snoc path hlast =>
      cases path with
      | singleton => exact Or.inr (Or.inl hlast)
      | snoc path hfirst =>
          cases path with
          | singleton => exact Or.inr (Or.inr ⟨_, hfirst, hlast⟩)
          | snoc path _ =>
              simp only [BinaryCircuit.MovePath.length] at hlength
              omega

/-- For any relation whose edge supports have size three or four, an arbitrary
path of length less than three between contextual two- and three-term
endpoints has exactly two edges and the unique-auxiliary support decomposition.
No locality or context-persistence condition is imposed on the path. -/
theorem short_path_two_support_localization
    {α : Type*} [DecidableEq α]
    {R : Finset α → Finset α → Prop} {C A B : Finset α}
    (hCA : Disjoint C A) (hCB : Disjoint C B) (hAB : Disjoint A B)
    (hA : A.card = 2) (hB : B.card = 3)
    (hSupportCard : ∀ {X Y}, R X Y →
      (X ∆ Y).card = 3 ∨ (X ∆ Y).card = 4)
    (path : BinaryCircuit.MovePath R (C ∪ A) (C ∪ B))
    (hlength : path.length < 3) :
    ∃ D t,
      R (C ∪ A) D ∧
      R D (C ∪ B) ∧
      t ∉ A ∪ B ∧
      ((C ∪ A) ∆ D) ∩ (D ∆ (C ∪ B)) = {t} ∧
      ((C ∪ A) ∆ D) ∪ (D ∆ (C ∪ B)) = insert t (A ∪ B) ∧
      (((C ∪ A) ∆ D).erase t ⊆ A ∪ B) ∧
      ((D ∆ (C ∪ B)).erase t ⊆ A ∪ B) ∧
      (((C ∪ A) ∆ D).card = 3 ∧ (D ∆ (C ∪ B)).card = 4 ∨
        ((C ∪ A) ∆ D).card = 4 ∧ (D ∆ (C ∪ B)).card = 3) := by
  rcases movePath_length_lt_three_cases path hlength with hzero | hone | htwo
  · have hstartCard : (C ∪ A).card = C.card + 2 := by
      rw [Finset.card_union_of_disjoint hCA, hA]
    have hfinishCard : (C ∪ B).card = C.card + 3 := by
      rw [Finset.card_union_of_disjoint hCB, hB]
    have hcards := congrArg Finset.card hzero
    omega
  · have hEndpoint : (C ∪ A) ∆ (C ∪ B) = A ∪ B :=
      symmDiff_context_union hCA hCB hAB
    have hABcard : (A ∪ B).card = 5 := by
      rw [Finset.card_union_of_disjoint hAB, hA, hB]
    rcases hSupportCard hone with hcard | hcard <;>
      rw [hEndpoint, hABcard] at hcard <;> omega
  · obtain ⟨D, hfirst, hsecond⟩ := htwo
    obtain ⟨t, htZ, htInter, htUnion, hfirstErase, hsecondErase,
        hcards⟩ := endpoint_support_localization hCA hCB hAB hA hB
      (hSupportCard hfirst) (hSupportCard hsecond)
    exact ⟨D, t, hfirst, hsecond, htZ, htInter, htUnion, hfirstErase,
      hsecondErase, hcards⟩

/-- A path of length less than two is either empty or a single edge. -/
theorem movePath_length_lt_two_cases
    {α : Type*} [DecidableEq α]
    {R : Finset α → Finset α → Prop} {D E : Finset α}
    (path : BinaryCircuit.MovePath R D E) (hlength : path.length < 2) :
    D = E ∨ R D E := by
  cases path with
  | singleton => exact Or.inl rfl
  | snoc path hlast =>
      cases path with
      | singleton => exact Or.inr hlast
      | snoc path _ =>
          simp only [BinaryCircuit.MovePath.length] at hlength
          omega

/-- Any path whose edge supports have cardinality three or four needs at
least two edges between contextual disjoint two- and three-term endpoints. -/
theorem movePath_length_two_le_of_support_card
    {α : Type*} [DecidableEq α]
    {R : Finset α → Finset α → Prop} {C A B : Finset α}
    (hCA : Disjoint C A) (hCB : Disjoint C B) (hAB : Disjoint A B)
    (hA : A.card = 2) (hB : B.card = 3)
    (hSupportCard : ∀ {X Y}, R X Y →
      (X ∆ Y).card = 3 ∨ (X ∆ Y).card = 4)
    (path : BinaryCircuit.MovePath R (C ∪ A) (C ∪ B)) :
    2 ≤ path.length := by
  by_contra hnot
  have hlength : path.length < 2 := Nat.lt_of_not_ge hnot
  rcases movePath_length_lt_two_cases path hlength with hzero | hone
  · have hstartCard : (C ∪ A).card = C.card + 2 := by
      rw [Finset.card_union_of_disjoint hCA, hA]
    have hfinishCard : (C ∪ B).card = C.card + 3 := by
      rw [Finset.card_union_of_disjoint hCB, hB]
    have hcards := congrArg Finset.card hzero
    omega
  · have hEndpoint : (C ∪ A) ∆ (C ∪ B) = A ∪ B :=
      symmDiff_context_union hCA hCB hAB
    have hABcard : (A ∪ B).card = 5 := by
      rw [Finset.card_union_of_disjoint hAB, hA, hB]
    rcases hSupportCard hone with hcard | hcard <;>
      rw [hEndpoint, hABcard] at hcard <;> omega

/-- Intrinsic all-mode ambient paths need at least two edges between contextual
disjoint two- and three-term endpoints. -/
theorem intrinsic_allModeMovePath_length_two_le
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    [DecidableEq U] [DecidableEq V] [DecidableEq W]
    {C A B : State U V W}
    (hCA : Disjoint C A) (hCB : Disjoint C B) (hAB : Disjoint A B)
    (hA : A.card = 2) (hB : B.card = 3)
    (path : BinaryCircuit.MovePath
      (fun D E : State U V W => BinaryAmbientMoves.AllModeMove D E)
      (C ∪ A) (C ∪ B)) :
    2 ≤ path.length := by
  exact movePath_length_two_le_of_support_card hCA hCB hAB hA hB
    (fun h => BinaryAmbientMoveSupport.AllModeMove.support_card h) path

/-- If every three-support edge has one supplied geometry predicate, every
four-support edge has another, and no three/four support pair XORs to the
endpoint difference, then no path of length less than three exists.  This is
the abstract semantic bridge for the small finite lower-bound checker; edge
legality and background occupancy no longer occur in its exclusion premise. -/
theorem no_short_path_of_no_three_four_support_pair
    {α : Type*} [DecidableEq α]
    {R : Finset α → Finset α → Prop} {C A B : Finset α}
    (IsThree IsFour : Finset α → Prop)
    (hCA : Disjoint C A) (hCB : Disjoint C B) (hAB : Disjoint A B)
    (hA : A.card = 2) (hB : B.card = 3)
    (hSupportCard : ∀ {X Y}, R X Y →
      (X ∆ Y).card = 3 ∨ (X ∆ Y).card = 4)
    (hThree : ∀ {X Y}, R X Y → (X ∆ Y).card = 3 → IsThree (X ∆ Y))
    (hFour : ∀ {X Y}, R X Y → (X ∆ Y).card = 4 → IsFour (X ∆ Y))
    (hExclude : ∀ {S T : Finset α},
      S ∆ T = A ∪ B → S.card = 3 → T.card = 4 →
      IsThree S → IsFour T → False)
    (path : BinaryCircuit.MovePath R (C ∪ A) (C ∪ B)) :
    ¬ path.length < 3 := by
  intro hlength
  obtain ⟨D, t, hfirst, hsecond, htZ, htInter, htUnion, hfirstErase,
      hsecondErase, hcards⟩ := short_path_two_support_localization
    hCA hCB hAB hA hB hSupportCard path hlength
  have hEndpoint : (C ∪ A) ∆ (C ∪ B) = A ∪ B :=
    symmDiff_context_union hCA hCB hAB
  have hSupport : ((C ∪ A) ∆ D) ∆ (D ∆ (C ∪ B)) = A ∪ B := by
    rw [symmDiff_chain, hEndpoint]
  rcases hcards with hcards | hcards
  · exact hExclude hSupport hcards.1 hcards.2
      (hThree hfirst hcards.1) (hFour hsecond hcards.2)
  · have hSupport' : (D ∆ (C ∪ B)) ∆ ((C ∪ A) ∆ D) = A ∪ B := by
      rw [symmDiff_comm, hSupport]
    exact hExclude hSupport' hcards.2 hcards.1
      (hThree hsecond hcards.2) (hFour hfirst hcards.1)

/-- Exact first-factor spans are monotone under inclusion of states. -/
theorem firstSpan_mono
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    [DecidableEq (Carrier U V W)]
    {S T : State U V W} (hST : S ⊆ T) :
    firstSpan S ≤ firstSpan T := by
  apply Submodule.span_mono
  exact Set.image_mono (by simpa using hST)

/-- Exact second-factor spans are monotone under inclusion of states. -/
theorem secondSpan_mono
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    [DecidableEq (Carrier U V W)]
    {S T : State U V W} (hST : S ⊆ T) :
    secondSpan S ≤ secondSpan T := by
  apply Submodule.span_mono
  exact Set.image_mono (by simpa using hST)

/-- Exact third-factor spans are monotone under inclusion of states. -/
theorem thirdSpan_mono
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    [DecidableEq (Carrier U V W)]
    {S T : State U V W} (hST : S ⊆ T) :
    thirdSpan S ≤ thirdSpan T := by
  apply Submodule.span_mono
  exact Set.image_mono (by simpa using hST)

/-- A term outside a finite symmetric difference has the same membership
status in both finite sets. -/
theorem mem_iff_mem_of_not_mem_symmDiff
    {α : Type*} [DecidableEq α] {D E : Finset α} {x : α}
    (hx : x ∉ D ∆ E) :
    x ∈ D ↔ x ∈ E := by
  simp only [Finset.mem_symmDiff] at hx
  tauto

/-- If an auxiliary term's factors lie in the exact spans of the other
terms of one support, and those other terms are endpoints, then all auxiliary
factors lie in the exact endpoint factor spans. -/
theorem factors_mem_endpoint_spans_of_support_erase_subset
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    [DecidableEq (Carrier U V W)]
    {S Z : State U V W} {t : Carrier U V W}
    (hSZ : S.erase t ⊆ Z)
    (hfirst : t.1.1 ∈ firstSpan (S.erase t))
    (hsecond : t.2.1.1 ∈ secondSpan (S.erase t))
    (hthird : t.2.2.1 ∈ thirdSpan (S.erase t)) :
    t.1.1 ∈ firstSpan Z ∧
      t.2.1.1 ∈ secondSpan Z ∧
      t.2.2.1 ∈ thirdSpan Z := by
  exact ⟨firstSpan_mono hSZ hfirst, secondSpan_mono hSZ hsecond,
    thirdSpan_mono hSZ hthird⟩

/-- Once the unique auxiliary belongs to the three exact endpoint factor
spans, the whole union of the two supports belongs to those spans. -/
theorem support_union_factors_mem_endpoint_spans
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    [DecidableEq (Carrier U V W)]
    {S T Z : State U V W} {t : Carrier U V W}
    (hUnion : S ∪ T = insert t Z)
    (ht : t.1.1 ∈ firstSpan Z ∧
      t.2.1.1 ∈ secondSpan Z ∧
      t.2.2.1 ∈ thirdSpan Z) :
    ∀ x ∈ S ∪ T,
      x.1.1 ∈ firstSpan Z ∧
      x.2.1.1 ∈ secondSpan Z ∧
      x.2.2.1 ∈ thirdSpan Z := by
  intro x hx
  have hxInsert : x ∈ insert t Z := by
    rw [← hUnion]
    exact hx
  rcases Finset.mem_insert.mp hxInsert with hxt | hxZ
  · subst x
    exact ht
  · exact ⟨first_mem_firstSpan hxZ, second_mem_secondSpan hxZ,
      third_mem_thirdSpan hxZ⟩

/-- A two-edge intermediate cannot change membership of a term outside the
factor box containing the union of its two supports. -/
theorem intermediate_mem_iff_of_support_union_factor_confined
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    [DecidableEq (Carrier U V W)]
    {D E F Z : State U V W} {x : Carrier U V W}
    (hlocal : ∀ y ∈ (D ∆ E) ∪ (E ∆ F),
      y.1.1 ∈ firstSpan Z ∧
      y.2.1.1 ∈ secondSpan Z ∧
      y.2.2.1 ∈ thirdSpan Z)
    (hxOutside : ¬(x.1.1 ∈ firstSpan Z ∧
      x.2.1.1 ∈ secondSpan Z ∧
      x.2.2.1 ∈ thirdSpan Z)) :
    (x ∈ D ↔ x ∈ E) ∧ (x ∈ E ↔ x ∈ F) := by
  have hxUnion : x ∉ (D ∆ E) ∪ (E ∆ F) := by
    intro hx
    exact hxOutside (hlocal x hx)
  have hxFirst : x ∉ D ∆ E := by
    intro hx
    exact hxUnion (Finset.mem_union_left _ hx)
  have hxSecond : x ∉ E ∆ F := by
    intro hx
    exact hxUnion (Finset.mem_union_right _ hx)
  exact ⟨mem_iff_mem_of_not_mem_symmDiff hxFirst,
    mem_iff_mem_of_not_mem_symmDiff hxSecond⟩

example :
    let Z : Finset (Fin 6) := {0, 1, 2, 3, 4}
    let S : Finset (Fin 6) := {0, 1, 5}
    let T : Finset (Fin 6) := {2, 3, 4, 5}
    S ∆ T = Z ∧ Z.card = 5 ∧ S.card = 3 ∧ T.card = 4 := by
  decide

#check @two_support_localization
#check @endpoint_support_localization
#check @factors_mem_endpoint_spans_of_support_erase_subset

end BilinearComplexity.BinaryAmbientContextOptimality
