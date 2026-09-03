import BilinearComplexity.NormalizedBinaryReplay221

set_option autoImplicit false

/-!
# Factorwise-injective transport spike for the profile-221 replay

This scratch module tests transport of the designated `(2,2,1)` replay into
`(3,3,2)` by non-coordinate linear embeddings in all three factors.  The
production move predicates are fixed to `profile221`, so the target predicates
below are deliberately local generalized copies rather than a redesign of the
move system.
-/

namespace BilinearComplexity.NormalizedBinaryTransport221Spike

open NormalizedBinaryCarrier BinaryCircuit
open NormalizedBinaryReplay221

/-- The target profile `(3,3,2)` of the transport experiment. -/
def profile332 : Profile := ⟨3, 3, 2⟩

example : profile332 = ⟨3, 3, 2⟩ := rfl

/-- A non-coordinate shear embedding `F2² → F2³`. -/
def shear2 (u : CoordinateVector 2) : CoordinateVector 3 :=
  ![u 0 + u 1, u 1, u 0]

example : shear2 (![1, 0] : CoordinateVector 2) = ![1, 0, 1] := by decide
example : shear2 (![0, 1] : CoordinateVector 2) = ![1, 1, 0] := by decide

/-- A diagonal embedding `F2¹ → F2²`, non-coordinate with respect to the
standard coordinate inclusions. -/
def diagonal1 (u : CoordinateVector 1) : CoordinateVector 2 := ![u 0, u 0]

example : diagonal1 (![1] : CoordinateVector 1) = ![1, 1] := by decide

/-- The shear embedding is injective. -/
theorem shear2_injective : Function.Injective shear2 := by
  intro u v huv
  funext i
  fin_cases i
  · exact congrFun huv 2
  · exact congrFun huv 1

/-- The diagonal embedding is injective. -/
theorem diagonal1_injective : Function.Injective diagonal1 := by
  intro u v huv
  funext i
  fin_cases i
  exact congrFun huv 0

/-- The shear embedding preserves addition. -/
theorem shear2_add (u v : CoordinateVector 2) :
    shear2 (u + v) = shear2 u + shear2 v := by
  funext i
  fin_cases i <;> simp [shear2]
  all_goals ring

/-- The diagonal embedding preserves addition. -/
theorem diagonal1_add (u v : CoordinateVector 1) :
    diagonal1 (u + v) = diagonal1 u + diagonal1 v := by
  funext i
  fin_cases i <;> simp [diagonal1]

/-- The shear embedding preserves subtraction. -/
theorem shear2_sub (u v : CoordinateVector 2) :
    shear2 (u - v) = shear2 u - shear2 v := by
  funext i
  fin_cases i <;> simp [shear2]
  all_goals ring

/-- The induced map on nonzero two-dimensional vectors. -/
def mapNonzero2 (u : NonzeroVector 2) : NonzeroVector 3 :=
  ⟨shear2 u.1, fun h => u.2 (shear2_injective (h.trans (by
    funext i
    fin_cases i <;> simp [shear2])))⟩

/-- The induced map on nonzero one-dimensional vectors. -/
def mapNonzero1 (u : NonzeroVector 1) : NonzeroVector 2 :=
  ⟨diagonal1 u.1, fun h => u.2 (diagonal1_injective (h.trans (by
    funext i
    fin_cases i <;> simp [diagonal1])))⟩

example : (mapNonzero2 e1).1 = ![1, 0, 1] := by
  funext i
  fin_cases i <;> decide
example : (mapNonzero1 w).1 = ![1, 1] := by
  funext i
  fin_cases i <;> decide

/-- The induced map on carrier triples. -/
def mapTerm (t : Term) : Carrier profile332 :=
  (mapNonzero2 t.1, mapNonzero2 t.2.1, mapNonzero1 t.2.2)

example : (mapTerm E11).1.1 = ![1, 0, 1] := by
  funext i
  fin_cases i <;> decide

/-- Factorwise injectivity makes the carrier map injective. -/
theorem mapTerm_injective : Function.Injective mapTerm := by
  intro s t h
  apply Prod.ext
  · apply Subtype.ext
    exact shear2_injective (congrArg (fun z => z.1.1) h)
  · apply Prod.ext
    · apply Subtype.ext
      exact shear2_injective (congrArg (fun z => z.2.1.1) h)
    · apply Subtype.ext
      exact diagonal1_injective (congrArg (fun z => z.2.2.1) h)

/-- Finite-set states are mapped by carrier image. -/
def mapState (D : State221) : State profile332 := D.image mapTerm

example : mapState (∅ : State221) = ∅ := rfl

/-- State transport preserves exact finite-set cardinality. -/
theorem mapState_card (D : State221) : (mapState D).card = D.card := by
  exact Finset.card_image_of_injective D mapTerm_injective

/-- A profile-polymorphic local form of the generated first-factor Split. -/
def GeneratedFirstSplitAt {p : Profile} (source outputLeft outputRight : Carrier p)
    (D E : State p) : Prop :=
  source ∈ D ∧ outputLeft ≠ outputRight ∧ outputLeft ∉ D.erase source ∧
  outputRight ∉ D.erase source ∧
  source.1.1 = outputLeft.1.1 + outputRight.1.1 ∧
  outputLeft.2.1.1 = source.2.1.1 ∧ outputRight.2.1.1 = source.2.1.1 ∧
  outputLeft.2.2.1 = source.2.2.1 ∧ outputRight.2.2.1 = source.2.2.1 ∧
  E = insert outputLeft (insert outputRight (D.erase source))

/-- A profile-polymorphic local form of the source third-factor Flip. -/
def SourceThirdFlipAt {p : Profile}
    (sourceLeft sourceRight targetLeft targetRight : Carrier p)
    (D E : State p) : Prop :=
  sourceLeft ∈ D ∧ sourceRight ∈ D ∧ sourceLeft ≠ sourceRight ∧
  targetLeft ∉ (D.erase sourceLeft).erase sourceRight ∧
  targetRight ∉ (D.erase sourceLeft).erase sourceRight ∧ targetLeft ≠ targetRight ∧
  sourceRight.2.2.1 = sourceLeft.2.2.1 ∧
  targetLeft.1.1 = sourceLeft.1.1 + sourceRight.1.1 ∧
  targetLeft.2.1.1 = sourceLeft.2.1.1 ∧
  targetLeft.2.2.1 = sourceLeft.2.2.1 ∧
  targetRight.1.1 = sourceRight.1.1 ∧
  targetRight.2.1.1 = sourceRight.2.1.1 - sourceLeft.2.1.1 ∧
  targetRight.2.2.1 = sourceLeft.2.2.1 ∧
  E = insert targetLeft (insert targetRight ((D.erase sourceLeft).erase sourceRight))

/-- A profile-polymorphic local form of the directed narrow pair Reduction. -/
def DirectedNarrowPairReductionAt {p : Profile}
    (sourceLeft sourceRight target : Carrier p) (D E : State p) : Prop :=
  sourceLeft ∈ D ∧ sourceRight ∈ D ∧ sourceLeft ≠ sourceRight ∧
  target ∉ (D.erase sourceLeft).erase sourceRight ∧
  sourceRight.2.1.1 = sourceLeft.2.1.1 ∧
  sourceRight.2.2.1 = sourceLeft.2.2.1 ∧
  target.1.1 = sourceLeft.1.1 + sourceRight.1.1 ∧
  target.2.1.1 = sourceLeft.2.1.1 ∧ target.2.2.1 = sourceLeft.2.2.1 ∧
  E = insert target ((D.erase sourceLeft).erase sourceRight)

example : GeneratedFirstSplit E11 E21 E31 S0 S1 := forwardSplit
example : SourceThirdFlip E22 E31 E12 J S1 S2 := forwardFlip
example : DirectedNarrowPairReduction E21 E31 E11 S1 S0 := reverseReduction

private theorem mapState_mem {t : Term} {D : State221} :
    mapTerm t ∈ mapState D ↔ t ∈ D := by
  constructor
  · intro h
    obtain ⟨s, hs, hst⟩ := Finset.mem_image.mp h
    have heq : s = t := mapTerm_injective hst
    simpa only [heq] using hs
  · exact fun h => Finset.mem_image.mpr ⟨t, h, rfl⟩

private theorem mapState_erase (D : State221) (t : Term) :
    mapState (D.erase t) = (mapState D).erase (mapTerm t) := by
  exact Finset.image_erase mapTerm_injective D t

private theorem mapState_insert (D : State221) (t : Term) :
    mapState (insert t D) = insert (mapTerm t) (mapState D) := by
  exact Finset.image_insert mapTerm t D

private theorem transportGeneratedFirstSplit
    {source outputLeft outputRight : Term} {D E : State221}
    (h : GeneratedFirstSplit source outputLeft outputRight D E) :
    GeneratedFirstSplitAt (mapTerm source) (mapTerm outputLeft) (mapTerm outputRight)
      (mapState D) (mapState E) := by
  rcases h with ⟨hmem, hne, hfreshLeft, hfreshRight, hfirst, hleftSecond,
    hrightSecond, hleftThird, hrightThird, htarget⟩
  refine ⟨mapState_mem.mpr hmem, fun heq => hne (mapTerm_injective heq), ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← mapState_erase]
    exact fun hm => hfreshLeft (mapState_mem.mp hm)
  · rw [← mapState_erase]
    exact fun hm => hfreshRight (mapState_mem.mp hm)
  · exact congrArg shear2 hfirst |>.trans (shear2_add _ _)
  · exact congrArg shear2 hleftSecond
  · exact congrArg shear2 hrightSecond
  · exact congrArg diagonal1 hleftThird
  · exact congrArg diagonal1 hrightThird
  · rw [htarget, mapState_insert, mapState_insert, mapState_erase]

private theorem transportSourceThirdFlip
    {sourceLeft sourceRight targetLeft targetRight : Term} {D E : State221}
    (h : SourceThirdFlip sourceLeft sourceRight targetLeft targetRight D E) :
    SourceThirdFlipAt (mapTerm sourceLeft) (mapTerm sourceRight)
      (mapTerm targetLeft) (mapTerm targetRight) (mapState D) (mapState E) := by
  rcases h with ⟨hl, hr, hs, hfl, hfr, ht, hthird, hlf, hls, hlt,
    hrf, hrs, hrt, htarget⟩
  refine ⟨mapState_mem.mpr hl, mapState_mem.mpr hr,
    fun heq => hs (mapTerm_injective heq), ?_, ?_,
    fun heq => ht (mapTerm_injective heq), congrArg diagonal1 hthird,
    ?_, congrArg shear2 hls, congrArg diagonal1 hlt, congrArg shear2 hrf,
    ?_, congrArg diagonal1 hrt, ?_⟩
  · rw [← mapState_erase, ← mapState_erase]
    exact fun hm => hfl (mapState_mem.mp hm)
  · rw [← mapState_erase, ← mapState_erase]
    exact fun hm => hfr (mapState_mem.mp hm)
  · exact congrArg shear2 hlf |>.trans (shear2_add _ _)
  · exact congrArg shear2 hrs |>.trans (shear2_sub _ _)
  · rw [htarget, mapState_insert, mapState_insert, mapState_erase, mapState_erase]

private theorem transportDirectedNarrowPairReduction
    {sourceLeft sourceRight target : Term} {D E : State221}
    (h : DirectedNarrowPairReduction sourceLeft sourceRight target D E) :
    DirectedNarrowPairReductionAt (mapTerm sourceLeft) (mapTerm sourceRight)
      (mapTerm target) (mapState D) (mapState E) := by
  rcases h with ⟨hl, hr, hs, hfresh, hsecond, hthird, hfirst,
    htargetSecond, htargetThird, htarget⟩
  refine ⟨mapState_mem.mpr hl, mapState_mem.mpr hr,
    fun heq => hs (mapTerm_injective heq), ?_, congrArg shear2 hsecond,
    congrArg diagonal1 hthird, ?_, congrArg shear2 htargetSecond,
    congrArg diagonal1 htargetThird, ?_⟩
  · rw [← mapState_erase, ← mapState_erase]
    exact fun hm => hfresh (mapState_mem.mp hm)
  · exact congrArg shear2 hfirst |>.trans (shear2_add _ _)
  · rw [htarget, mapState_insert, mapState_erase, mapState_erase]

/-- The mapped concrete generated Split satisfies formula and collision legality. -/
theorem transportedForwardSplit :
    GeneratedFirstSplitAt (mapTerm E11) (mapTerm E21) (mapTerm E31)
      (mapState S0) (mapState S1) := by
  exact transportGeneratedFirstSplit forwardSplit

/-- The mapped concrete forward Flip satisfies formula and collision legality. -/
theorem transportedForwardFlip :
    SourceThirdFlipAt (mapTerm E22) (mapTerm E31) (mapTerm E12) (mapTerm J)
      (mapState S1) (mapState S2) := by
  exact transportSourceThirdFlip forwardFlip

/-- The mapped reverse Flip preserves its source label and direction. -/
theorem transportedReverseFlip :
    SourceThirdFlipAt (mapTerm E12) (mapTerm J) (mapTerm E22) (mapTerm E31)
      (mapState S2) (mapState S1) := by
  exact transportSourceThirdFlip reverseFlip

/-- The mapped directed Reduction satisfies formula and collision legality. -/
theorem transportedReverseReduction :
    DirectedNarrowPairReductionAt (mapTerm E21) (mapTerm E31) (mapTerm E11)
      (mapState S1) (mapState S0) := by
  exact transportDirectedNarrowPairReduction reverseReduction

/-- The three labels of the mapped replay, with Reduction intrinsically directed. -/
inductive TransportMove : State profile332 → State profile332 → Prop
  | generatedFirstSplit {source outputLeft outputRight D E} :
      GeneratedFirstSplitAt source outputLeft outputRight D E → TransportMove D E
  | sourceThirdFlip {sourceLeft sourceRight targetLeft targetRight D E} :
      SourceThirdFlipAt sourceLeft sourceRight targetLeft targetRight D E → TransportMove D E
  | directedNarrowPairReduction {sourceLeft sourceRight target D E} :
      DirectedNarrowPairReductionAt sourceLeft sourceRight target D E → TransportMove D E

/-- The mapped forward path has the same labeled edge sequence. -/
def transportedForwardPath : MovePath TransportMove (mapState S0) (mapState S2) :=
  .snoc (.snoc (.singleton (mapState S0))
    (.generatedFirstSplit transportedForwardSplit))
    (.sourceThirdFlip transportedForwardFlip)

/-- The mapped reverse path uses a Flip followed by directed Reduction. -/
def transportedReversePath : MovePath TransportMove (mapState S2) (mapState S0) :=
  .snoc (.snoc (.singleton (mapState S2))
    (.sourceThirdFlip transportedReverseFlip))
    (.directedNarrowPairReduction transportedReverseReduction)

example : transportedForwardPath.length = 2 := by
  simp [transportedForwardPath, MovePath.length]
example : transportedReversePath.length = 2 := by
  simp [transportedReversePath, MovePath.length]

/-- Mapping preserves the exact vertex cardinalities `2,3,3`. -/
theorem transported_state_cardinalities :
    (mapState S0).card = 2 ∧ (mapState S1).card = 3 ∧ (mapState S2).card = 3 := by
  simpa only [mapState_card] using state_cardinalities

/-- Both explicitly transported paths retain exact altitude three. -/
theorem transported_path_metrics :
    transportedForwardPath.length = 2 ∧ transportedReversePath.length = 2 ∧
      transportedForwardPath.altitude = 3 ∧ transportedReversePath.altitude = 3 := by
  rcases transported_state_cardinalities with ⟨h0, h1, h2⟩
  simp only [transportedForwardPath, transportedReversePath, MovePath.length,
    MovePath.altitude]
  rw [h0, h1, h2]
  decide

#check @mapTerm_injective
#check @mapState_card
#check @transportedForwardFlip
#check @transported_path_metrics
#print axioms mapTerm_injective
#print axioms mapState_card
#print axioms transportedForwardFlip
#print axioms transported_path_metrics

end BilinearComplexity.NormalizedBinaryTransport221Spike
