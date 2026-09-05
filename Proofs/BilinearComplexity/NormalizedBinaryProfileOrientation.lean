import BilinearComplexity.ProfileInequality
import BilinearComplexity.NormalizedBinaryModePermutation
import BilinearComplexity.NormalizedBinaryFiveCircuitCertificate

set_option autoImplicit false

/-!
# Explicit orientation of normalized binary factor profiles

This module turns the unordered `List.Perm` conclusion of the production
five-circuit profile classification into concrete Type-valued data: one of the
four supported profile families and one of the six tensor-mode orientations.
For an arbitrary disjoint normalized `2|3` pair with equal evaluation and
exact factor spans, it explicitly enumerates the five terms by `Fin 5`, bridges
projected endpoint spans to the ranges of the three coordinate families, and
applies `pair_triple_profile_classification`.

The selected orientation preserves the ordered endpoint slots: it permutes
factor modes but never exchanges the two-term and three-term sides. Repeated
dimensions can admit several valid orientations; the table here makes a
deterministic choice and does not assert uniqueness.

AI disclosure: produced with AI assistance (see `README`).
-/

namespace BilinearComplexity.NormalizedBinaryProfileOrientation

open NormalizedBinaryCarrier
open NormalizedBinaryModePermutation
open NormalizedBinaryFiveCircuitCertificate
open Scheme.Action
open scoped BigOperators

/-- The four unordered exact factor-profile families supported by the binary
five-circuit profile classification. -/
inductive CanonicalProfileFamily : Type where
  /-- The profile family with dimensions `2,2,1`. -/
  | family221
  /-- The profile family with dimensions `4,1,1`. -/
  | family411
  /-- The profile family with dimensions `3,2,1`. -/
  | family321
  /-- The profile family with dimensions `2,2,2`. -/
  | family222
  deriving DecidableEq

/-- The fixed ordered representative profile attached to a supported family. -/
@[simp] def CanonicalProfileFamily.profile : CanonicalProfileFamily → Profile
  | .family221 => profile221
  | .family411 => profile411
  | .family321 => profile321
  | .family222 => profile222

example : CanonicalProfileFamily.family221.profile = profile221 ∧
    CanonicalProfileFamily.family411.profile = profile411 ∧
    CanonicalProfileFamily.family321.profile = profile321 ∧
    CanonicalProfileFamily.family222.profile = profile222 := by
  decide

/-- A concrete tensor-mode orientation from an ordered profile to the fixed
representative of one supported profile family. -/
structure ProfileOrientation (p : Profile) : Type where
  /-- The selected supported profile family. -/
  family : CanonicalProfileFamily
  /-- The selected permutation of the three tensor modes. -/
  orientation : Orientation
  /-- Applying the selected mode permutation produces the representative profile. -/
  profile_eq : permProfile orientation p = family.profile

/-- Deterministically select a supported family and orientation from each
supported ordered profile. The final branch is an explicit fallback outside
the supported profiles; `profileOrientation_of_perm` proves that no classified
profile uses it incorrectly. -/
def selectedFamilyOrientation : Profile → CanonicalProfileFamily × Orientation
  | ⟨2, 2, 1⟩ => (.family221, .abc)
  | ⟨2, 1, 2⟩ => (.family221, .acb)
  | ⟨1, 2, 2⟩ => (.family221, .bca)
  | ⟨4, 1, 1⟩ => (.family411, .abc)
  | ⟨1, 4, 1⟩ => (.family411, .bac)
  | ⟨1, 1, 4⟩ => (.family411, .cab)
  | ⟨3, 2, 1⟩ => (.family321, .abc)
  | ⟨3, 1, 2⟩ => (.family321, .acb)
  | ⟨2, 3, 1⟩ => (.family321, .bac)
  | ⟨2, 1, 3⟩ => (.family321, .cab)
  | ⟨1, 3, 2⟩ => (.family321, .bca)
  | ⟨1, 2, 3⟩ => (.family321, .cba)
  | ⟨2, 2, 2⟩ => (.family222, .abc)
  | _ => (.family222, .abc)

example : selectedFamilyOrientation ⟨1, 3, 2⟩ =
    (.family321, .bca) := rfl

example : selectedFamilyOrientation ⟨0, 0, 0⟩ =
    (.family222, .abc) := rfl

/-- Convert an unordered supported-profile classification into a concrete
family and orientation. The returned data is computed from `p`; the
`List.Perm` hypothesis proves that the selected table row is valid. -/
def profileOrientation_of_perm (p : Profile)
    (h : [p.first, p.second, p.third].Perm [2, 2, 1] ∨
      [p.first, p.second, p.third].Perm [3, 2, 1] ∨
      [p.first, p.second, p.third].Perm [2, 2, 2] ∨
      [p.first, p.second, p.third].Perm [4, 1, 1]) :
    ProfileOrientation p := by
  refine {
    family := (selectedFamilyOrientation p).1
    orientation := (selectedFamilyOrientation p).2
    profile_eq := ?_
  }
  rcases p with ⟨a, b, c⟩
  rcases h with h221 | h321 | h222 | h411
  · have hsum : a + (b + c) = 5 := by
      simpa using List.Perm.sum_eq h221
    have ha : a = 2 ∨ a = 1 := by
      have hm : a ∈ [2, 2, 1] :=
        (List.Perm.mem_iff h221).mp (by simp)
      simpa using hm
    have hb : b = 2 ∨ b = 1 := by
      have hm : b ∈ [2, 2, 1] :=
        (List.Perm.mem_iff h221).mp (by simp)
      simpa using hm
    have hc : c = 2 ∨ c = 1 := by
      have hm : c ∈ [2, 2, 1] :=
        (List.Perm.mem_iff h221).mp (by simp)
      simpa using hm
    rcases ha with ha | ha <;> rcases hb with hb | hb <;>
      rcases hc with hc | hc
    all_goals first | omega | (subst_vars; rfl)
  · have hsum : a + (b + c) = 6 := by
      simpa using List.Perm.sum_eq h321
    have ha : a = 3 ∨ a = 2 ∨ a = 1 := by
      have hm : a ∈ [3, 2, 1] :=
        (List.Perm.mem_iff h321).mp (by simp)
      simpa using hm
    have hb : b = 3 ∨ b = 2 ∨ b = 1 := by
      have hm : b ∈ [3, 2, 1] :=
        (List.Perm.mem_iff h321).mp (by simp)
      simpa using hm
    have hc : c = 3 ∨ c = 2 ∨ c = 1 := by
      have hm : c ∈ [3, 2, 1] :=
        (List.Perm.mem_iff h321).mp (by simp)
      simpa using hm
    rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;>
      rcases hc with hc | hc | hc
    all_goals first | omega | (subst_vars; rfl)
  · have ha : a = 2 := by
      have hm : a ∈ [2, 2, 2] :=
        (List.Perm.mem_iff h222).mp (by simp)
      simpa using hm
    have hb : b = 2 := by
      have hm : b ∈ [2, 2, 2] :=
        (List.Perm.mem_iff h222).mp (by simp)
      simpa using hm
    have hc : c = 2 := by
      have hm : c ∈ [2, 2, 2] :=
        (List.Perm.mem_iff h222).mp (by simp)
      simpa using hm
    subst a
    subst b
    subst c
    rfl
  · have hsum : a + (b + c) = 6 := by
      simpa using List.Perm.sum_eq h411
    have ha : a = 4 ∨ a = 1 := by
      have hm : a ∈ [4, 1, 1] :=
        (List.Perm.mem_iff h411).mp (by simp)
      simpa using hm
    have hb : b = 4 ∨ b = 1 := by
      have hm : b ∈ [4, 1, 1] :=
        (List.Perm.mem_iff h411).mp (by simp)
      simpa using hm
    have hc : c = 4 ∨ c = 1 := by
      have hm : c ∈ [4, 1, 1] :=
        (List.Perm.mem_iff h411).mp (by simp)
      simpa using hm
    rcases ha with ha | ha <;> rcases hb with hb | hb <;>
      rcases hc with hc | hc
    all_goals first | omega | (subst_vars; rfl)

example :
    (profileOrientation_of_perm profile221 (Or.inl (by rfl))).family = .family221 ∧
      (profileOrientation_of_perm profile221 (Or.inl (by rfl))).orientation = .abc :=
  ⟨rfl, rfl⟩

/-- A disjoint exact normalized `2|3` relation has one of the four supported
unordered factor profiles. The proof enumerates the left terms first and the
right terms last, so the production pair/triple equality has the required
order. -/
theorem exactPair_profile_perm {p : Profile} (A B : State p)
    (hAcard : A.card = 2) (hBcard : B.card = 3)
    (hdisjoint : Disjoint A B)
    (hevaluation : stateEvaluation A = stateEvaluation B)
    (hexact : HasExactFactorProfile (A ∪ B)) :
    [p.first, p.second, p.third].Perm [2, 2, 1] ∨
      [p.first, p.second, p.third].Perm [3, 2, 1] ∨
      [p.first, p.second, p.third].Perm [2, 2, 2] ∨
      [p.first, p.second, p.third].Perm [4, 1, 1] := by
  classical
  obtain ⟨a0, a1, ha01, hA⟩ := Finset.card_eq_two.mp hAcard
  obtain ⟨b0, b1, b2, hb01, hb02, hb12, hB⟩ :=
    Finset.card_eq_three.mp hBcard
  have ha0A : a0 ∈ A := by simp [hA]
  have ha1A : a1 ∈ A := by simp [hA]
  have hb0B : b0 ∈ B := by simp [hB]
  have hb1B : b1 ∈ B := by simp [hB]
  have hb2B : b2 ∈ B := by simp [hB]
  have hcross : ∀ {x y : Carrier p}, x ∈ A → y ∈ B → x ≠ y := by
    intro x y hx hy hxy
    subst y
    exact (Finset.disjoint_left.mp hdisjoint) hx hy
  have ha0b0 : a0 ≠ b0 := hcross ha0A hb0B
  have ha0b1 : a0 ≠ b1 := hcross ha0A hb1B
  have ha0b2 : a0 ≠ b2 := hcross ha0A hb2B
  have ha1b0 : a1 ≠ b0 := hcross ha1A hb0B
  have ha1b1 : a1 ≠ b1 := hcross ha1A hb1B
  have ha1b2 : a1 ≠ b2 := hcross ha1A hb2B
  let t : Fin 5 → Carrier p := ![a0, a1, b0, b1, b2]
  let U : Fin 5 → CoordinateVector p.first := fun i => (t i).1.1
  let V : Fin 5 → CoordinateVector p.second := fun i => (t i).2.1.1
  let W : Fin 5 → CoordinateVector p.third := fun i => (t i).2.2.1
  have htinj : Function.Injective t := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue,
        Matrix.cons_val_zero, Matrix.cons_val_one, Fin.reduceFinMk,
        Matrix.cons_val, Fin.reduceEq, zero_ne_one, one_ne_zero, t]
        at hij ⊢ <;> aesop
  have hnz : ∀ i, triad (U i) (V i) (W i) ≠ 0 := by
    intro i
    change tensorEvaluation (t i) ≠ 0
    exact tensorEvaluation_ne_zero (t i)
  have hinj : Function.Injective fun i => triad (U i) (V i) (W i) := by
    intro i j hij
    apply htinj
    apply tensorEvaluation_injective
    exact hij
  have heval5 : tensorEvaluation a0 + tensorEvaluation a1 =
      tensorEvaluation b0 + tensorEvaluation b1 + tensorEvaluation b2 := by
    simpa [hA, hB, ha01, hb01, hb02, hb12, add_assoc] using hevaluation
  have hsum : triad (U 0) (V 0) (W 0) + triad (U 1) (V 1) (W 1) =
      triad (U 2) (V 2) (W 2) + triad (U 3) (V 3) (W 3) +
        triad (U 4) (V 4) (W 4) := by
    simpa [tensorEvaluation, U, V, W, t] using heval5
  have hAB : A ∪ B = {a0, a1, b0, b1, b2} := by
    rw [hA, hB]
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hrange_image : ∀ {α : Type} (f : Carrier p → α),
      Set.range (fun i => f (t i)) =
        (↑((A ∪ B).image f) : Set α) := by
    intro α f
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      refine Finset.mem_image.mpr ⟨t i, ?_, rfl⟩
      fin_cases i <;> simp [hAB, t]
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      have hx' : x = a0 ∨ x = a1 ∨ x = b0 ∨ x = b1 ∨ x = b2 := by
        simpa [hAB] using hx
      rcases hx' with rfl | rfl | rfl | rfl | rfl
      · exact ⟨0, by simp [t]⟩
      · exact ⟨1, by simp [t]⟩
      · exact ⟨2, by simp [t]⟩
      · exact ⟨3, by simp [t]⟩
      · exact ⟨4, by simp [t]⟩
  have hUrange : Set.range U =
      (↑((A ∪ B).image (fun x : Carrier p => x.1.1)) :
        Set (CoordinateVector p.first)) := by
    simpa [U] using hrange_image (fun x : Carrier p => x.1.1)
  have hVrange : Set.range V =
      (↑((A ∪ B).image (fun x : Carrier p => x.2.1.1)) :
        Set (CoordinateVector p.second)) := by
    simpa [V] using hrange_image (fun x : Carrier p => x.2.1.1)
  have hWrange : Set.range W =
      (↑((A ∪ B).image (fun x : Carrier p => x.2.2.1)) :
        Set (CoordinateVector p.third)) := by
    simpa [W] using hrange_image (fun x : Carrier p => x.2.2.1)
  have hUtop : Submodule.span F2 (Set.range U) = ⊤ := by
    rw [hUrange]
    exact hexact.1
  have hVtop : Submodule.span F2 (Set.range V) = ⊤ := by
    rw [hVrange]
    exact hexact.2.1
  have hWtop : Submodule.span F2 (Set.range W) = ⊤ := by
    rw [hWrange]
    exact hexact.2.2
  have hrankU : Module.finrank F2 (Submodule.span F2 (Set.range U)) = p.first := by
    rw [hUtop, finrank_top, Module.finrank_fin_fun]
  have hrankV : Module.finrank F2 (Submodule.span F2 (Set.range V)) = p.second := by
    rw [hVtop, finrank_top, Module.finrank_fin_fun]
  have hrankW : Module.finrank F2 (Submodule.span F2 (Set.range W)) = p.third := by
    rw [hWtop, finrank_top, Module.finrank_fin_fun]
  have hclass := pair_triple_profile_classification U V W hnz hinj hsum
  simpa only [hrankU, hrankV, hrankW] using hclass

private theorem hasExactFactorProfile_permuteState {p : Profile}
    (o : Orientation) {D : State p} (hD : HasExactFactorProfile D) :
    HasExactFactorProfile (permuteState o D) := by
  cases o <;>
    simp only [HasExactFactorProfile, firstFactorSpan, secondFactorSpan,
      thirdFactorSpan, permuteState, Finset.image_image] at hD ⊢
  all_goals tauto

/-- Reindex a normalized state through the concrete profile equality after
permuting its three factor modes. -/
def ProfileOrientation.orientState {p : Profile} (choice : ProfileOrientation p)
    (D : State p) : State choice.family.profile :=
  cast (congrArg State choice.profile_eq) (permuteState choice.orientation D)

private theorem state_cast_card {p q : Profile} (h : p = q) (D : State p) :
    (cast (congrArg State h) D).card = D.card := by
  subst q
  rfl

private theorem state_cast_disjoint {p q : Profile} (h : p = q)
    {A B : State p} (hAB : Disjoint A B) :
    Disjoint (cast (congrArg State h) A) (cast (congrArg State h) B) := by
  subst q
  exact hAB

private theorem state_cast_evaluation_eq {p q : Profile} (h : p = q)
    {A B : State p} (hAB : stateEvaluation A = stateEvaluation B) :
    stateEvaluation (cast (congrArg State h) A) =
      stateEvaluation (cast (congrArg State h) B) := by
  subst q
  exact hAB

private theorem state_cast_exact {p q : Profile} (h : p = q)
    {D : State p} (hD : HasExactFactorProfile D) :
    HasExactFactorProfile (cast (congrArg State h) D) := by
  subst q
  exact hD

private theorem state_cast_union {p q : Profile} (h : p = q) (A B : State p) :
    cast (congrArg State h) (A ∪ B) =
      cast (congrArg State h) A ∪ cast (congrArg State h) B := by
  subst q
  rfl

example (choice : ProfileOrientation profile221) :
    (choice.orientState (∅ : State profile221)).card = 0 := by
  exact (state_cast_card choice.profile_eq
    (permuteState choice.orientation (∅ : State profile221))).trans
      (permuteState_card choice.orientation ∅)

/-- Reindexing an oriented state preserves its finite-set cardinality. -/
theorem ProfileOrientation.orientState_card {p : Profile}
    (choice : ProfileOrientation p) (D : State p) :
    (choice.orientState D).card = D.card := by
  exact (state_cast_card choice.profile_eq (permuteState choice.orientation D)).trans
    (permuteState_card choice.orientation D)

/-- Reindexing both oriented endpoints preserves disjointness. -/
theorem ProfileOrientation.orientState_disjoint {p : Profile}
    (choice : ProfileOrientation p) {A B : State p} (hAB : Disjoint A B) :
    Disjoint (choice.orientState A) (choice.orientState B) := by
  apply state_cast_disjoint choice.profile_eq
  exact (Finset.disjoint_image
    (permuteTerm_injective choice.orientation)).mpr hAB

/-- Equal endpoint evaluations remain equal after the selected orientation. -/
theorem ProfileOrientation.orientState_evaluation {p : Profile}
    (choice : ProfileOrientation p) {A B : State p}
    (hAB : stateEvaluation A = stateEvaluation B) :
    stateEvaluation (choice.orientState A) =
      stateEvaluation (choice.orientState B) := by
  apply state_cast_evaluation_eq choice.profile_eq
  rw [stateEvaluation_permuteState, stateEvaluation_permuteState, hAB]

/-- An exact factor profile remains exact after the selected orientation. -/
theorem ProfileOrientation.orientState_exact {p : Profile}
    (choice : ProfileOrientation p) {D : State p}
    (hD : HasExactFactorProfile D) :
    HasExactFactorProfile (choice.orientState D) := by
  apply state_cast_exact choice.profile_eq
  exact hasExactFactorProfile_permuteState choice.orientation hD

/-- Orienting a state commutes with finite-set union. -/
theorem ProfileOrientation.orientState_union {p : Profile}
    (choice : ProfileOrientation p) (A B : State p) :
    choice.orientState (A ∪ B) =
      choice.orientState A ∪ choice.orientState B := by
  rw [ProfileOrientation.orientState, permuteState_union]
  exact state_cast_union choice.profile_eq _ _

/-- The union of two oriented endpoints retains exact factor spans. -/
theorem ProfileOrientation.orientState_union_exact {p : Profile}
    (choice : ProfileOrientation p) {A B : State p}
    (hAB : HasExactFactorProfile (A ∪ B)) :
    HasExactFactorProfile (choice.orientState A ∪ choice.orientState B) := by
  rw [← choice.orientState_union]
  exact choice.orientState_exact hAB

/-- Select explicit supported-family and mode-orientation data for an arbitrary
normalized disjoint exact `2|3` pair with equal evaluation. -/
def exactPairProfileOrientation {p : Profile} (A B : State p)
    (hAcard : A.card = 2) (hBcard : B.card = 3)
    (hdisjoint : Disjoint A B)
    (hevaluation : stateEvaluation A = stateEvaluation B)
    (hexact : HasExactFactorProfile (A ∪ B)) : ProfileOrientation p :=
  profileOrientation_of_perm p
    (exactPair_profile_perm A B hAcard hBcard hdisjoint hevaluation hexact)

example :
    (exactPairProfileOrientation
      NormalizedBinaryReplay221.S0 NormalizedBinaryReplay221.S2
      NormalizedBinaryReplay221.state_cardinalities.1
      NormalizedBinaryReplay221.state_cardinalities.2.2
      NormalizedBinaryReplay221.designated_endpoint_exact_profile_221.1
      NormalizedBinaryReplay221.endpoint_evaluations.2
      designated_endpoint_hasExactFactorProfile).family = .family221 := rfl

/-- An arbitrary normalized exact `2|3` pair together with its concretely
oriented endpoints and all five transported semantic properties. -/
structure OrientedExactPair (p : Profile) (A B : State p) : Type where
  /-- Explicit supported family, orientation, and profile equality. -/
  choice : ProfileOrientation p
  /-- The oriented left endpoint still has two terms. -/
  card_left : (choice.orientState A).card = 2
  /-- The oriented right endpoint still has three terms. -/
  card_right : (choice.orientState B).card = 3
  /-- The oriented endpoint states remain disjoint. -/
  disjoint : Disjoint (choice.orientState A) (choice.orientState B)
  /-- The oriented endpoint evaluations remain equal. -/
  evaluation : stateEvaluation (choice.orientState A) =
    stateEvaluation (choice.orientState B)
  /-- The oriented endpoint union has the exact representative factor profile. -/
  exact_profile : HasExactFactorProfile
    (choice.orientState A ∪ choice.orientState B)

/-- Orient an arbitrary normalized exact `2|3` pair and return its concrete
Type-valued profile data together with transported endpoint semantics. -/
def orientExactPair {p : Profile} (A B : State p)
    (hAcard : A.card = 2) (hBcard : B.card = 3)
    (hdisjoint : Disjoint A B)
    (hevaluation : stateEvaluation A = stateEvaluation B)
    (hexact : HasExactFactorProfile (A ∪ B)) : OrientedExactPair p A B := by
  let choice := exactPairProfileOrientation A B hAcard hBcard hdisjoint
    hevaluation hexact
  exact {
    choice := choice
    card_left := (choice.orientState_card A).trans hAcard
    card_right := (choice.orientState_card B).trans hBcard
    disjoint := choice.orientState_disjoint hdisjoint
    evaluation := choice.orientState_evaluation hevaluation
    exact_profile := choice.orientState_union_exact hexact
  }

example :
    (orientExactPair NormalizedBinaryReplay221.S0 NormalizedBinaryReplay221.S2
      NormalizedBinaryReplay221.state_cardinalities.1
      NormalizedBinaryReplay221.state_cardinalities.2.2
      NormalizedBinaryReplay221.designated_endpoint_exact_profile_221.1
      NormalizedBinaryReplay221.endpoint_evaluations.2
      designated_endpoint_hasExactFactorProfile).choice.family = .family221 := rfl

#check @CanonicalProfileFamily.profile
#check @ProfileOrientation.profile_eq
#check @exactPair_profile_perm
#check @exactPairProfileOrientation
#check @ProfileOrientation.orientState_card
#check @ProfileOrientation.orientState_disjoint
#check @ProfileOrientation.orientState_evaluation
#check @ProfileOrientation.orientState_union_exact
#check @orientExactPair

#print axioms exactPair_profile_perm
#print axioms ProfileOrientation.orientState_union_exact
#print axioms orientExactPair

end BilinearComplexity.NormalizedBinaryProfileOrientation
