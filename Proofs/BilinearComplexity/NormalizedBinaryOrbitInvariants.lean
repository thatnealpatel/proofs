import BilinearComplexity.NormalizedBinaryCoverageCompiler

set_option autoImplicit false

/-!
# Semantic pair-agreement invariants for normalized binary relations

This module defines two coordinate-free finite-set counts.  A pair of distinct
normalized terms is adjacent when at least two corresponding factor vectors
are equal.  The first count uses ordered pairs internal to the right endpoint;
the second uses ordered pairs from the left endpoint to the right endpoint.
Both counts are preserved by arbitrary injective factor maps and by all six
permutations of the tensor modes.
-/

namespace BilinearComplexity.NormalizedBinaryOrbitInvariants

open NormalizedBinaryCarrier
open NormalizedBinaryCoverage
open NormalizedBinaryCoverageData
open NormalizedBinaryFiniteAction
open NormalizedBinaryModePermutation
open NormalizedBinaryMoveTransport
open NormalizedBinaryProfileOrientation
open Scheme.Action

/-- Two distinct normalized terms are pair-adjacent when they agree in at
least two of their three factor coordinates. -/
def PairAdjacent {p : Profile} (x y : Carrier p) : Prop :=
  x ≠ y ∧
    ((x.1 = y.1 ∧ x.2.1 = y.2.1) ∨
      (x.1 = y.1 ∧ x.2.2 = y.2.2) ∨
      (x.2.1 = y.2.1 ∧ x.2.2 = y.2.2))

example {p : Profile} (x : Carrier p) : ¬ PairAdjacent x x := by
  simp [PairAdjacent]

/-- Pair adjacency is decidable from equality of the three finite factor
vectors. -/
instance pairAdjacentDecidable {p : Profile} (x y : Carrier p) :
    Decidable (PairAdjacent x y) := by
  unfold PairAdjacent
  infer_instance

/-- Count ordered adjacent pairs whose first entry lies in `A` and whose
second entry lies in `B`.  The adjacency predicate itself excludes diagonal
pairs, so this one definition supplies both orbit statistics. -/
def crossCount {p : Profile} (A B : State p) : ℕ :=
  ((A ×ˢ B).filter fun xy : Carrier p × Carrier p =>
    PairAdjacent xy.1 xy.2).card

example {p : Profile} : crossCount (∅ : State p) ∅ = 0 := rfl

/-- The two semantic orbit statistics: the internal-right ordered count `X'`
and the left-to-right ordered cross count `Y`. -/
def relationInvariant {p : Profile} (R : RelationEndpoints p) : ℕ × ℕ :=
  (crossCount R.right R.right, crossCount R.left R.right)

example {p : Profile} :
    relationInvariant (⟨∅, ∅⟩ : RelationEndpoints p) = (0, 0) := rfl

/-- Pair adjacency is preserved and reflected by arbitrary injective maps in
the three corresponding factor spaces. -/
theorem pairAdjacent_mapTerm_iff {p q : Profile}
    (f : FactorwiseAdditiveInjection p q) (x y : Carrier p) :
    PairAdjacent (mapTerm f x) (mapTerm f y) ↔ PairAdjacent x y := by
  constructor
  · rintro ⟨hxy, h12 | h13 | h23⟩
    · refine ⟨fun h => hxy (congrArg (mapTerm f) h), Or.inl ⟨?_, ?_⟩⟩
      · exact Subtype.ext (f.first_injective (congrArg Subtype.val h12.1))
      · exact Subtype.ext (f.second_injective (congrArg Subtype.val h12.2))
    · refine ⟨fun h => hxy (congrArg (mapTerm f) h), Or.inr (Or.inl ⟨?_, ?_⟩)⟩
      · exact Subtype.ext (f.first_injective (congrArg Subtype.val h13.1))
      · exact Subtype.ext (f.third_injective (congrArg Subtype.val h13.2))
    · refine ⟨fun h => hxy (congrArg (mapTerm f) h), Or.inr (Or.inr ⟨?_, ?_⟩)⟩
      · exact Subtype.ext (f.second_injective (congrArg Subtype.val h23.1))
      · exact Subtype.ext (f.third_injective (congrArg Subtype.val h23.2))
  · rintro ⟨hxy, h12 | h13 | h23⟩
    · exact ⟨fun h => hxy (mapTerm_injective f h), Or.inl
        ⟨congrArg (mapNonzeroVector f.first f.first_injective) h12.1,
          congrArg (mapNonzeroVector f.second f.second_injective) h12.2⟩⟩
    · exact ⟨fun h => hxy (mapTerm_injective f h), Or.inr (Or.inl
        ⟨congrArg (mapNonzeroVector f.first f.first_injective) h13.1,
          congrArg (mapNonzeroVector f.third f.third_injective) h13.2⟩)⟩
    · exact ⟨fun h => hxy (mapTerm_injective f h), Or.inr (Or.inr
        ⟨congrArg (mapNonzeroVector f.second f.second_injective) h23.1,
          congrArg (mapNonzeroVector f.third f.third_injective) h23.2⟩)⟩

/-- The generic ordered adjacent-pair count is invariant under arbitrary
factorwise injections. -/
theorem crossCount_mapState {p q : Profile}
    (f : FactorwiseAdditiveInjection p q) (A B : State p) :
    crossCount (mapState f A) (mapState f B) = crossCount A B := by
  classical
  unfold crossCount
  apply Eq.symm
  apply Finset.card_bij
    (fun (xy : Carrier p × Carrier p) _ =>
      (mapTerm f xy.1, mapTerm f xy.2))
  · intro xy hxy
    rw [Finset.mem_filter] at hxy ⊢
    exact ⟨Finset.mem_product.mpr
      ⟨(mapState_mem f).mpr (Finset.mem_product.mp hxy.1).1,
        (mapState_mem f).mpr (Finset.mem_product.mp hxy.1).2⟩,
      (pairAdjacent_mapTerm_iff f xy.1 xy.2).mpr hxy.2⟩
  · intro x hx y hy hmap
    apply Prod.ext
    · exact mapTerm_injective f (congrArg Prod.fst hmap)
    · exact mapTerm_injective f (congrArg Prod.snd hmap)
  · intro xy hxy
    rw [Finset.mem_filter] at hxy
    obtain ⟨x, hxA, hxx⟩ := Finset.mem_image.mp
      (Finset.mem_product.mp hxy.1).1
    obtain ⟨y, hyB, hyy⟩ := Finset.mem_image.mp
      (Finset.mem_product.mp hxy.1).2
    have hmap : (mapTerm f x, mapTerm f y) = xy := Prod.ext hxx hyy
    have hadj : PairAdjacent x y := by
      apply (pairAdjacent_mapTerm_iff f x y).mp
      rw [hxx, hyy]
      exact hxy.2
    exact ⟨(x, y), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hxA, hyB⟩, hadj⟩, hmap⟩

/-- The pair of relation invariants is unchanged by arbitrary factorwise
injections applied to both ordered endpoint states. -/
theorem relationInvariant_map {p q : Profile}
    (f : FactorwiseAdditiveInjection p q) (R : RelationEndpoints p) :
    relationInvariant
      (⟨mapState f R.left, mapState f R.right⟩ : RelationEndpoints q) =
      relationInvariant R := by
  simp only [relationInvariant, crossCount_mapState]

/-- Pair adjacency is preserved and reflected by every permutation of the
three tensor modes. -/
theorem pairAdjacent_permuteTerm_iff {p : Profile} (o : Orientation)
    (x y : Carrier p) :
    PairAdjacent (permuteTerm o x) (permuteTerm o y) ↔ PairAdjacent x y := by
  constructor
  · rintro ⟨hne, hagree⟩
    refine ⟨fun hxy => hne (congrArg (permuteTerm o) hxy), ?_⟩
    cases o <;> simp only [permuteTerm] at hagree ⊢ <;> tauto
  · rintro ⟨hne, hagree⟩
    refine ⟨fun hxy => hne (permuteTerm_injective o hxy), ?_⟩
    cases o <;> simp only [permuteTerm] at hagree ⊢ <;> tauto

/-- The generic ordered adjacent-pair count is invariant under every tensor
mode permutation. -/
theorem crossCount_permuteState {p : Profile} (o : Orientation)
    (A B : State p) :
    crossCount (permuteState o A) (permuteState o B) = crossCount A B := by
  classical
  unfold crossCount
  apply Eq.symm
  apply Finset.card_bij
    (fun (xy : Carrier p × Carrier p) _ =>
      (permuteTerm o xy.1, permuteTerm o xy.2))
  · intro xy hxy
    rw [Finset.mem_filter] at hxy ⊢
    exact ⟨Finset.mem_product.mpr
      ⟨(permuteState_mem o).mpr (Finset.mem_product.mp hxy.1).1,
        (permuteState_mem o).mpr (Finset.mem_product.mp hxy.1).2⟩,
      (pairAdjacent_permuteTerm_iff o xy.1 xy.2).mpr hxy.2⟩
  · intro x hx y hy hmap
    apply Prod.ext
    · exact permuteTerm_injective o (congrArg Prod.fst hmap)
    · exact permuteTerm_injective o (congrArg Prod.snd hmap)
  · intro xy hxy
    rw [Finset.mem_filter] at hxy
    obtain ⟨x, hxA, hxx⟩ := Finset.mem_image.mp
      (Finset.mem_product.mp hxy.1).1
    obtain ⟨y, hyB, hyy⟩ := Finset.mem_image.mp
      (Finset.mem_product.mp hxy.1).2
    have hmap : (permuteTerm o x, permuteTerm o y) = xy := Prod.ext hxx hyy
    have hadj : PairAdjacent x y := by
      apply (pairAdjacent_permuteTerm_iff o x y).mp
      rw [hxx, hyy]
      exact hxy.2
    exact ⟨(x, y), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hxA, hyB⟩, hadj⟩, hmap⟩

/-- The relation invariant is unchanged by simultaneously permuting all three
factor modes of both ordered endpoints. -/
theorem relationInvariant_permute {p : Profile} (o : Orientation)
    (R : RelationEndpoints p) :
    relationInvariant
      (⟨permuteState o R.left, permuteState o R.right⟩ :
        RelationEndpoints (permProfile o p)) = relationInvariant R := by
  simp only [relationInvariant, crossCount_permuteState]

/-- Casting a relation along an equality of profiles does not change either
finite pair count. -/
theorem relationInvariant_cast {p q : Profile} (h : p = q)
    (R : RelationEndpoints p) :
    relationInvariant
      (⟨cast (congrArg State h) R.left, cast (congrArg State h) R.right⟩ :
        RelationEndpoints q) = relationInvariant R := by
  subst q
  rfl

/-- Orienting a relation through any `ProfileOrientation` leaves both pair
counts unchanged. -/
theorem relationInvariant_orient {p : Profile} (choice : ProfileOrientation p)
    (R : RelationEndpoints p) :
    relationInvariant
      (⟨choice.orientState R.left, choice.orientState R.right⟩ :
        RelationEndpoints choice.family.profile) = relationInvariant R := by
  change relationInvariant
    (⟨cast (congrArg State choice.profile_eq)
        (permuteState choice.orientation R.left),
      cast (congrArg State choice.profile_eq)
        (permuteState choice.orientation R.right)⟩ :
      RelationEndpoints choice.family.profile) = relationInvariant R
  calc
    _ = relationInvariant
        (⟨permuteState choice.orientation R.left,
          permuteState choice.orientation R.right⟩ :
          RelationEndpoints (permProfile choice.orientation p)) :=
      relationInvariant_cast choice.profile_eq _
    _ = relationInvariant R := relationInvariant_permute choice.orientation R

set_option maxHeartbeats 1000000 in
/-- Every checked profile action preserves the two pair counts. -/
theorem relationInvariant_profileAction {p : Profile} (action : ProfileAction p)
    (R : RelationEndpoints p) :
    relationInvariant (action.actEndpoints R) = relationInvariant R := by
  let mapped : RelationEndpoints p :=
    ⟨mapState action.factorwiseInjection R.left,
      mapState action.factorwiseInjection R.right⟩
  let permuted : RelationEndpoints (permProfile action.orientation p) :=
    ⟨permuteState action.orientation mapped.left,
      permuteState action.orientation mapped.right⟩
  let recast : RelationEndpoints p :=
    ⟨cast (congrArg State action.profile_eq) permuted.left,
      cast (congrArg State action.profile_eq) permuted.right⟩
  have haction : action.actEndpoints R = recast := by
    rfl
  have hrecast : relationInvariant recast = relationInvariant permuted := by
    exact relationInvariant_cast action.profile_eq permuted
  have hpermuted : relationInvariant permuted = relationInvariant mapped := by
    exact relationInvariant_permute action.orientation mapped
  have hmapped : relationInvariant mapped = relationInvariant R := by
    exact relationInvariant_map action.factorwiseInjection R
  rw [haction]
  exact hrecast.trans (hpermuted.trans hmapped)

/-- An arbitrary checked action witness forces its source and target relations
to have identical pair-count invariants. -/
theorem relationInvariant_actionWitness {p : Profile}
    {source target : RelationEndpoints p} (witness : ActionWitness source target) :
    relationInvariant source = relationInvariant target := by
  rw [← witness.maps_endpoints, relationInvariant_profileAction]

/-- Compute the invariant pair of every selected replay row in one canonical
profile family. -/
def actualRows : (family : CanonicalProfileFamily) → List (ℕ × ℕ)
  | .family221 => List.ofFn fun i : Fin 3 =>
      relationInvariant (familyRowSources .family221 i).endpoints
  | .family411 => List.ofFn fun i : Fin 1 =>
      relationInvariant (familyRowSources .family411 i).endpoints
  | .family321 => List.ofFn fun i : Fin 6 =>
      relationInvariant (familyRowSources .family321 i).endpoints
  | .family222 => List.ofFn fun i : Fin 3 =>
      relationInvariant (familyRowSources .family222 i).endpoints

example : actualRows .family221 = [(0, 4), (2, 2), (4, 2)] := by decide

/-- Kernel evaluation of the selected-row sources gives the reviewed thirteen
`(X',Y)` pairs, without assuming serialized invariant literals. -/
theorem actualRows_eq :
    actualRows .family221 = [(0, 4), (2, 2), (4, 2)] ∧
      actualRows .family411 = [(6, 6)] ∧
      actualRows .family321 =
        [(6, 0), (2, 2), (2, 0), (2, 3), (2, 1), (0, 2)] ∧
      actualRows .family222 = [(2, 0), (2, 1), (0, 2)] := by
  decide

/-- Within each canonical family, the selected replay-row index is determined
by its semantic pair-count invariant. -/
theorem selectedRowInvariant_injective (family : CanonicalProfileFamily) :
    Function.Injective fun i : FamilyRowIndex family =>
      relationInvariant (familyRowSources family i).endpoints := by
  cases family with
  | family221 =>
      change Function.Injective fun i : Fin 3 =>
        relationInvariant (familyRowSources .family221 i).endpoints
      intro i j hij
      fin_cases i <;> fin_cases j
      all_goals first | rfl | (exfalso; revert hij; decide)
  | family411 =>
      change Function.Injective fun i : Fin 1 =>
        relationInvariant (familyRowSources .family411 i).endpoints
      intro i j hij
      fin_cases i
      fin_cases j
      rfl
  | family321 =>
      change Function.Injective fun i : Fin 6 =>
        relationInvariant (familyRowSources .family321 i).endpoints
      intro i j hij
      fin_cases i <;> fin_cases j
      all_goals first | rfl | (exfalso; revert hij; decide)
  | family222 =>
      change Function.Injective fun i : Fin 3 =>
        relationInvariant (familyRowSources .family222 i).endpoints
      intro i j hij
      fin_cases i <;> fin_cases j
      all_goals first | rfl | (exfalso; revert hij; decide)

#check @PairAdjacent
#check @crossCount
#check @relationInvariant
#check @pairAdjacent_mapTerm_iff
#check @crossCount_mapState
#check @relationInvariant_map
#check @pairAdjacent_permuteTerm_iff
#check @crossCount_permuteState
#check @relationInvariant_profileAction
#check @relationInvariant_actionWitness
#check @actualRows_eq
#check @selectedRowInvariant_injective

#print axioms crossCount_mapState
#print axioms crossCount_permuteState
#print axioms relationInvariant_profileAction
#print axioms actualRows_eq
#print axioms selectedRowInvariant_injective

end BilinearComplexity.NormalizedBinaryOrbitInvariants
