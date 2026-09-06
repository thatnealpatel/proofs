import BilinearComplexity.FiniteBoundedSearch

set_option autoImplicit false

/-!
# Exhaustive weighted bounded search

This module augments complete primitive one-step expansion with finite certified
native path blocks.  A block is only a shortcut in enumeration: it stores its
actual native `MovePath`, has strictly positive cost equal to that path's
primitive length, and is concatenated into the candidate's actual path.
Admission checks the resulting path's full primitive length and full altitude,
so every internal block vertex is subject to the same ceiling.

Primitive successors are always retained.  Consequently completeness and the
all-competitor lower bound use only the primitive successor completeness
hypothesis; no coverage property is required of the optional block provider.
No pruning, deduplication, symmetry quotient, or state collapse is performed.

AI disclosure: produced with AI assistance (see `Proofs/README`).
-/

namespace BilinearComplexity.FiniteWeightedBoundedSearch

open BinaryCircuit

universe u

variable {α : Type u}

/-- A certified positive-cost shortcut whose payload is an actual native path. -/
structure CertifiedBlock (R : Scheme α → Scheme α → Prop) (D : Scheme α) where
  /-- The endpoint of the block. -/
  finish : Scheme α
  /-- The complete primitive path represented by the block. -/
  path : MovePath R D finish
  /-- Blocks have positive actual primitive cost. -/
  positive : 0 < path.length

/-- A generated weighted-search candidate, retaining its complete native path. -/
structure Candidate (R : Scheme α → Scheme α → Prop) (D : Scheme α) where
  /-- The candidate endpoint. -/
  finish : Scheme α
  /-- The complete primitive path from the search root. -/
  path : MovePath R D finish

/-- The zero-cost candidate at the search root. -/
def Candidate.root (R : Scheme α → Scheme α → Prop) (D : Scheme α) :
    Candidate R D :=
  ⟨D, .singleton D⟩

/-- Regard a certified primitive successor as a unit-cost certified block. -/
def CertifiedBlock.ofSuccessor {R : Scheme α → Scheme α → Prop}
    {D : Scheme α} (edge : FiniteBoundedSearch.Successor R D) :
    CertifiedBlock R D :=
  ⟨edge.finish, MovePath.one edge.edge, by
    simp only [MovePath.one, MovePath.length]
    omega⟩

/-- Concatenate a candidate with the complete path stored in a certified block. -/
def Candidate.extendBlock {R : Scheme α → Scheme α → Prop}
    {D : Scheme α} (candidate : Candidate R D)
    (block : CertifiedBlock R candidate.finish) : Candidate R D :=
  ⟨block.finish, candidate.path.trans block.path⟩

/-- Native primitive successors followed by all optional certified blocks.
Primitive expansion is never suppressed by block availability. -/
def availableBlocks {R : Scheme α → Scheme α → Prop}
    (successors : (X : Scheme α) → List (FiniteBoundedSearch.Successor R X))
    (blocks : (X : Scheme α) → List (CertifiedBlock R X))
    (D : Scheme α) : List (CertifiedBlock R D) :=
  (successors D).map CertifiedBlock.ofSuccessor ++ blocks D

/-- Extend by every available primitive edge and block whose complete
concatenated path respects both the primitive budget and altitude ceiling. -/
def admissibleExtensions {R : Scheme α → Scheme α → Prop}
    (successors : (X : Scheme α) → List (FiniteBoundedSearch.Successor R X))
    (blocks : (X : Scheme α) → List (CertifiedBlock R X))
    (k H : ℕ) {D : Scheme α} (candidate : Candidate R D) :
    List (Candidate R D) :=
  ((availableBlocks successors blocks candidate.finish).map candidate.extendBlock).filter
    fun next => decide (next.path.length ≤ k ∧ next.path.altitude ≤ H)

/-- Membership in an extension list certifies the complete concatenated path's
actual primitive budget and altitude bounds. -/
theorem admissibleExtensions_sound {R : Scheme α → Scheme α → Prop}
    (successors : (X : Scheme α) → List (FiniteBoundedSearch.Successor R X))
    (blocks : (X : Scheme α) → List (CertifiedBlock R X))
    (k H : ℕ) {D : Scheme α} (candidate next : Candidate R D)
    (hnext : next ∈ admissibleExtensions successors blocks k H candidate) :
    next.path.length ≤ k ∧ next.path.altitude ≤ H := by
  simp only [admissibleExtensions, List.mem_filter, List.mem_map] at hnext
  exact of_decide_eq_true hnext.2

/-- Exhaustive weighted candidate enumeration up to an actual primitive budget.
At every level it retains all earlier candidates and performs all admissible
primitive and block extensions; duplicate paths and endpoints remain present. -/
def boundedCandidates {R : Scheme α → Scheme α → Prop}
    (successors : (X : Scheme α) → List (FiniteBoundedSearch.Successor R X))
    (blocks : (X : Scheme α) → List (CertifiedBlock R X))
    (H : ℕ) (D : Scheme α) : ℕ → List (Candidate R D)
  | 0 => [Candidate.root R D]
  | k + 1 =>
      let prior := boundedCandidates successors blocks H D k
      prior ++ prior.flatMap (admissibleExtensions successors blocks (k + 1) H)

/-- Strictly smaller endpoint cardinality wins; ties retain the left candidate. -/
def prefer {R : Scheme α → Scheme α → Prop} {D : Scheme α}
    (left right : Candidate R D) : Candidate R D :=
  if right.finish.card < left.finish.card then right else left

/-- Deterministically select a minimum-cardinality endpoint from a candidate list. -/
def chooseBest {R : Scheme α → Scheme α → Prop} {D : Scheme α}
    (fallback : Candidate R D) (candidates : List (Candidate R D)) :
    Candidate R D :=
  candidates.foldl prefer fallback

/-- Concatenating paths charges the sum of their actual primitive lengths. -/
theorem MovePath.length_trans {R : Scheme α → Scheme α → Prop}
    {D E F : Scheme α} (first : MovePath R D E) (second : MovePath R E F) :
    (first.trans second).length = first.length + second.length := by
  induction second with
  | singleton => simp only [MovePath.trans, MovePath.length, Nat.add_zero]
  | snoc second edge ih =>
      simp only [MovePath.trans, MovePath.length, ih, Nat.add_assoc]

/-- Block extension charges exactly the block's positive primitive length. -/
theorem Candidate.extendBlock_length {R : Scheme α → Scheme α → Prop}
    {D : Scheme α} (candidate : Candidate R D)
    (block : CertifiedBlock R candidate.finish) :
    (candidate.extendBlock block).path.length =
      candidate.path.length + block.path.length := by
  exact MovePath.length_trans candidate.path block.path

/-- Every block extension strictly increases actual primitive cost. -/
theorem Candidate.length_lt_extendBlock {R : Scheme α → Scheme α → Prop}
    {D : Scheme α} (candidate : Candidate R D)
    (block : CertifiedBlock R candidate.finish) :
    candidate.path.length < (candidate.extendBlock block).path.length := by
  rw [Candidate.extendBlock_length]
  have hpositive := block.positive
  omega

/-- The starting state's cardinality is bounded by every path's altitude. -/
theorem MovePath.start_card_le_altitude {R : Scheme α → Scheme α → Prop}
    {D E : Scheme α} (path : MovePath R D E) : D.card ≤ path.altitude := by
  induction path with
  | singleton =>
      simp only [MovePath.altitude]
      exact Nat.le_refl _
  | snoc path edge ih =>
      simp only [MovePath.altitude]
      exact ih.trans (Nat.le_max_left _ _)

/-- Every generated candidate obeys the actual primitive budget and full-path
altitude ceiling, provided the root itself is below the ceiling. -/
theorem boundedCandidates_sound {R : Scheme α → Scheme α → Prop}
    (successors : (X : Scheme α) → List (FiniteBoundedSearch.Successor R X))
    (blocks : (X : Scheme α) → List (CertifiedBlock R X))
    {H : ℕ} {D : Scheme α} (hD : D.card ≤ H) (k : ℕ) :
    ∀ candidate ∈ boundedCandidates successors blocks H D k,
      candidate.path.length ≤ k ∧ candidate.path.altitude ≤ H := by
  induction k with
  | zero =>
      intro candidate hcandidate
      simp only [boundedCandidates, List.mem_singleton] at hcandidate
      subst candidate
      simp only [Candidate.root, MovePath.length, MovePath.altitude, Nat.le_refl,
        hD, and_self]
  | succ k ih =>
      intro candidate hcandidate
      simp only [boundedCandidates, List.mem_append, List.mem_flatMap] at hcandidate
      rcases hcandidate with hprior | hextension
      · have hbounds := ih candidate hprior
        exact ⟨hbounds.1.trans (Nat.le_succ k), hbounds.2⟩
      · obtain ⟨prior, hprior, hextension⟩ := hextension
        simp only [admissibleExtensions, List.mem_filter, List.mem_map] at hextension
        exact of_decide_eq_true hextension.2

/-- The root candidate is retained at every weighted recursion budget. -/
theorem root_mem_boundedCandidates {R : Scheme α → Scheme α → Prop}
    (successors : (X : Scheme α) → List (FiniteBoundedSearch.Successor R X))
    (blocks : (X : Scheme α) → List (CertifiedBlock R X))
    (H : ℕ) (D : Scheme α) (k : ℕ) :
    Candidate.root R D ∈ boundedCandidates successors blocks H D k := by
  induction k with
  | zero => simp [boundedCandidates]
  | succ k ih =>
      simp only [boundedCandidates, List.mem_append]
      exact Or.inl ih

/-- Every admissible primitive path is represented, independently of which
optional blocks are provided. -/
theorem boundedCandidates_complete {R : Scheme α → Scheme α → Prop}
    (successors : (X : Scheme α) → List (FiniteBoundedSearch.Successor R X))
    (blocks : (X : Scheme α) → List (CertifiedBlock R X))
    (hcomplete : ∀ {X Y : Scheme α}, R X Y →
      ∃ edge ∈ successors X, edge.finish = Y)
    {H : ℕ} {D E : Scheme α} (path : MovePath R D E) (k : ℕ)
    (hlength : path.length ≤ k) (haltitude : path.altitude ≤ H) :
    ∃ candidate ∈ boundedCandidates successors blocks H D k,
      candidate.finish = E := by
  induction path generalizing k with
  | singleton =>
      exact ⟨Candidate.root R D,
        root_mem_boundedCandidates successors blocks H D k, rfl⟩
  | snoc priorPath edge ih =>
      cases k with
      | zero =>
          simp only [MovePath.length] at hlength
          omega
      | succ k =>
          have hprefixLength : priorPath.length ≤ k := by
            simp only [MovePath.length] at hlength
            omega
          have hprefixAltitude : priorPath.altitude ≤ H := by
            simp only [MovePath.altitude, Nat.max_le] at haltitude
            exact haltitude.1
          obtain ⟨prior, hpriorMem, hpriorFinish⟩ :=
            ih k hprefixLength hprefixAltitude
          cases hpriorFinish
          obtain ⟨next, hnextMem, hnextFinish⟩ := hcomplete edge
          cases hnextFinish
          let block := CertifiedBlock.ofSuccessor next
          let extended := prior.extendBlock block
          have hroot : D.card ≤ H :=
            (MovePath.start_card_le_altitude (priorPath.snoc edge)).trans haltitude
          have hpriorBounds :=
            boundedCandidates_sound successors blocks hroot k prior hpriorMem
          have hblockMem : block ∈ availableBlocks successors blocks prior.finish := by
            simp only [availableBlocks, List.mem_append, List.mem_map]
            exact Or.inl ⟨next, hnextMem, rfl⟩
          have hextendedLength : extended.path.length ≤ k + 1 := by
            simp only [extended, block, Candidate.extendBlock_length,
              CertifiedBlock.ofSuccessor, MovePath.one, MovePath.length]
            omega
          have hextendedAltitude : extended.path.altitude ≤ H := by
            have hnextBound : next.finish.card ≤ H := by
              have haltitudeParts := haltitude
              simp only [MovePath.altitude, Nat.max_le] at haltitudeParts
              exact haltitudeParts.2
            simp only [extended, block, Candidate.extendBlock,
              CertifiedBlock.ofSuccessor, MovePath.one, MovePath.trans,
              MovePath.altitude]
            exact Nat.max_le.mpr ⟨hpriorBounds.2, hnextBound⟩
          refine ⟨extended, ?_, rfl⟩
          simp only [boundedCandidates, List.mem_append, List.mem_flatMap]
          apply Or.inr
          refine ⟨prior, hpriorMem, ?_⟩
          simp only [admissibleExtensions, List.mem_filter, List.mem_map]
          exact ⟨⟨block, hblockMem, rfl⟩,
            decide_eq_true ⟨hextendedLength, hextendedAltitude⟩⟩

/-- Deterministic comparison never increases cardinality from its left input. -/
theorem prefer_card_le_left {R : Scheme α → Scheme α → Prop}
    {D : Scheme α} (left right : Candidate R D) :
    (prefer left right).finish.card ≤ left.finish.card := by
  simp only [prefer]
  split
  next h => exact Nat.le_of_lt h
  next => exact Nat.le_refl _

/-- Deterministic comparison is no larger than its right input. -/
theorem prefer_card_le_right {R : Scheme α → Scheme α → Prop}
    {D : Scheme α} (left right : Candidate R D) :
    (prefer left right).finish.card ≤ right.finish.card := by
  simp only [prefer]
  split
  next => exact Nat.le_refl _
  next h => exact Nat.le_of_not_gt h

/-- Selection is no larger than its fallback. -/
theorem chooseBest_card_le_fallback {R : Scheme α → Scheme α → Prop}
    {D : Scheme α} (fallback : Candidate R D)
    (candidates : List (Candidate R D)) :
    (chooseBest fallback candidates).finish.card ≤ fallback.finish.card := by
  induction candidates generalizing fallback with
  | nil => exact Nat.le_refl _
  | cons head tail ih =>
      simp only [chooseBest, List.foldl_cons]
      exact (ih (prefer fallback head)).trans (prefer_card_le_left fallback head)

/-- Selection is no larger than every candidate in its input list. -/
theorem chooseBest_card_le_of_mem {R : Scheme α → Scheme α → Prop}
    {D : Scheme α} (fallback candidate : Candidate R D)
    {candidates : List (Candidate R D)} (hcandidate : candidate ∈ candidates) :
    (chooseBest fallback candidates).finish.card ≤ candidate.finish.card := by
  induction candidates generalizing fallback with
  | nil => simp at hcandidate
  | cons head tail ih =>
      simp only [chooseBest, List.foldl_cons]
      simp only [List.mem_cons] at hcandidate
      rcases hcandidate with heq | htail
      · subst candidate
        exact (chooseBest_card_le_fallback (prefer fallback head) tail).trans
          (prefer_card_le_right fallback head)
      · exact ih (prefer fallback head) htail

/-- A property shared by the fallback and every listed candidate is inherited
by deterministic selection. -/
theorem chooseBest_property {R : Scheme α → Scheme α → Prop}
    {D : Scheme α} {P : Candidate R D → Prop}
    (fallback : Candidate R D) (candidates : List (Candidate R D))
    (hfallback : P fallback) (hcandidates : ∀ c ∈ candidates, P c) :
    P (chooseBest fallback candidates) := by
  induction candidates generalizing fallback with
  | nil => exact hfallback
  | cons head tail ih =>
      simp only [chooseBest, List.foldl_cons]
      apply ih (prefer fallback head)
      · simp only [prefer]
        split
        next => exact hcandidates head (by simp)
        next => exact hfallback
      · intro candidate hcandidate
        exact hcandidates candidate (by
          simp only [List.mem_cons]
          exact Or.inr hcandidate)

/-- Certified output of exhaustive weighted bounded search. -/
structure Result (R : Scheme α → Scheme α → Prop) (D : Scheme α)
    (k H : ℕ) where
  /-- Selected endpoint. -/
  finish : Scheme α
  /-- Actual expanded primitive path attaining the endpoint. -/
  path : MovePath R D finish
  /-- Actual expanded primitive length respects the budget. -/
  length_le : path.length ≤ k
  /-- Every vertex, including internal block vertices, respects the ceiling. -/
  altitude_le : path.altitude ≤ H
  /-- Universal lower bound against every primitive admissible competitor. -/
  optimal : ∀ {E : Scheme α} (competitor : MovePath R D E),
    competitor.length ≤ k → competitor.altitude ≤ H → finish.card ≤ E.card

/-- Exhaustively search with primitive steps and certified weighted shortcuts,
then return an actual minimum-cardinality primitive path certificate. -/
def optimize {R : Scheme α → Scheme α → Prop}
    (successors : (X : Scheme α) → List (FiniteBoundedSearch.Successor R X))
    (hcomplete : ∀ {X Y : Scheme α}, R X Y →
      ∃ edge ∈ successors X, edge.finish = Y)
    (blocks : (X : Scheme α) → List (CertifiedBlock R X))
    (D : Scheme α) (k H : ℕ) (hD : D.card ≤ H) : Result R D k H := by
  let candidates := boundedCandidates successors blocks H D k
  let fallback := Candidate.root R D
  let best := chooseBest fallback candidates
  have hbestBounds : best.path.length ≤ k ∧ best.path.altitude ≤ H := by
    change (chooseBest fallback candidates).path.length ≤ k ∧
      (chooseBest fallback candidates).path.altitude ≤ H
    apply chooseBest_property
      (P := fun candidate =>
        candidate.path.length ≤ k ∧ candidate.path.altitude ≤ H)
      fallback candidates
    · dsimp only [fallback]
      exact ⟨by simp only [Candidate.root, MovePath.length]; omega,
        by simpa only [Candidate.root, MovePath.altitude] using hD⟩
    · exact boundedCandidates_sound successors blocks hD k
  refine ⟨best.finish, best.path, hbestBounds.1, hbestBounds.2, ?_⟩
  intro E competitor hlength haltitude
  obtain ⟨candidate, hcandidate, hfinish⟩ :=
    boundedCandidates_complete successors blocks hcomplete competitor k
      hlength haltitude
  have hbest : best.finish.card ≤ candidate.finish.card :=
    chooseBest_card_le_of_mem fallback candidate hcandidate
  simpa only [hfinish] using hbest

end BilinearComplexity.FiniteWeightedBoundedSearch

namespace BilinearComplexity.FiniteWeightedBoundedSearch.GroundModel

open BinaryCircuit

/-- Three-state finite carrier used to execute non-unit weighted blocks. -/
abbrev State := Finset (Fin 3)

/-- Singleton search root for the weighted ground model. -/
def start : State := {0}

/-- Three-element intermediate state, deliberately above the tight ceiling. -/
def peak : State := Finset.univ

/-- Primitive graph with the chain `start → peak → ∅`. -/
def Rel (D E : State) : Prop :=
  (D = start ∧ E = peak) ∨ (D = peak ∧ E = ∅)

/-- First primitive edge of the ground chain. -/
theorem start_peak : Rel start peak := Or.inl ⟨rfl, rfl⟩

/-- Second primitive edge of the ground chain. -/
theorem peak_empty : Rel peak ∅ := Or.inr ⟨rfl, rfl⟩

/-- Complete primitive successor provider for the ground chain. -/
def successors (D : State) : List (FiniteBoundedSearch.Successor Rel D) :=
  if hstart : D = start then
    [⟨peak, Or.inl ⟨hstart, rfl⟩⟩]
  else if hpeak : D = peak then
    [⟨∅, Or.inr ⟨hpeak, rfl⟩⟩]
  else []

/-- The ground primitive successor provider covers every graph edge. -/
theorem successors_complete {D E : State} (edge : Rel D E) :
    ∃ next ∈ successors D, next.finish = E := by
  rcases edge with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨⟨peak, start_peak⟩, ?_, rfl⟩
    simp [successors]
  · refine ⟨⟨∅, peak_empty⟩, ?_, rfl⟩
    have hne : peak ≠ start := by decide
    simp [successors, hne]

/-- Genuine cost-two certified block containing the high intermediate `peak`. -/
def twoEdgeBlock : CertifiedBlock Rel start :=
  ⟨∅, .snoc (.snoc (.singleton start) start_peak) peak_empty, by
    simp only [MovePath.length]
    omega⟩

/-- The example block is charged two primitive edges. -/
theorem twoEdgeBlock_length : twoEdgeBlock.path.length = 2 := by
  unfold twoEdgeBlock
  simp only [MovePath.length]

/-- The example block's exact altitude sees its high internal vertex. -/
theorem twoEdgeBlock_altitude : twoEdgeBlock.path.altitude = 3 := by
  unfold twoEdgeBlock
  rw [BilinearComplexity.BinaryCircuit.MovePath.altitude.eq_def]
  dsimp only
  rw [BilinearComplexity.BinaryCircuit.MovePath.altitude.eq_def]
  dsimp only
  rw [BilinearComplexity.BinaryCircuit.MovePath.altitude.eq_def]
  dsimp only
  decide

example : twoEdgeBlock.path.length = 2 ∧ twoEdgeBlock.path.altitude = 3 :=
  ⟨twoEdgeBlock_length, twoEdgeBlock_altitude⟩

/-- Block provider that emits the genuine cost-two block only at `start`. -/
def blocks (D : State) : List (CertifiedBlock Rel D) :=
  if h : D = start then by
    subst D
    exact [twoEdgeBlock]
  else []

example : (blocks start).length = 1 := by decide

/-- Macro-assisted result at insufficient primitive budget one. -/
def budgetOne : Result Rel start 1 3 :=
  optimize successors successors_complete blocks start 1 3 (by decide)

/-- Macro-assisted result at sufficient primitive budget two. -/
def budgetTwo : Result Rel start 2 3 :=
  optimize successors successors_complete blocks start 2 3 (by decide)

/-- Tight-ceiling result that must reject the block's internal `peak`. -/
def tightAltitude : Result Rel start 2 1 :=
  optimize successors successors_complete blocks start 2 1 (by decide)

/-- Primitive-only result over the same budget and ceiling. -/
def primitiveOnly : Result Rel start 2 3 :=
  optimize successors successors_complete (fun _ => []) start 2 3 (by decide)

example : (Candidate.root Rel start).extendBlock twoEdgeBlock ∈
    admissibleExtensions successors blocks 2 3 (Candidate.root Rel start) := by
  simp only [admissibleExtensions, List.mem_filter, List.mem_map]
  constructor
  · refine ⟨twoEdgeBlock, ?_, rfl⟩
    change twoEdgeBlock ∈ availableBlocks successors blocks start
    rw [availableBlocks, List.mem_append]
    exact Or.inr (by simp [blocks])
  · apply decide_eq_true
    have hpath : ((Candidate.root Rel start).extendBlock twoEdgeBlock).path =
        twoEdgeBlock.path := by rfl
    constructor
    · calc
        ((Candidate.root Rel start).extendBlock twoEdgeBlock).path.length =
            twoEdgeBlock.path.length := congrArg MovePath.length hpath
        _ = 2 := twoEdgeBlock_length
        _ ≤ 2 := Nat.le_refl _
    · calc
        ((Candidate.root Rel start).extendBlock twoEdgeBlock).path.altitude =
            twoEdgeBlock.path.altitude := congrArg MovePath.altitude hpath
        _ = 3 := twoEdgeBlock_altitude
        _ ≤ 3 := Nat.le_refl _

example : (Candidate.root Rel start).extendBlock twoEdgeBlock ∉
    admissibleExtensions successors blocks 1 3 (Candidate.root Rel start) := by
  intro hmem
  have hbounds := admissibleExtensions_sound successors blocks 1 3
    (Candidate.root Rel start)
    ((Candidate.root Rel start).extendBlock twoEdgeBlock) hmem
  have hpath : ((Candidate.root Rel start).extendBlock twoEdgeBlock).path =
      twoEdgeBlock.path := by rfl
  have hextendedLength :
      ((Candidate.root Rel start).extendBlock twoEdgeBlock).path.length = 2 :=
    (congrArg MovePath.length hpath).trans twoEdgeBlock_length
  omega

example : (Candidate.root Rel start).extendBlock twoEdgeBlock ∉
    admissibleExtensions successors blocks 2 1 (Candidate.root Rel start) := by
  intro hmem
  have hbounds := admissibleExtensions_sound successors blocks 2 1
    (Candidate.root Rel start)
    ((Candidate.root Rel start).extendBlock twoEdgeBlock) hmem
  have haltitude := hbounds.2
  have hpath : ((Candidate.root Rel start).extendBlock twoEdgeBlock).path =
      twoEdgeBlock.path := by rfl
  have hextendedAltitude :
      ((Candidate.root Rel start).extendBlock twoEdgeBlock).path.altitude = 3 :=
    (congrArg MovePath.altitude hpath).trans twoEdgeBlock_altitude
  omega

/-- Macro-assisted search attains the empty endpoint at budget two. -/
theorem budgetTwo_card : budgetTwo.finish.card = 0 := by
  have hminimum := budgetTwo.optimal twoEdgeBlock.path
    (twoEdgeBlock_length.le) (twoEdgeBlock_altitude.le)
  have hblockCard : twoEdgeBlock.finish.card = 0 := by
    simp [twoEdgeBlock]
  omega

/-- Primitive-only search attains the same empty endpoint cardinality. -/
theorem primitiveOnly_card : primitiveOnly.finish.card = 0 := by
  have hminimum := primitiveOnly.optimal twoEdgeBlock.path
    (twoEdgeBlock_length.le) (twoEdgeBlock_altitude.le)
  have hblockCard : twoEdgeBlock.finish.card = 0 := by
    simp [twoEdgeBlock]
  omega

example : primitiveOnly.finish.card = budgetTwo.finish.card := by
  rw [primitiveOnly_card, budgetTwo_card]

#eval
  (twoEdgeBlock.path.length, twoEdgeBlock.path.altitude,
    budgetOne.finish.card, budgetTwo.finish.card, budgetTwo.path.length,
    tightAltitude.finish.card, primitiveOnly.finish.card)

end BilinearComplexity.FiniteWeightedBoundedSearch.GroundModel

namespace BilinearComplexity.FiniteWeightedBoundedSearch

#check @boundedCandidates_sound
#check @boundedCandidates_complete
#check @optimize
#print axioms boundedCandidates_sound
#print axioms boundedCandidates_complete
#print axioms optimize
#print axioms GroundModel.successors_complete

end BilinearComplexity.FiniteWeightedBoundedSearch
