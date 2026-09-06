import BilinearComplexity.BinaryCircuit

set_option autoImplicit false

namespace BilinearComplexity.FiniteBoundedSearch

open BinaryCircuit

universe u

variable {α : Type u}

/-- A data-bearing outgoing edge from one finite-set state. -/
structure Successor (R : Scheme α → Scheme α → Prop) (D : Scheme α) where
  /-- The endpoint of the edge. -/
  finish : Scheme α
  /-- The proof that the edge belongs to the graph relation. -/
  edge : R D finish

/-- A data-bearing path from a fixed root. -/
structure Candidate (R : Scheme α → Scheme α → Prop) (D : Scheme α) where
  /-- The terminal state of the path. -/
  finish : Scheme α
  /-- The certified path to the terminal state. -/
  path : MovePath R D finish

/-- The zero-edge candidate at the root. -/
def Candidate.root (R : Scheme α → Scheme α → Prop) (D : Scheme α) :
    Candidate R D :=
  ⟨D, .singleton D⟩

/-- Extend a candidate by one data-bearing successor. -/
def Candidate.extend {R : Scheme α → Scheme α → Prop} {D : Scheme α}
    (c : Candidate R D) (e : Successor R c.finish) : Candidate R D :=
  ⟨e.finish, .snoc c.path e.edge⟩

/-- Extend every candidate by every enumerated successor whose endpoint respects
`H`. -/
def extendWithin {R : Scheme α → Scheme α → Prop} {D : Scheme α}
    (successors : (X : Scheme α) → List (Successor R X)) (H : ℕ)
    (c : Candidate R D) : List (Candidate R D) :=
  ((successors c.finish).filter (fun e => e.finish.card ≤ H)).map c.extend

/-- The unpruned bounded search tree, retaining every path of length at most the
specified budget whose vertices respect the ceiling. -/
def boundedCandidates {R : Scheme α → Scheme α → Prop}
    (successors : (X : Scheme α) → List (Successor R X)) (H : ℕ)
    (D : Scheme α) : ℕ → List (Candidate R D)
  | 0 => [Candidate.root R D]
  | k + 1 =>
      let prior := boundedCandidates successors H D k
      prior ++ prior.flatMap (extendWithin successors H)

/-- Prefer the right candidate exactly when it has strictly smaller endpoint
cardinality; ties deterministically retain the left candidate. -/
def prefer {R : Scheme α → Scheme α → Prop} {D : Scheme α}
    (left right : Candidate R D) : Candidate R D :=
  if right.finish.card < left.finish.card then right else left

/-- Fold a candidate list into a deterministic minimum, using the supplied
candidate as the fallback and initial incumbent. -/
def chooseBest {R : Scheme α → Scheme α → Prop} {D : Scheme α}
    (fallback : Candidate R D) (xs : List (Candidate R D)) : Candidate R D :=
  xs.foldl prefer fallback

/-- The root candidate finishes at its root state. -/
@[simp] theorem Candidate.root_finish
    (R : Scheme α → Scheme α → Prop) (D : Scheme α) :
    (Candidate.root R D).finish = D := rfl

/-- The root candidate has no edges. -/
@[simp] theorem Candidate.root_length
    (R : Scheme α → Scheme α → Prop) (D : Scheme α) :
    (Candidate.root R D).path.length = 0 := by
  simp only [Candidate.root, MovePath.length]

/-- The altitude of the root candidate is its root cardinality. -/
@[simp] theorem Candidate.root_altitude
    (R : Scheme α → Scheme α → Prop) (D : Scheme α) :
    (Candidate.root R D).path.altitude = D.card := by
  simp only [Candidate.root, MovePath.altitude]

/-- A one-edge extension finishes at the appended edge's endpoint. -/
@[simp] theorem Candidate.extend_finish
    {R : Scheme α → Scheme α → Prop} {D : Scheme α}
    (c : Candidate R D) (e : Successor R c.finish) :
    (c.extend e).finish = e.finish := rfl

/-- A one-edge extension increases path length by one. -/
@[simp] theorem Candidate.extend_length
    {R : Scheme α → Scheme α → Prop} {D : Scheme α}
    (c : Candidate R D) (e : Successor R c.finish) :
    (c.extend e).path.length = c.path.length + 1 := by
  simp only [Candidate.extend, MovePath.length]

/-- A one-edge extension has the maximum of the prior and endpoint altitudes. -/
@[simp] theorem Candidate.extend_altitude
    {R : Scheme α → Scheme α → Prop} {D : Scheme α}
    (c : Candidate R D) (e : Successor R c.finish) :
    (c.extend e).path.altitude = max c.path.altitude e.finish.card := by
  simp only [Candidate.extend, MovePath.altitude]

example :
    (boundedCandidates (R := fun _ _ : Finset (Fin 0) => False)
      (fun _ => []) 0 ∅ 0).length = 1 := by decide

example :
    (chooseBest
      (Candidate.root (fun _ _ : Finset (Fin 0) => False) ∅) []).finish = ∅ := by
  rfl

/-- The deterministic comparison never increases cardinality from its left
argument. -/
theorem prefer_card_le_left {R : Scheme α → Scheme α → Prop}
    {D : Scheme α} (left right : Candidate R D) :
    (prefer left right).finish.card ≤ left.finish.card := by
  simp only [prefer]
  split
  next h => exact Nat.le_of_lt h
  next => exact Nat.le_refl _

/-- The deterministic comparison has cardinality at most its right argument. -/
theorem prefer_card_le_right {R : Scheme α → Scheme α → Prop}
    {D : Scheme α} (left right : Candidate R D) :
    (prefer left right).finish.card ≤ right.finish.card := by
  simp only [prefer]
  split
  next => exact Nat.le_refl _
  next h => exact Nat.le_of_not_gt h

/-- Folding deterministic comparisons never increases cardinality from the
fallback. -/
theorem chooseBest_card_le_fallback {R : Scheme α → Scheme α → Prop}
    {D : Scheme α} (fallback : Candidate R D) (xs : List (Candidate R D)) :
    (chooseBest fallback xs).finish.card ≤ fallback.finish.card := by
  induction xs generalizing fallback with
  | nil => exact Nat.le_refl _
  | cons head tail ih =>
      simp only [chooseBest, List.foldl_cons]
      exact (ih (prefer fallback head)).trans (prefer_card_le_left fallback head)

/-- Folding deterministic comparisons gives a candidate no larger than any
member of the folded list. -/
theorem chooseBest_card_le_of_mem {R : Scheme α → Scheme α → Prop}
    {D : Scheme α} (fallback x : Candidate R D)
    {xs : List (Candidate R D)} (hx : x ∈ xs) :
    (chooseBest fallback xs).finish.card ≤ x.finish.card := by
  induction xs generalizing fallback with
  | nil => simp at hx
  | cons head tail ih =>
      simp only [chooseBest, List.foldl_cons]
      simp only [List.mem_cons] at hx
      rcases hx with hEq | hx
      · subst x
        exact (chooseBest_card_le_fallback (prefer fallback head) tail).trans
          (prefer_card_le_right fallback head)
      · exact ih (prefer fallback head) hx

/-- A predicate inherited by the fallback and every list member is inherited by
the deterministic selected candidate. -/
theorem chooseBest_property {R : Scheme α → Scheme α → Prop}
    {D : Scheme α} {P : Candidate R D → Prop}
    (fallback : Candidate R D) (xs : List (Candidate R D))
    (hfallback : P fallback) (hxs : ∀ c ∈ xs, P c) :
    P (chooseBest fallback xs) := by
  induction xs generalizing fallback with
  | nil => exact hfallback
  | cons head tail ih =>
      simp only [chooseBest, List.foldl_cons]
      apply ih (prefer fallback head)
      · simp only [prefer]
        split
        next => exact hxs head (by simp)
        next => exact hfallback
      · intro c hc
        exact hxs c (by simp only [List.mem_cons]; exact Or.inr hc)

/-- Every generated candidate has path length within the recursion budget and,
when the root respects the ceiling, altitude within the ceiling. -/
theorem boundedCandidates_sound {R : Scheme α → Scheme α → Prop}
    (successors : (X : Scheme α) → List (Successor R X))
    {H : ℕ} {D : Scheme α} (hD : D.card ≤ H) (k : ℕ) :
    ∀ c ∈ boundedCandidates successors H D k,
      c.path.length ≤ k ∧ c.path.altitude ≤ H := by
  induction k with
  | zero =>
      intro c hc
      simp only [boundedCandidates, List.mem_singleton] at hc
      subst c
      simp only [Candidate.root_length, Candidate.root_altitude, Nat.le_refl,
        hD, and_self]
  | succ k ih =>
      intro c hc
      simp only [boundedCandidates, List.mem_append, List.mem_flatMap] at hc
      rcases hc with hc | hc
      · have hprior := ih c hc
        exact ⟨hprior.1.trans (Nat.le_succ k), hprior.2⟩
      · obtain ⟨prior, hpriorMem, hcExtend⟩ := hc
        have hprior := ih prior hpriorMem
        simp only [extendWithin, List.mem_map] at hcExtend
        obtain ⟨edge, hedgeFilter, rfl⟩ := hcExtend
        have hedgeCard : edge.finish.card ≤ H := by
          exact of_decide_eq_true (List.mem_filter.mp hedgeFilter).2
        exact ⟨by simp only [Candidate.extend_length]; omega,
          by simp only [Candidate.extend_altitude, Nat.max_le]; exact ⟨hprior.2, hedgeCard⟩⟩

/-- The root occurs in the candidate tree at every recursion budget. -/
theorem root_mem_boundedCandidates {R : Scheme α → Scheme α → Prop}
    (successors : (X : Scheme α) → List (Successor R X)) (H : ℕ)
    (D : Scheme α) (k : ℕ) :
    Candidate.root R D ∈ boundedCandidates successors H D k := by
  induction k with
  | zero => simp [boundedCandidates]
  | succ k ih =>
      simp only [boundedCandidates, List.mem_append]
      exact Or.inl ih

/-- Every relation path within the length and altitude bounds has its endpoint
represented by a generated candidate, provided the successor enumeration is
complete. -/
theorem boundedCandidates_complete {R : Scheme α → Scheme α → Prop}
    (successors : (X : Scheme α) → List (Successor R X))
    (hcomplete : ∀ {X Y : Scheme α}, R X Y →
      ∃ edge ∈ successors X, edge.finish = Y)
    {H : ℕ} {D E : Scheme α} (path : MovePath R D E) (k : ℕ)
    (hlength : path.length ≤ k) (haltitude : path.altitude ≤ H) :
    ∃ c ∈ boundedCandidates successors H D k, c.finish = E := by
  induction path generalizing k with
  | singleton =>
      exact ⟨Candidate.root R D,
        root_mem_boundedCandidates successors H D k, rfl⟩
  | snoc =>
      rename_i priorPath edge ih
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
          have hnextCard : next.finish.card ≤ H := by
            rw [hnextFinish]
            simp only [MovePath.altitude, Nat.max_le] at haltitude
            exact haltitude.2
          let c := prior.extend next
          refine ⟨c, ?_, ?_⟩
          · simp only [boundedCandidates, List.mem_append, List.mem_flatMap]
            exact Or.inr ⟨prior, hpriorMem, by
              simp only [extendWithin, List.mem_map]
              exact ⟨next, by
                exact List.mem_filter.mpr ⟨hnextMem, decide_eq_true hnextCard⟩,
                rfl⟩⟩
          · exact hnextFinish

/-- The certified output of a bounded exhaustive finite-set graph search. -/
structure Result (R : Scheme α → Scheme α → Prop) (D : Scheme α)
    (k H : ℕ) where
  /-- The selected terminal state. -/
  finish : Scheme α
  /-- An actual graph path to the selected terminal state. -/
  path : MovePath R D finish
  /-- The selected path respects the primitive edge budget. -/
  length_le : path.length ≤ k
  /-- Every selected-path vertex respects the cardinality ceiling. -/
  altitude_le : path.altitude ≤ H
  /-- No bounded admissible path has a smaller terminal state. -/
  optimal : ∀ {E : Scheme α} (competitor : MovePath R D E),
    competitor.length ≤ k → competitor.altitude ≤ H → finish.card ≤ E.card

/-- Exhaustively enumerate all bounded paths and select a deterministic endpoint
of minimum cardinality. -/
def optimize {R : Scheme α → Scheme α → Prop}
    (successors : (X : Scheme α) → List (Successor R X))
    (hcomplete : ∀ {X Y : Scheme α}, R X Y →
      ∃ edge ∈ successors X, edge.finish = Y)
    (D : Scheme α) (k H : ℕ) (hD : D.card ≤ H) : Result R D k H := by
  let candidates := boundedCandidates successors H D k
  let fallback := Candidate.root R D
  let best := chooseBest fallback candidates
  have hbestBounds : best.path.length ≤ k ∧ best.path.altitude ≤ H := by
    change (chooseBest fallback candidates).path.length ≤ k ∧
      (chooseBest fallback candidates).path.altitude ≤ H
    apply chooseBest_property
      (P := fun c => c.path.length ≤ k ∧ c.path.altitude ≤ H)
      fallback candidates
    · dsimp only [fallback]
      exact ⟨Candidate.root_length R D ▸ Nat.zero_le k,
        Candidate.root_altitude R D ▸ hD⟩
    · exact boundedCandidates_sound successors hD k
  refine ⟨best.finish, best.path, hbestBounds.1, hbestBounds.2, ?_⟩
  intro E competitor hlength haltitude
  obtain ⟨c, hcMem, hcFinish⟩ :=
    boundedCandidates_complete successors hcomplete competitor k hlength haltitude
  have hbest : best.finish.card ≤ c.finish.card :=
    chooseBest_card_le_of_mem fallback c hcMem
  simpa only [hcFinish] using hbest

/-- At primitive budget zero, exhaustive search returns its root state. -/
theorem optimize_zero_finish {R : Scheme α → Scheme α → Prop}
    (successors : (X : Scheme α) → List (Successor R X))
    (hcomplete : ∀ {X Y : Scheme α}, R X Y →
      ∃ edge ∈ successors X, edge.finish = Y)
    (D : Scheme α) (H : ℕ) (hD : D.card ≤ H) :
    (optimize successors hcomplete D 0 H hD).finish = D := by
  simp [optimize, boundedCandidates, chooseBest, prefer, Candidate.root]

example :
    let R := fun _ _ : Finset (Fin 0) => False
    let result := optimize (R := R) (fun _ => [])
      (by intro X Y h; exact False.elim h) ∅ 0 0 (by decide)
    result.finish = ∅ := by
  rfl

/-- A one-edge ground model verifies that exhaustive search actually takes a
strictly cardinality-decreasing edge rather than always returning its root. -/
example :
    let start : Finset (Fin 1) := {0}
    let R := fun D E : Finset (Fin 1) => D = start ∧ E = ∅
    let successors : (D : Finset (Fin 1)) → List (Successor R D) :=
      fun D => if h : D = start then [⟨∅, h, rfl⟩] else []
    let result := optimize successors
      (by
        intro X Y h
        rcases h with ⟨rfl, rfl⟩
        refine ⟨⟨∅, rfl, rfl⟩, ?_, rfl⟩
        simp only [successors, ↓reduceDIte, List.mem_singleton])
      start 1 1 (by decide)
    result.finish.card = 0 := by
  rfl

#eval
  let start : Finset (Fin 1) := {0}
  let R := fun D E : Finset (Fin 1) => D = start ∧ E = ∅
  let successors : (D : Finset (Fin 1)) → List (Successor R D) :=
    fun D => if h : D = start then [⟨∅, h, rfl⟩] else []
  let result := optimize successors
    (by
      intro X Y h
      rcases h with ⟨rfl, rfl⟩
      refine ⟨⟨∅, rfl, rfl⟩, ?_, rfl⟩
      simp only [successors, ↓reduceDIte, List.mem_singleton])
    start 1 1 (by decide)
  result.finish.card

#check @boundedCandidates_complete
#check @optimize
#print axioms boundedCandidates_complete
#print axioms optimize

end BilinearComplexity.FiniteBoundedSearch
