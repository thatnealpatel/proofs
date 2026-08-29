import Mathlib

set_option autoImplicit false

/-!
# Abstract binary circuits

This file is the finite-set boundary of the circuit layer. The carrier `α` is
abstract and a scheme is literally a `Finset α`, so an element has no duplicate
occurrences. The only semantic datum is `value : α → V`, where `V` is an
additive `ZMod 2`-module. No injectivity, nonzeroness, tensor structure, or
finiteness of the ambient type `α` is silently assumed; each individual scheme
is finite.

A `MovePath.singleton` is the honest length-zero path with one vertex. The
restricted move relation records both endpoint boundary conditions, allowing
`PathVertex` to expose bounds for every intermediate vertex. This layer makes
no parity-to-integer-box identification.
-/

namespace BilinearComplexity.BinaryCircuit

open scoped BigOperators symmDiff

universe u v

variable {α : Type u} {V : Type v} [DecidableEq α] [AddCommGroup V] [Module (ZMod 2) V]

/-- A scheme is a finite set of carrier elements, not a multiset. -/
abbrev Scheme (α : Type*) := Finset α

/-- The value of a scheme is the finite sum of its carrier values. -/
def evaluation (value : α → V) (D : Scheme α) : V :=
  ∑ a ∈ D, value a

/-- Schemes evaluating to the displayed target; this set is allowed to be empty. -/
def TargetFiber (value : α → V) (target : V) : Set (Scheme α) :=
  {D | evaluation value D = target}

def BinaryCycle (value : α → V) (Z : Scheme α) : Prop :=
  evaluation value Z = 0

/-- An inclusion-minimal nonempty binary cycle. -/
def Circuit (value : α → V) (C : Scheme α) : Prop :=
  BinaryCycle value C ∧ C.Nonempty ∧
    ∀ Z : Scheme α, Z ⊂ C → Z.Nonempty → ¬ BinaryCycle value Z

def toggle (D C : Scheme α) : Scheme α :=
  D ∆ C

lemma add_self_eq_zero (x : V) : x + x = 0 := by
  have h : (1 : ZMod 2) + 1 = 0 := by decide
  calc
    x + x = (1 : ZMod 2) • x + (1 : ZMod 2) • x := by simp
    _ = ((1 : ZMod 2) + 1) • x := (add_smul 1 1 x).symm
    _ = 0 := by rw [h, zero_smul]

lemma evaluation_union {value : α → V} {A B : Scheme α} (h : Disjoint A B) :
    evaluation value (A ∪ B) = evaluation value A + evaluation value B := by
  simp [evaluation, Finset.sum_union h]

lemma evaluation_symmDiff (value : α → V) (D E : Scheme α) :
    evaluation value (toggle D E) = evaluation value D + evaluation value E := by
  let A := D \ E
  let B := E \ D
  let I := D ∩ E
  have hAB : Disjoint A B := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxA hxB
    have ha : x ∈ D ∧ x ∉ E := by simpa [A] using hxA
    have hb : x ∈ E ∧ x ∉ D := by simpa [B] using hxB
    exact ha.2 hb.1
  have hAI : Disjoint A I := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxA hxI
    have ha : x ∈ D ∧ x ∉ E := by simpa [A] using hxA
    have hi : x ∈ D ∧ x ∈ E := by simpa [I] using hxI
    exact ha.2 hi.2
  have hBI : Disjoint B I := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxB hxI
    have hb : x ∈ E ∧ x ∉ D := by simpa [B] using hxB
    have hi : x ∈ D ∧ x ∈ E := by simpa [I] using hxI
    exact hb.2 hi.1
  have hD : evaluation value D = evaluation value A + evaluation value I := by
    rw [← Finset.sdiff_union_inter D E]
    exact evaluation_union hAI
  have hE : evaluation value E = evaluation value B + evaluation value I := by
    have hEI : E \ D ∪ D ∩ E = E := by
      ext x
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
      tauto
    rw [← hEI]
    exact evaluation_union hBI
  calc
    evaluation value (toggle D E) = evaluation value A + evaluation value B := by
      apply evaluation_union hAB |>.trans ?_
      simp [A, B]
    _ = (evaluation value A + evaluation value I) +
          (evaluation value B + evaluation value I) := by
      symm
      calc
        (evaluation value A + evaluation value I) +
            (evaluation value B + evaluation value I) =
            evaluation value A + evaluation value B +
              (evaluation value I + evaluation value I) := by abel
        _ = evaluation value A + evaluation value B := by
          rw [add_self_eq_zero, add_zero]
    _ = evaluation value D + evaluation value E := by rw [hD, hE]

lemma same_fiber_symmDiff_cycle {value : α → V} {target : V} {D E : Scheme α}
    (hD : D ∈ TargetFiber value target) (hE : E ∈ TargetFiber value target) :
    BinaryCycle value (toggle D E) := by
  rw [BinaryCycle, evaluation_symmDiff, hD, hE, add_self_eq_zero]

lemma toggle_cycle_evaluation {value : α → V} {D C : Scheme α}
    (hC : BinaryCycle value C) :
    evaluation value (toggle D C) = evaluation value D := by
  rw [evaluation_symmDiff, hC, add_zero]

/-- A recursive certificate whose nonempty leaves are circuits and whose branches
are disjoint unions. -/
inductive CircuitDecomposition (value : α → V) : Scheme α → Type u
  | empty : CircuitDecomposition value ∅
  | leaf {C : Scheme α} : Circuit value C → CircuitDecomposition value C
  | disjointUnion {A B : Scheme α} : Disjoint A B →
      CircuitDecomposition value A → CircuitDecomposition value B →
      CircuitDecomposition value (A ∪ B)

lemma CircuitDecomposition.isCycle {value : α → V} {Z : Scheme α}
    (h : CircuitDecomposition value Z) : BinaryCycle value Z := by
  induction h with
  | empty => simp [BinaryCycle, evaluation]
  | leaf hC => exact hC.1
  | disjointUnion hd _ _ ihA ihB =>
      rw [BinaryCycle, evaluation_union hd, ihA, ihB, add_zero]

/-- Every binary cycle admits a concrete decomposition into disjoint circuits. -/
noncomputable def binaryCycle_decomposition (value : α → V) (Z : Scheme α)
    (hZ : BinaryCycle value Z) : CircuitDecomposition value Z := by
  induction Z using Finset.strongInduction with
  | H Z ih =>
      by_cases hEmpty : Z = ∅
      · subst Z
        exact CircuitDecomposition.empty
      by_cases hCircuit : Circuit value Z
      · exact CircuitDecomposition.leaf hCircuit
      · have hExists : ∃ A : Scheme α, A ⊂ Z ∧ A.Nonempty ∧ BinaryCycle value A := by
          by_contra h
          apply hCircuit
          refine ⟨hZ, Finset.nonempty_iff_ne_empty.mpr hEmpty, ?_⟩
          intro A hAZ hA hCycle
          exact h ⟨A, hAZ, hA, hCycle⟩
        let A := Classical.choose hExists
        have hSpec := Classical.choose_spec hExists
        have hAZ : A ⊂ Z := hSpec.1
        have hA : A.Nonempty := hSpec.2.1
        have hCycleA : BinaryCycle value A := hSpec.2.2
        let B := Z \ A
        have hAB : Disjoint A B := by
          exact Finset.disjoint_sdiff
        have hUnion : A ∪ B = Z := by
          exact Finset.union_sdiff_of_subset hAZ.subset
        have hCardA : A.card < Z.card := Finset.card_lt_card hAZ
        have hCardB : B.card < Z.card := by
          dsimp [B]
          rw [Finset.card_sdiff_of_subset hAZ.subset]
          have : 0 < A.card := Finset.card_pos.mpr hA
          omega
        have hBZ : B ⊂ Z := by
          apply Finset.ssubset_iff_subset_ne.mpr
          refine ⟨Finset.sdiff_subset, ?_⟩
          intro hEq
          have := congrArg Finset.card hEq
          omega
        have hCycleB : BinaryCycle value B := by
          have hEval := evaluation_union (value := value) hAB
          rw [hUnion] at hEval
          rw [BinaryCycle] at hCycleA hZ ⊢
          rw [hCycleA, hZ] at hEval
          simpa using hEval.symm
        rw [← hUnion]
        exact CircuitDecomposition.disjointUnion hAB
          (ih A hAZ hCycleA) (ih B hBZ hCycleB)

/-- A concrete finite path indexed by its endpoints. `singleton D` contains the
single vertex `D` and has zero edges; `snoc` appends one certified edge. -/
inductive MovePath (R : Scheme α → Scheme α → Prop) :
    Scheme α → Scheme α → Type u
  | singleton (D : Scheme α) : MovePath R D D
  | snoc {D E F : Scheme α} : MovePath R D E → R E F → MovePath R D F

namespace MovePath

/-- The one-edge path associated to one related pair. -/
def one {R : Scheme α → Scheme α → Prop} {D E : Scheme α} (h : R D E) :
    MovePath R D E :=
  .snoc (.singleton D) h

/-- Concatenation of two concrete paths with a common endpoint. -/
def trans {R : Scheme α → Scheme α → Prop} {D E : Scheme α}
    (p : MovePath R D E) : {F : Scheme α} → MovePath R E F → MovePath R D F
  | _, .singleton _ => p
  | _, .snoc q h => .snoc (trans p q) h

/-- A concrete path can be mapped along an implication between edge relations. -/
def mono {R S : Scheme α → Scheme α → Prop}
    (hRS : ∀ {X Y}, R X Y → S X Y) :
    {D E : Scheme α} → MovePath R D E → MovePath S D E
  | _, _, .singleton X => .singleton X
  | _, _, .snoc p h => .snoc (mono hRS p) (hRS h)

/-- The number of edges in a concrete path. -/
def length {R : Scheme α → Scheme α → Prop} :
    {D E : Scheme α} → MovePath R D E → ℕ
  | _, _, .singleton _ => 0
  | _, _, .snoc p _ => length (R := R) p + 1

/-- The ordered finite sequence of vertices visited by a concrete path. -/
def vertices {R : Scheme α → Scheme α → Prop} :
    {D E : Scheme α} → MovePath R D E → List (Scheme α)
  | _, _, .singleton X => [X]
  | _, F, .snoc p _ => vertices (R := R) p ++ [F]

/-- The maximum scheme cardinality among all vertices of a concrete path. -/
def altitude {R : Scheme α → Scheme α → Prop} :
    {D E : Scheme α} → MovePath R D E → ℕ
  | _, _, .singleton X => X.card
  | _, F, .snoc p _ => max (altitude (R := R) p) F.card

/-- A singleton path has zero edges. -/
example {R : Scheme α → Scheme α → Prop} (D : Scheme α) :
    (MovePath.singleton D : MovePath R D D).length = 0 := by simp [length]

/-- A singleton path records its unique endpoint as a vertex. -/
example {R : Scheme α → Scheme α → Prop} (D : Scheme α) :
    (MovePath.singleton D : MovePath R D D).vertices = [D] := by simp [vertices]

/-- The altitude of a singleton path is the cardinality of its endpoint. -/
example {R : Scheme α → Scheme α → Prop} (D : Scheme α) :
    (MovePath.singleton D : MovePath R D D).altitude = D.card := by simp [altitude]

/-- A path has one more recorded vertex than edges. -/
theorem vertices_length {R : Scheme α → Scheme α → Prop} {D E : Scheme α}
    (p : MovePath R D E) : p.vertices.length = p.length + 1 := by
  induction p with
  | singleton => simp [vertices, length]
  | snoc p _ ih => simp only [vertices, List.length_append, List.length_singleton,
      length, ih]

/-- The initial endpoint occurs in the concrete vertex sequence. -/
theorem start_mem_vertices {R : Scheme α → Scheme α → Prop} {D E : Scheme α}
    (p : MovePath R D E) : D ∈ p.vertices := by
  induction p with
  | singleton => simp [vertices]
  | snoc p _ ih =>
      simp only [vertices, List.mem_append, List.mem_singleton]
      exact Or.inl ih

/-- The terminal endpoint occurs in the concrete vertex sequence. -/
theorem end_mem_vertices {R : Scheme α → Scheme α → Prop} {D E : Scheme α}
    (p : MovePath R D E) : E ∈ p.vertices := by
  cases p with
  | singleton => simp [vertices]
  | snoc p _ => simp [vertices]

end MovePath

/-- `X` is an actual vertex of the specified concrete path `p`. -/
def PathVertex {R : Scheme α → Scheme α → Prop} {D E : Scheme α}
    (p : MovePath R D E) (X : Scheme α) : Prop :=
  X ∈ p.vertices

namespace MovePath

/-- A property holding initially and preserved by every edge holds at every
actual vertex of the specified path. -/
theorem vertex_property {R : Scheme α → Scheme α → Prop} {P : Scheme α → Prop}
    {D E : Scheme α} (p : MovePath R D E) (hD : P D)
    (hStep : ∀ {X Y}, R X Y → P X → P Y) :
    ∀ X, PathVertex p X → P X := by
  intro X hX
  induction p generalizing X with
  | singleton =>
      have hXD : X = D := by
        simpa only [PathVertex, vertices, List.mem_singleton] using hX
      rw [hXD]
      exact hD
  | snoc p hEdge ih =>
      simp only [PathVertex, vertices, List.mem_append, List.mem_singleton] at hX
      rcases hX with hX | rfl
      · exact ih X hX
      · exact hStep hEdge (ih _ (end_mem_vertices p))

/-- If the initial vertex and both endpoints of every edge lie in a boundary,
then every actual vertex of the specified path lies in that boundary. -/
theorem vertex_subset {R : Scheme α → Scheme α → Prop} {boundary D E : Scheme α}
    (p : MovePath R D E)
    (hR : ∀ {X Y}, R X Y → X ⊆ boundary ∧ Y ⊆ boundary)
    (hD : D ⊆ boundary) :
    ∀ X, PathVertex p X → X ⊆ boundary := by
  exact vertex_property p hD (fun hXY _ => (hR hXY).2)

/-- A common cardinality bound for all actual vertices bounds path altitude. -/
theorem altitude_le_of_forall_vertex {R : Scheme α → Scheme α → Prop}
    {D E : Scheme α} {n : ℕ} (p : MovePath R D E)
    (h : ∀ X, PathVertex p X → X.card ≤ n) : p.altitude ≤ n := by
  revert h
  induction p with
  | singleton =>
      intro h
      rw [altitude]
      apply h _
      simp [PathVertex, vertices]
  | snoc p hEdge ih =>
      intro h
      rw [altitude]
      apply Nat.max_le.mpr
      constructor
      · apply ih
        intro X hX
        apply h X
        simp only [PathVertex, vertices, List.mem_append, List.mem_singleton]
        exact Or.inl hX
      · apply h _
        simp [PathVertex, vertices]

end MovePath

/-- The named abstract move that toggles one binary circuit. -/
def CircuitMove (value : α → V) (D E : Scheme α) : Prop :=
  ∃ C : Scheme α, Circuit value C ∧ E = toggle D C

/-- A concrete path of abstract circuit moves, including singleton paths. -/
def CircuitPath (value : α → V) (D E : Scheme α) : Type u :=
  MovePath (CircuitMove value) D E

/-- A circuit move whose two endpoints lie in the explicit finite-set boundary. -/
def RestrictedCircuitMove (value : α → V) (boundary D E : Scheme α) : Prop :=
  CircuitMove value D E ∧ D ⊆ boundary ∧ E ⊆ boundary

/-- A concrete circuit path whose initial vertex and every edge endpoint lie in
an explicit finite-set boundary. -/
structure RestrictedCircuitPath (value : α → V) (boundary D E : Scheme α) where
  /-- The concrete sequence of restricted circuit moves. -/
  path : MovePath (RestrictedCircuitMove value boundary) D E
  /-- Boundary containment for the initial vertex, including a zero-edge path. -/
  start_subset : D ⊆ boundary

namespace RestrictedCircuitPath

/-- The number of edges in a restricted circuit path. -/
def length {value : α → V} {boundary D E : Scheme α}
    (p : RestrictedCircuitPath value boundary D E) : ℕ :=
  p.path.length

/-- The ordered sequence of actual vertices of a restricted circuit path. -/
def vertices {value : α → V} {boundary D E : Scheme α}
    (p : RestrictedCircuitPath value boundary D E) : List (Scheme α) :=
  p.path.vertices

/-- The maximum cardinality of an actual vertex of a restricted circuit path. -/
def altitude {value : α → V} {boundary D E : Scheme α}
    (p : RestrictedCircuitPath value boundary D E) : ℕ :=
  p.path.altitude

end RestrictedCircuitPath

/-- The singleton restricted path on the empty scheme is jointly realizable over `ZMod 2`. -/
example : RestrictedCircuitPath (fun _ : Fin 1 => (0 : ZMod 2)) ∅ ∅ ∅ :=
  ⟨MovePath.singleton ∅, Finset.Subset.rfl⟩

/-- Circuit moves preserve scheme evaluation. -/
lemma circuitMove_preserves_evaluation {value : α → V} {D E : Scheme α}
    (h : CircuitMove value D E) : evaluation value E = evaluation value D := by
  obtain ⟨C, hC, rfl⟩ := h
  exact toggle_cycle_evaluation hC.1

/-- The endpoints of a concrete circuit path have equal evaluation. -/
lemma circuitPath_preserves_evaluation {value : α → V} {D E : Scheme α}
    (p : CircuitPath value D E) : evaluation value E = evaluation value D := by
  induction p with
  | singleton => rfl
  | snoc _ h ih => exact (circuitMove_preserves_evaluation h).trans ih

/-- The final endpoint of a bounded concrete path lies in its boundary. -/
lemma MovePath.endpoint_subset {boundary D E : Scheme α}
    {R : Scheme α → Scheme α → Prop}
    (hR : ∀ {X Y}, R X Y → X ⊆ boundary ∧ Y ⊆ boundary)
    (hD : D ⊆ boundary) (p : MovePath R D E) : E ⊆ boundary := by
  exact MovePath.vertex_subset p hR hD E (MovePath.end_mem_vertices p)

/-- Every actual vertex of a restricted path lies in its stated boundary. -/
lemma restrictedCircuitPath_vertex_subset {value : α → V} {boundary D E X : Scheme α}
    (p : RestrictedCircuitPath value boundary D E)
    (hX : PathVertex p.path X) : X ⊆ boundary := by
  exact MovePath.vertex_subset p.path
    (fun h => ⟨h.2.1, h.2.2⟩) p.start_subset X hX

/-- Every actual vertex of a restricted path has cardinality at most that of its boundary. -/
lemma restrictedCircuitPath_vertex_card_le {value : α → V} {boundary D E X : Scheme α}
    (p : RestrictedCircuitPath value boundary D E)
    (hX : PathVertex p.path X) : X.card ≤ boundary.card :=
  Finset.card_le_card (restrictedCircuitPath_vertex_subset p hX)

/-- The altitude of a restricted path is at most the cardinality of its boundary. -/
lemma restrictedCircuitPath_altitude_le {value : α → V} {boundary D E : Scheme α}
    (p : RestrictedCircuitPath value boundary D E) :
    p.altitude ≤ boundary.card := by
  apply MovePath.altitude_le_of_forall_vertex p.path
  intro X hX
  exact restrictedCircuitPath_vertex_card_le p hX

/-- A decomposition yields the concrete restricted path obtained by toggling its
circuit leaves in order. -/
noncomputable def decomposition_restrictedCircuitPath {value : α → V} {Z D boundary : Scheme α}
    (h : CircuitDecomposition value Z) (hBoundary : D ∪ Z ⊆ boundary) :
    RestrictedCircuitPath value boundary D (toggle D Z) := by
  induction h generalizing D with
  | empty =>
      have hD : D ⊆ boundary :=
        fun x hx => hBoundary (Finset.mem_union_left ∅ hx)
      have hToggle : toggle D ∅ = D := by
        rw [toggle, symmDiff_def]
        simp
      rw [hToggle]
      exact ⟨MovePath.singleton D, hD⟩
  | leaf hC =>
      have hD : D ⊆ boundary := fun x hx => hBoundary (Finset.mem_union_left _ hx)
      have hT : toggle D _ ⊆ boundary :=
        fun x hx => hBoundary (Finset.symmDiff_subset_union hx)
      exact ⟨MovePath.one ⟨⟨_, hC, rfl⟩, hD, hT⟩, hD⟩
  | @disjointUnion A B hAB hA hB ihA ihB =>
      have hBoundA : D ∪ A ⊆ boundary := by
        intro x hx
        apply hBoundary
        rcases Finset.mem_union.mp hx with hx | hx
        · exact Finset.mem_union_left _ hx
        · exact Finset.mem_union_right _ (Finset.mem_union_left _ hx)
      let pA := ihA hBoundA
      have hBoundB : toggle D A ∪ B ⊆ boundary := by
        intro x hx
        rcases Finset.mem_union.mp hx with hx | hx
        · have hx' := Finset.symmDiff_subset_union hx
          rcases Finset.mem_union.mp hx' with hxD | hxA
          · exact hBoundary (Finset.mem_union_left _ hxD)
          · exact hBoundary (Finset.mem_union_right _ (Finset.mem_union_left _ hxA))
        · exact hBoundary (Finset.mem_union_right _ (Finset.mem_union_right _ hx))
      let pB := ihB hBoundB
      refine ⟨?_, pA.start_subset⟩
      simpa [toggle, symmDiff_assoc, Finset.symmDiff_eq_union hAB] using
        MovePath.trans pA.path pB.path

/-- The concrete restricted path constructed between two schemes in one fiber. -/
noncomputable def same_fiber_restrictedCircuitPath {value : α → V} {target : V} {D E : Scheme α}
    (hD : D ∈ TargetFiber value target) (hE : E ∈ TargetFiber value target) :
    RestrictedCircuitPath value (D ∪ E) D E := by
  have hCycle := same_fiber_symmDiff_cycle hD hE
  have hDecomp := binaryCycle_decomposition value (toggle D E) hCycle
  have hBoundary : D ∪ toggle D E ⊆ D ∪ E := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.mem_union_left _ hx
    · exact Finset.symmDiff_subset_union hx
  have p := decomposition_restrictedCircuitPath hDecomp hBoundary
  simpa [toggle, ← symmDiff_assoc] using p

/-- The underlying concrete unrestricted circuit path between two schemes in one fiber. -/
noncomputable def same_fiber_circuitPath {value : α → V} {target : V} {D E : Scheme α}
    (hD : D ∈ TargetFiber value target) (hE : E ∈ TargetFiber value target) :
    CircuitPath value D E := by
  let p := same_fiber_restrictedCircuitPath hD hE
  exact p.path.mono (fun h => h.1)

/-- Every actual vertex of a restricted circuit path from a target-fiber point
remains in the same target fiber. -/
lemma restrictedCircuitPath_vertex_in_fiber {value : α → V} {target : V}
    {boundary D E X : Scheme α} (hD : D ∈ TargetFiber value target)
    (p : RestrictedCircuitPath value boundary D E)
    (hX : PathVertex p.path X) : X ∈ TargetFiber value target := by
  apply MovePath.vertex_property p.path hD
  · intro Y Z hYZ hY
    exact (circuitMove_preserves_evaluation hYZ.1).trans hY
  · exact hX

/-- Every actual vertex of the specific same-fiber path lies in the endpoint
union and satisfies the corresponding cardinality bounds. -/
lemma same_fiber_intermediate_bounds {value : α → V} {target : V} {D E X : Scheme α}
    (hD : D ∈ TargetFiber value target) (hE : E ∈ TargetFiber value target)
    (hX : PathVertex (same_fiber_restrictedCircuitPath hD hE).path X) :
    X ⊆ D ∪ E ∧ X.card ≤ (D ∪ E).card ∧ (D ∪ E).card ≤ D.card + E.card := by
  let p := same_fiber_restrictedCircuitPath hD hE
  exact ⟨restrictedCircuitPath_vertex_subset p hX,
    restrictedCircuitPath_vertex_card_le p hX, Finset.card_union_le D E⟩

/-- Every actual vertex of the specific same-fiber path remains in that fiber. -/
lemma same_fiber_intermediate_in_fiber {value : α → V} {target : V} {D E X : Scheme α}
    (hD : D ∈ TargetFiber value target) (hE : E ∈ TargetFiber value target)
    (hX : PathVertex (same_fiber_restrictedCircuitPath hD hE).path X) :
    X ∈ TargetFiber value target := by
  exact restrictedCircuitPath_vertex_in_fiber hD
    (same_fiber_restrictedCircuitPath hD hE) hX

/-- Two schemes in one target fiber admit a specific restricted circuit path all
of whose actual vertices remain in their union; its altitude is bounded by the
union cardinality and hence by the sum of the endpoint cardinalities. -/
theorem same_fiber_restrictedCircuitPath_with_altitude
    {value : α → V} {target : V} {D E : Scheme α}
    (hD : D ∈ TargetFiber value target) (hE : E ∈ TargetFiber value target) :
    ∃ p : RestrictedCircuitPath value (D ∪ E) D E,
      (∀ X, PathVertex p.path X → X ⊆ D ∪ E) ∧
      p.altitude ≤ (D ∪ E).card ∧ (D ∪ E).card ≤ D.card + E.card := by
  let p := same_fiber_restrictedCircuitPath hD hE
  refine ⟨p, ?_, restrictedCircuitPath_altitude_le p, Finset.card_union_le D E⟩
  intro X hX
  exact restrictedCircuitPath_vertex_subset p hX

end BilinearComplexity.BinaryCircuit
