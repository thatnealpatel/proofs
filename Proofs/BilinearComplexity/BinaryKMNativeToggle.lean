import BilinearComplexity.BinaryAmbientMoveSupport

set_option autoImplicit false

namespace BilinearComplexity.BinaryKMNativeToggle

open scoped symmDiff
open BinaryCircuit
open BinaryAmbientCarrier
open BinaryAmbientMoves
open BinaryAmbientMoveSupport
open NormalizedBinaryCarrier (F2)

universe u v w

variable {U : Type u} {V : Type v} {W : Type w}
variable [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
variable [Module F2 U] [Module F2 V] [Module F2 W]
variable [DecidableEq U] [DecidableEq V] [DecidableEq W]

/-- The third coordinate is fixed and the first coordinates add. -/
structure FirstJoin (x y z : Carrier U V W) : Prop where
  second_eq : y.2.1.1 = x.2.1.1
  third_eq : y.2.2.1 = x.2.2.1
  output_first : z.1.1 = x.1.1 + y.1.1
  output_second : z.2.1.1 = x.2.1.1
  output_third : z.2.2.1 = x.2.2.1

/-- The first and third coordinates are fixed and the second coordinates add. -/
structure SecondJoin (x y z : Carrier U V W) : Prop where
  first_eq : y.1.1 = x.1.1
  third_eq : y.2.2.1 = x.2.2.1
  output_first : z.1.1 = x.1.1
  output_second : z.2.1.1 = x.2.1.1 + y.2.1.1
  output_third : z.2.2.1 = x.2.2.1

/-- The state-independent factor equations of a third-factor-preserving Flip. -/
structure ThirdFlipLaw (p t q r : Carrier U V W) : Prop where
  common_third : t.2.2.1 = p.2.2.1
  target_left_first : q.1.1 = p.1.1 + t.1.1
  target_left_second : q.2.1.1 = p.2.1.1
  target_left_third : q.2.2.1 = p.2.2.1
  target_right_first : r.1.1 = t.1.1
  target_right_second : r.2.1.1 = t.2.1.1 - p.2.1.1
  target_right_third : r.2.2.1 = p.2.2.1

/-- Swap the first two factors, retaining the common third factor. -/
def swap12Term (t : Carrier U V W) : Carrier V U W :=
  (t.2.1, t.1, t.2.2)

/-- Swap the first two factors in every term of a state. -/
def swap12State (D : State U V W) : State V U W :=
  D.image swap12Term

@[simp] theorem swap12Term_swap12Term (t : Carrier U V W) :
    swap12Term (swap12Term t) = t := rfl

@[simp] theorem permuteBACState_swap12State (D : State U V W) :
    permuteBACState (swap12State D) = D := by
  ext x
  simp only [permuteBACState, swap12State, Finset.mem_image]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    simpa only [swap12Term, permuteBACTerm] using hz
  · intro hx
    refine ⟨swap12Term x, ⟨x, hx, rfl⟩, ?_⟩
    rfl

@[simp] theorem mem_swap12State_iff (t : Carrier U V W) (D : State U V W) :
    swap12Term t ∈ swap12State D ↔ t ∈ D := by
  simp only [swap12State, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, hxt⟩
    have hxt' : x = t := by
      simpa only [swap12Term_swap12Term] using congrArg swap12Term hxt
    simpa only [hxt'] using hx
  · intro ht
    exact ⟨t, ht, rfl⟩

/-- Swapping the first two factors is injective. -/
theorem swap12Term_injective : Function.Injective
    (swap12Term : Carrier U V W → Carrier V U W) := by
  intro x y hxy
  simpa only [swap12Term_swap12Term] using congrArg swap12Term hxy

@[simp] theorem swap12State_insert (t : Carrier U V W) (D : State U V W) :
    swap12State (insert t D) = insert (swap12Term t) (swap12State D) := by
  exact Finset.image_insert
    (swap12Term : Carrier U V W → Carrier V U W) t D

@[simp] theorem swap12State_erase (t : Carrier U V W) (D : State U V W) :
    swap12State (D.erase t) = (swap12State D).erase (swap12Term t) := by
  exact Finset.image_erase (swap12Term_injective (U := U) (V := V) (W := W)) _ _

/-- A first-coordinate join occupied at both inputs and fresh at its output is
an intrinsic directed Reduction. -/
def firstReduction {x y z : Carrier U V W} {D : State U V W}
    (hjoin : FirstJoin x y z) (hx : x ∈ D) (hy : y ∈ D)
    (hxy : x ≠ y) (hz : z ∉ D) :
    AllModeMove D (insert z ((D.erase x).erase y)) := by
  apply AllModeMove.abc
  apply Move.directedNarrowPairReduction
  exact ⟨hx, hy, hxy, by
    intro hzmem
    exact hz (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hzmem)),
    hjoin.second_eq, hjoin.third_eq, hjoin.output_first,
    hjoin.output_second, hjoin.output_third, rfl⟩

/-- A first-coordinate join with occupied output and fresh inputs is an
intrinsic Split in reverse algebraic direction. -/
def firstSplit {x y z : Carrier U V W} {D : State U V W}
    (hjoin : FirstJoin x y z) (hz : z ∈ D) (hxy : x ≠ y)
    (hx : x ∉ D.erase z) (hy : y ∉ D.erase z) :
    AllModeMove D (insert x (insert y (D.erase z))) := by
  apply AllModeMove.abc
  apply Move.generatedFirstSplit
  refine ⟨hz, hxy, hx, hy, ?_, hjoin.output_second.symm,
    hjoin.second_eq.trans hjoin.output_second.symm,
    hjoin.output_third.symm, hjoin.third_eq.trans hjoin.output_third.symm, rfl⟩
  calc
    z.1.1 = x.1.1 + y.1.1 := hjoin.output_first

/-- A second-coordinate join occupied at both inputs and fresh at its output is
an intrinsic directed Reduction after the checked `(2,1,3)` permutation. -/
def secondReduction {x y z : Carrier U V W} {D : State U V W}
    (hjoin : SecondJoin x y z) (hx : x ∈ D) (hy : y ∈ D)
    (hxy : x ≠ y) (hz : z ∉ D) :
    AllModeMove D (insert z ((D.erase x).erase y)) := by
  let D₀ := swap12State D
  let E₀ := insert (swap12Term z)
    ((D₀.erase (swap12Term x)).erase (swap12Term y))
  have hmove : Move D₀ E₀ := by
    apply Move.directedNarrowPairReduction
    refine ⟨(mem_swap12State_iff x D).mpr hx,
      (mem_swap12State_iff y D).mpr hy, ?_, ?_, hjoin.first_eq,
      hjoin.third_eq, hjoin.output_second, hjoin.output_first,
      hjoin.output_third, rfl⟩
    · intro h
      exact hxy (congrArg swap12Term h)
    · intro hzmem
      have hzD₀ : swap12Term z ∉ D₀ := by
        simpa only [D₀, mem_swap12State_iff] using hz
      exact hzD₀ (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hzmem))
  apply AllModeMove.bac hmove
  · exact (permuteBACState_swap12State D).symm
  · have hE₀ : E₀ = swap12State (insert z ((D.erase x).erase y)) := by
      simp only [E₀, D₀, swap12State_insert, swap12State_erase]
    rw [hE₀, permuteBACState_swap12State]

/-- A second-coordinate join with occupied output and fresh inputs is an
intrinsic Split after the checked `(2,1,3)` permutation. -/
def secondSplit {x y z : Carrier U V W} {D : State U V W}
    (hjoin : SecondJoin x y z) (hz : z ∈ D) (hxy : x ≠ y)
    (hx : x ∉ D.erase z) (hy : y ∉ D.erase z) :
    AllModeMove D (insert x (insert y (D.erase z))) := by
  let D₀ := swap12State D
  let E₀ := insert (swap12Term x)
    (insert (swap12Term y) (D₀.erase (swap12Term z)))
  have hmove : Move D₀ E₀ := by
    apply Move.generatedFirstSplit
    refine ⟨(mem_swap12State_iff z D).mpr hz, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, rfl⟩
    · intro h
      exact hxy (congrArg swap12Term h)
    · intro hxmem
      rw [Finset.mem_erase] at hxmem
      apply hx
      exact Finset.mem_erase.mpr ⟨by
        intro heq
        apply hxmem.1
        subst x
        rfl,
        (mem_swap12State_iff x D).mp hxmem.2⟩
    · intro hymem
      rw [Finset.mem_erase] at hymem
      apply hy
      exact Finset.mem_erase.mpr ⟨by
        intro heq
        apply hymem.1
        subst y
        rfl,
        (mem_swap12State_iff y D).mp hymem.2⟩
    · exact hjoin.output_second
    · exact hjoin.output_first.symm
    · exact hjoin.first_eq.trans hjoin.output_first.symm
    · exact hjoin.output_third.symm
    · exact hjoin.third_eq.trans hjoin.output_third.symm
  apply AllModeMove.bac hmove
  · exact (permuteBACState_swap12State D).symm
  · have hE₀ : E₀ = swap12State (insert x (insert y (D.erase z))) := by
      simp only [E₀, D₀, swap12State_insert, swap12State_erase]
    rw [hE₀, permuteBACState_swap12State]


/-- A second-coordinate binary join can be solved for its right input. -/
theorem SecondJoin.rotateRight {x y z : Carrier U V W}
    (h : SecondJoin x y z) : SecondJoin x z y := by
  refine ⟨h.output_first, h.output_third, h.first_eq, ?_, h.third_eq⟩
  calc
    y.2.1.1 = (x.2.1.1 + x.2.1.1) + y.2.1.1 := by
      rw [ZModModule.add_self, zero_add]
    _ = x.2.1.1 + (x.2.1.1 + y.2.1.1) := by rw [add_assoc]
    _ = x.2.1.1 + z.2.1.1 := by rw [← h.output_second]

/-- A first-coordinate binary join can be solved for its right input. -/
theorem FirstJoin.rotateRight {x y z : Carrier U V W}
    (h : FirstJoin x y z) : FirstJoin x z y := by
  refine ⟨h.output_second, h.output_third, ?_, h.second_eq, h.third_eq⟩
  calc
    y.1.1 = (x.1.1 + x.1.1) + y.1.1 := by
      rw [ZModModule.add_self, zero_add]
    _ = x.1.1 + (x.1.1 + y.1.1) := by rw [add_assoc]
    _ = x.1.1 + z.1.1 := by rw [← h.output_first]

/-- Swapping the two residual-pivot roles preserves the binary Flip law. -/
theorem ThirdFlipLaw.swapPivot {p t q r : Carrier U V W}
    (h : ThirdFlipLaw p t q r) : ThirdFlipLaw q t p r := by
  refine ⟨h.common_third.trans h.target_left_third.symm,
    ?_, h.target_left_second.symm, h.target_left_third.symm,
    h.target_right_first, ?_, h.target_right_third.trans h.target_left_third.symm⟩
  · calc
      p.1.1 = (t.1.1 + t.1.1) + p.1.1 := by
        rw [ZModModule.add_self, zero_add]
      _ = (p.1.1 + t.1.1) + t.1.1 := by
        ac_rfl
      _ = q.1.1 + t.1.1 := by rw [← h.target_left_first]
  · calc
      r.2.1.1 = t.2.1.1 - p.2.1.1 := h.target_right_second
      _ = t.2.1.1 + p.2.1.1 := ZModModule.sub_eq_add _ _
      _ = t.2.1.1 + q.2.1.1 := by rw [h.target_left_second]
      _ = t.2.1.1 - q.2.1.1 := (ZModModule.sub_eq_add _ _).symm

/-- Realize a state-independent third-factor Flip law at exact occupied and
fresh atoms. -/
theorem thirdFlip {p t q r : Carrier U V W} {D : State U V W}
    (hlaw : ThirdFlipLaw p t q r) (hp : p ∈ D) (ht : t ∈ D)
    (hpt : p ≠ t) (hq : q ∉ (D.erase p).erase t)
    (hr : r ∉ (D.erase p).erase t) (hqr : q ≠ r) :
    AllModeMove D (insert q (insert r ((D.erase p).erase t))) := by
  apply AllModeMove.abc
  apply Move.sourceThirdFlip
  exact ⟨hp, ht, hpt, hq, hr, hqr, hlaw.common_third,
    hlaw.target_left_first, hlaw.target_left_second,
    hlaw.target_left_third, hlaw.target_right_first,
    hlaw.target_right_second, hlaw.target_right_third, rfl⟩

/-- The exact algebra and noncollision conditions for one three-support toggle
in working factor order `(b,c,a)`. -/
structure ThreeSupportLaws (p t u : Carrier U V W) : Prop where
  join : SecondJoin p t u
  p_ne_t : p ≠ t
  p_ne_u : p ≠ u
  t_ne_u : t ≠ u

/-- The exact algebra and noncollision conditions for one four-support toggle,
including the bridge atom `v`, in working factor order `(b,c,a)`. -/
structure FourSupportLaws (p q t u v : Carrier U V W) : Prop where
  flip : ThirdFlipLaw p t q u
  pivot_join : FirstJoin p q v
  bridge_join : SecondJoin v t u
  p_ne_q : p ≠ q
  p_ne_t : p ≠ t
  p_ne_u : p ≠ u
  p_ne_v : p ≠ v
  q_ne_t : q ≠ t
  q_ne_u : q ≠ u
  q_ne_v : q ≠ v
  t_ne_u : t ≠ u
  t_ne_v : t ≠ v
  u_ne_v : u ≠ v

/-- The finite carrier of a three-support toggle. -/
def threeSupport (p t u : Carrier U V W) : State U V W := {p, t, u}

/-- The finite carrier of a collision-aware four-support exchange. -/
def fourSupport (p q t u v : Carrier U V W) : State U V W := {p, q, t, u, v}

/-- Toggle the three algebraic support atoms in a state. -/
def toggleThree (D : State U V W) (p t u : Carrier U V W) : State U V W :=
  D ∆ threeSupport p t u

/-- Toggle the four endpoint atoms; the auxiliary bridge is not toggled. -/
def toggleFour (D : State U V W) (p q t u : Carrier U V W) : State U V W :=
  D ∆ {p, q, t, u}

/-- Membership in a three-support toggle is exclusive-or with support
membership. -/
theorem mem_toggleThree_iff (D : State U V W) (p t u x : Carrier U V W) :
    x ∈ toggleThree D p t u ↔ (x ∈ D) ≠ (x ∈ threeSupport p t u) := by
  by_cases hD : x ∈ D <;> by_cases hS : x ∈ threeSupport p t u <;>
    simp only [toggleThree, Finset.mem_symmDiff, hD, hS, ne_eq] <;> tauto

/-- Membership in a four-support toggle is exclusive-or with endpoint-support
membership. -/
theorem mem_toggleFour_iff (D : State U V W) (p q t u x : Carrier U V W) :
    x ∈ toggleFour D p q t u ↔ (x ∈ D) ≠ (x ∈ ({p, q, t, u} : State U V W)) := by
  by_cases hD : x ∈ D <;>
    by_cases hS : x ∈ ({p, q, t, u} : State U V W) <;>
      simp only [toggleFour, Finset.mem_symmDiff, hD, hS, ne_eq] <;> tauto

/-- An actual local native path together with its one-or-two edge bound,
no-growth bound, and pointwise preservation outside a supplied carrier. -/
structure LocalCompilation (D E K : State U V W) where
  path : MovePath (AllModeMove (U := U) (V := V) (W := W)) D E
  length_pos : 1 ≤ path.length
  length_le_two : path.length ≤ 2
  altitude_le : path.altitude ≤ max D.card E.card
  outside_fixed : ∀ X, X ∈ path.vertices → ∀ x, x ∉ K → (x ∈ X ↔ x ∈ D)

private theorem toggleThree_eq_reduction {D : State U V W}
    {p t u : Carrier U V W} (hp : p ∈ D) (ht : t ∈ D) (hu : u ∉ D)
    (hpt : p ≠ t) (hpu : p ≠ u) (htu : t ≠ u) :
    toggleThree D p t u = insert u ((D.erase p).erase t) := by
  ext x
  simp only [toggleThree, threeSupport, Finset.mem_symmDiff,
    Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase]
  aesop

private theorem toggleThree_eq_split {D : State U V W}
    {p t u : Carrier U V W} (hp : p ∉ D) (ht : t ∈ D) (hu : u ∉ D)
    (hpt : p ≠ t) (hpu : p ≠ u) (htu : t ≠ u) :
    toggleThree D p t u = insert p (insert u (D.erase t)) := by
  ext x
  simp only [toggleThree, threeSupport, Finset.mem_symmDiff,
    Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase]
  aesop

private theorem outside_toggleThree {D : State U V W}
    {p t u x : Carrier U V W} (hx : x ∉ threeSupport p t u) :
    (x ∈ toggleThree D p t u ↔ x ∈ D) := by
  simp only [toggleThree, Finset.mem_symmDiff, hx, not_false_eq_true,
    and_true]
  tauto

private def castPathFinish {α : Type*} [DecidableEq α]
    {R : Finset α → Finset α → Prop} {D E E' : Finset α}
    (h : E = E') (path : MovePath R D E) : MovePath R D E' := h ▸ path

@[simp] private theorem castPathFinish_length {α : Type*} [DecidableEq α]
    {R : Finset α → Finset α → Prop} {D E E' : Finset α}
    (h : E = E') (path : MovePath R D E) :
    (castPathFinish h path).length = path.length := by
  cases h
  rfl

@[simp] private theorem castPathFinish_altitude {α : Type*} [DecidableEq α]
    {R : Finset α → Finset α → Prop} {D E E' : Finset α}
    (h : E = E') (path : MovePath R D E) :
    (castPathFinish h path).altitude = path.altitude := by
  cases h
  rfl

@[simp] private theorem castPathFinish_vertices {α : Type*} [DecidableEq α]
    {R : Finset α → Finset α → Prop} {D E E' : Finset α}
    (h : E = E') (path : MovePath R D E) :
    (castPathFinish h path).vertices = path.vertices := by
  cases h
  rfl

/-- Compile a three-support binary toggle. Runtime branches only on the actual
membership of `p`; it returns a Split when absent and a Reduction when present. -/
def compileThreeSupportToggle (D : State U V W) (p t u : Carrier U V W)
    (laws : ThreeSupportLaws p t u) (ht : t ∈ D) (hu : u ∉ D) :
    LocalCompilation D (toggleThree D p t u) (threeSupport p t u) := by
  by_cases hp : p ∈ D
  · let E₀ := insert u ((D.erase p).erase t)
    have hedge : AllModeMove D E₀ := secondReduction laws.join hp ht
      laws.p_ne_t hu
    have htarget : toggleThree D p t u = E₀ :=
      toggleThree_eq_reduction hp ht hu laws.p_ne_t laws.p_ne_u laws.t_ne_u
    let path₀ : MovePath (AllModeMove (U := U) (V := V) (W := W)) D E₀ :=
      MovePath.one hedge
    let path : MovePath (AllModeMove (U := U) (V := V) (W := W))
        D (toggleThree D p t u) := castPathFinish htarget.symm path₀
    refine ⟨path, ?_, ?_, ?_, ?_⟩
    · simp only [path, castPathFinish_length, path₀, MovePath.one, MovePath.length]
      omega
    · simp only [path, castPathFinish_length, path₀, MovePath.one, MovePath.length]
      omega
    · simp only [path, castPathFinish_altitude, path₀, MovePath.one, MovePath.altitude]
      rw [htarget]
    · intro X hX x hx
      simp only [path, castPathFinish_vertices, path₀, MovePath.one,
        MovePath.vertices, List.mem_append, List.mem_singleton] at hX
      rcases hX with hX | hX
      · subst X
        exact Iff.rfl
      · subst X
        rw [← htarget]
        exact outside_toggleThree hx
  · have hpErase : p ∉ D.erase t := by
      intro hmem
      exact hp (Finset.mem_of_mem_erase hmem)
    have huErase : u ∉ D.erase t := by
      intro hmem
      exact hu (Finset.mem_of_mem_erase hmem)
    let E₀ := insert p (insert u (D.erase t))
    have hedge : AllModeMove D E₀ := secondSplit laws.join.rotateRight ht
      laws.p_ne_u hpErase huErase
    have htarget : toggleThree D p t u = E₀ :=
      toggleThree_eq_split hp ht hu laws.p_ne_t laws.p_ne_u laws.t_ne_u
    let path₀ : MovePath (AllModeMove (U := U) (V := V) (W := W)) D E₀ :=
      MovePath.one hedge
    let path : MovePath (AllModeMove (U := U) (V := V) (W := W))
        D (toggleThree D p t u) := castPathFinish htarget.symm path₀
    refine ⟨path, ?_, ?_, ?_, ?_⟩
    · simp only [path, castPathFinish_length, path₀, MovePath.one, MovePath.length]
      omega
    · simp only [path, castPathFinish_length, path₀, MovePath.one, MovePath.length]
      omega
    · simp only [path, castPathFinish_altitude, path₀, MovePath.one, MovePath.altitude]
      rw [htarget]
    · intro X hX x hx
      simp only [path, castPathFinish_vertices, path₀, MovePath.one,
        MovePath.vertices, List.mem_append, List.mem_singleton] at hX
      rcases hX with hX | hX
      · subst X
        exact Iff.rfl
      · subst X
        rw [← htarget]
        exact outside_toggleThree hx


private def oneCompilation {D E E₀ K : State U V W}
    (hmove : AllModeMove D E₀) (htarget : E = E₀)
    (hout : ∀ x, x ∉ K → (x ∈ E ↔ x ∈ D)) :
    LocalCompilation D E K := by
  let path₀ : MovePath (AllModeMove (U := U) (V := V) (W := W)) D E₀ :=
    MovePath.one hmove
  let path : MovePath (AllModeMove (U := U) (V := V) (W := W)) D E :=
    castPathFinish htarget.symm path₀
  refine ⟨path, ?_, ?_, ?_, ?_⟩
  · simp only [path, castPathFinish_length, path₀, MovePath.one, MovePath.length]
    omega
  · simp only [path, castPathFinish_length, path₀, MovePath.one, MovePath.length]
    omega
  · simp only [path, castPathFinish_altitude, path₀, MovePath.one,
      MovePath.altitude]
    rw [htarget]
  · intro X hX x hx
    simp only [path, castPathFinish_vertices, path₀, MovePath.one,
      MovePath.vertices, List.mem_append, List.mem_singleton] at hX
    rcases hX with hX | hX
    · subst X
      exact Iff.rfl
    · subst X
      rw [← htarget]
      exact hout x hx

private def twoCompilation {D M E E₀ K : State U V W}
    (hmove₁ : AllModeMove D M) (hmove₂ : AllModeMove M E₀)
    (htarget : E = E₀) (hcard : M.card ≤ max D.card E.card)
    (hmiddle : ∀ x, x ∉ K → (x ∈ M ↔ x ∈ D))
    (hout : ∀ x, x ∉ K → (x ∈ E ↔ x ∈ D)) :
    LocalCompilation D E K := by
  let path₀ : MovePath (AllModeMove (U := U) (V := V) (W := W)) D E₀ :=
    (MovePath.one hmove₁).snoc hmove₂
  let path : MovePath (AllModeMove (U := U) (V := V) (W := W)) D E :=
    castPathFinish htarget.symm path₀
  refine ⟨path, ?_, ?_, ?_, ?_⟩
  · simp only [path, castPathFinish_length, path₀, MovePath.one, MovePath.length]
    omega
  · simp only [path, castPathFinish_length, path₀, MovePath.one, MovePath.length]
    omega
  · simp only [path, castPathFinish_altitude, path₀, MovePath.one,
      MovePath.altitude]
    rw [htarget] at hcard ⊢
    simpa only [max_le_iff] using
      And.intro (And.intro (le_max_left D.card E₀.card) hcard)
        (le_max_right D.card E₀.card)
  · intro X hX x hx
    simp only [path, castPathFinish_vertices, path₀, MovePath.one,
      MovePath.vertices, List.mem_append, List.mem_singleton] at hX
    rcases hX with (rfl | rfl) | rfl
    · exact Iff.rfl
    · exact hmiddle x hx
    · rw [← htarget]
      exact hout x hx


private theorem not_mem_fourSupport_iff {p q t u v x : Carrier U V W} :
    x ∉ fourSupport p q t u v ↔
      x ≠ p ∧ x ≠ q ∧ x ≠ t ∧ x ≠ u ∧ x ≠ v := by
  simp only [fourSupport, Finset.mem_insert, Finset.mem_singleton, not_or]

private theorem outsideReduction {D : State U V W}
    {a b c x : Carrier U V W} (ha : x ≠ a) (hb : x ≠ b) (hc : x ≠ c) :
    (x ∈ insert c ((D.erase a).erase b) ↔ x ∈ D) := by
  have hax : a ≠ x := ha.symm
  have hbx : b ≠ x := hb.symm
  simp only [Finset.mem_insert, Finset.mem_erase, ha, hax, hb, hbx, hc,
    false_or, not_false_eq_true, true_and]
  tauto

private theorem outsideSplit {D : State U V W}
    {a b c x : Carrier U V W} (ha : x ≠ a) (hb : x ≠ b) (hc : x ≠ c) :
    (x ∈ insert b (insert c (D.erase a)) ↔ x ∈ D) := by
  have hax : a ≠ x := ha.symm
  simp only [Finset.mem_insert, Finset.mem_erase, ha, hax, hb, hc, false_or,
    not_false_eq_true, true_and]
  tauto

private theorem outside_toggleFour {D : State U V W}
    {p q t u v x : Carrier U V W} (hx : x ∉ fourSupport p q t u v) :
    (x ∈ toggleFour D p q t u ↔ x ∈ D) := by
  obtain ⟨hxp, hxq, hxt, hxu, _⟩ := not_mem_fourSupport_iff.mp hx
  simp only [toggleFour, Finset.mem_symmDiff, Finset.mem_insert,
    Finset.mem_singleton, hxp, hxq, hxt, hxu, false_or, not_false_eq_true,
    and_true]
  tauto

private theorem cardReduction {D : State U V W} {a b c : Carrier U V W}
    (ha : a ∈ D) (hb : b ∈ D) (hab : a ≠ b) (hc : c ∉ D) :
    (insert c ((D.erase a).erase b)).card + 1 = D.card := by
  have hbErase : b ∈ D.erase a := Finset.mem_erase.mpr ⟨hab.symm, hb⟩
  have hcErase : c ∉ (D.erase a).erase b := by
    intro hmem
    exact hc (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hmem))
  rw [Finset.card_insert_eq_ite, if_neg hcErase,
    Finset.card_erase_of_mem hbErase, Finset.card_erase_of_mem ha]
  have htwo : 2 ≤ D.card := by
    have hlt : (D.erase a).card < D.card := Finset.card_erase_lt_of_mem ha
    have hpos : 0 < (D.erase a).card := Finset.card_pos.mpr ⟨b, hbErase⟩
    omega
  omega

private theorem cardSplit {D : State U V W} {a b c : Carrier U V W}
    (ha : a ∈ D) (hb : b ∉ D) (hc : c ∉ D) (hbc : b ≠ c) :
    (insert b (insert c (D.erase a))).card = D.card + 1 := by
  have hbErase : b ∉ D.erase a := by
    intro hmem
    exact hb (Finset.mem_of_mem_erase hmem)
  have hcErase : c ∉ D.erase a := by
    intro hmem
    exact hc (Finset.mem_of_mem_erase hmem)
  have hbInsert : b ∉ insert c (D.erase a) := by
    simp only [Finset.mem_insert, hbErase, or_false]
    exact hbc
  rw [Finset.card_insert_eq_ite, if_neg hbInsert,
    Finset.card_insert_eq_ite, if_neg hcErase, Finset.card_erase_of_mem ha]
  have hpos : 0 < D.card := Finset.card_pos.mpr ⟨a, ha⟩
  omega


private theorem toggleFour_eq_reduce_vt_then_pq {D : State U V W}
    {p q t u v : Carrier U V W}
    (hp : p ∈ D) (hq : q ∈ D) (ht : t ∈ D) (hu : u ∉ D) (hv : v ∈ D)
    (hpq : p ≠ q) (hpt : p ≠ t) (hpu : p ≠ u) (hpv : p ≠ v)
    (hqt : q ≠ t) (hqu : q ≠ u) (hqv : q ≠ v)
    (htu : t ≠ u) (htv : t ≠ v) (huv : u ≠ v) :
    toggleFour D p q t u =
      insert v (((insert u ((D.erase v).erase t)).erase p).erase q) := by
  ext x
  simp only [toggleFour, Finset.mem_symmDiff, Finset.mem_insert,
    Finset.mem_singleton, Finset.mem_erase]
  by_cases hxp : x = p <;> by_cases hxq : x = q <;>
    by_cases hxt : x = t <;> by_cases hxu : x = u <;>
      by_cases hxv : x = v <;> simp_all only <;> tauto

private theorem toggleFour_eq_reduce_pq_then_vt {D : State U V W}
    {p q t u v : Carrier U V W}
    (hp : p ∈ D) (hq : q ∈ D) (ht : t ∈ D) (hu : u ∉ D) (hv : v ∉ D)
    (hpq : p ≠ q) (hpt : p ≠ t) (hpu : p ≠ u) (hpv : p ≠ v)
    (hqt : q ≠ t) (hqu : q ≠ u) (hqv : q ≠ v)
    (htu : t ≠ u) (htv : t ≠ v) (huv : u ≠ v) :
    toggleFour D p q t u =
      insert u (((insert v ((D.erase p).erase q)).erase v).erase t) := by
  ext x
  simp only [toggleFour, Finset.mem_symmDiff, Finset.mem_insert,
    Finset.mem_singleton, Finset.mem_erase]
  by_cases hxp : x = p <;> by_cases hxq : x = q <;>
    by_cases hxt : x = t <;> by_cases hxu : x = u <;>
      by_cases hxv : x = v <;> simp_all only <;> tauto

private theorem toggleFour_eq_split_t_then_v {D : State U V W}
    {p q t u v : Carrier U V W}
    (hp : p ∉ D) (hq : q ∉ D) (ht : t ∈ D) (hu : u ∉ D) (hv : v ∉ D)
    (hpq : p ≠ q) (hpt : p ≠ t) (hpu : p ≠ u) (hpv : p ≠ v)
    (hqt : q ≠ t) (hqu : q ≠ u) (hqv : q ≠ v)
    (htu : t ≠ u) (htv : t ≠ v) (huv : u ≠ v) :
    toggleFour D p q t u =
      insert p (insert q ((insert v (insert u (D.erase t))).erase v)) := by
  ext x
  simp only [toggleFour, Finset.mem_symmDiff, Finset.mem_insert,
    Finset.mem_singleton, Finset.mem_erase]
  by_cases hxp : x = p <;> by_cases hxq : x = q <;>
    by_cases hxt : x = t <;> by_cases hxu : x = u <;>
      by_cases hxv : x = v <;> simp_all only <;> tauto

private theorem toggleFour_eq_split_v_then_t {D : State U V W}
    {p q t u v : Carrier U V W}
    (hp : p ∉ D) (hq : q ∉ D) (ht : t ∈ D) (hu : u ∉ D) (hv : v ∈ D)
    (hpq : p ≠ q) (hpt : p ≠ t) (hpu : p ≠ u) (hpv : p ≠ v)
    (hqt : q ≠ t) (hqu : q ≠ u) (hqv : q ≠ v)
    (htu : t ≠ u) (htv : t ≠ v) (huv : u ≠ v) :
    toggleFour D p q t u =
      insert v (insert u ((insert p (insert q (D.erase v))).erase t)) := by
  ext x
  simp only [toggleFour, Finset.mem_symmDiff, Finset.mem_insert,
    Finset.mem_singleton, Finset.mem_erase]
  by_cases hxp : x = p <;> by_cases hxq : x = q <;>
    by_cases hxt : x = t <;> by_cases hxu : x = u <;>
      by_cases hxv : x = v <;> simp_all only <;> tauto

/-- Compile a collision-aware four-support exchange by branching on actual
residual-pivot and bridge occupancy. -/
def compileFourSupportToggle (D : State U V W)
    (p q t u v : Carrier U V W) (laws : FourSupportLaws p q t u v)
    (ht : t ∈ D) (hu : u ∉ D) :
    LocalCompilation D (toggleFour D p q t u) (fourSupport p q t u v) := by
  have hpq := laws.p_ne_q
  have hpt := laws.p_ne_t
  have hpu := laws.p_ne_u
  have hpv := laws.p_ne_v
  have hqt := laws.q_ne_t
  have hqu := laws.q_ne_u
  have hqv := laws.q_ne_v
  have htu := laws.t_ne_u
  have htv := laws.t_ne_v
  have huv := laws.u_ne_v
  by_cases hp : p ∈ D
  · by_cases hq : q ∈ D
    · by_cases hv : v ∈ D
      · let M := insert u ((D.erase v).erase t)
        have hmove₁ : AllModeMove D M := secondReduction laws.bridge_join hv ht
          laws.t_ne_v.symm hu
        have hpM : p ∈ M := by
          dsimp only [M]
          rw [Finset.mem_insert]
          exact Or.inr (Finset.mem_erase.mpr ⟨laws.p_ne_t,
            Finset.mem_erase.mpr ⟨laws.p_ne_v, hp⟩⟩)
        have hqM : q ∈ M := by
          dsimp only [M]
          rw [Finset.mem_insert]
          exact Or.inr (Finset.mem_erase.mpr ⟨laws.q_ne_t,
            Finset.mem_erase.mpr ⟨laws.q_ne_v, hq⟩⟩)
        have hvM : v ∉ M := by
          intro hmem
          rcases (Finset.mem_insert.mp (by simpa only [M] using hmem)) with hvu | herase
          · exact laws.u_ne_v hvu.symm
          · have hvErase : v ∈ D.erase v := Finset.mem_of_mem_erase herase
            exact (Finset.mem_erase.mp hvErase).1 rfl
        let E₀ := insert v ((M.erase p).erase q)
        have hmove₂ : AllModeMove M E₀ := firstReduction laws.pivot_join hpM hqM
          laws.p_ne_q hvM
        have htarget : toggleFour D p q t u = E₀ := by
          dsimp only [E₀, M]
          exact toggleFour_eq_reduce_vt_then_pq hp hq ht hu hv hpq hpt hpu hpv
            hqt hqu hqv htu htv huv
        have hcardM : M.card ≤ max D.card (toggleFour D p q t u).card := by
          have hcard := cardReduction hv ht laws.t_ne_v.symm hu
          change M.card + 1 = D.card at hcard
          omega
        apply twoCompilation hmove₁ hmove₂ htarget hcardM
        · intro x hx
          obtain ⟨_, _, hxt, hxu, hxv⟩ := not_mem_fourSupport_iff.mp hx
          exact outsideReduction hxv hxt hxu
        · intro x hx
          exact outside_toggleFour hx
      · let M := insert v ((D.erase p).erase q)
        have hmove₁ : AllModeMove D M := firstReduction laws.pivot_join hp hq
          laws.p_ne_q hv
        have hvM : v ∈ M := by
          simp only [M, Finset.mem_insert, true_or]
        have htM : t ∈ M := by
          dsimp only [M]
          rw [Finset.mem_insert]
          exact Or.inr (Finset.mem_erase.mpr ⟨laws.q_ne_t.symm,
            Finset.mem_erase.mpr ⟨laws.p_ne_t.symm, ht⟩⟩)
        have huM : u ∉ M := by
          intro hmem
          rcases (Finset.mem_insert.mp (by simpa only [M] using hmem)) with huv | herase
          · exact laws.u_ne_v huv
          · exact hu (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase herase))
        let E₀ := insert u ((M.erase v).erase t)
        have hmove₂ : AllModeMove M E₀ := secondReduction laws.bridge_join hvM htM
          laws.t_ne_v.symm huM
        have htarget : toggleFour D p q t u = E₀ := by
          dsimp only [E₀, M]
          exact toggleFour_eq_reduce_pq_then_vt hp hq ht hu hv hpq hpt hpu hpv
            hqt hqu hqv htu htv huv
        have hcardM : M.card ≤ max D.card (toggleFour D p q t u).card := by
          have hcard := cardReduction hp hq laws.p_ne_q hv
          change M.card + 1 = D.card at hcard
          omega
        apply twoCompilation hmove₁ hmove₂ htarget hcardM
        · intro x hx
          obtain ⟨hxp, hxq, _, _, hxv⟩ := not_mem_fourSupport_iff.mp hx
          exact outsideReduction hxp hxq hxv
        · intro x hx
          exact outside_toggleFour hx
    · let E₀ := insert q (insert u ((D.erase p).erase t))
      have hqErase : q ∉ (D.erase p).erase t := by
        intro hmem
        exact hq (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hmem))
      have huErase : u ∉ (D.erase p).erase t := by
        intro hmem
        exact hu (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hmem))
      have hmove : AllModeMove D E₀ := thirdFlip laws.flip hp ht laws.p_ne_t
        hqErase huErase laws.q_ne_u
      have htarget : toggleFour D p q t u = E₀ := by
        ext x
        simp only [toggleFour, E₀, Finset.mem_symmDiff, Finset.mem_insert,
          Finset.mem_singleton, Finset.mem_erase]
        by_cases hxp : x = p <;> by_cases hxq : x = q <;>
          by_cases hxt : x = t <;> by_cases hxu : x = u <;>
            simp_all only <;> tauto
      exact oneCompilation hmove htarget fun x hx => outside_toggleFour hx
  · by_cases hq : q ∈ D
    · let E₀ := insert p (insert u ((D.erase q).erase t))
      have hpErase : p ∉ (D.erase q).erase t := by
        intro hmem
        exact hp (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hmem))
      have huErase : u ∉ (D.erase q).erase t := by
        intro hmem
        exact hu (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hmem))
      have hmove : AllModeMove D E₀ := thirdFlip laws.flip.swapPivot hq ht
        laws.q_ne_t hpErase huErase laws.p_ne_u
      have htarget : toggleFour D p q t u = E₀ := by
        ext x
        simp only [toggleFour, E₀, Finset.mem_symmDiff, Finset.mem_insert,
          Finset.mem_singleton, Finset.mem_erase]
        by_cases hxp : x = p <;> by_cases hxq : x = q <;>
          by_cases hxt : x = t <;> by_cases hxu : x = u <;>
            simp_all only <;> tauto
      exact oneCompilation hmove htarget fun x hx => outside_toggleFour hx
    · by_cases hv : v ∈ D
      · have hpErase : p ∉ D.erase v := by
          intro hmem
          exact hp (Finset.mem_of_mem_erase hmem)
        have hqErase : q ∉ D.erase v := by
          intro hmem
          exact hq (Finset.mem_of_mem_erase hmem)
        let M := insert p (insert q (D.erase v))
        have hmove₁ : AllModeMove D M := firstSplit laws.pivot_join hv laws.p_ne_q
          hpErase hqErase
        have htM : t ∈ M := by
          dsimp only [M]
          rw [Finset.mem_insert]
          exact Or.inr (by
            rw [Finset.mem_insert]
            exact Or.inr (Finset.mem_erase.mpr ⟨laws.t_ne_v, ht⟩))
        have hvFresh : v ∉ M.erase t := by
          intro hmem
          have hvIn : v ∈ insert p (insert q (D.erase v)) := by
            simpa only [M] using Finset.mem_of_mem_erase hmem
          rcases Finset.mem_insert.mp hvIn with hvp | hvRest
          · exact laws.p_ne_v hvp.symm
          · rcases Finset.mem_insert.mp hvRest with hvq | hvErase
            · exact laws.q_ne_v hvq.symm
            · exact (Finset.mem_erase.mp hvErase).1 rfl
        have huFresh : u ∉ M.erase t := by
          intro hmem
          have huIn : u ∈ insert p (insert q (D.erase v)) := by
            simpa only [M] using Finset.mem_of_mem_erase hmem
          rcases Finset.mem_insert.mp huIn with hup | huRest
          · exact laws.p_ne_u hup.symm
          · rcases Finset.mem_insert.mp huRest with huq | huErase
            · exact laws.q_ne_u huq.symm
            · exact hu (Finset.mem_of_mem_erase huErase)
        have hvNotM : v ∉ M := by
          intro hvMem
          exact hvFresh (Finset.mem_erase.mpr ⟨laws.t_ne_v.symm, hvMem⟩)
        have huNotM : u ∉ M := by
          intro huMem
          exact huFresh (Finset.mem_erase.mpr ⟨laws.t_ne_u.symm, huMem⟩)
        let E₀ := insert v (insert u (M.erase t))
        have hmove₂ : AllModeMove M E₀ := secondSplit laws.bridge_join.rotateRight
          htM laws.u_ne_v.symm hvFresh huFresh
        have htarget : toggleFour D p q t u = E₀ := by
          dsimp only [E₀, M]
          exact toggleFour_eq_split_v_then_t hp hq ht hu hv hpq hpt hpu hpv
            hqt hqu hqv htu htv huv
        have hcardM : M.card ≤ max D.card (toggleFour D p q t u).card := by
          have hEcard := cardSplit htM hvNotM huNotM laws.u_ne_v.symm
          change E₀.card = M.card + 1 at hEcard
          rw [htarget]
          omega
        apply twoCompilation hmove₁ hmove₂ htarget hcardM
        · intro x hx
          obtain ⟨hxp, hxq, _, _, hxv⟩ := not_mem_fourSupport_iff.mp hx
          exact outsideSplit hxv hxp hxq
        · intro x hx
          exact outside_toggleFour hx
      · have hvErase : v ∉ D.erase t := by
          intro hmem
          exact hv (Finset.mem_of_mem_erase hmem)
        have huErase : u ∉ D.erase t := by
          intro hmem
          exact hu (Finset.mem_of_mem_erase hmem)
        let M := insert v (insert u (D.erase t))
        have hmove₁ : AllModeMove D M := secondSplit laws.bridge_join.rotateRight
          ht laws.u_ne_v.symm hvErase huErase
        have hvM : v ∈ M := by
          simp only [M, Finset.mem_insert, true_or]
        have hpFresh : p ∉ M.erase v := by
          intro hmem
          have hpIn : p ∈ insert v (insert u (D.erase t)) := by
            simpa only [M] using Finset.mem_of_mem_erase hmem
          rcases Finset.mem_insert.mp hpIn with hpvEq | hpRest
          · exact laws.p_ne_v hpvEq
          · rcases Finset.mem_insert.mp hpRest with hpuEq | hpErase
            · exact laws.p_ne_u hpuEq
            · exact hp (Finset.mem_of_mem_erase hpErase)
        have hqFresh : q ∉ M.erase v := by
          intro hmem
          have hqIn : q ∈ insert v (insert u (D.erase t)) := by
            simpa only [M] using Finset.mem_of_mem_erase hmem
          rcases Finset.mem_insert.mp hqIn with hqvEq | hqRest
          · exact laws.q_ne_v hqvEq
          · rcases Finset.mem_insert.mp hqRest with hquEq | hqErase
            · exact laws.q_ne_u hquEq
            · exact hq (Finset.mem_of_mem_erase hqErase)
        have hpNotM : p ∉ M := by
          intro hpMem
          exact hpFresh (Finset.mem_erase.mpr ⟨laws.p_ne_v, hpMem⟩)
        have hqNotM : q ∉ M := by
          intro hqMem
          exact hqFresh (Finset.mem_erase.mpr ⟨laws.q_ne_v, hqMem⟩)
        let E₀ := insert p (insert q (M.erase v))
        have hmove₂ : AllModeMove M E₀ := firstSplit laws.pivot_join hvM
          laws.p_ne_q hpFresh hqFresh
        have htarget : toggleFour D p q t u = E₀ := by
          dsimp only [E₀, M]
          exact toggleFour_eq_split_t_then_v hp hq ht hu hv hpq hpt hpu hpv
            hqt hqu hqv htu htv huv
        have hcardM : M.card ≤ max D.card (toggleFour D p q t u).card := by
          have hEcard := cardSplit hvM hpNotM hqNotM laws.p_ne_q
          change E₀.card = M.card + 1 at hEcard
          rw [htarget]
          omega
        apply twoCompilation hmove₁ hmove₂ htarget hcardM
        · intro x hx
          obtain ⟨_, _, hxt, hxu, hxv⟩ := not_mem_fourSupport_iff.mp hx
          exact outsideSplit hxt hxv hxu
        · intro x hx
          exact outside_toggleFour hx

end BilinearComplexity.BinaryKMNativeToggle
