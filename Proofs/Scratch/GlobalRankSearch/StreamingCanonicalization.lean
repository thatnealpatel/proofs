/-
  Scratch/GlobalRankSearch/StreamingCanonicalization — an ordered-list
  formalization of streaming a triad decomposition into a coordinate-pair
  accumulator.

  The canonical endpoint is determined by `decompSum L`: it coalesces all
  contributions at each coordinate pair and preserves repeated input terms
  through addition, rather than retaining duplicate list entries.

  `StreamingStep` is an abstract coarse relation.  In particular, an arbitrary
  list permutation and absorption into a coordinate table each count as one
  relation step.  The live quantity in this file is only the maximum *list
  length* along a legal path; it is neither a runtime nor a primitive-operation
  complexity bound, and is unrelated to `BilinearComplexity.peak`, which
  measures support sizes of residual tensors during peeling.
-/
import BilinearComplexity.Peeling
import Mathlib

set_option autoImplicit false

namespace BilinearComplexity

/-- The fixed standard basis in the second tensor mode. -/
def modeTwoBasis (k : Type*) [Zero k] [One k] {b : ℕ} (j : Fin b) : Fin b → k :=
  fun q => if q = j then 1 else 0

/-- The fixed standard basis in the third tensor mode. -/
def modeThreeBasis (k : Type*) [Zero k] [One k] {c : ℕ} (l : Fin c) : Fin c → k :=
  fun q => if q = l then 1 else 0

/-- Ground checks for the two separately named coordinate bases. -/
example : modeTwoBasis ℚ (b := 2) 1 = ![0, 1] := by
  funext q
  fin_cases q <;> rfl

example : modeThreeBasis ℚ (c := 2) 0 = ![1, 0] := by
  funext q
  fin_cases q <;> rfl

/-- `clearCoordinate x q` agrees with `x` away from `q` and is zero at `q`. -/
def clearCoordinate {k : Type*} [Zero k] {n : ℕ} (x : Fin n → k) (q : Fin n) :
    Fin n → k :=
  fun p => if p = q then 0 else x p

/-- Clearing coordinate one of a concrete vector changes only that coordinate. -/
example : clearCoordinate (x := ![(2 : ℚ), 3]) 1 = ![2, 0] := by
  funext q
  fin_cases q <;> rfl

/-- Coordinates in the accumulator are ordered with the third-mode coordinate
outermost and the second-mode coordinate innermost.  This is the order in
which the streaming proof extracts coordinates. -/
def streamingCoordinateOrder (b c : ℕ) : List (Fin b × Fin c) :=
  List.ofFn fun q : Fin (c * b) =>
    let p := finProdFinEquiv.symm q
    (p.2, p.1)

/-- The concrete `2 × 2` streaming order is column-major in `(second, third)`. -/
example : streamingCoordinateOrder 2 2 = [(0, 0), (1, 0), (0, 1), (1, 1)] := by
  decide

/-- The first-mode coefficient contributed by a triad at the coordinate pair
`(j,l)` in the fixed second- and third-mode bases. -/
def triadCoordinate {k : Type*} [Mul k] {a b c : ℕ}
    (t : TriadData k a b c) (j : Fin b) (l : Fin c) : Fin a → k :=
  fun i => t.1 i * t.2.1 j * t.2.2 l

/-- A scalar triad contributes the product of its three scalar entries. -/
example : triadCoordinate ((fun _ : Fin 1 => (2 : ℚ)),
    (fun _ : Fin 1 => 3), (fun _ : Fin 1 => 5)) 0 0 0 = 30 := by
  norm_num [triadCoordinate]

/-- The coordinate-pair accumulator of an ordered list.  Every occurrence
is added into its coordinate entry, so input multiplicity is preserved through
addition even though duplicate list entries are later coalesced. -/
def coordinateAccumulator {k : Type*} [CommSemiring k] {a b c : ℕ} :
    Decomp k a b c → Fin b → Fin c → Fin a → k
  | [], _j, _l => 0
  | t :: ts, j, l => triadCoordinate t j l + coordinateAccumulator ts j l

/-- Two identical scalar triads contribute twice to the accumulator. -/
example : coordinateAccumulator
    [((fun _ : Fin 1 => (2 : ℚ)), (fun _ : Fin 1 => 1), (fun _ : Fin 1 => 1)),
     ((fun _ : Fin 1 => 2), (fun _ : Fin 1 => 1), (fun _ : Fin 1 => 1))]
    0 0 0 = 4 := by
  norm_num [coordinateAccumulator, triadCoordinate]

/-- Add one first-mode coefficient to one coordinate-pair accumulator entry. -/
def addAccumulatorCoordinate {k : Type*} [Add k] {a b c : ℕ}
    (A : Fin b → Fin c → Fin a → k) (j : Fin b) (l : Fin c)
    (x : Fin a → k) : Fin b → Fin c → Fin a → k :=
  fun j' l' => if j' = j ∧ l' = l then x + A j' l' else A j' l'

/-- Updating `(1,0)` leaves `(0,0)` alone and adds pointwise at `(1,0)`. -/
example :
    let A : Fin 2 → Fin 1 → Fin 1 → ℚ := fun _ _ _ => 4
    addAccumulatorCoordinate A 1 0 (fun _ => 3) 1 0 0 = 7 ∧
      addAccumulatorCoordinate A 1 0 (fun _ => 3) 0 0 0 = 4 := by
  norm_num [addAccumulatorCoordinate]

/-- The full coordinate table, including entries whose first-mode accumulator
is zero.  Its length is always exactly `b*c`. -/
def fullCoordinateAccumulator {k : Type*} [Zero k] [One k] {a b c : ℕ}
    (A : Fin b → Fin c → Fin a → k) : Decomp k a b c :=
  (streamingCoordinateOrder b c).map fun p =>
    (A p.1 p.2, modeTwoBasis k p.1, modeThreeBasis k p.2)

/-- The full scalar coordinate table has one entry. -/
example : fullCoordinateAccumulator
    (fun _ : Fin 1 => fun _ : Fin 1 => fun _ : Fin 1 => (7 : ℚ)) =
    [((fun _ : Fin 1 => (7 : ℚ)), (fun _ : Fin 1 => (1 : ℚ)),
      (fun _ : Fin 1 => (1 : ℚ)))] := by
  change [((fun _ : Fin 1 => (7 : ℚ)), modeTwoBasis ℚ 0,
    modeThreeBasis ℚ 0)] = _
  congr 2
  apply Prod.ext
  · funext q
    fin_cases q
    rfl
  · funext q
    fin_cases q
    rfl

/-- The canonical coordinate-pair decomposition determined by `decompSum L`.
Contributions at the same coordinate pair are coalesced by addition and zero
first-mode accumulators are explicitly filtered out.  Thus input multiplicity
is preserved algebraically, not as duplicate output list entries. -/
noncomputable def coordinatePairAccumulator {k : Type*} [CommSemiring k] {a b c : ℕ}
    (L : Decomp k a b c) : Decomp k a b c := by
  classical
  exact ((streamingCoordinateOrder b c).filter fun p =>
    coordinateAccumulator L p.1 p.2 ≠ 0).map fun p =>
      (coordinateAccumulator L p.1 p.2,
        modeTwoBasis k p.1, modeThreeBasis k p.2)

/-- Opposite scalar duplicates cancel and their zero accumulator is deleted. -/
example : coordinatePairAccumulator
    [((fun _ : Fin 1 => (1 : ℚ)), (fun _ : Fin 1 => 1), (fun _ : Fin 1 => 1)),
     ((fun _ : Fin 1 => -1), (fun _ : Fin 1 => 1), (fun _ : Fin 1 => 1))] = [] := by
  classical
  have hz : coordinateAccumulator
      [((fun _ : Fin 1 => (1 : ℚ)), (fun _ : Fin 1 => 1), (fun _ : Fin 1 => 1)),
       ((fun _ : Fin 1 => -1), (fun _ : Fin 1 => 1), (fun _ : Fin 1 => 1))]
      0 0 = 0 := by
    funext i
    norm_num [coordinateAccumulator, triadCoordinate]
  simp [coordinatePairAccumulator, streamingCoordinateOrder, Subsingleton.elim _ (0 : Fin 1), hz]

/-- One legal elementary move in the abstract coarse streaming relation.
`perm` makes the convention multiset-permissive while retaining actual lists;
an arbitrary permutation counts as one relation step.  The split constructors
extract one normalized coordinate, `absorbCoordinate` coalesces one coordinate
term into the full table in one relation step, and the zero constructors model
insertion and deletion rather than silently identifying zero terms with
absence.  These steps are not claims about primitive-operation cost. -/
inductive StreamingStep {k : Type*} [CommSemiring k] {a b c : ℕ} :
    Decomp k a b c → Decomp k a b c → Prop
  | perm {L M} (h : L.Perm M) : StreamingStep L M
  | cons (t) {L M} (h : StreamingStep L M) : StreamingStep (t :: L) (t :: M)
  | splitSecond (R) (u : Fin a → k) (v : Fin b → k) (w : Fin c → k) (j : Fin b) :
      StreamingStep ((u, v, w) :: R)
        (((v j) • u, modeTwoBasis k j, w) ::
          (u, clearCoordinate v j, w) :: R)
  | splitThird (R) (u : Fin a → k) (v : Fin b → k) (w : Fin c → k) (l : Fin c) :
      StreamingStep ((u, v, w) :: R)
        (((w l) • u, v, modeThreeBasis k l) ::
          (u, v, clearCoordinate w l) :: R)
  | absorbCoordinate (R) (A : Fin b → Fin c → Fin a → k)
      (j : Fin b) (l : Fin c) (x : Fin a → k) :
      StreamingStep
        ((x, modeTwoBasis k j, modeThreeBasis k l) ::
          (R ++ fullCoordinateAccumulator A))
        (R ++ fullCoordinateAccumulator (addAccumulatorCoordinate A j l x))
  | insertZeroCoordinate (L) (j : Fin b) (l : Fin c) :
      StreamingStep L
        (((0 : Fin a → k), modeTwoBasis k j, modeThreeBasis k l) :: L)
  | deleteZeroFirst (L) (v : Fin b → k) (w : Fin c → k) :
      StreamingStep (((0 : Fin a → k), v, w) :: L) L
  | deleteZeroSecond (L) (u : Fin a → k) (w : Fin c → k) :
      StreamingStep ((u, (0 : Fin b → k), w) :: L) L
  | deleteZeroThird (L) (u : Fin a → k) (v : Fin b → k) :
      StreamingStep ((u, v, (0 : Fin c → k)) :: L) L

/-- A split really adds one live list term. -/
example :
    let u := fun _ : Fin 1 => (1 : ℚ)
    let v := fun _ : Fin 1 => (2 : ℚ)
    let w := fun _ : Fin 1 => (3 : ℚ)
    StreamingStep [(u, v, w)]
      [((v 0) • u, modeTwoBasis ℚ 0, w),
       (u, clearCoordinate v 0, w)] := by
  dsimp only
  exact StreamingStep.splitSecond (k := ℚ) (a := 1) (b := 1) (c := 1)
    [] _ _ _ (0 : Fin 1)

/-- A legal streaming path is a finite sequence of elementary list moves. -/
inductive StreamingPath {k : Type*} [CommSemiring k] {a b c : ℕ} :
    Decomp k a b c → Decomp k a b c → Type _
  | refl {L} : StreamingPath L L
  | tail {L M N} (p : StreamingPath L M) (h : StreamingStep M N) :
      StreamingPath L N

/-- The live-term peak of a path is the maximum list length among every state,
including both endpoints.  It measures neither runtime nor primitive-operation
complexity; in particular, coarse permutation and table-absorption steps each
count as one step.  It is also distinct from the residual-support `peak`. -/
def streamingLivePeak {k : Type*} [CommSemiring k] {a b c : ℕ}
    {L M : Decomp k a b c} (p : StreamingPath L M) : ℕ :=
  match p with
  | .refl => L.length
  | @StreamingPath.tail _ _ _ _ _ _ _ N p _ =>
      max (streamingLivePeak p) N.length

/-- The empty reflexive path has live-term peak zero. -/
example : streamingLivePeak
    (StreamingPath.refl : StreamingPath ([] : Decomp ℚ 1 1 1) []) = 0 :=
  rfl

private def coordinateTail {k : Type*} [Zero k] {n : ℕ}
    (x : Fin n → k) (m : ℕ) : Fin n → k :=
  fun q => if m ≤ q.val then x q else 0

/-- At the first stage no coordinate has been cleared. -/
example : coordinateTail (fun _ : Fin 2 => (3 : ℚ)) 0 = fun _ => 3 := by
  funext q
  simp [coordinateTail]

private def secondPrefix {k : Type*} [CommSemiring k] {a b c : ℕ}
    (A : Fin b → Fin c → Fin a → k) (U : Fin a → k) (v : Fin b → k)
    (l : Fin c) (m : ℕ) : Fin b → Fin c → Fin a → k :=
  fun j' l' => if l' = l ∧ j'.val < m then (v j') • U + A j' l' else A j' l'

/-- The empty second-coordinate prefix changes no accumulator entry. -/
example : secondPrefix (fun _ : Fin 1 => fun _ : Fin 1 => fun _ : Fin 1 => (4 : ℚ))
    (fun _ => 2) (fun _ => 3) 0 0 0 0 0 = 4 := by
  rfl

private def triadPrefix {k : Type*} [CommSemiring k] {a b c : ℕ}
    (A : Fin b → Fin c → Fin a → k) (t : TriadData k a b c) (m : ℕ) :
    Fin b → Fin c → Fin a → k :=
  fun j l => if l.val < m then triadCoordinate t j l + A j l else A j l

/-- The empty third-coordinate prefix changes no accumulator entry. -/
example : triadPrefix (fun _ : Fin 1 => fun _ : Fin 1 => fun _ : Fin 1 => (4 : ℚ))
    ((fun _ => 2), (fun _ => 3), (fun _ => 5)) 0 0 0 0 = 4 := by
  rfl

private def ReachesWithin {k : Type*} [CommSemiring k] {a b c : ℕ} (cap : ℕ)
    (L M : Decomp k a b c) : Prop :=
  ∃ p : StreamingPath L M, streamingLivePeak p ≤ cap

/-- A one-state scalar path fits under capacity one. -/
example : ReachesWithin 1
    ([((fun _ : Fin 1 => (1 : ℚ)), (fun _ => 1), (fun _ => 1))] : Decomp ℚ 1 1 1)
    [((fun _ : Fin 1 => 1), (fun _ => 1), (fun _ => 1))] := by
  exact ⟨(StreamingPath.refl : StreamingPath _ _), by decide⟩

/-- Concatenation of two legal paths is again a legal path. -/
def StreamingPath.trans {k : Type*} [CommSemiring k] {a b c : ℕ}
    {L M N : Decomp k a b c} (p : StreamingPath L M) :
    StreamingPath M N → StreamingPath L N
  | .refl => p
  | .tail q h => .tail (p.trans q) h

/-- Concatenating two reflexive empty paths still has live-term peak zero. -/
example : streamingLivePeak
    ((StreamingPath.refl : StreamingPath ([] : Decomp ℚ 1 1 1) []).trans
      StreamingPath.refl) = 0 := rfl

/-- Applying the same list prefix to every state of a path preserves legality. -/
def StreamingPath.cons {k : Type*} [CommSemiring k] {a b c : ℕ}
    (t : TriadData k a b c) {L M : Decomp k a b c} :
    StreamingPath L M → StreamingPath (t :: L) (t :: M)
  | .refl => .refl
  | .tail p h => .tail (p.cons t) (.cons t h)

/-- Prefixing a reflexive singleton path gives a singleton path of peak one. -/
example :
    let t : TriadData ℚ 1 1 1 :=
      ((fun _ => 1), (fun _ => 1), (fun _ => 1))
    streamingLivePeak ((StreamingPath.refl : StreamingPath ([] : Decomp ℚ 1 1 1) []).cons t) =
      1 := by
  rfl

private theorem streamingLivePeak_endpoint_le {k : Type*} [CommSemiring k]
    {a b c : ℕ} {L M : Decomp k a b c} (p : StreamingPath L M) :
    M.length ≤ streamingLivePeak p := by
  induction p with
  | refl => exact le_rfl
  | tail p h ih => exact Nat.le_max_right _ _

private theorem streamingLivePeak_trans_le {k : Type*} [CommSemiring k]
    {a b c : ℕ} {L M N : Decomp k a b c}
    (p : StreamingPath L M) (q : StreamingPath M N) :
    streamingLivePeak (p.trans q) ≤
      max (streamingLivePeak p) (streamingLivePeak q) := by
  induction q with
  | refl =>
      exact le_max_left _ _
  | tail q h ih =>
      simp only [StreamingPath.trans, streamingLivePeak]
      omega

private theorem streamingLivePeak_cons {k : Type*} [CommSemiring k]
    {a b c : ℕ} (t : TriadData k a b c) {L M : Decomp k a b c}
    (p : StreamingPath L M) :
    streamingLivePeak (p.cons t) = streamingLivePeak p + 1 := by
  induction p with
  | refl => simp [StreamingPath.cons, streamingLivePeak]
  | tail p h ih =>
      simp only [StreamingPath.cons, streamingLivePeak, List.length_cons, ih]
      omega

private theorem reachesWithin_refl {k : Type*} [CommSemiring k] {a b c : ℕ}
    {cap : ℕ} {L : Decomp k a b c} (hL : L.length ≤ cap) :
    ReachesWithin cap L L :=
  ⟨StreamingPath.refl, hL⟩

private theorem reachesWithin_step {k : Type*} [CommSemiring k] {a b c : ℕ}
    {cap : ℕ} {L M : Decomp k a b c} (h : StreamingStep L M)
    (hL : L.length ≤ cap) (hM : M.length ≤ cap) :
    ReachesWithin cap L M := by
  let p : StreamingPath L M := StreamingPath.tail StreamingPath.refl h
  refine ⟨p, ?_⟩
  change max L.length M.length ≤ cap
  exact max_le hL hM

private theorem ReachesWithin.trans {k : Type*} [CommSemiring k] {a b c : ℕ}
    {cap : ℕ} {L M N : Decomp k a b c}
    (hLM : ReachesWithin cap L M) (hMN : ReachesWithin cap M N) :
    ReachesWithin cap L N := by
  obtain ⟨p, hp⟩ := hLM
  obtain ⟨q, hq⟩ := hMN
  refine ⟨p.trans q, le_trans (streamingLivePeak_trans_le p q) ?_⟩
  exact max_le hp hq

private theorem ReachesWithin.mono {k : Type*} [CommSemiring k] {a b c : ℕ}
    {cap cap' : ℕ} {L M : Decomp k a b c} (h : ReachesWithin cap L M)
    (hcap : cap ≤ cap') : ReachesWithin cap' L M := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, hp.trans hcap⟩

private theorem ReachesWithin.cons {k : Type*} [CommSemiring k] {a b c : ℕ}
    {cap : ℕ} (t : TriadData k a b c) {L M : Decomp k a b c}
    (h : ReachesWithin cap L M) : ReachesWithin (cap + 1) (t :: L) (t :: M) := by
  obtain ⟨p, hp⟩ := h
  refine ⟨p.cons t, ?_⟩
  rw [streamingLivePeak_cons]
  omega

private theorem streamingCoordinateOrder_length (b c : ℕ) :
    (streamingCoordinateOrder b c).length = b * c := by
  simp [streamingCoordinateOrder, Nat.mul_comm]

private theorem fullCoordinateAccumulator_length {k : Type*} [Zero k] [One k]
    {a b c : ℕ} (A : Fin b → Fin c → Fin a → k) :
    (fullCoordinateAccumulator A).length = b * c := by
  simp [fullCoordinateAccumulator, streamingCoordinateOrder_length]

private theorem coordinateTail_at {k : Type*} [Zero k] {n m : ℕ}
    (x : Fin n → k) (hm : m < n) :
    coordinateTail x m ⟨m, hm⟩ = x ⟨m, hm⟩ := by
  simp [coordinateTail]

private theorem coordinateTail_clear {k : Type*} [Zero k] {n m : ℕ}
    (x : Fin n → k) (hm : m < n) :
    clearCoordinate (coordinateTail x m) ⟨m, hm⟩ = coordinateTail x (m + 1) := by
  funext q
  by_cases hq : q = ⟨m, hm⟩
  · subst q
    simp [clearCoordinate, coordinateTail]
  · have hval : q.val ≠ m := by
      intro h
      apply hq
      exact Fin.ext h
    by_cases hle : m ≤ q.val
    · have hsucc : m + 1 ≤ q.val := by omega
      simp [clearCoordinate, coordinateTail, hq, hle, hsucc]
    · have hnSucc : ¬m + 1 ≤ q.val := by omega
      simp [clearCoordinate, coordinateTail, hq, hle, hnSucc]

private theorem coordinateTail_top {k : Type*} [Zero k] {n : ℕ}
    (x : Fin n → k) : coordinateTail x n = 0 := by
  funext q
  simp [coordinateTail, show ¬n ≤ q.val by omega]

private theorem secondPrefix_succ {k : Type*} [CommSemiring k] {a b c m : ℕ}
    (A : Fin b → Fin c → Fin a → k) (U : Fin a → k) (v : Fin b → k)
    (l : Fin c) (hm : m < b) :
    addAccumulatorCoordinate (secondPrefix A U v l m) ⟨m, hm⟩ l
        ((coordinateTail v m ⟨m, hm⟩) • U) =
      secondPrefix A U v l (m + 1) := by
  funext j' l' i
  by_cases hl : l' = l
  · subst l'
    by_cases hjlt : j'.val < m
    · have hjne : j' ≠ ⟨m, hm⟩ := by
        intro hj
        have hjval : j'.val = m := by
          simpa using congrArg (fun q : Fin b => q.val) hj
        omega
      have hsucc : j'.val < m + 1 := by omega
      simp [addAccumulatorCoordinate, secondPrefix, hjne, hjlt, hsucc]
    · by_cases hjeq : j' = ⟨m, hm⟩
      · subst j'
        simp [addAccumulatorCoordinate, secondPrefix, coordinateTail_at]
      · have hval : j'.val ≠ m := by
          intro h
          apply hjeq
          exact Fin.ext h
        have hnSucc : ¬j'.val < m + 1 := by omega
        simp [addAccumulatorCoordinate, secondPrefix, hjeq, hjlt, hnSucc]
  · simp [addAccumulatorCoordinate, secondPrefix, hl]

private theorem secondPrefix_top_eq_triadPrefix_succ {k : Type*} [CommSemiring k]
    {a b c m : ℕ} (A : Fin b → Fin c → Fin a → k)
    (t : TriadData k a b c) (hm : m < c) :
    secondPrefix (triadPrefix A t m) ((t.2.2 ⟨m, hm⟩) • t.1) t.2.1
        ⟨m, hm⟩ b = triadPrefix A t (m + 1) := by
  funext j l' i
  by_cases hl : l' = ⟨m, hm⟩
  · subst l'
    simp only [secondPrefix, Fin.is_lt, and_self, ↓reduceIte, triadPrefix, lt_self_iff_false,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, lt_add_iff_pos_right, Order.lt_one_iff,
      triadCoordinate]
    ring
  · have hval : l'.val ≠ m := by
      intro h
      apply hl
      exact Fin.ext h
    have hlt : l'.val < m ↔ l'.val < m + 1 := by omega
    simp [secondPrefix, triadPrefix, hl, hlt]

private theorem triadPrefix_top {k : Type*} [CommSemiring k] {a b c : ℕ}
    (A : Fin b → Fin c → Fin a → k) (t : TriadData k a b c) :
    triadPrefix A t c = fun j l => triadCoordinate t j l + A j l := by
  funext j l i
  simp [triadPrefix]

private theorem streamSecondCoordinates {k : Type*} [CommSemiring k]
    {a b c m : ℕ} (A : Fin b → Fin c → Fin a → k)
    (U : Fin a → k) (v : Fin b → k) (l : Fin c)
    (R : Decomp k a b c) (hm : m ≤ b) :
    ReachesWithin (R.length + b * c + 2)
      ((U, coordinateTail v m, modeThreeBasis k l) ::
        (R ++ fullCoordinateAccumulator (secondPrefix A U v l m)))
      (R ++ fullCoordinateAccumulator (secondPrefix A U v l b)) := by
  generalize hn : b - m = n
  induction n generalizing m with
  | zero =>
      have hmb : m = b := by omega
      subst m
      rw [coordinateTail_top]
      apply reachesWithin_step (StreamingStep.deleteZeroSecond _ _ _)
      · simp [fullCoordinateAccumulator_length]
      · simp [fullCoordinateAccumulator_length]
  | succ n ih =>
      have hlt : m < b := by omega
      let j : Fin b := ⟨m, hlt⟩
      let A' := secondPrefix A U v l m
      let x := (coordinateTail v m j) • U
      have hs : ReachesWithin (R.length + b * c + 2)
          ((U, coordinateTail v m, modeThreeBasis k l) ::
            (R ++ fullCoordinateAccumulator A'))
          ((x, modeTwoBasis k j, modeThreeBasis k l) ::
            ((U, clearCoordinate (coordinateTail v m) j, modeThreeBasis k l) :: R ++
              fullCoordinateAccumulator A')) := by
        apply reachesWithin_step (StreamingStep.splitSecond _ _ _ _ j)
        · simp [fullCoordinateAccumulator_length]
        · simp [fullCoordinateAccumulator_length]
      have ha : ReachesWithin (R.length + b * c + 2)
          ((x, modeTwoBasis k j, modeThreeBasis k l) ::
            ((U, clearCoordinate (coordinateTail v m) j, modeThreeBasis k l) :: R ++
              fullCoordinateAccumulator A'))
          (((U, clearCoordinate (coordinateTail v m) j, modeThreeBasis k l) :: R) ++
            fullCoordinateAccumulator (addAccumulatorCoordinate A' j l x)) := by
        apply reachesWithin_step (StreamingStep.absorbCoordinate _ A' j l x)
        · simp [fullCoordinateAccumulator_length]
        · simp [fullCoordinateAccumulator_length]
      have hr := ih (m := m + 1) (by omega) (by omega)
      rw [← coordinateTail_clear v hlt, ← secondPrefix_succ A U v l hlt] at hr
      exact hs.trans (ha.trans hr)

private theorem streamThirdCoordinates {k : Type*} [CommSemiring k]
    {a b c m : ℕ} (A : Fin b → Fin c → Fin a → k)
    (t : TriadData k a b c) (R : Decomp k a b c) (hm : m ≤ c) :
    ReachesWithin (R.length + b * c + 3)
      ((t.1, t.2.1, coordinateTail t.2.2 m) ::
        (R ++ fullCoordinateAccumulator (triadPrefix A t m)))
      (R ++ fullCoordinateAccumulator (triadPrefix A t c)) := by
  generalize hn : c - m = n
  induction n generalizing m with
  | zero =>
      have hmc : m = c := by omega
      subst m
      rw [coordinateTail_top]
      apply reachesWithin_step (StreamingStep.deleteZeroThird _ _ _)
      · simp [fullCoordinateAccumulator_length]
      · simp [fullCoordinateAccumulator_length]
  | succ n ih =>
      have hlt : m < c := by omega
      let l : Fin c := ⟨m, hlt⟩
      let A' := triadPrefix A t m
      let U := (coordinateTail t.2.2 m l) • t.1
      have hs : ReachesWithin (R.length + b * c + 3)
          ((t.1, t.2.1, coordinateTail t.2.2 m) ::
            (R ++ fullCoordinateAccumulator A'))
          ((U, t.2.1, modeThreeBasis k l) ::
            ((t.1, t.2.1, clearCoordinate (coordinateTail t.2.2 m) l) :: R ++
              fullCoordinateAccumulator A')) := by
        apply reachesWithin_step (StreamingStep.splitThird _ _ _ _ l)
        · simp [fullCoordinateAccumulator_length]
        · simp [fullCoordinateAccumulator_length]
      have hsecond := streamSecondCoordinates A' U t.2.1 l
        ((t.1, t.2.1, clearCoordinate (coordinateTail t.2.2 m) l) :: R)
        (Nat.zero_le b)
      have htail : coordinateTail t.2.1 0 = t.2.1 := by
        funext j
        simp [coordinateTail]
      have hpref : secondPrefix A' U t.2.1 l 0 = A' := by
        funext j l'
        simp [secondPrefix]
      rw [htail, hpref] at hsecond
      have hsecond' : ReachesWithin (R.length + b * c + 3)
          ((U, t.2.1, modeThreeBasis k l) ::
            ((t.1, t.2.1, clearCoordinate (coordinateTail t.2.2 m) l) :: R ++
              fullCoordinateAccumulator A'))
          (((t.1, t.2.1, clearCoordinate (coordinateTail t.2.2 m) l) :: R) ++
            fullCoordinateAccumulator (secondPrefix A' U t.2.1 l b)) := by
        have hcap :
            ((t.1, t.2.1, clearCoordinate (coordinateTail t.2.2 m) l) :: R).length +
                b * c + 2 = R.length + b * c + 3 := by
          simp only [List.length_cons]
          omega
        rw [hcap] at hsecond
        exact hsecond
      have hr := ih (m := m + 1) (by omega) (by omega)
      rw [← coordinateTail_clear t.2.2 hlt,
        ← secondPrefix_top_eq_triadPrefix_succ A t hlt] at hr
      exact hs.trans (hsecond'.trans (by
        simpa [l, A', U, coordinateTail_at] using hr))

private theorem insertZeroCoordinateList {k : Type*} [CommSemiring k]
    {a b c : ℕ} (qs : List (Fin b × Fin c)) (L : Decomp k a b c) :
    ReachesWithin (L.length + qs.length) L
      (qs.map (fun p => ((0 : Fin a → k), modeTwoBasis k p.1,
        modeThreeBasis k p.2)) ++ L) := by
  induction qs with
  | nil =>
      simpa using reachesWithin_refl (Nat.le_refl L.length)
  | cons p qs ih =>
      have ih' := ih.mono (show L.length + qs.length ≤ L.length + (p :: qs).length by simp)
      have hs : ReachesWithin (L.length + (p :: qs).length)
          (qs.map (fun q => ((0 : Fin a → k), modeTwoBasis k q.1,
            modeThreeBasis k q.2)) ++ L)
          (((0 : Fin a → k), modeTwoBasis k p.1, modeThreeBasis k p.2) ::
            (qs.map (fun q => ((0 : Fin a → k), modeTwoBasis k q.1,
              modeThreeBasis k q.2)) ++ L)) := by
        apply reachesWithin_step (StreamingStep.insertZeroCoordinate _ p.1 p.2)
        · simp only [List.length_append, List.length_map, List.length_cons]
          omega
        · simp only [List.length_append, List.length_map, List.length_cons]
          omega
      simpa using ih'.trans hs

private theorem initializeZeroTable {k : Type*} [CommSemiring k] {a b c : ℕ}
    (L : Decomp k a b c) :
    ReachesWithin (L.length + b * c) L
      (L ++ fullCoordinateAccumulator (fun _ _ => (0 : Fin a → k))) := by
  have hi := insertZeroCoordinateList (streamingCoordinateOrder b c) L
  have hp : StreamingStep
      ((streamingCoordinateOrder b c).map
          (fun p => ((0 : Fin a → k), modeTwoBasis k p.1, modeThreeBasis k p.2)) ++ L)
      (L ++ (streamingCoordinateOrder b c).map
          (fun p => ((0 : Fin a → k), modeTwoBasis k p.1,
            modeThreeBasis k p.2))) :=
    StreamingStep.perm List.perm_append_comm
  have hi' : ReachesWithin (L.length + b * c) L
      ((streamingCoordinateOrder b c).map
          (fun p => ((0 : Fin a → k), modeTwoBasis k p.1, modeThreeBasis k p.2)) ++ L) := by
    simpa [streamingCoordinateOrder_length] using hi
  have hs : ReachesWithin (L.length + b * c)
      ((streamingCoordinateOrder b c).map
          (fun p => ((0 : Fin a → k), modeTwoBasis k p.1, modeThreeBasis k p.2)) ++ L)
      (L ++ (streamingCoordinateOrder b c).map
          (fun p => ((0 : Fin a → k), modeTwoBasis k p.1,
            modeThreeBasis k p.2))) := by
    apply reachesWithin_step hp
    · simp only [List.length_append, List.length_map,
        streamingCoordinateOrder_length]
      omega
    · simp [streamingCoordinateOrder_length]
  simpa [fullCoordinateAccumulator, streamingCoordinateOrder_length,
    Nat.add_comm] using hi'.trans hs

private theorem streamOneTriad {k : Type*} [CommSemiring k] {a b c : ℕ}
    (A : Fin b → Fin c → Fin a → k) (t : TriadData k a b c)
    (R : Decomp k a b c) :
    ReachesWithin (R.length + b * c + 3)
      (t :: (R ++ fullCoordinateAccumulator A))
      (R ++ fullCoordinateAccumulator
        (fun j l => triadCoordinate t j l + A j l)) := by
  have h := streamThirdCoordinates A t R (Nat.zero_le c)
  have htail : coordinateTail t.2.2 0 = t.2.2 := by
    funext l
    simp [coordinateTail]
  have hpref : triadPrefix A t 0 = A := by
    funext j l
    simp [triadPrefix]
  rw [htail, hpref, triadPrefix_top] at h
  exact h

private theorem streamWholeList {k : Type*} [CommSemiring k] {a b c : ℕ}
    (L : Decomp k a b c) :
    ReachesWithin (L.length + b * c + 2)
      (L ++ fullCoordinateAccumulator (fun _ _ => (0 : Fin a → k)))
      (fullCoordinateAccumulator (coordinateAccumulator L)) := by
  induction L with
  | nil =>
      apply reachesWithin_refl
      simp [fullCoordinateAccumulator_length]
  | cons t L ih =>
      have hc := ih.cons t
      have hc' : ReachesWithin ((t :: L).length + b * c + 2)
          ((t :: L) ++ fullCoordinateAccumulator (fun _ _ => (0 : Fin a → k)))
          (t :: fullCoordinateAccumulator (coordinateAccumulator L)) := by
        simpa only [List.cons_append, List.length_cons, Nat.add_assoc,
          Nat.add_left_comm, Nat.add_comm] using hc
      have ht := streamOneTriad (coordinateAccumulator L) t ([] : Decomp k a b c)
      have ht' : ReachesWithin ((t :: L).length + b * c + 2)
          (t :: fullCoordinateAccumulator (coordinateAccumulator L))
          (fullCoordinateAccumulator (coordinateAccumulator (t :: L))) := by
        apply ht.mono
        simp
      exact hc'.trans ht'

private theorem deleteZeroFirstFactors {k : Type*} [CommSemiring k] [DecidableEq k]
    {a b c : ℕ}
    (L : Decomp k a b c) :
    ReachesWithin L.length L (L.filter fun t => t.1 ≠ 0) := by
  classical
  induction L with
  | nil => exact reachesWithin_refl (Nat.le_refl 0)
  | cons t L ih =>
      rcases t with ⟨u, v, w⟩
      by_cases hu : u = 0
      · subst u
        have hs : ReachesWithin (L.length + 1) (((0 : Fin a → k), v, w) :: L) L := by
          apply reachesWithin_step (StreamingStep.deleteZeroFirst _ _ _)
          · simp
          · simp
        have ih' := ih.mono (Nat.le_succ L.length)
        simpa using hs.trans ih'
      · have hc := ih.cons (u, v, w)
        simpa [hu, Nat.add_comm] using hc

private theorem filteredFullCoordinateAccumulator {k : Type*} [CommSemiring k]
    [DecidableEq k] {a b c : ℕ} (L : Decomp k a b c) :
    (fullCoordinateAccumulator (coordinateAccumulator L)).filter
        (fun t => t.1 ≠ 0) = coordinatePairAccumulator L := by
  classical
  simp [fullCoordinateAccumulator, coordinatePairAccumulator,
    List.filter_map, Function.comp_def]

/-- Every ordered decomposition has a finite legal streaming path to the
canonical coordinate-pair endpoint determined by `decompSum L`.  Contributions
at each coordinate are coalesced, while repeated input terms retain their
multiplicity through addition rather than as duplicate endpoint entries.  The
maximum live list length, including both endpoints, is at most the starting
length plus the full `b*c` table and two transient split terms.  This is only a
list-length bound for the abstract coarse relation, not a runtime or
primitive-operation complexity bound; zero accumulators are removed by explicit
`deleteZeroFirst` moves. -/
theorem exists_streamingPath_coordinatePairAccumulator {k : Type*} [CommSemiring k]
    {a b c : ℕ} (L : Decomp k a b c) :
    ∃ p : StreamingPath L (coordinatePairAccumulator L),
      streamingLivePeak p ≤ L.length + b * c + 2 := by
  have hi := (initializeZeroTable L).mono
    (show L.length + b * c ≤ L.length + b * c + 2 by omega)
  have hw := streamWholeList L
  classical
  have hd := deleteZeroFirstFactors
    (fullCoordinateAccumulator (coordinateAccumulator L))
  have hd' := hd.mono (show (fullCoordinateAccumulator
      (coordinateAccumulator L)).length ≤ L.length + b * c + 2 by
    simp only [fullCoordinateAccumulator_length]
    omega)
  rw [filteredFullCoordinateAccumulator] at hd'
  exact (hi.trans hw).trans hd'

private theorem decompSum_append_local {k : Type*} [CommSemiring k] {a b c : ℕ}
    (L M : Decomp k a b c) :
    decompSum (L ++ M) = fun i j l => decompSum L i j l + decompSum M i j l := by
  induction L with
  | nil =>
      funext i j l
      simp
  | cons t L ih =>
      funext i j l
      simp only [List.cons_append, decompSum]
      rw [congrFun (congrFun (congrFun ih i) j) l]
      ring

private theorem decompSum_perm_apply {k : Type*} [CommSemiring k] {a b c : ℕ}
    {L M : Decomp k a b c} (h : L.Perm M) (i : Fin a) (j : Fin b) (l : Fin c) :
    decompSum L i j l = decompSum M i j l := by
  induction h with
  | nil => rfl
  | cons t h ih =>
      simp only [decompSum]
      rw [ih]
  | swap x y L =>
      simp only [decompSum]
      ring
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem streamingCoordinateOrder_nodup (b c : ℕ) :
    (streamingCoordinateOrder b c).Nodup := by
  rw [streamingCoordinateOrder, List.nodup_ofFn]
  intro q r h
  apply finProdFinEquiv.symm.injective
  apply Prod.ext
  · exact congrArg Prod.snd h
  · exact congrArg Prod.fst h

private theorem streamingCoordinateOrder_mem {b c : ℕ} (j : Fin b) (l : Fin c) :
    (j, l) ∈ streamingCoordinateOrder b c := by
  rw [streamingCoordinateOrder, List.mem_ofFn]
  refine ⟨finProdFinEquiv (l, j), ?_⟩
  simp

private theorem coordinateTable_apply_aux {k : Type*} [CommSemiring k] {a b c : ℕ}
    (A : Fin b → Fin c → Fin a → k) (qs : List (Fin b × Fin c))
    (hqs : qs.Nodup) (i : Fin a) (j : Fin b) (l : Fin c) :
    decompSum (qs.map fun p =>
        (A p.1 p.2, modeTwoBasis k p.1, modeThreeBasis k p.2)) i j l =
      if (j, l) ∈ qs then A j l i else 0 := by
  induction qs with
  | nil => simp
  | cons p qs ih =>
      have htail : qs.Nodup := hqs.tail
      rw [List.map_cons]
      simp only [decompSum]
      rw [ih htail]
      by_cases hp : p = (j, l)
      · subst p
        have hnot : (j, l) ∉ qs := (List.nodup_cons.mp hqs).1
        have heval : TriadData.eval
            (A j l, modeTwoBasis k j, modeThreeBasis k l) i j l = A j l i := by
          change A j l i * modeTwoBasis k j j * modeThreeBasis k l l = A j l i
          simp [modeTwoBasis, modeThreeBasis]
        simp [heval, hnot]
      · have hcoord : p.1 ≠ j ∨ p.2 ≠ l := by
          by_cases hj : p.1 = j
          · right
            intro hl
            exact hp (Prod.ext hj hl)
          · exact Or.inl hj
        have hnp : (j, l) ≠ p := Ne.symm hp
        rcases hcoord with hj | hl
        · have heval : TriadData.eval
              (A p.1 p.2, modeTwoBasis k p.1, modeThreeBasis k p.2) i j l = 0 := by
            change A p.1 p.2 i * modeTwoBasis k p.1 j *
              modeThreeBasis k p.2 l = 0
            simp [modeTwoBasis, Ne.symm hj]
          simp [heval, hnp]
        · have heval : TriadData.eval
              (A p.1 p.2, modeTwoBasis k p.1, modeThreeBasis k p.2) i j l = 0 := by
            change A p.1 p.2 i * modeTwoBasis k p.1 j *
              modeThreeBasis k p.2 l = 0
            simp [modeThreeBasis, Ne.symm hl]
          simp [heval, hnp]

private theorem fullCoordinateAccumulator_apply {k : Type*} [CommSemiring k]
    {a b c : ℕ} (A : Fin b → Fin c → Fin a → k)
    (i : Fin a) (j : Fin b) (l : Fin c) :
    decompSum (fullCoordinateAccumulator A) i j l = A j l i := by
  rw [fullCoordinateAccumulator,
    coordinateTable_apply_aux A _ (streamingCoordinateOrder_nodup b c)]
  simp [streamingCoordinateOrder_mem]

/-- Every elementary streaming move preserves the represented tensor. -/
theorem StreamingStep.decompSum_eq {k : Type*} [CommSemiring k] {a b c : ℕ}
    {L M : Decomp k a b c} (h : StreamingStep L M) :
    decompSum L = decompSum M := by
  funext i j l
  induction h with
  | perm hp => exact decompSum_perm_apply hp i j l
  | cons t h ih =>
      simp only [decompSum]
      rw [ih]
  | splitSecond R u v w q =>
      simp only [decompSum]
      by_cases hj : j = q
      · subst j
        change u i * v q * w l + decompSum R i q l =
          (v q * u i) * modeTwoBasis k q q * w l +
            (u i * clearCoordinate v q q * w l + decompSum R i q l)
        simp only [modeTwoBasis, ↓reduceIte, mul_one, clearCoordinate, mul_zero, zero_mul,
          zero_add]
        ring
      · change u i * v j * w l + decompSum R i j l =
          (v q * u i) * modeTwoBasis k q j * w l +
            (u i * clearCoordinate v q j * w l + decompSum R i j l)
        simp [modeTwoBasis, clearCoordinate, hj]
  | splitThird R u v w q =>
      simp only [decompSum]
      by_cases hl : l = q
      · subst l
        change u i * v j * w q + decompSum R i j q =
          (w q * u i) * v j * modeThreeBasis k q q +
            (u i * v j * clearCoordinate w q q + decompSum R i j q)
        simp only [modeThreeBasis, ↓reduceIte, mul_one, clearCoordinate, mul_zero, zero_add]
        ring
      · change u i * v j * w l + decompSum R i j l =
          (w q * u i) * v j * modeThreeBasis k q l +
            (u i * v j * clearCoordinate w q l + decompSum R i j l)
        simp [modeThreeBasis, clearCoordinate, hl]
  | absorbCoordinate R A q r x =>
      simp only [decompSum]
      rw [congrFun (congrFun (congrFun (decompSum_append_local R
        (fullCoordinateAccumulator A)) i) j) l]
      rw [congrFun (congrFun (congrFun (decompSum_append_local R
        (fullCoordinateAccumulator (addAccumulatorCoordinate A q r x))) i) j) l]
      rw [fullCoordinateAccumulator_apply, fullCoordinateAccumulator_apply]
      by_cases hj : j = q
      · subst j
        by_cases hl : l = r
        · subst l
          change x i * modeTwoBasis k q q * modeThreeBasis k r r +
              (decompSum R i q r + A q r i) =
            decompSum R i q r + (addAccumulatorCoordinate A q r x) q r i
          simp only [modeTwoBasis, ↓reduceIte, mul_one, modeThreeBasis,
            addAccumulatorCoordinate, and_self, Pi.add_apply]
          ring
        · change x i * modeTwoBasis k q q * modeThreeBasis k r l +
              (decompSum R i q l + A q l i) =
            decompSum R i q l + (addAccumulatorCoordinate A q r x) q l i
          simp [modeTwoBasis, modeThreeBasis, addAccumulatorCoordinate, hl]
      · change x i * modeTwoBasis k q j * modeThreeBasis k r l +
              (decompSum R i j l + A j l i) =
            decompSum R i j l + (addAccumulatorCoordinate A q r x) j l i
        simp [modeTwoBasis, addAccumulatorCoordinate, hj]
  | insertZeroCoordinate L q r =>
      simp only [decompSum]
      change decompSum L i j l =
        0 * modeTwoBasis k q j * modeThreeBasis k r l + decompSum L i j l
      simp
  | deleteZeroFirst L v w =>
      simp only [decompSum]
      change 0 * v j * w l + decompSum L i j l = decompSum L i j l
      simp
  | deleteZeroSecond L u w =>
      simp only [decompSum]
      change u i * 0 * w l + decompSum L i j l = decompSum L i j l
      simp
  | deleteZeroThird L u v =>
      simp only [decompSum]
      change u i * v j * 0 + decompSum L i j l = decompSum L i j l
      simp

/-- Every finite legal streaming path preserves the represented tensor. -/
theorem StreamingPath.decompSum_eq {k : Type*} [CommSemiring k] {a b c : ℕ}
    {L M : Decomp k a b c} (p : StreamingPath L M) :
    decompSum L = decompSum M := by
  induction p with
  | refl => rfl
  | tail p h ih => exact ih.trans h.decompSum_eq

/-- Exact ordered-list streaming canonicalization.  The canonical endpoint is
 determined by `decompSum L`: coordinate contributions are coalesced and input
 multiplicity is preserved through addition, rather than as duplicate output
 entries.  An exact input decomposition reaches this endpoint by explicit
 abstract coarse moves, never has more than `L.length + b*c + 2` live list
 terms, and remains an exact decomposition of the external tensor `T`.
 The hypothesis `hL` is essential for connecting the represented sum
 `decompSum L` to that external tensor.  The peak bound measures only list
 length, not runtime or primitive-operation complexity. -/
theorem streamingCanonicalization {k : Type*} [CommSemiring k] {a b c : ℕ}
    {T : Tensor k a b c} {L : Decomp k a b c} (hL : IsDecomp T L) :
    ∃ p : StreamingPath L (coordinatePairAccumulator L),
      streamingLivePeak p ≤ L.length + b * c + 2 ∧
        IsDecomp T (coordinatePairAccumulator L) := by
  obtain ⟨p, hp⟩ := exists_streamingPath_coordinatePairAccumulator L
  refine ⟨p, hp, ?_⟩
  change decompSum (coordinatePairAccumulator L) = T
  rw [← p.decompSum_eq]
  exact hL

/-- Joint nonvacuity: two nonzero `1 × 2 × 2` triads with opposite first
 factors stream all the way to the empty filtered accumulator.  The witness
 simultaneously supplies the legal path, its live-length bound, the actual
 filtered endpoint, and exactness for the zero tensor. -/
example :
    let L : Decomp ℚ 1 2 2 :=
      [((fun _ => 1), ![2, 3], ![4, 5]),
       ((fun _ => -1), ![2, 3], ![4, 5])]
    ∃ p : StreamingPath L (coordinatePairAccumulator L),
      streamingLivePeak p ≤ 8 ∧
        coordinatePairAccumulator L = [] ∧
          IsDecomp (0 : Tensor ℚ 1 2 2) (coordinatePairAccumulator L) := by
  dsimp only
  let L : Decomp ℚ 1 2 2 :=
    [((fun _ => 1), ![2, 3], ![4, 5]),
     ((fun _ => -1), ![2, 3], ![4, 5])]
  have hacc : coordinateAccumulator L = 0 := by
    funext j l i
    fin_cases j <;> fin_cases l <;> fin_cases i <;>
      norm_num [L, coordinateAccumulator, triadCoordinate]
  have hend : coordinatePairAccumulator L = [] := by
    simp [coordinatePairAccumulator, hacc]
  have hL : IsDecomp (0 : Tensor ℚ 1 2 2) L := by
    change decompSum L = 0
    funext i j l
    simp only [Pi.zero_apply]
    dsimp [L, decompSum, triad]
    ring
  obtain ⟨p, hp, hexact⟩ := streamingCanonicalization hL
  exact ⟨p, by simpa [L] using hp, hend, hexact⟩

#check @exists_streamingPath_coordinatePairAccumulator
#check @StreamingStep.decompSum_eq
#check @StreamingPath.decompSum_eq
#check @streamingCanonicalization

#print axioms exists_streamingPath_coordinatePairAccumulator
#print axioms StreamingStep.decompSum_eq
#print axioms StreamingPath.decompSum_eq
#print axioms streamingCanonicalization

end BilinearComplexity
