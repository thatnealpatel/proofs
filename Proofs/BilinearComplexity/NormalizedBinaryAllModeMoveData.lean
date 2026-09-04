import BilinearComplexity.NormalizedBinaryAllModeMoveTransport

set_option autoImplicit false

/-!
# Executable fixed-profile all-mode move witnesses

This module gives a finite, data-bearing witness for a normalized binary
`AllModeMove` at a fixed target profile.  Each witness stores an orientation
and one explicitly directed source operation at the canonical profile obtained
from `inversePermProfile`.  Successful deterministic replay is proved sound for
the existing relational `AllModeMove` semantics.

The heterogeneous `ReplayRow` wrapper permits rows at different fixed profiles
to coexist in one list or array.  This module does not enumerate relation
orbits, claim completeness of the witness format, or introduce a second
coordinate-native move semantics.

AI disclosure: produced with AI assistance (see `README`).
-/

namespace BilinearComplexity.NormalizedBinaryAllModeMoveData

open BinaryCircuit
open NormalizedBinaryCarrier
open NormalizedBinaryReplay221
open NormalizedBinaryModePermutation
open NormalizedBinaryAllModeMove
open NormalizedBinaryAllModeMoveTransport
open Scheme.Action

private abbrev stateDecidableEq (q : Profile) : DecidableEq (State q) :=
  @Finset.decidableEq (Carrier q) inferInstance

local instance (q : Profile) : DecidableEq (State q) :=
  stateDecidableEq q

/-- Finite source-coordinate data selecting one explicitly directed operation. -/
inductive SourceMoveData (p : Profile) where
  /-- A generated Split carrying its one source and two outputs. -/
  | split (source outputLeft outputRight : Carrier p)
  /-- A Flip carrying its ordered source pair and ordered target pair. -/
  | flip (sourceLeft sourceRight targetLeft targetRight : Carrier p)
  /-- A directed Reduction carrying its ordered source pair and one target. -/
  | reduction (sourceLeft sourceRight target : Carrier p)
  deriving DecidableEq

/-- Apply the exact finite-set replacement selected by source operation data. -/
def SourceMoveData.target {p : Profile} (m : SourceMoveData p)
    (D : State p) : State p :=
  match m with
  | .split source outputLeft outputRight =>
      insert outputLeft (insert outputRight (D.erase source))
  | .flip sourceLeft sourceRight targetLeft targetRight =>
      insert targetLeft
        (insert targetRight ((D.erase sourceLeft).erase sourceRight))
  | .reduction sourceLeft sourceRight target =>
      insert target ((D.erase sourceLeft).erase sourceRight)

/-- The existing source operation predicate specialized to the state computed
by `SourceMoveData.target`. -/
def SourceMoveData.Legal {p : Profile} (m : SourceMoveData p)
    (D : State p) : Prop :=
  match m with
  | .split source outputLeft outputRight =>
      GeneratedFirstSplit source outputLeft outputRight D
        (insert outputLeft (insert outputRight (D.erase source)))
  | .flip sourceLeft sourceRight targetLeft targetRight =>
      SourceThirdFlip sourceLeft sourceRight targetLeft targetRight D
        (insert targetLeft
          (insert targetRight ((D.erase sourceLeft).erase sourceRight)))
  | .reduction sourceLeft sourceRight target =>
      DirectedNarrowPairReduction sourceLeft sourceRight target D
        (insert target ((D.erase sourceLeft).erase sourceRight))

set_option synthInstance.maxSize 2048 in
/-- Source operation legality is executable using only finite equality,
membership, and coordinate checks. -/
instance SourceMoveData.instDecidableLegal {p : Profile}
    (m : SourceMoveData p) (D : State p) : Decidable (m.Legal D) := by
  cases m <;>
    simp only [SourceMoveData.Legal, GeneratedFirstSplit, SourceThirdFlip,
      DirectedNarrowPairReduction] <;>
    infer_instance

/-- Legal source data constructs the corresponding old ordered move without
changing the operation tag or its direction. -/
theorem SourceMoveData.toMove {p : Profile} (m : SourceMoveData p)
    (D : State p) (h : m.Legal D) : @Move p D (m.target D) := by
  cases m with
  | split _ _ _ => exact .generatedFirstSplit h
  | flip _ _ _ _ => exact .sourceThirdFlip h
  | reduction _ _ _ => exact .directedNarrowPairReduction h

/-- Check and execute one source-coordinate move, returning `none` exactly when
its supplied operation data are illegal at the input state. -/
def SourceMoveData.step? {p : Profile} (m : SourceMoveData p)
    (D : State p) : Option (State p) :=
  if m.Legal D then some (m.target D) else none

/-- Legal source data execute to their computed target. -/
theorem SourceMoveData.step?_eq_some {p : Profile} (m : SourceMoveData p)
    (D : State p) (h : m.Legal D) : m.step? D = some (m.target D) := by
  simp only [SourceMoveData.step?, h, if_true]

/-- Successful source execution constructs the corresponding old ordered
`Move`. -/
theorem SourceMoveData.step?_sound {p : Profile} (m : SourceMoveData p)
    {D E : State p} (h : m.step? D = some E) : @Move p D E := by
  simp only [SourceMoveData.step?] at h
  split at h
  next hlegal =>
    have htarget : m.target D = E := Option.some.inj h
    rw [← htarget]
    exact m.toMove D hlegal
  next => contradiction

/-- Reordering a profile and then applying the inverse orientation recovers the
original ordered profile. -/
theorem inversePermProfile_permProfile (o : Orientation) (p : Profile) :
    inversePermProfile o (permProfile o p) = p := by
  cases o <;> cases p <;> rfl

/-- Reorder one fixed target-coordinate term back to the canonical source
profile for an orientation. -/
def inversePermuteTerm {q : Profile} (o : Orientation) (t : Carrier q) :
    Carrier (inversePermProfile o q) :=
  match o with
  | .abc => (t.1, t.2.1, t.2.2)
  | .bca => (t.2.2, t.1, t.2.1)
  | .cab => (t.2.1, t.2.2, t.1)
  | .acb => (t.1, t.2.2, t.2.1)
  | .cba => (t.2.2, t.2.1, t.1)
  | .bac => (t.2.1, t.1, t.2.2)

/-- Pulling a permuted source term back through the same orientation recovers
the source term, after the displayed profile cast. -/
@[simp] theorem inversePermuteTerm_permuteTerm {p : Profile}
    (o : Orientation) (t : Carrier p) :
    cast (congrArg Carrier (inversePermProfile_permProfile o p))
      (inversePermuteTerm o (permuteTerm o t)) = t := by
  cases o <;> cases p <;> rcases t with ⟨t₁, t₂, t₃⟩ <;> rfl

/-- Permuting an inverse-permuted target term recovers the target term, after
the displayed recovered-profile cast. -/
@[simp] theorem cast_permuteTerm_inversePermuteTerm {q : Profile}
    (o : Orientation) (t : Carrier q) :
    cast (congrArg Carrier (permProfile_inversePermProfile o q))
      (permuteTerm o (inversePermuteTerm o t)) = t := by
  cases o <;> cases q <;> rcases t with ⟨t₁, t₂, t₃⟩ <;> rfl

/-- Permuting carrier terms by an orientation is injective. -/
theorem permuteTerm_injective {p : Profile} (o : Orientation) :
    Function.Injective (@permuteTerm p o) := by
  intro left right heq
  have hpull := congrArg
    (fun t => cast
      (congrArg Carrier (inversePermProfile_permProfile o p))
      (inversePermuteTerm o t)) heq
  simpa only [inversePermuteTerm_permuteTerm] using hpull

/-- The identity orientation pulls every term back unchanged. -/
@[simp] theorem inversePermuteTerm_abc {q : Profile} (t : Carrier q) :
    inversePermuteTerm .abc t = t := by
  rcases q with ⟨a, b, c⟩
  rcases t with ⟨t₁, t₂, t₃⟩
  rfl

/-- Reorder a fixed target-coordinate state back to the canonical source
profile for an orientation. -/
def inversePermuteState {q : Profile} (o : Orientation) (D : State q) :
    State (inversePermProfile o q) :=
  D.image (inversePermuteTerm o)

/-- Permute a canonical source-coordinate state into its fixed target profile. -/
def forwardState {q : Profile} (o : Orientation)
    (D : State (inversePermProfile o q)) : State q :=
  cast (congrArg State (permProfile_inversePermProfile o q))
    (permuteState o D)

/-- Permuting source states by an orientation is injective. -/
theorem permuteState_injective {p : Profile} (o : Orientation) :
    Function.Injective (@permuteState p o) :=
  Finset.image_injective (permuteTerm_injective o)

/-- Pulling a fixed-profile target state back and then pushing it forward is
the identity. -/
@[simp] theorem forwardState_inversePermuteState {q : Profile}
    (o : Orientation) (D : State q) :
    forwardState o (inversePermuteState o D) = D := by
  cases o <;> rcases q with ⟨a, b, c⟩ <;>
    simp only [forwardState, inversePermuteState, permuteState,
      Finset.image_image]
  all_goals
    change Finset.image (fun t => t) D = D
    exact Finset.image_id

/-- The identity orientation pulls every state back unchanged. -/
@[simp] theorem inversePermuteState_abc {q : Profile} (D : State q) :
    inversePermuteState .abc D = D := by
  rcases q with ⟨a, b, c⟩
  simp only [inversePermuteState]
  change Finset.image (fun t => t) D = D
  exact Finset.image_id

/-- The identity orientation pushes every state forward unchanged. -/
@[simp] theorem forwardState_abc {q : Profile} (D : State q) :
    forwardState .abc D = D := by
  calc
    forwardState .abc D =
        forwardState .abc (inversePermuteState .abc D) := by
      rw [inversePermuteState_abc]
    _ = D := forwardState_inversePermuteState .abc D

/-- Casting a state forward along a profile equality and back along its
symmetry recovers the original state. -/
@[simp] theorem cast_state_symm_cast {p q : Profile} (h : p = q)
    (D : State p) :
    cast (congrArg State h.symm) (cast (congrArg State h) D) = D := by
  subst q
  rfl

/-- Pushing canonical source states to a fixed target profile is injective. -/
theorem forwardState_injective {q : Profile} (o : Orientation) :
    Function.Injective (@forwardState q o) := by
  intro left right heq
  have hpull := congrArg
    (fun D : State q =>
      cast (congrArg State (permProfile_inversePermProfile o q).symm) D) heq
  simp only [forwardState,
    cast_state_symm_cast (permProfile_inversePermProfile o q)] at hpull
  exact permuteState_injective o hpull

/-- Pushing a canonical source state forward and then pulling it back recovers
the source state. -/
@[simp] theorem inversePermuteState_forwardState {q : Profile}
    (o : Orientation) (D : State (inversePermProfile o q)) :
    inversePermuteState o (forwardState o D) = D := by
  apply forwardState_injective o
  simp only [forwardState_inversePermuteState]

/-- Pushing an old ordered source move into a fixed target profile constructs
an `AllModeMove` with the same orientation and operation direction. -/
theorem allModeMove_forwardState {q : Profile} (o : Orientation)
    {D E : State (inversePermProfile o q)}
    (h : @Move (inversePermProfile o q) D E) :
    @AllModeMove q (forwardState o D) (forwardState o E) := by
  refine ⟨inversePermProfile o q, o, permProfile_inversePermProfile o q, ?_⟩
  change @OrientationMove (inversePermProfile o q) o
    (cast (congrArg State (permProfile_inversePermProfile o q).symm)
      (cast (congrArg State (permProfile_inversePermProfile o q))
        (permuteState o D)))
    (cast (congrArg State (permProfile_inversePermProfile o q).symm)
      (cast (congrArg State (permProfile_inversePermProfile o q))
        (permuteState o E)))
  rw [cast_state_symm_cast (permProfile_inversePermProfile o q)
      (permuteState o D),
    cast_state_symm_cast (permProfile_inversePermProfile o q)
      (permuteState o E)]
  exact permuteMove o h

/-- Executable witness data for one all-mode edge at a fixed target profile. -/
structure FixedMoveData (q : Profile) where
  orientation : Orientation
  sourceMove : SourceMoveData (inversePermProfile orientation q)
  deriving DecidableEq

/-- Check and execute one fixed-profile all-mode witness deterministically. -/
def FixedMoveData.step? {q : Profile} (w : FixedMoveData q)
    (D : State q) : Option (State q) :=
  (w.sourceMove.step? (inversePermuteState w.orientation D)).map
    (forwardState w.orientation)

/-- A legal fixed-profile witness executes to the forward image of its computed
source target. -/
theorem FixedMoveData.step?_eq_some_of_legal {q : Profile}
    (w : FixedMoveData q) (D : State q)
    (h : w.sourceMove.Legal (inversePermuteState w.orientation D)) :
    w.step? D = some
      (forwardState w.orientation
        (w.sourceMove.target (inversePermuteState w.orientation D))) := by
  simp only [FixedMoveData.step?, SourceMoveData.step?_eq_some _ _ h,
    Option.map_some]

/-- Successful fixed-profile execution constructs the existing relational
`AllModeMove`. -/
theorem FixedMoveData.step?_sound {q : Profile} (w : FixedMoveData q)
    {D E : State q} (h : w.step? D = some E) : @AllModeMove q D E := by
  rcases w with ⟨o, m⟩
  simp only [FixedMoveData.step?] at h
  generalize hsource : m.step? (inversePermuteState o D) = result at h
  cases result with
  | none => simp only [Option.map_none, reduceCtorEq] at h
  | some E₀ =>
      simp only [Option.map_some, Option.some.injEq] at h
      have hmove : @Move (inversePermProfile o q)
          (inversePermuteState o D) E₀ := m.step?_sound hsource
      have hedge := allModeMove_forwardState o hmove
      simp only [forwardState_inversePermuteState] at hedge
      rw [← h]
      exact hedge

/-- Execute a list of fixed-profile witnesses, failing at the first illegal
step and otherwise returning the final state. -/
def run? {q : Profile} (D : State q) :
    List (FixedMoveData q) → Option (State q)
  | [] => some D
  | w :: ws => (w.step? D).bind fun E => run? E ws

/-- Concatenating concrete paths adds their exact edge lengths. -/
theorem movePath_trans_length {q : Profile}
    {R : State q → State q → Prop} {D E F : State q}
    (path : MovePath R D E) (tail : MovePath R E F) :
    (path.trans tail).length = path.length + tail.length := by
  induction tail with
  | singleton => simp only [MovePath.trans, MovePath.length, Nat.add_zero]
  | snoc tail _ ih =>
      simp only [MovePath.trans, MovePath.length]
      rw [ih, Nat.add_assoc]

private def run?_cert {q : Profile} {D E : State q}
    {ws : List (FixedMoveData q)} (h : run? D ws = some E) :
    {path : MovePath (@AllModeMove q) D E // path.length = ws.length} := by
  induction ws generalizing D E with
  | nil =>
      simp only [run?, Option.some.injEq] at h
      rw [h]
      exact ⟨.singleton E, by simp only [MovePath.length, List.length_nil]⟩
  | cons w ws ih =>
      simp only [run?] at h
      generalize hstep : w.step? D = result at h
      cases result with
      | none => simp only [Option.bind_none, reduceCtorEq] at h
      | some D' =>
          simp only [Option.bind_some] at h
          let first := MovePath.one (w.step?_sound hstep)
          let rest := ih h
          refine ⟨first.trans rest.1, ?_⟩
          rw [movePath_trans_length, rest.2]
          simp only [first, MovePath.one, MovePath.length, List.length_cons,
            zero_add]
          omega

/-- Successful list execution constructs a concrete dependent `MovePath` in
the existing all-mode relation. -/
def run?_path {q : Profile} {D E : State q}
    {ws : List (FixedMoveData q)} (h : run? D ws = some E) :
    MovePath (@AllModeMove q) D E :=
  (run?_cert h).1

/-- The path compiled from a successful list has exactly one edge per witness. -/
@[simp] theorem run?_path_length {q : Profile} {D E : State q}
    {ws : List (FixedMoveData q)} (h : run? D ws = some E) :
    (run?_path h).length = ws.length :=
  (run?_cert h).2

/-- A heterogeneous replay row stores both directed witness lists at its own
fixed profile.  Rows at different profiles may inhabit one ordinary list or
array of `ReplayRow`. -/
structure ReplayRow where
  profile : Profile
  start : State profile
  finish : State profile
  forward : List (FixedMoveData profile)
  reverse : List (FixedMoveData profile)

/-- A row passes when both directed lists execute to their declared opposite
endpoints. -/
def ReplayRow.Passes (r : ReplayRow) : Prop :=
  run? r.start r.forward = some r.finish ∧
    run? r.finish r.reverse = some r.start

/-- Whether both exact endpoint runs of a heterogeneous replay row succeed is
decidable by finite computation. -/
instance ReplayRow.instDecidablePasses (r : ReplayRow) :
    Decidable r.Passes := by
  simp only [ReplayRow.Passes]
  infer_instance

/-- Boolean reflection of exact forward and reverse endpoint replay. -/
def ReplayRow.passes (r : ReplayRow) : Bool :=
  decide r.Passes

/-- The Boolean row checker is true exactly when both endpoint equations hold. -/
@[simp] theorem ReplayRow.passes_eq_true_iff (r : ReplayRow) :
    r.passes = true ↔ r.Passes := by
  simp only [ReplayRow.passes, decide_eq_true_eq]

/-- Construct both directed dependent paths from proof that a row passes. -/
def ReplayRow.toPaths (r : ReplayRow) (h : r.Passes) :
    MovePath (@AllModeMove r.profile) r.start r.finish ×
      MovePath (@AllModeMove r.profile) r.finish r.start :=
  ⟨run?_path h.1, run?_path h.2⟩

/-- A true Boolean row check supplies nonempty types of forward and reverse
paths in the existing all-mode relation. -/
theorem ReplayRow.passes_sound (r : ReplayRow) (h : r.passes = true) :
    Nonempty (MovePath (@AllModeMove r.profile) r.start r.finish) ∧
      Nonempty (MovePath (@AllModeMove r.profile) r.finish r.start) := by
  have hpasses : r.Passes := (r.passes_eq_true_iff).mp h
  let paths := r.toPaths hpasses
  exact ⟨⟨paths.1⟩, ⟨paths.2⟩⟩

/-- The designated identity-oriented Split witness from `S0` to `S1`. -/
def forwardSplitMoveData221 : FixedMoveData profile221 :=
  ⟨.abc, .split (inversePermuteTerm .abc E11)
    (inversePermuteTerm .abc E21) (inversePermuteTerm .abc E31)⟩

/-- The designated identity-oriented forward Flip witness from `S1` to `S2`. -/
def forwardFlipMoveData221 : FixedMoveData profile221 :=
  ⟨.abc, .flip (inversePermuteTerm .abc E22)
    (inversePermuteTerm .abc E31) (inversePermuteTerm .abc E12)
    (inversePermuteTerm .abc J)⟩

/-- The designated identity-oriented reverse Flip witness from `S2` to `S1`. -/
def reverseFlipMoveData221 : FixedMoveData profile221 :=
  ⟨.abc, .flip (inversePermuteTerm .abc E12)
    (inversePermuteTerm .abc J) (inversePermuteTerm .abc E22)
    (inversePermuteTerm .abc E31)⟩

/-- The designated identity-oriented directed Reduction witness from `S1` to
`S0`. -/
def reverseReductionMoveData221 : FixedMoveData profile221 :=
  ⟨.abc, .reduction (inversePermuteTerm .abc E21)
    (inversePermuteTerm .abc E31) (inversePermuteTerm .abc E11)⟩

/-- Existing profile-`221` forward operation data: Split followed by Flip. -/
def forwardMoveData221 : List (FixedMoveData profile221) :=
  [forwardSplitMoveData221, forwardFlipMoveData221]

/-- Existing profile-`221` reverse operation data: reverse Flip followed by the
directed two-to-one Reduction; the forward Split is not reversed as a Split. -/
def reverseMoveData221 : List (FixedMoveData profile221) :=
  [reverseFlipMoveData221, reverseReductionMoveData221]

/-- The designated source Split data compute the existing intermediate state. -/
theorem forwardSplitData221_target :
    SourceMoveData.target (.split E11 E21 E31) S0 = S1 := by
  decide

/-- The designated source Flip data compute the existing forward endpoint. -/
theorem forwardFlipData221_target :
    SourceMoveData.target (.flip E22 E31 E12 J) S1 = S2 := by
  decide

/-- The designated reverse Flip data compute the existing intermediate state. -/
theorem reverseFlipData221_target :
    SourceMoveData.target (.flip E12 J E22 E31) S2 = S1 := by
  decide

/-- The designated directed Reduction data compute the existing reverse
endpoint. -/
theorem reverseReductionData221_target :
    SourceMoveData.target (.reduction E21 E31 E11) S1 = S0 := by
  decide

/-- The fixed identity-oriented designated Split executes from `S0` to `S1`. -/
theorem step_forwardSplitMoveData221 :
    forwardSplitMoveData221.step? S0 = some S1 := by
  unfold FixedMoveData.step? forwardSplitMoveData221
  let m : SourceMoveData (inversePermProfile .abc profile221) :=
    .split (inversePermuteTerm .abc E11) (inversePermuteTerm .abc E21)
      (inversePermuteTerm .abc E31)
  change Option.map (@forwardState profile221 .abc)
    (m.step? (inversePermuteState .abc S0)) = some S1
  have hlegal : m.Legal (inversePermuteState .abc S0) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .abc S0) =
      inversePermuteState .abc S1 := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- The fixed identity-oriented designated forward Flip executes from `S1` to
`S2`. -/
theorem step_forwardFlipMoveData221 :
    forwardFlipMoveData221.step? S1 = some S2 := by
  unfold FixedMoveData.step? forwardFlipMoveData221
  let m : SourceMoveData (inversePermProfile .abc profile221) :=
    .flip (inversePermuteTerm .abc E22) (inversePermuteTerm .abc E31)
      (inversePermuteTerm .abc E12) (inversePermuteTerm .abc J)
  change Option.map (@forwardState profile221 .abc)
    (m.step? (inversePermuteState .abc S1)) = some S2
  have hlegal : m.Legal (inversePermuteState .abc S1) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .abc S1) =
      inversePermuteState .abc S2 := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- The fixed identity-oriented designated reverse Flip executes from `S2` to
`S1`. -/
theorem step_reverseFlipMoveData221 :
    reverseFlipMoveData221.step? S2 = some S1 := by
  unfold FixedMoveData.step? reverseFlipMoveData221
  let m : SourceMoveData (inversePermProfile .abc profile221) :=
    .flip (inversePermuteTerm .abc E12) (inversePermuteTerm .abc J)
      (inversePermuteTerm .abc E22) (inversePermuteTerm .abc E31)
  change Option.map (@forwardState profile221 .abc)
    (m.step? (inversePermuteState .abc S2)) = some S1
  have hlegal : m.Legal (inversePermuteState .abc S2) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .abc S2) =
      inversePermuteState .abc S1 := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- The fixed identity-oriented directed Reduction executes from `S1` to
`S0`; it is the second reverse operation and is not a reversed Split. -/
theorem step_reverseReductionMoveData221 :
    reverseReductionMoveData221.step? S1 = some S0 := by
  unfold FixedMoveData.step? reverseReductionMoveData221
  let m : SourceMoveData (inversePermProfile .abc profile221) :=
    .reduction (inversePermuteTerm .abc E21) (inversePermuteTerm .abc E31)
      (inversePermuteTerm .abc E11)
  change Option.map (@forwardState profile221 .abc)
    (m.step? (inversePermuteState .abc S1)) = some S0
  have hlegal : m.Legal (inversePermuteState .abc S1) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .abc S1) =
      inversePermuteState .abc S0 := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- The executable profile-`221` forward witness list reaches `S2` from `S0`. -/
theorem run_forwardMoveData221 :
    run? S0 forwardMoveData221 = some S2 := by
  simp only [forwardMoveData221, run?, step_forwardSplitMoveData221,
    Option.bind_some, step_forwardFlipMoveData221]

/-- The executable profile-`221` reverse witness list reaches `S0` from `S2`. -/
theorem run_reverseMoveData221 :
    run? S2 reverseMoveData221 = some S0 := by
  simp only [reverseMoveData221, run?, step_reverseFlipMoveData221,
    Option.bind_some, step_reverseReductionMoveData221]

/-- Concrete all-mode path compiled from the designated forward witness list. -/
def forwardMoveDataPath221 :
    MovePath (@AllModeMove profile221) S0 S2 :=
  run?_path run_forwardMoveData221

/-- Concrete all-mode path compiled from the designated reverse witness list. -/
def reverseMoveDataPath221 :
    MovePath (@AllModeMove profile221) S2 S0 :=
  run?_path run_reverseMoveData221

/-- The compiled forward witness path has two explicitly directed edges. -/
@[simp] theorem forwardMoveDataPath221_length :
    forwardMoveDataPath221.length = 2 := by
  rw [forwardMoveDataPath221, run?_path_length]
  rfl

/-- The compiled reverse witness path has a Flip and then a directed Reduction,
so it also has exactly two edges. -/
@[simp] theorem reverseMoveDataPath221_length :
    reverseMoveDataPath221.length = 2 := by
  rw [reverseMoveDataPath221, run?_path_length]
  rfl

/-- The designated executable forward and reverse lists jointly provide paths
in their stated directions and both have length two. -/
theorem moveData221_regression :
    Nonempty (MovePath (@AllModeMove profile221) S0 S2) ∧
      Nonempty (MovePath (@AllModeMove profile221) S2 S0) ∧
      forwardMoveDataPath221.length = 2 ∧
      reverseMoveDataPath221.length = 2 := by
  exact ⟨⟨forwardMoveDataPath221⟩, ⟨reverseMoveDataPath221⟩,
    forwardMoveDataPath221_length, reverseMoveDataPath221_length⟩

example : forwardMoveData221.length = 2 := rfl
example : reverseMoveData221.length = 2 := rfl
example : SourceMoveData.target (.split E11 E21 E31) S0 = S1 := by decide

#eval (run? S0 forwardMoveData221).isSome
#eval (run? S2 reverseMoveData221).isSome

#check @SourceMoveData
#check @FixedMoveData
#check @FixedMoveData.step?_sound
#check @run?_path
#check @ReplayRow
#check @ReplayRow.toPaths
#check @run_forwardMoveData221
#check @run_reverseMoveData221
#print axioms FixedMoveData.step?_sound
#print axioms run?_path
#print axioms ReplayRow.passes_sound
#print axioms run_forwardMoveData221
#print axioms run_reverseMoveData221
#print axioms moveData221_regression

end BilinearComplexity.NormalizedBinaryAllModeMoveData
