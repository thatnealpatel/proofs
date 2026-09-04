import BilinearComplexity.NormalizedBinaryAllModeMoveData
import BilinearComplexity.NormalizedBinaryFiveCircuitCertificate
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.FinCases

set_option autoImplicit false

/-!
# Kernel-replayed computationally selected binary five-circuit rows

The JSON file with schema version 2 and SHA-256
`c6c7ee94f2ac23ea26aa51efa63aa565e6b3f2e520f019db3af488af85457a88`,
produced by the generator whose SHA-256 is
`9886023058028d284bccfe66b022dbeb0beb03da2fae5234e5e495bad7bf7b68`,
supplied only candidate literals for this module.  The generated Lean literals below
are self-contained: this module has no runtime dependency on either external file.
Every sound fact is checked by the Lean kernel through exact directed move replay.

The thirteen rows are described only as computationally selected and replayed rows.
No orbit, stabilizer, census, coverage, canonicality, or shortestness claim is made.
Because every endpoint union is proved to span its normalized ambient factor spaces,
the certificate confinement fields follow from these exact-profile proofs; they
are not independent computations over the intermediate vertices.

AI disclosure: produced with AI assistance (see `README`).
-/

namespace BilinearComplexity.NormalizedBinaryFiveCircuitRows

open BinaryCircuit
open NormalizedBinaryCarrier
open NormalizedBinaryReplay221
open NormalizedBinaryModePermutation
open NormalizedBinaryAllModeMove
open NormalizedBinaryAllModeMoveTransport
open NormalizedBinaryAllModeMoveData
open NormalizedBinaryFiveCircuitCertificate

/-- The bit-mask coordinate vector in dimension `d`; the proof argument rejects every mask with a high bit. -/
abbrev coordinateVectorOfMask (d mask : ℕ)
    (_hbound : mask < 2 ^ d) : CoordinateVector d :=
  fun i => if mask.testBit i then 1 else 0

/-- A positive in-range bit mask gives a nonzero coordinate vector. -/
theorem coordinateVectorOfMask_ne_zero (d mask : ℕ)
    (hpos : 0 < mask) (hbound : mask < 2 ^ d) :
    coordinateVectorOfMask d mask hbound ≠ 0 := by
  obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero (Nat.ne_of_gt hpos)
  have hid : i < d := by
    by_contra hnot
    have hdi : d ≤ i := Nat.le_of_not_gt hnot
    have hpow : 2 ^ d ≤ 2 ^ i :=
      Nat.pow_le_pow_right (n := 2) (by omega) hdi
    have hmask : 2 ^ i ≤ mask := Nat.ge_two_pow_of_testBit hi
    omega
  intro hzero
  have hat := congrFun hzero ⟨i, hid⟩
  simp only [coordinateVectorOfMask, hi, if_true, Pi.zero_apply,
    one_ne_zero] at hat

/-- The normalized nonzero factor represented by a positive in-range bit mask; its two proof arguments reject zero and high bits. -/
abbrev nonzeroFactorOfMask (d mask : ℕ) (hpos : 0 < mask)
    (hbound : mask < 2 ^ d) : NonzeroVector d :=
  ⟨coordinateVectorOfMask d mask hbound,
    coordinateVectorOfMask_ne_zero d mask hpos hbound⟩

/-- The normalized carrier term represented by three positive bit masks, each checked against its profile dimension. -/
abbrev carrierOfMasks (p : Profile) (a b c : ℕ)
    (haPos : 0 < a) (haBound : a < 2 ^ p.first)
    (hbPos : 0 < b) (hbBound : b < 2 ^ p.second)
    (hcPos : 0 < c) (hcBound : c < 2 ^ p.third) : Carrier p :=
  (nonzeroFactorOfMask p.first a haPos haBound,
    nonzeroFactorOfMask p.second b hbPos hbBound,
    nonzeroFactorOfMask p.third c hcPos hcBound)

local macro "maskTerm(" p:term "," a:num "," b:num "," c:num ")" : term =>
  `(carrierOfMasks $p $a $b $c (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide))

example : coordinateVectorOfMask 2 1 (by decide) = ![1, 0] := by decide
example : (nonzeroFactorOfMask 2 2 (by decide) (by decide)).1 = ![0, 1] := by decide
example :
    (carrierOfMasks profile221 3 2 1 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).1.1 (0 : Fin 2) = 1 := by
  decide

/-- An all-mode edge changes endpoint cardinality by at most one in either direction. -/
theorem AllModeMove.card_bounds {q : Profile} {D E : State q}
    (h : @AllModeMove q D E) :
    E.card ≤ D.card + 1 ∧ D.card ≤ E.card + 1 := by
  rcases h.card_change with hchange | hchange | hchange <;> omega

/-- A path of at most three all-mode edges between endpoints of cardinality at most three has altitude at most four. -/
theorem allModeMovePath_altitude_le_four {q : Profile} {D E : State q}
    (path : MovePath (@AllModeMove q) D E)
    (hD : D.card ≤ 3) (hE : E.card ≤ 3) (hlen : path.length ≤ 3) :
    path.altitude ≤ 4 := by
  cases path with
  | singleton =>
      simp only [MovePath.altitude]
      omega
  | snoc path hlast =>
      cases path with
      | singleton =>
          have hbLast := AllModeMove.card_bounds hlast
          simp only [MovePath.altitude, max_le_iff]
          omega
      | snoc path hmiddle =>
          cases path with
          | singleton =>
              have hbMiddle := AllModeMove.card_bounds hmiddle
              have hbLast := AllModeMove.card_bounds hlast
              simp only [MovePath.altitude, max_le_iff]
              omega
          | snoc path hfirst =>
              cases path with
              | singleton =>
                  have hbFirst := AllModeMove.card_bounds hfirst
                  have hbMiddle := AllModeMove.card_bounds hmiddle
                  have hbLast := AllModeMove.card_bounds hlast
                  simp only [MovePath.altitude, max_le_iff]
                  omega
              | snoc path htooMany =>
                  simp only [MovePath.length] at hlen
                  omega

/-- An exact ambient factor profile confines every normalized state in all three factor modes. -/
theorem factorSpanConfined_of_exactFactorProfile {p : Profile}
    {K : State p} (hK : HasExactFactorProfile K) (X : State p) :
    FactorSpanConfined K X := by
  rw [FactorSpanConfined, hK.1, hK.2.1, hK.2.2]
  exact ⟨le_top, le_top, le_top⟩

/-- An exact ambient factor profile confines every actual vertex of any path. -/
theorem pathFactorSpanConfined_of_exactFactorProfile {p : Profile}
    {R : State p → State p → Prop} {D E K : State p}
    (hK : HasExactFactorProfile K) (path : MovePath R D E) :
    PathFactorSpanConfined path K := by
  intro X _hX
  exact factorSpanConfined_of_exactFactorProfile hK X

/-- A successful replay row with disjoint two-term and three-term endpoints, short witness lists, and exact endpoint factor profile yields a kernel certificate. -/
def replayRow_toFiveCircuitCertificate (r : ReplayRow)
    (hpasses : r.Passes) (hdisjoint : Disjoint r.start r.finish)
    (hstart : r.start.card = 2) (hfinish : r.finish.card = 3)
    (hforward : r.forward.length ≤ 3) (hreverse : r.reverse.length ≤ 3)
    (hexact : HasExactFactorProfile (r.start ∪ r.finish)) :
    FiveCircuitCertificate r.profile r.start r.finish where
  disjoint := hdisjoint
  card_left := hstart
  card_right := hfinish
  forward := run?_path hpasses.1
  reverse := run?_path hpasses.2
  forward_length_le := by
    rw [run?_path_length]
    exact hforward
  reverse_length_le := by
    rw [run?_path_length]
    exact hreverse
  forward_altitude_le := by
    apply allModeMovePath_altitude_le_four
    · omega
    · omega
    · rw [run?_path_length]
      exact hforward
  reverse_altitude_le := by
    apply allModeMovePath_altitude_le_four
    · omega
    · omega
    · rw [run?_path_length]
      exact hreverse
  forward_confined := pathFactorSpanConfined_of_exactFactorProfile hexact _
  reverse_confined := pathFactorSpanConfined_of_exactFactorProfile hexact _

/-- A heterogeneous certified replay row packages the concrete row and precisely the hypotheses used by `replayRow_toFiveCircuitCertificate`. -/
structure CertifiedReplayRow where
  /-- The self-contained fixed-profile replay data. -/
  row : ReplayRow
  /-- Both directed witness lists replay to the declared endpoints. -/
  passes : row.Passes
  /-- The endpoint term sets are disjoint. -/
  disjoint : Disjoint row.start row.finish
  /-- The starting endpoint has two terms. -/
  card_start : row.start.card = 2
  /-- The finishing endpoint has three terms. -/
  card_finish : row.finish.card = 3
  /-- The forward witness list has at most three entries. -/
  forward_length_le : row.forward.length ≤ 3
  /-- The reverse witness list has at most three entries. -/
  reverse_length_le : row.reverse.length ≤ 3
  /-- The endpoint union spans every ambient factor space exactly. -/
  exact_profile : HasExactFactorProfile (row.start ∪ row.finish)

/-- The kernel certificate carried by a heterogeneous certified replay row. -/
def CertifiedReplayRow.certificate (r : CertifiedReplayRow) :
    FiveCircuitCertificate r.row.profile r.row.start r.row.finish :=
  replayRow_toFiveCircuitCertificate r.row r.passes r.disjoint r.card_start
    r.card_finish r.forward_length_le r.reverse_length_le r.exact_profile

example (r : CertifiedReplayRow) :
    Nonempty (FiveCircuitCertificate r.row.profile r.row.start r.row.finish) :=
  ⟨r.certificate⟩

/-! ## Computationally selected and replayed row `221-01` -/

/-- The two-term starting state of computationally selected row `221-01`. -/
def row22101Start : State profile221 :=
  {maskTerm(profile221, 1, 1, 1),
   maskTerm(profile221, 2, 2, 1)}

/-- The three-term finishing state of computationally selected row `221-01`. -/
def row22101Finish : State profile221 :=
  {maskTerm(profile221, 1, 2, 1),
   maskTerm(profile221, 2, 1, 1),
   maskTerm(profile221, 3, 3, 1)}

/-- Target-coordinate intermediate state 1 on the forward replay of row `221-01`. -/
def row22101ForwardState1 : State profile221 :=
  {maskTerm(profile221, 1, 2, 1),
   maskTerm(profile221, 1, 3, 1),
   maskTerm(profile221, 2, 2, 1)}

/-- Target-coordinate intermediate state 1 on the reverse replay of row `221-01`. -/
def row22101ReverseState1 : State profile221 :=
  {maskTerm(profile221, 1, 2, 1),
   maskTerm(profile221, 1, 3, 1),
   maskTerm(profile221, 2, 2, 1)}

/-- The exact source-coordinate split data for forward step 1 of row `221-01`. -/
def row22101ForwardMove1 : FixedMoveData profile221 :=
  ⟨.cab, .split
      maskTerm(inversePermProfile .cab profile221, 1, 1, 1)
      maskTerm(inversePermProfile .cab profile221, 2, 1, 1)
      maskTerm(inversePermProfile .cab profile221, 3, 1, 1)⟩

/-- The exact source-coordinate flip data for forward step 2 of row `221-01`. -/
def row22101ForwardMove2 : FixedMoveData profile221 :=
  ⟨.abc, .flip
      maskTerm(inversePermProfile .abc profile221, 1, 3, 1)
      maskTerm(inversePermProfile .abc profile221, 2, 2, 1)
      maskTerm(inversePermProfile .abc profile221, 3, 3, 1)
      maskTerm(inversePermProfile .abc profile221, 2, 1, 1)⟩

/-- The exact source-coordinate flip data for reverse step 1 of row `221-01`. -/
def row22101ReverseMove1 : FixedMoveData profile221 :=
  ⟨.abc, .flip
      maskTerm(inversePermProfile .abc profile221, 3, 3, 1)
      maskTerm(inversePermProfile .abc profile221, 2, 1, 1)
      maskTerm(inversePermProfile .abc profile221, 1, 3, 1)
      maskTerm(inversePermProfile .abc profile221, 2, 2, 1)⟩

/-- The exact source-coordinate reduction data for reverse step 2 of row `221-01`. -/
def row22101ReverseMove2 : FixedMoveData profile221 :=
  ⟨.cab, .reduction
      maskTerm(inversePermProfile .cab profile221, 2, 1, 1)
      maskTerm(inversePermProfile .cab profile221, 3, 1, 1)
      maskTerm(inversePermProfile .cab profile221, 1, 1, 1)⟩

/-- Kernel replay of the directed Split at forward step 1 of row `221-01`. -/
theorem step_row22101ForwardMove1 :
    row22101ForwardMove1.step? row22101Start = some row22101ForwardState1 := by
  unfold FixedMoveData.step? row22101ForwardMove1
  let m : SourceMoveData (inversePermProfile .cab profile221) :=
    .split
          maskTerm(inversePermProfile .cab profile221, 1, 1, 1)
          maskTerm(inversePermProfile .cab profile221, 2, 1, 1)
          maskTerm(inversePermProfile .cab profile221, 3, 1, 1)
  change Option.map (@forwardState profile221 .cab)
    (m.step? (inversePermuteState .cab row22101Start)) = some row22101ForwardState1
  have hlegal : m.Legal (inversePermuteState .cab row22101Start) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .cab row22101Start) =
      inversePermuteState .cab row22101ForwardState1 := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Flip at forward step 2 of row `221-01`. -/
theorem step_row22101ForwardMove2 :
    row22101ForwardMove2.step? row22101ForwardState1 = some row22101Finish := by
  unfold FixedMoveData.step? row22101ForwardMove2
  let m : SourceMoveData (inversePermProfile .abc profile221) :=
    .flip
          maskTerm(inversePermProfile .abc profile221, 1, 3, 1)
          maskTerm(inversePermProfile .abc profile221, 2, 2, 1)
          maskTerm(inversePermProfile .abc profile221, 3, 3, 1)
          maskTerm(inversePermProfile .abc profile221, 2, 1, 1)
  change Option.map (@forwardState profile221 .abc)
    (m.step? (inversePermuteState .abc row22101ForwardState1)) = some row22101Finish
  have hlegal : m.Legal (inversePermuteState .abc row22101ForwardState1) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .abc row22101ForwardState1) =
      inversePermuteState .abc row22101Finish := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Flip at reverse step 1 of row `221-01`. -/
theorem step_row22101ReverseMove1 :
    row22101ReverseMove1.step? row22101Finish = some row22101ReverseState1 := by
  unfold FixedMoveData.step? row22101ReverseMove1
  let m : SourceMoveData (inversePermProfile .abc profile221) :=
    .flip
          maskTerm(inversePermProfile .abc profile221, 3, 3, 1)
          maskTerm(inversePermProfile .abc profile221, 2, 1, 1)
          maskTerm(inversePermProfile .abc profile221, 1, 3, 1)
          maskTerm(inversePermProfile .abc profile221, 2, 2, 1)
  change Option.map (@forwardState profile221 .abc)
    (m.step? (inversePermuteState .abc row22101Finish)) = some row22101ReverseState1
  have hlegal : m.Legal (inversePermuteState .abc row22101Finish) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .abc row22101Finish) =
      inversePermuteState .abc row22101ReverseState1 := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Reduction at reverse step 2 of row `221-01`. -/
theorem step_row22101ReverseMove2 :
    row22101ReverseMove2.step? row22101ReverseState1 = some row22101Start := by
  unfold FixedMoveData.step? row22101ReverseMove2
  let m : SourceMoveData (inversePermProfile .cab profile221) :=
    .reduction
          maskTerm(inversePermProfile .cab profile221, 2, 1, 1)
          maskTerm(inversePermProfile .cab profile221, 3, 1, 1)
          maskTerm(inversePermProfile .cab profile221, 1, 1, 1)
  change Option.map (@forwardState profile221 .cab)
    (m.step? (inversePermuteState .cab row22101ReverseState1)) = some row22101Start
  have hlegal : m.Legal (inversePermuteState .cab row22101ReverseState1) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .cab row22101ReverseState1) =
      inversePermuteState .cab row22101Start := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- The fixed directed forward witness list for row `221-01`. -/
def row22101ForwardMoves : List (FixedMoveData profile221) :=
  [row22101ForwardMove1, row22101ForwardMove2]

/-- The fixed directed reverse witness list for row `221-01`. -/
def row22101ReverseMoves : List (FixedMoveData profile221) :=
  [row22101ReverseMove1, row22101ReverseMove2]

/-- The heterogeneous raw replay data for computationally selected row `221-01`. -/
def row22101 : ReplayRow where
  profile := profile221
  start := row22101Start
  finish := row22101Finish
  forward := row22101ForwardMoves
  reverse := row22101ReverseMoves

/-- The exact forward run equation for row `221-01`. -/
theorem run_row22101ForwardMoves :
    run? row22101Start row22101ForwardMoves = some row22101Finish := by
  simp only [row22101ForwardMoves, run?, step_row22101ForwardMove1, Option.bind_some, step_row22101ForwardMove2]

/-- The exact reverse run equation for row `221-01`. -/
theorem run_row22101ReverseMoves :
    run? row22101Finish row22101ReverseMoves = some row22101Start := by
  simp only [row22101ReverseMoves, run?, step_row22101ReverseMove1, Option.bind_some, step_row22101ReverseMove2]

/-- Both exact directed runs of row `221-01` pass. -/
theorem row22101_passes : row22101.Passes := by
  simpa only [row22101, ReplayRow.Passes] using
    And.intro run_row22101ForwardMoves run_row22101ReverseMoves

/-- The actual `run?_path` data for the forward replay of row `221-01`. -/
def row22101ForwardPath :
    MovePath (@AllModeMove profile221) row22101Start row22101Finish :=
  run?_path run_row22101ForwardMoves

/-- The forward replay path of row `221-01` has exactly 2 edges. -/
@[simp] theorem row22101ForwardPath_length :
    row22101ForwardPath.length = 2 := by
  rw [row22101ForwardPath, run?_path_length]
  rfl

/-- The actual `run?_path` data for the reverse replay of row `221-01`. -/
def row22101ReversePath :
    MovePath (@AllModeMove profile221) row22101Finish row22101Start :=
  run?_path run_row22101ReverseMoves

/-- The reverse replay path of row `221-01` has exactly 2 edges. -/
@[simp] theorem row22101ReversePath_length :
    row22101ReversePath.length = 2 := by
  rw [row22101ReversePath, run?_path_length]
  rfl

/-- Both actual replay paths of row `221-01` have at most three edges. -/
theorem row22101_path_lengths_le_three :
    row22101ForwardPath.length ≤ 3 ∧ row22101ReversePath.length ≤ 3 := by
  rw [row22101ForwardPath_length, row22101ReversePath_length]
  omega

/-- The endpoint states of row `221-01` are disjoint. -/
theorem row22101_disjoint : Disjoint row22101Start row22101Finish := by
  decide

/-- The starting state of row `221-01` has exactly two terms. -/
theorem row22101_card_start : row22101Start.card = 2 := by
  decide

/-- The finishing state of row `221-01` has exactly three terms. -/
theorem row22101_card_finish : row22101Finish.card = 3 := by
  decide

/-- The visible standard-basis masks in the endpoint union of row `221-01` prove its exact factor profile. -/
theorem row22101_exactFactorProfile :
    HasExactFactorProfile (row22101Start ∪ row22101Finish) := by
  constructor
  · unfold firstFactorSpan
    apply (Submodule.eq_top_iff_forall_basis_mem
      (Pi.basisFun F2 (Fin profile221.first))).mpr
    intro i
    rw [Pi.basisFun_apply]
    apply Submodule.subset_span
    fin_cases i <;> decide
  constructor
  · unfold secondFactorSpan
    apply (Submodule.eq_top_iff_forall_basis_mem
      (Pi.basisFun F2 (Fin profile221.second))).mpr
    intro i
    rw [Pi.basisFun_apply]
    apply Submodule.subset_span
    fin_cases i <;> decide
  · unfold thirdFactorSpan
    apply (Submodule.eq_top_iff_forall_basis_mem
      (Pi.basisFun F2 (Fin profile221.third))).mpr
    intro i
    rw [Pi.basisFun_apply]
    apply Submodule.subset_span
    fin_cases i
    decide

/-- The kernel-replayed five-circuit certificate for row `221-01`. -/
def row22101Certificate :
    FiveCircuitCertificate profile221 row22101Start row22101Finish := by
  let cert := replayRow_toFiveCircuitCertificate row22101 row22101_passes
    (by change Disjoint row22101Start row22101Finish; exact row22101_disjoint)
    (by change row22101Start.card = 2; exact row22101_card_start)
    (by change row22101Finish.card = 3; exact row22101_card_finish)
    (by simp only [row22101, row22101ForwardMoves, List.length_cons,
      List.length_nil]; omega)
    (by simp only [row22101, row22101ReverseMoves, List.length_cons,
      List.length_nil]; omega)
    (by
      change HasExactFactorProfile (row22101Start ∪ row22101Finish)
      exact row22101_exactFactorProfile)
  change FiveCircuitCertificate profile221 row22101Start row22101Finish at cert
  exact cert

/-- The heterogeneous certified wrapper for computationally selected row `221-01`. -/
def certified22101 : CertifiedReplayRow where
  row := row22101
  passes := row22101_passes
  disjoint := by change Disjoint row22101Start row22101Finish; exact row22101_disjoint
  card_start := by change row22101Start.card = 2; exact row22101_card_start
  card_finish := by change row22101Finish.card = 3; exact row22101_card_finish
  forward_length_le := by simp only [row22101, row22101ForwardMoves, List.length_cons, List.length_nil]; omega
  reverse_length_le := by simp only [row22101, row22101ReverseMoves, List.length_cons, List.length_nil]; omega
  exact_profile := by
    change HasExactFactorProfile (row22101Start ∪ row22101Finish)
    exact row22101_exactFactorProfile

/-! ## Computationally selected and replayed row `221-02` -/

/-- The two-term starting state of computationally selected row `221-02`. -/
def row22102Start : State profile221 :=
  {maskTerm(profile221, 1, 1, 1),
   maskTerm(profile221, 1, 2, 1)}

/-- The three-term finishing state of computationally selected row `221-02`. -/
def row22102Finish : State profile221 :=
  {maskTerm(profile221, 2, 1, 1),
   maskTerm(profile221, 2, 2, 1),
   maskTerm(profile221, 3, 3, 1)}

/-- Target-coordinate intermediate state 1 on the forward replay of row `221-02`. -/
def row22102ForwardState1 : State profile221 :=
  {maskTerm(profile221, 1, 2, 1),
   maskTerm(profile221, 2, 1, 1),
   maskTerm(profile221, 3, 1, 1)}

/-- Target-coordinate intermediate state 1 on the reverse replay of row `221-02`. -/
def row22102ReverseState1 : State profile221 :=
  {maskTerm(profile221, 1, 2, 1),
   maskTerm(profile221, 2, 1, 1),
   maskTerm(profile221, 3, 1, 1)}

/-- The exact source-coordinate split data for forward step 1 of row `221-02`. -/
def row22102ForwardMove1 : FixedMoveData profile221 :=
  ⟨.abc, .split
      maskTerm(inversePermProfile .abc profile221, 1, 1, 1)
      maskTerm(inversePermProfile .abc profile221, 2, 1, 1)
      maskTerm(inversePermProfile .abc profile221, 3, 1, 1)⟩

/-- The exact source-coordinate flip data for forward step 2 of row `221-02`. -/
def row22102ForwardMove2 : FixedMoveData profile221 :=
  ⟨.abc, .flip
      maskTerm(inversePermProfile .abc profile221, 1, 2, 1)
      maskTerm(inversePermProfile .abc profile221, 3, 1, 1)
      maskTerm(inversePermProfile .abc profile221, 2, 2, 1)
      maskTerm(inversePermProfile .abc profile221, 3, 3, 1)⟩

/-- The exact source-coordinate flip data for reverse step 1 of row `221-02`. -/
def row22102ReverseMove1 : FixedMoveData profile221 :=
  ⟨.abc, .flip
      maskTerm(inversePermProfile .abc profile221, 2, 2, 1)
      maskTerm(inversePermProfile .abc profile221, 3, 3, 1)
      maskTerm(inversePermProfile .abc profile221, 1, 2, 1)
      maskTerm(inversePermProfile .abc profile221, 3, 1, 1)⟩

/-- The exact source-coordinate reduction data for reverse step 2 of row `221-02`. -/
def row22102ReverseMove2 : FixedMoveData profile221 :=
  ⟨.abc, .reduction
      maskTerm(inversePermProfile .abc profile221, 2, 1, 1)
      maskTerm(inversePermProfile .abc profile221, 3, 1, 1)
      maskTerm(inversePermProfile .abc profile221, 1, 1, 1)⟩

/-- Kernel replay of the directed Split at forward step 1 of row `221-02`. -/
theorem step_row22102ForwardMove1 :
    row22102ForwardMove1.step? row22102Start = some row22102ForwardState1 := by
  unfold FixedMoveData.step? row22102ForwardMove1
  let m : SourceMoveData (inversePermProfile .abc profile221) :=
    .split
          maskTerm(inversePermProfile .abc profile221, 1, 1, 1)
          maskTerm(inversePermProfile .abc profile221, 2, 1, 1)
          maskTerm(inversePermProfile .abc profile221, 3, 1, 1)
  change Option.map (@forwardState profile221 .abc)
    (m.step? (inversePermuteState .abc row22102Start)) = some row22102ForwardState1
  have hlegal : m.Legal (inversePermuteState .abc row22102Start) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .abc row22102Start) =
      inversePermuteState .abc row22102ForwardState1 := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Flip at forward step 2 of row `221-02`. -/
theorem step_row22102ForwardMove2 :
    row22102ForwardMove2.step? row22102ForwardState1 = some row22102Finish := by
  unfold FixedMoveData.step? row22102ForwardMove2
  let m : SourceMoveData (inversePermProfile .abc profile221) :=
    .flip
          maskTerm(inversePermProfile .abc profile221, 1, 2, 1)
          maskTerm(inversePermProfile .abc profile221, 3, 1, 1)
          maskTerm(inversePermProfile .abc profile221, 2, 2, 1)
          maskTerm(inversePermProfile .abc profile221, 3, 3, 1)
  change Option.map (@forwardState profile221 .abc)
    (m.step? (inversePermuteState .abc row22102ForwardState1)) = some row22102Finish
  have hlegal : m.Legal (inversePermuteState .abc row22102ForwardState1) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .abc row22102ForwardState1) =
      inversePermuteState .abc row22102Finish := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Flip at reverse step 1 of row `221-02`. -/
theorem step_row22102ReverseMove1 :
    row22102ReverseMove1.step? row22102Finish = some row22102ReverseState1 := by
  unfold FixedMoveData.step? row22102ReverseMove1
  let m : SourceMoveData (inversePermProfile .abc profile221) :=
    .flip
          maskTerm(inversePermProfile .abc profile221, 2, 2, 1)
          maskTerm(inversePermProfile .abc profile221, 3, 3, 1)
          maskTerm(inversePermProfile .abc profile221, 1, 2, 1)
          maskTerm(inversePermProfile .abc profile221, 3, 1, 1)
  change Option.map (@forwardState profile221 .abc)
    (m.step? (inversePermuteState .abc row22102Finish)) = some row22102ReverseState1
  have hlegal : m.Legal (inversePermuteState .abc row22102Finish) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .abc row22102Finish) =
      inversePermuteState .abc row22102ReverseState1 := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Reduction at reverse step 2 of row `221-02`. -/
theorem step_row22102ReverseMove2 :
    row22102ReverseMove2.step? row22102ReverseState1 = some row22102Start := by
  unfold FixedMoveData.step? row22102ReverseMove2
  let m : SourceMoveData (inversePermProfile .abc profile221) :=
    .reduction
          maskTerm(inversePermProfile .abc profile221, 2, 1, 1)
          maskTerm(inversePermProfile .abc profile221, 3, 1, 1)
          maskTerm(inversePermProfile .abc profile221, 1, 1, 1)
  change Option.map (@forwardState profile221 .abc)
    (m.step? (inversePermuteState .abc row22102ReverseState1)) = some row22102Start
  have hlegal : m.Legal (inversePermuteState .abc row22102ReverseState1) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .abc row22102ReverseState1) =
      inversePermuteState .abc row22102Start := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- The fixed directed forward witness list for row `221-02`. -/
def row22102ForwardMoves : List (FixedMoveData profile221) :=
  [row22102ForwardMove1, row22102ForwardMove2]

/-- The fixed directed reverse witness list for row `221-02`. -/
def row22102ReverseMoves : List (FixedMoveData profile221) :=
  [row22102ReverseMove1, row22102ReverseMove2]

/-- The heterogeneous raw replay data for computationally selected row `221-02`. -/
def row22102 : ReplayRow where
  profile := profile221
  start := row22102Start
  finish := row22102Finish
  forward := row22102ForwardMoves
  reverse := row22102ReverseMoves

/-- The exact forward run equation for row `221-02`. -/
theorem run_row22102ForwardMoves :
    run? row22102Start row22102ForwardMoves = some row22102Finish := by
  simp only [row22102ForwardMoves, run?, step_row22102ForwardMove1, Option.bind_some, step_row22102ForwardMove2]

/-- The exact reverse run equation for row `221-02`. -/
theorem run_row22102ReverseMoves :
    run? row22102Finish row22102ReverseMoves = some row22102Start := by
  simp only [row22102ReverseMoves, run?, step_row22102ReverseMove1, Option.bind_some, step_row22102ReverseMove2]

/-- Both exact directed runs of row `221-02` pass. -/
theorem row22102_passes : row22102.Passes := by
  simpa only [row22102, ReplayRow.Passes] using
    And.intro run_row22102ForwardMoves run_row22102ReverseMoves

/-- The actual `run?_path` data for the forward replay of row `221-02`. -/
def row22102ForwardPath :
    MovePath (@AllModeMove profile221) row22102Start row22102Finish :=
  run?_path run_row22102ForwardMoves

/-- The forward replay path of row `221-02` has exactly 2 edges. -/
@[simp] theorem row22102ForwardPath_length :
    row22102ForwardPath.length = 2 := by
  rw [row22102ForwardPath, run?_path_length]
  rfl

/-- The actual `run?_path` data for the reverse replay of row `221-02`. -/
def row22102ReversePath :
    MovePath (@AllModeMove profile221) row22102Finish row22102Start :=
  run?_path run_row22102ReverseMoves

/-- The reverse replay path of row `221-02` has exactly 2 edges. -/
@[simp] theorem row22102ReversePath_length :
    row22102ReversePath.length = 2 := by
  rw [row22102ReversePath, run?_path_length]
  rfl

/-- Both actual replay paths of row `221-02` have at most three edges. -/
theorem row22102_path_lengths_le_three :
    row22102ForwardPath.length ≤ 3 ∧ row22102ReversePath.length ≤ 3 := by
  rw [row22102ForwardPath_length, row22102ReversePath_length]
  omega

/-- The endpoint states of row `221-02` are disjoint. -/
theorem row22102_disjoint : Disjoint row22102Start row22102Finish := by
  decide

/-- The starting state of row `221-02` has exactly two terms. -/
theorem row22102_card_start : row22102Start.card = 2 := by
  decide

/-- The finishing state of row `221-02` has exactly three terms. -/
theorem row22102_card_finish : row22102Finish.card = 3 := by
  decide

/-- The visible standard-basis masks in the endpoint union of row `221-02` prove its exact factor profile. -/
theorem row22102_exactFactorProfile :
    HasExactFactorProfile (row22102Start ∪ row22102Finish) := by
  constructor
  · unfold firstFactorSpan
    apply (Submodule.eq_top_iff_forall_basis_mem
      (Pi.basisFun F2 (Fin profile221.first))).mpr
    intro i
    rw [Pi.basisFun_apply]
    apply Submodule.subset_span
    fin_cases i <;> decide
  constructor
  · unfold secondFactorSpan
    apply (Submodule.eq_top_iff_forall_basis_mem
      (Pi.basisFun F2 (Fin profile221.second))).mpr
    intro i
    rw [Pi.basisFun_apply]
    apply Submodule.subset_span
    fin_cases i <;> decide
  · unfold thirdFactorSpan
    apply (Submodule.eq_top_iff_forall_basis_mem
      (Pi.basisFun F2 (Fin profile221.third))).mpr
    intro i
    rw [Pi.basisFun_apply]
    apply Submodule.subset_span
    fin_cases i
    decide

/-- The kernel-replayed five-circuit certificate for row `221-02`. -/
def row22102Certificate :
    FiveCircuitCertificate profile221 row22102Start row22102Finish := by
  let cert := replayRow_toFiveCircuitCertificate row22102 row22102_passes
    (by change Disjoint row22102Start row22102Finish; exact row22102_disjoint)
    (by change row22102Start.card = 2; exact row22102_card_start)
    (by change row22102Finish.card = 3; exact row22102_card_finish)
    (by simp only [row22102, row22102ForwardMoves, List.length_cons,
      List.length_nil]; omega)
    (by simp only [row22102, row22102ReverseMoves, List.length_cons,
      List.length_nil]; omega)
    (by
      change HasExactFactorProfile (row22102Start ∪ row22102Finish)
      exact row22102_exactFactorProfile)
  change FiveCircuitCertificate profile221 row22102Start row22102Finish at cert
  exact cert

/-- The heterogeneous certified wrapper for computationally selected row `221-02`. -/
def certified22102 : CertifiedReplayRow where
  row := row22102
  passes := row22102_passes
  disjoint := by change Disjoint row22102Start row22102Finish; exact row22102_disjoint
  card_start := by change row22102Start.card = 2; exact row22102_card_start
  card_finish := by change row22102Finish.card = 3; exact row22102_card_finish
  forward_length_le := by simp only [row22102, row22102ForwardMoves, List.length_cons, List.length_nil]; omega
  reverse_length_le := by simp only [row22102, row22102ReverseMoves, List.length_cons, List.length_nil]; omega
  exact_profile := by
    change HasExactFactorProfile (row22102Start ∪ row22102Finish)
    exact row22102_exactFactorProfile

/-! ## Computationally selected and replayed row `221-03` -/

/-- The two-term starting state of computationally selected row `221-03`. -/
def row22103Start : State profile221 :=
  {maskTerm(profile221, 1, 1, 1),
   maskTerm(profile221, 3, 3, 1)}

/-- The three-term finishing state of computationally selected row `221-03`. -/
def row22103Finish : State profile221 :=
  {maskTerm(profile221, 1, 2, 1),
   maskTerm(profile221, 2, 1, 1),
   maskTerm(profile221, 2, 2, 1)}

/-- Target-coordinate intermediate state 1 on the forward replay of row `221-03`. -/
def row22103ForwardState1 : State profile221 :=
  {maskTerm(profile221, 1, 2, 1),
   maskTerm(profile221, 2, 3, 1)}

/-- Target-coordinate intermediate state 1 on the reverse replay of row `221-03`. -/
def row22103ReverseState1 : State profile221 :=
  {maskTerm(profile221, 1, 2, 1),
   maskTerm(profile221, 2, 3, 1)}

/-- The exact source-coordinate flip data for forward step 1 of row `221-03`. -/
def row22103ForwardMove1 : FixedMoveData profile221 :=
  ⟨.abc, .flip
      maskTerm(inversePermProfile .abc profile221, 3, 3, 1)
      maskTerm(inversePermProfile .abc profile221, 1, 1, 1)
      maskTerm(inversePermProfile .abc profile221, 2, 3, 1)
      maskTerm(inversePermProfile .abc profile221, 1, 2, 1)⟩

/-- The exact source-coordinate split data for forward step 2 of row `221-03`. -/
def row22103ForwardMove2 : FixedMoveData profile221 :=
  ⟨.cab, .split
      maskTerm(inversePermProfile .cab profile221, 3, 1, 2)
      maskTerm(inversePermProfile .cab profile221, 1, 1, 2)
      maskTerm(inversePermProfile .cab profile221, 2, 1, 2)⟩

/-- The exact source-coordinate reduction data for reverse step 1 of row `221-03`. -/
def row22103ReverseMove1 : FixedMoveData profile221 :=
  ⟨.cab, .reduction
      maskTerm(inversePermProfile .cab profile221, 1, 1, 2)
      maskTerm(inversePermProfile .cab profile221, 2, 1, 2)
      maskTerm(inversePermProfile .cab profile221, 3, 1, 2)⟩

/-- The exact source-coordinate flip data for reverse step 2 of row `221-03`. -/
def row22103ReverseMove2 : FixedMoveData profile221 :=
  ⟨.abc, .flip
      maskTerm(inversePermProfile .abc profile221, 2, 3, 1)
      maskTerm(inversePermProfile .abc profile221, 1, 2, 1)
      maskTerm(inversePermProfile .abc profile221, 3, 3, 1)
      maskTerm(inversePermProfile .abc profile221, 1, 1, 1)⟩

/-- Kernel replay of the directed Flip at forward step 1 of row `221-03`. -/
theorem step_row22103ForwardMove1 :
    row22103ForwardMove1.step? row22103Start = some row22103ForwardState1 := by
  unfold FixedMoveData.step? row22103ForwardMove1
  let m : SourceMoveData (inversePermProfile .abc profile221) :=
    .flip
          maskTerm(inversePermProfile .abc profile221, 3, 3, 1)
          maskTerm(inversePermProfile .abc profile221, 1, 1, 1)
          maskTerm(inversePermProfile .abc profile221, 2, 3, 1)
          maskTerm(inversePermProfile .abc profile221, 1, 2, 1)
  change Option.map (@forwardState profile221 .abc)
    (m.step? (inversePermuteState .abc row22103Start)) = some row22103ForwardState1
  have hlegal : m.Legal (inversePermuteState .abc row22103Start) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .abc row22103Start) =
      inversePermuteState .abc row22103ForwardState1 := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Split at forward step 2 of row `221-03`. -/
theorem step_row22103ForwardMove2 :
    row22103ForwardMove2.step? row22103ForwardState1 = some row22103Finish := by
  unfold FixedMoveData.step? row22103ForwardMove2
  let m : SourceMoveData (inversePermProfile .cab profile221) :=
    .split
          maskTerm(inversePermProfile .cab profile221, 3, 1, 2)
          maskTerm(inversePermProfile .cab profile221, 1, 1, 2)
          maskTerm(inversePermProfile .cab profile221, 2, 1, 2)
  change Option.map (@forwardState profile221 .cab)
    (m.step? (inversePermuteState .cab row22103ForwardState1)) = some row22103Finish
  have hlegal : m.Legal (inversePermuteState .cab row22103ForwardState1) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .cab row22103ForwardState1) =
      inversePermuteState .cab row22103Finish := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Reduction at reverse step 1 of row `221-03`. -/
theorem step_row22103ReverseMove1 :
    row22103ReverseMove1.step? row22103Finish = some row22103ReverseState1 := by
  unfold FixedMoveData.step? row22103ReverseMove1
  let m : SourceMoveData (inversePermProfile .cab profile221) :=
    .reduction
          maskTerm(inversePermProfile .cab profile221, 1, 1, 2)
          maskTerm(inversePermProfile .cab profile221, 2, 1, 2)
          maskTerm(inversePermProfile .cab profile221, 3, 1, 2)
  change Option.map (@forwardState profile221 .cab)
    (m.step? (inversePermuteState .cab row22103Finish)) = some row22103ReverseState1
  have hlegal : m.Legal (inversePermuteState .cab row22103Finish) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .cab row22103Finish) =
      inversePermuteState .cab row22103ReverseState1 := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Flip at reverse step 2 of row `221-03`. -/
theorem step_row22103ReverseMove2 :
    row22103ReverseMove2.step? row22103ReverseState1 = some row22103Start := by
  unfold FixedMoveData.step? row22103ReverseMove2
  let m : SourceMoveData (inversePermProfile .abc profile221) :=
    .flip
          maskTerm(inversePermProfile .abc profile221, 2, 3, 1)
          maskTerm(inversePermProfile .abc profile221, 1, 2, 1)
          maskTerm(inversePermProfile .abc profile221, 3, 3, 1)
          maskTerm(inversePermProfile .abc profile221, 1, 1, 1)
  change Option.map (@forwardState profile221 .abc)
    (m.step? (inversePermuteState .abc row22103ReverseState1)) = some row22103Start
  have hlegal : m.Legal (inversePermuteState .abc row22103ReverseState1) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .abc row22103ReverseState1) =
      inversePermuteState .abc row22103Start := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- The fixed directed forward witness list for row `221-03`. -/
def row22103ForwardMoves : List (FixedMoveData profile221) :=
  [row22103ForwardMove1, row22103ForwardMove2]

/-- The fixed directed reverse witness list for row `221-03`. -/
def row22103ReverseMoves : List (FixedMoveData profile221) :=
  [row22103ReverseMove1, row22103ReverseMove2]

/-- The heterogeneous raw replay data for computationally selected row `221-03`. -/
def row22103 : ReplayRow where
  profile := profile221
  start := row22103Start
  finish := row22103Finish
  forward := row22103ForwardMoves
  reverse := row22103ReverseMoves

/-- The exact forward run equation for row `221-03`. -/
theorem run_row22103ForwardMoves :
    run? row22103Start row22103ForwardMoves = some row22103Finish := by
  simp only [row22103ForwardMoves, run?, step_row22103ForwardMove1, Option.bind_some, step_row22103ForwardMove2]

/-- The exact reverse run equation for row `221-03`. -/
theorem run_row22103ReverseMoves :
    run? row22103Finish row22103ReverseMoves = some row22103Start := by
  simp only [row22103ReverseMoves, run?, step_row22103ReverseMove1, Option.bind_some, step_row22103ReverseMove2]

/-- Both exact directed runs of row `221-03` pass. -/
theorem row22103_passes : row22103.Passes := by
  simpa only [row22103, ReplayRow.Passes] using
    And.intro run_row22103ForwardMoves run_row22103ReverseMoves

/-- The actual `run?_path` data for the forward replay of row `221-03`. -/
def row22103ForwardPath :
    MovePath (@AllModeMove profile221) row22103Start row22103Finish :=
  run?_path run_row22103ForwardMoves

/-- The forward replay path of row `221-03` has exactly 2 edges. -/
@[simp] theorem row22103ForwardPath_length :
    row22103ForwardPath.length = 2 := by
  rw [row22103ForwardPath, run?_path_length]
  rfl

/-- The actual `run?_path` data for the reverse replay of row `221-03`. -/
def row22103ReversePath :
    MovePath (@AllModeMove profile221) row22103Finish row22103Start :=
  run?_path run_row22103ReverseMoves

/-- The reverse replay path of row `221-03` has exactly 2 edges. -/
@[simp] theorem row22103ReversePath_length :
    row22103ReversePath.length = 2 := by
  rw [row22103ReversePath, run?_path_length]
  rfl

/-- Both actual replay paths of row `221-03` have at most three edges. -/
theorem row22103_path_lengths_le_three :
    row22103ForwardPath.length ≤ 3 ∧ row22103ReversePath.length ≤ 3 := by
  rw [row22103ForwardPath_length, row22103ReversePath_length]
  omega

/-- The endpoint states of row `221-03` are disjoint. -/
theorem row22103_disjoint : Disjoint row22103Start row22103Finish := by
  decide

/-- The starting state of row `221-03` has exactly two terms. -/
theorem row22103_card_start : row22103Start.card = 2 := by
  decide

/-- The finishing state of row `221-03` has exactly three terms. -/
theorem row22103_card_finish : row22103Finish.card = 3 := by
  decide

/-- The visible standard-basis masks in the endpoint union of row `221-03` prove its exact factor profile. -/
theorem row22103_exactFactorProfile :
    HasExactFactorProfile (row22103Start ∪ row22103Finish) := by
  constructor
  · unfold firstFactorSpan
    apply (Submodule.eq_top_iff_forall_basis_mem
      (Pi.basisFun F2 (Fin profile221.first))).mpr
    intro i
    rw [Pi.basisFun_apply]
    apply Submodule.subset_span
    fin_cases i <;> decide
  constructor
  · unfold secondFactorSpan
    apply (Submodule.eq_top_iff_forall_basis_mem
      (Pi.basisFun F2 (Fin profile221.second))).mpr
    intro i
    rw [Pi.basisFun_apply]
    apply Submodule.subset_span
    fin_cases i <;> decide
  · unfold thirdFactorSpan
    apply (Submodule.eq_top_iff_forall_basis_mem
      (Pi.basisFun F2 (Fin profile221.third))).mpr
    intro i
    rw [Pi.basisFun_apply]
    apply Submodule.subset_span
    fin_cases i
    decide

/-- The kernel-replayed five-circuit certificate for row `221-03`. -/
def row22103Certificate :
    FiveCircuitCertificate profile221 row22103Start row22103Finish := by
  let cert := replayRow_toFiveCircuitCertificate row22103 row22103_passes
    (by change Disjoint row22103Start row22103Finish; exact row22103_disjoint)
    (by change row22103Start.card = 2; exact row22103_card_start)
    (by change row22103Finish.card = 3; exact row22103_card_finish)
    (by simp only [row22103, row22103ForwardMoves, List.length_cons,
      List.length_nil]; omega)
    (by simp only [row22103, row22103ReverseMoves, List.length_cons,
      List.length_nil]; omega)
    (by
      change HasExactFactorProfile (row22103Start ∪ row22103Finish)
      exact row22103_exactFactorProfile)
  change FiveCircuitCertificate profile221 row22103Start row22103Finish at cert
  exact cert

/-- The heterogeneous certified wrapper for computationally selected row `221-03`. -/
def certified22103 : CertifiedReplayRow where
  row := row22103
  passes := row22103_passes
  disjoint := by change Disjoint row22103Start row22103Finish; exact row22103_disjoint
  card_start := by change row22103Start.card = 2; exact row22103_card_start
  card_finish := by change row22103Finish.card = 3; exact row22103_card_finish
  forward_length_le := by simp only [row22103, row22103ForwardMoves, List.length_cons, List.length_nil]; omega
  reverse_length_le := by simp only [row22103, row22103ReverseMoves, List.length_cons, List.length_nil]; omega
  exact_profile := by
    change HasExactFactorProfile (row22103Start ∪ row22103Finish)
    exact row22103_exactFactorProfile

/-! ## Computationally selected and replayed row `411-01` -/

/-- The two-term starting state of computationally selected row `411-01`. -/
def row41101Start : State profile411 :=
  {maskTerm(profile411, 1, 1, 1),
   maskTerm(profile411, 2, 1, 1)}

/-- The three-term finishing state of computationally selected row `411-01`. -/
def row41101Finish : State profile411 :=
  {maskTerm(profile411, 4, 1, 1),
   maskTerm(profile411, 8, 1, 1),
   maskTerm(profile411, 15, 1, 1)}

/-- Target-coordinate intermediate state 1 on the forward replay of row `411-01`. -/
def row41101ForwardState1 : State profile411 :=
  {maskTerm(profile411, 3, 1, 1)}

/-- Target-coordinate intermediate state 2 on the forward replay of row `411-01`. -/
def row41101ForwardState2 : State profile411 :=
  {maskTerm(profile411, 4, 1, 1),
   maskTerm(profile411, 7, 1, 1)}

/-- Target-coordinate intermediate state 1 on the reverse replay of row `411-01`. -/
def row41101ReverseState1 : State profile411 :=
  {maskTerm(profile411, 4, 1, 1),
   maskTerm(profile411, 7, 1, 1)}

/-- Target-coordinate intermediate state 2 on the reverse replay of row `411-01`. -/
def row41101ReverseState2 : State profile411 :=
  {maskTerm(profile411, 3, 1, 1)}

/-- The exact source-coordinate reduction data for forward step 1 of row `411-01`. -/
def row41101ForwardMove1 : FixedMoveData profile411 :=
  ⟨.abc, .reduction
      maskTerm(inversePermProfile .abc profile411, 1, 1, 1)
      maskTerm(inversePermProfile .abc profile411, 2, 1, 1)
      maskTerm(inversePermProfile .abc profile411, 3, 1, 1)⟩

/-- The exact source-coordinate split data for forward step 2 of row `411-01`. -/
def row41101ForwardMove2 : FixedMoveData profile411 :=
  ⟨.abc, .split
      maskTerm(inversePermProfile .abc profile411, 3, 1, 1)
      maskTerm(inversePermProfile .abc profile411, 4, 1, 1)
      maskTerm(inversePermProfile .abc profile411, 7, 1, 1)⟩

/-- The exact source-coordinate split data for forward step 3 of row `411-01`. -/
def row41101ForwardMove3 : FixedMoveData profile411 :=
  ⟨.abc, .split
      maskTerm(inversePermProfile .abc profile411, 7, 1, 1)
      maskTerm(inversePermProfile .abc profile411, 8, 1, 1)
      maskTerm(inversePermProfile .abc profile411, 15, 1, 1)⟩

/-- The exact source-coordinate reduction data for reverse step 1 of row `411-01`. -/
def row41101ReverseMove1 : FixedMoveData profile411 :=
  ⟨.abc, .reduction
      maskTerm(inversePermProfile .abc profile411, 8, 1, 1)
      maskTerm(inversePermProfile .abc profile411, 15, 1, 1)
      maskTerm(inversePermProfile .abc profile411, 7, 1, 1)⟩

/-- The exact source-coordinate reduction data for reverse step 2 of row `411-01`. -/
def row41101ReverseMove2 : FixedMoveData profile411 :=
  ⟨.abc, .reduction
      maskTerm(inversePermProfile .abc profile411, 4, 1, 1)
      maskTerm(inversePermProfile .abc profile411, 7, 1, 1)
      maskTerm(inversePermProfile .abc profile411, 3, 1, 1)⟩

/-- The exact source-coordinate split data for reverse step 3 of row `411-01`. -/
def row41101ReverseMove3 : FixedMoveData profile411 :=
  ⟨.abc, .split
      maskTerm(inversePermProfile .abc profile411, 3, 1, 1)
      maskTerm(inversePermProfile .abc profile411, 1, 1, 1)
      maskTerm(inversePermProfile .abc profile411, 2, 1, 1)⟩

/-- Kernel replay of the directed Reduction at forward step 1 of row `411-01`. -/
theorem step_row41101ForwardMove1 :
    row41101ForwardMove1.step? row41101Start = some row41101ForwardState1 := by
  unfold FixedMoveData.step? row41101ForwardMove1
  let m : SourceMoveData (inversePermProfile .abc profile411) :=
    .reduction
          maskTerm(inversePermProfile .abc profile411, 1, 1, 1)
          maskTerm(inversePermProfile .abc profile411, 2, 1, 1)
          maskTerm(inversePermProfile .abc profile411, 3, 1, 1)
  change Option.map (@forwardState profile411 .abc)
    (m.step? (inversePermuteState .abc row41101Start)) = some row41101ForwardState1
  have hlegal : m.Legal (inversePermuteState .abc row41101Start) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .abc row41101Start) =
      inversePermuteState .abc row41101ForwardState1 := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Split at forward step 2 of row `411-01`. -/
theorem step_row41101ForwardMove2 :
    row41101ForwardMove2.step? row41101ForwardState1 = some row41101ForwardState2 := by
  unfold FixedMoveData.step? row41101ForwardMove2
  let m : SourceMoveData (inversePermProfile .abc profile411) :=
    .split
          maskTerm(inversePermProfile .abc profile411, 3, 1, 1)
          maskTerm(inversePermProfile .abc profile411, 4, 1, 1)
          maskTerm(inversePermProfile .abc profile411, 7, 1, 1)
  change Option.map (@forwardState profile411 .abc)
    (m.step? (inversePermuteState .abc row41101ForwardState1)) = some row41101ForwardState2
  have hlegal : m.Legal (inversePermuteState .abc row41101ForwardState1) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .abc row41101ForwardState1) =
      inversePermuteState .abc row41101ForwardState2 := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Split at forward step 3 of row `411-01`. -/
theorem step_row41101ForwardMove3 :
    row41101ForwardMove3.step? row41101ForwardState2 = some row41101Finish := by
  unfold FixedMoveData.step? row41101ForwardMove3
  let m : SourceMoveData (inversePermProfile .abc profile411) :=
    .split
          maskTerm(inversePermProfile .abc profile411, 7, 1, 1)
          maskTerm(inversePermProfile .abc profile411, 8, 1, 1)
          maskTerm(inversePermProfile .abc profile411, 15, 1, 1)
  change Option.map (@forwardState profile411 .abc)
    (m.step? (inversePermuteState .abc row41101ForwardState2)) = some row41101Finish
  have hlegal : m.Legal (inversePermuteState .abc row41101ForwardState2) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .abc row41101ForwardState2) =
      inversePermuteState .abc row41101Finish := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Reduction at reverse step 1 of row `411-01`. -/
theorem step_row41101ReverseMove1 :
    row41101ReverseMove1.step? row41101Finish = some row41101ReverseState1 := by
  unfold FixedMoveData.step? row41101ReverseMove1
  let m : SourceMoveData (inversePermProfile .abc profile411) :=
    .reduction
          maskTerm(inversePermProfile .abc profile411, 8, 1, 1)
          maskTerm(inversePermProfile .abc profile411, 15, 1, 1)
          maskTerm(inversePermProfile .abc profile411, 7, 1, 1)
  change Option.map (@forwardState profile411 .abc)
    (m.step? (inversePermuteState .abc row41101Finish)) = some row41101ReverseState1
  have hlegal : m.Legal (inversePermuteState .abc row41101Finish) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .abc row41101Finish) =
      inversePermuteState .abc row41101ReverseState1 := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Reduction at reverse step 2 of row `411-01`. -/
theorem step_row41101ReverseMove2 :
    row41101ReverseMove2.step? row41101ReverseState1 = some row41101ReverseState2 := by
  unfold FixedMoveData.step? row41101ReverseMove2
  let m : SourceMoveData (inversePermProfile .abc profile411) :=
    .reduction
          maskTerm(inversePermProfile .abc profile411, 4, 1, 1)
          maskTerm(inversePermProfile .abc profile411, 7, 1, 1)
          maskTerm(inversePermProfile .abc profile411, 3, 1, 1)
  change Option.map (@forwardState profile411 .abc)
    (m.step? (inversePermuteState .abc row41101ReverseState1)) = some row41101ReverseState2
  have hlegal : m.Legal (inversePermuteState .abc row41101ReverseState1) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .abc row41101ReverseState1) =
      inversePermuteState .abc row41101ReverseState2 := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Split at reverse step 3 of row `411-01`. -/
theorem step_row41101ReverseMove3 :
    row41101ReverseMove3.step? row41101ReverseState2 = some row41101Start := by
  unfold FixedMoveData.step? row41101ReverseMove3
  let m : SourceMoveData (inversePermProfile .abc profile411) :=
    .split
          maskTerm(inversePermProfile .abc profile411, 3, 1, 1)
          maskTerm(inversePermProfile .abc profile411, 1, 1, 1)
          maskTerm(inversePermProfile .abc profile411, 2, 1, 1)
  change Option.map (@forwardState profile411 .abc)
    (m.step? (inversePermuteState .abc row41101ReverseState2)) = some row41101Start
  have hlegal : m.Legal (inversePermuteState .abc row41101ReverseState2) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .abc row41101ReverseState2) =
      inversePermuteState .abc row41101Start := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- The fixed directed forward witness list for row `411-01`. -/
def row41101ForwardMoves : List (FixedMoveData profile411) :=
  [row41101ForwardMove1, row41101ForwardMove2, row41101ForwardMove3]

/-- The fixed directed reverse witness list for row `411-01`. -/
def row41101ReverseMoves : List (FixedMoveData profile411) :=
  [row41101ReverseMove1, row41101ReverseMove2, row41101ReverseMove3]

/-- The heterogeneous raw replay data for computationally selected row `411-01`. -/
def row41101 : ReplayRow where
  profile := profile411
  start := row41101Start
  finish := row41101Finish
  forward := row41101ForwardMoves
  reverse := row41101ReverseMoves

/-- The exact forward run equation for row `411-01`. -/
theorem run_row41101ForwardMoves :
    run? row41101Start row41101ForwardMoves = some row41101Finish := by
  simp only [row41101ForwardMoves, run?, step_row41101ForwardMove1, Option.bind_some, step_row41101ForwardMove2, Option.bind_some, step_row41101ForwardMove3]

/-- The exact reverse run equation for row `411-01`. -/
theorem run_row41101ReverseMoves :
    run? row41101Finish row41101ReverseMoves = some row41101Start := by
  simp only [row41101ReverseMoves, run?, step_row41101ReverseMove1, Option.bind_some, step_row41101ReverseMove2, Option.bind_some, step_row41101ReverseMove3]

/-- Both exact directed runs of row `411-01` pass. -/
theorem row41101_passes : row41101.Passes := by
  simpa only [row41101, ReplayRow.Passes] using
    And.intro run_row41101ForwardMoves run_row41101ReverseMoves

/-- The actual `run?_path` data for the forward replay of row `411-01`. -/
def row41101ForwardPath :
    MovePath (@AllModeMove profile411) row41101Start row41101Finish :=
  run?_path run_row41101ForwardMoves

/-- The forward replay path of row `411-01` has exactly 3 edges. -/
@[simp] theorem row41101ForwardPath_length :
    row41101ForwardPath.length = 3 := by
  rw [row41101ForwardPath, run?_path_length]
  rfl

/-- The actual `run?_path` data for the reverse replay of row `411-01`. -/
def row41101ReversePath :
    MovePath (@AllModeMove profile411) row41101Finish row41101Start :=
  run?_path run_row41101ReverseMoves

/-- The reverse replay path of row `411-01` has exactly 3 edges. -/
@[simp] theorem row41101ReversePath_length :
    row41101ReversePath.length = 3 := by
  rw [row41101ReversePath, run?_path_length]
  rfl

/-- Both actual replay paths of row `411-01` have at most three edges. -/
theorem row41101_path_lengths_le_three :
    row41101ForwardPath.length ≤ 3 ∧ row41101ReversePath.length ≤ 3 := by
  rw [row41101ForwardPath_length, row41101ReversePath_length]
  omega

/-- The endpoint states of row `411-01` are disjoint. -/
theorem row41101_disjoint : Disjoint row41101Start row41101Finish := by
  decide

/-- The starting state of row `411-01` has exactly two terms. -/
theorem row41101_card_start : row41101Start.card = 2 := by
  decide

/-- The finishing state of row `411-01` has exactly three terms. -/
theorem row41101_card_finish : row41101Finish.card = 3 := by
  decide

/-- The visible standard-basis masks in the endpoint union of row `411-01` prove its exact factor profile. -/
theorem row41101_exactFactorProfile :
    HasExactFactorProfile (row41101Start ∪ row41101Finish) := by
  constructor
  · unfold firstFactorSpan
    apply (Submodule.eq_top_iff_forall_basis_mem
      (Pi.basisFun F2 (Fin profile411.first))).mpr
    intro i
    rw [Pi.basisFun_apply]
    apply Submodule.subset_span
    fin_cases i <;> decide
  constructor
  · unfold secondFactorSpan
    apply (Submodule.eq_top_iff_forall_basis_mem
      (Pi.basisFun F2 (Fin profile411.second))).mpr
    intro i
    rw [Pi.basisFun_apply]
    apply Submodule.subset_span
    fin_cases i
    decide
  · unfold thirdFactorSpan
    apply (Submodule.eq_top_iff_forall_basis_mem
      (Pi.basisFun F2 (Fin profile411.third))).mpr
    intro i
    rw [Pi.basisFun_apply]
    apply Submodule.subset_span
    fin_cases i
    decide

/-- The kernel-replayed five-circuit certificate for row `411-01`. -/
def row41101Certificate :
    FiveCircuitCertificate profile411 row41101Start row41101Finish := by
  let cert := replayRow_toFiveCircuitCertificate row41101 row41101_passes
    (by change Disjoint row41101Start row41101Finish; exact row41101_disjoint)
    (by change row41101Start.card = 2; exact row41101_card_start)
    (by change row41101Finish.card = 3; exact row41101_card_finish)
    (by simp only [row41101, row41101ForwardMoves, List.length_cons,
      List.length_nil]; omega)
    (by simp only [row41101, row41101ReverseMoves, List.length_cons,
      List.length_nil]; omega)
    (by
      change HasExactFactorProfile (row41101Start ∪ row41101Finish)
      exact row41101_exactFactorProfile)
  change FiveCircuitCertificate profile411 row41101Start row41101Finish at cert
  exact cert

/-- The heterogeneous certified wrapper for computationally selected row `411-01`. -/
def certified41101 : CertifiedReplayRow where
  row := row41101
  passes := row41101_passes
  disjoint := by change Disjoint row41101Start row41101Finish; exact row41101_disjoint
  card_start := by change row41101Start.card = 2; exact row41101_card_start
  card_finish := by change row41101Finish.card = 3; exact row41101_card_finish
  forward_length_le := by simp only [row41101, row41101ForwardMoves, List.length_cons, List.length_nil]; omega
  reverse_length_le := by simp only [row41101, row41101ReverseMoves, List.length_cons, List.length_nil]; omega
  exact_profile := by
    change HasExactFactorProfile (row41101Start ∪ row41101Finish)
    exact row41101_exactFactorProfile

/-! ## Computationally selected and replayed row `321-01` -/

/-- The two-term starting state of computationally selected row `321-01`. -/
def row32101Start : State profile321 :=
  {maskTerm(profile321, 1, 1, 1),
   maskTerm(profile321, 1, 2, 1)}

/-- The three-term finishing state of computationally selected row `321-01`. -/
def row32101Finish : State profile321 :=
  {maskTerm(profile321, 2, 3, 1),
   maskTerm(profile321, 4, 3, 1),
   maskTerm(profile321, 7, 3, 1)}

/-- Target-coordinate intermediate state 1 on the forward replay of row `321-01`. -/
def row32101ForwardState1 : State profile321 :=
  {maskTerm(profile321, 1, 3, 1)}

/-- Target-coordinate intermediate state 2 on the forward replay of row `321-01`. -/
def row32101ForwardState2 : State profile321 :=
  {maskTerm(profile321, 2, 3, 1),
   maskTerm(profile321, 3, 3, 1)}

/-- Target-coordinate intermediate state 1 on the reverse replay of row `321-01`. -/
def row32101ReverseState1 : State profile321 :=
  {maskTerm(profile321, 2, 3, 1),
   maskTerm(profile321, 3, 3, 1)}

/-- Target-coordinate intermediate state 2 on the reverse replay of row `321-01`. -/
def row32101ReverseState2 : State profile321 :=
  {maskTerm(profile321, 1, 3, 1)}

/-- The exact source-coordinate reduction data for forward step 1 of row `321-01`. -/
def row32101ForwardMove1 : FixedMoveData profile321 :=
  ⟨.cab, .reduction
      maskTerm(inversePermProfile .cab profile321, 1, 1, 1)
      maskTerm(inversePermProfile .cab profile321, 2, 1, 1)
      maskTerm(inversePermProfile .cab profile321, 3, 1, 1)⟩

/-- The exact source-coordinate split data for forward step 2 of row `321-01`. -/
def row32101ForwardMove2 : FixedMoveData profile321 :=
  ⟨.abc, .split
      maskTerm(inversePermProfile .abc profile321, 1, 3, 1)
      maskTerm(inversePermProfile .abc profile321, 2, 3, 1)
      maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩

/-- The exact source-coordinate split data for forward step 3 of row `321-01`. -/
def row32101ForwardMove3 : FixedMoveData profile321 :=
  ⟨.abc, .split
      maskTerm(inversePermProfile .abc profile321, 3, 3, 1)
      maskTerm(inversePermProfile .abc profile321, 4, 3, 1)
      maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩

/-- The exact source-coordinate reduction data for reverse step 1 of row `321-01`. -/
def row32101ReverseMove1 : FixedMoveData profile321 :=
  ⟨.abc, .reduction
      maskTerm(inversePermProfile .abc profile321, 4, 3, 1)
      maskTerm(inversePermProfile .abc profile321, 7, 3, 1)
      maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩

/-- The exact source-coordinate reduction data for reverse step 2 of row `321-01`. -/
def row32101ReverseMove2 : FixedMoveData profile321 :=
  ⟨.abc, .reduction
      maskTerm(inversePermProfile .abc profile321, 2, 3, 1)
      maskTerm(inversePermProfile .abc profile321, 3, 3, 1)
      maskTerm(inversePermProfile .abc profile321, 1, 3, 1)⟩

/-- The exact source-coordinate split data for reverse step 3 of row `321-01`. -/
def row32101ReverseMove3 : FixedMoveData profile321 :=
  ⟨.cab, .split
      maskTerm(inversePermProfile .cab profile321, 3, 1, 1)
      maskTerm(inversePermProfile .cab profile321, 1, 1, 1)
      maskTerm(inversePermProfile .cab profile321, 2, 1, 1)⟩

/-- Kernel replay of the directed Reduction at forward step 1 of row `321-01`. -/
theorem step_row32101ForwardMove1 :
    row32101ForwardMove1.step? row32101Start = some row32101ForwardState1 := by
  unfold FixedMoveData.step? row32101ForwardMove1
  let m : SourceMoveData (inversePermProfile .cab profile321) :=
    .reduction
          maskTerm(inversePermProfile .cab profile321, 1, 1, 1)
          maskTerm(inversePermProfile .cab profile321, 2, 1, 1)
          maskTerm(inversePermProfile .cab profile321, 3, 1, 1)
  change Option.map (@forwardState profile321 .cab)
    (m.step? (inversePermuteState .cab row32101Start)) = some row32101ForwardState1
  have hlegal : m.Legal (inversePermuteState .cab row32101Start) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .cab row32101Start) =
      inversePermuteState .cab row32101ForwardState1 := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Split at forward step 2 of row `321-01`. -/
theorem step_row32101ForwardMove2 :
    row32101ForwardMove2.step? row32101ForwardState1 = some row32101ForwardState2 := by
  unfold FixedMoveData.step? row32101ForwardMove2
  let m : SourceMoveData (inversePermProfile .abc profile321) :=
    .split
          maskTerm(inversePermProfile .abc profile321, 1, 3, 1)
          maskTerm(inversePermProfile .abc profile321, 2, 3, 1)
          maskTerm(inversePermProfile .abc profile321, 3, 3, 1)
  change Option.map (@forwardState profile321 .abc)
    (m.step? (inversePermuteState .abc row32101ForwardState1)) = some row32101ForwardState2
  have hlegal : m.Legal (inversePermuteState .abc row32101ForwardState1) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .abc row32101ForwardState1) =
      inversePermuteState .abc row32101ForwardState2 := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Split at forward step 3 of row `321-01`. -/
theorem step_row32101ForwardMove3 :
    row32101ForwardMove3.step? row32101ForwardState2 = some row32101Finish := by
  unfold FixedMoveData.step? row32101ForwardMove3
  let m : SourceMoveData (inversePermProfile .abc profile321) :=
    .split
          maskTerm(inversePermProfile .abc profile321, 3, 3, 1)
          maskTerm(inversePermProfile .abc profile321, 4, 3, 1)
          maskTerm(inversePermProfile .abc profile321, 7, 3, 1)
  change Option.map (@forwardState profile321 .abc)
    (m.step? (inversePermuteState .abc row32101ForwardState2)) = some row32101Finish
  have hlegal : m.Legal (inversePermuteState .abc row32101ForwardState2) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .abc row32101ForwardState2) =
      inversePermuteState .abc row32101Finish := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Reduction at reverse step 1 of row `321-01`. -/
theorem step_row32101ReverseMove1 :
    row32101ReverseMove1.step? row32101Finish = some row32101ReverseState1 := by
  unfold FixedMoveData.step? row32101ReverseMove1
  let m : SourceMoveData (inversePermProfile .abc profile321) :=
    .reduction
          maskTerm(inversePermProfile .abc profile321, 4, 3, 1)
          maskTerm(inversePermProfile .abc profile321, 7, 3, 1)
          maskTerm(inversePermProfile .abc profile321, 3, 3, 1)
  change Option.map (@forwardState profile321 .abc)
    (m.step? (inversePermuteState .abc row32101Finish)) = some row32101ReverseState1
  have hlegal : m.Legal (inversePermuteState .abc row32101Finish) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .abc row32101Finish) =
      inversePermuteState .abc row32101ReverseState1 := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Reduction at reverse step 2 of row `321-01`. -/
theorem step_row32101ReverseMove2 :
    row32101ReverseMove2.step? row32101ReverseState1 = some row32101ReverseState2 := by
  unfold FixedMoveData.step? row32101ReverseMove2
  let m : SourceMoveData (inversePermProfile .abc profile321) :=
    .reduction
          maskTerm(inversePermProfile .abc profile321, 2, 3, 1)
          maskTerm(inversePermProfile .abc profile321, 3, 3, 1)
          maskTerm(inversePermProfile .abc profile321, 1, 3, 1)
  change Option.map (@forwardState profile321 .abc)
    (m.step? (inversePermuteState .abc row32101ReverseState1)) = some row32101ReverseState2
  have hlegal : m.Legal (inversePermuteState .abc row32101ReverseState1) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .abc row32101ReverseState1) =
      inversePermuteState .abc row32101ReverseState2 := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Split at reverse step 3 of row `321-01`. -/
theorem step_row32101ReverseMove3 :
    row32101ReverseMove3.step? row32101ReverseState2 = some row32101Start := by
  unfold FixedMoveData.step? row32101ReverseMove3
  let m : SourceMoveData (inversePermProfile .cab profile321) :=
    .split
          maskTerm(inversePermProfile .cab profile321, 3, 1, 1)
          maskTerm(inversePermProfile .cab profile321, 1, 1, 1)
          maskTerm(inversePermProfile .cab profile321, 2, 1, 1)
  change Option.map (@forwardState profile321 .cab)
    (m.step? (inversePermuteState .cab row32101ReverseState2)) = some row32101Start
  have hlegal : m.Legal (inversePermuteState .cab row32101ReverseState2) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .cab row32101ReverseState2) =
      inversePermuteState .cab row32101Start := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- The fixed directed forward witness list for row `321-01`. -/
def row32101ForwardMoves : List (FixedMoveData profile321) :=
  [row32101ForwardMove1, row32101ForwardMove2, row32101ForwardMove3]

/-- The fixed directed reverse witness list for row `321-01`. -/
def row32101ReverseMoves : List (FixedMoveData profile321) :=
  [row32101ReverseMove1, row32101ReverseMove2, row32101ReverseMove3]

/-- The heterogeneous raw replay data for computationally selected row `321-01`. -/
def row32101 : ReplayRow where
  profile := profile321
  start := row32101Start
  finish := row32101Finish
  forward := row32101ForwardMoves
  reverse := row32101ReverseMoves

/-- The exact forward run equation for row `321-01`. -/
theorem run_row32101ForwardMoves :
    run? row32101Start row32101ForwardMoves = some row32101Finish := by
  simp only [row32101ForwardMoves, run?, step_row32101ForwardMove1, Option.bind_some, step_row32101ForwardMove2, Option.bind_some, step_row32101ForwardMove3]

/-- The exact reverse run equation for row `321-01`. -/
theorem run_row32101ReverseMoves :
    run? row32101Finish row32101ReverseMoves = some row32101Start := by
  simp only [row32101ReverseMoves, run?, step_row32101ReverseMove1, Option.bind_some, step_row32101ReverseMove2, Option.bind_some, step_row32101ReverseMove3]

/-- Both exact directed runs of row `321-01` pass. -/
theorem row32101_passes : row32101.Passes := by
  simpa only [row32101, ReplayRow.Passes] using
    And.intro run_row32101ForwardMoves run_row32101ReverseMoves

/-- The actual `run?_path` data for the forward replay of row `321-01`. -/
def row32101ForwardPath :
    MovePath (@AllModeMove profile321) row32101Start row32101Finish :=
  run?_path run_row32101ForwardMoves

/-- The forward replay path of row `321-01` has exactly 3 edges. -/
@[simp] theorem row32101ForwardPath_length :
    row32101ForwardPath.length = 3 := by
  rw [row32101ForwardPath, run?_path_length]
  rfl

/-- The actual `run?_path` data for the reverse replay of row `321-01`. -/
def row32101ReversePath :
    MovePath (@AllModeMove profile321) row32101Finish row32101Start :=
  run?_path run_row32101ReverseMoves

/-- The reverse replay path of row `321-01` has exactly 3 edges. -/
@[simp] theorem row32101ReversePath_length :
    row32101ReversePath.length = 3 := by
  rw [row32101ReversePath, run?_path_length]
  rfl

/-- Both actual replay paths of row `321-01` have at most three edges. -/
theorem row32101_path_lengths_le_three :
    row32101ForwardPath.length ≤ 3 ∧ row32101ReversePath.length ≤ 3 := by
  rw [row32101ForwardPath_length, row32101ReversePath_length]
  omega

/-- The endpoint states of row `321-01` are disjoint. -/
theorem row32101_disjoint : Disjoint row32101Start row32101Finish := by
  decide

/-- The starting state of row `321-01` has exactly two terms. -/
theorem row32101_card_start : row32101Start.card = 2 := by
  decide

/-- The finishing state of row `321-01` has exactly three terms. -/
theorem row32101_card_finish : row32101Finish.card = 3 := by
  decide

/-- The visible standard-basis masks in the endpoint union of row `321-01` prove its exact factor profile. -/
theorem row32101_exactFactorProfile :
    HasExactFactorProfile (row32101Start ∪ row32101Finish) := by
  constructor
  · unfold firstFactorSpan
    apply (Submodule.eq_top_iff_forall_basis_mem
      (Pi.basisFun F2 (Fin profile321.first))).mpr
    intro i
    rw [Pi.basisFun_apply]
    apply Submodule.subset_span
    fin_cases i <;> decide
  constructor
  · unfold secondFactorSpan
    apply (Submodule.eq_top_iff_forall_basis_mem
      (Pi.basisFun F2 (Fin profile321.second))).mpr
    intro i
    rw [Pi.basisFun_apply]
    apply Submodule.subset_span
    fin_cases i <;> decide
  · unfold thirdFactorSpan
    apply (Submodule.eq_top_iff_forall_basis_mem
      (Pi.basisFun F2 (Fin profile321.third))).mpr
    intro i
    rw [Pi.basisFun_apply]
    apply Submodule.subset_span
    fin_cases i
    decide

/-- The kernel-replayed five-circuit certificate for row `321-01`. -/
def row32101Certificate :
    FiveCircuitCertificate profile321 row32101Start row32101Finish := by
  let cert := replayRow_toFiveCircuitCertificate row32101 row32101_passes
    (by change Disjoint row32101Start row32101Finish; exact row32101_disjoint)
    (by change row32101Start.card = 2; exact row32101_card_start)
    (by change row32101Finish.card = 3; exact row32101_card_finish)
    (by simp only [row32101, row32101ForwardMoves, List.length_cons,
      List.length_nil]; omega)
    (by simp only [row32101, row32101ReverseMoves, List.length_cons,
      List.length_nil]; omega)
    (by
      change HasExactFactorProfile (row32101Start ∪ row32101Finish)
      exact row32101_exactFactorProfile)
  change FiveCircuitCertificate profile321 row32101Start row32101Finish at cert
  exact cert

/-- The heterogeneous certified wrapper for computationally selected row `321-01`. -/
def certified32101 : CertifiedReplayRow where
  row := row32101
  passes := row32101_passes
  disjoint := by change Disjoint row32101Start row32101Finish; exact row32101_disjoint
  card_start := by change row32101Start.card = 2; exact row32101_card_start
  card_finish := by change row32101Finish.card = 3; exact row32101_card_finish
  forward_length_le := by simp only [row32101, row32101ForwardMoves, List.length_cons, List.length_nil]; omega
  reverse_length_le := by simp only [row32101, row32101ReverseMoves, List.length_cons, List.length_nil]; omega
  exact_profile := by
    change HasExactFactorProfile (row32101Start ∪ row32101Finish)
    exact row32101_exactFactorProfile

/-! ## Computationally selected and replayed row `321-02` -/

/-- The two-term starting state of computationally selected row `321-02`. -/
def row32102Start : State profile321 :=
  {maskTerm(profile321, 2, 3, 1),
   maskTerm(profile321, 4, 3, 1)}

/-- The three-term finishing state of computationally selected row `321-02`. -/
def row32102Finish : State profile321 :=
  {maskTerm(profile321, 1, 1, 1),
   maskTerm(profile321, 1, 2, 1),
   maskTerm(profile321, 7, 3, 1)}

/-- Target-coordinate intermediate state 1 on the forward replay of row `321-02`. -/
def row32102ForwardState1 : State profile321 :=
  {maskTerm(profile321, 1, 3, 1),
   maskTerm(profile321, 3, 3, 1),
   maskTerm(profile321, 4, 3, 1)}

/-- Target-coordinate intermediate state 2 on the forward replay of row `321-02`. -/
def row32102ForwardState2 : State profile321 :=
  {maskTerm(profile321, 1, 3, 1),
   maskTerm(profile321, 7, 3, 1)}

/-- Target-coordinate intermediate state 1 on the reverse replay of row `321-02`. -/
def row32102ReverseState1 : State profile321 :=
  {maskTerm(profile321, 1, 3, 1),
   maskTerm(profile321, 7, 3, 1)}

/-- Target-coordinate intermediate state 2 on the reverse replay of row `321-02`. -/
def row32102ReverseState2 : State profile321 :=
  {maskTerm(profile321, 1, 3, 1),
   maskTerm(profile321, 3, 3, 1),
   maskTerm(profile321, 4, 3, 1)}

/-- The exact source-coordinate split data for forward step 1 of row `321-02`. -/
def row32102ForwardMove1 : FixedMoveData profile321 :=
  ⟨.abc, .split
      maskTerm(inversePermProfile .abc profile321, 2, 3, 1)
      maskTerm(inversePermProfile .abc profile321, 1, 3, 1)
      maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩

/-- The exact source-coordinate reduction data for forward step 2 of row `321-02`. -/
def row32102ForwardMove2 : FixedMoveData profile321 :=
  ⟨.abc, .reduction
      maskTerm(inversePermProfile .abc profile321, 3, 3, 1)
      maskTerm(inversePermProfile .abc profile321, 4, 3, 1)
      maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩

/-- The exact source-coordinate split data for forward step 3 of row `321-02`. -/
def row32102ForwardMove3 : FixedMoveData profile321 :=
  ⟨.cab, .split
      maskTerm(inversePermProfile .cab profile321, 3, 1, 1)
      maskTerm(inversePermProfile .cab profile321, 1, 1, 1)
      maskTerm(inversePermProfile .cab profile321, 2, 1, 1)⟩

/-- The exact source-coordinate reduction data for reverse step 1 of row `321-02`. -/
def row32102ReverseMove1 : FixedMoveData profile321 :=
  ⟨.cab, .reduction
      maskTerm(inversePermProfile .cab profile321, 1, 1, 1)
      maskTerm(inversePermProfile .cab profile321, 2, 1, 1)
      maskTerm(inversePermProfile .cab profile321, 3, 1, 1)⟩

/-- The exact source-coordinate split data for reverse step 2 of row `321-02`. -/
def row32102ReverseMove2 : FixedMoveData profile321 :=
  ⟨.abc, .split
      maskTerm(inversePermProfile .abc profile321, 7, 3, 1)
      maskTerm(inversePermProfile .abc profile321, 3, 3, 1)
      maskTerm(inversePermProfile .abc profile321, 4, 3, 1)⟩

/-- The exact source-coordinate reduction data for reverse step 3 of row `321-02`. -/
def row32102ReverseMove3 : FixedMoveData profile321 :=
  ⟨.abc, .reduction
      maskTerm(inversePermProfile .abc profile321, 1, 3, 1)
      maskTerm(inversePermProfile .abc profile321, 3, 3, 1)
      maskTerm(inversePermProfile .abc profile321, 2, 3, 1)⟩

/-- Kernel replay of the directed Split at forward step 1 of row `321-02`. -/
theorem step_row32102ForwardMove1 :
    row32102ForwardMove1.step? row32102Start = some row32102ForwardState1 := by
  unfold FixedMoveData.step? row32102ForwardMove1
  let m : SourceMoveData (inversePermProfile .abc profile321) :=
    .split
          maskTerm(inversePermProfile .abc profile321, 2, 3, 1)
          maskTerm(inversePermProfile .abc profile321, 1, 3, 1)
          maskTerm(inversePermProfile .abc profile321, 3, 3, 1)
  change Option.map (@forwardState profile321 .abc)
    (m.step? (inversePermuteState .abc row32102Start)) = some row32102ForwardState1
  have hlegal : m.Legal (inversePermuteState .abc row32102Start) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .abc row32102Start) =
      inversePermuteState .abc row32102ForwardState1 := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Reduction at forward step 2 of row `321-02`. -/
theorem step_row32102ForwardMove2 :
    row32102ForwardMove2.step? row32102ForwardState1 = some row32102ForwardState2 := by
  unfold FixedMoveData.step? row32102ForwardMove2
  let m : SourceMoveData (inversePermProfile .abc profile321) :=
    .reduction
          maskTerm(inversePermProfile .abc profile321, 3, 3, 1)
          maskTerm(inversePermProfile .abc profile321, 4, 3, 1)
          maskTerm(inversePermProfile .abc profile321, 7, 3, 1)
  change Option.map (@forwardState profile321 .abc)
    (m.step? (inversePermuteState .abc row32102ForwardState1)) = some row32102ForwardState2
  have hlegal : m.Legal (inversePermuteState .abc row32102ForwardState1) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .abc row32102ForwardState1) =
      inversePermuteState .abc row32102ForwardState2 := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Split at forward step 3 of row `321-02`. -/
theorem step_row32102ForwardMove3 :
    row32102ForwardMove3.step? row32102ForwardState2 = some row32102Finish := by
  unfold FixedMoveData.step? row32102ForwardMove3
  let m : SourceMoveData (inversePermProfile .cab profile321) :=
    .split
          maskTerm(inversePermProfile .cab profile321, 3, 1, 1)
          maskTerm(inversePermProfile .cab profile321, 1, 1, 1)
          maskTerm(inversePermProfile .cab profile321, 2, 1, 1)
  change Option.map (@forwardState profile321 .cab)
    (m.step? (inversePermuteState .cab row32102ForwardState2)) = some row32102Finish
  have hlegal : m.Legal (inversePermuteState .cab row32102ForwardState2) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .cab row32102ForwardState2) =
      inversePermuteState .cab row32102Finish := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Reduction at reverse step 1 of row `321-02`. -/
theorem step_row32102ReverseMove1 :
    row32102ReverseMove1.step? row32102Finish = some row32102ReverseState1 := by
  unfold FixedMoveData.step? row32102ReverseMove1
  let m : SourceMoveData (inversePermProfile .cab profile321) :=
    .reduction
          maskTerm(inversePermProfile .cab profile321, 1, 1, 1)
          maskTerm(inversePermProfile .cab profile321, 2, 1, 1)
          maskTerm(inversePermProfile .cab profile321, 3, 1, 1)
  change Option.map (@forwardState profile321 .cab)
    (m.step? (inversePermuteState .cab row32102Finish)) = some row32102ReverseState1
  have hlegal : m.Legal (inversePermuteState .cab row32102Finish) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .cab row32102Finish) =
      inversePermuteState .cab row32102ReverseState1 := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Split at reverse step 2 of row `321-02`. -/
theorem step_row32102ReverseMove2 :
    row32102ReverseMove2.step? row32102ReverseState1 = some row32102ReverseState2 := by
  unfold FixedMoveData.step? row32102ReverseMove2
  let m : SourceMoveData (inversePermProfile .abc profile321) :=
    .split
          maskTerm(inversePermProfile .abc profile321, 7, 3, 1)
          maskTerm(inversePermProfile .abc profile321, 3, 3, 1)
          maskTerm(inversePermProfile .abc profile321, 4, 3, 1)
  change Option.map (@forwardState profile321 .abc)
    (m.step? (inversePermuteState .abc row32102ReverseState1)) = some row32102ReverseState2
  have hlegal : m.Legal (inversePermuteState .abc row32102ReverseState1) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .abc row32102ReverseState1) =
      inversePermuteState .abc row32102ReverseState2 := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Reduction at reverse step 3 of row `321-02`. -/
theorem step_row32102ReverseMove3 :
    row32102ReverseMove3.step? row32102ReverseState2 = some row32102Start := by
  unfold FixedMoveData.step? row32102ReverseMove3
  let m : SourceMoveData (inversePermProfile .abc profile321) :=
    .reduction
          maskTerm(inversePermProfile .abc profile321, 1, 3, 1)
          maskTerm(inversePermProfile .abc profile321, 3, 3, 1)
          maskTerm(inversePermProfile .abc profile321, 2, 3, 1)
  change Option.map (@forwardState profile321 .abc)
    (m.step? (inversePermuteState .abc row32102ReverseState2)) = some row32102Start
  have hlegal : m.Legal (inversePermuteState .abc row32102ReverseState2) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .abc row32102ReverseState2) =
      inversePermuteState .abc row32102Start := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- The fixed directed forward witness list for row `321-02`. -/
def row32102ForwardMoves : List (FixedMoveData profile321) :=
  [row32102ForwardMove1, row32102ForwardMove2, row32102ForwardMove3]

/-- The fixed directed reverse witness list for row `321-02`. -/
def row32102ReverseMoves : List (FixedMoveData profile321) :=
  [row32102ReverseMove1, row32102ReverseMove2, row32102ReverseMove3]

/-- The heterogeneous raw replay data for computationally selected row `321-02`. -/
def row32102 : ReplayRow where
  profile := profile321
  start := row32102Start
  finish := row32102Finish
  forward := row32102ForwardMoves
  reverse := row32102ReverseMoves

/-- The exact forward run equation for row `321-02`. -/
theorem run_row32102ForwardMoves :
    run? row32102Start row32102ForwardMoves = some row32102Finish := by
  simp only [row32102ForwardMoves, run?, step_row32102ForwardMove1, Option.bind_some, step_row32102ForwardMove2, Option.bind_some, step_row32102ForwardMove3]

/-- The exact reverse run equation for row `321-02`. -/
theorem run_row32102ReverseMoves :
    run? row32102Finish row32102ReverseMoves = some row32102Start := by
  simp only [row32102ReverseMoves, run?, step_row32102ReverseMove1, Option.bind_some, step_row32102ReverseMove2, Option.bind_some, step_row32102ReverseMove3]

/-- Both exact directed runs of row `321-02` pass. -/
theorem row32102_passes : row32102.Passes := by
  simpa only [row32102, ReplayRow.Passes] using
    And.intro run_row32102ForwardMoves run_row32102ReverseMoves

/-- The actual `run?_path` data for the forward replay of row `321-02`. -/
def row32102ForwardPath :
    MovePath (@AllModeMove profile321) row32102Start row32102Finish :=
  run?_path run_row32102ForwardMoves

/-- The forward replay path of row `321-02` has exactly 3 edges. -/
@[simp] theorem row32102ForwardPath_length :
    row32102ForwardPath.length = 3 := by
  rw [row32102ForwardPath, run?_path_length]
  rfl

/-- The actual `run?_path` data for the reverse replay of row `321-02`. -/
def row32102ReversePath :
    MovePath (@AllModeMove profile321) row32102Finish row32102Start :=
  run?_path run_row32102ReverseMoves

/-- The reverse replay path of row `321-02` has exactly 3 edges. -/
@[simp] theorem row32102ReversePath_length :
    row32102ReversePath.length = 3 := by
  rw [row32102ReversePath, run?_path_length]
  rfl

/-- Both actual replay paths of row `321-02` have at most three edges. -/
theorem row32102_path_lengths_le_three :
    row32102ForwardPath.length ≤ 3 ∧ row32102ReversePath.length ≤ 3 := by
  rw [row32102ForwardPath_length, row32102ReversePath_length]
  omega

/-- The endpoint states of row `321-02` are disjoint. -/
theorem row32102_disjoint : Disjoint row32102Start row32102Finish := by
  decide

/-- The starting state of row `321-02` has exactly two terms. -/
theorem row32102_card_start : row32102Start.card = 2 := by
  decide

/-- The finishing state of row `321-02` has exactly three terms. -/
theorem row32102_card_finish : row32102Finish.card = 3 := by
  decide

/-- The visible standard-basis masks in the endpoint union of row `321-02` prove its exact factor profile. -/
theorem row32102_exactFactorProfile :
    HasExactFactorProfile (row32102Start ∪ row32102Finish) := by
  constructor
  · unfold firstFactorSpan
    apply (Submodule.eq_top_iff_forall_basis_mem
      (Pi.basisFun F2 (Fin profile321.first))).mpr
    intro i
    rw [Pi.basisFun_apply]
    apply Submodule.subset_span
    fin_cases i <;> decide
  constructor
  · unfold secondFactorSpan
    apply (Submodule.eq_top_iff_forall_basis_mem
      (Pi.basisFun F2 (Fin profile321.second))).mpr
    intro i
    rw [Pi.basisFun_apply]
    apply Submodule.subset_span
    fin_cases i <;> decide
  · unfold thirdFactorSpan
    apply (Submodule.eq_top_iff_forall_basis_mem
      (Pi.basisFun F2 (Fin profile321.third))).mpr
    intro i
    rw [Pi.basisFun_apply]
    apply Submodule.subset_span
    fin_cases i
    decide

/-- The kernel-replayed five-circuit certificate for row `321-02`. -/
def row32102Certificate :
    FiveCircuitCertificate profile321 row32102Start row32102Finish := by
  let cert := replayRow_toFiveCircuitCertificate row32102 row32102_passes
    (by change Disjoint row32102Start row32102Finish; exact row32102_disjoint)
    (by change row32102Start.card = 2; exact row32102_card_start)
    (by change row32102Finish.card = 3; exact row32102_card_finish)
    (by simp only [row32102, row32102ForwardMoves, List.length_cons,
      List.length_nil]; omega)
    (by simp only [row32102, row32102ReverseMoves, List.length_cons,
      List.length_nil]; omega)
    (by
      change HasExactFactorProfile (row32102Start ∪ row32102Finish)
      exact row32102_exactFactorProfile)
  change FiveCircuitCertificate profile321 row32102Start row32102Finish at cert
  exact cert

/-- The heterogeneous certified wrapper for computationally selected row `321-02`. -/
def certified32102 : CertifiedReplayRow where
  row := row32102
  passes := row32102_passes
  disjoint := by change Disjoint row32102Start row32102Finish; exact row32102_disjoint
  card_start := by change row32102Start.card = 2; exact row32102_card_start
  card_finish := by change row32102Finish.card = 3; exact row32102_card_finish
  forward_length_le := by simp only [row32102, row32102ForwardMoves, List.length_cons, List.length_nil]; omega
  reverse_length_le := by simp only [row32102, row32102ReverseMoves, List.length_cons, List.length_nil]; omega
  exact_profile := by
    change HasExactFactorProfile (row32102Start ∪ row32102Finish)
    exact row32102_exactFactorProfile

/-! ## Computationally selected and replayed row `321-03` -/

/-- The two-term starting state of computationally selected row `321-03`. -/
def row32103Start : State profile321 :=
  {maskTerm(profile321, 1, 1, 1),
   maskTerm(profile321, 2, 1, 1)}

/-- The three-term finishing state of computationally selected row `321-03`. -/
def row32103Finish : State profile321 :=
  {maskTerm(profile321, 3, 2, 1),
   maskTerm(profile321, 4, 3, 1),
   maskTerm(profile321, 7, 3, 1)}

/-- Target-coordinate intermediate state 1 on the forward replay of row `321-03`. -/
def row32103ForwardState1 : State profile321 :=
  {maskTerm(profile321, 3, 1, 1)}

/-- Target-coordinate intermediate state 2 on the forward replay of row `321-03`. -/
def row32103ForwardState2 : State profile321 :=
  {maskTerm(profile321, 3, 2, 1),
   maskTerm(profile321, 3, 3, 1)}

/-- Target-coordinate intermediate state 1 on the reverse replay of row `321-03`. -/
def row32103ReverseState1 : State profile321 :=
  {maskTerm(profile321, 3, 2, 1),
   maskTerm(profile321, 3, 3, 1)}

/-- Target-coordinate intermediate state 2 on the reverse replay of row `321-03`. -/
def row32103ReverseState2 : State profile321 :=
  {maskTerm(profile321, 3, 1, 1)}

/-- The exact source-coordinate reduction data for forward step 1 of row `321-03`. -/
def row32103ForwardMove1 : FixedMoveData profile321 :=
  ⟨.abc, .reduction
      maskTerm(inversePermProfile .abc profile321, 1, 1, 1)
      maskTerm(inversePermProfile .abc profile321, 2, 1, 1)
      maskTerm(inversePermProfile .abc profile321, 3, 1, 1)⟩

/-- The exact source-coordinate split data for forward step 2 of row `321-03`. -/
def row32103ForwardMove2 : FixedMoveData profile321 :=
  ⟨.cab, .split
      maskTerm(inversePermProfile .cab profile321, 1, 1, 3)
      maskTerm(inversePermProfile .cab profile321, 2, 1, 3)
      maskTerm(inversePermProfile .cab profile321, 3, 1, 3)⟩

/-- The exact source-coordinate split data for forward step 3 of row `321-03`. -/
def row32103ForwardMove3 : FixedMoveData profile321 :=
  ⟨.abc, .split
      maskTerm(inversePermProfile .abc profile321, 3, 3, 1)
      maskTerm(inversePermProfile .abc profile321, 4, 3, 1)
      maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩

/-- The exact source-coordinate reduction data for reverse step 1 of row `321-03`. -/
def row32103ReverseMove1 : FixedMoveData profile321 :=
  ⟨.abc, .reduction
      maskTerm(inversePermProfile .abc profile321, 4, 3, 1)
      maskTerm(inversePermProfile .abc profile321, 7, 3, 1)
      maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩

/-- The exact source-coordinate reduction data for reverse step 2 of row `321-03`. -/
def row32103ReverseMove2 : FixedMoveData profile321 :=
  ⟨.cab, .reduction
      maskTerm(inversePermProfile .cab profile321, 2, 1, 3)
      maskTerm(inversePermProfile .cab profile321, 3, 1, 3)
      maskTerm(inversePermProfile .cab profile321, 1, 1, 3)⟩

/-- The exact source-coordinate split data for reverse step 3 of row `321-03`. -/
def row32103ReverseMove3 : FixedMoveData profile321 :=
  ⟨.abc, .split
      maskTerm(inversePermProfile .abc profile321, 3, 1, 1)
      maskTerm(inversePermProfile .abc profile321, 1, 1, 1)
      maskTerm(inversePermProfile .abc profile321, 2, 1, 1)⟩

/-- Kernel replay of the directed Reduction at forward step 1 of row `321-03`. -/
theorem step_row32103ForwardMove1 :
    row32103ForwardMove1.step? row32103Start = some row32103ForwardState1 := by
  unfold FixedMoveData.step? row32103ForwardMove1
  let m : SourceMoveData (inversePermProfile .abc profile321) :=
    .reduction
          maskTerm(inversePermProfile .abc profile321, 1, 1, 1)
          maskTerm(inversePermProfile .abc profile321, 2, 1, 1)
          maskTerm(inversePermProfile .abc profile321, 3, 1, 1)
  change Option.map (@forwardState profile321 .abc)
    (m.step? (inversePermuteState .abc row32103Start)) = some row32103ForwardState1
  have hlegal : m.Legal (inversePermuteState .abc row32103Start) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .abc row32103Start) =
      inversePermuteState .abc row32103ForwardState1 := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Split at forward step 2 of row `321-03`. -/
theorem step_row32103ForwardMove2 :
    row32103ForwardMove2.step? row32103ForwardState1 = some row32103ForwardState2 := by
  unfold FixedMoveData.step? row32103ForwardMove2
  let m : SourceMoveData (inversePermProfile .cab profile321) :=
    .split
          maskTerm(inversePermProfile .cab profile321, 1, 1, 3)
          maskTerm(inversePermProfile .cab profile321, 2, 1, 3)
          maskTerm(inversePermProfile .cab profile321, 3, 1, 3)
  change Option.map (@forwardState profile321 .cab)
    (m.step? (inversePermuteState .cab row32103ForwardState1)) = some row32103ForwardState2
  have hlegal : m.Legal (inversePermuteState .cab row32103ForwardState1) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .cab row32103ForwardState1) =
      inversePermuteState .cab row32103ForwardState2 := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Split at forward step 3 of row `321-03`. -/
theorem step_row32103ForwardMove3 :
    row32103ForwardMove3.step? row32103ForwardState2 = some row32103Finish := by
  unfold FixedMoveData.step? row32103ForwardMove3
  let m : SourceMoveData (inversePermProfile .abc profile321) :=
    .split
          maskTerm(inversePermProfile .abc profile321, 3, 3, 1)
          maskTerm(inversePermProfile .abc profile321, 4, 3, 1)
          maskTerm(inversePermProfile .abc profile321, 7, 3, 1)
  change Option.map (@forwardState profile321 .abc)
    (m.step? (inversePermuteState .abc row32103ForwardState2)) = some row32103Finish
  have hlegal : m.Legal (inversePermuteState .abc row32103ForwardState2) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .abc row32103ForwardState2) =
      inversePermuteState .abc row32103Finish := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Reduction at reverse step 1 of row `321-03`. -/
theorem step_row32103ReverseMove1 :
    row32103ReverseMove1.step? row32103Finish = some row32103ReverseState1 := by
  unfold FixedMoveData.step? row32103ReverseMove1
  let m : SourceMoveData (inversePermProfile .abc profile321) :=
    .reduction
          maskTerm(inversePermProfile .abc profile321, 4, 3, 1)
          maskTerm(inversePermProfile .abc profile321, 7, 3, 1)
          maskTerm(inversePermProfile .abc profile321, 3, 3, 1)
  change Option.map (@forwardState profile321 .abc)
    (m.step? (inversePermuteState .abc row32103Finish)) = some row32103ReverseState1
  have hlegal : m.Legal (inversePermuteState .abc row32103Finish) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .abc row32103Finish) =
      inversePermuteState .abc row32103ReverseState1 := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Reduction at reverse step 2 of row `321-03`. -/
theorem step_row32103ReverseMove2 :
    row32103ReverseMove2.step? row32103ReverseState1 = some row32103ReverseState2 := by
  unfold FixedMoveData.step? row32103ReverseMove2
  let m : SourceMoveData (inversePermProfile .cab profile321) :=
    .reduction
          maskTerm(inversePermProfile .cab profile321, 2, 1, 3)
          maskTerm(inversePermProfile .cab profile321, 3, 1, 3)
          maskTerm(inversePermProfile .cab profile321, 1, 1, 3)
  change Option.map (@forwardState profile321 .cab)
    (m.step? (inversePermuteState .cab row32103ReverseState1)) = some row32103ReverseState2
  have hlegal : m.Legal (inversePermuteState .cab row32103ReverseState1) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .cab row32103ReverseState1) =
      inversePermuteState .cab row32103ReverseState2 := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Split at reverse step 3 of row `321-03`. -/
theorem step_row32103ReverseMove3 :
    row32103ReverseMove3.step? row32103ReverseState2 = some row32103Start := by
  unfold FixedMoveData.step? row32103ReverseMove3
  let m : SourceMoveData (inversePermProfile .abc profile321) :=
    .split
          maskTerm(inversePermProfile .abc profile321, 3, 1, 1)
          maskTerm(inversePermProfile .abc profile321, 1, 1, 1)
          maskTerm(inversePermProfile .abc profile321, 2, 1, 1)
  change Option.map (@forwardState profile321 .abc)
    (m.step? (inversePermuteState .abc row32103ReverseState2)) = some row32103Start
  have hlegal : m.Legal (inversePermuteState .abc row32103ReverseState2) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .abc row32103ReverseState2) =
      inversePermuteState .abc row32103Start := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- The fixed directed forward witness list for row `321-03`. -/
def row32103ForwardMoves : List (FixedMoveData profile321) :=
  [row32103ForwardMove1, row32103ForwardMove2, row32103ForwardMove3]

/-- The fixed directed reverse witness list for row `321-03`. -/
def row32103ReverseMoves : List (FixedMoveData profile321) :=
  [row32103ReverseMove1, row32103ReverseMove2, row32103ReverseMove3]

/-- The heterogeneous raw replay data for computationally selected row `321-03`. -/
def row32103 : ReplayRow where
  profile := profile321
  start := row32103Start
  finish := row32103Finish
  forward := row32103ForwardMoves
  reverse := row32103ReverseMoves

/-- The exact forward run equation for row `321-03`. -/
theorem run_row32103ForwardMoves :
    run? row32103Start row32103ForwardMoves = some row32103Finish := by
  simp only [row32103ForwardMoves, run?, step_row32103ForwardMove1, Option.bind_some, step_row32103ForwardMove2, Option.bind_some, step_row32103ForwardMove3]

/-- The exact reverse run equation for row `321-03`. -/
theorem run_row32103ReverseMoves :
    run? row32103Finish row32103ReverseMoves = some row32103Start := by
  simp only [row32103ReverseMoves, run?, step_row32103ReverseMove1, Option.bind_some, step_row32103ReverseMove2, Option.bind_some, step_row32103ReverseMove3]

/-- Both exact directed runs of row `321-03` pass. -/
theorem row32103_passes : row32103.Passes := by
  simpa only [row32103, ReplayRow.Passes] using
    And.intro run_row32103ForwardMoves run_row32103ReverseMoves

/-- The actual `run?_path` data for the forward replay of row `321-03`. -/
def row32103ForwardPath :
    MovePath (@AllModeMove profile321) row32103Start row32103Finish :=
  run?_path run_row32103ForwardMoves

/-- The forward replay path of row `321-03` has exactly 3 edges. -/
@[simp] theorem row32103ForwardPath_length :
    row32103ForwardPath.length = 3 := by
  rw [row32103ForwardPath, run?_path_length]
  rfl

/-- The actual `run?_path` data for the reverse replay of row `321-03`. -/
def row32103ReversePath :
    MovePath (@AllModeMove profile321) row32103Finish row32103Start :=
  run?_path run_row32103ReverseMoves

/-- The reverse replay path of row `321-03` has exactly 3 edges. -/
@[simp] theorem row32103ReversePath_length :
    row32103ReversePath.length = 3 := by
  rw [row32103ReversePath, run?_path_length]
  rfl

/-- Both actual replay paths of row `321-03` have at most three edges. -/
theorem row32103_path_lengths_le_three :
    row32103ForwardPath.length ≤ 3 ∧ row32103ReversePath.length ≤ 3 := by
  rw [row32103ForwardPath_length, row32103ReversePath_length]
  omega

/-- The endpoint states of row `321-03` are disjoint. -/
theorem row32103_disjoint : Disjoint row32103Start row32103Finish := by
  decide

/-- The starting state of row `321-03` has exactly two terms. -/
theorem row32103_card_start : row32103Start.card = 2 := by
  decide

/-- The finishing state of row `321-03` has exactly three terms. -/
theorem row32103_card_finish : row32103Finish.card = 3 := by
  decide

/-- The visible standard-basis masks in the endpoint union of row `321-03` prove its exact factor profile. -/
theorem row32103_exactFactorProfile :
    HasExactFactorProfile (row32103Start ∪ row32103Finish) := by
  constructor
  · unfold firstFactorSpan
    apply (Submodule.eq_top_iff_forall_basis_mem
      (Pi.basisFun F2 (Fin profile321.first))).mpr
    intro i
    rw [Pi.basisFun_apply]
    apply Submodule.subset_span
    fin_cases i <;> decide
  constructor
  · unfold secondFactorSpan
    apply (Submodule.eq_top_iff_forall_basis_mem
      (Pi.basisFun F2 (Fin profile321.second))).mpr
    intro i
    rw [Pi.basisFun_apply]
    apply Submodule.subset_span
    fin_cases i <;> decide
  · unfold thirdFactorSpan
    apply (Submodule.eq_top_iff_forall_basis_mem
      (Pi.basisFun F2 (Fin profile321.third))).mpr
    intro i
    rw [Pi.basisFun_apply]
    apply Submodule.subset_span
    fin_cases i
    decide

/-- The kernel-replayed five-circuit certificate for row `321-03`. -/
def row32103Certificate :
    FiveCircuitCertificate profile321 row32103Start row32103Finish := by
  let cert := replayRow_toFiveCircuitCertificate row32103 row32103_passes
    (by change Disjoint row32103Start row32103Finish; exact row32103_disjoint)
    (by change row32103Start.card = 2; exact row32103_card_start)
    (by change row32103Finish.card = 3; exact row32103_card_finish)
    (by simp only [row32103, row32103ForwardMoves, List.length_cons,
      List.length_nil]; omega)
    (by simp only [row32103, row32103ReverseMoves, List.length_cons,
      List.length_nil]; omega)
    (by
      change HasExactFactorProfile (row32103Start ∪ row32103Finish)
      exact row32103_exactFactorProfile)
  change FiveCircuitCertificate profile321 row32103Start row32103Finish at cert
  exact cert

/-- The heterogeneous certified wrapper for computationally selected row `321-03`. -/
def certified32103 : CertifiedReplayRow where
  row := row32103
  passes := row32103_passes
  disjoint := by change Disjoint row32103Start row32103Finish; exact row32103_disjoint
  card_start := by change row32103Start.card = 2; exact row32103_card_start
  card_finish := by change row32103Finish.card = 3; exact row32103_card_finish
  forward_length_le := by simp only [row32103, row32103ForwardMoves, List.length_cons, List.length_nil]; omega
  reverse_length_le := by simp only [row32103, row32103ReverseMoves, List.length_cons, List.length_nil]; omega
  exact_profile := by
    change HasExactFactorProfile (row32103Start ∪ row32103Finish)
    exact row32103_exactFactorProfile

/-! ## Computationally selected and replayed row `321-04` -/

/-- The two-term starting state of computationally selected row `321-04`. -/
def row32104Start : State profile321 :=
  {maskTerm(profile321, 1, 1, 1),
   maskTerm(profile321, 2, 3, 1)}

/-- The three-term finishing state of computationally selected row `321-04`. -/
def row32104Finish : State profile321 :=
  {maskTerm(profile321, 1, 2, 1),
   maskTerm(profile321, 4, 3, 1),
   maskTerm(profile321, 7, 3, 1)}

/-- Target-coordinate intermediate state 1 on the forward replay of row `321-04`. -/
def row32104ForwardState1 : State profile321 :=
  {maskTerm(profile321, 1, 2, 1),
   maskTerm(profile321, 3, 3, 1)}

/-- Target-coordinate intermediate state 1 on the reverse replay of row `321-04`. -/
def row32104ReverseState1 : State profile321 :=
  {maskTerm(profile321, 1, 2, 1),
   maskTerm(profile321, 3, 3, 1)}

/-- The exact source-coordinate flip data for forward step 1 of row `321-04`. -/
def row32104ForwardMove1 : FixedMoveData profile321 :=
  ⟨.abc, .flip
      maskTerm(inversePermProfile .abc profile321, 2, 3, 1)
      maskTerm(inversePermProfile .abc profile321, 1, 1, 1)
      maskTerm(inversePermProfile .abc profile321, 3, 3, 1)
      maskTerm(inversePermProfile .abc profile321, 1, 2, 1)⟩

/-- The exact source-coordinate split data for forward step 2 of row `321-04`. -/
def row32104ForwardMove2 : FixedMoveData profile321 :=
  ⟨.abc, .split
      maskTerm(inversePermProfile .abc profile321, 3, 3, 1)
      maskTerm(inversePermProfile .abc profile321, 4, 3, 1)
      maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩

/-- The exact source-coordinate reduction data for reverse step 1 of row `321-04`. -/
def row32104ReverseMove1 : FixedMoveData profile321 :=
  ⟨.abc, .reduction
      maskTerm(inversePermProfile .abc profile321, 4, 3, 1)
      maskTerm(inversePermProfile .abc profile321, 7, 3, 1)
      maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩

/-- The exact source-coordinate flip data for reverse step 2 of row `321-04`. -/
def row32104ReverseMove2 : FixedMoveData profile321 :=
  ⟨.abc, .flip
      maskTerm(inversePermProfile .abc profile321, 3, 3, 1)
      maskTerm(inversePermProfile .abc profile321, 1, 2, 1)
      maskTerm(inversePermProfile .abc profile321, 2, 3, 1)
      maskTerm(inversePermProfile .abc profile321, 1, 1, 1)⟩

/-- Kernel replay of the directed Flip at forward step 1 of row `321-04`. -/
theorem step_row32104ForwardMove1 :
    row32104ForwardMove1.step? row32104Start = some row32104ForwardState1 := by
  unfold FixedMoveData.step? row32104ForwardMove1
  let m : SourceMoveData (inversePermProfile .abc profile321) :=
    .flip
          maskTerm(inversePermProfile .abc profile321, 2, 3, 1)
          maskTerm(inversePermProfile .abc profile321, 1, 1, 1)
          maskTerm(inversePermProfile .abc profile321, 3, 3, 1)
          maskTerm(inversePermProfile .abc profile321, 1, 2, 1)
  change Option.map (@forwardState profile321 .abc)
    (m.step? (inversePermuteState .abc row32104Start)) = some row32104ForwardState1
  have hlegal : m.Legal (inversePermuteState .abc row32104Start) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .abc row32104Start) =
      inversePermuteState .abc row32104ForwardState1 := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Split at forward step 2 of row `321-04`. -/
theorem step_row32104ForwardMove2 :
    row32104ForwardMove2.step? row32104ForwardState1 = some row32104Finish := by
  unfold FixedMoveData.step? row32104ForwardMove2
  let m : SourceMoveData (inversePermProfile .abc profile321) :=
    .split
          maskTerm(inversePermProfile .abc profile321, 3, 3, 1)
          maskTerm(inversePermProfile .abc profile321, 4, 3, 1)
          maskTerm(inversePermProfile .abc profile321, 7, 3, 1)
  change Option.map (@forwardState profile321 .abc)
    (m.step? (inversePermuteState .abc row32104ForwardState1)) = some row32104Finish
  have hlegal : m.Legal (inversePermuteState .abc row32104ForwardState1) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .abc row32104ForwardState1) =
      inversePermuteState .abc row32104Finish := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Reduction at reverse step 1 of row `321-04`. -/
theorem step_row32104ReverseMove1 :
    row32104ReverseMove1.step? row32104Finish = some row32104ReverseState1 := by
  unfold FixedMoveData.step? row32104ReverseMove1
  let m : SourceMoveData (inversePermProfile .abc profile321) :=
    .reduction
          maskTerm(inversePermProfile .abc profile321, 4, 3, 1)
          maskTerm(inversePermProfile .abc profile321, 7, 3, 1)
          maskTerm(inversePermProfile .abc profile321, 3, 3, 1)
  change Option.map (@forwardState profile321 .abc)
    (m.step? (inversePermuteState .abc row32104Finish)) = some row32104ReverseState1
  have hlegal : m.Legal (inversePermuteState .abc row32104Finish) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .abc row32104Finish) =
      inversePermuteState .abc row32104ReverseState1 := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Flip at reverse step 2 of row `321-04`. -/
theorem step_row32104ReverseMove2 :
    row32104ReverseMove2.step? row32104ReverseState1 = some row32104Start := by
  unfold FixedMoveData.step? row32104ReverseMove2
  let m : SourceMoveData (inversePermProfile .abc profile321) :=
    .flip
          maskTerm(inversePermProfile .abc profile321, 3, 3, 1)
          maskTerm(inversePermProfile .abc profile321, 1, 2, 1)
          maskTerm(inversePermProfile .abc profile321, 2, 3, 1)
          maskTerm(inversePermProfile .abc profile321, 1, 1, 1)
  change Option.map (@forwardState profile321 .abc)
    (m.step? (inversePermuteState .abc row32104ReverseState1)) = some row32104Start
  have hlegal : m.Legal (inversePermuteState .abc row32104ReverseState1) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .abc row32104ReverseState1) =
      inversePermuteState .abc row32104Start := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- The fixed directed forward witness list for row `321-04`. -/
def row32104ForwardMoves : List (FixedMoveData profile321) :=
  [row32104ForwardMove1, row32104ForwardMove2]

/-- The fixed directed reverse witness list for row `321-04`. -/
def row32104ReverseMoves : List (FixedMoveData profile321) :=
  [row32104ReverseMove1, row32104ReverseMove2]

/-- The heterogeneous raw replay data for computationally selected row `321-04`. -/
def row32104 : ReplayRow where
  profile := profile321
  start := row32104Start
  finish := row32104Finish
  forward := row32104ForwardMoves
  reverse := row32104ReverseMoves

/-- The exact forward run equation for row `321-04`. -/
theorem run_row32104ForwardMoves :
    run? row32104Start row32104ForwardMoves = some row32104Finish := by
  simp only [row32104ForwardMoves, run?, step_row32104ForwardMove1, Option.bind_some, step_row32104ForwardMove2]

/-- The exact reverse run equation for row `321-04`. -/
theorem run_row32104ReverseMoves :
    run? row32104Finish row32104ReverseMoves = some row32104Start := by
  simp only [row32104ReverseMoves, run?, step_row32104ReverseMove1, Option.bind_some, step_row32104ReverseMove2]

/-- Both exact directed runs of row `321-04` pass. -/
theorem row32104_passes : row32104.Passes := by
  simpa only [row32104, ReplayRow.Passes] using
    And.intro run_row32104ForwardMoves run_row32104ReverseMoves

/-- The actual `run?_path` data for the forward replay of row `321-04`. -/
def row32104ForwardPath :
    MovePath (@AllModeMove profile321) row32104Start row32104Finish :=
  run?_path run_row32104ForwardMoves

/-- The forward replay path of row `321-04` has exactly 2 edges. -/
@[simp] theorem row32104ForwardPath_length :
    row32104ForwardPath.length = 2 := by
  rw [row32104ForwardPath, run?_path_length]
  rfl

/-- The actual `run?_path` data for the reverse replay of row `321-04`. -/
def row32104ReversePath :
    MovePath (@AllModeMove profile321) row32104Finish row32104Start :=
  run?_path run_row32104ReverseMoves

/-- The reverse replay path of row `321-04` has exactly 2 edges. -/
@[simp] theorem row32104ReversePath_length :
    row32104ReversePath.length = 2 := by
  rw [row32104ReversePath, run?_path_length]
  rfl

/-- Both actual replay paths of row `321-04` have at most three edges. -/
theorem row32104_path_lengths_le_three :
    row32104ForwardPath.length ≤ 3 ∧ row32104ReversePath.length ≤ 3 := by
  rw [row32104ForwardPath_length, row32104ReversePath_length]
  omega

/-- The endpoint states of row `321-04` are disjoint. -/
theorem row32104_disjoint : Disjoint row32104Start row32104Finish := by
  decide

/-- The starting state of row `321-04` has exactly two terms. -/
theorem row32104_card_start : row32104Start.card = 2 := by
  decide

/-- The finishing state of row `321-04` has exactly three terms. -/
theorem row32104_card_finish : row32104Finish.card = 3 := by
  decide

/-- The visible standard-basis masks in the endpoint union of row `321-04` prove its exact factor profile. -/
theorem row32104_exactFactorProfile :
    HasExactFactorProfile (row32104Start ∪ row32104Finish) := by
  constructor
  · unfold firstFactorSpan
    apply (Submodule.eq_top_iff_forall_basis_mem
      (Pi.basisFun F2 (Fin profile321.first))).mpr
    intro i
    rw [Pi.basisFun_apply]
    apply Submodule.subset_span
    fin_cases i <;> decide
  constructor
  · unfold secondFactorSpan
    apply (Submodule.eq_top_iff_forall_basis_mem
      (Pi.basisFun F2 (Fin profile321.second))).mpr
    intro i
    rw [Pi.basisFun_apply]
    apply Submodule.subset_span
    fin_cases i <;> decide
  · unfold thirdFactorSpan
    apply (Submodule.eq_top_iff_forall_basis_mem
      (Pi.basisFun F2 (Fin profile321.third))).mpr
    intro i
    rw [Pi.basisFun_apply]
    apply Submodule.subset_span
    fin_cases i
    decide

/-- The kernel-replayed five-circuit certificate for row `321-04`. -/
def row32104Certificate :
    FiveCircuitCertificate profile321 row32104Start row32104Finish := by
  let cert := replayRow_toFiveCircuitCertificate row32104 row32104_passes
    (by change Disjoint row32104Start row32104Finish; exact row32104_disjoint)
    (by change row32104Start.card = 2; exact row32104_card_start)
    (by change row32104Finish.card = 3; exact row32104_card_finish)
    (by simp only [row32104, row32104ForwardMoves, List.length_cons,
      List.length_nil]; omega)
    (by simp only [row32104, row32104ReverseMoves, List.length_cons,
      List.length_nil]; omega)
    (by
      change HasExactFactorProfile (row32104Start ∪ row32104Finish)
      exact row32104_exactFactorProfile)
  change FiveCircuitCertificate profile321 row32104Start row32104Finish at cert
  exact cert

/-- The heterogeneous certified wrapper for computationally selected row `321-04`. -/
def certified32104 : CertifiedReplayRow where
  row := row32104
  passes := row32104_passes
  disjoint := by change Disjoint row32104Start row32104Finish; exact row32104_disjoint
  card_start := by change row32104Start.card = 2; exact row32104_card_start
  card_finish := by change row32104Finish.card = 3; exact row32104_card_finish
  forward_length_le := by simp only [row32104, row32104ForwardMoves, List.length_cons, List.length_nil]; omega
  reverse_length_le := by simp only [row32104, row32104ReverseMoves, List.length_cons, List.length_nil]; omega
  exact_profile := by
    change HasExactFactorProfile (row32104Start ∪ row32104Finish)
    exact row32104_exactFactorProfile

/-! ## Computationally selected and replayed row `321-05` -/

/-- The two-term starting state of computationally selected row `321-05`. -/
def row32105Start : State profile321 :=
  {maskTerm(profile321, 1, 1, 1),
   maskTerm(profile321, 3, 2, 1)}

/-- The three-term finishing state of computationally selected row `321-05`. -/
def row32105Finish : State profile321 :=
  {maskTerm(profile321, 2, 1, 1),
   maskTerm(profile321, 4, 3, 1),
   maskTerm(profile321, 7, 3, 1)}

/-- Target-coordinate intermediate state 1 on the forward replay of row `321-05`. -/
def row32105ForwardState1 : State profile321 :=
  {maskTerm(profile321, 2, 1, 1),
   maskTerm(profile321, 3, 3, 1)}

/-- Target-coordinate intermediate state 1 on the reverse replay of row `321-05`. -/
def row32105ReverseState1 : State profile321 :=
  {maskTerm(profile321, 2, 1, 1),
   maskTerm(profile321, 3, 3, 1)}

/-- The exact source-coordinate flip data for forward step 1 of row `321-05`. -/
def row32105ForwardMove1 : FixedMoveData profile321 :=
  ⟨.abc, .flip
      maskTerm(inversePermProfile .abc profile321, 1, 1, 1)
      maskTerm(inversePermProfile .abc profile321, 3, 2, 1)
      maskTerm(inversePermProfile .abc profile321, 2, 1, 1)
      maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩

/-- The exact source-coordinate split data for forward step 2 of row `321-05`. -/
def row32105ForwardMove2 : FixedMoveData profile321 :=
  ⟨.abc, .split
      maskTerm(inversePermProfile .abc profile321, 3, 3, 1)
      maskTerm(inversePermProfile .abc profile321, 4, 3, 1)
      maskTerm(inversePermProfile .abc profile321, 7, 3, 1)⟩

/-- The exact source-coordinate reduction data for reverse step 1 of row `321-05`. -/
def row32105ReverseMove1 : FixedMoveData profile321 :=
  ⟨.abc, .reduction
      maskTerm(inversePermProfile .abc profile321, 4, 3, 1)
      maskTerm(inversePermProfile .abc profile321, 7, 3, 1)
      maskTerm(inversePermProfile .abc profile321, 3, 3, 1)⟩

/-- The exact source-coordinate flip data for reverse step 2 of row `321-05`. -/
def row32105ReverseMove2 : FixedMoveData profile321 :=
  ⟨.abc, .flip
      maskTerm(inversePermProfile .abc profile321, 2, 1, 1)
      maskTerm(inversePermProfile .abc profile321, 3, 3, 1)
      maskTerm(inversePermProfile .abc profile321, 1, 1, 1)
      maskTerm(inversePermProfile .abc profile321, 3, 2, 1)⟩

/-- Kernel replay of the directed Flip at forward step 1 of row `321-05`. -/
theorem step_row32105ForwardMove1 :
    row32105ForwardMove1.step? row32105Start = some row32105ForwardState1 := by
  unfold FixedMoveData.step? row32105ForwardMove1
  let m : SourceMoveData (inversePermProfile .abc profile321) :=
    .flip
          maskTerm(inversePermProfile .abc profile321, 1, 1, 1)
          maskTerm(inversePermProfile .abc profile321, 3, 2, 1)
          maskTerm(inversePermProfile .abc profile321, 2, 1, 1)
          maskTerm(inversePermProfile .abc profile321, 3, 3, 1)
  change Option.map (@forwardState profile321 .abc)
    (m.step? (inversePermuteState .abc row32105Start)) = some row32105ForwardState1
  have hlegal : m.Legal (inversePermuteState .abc row32105Start) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .abc row32105Start) =
      inversePermuteState .abc row32105ForwardState1 := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Split at forward step 2 of row `321-05`. -/
theorem step_row32105ForwardMove2 :
    row32105ForwardMove2.step? row32105ForwardState1 = some row32105Finish := by
  unfold FixedMoveData.step? row32105ForwardMove2
  let m : SourceMoveData (inversePermProfile .abc profile321) :=
    .split
          maskTerm(inversePermProfile .abc profile321, 3, 3, 1)
          maskTerm(inversePermProfile .abc profile321, 4, 3, 1)
          maskTerm(inversePermProfile .abc profile321, 7, 3, 1)
  change Option.map (@forwardState profile321 .abc)
    (m.step? (inversePermuteState .abc row32105ForwardState1)) = some row32105Finish
  have hlegal : m.Legal (inversePermuteState .abc row32105ForwardState1) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .abc row32105ForwardState1) =
      inversePermuteState .abc row32105Finish := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Reduction at reverse step 1 of row `321-05`. -/
theorem step_row32105ReverseMove1 :
    row32105ReverseMove1.step? row32105Finish = some row32105ReverseState1 := by
  unfold FixedMoveData.step? row32105ReverseMove1
  let m : SourceMoveData (inversePermProfile .abc profile321) :=
    .reduction
          maskTerm(inversePermProfile .abc profile321, 4, 3, 1)
          maskTerm(inversePermProfile .abc profile321, 7, 3, 1)
          maskTerm(inversePermProfile .abc profile321, 3, 3, 1)
  change Option.map (@forwardState profile321 .abc)
    (m.step? (inversePermuteState .abc row32105Finish)) = some row32105ReverseState1
  have hlegal : m.Legal (inversePermuteState .abc row32105Finish) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .abc row32105Finish) =
      inversePermuteState .abc row32105ReverseState1 := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Flip at reverse step 2 of row `321-05`. -/
theorem step_row32105ReverseMove2 :
    row32105ReverseMove2.step? row32105ReverseState1 = some row32105Start := by
  unfold FixedMoveData.step? row32105ReverseMove2
  let m : SourceMoveData (inversePermProfile .abc profile321) :=
    .flip
          maskTerm(inversePermProfile .abc profile321, 2, 1, 1)
          maskTerm(inversePermProfile .abc profile321, 3, 3, 1)
          maskTerm(inversePermProfile .abc profile321, 1, 1, 1)
          maskTerm(inversePermProfile .abc profile321, 3, 2, 1)
  change Option.map (@forwardState profile321 .abc)
    (m.step? (inversePermuteState .abc row32105ReverseState1)) = some row32105Start
  have hlegal : m.Legal (inversePermuteState .abc row32105ReverseState1) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .abc row32105ReverseState1) =
      inversePermuteState .abc row32105Start := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- The fixed directed forward witness list for row `321-05`. -/
def row32105ForwardMoves : List (FixedMoveData profile321) :=
  [row32105ForwardMove1, row32105ForwardMove2]

/-- The fixed directed reverse witness list for row `321-05`. -/
def row32105ReverseMoves : List (FixedMoveData profile321) :=
  [row32105ReverseMove1, row32105ReverseMove2]

/-- The heterogeneous raw replay data for computationally selected row `321-05`. -/
def row32105 : ReplayRow where
  profile := profile321
  start := row32105Start
  finish := row32105Finish
  forward := row32105ForwardMoves
  reverse := row32105ReverseMoves

/-- The exact forward run equation for row `321-05`. -/
theorem run_row32105ForwardMoves :
    run? row32105Start row32105ForwardMoves = some row32105Finish := by
  simp only [row32105ForwardMoves, run?, step_row32105ForwardMove1, Option.bind_some, step_row32105ForwardMove2]

/-- The exact reverse run equation for row `321-05`. -/
theorem run_row32105ReverseMoves :
    run? row32105Finish row32105ReverseMoves = some row32105Start := by
  simp only [row32105ReverseMoves, run?, step_row32105ReverseMove1, Option.bind_some, step_row32105ReverseMove2]

/-- Both exact directed runs of row `321-05` pass. -/
theorem row32105_passes : row32105.Passes := by
  simpa only [row32105, ReplayRow.Passes] using
    And.intro run_row32105ForwardMoves run_row32105ReverseMoves

/-- The actual `run?_path` data for the forward replay of row `321-05`. -/
def row32105ForwardPath :
    MovePath (@AllModeMove profile321) row32105Start row32105Finish :=
  run?_path run_row32105ForwardMoves

/-- The forward replay path of row `321-05` has exactly 2 edges. -/
@[simp] theorem row32105ForwardPath_length :
    row32105ForwardPath.length = 2 := by
  rw [row32105ForwardPath, run?_path_length]
  rfl

/-- The actual `run?_path` data for the reverse replay of row `321-05`. -/
def row32105ReversePath :
    MovePath (@AllModeMove profile321) row32105Finish row32105Start :=
  run?_path run_row32105ReverseMoves

/-- The reverse replay path of row `321-05` has exactly 2 edges. -/
@[simp] theorem row32105ReversePath_length :
    row32105ReversePath.length = 2 := by
  rw [row32105ReversePath, run?_path_length]
  rfl

/-- Both actual replay paths of row `321-05` have at most three edges. -/
theorem row32105_path_lengths_le_three :
    row32105ForwardPath.length ≤ 3 ∧ row32105ReversePath.length ≤ 3 := by
  rw [row32105ForwardPath_length, row32105ReversePath_length]
  omega

/-- The endpoint states of row `321-05` are disjoint. -/
theorem row32105_disjoint : Disjoint row32105Start row32105Finish := by
  decide

/-- The starting state of row `321-05` has exactly two terms. -/
theorem row32105_card_start : row32105Start.card = 2 := by
  decide

/-- The finishing state of row `321-05` has exactly three terms. -/
theorem row32105_card_finish : row32105Finish.card = 3 := by
  decide

/-- The visible standard-basis masks in the endpoint union of row `321-05` prove its exact factor profile. -/
theorem row32105_exactFactorProfile :
    HasExactFactorProfile (row32105Start ∪ row32105Finish) := by
  constructor
  · unfold firstFactorSpan
    apply (Submodule.eq_top_iff_forall_basis_mem
      (Pi.basisFun F2 (Fin profile321.first))).mpr
    intro i
    rw [Pi.basisFun_apply]
    apply Submodule.subset_span
    fin_cases i <;> decide
  constructor
  · unfold secondFactorSpan
    apply (Submodule.eq_top_iff_forall_basis_mem
      (Pi.basisFun F2 (Fin profile321.second))).mpr
    intro i
    rw [Pi.basisFun_apply]
    apply Submodule.subset_span
    fin_cases i <;> decide
  · unfold thirdFactorSpan
    apply (Submodule.eq_top_iff_forall_basis_mem
      (Pi.basisFun F2 (Fin profile321.third))).mpr
    intro i
    rw [Pi.basisFun_apply]
    apply Submodule.subset_span
    fin_cases i
    decide

/-- The kernel-replayed five-circuit certificate for row `321-05`. -/
def row32105Certificate :
    FiveCircuitCertificate profile321 row32105Start row32105Finish := by
  let cert := replayRow_toFiveCircuitCertificate row32105 row32105_passes
    (by change Disjoint row32105Start row32105Finish; exact row32105_disjoint)
    (by change row32105Start.card = 2; exact row32105_card_start)
    (by change row32105Finish.card = 3; exact row32105_card_finish)
    (by simp only [row32105, row32105ForwardMoves, List.length_cons,
      List.length_nil]; omega)
    (by simp only [row32105, row32105ReverseMoves, List.length_cons,
      List.length_nil]; omega)
    (by
      change HasExactFactorProfile (row32105Start ∪ row32105Finish)
      exact row32105_exactFactorProfile)
  change FiveCircuitCertificate profile321 row32105Start row32105Finish at cert
  exact cert

/-- The heterogeneous certified wrapper for computationally selected row `321-05`. -/
def certified32105 : CertifiedReplayRow where
  row := row32105
  passes := row32105_passes
  disjoint := by change Disjoint row32105Start row32105Finish; exact row32105_disjoint
  card_start := by change row32105Start.card = 2; exact row32105_card_start
  card_finish := by change row32105Finish.card = 3; exact row32105_card_finish
  forward_length_le := by simp only [row32105, row32105ForwardMoves, List.length_cons, List.length_nil]; omega
  reverse_length_le := by simp only [row32105, row32105ReverseMoves, List.length_cons, List.length_nil]; omega
  exact_profile := by
    change HasExactFactorProfile (row32105Start ∪ row32105Finish)
    exact row32105_exactFactorProfile

/-! ## Computationally selected and replayed row `321-06` -/

/-- The two-term starting state of computationally selected row `321-06`. -/
def row32106Start : State profile321 :=
  {maskTerm(profile321, 1, 1, 1),
   maskTerm(profile321, 4, 3, 1)}

/-- The three-term finishing state of computationally selected row `321-06`. -/
def row32106Finish : State profile321 :=
  {maskTerm(profile321, 2, 1, 1),
   maskTerm(profile321, 3, 2, 1),
   maskTerm(profile321, 7, 3, 1)}

/-- Target-coordinate intermediate state 1 on the forward replay of row `321-06`. -/
def row32106ForwardState1 : State profile321 :=
  {maskTerm(profile321, 2, 1, 1),
   maskTerm(profile321, 3, 1, 1),
   maskTerm(profile321, 4, 3, 1)}

/-- Target-coordinate intermediate state 1 on the reverse replay of row `321-06`. -/
def row32106ReverseState1 : State profile321 :=
  {maskTerm(profile321, 2, 1, 1),
   maskTerm(profile321, 3, 1, 1),
   maskTerm(profile321, 4, 3, 1)}

/-- The exact source-coordinate split data for forward step 1 of row `321-06`. -/
def row32106ForwardMove1 : FixedMoveData profile321 :=
  ⟨.abc, .split
      maskTerm(inversePermProfile .abc profile321, 1, 1, 1)
      maskTerm(inversePermProfile .abc profile321, 2, 1, 1)
      maskTerm(inversePermProfile .abc profile321, 3, 1, 1)⟩

/-- The exact source-coordinate flip data for forward step 2 of row `321-06`. -/
def row32106ForwardMove2 : FixedMoveData profile321 :=
  ⟨.abc, .flip
      maskTerm(inversePermProfile .abc profile321, 4, 3, 1)
      maskTerm(inversePermProfile .abc profile321, 3, 1, 1)
      maskTerm(inversePermProfile .abc profile321, 7, 3, 1)
      maskTerm(inversePermProfile .abc profile321, 3, 2, 1)⟩

/-- The exact source-coordinate flip data for reverse step 1 of row `321-06`. -/
def row32106ReverseMove1 : FixedMoveData profile321 :=
  ⟨.abc, .flip
      maskTerm(inversePermProfile .abc profile321, 7, 3, 1)
      maskTerm(inversePermProfile .abc profile321, 3, 2, 1)
      maskTerm(inversePermProfile .abc profile321, 4, 3, 1)
      maskTerm(inversePermProfile .abc profile321, 3, 1, 1)⟩

/-- The exact source-coordinate reduction data for reverse step 2 of row `321-06`. -/
def row32106ReverseMove2 : FixedMoveData profile321 :=
  ⟨.abc, .reduction
      maskTerm(inversePermProfile .abc profile321, 2, 1, 1)
      maskTerm(inversePermProfile .abc profile321, 3, 1, 1)
      maskTerm(inversePermProfile .abc profile321, 1, 1, 1)⟩

/-- Kernel replay of the directed Split at forward step 1 of row `321-06`. -/
theorem step_row32106ForwardMove1 :
    row32106ForwardMove1.step? row32106Start = some row32106ForwardState1 := by
  unfold FixedMoveData.step? row32106ForwardMove1
  let m : SourceMoveData (inversePermProfile .abc profile321) :=
    .split
          maskTerm(inversePermProfile .abc profile321, 1, 1, 1)
          maskTerm(inversePermProfile .abc profile321, 2, 1, 1)
          maskTerm(inversePermProfile .abc profile321, 3, 1, 1)
  change Option.map (@forwardState profile321 .abc)
    (m.step? (inversePermuteState .abc row32106Start)) = some row32106ForwardState1
  have hlegal : m.Legal (inversePermuteState .abc row32106Start) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .abc row32106Start) =
      inversePermuteState .abc row32106ForwardState1 := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Flip at forward step 2 of row `321-06`. -/
theorem step_row32106ForwardMove2 :
    row32106ForwardMove2.step? row32106ForwardState1 = some row32106Finish := by
  unfold FixedMoveData.step? row32106ForwardMove2
  let m : SourceMoveData (inversePermProfile .abc profile321) :=
    .flip
          maskTerm(inversePermProfile .abc profile321, 4, 3, 1)
          maskTerm(inversePermProfile .abc profile321, 3, 1, 1)
          maskTerm(inversePermProfile .abc profile321, 7, 3, 1)
          maskTerm(inversePermProfile .abc profile321, 3, 2, 1)
  change Option.map (@forwardState profile321 .abc)
    (m.step? (inversePermuteState .abc row32106ForwardState1)) = some row32106Finish
  have hlegal : m.Legal (inversePermuteState .abc row32106ForwardState1) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .abc row32106ForwardState1) =
      inversePermuteState .abc row32106Finish := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Flip at reverse step 1 of row `321-06`. -/
theorem step_row32106ReverseMove1 :
    row32106ReverseMove1.step? row32106Finish = some row32106ReverseState1 := by
  unfold FixedMoveData.step? row32106ReverseMove1
  let m : SourceMoveData (inversePermProfile .abc profile321) :=
    .flip
          maskTerm(inversePermProfile .abc profile321, 7, 3, 1)
          maskTerm(inversePermProfile .abc profile321, 3, 2, 1)
          maskTerm(inversePermProfile .abc profile321, 4, 3, 1)
          maskTerm(inversePermProfile .abc profile321, 3, 1, 1)
  change Option.map (@forwardState profile321 .abc)
    (m.step? (inversePermuteState .abc row32106Finish)) = some row32106ReverseState1
  have hlegal : m.Legal (inversePermuteState .abc row32106Finish) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .abc row32106Finish) =
      inversePermuteState .abc row32106ReverseState1 := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Reduction at reverse step 2 of row `321-06`. -/
theorem step_row32106ReverseMove2 :
    row32106ReverseMove2.step? row32106ReverseState1 = some row32106Start := by
  unfold FixedMoveData.step? row32106ReverseMove2
  let m : SourceMoveData (inversePermProfile .abc profile321) :=
    .reduction
          maskTerm(inversePermProfile .abc profile321, 2, 1, 1)
          maskTerm(inversePermProfile .abc profile321, 3, 1, 1)
          maskTerm(inversePermProfile .abc profile321, 1, 1, 1)
  change Option.map (@forwardState profile321 .abc)
    (m.step? (inversePermuteState .abc row32106ReverseState1)) = some row32106Start
  have hlegal : m.Legal (inversePermuteState .abc row32106ReverseState1) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .abc row32106ReverseState1) =
      inversePermuteState .abc row32106Start := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- The fixed directed forward witness list for row `321-06`. -/
def row32106ForwardMoves : List (FixedMoveData profile321) :=
  [row32106ForwardMove1, row32106ForwardMove2]

/-- The fixed directed reverse witness list for row `321-06`. -/
def row32106ReverseMoves : List (FixedMoveData profile321) :=
  [row32106ReverseMove1, row32106ReverseMove2]

/-- The heterogeneous raw replay data for computationally selected row `321-06`. -/
def row32106 : ReplayRow where
  profile := profile321
  start := row32106Start
  finish := row32106Finish
  forward := row32106ForwardMoves
  reverse := row32106ReverseMoves

/-- The exact forward run equation for row `321-06`. -/
theorem run_row32106ForwardMoves :
    run? row32106Start row32106ForwardMoves = some row32106Finish := by
  simp only [row32106ForwardMoves, run?, step_row32106ForwardMove1, Option.bind_some, step_row32106ForwardMove2]

/-- The exact reverse run equation for row `321-06`. -/
theorem run_row32106ReverseMoves :
    run? row32106Finish row32106ReverseMoves = some row32106Start := by
  simp only [row32106ReverseMoves, run?, step_row32106ReverseMove1, Option.bind_some, step_row32106ReverseMove2]

/-- Both exact directed runs of row `321-06` pass. -/
theorem row32106_passes : row32106.Passes := by
  simpa only [row32106, ReplayRow.Passes] using
    And.intro run_row32106ForwardMoves run_row32106ReverseMoves

/-- The actual `run?_path` data for the forward replay of row `321-06`. -/
def row32106ForwardPath :
    MovePath (@AllModeMove profile321) row32106Start row32106Finish :=
  run?_path run_row32106ForwardMoves

/-- The forward replay path of row `321-06` has exactly 2 edges. -/
@[simp] theorem row32106ForwardPath_length :
    row32106ForwardPath.length = 2 := by
  rw [row32106ForwardPath, run?_path_length]
  rfl

/-- The actual `run?_path` data for the reverse replay of row `321-06`. -/
def row32106ReversePath :
    MovePath (@AllModeMove profile321) row32106Finish row32106Start :=
  run?_path run_row32106ReverseMoves

/-- The reverse replay path of row `321-06` has exactly 2 edges. -/
@[simp] theorem row32106ReversePath_length :
    row32106ReversePath.length = 2 := by
  rw [row32106ReversePath, run?_path_length]
  rfl

/-- Both actual replay paths of row `321-06` have at most three edges. -/
theorem row32106_path_lengths_le_three :
    row32106ForwardPath.length ≤ 3 ∧ row32106ReversePath.length ≤ 3 := by
  rw [row32106ForwardPath_length, row32106ReversePath_length]
  omega

/-- The endpoint states of row `321-06` are disjoint. -/
theorem row32106_disjoint : Disjoint row32106Start row32106Finish := by
  decide

/-- The starting state of row `321-06` has exactly two terms. -/
theorem row32106_card_start : row32106Start.card = 2 := by
  decide

/-- The finishing state of row `321-06` has exactly three terms. -/
theorem row32106_card_finish : row32106Finish.card = 3 := by
  decide

/-- The visible standard-basis masks in the endpoint union of row `321-06` prove its exact factor profile. -/
theorem row32106_exactFactorProfile :
    HasExactFactorProfile (row32106Start ∪ row32106Finish) := by
  constructor
  · unfold firstFactorSpan
    apply (Submodule.eq_top_iff_forall_basis_mem
      (Pi.basisFun F2 (Fin profile321.first))).mpr
    intro i
    rw [Pi.basisFun_apply]
    apply Submodule.subset_span
    fin_cases i <;> decide
  constructor
  · unfold secondFactorSpan
    apply (Submodule.eq_top_iff_forall_basis_mem
      (Pi.basisFun F2 (Fin profile321.second))).mpr
    intro i
    rw [Pi.basisFun_apply]
    apply Submodule.subset_span
    fin_cases i <;> decide
  · unfold thirdFactorSpan
    apply (Submodule.eq_top_iff_forall_basis_mem
      (Pi.basisFun F2 (Fin profile321.third))).mpr
    intro i
    rw [Pi.basisFun_apply]
    apply Submodule.subset_span
    fin_cases i
    decide

/-- The kernel-replayed five-circuit certificate for row `321-06`. -/
def row32106Certificate :
    FiveCircuitCertificate profile321 row32106Start row32106Finish := by
  let cert := replayRow_toFiveCircuitCertificate row32106 row32106_passes
    (by change Disjoint row32106Start row32106Finish; exact row32106_disjoint)
    (by change row32106Start.card = 2; exact row32106_card_start)
    (by change row32106Finish.card = 3; exact row32106_card_finish)
    (by simp only [row32106, row32106ForwardMoves, List.length_cons,
      List.length_nil]; omega)
    (by simp only [row32106, row32106ReverseMoves, List.length_cons,
      List.length_nil]; omega)
    (by
      change HasExactFactorProfile (row32106Start ∪ row32106Finish)
      exact row32106_exactFactorProfile)
  change FiveCircuitCertificate profile321 row32106Start row32106Finish at cert
  exact cert

/-- The heterogeneous certified wrapper for computationally selected row `321-06`. -/
def certified32106 : CertifiedReplayRow where
  row := row32106
  passes := row32106_passes
  disjoint := by change Disjoint row32106Start row32106Finish; exact row32106_disjoint
  card_start := by change row32106Start.card = 2; exact row32106_card_start
  card_finish := by change row32106Finish.card = 3; exact row32106_card_finish
  forward_length_le := by simp only [row32106, row32106ForwardMoves, List.length_cons, List.length_nil]; omega
  reverse_length_le := by simp only [row32106, row32106ReverseMoves, List.length_cons, List.length_nil]; omega
  exact_profile := by
    change HasExactFactorProfile (row32106Start ∪ row32106Finish)
    exact row32106_exactFactorProfile

/-! ## Computationally selected and replayed row `222-01` -/

/-- The two-term starting state of computationally selected row `222-01`. -/
def row22201Start : State profile222 :=
  {maskTerm(profile222, 1, 1, 1),
   maskTerm(profile222, 1, 1, 2)}

/-- The three-term finishing state of computationally selected row `222-01`. -/
def row22201Finish : State profile222 :=
  {maskTerm(profile222, 1, 2, 3),
   maskTerm(profile222, 2, 3, 3),
   maskTerm(profile222, 3, 3, 3)}

/-- Target-coordinate intermediate state 1 on the forward replay of row `222-01`. -/
def row22201ForwardState1 : State profile222 :=
  {maskTerm(profile222, 1, 1, 3)}

/-- Target-coordinate intermediate state 2 on the forward replay of row `222-01`. -/
def row22201ForwardState2 : State profile222 :=
  {maskTerm(profile222, 1, 2, 3),
   maskTerm(profile222, 1, 3, 3)}

/-- Target-coordinate intermediate state 1 on the reverse replay of row `222-01`. -/
def row22201ReverseState1 : State profile222 :=
  {maskTerm(profile222, 1, 2, 3),
   maskTerm(profile222, 1, 3, 3)}

/-- Target-coordinate intermediate state 2 on the reverse replay of row `222-01`. -/
def row22201ReverseState2 : State profile222 :=
  {maskTerm(profile222, 1, 1, 3)}

/-- The exact source-coordinate reduction data for forward step 1 of row `222-01`. -/
def row22201ForwardMove1 : FixedMoveData profile222 :=
  ⟨.bca, .reduction
      maskTerm(inversePermProfile .bca profile222, 1, 1, 1)
      maskTerm(inversePermProfile .bca profile222, 2, 1, 1)
      maskTerm(inversePermProfile .bca profile222, 3, 1, 1)⟩

/-- The exact source-coordinate split data for forward step 2 of row `222-01`. -/
def row22201ForwardMove2 : FixedMoveData profile222 :=
  ⟨.cab, .split
      maskTerm(inversePermProfile .cab profile222, 1, 3, 1)
      maskTerm(inversePermProfile .cab profile222, 2, 3, 1)
      maskTerm(inversePermProfile .cab profile222, 3, 3, 1)⟩

/-- The exact source-coordinate split data for forward step 3 of row `222-01`. -/
def row22201ForwardMove3 : FixedMoveData profile222 :=
  ⟨.abc, .split
      maskTerm(inversePermProfile .abc profile222, 1, 3, 3)
      maskTerm(inversePermProfile .abc profile222, 2, 3, 3)
      maskTerm(inversePermProfile .abc profile222, 3, 3, 3)⟩

/-- The exact source-coordinate reduction data for reverse step 1 of row `222-01`. -/
def row22201ReverseMove1 : FixedMoveData profile222 :=
  ⟨.abc, .reduction
      maskTerm(inversePermProfile .abc profile222, 2, 3, 3)
      maskTerm(inversePermProfile .abc profile222, 3, 3, 3)
      maskTerm(inversePermProfile .abc profile222, 1, 3, 3)⟩

/-- The exact source-coordinate reduction data for reverse step 2 of row `222-01`. -/
def row22201ReverseMove2 : FixedMoveData profile222 :=
  ⟨.cab, .reduction
      maskTerm(inversePermProfile .cab profile222, 2, 3, 1)
      maskTerm(inversePermProfile .cab profile222, 3, 3, 1)
      maskTerm(inversePermProfile .cab profile222, 1, 3, 1)⟩

/-- The exact source-coordinate split data for reverse step 3 of row `222-01`. -/
def row22201ReverseMove3 : FixedMoveData profile222 :=
  ⟨.bca, .split
      maskTerm(inversePermProfile .bca profile222, 3, 1, 1)
      maskTerm(inversePermProfile .bca profile222, 1, 1, 1)
      maskTerm(inversePermProfile .bca profile222, 2, 1, 1)⟩

/-- Kernel replay of the directed Reduction at forward step 1 of row `222-01`. -/
theorem step_row22201ForwardMove1 :
    row22201ForwardMove1.step? row22201Start = some row22201ForwardState1 := by
  unfold FixedMoveData.step? row22201ForwardMove1
  let m : SourceMoveData (inversePermProfile .bca profile222) :=
    .reduction
          maskTerm(inversePermProfile .bca profile222, 1, 1, 1)
          maskTerm(inversePermProfile .bca profile222, 2, 1, 1)
          maskTerm(inversePermProfile .bca profile222, 3, 1, 1)
  change Option.map (@forwardState profile222 .bca)
    (m.step? (inversePermuteState .bca row22201Start)) = some row22201ForwardState1
  have hlegal : m.Legal (inversePermuteState .bca row22201Start) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .bca row22201Start) =
      inversePermuteState .bca row22201ForwardState1 := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Split at forward step 2 of row `222-01`. -/
theorem step_row22201ForwardMove2 :
    row22201ForwardMove2.step? row22201ForwardState1 = some row22201ForwardState2 := by
  unfold FixedMoveData.step? row22201ForwardMove2
  let m : SourceMoveData (inversePermProfile .cab profile222) :=
    .split
          maskTerm(inversePermProfile .cab profile222, 1, 3, 1)
          maskTerm(inversePermProfile .cab profile222, 2, 3, 1)
          maskTerm(inversePermProfile .cab profile222, 3, 3, 1)
  change Option.map (@forwardState profile222 .cab)
    (m.step? (inversePermuteState .cab row22201ForwardState1)) = some row22201ForwardState2
  have hlegal : m.Legal (inversePermuteState .cab row22201ForwardState1) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .cab row22201ForwardState1) =
      inversePermuteState .cab row22201ForwardState2 := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Split at forward step 3 of row `222-01`. -/
theorem step_row22201ForwardMove3 :
    row22201ForwardMove3.step? row22201ForwardState2 = some row22201Finish := by
  unfold FixedMoveData.step? row22201ForwardMove3
  let m : SourceMoveData (inversePermProfile .abc profile222) :=
    .split
          maskTerm(inversePermProfile .abc profile222, 1, 3, 3)
          maskTerm(inversePermProfile .abc profile222, 2, 3, 3)
          maskTerm(inversePermProfile .abc profile222, 3, 3, 3)
  change Option.map (@forwardState profile222 .abc)
    (m.step? (inversePermuteState .abc row22201ForwardState2)) = some row22201Finish
  have hlegal : m.Legal (inversePermuteState .abc row22201ForwardState2) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .abc row22201ForwardState2) =
      inversePermuteState .abc row22201Finish := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Reduction at reverse step 1 of row `222-01`. -/
theorem step_row22201ReverseMove1 :
    row22201ReverseMove1.step? row22201Finish = some row22201ReverseState1 := by
  unfold FixedMoveData.step? row22201ReverseMove1
  let m : SourceMoveData (inversePermProfile .abc profile222) :=
    .reduction
          maskTerm(inversePermProfile .abc profile222, 2, 3, 3)
          maskTerm(inversePermProfile .abc profile222, 3, 3, 3)
          maskTerm(inversePermProfile .abc profile222, 1, 3, 3)
  change Option.map (@forwardState profile222 .abc)
    (m.step? (inversePermuteState .abc row22201Finish)) = some row22201ReverseState1
  have hlegal : m.Legal (inversePermuteState .abc row22201Finish) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .abc row22201Finish) =
      inversePermuteState .abc row22201ReverseState1 := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Reduction at reverse step 2 of row `222-01`. -/
theorem step_row22201ReverseMove2 :
    row22201ReverseMove2.step? row22201ReverseState1 = some row22201ReverseState2 := by
  unfold FixedMoveData.step? row22201ReverseMove2
  let m : SourceMoveData (inversePermProfile .cab profile222) :=
    .reduction
          maskTerm(inversePermProfile .cab profile222, 2, 3, 1)
          maskTerm(inversePermProfile .cab profile222, 3, 3, 1)
          maskTerm(inversePermProfile .cab profile222, 1, 3, 1)
  change Option.map (@forwardState profile222 .cab)
    (m.step? (inversePermuteState .cab row22201ReverseState1)) = some row22201ReverseState2
  have hlegal : m.Legal (inversePermuteState .cab row22201ReverseState1) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .cab row22201ReverseState1) =
      inversePermuteState .cab row22201ReverseState2 := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Split at reverse step 3 of row `222-01`. -/
theorem step_row22201ReverseMove3 :
    row22201ReverseMove3.step? row22201ReverseState2 = some row22201Start := by
  unfold FixedMoveData.step? row22201ReverseMove3
  let m : SourceMoveData (inversePermProfile .bca profile222) :=
    .split
          maskTerm(inversePermProfile .bca profile222, 3, 1, 1)
          maskTerm(inversePermProfile .bca profile222, 1, 1, 1)
          maskTerm(inversePermProfile .bca profile222, 2, 1, 1)
  change Option.map (@forwardState profile222 .bca)
    (m.step? (inversePermuteState .bca row22201ReverseState2)) = some row22201Start
  have hlegal : m.Legal (inversePermuteState .bca row22201ReverseState2) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .bca row22201ReverseState2) =
      inversePermuteState .bca row22201Start := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- The fixed directed forward witness list for row `222-01`. -/
def row22201ForwardMoves : List (FixedMoveData profile222) :=
  [row22201ForwardMove1, row22201ForwardMove2, row22201ForwardMove3]

/-- The fixed directed reverse witness list for row `222-01`. -/
def row22201ReverseMoves : List (FixedMoveData profile222) :=
  [row22201ReverseMove1, row22201ReverseMove2, row22201ReverseMove3]

/-- The heterogeneous raw replay data for computationally selected row `222-01`. -/
def row22201 : ReplayRow where
  profile := profile222
  start := row22201Start
  finish := row22201Finish
  forward := row22201ForwardMoves
  reverse := row22201ReverseMoves

/-- The exact forward run equation for row `222-01`. -/
theorem run_row22201ForwardMoves :
    run? row22201Start row22201ForwardMoves = some row22201Finish := by
  simp only [row22201ForwardMoves, run?, step_row22201ForwardMove1, Option.bind_some, step_row22201ForwardMove2, Option.bind_some, step_row22201ForwardMove3]

/-- The exact reverse run equation for row `222-01`. -/
theorem run_row22201ReverseMoves :
    run? row22201Finish row22201ReverseMoves = some row22201Start := by
  simp only [row22201ReverseMoves, run?, step_row22201ReverseMove1, Option.bind_some, step_row22201ReverseMove2, Option.bind_some, step_row22201ReverseMove3]

/-- Both exact directed runs of row `222-01` pass. -/
theorem row22201_passes : row22201.Passes := by
  simpa only [row22201, ReplayRow.Passes] using
    And.intro run_row22201ForwardMoves run_row22201ReverseMoves

/-- The actual `run?_path` data for the forward replay of row `222-01`. -/
def row22201ForwardPath :
    MovePath (@AllModeMove profile222) row22201Start row22201Finish :=
  run?_path run_row22201ForwardMoves

/-- The forward replay path of row `222-01` has exactly 3 edges. -/
@[simp] theorem row22201ForwardPath_length :
    row22201ForwardPath.length = 3 := by
  rw [row22201ForwardPath, run?_path_length]
  rfl

/-- The actual `run?_path` data for the reverse replay of row `222-01`. -/
def row22201ReversePath :
    MovePath (@AllModeMove profile222) row22201Finish row22201Start :=
  run?_path run_row22201ReverseMoves

/-- The reverse replay path of row `222-01` has exactly 3 edges. -/
@[simp] theorem row22201ReversePath_length :
    row22201ReversePath.length = 3 := by
  rw [row22201ReversePath, run?_path_length]
  rfl

/-- Both actual replay paths of row `222-01` have at most three edges. -/
theorem row22201_path_lengths_le_three :
    row22201ForwardPath.length ≤ 3 ∧ row22201ReversePath.length ≤ 3 := by
  rw [row22201ForwardPath_length, row22201ReversePath_length]
  omega

/-- The endpoint states of row `222-01` are disjoint. -/
theorem row22201_disjoint : Disjoint row22201Start row22201Finish := by
  decide

/-- The starting state of row `222-01` has exactly two terms. -/
theorem row22201_card_start : row22201Start.card = 2 := by
  decide

/-- The finishing state of row `222-01` has exactly three terms. -/
theorem row22201_card_finish : row22201Finish.card = 3 := by
  decide

/-- The visible standard-basis masks in the endpoint union of row `222-01` prove its exact factor profile. -/
theorem row22201_exactFactorProfile :
    HasExactFactorProfile (row22201Start ∪ row22201Finish) := by
  constructor
  · unfold firstFactorSpan
    apply (Submodule.eq_top_iff_forall_basis_mem
      (Pi.basisFun F2 (Fin profile222.first))).mpr
    intro i
    rw [Pi.basisFun_apply]
    apply Submodule.subset_span
    fin_cases i <;> decide
  constructor
  · unfold secondFactorSpan
    apply (Submodule.eq_top_iff_forall_basis_mem
      (Pi.basisFun F2 (Fin profile222.second))).mpr
    intro i
    rw [Pi.basisFun_apply]
    apply Submodule.subset_span
    fin_cases i <;> decide
  · unfold thirdFactorSpan
    apply (Submodule.eq_top_iff_forall_basis_mem
      (Pi.basisFun F2 (Fin profile222.third))).mpr
    intro i
    rw [Pi.basisFun_apply]
    apply Submodule.subset_span
    fin_cases i <;> decide

/-- The kernel-replayed five-circuit certificate for row `222-01`. -/
def row22201Certificate :
    FiveCircuitCertificate profile222 row22201Start row22201Finish := by
  let cert := replayRow_toFiveCircuitCertificate row22201 row22201_passes
    (by change Disjoint row22201Start row22201Finish; exact row22201_disjoint)
    (by change row22201Start.card = 2; exact row22201_card_start)
    (by change row22201Finish.card = 3; exact row22201_card_finish)
    (by simp only [row22201, row22201ForwardMoves, List.length_cons,
      List.length_nil]; omega)
    (by simp only [row22201, row22201ReverseMoves, List.length_cons,
      List.length_nil]; omega)
    (by
      change HasExactFactorProfile (row22201Start ∪ row22201Finish)
      exact row22201_exactFactorProfile)
  change FiveCircuitCertificate profile222 row22201Start row22201Finish at cert
  exact cert

/-- The heterogeneous certified wrapper for computationally selected row `222-01`. -/
def certified22201 : CertifiedReplayRow where
  row := row22201
  passes := row22201_passes
  disjoint := by change Disjoint row22201Start row22201Finish; exact row22201_disjoint
  card_start := by change row22201Start.card = 2; exact row22201_card_start
  card_finish := by change row22201Finish.card = 3; exact row22201_card_finish
  forward_length_le := by simp only [row22201, row22201ForwardMoves, List.length_cons, List.length_nil]; omega
  reverse_length_le := by simp only [row22201, row22201ReverseMoves, List.length_cons, List.length_nil]; omega
  exact_profile := by
    change HasExactFactorProfile (row22201Start ∪ row22201Finish)
    exact row22201_exactFactorProfile

/-! ## Computationally selected and replayed row `222-02` -/

/-- The two-term starting state of computationally selected row `222-02`. -/
def row22202Start : State profile222 :=
  {maskTerm(profile222, 1, 1, 1),
   maskTerm(profile222, 1, 2, 3)}

/-- The three-term finishing state of computationally selected row `222-02`. -/
def row22202Finish : State profile222 :=
  {maskTerm(profile222, 1, 1, 2),
   maskTerm(profile222, 2, 3, 3),
   maskTerm(profile222, 3, 3, 3)}

/-- Target-coordinate intermediate state 1 on the forward replay of row `222-02`. -/
def row22202ForwardState1 : State profile222 :=
  {maskTerm(profile222, 1, 1, 2),
   maskTerm(profile222, 1, 3, 3)}

/-- Target-coordinate intermediate state 1 on the reverse replay of row `222-02`. -/
def row22202ReverseState1 : State profile222 :=
  {maskTerm(profile222, 1, 1, 2),
   maskTerm(profile222, 1, 3, 3)}

/-- The exact source-coordinate flip data for forward step 1 of row `222-02`. -/
def row22202ForwardMove1 : FixedMoveData profile222 :=
  ⟨.cab, .flip
      maskTerm(inversePermProfile .cab profile222, 2, 3, 1)
      maskTerm(inversePermProfile .cab profile222, 1, 1, 1)
      maskTerm(inversePermProfile .cab profile222, 3, 3, 1)
      maskTerm(inversePermProfile .cab profile222, 1, 2, 1)⟩

/-- The exact source-coordinate split data for forward step 2 of row `222-02`. -/
def row22202ForwardMove2 : FixedMoveData profile222 :=
  ⟨.abc, .split
      maskTerm(inversePermProfile .abc profile222, 1, 3, 3)
      maskTerm(inversePermProfile .abc profile222, 2, 3, 3)
      maskTerm(inversePermProfile .abc profile222, 3, 3, 3)⟩

/-- The exact source-coordinate reduction data for reverse step 1 of row `222-02`. -/
def row22202ReverseMove1 : FixedMoveData profile222 :=
  ⟨.abc, .reduction
      maskTerm(inversePermProfile .abc profile222, 2, 3, 3)
      maskTerm(inversePermProfile .abc profile222, 3, 3, 3)
      maskTerm(inversePermProfile .abc profile222, 1, 3, 3)⟩

/-- The exact source-coordinate flip data for reverse step 2 of row `222-02`. -/
def row22202ReverseMove2 : FixedMoveData profile222 :=
  ⟨.cab, .flip
      maskTerm(inversePermProfile .cab profile222, 3, 3, 1)
      maskTerm(inversePermProfile .cab profile222, 1, 2, 1)
      maskTerm(inversePermProfile .cab profile222, 2, 3, 1)
      maskTerm(inversePermProfile .cab profile222, 1, 1, 1)⟩

/-- Kernel replay of the directed Flip at forward step 1 of row `222-02`. -/
theorem step_row22202ForwardMove1 :
    row22202ForwardMove1.step? row22202Start = some row22202ForwardState1 := by
  unfold FixedMoveData.step? row22202ForwardMove1
  let m : SourceMoveData (inversePermProfile .cab profile222) :=
    .flip
          maskTerm(inversePermProfile .cab profile222, 2, 3, 1)
          maskTerm(inversePermProfile .cab profile222, 1, 1, 1)
          maskTerm(inversePermProfile .cab profile222, 3, 3, 1)
          maskTerm(inversePermProfile .cab profile222, 1, 2, 1)
  change Option.map (@forwardState profile222 .cab)
    (m.step? (inversePermuteState .cab row22202Start)) = some row22202ForwardState1
  have hlegal : m.Legal (inversePermuteState .cab row22202Start) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .cab row22202Start) =
      inversePermuteState .cab row22202ForwardState1 := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Split at forward step 2 of row `222-02`. -/
theorem step_row22202ForwardMove2 :
    row22202ForwardMove2.step? row22202ForwardState1 = some row22202Finish := by
  unfold FixedMoveData.step? row22202ForwardMove2
  let m : SourceMoveData (inversePermProfile .abc profile222) :=
    .split
          maskTerm(inversePermProfile .abc profile222, 1, 3, 3)
          maskTerm(inversePermProfile .abc profile222, 2, 3, 3)
          maskTerm(inversePermProfile .abc profile222, 3, 3, 3)
  change Option.map (@forwardState profile222 .abc)
    (m.step? (inversePermuteState .abc row22202ForwardState1)) = some row22202Finish
  have hlegal : m.Legal (inversePermuteState .abc row22202ForwardState1) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .abc row22202ForwardState1) =
      inversePermuteState .abc row22202Finish := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Reduction at reverse step 1 of row `222-02`. -/
theorem step_row22202ReverseMove1 :
    row22202ReverseMove1.step? row22202Finish = some row22202ReverseState1 := by
  unfold FixedMoveData.step? row22202ReverseMove1
  let m : SourceMoveData (inversePermProfile .abc profile222) :=
    .reduction
          maskTerm(inversePermProfile .abc profile222, 2, 3, 3)
          maskTerm(inversePermProfile .abc profile222, 3, 3, 3)
          maskTerm(inversePermProfile .abc profile222, 1, 3, 3)
  change Option.map (@forwardState profile222 .abc)
    (m.step? (inversePermuteState .abc row22202Finish)) = some row22202ReverseState1
  have hlegal : m.Legal (inversePermuteState .abc row22202Finish) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .abc row22202Finish) =
      inversePermuteState .abc row22202ReverseState1 := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Flip at reverse step 2 of row `222-02`. -/
theorem step_row22202ReverseMove2 :
    row22202ReverseMove2.step? row22202ReverseState1 = some row22202Start := by
  unfold FixedMoveData.step? row22202ReverseMove2
  let m : SourceMoveData (inversePermProfile .cab profile222) :=
    .flip
          maskTerm(inversePermProfile .cab profile222, 3, 3, 1)
          maskTerm(inversePermProfile .cab profile222, 1, 2, 1)
          maskTerm(inversePermProfile .cab profile222, 2, 3, 1)
          maskTerm(inversePermProfile .cab profile222, 1, 1, 1)
  change Option.map (@forwardState profile222 .cab)
    (m.step? (inversePermuteState .cab row22202ReverseState1)) = some row22202Start
  have hlegal : m.Legal (inversePermuteState .cab row22202ReverseState1) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .cab row22202ReverseState1) =
      inversePermuteState .cab row22202Start := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- The fixed directed forward witness list for row `222-02`. -/
def row22202ForwardMoves : List (FixedMoveData profile222) :=
  [row22202ForwardMove1, row22202ForwardMove2]

/-- The fixed directed reverse witness list for row `222-02`. -/
def row22202ReverseMoves : List (FixedMoveData profile222) :=
  [row22202ReverseMove1, row22202ReverseMove2]

/-- The heterogeneous raw replay data for computationally selected row `222-02`. -/
def row22202 : ReplayRow where
  profile := profile222
  start := row22202Start
  finish := row22202Finish
  forward := row22202ForwardMoves
  reverse := row22202ReverseMoves

/-- The exact forward run equation for row `222-02`. -/
theorem run_row22202ForwardMoves :
    run? row22202Start row22202ForwardMoves = some row22202Finish := by
  simp only [row22202ForwardMoves, run?, step_row22202ForwardMove1, Option.bind_some, step_row22202ForwardMove2]

/-- The exact reverse run equation for row `222-02`. -/
theorem run_row22202ReverseMoves :
    run? row22202Finish row22202ReverseMoves = some row22202Start := by
  simp only [row22202ReverseMoves, run?, step_row22202ReverseMove1, Option.bind_some, step_row22202ReverseMove2]

/-- Both exact directed runs of row `222-02` pass. -/
theorem row22202_passes : row22202.Passes := by
  simpa only [row22202, ReplayRow.Passes] using
    And.intro run_row22202ForwardMoves run_row22202ReverseMoves

/-- The actual `run?_path` data for the forward replay of row `222-02`. -/
def row22202ForwardPath :
    MovePath (@AllModeMove profile222) row22202Start row22202Finish :=
  run?_path run_row22202ForwardMoves

/-- The forward replay path of row `222-02` has exactly 2 edges. -/
@[simp] theorem row22202ForwardPath_length :
    row22202ForwardPath.length = 2 := by
  rw [row22202ForwardPath, run?_path_length]
  rfl

/-- The actual `run?_path` data for the reverse replay of row `222-02`. -/
def row22202ReversePath :
    MovePath (@AllModeMove profile222) row22202Finish row22202Start :=
  run?_path run_row22202ReverseMoves

/-- The reverse replay path of row `222-02` has exactly 2 edges. -/
@[simp] theorem row22202ReversePath_length :
    row22202ReversePath.length = 2 := by
  rw [row22202ReversePath, run?_path_length]
  rfl

/-- Both actual replay paths of row `222-02` have at most three edges. -/
theorem row22202_path_lengths_le_three :
    row22202ForwardPath.length ≤ 3 ∧ row22202ReversePath.length ≤ 3 := by
  rw [row22202ForwardPath_length, row22202ReversePath_length]
  omega

/-- The endpoint states of row `222-02` are disjoint. -/
theorem row22202_disjoint : Disjoint row22202Start row22202Finish := by
  decide

/-- The starting state of row `222-02` has exactly two terms. -/
theorem row22202_card_start : row22202Start.card = 2 := by
  decide

/-- The finishing state of row `222-02` has exactly three terms. -/
theorem row22202_card_finish : row22202Finish.card = 3 := by
  decide

/-- The visible standard-basis masks in the endpoint union of row `222-02` prove its exact factor profile. -/
theorem row22202_exactFactorProfile :
    HasExactFactorProfile (row22202Start ∪ row22202Finish) := by
  constructor
  · unfold firstFactorSpan
    apply (Submodule.eq_top_iff_forall_basis_mem
      (Pi.basisFun F2 (Fin profile222.first))).mpr
    intro i
    rw [Pi.basisFun_apply]
    apply Submodule.subset_span
    fin_cases i <;> decide
  constructor
  · unfold secondFactorSpan
    apply (Submodule.eq_top_iff_forall_basis_mem
      (Pi.basisFun F2 (Fin profile222.second))).mpr
    intro i
    rw [Pi.basisFun_apply]
    apply Submodule.subset_span
    fin_cases i <;> decide
  · unfold thirdFactorSpan
    apply (Submodule.eq_top_iff_forall_basis_mem
      (Pi.basisFun F2 (Fin profile222.third))).mpr
    intro i
    rw [Pi.basisFun_apply]
    apply Submodule.subset_span
    fin_cases i <;> decide

/-- The kernel-replayed five-circuit certificate for row `222-02`. -/
def row22202Certificate :
    FiveCircuitCertificate profile222 row22202Start row22202Finish := by
  let cert := replayRow_toFiveCircuitCertificate row22202 row22202_passes
    (by change Disjoint row22202Start row22202Finish; exact row22202_disjoint)
    (by change row22202Start.card = 2; exact row22202_card_start)
    (by change row22202Finish.card = 3; exact row22202_card_finish)
    (by simp only [row22202, row22202ForwardMoves, List.length_cons,
      List.length_nil]; omega)
    (by simp only [row22202, row22202ReverseMoves, List.length_cons,
      List.length_nil]; omega)
    (by
      change HasExactFactorProfile (row22202Start ∪ row22202Finish)
      exact row22202_exactFactorProfile)
  change FiveCircuitCertificate profile222 row22202Start row22202Finish at cert
  exact cert

/-- The heterogeneous certified wrapper for computationally selected row `222-02`. -/
def certified22202 : CertifiedReplayRow where
  row := row22202
  passes := row22202_passes
  disjoint := by change Disjoint row22202Start row22202Finish; exact row22202_disjoint
  card_start := by change row22202Start.card = 2; exact row22202_card_start
  card_finish := by change row22202Finish.card = 3; exact row22202_card_finish
  forward_length_le := by simp only [row22202, row22202ForwardMoves, List.length_cons, List.length_nil]; omega
  reverse_length_le := by simp only [row22202, row22202ReverseMoves, List.length_cons, List.length_nil]; omega
  exact_profile := by
    change HasExactFactorProfile (row22202Start ∪ row22202Finish)
    exact row22202_exactFactorProfile

/-! ## Computationally selected and replayed row `222-03` -/

/-- The two-term starting state of computationally selected row `222-03`. -/
def row22203Start : State profile222 :=
  {maskTerm(profile222, 1, 1, 1),
   maskTerm(profile222, 2, 3, 3)}

/-- The three-term finishing state of computationally selected row `222-03`. -/
def row22203Finish : State profile222 :=
  {maskTerm(profile222, 1, 1, 2),
   maskTerm(profile222, 1, 2, 3),
   maskTerm(profile222, 3, 3, 3)}

/-- Target-coordinate intermediate state 1 on the forward replay of row `222-03`. -/
def row22203ForwardState1 : State profile222 :=
  {maskTerm(profile222, 1, 1, 2),
   maskTerm(profile222, 1, 1, 3),
   maskTerm(profile222, 2, 3, 3)}

/-- Target-coordinate intermediate state 1 on the reverse replay of row `222-03`. -/
def row22203ReverseState1 : State profile222 :=
  {maskTerm(profile222, 1, 1, 2),
   maskTerm(profile222, 1, 1, 3),
   maskTerm(profile222, 2, 3, 3)}

/-- The exact source-coordinate split data for forward step 1 of row `222-03`. -/
def row22203ForwardMove1 : FixedMoveData profile222 :=
  ⟨.bca, .split
      maskTerm(inversePermProfile .bca profile222, 1, 1, 1)
      maskTerm(inversePermProfile .bca profile222, 2, 1, 1)
      maskTerm(inversePermProfile .bca profile222, 3, 1, 1)⟩

/-- The exact source-coordinate flip data for forward step 2 of row `222-03`. -/
def row22203ForwardMove2 : FixedMoveData profile222 :=
  ⟨.abc, .flip
      maskTerm(inversePermProfile .abc profile222, 2, 3, 3)
      maskTerm(inversePermProfile .abc profile222, 1, 1, 3)
      maskTerm(inversePermProfile .abc profile222, 3, 3, 3)
      maskTerm(inversePermProfile .abc profile222, 1, 2, 3)⟩

/-- The exact source-coordinate flip data for reverse step 1 of row `222-03`. -/
def row22203ReverseMove1 : FixedMoveData profile222 :=
  ⟨.abc, .flip
      maskTerm(inversePermProfile .abc profile222, 3, 3, 3)
      maskTerm(inversePermProfile .abc profile222, 1, 2, 3)
      maskTerm(inversePermProfile .abc profile222, 2, 3, 3)
      maskTerm(inversePermProfile .abc profile222, 1, 1, 3)⟩

/-- The exact source-coordinate reduction data for reverse step 2 of row `222-03`. -/
def row22203ReverseMove2 : FixedMoveData profile222 :=
  ⟨.bca, .reduction
      maskTerm(inversePermProfile .bca profile222, 2, 1, 1)
      maskTerm(inversePermProfile .bca profile222, 3, 1, 1)
      maskTerm(inversePermProfile .bca profile222, 1, 1, 1)⟩

/-- Kernel replay of the directed Split at forward step 1 of row `222-03`. -/
theorem step_row22203ForwardMove1 :
    row22203ForwardMove1.step? row22203Start = some row22203ForwardState1 := by
  unfold FixedMoveData.step? row22203ForwardMove1
  let m : SourceMoveData (inversePermProfile .bca profile222) :=
    .split
          maskTerm(inversePermProfile .bca profile222, 1, 1, 1)
          maskTerm(inversePermProfile .bca profile222, 2, 1, 1)
          maskTerm(inversePermProfile .bca profile222, 3, 1, 1)
  change Option.map (@forwardState profile222 .bca)
    (m.step? (inversePermuteState .bca row22203Start)) = some row22203ForwardState1
  have hlegal : m.Legal (inversePermuteState .bca row22203Start) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .bca row22203Start) =
      inversePermuteState .bca row22203ForwardState1 := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Flip at forward step 2 of row `222-03`. -/
theorem step_row22203ForwardMove2 :
    row22203ForwardMove2.step? row22203ForwardState1 = some row22203Finish := by
  unfold FixedMoveData.step? row22203ForwardMove2
  let m : SourceMoveData (inversePermProfile .abc profile222) :=
    .flip
          maskTerm(inversePermProfile .abc profile222, 2, 3, 3)
          maskTerm(inversePermProfile .abc profile222, 1, 1, 3)
          maskTerm(inversePermProfile .abc profile222, 3, 3, 3)
          maskTerm(inversePermProfile .abc profile222, 1, 2, 3)
  change Option.map (@forwardState profile222 .abc)
    (m.step? (inversePermuteState .abc row22203ForwardState1)) = some row22203Finish
  have hlegal : m.Legal (inversePermuteState .abc row22203ForwardState1) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .abc row22203ForwardState1) =
      inversePermuteState .abc row22203Finish := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Flip at reverse step 1 of row `222-03`. -/
theorem step_row22203ReverseMove1 :
    row22203ReverseMove1.step? row22203Finish = some row22203ReverseState1 := by
  unfold FixedMoveData.step? row22203ReverseMove1
  let m : SourceMoveData (inversePermProfile .abc profile222) :=
    .flip
          maskTerm(inversePermProfile .abc profile222, 3, 3, 3)
          maskTerm(inversePermProfile .abc profile222, 1, 2, 3)
          maskTerm(inversePermProfile .abc profile222, 2, 3, 3)
          maskTerm(inversePermProfile .abc profile222, 1, 1, 3)
  change Option.map (@forwardState profile222 .abc)
    (m.step? (inversePermuteState .abc row22203Finish)) = some row22203ReverseState1
  have hlegal : m.Legal (inversePermuteState .abc row22203Finish) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .abc row22203Finish) =
      inversePermuteState .abc row22203ReverseState1 := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- Kernel replay of the directed Reduction at reverse step 2 of row `222-03`. -/
theorem step_row22203ReverseMove2 :
    row22203ReverseMove2.step? row22203ReverseState1 = some row22203Start := by
  unfold FixedMoveData.step? row22203ReverseMove2
  let m : SourceMoveData (inversePermProfile .bca profile222) :=
    .reduction
          maskTerm(inversePermProfile .bca profile222, 2, 1, 1)
          maskTerm(inversePermProfile .bca profile222, 3, 1, 1)
          maskTerm(inversePermProfile .bca profile222, 1, 1, 1)
  change Option.map (@forwardState profile222 .bca)
    (m.step? (inversePermuteState .bca row22203ReverseState1)) = some row22203Start
  have hlegal : m.Legal (inversePermuteState .bca row22203ReverseState1) := by
    unfold m SourceMoveData.Legal
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  rw [SourceMoveData.step?_eq_some m _ hlegal]
  have htarget : m.target (inversePermuteState .bca row22203ReverseState1) =
      inversePermuteState .bca row22203Start := by
    unfold m SourceMoveData.target
    decide
  simp only [Option.map_some, htarget, forwardState_inversePermuteState]

/-- The fixed directed forward witness list for row `222-03`. -/
def row22203ForwardMoves : List (FixedMoveData profile222) :=
  [row22203ForwardMove1, row22203ForwardMove2]

/-- The fixed directed reverse witness list for row `222-03`. -/
def row22203ReverseMoves : List (FixedMoveData profile222) :=
  [row22203ReverseMove1, row22203ReverseMove2]

/-- The heterogeneous raw replay data for computationally selected row `222-03`. -/
def row22203 : ReplayRow where
  profile := profile222
  start := row22203Start
  finish := row22203Finish
  forward := row22203ForwardMoves
  reverse := row22203ReverseMoves

/-- The exact forward run equation for row `222-03`. -/
theorem run_row22203ForwardMoves :
    run? row22203Start row22203ForwardMoves = some row22203Finish := by
  simp only [row22203ForwardMoves, run?, step_row22203ForwardMove1, Option.bind_some, step_row22203ForwardMove2]

/-- The exact reverse run equation for row `222-03`. -/
theorem run_row22203ReverseMoves :
    run? row22203Finish row22203ReverseMoves = some row22203Start := by
  simp only [row22203ReverseMoves, run?, step_row22203ReverseMove1, Option.bind_some, step_row22203ReverseMove2]

/-- Both exact directed runs of row `222-03` pass. -/
theorem row22203_passes : row22203.Passes := by
  simpa only [row22203, ReplayRow.Passes] using
    And.intro run_row22203ForwardMoves run_row22203ReverseMoves

/-- The actual `run?_path` data for the forward replay of row `222-03`. -/
def row22203ForwardPath :
    MovePath (@AllModeMove profile222) row22203Start row22203Finish :=
  run?_path run_row22203ForwardMoves

/-- The forward replay path of row `222-03` has exactly 2 edges. -/
@[simp] theorem row22203ForwardPath_length :
    row22203ForwardPath.length = 2 := by
  rw [row22203ForwardPath, run?_path_length]
  rfl

/-- The actual `run?_path` data for the reverse replay of row `222-03`. -/
def row22203ReversePath :
    MovePath (@AllModeMove profile222) row22203Finish row22203Start :=
  run?_path run_row22203ReverseMoves

/-- The reverse replay path of row `222-03` has exactly 2 edges. -/
@[simp] theorem row22203ReversePath_length :
    row22203ReversePath.length = 2 := by
  rw [row22203ReversePath, run?_path_length]
  rfl

/-- Both actual replay paths of row `222-03` have at most three edges. -/
theorem row22203_path_lengths_le_three :
    row22203ForwardPath.length ≤ 3 ∧ row22203ReversePath.length ≤ 3 := by
  rw [row22203ForwardPath_length, row22203ReversePath_length]
  omega

/-- The endpoint states of row `222-03` are disjoint. -/
theorem row22203_disjoint : Disjoint row22203Start row22203Finish := by
  decide

/-- The starting state of row `222-03` has exactly two terms. -/
theorem row22203_card_start : row22203Start.card = 2 := by
  decide

/-- The finishing state of row `222-03` has exactly three terms. -/
theorem row22203_card_finish : row22203Finish.card = 3 := by
  decide

/-- The visible standard-basis masks in the endpoint union of row `222-03` prove its exact factor profile. -/
theorem row22203_exactFactorProfile :
    HasExactFactorProfile (row22203Start ∪ row22203Finish) := by
  constructor
  · unfold firstFactorSpan
    apply (Submodule.eq_top_iff_forall_basis_mem
      (Pi.basisFun F2 (Fin profile222.first))).mpr
    intro i
    rw [Pi.basisFun_apply]
    apply Submodule.subset_span
    fin_cases i <;> decide
  constructor
  · unfold secondFactorSpan
    apply (Submodule.eq_top_iff_forall_basis_mem
      (Pi.basisFun F2 (Fin profile222.second))).mpr
    intro i
    rw [Pi.basisFun_apply]
    apply Submodule.subset_span
    fin_cases i <;> decide
  · unfold thirdFactorSpan
    apply (Submodule.eq_top_iff_forall_basis_mem
      (Pi.basisFun F2 (Fin profile222.third))).mpr
    intro i
    rw [Pi.basisFun_apply]
    apply Submodule.subset_span
    fin_cases i <;> decide

/-- The kernel-replayed five-circuit certificate for row `222-03`. -/
def row22203Certificate :
    FiveCircuitCertificate profile222 row22203Start row22203Finish := by
  let cert := replayRow_toFiveCircuitCertificate row22203 row22203_passes
    (by change Disjoint row22203Start row22203Finish; exact row22203_disjoint)
    (by change row22203Start.card = 2; exact row22203_card_start)
    (by change row22203Finish.card = 3; exact row22203_card_finish)
    (by simp only [row22203, row22203ForwardMoves, List.length_cons,
      List.length_nil]; omega)
    (by simp only [row22203, row22203ReverseMoves, List.length_cons,
      List.length_nil]; omega)
    (by
      change HasExactFactorProfile (row22203Start ∪ row22203Finish)
      exact row22203_exactFactorProfile)
  change FiveCircuitCertificate profile222 row22203Start row22203Finish at cert
  exact cert

/-- The heterogeneous certified wrapper for computationally selected row `222-03`. -/
def certified22203 : CertifiedReplayRow where
  row := row22203
  passes := row22203_passes
  disjoint := by change Disjoint row22203Start row22203Finish; exact row22203_disjoint
  card_start := by change row22203Start.card = 2; exact row22203_card_start
  card_finish := by change row22203Finish.card = 3; exact row22203_card_finish
  forward_length_le := by simp only [row22203, row22203ForwardMoves, List.length_cons, List.length_nil]; omega
  reverse_length_le := by simp only [row22203, row22203ReverseMoves, List.length_cons, List.length_nil]; omega
  exact_profile := by
    change HasExactFactorProfile (row22203Start ∪ row22203Finish)
    exact row22203_exactFactorProfile

/-- The computationally selected and kernel-replayed profile-`221` rows. -/
def selectedRows221 : List CertifiedReplayRow :=
  [certified22101, certified22102, certified22103]

/-- The computationally selected and kernel-replayed profile-`411` rows. -/
def selectedRows411 : List CertifiedReplayRow :=
  [certified41101]

/-- The computationally selected and kernel-replayed profile-`321` rows. -/
def selectedRows321 : List CertifiedReplayRow :=
  [certified32101, certified32102, certified32103, certified32104, certified32105, certified32106]

/-- The computationally selected and kernel-replayed profile-`222` rows. -/
def selectedRows222 : List CertifiedReplayRow :=
  [certified22201, certified22202, certified22203]

/-- All thirteen computationally selected and kernel-replayed rows in one heterogeneous list. -/
def selectedReplayRows : List CertifiedReplayRow :=
  selectedRows221 ++ selectedRows411 ++ selectedRows321 ++ selectedRows222

/-- The four profile-group lists have lengths three, one, six, and three, and the heterogeneous list has length thirteen. -/
theorem selectedReplayRows_lengths :
    selectedRows221.length = 3 ∧
    selectedRows411.length = 1 ∧
    selectedRows321.length = 6 ∧
    selectedRows222.length = 3 ∧
    selectedReplayRows.length = 13 := by
  decide

/-- Each profile-group list contains only rows with its displayed target profile. -/
theorem selectedReplayRows_profiles :
    selectedRows221.map (fun r => r.row.profile) =
      [profile221, profile221, profile221] ∧
    selectedRows411.map (fun r => r.row.profile) = [profile411] ∧
    selectedRows321.map (fun r => r.row.profile) =
      [profile321, profile321, profile321, profile321, profile321, profile321] ∧
    selectedRows222.map (fun r => r.row.profile) =
      [profile222, profile222, profile222] := by
  decide

#check @coordinateVectorOfMask
#check @nonzeroFactorOfMask
#check @carrierOfMasks
#check @replayRow_toFiveCircuitCertificate
#check @CertifiedReplayRow
#check @selectedReplayRows
#print axioms allModeMovePath_altitude_le_four
#print axioms replayRow_toFiveCircuitCertificate
#print axioms row22101Certificate
#print axioms row22102Certificate
#print axioms row22103Certificate
#print axioms row41101Certificate
#print axioms row32101Certificate
#print axioms row32102Certificate
#print axioms row32103Certificate
#print axioms row32104Certificate
#print axioms row32105Certificate
#print axioms row32106Certificate
#print axioms row22201Certificate
#print axioms row22202Certificate
#print axioms row22203Certificate

end BilinearComplexity.NormalizedBinaryFiveCircuitRows
