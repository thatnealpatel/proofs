import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Swap
import Mathlib.LinearAlgebra.Matrix.Transvection

set_option autoImplicit false

namespace BilinearComplexity

open Matrix

/-- The canonical rectangular pivot matrix with an identity block of size `r`,
transported to the supplied row and column indexings. -/
def pivotNormal {F rows cols rowFree colFree : Type*} [Zero F] [One F]
    {r : ℕ} (rowEquiv : rows ≃ Fin r ⊕ rowFree)
    (colEquiv : cols ≃ Fin r ⊕ colFree) : Matrix rows cols F :=
  (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) F)
    (0 : Matrix (Fin r) colFree F) (0 : Matrix rowFree (Fin r) F)
    (0 : Matrix rowFree colFree F)).submatrix rowEquiv colEquiv

example :
    pivotNormal (F := ZMod 2) (Equiv.refl (Fin 1 ⊕ Fin 1))
      (Equiv.refl (Fin 1 ⊕ Fin 1)) (Sum.inl 0) (Sum.inl 0) = 1 := by
  simp [pivotNormal]

/-- A canonical rectangular pivot matrix has rank equal to the size of its
identity block. -/
theorem rank_pivotNormal {F rows cols rowFree colFree : Type*} [Field F]
    [Fintype rows] [Fintype cols] [Fintype rowFree] [Fintype colFree]
    {r : ℕ} (rowEquiv : rows ≃ Fin r ⊕ rowFree)
    (colEquiv : cols ≃ Fin r ⊕ colFree) :
    (pivotNormal (F := F) rowEquiv colEquiv).rank = r := by
  classical
  let E : Matrix (Fin r ⊕ rowFree) (Fin r ⊕ colFree) F :=
    Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) F)
      (0 : Matrix (Fin r) colFree F) (0 : Matrix rowFree (Fin r) F)
      (0 : Matrix rowFree colFree F)
  let L : Matrix (Fin r ⊕ rowFree) (Fin r) F :=
    fun i j => Sum.elim (fun i' => (1 : Matrix (Fin r) (Fin r) F) i' j)
      (fun _ => 0) i
  let U : Matrix (Fin r) (Fin r ⊕ colFree) F :=
    fun i j => Sum.elim (fun j' => (1 : Matrix (Fin r) (Fin r) F) i j')
      (fun _ => 0) j
  have hfactor : E = L * U := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · change (1 : Matrix (Fin r) (Fin r) F) i j =
        ∑ k, (1 : Matrix (Fin r) (Fin r) F) i k *
          (1 : Matrix (Fin r) (Fin r) F) k j
      simpa only [Matrix.mul_apply] using
        congrFun (congrFun (Matrix.mul_one
          (1 : Matrix (Fin r) (Fin r) F)) i) j |>.symm
    · rw [Matrix.mul_apply]
      simp [E, L, U]
    · rw [Matrix.mul_apply]
      simp [E, L, U]
    · rw [Matrix.mul_apply]
      simp [E, L, U]
  have hlower : r ≤ E.rank := by
    have hsub : E.submatrix Sum.inl Sum.inl =
        (1 : Matrix (Fin r) (Fin r) F) := by
      ext i j
      simp [E]
    calc
      r = Fintype.card (Fin r) := (Fintype.card_fin r).symm
      _ = (1 : Matrix (Fin r) (Fin r) F).rank := (Matrix.rank_one).symm
      _ = (E.submatrix Sum.inl Sum.inl).rank := congrArg Matrix.rank hsub.symm
      _ ≤ E.rank := Matrix.rank_submatrix_le E Sum.inl Sum.inl
  have hupper : E.rank ≤ r := by
    rw [hfactor]
    calc
      (L * U).rank ≤ L.rank := Matrix.rank_mul_le_left L U
      _ ≤ Fintype.card (Fin r) := Matrix.rank_le_card_width L
      _ = r := Fintype.card_fin r
  have hE : E.rank = r := Nat.le_antisymm hupper hlower
  rw [pivotNormal, Matrix.rank_submatrix]
  exact hE

/-- One raw elementary elimination operation. Swaps and transvections are
sufficient for Gaussian elimination over `ZMod 2`; both row and column forms
are included so a trace can expose a canonical pivot block. -/
inductive ElementaryOperation (F rows cols : Type*) where
  | rowSwap (i j : rows)
  | rowAdd (target source : rows) (coefficient : F)
  | columnSwap (i j : cols)
  | columnAdd (source target : cols) (coefficient : F)
  deriving DecidableEq

namespace ElementaryOperation

variable {F rows cols : Type*} [Field F] [Fintype rows] [Fintype cols]
  [DecidableEq rows] [DecidableEq cols]

/-- The Boolean side-condition checker rejects a transvection whose source and
target coincide. Swaps, including no-op swaps, are always reversible. -/
def valid (op : ElementaryOperation F rows cols) : Bool :=
  match op with
  | .rowSwap _ _ => true
  | .rowAdd i j _ => decide (i ≠ j)
  | .columnSwap _ _ => true
  | .columnAdd i j _ => decide (i ≠ j)

/-- Replay one raw operation by multiplication with Mathlib's swap or
transvection matrix. -/
def apply (op : ElementaryOperation F rows cols) (A : Matrix rows cols F) :
    Matrix rows cols F :=
  match op with
  | .rowSwap i j => Matrix.swap F i j * A
  | .rowAdd i j c => Matrix.transvection i j c * A
  | .columnSwap i j => A * Matrix.swap F i j
  | .columnAdd i j c => A * Matrix.transvection i j c

/-- The raw inverse operation reverses swaps and negates transvection
coefficients. -/
def inverse (op : ElementaryOperation F rows cols) :
    ElementaryOperation F rows cols :=
  match op with
  | .rowSwap i j => .rowSwap i j
  | .rowAdd i j c => .rowAdd i j (-c)
  | .columnSwap i j => .columnSwap i j
  | .columnAdd i j c => .columnAdd i j (-c)

/-- A raw operation accepted by `valid` is reversed exactly by `inverse`; this
is the replay semantics used by the checker soundness proof. -/
theorem inverse_apply_apply (op : ElementaryOperation F rows cols)
    (A : Matrix rows cols F) (hop : op.valid = true) :
    op.inverse.apply (op.apply A) = A := by
  rcases op with ⟨i, j⟩ | ⟨i, j, c⟩ | ⟨i, j⟩ | ⟨i, j, c⟩
  · simp only [inverse, apply, ← Matrix.mul_assoc, Matrix.swap_mul_self,
      Matrix.one_mul]
  · have hij : i ≠ j := of_decide_eq_true hop
    change Matrix.transvection i j (-c) *
      (Matrix.transvection i j c * A) = A
    rw [← Matrix.mul_assoc,
      Matrix.transvection_mul_transvection_same i j hij, neg_add_cancel,
      Matrix.transvection_zero, Matrix.one_mul]
  · simp only [inverse, apply, Matrix.mul_assoc, Matrix.swap_mul_self,
      Matrix.mul_one]
  · have hij : i ≠ j := of_decide_eq_true hop
    change (A * Matrix.transvection i j c) *
      Matrix.transvection i j (-c) = A
    rw [Matrix.mul_assoc,
      Matrix.transvection_mul_transvection_same i j hij, add_neg_cancel,
      Matrix.transvection_zero, Matrix.mul_one]

/-- Applying any raw operation cannot increase matrix rank. -/
theorem rank_apply_le (op : ElementaryOperation F rows cols)
    (A : Matrix rows cols F) : (op.apply A).rank ≤ A.rank := by
  rcases op with ⟨i, j⟩ | ⟨i, j, c⟩ | ⟨i, j⟩ | ⟨i, j, c⟩
  · exact Matrix.rank_mul_le_right _ _
  · exact Matrix.rank_mul_le_right _ _
  · exact Matrix.rank_mul_le_left _ _
  · exact Matrix.rank_mul_le_left _ _

/-- Applying an accepted raw operation preserves ordinary matrix rank. -/
theorem rank_apply_eq (op : ElementaryOperation F rows cols)
    (A : Matrix rows cols F) (hop : op.valid = true) :
    (op.apply A).rank = A.rank := by
  apply Nat.le_antisymm (rank_apply_le op A)
  have hback := rank_apply_le op.inverse (op.apply A)
  rw [op.inverse_apply_apply A hop] at hback
  exact hback

end ElementaryOperation

/-- Compact untrusted elimination input: a list of elementary row and column
operations whose replay and side conditions are checked computationally. -/
abbrev RawEliminationTrace (F rows cols : Type*) :=
  List (ElementaryOperation F rows cols)

namespace RawEliminationTrace

variable {F rows cols : Type*} [Field F] [Fintype rows] [Fintype cols]
  [DecidableEq rows] [DecidableEq cols]

/-- Replay a raw trace from left to right. -/
def replay (trace : RawEliminationTrace F rows cols)
    (A : Matrix rows cols F) : Matrix rows cols F :=
  trace.foldl (fun M op => op.apply M) A

/-- Boolean validation of all reversible-operation side conditions in a raw
trace. -/
def valid (trace : RawEliminationTrace F rows cols) : Bool :=
  trace.all ElementaryOperation.valid

/-- Replaying a Boolean-valid raw trace preserves ordinary matrix rank. -/
theorem rank_replay_eq (trace : RawEliminationTrace F rows cols)
    (A : Matrix rows cols F) (htrace : valid trace = true) :
    (replay trace A).rank = A.rank := by
  induction trace generalizing A with
  | nil => rfl
  | cons op trace ih =>
      change (op.valid && trace.all ElementaryOperation.valid) = true at htrace
      have hand := Bool.and_eq_true_iff.mp htrace
      have hop : op.valid = true := hand.1
      have htail : valid trace = true := hand.2
      change (replay trace (op.apply A)).rank = A.rank
      exact (ih (op.apply A) htail).trans (op.rank_apply_eq A hop)

end RawEliminationTrace

/-- Executable verifier for untrusted finite-field elimination data. It checks
all elementary-operation side conditions and exact equality of the replayed
matrix with the claimed canonical pivot matrix. -/
def checkEliminationTrace
    {F rows cols rowFree colFree : Type*} [Field F]
    [Fintype rows] [Fintype cols] [Fintype rowFree] [Fintype colFree]
    [DecidableEq F] [DecidableEq rows] [DecidableEq cols]
    {r : ℕ} (rowEquiv : rows ≃ Fin r ⊕ rowFree)
    (colEquiv : cols ≃ Fin r ⊕ colFree)
    (A : Matrix rows cols F)
    (trace : RawEliminationTrace F rows cols) : Bool :=
  trace.valid &&
    decide (trace.replay A = pivotNormal rowEquiv colEquiv)

/-- Soundness of the executable verifier: accepted untrusted trace and pivot
data prove the ordinary Mathlib matrix rank. -/
theorem rank_eq_of_checkEliminationTrace_eq_true
    {F rows cols rowFree colFree : Type*} [Field F]
    [Fintype rows] [Fintype cols] [Fintype rowFree] [Fintype colFree]
    [DecidableEq F] [DecidableEq rows] [DecidableEq cols]
    {r : ℕ} (rowEquiv : rows ≃ Fin r ⊕ rowFree)
    (colEquiv : cols ≃ Fin r ⊕ colFree)
    (A : Matrix rows cols F)
    (trace : RawEliminationTrace F rows cols)
    (hcheck : checkEliminationTrace rowEquiv colEquiv A trace = true) :
    A.rank = r := by
  change (trace.valid && decide
    (trace.replay A = pivotNormal rowEquiv colEquiv)) = true at hcheck
  have hand := Bool.and_eq_true_iff.mp hcheck
  have hreplay : trace.replay A = pivotNormal rowEquiv colEquiv :=
    of_decide_eq_true hand.2
  have hrank := trace.rank_replay_eq A hand.1
  rw [hreplay, rank_pivotNormal] at hrank
  exact hrank.symm

/-- A replayable elimination certificate. The two-sided inverse equations
validate the row and column equivalences, `replay` validates the pivot normal
form, and the final three equations give an explicit kernel generator,
decoder, and contracting identity. -/
structure EliminationCertificate {F rows cols : Type*} [Field F]
    [Fintype rows] [Fintype cols] [DecidableEq rows] [DecidableEq cols]
    (A : Matrix rows cols F) (r : ℕ) where
  rowEquiv : rows ≃ Fin r ⊕ Fin (Fintype.card rows - r)
  colEquiv : cols ≃ Fin r ⊕ Fin (Fintype.card cols - r)
  left : Matrix rows rows F
  leftInv : Matrix rows rows F
  right : Matrix cols cols F
  rightInv : Matrix cols cols F
  leftInv_left : leftInv * left = 1
  left_leftInv : left * leftInv = 1
  rightInv_right : rightInv * right = 1
  right_rightInv : right * rightInv = 1
  replay : left * A * right = pivotNormal rowEquiv colEquiv
  kernelBasis : Matrix cols (Fin (Fintype.card cols - r)) F
  kernelCoordinates : Matrix (Fin (Fintype.card cols - r)) cols F
  kernelHomotopy : Matrix cols rows F
  kernel_zero : A * kernelBasis = 0
  kernel_split : kernelBasis * kernelCoordinates + kernelHomotopy * A = 1
  kernel_leftInverse : kernelCoordinates * kernelBasis = 1

namespace EliminationCertificate

variable {F rows cols : Type*} [Field F] [Fintype rows] [Fintype cols]
  [DecidableEq rows] [DecidableEq cols]
variable {A : Matrix rows cols F} {r : ℕ}

/-- Replaying an accepted elimination certificate proves the ordinary Mathlib
matrix rank, rather than merely returning the reported pivot count. -/
theorem matrix_rank_eq (c : EliminationCertificate A r) : A.rank = r := by
  classical
  let N : Matrix rows cols F := pivotNormal c.rowEquiv c.colEquiv
  have hnormal_le : N.rank ≤ A.rank := by
    change (pivotNormal c.rowEquiv c.colEquiv).rank ≤ A.rank
    rw [← c.replay]
    exact (Matrix.rank_mul_le_left (c.left * A) c.right).trans
      (Matrix.rank_mul_le_right c.left A)
  have hrecover : A = c.leftInv * N * c.rightInv := by
    calc
      A = (c.leftInv * c.left) * A * (c.right * c.rightInv) := by
        rw [c.leftInv_left, c.right_rightInv, Matrix.one_mul, Matrix.mul_one]
      _ = c.leftInv * (c.left * A * c.right) * c.rightInv := by
        simp only [Matrix.mul_assoc]
      _ = c.leftInv * N * c.rightInv := by rw [c.replay]
  have hmatrix_le : A.rank ≤ N.rank := by
    rw [hrecover]
    exact (Matrix.rank_mul_le_left (c.leftInv * N) c.rightInv).trans
      (Matrix.rank_mul_le_right c.leftInv N)
  calc
    A.rank = N.rank := Nat.le_antisymm hmatrix_le hnormal_le
    _ = r := rank_pivotNormal c.rowEquiv c.colEquiv

/-- An accepted elimination certificate also proves the cardinal-valued rank
of the associated abstract linear map. -/
theorem linearMap_rank_eq (c : EliminationCertificate A r) :
    LinearMap.rank A.mulVecLin = (r : Cardinal) := by
  change Module.rank F (LinearMap.range A.mulVecLin) = (r : Cardinal)
  rw [← Module.finrank_eq_rank]
  exact_mod_cast c.matrix_rank_eq

/-- The certified kernel generator is injective because the supplied decoder
is a verified left inverse. -/
theorem kernelBasis_mulVec_injective (c : EliminationCertificate A r) :
    Function.Injective c.kernelBasis.mulVecLin := by
  intro x y hxy
  change c.kernelBasis *ᵥ x = c.kernelBasis *ᵥ y at hxy
  have hxy' := congrArg (fun z => c.kernelCoordinates *ᵥ z) hxy
  simpa only [Matrix.mulVec_mulVec, c.kernel_leftInverse,
    Matrix.one_mulVec] using hxy'

/-- The kernel equations in an accepted certificate characterize every kernel
vector exactly as a generated vector. -/
theorem mulVec_eq_zero_iff (c : EliminationCertificate A r) (x : cols → F) :
    A *ᵥ x = 0 ↔ ∃ z, c.kernelBasis *ᵥ z = x := by
  constructor
  · intro hx
    refine ⟨c.kernelCoordinates *ᵥ x, ?_⟩
    have hrecover : x = c.kernelBasis *ᵥ (c.kernelCoordinates *ᵥ x) := by
      calc
        x = (1 : Matrix cols cols F) *ᵥ x := (Matrix.one_mulVec x).symm
        _ = (c.kernelBasis * c.kernelCoordinates + c.kernelHomotopy * A) *ᵥ x := by
          rw [c.kernel_split]
        _ = (c.kernelBasis * c.kernelCoordinates) *ᵥ x +
            (c.kernelHomotopy * A) *ᵥ x := Matrix.add_mulVec _ _ _
        _ = c.kernelBasis *ᵥ (c.kernelCoordinates *ᵥ x) +
            c.kernelHomotopy *ᵥ (A *ᵥ x) := by
          rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
        _ = c.kernelBasis *ᵥ (c.kernelCoordinates *ᵥ x) := by rw [hx]; simp
    exact hrecover.symm
  · rintro ⟨z, rfl⟩
    rw [Matrix.mulVec_mulVec, c.kernel_zero, Matrix.zero_mulVec]

/-- The abstract kernel submodule is exactly the range of the certified kernel
basis map. -/
theorem ker_eq_range (c : EliminationCertificate A r) :
    LinearMap.ker A.mulVecLin = LinearMap.range c.kernelBasis.mulVecLin := by
  ext x
  constructor
  · intro hx
    change A *ᵥ x = 0 at hx
    obtain ⟨z, hz⟩ := (c.mulVec_eq_zero_iff x).mp hx
    exact ⟨z, hz⟩
  · rintro ⟨z, rfl⟩
    change A *ᵥ (c.kernelBasis *ᵥ z) = 0
    exact (c.mulVec_eq_zero_iff _).mpr ⟨z, rfl⟩

/-- Kernel coordinates supplied by an accepted certificate exist uniquely for
every kernel vector. -/
theorem existsUnique_kernelCoordinates (c : EliminationCertificate A r)
    {x : cols → F} (hx : A *ᵥ x = 0) :
    ∃! z, c.kernelBasis *ᵥ z = x := by
  obtain ⟨z, hz⟩ := (c.mulVec_eq_zero_iff x).mp hx
  refine ⟨z, hz, fun y hy => ?_⟩
  exact c.kernelBasis_mulVec_injective (hy.trans hz.symm)

/-- The dimension of the certified kernel is derived from the explicit
injective generator and exact kernel characterization, not trusted as data. -/
theorem finrank_ker_eq (c : EliminationCertificate A r) :
    Module.finrank F (LinearMap.ker A.mulVecLin) = Fintype.card cols - r := by
  rw [c.ker_eq_range, LinearMap.finrank_range_of_inj c.kernelBasis_mulVec_injective,
    Module.finrank_pi, Fintype.card_fin]

end EliminationCertificate

/-- A replayable inconsistency certificate consists of a left-null row whose
pairing with the proposed right-hand side is nonzero. -/
structure InconsistencyCertificate {F rows cols : Type*} [Field F]
    [Fintype rows] [Fintype cols] (A : Matrix rows cols F) (b : rows → F) where
  leftNull : rows → F
  annihilates : leftNull ᵥ* A = 0
  detects : leftNull ⬝ᵥ b ≠ 0

namespace InconsistencyCertificate

variable {F rows cols : Type*} [Field F] [Fintype rows] [Fintype cols]
variable {A : Matrix rows cols F} {b : rows → F}

/-- An accepted left-null certificate proves that the matrix equation has no
solution. -/
theorem no_solution (c : InconsistencyCertificate A b) :
    ¬ ∃ x, A *ᵥ x = b := by
  rintro ⟨x, hx⟩
  apply c.detects
  calc
    c.leftNull ⬝ᵥ b = c.leftNull ⬝ᵥ (A *ᵥ x) := congrArg _ hx.symm
    _ = c.leftNull ᵥ* A ⬝ᵥ x := Matrix.dotProduct_mulVec _ _ _
    _ = 0 := by rw [c.annihilates]; simp

/-- An accepted left-null certificate proves that the right-hand side is not
in the range of the associated abstract linear map. -/
theorem not_mem_range (c : InconsistencyCertificate A b) :
    b ∉ LinearMap.range A.mulVecLin := by
  rintro ⟨x, hx⟩
  exact c.no_solution ⟨x, hx⟩

end InconsistencyCertificate

/-- One replay-facing proof-carrying interface for an inconsistent linear
system. Its elimination component carries the checked pivot normal form,
ordinary rank, and exact kernel data, while its inconsistency component carries
a left-null witness for the same matrix and right-hand side. -/
structure InconsistentLinearSystemCertificate
    {F rows cols : Type*} [Field F]
    [Fintype rows] [Fintype cols] [DecidableEq rows] [DecidableEq cols]
    (A : Matrix rows cols F) (b : rows → F) (r : ℕ) where
  elimination : EliminationCertificate A r
  inconsistency : InconsistencyCertificate A b

namespace InconsistentLinearSystemCertificate

variable {F rows cols : Type*} [Field F]
  [Fintype rows] [Fintype cols] [DecidableEq rows] [DecidableEq cols]
variable {A : Matrix rows cols F} {b : rows → F} {r : ℕ}

/-- The aggregate certificate reports the exact ordinary matrix rank certified
by its pivot replay. -/
theorem matrix_rank_eq (c : InconsistentLinearSystemCertificate A b r) :
    A.rank = r :=
  c.elimination.matrix_rank_eq

/-- The aggregate certificate identifies the kernel with the range of its
certified kernel basis. -/
theorem ker_eq_range (c : InconsistentLinearSystemCertificate A b r) :
    LinearMap.ker A.mulVecLin =
      LinearMap.range c.elimination.kernelBasis.mulVecLin :=
  c.elimination.ker_eq_range

/-- The aggregate certificate reports the nullity derived from its exact
kernel basis and pivot count. -/
theorem finrank_ker_eq (c : InconsistentLinearSystemCertificate A b r) :
    Module.finrank F (LinearMap.ker A.mulVecLin) =
      Fintype.card cols - r :=
  c.elimination.finrank_ker_eq

/-- The aggregate certificate's left-null witness proves that its right-hand
side is inconsistent. -/
theorem no_solution (c : InconsistentLinearSystemCertificate A b r) :
    ¬ ∃ x, A *ᵥ x = b :=
  c.inconsistency.no_solution

end InconsistentLinearSystemCertificate

/-- Executable kernel-membership checker for an untrusted candidate vector. -/
def checkKernelVector {F rows cols : Type*} [Field F]
    [Fintype rows] [Fintype cols] [DecidableEq F]
    (A : Matrix rows cols F) (x : cols → F) : Bool :=
  decide (A *ᵥ x = 0)

/-- Soundness of the executable kernel-membership checker in the abstract
linear-map kernel. -/
theorem mem_ker_of_checkKernelVector_eq_true
    {F rows cols : Type*} [Field F]
    [Fintype rows] [Fintype cols] [DecidableEq F]
    (A : Matrix rows cols F) (x : cols → F)
    (hcheck : checkKernelVector A x = true) :
    x ∈ LinearMap.ker A.mulVecLin := by
  change A *ᵥ x = 0
  exact of_decide_eq_true hcheck

/-- Executable checker for an untrusted left-null inconsistency vector. -/
def checkInconsistencyVector {F rows cols : Type*} [Field F]
    [Fintype rows] [Fintype cols] [DecidableEq F]
    (A : Matrix rows cols F) (b y : rows → F) : Bool :=
  decide (y ᵥ* A = 0) && decide (y ⬝ᵥ b ≠ 0)

/-- Soundness of the executable inconsistency checker: an accepted raw
left-null vector proves that the matrix equation has no solution. -/
theorem no_solution_of_checkInconsistencyVector_eq_true
    {F rows cols : Type*} [Field F]
    [Fintype rows] [Fintype cols] [DecidableEq F]
    (A : Matrix rows cols F) (b y : rows → F)
    (hcheck : checkInconsistencyVector A b y = true) :
    ¬ ∃ x, A *ᵥ x = b := by
  have hand := Bool.and_eq_true_iff.mp hcheck
  let c : InconsistencyCertificate A b :=
    { leftNull := y
      annihilates := of_decide_eq_true hand.1
      detects := of_decide_eq_true hand.2 }
  exact c.no_solution

/-- Untrusted finite data for one Boolean-checked external audit of a linear
system.  The same witness aggregates elimination replay and pivot rank, a
candidate kernel vector, and a left-null inconsistency vector. -/
structure RawLinearSystemAuditWitness
    (F rows cols : Type*) where
  /-- Untrusted row/column elimination operations. -/
  elimination : RawEliminationTrace F rows cols
  /-- Untrusted candidate whose kernel membership is checked. -/
  kernelVector : cols → F
  /-- Untrusted left-null vector whose inconsistency pairing is checked. -/
  inconsistencyVector : rows → F

/-- Boolean verifier for an external aggregate witness.  No reported rank,
kernel membership, or inconsistency fact is accepted without recomputation. -/
def checkLinearSystemAuditWitness
    {F rows cols rowFree colFree : Type*} [Field F]
    [Fintype rows] [Fintype cols] [Fintype rowFree] [Fintype colFree]
    [DecidableEq F] [DecidableEq rows] [DecidableEq cols]
    {r : ℕ} (rowEquiv : rows ≃ Fin r ⊕ rowFree)
    (colEquiv : cols ≃ Fin r ⊕ colFree)
    (A : Matrix rows cols F) (b : rows → F)
    (w : RawLinearSystemAuditWitness F rows cols) : Bool :=
  checkEliminationTrace rowEquiv colEquiv A w.elimination &&
    (checkKernelVector A w.kernelVector &&
      checkInconsistencyVector A b w.inconsistencyVector)

/-- Soundness of the aggregate Boolean verifier: acceptance proves the exact
ordinary rank, the checked kernel membership, and rejection of the proposed
right-hand side for the same matrix. -/
theorem linearSystemAuditWitness_sound
    {F rows cols rowFree colFree : Type*} [Field F]
    [Fintype rows] [Fintype cols] [Fintype rowFree] [Fintype colFree]
    [DecidableEq F] [DecidableEq rows] [DecidableEq cols]
    {r : ℕ} (rowEquiv : rows ≃ Fin r ⊕ rowFree)
    (colEquiv : cols ≃ Fin r ⊕ colFree)
    (A : Matrix rows cols F) (b : rows → F)
    (w : RawLinearSystemAuditWitness F rows cols)
    (hcheck : checkLinearSystemAuditWitness rowEquiv colEquiv A b w = true) :
    A.rank = r ∧
      w.kernelVector ∈ LinearMap.ker A.mulVecLin ∧
      ¬ ∃ x, A *ᵥ x = b := by
  have houter := Bool.and_eq_true_iff.mp hcheck
  have hinner := Bool.and_eq_true_iff.mp houter.2
  exact ⟨rank_eq_of_checkEliminationTrace_eq_true
      rowEquiv colEquiv A w.elimination houter.1,
    mem_ker_of_checkKernelVector_eq_true A w.kernelVector hinner.1,
    no_solution_of_checkInconsistencyVector_eq_true
      A b w.inconsistencyVector hinner.2⟩

namespace InconsistencyCertificate

variable {F K rows cols : Type*} [Field F] [Field K]
  [Fintype rows] [Fintype cols]
variable {A : Matrix rows cols F} {b : rows → F}

/-- Map a left-null inconsistency certificate along a field homomorphism. The
homomorphism's injectivity preserves the nonzero detecting pairing. -/
def map (c : InconsistencyCertificate A b) (f : F →+* K) :
    InconsistencyCertificate (A.map f) (f ∘ b) where
  leftNull := f ∘ c.leftNull
  annihilates := by
    funext j
    rw [← f.map_vecMul A c.leftNull j, c.annihilates]
    simp only [Pi.zero_apply, map_zero]
  detects := by
    intro hzero
    apply c.detects
    apply f.injective
    rw [map_zero, f.map_dotProduct]
    exact hzero

/-- Map a binary inconsistency certificate to any characteristic-two field
using the canonical homomorphism from `ZMod 2`. -/
def mapZModTwo {K rows cols : Type*} [Field K] [CharP K 2]
    [Fintype rows] [Fintype cols]
    {A : Matrix rows cols (ZMod 2)} {b : rows → ZMod 2}
    (c : InconsistencyCertificate A b) :
    InconsistencyCertificate
      (A.map (ZMod.castHom (dvd_refl 2) K))
      (ZMod.castHom (dvd_refl 2) K ∘ b) :=
  c.map (ZMod.castHom (dvd_refl 2) K)

end InconsistencyCertificate

/-- Entrywise scalar extension of a finite matrix between fields preserves its
Mathlib matrix rank. -/
theorem matrix_rank_map_algebraMap {F K rows cols : Type*} [Field F] [Field K]
    [Algebra F K] [Fintype rows] [Fintype cols] (A : Matrix rows cols F) :
    (A.map (algebraMap F K)).rank = A.rank := by
  classical
  let s : Set (rows → F) := Set.range A.col
  obtain ⟨f, hf_mem, hf_span, hf_ind⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq (K := F) (s := s)
  choose c hc using hf_mem
  let B : Matrix rows (Fin (Module.finrank F (Submodule.span F s))) F :=
    A.submatrix id c
  have hBcol : B.col = f := by
    funext i
    exact hc i
  have hcol_mem : ∀ j : cols, A.col j ∈ Submodule.span F (Set.range f) := by
    intro j
    rw [hf_span]
    exact Submodule.subset_span ⟨j, rfl⟩
  have hcoeff_exists : ∀ j : cols,
      ∃ d : Fin (Module.finrank F (Submodule.span F s)) → F,
        ∑ i, d i • f i = A.col j := by
    intro j
    exact (Submodule.mem_span_range_iff_exists_fun F).mp (hcol_mem j)
  choose coeff hcoeff using hcoeff_exists
  let C : Matrix (Fin (Module.finrank F (Submodule.span F s))) cols F :=
    fun i j => coeff j i
  have hfactor : B * C = A := by
    ext i j
    have hij := congrFun (hcoeff j) i
    have hBij : ∀ x, B i x = f x i := by
      intro x
      exact congrFun (congrFun hBcol x) i
    rw [Matrix.mul_apply]
    simp_rw [hBij]
    simpa [C, mul_comm] using hij
  have hmap_factor : A.map (algebraMap F K) =
      B.map (algebraMap F K) * C.map (algebraMap F K) := by
    rw [← Matrix.map_mul, hfactor]
  have hupper : (A.map (algebraMap F K)).rank ≤
      Module.finrank F (Submodule.span F s) := by
    rw [hmap_factor]
    exact (Matrix.rank_mul_le_left _ _).trans
      ((Matrix.rank_le_card_width (B.map (algebraMap F K))).trans_eq
        (Fintype.card_fin _))
  have hmapBcol : (B.map (algebraMap F K)).col =
      fun i => algebraMap F K ∘ f i := by
    funext i j
    change algebraMap F K (A j (c i)) = algebraMap F K (f i j)
    exact congrArg (algebraMap F K) (congrFun (hc i) j)
  have hmap_ind : LinearIndependent K (B.map (algebraMap F K)).col := by
    rw [hmapBcol, linearIndependent_algebraMap_comp_iff]
    exact hf_ind
  have hmapB_rank : (B.map (algebraMap F K)).rank =
      Module.finrank F (Submodule.span F s) := by
    rw [Matrix.rank_eq_finrank_span_cols, finrank_span_eq_card hmap_ind,
      Fintype.card_fin]
  have hsubmatrix : (A.map (algebraMap F K)).submatrix id c =
      B.map (algebraMap F K) := by
    ext i j
    rfl
  have hlower : Module.finrank F (Submodule.span F s) ≤
      (A.map (algebraMap F K)).rank := by
    rw [← hmapB_rank, ← hsubmatrix]
    exact Matrix.rank_submatrix_le _ id c
  calc
    (A.map (algebraMap F K)).rank =
        Module.finrank F (Submodule.span F s) :=
      Nat.le_antisymm hupper hlower
    _ = A.rank := by rw [Matrix.rank_eq_finrank_span_cols]

/-- Over a characteristic-two field, entrywise application of the canonical
map from `ZMod 2` preserves matrix rank. -/
theorem matrix_rank_map_zmod_two {K rows cols : Type*} [Field K] [CharP K 2]
    [Fintype rows] [Fintype cols] (A : Matrix rows cols (ZMod 2)) :
    (A.map (ZMod.castHom (dvd_refl 2) K)).rank = A.rank := by
  letI : Algebra (ZMod 2) K :=
    (ZMod.castHom (dvd_refl 2) K).toAlgebra
  exact matrix_rank_map_algebraMap A

/-- Full column rank of a finite matrix over a field implies injectivity of its
associated abstract linear map. -/
theorem mulVecLin_injective_of_rank_eq_card {F rows cols : Type*} [Field F]
    [Fintype rows] [Fintype cols] {A : Matrix rows cols F}
    (hA : A.rank = Fintype.card cols) : Function.Injective A.mulVecLin := by
  rw [← LinearMap.ker_eq_bot]
  apply Submodule.finrank_eq_zero.mp
  have hnullity := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  rw [← Matrix.rank, hA, Module.finrank_pi] at hnullity
  omega

/-- A certified full-column-rank restricted system over `ZMod 2` has no
nonzero kernel direction after mapping to any characteristic-two field. -/
theorem certified_support_noKernel_over_charTwo
    {K rows cols : Type*} [Field K] [CharP K 2]
    [Fintype rows] [Fintype cols] [DecidableEq rows] [DecidableEq cols]
    {A : Matrix rows cols (ZMod 2)}
    (c : EliminationCertificate A (Fintype.card cols)) :
    Function.Injective
      (A.map (ZMod.castHom (dvd_refl 2) K)).mulVecLin := by
  apply mulVecLin_injective_of_rank_eq_card
  rw [matrix_rank_map_zmod_two, c.matrix_rank_eq]

/-- Verified coordinates for a direct decomposition of an ambient domain into
a supplied gauge subspace and a supplied complement. The split identity,
two left inverses, and two cross-zero identities are explicit qualifications;
this structure does not infer gauge directions from deleted columns. -/
structure GaugeComplementDecomposition
    (F ambient gauge complement : Type*)
    [Field F] [Fintype ambient] [Fintype gauge] [Fintype complement]
    [DecidableEq ambient] [DecidableEq gauge] [DecidableEq complement] where
  gaugeBasis : Matrix ambient gauge F
  complementBasis : Matrix ambient complement F
  gaugeCoordinates : Matrix gauge ambient F
  complementCoordinates : Matrix complement ambient F
  split : gaugeBasis * gaugeCoordinates +
    complementBasis * complementCoordinates = 1
  gauge_leftInverse : gaugeCoordinates * gaugeBasis = 1
  complement_leftInverse : complementCoordinates * complementBasis = 1
  gaugeCoordinates_complement : gaugeCoordinates * complementBasis = 0
  complementCoordinates_gauge : complementCoordinates * gaugeBasis = 0

/-- If the binary matrix restricted through a verified complement has
certified full column rank, its mapped complement restriction has zero kernel
over every characteristic-two field. The gauge decomposition is supplied and
verified, not reconstructed from a column deletion. -/
theorem certified_complement_noKernel_over_charTwo
    {K ambient gauge complement equations : Type*}
    [Field K] [CharP K 2]
    [Fintype ambient] [Fintype gauge] [Fintype complement]
    [Fintype equations]
    [DecidableEq ambient] [DecidableEq gauge]
    [DecidableEq equations] [DecidableEq complement]
    (d : GaugeComplementDecomposition (ZMod 2) ambient gauge complement)
    (A : Matrix equations ambient (ZMod 2))
    (c : EliminationCertificate (A * d.complementBasis)
      (Fintype.card complement)) :
    Function.Injective
      ((A.map (ZMod.castHom (dvd_refl 2) K)) *
        (d.complementBasis.map (ZMod.castHom (dvd_refl 2) K))).mulVecLin := by
  simpa only [Matrix.map_mul] using
    certified_support_noKernel_over_charTwo (K := K) c

/-- Under the additional audited equality that the supplied gauge basis is
annihilated, a full-rank complement certificate identifies the mapped kernel
exactly with the mapped supplied gauge range. This theorem makes no claim that
any particular deleted columns are gauge directions. -/
theorem certified_kernel_eq_mappedGauge_over_charTwo
    {K ambient gauge complement equations : Type*}
    [Field K] [CharP K 2]
    [Fintype ambient] [Fintype gauge] [Fintype complement]
    [Fintype equations]
    [DecidableEq ambient] [DecidableEq gauge]
    [DecidableEq equations] [DecidableEq complement]
    (d : GaugeComplementDecomposition (ZMod 2) ambient gauge complement)
    (A : Matrix equations ambient (ZMod 2))
    (hGauge : A * d.gaugeBasis = 0)
    (c : EliminationCertificate (A * d.complementBasis)
      (Fintype.card complement)) :
    LinearMap.ker (A.map (ZMod.castHom (dvd_refl 2) K)).mulVecLin =
      LinearMap.range
        (d.gaugeBasis.map (ZMod.castHom (dvd_refl 2) K)).mulVecLin := by
  let f := ZMod.castHom (dvd_refl 2) K
  let AK := A.map f
  let GK := d.gaugeBasis.map f
  let CK := d.complementBasis.map f
  let GC := d.gaugeCoordinates.map f
  let CC := d.complementCoordinates.map f
  have hsplitK : GK * GC + CK * CC = 1 := by
    change d.gaugeBasis.map f * d.gaugeCoordinates.map f +
      d.complementBasis.map f * d.complementCoordinates.map f = 1
    calc
      d.gaugeBasis.map f * d.gaugeCoordinates.map f +
          d.complementBasis.map f * d.complementCoordinates.map f =
          (d.gaugeBasis * d.gaugeCoordinates +
            d.complementBasis * d.complementCoordinates).map f := by
        rw [Matrix.map_add f (map_add f), Matrix.map_mul, Matrix.map_mul]
      _ = (1 : Matrix ambient ambient (ZMod 2)).map f :=
        congrArg (fun M => M.map f) d.split
      _ = 1 := Matrix.map_one f (map_zero f) (map_one f)
  have hGaugeK : AK * GK = 0 := by
    change A.map f * d.gaugeBasis.map f = 0
    calc
      A.map f * d.gaugeBasis.map f = (A * d.gaugeBasis).map f :=
        Matrix.map_mul.symm
      _ = (0 : Matrix equations gauge (ZMod 2)).map f :=
        congrArg (fun M => M.map f) hGauge
      _ = 0 := by ext; simp
  have hinj : Function.Injective (AK * CK).mulVecLin := by
    exact certified_complement_noKernel_over_charTwo (K := K) d A c
  have hAC : AK = (AK * CK) * CC := by
    calc
      AK = AK * 1 := (Matrix.mul_one AK).symm
      _ = AK * (GK * GC + CK * CC) := by rw [hsplitK]
      _ = (AK * GK) * GC + (AK * CK) * CC := by
        simp only [Matrix.mul_add, Matrix.mul_assoc]
      _ = (AK * CK) * CC := by rw [hGaugeK]; simp
  ext x
  constructor
  · intro hx
    change AK *ᵥ x = 0 at hx
    have hzero : (AK * CK) *ᵥ (CC *ᵥ x) = 0 := by
      calc
        (AK * CK) *ᵥ (CC *ᵥ x) = ((AK * CK) * CC) *ᵥ x :=
          Matrix.mulVec_mulVec _ _ _
        _ = AK *ᵥ x := by rw [← hAC]
        _ = 0 := hx
    have hcoord : CC *ᵥ x = 0 := by
      apply hinj
      change (AK * CK) *ᵥ (CC *ᵥ x) =
        (AK * CK) *ᵥ (0 : complement → K)
      rw [Matrix.mulVec_zero]
      exact hzero
    refine ⟨GC *ᵥ x, ?_⟩
    change GK *ᵥ (GC *ᵥ x) = x
    calc
      GK *ᵥ (GC *ᵥ x) =
          GK *ᵥ (GC *ᵥ x) + CK *ᵥ (CC *ᵥ x) := by rw [hcoord]; simp
      _ = (GK * GC + CK * CC) *ᵥ x := by
        rw [Matrix.add_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      _ = x := by rw [hsplitK, Matrix.one_mulVec]
  · rintro ⟨z, rfl⟩
    change AK *ᵥ (GK *ᵥ z) = 0
    rw [Matrix.mulVec_mulVec, hGaugeK, Matrix.zero_mulVec]

universe uK uRows uCols

/-- The cardinal-valued rank of the matrix linear map is also preserved by
scalar extension from `ZMod 2` to any characteristic-two field. -/
theorem linearMap_rank_map_zmod_two
    {K : Type uK} {rows : Type uRows} {cols : Type uCols}
    [Field K] [CharP K 2] [Fintype rows] [Fintype cols]
    (A : Matrix rows cols (ZMod 2)) :
    Cardinal.lift.{uRows} (LinearMap.rank
      (A.map (ZMod.castHom (dvd_refl 2) K)).mulVecLin) =
      Cardinal.lift.{uK} (LinearMap.rank A.mulVecLin) := by
  change Cardinal.lift.{uRows}
      (Module.rank K (LinearMap.range
        (A.map (ZMod.castHom (dvd_refl 2) K)).mulVecLin)) =
    Cardinal.lift.{uK}
      (Module.rank (ZMod 2) (LinearMap.range A.mulVecLin))
  let VMap := LinearMap.range
    (A.map (ZMod.castHom (dvd_refl 2) K)).mulVecLin
  let VA := LinearMap.range A.mulVecLin
  let nMap := Module.finrank K VMap
  let nA := Module.finrank (ZMod 2) VA
  have hfin : nMap = nA := matrix_rank_map_zmod_two (K := K) A
  have hMap : (nMap : Cardinal.{max uK uRows}) = Module.rank K VMap :=
    Module.finrank_eq_rank K VMap
  have hA : (nA : Cardinal.{uRows}) = Module.rank (ZMod 2) VA :=
    Module.finrank_eq_rank (ZMod 2) VA
  calc
    Cardinal.lift.{uRows} (Module.rank K VMap) =
        Cardinal.lift.{uRows} (nMap : Cardinal.{max uK uRows}) :=
      congrArg Cardinal.lift hMap.symm
    _ = (nMap : Cardinal.{max uK uRows}) := Cardinal.lift_natCast nMap
    _ = (nA : Cardinal.{max uK uRows}) := congrArg (fun n : ℕ => (n : Cardinal)) hfin
    _ = Cardinal.lift.{uK} (nA : Cardinal.{uRows}) :=
      (Cardinal.lift_natCast nA).symm
    _ = Cardinal.lift.{uK} (Module.rank (ZMod 2) VA) :=
      congrArg Cardinal.lift hA

/-- A rank-one binary matrix used to exercise pivot, kernel, and scalar
extension replay on a nontrivial kernel. -/
def binaryRankOneMatrix : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  Matrix.diagonal ![1, 0]

example : binaryRankOneMatrix 0 0 = 1 := by decide
example : binaryRankOneMatrix 1 1 = 0 := by decide

/-- A direct accepted elimination certificate for the binary rank-one test
matrix, including its one-dimensional kernel generator and decoder. -/
def binaryRankOneCertificate : EliminationCertificate binaryRankOneMatrix 1 := by
  classical
  let e : Fin 2 ≃ Fin 1 ⊕ Fin 1 :=
    (finSumFinEquiv (m := 1) (n := 1)).symm
  let N : Matrix (Fin 2) (Fin 1) (ZMod 2) :=
    fun i _ => if i = 1 then 1 else 0
  let D : Matrix (Fin 1) (Fin 2) (ZMod 2) :=
    fun _ j => if j = 1 then 1 else 0
  refine
    { rowEquiv := e
      colEquiv := e
      left := 1
      leftInv := 1
      right := 1
      rightInv := 1
      leftInv_left := by simp
      left_leftInv := by simp
      rightInv_right := by simp
      right_rightInv := by simp
      replay := by decide
      kernelBasis := N
      kernelCoordinates := D
      kernelHomotopy := binaryRankOneMatrix
      kernel_zero := by decide
      kernel_split := by decide
      kernel_leftInverse := by decide }

example : binaryRankOneMatrix.rank = 1 :=
  binaryRankOneCertificate.matrix_rank_eq

example : Module.finrank (ZMod 2)
    (LinearMap.ker binaryRankOneMatrix.mulVecLin) = 1 := by
  simpa using binaryRankOneCertificate.finrank_ker_eq

example : binaryRankOneMatrix *ᵥ ![0, 1] = 0 := by decide

example : checkKernelVector binaryRankOneMatrix ![0, 1] = true := by
  decide

example : ![0, 1] ∈ LinearMap.ker binaryRankOneMatrix.mulVecLin :=
  mem_ker_of_checkKernelVector_eq_true binaryRankOneMatrix ![0, 1] (by decide)

example : ∃! z, binaryRankOneCertificate.kernelBasis *ᵥ z = ![0, 1] :=
  binaryRankOneCertificate.existsUnique_kernelCoordinates (by decide)

/-- A direct left-null inconsistency certificate for the equation with the
binary rank-one test matrix and right-hand side `(0,1)`. -/
def binaryInconsistentCertificate :
    InconsistencyCertificate binaryRankOneMatrix ![0, 1] := by
  refine
    { leftNull := ![0, 1]
      annihilates := by decide
      detects := by decide }

example : ¬ ∃ x, binaryRankOneMatrix *ᵥ x = ![0, 1] :=
  binaryInconsistentCertificate.no_solution

example : checkInconsistencyVector binaryRankOneMatrix ![0, 1] ![0, 1] = true := by
  decide

example : ¬ ∃ x, binaryRankOneMatrix *ᵥ x = ![0, 1] :=
  no_solution_of_checkInconsistencyVector_eq_true
    binaryRankOneMatrix ![0, 1] ![0, 1] (by decide)

example {K : Type*} [Field K] [CharP K 2] :
    (binaryRankOneMatrix.map (ZMod.castHom (dvd_refl 2) K)).rank = 1 := by
  rw [matrix_rank_map_zmod_two, binaryRankOneCertificate.matrix_rank_eq]

example {K : Type*} [Field K] [CharP K 2] :
    ¬ ∃ x,
      binaryRankOneMatrix.map (ZMod.castHom (dvd_refl 2) K) *ᵥ x =
        ZMod.castHom (dvd_refl 2) K ∘ ![0, 1] :=
  (binaryInconsistentCertificate.mapZModTwo (K := K)).no_solution

/-- A concrete aggregate certificate exercising the replayed pivot, exact
kernel, and inconsistency interfaces on the same binary linear system. -/
def binaryRankOneInconsistentSystemCertificate :
    InconsistentLinearSystemCertificate binaryRankOneMatrix ![0, 1] 1 where
  elimination := binaryRankOneCertificate
  inconsistency := binaryInconsistentCertificate

example : binaryRankOneInconsistentSystemCertificate.elimination.replay =
    binaryRankOneCertificate.replay := rfl

example : binaryRankOneMatrix.rank = 1 :=
  binaryRankOneInconsistentSystemCertificate.matrix_rank_eq

example : LinearMap.ker binaryRankOneMatrix.mulVecLin =
    LinearMap.range
      binaryRankOneInconsistentSystemCertificate.elimination.kernelBasis.mulVecLin :=
  binaryRankOneInconsistentSystemCertificate.ker_eq_range

example : ¬ ∃ x, binaryRankOneMatrix *ᵥ x = ![0, 1] :=
  binaryRankOneInconsistentSystemCertificate.no_solution

/-- One compact external witness for the binary rank-one system.  Its empty
elimination trace, kernel candidate, and inconsistency vector are all raw data
accepted only through the aggregate Boolean checker. -/
def binaryRankOneExternalAuditWitness :
    RawLinearSystemAuditWitness (ZMod 2) (Fin 2) (Fin 2) where
  elimination := []
  kernelVector := ![0, 1]
  inconsistencyVector := ![0, 1]

example : checkLinearSystemAuditWitness
    (rowFree := Fin 1) (colFree := Fin 1)
    (finSumFinEquiv (m := 1) (n := 1)).symm
    (finSumFinEquiv (m := 1) (n := 1)).symm
    binaryRankOneMatrix ![0, 1] binaryRankOneExternalAuditWitness = true := by
  decide

/-- Soundness of the compact external witness simultaneously certifies rank
one, kernel membership of the displayed candidate, and inconsistency of the right-hand side. -/
theorem binaryRankOneExternalAuditWitness_sound :
    binaryRankOneMatrix.rank = 1 ∧
      (![0, 1] : Fin 2 → ZMod 2) ∈
        LinearMap.ker binaryRankOneMatrix.mulVecLin ∧
      ¬ ∃ x, binaryRankOneMatrix *ᵥ x = ![0, 1] := by
  exact linearSystemAuditWitness_sound
    (rowFree := Fin 1) (colFree := Fin 1)
    (finSumFinEquiv (m := 1) (n := 1)).symm
    (finSumFinEquiv (m := 1) (n := 1)).symm
    binaryRankOneMatrix ![0, 1] binaryRankOneExternalAuditWitness (by decide)

/-- The Boolean-checked external witness rejects the concrete inconsistent
binary system without using the proof-bearing aggregate certificate. -/
theorem binaryRankOneExternalAuditWitness_rejects :
    ¬ ∃ x, binaryRankOneMatrix *ᵥ x = ![0, 1] :=
  binaryRankOneExternalAuditWitness_sound.2.2

/-- A rectangular binary matrix with two displaced pivots, used to test raw
row/column permutation replay. -/
def rectangularPermutationMatrix : Matrix (Fin 2) (Fin 3) (ZMod 2) :=
  !![0, 0, 1; 1, 0, 0]

/-- A compact raw trace that moves both displaced pivots into canonical order. -/
def rectangularPermutationTrace :
    RawEliminationTrace (ZMod 2) (Fin 2) (Fin 3) :=
  [.rowSwap 0 1, .columnSwap 1 2]

example : checkEliminationTrace
    (rowFree := Fin 0) (colFree := Fin 1)
    (finSumFinEquiv (m := 2) (n := 0)).symm
    (finSumFinEquiv (m := 2) (n := 1)).symm
    rectangularPermutationMatrix rectangularPermutationTrace = true := by
  decide

example : rectangularPermutationMatrix.rank = 2 :=
  rank_eq_of_checkEliminationTrace_eq_true
    (rowFree := Fin 0) (colFree := Fin 1)
    (finSumFinEquiv (m := 2) (n := 0)).symm
    (finSumFinEquiv (m := 2) (n := 1)).symm
    rectangularPermutationMatrix rectangularPermutationTrace (by decide)

example :
    (ElementaryOperation.rowAdd (F := ZMod 2) (cols := Fin 2) 1 0 1).apply
      binaryRankOneMatrix = !![1, 0; 1, 0] := by
  decide

example :
    (ElementaryOperation.columnAdd (F := ZMod 2) (rows := Fin 2) 0 1 1).apply
      binaryRankOneMatrix = !![1, 1; 0, 0] := by
  decide

example :
    let op : ElementaryOperation (ZMod 3) (Fin 2) (Fin 2) := .rowAdd 1 0 1
    op.inverse = .rowAdd 1 0 2 := by
  decide

example :
    let op : ElementaryOperation (ZMod 3) (Fin 2) (Fin 2) := .columnAdd 0 1 1
    op.inverse.apply (op.apply (1 : Matrix (Fin 2) (Fin 2) (ZMod 3))) = 1 := by
  decide

example :
    (ElementaryOperation.rowAdd (F := ZMod 2) (cols := Fin 2) 0 0 1).valid =
      false := by
  decide

example :
    let malformed : RawEliminationTrace (ZMod 2) (Fin 2) (Fin 2) :=
      [.rowAdd 0 0 1]
    malformed.valid = false := by
  decide

example :
    let malformed : RawEliminationTrace (ZMod 2) (Fin 2) (Fin 2) :=
      [.rowAdd 0 0 1]
    checkEliminationTrace
      (rowFree := Fin 1) (colFree := Fin 1)
      (finSumFinEquiv (m := 1) (n := 1)).symm
      (finSumFinEquiv (m := 1) (n := 1)).symm
      binaryRankOneMatrix malformed = false := by
  decide

example : checkEliminationTrace
    (rowFree := Fin 0) (colFree := Fin 0)
    (finSumFinEquiv (m := 2) (n := 0)).symm
    (finSumFinEquiv (m := 2) (n := 0)).symm
    binaryRankOneMatrix [] = false := by
  decide

example : checkKernelVector binaryRankOneMatrix ![1, 0] = false := by
  decide

example :
    checkInconsistencyVector binaryRankOneMatrix ![0, 1] ![1, 0] = false := by
  decide

/-- The one-equation binary system whose first ambient coordinate is a supplied
gauge direction and whose second coordinate is a direct complement. -/
def binaryGaugeMatrix : Matrix (Fin 1) (Fin 2) (ZMod 2) :=
  !![0, 1]

/-- A concrete verified decomposition of a binary two-dimensional domain into
its first-coordinate gauge line and second-coordinate complement line. -/
def binaryGaugeComplementDecomposition :
    GaugeComplementDecomposition (ZMod 2) (Fin 2) (Fin 1) (Fin 1) := by
  refine
    { gaugeBasis := !![1; 0]
      complementBasis := !![0; 1]
      gaugeCoordinates := !![1, 0]
      complementCoordinates := !![0, 1]
      split := by decide
      gauge_leftInverse := by decide
      complement_leftInverse := by decide
      gaugeCoordinates_complement := by decide
      complementCoordinates_gauge := by decide }

/-- A direct full-rank proof-carrying certificate for the concrete one-column
complement restriction. -/
def binaryComplementCertificate :
    EliminationCertificate
      (binaryGaugeMatrix * binaryGaugeComplementDecomposition.complementBasis) 1 := by
  classical
  refine
    { rowEquiv := (finSumFinEquiv (m := 1) (n := 0)).symm
      colEquiv := (finSumFinEquiv (m := 1) (n := 0)).symm
      left := 1
      leftInv := 1
      right := 1
      rightInv := 1
      leftInv_left := by simp
      left_leftInv := by simp
      rightInv_right := by simp
      right_rightInv := by simp
      replay := by decide
      kernelBasis := 0
      kernelCoordinates := 0
      kernelHomotopy := 1
      kernel_zero := by decide
      kernel_split := by decide
      kernel_leftInverse := by decide }

example : binaryGaugeMatrix *
    binaryGaugeComplementDecomposition.gaugeBasis = 0 := by
  decide

example {K : Type*} [Field K] [CharP K 2] :
    LinearMap.ker
      (binaryGaugeMatrix.map (ZMod.castHom (dvd_refl 2) K)).mulVecLin =
    LinearMap.range
      (binaryGaugeComplementDecomposition.gaugeBasis.map
        (ZMod.castHom (dvd_refl 2) K)).mulVecLin :=
  certified_kernel_eq_mappedGauge_over_charTwo
    (K := K) binaryGaugeComplementDecomposition binaryGaugeMatrix
    (by decide) binaryComplementCertificate

#check @rank_eq_of_checkEliminationTrace_eq_true
#check @mem_ker_of_checkKernelVector_eq_true
#check @no_solution_of_checkInconsistencyVector_eq_true
#check @checkLinearSystemAuditWitness
#check @linearSystemAuditWitness_sound
#check @binaryRankOneExternalAuditWitness_rejects
#check @EliminationCertificate.matrix_rank_eq
#check @EliminationCertificate.linearMap_rank_eq
#check @EliminationCertificate.ker_eq_range
#check @EliminationCertificate.finrank_ker_eq
#check @InconsistencyCertificate.no_solution
#check @InconsistencyCertificate.map
#check @InconsistencyCertificate.mapZModTwo
#check @InconsistentLinearSystemCertificate.matrix_rank_eq
#check @InconsistentLinearSystemCertificate.ker_eq_range
#check @InconsistentLinearSystemCertificate.finrank_ker_eq
#check @InconsistentLinearSystemCertificate.no_solution
#check @matrix_rank_map_algebraMap
#check @matrix_rank_map_zmod_two
#check @linearMap_rank_map_zmod_two
#check @certified_support_noKernel_over_charTwo
#check @certified_complement_noKernel_over_charTwo
#check @certified_kernel_eq_mappedGauge_over_charTwo

#print axioms rank_eq_of_checkEliminationTrace_eq_true
#print axioms mem_ker_of_checkKernelVector_eq_true
#print axioms no_solution_of_checkInconsistencyVector_eq_true
#print axioms linearSystemAuditWitness_sound
#print axioms binaryRankOneExternalAuditWitness_rejects
#print axioms EliminationCertificate.matrix_rank_eq
#print axioms EliminationCertificate.linearMap_rank_eq
#print axioms EliminationCertificate.ker_eq_range
#print axioms EliminationCertificate.finrank_ker_eq
#print axioms InconsistencyCertificate.no_solution
#print axioms InconsistencyCertificate.mapZModTwo
#print axioms InconsistentLinearSystemCertificate.matrix_rank_eq
#print axioms InconsistentLinearSystemCertificate.ker_eq_range
#print axioms InconsistentLinearSystemCertificate.finrank_ker_eq
#print axioms InconsistentLinearSystemCertificate.no_solution
#print axioms matrix_rank_map_algebraMap
#print axioms matrix_rank_map_zmod_two
#print axioms linearMap_rank_map_zmod_two
#print axioms certified_support_noKernel_over_charTwo
#print axioms certified_complement_noKernel_over_charTwo
#print axioms certified_kernel_eq_mappedGauge_over_charTwo

end BilinearComplexity
