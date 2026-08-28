import BilinearComplexity.LinearFlattening
import BilinearComplexity.SchemeReplacement
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace BilinearComplexity

section MatrixRankDefectNat

variable {k rows cols ι : Type*} [Field k] [Fintype rows] [Fintype cols]

/-- A finite sum of matrices of rank at most one has rank at most its number of summands. -/
theorem matrix_rank_sum_le_card_of_rank_le_one (A : ι → Matrix rows cols k)
    (hA : ∀ i, Matrix.rank (A i) ≤ 1) (s : Finset ι) :
    Matrix.rank (∑ i ∈ s, A i) ≤ s.card := by
  calc
    Matrix.rank (∑ i ∈ s, A i) ≤ ∑ i ∈ s, Matrix.rank (A i) :=
      matrix_rank_sum_le s A
    _ ≤ ∑ _i ∈ s, 1 := Finset.sum_le_sum fun i _hi => hA i
    _ = s.card := by simp

omit [Fintype rows] [Fintype cols] in
/-- Splitting a finite matrix sum into a subset and its relative complement. -/
theorem matrix_sum_eq_add_sdiff [DecidableEq ι]
    (A : ι → Matrix rows cols k) {I G : Finset ι}
    (hIG : I ⊆ G) :
    (∑ i ∈ G, A i) = (∑ i ∈ I, A i) + ∑ i ∈ G \ I, A i := by
  classical
  calc
    (∑ i ∈ G, A i) = (∑ i ∈ G \ I, A i) + ∑ i ∈ I, A i :=
      (Finset.sum_sdiff hIG).symm
    _ = (∑ i ∈ I, A i) + ∑ i ∈ G \ I, A i := add_comm _ _

/-- Adjoining rank-at-most-one matrices increases rank by at most the number adjoined. -/
theorem matrix_rank_sum_growth [DecidableEq ι] (A : ι → Matrix rows cols k)
    (hA : ∀ i, Matrix.rank (A i) ≤ 1) {I G : Finset ι} (hIG : I ⊆ G) :
    Matrix.rank (∑ i ∈ G, A i) ≤
      Matrix.rank (∑ i ∈ I, A i) + (G \ I).card := by
  classical
  rw [matrix_sum_eq_add_sdiff A hIG]
  exact (matrix_rank_add_le _ _).trans
    (Nat.add_le_add_left (matrix_rank_sum_le_card_of_rank_le_one A hA (G \ I)) _)

/-- Natural-number cardinality minus matrix-sum rank. Because `Nat` subtraction truncates,
this value has the numerical rank-defect interpretation only after proving the sum-rank bound. -/
noncomputable def matrixRankDefectNat (A : ι → Matrix rows cols k) (s : Finset ι) : ℕ :=
  s.card - Matrix.rank (∑ i ∈ s, A i)

/-- For rank-at-most-one summands, the sum-rank bound makes `matrixRankDefectNat`
an honest cardinality-minus-rank value rather than an unguarded truncated subtraction. -/
theorem matrix_rank_sum_le_card (A : ι → Matrix rows cols k)
    (hA : ∀ i, Matrix.rank (A i) ≤ 1) (s : Finset ι) :
    Matrix.rank (∑ i ∈ s, A i) ≤ s.card :=
  matrix_rank_sum_le_card_of_rank_le_one A hA s

/-- Under the rank-at-most-one guard, `matrixRankDefectNat` is monotone on finite subsets. -/
theorem matrixRankDefectNat_mono (A : ι → Matrix rows cols k)
    (hA : ∀ i, Matrix.rank (A i) ≤ 1) {I G : Finset ι} (hIG : I ⊆ G) :
    matrixRankDefectNat A I ≤ matrixRankDefectNat A G := by
  classical
  have hI := matrix_rank_sum_le_card A hA I
  have hgrowth := matrix_rank_sum_growth A hA hIG
  have hcardDiff := Finset.card_sdiff_of_subset hIG
  have hcard := Finset.card_le_card hIG
  simp only [matrixRankDefectNat]
  omega

/-- Under the rank-at-most-one guard, zero on a containing class forces zero on a subset. -/
theorem matrixRankDefectNat_eq_zero_of_subset (A : ι → Matrix rows cols k)
    (hA : ∀ i, Matrix.rank (A i) ≤ 1) {I G : Finset ι} (hIG : I ⊆ G)
    (hG : matrixRankDefectNat A G = 0) : matrixRankDefectNat A I = 0 := by
  have hmono := matrixRankDefectNat_mono A hA hIG
  omega

/-- Under the rank-at-most-one guard, positivity on a subset forces positivity on its container. -/
theorem matrixRankDefectNat_pos_of_subset (A : ι → Matrix rows cols k)
    (hA : ∀ i, Matrix.rank (A i) ≤ 1) {I G : Finset ι} (hIG : I ⊆ G)
    (hI : 0 < matrixRankDefectNat A I) : 0 < matrixRankDefectNat A G :=
  hI.trans_le (matrixRankDefectNat_mono A hA hIG)

omit [Fintype rows] in
/-- Every outer-product matrix has rank at most one. -/
theorem matrix_rank_vecMulVec_le_one (v : ι → rows → k) (w : ι → cols → k) (i : ι) :
    Matrix.rank (Matrix.vecMulVec (v i) (w i)) ≤ 1 :=
  Matrix.rank_vecMulVec_le _ _

/-- The empty family has zero natural cardinality-minus-rank value. -/
example (A : ι → Matrix rows cols k) : matrixRankDefectNat A ∅ = 0 := by
  simp [matrixRankDefectNat]

end MatrixRankDefectNat

section MatrixRankFactorization

variable {k rows cols : Type*} [Field k] [Fintype cols]

private noncomputable def matrixRangeColumn (A : Matrix rows cols k) (j : cols) :
    LinearMap.range A.mulVecLin := by
  classical
  exact ⟨A.col j, ⟨Pi.single j 1, Matrix.mulVec_single_one A j⟩⟩

/-- Every finite-column matrix is exactly a sum of `Matrix.rank A` outer products. -/
theorem exists_eq_sum_vecMulVec_rank (A : Matrix rows cols k) :
    ∃ v : Fin (Matrix.rank A) → rows → k,
      ∃ w : Fin (Matrix.rank A) → cols → k,
        A = ∑ s, Matrix.vecMulVec (v s) (w s) := by
  let b := Module.finBasis k (LinearMap.range A.mulVecLin)
  let v : Fin (Matrix.rank A) → rows → k := fun s => (b s : rows → k)
  let w : Fin (Matrix.rank A) → cols → k :=
    fun s j => b.repr (matrixRangeColumn A j) s
  refine ⟨v, w, ?_⟩
  funext i j
  have hcolumn :
      (∑ s, b.repr (matrixRangeColumn A j) s * (b s : rows → k) i) = A i j := by
    simpa only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, matrixRangeColumn, Matrix.col_apply] using
      congrArg (fun x : LinearMap.range A.mulVecLin => (x : rows → k) i)
        (b.sum_repr (matrixRangeColumn A j))
  rw [Matrix.sum_apply]
  simp only [Matrix.vecMulVec_apply]
  rw [← hcolumn]
  apply Finset.sum_congr rfl
  intro s _hs
  ring

end MatrixRankFactorization

section SharedFactorReconstruction

variable {k : Type*} [Field k] {a b c r : ℕ}

/-- A common first factor gives a tensor-rank upper bound by the complementary matrix rank;
the common factor is not required to be nonzero. -/
theorem rankLE_common_first_factor_matrix (u : Fin a → k)
    (A : Matrix (Fin b) (Fin c) k) :
    RankLE (fun i j l => u i * A j l) (Matrix.rank A) := by
  obtain ⟨v, w, hA⟩ := exists_eq_sum_vecMulVec_rank A
  refine ⟨fun _s => u, v, w, ?_⟩
  funext i j l
  have hentry := congrFun (congrFun hA j) l
  rw [Matrix.sum_apply] at hentry
  simp only [Matrix.vecMulVec_apply] at hentry
  rw [hentry, Finset.mul_sum]
  simp only [mul_assoc]

/-- A finite tensor sum with a common first factor admits a `RankLE` witness indexed by
the rank of its complementary matrix sum; this does not assert exact tensor rank. -/
theorem rankLE_sum_shared_first_factor (u : Fin a → k)
    (v : Fin r → Fin b → k) (w : Fin r → Fin c → k) :
    RankLE (fun i j l => ∑ s, u i * v s j * w s l)
      (Matrix.rank (∑ s, Matrix.vecMulVec (v s) (w s))) := by
  let A : Matrix (Fin b) (Fin c) k := ∑ s, Matrix.vecMulVec (v s) (w s)
  have hcommon := rankLE_common_first_factor_matrix u A
  convert hcommon using 1
  funext i j l
  simp only [A, Matrix.sum_apply, Matrix.vecMulVec_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _hs
  ring

/-- The common-second-factor reconstruction is the common-first theorem with the first two
modes permuted. -/
theorem rankLE_sum_shared_second_factor (u : Fin r → Fin a → k)
    (v : Fin b → k) (w : Fin r → Fin c → k) :
    RankLE (fun i j l => ∑ s, u s i * v j * w s l)
      (Matrix.rank (∑ s, Matrix.vecMulVec (u s) (w s))) := by
  obtain ⟨v', u', w', hdecomp⟩ :=
    rankLE_sum_shared_first_factor v u w
  refine ⟨u', v', w', ?_⟩
  funext i j l
  have hentry := congrFun (congrFun (congrFun hdecomp j) i) l
  calc
    (∑ s, u s i * v j * w s l) = ∑ s, v j * u s i * w s l := by
      apply Finset.sum_congr rfl
      intro s _hs
      ring
    _ = ∑ s, u' s i * v' s j * w' s l := by
      rw [hentry]
      apply Finset.sum_congr rfl
      intro s _hs
      ring

/-- The common-third-factor reconstruction is the common-first theorem after a cyclic
permutation of tensor modes. -/
theorem rankLE_sum_shared_third_factor (u : Fin r → Fin a → k)
    (v : Fin r → Fin b → k) (w : Fin c → k) :
    RankLE (fun i j l => ∑ s, u s i * v s j * w l)
      (Matrix.rank (∑ s, Matrix.vecMulVec (u s) (v s))) := by
  obtain ⟨w', u', v', hdecomp⟩ :=
    rankLE_sum_shared_first_factor w u v
  refine ⟨u', v', w', ?_⟩
  funext i j l
  have hentry := congrFun (congrFun (congrFun hdecomp l) i) j
  calc
    (∑ s, u s i * v s j * w l) = ∑ s, w l * u s i * v s j := by
      apply Finset.sum_congr rfl
      intro s _hs
      ring
    _ = ∑ s, u' s i * v' s j * w' s l := by
      rw [hentry]
      apply Finset.sum_congr rfl
      intro s _hs
      ring

end SharedFactorReconstruction

namespace Scheme.Replacement

section LiteralFirstFactor

variable {k : Type*} [Field k] {a b c r : ℕ}

/-- A full literal first-factor class is specified by an anchored scheme slot whose stored
first factor is the fixed nonzero vector; its slots are all scheme slots with that factor. -/
structure LiteralFirstFactorClass (S : Scheme k a b c r) where
  /-- The common stored first factor. -/
  factor : Fin a → k
  /-- A source slot witnessing that the literal factor class is inhabited. -/
  anchor : Fin r
  /-- The anchor's stored first factor is the fixed factor. -/
  anchor_factor : (S.term anchor).1 = factor
  /-- Literal shared-factor classes used for reduction have a nonzero fixed factor. -/
  factor_ne_zero : factor ≠ 0

namespace LiteralFirstFactorClass

/-- Every slot of a scheme whose stored first factor is literally the fixed nonzero factor. -/
noncomputable def slots {S : Scheme k a b c r} (F : LiteralFirstFactorClass S) :
    Finset (Fin r) := by
  classical
  exact Finset.univ.filter fun s => (S.term s).1 = F.factor

/-- Membership in the full literal class is exactly equality of the stored first factor. -/
@[simp] theorem mem_slots {S : Scheme k a b c r} (F : LiteralFirstFactorClass S)
    (s : Fin r) : s ∈ F.slots ↔ (S.term s).1 = F.factor := by
  classical
  simp [slots]

/-- The anchor belongs to the full literal factor fiber. -/
@[simp] theorem anchor_mem_slots {S : Scheme k a b c r} (F : LiteralFirstFactorClass S) :
    F.anchor ∈ F.slots :=
  (F.mem_slots F.anchor).2 F.anchor_factor

/-- The anchored full literal factor fiber is nonempty. -/
theorem slots_nonempty {S : Scheme k a b c r} (F : LiteralFirstFactorClass S) :
    F.slots.Nonempty :=
  ⟨F.anchor, F.anchor_mem_slots⟩

/-- The complementary matrix sum after removing the common first factor from the full class. -/
noncomputable def complementaryMatrix {S : Scheme k a b c r}
    (F : LiteralFirstFactorClass S) : Matrix (Fin b) (Fin c) k :=
  ∑ s ∈ F.slots, Matrix.vecMulVec (S.term s).2.1 (S.term s).2.2

/-- The complementary matrix is pointwise the sum of the stored outer products. -/
@[simp] theorem complementaryMatrix_apply {S : Scheme k a b c r}
    (F : LiteralFirstFactorClass S) (j : Fin b) (l : Fin c) :
    F.complementaryMatrix j l =
      ∑ s ∈ F.slots, (S.term s).2.1 j * (S.term s).2.2 l := by
  classical
  simp [complementaryMatrix, Matrix.sum_apply, Matrix.vecMulVec_apply]

/-- The complementary matrix rank never exceeds the cardinality of the literal class. -/
theorem complementaryMatrix_rank_le_card {S : Scheme k a b c r}
    (F : LiteralFirstFactorClass S) : F.complementaryMatrix.rank ≤ F.slots.card := by
  classical
  exact matrix_rank_sum_le_card_of_rank_le_one
    (fun s : Fin r => Matrix.vecMulVec (S.term s).2.1 (S.term s).2.2)
    (fun s => Matrix.rank_vecMulVec_le _ _) F.slots

/-- For the outer-product family in a literal class, the guarded natural-number
expression unfolds to fiber cardinality minus complementary matrix rank. -/
@[simp] theorem matrixRankDefectNat_eq_card_sub_rank {S : Scheme k a b c r}
    (F : LiteralFirstFactorClass S) :
    matrixRankDefectNat
        (fun s : Fin r => Matrix.vecMulVec (S.term s).2.1 (S.term s).2.2) F.slots =
      F.slots.card - F.complementaryMatrix.rank := by
  rfl

end LiteralFirstFactorClass

open LiteralFirstFactorClass

/-- Exact certificate existence: remove precisely the full literal first-factor class and
insert exactly as many common-factor triads as the rank of its complementary matrix. -/
theorem exists_literalFirstFactorClass_certificate {S : Scheme k a b c r}
    (F : LiteralFirstFactorClass S) :
    ∃ C : Certificate S,
      C.removed = F.slots ∧
      C.inserted.length = F.complementaryMatrix.rank ∧
      C.resultRank = r - F.slots.card + F.complementaryMatrix.rank := by
  obtain ⟨v, w, hM⟩ := exists_eq_sum_vecMulVec_rank F.complementaryMatrix
  let L : List (TriadData k a b c) := List.ofFn fun q => (F.factor, v q, w q)
  have hlocal : selectedTensor S F.slots = insertedTensor L := by
    funext i j l
    simp only [selectedTensor, Finset.sum_apply, insertedTensor, List.map_ofFn,
      List.sum_ofFn, Function.comp_apply, TriadData.eval, triad, L]
    have hMentry := congrFun (congrFun hM j) l
    rw [Matrix.sum_apply] at hMentry
    simp only [Matrix.vecMulVec_apply] at hMentry
    calc
      (∑ x ∈ F.slots, (S.term x).1 i * (S.term x).2.1 j * (S.term x).2.2 l) =
          ∑ x ∈ F.slots, F.factor i * (S.term x).2.1 j * (S.term x).2.2 l := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [(F.mem_slots x).mp hx]
      _ = F.factor i * F.complementaryMatrix j l := by
            simp only [complementaryMatrix_apply, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x _hx
            ring
      _ = F.factor i * ∑ q, v q j * w q l := by rw [hMentry]
      _ = ∑ q, F.factor i * v q j * w q l := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro q _hq
            ring
  let C : Certificate S := {
    removed := F.slots
    inserted := L
    local_eq := hlocal
  }
  refine ⟨C, rfl, ?_, ?_⟩
  · simp [C, L]
  · simp [Certificate.resultRank, C, L]

namespace LiteralFirstFactorClass

/-- The noncomputably chosen exact replacement certificate supplied by complementary matrix
factorization. -/
noncomputable def certificate {S : Scheme k a b c r} (F : LiteralFirstFactorClass S) :
    Certificate S :=
  Classical.choose (exists_literalFirstFactorClass_certificate F)

/-- The chosen certificate satisfies the full-fiber removal, insertion-length, and
natural-number result-rank bookkeeping specification. -/
theorem certificate_spec {S : Scheme k a b c r} (F : LiteralFirstFactorClass S) :
    F.certificate.removed = F.slots ∧
    F.certificate.inserted.length = F.complementaryMatrix.rank ∧
    F.certificate.resultRank = r - F.slots.card + F.complementaryMatrix.rank :=
  Classical.choose_spec (exists_literalFirstFactorClass_certificate F)

/-- The chosen certificate removes exactly the full literal fiber. -/
@[simp] theorem certificate_removed {S : Scheme k a b c r} (F : LiteralFirstFactorClass S) :
    F.certificate.removed = F.slots :=
  F.certificate_spec.1

/-- The chosen certificate inserts exactly the complementary matrix rank many terms. -/
@[simp] theorem certificate_inserted_length {S : Scheme k a b c r}
    (F : LiteralFirstFactorClass S) :
    F.certificate.inserted.length = F.complementaryMatrix.rank :=
  F.certificate_spec.2.1

/-- Exact output-length bookkeeping for full literal-fiber replacement. -/
@[simp] theorem certificate_resultRank {S : Scheme k a b c r}
    (F : LiteralFirstFactorClass S) :
    F.certificate.resultRank = r - F.slots.card + F.complementaryMatrix.rank :=
  F.certificate_spec.2.2

/-- The chosen certificate's local equality is exposed with the full literal fiber named. -/
theorem certificate_local_eq {S : Scheme k a b c r} (F : LiteralFirstFactorClass S) :
    selectedTensor S F.slots = insertedTensor F.certificate.inserted := by
  rw [← F.certificate_removed]
  exact F.certificate.local_eq

/-- The chosen certificate output represents the source tensor sum; this does not assert that
the output satisfies `Scheme.Valid`. -/
theorem certificate_sumTensor_eq {S : Scheme k a b c r} (F : LiteralFirstFactorClass S) :
    F.certificate.output.sumTensor = S.sumTensor :=
  F.certificate.sumTensor_eq

/-- The chosen certificate gives a `RankLE` upper bound at its result-rank parameter; this
asserts neither exact tensor rank nor `Scheme.Valid` for the output. -/
theorem certificate_rankLE {S : Scheme k a b c r} (F : LiteralFirstFactorClass S) :
    RankLE S.sumTensor (r - F.slots.card + F.complementaryMatrix.rank) := by
  rw [← F.certificate_resultRank]
  exact F.certificate.rankLE_resultRank

/-- Strict complementary matrix rank below fiber cardinality makes the chosen certificate shorter. -/
theorem certificate_resultRank_lt {S : Scheme k a b c r}
    (F : LiteralFirstFactorClass S) (hdefect : F.complementaryMatrix.rank < F.slots.card) :
    F.certificate.resultRank < r := by
  rw [F.certificate_resultRank]
  have hcard : F.slots.card ≤ r := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ F.slots)
  omega

/-- Positivity of the guarded natural cardinality-minus-rank value makes the chosen
full-fiber certificate shorter. -/
theorem certificate_resultRank_lt_of_matrixRankDefectNat_pos {S : Scheme k a b c r}
    (F : LiteralFirstFactorClass S)
    (hdefect : 0 < matrixRankDefectNat
      (fun s : Fin r => Matrix.vecMulVec (S.term s).2.1 (S.term s).2.2) F.slots) :
    F.certificate.resultRank < r := by
  have hrank := F.complementaryMatrix_rank_le_card
  have hlt : F.complementaryMatrix.rank < F.slots.card := by
    change 0 < F.slots.card - F.complementaryMatrix.rank at hdefect
    omega
  exact F.certificate_resultRank_lt hlt

/-- A positive full-class defect gives a one-step smaller tensor-rank upper bound. -/
theorem rankLE_pred_of_complementaryMatrix_rank_lt {S : Scheme k a b c r}
    (F : LiteralFirstFactorClass S) (hdefect : F.complementaryMatrix.rank < F.slots.card) :
    RankLE S.sumTensor (r - 1) := by
  have hshort := F.certificate_resultRank_lt hdefect
  exact F.certificate.rankLE_resultRank.mono (by omega)

end LiteralFirstFactorClass

end LiteralFirstFactor

end Scheme.Replacement

section DependenceCompatibility

/-- A dependent family of second factors sharing one first factor admits explicit pivot
elimination, independently of the complementary-matrix certificate construction. -/
theorem exists_shared_first_factor_reduction_certificate
    {k : Type*} [Field k] {a b c n : ℕ}
    (u : Fin a → k) (v : Fin (n + 1) → Fin b → k)
    (w : Fin (n + 1) → Fin c → k)
    (hdep : ¬ LinearIndependent k v) :
    ∃ (p : Fin (n + 1)) (g : Fin (n + 1) → k),
      g p ≠ 0 ∧ (∑ s, g s • v s) = 0 ∧
        ∀ i j l,
          (∑ s, u i * v s j * w s l) =
            ∑ t : Fin n, u i * v (p.succAbove t) j *
              (w (p.succAbove t) l - (g (p.succAbove t) / g p) * w p l) := by
  rw [Fintype.linearIndependent_iff] at hdep
  push Not at hdep
  obtain ⟨g, hg, p, hgp⟩ := hdep
  refine ⟨p, g, hgp, hg, ?_⟩
  intro i j l
  have hrel : (∑ s, g s * v s j) = 0 := by
    have hrelFun := congrFun hg j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using hrelFun
  rw [Fin.sum_univ_succAbove (fun s => g s * v s j) p] at hrel
  have hpterm : g p * v p j = -(∑ t, g (p.succAbove t) * v (p.succAbove t) j) :=
    eq_neg_of_add_eq_zero_left hrel
  have hvp : v p j =
      ∑ t, -(g (p.succAbove t) / g p) * v (p.succAbove t) j := by
    calc
      v p j = (g p)⁻¹ * (g p * v p j) := by
        rw [← mul_assoc, inv_mul_cancel₀ hgp, one_mul]
      _ = (g p)⁻¹ * (-(∑ t, g (p.succAbove t) * v (p.succAbove t) j)) := by
        rw [hpterm]
      _ = ∑ t, -(g (p.succAbove t) / g p) * v (p.succAbove t) j := by
        rw [mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro t _ht
        simp only [div_eq_mul_inv]
        ring
  rw [Fin.sum_univ_succAbove (fun s => u i * v s j * w s l) p]
  rw [hvp, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _ht
  ring

/-- A nonempty common-first-factor family with dependent second factors has rank at most one less. -/
theorem rankLE_sum_shared_first_factor_of_not_linearIndependent
    {k : Type*} [Field k] {a b c r : ℕ} (hr : 0 < r)
    (u : Fin a → k) (v : Fin r → Fin b → k) (w : Fin r → Fin c → k)
    (hdep : ¬ LinearIndependent k v) :
    RankLE (fun i j l => ∑ s, u i * v s j * w s l) (r - 1) := by
  cases r with
  | zero => simp at hr
  | succ n =>
      obtain ⟨p, g, _hgp, _hrel, hrewrite⟩ :=
        exists_shared_first_factor_reduction_certificate u v w hdep
      let w' : Fin n → Fin c → k := fun t l =>
        w (p.succAbove t) l - (g (p.succAbove t) / g p) * w p l
      have hrank : RankLE (fun i j l => ∑ s, u i * v s j * w s l) n := by
        refine ⟨fun _ => u, fun t => v (p.succAbove t), w', ?_⟩
        funext i j l
        exact hrewrite i j l
      simpa only [Nat.succ_sub_one] using hrank

/-- Scalar multiples of a common first factor may be absorbed in the third factors before
applying complementary second-factor dependence. -/
theorem rankLE_sum_scalar_shared_first_factor_of_not_linearIndependent
    {k : Type*} [Field k] {a b c r : ℕ} (hr : 0 < r)
    (u : Fin a → k) (q : Fin r → k)
    (v : Fin r → Fin b → k) (w : Fin r → Fin c → k)
    (hdep : ¬ LinearIndependent k v) :
    RankLE (fun i j l => ∑ s, (q s • u) i * v s j * w s l) (r - 1) := by
  let wscaled : Fin r → Fin c → k := fun s l => q s * w s l
  obtain ⟨u', v', w', hdecomp⟩ :=
    rankLE_sum_shared_first_factor_of_not_linearIndependent hr u v wscaled hdep
  refine ⟨u', v', w', ?_⟩
  calc
    (fun i j l => ∑ s, (q s • u) i * v s j * w s l) =
        (fun i j l => ∑ s, u i * v s j * wscaled s l) := by
          funext i j l
          apply Finset.sum_congr rfl
          intro s _hs
          simp only [Pi.smul_apply, smul_eq_mul, wscaled]
          ring
    _ = fun i j l => ∑ s, u' s i * v' s j * w' s l := hdecomp

/-- A common second factor and dependent first factors also give rank at most one less,
by permuting the first two tensor modes. -/
theorem rankLE_sum_shared_second_factor_of_not_linearIndependent
    {k : Type*} [Field k] {a b c r : ℕ} (hr : 0 < r)
    (u : Fin r → Fin a → k) (v : Fin b → k) (w : Fin r → Fin c → k)
    (hdep : ¬ LinearIndependent k u) :
    RankLE (fun i j l => ∑ s, u s i * v j * w s l) (r - 1) := by
  obtain ⟨v', u', w', hdecomp⟩ :=
    rankLE_sum_shared_first_factor_of_not_linearIndependent hr v u w hdep
  refine ⟨u', v', w', ?_⟩
  funext i j l
  have hentry := congrFun (congrFun (congrFun hdecomp j) i) l
  calc
    (∑ s, u s i * v j * w s l) = ∑ s, v j * u s i * w s l := by
      apply Finset.sum_congr rfl
      intro s _hs
      ring
    _ = ∑ s, v' s j * u' s i * w' s l := hentry
    _ = ∑ s, u' s i * v' s j * w' s l := by
      apply Finset.sum_congr rfl
      intro s _hs
      ring

end DependenceCompatibility

section BoundaryAcceptance

/-- A singleton nonzero rank-one matrix has zero defect, while enlarging it by a duplicate
has positive defect; this also disproves monotonicity in the reverse direction. -/
example :
    let A : Fin 2 → Matrix (Fin 1) (Fin 1) ℚ := fun _ => 1
    let I : Finset (Fin 2) := {0}
    let G : Finset (Fin 2) := Finset.univ
    matrixRankDefectNat A I = 0 ∧
      0 < matrixRankDefectNat A G ∧
      ¬matrixRankDefectNat A G ≤ matrixRankDefectNat A I := by
  dsimp only
  let A : Fin 2 → Matrix (Fin 1) (Fin 1) ℚ := fun _ => 1
  let I : Finset (Fin 2) := {0}
  let G : Finset (Fin 2) := Finset.univ
  change matrixRankDefectNat A I = 0 ∧
    0 < matrixRankDefectNat A G ∧
    ¬matrixRankDefectNat A G ≤ matrixRankDefectNat A I
  have hrankOne : Matrix.rank (1 : Matrix (Fin 1) (Fin 1) ℚ) = 1 := by
    simp [Matrix.rank_one]
  have hI : matrixRankDefectNat A I = 0 := by
    simp [matrixRankDefectNat, A, I, hrankOne]
  have hbound : Matrix.rank (∑ i ∈ G, A i) ≤ 1 := by
    simpa using Matrix.rank_le_card_width (∑ i ∈ G, A i)
  have hG : 0 < matrixRankDefectNat A G := by
    have hGcard : G.card = 2 := by simp [G]
    change 0 < G.card - Matrix.rank (∑ i ∈ G, A i)
    rw [hGcard]
    omega
  refine ⟨hI, hG, ?_⟩
  simpa only [hI] using (not_le_of_gt hG)

/-- Two zero outer-product matrices exercise zero complementary vectors and maximal defect. -/
example : matrixRankDefectNat
    (fun _ : Fin 2 => (0 : Matrix (Fin 1) (Fin 1) ℚ)) Finset.univ = 2 := by
  simp [matrixRankDefectNat]

namespace Scheme.Replacement.LiteralFirstFactorClass

/-- A valid two-slot source with a shared nonzero first factor and distinct evaluated terms
has a full anchored fiber, complementary rank one, chosen result rank one, and `RankLE` one. -/
example :
    let S : Scheme ℚ 1 1 2 2 :=
      ⟨fun s => (fun _ => 1, fun _ => 1, fun l => if l = s then 1 else 0)⟩
    let F : LiteralFirstFactorClass S := {
      factor := fun _ => 1
      anchor := 0
      anchor_factor := rfl
      factor_ne_zero := by
        intro h
        have h0 := congrFun h 0
        norm_num at h0
    }
    S.Valid S.sumTensor ∧
      F.slots = Finset.univ ∧
      F.complementaryMatrix.rank = 1 ∧
      F.certificate.resultRank = 1 ∧
      RankLE S.sumTensor 1 := by
  dsimp only
  let S : Scheme ℚ 1 1 2 2 :=
    ⟨fun s => (fun _ => 1, fun _ => 1, fun l => if l = s then 1 else 0)⟩
  let F : LiteralFirstFactorClass S := {
    factor := fun _ => 1
    anchor := 0
    anchor_factor := rfl
    factor_ne_zero := by
      intro h
      have h0 := congrFun h 0
      norm_num at h0
  }
  have hvalid : S.Valid S.sumTensor := by
    refine ⟨rfl, ?_, ?_⟩
    · intro s hzero
      have hentry := congrFun (congrFun (congrFun hzero 0) 0) s
      norm_num [Scheme.TermNonzero, TriadData.eval, S] at hentry
    · intro s t heval
      by_contra hst
      have hentry := congrFun (congrFun (congrFun heval 0) 0) s
      norm_num [TriadData.eval, S, hst] at hentry
  have hslots : F.slots = Finset.univ := by
    ext s
    simp [slots, F, S]
  have hrank : F.complementaryMatrix.rank ≤ 1 := by
    simpa using Matrix.rank_le_card_height F.complementaryMatrix
  have hentry : F.complementaryMatrix 0 0 = 1 := by
    rw [complementaryMatrix_apply, hslots]
    norm_num [F, S]
  have hrankLower : 1 ≤ F.complementaryMatrix.rank := by
    apply le_rank_of_submatrix_det_ne_zero F.complementaryMatrix
      (fun i => i) (fun _ => (0 : Fin 2))
    rw [Matrix.det_fin_one]
    change F.complementaryMatrix 0 0 ≠ 0
    rw [hentry]
    norm_num
  have hrankEq : F.complementaryMatrix.rank = 1 := by omega
  have hlt : F.complementaryMatrix.rank < F.slots.card := by
    rw [hslots]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  have hresult : F.certificate.resultRank = 1 := by
    rw [certificate_resultRank, hslots, hrankEq]
    norm_num
  have hrankLE := F.rankLE_pred_of_complementaryMatrix_rank_lt hlt
  exact ⟨hvalid, hslots, hrankEq, hresult, hrankLE⟩

end Scheme.Replacement.LiteralFirstFactorClass

end BoundaryAcceptance

#check @matrix_rank_sum_le_card_of_rank_le_one
#check @matrix_rank_sum_growth
#check @matrixRankDefectNat
#check @matrixRankDefectNat_mono
#check @matrixRankDefectNat_eq_zero_of_subset
#check @matrixRankDefectNat_pos_of_subset
#check @exists_eq_sum_vecMulVec_rank
#check @rankLE_common_first_factor_matrix
#check @rankLE_sum_shared_first_factor
#check @rankLE_sum_shared_second_factor
#check @rankLE_sum_shared_third_factor
#check @Scheme.Replacement.LiteralFirstFactorClass
#check @Scheme.Replacement.LiteralFirstFactorClass.mk
#check @Scheme.Replacement.LiteralFirstFactorClass.mem_slots
#check @Scheme.Replacement.LiteralFirstFactorClass.anchor_mem_slots
#check @Scheme.Replacement.LiteralFirstFactorClass.slots_nonempty
#check @Scheme.Replacement.LiteralFirstFactorClass.matrixRankDefectNat_eq_card_sub_rank
#check @Scheme.Replacement.exists_literalFirstFactorClass_certificate
#check @Scheme.Replacement.LiteralFirstFactorClass.certificate_local_eq
#check @Scheme.Replacement.LiteralFirstFactorClass.certificate_sumTensor_eq
#check @Scheme.Replacement.LiteralFirstFactorClass.certificate_rankLE
#check @Scheme.Replacement.LiteralFirstFactorClass.certificate_resultRank_lt
#check @Scheme.Replacement.LiteralFirstFactorClass.certificate_resultRank_lt_of_matrixRankDefectNat_pos
#check @Scheme.Replacement.LiteralFirstFactorClass.rankLE_pred_of_complementaryMatrix_rank_lt
#check @exists_shared_first_factor_reduction_certificate
#check @rankLE_sum_shared_first_factor_of_not_linearIndependent
#check @rankLE_sum_scalar_shared_first_factor_of_not_linearIndependent
#check @rankLE_sum_shared_second_factor_of_not_linearIndependent

#print axioms matrixRankDefectNat_mono
#print axioms Scheme.Replacement.LiteralFirstFactorClass.anchor_mem_slots
#print axioms Scheme.Replacement.LiteralFirstFactorClass.slots_nonempty
#print axioms exists_eq_sum_vecMulVec_rank
#print axioms rankLE_sum_shared_first_factor
#print axioms rankLE_sum_shared_second_factor
#print axioms rankLE_sum_shared_third_factor
#print axioms Scheme.Replacement.exists_literalFirstFactorClass_certificate
#print axioms Scheme.Replacement.LiteralFirstFactorClass.certificate_local_eq
#print axioms Scheme.Replacement.LiteralFirstFactorClass.certificate_sumTensor_eq
#print axioms Scheme.Replacement.LiteralFirstFactorClass.certificate_rankLE
#print axioms Scheme.Replacement.LiteralFirstFactorClass.certificate_resultRank_lt
#print axioms Scheme.Replacement.LiteralFirstFactorClass.certificate_resultRank_lt_of_matrixRankDefectNat_pos
#print axioms Scheme.Replacement.LiteralFirstFactorClass.rankLE_pred_of_complementaryMatrix_rank_lt
#print axioms exists_shared_first_factor_reduction_certificate
#print axioms rankLE_sum_shared_first_factor_of_not_linearIndependent
#print axioms rankLE_sum_scalar_shared_first_factor_of_not_linearIndependent
#print axioms rankLE_sum_shared_second_factor_of_not_linearIndependent

end BilinearComplexity
