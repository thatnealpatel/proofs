/-
  BilinearComplexity/Flattening — rectangular flattenings and the
  flattening lower bound n² ≤ R⟨n,n,n⟩ (port of the Vp2 cubic bound).

    · `flattening T`     — the first-factor flattening of a rectangular
                           3-tensor, an `a × (b*c)` matrix with columns
                           indexed by `Fin b × Fin c` (rectangular port
                           of `Vp2.flattening`).
    · `RankLE.rank_flattening_le` — a rank-≤ r tensor has flattening
                           rank ≤ r: the flattening factors through
                           `Fin r` as an `a × r` times `r × (b*c)`
                           product (port of
                           `Vp2.RankLE.rank_flattening_le`).
    · `rank_flattening_matMulTensor` — the flattening of `⟨n,n,n⟩` has
                           FULL rank `n * n`: the submatrix on the
                           distinguished columns
                           `y₀(i,j) = ((j,0), (0,i))` is the identity
                           matrix (the δ-conditions pin the unique
                           nonzero row), so `rank_submatrix_le` gives
                           the lower bound and the row count the upper.
    · `sq_le_rank_matMulTensor` — the payoff `n ^ 2 ≤ rank ⟨n,n,n⟩`:
                           the classical flattening lower bound on the
                           rank of matrix multiplication.

  AI disclosure: produced with AI assistance (see Proofs/README).
-/
import Mathlib.LinearAlgebra.Matrix.Rank
import BilinearComplexity.Basic
import BilinearComplexity.LinearFlattening

set_option autoImplicit false

namespace BilinearComplexity

/-! ## 1. The flattening and its rank bound -/

/-- The first-factor flattening of a rectangular 3-tensor, as an
`a × (b*c)` matrix: row `i`, column `(j, l)` holds `T i j l`. -/
def flattening {k : Type*} {a b c : ℕ} (T : Tensor k a b c) :
    Matrix (Fin a) (Fin b × Fin c) k :=
  fun i jl => T i jl.1 jl.2

/-- The first-factor flattening as a linear map over a field. Its value is
definitionally the existing ring-generic `flattening`. -/
def flatteningLinear {k : Type*} [Field k] {a b c : ℕ} :
    Tensor k a b c →ₗ[k] Matrix (Fin a) (Fin b × Fin c) k where
  toFun := flattening
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Evaluating the linear wrapper gives the original flattening. -/
@[simp] theorem flatteningLinear_apply {k : Type*} [Field k] {a b c : ℕ}
    (T : Tensor k a b c) : flatteningLinear T = flattening T := rfl

/-- Ground-truth check: the linear wrapper has the expected entry formula. -/
example {k : Type*} [Field k] {a b c : ℕ} (T : Tensor k a b c)
    (i : Fin a) (j : Fin b) (l : Fin c) :
    flatteningLinear T i (j, l) = T i j l := rfl

#check @flatteningLinear
#check @flatteningLinear_apply

/-- A rank-≤ r tensor has flattening rank ≤ r: the flattening factors as
an `a × r` times `r × (b*c)` matrix product, so its rank is bounded by
the inner dimension. -/
theorem RankLE.rank_flattening_le {k : Type*} [CommRing k] [Nontrivial k]
    {a b c : ℕ} {T : Tensor k a b c} {r : ℕ} (h : RankLE T r) :
    (flattening T).rank ≤ r := by
  obtain ⟨u, v, w, rfl⟩ := h
  have hfac : flattening (fun i j l => ∑ s, u s i * v s j * w s l) =
      Matrix.of (fun i (s : Fin r) => u s i) *
        Matrix.of (fun (s : Fin r) jl => v s jl.1 * w s jl.2) := by
    ext i jl
    simp [flattening, Matrix.mul_apply, mul_assoc]
  rw [hfac]
  exact (Matrix.rank_mul_le_left _ _).trans
    ((Matrix.rank_le_card_width _).trans_eq (Fintype.card_fin r))

/-- The ordinary flattening of a simple tensor factors through one column,
so its matrix rank is at most one. This proof is independent of the legacy
tensor-rank flattening theorem. -/
theorem rank_flatteningLinear_simple_le_one {k : Type*} [Field k]
    {a b c : ℕ} (u : Fin a → k) (v : Fin b → k) (w : Fin c → k) :
    (flatteningLinear (fun i j l => u i * v j * w l)).rank ≤ 1 := by
  have hfac : flatteningLinear (fun i j l => u i * v j * w l) =
      Matrix.of (fun i (_s : Fin 1) => u i) *
        Matrix.of (fun (_s : Fin 1) jl => v jl.1 * w jl.2) := by
    rw [flatteningLinear_apply]
    ext i jl
    simp [flattening, Matrix.mul_apply, mul_assoc]
  rw [hfac]
  exact (Matrix.rank_mul_le_left _ _).trans
    ((Matrix.rank_le_card_width _).trans_eq (Fintype.card_fin 1))

/-- Over a field, the generic linear-flattening theorem recovers the existing
ordinary flattening rank bound. The ring-generic theorem above remains
unchanged. -/
theorem RankLE.rank_flatteningLinear_le {k : Type*} [Field k]
    {a b c r : ℕ} {T : Tensor k a b c} (hT : RankLE T r) :
    (flatteningLinear T).rank ≤ r := by
  simpa using rank_linearMap_le_mul_of_rankLE flatteningLinear
    rank_flatteningLinear_simple_le_one hT

/-- A tiny linear flattening from `1 × 1 × 2` tensors to `2 × 2`
matrices, placing the two tensor coordinates on the diagonal. Unlike adding a
flattening to itself, a simple tensor can have image rank exactly two. -/
def twoDiagonalLinear {k : Type*} [Field k] :
    Tensor k 1 1 2 →ₗ[k] Matrix (Fin 2) (Fin 2) k where
  toFun T i j := if i = j then T 0 0 i else 0
  map_add' T S := by
    ext i j
    change (if i = j then (T + S) 0 0 i else 0) =
      (if i = j then T 0 0 i else 0) + (if i = j then S 0 0 i else 0)
    by_cases hij : i = j <;> simp [hij]
  map_smul' x T := by
    ext i j
    change (if i = j then (x • T) 0 0 i else 0) =
      x * (if i = j then T 0 0 i else 0)
    by_cases hij : i = j <;> simp [hij]

/-- Entry formula for the tiny two-diagonal linear flattening. -/
@[simp] theorem twoDiagonalLinear_apply {k : Type*} [Field k]
    (T : Tensor k 1 1 2) (i j : Fin 2) :
    twoDiagonalLinear T i j = if i = j then T 0 0 i else 0 := rfl

/-- Ground-truth check: the first tensor coordinate occupies the first
diagonal entry. -/
example : twoDiagonalLinear (k := ℚ) (fun _ _ l => (l : ℚ) + 3) 0 0 = 3 := by
  simp

/-- Every simple tensor has two-diagonal image rank at most two. -/
theorem rank_twoDiagonalLinear_simple_le_two {k : Type*} [Field k]
    (u : Fin 1 → k) (v : Fin 1 → k) (w : Fin 2 → k) :
    (twoDiagonalLinear (fun i j l => u i * v j * w l)).rank ≤ 2 :=
  (Matrix.rank_le_card_height _).trans_eq (Fintype.card_fin 2)

/-- The generic linear-flattening theorem gives the genuine non-unit bound
`rank (twoDiagonalLinear T) ≤ r * 2` from an `r`-triad decomposition. -/
theorem RankLE.rank_twoDiagonalLinear_le {k : Type*} [Field k]
    {r : ℕ} {T : Tensor k 1 1 2} (hT : RankLE T r) :
    (twoDiagonalLinear T).rank ≤ r * 2 :=
  rank_linearMap_le_mul_of_rankLE twoDiagonalLinear
    rank_twoDiagonalLinear_simple_le_two hT

/-- Over `ℚ`, the all-ones simple `1 × 1 × 2` tensor has a one-term
triad decomposition and maps to the identity. Thus the uniform simple-image
bound two is attained exactly, jointly with the generic `r * 2` application. -/
example :
    let T : Tensor ℚ 1 1 2 := fun _ _ _ => 1
    RankLE T 1 ∧ (twoDiagonalLinear T).rank = 2 ∧
      (twoDiagonalLinear T).rank ≤ 1 * 2 := by
  dsimp
  have hT : RankLE (fun _ _ _ => (1 : ℚ) : Tensor ℚ 1 1 2) 1 :=
    ⟨fun _ _ => 1, fun _ _ => 1, fun _ _ => 1, by funext; simp⟩
  have hmatrix : twoDiagonalLinear (fun _ _ _ => (1 : ℚ)) = 1 := by
    ext i j
    simp only [twoDiagonalLinear_apply, Matrix.one_apply]
  refine ⟨hT, ?_, hT.rank_twoDiagonalLinear_le⟩
  rw [hmatrix, Matrix.rank_one, Fintype.card_fin]

#check @twoDiagonalLinear
#check @twoDiagonalLinear_apply
#check @rank_twoDiagonalLinear_simple_le_two
#check @RankLE.rank_twoDiagonalLinear_le

#check @rank_flatteningLinear_simple_le_one
#check @RankLE.rank_flatteningLinear_le

/-! ## 2. The flattening of the matmul tensor has full rank -/

/-- The flattening of the matrix multiplication tensor `⟨n,n,n⟩` has full
rank `n * n`. Lower bound: for each row `x = (i,j)` the distinguished
column `y₀ x = ((j,0), (0,i))` has its unique nonzero entry `1` in row
`x` — the δ-conditions `j = j'`, `l = l' = 0`, `i' = i` pin the row — so
the square submatrix on the columns `y₀` is the identity matrix, whose
rank `n * n` bounds the flattening rank from below
(`Matrix.rank_submatrix_le`). Upper bound: the matrix has `n * n` rows. -/
theorem rank_flattening_matMulTensor (k : Type*) [CommRing k] [Nontrivial k]
    (n : ℕ) : (flattening (matMulTensor k n n n)).rank = n * n := by
  refine le_antisymm
    ((Matrix.rank_le_card_height _).trans_eq (Fintype.card_fin _)) ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Nat.zero_le _
  have hsub : (flattening (matMulTensor k n n n)).submatrix id
      (fun x : Fin (n * n) =>
        (finProdFinEquiv ((finProdFinEquiv.symm x).2, ⟨0, hn⟩),
         finProdFinEquiv (⟨0, hn⟩, (finProdFinEquiv.symm x).1))) = 1 := by
    ext x x'
    simp only [Matrix.submatrix_apply, id_eq, flattening, matMulTensor_apply,
      Equiv.symm_apply_apply, Matrix.one_apply]
    by_cases h : x = x'
    · subst h; simp
    · rw [if_neg h]
      refine if_neg ?_
      rintro ⟨h1, -, h3⟩
      exact h (finProdFinEquiv.symm.injective (Prod.ext h3.symm h1))
  calc n * n = Fintype.card (Fin (n * n)) := (Fintype.card_fin _).symm
    _ = (1 : Matrix (Fin (n * n)) (Fin (n * n)) k).rank := Matrix.rank_one.symm
    _ = ((flattening (matMulTensor k n n n)).submatrix id
          (fun x : Fin (n * n) =>
            (finProdFinEquiv ((finProdFinEquiv.symm x).2, ⟨0, hn⟩),
             finProdFinEquiv (⟨0, hn⟩, (finProdFinEquiv.symm x).1)))).rank := by
        rw [hsub]
    _ ≤ (flattening (matMulTensor k n n n)).rank :=
        Matrix.rank_submatrix_le _ _ _

/-! ## 3. The payoff: n² ≤ R⟨n,n,n⟩ -/

/-- The flattening lower bound on the rank of matrix multiplication:
`n ^ 2 ≤ rank ⟨n,n,n⟩`. Any decomposition of `⟨n,n,n⟩` into `r` triads
bounds the flattening rank by `r` (`RankLE.rank_flattening_le`), and the
flattening has full rank `n²` (`rank_flattening_matMulTensor`). -/
theorem sq_le_rank_matMulTensor (k : Type*) [CommRing k] [Nontrivial k]
    (n : ℕ) : n ^ 2 ≤ rank (matMulTensor k n n n) :=
  calc n ^ 2 = n * n := pow_two n
    _ = (flattening (matMulTensor k n n n)).rank :=
        (rank_flattening_matMulTensor k n).symm
    _ ≤ rank (matMulTensor k n n n) :=
        (rankLE_rank (matMulTensor k n n n)).rank_flattening_le

/-! ## 4. Concrete satisfiability audit -/

/-- Over `ℚ`, the `1 × 1 × 1` multiplication tensor simultaneously has a
one-triad decomposition and a nonzero `1 × 1` flattening minor, so the
certificate hypotheses are jointly satisfiable and non-vacuous. -/
example :
    let T := matMulTensor ℚ 1 1 1
    RankLE T 1 ∧
      ((flatteningLinear T).submatrix id (fun x : Fin 1 => (x, x))).det ≠ 0 := by
  dsimp
  constructor
  · exact rankLE_matMulTensor_one ℚ
  · have hmatrix :
        (flatteningLinear (matMulTensor ℚ 1 1 1)).submatrix id
          (fun x : Fin 1 => (x, x)) = 1 := by
      ext i j
      simp only [Matrix.submatrix_apply, id_eq, flatteningLinear_apply, flattening,
        matMulTensor_apply, Matrix.one_apply]
      rw [if_pos ⟨Fin.ext (by omega), Fin.ext (by omega),
        Fin.ext (by omega)⟩, if_pos (Fin.ext (by omega))]
    change ((flatteningLinear (matMulTensor ℚ 1 1 1)).submatrix id
      (fun x : Fin 1 => (x, x))).det ≠ 0
    rw [hmatrix, Matrix.det_one]
    exact one_ne_zero

/-- The generic theorem's simple-image and decomposition hypotheses are
jointly realized by the positive-dimensional `1 × 1 × 1` multiplication tensor. -/
example : (flatteningLinear (matMulTensor ℚ 1 1 1)).rank ≤ 1 :=
  rank_linearMap_le_mul_of_rankLE flatteningLinear
    rank_flatteningLinear_simple_le_one (rankLE_matMulTensor_one ℚ)

/-- The strict minor threshold is jointly satisfiable: the nonzero scalar
tensor cannot have a zero-term triad decomposition. -/
example : ¬ RankLE (matMulTensor ℚ 1 1 1) 0 := by
  have hmatrix :
      (flatteningLinear (matMulTensor ℚ 1 1 1)).submatrix id
        (fun x : Fin 1 => (x, x)) = 1 := by
    ext i j
    simp only [Matrix.submatrix_apply, id_eq, flatteningLinear_apply, flattening,
      matMulTensor_apply, Matrix.one_apply]
    rw [if_pos ⟨Fin.ext (by omega), Fin.ext (by omega),
      Fin.ext (by omega)⟩, if_pos (Fin.ext (by omega))]
  have hdet :
      ((flatteningLinear (matMulTensor ℚ 1 1 1)).submatrix id
        (fun x : Fin 1 => (x, x))).det ≠ 0 := by
    rw [hmatrix, Matrix.det_one]
    exact one_ne_zero
  exact not_rankLE_of_mul_lt_of_submatrix_det_ne_zero
    (r := 0) (q := 1) flatteningLinear rank_flatteningLinear_simple_le_one
    id (fun x : Fin 1 => (x, x)) hdet (by omega)

/-- A zero tensor mode is explicitly non-vacuous at the tensor level: the
unique `0 × 1 × 1` tensor has a zero-term decomposition, and the generic
linear theorem forces its flattening rank to zero. -/
example :
    let T : Tensor ℚ 0 1 1 := 0
    RankLE T 0 ∧ (flatteningLinear T).rank = 0 := by
  dsimp
  have hT : RankLE (0 : Tensor ℚ 0 1 1) 0 := by
    refine ⟨fun s => Fin.elim0 s, fun s => Fin.elim0 s,
      fun s => Fin.elim0 s, ?_⟩
    funext i
    exact Fin.elim0 i
  refine ⟨hT, Nat.le_zero.mp ?_⟩
  exact rank_linearMap_le_mul_of_rankLE flatteningLinear
    rank_flatteningLinear_simple_le_one hT

/-- The second tensor mode may also be zero: the unique `1 × 0 × 1` tensor
has a zero-term decomposition and zero flattening rank through the generic
theorem. -/
example :
    let T : Tensor ℚ 1 0 1 := 0
    RankLE T 0 ∧ (flatteningLinear T).rank = 0 := by
  dsimp
  have hT : RankLE (0 : Tensor ℚ 1 0 1) 0 := by
    refine ⟨fun s => Fin.elim0 s, fun s => Fin.elim0 s,
      fun s => Fin.elim0 s, ?_⟩
    funext i j
    exact Fin.elim0 j
  refine ⟨hT, Nat.le_zero.mp ?_⟩
  exact rank_linearMap_le_mul_of_rankLE flatteningLinear
    rank_flatteningLinear_simple_le_one hT

/-- The third tensor mode may likewise be zero: the unique `1 × 1 × 0`
tensor has a zero-term decomposition and zero flattening rank through the
generic theorem. -/
example :
    let T : Tensor ℚ 1 1 0 := 0
    RankLE T 0 ∧ (flatteningLinear T).rank = 0 := by
  dsimp
  have hT : RankLE (0 : Tensor ℚ 1 1 0) 0 := by
    refine ⟨fun s => Fin.elim0 s, fun s => Fin.elim0 s,
      fun s => Fin.elim0 s, ?_⟩
    funext i j l
    exact Fin.elim0 l
  refine ⟨hT, Nat.le_zero.mp ?_⟩
  exact rank_linearMap_le_mul_of_rankLE flatteningLinear
    rank_flatteningLinear_simple_le_one hT

#print axioms flatteningLinear_apply
#print axioms rank_flatteningLinear_simple_le_one
#print axioms RankLE.rank_flatteningLinear_le
#print axioms twoDiagonalLinear_apply
#print axioms rank_twoDiagonalLinear_simple_le_two
#print axioms RankLE.rank_twoDiagonalLinear_le

end BilinearComplexity
