/-
  Scratch/GlobalRankSearch/ContractionSupport — contraction support bounds for
  exact decompositions of square matrix multiplication.

  The packed convention is row-major.  Thus `packedFunctional F` evaluates a
  matrix functional on the matrix whose `(i,j)` entry is coordinate `(i,j)`;
  equivalently its coefficient at `finProdFinEquiv (i,j)` is `F i j`.
-/
import BilinearComplexity.RankCalculus
import BilinearComplexity.Support
import BilinearComplexity.LinearFlattening
import Mathlib.LinearAlgebra.Matrix.Rank

set_option autoImplicit false

namespace BilinearComplexity

/-- Pack the coefficients of an `n × n` matrix functional in the row-major
coordinate convention used by `matMulTensor`: row is slow and column is fast. -/
def packedFunctional {k : Type*} {n : ℕ} (F : Matrix (Fin n) (Fin n) k) :
    Fin (n * n) → k := fun x => F (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm x).2

/-- Ground check for the packed matrix-functional convention. -/
example : packedFunctional !![(1 : ℚ), 2; 3, 4] (finProdFinEquiv (1, 0)) = 3 := by
  rfl

/-- The matrix obtained by flattening the last two modes of a tensor whose
first mode is a singleton. -/
def singletonFlatten {k : Type*} {b c : ℕ} (T : Tensor k 1 b c) :
    Matrix (Fin b) (Fin c) k := fun j l => T 0 j l

/-- Nonempty ground check: singleton flattening preserves the last-mode column
orientation of a `1 × 1 × 2` tensor. -/
example : singletonFlatten
    (fun (_ : Fin 1) (_ : Fin 1) (l : Fin 2) => (l.1 : ℚ)) 0 1 = 1 := by
  rfl

/-- Flattening a singleton-first-mode triad is an outer-product matrix. -/
theorem singletonFlatten_triad {k : Type*} [CommSemiring k] {b c : ℕ}
    (u : Fin 1 → k) (v : Fin b → k) (w : Fin c → k) :
    singletonFlatten (triad u v w) = Matrix.vecMulVec (u 0 • v) w := by
  ext j l
  simp [singletonFlatten, triad, Matrix.vecMulVec, mul_assoc]

/-- Matrix rank of the singleton flattening never exceeds tensor rank. -/
theorem singletonFlatten_rank_le {k : Type*} [Field k] {b c : ℕ}
    (T : Tensor k 1 b c) : (singletonFlatten T).rank ≤ rank T := by
  let L : Tensor k 1 b c →ₗ[k] Matrix (Fin b) (Fin c) k :=
    { toFun := singletonFlatten
      map_add' := by intro A B; ext; rfl
      map_smul' := by intro x A; ext; rfl }
  have hsimple : ∀ (u : Fin 1 → k) (v : Fin b → k) (w : Fin c → k),
      (L (triad u v w)).rank ≤ 1 := by
    intro u v w
    rw [show L (triad u v w) = singletonFlatten (triad u v w) from rfl,
      singletonFlatten_triad]
    exact Matrix.rank_vecMulVec_le (R := k) (u 0 • v) w
  simpa only [show L T = singletonFlatten T from rfl, Nat.mul_one] using
    rank_linearMap_le_mul_of_rankLE L hsimple (rankLE_rank T)

/-- Contract square matrix multiplication in mode one by a packed matrix
functional.  This names the exact tensor whose rank controls mode-one support. -/
def matMulContractOne {k : Type*} [CommSemiring k] (n : ℕ)
    (F : Matrix (Fin n) (Fin n) k) : Tensor k 1 (n * n) (n * n) :=
  contract₁ (fun _ x => packedFunctional F x) (matMulTensor k n n n)

/-- Coordinate formula for mode-one contraction: at `y=(j,l)` and `z=(l',i)`
the output is `F i j` when `l=l'`, and zero otherwise. -/
theorem matMulContractOne_apply {k : Type*} [CommSemiring k] (n : ℕ)
    (F : Matrix (Fin n) (Fin n) k) (y z : Fin (n * n)) :
    matMulContractOne n F 0 y z =
      if (finProdFinEquiv.symm y).2 = (finProdFinEquiv.symm z).1 then
        F (finProdFinEquiv.symm z).2 (finProdFinEquiv.symm y).1 else 0 := by
  classical
  simp only [matMulContractOne, contract₁, packedFunctional, matMulTensor_apply]
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin n × Fin n ≃ Fin (n * n))]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type]
  change (∑ i : Fin n, ∑ j : Fin n,
      F i j * if j = y.divNat ∧ y.modNat = z.divNat ∧ z.modNat = i then 1 else 0) =
    if y.modNat = z.divNat then F z.modNat y.divNat else 0
  by_cases h : y.modNat = z.divNat
  · rw [if_pos h]
    rw [Finset.sum_eq_single (finProdFinEquiv.symm z).2]
    · rw [Finset.sum_eq_single (finProdFinEquiv.symm y).1]
      · simp [h]
      · intro j _ hj
        simp only [mul_ite, mul_one, mul_zero, ite_eq_right_iff]
        rintro ⟨hj', _, _⟩
        exact (hj (by simpa using hj')).elim
      · simp
    · intro i _ hi
      apply Finset.sum_eq_zero
      intro j _
      simp only [mul_ite, mul_one, mul_zero, ite_eq_right_iff]
      rintro ⟨_, _, hiz⟩
      exact (hi (by simpa using hiz.symm)).elim
    · simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    simp only [mul_ite, mul_one, mul_zero, ite_eq_right_iff]
    rintro ⟨_, hyz, _⟩
    exact (h hyz).elim

/-- Nonempty ground check: contracting the unique coordinate of a `1 × 1`
matrix returns its scalar in the unique remaining matrix entry. -/
example : matMulContractOne 1 !![(7 : ℚ)] 0 0 0 = 7 := by
  rw [matMulContractOne_apply]
  rfl

/-- A square matrix is a sum of exactly `F.rank` outer products. -/
theorem exists_outer_decomposition {k : Type*} [Field k] {n : ℕ}
    (F : Matrix (Fin n) (Fin n) k) :
    ∃ u v : Fin F.rank → Fin n → k,
      F = fun i j => ∑ p, u p i * v p j := by
  classical
  let S : Submodule k (Fin n → k) := Submodule.span k (Set.range F.col)
  let bS := Module.finBasis k S
  have hr : F.rank = Module.finrank k S := Matrix.rank_eq_finrank_span_cols F
  let colS (j : Fin n) : S :=
    ⟨F.col j, Submodule.subset_span (Set.mem_range_self j)⟩
  let u : Fin F.rank → Fin n → k := fun p i =>
    (bS (Fin.cast hr p) : Fin n → k) i
  let v : Fin F.rank → Fin n → k := fun p j =>
    (bS.repr (colS j)) (Fin.cast hr p)
  refine ⟨u, v, ?_⟩
  ext i j
  have hs := bS.sum_repr (colS j)
  have hi := congrFun (congrArg Subtype.val hs) i
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] at hi
  change (∑ q, (bS.repr (colS j)) q * (bS q : Fin n → k) i) = F i j at hi
  have hq : F i j = ∑ q : Fin (Module.finrank k S),
      (bS q : Fin n → k) i * (bS.repr (colS j)) q := by
    simpa only [mul_comm] using hi.symm
  calc
    F i j = _ := hq
    _ = ∑ p : Fin F.rank, u p i * v p j := by
      rw [← Equiv.sum_comp (Fin.castOrderIso hr).toEquiv]
      rfl

/-- The mode-one contraction has an `n * F.rank`-term decomposition. -/
theorem matMulContractOne_rank_le {k : Type*} [Field k] (n : ℕ)
    (F : Matrix (Fin n) (Fin n) k) : rank (matMulContractOne n F) ≤ n * F.rank := by
  classical
  obtain ⟨u, v, hF⟩ := exists_outer_decomposition F
  apply rank_le_of_rankLE
  refine ⟨fun _ _ => 1,
    fun s y => if (finProdFinEquiv.symm s).1 = (finProdFinEquiv.symm y).2 then
      v (finProdFinEquiv.symm s).2 (finProdFinEquiv.symm y).1 else 0,
    fun s z => if (finProdFinEquiv.symm s).1 = (finProdFinEquiv.symm z).1 then
      u (finProdFinEquiv.symm s).2 (finProdFinEquiv.symm z).2 else 0, ?_⟩
  funext x y z
  have hx : x = (0 : Fin 1) := Subsingleton.elim _ _
  subst x
  rw [matMulContractOne_apply]
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin n × Fin F.rank ≃ Fin (n * F.rank))]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type, one_mul]
  change (if y.modNat = z.divNat then F z.modNat y.divNat else 0) =
    ∑ l : Fin n, ∑ p : Fin F.rank,
      (if l = y.modNat then v p y.divNat else 0) *
        if l = z.divNat then u p z.modNat else 0
  by_cases h : y.modNat = z.divNat
  · rw [if_pos h]
    have hFyz := congrFun (congrFun hF z.modNat) y.divNat
    rw [hFyz]
    rw [Finset.sum_eq_single y.modNat]
    · exact Finset.sum_congr rfl fun p _ => by simp [h, mul_comm]
    · intro l _ hl
      simp [hl]
    · simp
  · rw [if_neg h]
    symm
    apply Finset.sum_eq_zero
    intro l _
    by_cases hl : l = y.modNat
    · subst l
      simp [h]
    · simp [hl]

/-- Repeat a square matrix on `n` independent diagonal blocks, with the block
index in the second component. -/
def repeatedBlock {k : Type*} [Zero k] {m n : ℕ} (A : Matrix (Fin m) (Fin m) k) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) k := fun jl il' =>
  if jl.2 = il'.2 then A jl.1 il'.1 else 0

/-- Nonempty ground check: two scalar blocks retain their diagonal scalar and
have zero cross-block entries. -/
example :
    repeatedBlock (n := 2) !![(7 : ℚ)] (0, 0) (0, 0) = 7 ∧
      repeatedBlock (n := 2) !![(7 : ℚ)] (0, 0) (0, 1) = 0 := by
  constructor <;> rfl

/-- Multiplication by `repeatedBlock A` applies `A` independently in every block. -/
theorem repeatedBlock_mulVec {k : Type*} [Semiring k] {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) k) (x : Fin m × Fin n → k) (j : Fin m) (l : Fin n) :
    (repeatedBlock A).mulVec x (j, l) = A.mulVec (fun i => x (i, l)) j := by
  classical
  simp only [Matrix.mulVec, dotProduct, repeatedBlock]
  rw [Fintype.sum_prod_type]
  simp

/-- The rank of `n` repeated diagonal blocks is `n` times the rank of the block. -/
theorem repeatedBlock_rank {k : Type*} [Field k] {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) k) : (repeatedBlock (n := n) A).rank = n * A.rank := by
  classical
  let RA := LinearMap.range A.mulVecLin
  let B := repeatedBlock (n := n) A
  let RB := LinearMap.range B.mulVecLin
  let e : RB ≃ₗ[k] (Fin n → RA) :=
    { toFun := fun y l =>
        ⟨fun j => y.1 (j, l), by
          obtain ⟨x, hx⟩ := y.2
          refine ⟨fun i => x (i, l), ?_⟩
          funext j
          have he := congrFun hx (j, l)
          simpa only [B, Matrix.mulVecLin_apply, repeatedBlock_mulVec] using he⟩
      map_add' := by intro x y; ext; rfl
      map_smul' := by intro c x; ext; rfl
      invFun := fun f =>
        ⟨fun jl => (f jl.2).1 jl.1, by
          choose x hx using fun l => (f l).2
          refine ⟨fun il => x il.2 il.1, ?_⟩
          funext jl
          rw [show jl = (jl.1, jl.2) from (Prod.eta jl).symm]
          simpa only [B, Matrix.mulVecLin_apply, repeatedBlock_mulVec] using
            congrFun (hx jl.2) jl.1⟩
      left_inv := by intro y; ext; rfl
      right_inv := by intro f; ext; rfl }
  rw [Matrix.rank]
  change Module.finrank k RB = n * Module.finrank k RA
  calc
    Module.finrank k RB = Module.finrank k (Fin n → RA) := e.finrank_eq
    _ = ∑ _ : Fin n, Module.finrank k RA := Module.finrank_pi_fintype k
    _ = n * Module.finrank k RA := by simp

/-- The singleton flattening of the mode-one contraction is the repeated block
matrix `Fᵀ`, up to the row-major product reindexing. -/
theorem matMulContractOne_flatten_rank {k : Type*} [Field k] (n : ℕ)
    (F : Matrix (Fin n) (Fin n) k) :
    (singletonFlatten (matMulContractOne n F)).rank = n * F.rank := by
  let ep : Fin n × Fin n ≃ Fin (n * n) := finProdFinEquiv
  let ec : Fin n × Fin n ≃ Fin (n * n) := (Equiv.prodComm (Fin n) (Fin n)).trans ep
  have hmatrix : singletonFlatten (matMulContractOne n F) =
      (repeatedBlock (n := n) (Matrix.transpose F)).reindex ep ec := by
    ext y z
    change matMulContractOne n F 0 y z = _
    rw [Matrix.reindex_apply, matMulContractOne_apply]
    simp [repeatedBlock, ep, ec]
  rw [hmatrix, Matrix.rank_reindex, repeatedBlock_rank, Matrix.rank_transpose]

/-- The exact tensor rank of the mode-one contraction is `n * F.rank`. -/
theorem matMulContractOne_rank {k : Type*} [Field k] (n : ℕ)
    (F : Matrix (Fin n) (Fin n) k) : rank (matMulContractOne n F) = n * F.rank := by
  apply le_antisymm (matMulContractOne_rank_le n F)
  rw [← matMulContractOne_flatten_rank]
  exact singletonFlatten_rank_le _

/-- Indices on which a packed matrix functional has nonzero coefficient. -/
noncomputable def functionalSupport {k : Type*} [CommSemiring k] {n s : ℕ}
    (F : Matrix (Fin n) (Fin n) k) (u : Fin s → Fin (n * n) → k) : Finset (Fin s) :=
  @Finset.filter (Fin s) (fun t => (∑ x, packedFunctional F x * u t x) ≠ 0)
    (fun _ => Classical.propDecidable _) Finset.univ

/-- Membership in `functionalSupport` is exactly nonvanishing of the coefficient. -/
theorem mem_functionalSupport_iff {k : Type*} [CommSemiring k] {n s : ℕ}
    (F : Matrix (Fin n) (Fin n) k) (u : Fin s → Fin (n * n) → k) (t : Fin s) :
    t ∈ functionalSupport F u ↔ (∑ x, packedFunctional F x * u t x) ≠ 0 := by
  classical
  simp [functionalSupport]

/-- In an exact decomposition, mode-one terms whose packed functional
coefficient is nonzero themselves decompose the mode-one contraction. -/
theorem rankLE_matMulContractOne_support {k : Type*} [CommSemiring k] {n s : ℕ}
    (u v w : Fin s → Fin (n * n) → k)
    (hdecomp : matMulTensor k n n n = fun x y z => ∑ t, u t x * v t y * w t z)
    (F : Matrix (Fin n) (Fin n) k) :
    RankLE (matMulContractOne n F) (functionalSupport F u).card := by
  classical
  let c : Fin s → k := fun t => ∑ x, packedFunctional F x * u t x
  let active := functionalSupport F u
  let e := active.equivFin.symm
  refine ⟨fun q _ => c (e q), fun q => v (e q), fun q => w (e q), ?_⟩
  funext q y z
  have hq : q = (0 : Fin 1) := Subsingleton.elim _ _
  subst q
  change contract₁ (fun _ x => packedFunctional F x) (matMulTensor k n n n) 0 y z = _
  rw [hdecomp]
  simp only [contract₁, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hrearr :
      (∑ t, ∑ x, packedFunctional F x * (u t x * v t y * w t z)) =
        ∑ t, c t * v t y * w t z := by
    apply Finset.sum_congr rfl
    intro t _
    simp only [c, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hrearr]
  calc
    (∑ t, c t * v t y * w t z) = ∑ t ∈ active, c t * v t y * w t z := by
      symm
      apply Finset.sum_subset (Finset.subset_univ active)
      intro t _ ht
      have hct : c t = 0 := by
        apply not_ne_iff.mp
        intro hne
        exact ht (by simp [active, functionalSupport, c, hne])
      simp [hct]
    _ = ∑ t : active, c t * v t y * w t z := by
      apply Finset.sum_subtype active
      intro t
      rfl
    _ = ∑ q : Fin active.card, c (e q) * v (e q) y * w (e q) z := by
      exact (Equiv.sum_comp e (fun t : active => c t * v t y * w t z)).symm

/-- Indices annihilated by a packed functional; this is the multiplicity-aware
complement of `functionalSupport`. -/
noncomputable def functionalInactive {k : Type*} [CommSemiring k] {n s : ℕ}
    (F : Matrix (Fin n) (Fin n) k) (u : Fin s → Fin (n * n) → k) : Finset (Fin s) :=
  Finset.univ \ functionalSupport F u

/-- Active and inactive indices partition the exact decomposition index set. -/
theorem functionalSupport_card_add_inactive {k : Type*} [CommSemiring k] {n s : ℕ}
    (F : Matrix (Fin n) (Fin n) k) (u : Fin s → Fin (n * n) → k) :
    (functionalSupport F u).card + (functionalInactive F u).card = s := by
  classical
  rw [Nat.add_comm, functionalInactive, Finset.card_sdiff_add_card_eq_card]
  · simp
  · exact Finset.subset_univ _

/-- Every mode-one normal of rank `F.rank` meets at least `n * F.rank`
decomposition terms.  No minimality assumption is used. -/
theorem modeOne_mul_rank_le_card_functionalSupport {k : Type*} [Field k] {n s : ℕ}
    (u v w : Fin s → Fin (n * n) → k)
    (hdecomp : matMulTensor k n n n = fun x y z => ∑ t, u t x * v t y * w t z)
    (F : Matrix (Fin n) (Fin n) k) :
    n * F.rank ≤ (functionalSupport F u).card := by
  rw [← matMulContractOne_rank n F]
  exact rank_le_of_rankLE (rankLE_matMulContractOne_support u v w hdecomp F)

/-- Heavy-hyperplane form in mode one: required active multiplicity plus the
inactive multiplicity is at most the decomposition length. -/
theorem modeOne_heavy_hyperplane {k : Type*} [Field k] {n s : ℕ}
    (u v w : Fin s → Fin (n * n) → k)
    (hdecomp : matMulTensor k n n n = fun x y z => ∑ t, u t x * v t y * w t z)
    (F : Matrix (Fin n) (Fin n) k) :
    n * F.rank + (functionalInactive F u).card ≤ s := by
  have hs := modeOne_mul_rank_le_card_functionalSupport u v w hdecomp F
  have hp := functionalSupport_card_add_inactive F u
  omega

/-- Mode-two version of the contraction-support bound, obtained by genuine
cyclic symmetry of square matrix multiplication. -/
theorem modeTwo_mul_rank_le_card_functionalSupport {k : Type*} [Field k] {n s : ℕ}
    (u v w : Fin s → Fin (n * n) → k)
    (hdecomp : matMulTensor k n n n = fun x y z => ∑ t, u t x * v t y * w t z)
    (F : Matrix (Fin n) (Fin n) k) :
    n * F.rank ≤ (functionalSupport F v).card := by
  have hrot : matMulTensor k n n n = fun y z x => ∑ t, v t y * w t z * u t x := by
    rw [← cyc_matMulTensor k n n n]
    funext y z x
    have h := congrFun (congrFun (congrFun hdecomp x) y) z
    simp only [cyc_apply]
    rw [h]
    exact Finset.sum_congr rfl fun t _ => by ring
  exact modeOne_mul_rank_le_card_functionalSupport v w u hrot F

/-- Heavy-hyperplane form in mode two. -/
theorem modeTwo_heavy_hyperplane {k : Type*} [Field k] {n s : ℕ}
    (u v w : Fin s → Fin (n * n) → k)
    (hdecomp : matMulTensor k n n n = fun x y z => ∑ t, u t x * v t y * w t z)
    (F : Matrix (Fin n) (Fin n) k) :
    n * F.rank + (functionalInactive F v).card ≤ s := by
  have hs := modeTwo_mul_rank_le_card_functionalSupport u v w hdecomp F
  have hp := functionalSupport_card_add_inactive F v
  omega

/-- Mode-three version of the contraction-support bound. -/
theorem modeThree_mul_rank_le_card_functionalSupport {k : Type*} [Field k] {n s : ℕ}
    (u v w : Fin s → Fin (n * n) → k)
    (hdecomp : matMulTensor k n n n = fun x y z => ∑ t, u t x * v t y * w t z)
    (F : Matrix (Fin n) (Fin n) k) :
    n * F.rank ≤ (functionalSupport F w).card := by
  have hrot : matMulTensor k n n n = fun y z x => ∑ t, v t y * w t z * u t x := by
    rw [← cyc_matMulTensor k n n n]
    funext y z x
    have h := congrFun (congrFun (congrFun hdecomp x) y) z
    simp only [cyc_apply]
    rw [h]
    exact Finset.sum_congr rfl fun t _ => by ring
  exact modeTwo_mul_rank_le_card_functionalSupport v w u hrot F

/-- Heavy-hyperplane form in mode three. -/
theorem modeThree_heavy_hyperplane {k : Type*} [Field k] {n s : ℕ}
    (u v w : Fin s → Fin (n * n) → k)
    (hdecomp : matMulTensor k n n n = fun x y z => ∑ t, u t x * v t y * w t z)
    (F : Matrix (Fin n) (Fin n) k) :
    n * F.rank + (functionalInactive F w).card ≤ s := by
  have hs := modeThree_mul_rank_le_card_functionalSupport u v w hdecomp F
  have hp := functionalSupport_card_add_inactive F w
  omega

/-- If an exact `Fin r` triad decomposition has tensor rank exactly `r`, the
full triad family is linearly independent.  This does not assert independence
of any individual mode-factor family, and it includes the `r = 0` case. -/
theorem triad_linearIndependent_of_rank_eq {k : Type*} [Field k]
    {a b c r : ℕ} (T : Tensor k a b c)
    (u : Fin r → Fin a → k) (v : Fin r → Fin b → k) (w : Fin r → Fin c → k)
    (hdecomp : T = fun i j l => ∑ t, u t i * v t j * w t l)
    (hrank : rank T = r) :
    LinearIndependent k (fun t => triad (u t) (v t) (w t)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hzero i
  by_contra hgi
  have hgi' : g i ≠ 0 := hgi
  let others := Finset.univ.erase i
  let e := others.equivFin.symm
  have hshort : RankLE T others.card := by
    refine ⟨fun q x => (1 - g (e q) / g i) * u (e q) x,
      fun q => v (e q), fun q => w (e q), ?_⟩
    funext x y z
    have hz := congrFun (congrFun (congrFun hzero x) y) z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, triad] at hz
    rw [hdecomp]
    let term : Fin r → k := fun t => u t x * v t y * w t z
    have hz' : ∑ t, g t * term t = 0 := by simpa [term, mul_assoc] using hz
    calc
      (∑ t, term t) = term i + ∑ t ∈ others, term t := by
        rw [show others = Finset.univ.erase i from rfl]
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
        ac_rfl
      _ = ∑ t ∈ others, (1 - g t / g i) * term t := by
        have hz'' := hz'
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)] at hz''
        have hrel : g i * term i + ∑ t ∈ others, g t * term t = 0 := by
          rw [show others = Finset.univ.erase i from rfl]
          calc
            g i * term i + ∑ t ∈ Finset.univ.erase i, g t * term t =
                (∑ t ∈ Finset.univ.erase i, g t * term t) + g i * term i := by ac_rfl
            _ = 0 := hz''
        let weighted := ∑ t ∈ others, g t * term t
        have hsolve : term i = -weighted / g i := by
          apply (eq_div_iff hgi').2
          change term i * g i = -weighted
          change g i * term i + weighted = 0 at hrel
          calc
            term i * g i = g i * term i := mul_comm _ _
            _ = -weighted := eq_neg_of_add_eq_zero_left hrel
        rw [hsolve]
        simp_rw [sub_mul, one_mul]
        rw [Finset.sum_sub_distrib]
        have hweighted : ∑ t ∈ others, g t / g i * term t = weighted / g i := by
          calc
            (∑ t ∈ others, g t / g i * term t) =
                ∑ t ∈ others, (g t * term t) / g i := by
              apply Finset.sum_congr rfl
              intro t _
              ring
            _ = weighted / g i := by
              simp [weighted, div_eq_mul_inv, Finset.sum_mul]
        rw [hweighted]
        ring
      _ = ∑ t : others, (1 - g t / g i) * term t := by
        apply Finset.sum_subtype others
        intro t
        rfl
      _ = ∑ q : Fin others.card, (1 - g (e q) / g i) * term (e q) := by
        exact (Equiv.sum_comp e (fun t : others => (1 - g t / g i) * term t)).symm
      _ = ∑ q, ((1 - g (e q) / g i) * u (e q) x) * v (e q) y * w (e q) z := by
        apply Finset.sum_congr rfl
        intro q _
        simp only [term]
        ring
  have hrle : r ≤ others.card := by
    calc
      r = rank T := hrank.symm
      _ ≤ others.card := rank_le_of_rankLE hshort
  have hcard : others.card = r - 1 := by simp [others]
  have hil := i.isLt
  have hrpos : 0 < r := by omega
  omega

/-- Satisfiability regression for the generic exact-decomposition premise:
the canonical schoolbook decomposition of `1 × 1` multiplication has one
term and all quantified coordinate types are nonempty. -/
example : ∃ u v w : Fin 1 → Fin 1 → ℚ,
    matMulTensor ℚ 1 1 1 = fun x y z => ∑ t, u t x * v t y * w t z := by
  obtain ⟨u, v, w, hdecomp⟩ := rankLE_matMulTensor ℚ 1 1 1
  exact ⟨u, v, w, hdecomp⟩

/-- Satisfiability regression for triad independence: a concrete nonzero
rank-one tensor jointly satisfies the exact decomposition and rank premises. -/
example : ∃ (T : Tensor ℚ 1 1 1) (u v w : Fin 1 → Fin 1 → ℚ),
    T = (fun i j l => ∑ t, u t i * v t j * w t l) ∧
      rank T = 1 ∧ LinearIndependent ℚ (fun t => triad (u t) (v t) (w t)) := by
  let T : Tensor ℚ 1 1 1 := fun _ _ _ => 1
  let u : Fin 1 → Fin 1 → ℚ := fun _ _ => 1
  let v : Fin 1 → Fin 1 → ℚ := fun _ _ => 1
  let w : Fin 1 → Fin 1 → ℚ := fun _ _ => 1
  have hdecomp : T = fun i j l => ∑ t, u t i * v t j * w t l := by
    funext i j l
    simp [T, u, v, w]
  have hle : rank T ≤ 1 := rank_le_of_rankLE ⟨u, v, w, hdecomp⟩
  have hne : T ≠ 0 := by
    intro hzero
    have hentry := congrFun (congrFun (congrFun hzero 0) 0) 0
    simp [T] at hentry
  have hrank : rank T = 1 := by
    have hrank_ne : rank T ≠ 0 := fun hrank_zero => hne (rank_eq_zero_iff.mp hrank_zero)
    omega
  exact ⟨T, u, v, w, hdecomp, hrank,
    triad_linearIndependent_of_rank_eq T u v w hdecomp hrank⟩

/-- The mode-two identity normal for `2 × 2` multiplication meets at least
four terms in every exact decomposition. -/
theorem four_le_card_modeTwo_identity_functionalSupport {k : Type*} [Field k] {s : ℕ}
    (u v w : Fin s → Fin 4 → k)
    (hdecomp : matMulTensor k 2 2 2 = fun x y z => ∑ t, u t x * v t y * w t z) :
    4 ≤ (functionalSupport (1 : Matrix (Fin 2) (Fin 2) k) v).card := by
  simpa [Matrix.rank_one] using
    (modeTwo_mul_rank_le_card_functionalSupport u v w hdecomp (1 : Matrix (Fin 2) (Fin 2) k))

/-- The mode-three identity normal for `3 × 3` multiplication meets at least
nine terms in every exact decomposition. -/
theorem nine_le_card_modeThree_identity_functionalSupport {k : Type*} [Field k] {s : ℕ}
    (u v w : Fin s → Fin 9 → k)
    (hdecomp : matMulTensor k 3 3 3 = fun x y z => ∑ t, u t x * v t y * w t z) :
    9 ≤ (functionalSupport (1 : Matrix (Fin 3) (Fin 3) k) w).card := by
  simpa [Matrix.rank_one] using
    (modeThree_mul_rank_le_card_functionalSupport u v w hdecomp
      (1 : Matrix (Fin 3) (Fin 3) k))

/-- The canonical eight-term schoolbook decomposition jointly witnesses the
premise and conclusion of the `2 × 2` mode-two numerical bound. -/
example : ∃ u v w : Fin 8 → Fin 4 → ℚ,
    matMulTensor ℚ 2 2 2 = (fun x y z => ∑ t, u t x * v t y * w t z) ∧
      4 ≤ (functionalSupport (1 : Matrix (Fin 2) (Fin 2) ℚ) v).card := by
  obtain ⟨u, v, w, hdecomp⟩ := rankLE_matMulTensor ℚ 2 2 2
  exact ⟨u, v, w, hdecomp,
    four_le_card_modeTwo_identity_functionalSupport u v w hdecomp⟩

/-- The canonical twenty-seven-term schoolbook decomposition jointly witnesses
the premise and conclusion of the `3 × 3` mode-three numerical bound. -/
example : ∃ u v w : Fin 27 → Fin 9 → ℚ,
    matMulTensor ℚ 3 3 3 = (fun x y z => ∑ t, u t x * v t y * w t z) ∧
      9 ≤ (functionalSupport (1 : Matrix (Fin 3) (Fin 3) ℚ) w).card := by
  obtain ⟨u, v, w, hdecomp⟩ := rankLE_matMulTensor ℚ 3 3 3
  exact ⟨u, v, w, hdecomp,
    nine_le_card_modeThree_identity_functionalSupport u v w hdecomp⟩

-- Ground checks for the two noncomputable support-set definitions.
example : functionalSupport (1 : Matrix (Fin 0) (Fin 0) ℚ)
    (fun _t : Fin 0 => fun _x : Fin 0 => (0 : ℚ)) = ∅ := by
  simp [functionalSupport]

example : functionalInactive (1 : Matrix (Fin 0) (Fin 0) ℚ)
    (fun _t : Fin 0 => fun _x : Fin 0 => (0 : ℚ)) = ∅ := by
  simp [functionalInactive, functionalSupport]

/-- Nonempty support regression: the first of two terms is active and the
second is inactive for the unique `1 × 1` identity functional. -/
example :
    let u : Fin 2 → Fin 1 → ℚ := fun t _ => if t = 0 then 1 else 0
    functionalSupport !![(1 : ℚ)] u = {0} ∧
      functionalInactive !![(1 : ℚ)] u = {1} := by
  dsimp
  constructor <;> ext t <;>
    fin_cases t <;>
      simp [functionalSupport, functionalInactive, packedFunctional]


#check @packedFunctional
#check @singletonFlatten
#check @singletonFlatten_triad
#check @singletonFlatten_rank_le
#check @matMulContractOne
#check @matMulContractOne_apply
#check @exists_outer_decomposition
#check @matMulContractOne_rank_le
#check @matMulContractOne_flatten_rank
#check @matMulContractOne_rank
#check @repeatedBlock
#check @repeatedBlock_mulVec
#check @repeatedBlock_rank
#check @functionalSupport
#check @mem_functionalSupport_iff
#check @rankLE_matMulContractOne_support
#check @functionalInactive
#check @functionalSupport_card_add_inactive
#check @modeOne_mul_rank_le_card_functionalSupport
#check @modeOne_heavy_hyperplane
#check @modeTwo_mul_rank_le_card_functionalSupport
#check @modeTwo_heavy_hyperplane
#check @modeThree_mul_rank_le_card_functionalSupport
#check @modeThree_heavy_hyperplane
#check @triad_linearIndependent_of_rank_eq
#check @four_le_card_modeTwo_identity_functionalSupport
#check @nine_le_card_modeThree_identity_functionalSupport

#print axioms matMulContractOne_rank
#print axioms mem_functionalSupport_iff
#print axioms rankLE_matMulContractOne_support
#print axioms modeOne_mul_rank_le_card_functionalSupport
#print axioms modeTwo_mul_rank_le_card_functionalSupport
#print axioms modeThree_mul_rank_le_card_functionalSupport
#print axioms modeOne_heavy_hyperplane
#print axioms modeTwo_heavy_hyperplane
#print axioms modeThree_heavy_hyperplane
#print axioms triad_linearIndependent_of_rank_eq
#print axioms four_le_card_modeTwo_identity_functionalSupport
#print axioms nine_le_card_modeThree_identity_functionalSupport

end BilinearComplexity
