import Mathlib.Data.ZMod.Basic
import BilinearComplexity.Peeling
import BilinearComplexity.RankCalculus

set_option autoImplicit false

namespace BilinearComplexity

/-- An ordered rank-one presentation with exactly one stored triad in each slot of `Fin r`. -/
structure Scheme (k : Type*) (a b c r : ℕ) where
  /-- The rank-one factor triple stored in an operationally significant slot. -/
  term : Fin r → TriadData k a b c

namespace Scheme

variable {k K : Type*} {a b c r : ℕ}

/-- The tensor represented by an ordered scheme is the pointwise sum of its evaluated triads. -/
def sumTensor [CommSemiring k] (S : Scheme k a b c r) : Tensor k a b c :=
  fun i j l => ∑ s, (S.term s).eval i j l

/-- A stored term is nonzero when its evaluated rank-one tensor is nonzero. -/
def TermNonzero [CommSemiring k] (S : Scheme k a b c r) (s : Fin r) : Prop :=
  (S.term s).eval ≠ 0

/-- A scheme is valid for a tensor when its represented sum is exact and its evaluated terms
are nonzero and pairwise distinct. -/
def Valid [CommSemiring k] (T : Tensor k a b c) (S : Scheme k a b c r) : Prop :=
  S.sumTensor = T ∧ (∀ s, S.TermNonzero s) ∧
    Function.Injective (fun s => (S.term s).eval)

/-- Every ordered scheme is a rank-at-most witness for the tensor it represents. -/
theorem rankLE_sumTensor [CommSemiring k] (S : Scheme k a b c r) :
    RankLE S.sumTensor r := by
  refine ⟨fun s => (S.term s).1, fun s => (S.term s).2.1,
    fun s => (S.term s).2.2, ?_⟩
  rfl

/-- A valid length-`r` presentation proves a rank-at-most-`r` statement, not minimal rank. -/
theorem Valid.rankLE [CommSemiring k] {T : Tensor k a b c}
    {S : Scheme k a b c r} (hS : S.Valid T) : RankLE T r := by
  rw [← hS.1]
  exact S.rankLE_sumTensor

/-- Pointwise equality of evaluated terms implies equality of represented tensors. -/
theorem sumTensor_eq_of_eval_eq [CommSemiring k] {S R : Scheme k a b c r}
    (h : ∀ s, (S.term s).eval = (R.term s).eval) : S.sumTensor = R.sumTensor := by
  funext i j l
  apply Finset.sum_congr rfl
  intro s _hs
  exact congrFun (congrFun (congrFun (h s) i) j) l

/-- Relabeling ordered slots by a permutation retains the source term at its image slot. -/
def permute (S : Scheme k a b c r) (e : Fin r ≃ Fin r) : Scheme k a b c r :=
  ⟨fun s => S.term (e.symm s)⟩

/-- The term in slot `e s` after a permutation is the old term in slot `s`. -/
@[simp] theorem permute_term_apply (S : Scheme k a b c r) (e : Fin r ≃ Fin r)
    (s : Fin r) : (S.permute e).term (e s) = S.term s := by
  simp only [permute, Equiv.symm_apply_apply]

/-- Permuting ordered slots preserves the represented tensor. -/
theorem sumTensor_permute [CommSemiring k] (S : Scheme k a b c r)
    (e : Fin r ≃ Fin r) : (S.permute e).sumTensor = S.sumTensor := by
  funext i j l
  simp only [sumTensor]
  rw [← Equiv.sum_comp e]
  simp only [permute, Equiv.symm_apply_apply]

/-- Permuting ordered slots preserves the stronger validity predicate. -/
theorem Valid.permute [CommSemiring k] {T : Tensor k a b c}
    {S : Scheme k a b c r} (hS : S.Valid T) (e : Fin r ≃ Fin r) :
    (S.permute e).Valid T := by
  refine ⟨(sumTensor_permute S e).trans hS.1, ?_, ?_⟩
  · intro s
    exact hS.2.1 (e.symm s)
  · intro s t hst
    have hsource : e.symm s = e.symm t := hS.2.2 hst
    exact e.symm.injective hsource

end Scheme

variable {k K : Type*} {a b c r : ℕ}

/-- The row-major equivalence between matrix entries and flattened coordinates. -/
def matrixIndexEquiv (m n : ℕ) : Fin m × Fin n ≃ Fin (m * n) :=
  finProdFinEquiv

/-- Row-major flattening and reshaping form an explicit equivalence between matrices and vectors. -/
def matrixVectorEquiv (k : Type*) (m n : ℕ) :
    Matrix (Fin m) (Fin n) k ≃ (Fin (m * n) → k) where
  toFun M x := M (matrixIndexEquiv m n |>.symm x).1
    (matrixIndexEquiv m n |>.symm x).2
  invFun u i j := u (matrixIndexEquiv m n (i, j))
  left_inv M := by
    funext i j
    simp only [matrixIndexEquiv, Equiv.symm_apply_apply]
  right_inv u := by
    funext x
    change u (finProdFinEquiv (finProdFinEquiv.symm x)) = u x
    rw [Equiv.apply_symm_apply]

/-- Flatten a matrix in row-major order. -/
def flattenMatrix (M : Matrix (Fin a) (Fin b) k) : Fin (a * b) → k :=
  matrixVectorEquiv k a b M

/-- Reshape a row-major vector into a matrix. -/
def reshapeVector (u : Fin (a * b) → k) : Matrix (Fin a) (Fin b) k :=
  (matrixVectorEquiv k a b).symm u

/-- Read a flattened matrix vector at row `i` and column `j`. -/
def matrixEntry (u : Fin (a * b) → k) (i : Fin a) (j : Fin b) : k :=
  u (matrixIndexEquiv a b (i, j))

/-- Flattening followed by matrix entry evaluation recovers the original entry. -/
@[simp] theorem flattenMatrix_entry (M : Matrix (Fin a) (Fin b) k)
    (i : Fin a) (j : Fin b) : matrixEntry (flattenMatrix M) i j = M i j := by
  change M (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1
    (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2 = M i j
  rw [Equiv.symm_apply_apply]

/-- Reshaping a vector exposes exactly its row-major matrix entries. -/
@[simp] theorem reshapeVector_apply (u : Fin (a * b) → k) (i : Fin a) (j : Fin b) :
    reshapeVector u i j = matrixEntry u i j := rfl

/-- The flattened elementary matrix `E(i,j)`. -/
def matrixUnit (k : Type*) [Zero k] [One k] (i : Fin a) (j : Fin b) :
    Fin (a * b) → k :=
  fun x => if x = matrixIndexEquiv a b (i, j) then 1 else 0

/-- The coordinate of a flattened elementary matrix is the corresponding Kronecker delta. -/
@[simp] theorem matrixEntry_matrixUnit [Semiring k] (i i' : Fin a) (j j' : Fin b) :
    matrixEntry (matrixUnit k i j) i' j' = if i' = i ∧ j' = j then 1 else 0 := by
  simp only [matrixEntry, matrixUnit, Equiv.apply_eq_iff_eq, Prod.mk.injEq]

/-- The standard elementary-matrix sum for rectangular matrix multiplication. -/
def matrixMultiplicationSum (k : Type*) [CommSemiring k] (n₁ n₂ n₃ : ℕ) :
    Tensor k (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) :=
  fun x y z => ∑ i : Fin n₁, ∑ j : Fin n₂, ∑ l : Fin n₃,
    matrixUnit k i j x * matrixUnit k j l y * matrixUnit k l i z

set_option maxRecDepth 2048 in
/-- The elementary-matrix sum agrees exactly with the repository's row-major matrix multiplication tensor. -/
theorem matrixMultiplicationSum_eq_matMulTensor (k : Type*) [CommSemiring k]
    (n₁ n₂ n₃ : ℕ) :
    matrixMultiplicationSum k n₁ n₂ n₃ = matMulTensor k n₁ n₂ n₃ := by
  funext x y z
  rcases matrixIndexEquiv n₁ n₂ |>.surjective x with ⟨⟨i, j⟩, rfl⟩
  rcases matrixIndexEquiv n₂ n₃ |>.surjective y with ⟨⟨j', l⟩, rfl⟩
  rcases matrixIndexEquiv n₃ n₁ |>.surjective z with ⟨⟨l', i'⟩, rfl⟩
  change (∑ p : Fin n₁, ∑ q : Fin n₂, ∑ t : Fin n₃,
      matrixEntry (matrixUnit k p q) i j *
        matrixEntry (matrixUnit k q t) j' l *
        matrixEntry (matrixUnit k t p) l' i') = _
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · rw [Finset.sum_eq_single l]
      · simp only [matrixEntry_matrixUnit, and_self, ite_true, one_mul, and_true]
        rw [matMulTensor_apply]
        simp only [matrixIndexEquiv, Equiv.symm_apply_apply]
        by_cases hj : j = j'
        · subst j'
          by_cases hl : l = l'
          · subst l'
            by_cases hi : i = i'
            · subst i'
              simp only [ite_true, and_self, mul_one]
            · have hir : i' ≠ i := fun h => hi h.symm
              simp only [hir, ite_false, and_false, mul_zero]
          · have hlr : l' ≠ l := fun h => hl h.symm
            simp only [hl, hlr, ite_false, false_and, and_false, mul_zero]
        · have hjr : j' ≠ j := fun h => hj h.symm
          simp only [hj, hjr, ite_false, false_and, zero_mul]
      · intro t _ht htl
        simp only [matrixEntry_matrixUnit]
        have hlt : l ≠ t := fun h => htl h.symm
        simp only [hlt, and_false, ite_false, mul_zero, zero_mul]
      · intro hnot
        exact (hnot (Finset.mem_univ l)).elim
    · intro q _hq hqj
      simp only [matrixEntry_matrixUnit]
      have hjq : j ≠ q := fun h => hqj h.symm
      simp only [hjq, and_false, ite_false, zero_mul, Finset.sum_const_zero]
    · intro hnot
      exact (hnot (Finset.mem_univ j)).elim
  · intro p _hp hpi
    simp only [matrixEntry_matrixUnit]
    have hip : i ≠ p := fun h => hpi h.symm
    simp only [hip, false_and, ite_false, zero_mul, Finset.sum_const_zero]
  · intro hnot
    exact (hnot (Finset.mem_univ i)).elim

namespace Scheme

variable {k K : Type*} {n₁ n₂ n₃ r : ℕ}

/-- Positivity of all three vertex dimensions for replay contexts in which every Brent
quantifier must have a concrete coordinate. -/
structure PositiveDimensions (n₁ n₂ n₃ : ℕ) : Prop where
  /-- The first vertex space is nonempty. -/
  first : 0 < n₁
  /-- The second vertex space is nonempty. -/
  second : 0 < n₂
  /-- The third vertex space is nonempty. -/
  third : 0 < n₃

/-- The concrete `4 × 4 × 4` replay dimensions are jointly positive. -/
example : PositiveDimensions 4 4 4 := ⟨by decide, by decide, by decide⟩

/-- The exact rectangular shape of an ordered matrix-multiplication presentation. -/
abbrev MatrixScheme (k : Type*) (n₁ n₂ n₃ r : ℕ) :=
  Scheme k (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) r

/-- A rectangular ordered scheme satisfies the Brent equations in the binding convention
`U[i,j] V[j',l] W[l',i']`. -/
def Brent [CommSemiring k] (S : MatrixScheme k n₁ n₂ n₃ r) : Prop :=
  ∀ i : Fin n₁, ∀ j j' : Fin n₂, ∀ l l' : Fin n₃, ∀ i' : Fin n₁,
    (∑ s, matrixEntry (S.term s).1 i j *
      matrixEntry (S.term s).2.1 j' l *
      matrixEntry (S.term s).2.2 l' i') =
    (if j = j' then 1 else 0) *
      (if l = l' then 1 else 0) *
      (if i = i' then 1 else 0)

/-- The product of the three coordinate deltas is the conjunction used by `matMulTensor`. -/
theorem brentDelta_eq_condition [CommSemiring k]
    (i i' : Fin n₁) (j j' : Fin n₂) (l l' : Fin n₃) :
    (if j = j' then 1 else 0 : k) *
        (if l = l' then 1 else 0) * (if i = i' then 1 else 0) =
      if j = j' ∧ l = l' ∧ i' = i then 1 else 0 := by
  by_cases hj : j = j'
  · subst j'
    by_cases hl : l = l'
    · subst l'
      by_cases hi : i = i'
      · subst i'
        simp only [ite_true, mul_one, true_and]
      · have hir : i' ≠ i := fun h => hi h.symm
        simp only [ite_true, hi, ite_false, mul_zero, hir, and_false]
    · simp only [ite_true, hl, ite_false, mul_zero, zero_mul, true_and, false_and]
  · simp only [hj, ite_false, zero_mul, false_and]

/-- The coordinate Brent equations are equivalent to equality with the exact row-major
matrix multiplication tensor. -/
theorem brent_iff_sumTensor_eq_matMulTensor [CommSemiring k]
    (S : MatrixScheme k n₁ n₂ n₃ r) :
    S.Brent ↔ S.sumTensor = matMulTensor k n₁ n₂ n₃ := by
  constructor
  · intro h
    funext x y z
    rcases matrixIndexEquiv n₁ n₂ |>.surjective x with ⟨⟨i, j⟩, rfl⟩
    rcases matrixIndexEquiv n₂ n₃ |>.surjective y with ⟨⟨j', l⟩, rfl⟩
    rcases matrixIndexEquiv n₃ n₁ |>.surjective z with ⟨⟨l', i'⟩, rfl⟩
    change (∑ s, matrixEntry (S.term s).1 i j *
      matrixEntry (S.term s).2.1 j' l *
      matrixEntry (S.term s).2.2 l' i') = _
    rw [h i j j' l l' i', brentDelta_eq_condition]
    simp only [matMulTensor_apply, matrixIndexEquiv, Equiv.symm_apply_apply]
  · intro h i j j' l l' i'
    have hentry := congrFun (congrFun (congrFun h
      (matrixIndexEquiv n₁ n₂ (i, j)))
      (matrixIndexEquiv n₂ n₃ (j', l)))
      (matrixIndexEquiv n₃ n₁ (l', i'))
    simp only [sumTensor, TriadData.eval, triad] at hentry
    calc
      (∑ s, matrixEntry (S.term s).1 i j *
        matrixEntry (S.term s).2.1 j' l *
        matrixEntry (S.term s).2.2 l' i') =
          matMulTensor k n₁ n₂ n₃ (matrixIndexEquiv n₁ n₂ (i, j))
            (matrixIndexEquiv n₂ n₃ (j', l))
            (matrixIndexEquiv n₃ n₁ (l', i')) := hentry
      _ = if j = j' ∧ l = l' ∧ i' = i then 1 else 0 := by
        simp only [matMulTensor_apply, matrixIndexEquiv, Equiv.symm_apply_apply]
      _ = (if j = j' then 1 else 0) * (if l = l' then 1 else 0) *
          (if i = i' then 1 else 0) :=
        (brentDelta_eq_condition i i' j j' l l').symm

/-- Brent equality is equivalently equality with the explicit sum of elementary matrix triads. -/
theorem brent_iff_sumTensor_eq_matrixMultiplicationSum [CommSemiring k]
    (S : MatrixScheme k n₁ n₂ n₃ r) :
    S.Brent ↔ S.sumTensor = matrixMultiplicationSum k n₁ n₂ n₃ := by
  rw [matrixMultiplicationSum_eq_matMulTensor]
  exact brent_iff_sumTensor_eq_matMulTensor S

/-- Any length-`r` Brent presentation supplies the corresponding `RankLE r` witness. -/
theorem Brent.rankLE [CommSemiring k] {S : MatrixScheme k n₁ n₂ n₃ r}
    (hS : S.Brent) : RankLE (matMulTensor k n₁ n₂ n₃) r := by
  rw [← (brent_iff_sumTensor_eq_matMulTensor S).mp hS]
  exact S.rankLE_sumTensor

/-- Apply a unital semiring map to every coordinate of a tensor. -/
def mapTensor [CommSemiring k] [CommSemiring K] (f : k →+* K)
    (T : Tensor k a b c) : Tensor K a b c :=
  fun i j l => f (T i j l)

/-- Apply a unital semiring map to every factor coordinate of an ordered scheme. -/
def map [CommSemiring k] [CommSemiring K] (f : k →+* K)
    (S : Scheme k a b c r) : Scheme K a b c r :=
  ⟨fun s =>
    (fun i => f ((S.term s).1 i),
      fun j => f ((S.term s).2.1 j),
      fun l => f ((S.term s).2.2 l))⟩

/-- Evaluation of a mapped triad is coordinatewise scalar extension of its evaluation. -/
theorem eval_map [CommSemiring k] [CommSemiring K] (f : k →+* K)
    (S : Scheme k a b c r) (s : Fin r) :
    ((S.map f).term s).eval = mapTensor f (S.term s).eval := by
  funext i j l
  simp only [map, TriadData.eval, triad, mapTensor, map_mul]

/-- Scalar extension commutes with the represented finite tensor sum. -/
theorem sumTensor_map [CommSemiring k] [CommSemiring K] (f : k →+* K)
    (S : Scheme k a b c r) :
    (S.map f).sumTensor = mapTensor f S.sumTensor := by
  funext i j l
  change (∑ s, f ((S.term s).1 i) * f ((S.term s).2.1 j) *
    f ((S.term s).2.2 l)) = f (∑ s, (S.term s).1 i *
      (S.term s).2.1 j * (S.term s).2.2 l)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro s _hs
  simp only [map_mul]

/-- An injective scalar map induces an injective coordinatewise map on tensors. -/
theorem mapTensor_injective [CommSemiring k] [CommSemiring K] (f : k →+* K)
    (hf : Function.Injective f) : Function.Injective (mapTensor f :
      Tensor k a b c → Tensor K a b c) := by
  intro T U hTU
  funext i j l
  apply hf
  exact congrFun (congrFun (congrFun hTU i) j) l

/-- A replay-facing Brent witness records positive dimensions, a nontrivial coefficient
semiring, and the extensional coordinate equations. -/
def ReplayableBrent [CommSemiring k] [Nontrivial k]
    (S : MatrixScheme k n₁ n₂ n₃ r) : Prop :=
  PositiveDimensions n₁ n₂ n₃ ∧ S.Brent

/-- Every replay-facing Brent witness supplies the same rank-at-most conclusion. -/
theorem ReplayableBrent.rankLE [CommSemiring k] [Nontrivial k]
    {S : MatrixScheme k n₁ n₂ n₃ r}
    (hS : S.ReplayableBrent) : RankLE (matMulTensor k n₁ n₂ n₃) r :=
  hS.2.rankLE

/-- A unital semiring map preserves every Brent equation and hence the resulting
rank-at-most statement after scalar extension. -/
theorem Brent.map [CommSemiring k] [CommSemiring K] (f : k →+* K)
    {S : MatrixScheme k n₁ n₂ n₃ r} (hS : S.Brent) : (S.map f).Brent := by
  apply (brent_iff_sumTensor_eq_matMulTensor (S.map f)).mpr
  rw [sumTensor_map, (brent_iff_sumTensor_eq_matMulTensor S).mp hS]
  funext x y z
  simp only [mapTensor, matMulTensor]
  split_ifs <;> simp only [map_one, map_zero]

/-- The scalar extension of a Brent presentation gives a `RankLE` witness over the target semiring. -/
theorem Brent.map_rankLE [CommSemiring k] [CommSemiring K] (f : k →+* K)
    {S : MatrixScheme k n₁ n₂ n₃ r} (hS : S.Brent) :
    RankLE (matMulTensor K n₁ n₂ n₃) r :=
  (hS.map f).rankLE

/-- Scalar extension preserves replay-facing Brent data when both coefficient semirings are
nontrivial, including the explicit positive vertex-dimension guard. -/
theorem ReplayableBrent.map [CommSemiring k] [Nontrivial k]
    [CommSemiring K] [Nontrivial K] (f : k →+* K)
    {S : MatrixScheme k n₁ n₂ n₃ r} (hS : S.ReplayableBrent) :
    (S.map f).ReplayableBrent :=
  ⟨hS.1, hS.2.map f⟩

/-- Replay-facing scalar extension supplies the target rank-at-most conclusion, even when only
the source coefficient semiring needs the nontriviality required by replay data. -/
theorem ReplayableBrent.map_rankLE [CommSemiring k] [Nontrivial k] [CommSemiring K]
    (f : k →+* K) {S : MatrixScheme k n₁ n₂ n₃ r} (hS : S.ReplayableBrent) :
    RankLE (matMulTensor K n₁ n₂ n₃) r :=
  hS.2.map_rankLE f

/-- Strong validity is preserved under an injective scalar map; injectivity is needed
for both nonzero terms and distinct evaluated summands. -/
theorem Valid.map_of_injective [CommSemiring k] [CommSemiring K]
    (f : k →+* K) (hf : Function.Injective f) {T : Tensor k a b c}
    {S : Scheme k a b c r} (hS : S.Valid T) :
    (S.map f).Valid (mapTensor f T) := by
  have hmapInjective : Function.Injective
      (mapTensor f : Tensor k a b c → Tensor K a b c) :=
    mapTensor_injective f hf
  refine ⟨(sumTensor_map f S).trans (congrArg (mapTensor f) hS.1), ?_, ?_⟩
  · intro s hzero
    apply hS.2.1 s
    apply hmapInjective
    rw [← eval_map f S s, hzero]
    funext i j l
    simp only [mapTensor, Pi.zero_apply, map_zero]
  · intro s t hst
    apply hS.2.2
    apply hmapInjective
    simpa only [← eval_map f S] using hst

end Scheme

/-- The one-term scalar multiplication presentation jointly satisfies replay-facing Brent
and validity hypotheses with nonempty vertex dimensions. -/
example :
    let S : Scheme.MatrixScheme (ZMod 2) 1 1 1 1 :=
      ⟨fun _ => (fun _ => 1, fun _ => 1, fun _ => 1)⟩
    S.ReplayableBrent ∧ S.Valid (matMulTensor (ZMod 2) 1 1 1) := by
  let S : Scheme.MatrixScheme (ZMod 2) 1 1 1 1 :=
    ⟨fun _ => (fun _ => 1, fun _ => 1, fun _ => 1)⟩
  have hsum : S.sumTensor = matMulTensor (ZMod 2) 1 1 1 := by
    funext i j l
    rw [matMulTensor_apply, if_pos ⟨Subsingleton.elim _ _,
      Subsingleton.elim _ _, Subsingleton.elim _ _⟩]
    norm_num [S, Scheme.sumTensor, TriadData.eval, triad]
  have hbrent : S.Brent :=
    (Scheme.brent_iff_sumTensor_eq_matMulTensor S).mpr hsum
  refine ⟨⟨⟨by decide, by decide, by decide⟩, hbrent⟩, hsum, ?_, ?_⟩
  · intro s hzero
    have hentry := congrFun (congrFun (congrFun hzero 0) 0) 0
    norm_num [S, TriadData.eval, triad] at hentry
  · intro s t _hst
    exact Subsingleton.elim s t

#check @Scheme.brent_iff_sumTensor_eq_matMulTensor
#check @Scheme.brent_iff_sumTensor_eq_matrixMultiplicationSum
#check @Scheme.Brent.rankLE
#check @Scheme.sumTensor_map
#check @Scheme.Brent.map
#check @Scheme.Brent.map_rankLE
#check @Scheme.ReplayableBrent.map
#check @Scheme.ReplayableBrent.map_rankLE
#check @Scheme.Valid.map_of_injective

#print axioms Scheme.brent_iff_sumTensor_eq_matMulTensor
#print axioms Scheme.Brent.rankLE
#print axioms Scheme.sumTensor_map
#print axioms Scheme.Brent.map
#print axioms Scheme.ReplayableBrent.map
#print axioms Scheme.ReplayableBrent.map_rankLE
#print axioms Scheme.Valid.map_of_injective

end BilinearComplexity
