/-
  BilinearComplexity/BorderRankCompression — polynomial-closure preservation
  under coordinate pullbacks and factorwise linear contractions.
-/
import BilinearComplexity.BorderRank
import BilinearComplexity.MatMulMono
import BilinearComplexity.RankCalculus

set_option autoImplicit false

namespace BilinearComplexity

/-- The polynomial coordinate map induced by pulling a tensor back along one
function on each factor. -/
noncomputable def compPolynomialMap {k : Type*} [Field k]
    {a b c a' b' c' : ℕ} (f : Fin a → Fin a') (g : Fin b → Fin b')
    (e : Fin c → Fin c') :
    PolynomialClosure.Map k (EntryIndex a' b' c') (EntryIndex a b c) where
  coordinate ijl := MvPolynomial.X (f ijl.1, g ijl.2.1, e ijl.2.2)

/-- Evaluating the pullback polynomial map on tensor entries gives the entry
vector of the pulled-back tensor. -/
theorem compPolynomialMap_eval_entries {k : Type*} [Field k]
    {a b c a' b' c' : ℕ} (f : Fin a → Fin a') (g : Fin b → Fin b')
    (e : Fin c → Fin c') (T : Tensor k a' b' c') :
    (compPolynomialMap f g e).eval (entries T) =
      entries (fun i j l => T (f i) (g j) (e l)) := by
  funext ijl
  simp [compPolynomialMap, PolynomialClosure.Map.eval, entries]

/-- Polynomial-closure border rank does not increase under arbitrary
factorwise coordinate pullback; the index maps need not be injective. -/
theorem BorderRankLE.comp {k : Type*} [Field k]
    {a b c a' b' c' r : ℕ} {T : Tensor k a' b' c'}
    (hT : BorderRankLE T r) (f : Fin a → Fin a') (g : Fin b → Fin b')
    (e : Fin c → Fin c') :
    BorderRankLE (fun i j l => T (f i) (g j) (e l)) r := by
  let P := compPolynomialMap (k := k) f g e
  have hmap : Set.MapsTo P.eval (rankLocus k a' b' c' r) (rankLocus k a b c r) := by
    rintro x ⟨S, hS, rfl⟩
    refine ⟨fun i j l => S (f i) (g j) (e l), hS.comp f g e, ?_⟩
    exact compPolynomialMap_eval_entries f g e S
  have hclosure := P.mapsTo_closure hmap hT
  rw [compPolynomialMap_eval_entries] at hclosure
  exact hclosure

/-- The polynomial coordinate map for contraction on the first tensor factor. -/
noncomputable def contract₁PolynomialMap {k : Type*} [Field k]
    {a a' b c : ℕ} (M : Matrix (Fin a') (Fin a) k) :
    PolynomialClosure.Map k (EntryIndex a b c) (EntryIndex a' b c) where
  coordinate ijl := ∑ i, MvPolynomial.C (M ijl.1 i) *
    MvPolynomial.X (i, ijl.2.1, ijl.2.2)

/-- Evaluating the first-factor contraction polynomial map gives exactly the
entry vector of `contract₁`. -/
theorem contract₁PolynomialMap_eval_entries {k : Type*} [Field k]
    {a a' b c : ℕ} (M : Matrix (Fin a') (Fin a) k) (T : Tensor k a b c) :
    (contract₁PolynomialMap M).eval (entries T) = entries (contract₁ M T) := by
  funext ijl
  simp [contract₁PolynomialMap, PolynomialClosure.Map.eval, entries, contract₁]

/-- Polynomial-closure border rank does not increase under a linear map on the
first factor. -/
theorem BorderRankLE.contract₁ {k : Type*} [Field k]
    {a a' b c r : ℕ} {T : Tensor k a b c} (hT : BorderRankLE T r)
    (M : Matrix (Fin a') (Fin a) k) : BorderRankLE (contract₁ M T) r := by
  let P := contract₁PolynomialMap (b := b) (c := c) M
  have hmap : Set.MapsTo P.eval (rankLocus k a b c r) (rankLocus k a' b c r) := by
    rintro x ⟨S, hS, rfl⟩
    exact ⟨BilinearComplexity.contract₁ M S, hS.contract₁ M,
      contract₁PolynomialMap_eval_entries M S⟩
  have hclosure := P.mapsTo_closure hmap hT
  rw [contract₁PolynomialMap_eval_entries] at hclosure
  exact hclosure

/-- The polynomial coordinate map for contraction on the second tensor factor. -/
noncomputable def contract₂PolynomialMap {k : Type*} [Field k]
    {a b b' c : ℕ} (M : Matrix (Fin b') (Fin b) k) :
    PolynomialClosure.Map k (EntryIndex a b c) (EntryIndex a b' c) where
  coordinate ijl := ∑ j, MvPolynomial.C (M ijl.2.1 j) *
    MvPolynomial.X (ijl.1, j, ijl.2.2)

/-- Evaluating the second-factor contraction polynomial map gives exactly the
entry vector of `contract₂`. -/
theorem contract₂PolynomialMap_eval_entries {k : Type*} [Field k]
    {a b b' c : ℕ} (M : Matrix (Fin b') (Fin b) k) (T : Tensor k a b c) :
    (contract₂PolynomialMap M).eval (entries T) = entries (contract₂ M T) := by
  funext ijl
  simp [contract₂PolynomialMap, PolynomialClosure.Map.eval, entries, contract₂]

/-- Polynomial-closure border rank does not increase under a linear map on the
second factor. -/
theorem BorderRankLE.contract₂ {k : Type*} [Field k]
    {a b b' c r : ℕ} {T : Tensor k a b c} (hT : BorderRankLE T r)
    (M : Matrix (Fin b') (Fin b) k) : BorderRankLE (contract₂ M T) r := by
  let P := contract₂PolynomialMap (a := a) (c := c) M
  have hmap : Set.MapsTo P.eval (rankLocus k a b c r) (rankLocus k a b' c r) := by
    rintro x ⟨S, hS, rfl⟩
    exact ⟨BilinearComplexity.contract₂ M S, hS.contract₂ M,
      contract₂PolynomialMap_eval_entries M S⟩
  have hclosure := P.mapsTo_closure hmap hT
  rw [contract₂PolynomialMap_eval_entries] at hclosure
  exact hclosure

/-- The polynomial coordinate map for contraction on the third tensor factor. -/
noncomputable def contract₃PolynomialMap {k : Type*} [Field k]
    {a b c c' : ℕ} (M : Matrix (Fin c') (Fin c) k) :
    PolynomialClosure.Map k (EntryIndex a b c) (EntryIndex a b c') where
  coordinate ijl := ∑ l, MvPolynomial.C (M ijl.2.2 l) *
    MvPolynomial.X (ijl.1, ijl.2.1, l)

/-- Evaluating the third-factor contraction polynomial map gives exactly the
entry vector of `contract₃`. -/
theorem contract₃PolynomialMap_eval_entries {k : Type*} [Field k]
    {a b c c' : ℕ} (M : Matrix (Fin c') (Fin c) k) (T : Tensor k a b c) :
    (contract₃PolynomialMap M).eval (entries T) = entries (contract₃ M T) := by
  funext ijl
  simp [contract₃PolynomialMap, PolynomialClosure.Map.eval, entries, contract₃]

/-- Polynomial-closure border rank does not increase under a linear map on the
third factor. -/
theorem BorderRankLE.contract₃ {k : Type*} [Field k]
    {a b c c' r : ℕ} {T : Tensor k a b c} (hT : BorderRankLE T r)
    (M : Matrix (Fin c') (Fin c) k) : BorderRankLE (contract₃ M T) r := by
  let P := contract₃PolynomialMap (a := a) (b := b) M
  have hmap : Set.MapsTo P.eval (rankLocus k a b c r) (rankLocus k a b c' r) := by
    rintro x ⟨S, hS, rfl⟩
    exact ⟨BilinearComplexity.contract₃ M S, hS.contract₃ M,
      contract₃PolynomialMap_eval_entries M S⟩
  have hclosure := P.mapsTo_closure hmap hT
  rw [contract₃PolynomialMap_eval_entries] at hclosure
  exact hclosure

/-- Applying linear maps on all three factors, in sequence, preserves a
polynomial-closure border-rank upper bound. -/
theorem BorderRankLE.factorwise {k : Type*} [Field k]
    {a a' b b' c c' r : ℕ} {T : Tensor k a b c} (hT : BorderRankLE T r)
    (M₁ : Matrix (Fin a') (Fin a) k) (M₂ : Matrix (Fin b') (Fin b) k)
    (M₃ : Matrix (Fin c') (Fin c) k) :
    BorderRankLE (BilinearComplexity.contract₃ M₃
      (BilinearComplexity.contract₂ M₂ (BilinearComplexity.contract₁ M₁ T))) r :=
  ((hT.contract₁ M₁).contract₂ M₂).contract₃ M₃

#check @compPolynomialMap
#check @BorderRankLE.comp
#check @contract₁PolynomialMap
#check @BorderRankLE.contract₁
#check @BorderRankLE.contract₂
#check @BorderRankLE.contract₃
#check @BorderRankLE.factorwise

/-- Non-vacuity audit for every preservation adapter. A nonconstant
rank-one `2 × 2 × 2` tensor is pulled back to a proper `2 × 1 × 2`
subtensor and individually contracted by three nonzero rectangular matrices.
The factorwise audit instead uses three nonzero, nonidentity `2 × 2` matrices,
so its output remains in a genuine `2 × 2 × 2` rank-one locus. Explicit
coordinates show that neither transformation is annihilated. -/
example :
    let T : Tensor ℚ 2 2 2 := fun i j l =>
      ((i.val : ℚ) + 1) * ((j.val : ℚ) + 1) * ((l.val : ℚ) + 1)
    let f : Fin 2 → Fin 2 := fun i => if i = 0 then 1 else 0
    let g : Fin 1 → Fin 2 := fun _ => 1
    let e : Fin 2 → Fin 2 := id
    let M₁ : Matrix (Fin 1) (Fin 2) ℚ := fun _ i => if i = 0 then 1 else 2
    let M₂ : Matrix (Fin 1) (Fin 2) ℚ := fun _ j => if j = 0 then 1 else 3
    let M₃ : Matrix (Fin 1) (Fin 2) ℚ := fun _ l => if l = 0 then 2 else 1
    let N₁ : Matrix (Fin 2) (Fin 2) ℚ := fun i j =>
      if i = j then if i = 0 then 1 else 2 else 0
    let N₂ : Matrix (Fin 2) (Fin 2) ℚ := fun i j =>
      if i = j then if i = 0 then 2 else 1 else 0
    let N₃ : Matrix (Fin 2) (Fin 2) ℚ := fun i j =>
      if i = j then if i = 0 then 3 else 1 else 0
    BorderRankLE (fun i j l => T (f i) (g j) (e l)) 1 ∧
      BorderRankLE (BilinearComplexity.contract₁ M₁ T) 1 ∧
      BorderRankLE (BilinearComplexity.contract₂ M₂ T) 1 ∧
      BorderRankLE (BilinearComplexity.contract₃ M₃ T) 1 ∧
      BorderRankLE (BilinearComplexity.contract₃ N₃
        (BilinearComplexity.contract₂ N₂
          (BilinearComplexity.contract₁ N₁ T))) 1 ∧
      f 0 ≠ f 1 ∧
      (fun i j l => T (f i) (g j) (e l)) 0 0 0 = 4 ∧
      BilinearComplexity.contract₃ N₃
        (BilinearComplexity.contract₂ N₂
          (BilinearComplexity.contract₁ N₁ T)) 0 0 0 = 6 ∧
      M₁ ≠ 0 ∧ M₂ ≠ 0 ∧ M₃ ≠ 0 ∧
      N₁ ≠ 0 ∧ N₂ ≠ 0 ∧ N₃ ≠ 0 ∧ N₁ ≠ 1 ∧ N₂ ≠ 1 ∧ N₃ ≠ 1 := by
  dsimp
  let T : Tensor ℚ 2 2 2 := fun i j l =>
    ((i.val : ℚ) + 1) * ((j.val : ℚ) + 1) * ((l.val : ℚ) + 1)
  let f : Fin 2 → Fin 2 := fun i => if i = 0 then 1 else 0
  let g : Fin 1 → Fin 2 := fun _ => 1
  let e : Fin 2 → Fin 2 := id
  let M₁ : Matrix (Fin 1) (Fin 2) ℚ := fun _ i => if i = 0 then 1 else 2
  let M₂ : Matrix (Fin 1) (Fin 2) ℚ := fun _ j => if j = 0 then 1 else 3
  let M₃ : Matrix (Fin 1) (Fin 2) ℚ := fun _ l => if l = 0 then 2 else 1
  let N₁ : Matrix (Fin 2) (Fin 2) ℚ := fun i j =>
    if i = j then if i = 0 then 1 else 2 else 0
  let N₂ : Matrix (Fin 2) (Fin 2) ℚ := fun i j =>
    if i = j then if i = 0 then 2 else 1 else 0
  let N₃ : Matrix (Fin 2) (Fin 2) ℚ := fun i j =>
    if i = j then if i = 0 then 3 else 1 else 0
  let u : Fin 1 → Fin 2 → ℚ := fun _ i => (i.val : ℚ) + 1
  let v : Fin 1 → Fin 2 → ℚ := fun _ j => (j.val : ℚ) + 1
  let w : Fin 1 → Fin 2 → ℚ := fun _ l => (l.val : ℚ) + 1
  have hdecomp : T = fun i j l => ∑ s, u s i * v s j * w s l := by
    funext i j l
    simp [T, u, v, w]
  have hR : RankLE T 1 := by
    exact ⟨u, v, w, hdecomp⟩
  have hB : BorderRankLE T 1 := hR.borderRankLE
  have hComp : BorderRankLE (fun i j l => T (f i) (g j) (e l)) 1 :=
    hB.comp f g e
  have hContract₁ : BorderRankLE (BilinearComplexity.contract₁ M₁ T) 1 :=
    hB.contract₁ M₁
  have hContract₂ : BorderRankLE (BilinearComplexity.contract₂ M₂ T) 1 :=
    hB.contract₂ M₂
  have hContract₃ : BorderRankLE (BilinearComplexity.contract₃ M₃ T) 1 :=
    hB.contract₃ M₃
  have hFactorwise : BorderRankLE (BilinearComplexity.contract₃ N₃
      (BilinearComplexity.contract₂ N₂
        (BilinearComplexity.contract₁ N₁ T))) 1 :=
    hB.factorwise N₁ N₂ N₃
  have hf_nonconstant : f 0 ≠ f 1 := by
    norm_num [f]
  have hpullback_nonzero : (fun i j l => T (f i) (g j) (e l)) 0 0 0 = 4 := by
    norm_num [T, f, g, e]
  have hfactorwise_nonzero : BilinearComplexity.contract₃ N₃
      (BilinearComplexity.contract₂ N₂
        (BilinearComplexity.contract₁ N₁ T)) 0 0 0 = 6 := by
    norm_num [T, N₁, N₂, N₃, BilinearComplexity.contract₁,
      BilinearComplexity.contract₂, BilinearComplexity.contract₃, Fin.sum_univ_two]
  have hM₁ : M₁ ≠ 0 := by
    intro hzero
    have hentry := congrFun (congrFun hzero (0 : Fin 1)) (0 : Fin 2)
    norm_num [M₁] at hentry
  have hM₂ : M₂ ≠ 0 := by
    intro hzero
    have hentry := congrFun (congrFun hzero (0 : Fin 1)) (0 : Fin 2)
    norm_num [M₂] at hentry
  have hM₃ : M₃ ≠ 0 := by
    intro hzero
    have hentry := congrFun (congrFun hzero (0 : Fin 1)) (0 : Fin 2)
    norm_num [M₃] at hentry
  have hN₁_nonzero : N₁ ≠ 0 := by
    intro hzero
    have hentry := congrFun (congrFun hzero (0 : Fin 2)) (0 : Fin 2)
    norm_num [N₁] at hentry
  have hN₂_nonzero : N₂ ≠ 0 := by
    intro hzero
    have hentry := congrFun (congrFun hzero (0 : Fin 2)) (0 : Fin 2)
    norm_num [N₂] at hentry
  have hN₃_nonzero : N₃ ≠ 0 := by
    intro hzero
    have hentry := congrFun (congrFun hzero (0 : Fin 2)) (0 : Fin 2)
    norm_num [N₃] at hentry
  have hN₁ : N₁ ≠ 1 := by
    intro hone
    have hentry := congrFun (congrFun hone (1 : Fin 2)) (1 : Fin 2)
    norm_num [N₁] at hentry
  have hN₂ : N₂ ≠ 1 := by
    intro hone
    have hentry := congrFun (congrFun hone (0 : Fin 2)) (0 : Fin 2)
    norm_num [N₂] at hentry
  have hN₃ : N₃ ≠ 1 := by
    intro hone
    have hentry := congrFun (congrFun hone (0 : Fin 2)) (0 : Fin 2)
    norm_num [N₃] at hentry
  constructor
  · exact hComp
  constructor
  · exact hContract₁
  constructor
  · exact hContract₂
  constructor
  · exact hContract₃
  constructor
  · exact hFactorwise
  constructor
  · exact hf_nonconstant
  constructor
  · exact hpullback_nonzero
  constructor
  · exact hfactorwise_nonzero
  constructor
  · exact hM₁
  constructor
  · exact hM₂
  constructor
  · exact hM₃
  constructor
  · exact hN₁_nonzero
  constructor
  · exact hN₂_nonzero
  constructor
  · exact hN₃_nonzero
  constructor
  · exact hN₁
  constructor
  · exact hN₂
  · exact hN₃

#print axioms compPolynomialMap_eval_entries
#print axioms BorderRankLE.comp
#print axioms contract₁PolynomialMap_eval_entries
#print axioms BorderRankLE.contract₁
#print axioms contract₂PolynomialMap_eval_entries
#print axioms BorderRankLE.contract₂
#print axioms contract₃PolynomialMap_eval_entries
#print axioms BorderRankLE.contract₃
#print axioms BorderRankLE.factorwise

end BilinearComplexity
