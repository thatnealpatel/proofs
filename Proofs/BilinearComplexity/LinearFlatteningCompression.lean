/-
  BilinearComplexity/LinearFlatteningCompression — downstream certificate
  adapters for contractions and coordinate pullbacks.
-/
import BilinearComplexity.Flattening
import BilinearComplexity.LinearFlattening
import BilinearComplexity.MatMulMono
import BilinearComplexity.RankCalculus

set_option autoImplicit false

namespace BilinearComplexity

section CompressionCertificates

variable {k : Type*} [Field k] {a b c r q : ℕ}
variable {rows cols : Type*} [Fintype rows] [Fintype cols]

/-- A minor certificate lifts through mode-1 contraction: apply the core
certificate after transporting the decomposition with `RankLE.contract₁`. -/
theorem le_mul_of_contract₁_submatrix_det_ne_zero_of_rankLE
    {a' : ℕ} (F : Tensor k a' b c →ₗ[k] Matrix rows cols k)
    (hsimple : ∀ (u : Fin a' → k) (v : Fin b → k) (w : Fin c → k),
      (F (fun i j l => u i * v j * w l)).rank ≤ q)
    (M : Matrix (Fin a') (Fin a) k) {m : ℕ}
    (ri : Fin m → rows) (ci : Fin m → cols) {T : Tensor k a b c}
    (hdet : ((F (contract₁ M T)).submatrix ri ci).det ≠ 0)
    (hT : RankLE T r) : m ≤ r * q :=
  le_mul_of_submatrix_det_ne_zero_of_rankLE F hsimple ri ci hdet (hT.contract₁ M)

/-- A minor certificate lifts through arbitrary coordinate pullback: apply the
core certificate after transporting the decomposition with `RankLE.comp`; no
injectivity assumptions are needed on the index maps. -/
theorem le_mul_of_comp_submatrix_det_ne_zero_of_rankLE
    {a' b' c' : ℕ} (F : Tensor k a b c →ₗ[k] Matrix rows cols k)
    (hsimple : ∀ (u : Fin a → k) (v : Fin b → k) (w : Fin c → k),
      (F (fun i j l => u i * v j * w l)).rank ≤ q)
    (f : Fin a → Fin a') (g : Fin b → Fin b') (e : Fin c → Fin c')
    {m : ℕ} (ri : Fin m → rows) (ci : Fin m → cols) {T : Tensor k a' b' c'}
    (hdet : ((F (fun i j l => T (f i) (g j) (e l))).submatrix ri ci).det ≠ 0)
    (hT : RankLE T r) : m ≤ r * q :=
  le_mul_of_submatrix_det_ne_zero_of_rankLE F hsimple ri ci hdet (hT.comp f g e)

#check @le_mul_of_contract₁_submatrix_det_ne_zero_of_rankLE
#check @le_mul_of_comp_submatrix_det_ne_zero_of_rankLE

end CompressionCertificates

/-! ## Concrete non-vacuity audits -/

/-- A positive-dimensional mode-1 certificate works through multiplication by
the genuinely nonidentity `1 × 1` matrix `[2]` over `ℚ`. -/
example :
    let M : Matrix (Fin 1) (Fin 1) ℚ := fun _ _ => 2
    let T : Tensor ℚ 1 1 1 := fun _ _ _ => 1
    M ≠ 1 ∧
      ((flatteningLinear (contract₁ M T)).submatrix id
        (fun x : Fin 1 => (x, x))).det ≠ 0 ∧
      1 ≤ 1 * 1 := by
  dsimp
  constructor
  · intro hM
    have hentry := congrFun (congrFun hM (0 : Fin 1)) (0 : Fin 1)
    norm_num [Matrix.one_apply] at hentry
  constructor
  · norm_num [Matrix.det_fin_one, Matrix.submatrix_apply,
      flatteningLinear_apply, flattening, contract₁]
  · have hdet :
        ((flatteningLinear (contract₁ (fun _ _ : Fin 1 => (2 : ℚ))
          (fun _ _ _ => (1 : ℚ)))).submatrix id
          (fun x : Fin 1 => (x, x))).det ≠ 0 := by
      norm_num [Matrix.det_fin_one, Matrix.submatrix_apply,
        flatteningLinear_apply, flattening, contract₁]
    have hT : RankLE (fun _ _ _ => (1 : ℚ) : Tensor ℚ 1 1 1) 1 :=
      ⟨fun _ _ => 1, fun _ _ => 1, fun _ _ => 1, by funext; simp⟩
    exact le_mul_of_contract₁_submatrix_det_ne_zero_of_rankLE
      (r := 1) (q := 1) (T := fun _ _ _ => (1 : ℚ))
      flatteningLinear rank_flatteningLinear_simple_le_one
      (fun _ _ : Fin 1 => (2 : ℚ)) id (fun x : Fin 1 => (x, x)) hdet hT

/-- A positive-dimensional pullback certificate works when the first tensor
index map `Fin 2 → Fin 2` is constant and hence genuinely noninjective. -/
example :
    let f : Fin 2 → Fin 2 := fun _ => 0
    let T : Tensor ℚ 2 1 1 := fun _ _ _ => 1
    ¬ Function.Injective f ∧
      ((flatteningLinear (fun i j l => T (f i) j l)).submatrix
        (fun _ : Fin 1 => 0) (fun x : Fin 1 => (x, x))).det ≠ 0 ∧
      1 ≤ 1 * 1 := by
  dsimp
  constructor
  · intro hf
    have h01 : (0 : Fin 2) = 1 := hf rfl
    exact Fin.zero_ne_one h01
  constructor
  · norm_num [Matrix.det_fin_one, Matrix.submatrix_apply,
      flatteningLinear_apply, flattening]
  · have hdet :
        ((flatteningLinear (fun i j l =>
          (fun _ _ _ => (1 : ℚ)) ((fun _ : Fin 2 => (0 : Fin 2)) i) j l)).submatrix
          (fun _ : Fin 1 => (0 : Fin 2)) (fun x : Fin 1 => (x, x))).det ≠ 0 := by
      norm_num [Matrix.det_fin_one, Matrix.submatrix_apply,
        flatteningLinear_apply, flattening]
    have hT : RankLE (fun _ _ _ => (1 : ℚ) : Tensor ℚ 2 1 1) 1 :=
      ⟨fun _ _ => 1, fun _ _ => 1, fun _ _ => 1, by funext; simp⟩
    exact le_mul_of_comp_submatrix_det_ne_zero_of_rankLE
      (r := 1) (q := 1) (T := fun _ _ _ => (1 : ℚ))
      flatteningLinear rank_flatteningLinear_simple_le_one
      (fun _ : Fin 2 => (0 : Fin 2)) id id
      (fun _ : Fin 1 => (0 : Fin 2)) (fun x : Fin 1 => (x, x)) hdet hT

#print axioms le_mul_of_contract₁_submatrix_det_ne_zero_of_rankLE
#print axioms le_mul_of_comp_submatrix_det_ne_zero_of_rankLE

end BilinearComplexity
