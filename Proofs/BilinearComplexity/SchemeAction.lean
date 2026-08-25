import BilinearComplexity.Scheme

set_option autoImplicit false

namespace BilinearComplexity
namespace Scheme
namespace Action

variable {k : Type*} {a b c r : ℕ}

/-- A product-one triple of units used to rescale the three factors of one term. -/
structure Gauge (k : Type*) [CommMonoid k] where
  /-- The unit multiplying the first factor. -/
  first : kˣ
  /-- The unit multiplying the second factor. -/
  second : kˣ
  /-- The unit multiplying the third factor. -/
  third : kˣ
  /-- The three units have product one. -/
  product_eq_one : first * second * third = 1

/-- The trivial product-one gauge. -/
def Gauge.one (k : Type*) [CommMonoid k] : Gauge k :=
  ⟨1, 1, 1, by simp only [mul_one]⟩

/-- The trivial gauge really has unit coefficients in every leg. -/
example [CommMonoid k] : (Gauge.one k).first = 1 := rfl

/-- Apply a product-one gauge independently to every stored term. -/
def gauge [CommSemiring k] (S : Scheme k a b c r) (g : Fin r → Gauge k) :
    Scheme k a b c r :=
  ⟨fun s =>
    (fun i => (g s).first * (S.term s).1 i,
      fun j => (g s).second * (S.term s).2.1 j,
      fun l => (g s).third * (S.term s).2.2 l)⟩

/-- The one-term trivial gauge leaves the unique term unchanged. -/
example [CommSemiring k] (S : Scheme k 1 1 1 1) :
    gauge S (fun _ => Gauge.one k) = S := by
  cases S
  simp only [gauge, Gauge.one, Units.val_one, one_mul]

/-- Product-one gauges preserve each evaluated rank-one triad exactly. -/
@[simp] theorem eval_gauge [CommSemiring k] (S : Scheme k a b c r)
    (g : Fin r → Gauge k) (s : Fin r) :
    ((gauge S g).term s).eval = (S.term s).eval := by
  funext i j l
  change ((g s).first : k) * (S.term s).1 i *
      (((g s).second : k) * (S.term s).2.1 j) *
      (((g s).third : k) * (S.term s).2.2 l) = _
  have hproduct : ((g s).first : k) * (g s).second * (g s).third = 1 := by
    have h := congrArg (fun u : kˣ => (u : k)) (g s).product_eq_one
    simpa only [Units.val_mul, Units.val_one] using h
  calc
    ((g s).first : k) * (S.term s).1 i *
        (((g s).second : k) * (S.term s).2.1 j) *
        (((g s).third : k) * (S.term s).2.2 l) =
      (((g s).first : k) * (g s).second * (g s).third) *
        ((S.term s).1 i * (S.term s).2.1 j * (S.term s).2.2 l) := by ac_rfl
    _ = _ := by rw [hproduct, one_mul]

/-- Product-one termwise gauges preserve the represented tensor exactly. -/
@[simp] theorem sumTensor_gauge [CommSemiring k] (S : Scheme k a b c r)
    (g : Fin r → Gauge k) : (gauge S g).sumTensor = S.sumTensor :=
  sumTensor_eq_of_eval_eq (eval_gauge S g)

/-- The six possible ordered permutations of three tensor legs. -/
inductive Orientation where
  /-- Keep the order `(1,2,3)`. -/
  | abc
  /-- Use the cyclic order `(2,3,1)`. -/
  | bca
  /-- Use the cyclic order `(3,1,2)`. -/
  | cab
  /-- Use the order `(1,3,2)`. -/
  | acb
  /-- Use the reversal `(3,2,1)`. -/
  | cba
  /-- Use the order `(2,1,3)`. -/
  | bac
  deriving DecidableEq

/-- The six orientations form a finite type with no hidden additional cases. -/
instance : Fintype Orientation where
  elems := {.abc, .bca, .cab, .acb, .cba, .bac}
  complete x := by cases x <;> simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto

/-- The first output dimension selected by an orientation. -/
def Orientation.firstDim (o : Orientation) (a b c : ℕ) : ℕ :=
  match o with
  | .abc | .acb => a
  | .bca | .bac => b
  | .cab | .cba => c

/-- The second output dimension selected by an orientation. -/
def Orientation.secondDim (o : Orientation) (a b c : ℕ) : ℕ :=
  match o with
  | .abc | .cba => b
  | .bca | .acb => c
  | .cab | .bac => a

/-- The third output dimension selected by an orientation. -/
def Orientation.thirdDim (o : Orientation) (a b c : ℕ) : ℕ :=
  match o with
  | .abc | .bac => c
  | .bca | .cba => a
  | .cab | .acb => b

/-- The identity orientation selects the original three dimensions. -/
example : (Orientation.abc.firstDim 2 3 5,
    Orientation.abc.secondDim 2 3 5, Orientation.abc.thirdDim 2 3 5) = (2, 3, 5) := rfl

/-- Transport a tensor by one of the six explicit permutations of its arguments. -/
def orientTensor [CommSemiring k] (o : Orientation) (T : Tensor k a b c) :
    Tensor k (o.firstDim a b c) (o.secondDim a b c) (o.thirdDim a b c) :=
  match o with
  | .abc => fun i j l => T i j l
  | .bca => fun j l i => T i j l
  | .cab => fun l i j => T i j l
  | .acb => fun i l j => T i j l
  | .cba => fun l j i => T i j l
  | .bac => fun j i l => T i j l

/-- Identity orientation is definitionally identity on tensor coordinates. -/
example [CommSemiring k] (T : Tensor k 2 3 5) : orientTensor .abc T = T := rfl

/-- Transport every triad of a scheme by one of the six explicit leg permutations. -/
def orient (o : Orientation) (S : Scheme k a b c r) :
    Scheme k (o.firstDim a b c) (o.secondDim a b c) (o.thirdDim a b c) r :=
  match o with
  | .abc => ⟨fun s => ((S.term s).1, (S.term s).2.1, (S.term s).2.2)⟩
  | .bca => ⟨fun s => ((S.term s).2.1, (S.term s).2.2, (S.term s).1)⟩
  | .cab => ⟨fun s => ((S.term s).2.2, (S.term s).1, (S.term s).2.1)⟩
  | .acb => ⟨fun s => ((S.term s).1, (S.term s).2.2, (S.term s).2.1)⟩
  | .cba => ⟨fun s => ((S.term s).2.2, (S.term s).2.1, (S.term s).1)⟩
  | .bac => ⟨fun s => ((S.term s).2.1, (S.term s).1, (S.term s).2.2)⟩

/-- Identity orientation is definitionally identity on schemes. -/
example (S : Scheme k 2 3 5 r) : orient .abc S = S := by
  cases S
  rfl

/-- Cyclically rotate the three factors and dimensions from `(a,b,c)` to `(b,c,a)`. -/
def cyclic (S : Scheme k a b c r) : Scheme k b c a r := orient .bca S

/-- Cyclic orientation sends the factors `(u,v,w)` to `(v,w,u)`. -/
example (S : Scheme k a b c r) (s : Fin r) :
    (cyclic S).term s = ((S.term s).2.1, (S.term s).2.2, (S.term s).1) := rfl

/-- Reverse the three factors and dimensions from `(a,b,c)` to `(c,b,a)`. -/
def reversal (S : Scheme k a b c r) : Scheme k c b a r := orient .cba S

/-- Reversal sends the factors `(u,v,w)` to `(w,v,u)`. -/
example (S : Scheme k a b c r) (s : Fin r) :
    (reversal S).term s = ((S.term s).2.2, (S.term s).2.1, (S.term s).1) := rfl

/-- Orientation commutes exactly with taking the represented tensor. -/
@[simp] theorem sumTensor_orient [CommSemiring k] (o : Orientation)
    (S : Scheme k a b c r) : (orient o S).sumTensor = orientTensor o S.sumTensor := by
  cases o <;> funext i j l <;>
    simp only [orient, orientTensor, sumTensor, TriadData.eval, triad] <;>
    apply Finset.sum_congr rfl <;> intro s hs <;>
    ac_rfl

/-- The exact slot-permutation action, named here as part of the action API. -/
def reorder (S : Scheme k a b c r) (e : Fin r ≃ Fin r) : Scheme k a b c r :=
  S.permute e

/-- Reordering by the identity equivalence does nothing. -/
example (S : Scheme k a b c r) : reorder S (Equiv.refl (Fin r)) = S := by
  cases S
  rfl

/-- Exact term permutation preserves the represented tensor. -/
@[simp] theorem sumTensor_reorder [CommSemiring k] (S : Scheme k a b c r)
    (e : Fin r ≃ Fin r) : (reorder S e).sumTensor = S.sumTensor :=
  sumTensor_permute S e

variable {n₁ n₂ n₃ : ℕ}

/-- Explicit compatible changes of bases for the three vertex spaces, including named inverses. -/
structure Sandwich (k : Type*) [CommSemiring k] (n₁ n₂ n₃ : ℕ) where
  /-- Change of basis on the first vertex space. -/
  P : Matrix (Fin n₁) (Fin n₁) k
  /-- Explicit inverse of `P`. -/
  PInv : Matrix (Fin n₁) (Fin n₁) k
  /-- Change of basis on the second vertex space. -/
  Q : Matrix (Fin n₂) (Fin n₂) k
  /-- Explicit inverse of `Q`. -/
  QInv : Matrix (Fin n₂) (Fin n₂) k
  /-- Change of basis on the third vertex space. -/
  R : Matrix (Fin n₃) (Fin n₃) k
  /-- Explicit inverse of `R`. -/
  RInv : Matrix (Fin n₃) (Fin n₃) k
  /-- `PInv` is a left inverse of `P`. -/
  PInv_mul_P : PInv * P = 1
  /-- `PInv` is a right inverse of `P`. -/
  P_mul_PInv : P * PInv = 1
  /-- `QInv` is a left inverse of `Q`. -/
  QInv_mul_Q : QInv * Q = 1
  /-- `QInv` is a right inverse of `Q`. -/
  Q_mul_QInv : Q * QInv = 1
  /-- `RInv` is a left inverse of `R`. -/
  RInv_mul_R : RInv * R = 1
  /-- `RInv` is a right inverse of `R`. -/
  R_mul_RInv : R * RInv = 1

/-- The identity sandwich has identity matrices and identity inverses. -/
def Sandwich.one (k : Type*) [CommSemiring k] (n₁ n₂ n₃ : ℕ) : Sandwich k n₁ n₂ n₃ :=
  ⟨1, 1, 1, 1, 1, 1, by simp only [mul_one], by simp only [mul_one],
    by simp only [mul_one], by simp only [mul_one], by simp only [mul_one], by simp only [mul_one]⟩

/-- Every matrix of the identity sandwich is the identity matrix. -/
example [CommSemiring k] : (Sandwich.one k 2 3 5).P = 1 := rfl

/-- Apply `P U Q⁻¹`, `Q V R⁻¹`, and `R W P⁻¹` in row-major matrix coordinates. -/
def sandwich [CommSemiring k] (S : MatrixScheme k n₁ n₂ n₃ r) (d : Sandwich k n₁ n₂ n₃) :
    MatrixScheme k n₁ n₂ n₃ r :=
  ⟨fun s =>
    (flattenMatrix (d.P * reshapeVector (S.term s).1 * d.QInv),
      flattenMatrix (d.Q * reshapeVector (S.term s).2.1 * d.RInv),
      flattenMatrix (d.R * reshapeVector (S.term s).2.2 * d.PInv))⟩

/-- The identity sandwich fixes every ordered scheme. -/
example [CommSemiring k] (S : MatrixScheme k n₁ n₂ n₃ r) :
    sandwich S (Sandwich.one k n₁ n₂ n₃) = S := by
  cases S with
  | mk term =>
    simp only [sandwich, Sandwich.one]
    congr
    funext s
    rcases term s with ⟨u, v, w⟩
    simp only [Prod.mk.injEq]
    constructor
    · rw [Matrix.one_mul, Matrix.mul_one]
      change (matrixVectorEquiv k n₁ n₂) ((matrixVectorEquiv k n₁ n₂).symm u) = u
      exact (matrixVectorEquiv k n₁ n₂).apply_symm_apply u
    · constructor
      · rw [Matrix.one_mul, Matrix.mul_one]
        change (matrixVectorEquiv k n₂ n₃) ((matrixVectorEquiv k n₂ n₃).symm v) = v
        exact (matrixVectorEquiv k n₂ n₃).apply_symm_apply v
      · rw [Matrix.one_mul, Matrix.mul_one]
        change (matrixVectorEquiv k n₃ n₁) ((matrixVectorEquiv k n₃ n₁).symm w) = w
        exact (matrixVectorEquiv k n₃ n₁).apply_symm_apply w

/-- A sandwiched first factor has the stated double-sum coordinate formula. -/
@[simp] theorem matrixEntry_sandwich_first [CommSemiring k]
    (S : MatrixScheme k n₁ n₂ n₃ r) (d : Sandwich k n₁ n₂ n₃)
    (s : Fin r) (i : Fin n₁) (j : Fin n₂) :
    matrixEntry ((sandwich S d).term s).1 i j =
      ∑ p, ∑ q, d.P i p * matrixEntry (S.term s).1 p q * d.QInv q j := by
  simp only [sandwich, flattenMatrix_entry, Matrix.mul_apply, reshapeVector_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_mul]

/-- A sandwiched second factor has the stated double-sum coordinate formula. -/
@[simp] theorem matrixEntry_sandwich_second [CommSemiring k]
    (S : MatrixScheme k n₁ n₂ n₃ r) (d : Sandwich k n₁ n₂ n₃)
    (s : Fin r) (j : Fin n₂) (l : Fin n₃) :
    matrixEntry ((sandwich S d).term s).2.1 j l =
      ∑ q, ∑ t, d.Q j q * matrixEntry (S.term s).2.1 q t * d.RInv t l := by
  simp only [sandwich, flattenMatrix_entry, Matrix.mul_apply, reshapeVector_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.sum_mul]

/-- A sandwiched third factor has the stated double-sum coordinate formula. -/
@[simp] theorem matrixEntry_sandwich_third [CommSemiring k]
    (S : MatrixScheme k n₁ n₂ n₃ r) (d : Sandwich k n₁ n₂ n₃)
    (s : Fin r) (l : Fin n₃) (i : Fin n₁) :
    matrixEntry ((sandwich S d).term s).2.2 l i =
      ∑ t, ∑ p, d.R l t * matrixEntry (S.term s).2.2 t p * d.PInv p i := by
  simp only [sandwich, flattenMatrix_entry, Matrix.mul_apply, reshapeVector_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.sum_mul]

/-- Sandwiching transports a represented tensor by the explicit sixfold coordinate contraction. -/
theorem sumTensor_sandwich_apply [CommSemiring k]
    (S : MatrixScheme k n₁ n₂ n₃ r) (d : Sandwich k n₁ n₂ n₃)
    (i : Fin n₁) (j : Fin n₂) (l : Fin n₃) :
    (sandwich S d).sumTensor (matrixIndexEquiv n₁ n₂ (i, j))
        (matrixIndexEquiv n₂ n₃ (j, l)) (matrixIndexEquiv n₃ n₁ (l, i)) =
      ∑ s, (∑ p, ∑ q, d.P i p * matrixEntry (S.term s).1 p q * d.QInv q j) *
        (∑ q, ∑ t, d.Q j q * matrixEntry (S.term s).2.1 q t * d.RInv t l) *
        (∑ t, ∑ p, d.R l t * matrixEntry (S.term s).2.2 t p * d.PInv p i) := by
  change ∑ s, matrixEntry ((sandwich S d).term s).1 i j *
      matrixEntry ((sandwich S d).term s).2.1 j l *
      matrixEntry ((sandwich S d).term s).2.2 l i = _
  simp only [matrixEntry_sandwich_first, matrixEntry_sandwich_second,
    matrixEntry_sandwich_third]

/-- Sandwiching by the explicit two-sided changes of basis preserves the Brent equations. -/
theorem Brent.sandwich [CommSemiring k] {S : MatrixScheme k n₁ n₂ n₃ r}
    (hS : S.Brent) (d : Sandwich k n₁ n₂ n₃) : (Action.sandwich S d).Brent := by
  intro i j j' l l' i'
  let X := Fin n₁ × Fin n₂ × Fin n₃ × Fin n₁ × Fin n₂ × Fin n₃
  let coefficient : X → k := fun x =>
    d.P i x.1 * d.QInv x.2.1 j * d.R l' x.2.2.1 * d.PInv x.2.2.2.1 i' *
      d.Q j' x.2.2.2.2.1 * d.RInv x.2.2.2.2.2 l
  let sourceProduct : Fin r → X → k := fun s x =>
    matrixEntry (S.term s).1 x.1 x.2.1 *
      matrixEntry (S.term s).2.1 x.2.2.2.2.1 x.2.2.2.2.2 *
      matrixEntry (S.term s).2.2 x.2.2.1 x.2.2.2.1
  have hfactor (s : Fin r) :
      matrixEntry ((Action.sandwich S d).term s).1 i j *
          matrixEntry ((Action.sandwich S d).term s).2.1 j' l *
          matrixEntry ((Action.sandwich S d).term s).2.2 l' i' =
        ∑ x : X, coefficient x * sourceProduct s x := by
    simp only [matrixEntry_sandwich_first, matrixEntry_sandwich_second,
      matrixEntry_sandwich_third, X, coefficient, sourceProduct]
    simp_rw [Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro t' ht'
    apply Finset.sum_congr rfl
    intro p' hp'
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q' hq'
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t ht
    ac_rfl
  have hsource (x : X) :
      ∑ s, sourceProduct s x =
        (if x.2.1 = x.2.2.2.2.1 then 1 else 0) *
          (if x.2.2.2.2.2 = x.2.2.1 then 1 else 0) *
          (if x.1 = x.2.2.2.1 then 1 else 0) := by
    exact hS x.1 x.2.1 x.2.2.2.2.1 x.2.2.2.2.2 x.2.2.1 x.2.2.2.1
  simp_rw [hfactor]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hsource]
  simp only [X, coefficient]
  simp_rw [Fintype.sum_prod_type]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_irrel, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte, Finset.sum_const_zero, Finset.sum_ite_eq]
  calc
    (∑ p, ∑ q, ∑ t,
        d.P i p * d.QInv q j * d.R l' t * d.PInv p i' * d.Q j' q * d.RInv t l) =
        (∑ p, d.P i p * d.PInv p i') * (∑ t, d.R l' t * d.RInv t l) *
          (∑ q, d.Q j' q * d.QInv q j) := by
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro t ht
      ac_rfl
    _ = (d.P * d.PInv) i i' * (d.R * d.RInv) l' l * (d.Q * d.QInv) j' j := by
      simp only [Matrix.mul_apply]
    _ = _ := by
      rw [d.P_mul_PInv, d.Q_mul_QInv, d.R_mul_RInv]
      simp only [Matrix.one_apply, eq_comm]
      by_cases hi : i = i' <;> by_cases hl : l = l' <;> by_cases hj : j = j' <;>
        simp only [hi, hl, hj, if_true, if_false, mul_zero, mul_one]

/-- Transpose a flattened rectangular matrix while preserving row-major coordinates. -/
def transposeFactor (u : Fin (a * b) → k) : Fin (b * a) → k :=
  flattenMatrix (Matrix.transpose (reshapeVector u))

/-- Transposing a flattened `2 × 3` zero matrix produces a flattened `3 × 2` zero matrix. -/
example : transposeFactor (k := ℕ) (a := 2) (b := 3) (fun _ => 0) = fun _ => 0 := by
  funext x
  rfl

/-- Matrix entries of a flattened transpose have their row and column exchanged. -/
@[simp] theorem matrixEntry_transposeFactor (u : Fin (a * b) → k)
    (j : Fin b) (i : Fin a) : matrixEntry (transposeFactor u) j i = matrixEntry u i j := by
  simp only [transposeFactor, flattenMatrix_entry, Matrix.transpose_apply, reshapeVector_apply]

/-- Apply one of all six vertex orientations to a rectangular matrix scheme.
The odd orientations transpose every reversed edge. -/
def orientMatrix (o : Orientation) (S : MatrixScheme k n₁ n₂ n₃ r) :
    MatrixScheme k (o.firstDim n₁ n₂ n₃) (o.secondDim n₁ n₂ n₃)
      (o.thirdDim n₁ n₂ n₃) r :=
  match o with
  | .abc => ⟨fun s => ((S.term s).1, (S.term s).2.1, (S.term s).2.2)⟩
  | .bca => ⟨fun s => ((S.term s).2.1, (S.term s).2.2, (S.term s).1)⟩
  | .cab => ⟨fun s => ((S.term s).2.2, (S.term s).1, (S.term s).2.1)⟩
  | .acb => ⟨fun s => (transposeFactor (S.term s).2.2,
      transposeFactor (S.term s).2.1, transposeFactor (S.term s).1)⟩
  | .cba => ⟨fun s => (transposeFactor (S.term s).2.1,
      transposeFactor (S.term s).1, transposeFactor (S.term s).2.2)⟩
  | .bac => ⟨fun s => (transposeFactor (S.term s).1,
      transposeFactor (S.term s).2.2, transposeFactor (S.term s).2.1)⟩

/-- The `acb` orientation reverses and transposes all three directed edges. -/
@[simp] theorem orientMatrix_acb_term (S : MatrixScheme k n₁ n₂ n₃ r) (s : Fin r) :
    (orientMatrix Orientation.acb S).term s = (transposeFactor (S.term s).2.2,
      transposeFactor (S.term s).2.1, transposeFactor (S.term s).1) := rfl

/-- The `cba` orientation is the requested transpose/reversal factor map. -/
@[simp] theorem orientMatrix_cba_term (S : MatrixScheme k n₁ n₂ n₃ r) (s : Fin r) :
    (orientMatrix Orientation.cba S).term s = (transposeFactor (S.term s).2.1,
      transposeFactor (S.term s).1, transposeFactor (S.term s).2.2) := rfl

/-- The `bac` orientation reverses and transposes all three directed edges. -/
@[simp] theorem orientMatrix_bac_term (S : MatrixScheme k n₁ n₂ n₃ r) (s : Fin r) :
    (orientMatrix Orientation.bac S).term s = (transposeFactor (S.term s).1,
      transposeFactor (S.term s).2.2, transposeFactor (S.term s).2.1) := rfl

/-- First coordinate equation for the `acb` orientation. -/
@[simp] theorem matrixEntry_orientMatrix_acb_first (S : MatrixScheme k n₁ n₂ n₃ r)
    (s : Fin r) (i : Fin n₁) (l : Fin n₃) :
    matrixEntry ((orientMatrix Orientation.acb S).term s).1 i l =
      matrixEntry (S.term s).2.2 l i := by
  simp only [Orientation.firstDim, Orientation.secondDim, Orientation.thirdDim]
  rw [orientMatrix_acb_term, matrixEntry_transposeFactor]

/-- Second coordinate equation for the `acb` orientation. -/
@[simp] theorem matrixEntry_orientMatrix_acb_second (S : MatrixScheme k n₁ n₂ n₃ r)
    (s : Fin r) (l : Fin n₃) (j : Fin n₂) :
    matrixEntry ((orientMatrix Orientation.acb S).term s).2.1 l j =
      matrixEntry (S.term s).2.1 j l := by
  simp only [Orientation.firstDim, Orientation.secondDim, Orientation.thirdDim]
  rw [orientMatrix_acb_term, matrixEntry_transposeFactor]

/-- Third coordinate equation for the `acb` orientation. -/
@[simp] theorem matrixEntry_orientMatrix_acb_third (S : MatrixScheme k n₁ n₂ n₃ r)
    (s : Fin r) (j : Fin n₂) (i : Fin n₁) :
    matrixEntry ((orientMatrix Orientation.acb S).term s).2.2 j i =
      matrixEntry (S.term s).1 i j := by
  simp only [Orientation.firstDim, Orientation.secondDim, Orientation.thirdDim]
  rw [orientMatrix_acb_term, matrixEntry_transposeFactor]

/-- First coordinate equation for transpose/reversal. -/
@[simp] theorem matrixEntry_orientMatrix_cba_first (S : MatrixScheme k n₁ n₂ n₃ r)
    (s : Fin r) (l : Fin n₃) (j : Fin n₂) :
    matrixEntry ((orientMatrix Orientation.cba S).term s).1 l j =
      matrixEntry (S.term s).2.1 j l := by
  simp only [Orientation.firstDim, Orientation.secondDim, Orientation.thirdDim]
  rw [orientMatrix_cba_term, matrixEntry_transposeFactor]

/-- Second coordinate equation for transpose/reversal. -/
@[simp] theorem matrixEntry_orientMatrix_cba_second (S : MatrixScheme k n₁ n₂ n₃ r)
    (s : Fin r) (j : Fin n₂) (i : Fin n₁) :
    matrixEntry ((orientMatrix Orientation.cba S).term s).2.1 j i =
      matrixEntry (S.term s).1 i j := by
  simp only [Orientation.firstDim, Orientation.secondDim, Orientation.thirdDim]
  rw [orientMatrix_cba_term, matrixEntry_transposeFactor]

/-- Third coordinate equation for transpose/reversal. -/
@[simp] theorem matrixEntry_orientMatrix_cba_third (S : MatrixScheme k n₁ n₂ n₃ r)
    (s : Fin r) (i : Fin n₁) (l : Fin n₃) :
    matrixEntry ((orientMatrix Orientation.cba S).term s).2.2 i l =
      matrixEntry (S.term s).2.2 l i := by
  simp only [Orientation.firstDim, Orientation.secondDim, Orientation.thirdDim]
  rw [orientMatrix_cba_term, matrixEntry_transposeFactor]

/-- First coordinate equation for the `bac` orientation. -/
@[simp] theorem matrixEntry_orientMatrix_bac_first (S : MatrixScheme k n₁ n₂ n₃ r)
    (s : Fin r) (j : Fin n₂) (i : Fin n₁) :
    matrixEntry ((orientMatrix Orientation.bac S).term s).1 j i =
      matrixEntry (S.term s).1 i j := by
  simp only [Orientation.firstDim, Orientation.secondDim, Orientation.thirdDim]
  rw [orientMatrix_bac_term, matrixEntry_transposeFactor]

/-- Second coordinate equation for the `bac` orientation. -/
@[simp] theorem matrixEntry_orientMatrix_bac_second (S : MatrixScheme k n₁ n₂ n₃ r)
    (s : Fin r) (i : Fin n₁) (l : Fin n₃) :
    matrixEntry ((orientMatrix Orientation.bac S).term s).2.1 i l =
      matrixEntry (S.term s).2.2 l i := by
  simp only [Orientation.firstDim, Orientation.secondDim, Orientation.thirdDim]
  rw [orientMatrix_bac_term, matrixEntry_transposeFactor]

/-- Third coordinate equation for the `bac` orientation. -/
@[simp] theorem matrixEntry_orientMatrix_bac_third (S : MatrixScheme k n₁ n₂ n₃ r)
    (s : Fin r) (l : Fin n₃) (j : Fin n₂) :
    matrixEntry ((orientMatrix Orientation.bac S).term s).2.2 l j =
      matrixEntry (S.term s).2.1 j l := by
  simp only [Orientation.firstDim, Orientation.secondDim, Orientation.thirdDim]
  rw [orientMatrix_bac_term, matrixEntry_transposeFactor]

/-- The identity matrix orientation fixes every factor. -/
example (S : MatrixScheme k n₁ n₂ n₃ r) : orientMatrix .abc S = S := by
  cases S
  rfl

/-- Cyclic matrix rotation sends `(U,V,W)` to `(V,W,U)` and dimensions
`(n₁,n₂,n₃)` to `(n₂,n₃,n₁)`. -/
def cyclicMatrix (S : MatrixScheme k n₁ n₂ n₃ r) : MatrixScheme k n₂ n₃ n₁ r :=
  orientMatrix .bca S

/-- Cyclic rotation has the exact requested factor order. -/
example (S : MatrixScheme k n₁ n₂ n₃ r) (s : Fin r) :
    (cyclicMatrix S).term s = ((S.term s).2.1, (S.term s).2.2, (S.term s).1) := rfl

/-- Transpose/reversal sends `(U,V,W)` to `(Vᵀ,Uᵀ,Wᵀ)` and dimensions
`(n₁,n₂,n₃)` to `(n₃,n₂,n₁)`. -/
def transposeReversal (S : MatrixScheme k n₁ n₂ n₃ r) : MatrixScheme k n₃ n₂ n₁ r :=
  orientMatrix Orientation.cba S

/-- Transpose/reversal has the exact requested three flattened factors. -/
example (S : MatrixScheme k n₁ n₂ n₃ r) (s : Fin r) :
    (transposeReversal S).term s = (transposeFactor (S.term s).2.1,
      transposeFactor (S.term s).1, transposeFactor (S.term s).2.2) := rfl

/-- Every one of the six matrix orientations preserves the corresponding rectangular
Brent equations. -/
theorem Brent.orientMatrix [CommSemiring k] {S : MatrixScheme k n₁ n₂ n₃ r}
    (hS : S.Brent) (o : Orientation) : (orientMatrix o S).Brent := by
  cases o with
  | abc => exact hS
  | bca =>
      intro j l l' i i' j'
      change (∑ s, matrixEntry (S.term s).2.1 j l *
        matrixEntry (S.term s).2.2 l' i * matrixEntry (S.term s).1 i' j') = _
      calc
        _ = ∑ s, matrixEntry (S.term s).1 i' j' *
            matrixEntry (S.term s).2.1 j l * matrixEntry (S.term s).2.2 l' i := by
          apply Finset.sum_congr rfl
          intro s hs
          ac_rfl
        _ = (if j' = j then 1 else 0) * (if l = l' then 1 else 0) *
            (if i' = i then 1 else 0) := hS i' j' j l l' i
        _ = _ := by simp only [eq_comm]; ring
  | cab =>
      intro l i i' j j' l'
      change (∑ s, matrixEntry (S.term s).2.2 l i *
        matrixEntry (S.term s).1 i' j * matrixEntry (S.term s).2.1 j' l') = _
      calc
        _ = ∑ s, matrixEntry (S.term s).1 i' j *
            matrixEntry (S.term s).2.1 j' l' * matrixEntry (S.term s).2.2 l i := by
          apply Finset.sum_congr rfl
          intro s hs
          ac_rfl
        _ = (if j = j' then 1 else 0) * (if l' = l then 1 else 0) *
            (if i' = i then 1 else 0) := hS i' j j' l' l i
        _ = _ := by simp only [eq_comm]; ring
  | acb =>
      unfold Scheme.Brent
      simp only [Orientation.firstDim, Orientation.secondDim, Orientation.thirdDim]
      intro i l l' j j' i'
      simp only [Action.orientMatrix, Orientation.firstDim, Orientation.secondDim,
        Orientation.thirdDim]
      simp only [matrixEntry_transposeFactor]
      calc
        (∑ s, matrixEntry (S.term s).2.2 l i * matrixEntry (S.term s).2.1 j l' *
            matrixEntry (S.term s).1 i' j') =
          ∑ s, matrixEntry (S.term s).1 i' j' *
            matrixEntry (S.term s).2.1 j l' * matrixEntry (S.term s).2.2 l i := by
              apply Finset.sum_congr rfl
              intro s hs
              ac_rfl
        _ = (if j' = j then 1 else 0) * (if l' = l then 1 else 0) *
            (if i' = i then 1 else 0) := hS i' j' j l' l i
        _ = _ := by simp only [eq_comm]; ac_rfl
  | cba =>
      unfold Scheme.Brent
      simp only [Orientation.firstDim, Orientation.secondDim, Orientation.thirdDim]
      intro l j j' i i' l'
      simp only [Action.orientMatrix, Orientation.firstDim, Orientation.secondDim,
        Orientation.thirdDim]
      simp only [matrixEntry_transposeFactor]
      calc
        (∑ s, matrixEntry (S.term s).2.1 j l * matrixEntry (S.term s).1 i j' *
            matrixEntry (S.term s).2.2 l' i') =
          ∑ s, matrixEntry (S.term s).1 i j' *
            matrixEntry (S.term s).2.1 j l * matrixEntry (S.term s).2.2 l' i' := by
              apply Finset.sum_congr rfl
              intro s hs
              ac_rfl
        _ = (if j' = j then 1 else 0) * (if l = l' then 1 else 0) *
            (if i = i' then 1 else 0) := hS i j' j l l' i'
        _ = _ := by simp only [eq_comm]; ac_rfl
  | bac =>
      unfold Scheme.Brent
      simp only [Orientation.firstDim, Orientation.secondDim, Orientation.thirdDim]
      intro j i i' l l' j'
      simp only [Action.orientMatrix, Orientation.firstDim, Orientation.secondDim,
        Orientation.thirdDim]
      simp only [matrixEntry_transposeFactor]
      calc
        (∑ s, matrixEntry (S.term s).1 i j * matrixEntry (S.term s).2.2 l i' *
            matrixEntry (S.term s).2.1 j' l') =
          ∑ s, matrixEntry (S.term s).1 i j *
            matrixEntry (S.term s).2.1 j' l' * matrixEntry (S.term s).2.2 l i' := by
              apply Finset.sum_congr rfl
              intro s hs
              ac_rfl
        _ = (if j = j' then 1 else 0) * (if l' = l then 1 else 0) *
            (if i = i' then 1 else 0) := hS i j j' l' l i'
        _ = _ := by simp only [eq_comm]; ac_rfl

/-- Product-one gauges preserve every rectangular Brent decomposition. -/
theorem Brent.gauge [CommSemiring k] {S : MatrixScheme k n₁ n₂ n₃ r}
    (hS : S.Brent) (g : Fin r → Gauge k) : (Action.gauge S g).Brent := by
  apply (brent_iff_sumTensor_eq_matMulTensor (Action.gauge S g)).2
  rw [sumTensor_gauge]
  exact (brent_iff_sumTensor_eq_matMulTensor S).1 hS

/-- Exact slot reordering preserves every rectangular Brent decomposition. -/
theorem Brent.reorder [CommSemiring k] {S : MatrixScheme k n₁ n₂ n₃ r}
    (hS : S.Brent) (e : Fin r ≃ Fin r) : (Action.reorder S e).Brent := by
  apply (brent_iff_sumTensor_eq_matMulTensor (Action.reorder S e)).2
  rw [sumTensor_reorder]
  exact (brent_iff_sumTensor_eq_matMulTensor S).1 hS

/-- Positivity of the three vertex dimensions is preserved by every outer orientation. -/
theorem PositiveDimensions.orient (h : PositiveDimensions n₁ n₂ n₃) (o : Orientation) :
    PositiveDimensions (o.firstDim n₁ n₂ n₃) (o.secondDim n₁ n₂ n₃)
      (o.thirdDim n₁ n₂ n₃) := by
  rcases h with ⟨h₁, h₂, h₃⟩
  cases o <;> exact ⟨by assumption, by assumption, by assumption⟩

/-- Sandwiching preserves replay-facing Brent data and its nonempty-dimension guard. -/
theorem ReplayableBrent.sandwich [CommSemiring k] [Nontrivial k]
    {S : MatrixScheme k n₁ n₂ n₃ r} (hS : S.ReplayableBrent)
    (d : Sandwich k n₁ n₂ n₃) : (Action.sandwich S d).ReplayableBrent :=
  ⟨hS.1, Brent.sandwich hS.2 d⟩

/-- Outer orientation preserves replay-facing Brent data and permutes its positive dimensions. -/
theorem ReplayableBrent.orientMatrix [CommSemiring k] [Nontrivial k]
    {S : MatrixScheme k n₁ n₂ n₃ r} (hS : S.ReplayableBrent) (o : Orientation) :
    (Action.orientMatrix o S).ReplayableBrent :=
  ⟨PositiveDimensions.orient hS.1 o, Brent.orientMatrix hS.2 o⟩

/-- Product-one gauges preserve replay-facing Brent data. -/
theorem ReplayableBrent.gauge [CommSemiring k] [Nontrivial k]
    {S : MatrixScheme k n₁ n₂ n₃ r} (hS : S.ReplayableBrent)
    (g : Fin r → Gauge k) : (Action.gauge S g).ReplayableBrent :=
  ⟨hS.1, Brent.gauge hS.2 g⟩

/-- Exact slot reordering preserves replay-facing Brent data. -/
theorem ReplayableBrent.reorder [CommSemiring k] [Nontrivial k]
    {S : MatrixScheme k n₁ n₂ n₃ r} (hS : S.ReplayableBrent)
    (e : Fin r ≃ Fin r) : (Action.reorder S e).ReplayableBrent :=
  ⟨hS.1, Brent.reorder hS.2 e⟩

/-- All replay data after fixing the output orientation: explicit bases and inverses,
an exact slot permutation, and product-one gauges. -/
structure Replay [CommSemiring k] (n₁ n₂ n₃ r : ℕ) (o : Orientation) where
  /-- Explicit two-sided invertible sandwich data in the oriented dimensions. -/
  sandwich : Sandwich k (o.firstDim n₁ n₂ n₃) (o.secondDim n₁ n₂ n₃)
    (o.thirdDim n₁ n₂ n₃)
  /-- Exact permutation of stored terms. -/
  permutation : Fin r ≃ Fin r
  /-- Product-one gauge attached to each output slot. -/
  gauges : Fin r → Gauge k

/-- Replay orientation, sandwich, exact slot permutation, then product-one gauges. -/
def replay [CommSemiring k] (o : Orientation) (S : MatrixScheme k n₁ n₂ n₃ r)
    (x : Replay (k := k) n₁ n₂ n₃ r o) :
    MatrixScheme k (o.firstDim n₁ n₂ n₃) (o.secondDim n₁ n₂ n₃)
      (o.thirdDim n₁ n₂ n₃) r :=
  gauge (reorder (sandwich (orientMatrix o S) x.sandwich) x.permutation) x.gauges

/-- Trivial replay data for the identity orientation. -/
def Replay.one [CommSemiring k] (n₁ n₂ n₃ r : ℕ) : Replay (k := k) n₁ n₂ n₃ r .abc :=
  ⟨Sandwich.one k n₁ n₂ n₃, Equiv.refl (Fin r), fun _ => Gauge.one k⟩

/-- Trivial replay data stores identity permutation. -/
example [CommSemiring k] : (Replay.one (k := k) 1 1 1 1).permutation = Equiv.refl (Fin 1) := rfl

/-- A combined replay witness records the output scheme and its three exact mapped-factor
equations at the permuted slot; its replay data itself contains all six inverse checks. -/
structure ReplayWitness [CommSemiring k] (S : MatrixScheme k n₁ n₂ n₃ r)
    (o : Orientation)
    (T : MatrixScheme k (o.firstDim n₁ n₂ n₃) (o.secondDim n₁ n₂ n₃)
      (o.thirdDim n₁ n₂ n₃) r) where
  /-- The orientation, two-sided inverses, permutation, and gauges used in replay. -/
  data : Replay (k := k) n₁ n₂ n₃ r o
  /-- Exact first-factor equation in the target slot `permutation s`. -/
  first_eq : ∀ s, (T.term (data.permutation s)).1 =
    fun i => (data.gauges (data.permutation s)).first *
      ((sandwich (orientMatrix o S) data.sandwich).term s).1 i
  /-- Exact second-factor equation in the target slot `permutation s`. -/
  second_eq : ∀ s, (T.term (data.permutation s)).2.1 =
    fun j => (data.gauges (data.permutation s)).second *
      ((sandwich (orientMatrix o S) data.sandwich).term s).2.1 j
  /-- Exact third-factor equation in the target slot `permutation s`. -/
  third_eq : ∀ s, (T.term (data.permutation s)).2.2 =
    fun l => (data.gauges (data.permutation s)).third *
      ((sandwich (orientMatrix o S) data.sandwich).term s).2.2 l

/-- Every computed replay supplies its combined exact replay witness. -/
def replayWitness [CommSemiring k] (o : Orientation)
    (S : MatrixScheme k n₁ n₂ n₃ r) (x : Replay (k := k) n₁ n₂ n₃ r o) :
    ReplayWitness S o (replay o S x) := by
  refine ⟨x, ?_, ?_, ?_⟩ <;> intro s <;>
    simp only [replay, gauge, reorder, Scheme.permute, Equiv.symm_apply_apply]

/-- The three exact factor equations in an arbitrary witness determine its target as the
computed replay; hence externally supplied replay data are sufficient without trusting how the
target scheme was produced. -/
theorem ReplayWitness.target_eq_replay [CommSemiring k]
    {S : MatrixScheme k n₁ n₂ n₃ r} {o : Orientation}
    {T : MatrixScheme k (o.firstDim n₁ n₂ n₃) (o.secondDim n₁ n₂ n₃)
      (o.thirdDim n₁ n₂ n₃) r} (h : ReplayWitness S o T) :
    T = replay o S h.data := by
  rcases T with ⟨term⟩
  congr 1
  funext q
  obtain ⟨s, rfl⟩ := h.data.permutation.surjective q
  apply Prod.ext
  · simpa only [replay, gauge, reorder, Scheme.permute, Equiv.symm_apply_apply] using
      h.first_eq s
  · apply Prod.ext
    · simpa only [replay, gauge, reorder, Scheme.permute, Equiv.symm_apply_apply] using
        h.second_eq s
    · simpa only [replay, gauge, reorder, Scheme.permute, Equiv.symm_apply_apply] using
        h.third_eq s

/-- The computed witness retains exactly the supplied combined replay data. -/
example [CommSemiring k] (o : Orientation) (S : MatrixScheme k n₁ n₂ n₃ r)
    (x : Replay (k := k) n₁ n₂ n₃ r o) : (replayWitness o S x).data = x := rfl

/-- An algebraic replay of a Brent decomposition is again a Brent decomposition in its
oriented shape; use `ReplayableBrent.replay` when nonempty replay dimensions are intended. -/
theorem Brent.replay [CommSemiring k] {S : MatrixScheme k n₁ n₂ n₃ r}
    (hS : S.Brent) (o : Orientation) (x : Replay (k := k) n₁ n₂ n₃ r o) :
    (Action.replay o S x).Brent :=
  Brent.gauge (Brent.reorder (Brent.sandwich (Brent.orientMatrix hS o) x.sandwich)
    x.permutation) x.gauges

/-- Combined replay preserves both Brent equations and the explicit nonempty-dimension guard. -/
theorem ReplayableBrent.replay [CommSemiring k] [Nontrivial k]
    {S : MatrixScheme k n₁ n₂ n₃ r} (hS : S.ReplayableBrent) (o : Orientation)
    (x : Replay (k := k) n₁ n₂ n₃ r o) :
    (Action.replay o S x).ReplayableBrent :=
  ⟨PositiveDimensions.orient hS.1 o, Brent.replay hS.2 o x⟩

/-- Every arbitrary exact replay witness is sufficient to verify the target Brent equations. -/
theorem ReplayWitness.brent [CommSemiring k]
    {S : MatrixScheme k n₁ n₂ n₃ r} {o : Orientation}
    {T : MatrixScheme k (o.firstDim n₁ n₂ n₃) (o.secondDim n₁ n₂ n₃)
      (o.thirdDim n₁ n₂ n₃) r} (h : ReplayWitness S o T) (hS : S.Brent) : T.Brent := by
  rw [h.target_eq_replay]
  exact Brent.replay hS o h.data

/-- Every arbitrary exact witness transports replay-facing Brent data, including positivity. -/
theorem ReplayWitness.replayableBrent [CommSemiring k] [Nontrivial k]
    {S : MatrixScheme k n₁ n₂ n₃ r} {o : Orientation}
    {T : MatrixScheme k (o.firstDim n₁ n₂ n₃) (o.secondDim n₁ n₂ n₃)
      (o.thirdDim n₁ n₂ n₃) r} (h : ReplayWitness S o T)
    (hS : S.ReplayableBrent) : T.ReplayableBrent :=
  ⟨PositiveDimensions.orient hS.1 o, h.brent hS.2⟩

/-- Action equivalence records the existence of exact replay data and mapped-factor equations;
it is strictly more structured than equality of represented tensors. -/
def ActionEquivalent [CommSemiring k] (S : MatrixScheme k n₁ n₂ n₃ r)
    (o : Orientation)
    (T : MatrixScheme k (o.firstDim n₁ n₂ n₃) (o.secondDim n₁ n₂ n₃)
      (o.thirdDim n₁ n₂ n₃) r) : Prop :=
  Nonempty (ReplayWitness S o T)

/-- A computed replay is action-equivalent to its source by its exact combined witness. -/
theorem replay_actionEquivalent [CommSemiring k] (o : Orientation)
    (S : MatrixScheme k n₁ n₂ n₃ r) (x : Replay (k := k) n₁ n₂ n₃ r o) :
    ActionEquivalent S o (replay o S x) :=
  ⟨replayWitness o S x⟩

/-- Action equivalence transports the exact Brent property to the oriented target. -/
theorem ActionEquivalent.brent [CommSemiring k]
    {S : MatrixScheme k n₁ n₂ n₃ r} {o : Orientation}
    {T : MatrixScheme k (o.firstDim n₁ n₂ n₃) (o.secondDim n₁ n₂ n₃)
      (o.thirdDim n₁ n₂ n₃) r} (h : ActionEquivalent S o T) (hS : S.Brent) : T.Brent := by
  rcases h with ⟨witness⟩
  exact witness.brent hS

/-- Action equivalence transports replay-facing Brent data and its positive-dimension guard. -/
theorem ActionEquivalent.replayableBrent [CommSemiring k] [Nontrivial k]
    {S : MatrixScheme k n₁ n₂ n₃ r} {o : Orientation}
    {T : MatrixScheme k (o.firstDim n₁ n₂ n₃) (o.secondDim n₁ n₂ n₃)
      (o.thirdDim n₁ n₂ n₃) r} (h : ActionEquivalent S o T)
    (hS : S.ReplayableBrent) : T.ReplayableBrent := by
  rcases h with ⟨witness⟩
  exact witness.replayableBrent hS

/-- A sandwich is an isotropy of the matrix-multiplication tensor when it preserves the Brent
property for every ordered decomposition and every presentation length. This property concerns
the ambient tensor, not literal stabilization of one particular ordered scheme. -/
def TensorIsotropy [CommSemiring k] (d : Sandwich k n₁ n₂ n₃) : Prop :=
  ∀ (r : ℕ) (S : MatrixScheme k n₁ n₂ n₃ r), S.Brent → (sandwich S d).Brent

/-- Every sandwich carrying explicit two-sided inverse equations is a tensor isotropy. -/
theorem Sandwich.tensorIsotropy [CommSemiring k] (d : Sandwich k n₁ n₂ n₃) :
    TensorIsotropy d := by
  intro r S hS
  exact BilinearComplexity.Scheme.Action.Brent.sandwich hS d

/-- The identity sandwich is a tensor isotropy in every rectangular shape. -/
example [CommSemiring k] : TensorIsotropy (Sandwich.one k n₁ n₂ n₃) :=
  Sandwich.tensorIsotropy _

/-- Equality of represented tensors, intentionally forgetting ordered term data and allowing
different presentation lengths. -/
def RepresentedEquivalent [CommSemiring k] {r' : ℕ}
    (S : Scheme k a b c r) (T : Scheme k a b c r') : Prop :=
  S.sumTensor = T.sumTensor

/-- Represented equivalence is reflexive. -/
theorem RepresentedEquivalent.refl [CommSemiring k] (S : Scheme k a b c r) :
    RepresentedEquivalent S S := rfl

/-- Ordered stabilizer membership requires literal equality of the replayed ordered scheme,
which is strictly more data than equality of represented tensors. -/
def OrderedStabilizer [CommSemiring k] (S : MatrixScheme k n₁ n₂ n₃ r)
    (x : Replay (k := k) n₁ n₂ n₃ r .abc) : Prop := replay .abc S x = S

/-- Literal ordered stabilization implies represented-tensor equivalence. -/
theorem OrderedStabilizer.representedEquivalent [CommSemiring k]
    (S : MatrixScheme k n₁ n₂ n₃ r) (x : Replay (k := k) n₁ n₂ n₃ r .abc)
    (h : OrderedStabilizer S x) : RepresentedEquivalent (replay .abc S x) S := by
  rw [h]
  exact RepresentedEquivalent.refl S

/-- Identity replay fixes the ordered scheme. -/
theorem replay_one [CommSemiring k] (S : MatrixScheme k n₁ n₂ n₃ r) :
    replay .abc S (Replay.one (k := k) n₁ n₂ n₃ r) = S := by
  simp only [replay, Replay.one, Orientation.firstDim, Orientation.secondDim,
    Orientation.thirdDim]
  rw [show orientMatrix .abc S = S by cases S; rfl]
  rw [show sandwich S (Sandwich.one k n₁ n₂ n₃) = S by
    cases S with
    | mk term =>
      simp only [sandwich, Sandwich.one]
      congr
      funext s
      rcases term s with ⟨u, v, w⟩
      simp only [Prod.mk.injEq]
      constructor
      · rw [Matrix.one_mul, Matrix.mul_one]
        exact (matrixVectorEquiv k n₁ n₂).apply_symm_apply u
      · constructor
        · rw [Matrix.one_mul, Matrix.mul_one]
          exact (matrixVectorEquiv k n₂ n₃).apply_symm_apply v
        · rw [Matrix.one_mul, Matrix.mul_one]
          exact (matrixVectorEquiv k n₃ n₁).apply_symm_apply w]
  cases S
  simp only [gauge, reorder, Scheme.permute, Gauge.one, Units.val_one, one_mul]
  congr

/-- The finite orientation check is executable by ordinary kernel `decide`. -/
example : (Fintype.card Orientation = 6) := by decide

/-- A concrete one-by-one replay check is discharged by the ordinary simplifier. -/
example (S : MatrixScheme ℕ 1 1 1 1) :
    replay .abc S (Replay.one (k := ℕ) 1 1 1 1) = S := by
  simpa only using replay_one S

namespace AsymmetricReplay

/-- The nontrivial unit used by the asymmetric replay fixture over `ZMod 3`. -/
def twoUnit : (ZMod 3)ˣ :=
  ⟨(2 : ZMod 3), 2, by decide, by decide⟩

/-- The nontrivial fixture unit has coefficient two. -/
theorem twoUnit_val : (twoUnit : ZMod 3) = 2 := rfl

/-- The fixture uses the odd `bac` orientation. -/
def orientation : Orientation := .bac

/-- The fixture orientation is literally `bac` and changes `(1,2,1)` to `(2,1,1)`. -/
theorem orientation_eq_bac_and_dims : orientation = .bac ∧
    (orientation.firstDim 1 2 1, orientation.secondDim 1 2 1,
      orientation.thirdDim 1 2 1) = (2, 1, 1) := by
  decide

/-- The asymmetric two-term Brent decomposition of the `1 × 2 × 1` multiplication tensor;
each term scales its first and third factors by two, so its rank-one product is unchanged while
its first and second stored coefficients differ. -/
def source : MatrixScheme (ZMod 3) 1 2 1 2 :=
  ⟨fun s => if s = 0 then (![2, 0], ![1, 0], ![2]) else (![0, 2], ![0, 1], ![2])⟩

/-- The fixture source has the rescaled first matrix-multiplication term in slot zero. -/
theorem source_term_zero : source.term 0 = (![2, 0], ![1, 0], ![2]) := by decide

/-- The fixture source has the rescaled second matrix-multiplication term in slot one. -/
theorem source_term_one : source.term 1 = (![0, 2], ![0, 1], ![2]) := by decide

/-- In both source terms the stored first and second coefficients are genuinely unequal. -/
theorem source_first_ne_second :
    (source.term 0).1 ≠ (source.term 0).2.1 ∧
      (source.term 1).1 ≠ (source.term 1).2.1 := by decide

/-- Rescaling the first and third factors preserves each source rank-one product. -/
theorem source_term_evals_eq_standard :
    (source.term 0).eval = TriadData.eval
        ((![1, 0], ![1, 0], ![1]) : TriadData (ZMod 3) 2 2 1) ∧
      (source.term 1).eval = TriadData.eval
        ((![0, 1], ![0, 1], ![1]) : TriadData (ZMod 3) 2 2 1) := by decide

/-- The nonidentity sandwich used after the odd orientation in the fixture. -/
def sandwichData : Sandwich (ZMod 3) 2 1 1 where
  P := fun i j => if i = Equiv.swap 0 1 j then 1 else 0
  PInv := fun i j => if i = Equiv.swap 0 1 j then 1 else 0
  Q := fun _ _ => 2
  QInv := fun _ _ => 2
  R := fun _ _ => 1
  RInv := fun _ _ => 1
  PInv_mul_P := by
    ext i j
    fin_cases i
    all_goals fin_cases j
    all_goals decide
  P_mul_PInv := by
    ext i j
    fin_cases i
    all_goals fin_cases j
    all_goals decide
  QInv_mul_Q := by
    ext i j
    fin_cases i
    all_goals fin_cases j
    all_goals decide
  Q_mul_QInv := by
    ext i j
    fin_cases i
    all_goals fin_cases j
    all_goals decide
  RInv_mul_R := by
    ext i j
    fin_cases i
    all_goals fin_cases j
    all_goals decide
  R_mul_RInv := by
    ext i j
    fin_cases i
    all_goals fin_cases j
    all_goals decide

/-- The fixture sandwich is genuinely nonidentity in its two-dimensional vertex space. -/
theorem sandwichData_P_ne_one : sandwichData.P ≠ 1 := by
  intro h
  have h00 := congrFun (congrFun h (0 : Fin 2)) (0 : Fin 2)
  norm_num [sandwichData] at h00

/-- The fixture sandwich also uses the nonidentity scalar basis change on its second vertex. -/
theorem sandwichData_Q_ne_one : sandwichData.Q ≠ 1 := by
  intro h
  have h00 := congrFun (congrFun h (0 : Fin 1)) (0 : Fin 1)
  exact (by decide : (2 : ZMod 3) ≠ 1) h00

/-- The nontrivial slot permutation swaps the two fixture terms. -/
def permutation : Fin 2 ≃ Fin 2 := Equiv.swap 0 1

/-- The fixture permutation sends slot zero to slot one. -/
theorem permutation_zero : permutation 0 = 1 := by decide

/-- The fixture permutation is not the identity permutation. -/
theorem permutation_ne_refl : permutation ≠ Equiv.refl (Fin 2) := by
  intro h
  have h0 := congrArg (fun e : Fin 2 ≃ Fin 2 => e (0 : Fin 2)) h
  exact (by decide : (1 : Fin 2) ≠ 0) (permutation_zero.symm.trans h0)

/-- Independently nontrivial product-one gauges for the two target slots. -/
def gauges : Fin 2 → Gauge (ZMod 3) := fun s =>
  if s = 0 then ⟨twoUnit, twoUnit, 1, by
    change twoUnit * twoUnit * 1 = 1
    ext
    decide⟩
  else ⟨twoUnit, 1, twoUnit, by
    change twoUnit * 1 * twoUnit = 1
    ext
    decide⟩

/-- The slot-zero fixture gauge is nonidentity. -/
theorem gauges_zero_ne_one : gauges 0 ≠ Gauge.one (ZMod 3) := by
  intro h
  have hf := congrArg Gauge.first h
  change twoUnit = 1 at hf
  have hv := congrArg (fun u : (ZMod 3)ˣ => (u : ZMod 3)) hf
  exact (by decide : (2 : ZMod 3) ≠ 1) hv

/-- The slot-one fixture gauge is nonidentity. -/
theorem gauges_one_ne_one : gauges 1 ≠ Gauge.one (ZMod 3) := by
  intro h
  have ht := congrArg Gauge.third h
  change twoUnit = 1 at ht
  have hv := congrArg (fun u : (ZMod 3)ˣ => (u : ZMod 3)) ht
  exact (by decide : (2 : ZMod 3) ≠ 1) hv

/-- Complete nonidentity replay data for the odd asymmetric fixture. -/
def data : Replay (k := ZMod 3) 1 2 1 2 orientation :=
  ⟨sandwichData, permutation, gauges⟩

/-- The replay data retains the explicitly checked nonidentity permutation. -/
theorem data_permutation_zero : data.permutation 0 = 1 := permutation_zero

/-- The expected target scheme, written independently of `replay`. -/
def target : MatrixScheme (ZMod 3) 2 1 1 2 :=
  ⟨fun s => if s = 0 then (![2, 0], ![2], ![1, 0]) else (![0, 2], ![1], ![0, 2])⟩

/-- The independently written target has its first explicit mapped term in slot zero. -/
theorem target_term_zero : target.term 0 = (![2, 0], ![2], ![1, 0]) := by decide

/-- The independently written target has its second explicit mapped term in slot one. -/
theorem target_term_one : target.term 1 = (![0, 2], ![1], ![0, 2]) := by decide

/-- Direct finite computation verifies every mapped first-factor equation. -/
theorem mapped_first : ∀ s, (target.term (data.permutation s)).1 =
    fun i => (data.gauges (data.permutation s)).first *
      ((Action.sandwich (orientMatrix orientation source) data.sandwich).term s).1 i := by
  intro s
  fin_cases s <;> ext i <;> fin_cases i <;> decide

/-- Direct finite computation verifies every mapped second-factor equation. -/
theorem mapped_second : ∀ s, (target.term (data.permutation s)).2.1 =
    fun j => (data.gauges (data.permutation s)).second *
      ((Action.sandwich (orientMatrix orientation source) data.sandwich).term s).2.1 j := by
  intro s
  fin_cases s <;> ext j <;> fin_cases j <;> decide

/-- Direct finite computation verifies every mapped third-factor equation. -/
theorem mapped_third : ∀ s, (target.term (data.permutation s)).2.2 =
    fun l => (data.gauges (data.permutation s)).third *
      ((Action.sandwich (orientMatrix orientation source) data.sandwich).term s).2.2 l := by
  intro s
  fin_cases s <;> ext l <;> fin_cases l <;> decide

/-- The independently checked factor equations assemble into an exact asymmetric replay witness. -/
def witness : ReplayWitness source orientation target :=
  ⟨data, mapped_first, mapped_second, mapped_third⟩

/-- The fixture witness stores exactly the declared nonidentity replay data. -/
theorem witness_data : witness.data = data := rfl

/-- The asymmetric explicit target is exactly the computed nonidentity replay. -/
theorem target_eq_replay : target = replay orientation source data :=
  witness.target_eq_replay

/-- The same sandwich, permutation, and gauges, deliberately attached to the even `bca`
orientation for an orientation-ablation check. -/
def bcaData : Replay (k := ZMod 3) 1 2 1 2 .bca :=
  ⟨sandwichData, permutation, gauges⟩

/-- Replacing the intended `bac` reversal by `bca` changes the ordered replay target. -/
theorem target_ne_replay_bca : target ≠ replay .bca source bcaData := by
  intro heq
  let i₀ : Fin (Orientation.bca.firstDim 1 2 1 * Orientation.bca.secondDim 1 2 1) :=
    ⟨0, by decide⟩
  have hentry := congrArg (fun X => (X.term 0).1 i₀) heq
  have htarget : (target.term 0).1 i₀ = 2 := by decide
  have hbca : ((replay .bca source bcaData).term 0).1 i₀ = 1 := by decide
  rw [htarget, hbca] at hentry
  exact (by decide : (2 : ZMod 3) ≠ 1) hentry

/-- The explicit source fixture satisfies positive dimensions and the Brent equations. -/
theorem source_replayableBrent : source.ReplayableBrent := by
  refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
  intro i j j' l l' i'
  fin_cases i
  fin_cases j <;> fin_cases j'
  all_goals fin_cases l; fin_cases l'; fin_cases i'; decide

/-- Exact witness replay preserves the source fixture's Brent equations and positivity. -/
theorem target_replayableBrent : target.ReplayableBrent :=
  witness.replayableBrent source_replayableBrent

end AsymmetricReplay

#check @sandwich
#check @matrixEntry_sandwich_first
#check @matrixEntry_sandwich_second
#check @matrixEntry_sandwich_third
#check @Brent.sandwich
#check @Brent.orientMatrix
#check @Brent.replay
#check @ReplayableBrent.sandwich
#check @ReplayableBrent.orientMatrix
#check @ReplayableBrent.replay
#check @ReplayWitness.target_eq_replay
#check @ReplayWitness.brent
#check @ReplayWitness.replayableBrent
#check @replayWitness
#check @ActionEquivalent.brent
#check @ActionEquivalent.replayableBrent
#check @Sandwich.tensorIsotropy
#check @OrderedStabilizer.representedEquivalent
#check @AsymmetricReplay.orientation_eq_bac_and_dims
#check @AsymmetricReplay.source_first_ne_second
#check @AsymmetricReplay.source_term_evals_eq_standard
#check @AsymmetricReplay.permutation_ne_refl
#check @AsymmetricReplay.sandwichData_P_ne_one
#check @AsymmetricReplay.gauges_zero_ne_one
#check @AsymmetricReplay.mapped_first
#check @AsymmetricReplay.mapped_second
#check @AsymmetricReplay.mapped_third
#check @AsymmetricReplay.target_eq_replay
#check @AsymmetricReplay.bcaData
#check @AsymmetricReplay.target_ne_replay_bca
#check @AsymmetricReplay.target_replayableBrent
#print axioms Brent.sandwich
#print axioms Brent.orientMatrix
#print axioms Brent.replay
#print axioms ReplayableBrent.sandwich
#print axioms ReplayableBrent.orientMatrix
#print axioms ReplayableBrent.replay
#print axioms ReplayWitness.target_eq_replay
#print axioms ReplayWitness.brent
#print axioms ReplayWitness.replayableBrent
#print axioms replayWitness
#print axioms ActionEquivalent.brent
#print axioms ActionEquivalent.replayableBrent
#print axioms Sandwich.tensorIsotropy
#print axioms AsymmetricReplay.orientation_eq_bac_and_dims
#print axioms AsymmetricReplay.source_first_ne_second
#print axioms AsymmetricReplay.source_term_evals_eq_standard
#print axioms AsymmetricReplay.permutation_ne_refl
#print axioms AsymmetricReplay.sandwichData_P_ne_one
#print axioms AsymmetricReplay.gauges_zero_ne_one
#print axioms AsymmetricReplay.mapped_first
#print axioms AsymmetricReplay.mapped_second
#print axioms AsymmetricReplay.mapped_third
#print axioms AsymmetricReplay.target_eq_replay
#print axioms AsymmetricReplay.target_ne_replay_bca
#print axioms AsymmetricReplay.source_replayableBrent
#print axioms AsymmetricReplay.target_replayableBrent

end Action
end Scheme
end BilinearComplexity
