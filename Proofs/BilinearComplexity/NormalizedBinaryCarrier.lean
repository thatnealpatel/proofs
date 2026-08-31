import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.NormNum
import BilinearComplexity.BinaryCircuit
import BilinearComplexity.Support

set_option autoImplicit false

/-!
# Normalized heterogeneous binary tensor carriers

This module gives the finite coordinate carrier

`(𝔽₂^a \ {0}) × (𝔽₂^b \ {0}) × (𝔽₂^c \ {0})`

for an ordered dimension profile `(a,b,c)`.  A carrier point evaluates to its
coordinate rank-one tensor.  Over `𝔽₂`, the absence of nontrivial nonzero
scalars makes this evaluation both nonzero and injective.

The `State` alias records only the intended finite-set semantics.  This module
does not define moves, graphs, occurrence-aware multisets, or bridges to the
ordered full-scheme representation.

AI disclosure: produced with AI assistance (see `Proofs/README`).
-/

namespace BilinearComplexity.NormalizedBinaryCarrier

/-- The binary field used by normalized coordinate carriers. -/
abbrev F2 : Type := ZMod 2

/-- A coordinate vector of dimension `d` over `𝔽₂`. -/
abbrev CoordinateVector (d : ℕ) : Type := Fin d → F2

/-- A nonzero coordinate vector, which is the unique normalized representative
of its projective direction over `𝔽₂`. -/
abbrev NonzeroVector (d : ℕ) : Type := {u : CoordinateVector d // u ≠ 0}

/-- The ordered dimensions of the three factor modes of a heterogeneous tensor. -/
structure Profile where
  first : ℕ
  second : ℕ
  third : ℕ
  deriving DecidableEq, Repr

/-- The homogeneous three-mode profile `(d,d,d)`. -/
def Profile.homogeneous (d : ℕ) : Profile := ⟨d, d, d⟩

/-- The ordered minimal profile `(2,2,1)`. -/
def profile221 : Profile := ⟨2, 2, 1⟩

/-- The ordered minimal profile `(4,1,1)`. -/
def profile411 : Profile := ⟨4, 1, 1⟩

/-- The ordered minimal profile `(3,2,1)`. -/
def profile321 : Profile := ⟨3, 2, 1⟩

/-- The ordered homogeneous profile `(2,2,2)`. -/
def profile222 : Profile := ⟨2, 2, 2⟩

example : (1 : F2) + 1 = 0 := by decide
example : (fun _ : Fin 1 => (1 : F2)) (0 : Fin 1) = 1 := rfl
example : Profile.homogeneous 3 = ⟨3, 3, 3⟩ := rfl
example : profile221 = ⟨2, 2, 1⟩ := rfl
example : profile411 = ⟨4, 1, 1⟩ := rfl
example : profile321 = ⟨3, 2, 1⟩ := rfl
example : profile222 = ⟨2, 2, 2⟩ := rfl

/-- Admissible normalized factor triples for the ordered profile `p`.
Every factor is represented by a nonzero coordinate vector. -/
abbrev Carrier (p : Profile) : Type :=
  NonzeroVector p.first × NonzeroVector p.second × NonzeroVector p.third

/-- A local state has finite-set semantics, so repeated carrier points are not
represented as distinct occurrences. -/
abbrev State (p : Profile) : Type := BinaryCircuit.Scheme (Carrier p)

example (p : Profile) : DecidableEq (Carrier p) := inferInstance
example (p : Profile) : Fintype (Carrier p) := inferInstance
example : (∅ : State profile221) = ∅ := rfl

example : Nonempty (Carrier profile221) := by
  refine ⟨⟨⟨fun _ => 1, ?_⟩, ⟨⟨fun _ => 1, ?_⟩, ⟨fun _ => 1, ?_⟩⟩⟩⟩
  · intro h
    have h0 := congrFun h (0 : Fin 2)
    exact one_ne_zero h0
  · intro h
    have h0 := congrFun h (0 : Fin 2)
    exact one_ne_zero h0
  · intro h
    have h0 := congrFun h (0 : Fin 1)
    exact one_ne_zero h0

/-- Coordinate evaluation of a normalized factor triple as a rank-one tensor. -/
def tensorEvaluation {p : Profile} (t : Carrier p) :
    Tensor F2 p.first p.second p.third :=
  triad t.1.1 t.2.1.1 t.2.2.1

/-- Coordinate evaluation is the existing `triad` construction on the three
underlying factor vectors. -/
theorem tensorEvaluation_eq_triad {p : Profile} (t : Carrier p) :
    tensorEvaluation t = triad t.1.1 t.2.1.1 t.2.2.1 :=
  rfl

/-- State evaluation is the abstract binary-circuit evaluation specialized to
normalized coordinate tensors. -/
def stateEvaluation {p : Profile} (D : State p) :
    Tensor F2 p.first p.second p.third :=
  BinaryCircuit.evaluation tensorEvaluation D

/-- Specialized state evaluation is the finite sum of coordinate tensor
values over the state. -/
@[simp] theorem stateEvaluation_eq_sum {p : Profile} (D : State p) :
    stateEvaluation D = ∑ t ∈ D, tensorEvaluation t :=
  rfl

/-- Entrywise formula for coordinate tensor evaluation. -/
@[simp] theorem tensorEvaluation_apply {p : Profile} (t : Carrier p)
    (i : Fin p.first) (j : Fin p.second) (k : Fin p.third) :
    tensorEvaluation t i j k = t.1.1 i * t.2.1.1 j * t.2.2.1 k :=
  rfl

/-- A coordinate tensor evaluated from an admissible triple is nonzero. -/
theorem tensorEvaluation_ne_zero {p : Profile} (t : Carrier p) :
    tensorEvaluation t ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp t.1.2
  obtain ⟨j, hj⟩ := Function.ne_iff.mp t.2.1.2
  obtain ⟨k, hk⟩ := Function.ne_iff.mp t.2.2.2
  intro hzero
  have hijk := congrFun (congrFun (congrFun hzero i) j) k
  have hprod : t.1.1 i * t.2.1.1 j * t.2.2.1 k ≠ 0 :=
    mul_ne_zero (mul_ne_zero hi hj) hk
  exact hprod (by simpa using hijk)

private theorem eq_one_of_ne_zero (x : F2) (hx : x ≠ 0) : x = 1 := by
  have hxval : x.val < 2 := ZMod.val_lt x
  have hval : x.val = 0 ∨ x.val = 1 := by omega
  rcases hval with hval | hval
  · apply False.elim
    apply hx
    apply ZMod.val_injective
    simpa using hval
  · apply ZMod.val_injective
    change x.val = 1
    exact hval

/-- Coordinate evaluation is injective on normalized binary factor triples. -/
theorem tensorEvaluation_injective {p : Profile} :
    Function.Injective (@tensorEvaluation p) := by
  intro s t hst
  obtain ⟨i, hi⟩ := Function.ne_iff.mp s.1.2
  obtain ⟨j, hj⟩ := Function.ne_iff.mp s.2.1.2
  obtain ⟨k, hk⟩ := Function.ne_iff.mp s.2.2.2
  have hsi : s.1.1 i = 1 := eq_one_of_ne_zero _ hi
  have hsj : s.2.1.1 j = 1 := eq_one_of_ne_zero _ hj
  have hsk : s.2.2.1 k = 1 := eq_one_of_ne_zero _ hk
  have hbase := congrFun (congrFun (congrFun hst i) j) k
  have htprod : t.1.1 i * t.2.1.1 j * t.2.2.1 k = 1 := by
    simpa [hsi, hsj, hsk] using hbase.symm
  have htij : t.1.1 i * t.2.1.1 j = 1 := (mul_eq_one.mp htprod).1
  have hti : t.1.1 i = 1 := (mul_eq_one.mp htij).1
  have htj : t.2.1.1 j = 1 := (mul_eq_one.mp htij).2
  have htk : t.2.2.1 k = 1 := (mul_eq_one.mp htprod).2
  have hfirst : s.1.1 = t.1.1 := by
    funext i'
    have hi' := congrFun (congrFun (congrFun hst i') j) k
    simpa [hsj, hsk, htj, htk] using hi'
  have hsecond : s.2.1.1 = t.2.1.1 := by
    funext j'
    have hj' := congrFun (congrFun (congrFun hst i) j') k
    simpa [hsi, hsk, hti, htk] using hj'
  have hthird : s.2.2.1 = t.2.2.1 := by
    funext k'
    have hk' := congrFun (congrFun (congrFun hst i) j) k'
    simpa [hsi, hsj, hti, htj] using hk'
  apply Prod.ext
  · exact Subtype.ext hfirst
  · apply Prod.ext
    · exact Subtype.ext hsecond
    · exact Subtype.ext hthird

/-- The number of nonzero binary coordinate vectors plus the omitted zero
vector is `2^d`.  The additive form avoids totalized natural subtraction at
dimension zero. -/
theorem card_nonzeroVector_add_one (d : ℕ) :
    Fintype.card (NonzeroVector d) + 1 = 2 ^ d := by
  rw [Fintype.card_subtype_compl (fun u : CoordinateVector d => u = 0)]
  have hpow : 1 ≤ 2 ^ d := Nat.one_le_pow d 2 (by omega)
  simp only [CoordinateVector, F2, Fintype.card_fun, Fintype.card_fin,
    ZMod.card, Fintype.card_subtype_eq]
  omega

/-- There is one nonzero binary coordinate vector in dimension one. -/
theorem card_nonzeroVector_one : Fintype.card (NonzeroVector 1) = 1 := by
  have hcard := card_nonzeroVector_add_one 1
  norm_num at hcard ⊢

/-- There are three nonzero binary coordinate vectors in dimension two. -/
theorem card_nonzeroVector_two : Fintype.card (NonzeroVector 2) = 3 := by
  have hcard := card_nonzeroVector_add_one 2
  norm_num at hcard ⊢

/-- There are seven nonzero binary coordinate vectors in dimension three. -/
theorem card_nonzeroVector_three : Fintype.card (NonzeroVector 3) = 7 := by
  have hcard := card_nonzeroVector_add_one 3
  norm_num at hcard ⊢

/-- There are fifteen nonzero binary coordinate vectors in dimension four. -/
theorem card_nonzeroVector_four : Fintype.card (NonzeroVector 4) = 15 := by
  have hcard := card_nonzeroVector_add_one 4
  norm_num at hcard ⊢

/-- The normalized carrier cardinality is the product of the three factor
carrier cardinalities. -/
theorem card_carrier (p : Profile) :
    Fintype.card (Carrier p) =
      Fintype.card (NonzeroVector p.first) *
        Fintype.card (NonzeroVector p.second) *
          Fintype.card (NonzeroVector p.third) := by
  simp only [Carrier, Fintype.card_prod, mul_assoc]

/-- A homogeneous dimension-`d` carrier has the cube of the nonzero-vector
cardinality. -/
theorem card_homogeneous (d : ℕ) :
    Fintype.card (Carrier (Profile.homogeneous d)) =
      Fintype.card (NonzeroVector d) ^ 3 := by
  rw [card_carrier]
  simp only [Profile.homogeneous, pow_succ, pow_zero, one_mul, mul_assoc]
  rfl

/-- The `(2,2,1)` carrier has `9` points. -/
theorem card_profile221 : Fintype.card (Carrier profile221) = 9 := by
  rw [card_carrier]
  norm_num [profile221, card_nonzeroVector_one, card_nonzeroVector_two]

/-- The `(4,1,1)` carrier has `15` points. -/
theorem card_profile411 : Fintype.card (Carrier profile411) = 15 := by
  rw [card_carrier]
  norm_num [profile411, card_nonzeroVector_one, card_nonzeroVector_four]

/-- The `(3,2,1)` carrier has `21` points. -/
theorem card_profile321 : Fintype.card (Carrier profile321) = 21 := by
  rw [card_carrier]
  norm_num [profile321, card_nonzeroVector_one, card_nonzeroVector_two,
    card_nonzeroVector_three]

/-- The `(2,2,2)` carrier has `27` points. -/
theorem card_profile222 : Fintype.card (Carrier profile222) = 27 := by
  rw [card_carrier]
  norm_num [profile222, card_nonzeroVector_two]

/-- The homogeneous dimension-two carrier has `27` points. -/
theorem card_homogeneous_two :
    Fintype.card (Carrier (Profile.homogeneous 2)) = 27 := by
  calc
    Fintype.card (Carrier (Profile.homogeneous 2)) =
        Fintype.card (NonzeroVector 2) ^ 3 := card_homogeneous 2
    _ = 27 := by rw [card_nonzeroVector_two]; norm_num

/-- The homogeneous dimension-three carrier has `343` points. -/
theorem card_homogeneous_three :
    Fintype.card (Carrier (Profile.homogeneous 3)) = 343 := by
  calc
    Fintype.card (Carrier (Profile.homogeneous 3)) =
        Fintype.card (NonzeroVector 3) ^ 3 := card_homogeneous 3
    _ = 343 := by rw [card_nonzeroVector_three]; norm_num

example : Fintype.card (Carrier (Profile.homogeneous 0)) = 0 := by
  rw [card_homogeneous]
  have hcard := card_nonzeroVector_add_one 0
  norm_num at hcard ⊢

example : Nonempty (Carrier (Profile.homogeneous 3)) := by
  apply Fintype.card_pos_iff.mp
  rw [card_homogeneous_three]
  omega

#check @Profile.homogeneous
#check @Carrier
#check @tensorEvaluation
#check @tensorEvaluation_ne_zero
#check @tensorEvaluation_injective
#check @card_nonzeroVector_add_one
#check @card_carrier
#check @card_homogeneous

#print axioms tensorEvaluation_ne_zero
#print axioms tensorEvaluation_injective
#print axioms card_carrier
#print axioms card_homogeneous_three

end BilinearComplexity.NormalizedBinaryCarrier
