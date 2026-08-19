/-
  Scratch/FlipQuantum/Phase1Schemes — exact indexed schemes and flip-graph foundations.

  Schemes remain indexed so that moves have explicit term positions.  Paper-facing
  vertices additionally require positive size, nonzero and pairwise distinct evaluated
  rank-one tensors, and an exact tensor sum.  Elementary flips are invariant under
  refactorization of a rank-one tensor by nonzero scalar rescaling.
-/
import Mathlib
import BilinearComplexity.Peeling

set_option autoImplicit false

namespace BilinearComplexity.FlipQuantum

variable {k : Type*} {a b c r : ℕ}

/-- An `r`-term indexed decomposition stores one triad at every index in `Fin r`.
Indices are retained as data and are not quotiented by permutations or symmetries. -/
structure Scheme (k : Type*) (a b c r : ℕ) where
  term : Fin r → BilinearComplexity.TriadData k a b c

namespace Scheme

variable [CommSemiring k]

/-- The tensor represented by an indexed scheme is the pointwise sum of its triads. -/
def sumTensor (S : Scheme k a b c r) : BilinearComplexity.Tensor k a b c :=
  fun i j l => ∑ s, (S.term s).eval i j l

/-- A term is nonzero when its evaluated rank-one tensor is not the zero tensor. -/
def TermNonzero (S : Scheme k a b c r) (s : Fin r) : Prop :=
  (S.term s).eval ≠ 0

/-- A scheme is valid for `T` when its sum is `T`, every evaluated triad is nonzero,
and distinct indices evaluate to distinct rank-one tensors.  The last condition makes
the indexed presentation faithful to the paper's finite-set cardinality. -/
def Valid (T : BilinearComplexity.Tensor k a b c) (S : Scheme k a b c r) : Prop :=
  S.sumTensor = T ∧ (∀ s, S.TermNonzero s) ∧
    Function.Injective (fun s => (S.term s).eval)

/-- Every indexed scheme gives an explicit rank-at-most-`r` witness for its sum. -/
theorem rankLE_sumTensor (S : Scheme k a b c r) :
    BilinearComplexity.RankLE S.sumTensor r := by
  refine ⟨fun s => (S.term s).1, fun s => (S.term s).2.1,
    fun s => (S.term s).2.2, ?_⟩
  rfl

/-- Validity exposes the stored factors as an exact `RankLE T r` witness. -/
theorem Valid.rankLE {T : BilinearComplexity.Tensor k a b c}
    {S : Scheme k a b c r} (hS : S.Valid T) : BilinearComplexity.RankLE T r := by
  rw [← hS.1]
  exact S.rankLE_sumTensor

/-- A zero-term indexed scheme is valid exactly for the zero tensor. -/
theorem valid_zero_iff (T : BilinearComplexity.Tensor k a b c)
    (S : Scheme k a b c 0) : S.Valid T ↔ T = 0 := by
  have hsum : S.sumTensor = 0 := by
    funext i j l
    simp [sumTensor]
  constructor
  · intro hS
    rw [← hS.1]
    exact hsum
  · intro hT
    refine ⟨hsum.trans hT.symm, ?_, ?_⟩
    · exact fun s => Fin.elim0 s
    · exact fun s => Fin.elim0 s

/-- A positive-size valid scheme cannot have an empty first tensor mode. -/
theorem not_valid_of_first_mode_empty (hr : 0 < r)
    (T : BilinearComplexity.Tensor k 0 b c) (S : Scheme k 0 b c r) :
    ¬ S.Valid T := by
  intro hS
  let s : Fin r := ⟨0, hr⟩
  have hzero : (S.term s).eval = 0 := by
    funext i
    exact Fin.elim0 i
  exact hS.2.1 s hzero

/-- A positive-size valid scheme cannot have an empty second tensor mode. -/
theorem not_valid_of_second_mode_empty (hr : 0 < r)
    (T : BilinearComplexity.Tensor k a 0 c) (S : Scheme k a 0 c r) :
    ¬ S.Valid T := by
  intro hS
  let s : Fin r := ⟨0, hr⟩
  have hzero : (S.term s).eval = 0 := by
    funext i j
    exact Fin.elim0 j
  exact hS.2.1 s hzero

/-- A positive-size valid scheme cannot have an empty third tensor mode. -/
theorem not_valid_of_third_mode_empty (hr : 0 < r)
    (T : BilinearComplexity.Tensor k a b 0) (S : Scheme k a b 0 r) :
    ¬ S.Valid T := by
  intro hS
  let s : Fin r := ⟨0, hr⟩
  have hzero : (S.term s).eval = 0 := by
    funext i j l
    exact Fin.elim0 l
  exact hS.2.1 s hzero

/-- A paper-facing graph vertex is a positive-size valid exact scheme. -/
def GraphVertex (T : BilinearComplexity.Tensor k a b c)
    (S : Scheme k a b c r) : Prop :=
  0 < r ∧ S.Valid T

end Scheme

section Projective

variable [Field k] {ι : Type*}

/-- Two vectors are projectively equal when one is a nonzero scalar multiple of the other. -/
def ProjectivelyEqual (x y : ι → k) : Prop :=
  ∃ q : k, q ≠ 0 ∧ y = q • x

/-- Literal equality implies projective equality. -/
theorem projectivelyEqual_of_eq {x y : ι → k} (hxy : x = y) :
    ProjectivelyEqual x y := by
  refine ⟨1, one_ne_zero, ?_⟩
  simpa only [one_smul] using hxy.symm

/-- Every vector is projectively equal to itself. -/
theorem projectivelyEqual_refl (x : ι → k) : ProjectivelyEqual x x :=
  projectivelyEqual_of_eq rfl

end Projective

namespace Scheme

variable [Field k]

/-- Two indexed presentations represent the same rank-one tensor at every index. -/
def SameTensors (S R : Scheme k a b c r) : Prop :=
  ∀ s, (S.term s).eval = (R.term s).eval

/-- Tensorwise presentation equivalence is reflexive. -/
theorem sameTensors_refl (S : Scheme k a b c r) : S.SameTensors S :=
  fun _ => rfl

/-- Raw first-mode shear.  Distinctness and a shared first factor are imposed by
`RawElementaryFlip`, not by this update operation. -/
def flipFirst (S : Scheme k a b c r) (i j : Fin r) (q : k) : Scheme k a b c r :=
  let ti := S.term i
  let tj := S.term j
  let ti' : BilinearComplexity.TriadData k a b c :=
    (ti.1, ti.2.1 + q • tj.2.1, ti.2.2)
  let tj' : BilinearComplexity.TriadData k a b c :=
    (tj.1, tj.2.1, tj.2.2 - q • ti.2.2)
  ⟨Function.update (Function.update S.term i ti') j tj'⟩

/-- Raw second-mode shear, intended for distinct indices sharing a second factor. -/
def flipSecond (S : Scheme k a b c r) (i j : Fin r) (q : k) : Scheme k a b c r :=
  let ti := S.term i
  let tj := S.term j
  let ti' : BilinearComplexity.TriadData k a b c :=
    (ti.1 + q • tj.1, ti.2.1, ti.2.2)
  let tj' : BilinearComplexity.TriadData k a b c :=
    (tj.1, tj.2.1, tj.2.2 - q • ti.2.2)
  ⟨Function.update (Function.update S.term i ti') j tj'⟩

/-- Raw third-mode shear, intended for distinct indices sharing a third factor. -/
def flipThird (S : Scheme k a b c r) (i j : Fin r) (q : k) : Scheme k a b c r :=
  let ti := S.term i
  let tj := S.term j
  let ti' : BilinearComplexity.TriadData k a b c :=
    (ti.1 + q • tj.1, ti.2.1, ti.2.2)
  let tj' : BilinearComplexity.TriadData k a b c :=
    (tj.1, tj.2.1 - q • ti.2.1, tj.2.2)
  ⟨Function.update (Function.update S.term i ti') j tj'⟩

/-- A raw elementary flip is a literal shared-factor shear on one presentation. -/
inductive RawElementaryFlip : Scheme k a b c r → Scheme k a b c r → Prop
  /-- A first-mode raw flip shears the second and third factors. -/
  | first (S : Scheme k a b c r) (i j : Fin r) (q : k)
      (hij : i ≠ j) (hq : q ≠ 0) (hshared : (S.term i).1 = (S.term j).1) :
      RawElementaryFlip S (flipFirst S i j q)
  /-- A second-mode raw flip shears the first and third factors. -/
  | second (S : Scheme k a b c r) (i j : Fin r) (q : k)
      (hij : i ≠ j) (hq : q ≠ 0) (hshared : (S.term i).2.1 = (S.term j).2.1) :
      RawElementaryFlip S (flipSecond S i j q)
  /-- A third-mode raw flip shears the first and second factors. -/
  | third (S : Scheme k a b c r) (i j : Fin r) (q : k)
      (hij : i ≠ j) (hq : q ≠ 0) (hshared : (S.term i).2.2 = (S.term j).2.2) :
      RawElementaryFlip S (flipThird S i j q)

/-- An elementary paper flip permits nonzero scalar refactorization before applying
a literal shared-factor shear, so it depends on rank-one tensors rather than stored gauges. -/
def ElementaryFlip (S S' : Scheme k a b c r) : Prop :=
  ∃ R R' : Scheme k a b c r,
    S.SameTensors R ∧ S'.SameTensors R' ∧ RawElementaryFlip R R'

/-- A valid flip edge joins positive-size valid schemes for one tensor by an elementary flip. -/
def Flip (T : BilinearComplexity.Tensor k a b c)
    (S S' : Scheme k a b c r) : Prop :=
  S.GraphVertex T ∧ S'.GraphVertex T ∧ ElementaryFlip S S'

/-- A selected family is reducible in an ordered pair of modes when it is nonempty,
its first family is projectively common, and its second family is linearly dependent. -/
def ReducibleFamily {ι κ : Type*} (x : Fin r → ι → k) (y : Fin r → κ → k) : Prop :=
  ∃ I : Finset (Fin r), I.Nonempty ∧
    (∃ p : Fin r, p ∈ I ∧ ∀ i : Fin r, i ∈ I → ProjectivelyEqual (x p) (x i)) ∧
    ¬ LinearIndependent k (fun i : {i : Fin r // i ∈ I} => y i.1)

/-- A graph vertex is reducible when a nonempty selected family satisfies the paper's
common-factor/dependent-factor condition in one of the six ordered mode pairs. -/
def Reducible (T : BilinearComplexity.Tensor k a b c) (S : Scheme k a b c r) : Prop :=
  S.GraphVertex T ∧
    (ReducibleFamily (fun s => (S.term s).1) (fun s => (S.term s).2.1) ∨
     ReducibleFamily (fun s => (S.term s).1) (fun s => (S.term s).2.2) ∨
     ReducibleFamily (fun s => (S.term s).2.1) (fun s => (S.term s).1) ∨
     ReducibleFamily (fun s => (S.term s).2.1) (fun s => (S.term s).2.2) ∨
     ReducibleFamily (fun s => (S.term s).2.2) (fun s => (S.term s).1) ∨
     ReducibleFamily (fun s => (S.term s).2.2) (fun s => (S.term s).2.1))

/-- Flip reachability requires valid endpoints and a reflexive-transitive chain of valid edges. -/
def Reachable (T : BilinearComplexity.Tensor k a b c)
    (S S' : Scheme k a b c r) : Prop :=
  S.GraphVertex T ∧ S'.GraphVertex T ∧ Relation.ReflTransGen (Flip T) S S'

/-- Every graph vertex is flip-reachable from itself. -/
theorem reachable_refl {T : BilinearComplexity.Tensor k a b c}
    {S : Scheme k a b c r} (hS : S.GraphVertex T) : Reachable T S S :=
  ⟨hS, hS, Relation.ReflTransGen.refl⟩

/-- Flip reachability is transitive. -/
theorem Reachable.trans {T : BilinearComplexity.Tensor k a b c}
    {S₁ S₂ S₃ : Scheme k a b c r}
    (h₁₂ : Reachable T S₁ S₂) (h₂₃ : Reachable T S₂ S₃) :
    Reachable T S₁ S₃ :=
  ⟨h₁₂.1, h₂₃.2.1, Relation.ReflTransGen.trans h₁₂.2.2 h₂₃.2.2⟩

/-- A valid flip edge supplies an exact rank-at-most-`r` witness for its tensor. -/
theorem Flip.rankLE {T : BilinearComplexity.Tensor k a b c}
    {S S' : Scheme k a b c r} (hflip : Flip T S S') :
    BilinearComplexity.RankLE T r :=
  hflip.1.2.rankLE

/-- No raw elementary flip exists at level zero. -/
theorem not_rawElementaryFlip_zero (S S' : Scheme k a b c 0) :
    ¬ RawElementaryFlip S S' := by
  intro hflip
  cases hflip <;> rename_i i j q hij hq hshared <;> exact Fin.elim0 i

/-- No elementary paper flip exists at level zero. -/
theorem not_elementaryFlip_zero (S S' : Scheme k a b c 0) :
    ¬ ElementaryFlip S S' := by
  rintro ⟨R, R', _hR, _hR', hflip⟩
  exact not_rawElementaryFlip_zero R R' hflip

/-- No zero-term scheme is a paper graph vertex. -/
theorem not_graphVertex_zero (T : BilinearComplexity.Tensor k a b c)
    (S : Scheme k a b c 0) : ¬ S.GraphVertex T := by
  intro hS
  exact (Nat.not_lt_zero 0) hS.1

/-- No zero-term scheme is reducible. -/
theorem not_reducible_zero (T : BilinearComplexity.Tensor k a b c)
    (S : Scheme k a b c 0) : ¬ S.Reducible T := by
  intro hS
  exact not_graphVertex_zero T S hS.1

end Scheme

/-! Ground and boundary checks. -/

example :
    let S : Scheme ℚ 1 1 1 1 :=
      ⟨fun _ => (fun _ => 1, fun _ => 1, fun _ => 1)⟩
    S.GraphVertex (fun _ _ _ => 1) := by
  dsimp [Scheme.GraphVertex, Scheme.Valid, Scheme.sumTensor, Scheme.TermNonzero]
  refine ⟨by omega, ?_, ?_, ?_⟩
  · funext i j l
    change (∑ _s : Fin 1, (1 : ℚ) * 1 * 1) = 1
    norm_num
  · intro s hzero
    have hone := congrFun (congrFun (congrFun hzero 0) 0) 0
    norm_num [BilinearComplexity.TriadData.eval, BilinearComplexity.triad] at hone
  · intro x y _hxy
    exact Subsingleton.elim x y

example :
    ProjectivelyEqual (fun _ : Fin 1 => (1 : ℚ)) (fun _ : Fin 1 => (2 : ℚ)) := by
  refine ⟨2, by norm_num, ?_⟩
  funext x
  norm_num

example :
    let i : Fin 2 := 0
    let j : Fin 2 := 1
    let S : Scheme ℚ 1 1 1 2 :=
      ⟨fun s => (fun _ => 1, fun _ => 1, fun _ => if s = i then 1 else 2)⟩
    let S' := S.flipFirst i j 1
    Scheme.ElementaryFlip S S' := by
  dsimp
  refine ⟨_, _, Scheme.sameTensors_refl _, Scheme.sameTensors_refl _, ?_⟩
  exact Scheme.RawElementaryFlip.first _ 0 1 1 (by decide) (by norm_num) rfl

example :
    let i : Fin 2 := 0
    let S : Scheme ℚ 1 1 1 2 :=
      ⟨fun s => (fun _ => 1, fun _ => 1, fun _ => if s = i then 1 else 2)⟩
    let T : BilinearComplexity.Tensor ℚ 1 1 1 := fun _ _ _ => 3
    S.Reducible T := by
  dsimp [Scheme.Reducible, Scheme.GraphVertex, Scheme.Valid, Scheme.sumTensor,
    Scheme.TermNonzero, Scheme.ReducibleFamily]
  refine ⟨⟨by omega, ?_, ?_, ?_⟩, Or.inl ?_⟩
  · funext x y z
    change (∑ s : Fin 2, (1 : ℚ) * 1 * if s = 0 then 1 else 2) = 3
    norm_num [Fin.sum_univ_two]
  · intro s hzero
    fin_cases s
    · have hone := congrFun (congrFun (congrFun hzero 0) 0) 0
      norm_num [BilinearComplexity.TriadData.eval, BilinearComplexity.triad] at hone
    · have htwo := congrFun (congrFun (congrFun hzero 0) 0) 0
      norm_num [BilinearComplexity.TriadData.eval, BilinearComplexity.triad] at htwo
  · intro x y hxy
    fin_cases x <;> fin_cases y
    · rfl
    · have hentry := congrFun (congrFun (congrFun hxy 0) 0) 0
      norm_num [BilinearComplexity.TriadData.eval, BilinearComplexity.triad] at hentry
    · have hentry := congrFun (congrFun (congrFun hxy 0) 0) 0
      norm_num [BilinearComplexity.TriadData.eval, BilinearComplexity.triad] at hentry
    · rfl
  · let I : Finset (Fin 2) := Finset.univ
    refine ⟨I, Finset.univ_nonempty, ?_, ?_⟩
    · refine ⟨0, Finset.mem_univ _, ?_⟩
      intro s _hs
      exact projectivelyEqual_of_eq rfl
    · intro hli
      have hinj := hli.injective
      let x : {s : Fin 2 // s ∈ I} := ⟨0, Finset.mem_univ _⟩
      let y : {s : Fin 2 // s ∈ I} := ⟨1, Finset.mem_univ _⟩
      have hxy : x = y := hinj rfl
      have hval := congrArg (fun s => (s.1 : Fin 2).val) hxy
      norm_num [x, y] at hval

example {T : BilinearComplexity.Tensor ℚ 1 1 1} {S : Scheme ℚ 1 1 1 1}
    (hS : S.GraphVertex T) : S.Reachable T S :=
  Scheme.reachable_refl hS

example (T : BilinearComplexity.Tensor ℚ 0 1 1) (S : Scheme ℚ 0 1 1 1) :
    ¬ S.Valid T :=
  Scheme.not_valid_of_first_mode_empty (by omega) T S

example (T : BilinearComplexity.Tensor ℚ 1 1 1) (S : Scheme ℚ 1 1 1 0) :
    ¬ S.GraphVertex T :=
  Scheme.not_graphVertex_zero T S

#check @Scheme.rankLE_sumTensor
#check @Scheme.Valid.rankLE
#check @Scheme.valid_zero_iff
#check @Scheme.not_valid_of_first_mode_empty
#check @Scheme.not_valid_of_second_mode_empty
#check @Scheme.not_valid_of_third_mode_empty
#check @projectivelyEqual_of_eq
#check @projectivelyEqual_refl
#check @Scheme.sameTensors_refl
#check @Scheme.RawElementaryFlip.first
#check @Scheme.Reducible
#check @Scheme.reachable_refl
#check @Scheme.Reachable.trans
#check @Scheme.Flip.rankLE
#check @Scheme.not_rawElementaryFlip_zero
#check @Scheme.not_elementaryFlip_zero
#check @Scheme.not_graphVertex_zero
#check @Scheme.not_reducible_zero

#print axioms Scheme.rankLE_sumTensor
#print axioms Scheme.Valid.rankLE
#print axioms Scheme.valid_zero_iff
#print axioms Scheme.not_valid_of_first_mode_empty
#print axioms Scheme.not_valid_of_second_mode_empty
#print axioms Scheme.not_valid_of_third_mode_empty
#print axioms projectivelyEqual_of_eq
#print axioms projectivelyEqual_refl
#print axioms Scheme.sameTensors_refl
#print axioms Scheme.reachable_refl
#print axioms Scheme.Reachable.trans
#print axioms Scheme.Flip.rankLE
#print axioms Scheme.not_rawElementaryFlip_zero
#print axioms Scheme.not_elementaryFlip_zero
#print axioms Scheme.not_graphVertex_zero
#print axioms Scheme.not_reducible_zero

end BilinearComplexity.FlipQuantum
