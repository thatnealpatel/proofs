import BilinearComplexity.Scheme
import Mathlib.Data.Multiset.Basic
import Mathlib.Logic.Relation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false

/-!
# A directed-Forward counterexample for adaptive Plus

Arai--Ichikawa--Hukushima, arXiv:2312.16960v2, Definition 2.4, uses finite
multisets of rank-one terms. Definitions 2.5, 2.6, and 4.1 respectively make
Flip cardinality-preserving, Reduction cardinality-decreasing, and Plus
cardinality-increasing by one. Plus selects two occurrences whose factors
differ in all three positions.

`ForwardStep` is a deliberately larger relation than the literal moves: it
retains exact tensor preservation, the full Plus selection premise, and the
three cardinality effects, but forgets the Flip, Reduction, and Plus payload
formulas. Consequently, nonreachability for `ForwardStep` implies
nonreachability for any exact implementation proved to be its subrelation;
`no_forward_path_of_subrelation` records this implication. This module does
not claim to refute connectivity after symmetrizing the paper's ordered edge
pairs.
-/

namespace BilinearComplexity
namespace AdaptivePlusCounterexample

/-- The finite-multiset carrier of a paper scheme, storing factorized nonzero rank-one terms.
The separate predicate `IsMatrixMultiplicationScheme` imposes the required represented sum. -/
structure PaperScheme (k : Type*) [CommSemiring k] (a b c : ℕ) where
  /-- The finite multiset of rank-one factor triples. -/
  terms : Multiset (TriadData k a b c)
  /-- Every occurrence evaluates to a nonzero rank-one tensor. -/
  term_nonzero : ∀ t, t ∈ terms → t.eval ≠ 0

namespace PaperScheme

variable {k : Type*} [CommSemiring k] {a b c : ℕ}

/-- The tensor represented by a paper scheme is the sum, with multiplicity, of its terms. -/
def representedTensor (S : PaperScheme k a b c) : Tensor k a b c :=
  (S.terms.map fun t => t.eval).sum

/-- The size of a paper scheme counts terms with multiplicity. -/
def card (S : PaperScheme k a b c) : ℕ :=
  S.terms.card

example (S : PaperScheme k a b c) :
    S.representedTensor = (S.terms.map fun t => t.eval).sum := rfl

example (S : PaperScheme k a b c) : S.card = S.terms.card := rfl

end PaperScheme

/-- A carrier is an `(n,m,p)` matrix-multiplication scheme when its represented sum is the
repository's row-major matrix-multiplication tensor. -/
def IsMatrixMultiplicationScheme {k : Type*} [CommSemiring k] (n m p : ℕ)
    (S : PaperScheme k (n * m) (m * p) (p * n)) : Prop :=
  S.representedTensor = matMulTensor k n m p

/-- The scheme predicate is exactly the represented-tensor equality from Definition 2.4. -/
theorem isMatrixMultiplicationScheme_iff {k : Type*} [CommSemiring k] (n m p : ℕ)
    (S : PaperScheme k (n * m) (m * p) (p * n)) :
    IsMatrixMultiplicationScheme n m p S ↔
      S.representedTensor = matMulTensor k n m p :=
  Iff.rfl

/-- The two-element field used by the witness. -/
abbrev F₂ := ZMod 2

/-- The unique all-one rank-one term in the `(1,1,1)` witness. -/
def unitTriad : TriadData F₂ 1 1 1 :=
  (fun _ => 1, fun _ => 1, fun _ => 1)

example : unitTriad.eval 0 0 0 = 1 := by
  rfl

/-- The all-one witness term evaluates to a nonzero tensor. -/
theorem unitTriad_eval_ne_zero : unitTriad.eval ≠ 0 := by
  intro hzero
  have hentry := congrFun (congrFun (congrFun hzero 0) 0) 0
  norm_num [unitTriad, TriadData.eval, triad] at hentry

/-- The one-term scheme for the `(1,1,1)` matrix-multiplication tensor over `F₂`. -/
def source : PaperScheme F₂ 1 1 1 where
  terms := {unitTriad}
  term_nonzero := by
    intro t ht
    simpa only [Multiset.mem_singleton.mp ht] using unitTriad_eval_ne_zero

/-- The three-copy scheme for the `(1,1,1)` matrix-multiplication tensor over `F₂`. -/
def target : PaperScheme F₂ 1 1 1 where
  terms := unitTriad ::ₘ unitTriad ::ₘ {unitTriad}
  term_nonzero := by
    intro t ht
    simp only [Multiset.mem_cons, Multiset.mem_singleton] at ht
    rcases ht with ht | ht | ht
    · simpa only [ht] using unitTriad_eval_ne_zero
    · simpa only [ht] using unitTriad_eval_ne_zero
    · simpa only [ht] using unitTriad_eval_ne_zero

example : source.card = 1 := by
  rfl

example : target.card = 3 := by
  rfl

/-- The source represents the `(1,1,1)` matrix-multiplication tensor over `F₂`. -/
theorem source_represents_matMul :
    source.representedTensor = matMulTensor F₂ 1 1 1 := by
  funext i j l
  fin_cases i
  fin_cases j
  fin_cases l
  norm_num [PaperScheme.representedTensor, source, unitTriad,
    TriadData.eval, triad, matMulTensor]
  exact Subsingleton.elim _ _

/-- The target represents the `(1,1,1)` matrix-multiplication tensor over `F₂`; here the
pointwise scalar identity is `1 + 1 + 1 = 1` in `F₂`. -/
theorem target_represents_matMul :
    target.representedTensor = matMulTensor F₂ 1 1 1 := by
  funext i j l
  fin_cases i
  fin_cases j
  fin_cases l
  norm_num [PaperScheme.representedTensor, target, unitTriad,
    TriadData.eval, triad, matMulTensor]
  rw [if_pos (Subsingleton.elim _ _)]
  change (3 : F₂) = 1
  decide

/-- The source satisfies the paper's matrix-multiplication-scheme sum premise. -/
theorem source_isMatrixMultiplicationScheme :
    IsMatrixMultiplicationScheme 1 1 1 source :=
  source_represents_matMul

/-- The target satisfies the paper's matrix-multiplication-scheme sum premise. -/
theorem target_isMatrixMultiplicationScheme :
    IsMatrixMultiplicationScheme 1 1 1 target :=
  target_represents_matMul

/-- The witness jointly realizes the required cardinalities and nonzero-term premises. -/
theorem witness_nonvacuous :
    source.card = 1 ∧ target.card = 3 ∧
      (∀ t, t ∈ source.terms → t.eval ≠ 0) ∧
      (∀ t, t ∈ target.terms → t.eval ≠ 0) := by
  exact ⟨rfl, rfl, source.term_nonzero, target.term_nonzero⟩

/-- The one-copy and three-copy schemes represent exactly the same tensor over `F₂`. -/
theorem representedTensor_source_eq_target :
    source.representedTensor = target.representedTensor := by
  rw [source_represents_matMul, target_represents_matMul]

/-- A scheme contains two selected occurrences when its multiset can expose both of them. -/
def HasSelectedPair {k : Type*} [CommSemiring k] {a b c : ℕ}
    (S : PaperScheme k a b c) : Prop :=
  ∃ t u rest, S.terms = t ::ₘ u ::ₘ rest

/-- A Plus selection exposes two occurrences whose three corresponding factors all differ. -/
def PlusEligible {k : Type*} [CommSemiring k] {a b c : ℕ}
    (S : PaperScheme k a b c) : Prop :=
  ∃ t u rest, S.terms = t ::ₘ u ::ₘ rest ∧
    t.1 ≠ u.1 ∧ t.2.1 ≠ u.2.1 ∧ t.2.2 ≠ u.2.2

/-- The singleton source has no two selected occurrences. -/
theorem not_hasSelectedPair_source : ¬ HasSelectedPair source := by
  rintro ⟨t, u, rest, hterms⟩
  have hcard := congrArg Multiset.card hterms
  norm_num [source] at hcard

/-- In particular, no Plus selection is available at the singleton source. -/
theorem not_plusEligible_source : ¬ PlusEligible source := by
  rintro ⟨t, u, rest, hterms, _hfirst, _hsecond, _hthird⟩
  have hcard := congrArg Multiset.card hterms
  norm_num [source] at hcard

/-- No Plus selection is available at the target either, because all three copies have equal
factors in every position. -/
theorem not_plusEligible_target : ¬ PlusEligible target := by
  rintro ⟨t, u, rest, hterms, hfirst, _hsecond, _hthird⟩
  have ht : t ∈ target.terms := by
    rw [hterms]
    simp only [Multiset.mem_cons, true_or]
  have hu : u ∈ target.terms := by
    rw [hterms]
    simp only [Multiset.mem_cons, true_or, or_true]
  have htunit : t = unitTriad := by
    simpa only [target, Multiset.mem_cons, Multiset.mem_singleton, or_self] using ht
  have huunit : u = unitTriad := by
    simpa only [target, Multiset.mem_cons, Multiset.mem_singleton, or_self] using hu
  exact hfirst (congrArg Prod.fst (htunit.trans huunit.symm))

/-- The directed cardinal-and-selection envelope of the paper's forward moves. Every
constructor requires exact tensor preservation. Plus also requires the paper's
all-three-factors-different selected pair and raises cardinality by one; Flip preserves
cardinality; Reduction strictly lowers it. The literal payload formulas are not modeled. -/
inductive ForwardStep {k : Type*} [CommSemiring k] {a b c : ℕ} :
    PaperScheme k a b c → PaperScheme k a b c → Prop
  /-- A forward Plus step in the necessary-condition envelope. -/
  | plus {S R} (tensor_eq : R.representedTensor = S.representedTensor)
      (eligible : PlusEligible S) (card_eq : R.card = S.card + 1) : ForwardStep S R
  /-- A forward Flip step in the necessary-condition envelope. -/
  | flip {S R} (tensor_eq : R.representedTensor = S.representedTensor)
      (card_eq : R.card = S.card) : ForwardStep S R
  /-- A forward Reduction step in the necessary-condition envelope. -/
  | reduction {S R} (tensor_eq : R.representedTensor = S.representedTensor)
      (card_lt : R.card < S.card) : ForwardStep S R

/-- Directed reachability is the reflexive-transitive closure of forward steps, with no
symmetric closure and no use of inverse Reduction edges. -/
def ForwardReachable {k : Type*} [CommSemiring k] {a b c : ℕ}
    (S R : PaperScheme k a b c) : Prop :=
  Relation.ReflTransGen ForwardStep S R

example : ForwardReachable source source := Relation.ReflTransGen.refl

/-- Every selected pair contributes at least two occurrences to the source multiset. -/
theorem card_two_le_of_hasSelectedPair {k : Type*} [CommSemiring k] {a b c : ℕ}
    {S : PaperScheme k a b c} (hpair : HasSelectedPair S) : 2 ≤ S.card := by
  rcases hpair with ⟨t, u, rest, hterms⟩
  change 2 ≤ S.terms.card
  rw [hterms]
  simp only [Multiset.card_cons]
  omega

/-- Plus eligibility in particular supplies two selected occurrences. -/
theorem HasSelectedPair.of_plusEligible {k : Type*} [CommSemiring k] {a b c : ℕ}
    {S : PaperScheme k a b c} (hplus : PlusEligible S) : HasSelectedPair S := by
  rcases hplus with ⟨t, u, rest, hterms, _hfirst, _hsecond, _hthird⟩
  exact ⟨t, u, rest, hterms⟩

/-- Every abstract forward step preserves the represented tensor exactly. -/
theorem ForwardStep.tensor_eq {k : Type*} [CommSemiring k] {a b c : ℕ}
    {S R : PaperScheme k a b c} (hstep : ForwardStep S R) :
    R.representedTensor = S.representedTensor := by
  cases hstep with
  | plus tensor_eq _eligible _card_eq => exact tensor_eq
  | flip tensor_eq _card_eq => exact tensor_eq
  | reduction tensor_eq _card_lt => exact tensor_eq

/-- Directed forward reachability preserves the represented tensor exactly. -/
theorem ForwardReachable.tensor_eq {k : Type*} [CommSemiring k] {a b c : ℕ}
    {S R : PaperScheme k a b c} (hreach : ForwardReachable S R) :
    R.representedTensor = S.representedTensor := by
  induction hreach with
  | refl => rfl
  | tail hpath hstep ih => exact hstep.tensor_eq.trans ih

/-- A tensor-preserving forward step from a one-term scheme with nonzero represented tensor
cannot change its cardinality. -/
theorem ForwardStep.card_eq_one_of_source {k : Type*} [CommSemiring k]
    {a b c : ℕ} {S R : PaperScheme k a b c} (hstep : ForwardStep S R)
    (hcard : S.card = 1) (hnonzero : S.representedTensor ≠ 0) : R.card = 1 := by
  cases hstep with
  | plus _tensor_eq eligible _step_card =>
      have htwo : 2 ≤ S.card :=
        card_two_le_of_hasSelectedPair (HasSelectedPair.of_plusEligible eligible)
      omega
  | flip _tensor_eq step_card =>
      omega
  | reduction tensor_eq card_lt =>
      have hRcard : R.card = 0 := by omega
      have hRterms : R.terms = 0 := by
        apply Multiset.card_eq_zero.mp
        simpa only [PaperScheme.card] using hRcard
      have hRzero : R.representedTensor = 0 := by
        simp only [PaperScheme.representedTensor, hRterms, Multiset.map_zero,
          Multiset.sum_zero]
      exfalso
      apply hnonzero
      rw [← tensor_eq, hRzero]

/-- Directed forward reachability from a nonzero one-term scheme remains at cardinality one. -/
theorem ForwardReachable.card_eq_one {k : Type*} [CommSemiring k]
    {a b c : ℕ} {S R : PaperScheme k a b c} (hreach : ForwardReachable S R)
    (hcard : S.card = 1) (hnonzero : S.representedTensor ≠ 0) : R.card = 1 := by
  induction hreach with
  | refl => exact hcard
  | @tail R Q hpath hstep ih =>
      have hRtensor : R.representedTensor = S.representedTensor :=
        ForwardReachable.tensor_eq hpath
      have hRnonzero : R.representedTensor ≠ 0 := by
        rw [hRtensor]
        exact hnonzero
      exact hstep.card_eq_one_of_source ih hRnonzero

/-- The represented tensor of the source witness is nonzero. -/
theorem source_representedTensor_ne_zero : source.representedTensor ≠ 0 := by
  rw [source_represents_matMul]
  intro hzero
  have hentry := congrFun (congrFun (congrFun hzero 0) 0) 0
  norm_num [matMulTensor] at hentry
  exact hentry (Subsingleton.elim _ _)

/-- There is no directed path in the forward envelope from the one-copy scheme to the
three-copy scheme. -/
theorem not_forwardReachable_source_target :
    ¬ ForwardReachable source target := by
  intro hreach
  have hcard : target.card = 1 :=
    hreach.card_eq_one (by rfl) source_representedTensor_ne_zero
  norm_num [PaperScheme.card, target] at hcard

/-- Any exact forward move relation contained in `ForwardStep` also has no directed path from
`source` to `target`. This is the formal boundary between the proved envelope result and a
future formalization of the paper's literal move payloads. -/
theorem no_forward_path_of_subrelation
    (ExactStep : PaperScheme F₂ 1 1 1 → PaperScheme F₂ 1 1 1 → Prop)
    (hsub : ∀ {S R}, ExactStep S R → ForwardStep S R) :
    ¬ Relation.ReflTransGen ExactStep source target := by
  intro hpath
  apply not_forwardReachable_source_target
  change Relation.ReflTransGen ForwardStep source target
  exact Relation.ReflTransGen.mono (r := ExactStep) (p := ForwardStep)
    (fun _ _ hstep => hsub hstep) source target hpath

/-- Counterexample to the directed-forward reading of Theorem 5.2: two nonempty schemes of
nonzero rank-one terms represent the same `(1,1,1)` matrix-multiplication tensor over `F₂`,
yet the target is not reachable from the source in the forward transition envelope. -/
theorem directed_forward_interpretation_counterexample :
    IsMatrixMultiplicationScheme 1 1 1 source ∧
    IsMatrixMultiplicationScheme 1 1 1 target ∧
    source.representedTensor = target.representedTensor ∧
    ¬ ForwardReachable source target := by
  exact ⟨source_isMatrixMultiplicationScheme, target_isMatrixMultiplicationScheme,
    representedTensor_source_eq_target, not_forwardReachable_source_target⟩

#check @source_represents_matMul
#check @target_represents_matMul
#check @representedTensor_source_eq_target
#check @not_forwardReachable_source_target
#check @directed_forward_interpretation_counterexample
#print axioms directed_forward_interpretation_counterexample

end AdaptivePlusCounterexample
end BilinearComplexity
