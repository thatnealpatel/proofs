import GroupTPP.MonomialRealization
import GroupTPP.TPP

/-!
# Complete monomial realizations normalize to indexed TPP data

This file proves the order-sensitive algebraic normalization behind the finite
CSP reduction for complete generalized monomial realizations. It works first
with indexed data, avoiding finite-set cardinality plumbing.
-/

set_option autoImplicit false

namespace GroupTPP.MonomialNormalForm

open GroupTPP.MonomialRealization
open GroupTPP.TPP

variable {I J K : Type*}
variable {G : Type*} [Group G]
variable {F : Type*} [Field F]

/-- The indexed left-quotient triple product property. This is the list-valued
version of `GroupTPP.TPP.TripleProductProperty`. -/
def IndexedTPP (s : I → G) (t : J → G) (u : K → G) : Prop :=
  ∀ i i' j j' k k',
    (s i')⁻¹ * s i * (t j')⁻¹ * t j * (u k')⁻¹ * u k = 1 →
      i = i' ∧ j = j' ∧ k = k'

/-- The indexed TPP is inhabited at singleton index types. This ground-truth
check shows that the definition and the nonempty hypotheses used below are
jointly satisfiable. -/
example : IndexedTPP (fun _ : Unit => (1 : G)) (fun _ : Unit => 1) (fun _ : Unit => 1) := by
  intro i i' j j' k k' _
  exact ⟨Subsingleton.elim i i', Subsingleton.elim j j', Subsingleton.elim k k'⟩

/-- For nonempty finite index types, indexed TPP is ordinary TPP on the
three image finsets together with injectivity of all three index maps. The
injectivity conjuncts are essential: image finsets alone forget duplicate list
entries. -/
theorem indexedTPP_iff_image_tpp_and_injective
    [Fintype I] [Fintype J] [Fintype K]
    [Nonempty I] [Nonempty J] [Nonempty K] [DecidableEq G]
    (s : I → G) (t : J → G) (u : K → G) :
    IndexedTPP s t u ↔
      TripleProductProperty (Finset.univ.image s) (Finset.univ.image t)
        (Finset.univ.image u) ∧
      Function.Injective s ∧ Function.Injective t ∧ Function.Injective u := by
  constructor
  · intro h
    have htpp : TripleProductProperty (Finset.univ.image s) (Finset.univ.image t)
        (Finset.univ.image u) := by
      intro sv hsv sv' hsv' tv htv tv' htv' uv huv uv' huv' hquot
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hsv
      obtain ⟨i', _, rfl⟩ := Finset.mem_image.mp hsv'
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp htv
      obtain ⟨j', _, rfl⟩ := Finset.mem_image.mp htv'
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp huv
      obtain ⟨k', _, rfl⟩ := Finset.mem_image.mp huv'
      obtain ⟨hi, hj, hk⟩ := h i i' j j' k k' hquot
      exact ⟨congrArg s hi, congrArg t hj, congrArg u hk⟩
    let i₀ : I := Classical.choice inferInstance
    let j₀ : J := Classical.choice inferInstance
    let k₀ : K := Classical.choice inferInstance
    have hs : Function.Injective s := by
      intro i i' heq
      have hquot : (s i')⁻¹ * s i * (t j₀)⁻¹ * t j₀ * (u k₀)⁻¹ * u k₀ = 1 := by
        rw [heq]
        group
      exact (h i i' j₀ j₀ k₀ k₀ hquot).1
    have ht : Function.Injective t := by
      intro j j' heq
      have hquot : (s i₀)⁻¹ * s i₀ * (t j')⁻¹ * t j * (u k₀)⁻¹ * u k₀ = 1 := by
        rw [heq]
        group
      exact (h i₀ i₀ j j' k₀ k₀ hquot).2.1
    have hu : Function.Injective u := by
      intro k k' heq
      have hquot : (s i₀)⁻¹ * s i₀ * (t j₀)⁻¹ * t j₀ * (u k')⁻¹ * u k = 1 := by
        rw [heq]
        group
      exact (h i₀ i₀ j₀ j₀ k k' hquot).2.2
    exact ⟨htpp, hs, ht, hu⟩
  · rintro ⟨h, hs, ht, hu⟩ i i' j j' k k' hquot
    have himage := h (s i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
      (s i') (Finset.mem_image.mpr ⟨i', Finset.mem_univ i', rfl⟩)
      (t j) (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
      (t j') (Finset.mem_image.mpr ⟨j', Finset.mem_univ j', rfl⟩)
      (u k) (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩)
      (u k') (Finset.mem_image.mpr ⟨k', Finset.mem_univ k', rfl⟩) hquot
    exact ⟨hs himage.1, ht himage.2.1, hu himage.2.2⟩

/-- Diagonal equations force the first group table into the normal form
`a i j = s i * (t j)⁻¹`, with the anchors and multiplication order shown. -/
theorem diagonal_group_normal_form_a
    (a : I → J → G) (b : J → K → G) (c : K → I → G)
    (hdiag : ∀ i j k, a i j * b j k * c k i = 1)
    (j₀ : J) (k₀ : K) :
    ∀ i j,
      a i j = a i j₀ * (b j k₀ * (b j₀ k₀)⁻¹)⁻¹ := by
  intro i j
  have hij := hdiag i j k₀
  have hi0 := hdiag i j₀ k₀
  have hab : a i j * b j k₀ = a i j₀ * b j₀ k₀ := by
    calc
      a i j * b j k₀ = (c k₀ i)⁻¹ := eq_inv_of_mul_eq_one_left hij
      _ = a i j₀ * b j₀ k₀ := (eq_inv_of_mul_eq_one_left hi0).symm
  calc
    a i j = (a i j * b j k₀) * (b j k₀)⁻¹ := by group
    _ = (a i j₀ * b j₀ k₀) * (b j k₀)⁻¹ := by rw [hab]
    _ = a i j₀ * (b j k₀ * (b j₀ k₀)⁻¹)⁻¹ := by
      rw [mul_inv_rev, inv_inv]
      group

/-- Diagonal equations force the second group table into the normal form
`b j k = t j * (u k)⁻¹`, with the same anchors as the first table. -/
theorem diagonal_group_normal_form_b
    (a : I → J → G) (b : J → K → G) (c : K → I → G)
    (hdiag : ∀ i j k, a i j * b j k * c k i = 1)
    (i₀ : I) (j₀ : J) (k₀ : K) :
    ∀ j k,
      b j k = (b j k₀ * (b j₀ k₀)⁻¹) * ((b j₀ k)⁻¹)⁻¹ := by
  intro j k
  have hjk := hdiag i₀ j k
  have h0k := hdiag i₀ j₀ k
  have haj := diagonal_group_normal_form_a a b c hdiag j₀ k₀ i₀ j
  have hab : a i₀ j * b j k = a i₀ j₀ * b j₀ k := by
    calc
      a i₀ j * b j k = (c k i₀)⁻¹ := eq_inv_of_mul_eq_one_left hjk
      _ = a i₀ j₀ * b j₀ k := (eq_inv_of_mul_eq_one_left h0k).symm
  calc
    b j k = (a i₀ j)⁻¹ * (a i₀ j * b j k) := by group
    _ = (a i₀ j)⁻¹ * (a i₀ j₀ * b j₀ k) := by rw [hab]
    _ = (b j k₀ * (b j₀ k₀)⁻¹) * b j₀ k := by
      rw [haj]
      group
    _ = (b j k₀ * (b j₀ k₀)⁻¹) * ((b j₀ k)⁻¹)⁻¹ := by rw [inv_inv]

/-- All three diagonal group equations are equivalent to a common three-map
normal form once one element of each index type is chosen. -/
theorem diagonal_group_normal_form
    (a : I → J → G) (b : J → K → G) (c : K → I → G)
    (hdiag : ∀ i j k, a i j * b j k * c k i = 1)
    (i₀ : I) (j₀ : J) (k₀ : K) :
    let s : I → G := fun i => a i j₀
    let t : J → G := fun j => b j k₀ * (b j₀ k₀)⁻¹
    let u : K → G := fun k => (b j₀ k)⁻¹
    (∀ i j, a i j = s i * (t j)⁻¹) ∧
    (∀ j k, b j k = t j * (u k)⁻¹) ∧
    (∀ k i, c k i = u k * (s i)⁻¹) := by
  dsimp only
  have ha := diagonal_group_normal_form_a a b c hdiag j₀ k₀
  have hb := diagonal_group_normal_form_b a b c hdiag i₀ j₀ k₀
  refine ⟨ha, hb, ?_⟩
  intro k i
  have hik := hdiag i j₀ k
  calc
    c k i = (a i j₀ * b j₀ k)⁻¹ := eq_inv_of_mul_eq_one_right hik
    _ = (b j₀ k)⁻¹ * (a i j₀)⁻¹ := by rw [mul_inv_rev]

/-- A collision in normal-form tables is equivalent, after cyclic conjugation,
to a product of three quotients. The `J` and `K` quotients have the reversed
index orientation displayed in the conclusion. -/
theorem normal_form_collision_iff_quotient
    (s : I → G) (t : J → G) (u : K → G)
    (i i' : I) (j j' : J) (k k' : K) :
    (s i * (t j)⁻¹) * (t j' * (u k)⁻¹) * (u k' * (s i')⁻¹) = 1 ↔
      (s i')⁻¹ * s i * (t j)⁻¹ * t j' * (u k)⁻¹ * u k' = 1 := by
  constructor <;> intro h
  · calc
      (s i')⁻¹ * s i * (t j)⁻¹ * t j' * (u k)⁻¹ * u k'
          = (s i')⁻¹ *
              ((s i * (t j)⁻¹) * (t j' * (u k)⁻¹) * (u k' * (s i')⁻¹)) *
              s i' := by group
      _ = 1 := by rw [h]; group
  · calc
      (s i * (t j)⁻¹) * (t j' * (u k)⁻¹) * (u k' * (s i')⁻¹)
          = s i' *
              ((s i')⁻¹ * s i * (t j)⁻¹ * t j' * (u k)⁻¹ * u k') *
              (s i')⁻¹ := by group
      _ = 1 := by rw [h]; group

/-- For normal-form group tables, complete no-cancellation is equivalent to the
indexed left-quotient TPP. The proof explicitly swaps both `J` and `K` ordered
pairs, preventing a quotient-orientation error. -/
theorem normal_form_no_cancellation_iff_indexedTPP
    (s : I → G) (t : J → G) (u : K → G) :
    (∀ i i' j j' k k',
      (s i * (t j)⁻¹) * (t j' * (u k)⁻¹) * (u k' * (s i')⁻¹) = 1 →
        j = j' ∧ k = k' ∧ i = i') ↔
      IndexedTPP s t u := by
  constructor
  · intro h i i' j j' k k' hquot
    have hcol :
        (s i * (t j')⁻¹) * (t j * (u k')⁻¹) * (u k * (s i')⁻¹) = 1 :=
      (normal_form_collision_iff_quotient s t u i i' j' j k' k).mpr hquot
    obtain ⟨hj, hk, hi⟩ := h i i' j' j k' k hcol
    exact ⟨hi, hj.symm, hk.symm⟩
  · intro h i i' j j' k k' hcol
    have hquot := (normal_form_collision_iff_quotient s t u i i' j j' k k').mp hcol
    obtain ⟨hi, hj, hk⟩ := h i i' j' j k' k hquot
    exact ⟨hj.symm, hk.symm, hi⟩

/-- An indexed TPP map in the first mode is injective, provided the other two
index types are nonempty so their quotients can be fixed to `1`. -/
theorem IndexedTPP.injective_s
    {s : I → G} {t : J → G} {u : K → G} [Nonempty J] [Nonempty K]
    (h : IndexedTPP s t u) : Function.Injective s := by
  intro i i' hii'
  let j₀ : J := Classical.choice inferInstance
  let k₀ : K := Classical.choice inferInstance
  have hquot : (s i')⁻¹ * s i * (t j₀)⁻¹ * t j₀ * (u k₀)⁻¹ * u k₀ = 1 := by
    rw [hii']
    group
  exact (h i i' j₀ j₀ k₀ k₀ hquot).1

/-- An indexed TPP map in the second mode is injective. -/
theorem IndexedTPP.injective_t
    {s : I → G} {t : J → G} {u : K → G} [Nonempty I] [Nonempty K]
    (h : IndexedTPP s t u) : Function.Injective t := by
  intro j j' hjj'
  let i₀ : I := Classical.choice inferInstance
  let k₀ : K := Classical.choice inferInstance
  have hquot : (s i₀)⁻¹ * s i₀ * (t j')⁻¹ * t j * (u k₀)⁻¹ * u k₀ = 1 := by
    rw [hjj']
    group
  exact (h i₀ i₀ j j' k₀ k₀ hquot).2.1

/-- An indexed TPP map in the third mode is injective. -/
theorem IndexedTPP.injective_u
    {s : I → G} {t : J → G} {u : K → G} [Nonempty I] [Nonempty J]
    (h : IndexedTPP s t u) : Function.Injective u := by
  intro k k' hkk'
  let i₀ : I := Classical.choice inferInstance
  let j₀ : J := Classical.choice inferInstance
  have hquot : (s i₀)⁻¹ * s i₀ * (t j₀)⁻¹ * t j₀ * (u k')⁻¹ * u k = 1 := by
    rw [hkk']
    group
  exact (h i₀ i₀ j₀ j₀ k k' hquot).2.2

/-- The first pair map `(i,j) ↦ s i * (t j)⁻¹` is injective under indexed TPP,
provided the unused third index type is nonempty. -/
theorem IndexedTPP.injective_st
    {s : I → G} {t : J → G} {u : K → G} [Nonempty K]
    (h : IndexedTPP s t u) :
    Function.Injective (fun q : I × J => s q.1 * (t q.2)⁻¹) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ heq
  let k₀ : K := Classical.choice inferInstance
  have heq' : s i * (t j)⁻¹ = s i' * (t j')⁻¹ := heq
  have hst : (s i')⁻¹ * s i * (t j)⁻¹ * t j' = 1 := by
      calc
        (s i')⁻¹ * s i * (t j)⁻¹ * t j'
            = (s i')⁻¹ * (s i * (t j)⁻¹) * t j' := by group
        _ = (s i')⁻¹ * (s i' * (t j')⁻¹) * t j' := by rw [heq']
        _ = 1 := by group
  have hquot : (s i')⁻¹ * s i * (t j)⁻¹ * t j' * (u k₀)⁻¹ * u k₀ = 1 := by
    rw [hst]
    group
  obtain ⟨hi, hj, _⟩ := h i i' j' j k₀ k₀ hquot
  exact Prod.ext hi hj.symm

/-- The second pair map `(j,k) ↦ t j * (u k)⁻¹` is injective under indexed TPP,
provided the unused first index type is nonempty. -/
theorem IndexedTPP.injective_tu
    {s : I → G} {t : J → G} {u : K → G} [Nonempty I]
    (h : IndexedTPP s t u) :
    Function.Injective (fun q : J × K => t q.1 * (u q.2)⁻¹) := by
  rintro ⟨j, k⟩ ⟨j', k'⟩ heq
  let i₀ : I := Classical.choice inferInstance
  have heq' : t j * (u k)⁻¹ = t j' * (u k')⁻¹ := heq
  have htu : (t j')⁻¹ * t j * (u k)⁻¹ * u k' = 1 := by
      calc
        (t j')⁻¹ * t j * (u k)⁻¹ * u k'
            = (t j')⁻¹ * (t j * (u k)⁻¹) * u k' := by group
        _ = (t j')⁻¹ * (t j' * (u k')⁻¹) * u k' := by rw [heq']
        _ = 1 := by group
  have hquot : (s i₀)⁻¹ * s i₀ * (t j')⁻¹ * t j * (u k)⁻¹ * u k' = 1 := by
    calc
      (s i₀)⁻¹ * s i₀ * (t j')⁻¹ * t j * (u k)⁻¹ * u k'
          = (t j')⁻¹ * t j * (u k)⁻¹ * u k' := by group
      _ = 1 := htu
  obtain ⟨_, hj, hk⟩ := h i₀ i₀ j j' k' k hquot
  exact Prod.ext hj hk.symm

/-- The third pair map `(k,i) ↦ u k * (s i)⁻¹` is injective under indexed TPP,
provided the unused second index type is nonempty. -/
theorem IndexedTPP.injective_us
    {s : I → G} {t : J → G} {u : K → G} [Nonempty J]
    (h : IndexedTPP s t u) :
    Function.Injective (fun q : K × I => u q.1 * (s q.2)⁻¹) := by
  rintro ⟨k, i⟩ ⟨k', i'⟩ heq
  let j₀ : J := Classical.choice inferInstance
  have heq' : u k * (s i)⁻¹ = u k' * (s i')⁻¹ := heq
  have hus : (u k')⁻¹ * u k * (s i)⁻¹ * s i' = 1 := by
    calc
      (u k')⁻¹ * u k * (s i)⁻¹ * s i'
          = (u k')⁻¹ * (u k * (s i)⁻¹) * s i' := by group
      _ = (u k')⁻¹ * (u k' * (s i')⁻¹) * s i' := by rw [heq']
      _ = 1 := by group
  have hquot : (s i)⁻¹ * s i' * (t j₀)⁻¹ * t j₀ * (u k')⁻¹ * u k = 1 := by
    have hus' : ((u k')⁻¹ * u k) * ((s i)⁻¹ * s i') = 1 := by
      rw [← hus]
      group
    have hsolve : (s i)⁻¹ * s i' = ((u k')⁻¹ * u k)⁻¹ :=
      eq_inv_of_mul_eq_one_right hus'
    calc
      (s i)⁻¹ * s i' * (t j₀)⁻¹ * t j₀ * (u k')⁻¹ * u k
          = ((s i)⁻¹ * s i') * ((u k')⁻¹ * u k) := by group
      _ = ((u k')⁻¹ * u k)⁻¹ * ((u k')⁻¹ * u k) := by rw [hsolve]
      _ = 1 := by group
  obtain ⟨hi, _, hk⟩ := h i' i j₀ j₀ k k' hquot
  exact Prod.ext hk hi.symm

section CompleteRealization

variable [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq G]
variable {a : I → J → G} {b : J → K → G} {c : K → I → G}
variable {α : I → J → F} {β : J → K → F} {γ : K → I → F}

/-- A complete generalized monomial realization over nonempty index types has
normal-form group tables whose one-variable data satisfy indexed left TPP. -/
theorem IsMonomialRealizationGen.exists_normal_form_indexedTPP
    [Nonempty I] [Nonempty J] [Nonempty K]
    (h : IsMonomialRealizationGen a b c α β γ) :
    ∃ s : I → G, ∃ t : J → G, ∃ u : K → G,
      (∀ i j, a i j = s i * (t j)⁻¹) ∧
      (∀ j k, b j k = t j * (u k)⁻¹) ∧
      (∀ k i, c k i = u k * (s i)⁻¹) ∧
      IndexedTPP s t u := by
  let i₀ : I := Classical.choice inferInstance
  let j₀ : J := Classical.choice inferInstance
  let k₀ : K := Classical.choice inferInstance
  let s : I → G := fun i => a i j₀
  let t : J → G := fun j => b j k₀ * (b j₀ k₀)⁻¹
  let u : K → G := fun k => (b j₀ k)⁻¹
  have hdiag : ∀ i j k, a i j * b j k * c k i = 1 :=
    h.diagonal_group_prod_eq_one
  obtain ⟨ha, hb, hc⟩ := diagonal_group_normal_form a b c hdiag i₀ j₀ k₀
  refine ⟨s, t, u, ha, hb, hc, ?_⟩
  rw [← normal_form_no_cancellation_iff_indexedTPP]
  intro i i' j j' k k' hcol
  apply h.no_cancellation
  rw [ha i j, hb j' k, hc k' i']
  exact hcol

/-- Any indexed TPP triple gives a complete generalized monomial realization
with its normal-form group tables and all coefficients equal to one. -/
theorem indexedTPP_monomialRealizationGen
    (s : I → G) (t : J → G) (u : K → G)
    (h : IndexedTPP s t u) :
    IsMonomialRealizationGen (F := F)
      (fun i j => s i * (t j)⁻¹)
      (fun j k => t j * (u k)⁻¹)
      (fun k i => u k * (s i)⁻¹)
      (fun _ _ => 1) (fun _ _ => 1) (fun _ _ => 1) where
  alpha_ne_zero _ _ := one_ne_zero
  beta_ne_zero _ _ := one_ne_zero
  gamma_ne_zero _ _ := one_ne_zero
  coeff_identity := by
    intro i i' j j' k k'
    simp only [one_mul]
    by_cases hcol :
        (s i * (t j)⁻¹) * (t j' * (u k)⁻¹) * (u k' * (s i')⁻¹) = 1
    · have hdiag := (normal_form_no_cancellation_iff_indexedTPP s t u).mpr h
        i i' j j' k k' hcol
      rw [if_pos hcol, if_pos hdiag]
    · rw [if_neg hcol, if_neg]
      intro hdiag
      obtain ⟨rfl, rfl, rfl⟩ := hdiag
      apply hcol
      group


/-- Constant identity-valued data on singleton indices jointly satisfy the
indexed TPP, diagonal group-table, and complete realization hypotheses. -/
example :
    IsMonomialRealizationGen (F := ℚ)
      (fun _ : Unit => fun _ : Unit => (1 : Unit))
      (fun _ : Unit => fun _ : Unit => (1 : Unit))
      (fun _ : Unit => fun _ : Unit => (1 : Unit))
      (fun _ : Unit => fun _ : Unit => (1 : ℚ))
      (fun _ : Unit => fun _ : Unit => (1 : ℚ))
      (fun _ : Unit => fun _ : Unit => (1 : ℚ)) := by
  exact indexedTPP_monomialRealizationGen
    (F := ℚ) (fun _ : Unit => (1 : Unit))
    (fun _ : Unit => (1 : Unit)) (fun _ : Unit => (1 : Unit)) (by
      intro i i' j j' k k' _
      exact ⟨Subsingleton.elim i i', Subsingleton.elim j j', Subsingleton.elim k k'⟩)

/-- Complete generalized monomial realizability is equivalent, for nonempty
index types, to existence of indexed left-TPP data. Coefficients do not enlarge
the feasible class because the converse uses coefficients identically one. -/
theorem exists_monomialRealizationGen_iff_exists_indexedTPP
    [Nonempty I] [Nonempty J] [Nonempty K] :
    (∃ (a : I → J → G) (b : J → K → G) (c : K → I → G)
        (α : I → J → F) (β : J → K → F) (γ : K → I → F),
      IsMonomialRealizationGen a b c α β γ) ↔
      ∃ (s : I → G) (t : J → G) (u : K → G), IndexedTPP s t u := by
  constructor
  · rintro ⟨a, b, c, α, β, γ, h⟩
    obtain ⟨s, t, u, _, _, _, htpp⟩ :=
      IsMonomialRealizationGen.exists_normal_form_indexedTPP h
    exact ⟨s, t, u, htpp⟩
  · rintro ⟨s, t, u, htpp⟩
    exact ⟨fun i j => s i * (t j)⁻¹,
      fun j k => t j * (u k)⁻¹,
      fun k i => u k * (s i)⁻¹,
      fun _ _ => 1, fun _ _ => 1, fun _ _ => 1,
      indexedTPP_monomialRealizationGen s t u htpp⟩

end CompleteRealization

/-! ### Coefficient normal form in the unit group -/

/-- Multiplicative unit-valued diagonal coefficient equations have the same
normal form as the group tables. This is the coefficient gauge theorem at the
correct type: the factors are units rather than unguarded field elements. -/
theorem diagonal_coeff_unit_normal_form
    (α : I → J → Fˣ) (β : J → K → Fˣ) (γ : K → I → Fˣ)
    (hdiag : ∀ i j k, α i j * β j k * γ k i = 1)
    (i₀ : I) (j₀ : J) (k₀ : K) :
    let x : I → Fˣ := fun i => α i j₀
    let y : J → Fˣ := fun j => β j k₀ * (β j₀ k₀)⁻¹
    let z : K → Fˣ := fun k => (β j₀ k)⁻¹
    (∀ i j, α i j = x i * (y j)⁻¹) ∧
    (∀ j k, β j k = y j * (z k)⁻¹) ∧
    (∀ k i, γ k i = z k * (x i)⁻¹) :=
  diagonal_group_normal_form α β γ hdiag i₀ j₀ k₀

/-- Nonzero field-valued diagonal coefficient equations factor through three
families of units. Coercing the unit equations recovers the original scalar
coefficients exactly. -/
theorem diagonal_coeff_normal_form
    (α : I → J → F) (β : J → K → F) (γ : K → I → F)
    (hα : ∀ i j, α i j ≠ 0) (hβ : ∀ j k, β j k ≠ 0)
    (hγ : ∀ k i, γ k i ≠ 0)
    (hdiag : ∀ i j k, α i j * β j k * γ k i = 1)
    (i₀ : I) (j₀ : J) (k₀ : K) :
    ∃ x : I → Fˣ, ∃ y : J → Fˣ, ∃ z : K → Fˣ,
      (∀ i j, α i j = (x i * (y j)⁻¹ : Fˣ)) ∧
      (∀ j k, β j k = (y j * (z k)⁻¹ : Fˣ)) ∧
      (∀ k i, γ k i = (z k * (x i)⁻¹ : Fˣ)) := by
  let αu : I → J → Fˣ := fun i j => Units.mk0 (α i j) (hα i j)
  let βu : J → K → Fˣ := fun j k => Units.mk0 (β j k) (hβ j k)
  let γu : K → I → Fˣ := fun k i => Units.mk0 (γ k i) (hγ k i)
  have hdiagu : ∀ i j k, αu i j * βu j k * γu k i = 1 := by
    intro i j k
    apply Units.ext
    exact hdiag i j k
  obtain ⟨hαu, hβu, hγu⟩ := diagonal_coeff_unit_normal_form αu βu γu hdiagu i₀ j₀ k₀
  let x : I → Fˣ := fun i => αu i j₀
  let y : J → Fˣ := fun j => βu j k₀ * (βu j₀ k₀)⁻¹
  let z : K → Fˣ := fun k => (βu j₀ k)⁻¹
  refine ⟨x, y, z, ?_, ?_, ?_⟩
  · intro i j
    change (αu i j : F) = (x i * (y j)⁻¹ : Fˣ)
    exact congrArg (fun q : Fˣ => (q : F)) (hαu i j)
  · intro j k
    change (βu j k : F) = (y j * (z k)⁻¹ : Fˣ)
    exact congrArg (fun q : Fˣ => (q : F)) (hβu j k)
  · intro k i
    change (γu k i : F) = (z k * (x i)⁻¹ : Fˣ)
    exact congrArg (fun q : Fˣ => (q : F)) (hγu k i)

/-- The coefficient normal-form hypotheses are jointly satisfiable: constant
unit coefficients give constant unit gauge factors on singleton indices. -/
example :
    ∃ x : Unit → ℚˣ, ∃ y : Unit → ℚˣ, ∃ z : Unit → ℚˣ,
      (∀ i j, (1 : ℚ) = (x i * (y j)⁻¹ : ℚˣ)) ∧
      (∀ j k, (1 : ℚ) = (y j * (z k)⁻¹ : ℚˣ)) ∧
      (∀ k i, (1 : ℚ) = (z k * (x i)⁻¹ : ℚˣ)) := by
  exact diagonal_coeff_normal_form
    (fun _ _ => (1 : ℚ)) (fun _ _ => (1 : ℚ)) (fun _ _ => (1 : ℚ))
    (fun _ _ => one_ne_zero) (fun _ _ => one_ne_zero) (fun _ _ => one_ne_zero)
    (fun _ _ _ => by norm_num) () () ()

#check @IndexedTPP
#check @indexedTPP_iff_image_tpp_and_injective
#check @diagonal_group_normal_form_a
#check @diagonal_group_normal_form_b
#check @diagonal_group_normal_form
#check @normal_form_collision_iff_quotient
#check @normal_form_no_cancellation_iff_indexedTPP
#check @IndexedTPP.injective_s
#check @IndexedTPP.injective_t
#check @IndexedTPP.injective_u
#check @IndexedTPP.injective_st
#check @IndexedTPP.injective_tu
#check @IndexedTPP.injective_us
#check @IsMonomialRealizationGen.exists_normal_form_indexedTPP
#check @indexedTPP_monomialRealizationGen
#check @exists_monomialRealizationGen_iff_exists_indexedTPP
#check @diagonal_coeff_unit_normal_form
#check @diagonal_coeff_normal_form

#print axioms indexedTPP_iff_image_tpp_and_injective
#print axioms diagonal_group_normal_form_a
#print axioms diagonal_group_normal_form_b
#print axioms diagonal_group_normal_form
#print axioms normal_form_collision_iff_quotient
#print axioms normal_form_no_cancellation_iff_indexedTPP
#print axioms IndexedTPP.injective_s
#print axioms IndexedTPP.injective_t
#print axioms IndexedTPP.injective_u
#print axioms IndexedTPP.injective_st
#print axioms IndexedTPP.injective_tu
#print axioms IndexedTPP.injective_us
#print axioms IsMonomialRealizationGen.exists_normal_form_indexedTPP
#print axioms indexedTPP_monomialRealizationGen
#print axioms exists_monomialRealizationGen_iff_exists_indexedTPP
#print axioms diagonal_coeff_unit_normal_form
#print axioms diagonal_coeff_normal_form

end GroupTPP.MonomialNormalForm
