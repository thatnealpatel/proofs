import BilinearComplexity.FieldFiveCircuitProfile

set_option autoImplicit false

open scoped BigOperators

namespace BilinearComplexity
namespace FieldTernaryFiveCircuitPair

open FieldRankOne
open FieldFiveCircuitProfile

abbrev F3 := ZMod 3

/-- Unit proportionality of ternary coordinate vectors. It is zero-aware (`SameRay 0 0`);
its interpretation as equality of projective rays applies only when both vectors are nonzero. -/
def SameRay {n : ℕ} (u v : Fin n → F3) : Prop :=
  u = v ∨ u = (2 : F3) • v

example : SameRay (fun _ : Fin 1 => (1 : F3)) (fun _ => 2) := by
  right
  funext i
  fin_cases i
  decide

/-- Over `F3`, explicit ray equality is the same as proportionality by a nonzero scalar. -/
theorem sameRay_iff_exists_smul {n : ℕ} {u v : Fin n → F3} :
    SameRay u v ↔ ∃ c : F3, c ≠ 0 ∧ u = c • v := by
  constructor
  · rintro (h | h)
    · exact ⟨1, one_ne_zero, by simpa only [one_smul] using h⟩
    · exact ⟨2, by decide, h⟩
  · rintro ⟨c, hc, h⟩
    have hc3 : c = 0 ∨ c = 1 ∨ c = 2 := by
      exact (by decide : ∀ d : F3, d = 0 ∨ d = 1 ∨ d = 2) c
    rcases hc3 with rfl | rfl | rfl
    · exact (hc rfl).elim
    · exact Or.inl (by simpa only [one_smul] using h)
    · exact Or.inr h

private theorem sameRay_refl {n : ℕ} (u : Fin n → F3) : SameRay u u :=
  Or.inl rfl

private theorem sameRay_symm {n : ℕ} {u v : Fin n → F3} :
    SameRay u v → SameRay v u := by
  rintro (h | h)
  · exact Or.inl h.symm
  · right
    rw [h]
    ext i
    simp only [Pi.smul_apply, smul_eq_mul]
    change v i = 2 * (2 * v i)
    rw [← mul_assoc, show (2 : F3) * 2 = 1 by decide, one_mul]

private theorem sameRay_trans {n : ℕ} {u v w : Fin n → F3} :
    SameRay u v → SameRay v w → SameRay u w := by
  rintro (huv | huv) (hvw | hvw)
  · exact Or.inl (huv.trans hvw)
  · exact Or.inr (huv.trans hvw)
  · exact Or.inr (huv.trans (congrArg ((2 : F3) • ·) hvw))
  · left
    rw [huv, hvw]
    ext i
    simp only [Pi.smul_apply, smul_eq_mul]
    change 2 * (2 * w i) = w i
    rw [← mul_assoc, show (2 : F3) * 2 = 1 by decide, one_mul]


/-- The coordinate minor detecting whether two vectors lie on one ray. -/
def detAt {n : ℕ} (u v : Fin n → F3) (p q : Fin n) : F3 :=
  u p * v q - u q * v p

example : detAt (fun i : Fin 2 => if i = 0 then 1 else 0)
    (fun i : Fin 2 => if i = 1 then 1 else 0) 0 1 = 1 := by
  decide

private theorem detAt_eq_zero_of_sameRay {n : ℕ} {u v : Fin n → F3}
    (h : SameRay u v) (p q : Fin n) : detAt u v p q = 0 := by
  rcases h with rfl | rfl
  · simp only [detAt]
    ring
  · simp only [detAt, Pi.smul_apply, smul_eq_mul]
    ring

private theorem sameRay_iff_forall_detAt_eq_zero {n : ℕ} {u v : Fin n → F3}
    (hu : u ≠ 0) (hv : v ≠ 0) :
    SameRay u v ↔ ∀ p q, detAt u v p q = 0 := by
  constructor
  · intro h p q
    exact detAt_eq_zero_of_sameRay h p q
  · intro h
    obtain ⟨p, hvp⟩ := Function.ne_iff.mp hv
    let c : F3 := u p / v p
    have huv : u = c • v := by
      funext q
      have hpq := h p q
      simp only [detAt] at hpq
      simp only [c, Pi.smul_apply, smul_eq_mul]
      rw [div_mul_eq_mul_div]
      apply (eq_div_iff hvp).mpr
      linear_combination -hpq
    have hc : c ≠ 0 := by
      intro hc
      apply hu
      rw [huv, hc, zero_smul]
    exact sameRay_iff_exists_smul.mpr ⟨c, hc, huv⟩

private theorem family_mem_span {n : ℕ} (v : Fin 5 → Fin n → F3) (i : Fin 5) :
    v i ∈ Submodule.span F3 (Set.range v) :=
  Submodule.subset_span (Set.mem_range_self i)

private theorem rank_two_ray_test {n : ℕ} (v : Fin 5 → Fin n → F3)
    (hv : ∀ i, v i ≠ 0) (hr : familyRank (k := F3) v = 2) (i : Fin 5) :
    ∃ p q : Fin n, ∀ j, detAt (v i) (v j) p q = 0 ↔ SameRay (v j) (v i) := by
  classical
  have ht : ∃ t : Fin 5, ¬SameRay (v t) (v i) := by
    by_contra hnone
    push Not at hnone
    let L : Submodule F3 (Fin n → F3) := F3 ∙ v i
    let U : Submodule F3 (Fin n → F3) := Submodule.span F3 (Set.range v)
    have hUL : U ≤ L := by
      apply Submodule.span_le.mpr
      rintro w ⟨j, rfl⟩
      obtain ⟨c, hc, heq⟩ := sameRay_iff_exists_smul.mp (hnone j)
      rw [heq]
      exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self (v i))
    have hle := Submodule.finrank_mono hUL
    have hLrank : Module.finrank F3 L = 1 := finrank_span_singleton (hv i)
    change familyRank (k := F3) v ≤ Module.finrank F3 L at hle
    rw [hr, hLrank] at hle
    omega
  obtain ⟨t, ht⟩ := ht
  let L : Submodule F3 (Fin n → F3) := F3 ∙ v i
  let P : Submodule F3 (Fin n → F3) := Submodule.span F3 {v i, v t}
  let U : Submodule F3 (Fin n → F3) := Submodule.span F3 (Set.range v)
  have hLP : L ≤ P := by
    apply Submodule.span_mono
    intro w hw
    have hw' : w = v i := Set.mem_singleton_iff.mp hw
    rw [hw']
    exact Set.mem_insert (v i) {v t}
  have hPU : P ≤ U := by
    apply Submodule.span_le.mpr
    intro w hw
    rcases hw with (rfl | hw)
    · exact family_mem_span v i
    · have hwt : w = v t := Set.mem_singleton_iff.mp hw
      rw [hwt]
      exact family_mem_span v t
  have hPrank : Module.finrank F3 P = 2 := by
    have hit : v i ≠ v t := by
      intro heq
      apply ht
      exact Or.inl heq.symm
    have hupper : Module.finrank F3 P ≤ 2 := by
      convert finrank_span_le_card (R := F3) ({v i, v t} : Set (Fin n → F3)) using 1
      simp [hit]
    have hlower : 2 ≤ Module.finrank F3 P := by
      by_contra hnot
      have hPle : Module.finrank F3 P ≤ 1 := by omega
      have hLrank : Module.finrank F3 L = 1 := finrank_span_singleton (hv i)
      have hLP_eq : L = P :=
        Submodule.eq_of_le_of_finrank_le hLP (by simpa only [hLrank] using hPle)
      apply ht
      have htmem : v t ∈ L := by
        rw [hLP_eq]
        exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp htmem
      have hc0 : c ≠ 0 := by
        intro hc0
        apply hv t
        rw [← hc, hc0, zero_smul]
      exact sameRay_iff_exists_smul.mpr ⟨c, hc0, hc.symm⟩
    omega
  have hPUeq : P = U := by
    apply Submodule.eq_of_le_of_finrank_le hPU
    change familyRank (k := F3) v ≤ Module.finrank F3 P
    rw [hr, hPrank]
  have hdet : ∃ p q, detAt (v i) (v t) p q ≠ 0 := by
    by_contra hzero
    push Not at hzero
    apply ht
    apply sameRay_symm
    exact (sameRay_iff_forall_detAt_eq_zero (hv i) (hv t)).mpr hzero
  obtain ⟨p, q, hpq⟩ := hdet
  refine ⟨p, q, fun j => ?_⟩
  have hjmem : v j ∈ P := by
    rw [hPUeq]
    exact family_mem_span v j
  obtain ⟨A, B, hAB⟩ := Submodule.mem_span_pair.mp hjmem
  have hformula : detAt (v i) (v j) p q = B * detAt (v i) (v t) p q := by
    rw [← hAB]
    simp only [detAt, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  constructor
  · intro hzero
    have hB : B = 0 := by
      apply (mul_eq_zero.mp (hformula ▸ hzero)).resolve_right hpq
    have hjA : v j = A • v i := by
      rw [← hAB, hB, zero_smul, add_zero]
    have hA : A ≠ 0 := by
      intro hA
      apply hv j
      rw [hjA, hA, zero_smul]
    exact sameRay_iff_exists_smul.mpr ⟨A, hA, hjA⟩
  · intro hsame
    exact detAt_eq_zero_of_sameRay (sameRay_symm hsame) p q


private theorem one_vector_relation_false {n : ℕ} {A : F3} {u : Fin n → F3}
    (hA : A ≠ 0) (hu : u ≠ 0) (h : ∀ p, A * u p = 0) : False := by
  obtain ⟨p, hp⟩ := Function.ne_iff.mp hu
  exact mul_ne_zero hA hp (h p)

private theorem sameRay_of_two_vector_relation {n : ℕ} {A B : F3}
    {u v : Fin n → F3} (hA : A ≠ 0) (hB : B ≠ 0)
    (h : ∀ p, A * u p + B * v p = 0) : SameRay u v := by
  let c : F3 := -B / A
  have hc : c ≠ 0 := div_ne_zero (neg_ne_zero.mpr hB) hA
  apply sameRay_iff_exists_smul.mpr
  refine ⟨c, hc, ?_⟩
  funext p
  simp only [c, Pi.smul_apply, smul_eq_mul]
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hA).mpr
  linear_combination h p

private theorem two_outer_relation {b c : ℕ} {A B : F3}
    {y₁ y₂ : Fin b → F3} {z₁ z₂ : Fin c → F3}
    (hA : A ≠ 0) (hB : B ≠ 0) (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0)
    (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0)
    (h : ∀ p q, A * y₁ p * z₁ q + B * y₂ p * z₂ q = 0) :
    SameRay y₁ y₂ ∧ SameRay z₁ z₂ := by
  obtain ⟨p, hyp⟩ := Function.ne_iff.mp hy₁
  have hy₂p : y₂ p ≠ 0 := by
    intro hy₂p
    obtain ⟨q, hzq⟩ := Function.ne_iff.mp hz₁
    have hpq := h p q
    rw [hy₂p, mul_zero, zero_mul, add_zero] at hpq
    exact mul_ne_zero (mul_ne_zero hA hyp) hzq hpq
  have hz : SameRay z₁ z₂ := by
    apply sameRay_of_two_vector_relation (mul_ne_zero hA hyp) (mul_ne_zero hB hy₂p)
    intro q
    exact h p q
  obtain ⟨q, hzq⟩ := Function.ne_iff.mp hz₁
  have hz₂q : z₂ q ≠ 0 := by
    intro hz₂q
    obtain ⟨p', hyp'⟩ := Function.ne_iff.mp hy₁
    have hpq := h p' q
    rw [hz₂q, mul_zero, add_zero] at hpq
    exact mul_ne_zero (mul_ne_zero hA hyp') hzq hpq
  have hy : SameRay y₁ y₂ := by
    apply sameRay_of_two_vector_relation (mul_ne_zero hA hzq) (mul_ne_zero hB hz₂q)
    intro p'
    have hpq := h p' q
    linear_combination hpq
  exact ⟨hy, hz⟩

private theorem three_outer_common_right_of_not_same_left {b c : ℕ}
    {A B C : F3} {y₀ y₁ y₂ : Fin b → F3} {z₀ z₁ z₂ : Fin c → F3}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hy₀ : y₀ ≠ 0) (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0)
    (hz₀ : z₀ ≠ 0) (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0)
    (hnray : ¬SameRay y₁ y₀)
    (h : ∀ p q, A * y₀ p * z₀ q + B * y₁ p * z₁ q + C * y₂ p * z₂ q = 0) :
    SameRay z₁ z₀ ∧ SameRay z₂ z₀ := by
  have hminor₀₁ : ∃ p q, detAt y₀ y₁ p q ≠ 0 := by
    by_contra hzero
    push Not at hzero
    apply hnray
    apply sameRay_symm
    exact (sameRay_iff_forall_detAt_eq_zero hy₀ hy₁).mpr hzero
  obtain ⟨p, q, hpq⟩ := hminor₀₁
  have hcontract₀ (l : Fin c) :
      (B * detAt y₀ y₁ p q) * z₁ l +
        (C * detAt y₀ y₂ p q) * z₂ l = 0 := by
    have hp := h p l
    have hq := h q l
    simp only [detAt]
    linear_combination y₀ p * hq - y₀ q * hp
  have hminor₀₂ : detAt y₀ y₂ p q ≠ 0 := by
    intro hzero
    have hone : ∀ l, (B * detAt y₀ y₁ p q) * z₁ l = 0 := by
      intro l
      simpa only [hzero, mul_zero, zero_mul, add_zero] using hcontract₀ l
    exact one_vector_relation_false (mul_ne_zero hB hpq) hz₁ hone
  have hz₁₂ : SameRay z₁ z₂ :=
    sameRay_of_two_vector_relation (mul_ne_zero hB hpq)
      (mul_ne_zero hC hminor₀₂) hcontract₀
  have hminor₁₀ : detAt y₁ y₀ p q ≠ 0 := by
    intro hzero
    apply hpq
    simp only [detAt] at hzero ⊢
    linear_combination -hzero
  have hcontract₁ (l : Fin c) :
      (A * detAt y₁ y₀ p q) * z₀ l +
        (C * detAt y₁ y₂ p q) * z₂ l = 0 := by
    have hp := h p l
    have hq := h q l
    simp only [detAt]
    linear_combination y₁ p * hq - y₁ q * hp
  have hminor₁₂ : detAt y₁ y₂ p q ≠ 0 := by
    intro hzero
    have hone : ∀ l, (A * detAt y₁ y₀ p q) * z₀ l = 0 := by
      intro l
      simpa only [hzero, mul_zero, zero_mul, add_zero] using hcontract₁ l
    exact one_vector_relation_false (mul_ne_zero hA hminor₁₀) hz₀ hone
  have hz₀₂ : SameRay z₀ z₂ :=
    sameRay_of_two_vector_relation (mul_ne_zero hA hminor₁₀)
      (mul_ne_zero hC hminor₁₂) hcontract₁
  exact ⟨sameRay_trans hz₁₂ (sameRay_symm hz₀₂), sameRay_symm hz₀₂⟩

private theorem three_outer_relation_dichotomy {b c : ℕ}
    {A B C : F3} {y₀ y₁ y₂ : Fin b → F3} {z₀ z₁ z₂ : Fin c → F3}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hy₀ : y₀ ≠ 0) (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0)
    (hz₀ : z₀ ≠ 0) (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0)
    (h : ∀ p q, A * y₀ p * z₀ q + B * y₁ p * z₁ q + C * y₂ p * z₂ q = 0) :
    (SameRay y₁ y₀ ∧ SameRay y₂ y₀) ∨
      (SameRay z₁ z₀ ∧ SameRay z₂ z₀) := by
  by_cases hy₁₀ : SameRay y₁ y₀
  · by_cases hy₂₀ : SameRay y₂ y₀
    · exact Or.inl ⟨hy₁₀, hy₂₀⟩
    · right
      have hz := three_outer_common_right_of_not_same_left hA hC hB
        hy₀ hy₂ hy₁ hz₀ hz₂ hz₁ hy₂₀ (fun p q => by
          have hpq := h p q
          linear_combination hpq)
      exact ⟨hz.2, hz.1⟩
  · exact Or.inr (three_outer_common_right_of_not_same_left hA hB hC
      hy₀ hy₁ hy₂ hz₀ hz₁ hz₂ hy₁₀ h)

private theorem relation_pointwise {a b c : ℕ} {x : Fin 5 → Fin a → F3}
    {y : Fin 5 → Fin b → F3} {z : Fin 5 → Fin c → F3} {q : Fin 5 → F3}
    (h : IsProductRelation x y z q) :
    ∀ p j l, ∑ i, q i * x i p * y i j * z i l = 0 := by
  intro p j l
  have hp := congrFun (congrFun (congrFun h p) j) l
  simpa only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, evalFactors,
    one_mul, smul_eq_mul, mul_assoc] using hp

private theorem rank_one_all_sameRay {n : ℕ} (v : Fin 5 → Fin n → F3)
    (hv : ∀ i, v i ≠ 0) (hr : familyRank (k := F3) v = 1) :
    ∀ i j, SameRay (v i) (v j) := by
  intro i j
  let L : Submodule F3 (Fin n → F3) := F3 ∙ v j
  let U : Submodule F3 (Fin n → F3) := Submodule.span F3 (Set.range v)
  have hLU : L ≤ U := by
    apply Submodule.span_le.mpr
    intro w hw
    obtain rfl := Set.mem_singleton_iff.mp hw
    exact family_mem_span v j
  have hLrank : Module.finrank F3 L = 1 := finrank_span_singleton (hv j)
  have hUrank : Module.finrank F3 U = 1 := hr
  have hLUeq : L = U :=
    Submodule.eq_of_le_of_finrank_le hLU (by rw [hLrank, hUrank])
  have hmem : v i ∈ L := by
    rw [hLUeq]
    exact family_mem_span v i
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hc0 : c ≠ 0 := by
    intro hzero
    apply hv i
    rw [← hc, hzero, zero_smul]
  exact sameRay_iff_exists_smul.mpr ⟨c, hc0, hc.symm⟩

private theorem rank_le_two_has_repeated_ray {n : ℕ} (v : Fin 5 → Fin n → F3)
    (hv : ∀ i, v i ≠ 0) (hr : familyRank (k := F3) v ≤ 2) :
    ∃ i j, i ≠ j ∧ SameRay (v i) (v j) := by
  classical
  by_contra hnone
  push Not at hnone
  let U : Submodule F3 (Fin n → F3) := Submodule.span F3 (Set.range v)
  let f : Fin 5 × Fin 2 → U := fun p =>
    ⟨(if p.2 = 0 then (1 : F3) else 2) • v p.1,
      U.smul_mem _ (family_mem_span v p.1)⟩
  have hf : Function.Injective f := by
    rintro ⟨i, s⟩ ⟨j, t⟩ h
    have heq : (if s = 0 then (1 : F3) else 2) • v i =
        (if t = 0 then (1 : F3) else 2) • v j :=
      congrArg Subtype.val h
    by_cases hij : i = j
    · subst j
      have hst : s = t := by
        fin_cases s <;> fin_cases t
        · rfl
        · exfalso
          have hscalar : (1 : F3) = 2 := by
            apply (smul_left_injective F3 (hv i))
            simpa using heq
          exact (by decide : (1 : F3) ≠ 2) hscalar
        · exfalso
          have hscalar : (2 : F3) = 1 := by
            apply (smul_left_injective F3 (hv i))
            simpa using heq
          exact (by decide : (2 : F3) ≠ 1) hscalar
        · rfl
      subst t
      rfl
    · exfalso
      apply hnone i j hij
      fin_cases s <;> fin_cases t
      · exact Or.inl (by simpa using heq)
      · exact Or.inr (by simpa using heq)
      · apply sameRay_symm
        exact Or.inr (by simpa using heq.symm)
      · exact Or.inl (by
          apply (smul_right_injective (Fin n → F3) (by decide : (2 : F3) ≠ 0))
          simpa using heq)
  have hcardLower : 10 ≤ Fintype.card U := by
    simpa only [Fintype.card_prod, Fintype.card_fin, Nat.reduceMul] using
      Fintype.card_le_of_injective f hf
  let bU := Module.finBasis F3 U
  have hcardU : Fintype.card U = 3 ^ Module.finrank F3 U := by
    simpa only [Fintype.card_fin, ZMod.card] using Module.card_fintype bU
  have hfinrank : Module.finrank F3 U ≤ 2 := hr
  have hcardUpper : Fintype.card U ≤ 9 := by
    rw [hcardU]
    have hdim : Module.finrank F3 U = 0 ∨ Module.finrank F3 U = 1 ∨
        Module.finrank F3 U = 2 := by omega
    rcases hdim with hdim | hdim | hdim <;> rw [hdim] <;> norm_num
  omega



private theorem rank_two_has_other_ray {n : ℕ} (v : Fin 5 → Fin n → F3)
    (hv : ∀ i, v i ≠ 0) (hr : familyRank (k := F3) v = 2) (i : Fin 5) :
    ∃ j, ¬SameRay (v j) (v i) := by
  by_contra hnone
  push Not at hnone
  let L : Submodule F3 (Fin n → F3) := F3 ∙ v i
  let U : Submodule F3 (Fin n → F3) := Submodule.span F3 (Set.range v)
  have hUL : U ≤ L := by
    apply Submodule.span_le.mpr
    rintro w ⟨j, rfl⟩
    obtain ⟨c, hc, heq⟩ := sameRay_iff_exists_smul.mp (hnone j)
    rw [heq]
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self (v i))
  have hle := Submodule.finrank_mono hUL
  have hLrank : Module.finrank F3 L = 1 := finrank_span_singleton (hv i)
  change familyRank (k := F3) v ≤ Module.finrank F3 L at hle
  rw [hr, hLrank] at hle
  omega

private theorem secondary_support_conclusion {a b c : ℕ}
    (u : Fin 5 → Fin a → F3) (v : Fin 5 → Fin b → F3)
    (w : Fin 5 → Fin c → F3)
    (hu : ∀ i, u i ≠ 0) (hv : ∀ i, v i ≠ 0) (hw : ∀ i, w i ≠ 0)
    (q : Fin 5 → F3) (hq : ∀ i, q i ≠ 0)
    (hrel : ∀ p j l, ∑ i, q i * u i p * v i j * w i l = 0)
    (hvrank : familyRank (k := F3) v = 2)
    (S : Finset (Fin 5)) (hScard : S.card = 3) (r : Fin 5)
    (hrS : r ∈ S) (hcommon : ∀ k ∈ S, SameRay (v k) (v r))
    (i j : Fin 5) (hij : i ≠ j) (huij : SameRay (u i) (u j)) :
    ∃ m n, m ≠ n ∧
      ((SameRay (u m) (u n) ∧ SameRay (v m) (v n)) ∨
        (SameRay (u m) (u n) ∧ SameRay (w m) (w n))) := by
  classical
  obtain ⟨p₀, p₁, htest⟩ := rank_two_ray_test v hv hvrank r
  let d : Fin 5 → F3 := fun k => detAt (v r) (v k) p₀ p₁
  let T : Finset (Fin 5) := Finset.univ.filter fun k => d k ≠ 0
  have hTmem (k : Fin 5) : k ∈ T ↔ d k ≠ 0 := by simp only [T, Finset.mem_filter,
    Finset.mem_univ, true_and]
  have hdtest (k : Fin 5) : d k = 0 ↔ SameRay (v k) (v r) := htest k
  have hdisj : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro k hkS hkT
    exact (hTmem k).mp hkT ((hdtest k).mpr (hcommon k hkS))
  have hcardT : T.card ≤ 2 := by
    have hunion : (S ∪ T).card ≤ 5 := by
      simpa only [Fintype.card_fin] using Finset.card_le_univ (S ∪ T)
    rw [Finset.card_union_of_disjoint hdisj, hScard] at hunion
    omega
  have hcontract (p : Fin a) (l : Fin c) :
      ∑ k, (q k * d k) * u k p * w k l = 0 := by
    have h₀ := hrel p p₀ l
    have h₁ := hrel p p₁ l
    calc
      ∑ k, (q k * d k) * u k p * w k l =
          v r p₀ * (∑ k, q k * u k p * v k p₁ * w k l) -
            v r p₁ * (∑ k, q k * u k p * v k p₀ * w k l) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        simp only [d, detAt]
        ring
      _ = 0 := by rw [h₀, h₁]; ring
  have hrelT (p : Fin a) (l : Fin c) :
      ∑ k ∈ T, (q k * d k) * u k p * w k l = 0 := by
    rw [Finset.sum_subset (Finset.subset_univ T)]
    · exact hcontract p l
    · intro k hkU hkT
      have hdk : d k = 0 := not_ne_iff.mp (mt (hTmem k).mpr hkT)
      simp only [hdk, mul_zero, zero_mul]
  have hcardCases : T.card = 0 ∨ T.card = 1 ∨ T.card = 2 := by omega
  rcases hcardCases with hT0 | hT1 | hT2
  · have hTempty : T = ∅ := Finset.card_eq_zero.mp hT0
    have hvij : SameRay (v i) (v j) := by
      have hi0 : d i = 0 := by
        by_contra hi
        have : i ∈ T := (hTmem i).mpr hi
        simpa [hTempty] using this
      have hj0 : d j = 0 := by
        by_contra hj
        have : j ∈ T := (hTmem j).mpr hj
        simpa [hTempty] using this
      exact sameRay_trans (hdtest i |>.mp hi0) (sameRay_symm (hdtest j |>.mp hj0))
    exact ⟨i, j, hij, Or.inl ⟨huij, hvij⟩⟩
  · obtain ⟨s, hTs⟩ := Finset.card_eq_one.mp hT1
    have hsT : s ∈ T := by rw [hTs]; exact Finset.mem_singleton_self s
    have hds : d s ≠ 0 := (hTmem s).mp hsT
    obtain ⟨p, hup⟩ := Function.ne_iff.mp (hu s)
    obtain ⟨l, hwl⟩ := Function.ne_iff.mp (hw s)
    have hone := hrelT p l
    rw [hTs] at hone
    simp only [Finset.sum_singleton] at hone
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (hq s) hds) hup) hwl hone).elim
  · obtain ⟨s, t, hst, hTst⟩ := Finset.card_eq_two.mp hT2
    have hsT : s ∈ T := by rw [hTst]; exact Finset.mem_insert_self s {t}
    have htT : t ∈ T := by rw [hTst]; simp
    have houter : SameRay (u s) (u t) ∧ SameRay (w s) (w t) := by
      apply two_outer_relation (mul_ne_zero (hq s) ((hTmem s).mp hsT))
        (mul_ne_zero (hq t) ((hTmem t).mp htT)) (hu s) (hu t) (hw s) (hw t)
      intro p l
      have hsum := hrelT p l
      rw [hTst] at hsum
      simpa [hTst, hst] using hsum
    exact ⟨s, t, hst, Or.inr houter⟩


private theorem rank222_pair {a b c : ℕ}
    (x : Fin 5 → Fin a → F3) (y : Fin 5 → Fin b → F3)
    (z : Fin 5 → Fin c → F3)
    (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0) (hz : ∀ i, z i ≠ 0)
    (q : Fin 5 → F3) (hq : ∀ i, q i ≠ 0)
    (hrel : IsProductRelation x y z q)
    (hrx : familyRank (k := F3) x = 2)
    (hry : familyRank (k := F3) y = 2)
    (hrz : familyRank (k := F3) z = 2) :
    ∃ i j, i ≠ j ∧
      ((SameRay (x i) (x j) ∧ SameRay (y i) (y j)) ∨
        (SameRay (x i) (x j) ∧ SameRay (z i) (z j)) ∨
        (SameRay (y i) (y j) ∧ SameRay (z i) (z j))) := by
  classical
  have hpoint := relation_pointwise hrel
  obtain ⟨i, j, hij, hxij⟩ := rank_le_two_has_repeated_ray x hx (by omega)
  obtain ⟨p₀, p₁, htest⟩ := rank_two_ray_test x hx hrx i
  let d : Fin 5 → F3 := fun k => detAt (x i) (x k) p₀ p₁
  let S : Finset (Fin 5) := Finset.univ.filter fun k => d k ≠ 0
  have hSmem (k : Fin 5) : k ∈ S ↔ d k ≠ 0 := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
  have hdtest (k : Fin 5) : d k = 0 ↔ SameRay (x k) (x i) := htest k
  have hiS : i ∉ S := by
    intro hi
    exact (hSmem i).mp hi ((hdtest i).mpr (sameRay_refl (x i)))
  have hjS : j ∉ S := by
    intro hj
    exact (hSmem j).mp hj ((hdtest j).mpr (sameRay_symm hxij))
  have hcardS : S.card ≤ 3 := by
    have hsub : S ⊆ (Finset.univ.erase i).erase j := by
      intro k hk
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact ⟨fun hkj => hjS (hkj ▸ hk), fun hki => hiS (hki ▸ hk)⟩
    have hcard := Finset.card_le_card hsub
    have herase : ((Finset.univ.erase i).erase j).card = 3 := by
      have hiU : i ∈ (Finset.univ : Finset (Fin 5)) := Finset.mem_univ i
      have hjE : j ∈ (Finset.univ.erase i : Finset (Fin 5)) := by
        simp only [Finset.mem_erase, Finset.mem_univ, and_true]
        exact Ne.symm hij
      rw [Finset.card_erase_of_mem hjE, Finset.card_erase_of_mem hiU]
      decide
    omega
  have hSnonempty : S.Nonempty := by
    obtain ⟨t, ht⟩ := rank_two_has_other_ray x hx hrx i
    refine ⟨t, (hSmem t).mpr ?_⟩
    intro hzero
    exact ht ((hdtest t).mp hzero)
  have hcontract (p : Fin b) (l : Fin c) :
      ∑ k, (q k * d k) * y k p * z k l = 0 := by
    have h₀ := hpoint p₀ p l
    have h₁ := hpoint p₁ p l
    calc
      ∑ k, (q k * d k) * y k p * z k l =
          x i p₀ * (∑ k, q k * x k p₁ * y k p * z k l) -
            x i p₁ * (∑ k, q k * x k p₀ * y k p * z k l) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        simp only [d, detAt]
        ring
      _ = 0 := by rw [h₀, h₁]; ring
  have hrelS (p : Fin b) (l : Fin c) :
      ∑ k ∈ S, (q k * d k) * y k p * z k l = 0 := by
    rw [Finset.sum_subset (Finset.subset_univ S)]
    · exact hcontract p l
    · intro k hkU hkS
      have hdk : d k = 0 := not_ne_iff.mp (mt (hSmem k).mpr hkS)
      simp only [hdk, mul_zero, zero_mul]
  have hcardCases : S.card = 1 ∨ S.card = 2 ∨ S.card = 3 := by
    have hpos := Finset.card_pos.mpr hSnonempty
    omega
  rcases hcardCases with hS1 | hS2 | hS3
  · obtain ⟨r, hSr⟩ := Finset.card_eq_one.mp hS1
    have hrS : r ∈ S := by rw [hSr]; exact Finset.mem_singleton_self r
    have hdr : d r ≠ 0 := (hSmem r).mp hrS
    obtain ⟨p, hyp⟩ := Function.ne_iff.mp (hy r)
    obtain ⟨l, hzl⟩ := Function.ne_iff.mp (hz r)
    have hone := hrelS p l
    rw [hSr] at hone
    simp only [Finset.sum_singleton] at hone
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (hq r) hdr) hyp) hzl hone).elim
  · obtain ⟨r, s, hrs, hSrs⟩ := Finset.card_eq_two.mp hS2
    have hrS : r ∈ S := by rw [hSrs]; exact Finset.mem_insert_self r {s}
    have hsS : s ∈ S := by rw [hSrs]; simp
    have houter : SameRay (y r) (y s) ∧ SameRay (z r) (z s) := by
      apply two_outer_relation (mul_ne_zero (hq r) ((hSmem r).mp hrS))
        (mul_ne_zero (hq s) ((hSmem s).mp hsS)) (hy r) (hy s) (hz r) (hz s)
      intro p l
      have hsum := hrelS p l
      rw [hSrs] at hsum
      simpa [hSrs, hrs] using hsum
    exact ⟨r, s, hrs, Or.inr (Or.inr houter)⟩
  · obtain ⟨r, s, t, hrs, hrt, hst, hSrst⟩ := Finset.card_eq_three.mp hS3
    have hrS : r ∈ S := by rw [hSrst]; simp
    have hsS : s ∈ S := by rw [hSrst]; simp
    have htS : t ∈ S := by rw [hSrst]; simp
    have hthree :
        (SameRay (y s) (y r) ∧ SameRay (y t) (y r)) ∨
          (SameRay (z s) (z r) ∧ SameRay (z t) (z r)) := by
      apply three_outer_relation_dichotomy
        (mul_ne_zero (hq r) ((hSmem r).mp hrS))
        (mul_ne_zero (hq s) ((hSmem s).mp hsS))
        (mul_ne_zero (hq t) ((hSmem t).mp htS))
        (hy r) (hy s) (hy t) (hz r) (hz s) (hz t)
      intro p l
      have hsum := hrelS p l
      rw [hSrst] at hsum
      simpa [hrs, hrt, hst, add_assoc] using hsum
    rcases hthree with hycommon | hzcommon
    · have hcommon : ∀ k ∈ S, SameRay (y k) (y r) := by
        intro k hk
        rw [hSrst] at hk
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl
        · exact sameRay_refl (y k)
        · exact hycommon.1
        · exact hycommon.2
      obtain ⟨m, n, hmn, hpair⟩ := secondary_support_conclusion x y z hx hy hz q hq
        hpoint hry S hS3 r hrS hcommon i j hij hxij
      exact ⟨m, n, hmn, hpair.elim Or.inl (fun h => Or.inr (Or.inl h))⟩
    · have hcommon : ∀ k ∈ S, SameRay (z k) (z r) := by
        intro k hk
        rw [hSrst] at hk
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl
        · exact sameRay_refl (z k)
        · exact hzcommon.1
        · exact hzcommon.2
      have hpoint' : ∀ p l qcoord, ∑ k, q k * x k p * z k l * y k qcoord = 0 := by
        intro p l qcoord
        calc
          ∑ k, q k * x k p * z k l * y k qcoord =
              ∑ k, q k * x k p * y k qcoord * z k l := by
            apply Finset.sum_congr rfl
            intro k hk
            ring
          _ = 0 := hpoint p qcoord l
      obtain ⟨m, n, hmn, hpair⟩ := secondary_support_conclusion x z y hx hz hy q hq
        hpoint' hrz S hS3 r hrS hcommon i j hij hxij
      exact ⟨m, n, hmn, hpair.elim (fun h => Or.inr (Or.inl h)) Or.inl⟩

private theorem profile_oriented_cases {rx ry rz : ℕ}
    (h : [rx, ry, rz].Perm [4, 1, 1] ∨ [rx, ry, rz].Perm [3, 2, 1] ∨
      [rx, ry, rz].Perm [2, 2, 1] ∨ [rx, ry, rz].Perm [2, 2, 2]) :
    (rx = 2 ∧ ry = 2 ∧ rz = 2) ∨
    (rx = 1 ∧ ry ≤ 2) ∨ (rx = 1 ∧ rz ≤ 2) ∨
    (ry = 1 ∧ rx ≤ 2) ∨ (ry = 1 ∧ rz ≤ 2) ∨
    (rz = 1 ∧ rx ≤ 2) ∨ (rz = 1 ∧ ry ≤ 2) := by
  rcases h with h | h | h | h
  all_goals
    have h1 := h.count_eq 1
    have h2 := h.count_eq 2
    simp only [List.count_cons, List.count_nil, beq_iff_eq] at h1 h2
    by_cases hx1 : rx = 1 <;> by_cases hy1 : ry = 1 <;> by_cases hz1 : rz = 1 <;>
      by_cases hx2 : rx = 2 <;> by_cases hy2 : ry = 2 <;> by_cases hz2 : rz = 2 <;>
      simp_all <;> omega


/-- A five-term factor family has two distinct indices sharing unit-proportional factors in
two modes. These are genuine projective rays only when the displayed factors are nonzero. -/
def HasSharedTwoRayPair {a b c : ℕ}
    (x : Fin 5 → Fin a → F3) (y : Fin 5 → Fin b → F3)
    (z : Fin 5 → Fin c → F3) : Prop :=
  ∃ i j, i ≠ j ∧
    ((SameRay (x i) (x j) ∧ SameRay (y i) (y j)) ∨
      (SameRay (x i) (x j) ∧ SameRay (z i) (z j)) ∨
      (SameRay (y i) (y j) ∧ SameRay (z i) (z j)))

example : HasSharedTwoRayPair
    (fun _ : Fin 5 => fun _ : Fin 1 => (1 : F3))
    (fun _ : Fin 5 => fun _ : Fin 1 => (1 : F3))
    (fun _ : Fin 5 => fun _ : Fin 1 => (1 : F3)) := by
  exact ⟨0, 1, by decide, Or.inl ⟨Or.inl rfl, Or.inl rfl⟩⟩

/-- Every nonzero minimal five-product circuit over `F3` contains two distinct terms whose
factors determine the same projective rays in two of the three modes. -/
theorem exists_shared_two_factor_rays {a b c : ℕ}
    (x : Fin 5 → Fin a → F3) (y : Fin 5 → Fin b → F3)
    (z : Fin 5 → Fin c → F3)
    (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0) (hz : ∀ i, z i ≠ 0)
    (hminimal : IsMinimalFiveProductCircuit x y z) :
    HasSharedTwoRayPair x y z := by
  obtain ⟨q, hqne, hrel⟩ := hminimal.1
  have hq : ∀ i, q i ≠ 0 := by
    intro i hqi
    have hqzero := hminimal.2 q hrel ⟨i, hqi⟩
    exact hqne hqzero
  have hprofile := profile_oriented_cases
    (factorRank_profile x y z hx hy hz hminimal)
  rcases hprofile with h222 | hx1y2 | hx1z2 | hy1x2 | hy1z2 | hz1x2 | hz1y2
  · exact rank222_pair x y z hx hy hz q hq hrel h222.1 h222.2.1 h222.2.2
  · obtain ⟨i, j, hij, hyij⟩ := rank_le_two_has_repeated_ray y hy hx1y2.2
    exact ⟨i, j, hij, Or.inl ⟨rank_one_all_sameRay x hx hx1y2.1 i j, hyij⟩⟩
  · obtain ⟨i, j, hij, hzij⟩ := rank_le_two_has_repeated_ray z hz hx1z2.2
    exact ⟨i, j, hij, Or.inr (Or.inl ⟨rank_one_all_sameRay x hx hx1z2.1 i j, hzij⟩)⟩
  · obtain ⟨i, j, hij, hxij⟩ := rank_le_two_has_repeated_ray x hx hy1x2.2
    exact ⟨i, j, hij, Or.inl ⟨hxij, rank_one_all_sameRay y hy hy1x2.1 i j⟩⟩
  · obtain ⟨i, j, hij, hzij⟩ := rank_le_two_has_repeated_ray z hz hy1z2.2
    exact ⟨i, j, hij, Or.inr (Or.inr ⟨rank_one_all_sameRay y hy hy1z2.1 i j, hzij⟩)⟩
  · obtain ⟨i, j, hij, hxij⟩ := rank_le_two_has_repeated_ray x hx hz1x2.2
    exact ⟨i, j, hij, Or.inr (Or.inl ⟨hxij, rank_one_all_sameRay z hz hz1x2.1 i j⟩)⟩
  · obtain ⟨i, j, hij, hyij⟩ := rank_le_two_has_repeated_ray y hy hz1y2.2
    exact ⟨i, j, hij, Or.inr (Or.inr ⟨hyij, rank_one_all_sameRay z hz hz1y2.1 i j⟩)⟩


/-- The three choices of two factor modes. -/
inductive Orientation where
  | xy
  | xz
  | yz
  deriving DecidableEq, Repr

/-- Concrete data tested by the bounded ternary shared-ray scan. -/
structure Candidate where
  first : Fin 5
  second : Fin 5
  orientation : Orientation
  firstScalar : F3
  secondScalar : F3
  deriving DecidableEq, Repr

/-- A scan candidate certifies distinct indices with nonzero product presentations and its two
displayed scalar proportionalities. Thus its ray claims have a genuine projective meaning. -/
def Candidate.Valid {a b c : ℕ} (candidate : Candidate)
    (x : Fin 5 → Fin a → F3) (y : Fin 5 → Fin b → F3)
    (z : Fin 5 → Fin c → F3) : Prop :=
  candidate.first ≠ candidate.second ∧
    (x candidate.first ≠ 0 ∧ y candidate.first ≠ 0 ∧ z candidate.first ≠ 0) ∧
    (x candidate.second ≠ 0 ∧ y candidate.second ≠ 0 ∧ z candidate.second ≠ 0) ∧
    candidate.firstScalar ≠ 0 ∧ candidate.secondScalar ≠ 0 ∧
    match candidate.orientation with
    | .xy => x candidate.first = candidate.firstScalar • x candidate.second ∧
        y candidate.first = candidate.secondScalar • y candidate.second
    | .xz => x candidate.first = candidate.firstScalar • x candidate.second ∧
        z candidate.first = candidate.secondScalar • z candidate.second
    | .yz => y candidate.first = candidate.firstScalar • y candidate.second ∧
        z candidate.first = candidate.secondScalar • z candidate.second

private instance candidateValidDecidable {a b c : ℕ} (candidate : Candidate)
    (x : Fin 5 → Fin a → F3) (y : Fin 5 → Fin b → F3)
    (z : Fin 5 → Fin c → F3) : Decidable (candidate.Valid x y z) := by
  unfold Candidate.Valid
  cases candidate.orientation <;> infer_instance

example : Candidate.Valid ⟨0, 1, .xy, 1, 1⟩
    (fun _ : Fin 5 => fun _ : Fin 1 => (1 : F3))
    (fun _ : Fin 5 => fun _ : Fin 1 => (1 : F3))
    (fun _ : Fin 5 => fun _ : Fin 1 => (1 : F3)) := by
  decide

/-- The finite search space: ordered distinctness is checked by `Candidate.Valid`, while both
ray scalars are drawn only from the two nonzero elements of `F3`. -/
def candidates : List Candidate :=
  (List.ofFn (fun i : Fin 5 => i)).flatMap fun i =>
    (List.ofFn (fun j : Fin 5 => j)).flatMap fun j =>
      [.xy, .xz, .yz].flatMap fun orientation =>
        ([1, 2] : List F3).flatMap fun firstScalar =>
          ([1, 2] : List F3).map fun secondScalar =>
            ⟨i, j, orientation, firstScalar, secondScalar⟩

private theorem candidate_mem_candidates (i j : Fin 5) (orientation : Orientation)
    (horientation : orientation ∈ [.xy, .xz, .yz]) (s t : F3)
    (hs : s ∈ ([1, 2] : List F3)) (ht : t ∈ ([1, 2] : List F3)) :
    (⟨i, j, orientation, s, t⟩ : Candidate) ∈ candidates := by
  simp only [candidates, List.mem_flatMap, List.mem_ofFn, List.mem_map]
  exact ⟨i, ⟨i, rfl⟩, j, ⟨j, rfl⟩, orientation, horientation, s, hs, t, ht, rfl⟩

example : (⟨0, 1, .xy, 1, 1⟩ : Candidate) ∈ candidates := by
  apply candidate_mem_candidates
  · simp
  · simp
  · simp

/-- Executably scan all index pairs, orientations, and nonzero ternary ray scalars. -/
def scan {a b c : ℕ} (x : Fin 5 → Fin a → F3) (y : Fin 5 → Fin b → F3)
    (z : Fin 5 → Fin c → F3) : Option Candidate :=
  candidates.find? fun candidate => decide (candidate.Valid x y z)

example : (scan
    (fun _ : Fin 5 => fun _ : Fin 1 => (1 : F3))
    (fun _ : Fin 5 => fun _ : Fin 1 => (1 : F3))
    (fun _ : Fin 5 => fun _ : Fin 1 => (1 : F3))).isSome = true := by
  decide

private theorem candidate_valid_has_shared_pair {a b c : ℕ} {candidate : Candidate}
    {x : Fin 5 → Fin a → F3} {y : Fin 5 → Fin b → F3}
    {z : Fin 5 → Fin c → F3} (hvalid : candidate.Valid x y z) :
    HasSharedTwoRayPair x y z := by
  rcases hvalid with ⟨hneq, _hfirst, _hsecond, hsx, hsy, horiented⟩
  refine ⟨candidate.first, candidate.second, hneq, ?_⟩
  cases ho : candidate.orientation with
  | xy =>
      rw [ho] at horiented
      exact Or.inl ⟨sameRay_iff_exists_smul.mpr ⟨_, hsx, horiented.1⟩,
        sameRay_iff_exists_smul.mpr ⟨_, hsy, horiented.2⟩⟩
  | xz =>
      rw [ho] at horiented
      exact Or.inr (Or.inl ⟨sameRay_iff_exists_smul.mpr ⟨_, hsx, horiented.1⟩,
        sameRay_iff_exists_smul.mpr ⟨_, hsy, horiented.2⟩⟩)
  | yz =>
      rw [ho] at horiented
      exact Or.inr (Or.inr ⟨sameRay_iff_exists_smul.mpr ⟨_, hsx, horiented.1⟩,
        sameRay_iff_exists_smul.mpr ⟨_, hsy, horiented.2⟩⟩)

/-- Every candidate returned by `scan` consists of two nonzero product presentations and
certifies genuine shared projective rays in its selected two modes. -/
theorem scan_sound {a b c : ℕ} {candidate : Candidate}
    {x : Fin 5 → Fin a → F3} {y : Fin 5 → Fin b → F3}
    {z : Fin 5 → Fin c → F3} (hscan : scan x y z = some candidate) :
    candidate.Valid x y z := by
  unfold scan at hscan
  have hvalid : decide (candidate.Valid x y z) = true :=
    List.find?_some (p := fun tested : Candidate => decide (Candidate.Valid tested x y z)) hscan
  exact of_decide_eq_true hvalid

private theorem scalar_mem_nonzero_choices (s : F3) (hs : s ≠ 0) : s ∈ ([1, 2] : List F3) := by
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 :=
    (by decide : ∀ t : F3, t = 0 ∨ t = 1 ∨ t = 2) s
  rcases hcases with rfl | rfl | rfl
  · exact (hs rfl).elim
  · simp
  · simp

private theorem candidate_exists_of_shared_pair {a b c : ℕ}
    {x : Fin 5 → Fin a → F3} {y : Fin 5 → Fin b → F3}
    {z : Fin 5 → Fin c → F3}
    (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0) (hz : ∀ i, z i ≠ 0)
    (hpair : HasSharedTwoRayPair x y z) :
    ∃ candidate ∈ candidates, candidate.Valid x y z := by
  obtain ⟨i, j, hij, hxy | hxz | hyz⟩ := hpair
  · obtain ⟨sx, hsx, hxeq⟩ := sameRay_iff_exists_smul.mp hxy.1
    obtain ⟨sy, hsy, hyeq⟩ := sameRay_iff_exists_smul.mp hxy.2
    let candidate : Candidate := ⟨i, j, .xy, sx, sy⟩
    refine ⟨candidate, ?_, hij, ⟨hx i, hy i, hz i⟩, ⟨hx j, hy j, hz j⟩,
      hsx, hsy, hxeq, hyeq⟩
    apply candidate_mem_candidates
    · simp
    · exact scalar_mem_nonzero_choices sx hsx
    · exact scalar_mem_nonzero_choices sy hsy
  · obtain ⟨sx, hsx, hxeq⟩ := sameRay_iff_exists_smul.mp hxz.1
    obtain ⟨sz, hsz, hzeq⟩ := sameRay_iff_exists_smul.mp hxz.2
    let candidate : Candidate := ⟨i, j, .xz, sx, sz⟩
    refine ⟨candidate, ?_, hij, ⟨hx i, hy i, hz i⟩, ⟨hx j, hy j, hz j⟩,
      hsx, hsz, hxeq, hzeq⟩
    apply candidate_mem_candidates
    · simp
    · exact scalar_mem_nonzero_choices sx hsx
    · exact scalar_mem_nonzero_choices sz hsz
  · obtain ⟨sy, hsy, hyeq⟩ := sameRay_iff_exists_smul.mp hyz.1
    obtain ⟨sz, hsz, hzeq⟩ := sameRay_iff_exists_smul.mp hyz.2
    let candidate : Candidate := ⟨i, j, .yz, sy, sz⟩
    refine ⟨candidate, ?_, hij, ⟨hx i, hy i, hz i⟩, ⟨hx j, hy j, hz j⟩,
      hsy, hsz, hyeq, hzeq⟩
    apply candidate_mem_candidates
    · simp
    · exact scalar_mem_nonzero_choices sy hsy
    · exact scalar_mem_nonzero_choices sz hsz

/-- The bounded scan succeeds for every nonzero minimal ternary five-product circuit. -/
theorem scan_isSome {a b c : ℕ}
    (x : Fin 5 → Fin a → F3) (y : Fin 5 → Fin b → F3)
    (z : Fin 5 → Fin c → F3)
    (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0) (hz : ∀ i, z i ≠ 0)
    (hminimal : IsMinimalFiveProductCircuit x y z) :
    (scan x y z).isSome = true := by
  unfold scan
  apply List.find?_isSome.mpr
  obtain ⟨candidate, hmem, hvalid⟩ := candidate_exists_of_shared_pair hx hy hz
    (exists_shared_two_factor_rays x y z hx hy hz hminimal)
  exact ⟨candidate, hmem, decide_eq_true hvalid⟩

/-- The proof-bearing total result of the executable bounded shared-ray scan. -/
def certifiedScan {a b c : ℕ}
    (x : Fin 5 → Fin a → F3) (y : Fin 5 → Fin b → F3)
    (z : Fin 5 → Fin c → F3)
    (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0) (hz : ∀ i, z i ≠ 0)
    (hminimal : IsMinimalFiveProductCircuit x y z) :
    {candidate : Candidate // Candidate.Valid candidate x y z} := by
  let hisSome := scan_isSome x y z hx hy hz hminimal
  let candidate := (scan x y z).get hisSome
  exact ⟨candidate, scan_sound (Option.some_get hisSome).symm⟩

set_option maxRecDepth 10000 in
/-- The bounded scan enumerates exactly five-by-five ordered index choices, three orientations,
and two choices for each of its two nonzero scalars. -/
theorem candidates_length : candidates.length = 300 := by
  decide

/-- The strengthened standalone scan rejects five presentations whose factors are all zero. -/
theorem scan_all_zero_eq_none :
    scan
      (fun _ : Fin 5 => fun _ : Fin 1 => (0 : F3))
      (fun _ : Fin 5 => fun _ : Fin 1 => (0 : F3))
      (fun _ : Fin 5 => fun _ : Fin 1 => (0 : F3)) = none := by
  decide

#eval scan
  (fun _ : Fin 5 => fun _ : Fin 1 => (0 : F3))
  (fun _ : Fin 5 => fun _ : Fin 1 => (0 : F3))
  (fun _ : Fin 5 => fun _ : Fin 1 => (0 : F3))

/-- In zero coordinate dimensions every factor vector is zero, so the scan returns no
projective certificate. -/
theorem scan_zero_dimensional_eq_none :
    scan
      (fun _ : Fin 5 => fun i : Fin 0 => Fin.elim0 i)
      (fun _ : Fin 5 => fun i : Fin 0 => Fin.elim0 i)
      (fun _ : Fin 5 => fun i : Fin 0 => Fin.elim0 i) = none := by
  decide

#eval scan
  (fun _ : Fin 5 => fun i : Fin 0 => Fin.elim0 i)
  (fun _ : Fin 5 => fun i : Fin 0 => Fin.elim0 i)
  (fun _ : Fin 5 => fun i : Fin 0 => Fin.elim0 i)


/-- The proof-bearing result of running the bounded scan on the genuine ternary fixture. -/
def fixtureCertificate :
    {candidate : Candidate // Candidate.Valid candidate F3Fixture.first F3Fixture.second
      F3Fixture.third} :=
  certifiedScan F3Fixture.first F3Fixture.second F3Fixture.third
    F3Fixture.factors_nonzero.1 F3Fixture.factors_nonzero.2.1
    F3Fixture.factors_nonzero.2.2 F3Fixture.isMinimalFiveProductCircuit

example : Candidate.Valid fixtureCertificate.val F3Fixture.first F3Fixture.second
    F3Fixture.third := fixtureCertificate.property


#eval fixtureCertificate.val

#eval scan F3Fixture.first F3Fixture.second F3Fixture.third

/-- Kernel-checked execution of the bounded scan on the genuine ternary fixture. -/
theorem fixture_scan_execution :
    scan F3Fixture.first F3Fixture.second F3Fixture.third =
      some ⟨0, 2, .xz, 2, 1⟩ := by
  decide

example : Candidate.Valid ⟨0, 2, .xz, 2, 1⟩ F3Fixture.first F3Fixture.second
    F3Fixture.third := scan_sound fixture_scan_execution

#check @SameRay
#check @sameRay_iff_exists_smul
#check @HasSharedTwoRayPair
#check @exists_shared_two_factor_rays
#check @Candidate.Valid
#check @scan_sound
#check @scan_isSome
#check @certifiedScan
#check candidates_length
#check scan_all_zero_eq_none
#check scan_zero_dimensional_eq_none
#check fixture_scan_execution

#print axioms sameRay_iff_exists_smul
#print axioms exists_shared_two_factor_rays
#print axioms scan_sound
#print axioms scan_isSome
#print axioms candidates_length
#print axioms scan_all_zero_eq_none
#print axioms scan_zero_dimensional_eq_none
#print axioms fixture_scan_execution

end FieldTernaryFiveCircuitPair
end BilinearComplexity
