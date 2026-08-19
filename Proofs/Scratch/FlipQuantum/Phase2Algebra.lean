/-
  Scratch/FlipQuantum/Phase2Algebra — algebraic invariants and reduction for flips.
-/
import Scratch.FlipQuantum.Phase1Schemes

set_option autoImplicit false

namespace BilinearComplexity.FlipQuantum

namespace Scheme

variable {k : Type*} {a b c r : ℕ} [Field k]

/-- Two functions on a finite type have equal sums if they agree away from two
 distinct indices and the sum of their values at those indices agrees. -/
private theorem sum_eq_of_eq_off_two {ι M : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommMonoid M] (f g : ι → M) (i j : ι) (hij : i ≠ j)
    (hoff : ∀ s, s ≠ i → s ≠ j → f s = g s)
    (hpair : f i + f j = g i + g j) : ∑ s, f s = ∑ s, g s := by
  classical
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)]
  have hrest : (∑ x ∈ (Finset.univ.erase i).erase j, f x) =
      ∑ x ∈ (Finset.univ.erase i).erase j, g x := by
    apply Finset.sum_congr rfl
    intro s hs
    exact hoff s (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hs))
      (Finset.ne_of_mem_erase hs)
  calc
    (∑ x ∈ (Finset.univ.erase i).erase j, f x) + f j + f i =
        (∑ x ∈ (Finset.univ.erase i).erase j, f x) + (f i + f j) := by ac_rfl
    _ = (∑ x ∈ (Finset.univ.erase i).erase j, f x) + (g i + g j) := by rw [hpair]
    _ = (∑ x ∈ (Finset.univ.erase i).erase j, f x) + g j + g i := by ac_rfl
    _ = (∑ x ∈ (Finset.univ.erase i).erase j, g x) + g j + g i := by rw [hrest]

#check @sum_eq_of_eq_off_two
#print axioms sum_eq_of_eq_off_two

/-- A raw first-mode shear preserves the represented tensor when its two first
 factors are literally equal. -/
theorem sumTensor_flipFirst (S : Scheme k a b c r) (i j : Fin r) (q : k)
    (hij : i ≠ j) (hshared : (S.term i).1 = (S.term j).1) :
    (S.flipFirst i j q).sumTensor = S.sumTensor := by
  funext x y z
  apply sum_eq_of_eq_off_two _ _ i j hij
  · intro s hsi hsj
    have hs : (S.flipFirst i j q).term s = S.term s := by
      simp [flipFirst, hsi, hsj]
    rw [hs]
  · have hx := congrFun hshared x
    have hi : (S.flipFirst i j q).term i =
        ((S.term i).1, (S.term i).2.1 + q • (S.term j).2.1,
          (S.term i).2.2) := by
      simp [flipFirst, hij]
    have hj : (S.flipFirst i j q).term j =
        ((S.term j).1, (S.term j).2.1,
          (S.term j).2.2 - q • (S.term i).2.2) := by
      simp [flipFirst]
    rw [hi, hj]
    simp only [BilinearComplexity.TriadData.eval, BilinearComplexity.triad]
    rw [hx]
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring

/-- A raw second-mode shear preserves the represented tensor when its two second
 factors are literally equal. -/
theorem sumTensor_flipSecond (S : Scheme k a b c r) (i j : Fin r) (q : k)
    (hij : i ≠ j) (hshared : (S.term i).2.1 = (S.term j).2.1) :
    (S.flipSecond i j q).sumTensor = S.sumTensor := by
  funext x y z
  apply sum_eq_of_eq_off_two _ _ i j hij
  · intro s hsi hsj
    have hs : (S.flipSecond i j q).term s = S.term s := by
      simp [flipSecond, hsi, hsj]
    rw [hs]
  · have hy := congrFun hshared y
    have hi : (S.flipSecond i j q).term i =
        ((S.term i).1 + q • (S.term j).1, (S.term i).2.1,
          (S.term i).2.2) := by
      simp [flipSecond, hij]
    have hj : (S.flipSecond i j q).term j =
        ((S.term j).1, (S.term j).2.1,
          (S.term j).2.2 - q • (S.term i).2.2) := by
      simp [flipSecond]
    rw [hi, hj]
    simp only [BilinearComplexity.TriadData.eval, BilinearComplexity.triad]
    rw [hy]
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring

/-- A raw third-mode shear preserves the represented tensor when its two third
 factors are literally equal. -/
theorem sumTensor_flipThird (S : Scheme k a b c r) (i j : Fin r) (q : k)
    (hij : i ≠ j) (hshared : (S.term i).2.2 = (S.term j).2.2) :
    (S.flipThird i j q).sumTensor = S.sumTensor := by
  funext x y z
  apply sum_eq_of_eq_off_two _ _ i j hij
  · intro s hsi hsj
    have hs : (S.flipThird i j q).term s = S.term s := by
      simp [flipThird, hsi, hsj]
    rw [hs]
  · have hz := congrFun hshared z
    have hi : (S.flipThird i j q).term i =
        ((S.term i).1 + q • (S.term j).1, (S.term i).2.1,
          (S.term i).2.2) := by
      simp [flipThird, hij]
    have hj : (S.flipThird i j q).term j =
        ((S.term j).1, (S.term j).2.1 - q • (S.term i).2.1,
          (S.term j).2.2) := by
      simp [flipThird]
    rw [hi, hj]
    simp only [BilinearComplexity.TriadData.eval, BilinearComplexity.triad]
    rw [hz]
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring

/-- Pointwise equality of evaluated terms preserves the represented tensor. -/
theorem SameTensors.sumTensor_eq {S R : Scheme k a b c r} (h : S.SameTensors R) :
    S.sumTensor = R.sumTensor := by
  funext x y z
  apply Finset.sum_congr rfl
  intro s _hs
  exact congrFun (congrFun (congrFun (h s) x) y) z

/-- Every raw elementary flip preserves the represented tensor. -/
theorem RawElementaryFlip.sumTensor_eq {S R : Scheme k a b c r}
    (h : RawElementaryFlip S R) : S.sumTensor = R.sumTensor := by
  cases h with
  | first i j q hij _hq hshared => exact (sumTensor_flipFirst S i j q hij hshared).symm
  | second i j q hij _hq hshared => exact (sumTensor_flipSecond S i j q hij hshared).symm
  | third i j q hij _hq hshared => exact (sumTensor_flipThird S i j q hij hshared).symm

/-- Every elementary flip, including projective refactorizations, preserves the
 represented tensor. -/
theorem ElementaryFlip.sumTensor_eq {S R : Scheme k a b c r}
    (h : ElementaryFlip S R) : S.sumTensor = R.sumTensor := by
  obtain ⟨U, V, hSU, hRV, hUV⟩ := h
  exact hSU.sumTensor_eq.trans (hUV.sumTensor_eq.trans hRV.sumTensor_eq.symm)

/-- Applying the opposite first-mode shear at the same ordered pair undoes a
 first-mode shear; only distinctness of the indices is needed. -/
theorem flipFirst_neg (S : Scheme k a b c r) (i j : Fin r) (q : k) (hij : i ≠ j) :
    (S.flipFirst i j q).flipFirst i j (-q) = S := by
  change Scheme.mk _ = Scheme.mk S.term
  congr 1
  funext s
  by_cases hsi : s = i
  · subst s
    simp [flipFirst, hij]
  · by_cases hsj : s = j
    · subst s
      simp [flipFirst, hij]
    · simp [flipFirst, hsi, hsj]

/-- Applying the opposite second-mode shear at the same ordered pair undoes a
 second-mode shear; only distinctness of the indices is needed. -/
theorem flipSecond_neg (S : Scheme k a b c r) (i j : Fin r) (q : k) (hij : i ≠ j) :
    (S.flipSecond i j q).flipSecond i j (-q) = S := by
  change Scheme.mk _ = Scheme.mk S.term
  congr 1
  funext s
  by_cases hsi : s = i
  · subst s
    simp [flipSecond, hij]
  · by_cases hsj : s = j
    · subst s
      simp [flipSecond, hij]
    · simp [flipSecond, hsi, hsj]

/-- Applying the opposite third-mode shear at the same ordered pair undoes a
 third-mode shear; only distinctness of the indices is needed. -/
theorem flipThird_neg (S : Scheme k a b c r) (i j : Fin r) (q : k) (hij : i ≠ j) :
    (S.flipThird i j q).flipThird i j (-q) = S := by
  change Scheme.mk _ = Scheme.mk S.term
  congr 1
  funext s
  by_cases hsi : s = i
  · subst s
    simp [flipThird, hij]
  · by_cases hsj : s = j
    · subst s
      simp [flipThird, hij]
    · simp [flipThird, hsi, hsj]

/-- An arbitrary nonempty selected family with projectively common first factors
and dependent second factors gives a rank-at-most bound after eliminating one
summand. The positive-size hypothesis guards `r - 1`; terms outside the selected
`Finset` retain their indexed multiplicities. This constructs a `RankLE` witness,
which may contain zero or duplicate terms; it does not claim a normalized paper
scheme of cardinality exactly `r - 1`. -/
theorem rankLE_sum_of_reducibleFamily_first_second
    (hr : 0 < r) (x : Fin r → Fin a → k) (y : Fin r → Fin b → k)
    (z : Fin r → Fin c → k) (hred : ReducibleFamily x y) :
    BilinearComplexity.RankLE
      (fun i j l => ∑ s, x s i * y s j * z s l) (r - 1) := by
  classical
  obtain ⟨I, _hI, ⟨base, _hbase, hcommon⟩, hdep⟩ := hred
  rw [Fintype.linearIndependent_iff] at hdep
  push Not at hdep
  obtain ⟨g, hg, pivot, hgpivot⟩ := hdep
  let q : {s : Fin r // s ∈ I} → k := fun s =>
    Classical.choose (hcommon s.1 s.2)
  have hq : ∀ s, q s ≠ 0 := fun s => (Classical.choose_spec
    (hcommon s.1 s.2)).1
  have hx : ∀ s, x s.1 = q s • x base := fun s => (Classical.choose_spec
    (hcommon s.1 s.2)).2
  let G : Fin r → k := fun s => if hs : s ∈ I then g ⟨s, hs⟩ else 0
  let Q : Fin r → k := fun s => if hs : s ∈ I then q ⟨s, hs⟩ else 1
  have hGpivot : G pivot.1 ≠ 0 := by
    simp only [G, dif_pos pivot.2]
    exact hgpivot
  have hQ : ∀ s, Q s ≠ 0 := by
    intro s
    simp only [Q]
    split
    · next hs => exact hq ⟨s, hs⟩
    · exact one_ne_zero
  have hQpivot : Q pivot.1 = q pivot := by
    simp only [Q, dif_pos pivot.2]
  have hGrel : (∑ s, G s • y s) = 0 := by
    calc
      (∑ s, G s • y s) = ∑ s ∈ I, G s • y s := by
        symm
        apply Finset.sum_subset (Finset.subset_univ I)
        intro s _hsI hs
        simp only [G, dif_neg hs, zero_smul]
      _ = ∑ s : {s : Fin r // s ∈ I}, G s.1 • y s.1 :=
        Finset.sum_subtype I (fun _ => Iff.rfl) (fun s => G s • y s)
      _ = ∑ s : {s : Fin r // s ∈ I}, g s • y s.1 := by
        apply Finset.sum_congr rfl
        intro s _hs
        simp only [G, dif_pos s.2]
      _ = 0 := hg
  cases r with
  | zero => simp at hr
  | succ n =>
      let p : Fin (n + 1) := pivot.1
      let z' : Fin n → Fin c → k := fun t l =>
        let s := p.succAbove t
        z s l - (G s * Q p / (G p * Q s)) * z p l
      have hyrel : ∀ j, y p j =
          ∑ t : Fin n, -(G (p.succAbove t) / G p) * y (p.succAbove t) j := by
        intro j
        have hcoord := congrFun hGrel j
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hcoord
        rw [Fin.sum_univ_succAbove (fun s => G s * y s j) p] at hcoord
        have hpterm : G p * y p j =
            -(∑ t, G (p.succAbove t) * y (p.succAbove t) j) :=
          eq_neg_of_add_eq_zero_left hcoord
        calc
          y p j = (G p)⁻¹ * (G p * y p j) := by
            rw [← mul_assoc, inv_mul_cancel₀ hGpivot, one_mul]
          _ = (G p)⁻¹ * (-(∑ t, G (p.succAbove t) *
              y (p.succAbove t) j)) := by rw [hpterm]
          _ = ∑ t, -(G (p.succAbove t) / G p) *
              y (p.succAbove t) j := by
            rw [mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro t _ht
            simp only [div_eq_mul_inv]
            ring
      simp only [Nat.succ_sub_one]
      refine ⟨fun t => x (p.succAbove t), fun t => y (p.succAbove t), z', ?_⟩
      funext i j l
      rw [Fin.sum_univ_succAbove
        (fun s => x s i * y s j * z s l) p]
      rw [hyrel j, Finset.mul_sum, Finset.sum_mul,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t _ht
      let s := p.succAbove t
      change x p i * (-(G s / G p) * y s j) * z p l +
          x s i * y s j * z s l = x s i * y s j * z' t l
      have hxp : x p = Q p • x base := by
        rw [hQpivot]
        exact hx pivot
      by_cases hs : s ∈ I
      · have hxs : x s = Q s • x base := by
          simp only [Q, dif_pos hs]
          exact hx ⟨s, hs⟩
        have hGp : G p ≠ 0 := hGpivot
        have hQp : Q p ≠ 0 := hQ p
        have hQs : Q s ≠ 0 := hQ s
        simp only [z', s, hxp, hxs, Pi.smul_apply, smul_eq_mul]
        field_simp [hGp, hQs]
        have hcancel : Q s * (Q s)⁻¹ = 1 := mul_inv_cancel₀ hQs
        linear_combination
          (x base i * y s j * Q p * G s * z p l) * hcancel
      · have hGs : G s = 0 := by simp only [G, dif_neg hs]
        simp [z', s, hGs]

/-- Every phase-1 reducible graph vertex represents a tensor of rank at most
`r - 1`. All six ordered mode pairs are handled. The conclusion is deliberately
`RankLE`, not an exact normalized output scheme: elimination can create zero or
duplicate terms over some fields. -/
theorem Reducible.rankLE_pred {T : BilinearComplexity.Tensor k a b c}
    {S : Scheme k a b c r} (hred : S.Reducible T) :
    BilinearComplexity.RankLE T (r - 1) := by
  let u : Fin r → Fin a → k := fun s => (S.term s).1
  let v : Fin r → Fin b → k := fun s => (S.term s).2.1
  let w : Fin r → Fin c → k := fun s => (S.term s).2.2
  have hr : 0 < r := hred.1.1
  have hsum : S.sumTensor = T := hred.1.2.1
  rw [← hsum]
  rcases hred.2 with h₁ | h₂ | h₃ | h₄ | h₅ | h₆
  · obtain ⟨u', v', w', hdec⟩ :=
      rankLE_sum_of_reducibleFamily_first_second hr u v w h₁
    exact ⟨u', v', w', by
      funext i j l
      have he := congrFun (congrFun (congrFun hdec i) j) l
      simpa only [sumTensor, BilinearComplexity.TriadData.eval,
        BilinearComplexity.triad, u, v, w] using he⟩
  · obtain ⟨u', w', v', hdec⟩ :=
      rankLE_sum_of_reducibleFamily_first_second hr u w v h₂
    refine ⟨u', v', w', ?_⟩
    funext i j l
    have he := congrFun (congrFun (congrFun hdec i) l) j
    calc
      (∑ s, (S.term s).eval i j l) = ∑ s, u s i * w s l * v s j := by
        apply Finset.sum_congr rfl
        intro s _hs
        simp only [BilinearComplexity.TriadData.eval, BilinearComplexity.triad,
          u, v, w]
        ring
      _ = ∑ s, u' s i * w' s l * v' s j := he
      _ = ∑ s, u' s i * v' s j * w' s l := by
        apply Finset.sum_congr rfl
        intro s _hs
        ring
  · obtain ⟨v', u', w', hdec⟩ :=
      rankLE_sum_of_reducibleFamily_first_second hr v u w h₃
    refine ⟨u', v', w', ?_⟩
    funext i j l
    have he := congrFun (congrFun (congrFun hdec j) i) l
    calc
      (∑ s, (S.term s).eval i j l) = ∑ s, v s j * u s i * w s l := by
        apply Finset.sum_congr rfl
        intro s _hs
        simp only [BilinearComplexity.TriadData.eval, BilinearComplexity.triad,
          u, v, w]
        ring
      _ = ∑ s, v' s j * u' s i * w' s l := he
      _ = ∑ s, u' s i * v' s j * w' s l := by
        apply Finset.sum_congr rfl
        intro s _hs
        ring
  · obtain ⟨v', w', u', hdec⟩ :=
      rankLE_sum_of_reducibleFamily_first_second hr v w u h₄
    refine ⟨u', v', w', ?_⟩
    funext i j l
    have he := congrFun (congrFun (congrFun hdec j) l) i
    calc
      (∑ s, (S.term s).eval i j l) = ∑ s, v s j * w s l * u s i := by
        apply Finset.sum_congr rfl
        intro s _hs
        simp only [BilinearComplexity.TriadData.eval, BilinearComplexity.triad,
          u, v, w]
        ring
      _ = ∑ s, v' s j * w' s l * u' s i := he
      _ = ∑ s, u' s i * v' s j * w' s l := by
        apply Finset.sum_congr rfl
        intro s _hs
        ring
  · obtain ⟨w', u', v', hdec⟩ :=
      rankLE_sum_of_reducibleFamily_first_second hr w u v h₅
    refine ⟨u', v', w', ?_⟩
    funext i j l
    have he := congrFun (congrFun (congrFun hdec l) i) j
    calc
      (∑ s, (S.term s).eval i j l) = ∑ s, w s l * u s i * v s j := by
        apply Finset.sum_congr rfl
        intro s _hs
        simp only [BilinearComplexity.TriadData.eval, BilinearComplexity.triad,
          u, v, w]
        ring
      _ = ∑ s, w' s l * u' s i * v' s j := he
      _ = ∑ s, u' s i * v' s j * w' s l := by
        apply Finset.sum_congr rfl
        intro s _hs
        ring
  · obtain ⟨w', v', u', hdec⟩ :=
      rankLE_sum_of_reducibleFamily_first_second hr w v u h₆
    refine ⟨u', v', w', ?_⟩
    funext i j l
    have he := congrFun (congrFun (congrFun hdec l) j) i
    calc
      (∑ s, (S.term s).eval i j l) = ∑ s, w s l * v s j * u s i := by
        apply Finset.sum_congr rfl
        intro s _hs
        simp only [BilinearComplexity.TriadData.eval, BilinearComplexity.triad,
          u, v, w]
        ring
      _ = ∑ s, w' s l * v' s j * u' s i := he
      _ = ∑ s, u' s i * v' s j * w' s l := by
        apply Finset.sum_congr rfl
        intro s _hs
        ring

/-- The raw elementary-flip relation is symmetric.  The reverse shear uses the
same ordered indices and coefficient `-q`; no additional hypotheses are needed. -/
theorem RawElementaryFlip.symm {S R : Scheme k a b c r}
    (h : RawElementaryFlip S R) : RawElementaryFlip R S := by
  cases h with
  | first i j q hij hq hshared =>
      have hrev : RawElementaryFlip (S.flipFirst i j q)
          ((S.flipFirst i j q).flipFirst i j (-q)) := by
        apply RawElementaryFlip.first _ i j (-q) hij (neg_ne_zero.mpr hq)
        simpa [flipFirst, hij] using hshared
      rwa [flipFirst_neg S i j q hij] at hrev
  | second i j q hij hq hshared =>
      have hrev : RawElementaryFlip (S.flipSecond i j q)
          ((S.flipSecond i j q).flipSecond i j (-q)) := by
        apply RawElementaryFlip.second _ i j (-q) hij (neg_ne_zero.mpr hq)
        simpa [flipSecond, hij] using hshared
      rwa [flipSecond_neg S i j q hij] at hrev
  | third i j q hij hq hshared =>
      have hrev : RawElementaryFlip (S.flipThird i j q)
          ((S.flipThird i j q).flipThird i j (-q)) := by
        apply RawElementaryFlip.third _ i j (-q) hij (neg_ne_zero.mpr hq)
        simpa [flipThird, hij] using hshared
      rwa [flipThird_neg S i j q hij] at hrev

/-- The elementary flip relation is symmetric, including its tensorwise
refactorization witnesses. -/
theorem ElementaryFlip.symm {S R : Scheme k a b c r}
    (h : ElementaryFlip S R) : ElementaryFlip R S := by
  obtain ⟨U, V, hSU, hRV, hUV⟩ := h
  exact ⟨V, U, hRV, hSU, hUV.symm⟩

end Scheme

/-! Ground checks and trust-surface audit. -/

example :
    let S : Scheme ℚ 1 1 1 2 :=
      ⟨fun s => (fun _ => 1, fun _ => if s = 0 then 2 else 3,
        fun _ => if s = 0 then 5 else 7)⟩
    (S.flipFirst 0 1 2).sumTensor = S.sumTensor := by
  dsimp
  apply Scheme.sumTensor_flipFirst _ 0 1 2 (by decide)
  rfl

example :
    let S : Scheme ℚ 1 1 1 2 :=
      ⟨fun s => (fun _ => 1, fun _ => if s = 0 then 2 else 3,
        fun _ => if s = 0 then 5 else 7)⟩
    Scheme.ElementaryFlip (S.flipFirst 0 1 2) S := by
  dsimp
  apply Scheme.ElementaryFlip.symm
  exact ⟨_, _, Scheme.sameTensors_refl _, Scheme.sameTensors_refl _,
    Scheme.RawElementaryFlip.first _ 0 1 2 (by decide) (by norm_num) rfl⟩

example :
    let S : Scheme ℚ 1 1 1 2 :=
      ⟨fun s => (fun _ => if s = 0 then 2 else 3,
        fun _ => if s = 0 then 5 else 7, fun _ => 1)⟩
    (S.flipThird 0 1 2).sumTensor = S.sumTensor := by
  dsimp
  apply Scheme.sumTensor_flipThird _ 0 1 2 (by decide)
  rfl

example :
    let x : Fin 3 → Fin 1 → ℚ := fun _ _ => 1
    let y : Fin 3 → Fin 1 → ℚ := fun s _ => if s = 1 then 2 else 1
    let z : Fin 3 → Fin 1 → ℚ := fun s _ => (s.val : ℚ) + 1
    BilinearComplexity.RankLE
      (fun i j l => ∑ s, x s i * y s j * z s l) (3 - 1) := by
  dsimp only
  let I : Finset (Fin 3) := {0, 2}
  have hI : I.Nonempty := by simp [I]
  have hcommon : ∃ p : Fin 3, p ∈ I ∧
      ∀ i : Fin 3, i ∈ I → ProjectivelyEqual
        (fun _ : Fin 1 => (1 : ℚ)) (fun _ : Fin 1 => 1) := by
    refine ⟨0, by simp [I], ?_⟩
    intro i _hi
    exact projectivelyEqual_refl _
  have hdep : ¬ LinearIndependent ℚ
      (fun i : {i : Fin 3 // i ∈ I} =>
        fun _ : Fin 1 => if i.1 = 1 then (2 : ℚ) else 1) := by
    intro hli
    have hinj := hli.injective
    let i0 : {i : Fin 3 // i ∈ I} := ⟨0, by simp [I]⟩
    let i2 : {i : Fin 3 // i ∈ I} := ⟨2, by simp [I]⟩
    have heq : i0 = i2 := hinj (by
      funext j
      simp [i0, i2])
    have hval := congrArg (fun i => i.1.val) heq
    norm_num [i0, i2] at hval
  apply Scheme.rankLE_sum_of_reducibleFamily_first_second (by omega)
  exact ⟨I, hI, hcommon, hdep⟩

#check @Scheme.sumTensor_flipFirst
#check @Scheme.sumTensor_flipSecond
#check @Scheme.sumTensor_flipThird
#check @Scheme.SameTensors.sumTensor_eq
#check @Scheme.RawElementaryFlip.sumTensor_eq
#check @Scheme.ElementaryFlip.sumTensor_eq
#check @Scheme.flipFirst_neg
#check @Scheme.flipSecond_neg
#check @Scheme.flipThird_neg
#check @Scheme.rankLE_sum_of_reducibleFamily_first_second
#check @Scheme.Reducible.rankLE_pred
#check @Scheme.RawElementaryFlip.symm
#check @Scheme.ElementaryFlip.symm

#print axioms Scheme.sumTensor_flipFirst
#print axioms Scheme.sumTensor_flipSecond
#print axioms Scheme.sumTensor_flipThird
#print axioms Scheme.SameTensors.sumTensor_eq
#print axioms Scheme.RawElementaryFlip.sumTensor_eq
#print axioms Scheme.ElementaryFlip.sumTensor_eq
#print axioms Scheme.flipFirst_neg
#print axioms Scheme.flipSecond_neg
#print axioms Scheme.flipThird_neg
#print axioms Scheme.rankLE_sum_of_reducibleFamily_first_second
#print axioms Scheme.Reducible.rankLE_pred
#print axioms Scheme.RawElementaryFlip.symm
#print axioms Scheme.ElementaryFlip.symm

end BilinearComplexity.FlipQuantum
