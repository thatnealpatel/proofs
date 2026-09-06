import BilinearComplexity.FieldNativeMoves
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace BilinearComplexity
namespace FieldThreeProductCircuit

open FieldRankOne FieldContextual FieldNativeMoves

variable {k : Type*} {a b c : ℕ} [Field k]

private def SameRay {ι : Type*} (u v : ι → k) : Prop :=
  ∃ r : k, u = r • v

example : SameRay (k := ℚ) (fun _ : Fin 1 => 2) (fun _ : Fin 1 => 1) := by
  exact ⟨2, by funext i; fin_cases i; norm_num⟩

private theorem exists_apply_ne_zero {ι : Type*} {u : ι → k} (hu : u ≠ 0) :
    ∃ i, u i ≠ 0 := by
  exact Function.ne_iff.mp hu

private theorem sameRay_iff_cross {ι : Type*} {u v : ι → k} (hv : v ≠ 0) :
    SameRay u v ↔ ∀ i j, u i * v j = u j * v i := by
  constructor
  · rintro ⟨r, rfl⟩ i j
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · intro h
    obtain ⟨i, hi⟩ := exists_apply_ne_zero hv
    refine ⟨u i / v i, ?_⟩
    funext j
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div]
    exact (eq_div_iff hi).2 (h j i)

private def outer {ι κ : Type*} (u : ι → k) (v : κ → k) : ι × κ → k :=
  fun p => u p.1 * v p.2

example : outer (k := ℚ) (fun _ : Fin 1 => 2) (fun _ : Fin 1 => 3) (0, 0) = 6 := by
  norm_num [outer]

private theorem outer_ne_zero {ι κ : Type*} {u : ι → k} {v : κ → k}
    (hu : u ≠ 0) (hv : v ≠ 0) : outer u v ≠ 0 := by
  obtain ⟨i, hi⟩ := exists_apply_ne_zero hu
  obtain ⟨j, hj⟩ := exists_apply_ne_zero hv
  intro hzero
  have hij := congrFun hzero (i, j)
  simp only [outer, Pi.zero_apply] at hij
  exact mul_ne_zero hi hj hij

private theorem outer_sum_ruling {ι κ : Type*}
    {u₁ u₂ u₃ : ι → k} {v₁ v₂ v₃ : κ → k}
    (hu₂ : u₂ ≠ 0) (hv₂ : v₂ ≠ 0)
    (h : ∀ i j, u₁ i * v₁ j + u₂ i * v₂ j = u₃ i * v₃ j) :
    SameRay u₁ u₂ ∨ SameRay v₁ v₂ := by
  have hminor (i i' : ι) (j j' : κ) :
      (u₁ i * u₂ i' - u₂ i * u₁ i') *
          (v₁ j * v₂ j' - v₂ j * v₁ j') = 0 := by
    calc
      (u₁ i * u₂ i' - u₂ i * u₁ i') *
          (v₁ j * v₂ j' - v₂ j * v₁ j') =
          (u₁ i * v₁ j + u₂ i * v₂ j) *
              (u₁ i' * v₁ j' + u₂ i' * v₂ j') -
            (u₁ i * v₁ j' + u₂ i * v₂ j') *
              (u₁ i' * v₁ j + u₂ i' * v₂ j) := by ring
      _ = (u₃ i * v₃ j) * (u₃ i' * v₃ j') -
          (u₃ i * v₃ j') * (u₃ i' * v₃ j) := by
            rw [h i j, h i' j', h i j', h i' j]
      _ = 0 := by ring
  by_cases hu : SameRay u₁ u₂
  · exact Or.inl hu
  · right
    apply (sameRay_iff_cross hv₂).2
    have hex : ∃ i i', u₁ i * u₂ i' ≠ u₁ i' * u₂ i := by
      by_contra hnone
      push Not at hnone
      apply hu
      apply (sameRay_iff_cross hu₂).2
      exact hnone
    obtain ⟨i, i', hii'⟩ := hex
    have hleft : u₁ i * u₂ i' - u₂ i * u₁ i' ≠ 0 := by
      rw [sub_ne_zero]
      simpa only [mul_comm] using hii'
    intro j j'
    have hright : v₁ j * v₂ j' - v₂ j * v₁ j' = 0 :=
      (mul_eq_zero.mp (hminor i i' j j')).resolve_left hleft
    rw [sub_eq_zero] at hright
    simpa only [mul_comm] using hright

private theorem rays_of_ray_outer {ι κ : Type*} {u u' : ι → k} {v v' : κ → k}
    (h : SameRay (outer u v) (outer u' v')) (hu : u ≠ 0) (hv : v ≠ 0) :
    SameRay u u' ∧ SameRay v v' := by
  rcases h with ⟨r, hr⟩
  obtain ⟨i, hi⟩ := exists_apply_ne_zero hu
  obtain ⟨j, hj⟩ := exists_apply_ne_zero hv
  have hcoord (p : ι) (q : κ) : u p * v q = r * (u' p * v' q) := by
    have hpq := congrFun hr (p, q)
    simpa only [outer, Pi.smul_apply, smul_eq_mul] using hpq
  constructor
  · refine ⟨r * v' j / v j, ?_⟩
    funext p
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hj).2
    calc
      u p * v j = r * (u' p * v' j) := hcoord p j
      _ = (r * v' j) * u' p := by ring
  · refine ⟨r * u' i / u i, ?_⟩
    funext q
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hi).2
    calc
      v q * u i = u i * v q := by ring
      _ = r * (u' i * v' q) := hcoord i q
      _ = (r * u' i) * v' q := by ring

private theorem sameRay_of_scaled {ι : Type*} {s t : k} {u v : ι → k}
    (hs : s ≠ 0) (h : SameRay (s • u) (t • v)) : SameRay u v := by
  rcases h with ⟨r, hr⟩
  refine ⟨s⁻¹ * r * t, ?_⟩
  calc
    u = s⁻¹ • (s • u) := by
      rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
    _ = s⁻¹ • (r • (t • v)) := congrArg (s⁻¹ • ·) hr
    _ = (s⁻¹ * r * t) • v := by rw [smul_smul, smul_smul, mul_assoc]

private theorem three_product_ruling
    {u₁ u₂ u₃ : Fin a → k} {v₁ v₂ v₃ : Fin b → k} {w₁ w₂ w₃ : Fin c → k}
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0)
    (hw₁ : w₁ ≠ 0) (hw₂ : w₂ ≠ 0)
    (h : ∀ i j l, u₁ i * v₁ j * w₁ l + u₂ i * v₂ j * w₂ l =
      u₃ i * v₃ j * w₃ l) :
    (SameRay u₁ u₂ ∧ SameRay v₁ v₂) ∨
      (SameRay u₁ u₂ ∧ SameRay w₁ w₂) ∨
      (SameRay v₁ v₂ ∧ SameRay w₁ w₂) := by
  have hflat (i : Fin a) (p : Fin b × Fin c) :
      u₁ i * outer v₁ w₁ p + u₂ i * outer v₂ w₂ p =
        u₃ i * outer v₃ w₃ p := by
    simpa only [outer, mul_assoc] using h i p.1 p.2
  rcases outer_sum_ruling hu₂ (outer_ne_zero hv₂ hw₂) hflat with hu | hvw
  · obtain ⟨s, hs⟩ := hu
    have huRay : SameRay u₁ u₂ := ⟨s, hs⟩
    obtain ⟨i, hi⟩ := exists_apply_ne_zero hu₁
    have hui₂ : u₂ i ≠ 0 := by
      intro hz
      apply hi
      have hsi := congrFun hs i
      simpa only [Pi.smul_apply, smul_eq_mul, hz, mul_zero] using hsi
    have hslice (j : Fin b) (l : Fin c) :
        ((u₁ i) • v₁) j * w₁ l + ((u₂ i) • v₂) j * w₂ l =
          ((u₃ i) • v₃) j * w₃ l := by
      simpa only [Pi.smul_apply, smul_eq_mul] using h i j l
    rcases outer_sum_ruling (smul_ne_zero hui₂ hv₂) hw₂ hslice with hv | hw
    · exact Or.inl ⟨huRay, sameRay_of_scaled hi hv⟩
    · exact Or.inr (Or.inl ⟨huRay, hw⟩)
  · exact Or.inr (Or.inr (rays_of_ray_outer hvw hv₁ hw₁))

private theorem eval_absorb_first_second {u u' : Fin a → k} {v v' : Fin b → k}
    (w : Fin c → k) (s t : k) (hu : u = s • u') (hv : v = t • v') :
    evalFactors 1 u v w = evalFactors 1 u' v' ((s * t) • w) := by
  rw [hu, hv]
  funext i j l
  simp only [evalFactors, Pi.smul_apply, smul_eq_mul, one_mul]
  ring

private theorem eval_absorb_first_third {u u' : Fin a → k} (v : Fin b → k)
    {w w' : Fin c → k} (s t : k) (hu : u = s • u') (hw : w = t • w') :
    evalFactors 1 u v w = evalFactors 1 u' ((s * t) • v) w' := by
  rw [hu, hw]
  funext i j l
  simp only [evalFactors, Pi.smul_apply, smul_eq_mul, one_mul]
  ring

private theorem eval_absorb_second_third (u : Fin a → k) {v v' : Fin b → k}
    {w w' : Fin c → k} (s t : k) (hv : v = s • v') (hw : w = t • w') :
    evalFactors 1 u v w = evalFactors 1 ((s * t) • u) v' w' := by
  rw [hv, hw]
  funext i j l
  simp only [evalFactors, Pi.smul_apply, smul_eq_mul, one_mul]
  ring

private theorem split_third_of_common (x y z : Atom k a b c)
    (u : Fin a → k) (v : Fin b → k) (p q : Fin c → k)
    (hu : u ≠ 0) (hv : v ≠ 0)
    (hx : x.val = evalFactors 1 u v p)
    (hy : y.val = evalFactors 1 u v q)
    (hz : z.val = evalFactors 1 u v (p + q)) : SplitFormula z x y := by
  have hp : p ≠ 0 := by
    intro hp
    apply x.nonzero
    rw [hx, hp]
    funext i j l
    simp only [evalFactors, Pi.zero_apply, mul_zero]
  have hq : q ≠ 0 := by
    intro hq
    apply y.nonzero
    rw [hy, hq]
    funext i j l
    simp only [evalFactors, Pi.zero_apply, mul_zero]
  have hpq : p + q ≠ 0 := by
    intro hpq
    apply z.nonzero
    rw [hz, hpq]
    funext i j l
    simp only [evalFactors, Pi.zero_apply, mul_zero]
  let U : Factor k a := ⟨u, hu⟩
  let V : Factor k b := ⟨v, hv⟩
  let P : Factor k c := ⟨p, hp⟩
  let Q : Factor k c := ⟨q, hq⟩
  apply SplitFormula.third U V
  refine { x := P, y := Q, sum_ne := hpq, source_eq := ?_, left_eq := ?_, right_eq := ?_ }
  · apply Atom.ext
    exact hz
  · apply Atom.ext
    exact hx
  · apply Atom.ext
    exact hy

private theorem split_second_of_common (x y z : Atom k a b c)
    (u : Fin a → k) (w : Fin c → k) (p q : Fin b → k)
    (hu : u ≠ 0) (hw : w ≠ 0)
    (hx : x.val = evalFactors 1 u p w)
    (hy : y.val = evalFactors 1 u q w)
    (hz : z.val = evalFactors 1 u (p + q) w) : SplitFormula z x y := by
  have hp : p ≠ 0 := by
    intro hp
    apply x.nonzero
    rw [hx, hp]
    funext i j l
    simp only [evalFactors, Pi.zero_apply, zero_mul, mul_zero]
  have hq : q ≠ 0 := by
    intro hq
    apply y.nonzero
    rw [hy, hq]
    funext i j l
    simp only [evalFactors, Pi.zero_apply, zero_mul, mul_zero]
  have hpq : p + q ≠ 0 := by
    intro hpq
    apply z.nonzero
    rw [hz, hpq]
    funext i j l
    simp only [evalFactors, Pi.zero_apply, zero_mul, mul_zero]
  let U : Factor k a := ⟨u, hu⟩
  let W : Factor k c := ⟨w, hw⟩
  let P : Factor k b := ⟨p, hp⟩
  let Q : Factor k b := ⟨q, hq⟩
  apply SplitFormula.second U W
  refine { x := P, y := Q, sum_ne := hpq, source_eq := ?_, left_eq := ?_, right_eq := ?_ }
  · apply Atom.ext
    exact hz
  · apply Atom.ext
    exact hx
  · apply Atom.ext
    exact hy

private theorem split_first_of_common (x y z : Atom k a b c)
    (v : Fin b → k) (w : Fin c → k) (p q : Fin a → k)
    (hv : v ≠ 0) (hw : w ≠ 0)
    (hx : x.val = evalFactors 1 p v w)
    (hy : y.val = evalFactors 1 q v w)
    (hz : z.val = evalFactors 1 (p + q) v w) : SplitFormula z x y := by
  have hp : p ≠ 0 := by
    intro hp
    apply x.nonzero
    rw [hx, hp]
    funext i j l
    simp only [evalFactors, Pi.zero_apply, one_mul, zero_mul]
  have hq : q ≠ 0 := by
    intro hq
    apply y.nonzero
    rw [hy, hq]
    funext i j l
    simp only [evalFactors, Pi.zero_apply, one_mul, zero_mul]
  have hpq : p + q ≠ 0 := by
    intro hpq
    apply z.nonzero
    rw [hz, hpq]
    funext i j l
    simp only [evalFactors, Pi.zero_apply, one_mul, zero_mul]
  let V : Factor k b := ⟨v, hv⟩
  let W : Factor k c := ⟨w, hw⟩
  let P : Factor k a := ⟨p, hp⟩
  let Q : Factor k a := ⟨q, hq⟩
  apply SplitFormula.first V W
  refine { x := P, y := Q, sum_ne := hpq, source_eq := ?_, left_eq := ?_, right_eq := ?_ }
  · apply Atom.ext
    exact hz
  · apply Atom.ext
    exact hx
  · apply Atom.ext
    exact hy

example : ∃ x y z : Atom ℚ 1 1 1, x.val + y.val = z.val := by
  let one : Factor ℚ 1 := ⟨fun _ => 1, by
    intro h
    have h0 := congrFun h 0
    norm_num at h0⟩
  let two : Factor ℚ 1 := ⟨fun _ => 2, by
    intro h
    have h0 := congrFun h 0
    norm_num at h0⟩
  refine ⟨atom one one one, atom one one one, atom two one one, ?_⟩
  funext i j l
  fin_cases i
  fin_cases j
  fin_cases l
  norm_num [atom_val, evalFactors, one, two]

/-- Three nonzero semantic pure tensors satisfying `x + y = z` lie on one ruling of the
Segre cone, so the equality has an actual field-native Split formula in some factor mode. -/
theorem splitFormula_of_val_add_eq (x y z : Atom k a b c)
    (h : x.val + y.val = z.val) : SplitFormula z x y := by
  obtain ⟨ux, vx, wx, rfl⟩ := atom_surjective x
  obtain ⟨uy, vy, wy, rfl⟩ := atom_surjective y
  obtain ⟨uz, vz, wz, rfl⟩ := atom_surjective z
  have hpoint (i : Fin a) (j : Fin b) (l : Fin c) :
      ux.1 i * vx.1 j * wx.1 l + uy.1 i * vy.1 j * wy.1 l =
        uz.1 i * vz.1 j * wz.1 l := by
    have hijl := congrFun (congrFun (congrFun h i) j) l
    simpa only [atom_val, evalFactors, Pi.add_apply, one_mul] using hijl
  rcases three_product_ruling ux.2 uy.2 vx.2 vy.2 wx.2 wy.2 hpoint with hxy | hxz | hyz
  · rcases hxy with ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    let p : Fin c → k := (s * t) • wx.1
    have hxnorm : (atom ux vx wx).val = evalFactors 1 uy.1 vy.1 p :=
      eval_absorb_first_second wx.1 s t hs ht
    have hynorm : (atom uy vy wy).val = evalFactors 1 uy.1 vy.1 wy.1 := rfl
    apply split_third_of_common (atom ux vx wx) (atom uy vy wy) (atom uz vz wz)
      uy.1 vy.1 p wy.1 uy.2 vy.2 hxnorm hynorm
    rw [← h]
    rw [hxnorm, hynorm]
    funext i j l
    simp only [evalFactors, Pi.add_apply, p, Pi.smul_apply, smul_eq_mul, one_mul]
    ring
  · rcases hxz with ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    let p : Fin b → k := (s * t) • vx.1
    have hxnorm : (atom ux vx wx).val = evalFactors 1 uy.1 p wy.1 :=
      eval_absorb_first_third vx.1 s t hs ht
    have hynorm : (atom uy vy wy).val = evalFactors 1 uy.1 vy.1 wy.1 := rfl
    apply split_second_of_common (atom ux vx wx) (atom uy vy wy) (atom uz vz wz)
      uy.1 wy.1 p vy.1 uy.2 wy.2 hxnorm hynorm
    rw [← h]
    rw [hxnorm, hynorm]
    funext i j l
    simp only [evalFactors, Pi.add_apply, p, Pi.smul_apply, smul_eq_mul, one_mul]
    ring
  · rcases hyz with ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    let p : Fin a → k := (s * t) • ux.1
    have hxnorm : (atom ux vx wx).val = evalFactors 1 p vy.1 wy.1 :=
      eval_absorb_second_third ux.1 s t hs ht
    have hynorm : (atom uy vy wy).val = evalFactors 1 uy.1 vy.1 wy.1 := rfl
    apply split_first_of_common (atom ux vx wx) (atom uy vy wy) (atom uz vz wz)
      vy.1 wy.1 p uy.1 vy.2 wy.2 hxnorm hynorm
    rw [← h]
    rw [hxnorm, hynorm]
    funext i j l
    simp only [evalFactors, Pi.add_apply, p, Pi.smul_apply, smul_eq_mul, one_mul]
    ring

example : ∃ x y z : Atom ℚ 1 1 1, x ≠ y ∧ x.val + y.val = z.val := by
  let one : Factor ℚ 1 := ⟨fun _ => 1, by
    intro h
    have h0 := congrFun h 0
    norm_num at h0⟩
  let two : Factor ℚ 1 := ⟨fun _ => 2, by
    intro h
    have h0 := congrFun h 0
    norm_num at h0⟩
  let three : Factor ℚ 1 := ⟨fun _ => 3, by
    intro h
    have h0 := congrFun h 0
    norm_num at h0⟩
  refine ⟨atom one one one, atom two one one, atom three one one, ?_, ?_⟩
  · intro h
    have h0 := congrArg (fun t : Atom ℚ 1 1 1 => t.val 0 0 0) h
    norm_num [atom_val, evalFactors, one, two] at h0
  · funext i j l
    fin_cases i
    fin_cases j
    fin_cases l
    norm_num [atom_val, evalFactors, one, two, three]

/-- Distinct nonzero semantic pure summands of a pure tensor determine a native Split
replacement, with finite-set arity certified by their distinctness. -/
theorem nativeReplacement_split_of_val_add_eq (x y z : Atom k a b c)
    (h : x.val + y.val = z.val) (hxy : x ≠ y) :
    NativeReplacement (singletonState z) (pairState x y) :=
  .split (splitFormula_of_val_add_eq x y z h) hxy

#check @splitFormula_of_val_add_eq
#check @nativeReplacement_split_of_val_add_eq
#print axioms splitFormula_of_val_add_eq
#print axioms nativeReplacement_split_of_val_add_eq

end FieldThreeProductCircuit
end BilinearComplexity
