/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Lipschitz.Calc
public import SuperdiffusionCLT.Section7.Analytic.Geometry.DomainPoincareL

/-!
# Calculus of the pinned flatness

Slopes of pinned affine functions at consecutive scales, restriction of the pinned flatness to
the next smaller scale, and the comparison of the slope `0` with an arbitrary slope.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal Pointwise

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem lip_pin_abs_vecDot_le (b v : Vec d) : |vecDot b v| ≤ (d : ℝ) * (‖b‖ * ‖v‖) := by
  unfold vecDot
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |b i * v i| ≤ ∑ _i : Fin d, ‖b‖ * ‖v‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        exact mul_le_mul (by simpa using norm_le_pi_norm b i) (by simpa using norm_le_pi_norm v i)
          (abs_nonneg _) (norm_nonneg _)
    _ = (d : ℝ) * (‖b‖ * ‖v‖) := by simp

theorem lip_pin_affine_bound {S : Set (Vec d)} {z : Vec d} {R : ℝ} (hSz : S ⊆ Metric.ball z R)
    (x₀ b : Vec d) (a : ℝ) :
    ∀ x ∈ S, ‖a + vecDot b (x - x₀)‖ ≤ |a| + (d : ℝ) * (‖b‖ * (‖x₀ - z‖ + R)) := by
  intro x hx
  have hxz : ‖x - z‖ < R := by
    have := hSz hx
    rwa [Metric.mem_ball, dist_eq_norm] at this
  have h1 : ‖x - x₀‖ ≤ ‖x₀ - z‖ + R := by
    calc ‖x - x₀‖ = ‖(x - z) - (x₀ - z)‖ := by rw [sub_sub_sub_cancel_right]
      _ ≤ ‖x - z‖ + ‖x₀ - z‖ := norm_sub_le _ _
      _ ≤ ‖x₀ - z‖ + R := by linarith only [hxz]
  have h2 := lip_pin_abs_vecDot_le b (x - x₀)
  have h3 : (d : ℝ) * (‖b‖ * ‖x - x₀‖) ≤ (d : ℝ) * (‖b‖ * (‖x₀ - z‖ + R)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)) (Nat.cast_nonneg _)
  rw [Real.norm_eq_abs]
  calc |a + vecDot b (x - x₀)| ≤ |a| + |vecDot b (x - x₀)| := abs_add_le _ _
    _ ≤ _ := by linarith only [h2, h3]

theorem lip_pin_affine_memLp {S : Set (Vec d)} {z : Vec d} {R : ℝ} (hS : MeasurableSet S)
    (hSz : S ⊆ Metric.ball z R) (x₀ b : Vec d) (a : ℝ) :
    MemLp (fun x => a + vecDot b (x - x₀)) 2 (volume.restrict S) := by
  have hcont : Continuous fun x : Vec d => a + vecDot b (x - x₀) := by
    unfold vecDot
    fun_prop
  have hfin : IsFiniteMeasure (volume.restrict S) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_lt (measure_mono hSz) measure_ball_lt_top
  refine MemLp.of_bound hcont.aestronglyMeasurable (|a| + (d : ℝ) * (‖b‖ * (‖x₀ - z‖ + R))) ?_
  rw [ae_restrict_iff' hS]
  exact Filter.Eventually.of_forall fun x hx => lip_pin_affine_bound hSz x₀ b a x hx

/-- The normalized `L²` norm of an affine function on a ball is at least `s ‖b‖ / 4`. -/
theorem lip_pin_ball_lower {q : Vec d} {s : ℝ} (hs : 0 < s) (a : ℝ) (b : Vec d) :
    s * ‖b‖ / 4 ≤ lipL2 (Metric.ball q s) (fun x => a + vecDot b (x - q)) := by
  have hV0 : volume (Metric.ball q s) ≠ 0 := (Metric.measure_ball_pos volume q hs).ne'
  have hVt : volume (Metric.ball q s) ≠ ⊤ := measure_ball_lt_top.ne
  have hlow := a10_affine_L2_lower (W := Metric.ball q s) hs subset_rfl a b
  have hcont : Continuous fun x : Vec d => a + vecDot b (x - q) := by
    unfold vecDot
    fun_prop
  have hmem : MemLp (fun x => a + vecDot b (x - q)) 2 (volume.restrict (Metric.ball q s)) :=
    lip_pin_affine_memLp Metric.isOpen_ball.measurableSet subset_rfl q b a
  have hne := lip_lpBar_ne_top hV0 hmem
  have hl : ENNReal.ofReal (s * ‖b‖ / 4) ≤
      lpBar (Metric.ball q s) 2 (fun x => a + vecDot b (x - q)) := by
    unfold lpBar
    rw [eLpNorm_smul_measure_of_ne_zero (ENNReal.inv_ne_zero.2 hVt)]
    have h12 : (1 / (2 : ℝ≥0∞)).toReal = 1 / (2 : ℝ) := by
      rw [ENNReal.toReal_div]; norm_num
    rw [h12, smul_eq_mul]
    calc ENNReal.ofReal (s * ‖b‖ / 4)
        = ((volume (Metric.ball q s))⁻¹) ^ (1 / (2 : ℝ)) *
            (ENNReal.ofReal (s * ‖b‖ / 4) * volume (Metric.ball q s) ^ (1 / (2 : ℝ))) := by
          rw [← mul_assoc, mul_comm _ (ENNReal.ofReal _), mul_assoc, ← ENNReal.mul_rpow_of_nonneg
            _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2), ENNReal.inv_mul_cancel hV0 hVt]
          simp
      _ ≤ _ := by gcongr
  have := ENNReal.toReal_mono hne hl
  rwa [ENNReal.toReal_ofReal (by positivity)] at this

theorem lip_pin_vecDot_sub_left (p p' v : Vec d) : vecDot (p' - p) v = vecDot p' v - vecDot p v := by
  unfold vecDot
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by simp only [Pi.sub_apply]; ring

theorem lip_pin_vecDot_sub_right (b x q x₀ : Vec d) :
    vecDot b (x - x₀) = vecDot b (x - q) + vecDot b (q - x₀) := by
  unfold vecDot
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by simp only [Pi.sub_apply]; ring

theorem lip_pin_resid_memLp {S S' : Set (Vec d)} {z : Vec d} {R : ℝ} (hS' : MeasurableSet S')
    (hS'z : S' ⊆ Metric.ball z R) {u : Vec d → ℝ} (hu : MemLp u 2 (volume.restrict S'))
    (x₀ : Vec d) (c₀ : ℝ) (p : Vec d) (hSS : S ⊆ S') :
    MemLp (fun x => u x - c₀ - vecDot p (x - x₀)) 2 (volume.restrict S') ∧
      MemLp (fun x => u x - c₀ - vecDot p (x - x₀)) 2 (volume.restrict S) := by
  have h := hu.sub (lip_pin_affine_memLp hS' hS'z x₀ p c₀)
  have h' : MemLp (fun x => u x - c₀ - vecDot p (x - x₀)) 2 (volume.restrict S') := by
    refine MemLp.ae_eq (Filter.Eventually.of_forall fun x => ?_) h
    simp only [Pi.sub_apply]
    ring
  exact ⟨h', h'.mono_measure (Measure.restrict_mono hSS le_rfl)⟩

/-- The volume of the larger set is controlled by the volume of the inner ball. -/
theorem lip_pin_geom {c : ℝ} (hc : 0 < c) {S S' : Set (Vec d)} {z q : Vec d} {j : ℕ}
    (hSS : S ⊆ S') (hb : Metric.ball q (c * (3 : ℝ) ^ j) ⊆ S)
    (hS'z : S' ⊆ Metric.ball z ((3 : ℝ) ^ (j + 1) / 2)) :
    volume S' ≤ ENNReal.ofReal ((3 / c) ^ d) * volume (Metric.ball q (c * (3 : ℝ) ^ j)) := by
  have hs : 0 < c * (3 : ℝ) ^ j := by positivity
  have hqz : ‖q - z‖ < (3 : ℝ) ^ (j + 1) / 2 := by
    have := hS'z (hSS (hb (Metric.mem_ball_self hs)))
    rwa [Metric.mem_ball, dist_eq_norm] at this
  have := a10_volume_le_ratio (W := S') (x0 := q) (s := c * (3 : ℝ) ^ j) (D := (3 : ℝ) ^ (j + 1))
    hs (by positivity) (fun x hx => by
      have hxz : ‖x - z‖ < (3 : ℝ) ^ (j + 1) / 2 := by
        have := hS'z hx
        rwa [Metric.mem_ball, dist_eq_norm] at this
      calc ‖x - q‖ = ‖(x - z) - (q - z)‖ := by rw [sub_sub_sub_cancel_right]
        _ ≤ ‖x - z‖ + ‖q - z‖ := norm_sub_le _ _
        _ ≤ (3 : ℝ) ^ (j + 1) := by linarith only [hxz, hqz])
  have hr : (3 : ℝ) ^ (j + 1) / (c * (3 : ℝ) ^ j) = 3 / c := by
    rw [pow_succ]
    field_simp
  rwa [hr] at this

/-- **C2c(i) — slopes of pinned affine functions at consecutive scales.** -/
theorem lip_pin_slope (d : ℕ) [NeZero d] (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    ∃ Cs : ℝ, 0 ≤ Cs ∧
      ∀ (S S' : Set (Vec d)) (z q x₀ : Vec d) (j : ℕ) (c₀ : ℝ) (u : Vec d → ℝ) (p p' : Vec d),
        MeasurableSet S → MeasurableSet S' → S ⊆ S' →
        Metric.ball q (c * (3 : ℝ) ^ j) ⊆ S → S' ⊆ Metric.ball z ((3 : ℝ) ^ (j + 1) / 2) →
        MemLp u 2 (volume.restrict S') →
        ‖p - p'‖ ≤ Cs * (lipPin S j x₀ c₀ u p + lipPin S' (j + 1) x₀ c₀ u p') := by
  have _ := hc1
  set κ : ℝ := (3 / c) ^ d with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set r : ℝ := Real.sqrt κ with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  refine ⟨(4 / c) * r * (1 + 3 * r), by positivity, ?_⟩
  intro S S' z q x₀ j c₀ u p p' hS hS' hSS' hb hS'z hu
  set s : ℝ := c * (3 : ℝ) ^ j with hs
  have hs0 : 0 < s := by positivity
  set t : ℝ := (3 : ℝ) ^ j with ht
  have ht0 : 0 < t := by positivity
  have hvol := lip_pin_geom hc hSS' hb hS'z
  have hBS : Metric.ball q s ⊆ S' := hb.trans hSS'
  have hV0 : volume (Metric.ball q s) ≠ 0 := (Metric.measure_ball_pos volume q hs0).ne'
  have hS0 : volume S ≠ 0 := fun h => hV0 (measure_mono_null hb h)
  have hSt : volume S ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono (hSS'.trans hS'z)) measure_ball_lt_top).ne
  have hS't : volume S' ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono hS'z) measure_ball_lt_top).ne
  have hvolS : volume S ≤ ENNReal.ofReal κ * volume (Metric.ball q s) :=
    (measure_mono hSS').trans hvol
  have hvolS' : volume S' ≤ ENNReal.ofReal κ * volume S := by
    refine hvol.trans ?_
    gcongr
  obtain ⟨hFp', hFpS'⟩ := lip_pin_resid_memLp (S := S) hS' hS'z hu x₀ c₀ p' hSS'
  obtain ⟨-, hFp⟩ := lip_pin_resid_memLp (S := S) hS' hS'z hu x₀ c₀ p hSS'
  -- the difference of the two residuals is affine
  set b : Vec d := p' - p with hbdef
  set a : ℝ := vecDot b (q - x₀) with ha
  have hA : (fun x => (u x - c₀ - vecDot p (x - x₀)) + -(u x - c₀ - vecDot p' (x - x₀))) =
      fun x => a + vecDot b (x - q) := by
    funext x
    simp only [hbdef, ha, lip_pin_vecDot_sub_left, lip_pin_vecDot_sub_right p' x q x₀,
      lip_pin_vecDot_sub_right p x q x₀]
    ring
  have hAS : MemLp (fun x => a + vecDot b (x - q)) 2 (volume.restrict S) :=
    (lip_pin_affine_memLp hS (hSS'.trans hS'z) q b a)
  have h1 := lip_pin_ball_lower hs0 a b (q := q)
  have h2 := lipL2_mono_set (f := fun x => a + vecDot b (x - q)) hκ0 hb hV0 hSt hvolS hAS
  have hnegm : MemLp (fun x => -(u x - c₀ - vecDot p' (x - x₀))) 2 (volume.restrict S) :=
    hFpS'.neg
  have h3 := lipL2_add_le hS0 hSt hFp hnegm
  rw [hA] at h3
  have hneg : lipL2 S (fun x => -(u x - c₀ - vecDot p' (x - x₀))) =
      lipL2 S (fun x => u x - c₀ - vecDot p' (x - x₀)) := by
    unfold lipL2 lpBar
    rw [show (fun x => -(u x - c₀ - vecDot p' (x - x₀))) =
      -(fun x => u x - c₀ - vecDot p' (x - x₀)) from rfl, eLpNorm_neg]
  have h4 := lipL2_mono_set (f := fun x => u x - c₀ - vecDot p' (x - x₀)) hκ0 hSS' hS0 hS't
    hvolS' hFp'
  rw [hneg] at h3
  set X := lipL2 S (fun x => u x - c₀ - vecDot p (x - x₀)) with hX
  set Y := lipL2 S' (fun x => u x - c₀ - vecDot p' (x - x₀)) with hY
  have hX0 : 0 ≤ X := ENNReal.toReal_nonneg
  have hY0 : 0 ≤ Y := ENNReal.toReal_nonneg
  have hmain : s * ‖b‖ / 4 ≤ r * (X + r * Y) := by
    have : lipL2 (Metric.ball q s) (fun x => a + vecDot b (x - q)) ≤ r * (X + r * Y) := by
      calc lipL2 (Metric.ball q s) (fun x => a + vecDot b (x - q))
          ≤ r * lipL2 S (fun x => a + vecDot b (x - q)) := h2
        _ ≤ r * (X + r * Y) := by
          refine mul_le_mul_of_nonneg_left ?_ hr0
          calc lipL2 S (fun x => a + vecDot b (x - q)) ≤ X + lipL2 S _ := h3
            _ ≤ X + r * Y := by linarith only [h4]
    linarith only [h1, this]
  have hb1 : ‖b‖ ≤ (4 / (c * t)) * (r * (X + r * Y)) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have : s = c * t := rfl
    rw [this] at hmain
    linarith only [hmain]
  have hnb : ‖p - p'‖ = ‖b‖ := norm_sub_rev p p'
  have hpin : lipPin S j x₀ c₀ u p = t⁻¹ * X := by
    unfold lipPin
    rw [inv_pow]
  have hpin' : lipPin S' (j + 1) x₀ c₀ u p' = (t * 3)⁻¹ * Y := by
    unfold lipPin
    rw [inv_pow, pow_succ]
  rw [hnb, hpin, hpin']
  refine hb1.trans ?_
  have heq : (4 / (c * t)) * (r * (X + r * Y)) =
      (4 / c) * r * (t⁻¹ * X + 3 * r * ((t * 3)⁻¹ * Y)) := by
    field_simp
  rw [heq]
  have hP : 0 ≤ t⁻¹ * X := by positivity
  have hP' : 0 ≤ (t * 3)⁻¹ * Y := by positivity
  have : t⁻¹ * X + 3 * r * ((t * 3)⁻¹ * Y) ≤ (1 + 3 * r) * (t⁻¹ * X + (t * 3)⁻¹ * Y) := by
    have h5 : 0 ≤ 3 * r * (t⁻¹ * X) := by positivity
    linarith only [h5, hP']
  calc (4 / c) * r * (t⁻¹ * X + 3 * r * ((t * 3)⁻¹ * Y))
      ≤ (4 / c) * r * ((1 + 3 * r) * (t⁻¹ * X + (t * 3)⁻¹ * Y)) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := by ring

/-- **C2c(ii) — restriction to the next smaller scale.** -/
theorem lip_pin_restrict (d : ℕ) [NeZero d] (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    ∃ Cr : ℝ, 1 ≤ Cr ∧
      ∀ (S S' : Set (Vec d)) (z q x₀ : Vec d) (j : ℕ) (c₀ : ℝ) (u : Vec d → ℝ) (p : Vec d),
        MeasurableSet S → MeasurableSet S' → S ⊆ S' →
        Metric.ball q (c * (3 : ℝ) ^ j) ⊆ S → S' ⊆ Metric.ball z ((3 : ℝ) ^ (j + 1) / 2) →
        MemLp u 2 (volume.restrict S') →
        lipPin S j x₀ c₀ u p ≤ Cr * lipPin S' (j + 1) x₀ c₀ u p := by
  have _ := hc1
  set κ : ℝ := (3 / c) ^ d with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set r : ℝ := Real.sqrt κ with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  refine ⟨1 + 3 * r, by linarith only [hr0], ?_⟩
  intro S S' z q x₀ j c₀ u p hS hS' hSS' hb hS'z hu
  set t : ℝ := (3 : ℝ) ^ j with ht
  have ht0 : 0 < t := by positivity
  have hs0 : 0 < c * (3 : ℝ) ^ j := by positivity
  have hvol := lip_pin_geom hc hSS' hb hS'z
  have hV0 : volume (Metric.ball q (c * (3 : ℝ) ^ j)) ≠ 0 :=
    (Metric.measure_ball_pos volume q hs0).ne'
  have hS0 : volume S ≠ 0 := fun h => hV0 (measure_mono_null hb h)
  have hS't : volume S' ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono hS'z) measure_ball_lt_top).ne
  have hvolS' : volume S' ≤ ENNReal.ofReal κ * volume S := by
    refine hvol.trans ?_
    gcongr
  obtain ⟨hF, -⟩ := lip_pin_resid_memLp (S := S) hS' hS'z hu x₀ c₀ p hSS'
  have h4 := lipL2_mono_set (f := fun x => u x - c₀ - vecDot p (x - x₀)) hκ0 hSS' hS0 hS't
    hvolS' hF
  set Y := lipL2 S' (fun x => u x - c₀ - vecDot p (x - x₀)) with hY
  have hY0 : 0 ≤ Y := ENNReal.toReal_nonneg
  have hpin : lipPin S j x₀ c₀ u p = t⁻¹ * lipL2 S (fun x => u x - c₀ - vecDot p (x - x₀)) := by
    unfold lipPin
    rw [inv_pow]
  have hpin' : lipPin S' (j + 1) x₀ c₀ u p = (t * 3)⁻¹ * Y := by
    unfold lipPin
    rw [inv_pow, pow_succ]
  rw [hpin, hpin']
  have h5 : t⁻¹ * lipL2 S (fun x => u x - c₀ - vecDot p (x - x₀)) ≤ t⁻¹ * (r * Y) :=
    mul_le_mul_of_nonneg_left h4 (by positivity)
  have h6 : t⁻¹ * (r * Y) = 3 * r * ((t * 3)⁻¹ * Y) := by
    field_simp
  have h7 : 0 ≤ (t * 3)⁻¹ * Y := by positivity
  have h8 : 0 ≤ r * ((t * 3)⁻¹ * Y) := mul_nonneg hr0 h7
  calc _ ≤ t⁻¹ * (r * Y) := h5
    _ = 3 * r * ((t * 3)⁻¹ * Y) := h6
    _ ≤ (1 + 3 * r) * ((t * 3)⁻¹ * Y) := by linarith only [h7, h8]

/-- **C2c(iii) — the slope `0`.** -/
theorem lip_pin_zero (d : ℕ) [NeZero d] (S : Set (Vec d)) (z x₀ : Vec d) (j : ℕ) (c₀ : ℝ)
    (u : Vec d → ℝ) (p : Vec d) (hS : MeasurableSet S)
    (hSz : S ⊆ Metric.ball z ((3 : ℝ) ^ j / 2)) (hx₀ : ‖x₀ - z‖ ≤ (3 : ℝ) ^ j / 2)
    (hS0 : volume S ≠ 0) (hu : MemLp u 2 (volume.restrict S)) :
    lipPin S j x₀ c₀ u 0 ≤ lipPin S j x₀ c₀ u p + (d : ℝ) * ‖p‖ := by
  set t : ℝ := (3 : ℝ) ^ j with ht
  have ht0 : 0 < t := by positivity
  have hSt : volume S ≠ ⊤ := (lt_of_le_of_lt (measure_mono hSz) measure_ball_lt_top).ne
  obtain ⟨-, hF⟩ := lip_pin_resid_memLp (S := S) hS hSz hu x₀ c₀ p subset_rfl
  have hG : MemLp (fun x => vecDot p (x - x₀)) 2 (volume.restrict S) := by
    have := lip_pin_affine_memLp hS hSz x₀ p 0
    simpa using this
  have hsum : (fun x => u x - c₀ - vecDot (0 : Vec d) (x - x₀)) =
      fun x => (u x - c₀ - vecDot p (x - x₀)) + vecDot p (x - x₀) := by
    funext x
    simp [vecDot]
  have h1 := lipL2_add_le hS0 hSt hF hG
  have hbd : lipL2 S (fun x => vecDot p (x - x₀)) ≤ (d : ℝ) * (‖p‖ * t) := by
    refine lipL2_le_of_ae_abs_le (by positivity) hS0 hSt ?_
    rw [ae_restrict_iff' hS]
    refine Filter.Eventually.of_forall fun x hx => ?_
    have hxz : ‖x - z‖ < t / 2 := by
      have := hSz hx
      rwa [Metric.mem_ball, dist_eq_norm] at this
    have h2 : ‖x - x₀‖ ≤ t := by
      calc ‖x - x₀‖ = ‖(x - z) - (x₀ - z)‖ := by rw [sub_sub_sub_cancel_right]
        _ ≤ ‖x - z‖ + ‖x₀ - z‖ := norm_sub_le _ _
        _ ≤ t := by linarith only [hxz, hx₀]
    calc |vecDot p (x - x₀)| ≤ (d : ℝ) * (‖p‖ * ‖x - x₀‖) := lip_pin_abs_vecDot_le p _
      _ ≤ (d : ℝ) * (‖p‖ * t) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
          (Nat.cast_nonneg _)
  have hpin : lipPin S j x₀ c₀ u 0 = t⁻¹ * lipL2 S (fun x => u x - c₀ - vecDot (0 : Vec d) (x - x₀)) := by
    unfold lipPin
    rw [inv_pow]
  have hpin' : lipPin S j x₀ c₀ u p = t⁻¹ * lipL2 S (fun x => u x - c₀ - vecDot p (x - x₀)) := by
    unfold lipPin
    rw [inv_pow]
  rw [hpin, hpin', hsum]
  have h3 : t⁻¹ * lipL2 S (fun x => (u x - c₀ - vecDot p (x - x₀)) + vecDot p (x - x₀)) ≤
      t⁻¹ * (lipL2 S (fun x => u x - c₀ - vecDot p (x - x₀)) +
        lipL2 S (fun x => vecDot p (x - x₀))) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h4 : t⁻¹ * lipL2 S (fun x => vecDot p (x - x₀)) ≤ (d : ℝ) * ‖p‖ := by
    calc t⁻¹ * lipL2 S (fun x => vecDot p (x - x₀)) ≤ t⁻¹ * ((d : ℝ) * (‖p‖ * t)) :=
          mul_le_mul_of_nonneg_left hbd (by positivity)
      _ = (d : ℝ) * ‖p‖ := by field_simp
  calc _ ≤ _ := h3
    _ = t⁻¹ * lipL2 S (fun x => u x - c₀ - vecDot p (x - x₀)) +
        t⁻¹ * lipL2 S (fun x => vecDot p (x - x₀)) := by ring
    _ ≤ _ := by linarith only [h4]

/-- Witness: the hypotheses of the three statements hold together (`j = 0`, a ball of radius
`1/3` at the origin, the zero function). -/
example (d : ℕ) [NeZero d] : ∃ Cs : ℝ, 0 ≤ Cs ∧ ‖(0 : Vec d) - 0‖ ≤
    Cs * (lipPin (Metric.ball (0 : Vec d) (1 / 3)) 0 0 0 (fun _ => 0) 0 +
      lipPin (Metric.ball (0 : Vec d) (1 / 3)) (0 + 1) 0 0 (fun _ => 0) 0) := by
  obtain ⟨Cs, hCs, H⟩ := lip_pin_slope d (1 / 3) (by norm_num) (by norm_num)
  refine ⟨Cs, hCs, H (Metric.ball 0 (1 / 3)) (Metric.ball 0 (1 / 3)) 0 0 0 0 0 (fun _ => 0) 0 0
    Metric.isOpen_ball.measurableSet Metric.isOpen_ball.measurableSet subset_rfl
    (by simp) (Metric.ball_subset_ball (by norm_num)) ?_⟩
  exact MemLp.zero'

example (d : ℕ) [NeZero d] :
    lipPin (Metric.ball (0 : Vec d) (1 / 2)) 0 0 0 (fun _ => 0) 0 ≤
      lipPin (Metric.ball (0 : Vec d) (1 / 2)) 0 0 0 (fun _ => 0) 0 + (d : ℝ) * ‖(0 : Vec d)‖ :=
  lip_pin_zero d (Metric.ball 0 (1 / 2)) 0 0 0 0 (fun _ => 0) 0
    Metric.isOpen_ball.measurableSet (by simp) (by simp)
    (Metric.measure_ball_pos volume _ (by norm_num)).ne' MemLp.zero'

end SuperdiffusionCLT.Section7
