/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Defs

/-!
# Mollification of a Lipschitz function (`e.Dir.new.Linfty.gsmooth`)

`G = φ ⋆ h` for a smooth bump `φ` supported in the unit ball and an `L`-Lipschitz function `h`:
`G` is smooth, `|G - h| ≤ L`, `G` is `L`-Lipschitz and `∇G` is `C L`-Lipschitz, with `C = ∫ ‖∇φ‖`.
The mollification of `g` at radius `r` is `r G(x / r)` with `h = g(r ·) / r`.  Lipschitz constants
are for the sup norm on `Vec d`; the constant `C` depends on `d` only.

`G = φ ⋆ h` for a smooth bump `φ` supported in the unit ball and an `L`-Lipschitz function `h`:
`G` is smooth, `|G - h| ≤ L`, `G` is `L`-Lipschitz and `∇G` is `C L`-Lipschitz, with `C = ∫ ‖∇φ‖`.
-/

@[expose] public section

open Homogenization MeasureTheory Convolution

namespace SuperdiffusionCLT.Section7

variable {d : ℕ} {r : ℝ}


/-- The smooth unit bump: nonnegative, of integral one, supported in the open unit ball. -/
noncomputable def li1_bump (d : ℕ) : Vec d → ℝ :=
  ((⟨1 / 2, 1, by norm_num, by norm_num⟩ : ContDiffBump (0 : Vec d))).normed volume

theorem li1_bump_contDiff (d : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (li1_bump d) :=
  ContDiffBump.contDiff_normed _

theorem li1_bump_nonneg (d : ℕ) (x : Vec d) : 0 ≤ li1_bump d x :=
  ContDiffBump.nonneg_normed _ x

theorem li1_bump_integral (d : ℕ) : ∫ x, li1_bump d x = 1 :=
  ContDiffBump.integral_normed _

theorem li1_bump_compact (d : ℕ) : HasCompactSupport (li1_bump d) :=
  ContDiffBump.hasCompactSupport_normed _

theorem li1_bump_norm_lt {d : ℕ} {x : Vec d} (hx : li1_bump d x ≠ 0) : ‖x‖ < 1 := by
  have h : x ∈ Function.support (li1_bump d) := hx
  have h2 := ContDiffBump.support_normed_eq
    ((⟨1 / 2, 1, by norm_num, by norm_num⟩ : ContDiffBump (0 : Vec d))) (μ := volume)
  unfold li1_bump at h
  rw [h2] at h
  simpa using h

theorem li1_bump_integrable (d : ℕ) : Integrable (li1_bump d) :=
  (li1_bump_contDiff d).continuous.integrable_of_hasCompactSupport (li1_bump_compact d)

/-- The constant `∫ ‖∇φ‖`. -/
noncomputable def li1_const (d : ℕ) : ℝ := ∫ x, ‖fderiv ℝ (li1_bump d) x‖

theorem li1_fderiv_continuous (d : ℕ) : Continuous (fderiv ℝ (li1_bump d)) :=
  (li1_bump_contDiff d).continuous_fderiv (by simp)

theorem li1_fderiv_compact (d : ℕ) : HasCompactSupport (fderiv ℝ (li1_bump d)) :=
  (li1_bump_compact d).fderiv (𝕜 := ℝ)

theorem li1_fderiv_norm_integrable (d : ℕ) : Integrable (fun x => ‖fderiv ℝ (li1_bump d) x‖) :=
  ((li1_fderiv_continuous d).norm).integrable_of_hasCompactSupport (li1_fderiv_compact d).norm

theorem li1_const_nonneg (d : ℕ) : 0 ≤ li1_const d :=
  integral_nonneg fun _ => norm_nonneg _

/-- The unit-scale mollification. -/
noncomputable def li1_unit (h : Vec d → ℝ) : Vec d → ℝ :=
  (li1_bump d) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] h

theorem li1_unit_apply (h : Vec d → ℝ) (x : Vec d) :
    li1_unit h x = ∫ t, li1_bump d t * h (x - t) := by
  unfold li1_unit
  rw [convolution_def]
  rfl

/-- Integrability of `t ↦ φ t * h (x - t)` for continuous `h`. -/
theorem li1_integrable_shift {h : Vec d → ℝ} (hh : Continuous h) (x : Vec d) :
    Integrable (fun t => li1_bump d t * h (x - t)) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact (li1_bump_contDiff d).continuous.mul (hh.comp (continuous_const.sub continuous_id))
  · exact (li1_bump_compact d).mul_right

theorem li1_unit_sub_le {h : Vec d → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hh : ∀ x y, |h x - h y| ≤ L * ‖x - y‖) (x : Vec d) : |li1_unit h x - h x| ≤ L := by
  have hc : Continuous h := by
    have : LipschitzWith (Real.toNNReal L) h := LipschitzWith.of_dist_le_mul fun a b => by
      rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hL]; exact hh a b
    exact this.continuous
  have h1 : li1_unit h x - h x = ∫ t, li1_bump d t * (h (x - t) - h x) := by
    rw [li1_unit_apply]
    simp only [mul_sub]
    rw [integral_sub (li1_integrable_shift hc x) ((li1_bump_integrable d).mul_const _),
      integral_mul_const, li1_bump_integral, one_mul]
  rw [h1]
  have hbd : ∀ t, ‖li1_bump d t * (h (x - t) - h x)‖ ≤ L * li1_bump d t := by
    intro t
    by_cases ht : li1_bump d t = 0
    · simp [ht]
    · have := li1_bump_norm_lt ht
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (li1_bump_nonneg d t),
        abs_sub_comm]
      have h2 := hh x (x - t)
      rw [sub_sub_cancel] at h2
      have h3 : L * ‖t‖ ≤ L := by nlinarith only [this, hL]
      nlinarith only [h2, h3, li1_bump_nonneg d t, hL]
  have := norm_integral_le_of_norm_le ((li1_bump_integrable d).const_mul L) (Filter.Eventually.of_forall hbd)
  rw [integral_const_mul, li1_bump_integral, mul_one] at this
  simpa using this



theorem li1_lip_continuous {h : Vec d → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hh : ∀ x y, |h x - h y| ≤ L * ‖x - y‖) : Continuous h := by
  have : LipschitzWith (Real.toNNReal L) h := LipschitzWith.of_dist_le_mul fun a b => by
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hL]; exact hh a b
  exact this.continuous

theorem li1_unit_lip {h : Vec d → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hh : ∀ x y, |h x - h y| ≤ L * ‖x - y‖) (x y : Vec d) :
    |li1_unit h x - li1_unit h y| ≤ L * ‖x - y‖ := by
  have hc := li1_lip_continuous hL hh
  rw [li1_unit_apply, li1_unit_apply, ← integral_sub (li1_integrable_shift hc x)
    (li1_integrable_shift hc y)]
  have hbd : ∀ t, ‖li1_bump d t * h (x - t) - li1_bump d t * h (y - t)‖ ≤
      (L * ‖x - y‖) * li1_bump d t := by
    intro t
    rw [← mul_sub, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (li1_bump_nonneg d t)]
    have h2 := hh (x - t) (y - t)
    rw [sub_sub_sub_cancel_right] at h2
    nlinarith only [h2, li1_bump_nonneg d t]
  have := norm_integral_le_of_norm_le ((li1_bump_integrable d).const_mul (L * ‖x - y‖))
    (Filter.Eventually.of_forall hbd)
  rw [integral_const_mul, li1_bump_integral, mul_one] at this
  simpa using this

theorem li1_unit_contDiff {h : Vec d → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hh : ∀ x y, |h x - h y| ≤ L * ‖x - y‖) : ContDiff ℝ (⊤ : ℕ∞) (li1_unit h) :=
  HasCompactSupport.contDiff_convolution_left (μ := (volume : Measure (Vec d))) _ (li1_bump_compact d) (li1_bump_contDiff d)
    ((li1_lip_continuous hL hh).locallyIntegrable (μ := (volume : Measure (Vec d))))

theorem li1_unit_fderiv_apply {h : Vec d → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hh : ∀ x y, |h x - h y| ≤ L * ‖x - y‖) (x v : Vec d) :
    fderiv ℝ (li1_unit h) x v = ∫ t, fderiv ℝ (li1_bump d) t v * h (x - t) := by
  have hd := HasCompactSupport.hasFDerivAt_convolution_left (μ := (volume : Measure (Vec d))) (ContinuousLinearMap.mul ℝ ℝ)
    (li1_bump_compact d) ((li1_bump_contDiff d).of_le (by simp)) 
    ((li1_lip_continuous hL hh).locallyIntegrable (μ := (volume : Measure (Vec d)))) x
  have hd2 : HasFDerivAt (li1_unit h) _ x := hd
  rw [hd2.fderiv]
  rw [convolution_def]
  have hc := li1_lip_continuous hL hh
  have hint : Integrable (fun t => (ContinuousLinearMap.precompL (Vec d)
      (ContinuousLinearMap.mul ℝ ℝ)) (fderiv ℝ (li1_bump d) t) (h (x - t))) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact ((ContinuousLinearMap.precompL (Vec d)
        (ContinuousLinearMap.mul ℝ ℝ)).continuous.comp (li1_fderiv_continuous d)).clm_apply
        (hc.comp (continuous_const.sub continuous_id))
    · refine HasCompactSupport.intro (li1_fderiv_compact d) fun t ht => ?_
      rw [image_eq_zero_of_notMem_tsupport ht]
      simp
  rw [ContinuousLinearMap.integral_apply hint]
  rfl

theorem li1_unit_fderiv_lip {h : Vec d → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hh : ∀ x y, |h x - h y| ≤ L * ‖x - y‖) (x y : Vec d) :
    ‖fderiv ℝ (li1_unit h) x - fderiv ℝ (li1_unit h) y‖ ≤ (li1_const d * L) * ‖x - y‖ := by
  have hc := li1_lip_continuous hL hh
  have hint : ∀ z : Vec d, ∀ v : Vec d,
      Integrable (fun t => fderiv ℝ (li1_bump d) t v * h (z - t)) := by
    intro z v
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (((li1_fderiv_continuous d).clm_apply continuous_const)).mul
        (hc.comp (continuous_const.sub continuous_id))
    · refine HasCompactSupport.intro (li1_fderiv_compact d) fun t ht => ?_
      rw [image_eq_zero_of_notMem_tsupport ht]
      simp
  refine ContinuousLinearMap.opNorm_le_bound _ (by
    have := li1_const_nonneg d
    positivity) fun v => ?_
  rw [sub_apply, li1_unit_fderiv_apply hL hh, li1_unit_fderiv_apply hL hh,
    ← integral_sub (hint x v) (hint y v)]
  have hbd : ∀ t, ‖fderiv ℝ (li1_bump d) t v * h (x - t) - fderiv ℝ (li1_bump d) t v * h (y - t)‖
      ≤ (L * ‖x - y‖ * ‖v‖) * ‖fderiv ℝ (li1_bump d) t‖ := by
    intro t
    rw [← mul_sub, norm_mul, Real.norm_eq_abs (h (x - t) - h (y - t))]
    have h2 := hh (x - t) (y - t)
    rw [sub_sub_sub_cancel_right] at h2
    have h3 : ‖fderiv ℝ (li1_bump d) t v‖ ≤ ‖fderiv ℝ (li1_bump d) t‖ * ‖v‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have h4 : 0 ≤ ‖fderiv ℝ (li1_bump d) t v‖ := norm_nonneg _
    have h5 : 0 ≤ L * ‖x - y‖ := by positivity
    nlinarith only [h2, h3, h4, h5]
  have := norm_integral_le_of_norm_le ((li1_fderiv_norm_integrable d).const_mul (L * ‖x - y‖ * ‖v‖))
    (Filter.Eventually.of_forall hbd)
  rw [integral_const_mul] at this
  unfold li1_const
  calc _ ≤ _ := this
    _ = _ := by ring

theorem li1_unit_fderiv_norm {h : Vec d → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hh : ∀ x y, |h x - h y| ≤ L * ‖x - y‖) (x : Vec d) : ‖fderiv ℝ (li1_unit h) x‖ ≤ L := by
  have hl : LipschitzWith (Real.toNNReal L) (li1_unit h) :=
    LipschitzWith.of_dist_le_mul fun a b => by
      rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hL]; exact li1_unit_lip hL hh a b
  have := norm_fderiv_le_of_lipschitz ℝ (x₀ := x) hl
  rwa [Real.coe_toNNReal _ hL] at this

/-- The rescaled mollification `r G(x / r)` of `g`, `G = φ ⋆ (g(r ·) / r)`. -/
noncomputable def li1_mollify (r : ℝ) (g : Vec d → ℝ) (x : Vec d) : ℝ :=
  r * li1_unit (fun y => g (r • y) / r) (r⁻¹ • x)

theorem li1_scaled_lip {g : Vec d → ℝ} {L r : ℝ} (hr : 0 < r)
    (hg : ∀ x y, |g x - g y| ≤ L * ‖x - y‖) (x y : Vec d) :
    |g (r • x) / r - g (r • y) / r| ≤ L * ‖x - y‖ := by
  rw [← sub_div, abs_div, abs_of_pos hr, div_le_iff₀ hr]
  have := hg (r • x) (r • y)
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hr] at this
  linarith only [this]

theorem li1_mollify_fderiv (hr : 0 < r) {g : Vec d → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hg : ∀ x y, |g x - g y| ≤ L * ‖x - y‖) (x : Vec d) :
    fderiv ℝ (li1_mollify r g) x = fderiv ℝ (li1_unit (fun y => g (r • y) / r)) (r⁻¹ • x) := by
  have hh := li1_scaled_lip hr hg
  have hG := ((li1_unit_contDiff hL hh).differentiable (by simp)) (r⁻¹ • x)
  have hs : HasFDerivAt (fun x : Vec d => r⁻¹ • x) (r⁻¹ • ContinuousLinearMap.id ℝ (Vec d)) x :=
    (hasFDerivAt_id x).const_smul r⁻¹
  have hc := (hG.hasFDerivAt.comp x hs).const_mul r
  have : HasFDerivAt (li1_mollify r g) (r • (fderiv ℝ (li1_unit (fun y => g (r • y) / r))
      (r⁻¹ • x)).comp (r⁻¹ • ContinuousLinearMap.id ℝ (Vec d))) x := hc
  rw [this.fderiv]
  ext v
  simp [smul_smul, mul_inv_cancel₀ hr.ne']

theorem li1_mollify_contDiff (hr : 0 < r) {g : Vec d → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hg : ∀ x y, |g x - g y| ≤ L * ‖x - y‖) : ContDiff ℝ (⊤ : ℕ∞) (li1_mollify r g) := by
  have hh := li1_scaled_lip hr hg
  exact contDiff_const.mul ((li1_unit_contDiff hL hh).comp (contDiff_const_smul _))

theorem li1_mollify_approx (hr : 0 < r) {g : Vec d → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hg : ∀ x y, |g x - g y| ≤ L * ‖x - y‖) (x : Vec d) :
    |li1_mollify r g x - g x| ≤ r * L := by
  have hh := li1_scaled_lip hr hg
  have h1 := li1_unit_sub_le hL hh (r⁻¹ • x)
  have h2 : g (r • r⁻¹ • x) / r = g x / r := by
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have h3 : li1_mollify r g x - g x =
      r * (li1_unit (fun y => g (r • y) / r) (r⁻¹ • x) - g (r • r⁻¹ • x) / r) := by
    rw [h2]
    unfold li1_mollify
    field_simp
  rw [h3, abs_mul, abs_of_pos hr]
  exact mul_le_mul_of_nonneg_left h1 hr.le

theorem li1_mollify_fderiv_norm (hr : 0 < r) {g : Vec d → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hg : ∀ x y, |g x - g y| ≤ L * ‖x - y‖) (x : Vec d) : ‖fderiv ℝ (li1_mollify r g) x‖ ≤ L := by
  rw [li1_mollify_fderiv hr hL hg]
  exact li1_unit_fderiv_norm hL (li1_scaled_lip hr hg) _

theorem li1_mollify_fderiv_lip (hr : 0 < r) {g : Vec d → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hg : ∀ x y, |g x - g y| ≤ L * ‖x - y‖) (x y : Vec d) :
    ‖fderiv ℝ (li1_mollify r g) x - fderiv ℝ (li1_mollify r g) y‖ ≤
      li1_const d * L / r * ‖x - y‖ := by
  rw [li1_mollify_fderiv hr hL hg, li1_mollify_fderiv hr hL hg]
  refine (li1_unit_fderiv_lip hL (li1_scaled_lip hr hg) _ _).trans ?_
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
  apply le_of_eq
  field_simp

theorem li1_mollify_iterated_norm (hr : 0 < r) {g : Vec d → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hg : ∀ x y, |g x - g y| ≤ L * ‖x - y‖) (x : Vec d) :
    ‖iteratedFDeriv ℝ 2 (li1_mollify r g) x‖ ≤ li1_const d * L / r := by
  have hC : 0 ≤ li1_const d * L / r := by
    have := li1_const_nonneg d
    positivity
  have hl : LipschitzWith (Real.toNNReal (li1_const d * L / r)) (fderiv ℝ (li1_mollify r g)) :=
    LipschitzWith.of_dist_le_mul fun a b => by
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hC]
      exact li1_mollify_fderiv_lip hr hL hg a b
  have h1 := norm_fderiv_le_of_lipschitz ℝ (x₀ := x) hl
  rw [Real.coe_toNNReal _ hC] at h1
  have h2 : ‖iteratedFDeriv ℝ 2 (li1_mollify r g) x‖ =
      ‖iteratedFDeriv ℝ 1 (fderiv ℝ (li1_mollify r g)) x‖ :=
    (norm_iteratedFDeriv_fderiv (n := 1)).symm
  rw [h2, norm_iteratedFDeriv_one]
  exact h1

/-- **Smoothing of Lipschitz boundary data** (`e.Dir.new.Linfty.gsmooth`).  There is `C = C(d)`
such that every `L`-Lipschitz function `g` on `Vec d` and every radius `r > 0` possess a smooth
`g̃` with `|g̃ - g| ≤ r L`, `‖∇g̃‖ ≤ L`, `∇g̃` being `C L / r`-Lipschitz and
`‖∇²g̃‖ ≤ C L / r`. -/
theorem li1_exists_mollification (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : Vec d → ℝ) (L r : ℝ), 0 ≤ L → 0 < r →
      (∀ x y, |g x - g y| ≤ L * ‖x - y‖) →
      ∃ gt : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) gt ∧ (∀ x, |gt x - g x| ≤ r * L) ∧
        (∀ x, ‖fderiv ℝ gt x‖ ≤ L) ∧
        (∀ x y, ‖fderiv ℝ gt x - fderiv ℝ gt y‖ ≤ C * L / r * ‖x - y‖) ∧
        (∀ x, ‖iteratedFDeriv ℝ 2 gt x‖ ≤ C * L / r) :=
  ⟨li1_const d, li1_const_nonneg d, fun g _ r hL hr hg =>
    ⟨li1_mollify r g, li1_mollify_contDiff hr hL hg, li1_mollify_approx hr hL hg,
      li1_mollify_fderiv_norm hr hL hg, li1_mollify_fderiv_lip hr hL hg,
      li1_mollify_iterated_norm hr hL hg⟩⟩

/-- The same for a function Lipschitz only on a set `W`: the Lipschitz extension of Mathlib is
mollified, and the approximation holds on `W`. -/
theorem li1_exists_mollification_on (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (W : Set (Vec d)) (g : Vec d → ℝ) (L : NNReal) (r : ℝ), 0 < r →
      LipschitzOnWith L g W →
      ∃ gt : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) gt ∧ (∀ x ∈ W, |gt x - g x| ≤ r * L) ∧
        (∀ x, ‖fderiv ℝ gt x‖ ≤ L) ∧
        (∀ x y, ‖fderiv ℝ gt x - fderiv ℝ gt y‖ ≤ C * L / r * ‖x - y‖) ∧
        (∀ x, ‖iteratedFDeriv ℝ 2 gt x‖ ≤ C * L / r) := by
  obtain ⟨C, hC, h⟩ := li1_exists_mollification d
  refine ⟨C, hC, fun W g L r hr hg => ?_⟩
  obtain ⟨ge, hge, heq⟩ := hg.extend_real
  have hl : ∀ x y, |ge x - ge y| ≤ (L : ℝ) * ‖x - y‖ := fun x y => by
    have := hge.dist_le_mul x y
    rwa [Real.dist_eq, dist_eq_norm] at this
  obtain ⟨gt, h1, h2, h3, h4, h5⟩ := h ge L r L.coe_nonneg hr hl
  exact ⟨gt, h1, fun x hx => by rw [heq hx]; exact h2 x, h3, h4, h5⟩

/-- Witness: the zero datum, radius one. -/
example : ∃ gt : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) gt ∧ (∀ x, |gt x - (0 : Vec 2 → ℝ) x| ≤ 1 * 0) := by
  obtain ⟨C, -, h⟩ := li1_exists_mollification 2
  obtain ⟨gt, h1, h2, -⟩ := h 0 0 1 le_rfl one_pos (fun x y => by simp)
  exact ⟨gt, h1, h2⟩

end SuperdiffusionCLT.Section7
