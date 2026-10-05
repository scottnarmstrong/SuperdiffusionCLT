/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Root.AnnealedDtB
public import SuperdiffusionCLT.Section8.Prereq.CrudeMomentsLargeH
public import SuperdiffusionCLT.Section8.Prereq.GradientScaleB

/-!
# The annealed variance bound: the crude constant is a polynomial in the gradient scale

The constant of the crude second moment bound depends on the sample through the freezing amplitude
`min 1 (δ₀ ν / (1 + 3 d G))`, `G` the gradient scale.  It is bounded by a constant times a power of
`1 + G`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization MeasureTheory

noncomputable section

theorem annDt_amp_inv_le {x : ℝ} (hx : 0 < x) : (min 1 x)⁻¹ ≤ 1 + x⁻¹ := by
  have : 0 ≤ x⁻¹ := inv_nonneg.2 hx.le
  rcases min_choice 1 x with h | h
  · rw [h]; simp only [inv_one]; linarith only [this]
  · rw [h]; linarith only

variable {d : ℕ}

/-- The amplitude is bounded below by a constant over `1 + G`. -/
theorem annDt_amp_inv_le_gradient {nu δ0 : ℝ} (hnu : 0 < nu) (hδ : 0 < δ0) {G : ℝ} (hG : 0 ≤ G) :
    (min 1 (δ0 * nu / (1 + 3 * ((d : ℝ) * G))))⁻¹ ≤
      (1 + (1 + 3 * (d : ℝ)) / (δ0 * nu)) * (1 + G) := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hdG : 0 ≤ (d : ℝ) * G := mul_nonneg hd hG
  have hden : 0 < 1 + 3 * ((d : ℝ) * G) := by linarith only [hdG]
  have hx : 0 < δ0 * nu / (1 + 3 * ((d : ℝ) * G)) := by positivity
  refine (annDt_amp_inv_le hx).trans ?_
  rw [inv_div]
  have hc : 0 ≤ (1 + 3 * (d : ℝ)) / (δ0 * nu) := by positivity
  have h1 : (1 + 3 * ((d : ℝ) * G)) / (δ0 * nu) ≤ (1 + 3 * (d : ℝ)) / (δ0 * nu) * (1 + G) := by
    rw [← mul_div_right_comm]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    nlinarith only [hG, hd, hdG]
  nlinarith only [h1, hc, hG]

theorem annDt_cut_le [NeZero d] {nu c0 δ0 : ℝ} (hnu : 0 < nu) (hc0 : 0 ≤ c0) (hδ : 0 < δ0)
    (n : ℕ) :
    ∃ s1 : ℝ, 1 ≤ s1 ∧ ∀ G : ℝ, 0 ≤ G →
      crudeMomL_cut d nu c0 (min 1 (δ0 * nu / (1 + 3 * ((d : ℝ) * G)))) n ≤
        s1 * (1 + G) ^ d := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  set e1 : ℝ := 1 + (1 + 3 * (d : ℝ)) / (δ0 * nu) with he1
  have he1' : 1 ≤ e1 := by
    have : 0 ≤ (1 + 3 * (d : ℝ)) / (δ0 * nu) := by positivity
    linarith only [this]
  set e2 : ℝ := (1 + 2 * (d : ℝ)) * e1 with he2
  have hCc := crudeMomL_Cc_nonneg (d := d) hnu
  have hΛ := crudeMomL_Lam1_pos hnu hc0 n
  have hr := crudeMomL_r1_pos (d := d) hnu
  have hκ := crudeMomL_kappa_pos n hΛ hr
  set Cc := crudeMomL_Cc d nu
  set Λ1 := crudeMomL_Lam1 nu c0 n
  set κ := crudeMomL_kappa n Λ1 (crudeMomL_r1 d nu)
  set a0 : ℝ := Cc * (Λ1 * (1 + 4 * (n : ℝ)) ^ n + 4) with ha0
  have ha0nn : 0 ≤ a0 := by
    have : 0 ≤ Λ1 * (1 + 4 * (n : ℝ)) ^ n + 4 := by positivity
    exact mul_nonneg hCc this
  set b0 : ℝ := ((4 * n + 4 * n * d : ℕ) : ℝ) + d with hb0
  have hb0nn : 0 ≤ b0 := by positivity
  set q1 : ℝ := a0 * (4 * e2) ^ d + b0 with hq1
  have hq1nn : 0 ≤ q1 := by positivity
  refine ⟨1 + q1 / κ, by have : 0 ≤ q1 / κ := by positivity
                         linarith only [this], fun G hG => ?_⟩
  have hG1 : 1 ≤ 1 + G := by linarith only [hG]
  have hpow1 : 1 ≤ (1 + G) ^ d := one_le_pow₀ hG1
  have hAq : (1 + 2 * (d : ℝ)) / (min 1 (δ0 * nu / (1 + 3 * ((d : ℝ) * G)))) ≤
      e2 * (1 + G) := by
    rw [div_eq_mul_inv, he2, mul_assoc]
    exact mul_le_mul_of_nonneg_left (annDt_amp_inv_le_gradient hnu hδ hG) (by positivity)
  have hAq0 : 0 ≤ (1 + 2 * (d : ℝ)) / (min 1 (δ0 * nu / (1 + 3 * ((d : ℝ) * G)))) := by
    have hdG : 0 ≤ (d : ℝ) * G := mul_nonneg hd hG
    have : 0 < δ0 * nu / (1 + 3 * ((d : ℝ) * G)) := by positivity
    have : 0 < min 1 (δ0 * nu / (1 + 3 * ((d : ℝ) * G))) := lt_min one_pos this
    positivity
  unfold crudeMomL_cut crudeMomL_W0
  refine max_le ?_ ?_
  · have : 0 ≤ q1 / κ := by positivity
    nlinarith only [this, hpow1]
  · rw [div_le_iff₀ hκ]
    have h4 : (4 * ((1 + 2 * (d : ℝ)) / (min 1 (δ0 * nu / (1 + 3 * ((d : ℝ) * G))))))  ^ d ≤
        (4 * e2) ^ d * (1 + G) ^ d := by
      rw [← mul_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ d
      nlinarith only [hAq]
    have hQ : a0 * (4 * ((1 + 2 * (d : ℝ)) / (min 1 (δ0 * nu / (1 + 3 * ((d : ℝ) * G)))))) ^ d + b0
        ≤ q1 * (1 + G) ^ d := by
      have := mul_le_mul_of_nonneg_left h4 ha0nn
      nlinarith only [this, hpow1, hb0nn, hq1]
    have hfin : q1 * (1 + G) ^ d ≤ (1 + q1 / κ) * (1 + G) ^ d * κ := by
      have h5 : q1 ≤ (1 + q1 / κ) * κ := by
        rw [add_mul, one_mul, div_mul_cancel₀ _ hκ.ne']
        linarith only [hκ]
      have h6 := mul_le_mul_of_nonneg_right h5 (le_trans zero_le_one hpow1)
      linarith only [h6]
    have h := hQ.trans hfin
    simp only [ha0, hb0] at h
    linarith only [h]

/-- **The crude constant is a power of `1 + G`.** -/
theorem annDt_const_le [NeZero d] {nu c0 δ0 : ℝ} (hnu : 0 < nu) (hc0 : 0 ≤ c0) (hδ : 0 < δ0)
    (n : ℕ) :
    ∃ c4 : ℝ, 1 ≤ c4 ∧ ∀ G : ℝ, 0 ≤ G →
      crudeMomL_const d nu c0 (min 1 (δ0 * nu / (1 + 3 * ((d : ℝ) * G)))) n ≤
        c4 * (1 + G) ^ (8 * n * d) := by
  obtain ⟨s1, hs1, hcut⟩ := annDt_cut_le (d := d) hnu hc0 hδ n
  set cd : ℝ := 1 + 2 * Real.log (1 + 2 * (d : ℝ)) with hcd
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hcd1 : 1 ≤ cd := by
    have : 0 ≤ Real.log (1 + 2 * (d : ℝ)) := Real.log_nonneg (by linarith only [hd0])
    linarith only [this]
  set bud : ℝ := 8 * Real.exp 1 * crudeMomL_budget (crudeMomL_kap d nu c0 n) with hbud
  have hbud0 : 0 ≤ bud := mul_nonneg (by positivity) (crudeMomL_budget_nonneg _)
  refine ⟨14641 * ((s1 * cd) ^ (8 * n) + bud), ?_, fun G hG => ?_⟩
  · have h1 : 1 ≤ (s1 * cd) ^ (8 * n) := one_le_pow₀ (by nlinarith only [hs1, hcd1])
    nlinarith only [h1, hbud0]
  · have hG1 : 1 ≤ 1 + G := by linarith only [hG]
    have hpow : 1 ≤ (1 + G) ^ (8 * n * d) := one_le_pow₀ hG1
    have hc1 := one_le_crudeMomL_cut (d := d) nu c0 (min 1 (δ0 * nu / (1 + 3 * ((d : ℝ) * G)))) n
    have hcutG := hcut G hG
    set cut := crudeMomL_cut d nu c0 (min 1 (δ0 * nu / (1 + 3 * ((d : ℝ) * G)))) n
    have h1 : (cut * cd) ^ (8 * n) ≤ (s1 * cd) ^ (8 * n) * (1 + G) ^ (8 * n * d) := by
      have : cut * cd ≤ (s1 * cd) * (1 + G) ^ d := by
        have := mul_le_mul_of_nonneg_right hcutG (by linarith only [hcd1] : 0 ≤ cd)
        linarith only [this]
      calc (cut * cd) ^ (8 * n) ≤ ((s1 * cd) * (1 + G) ^ d) ^ (8 * n) :=
            pow_le_pow_left₀ (by positivity) this _
        _ = _ := by rw [mul_pow, ← pow_mul]; ring_nf
    unfold crudeMomL_const
    have h2 : bud ≤ bud * (1 + G) ^ (8 * n * d) := by nlinarith only [hbud0, hpow]
    nlinarith only [h1, h2]

end

end SuperdiffusionCLT.Section8
