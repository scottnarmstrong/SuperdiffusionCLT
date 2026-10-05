/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Root.DtExpL
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import SuperdiffusionCLT.Section8.Root.AnnealedDtE

/-!
# The quenched second moment: thresholds and tails

The times beyond which the numerical conditions of the good-time estimate hold, and the tails of
the random scales rewritten at the scale `log t`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Filter Topology

/-- A power times a stretched exponential decay is eventually at most one. -/
theorem dtExp_pow_exp_le (A k c κ : ℝ) (hc : 0 < c) (hκ : 0 < κ) :
    ∀ᶠ L : ℝ in atTop, A * L ^ k * Real.exp (-(c * L ^ κ)) ≤ 1 := by
  have h1 : Tendsto (fun L : ℝ => L ^ κ) atTop atTop := tendsto_rpow_atTop hκ
  have h2 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k / κ) c hc).comp h1
  have h3 := h2.const_mul A
  rw [mul_zero] at h3
  have h4 : ∀ᶠ L : ℝ in atTop, A * ((L ^ κ) ^ (k / κ) * Real.exp (-c * L ^ κ)) < 1 :=
    h3.eventually (gt_mem_nhds one_pos)
  filter_upwards [h4, eventually_gt_atTop 0] with L hL hL0
  have : (L ^ κ) ^ (k / κ) = L ^ k := by
    rw [← Real.rpow_mul hL0.le]; congr 1; field_simp
  calc A * L ^ k * Real.exp (-(c * L ^ κ)) = A * ((L ^ κ) ^ (k / κ) * Real.exp (-c * L ^ κ)) := by
        rw [this]; ring_nf
    _ ≤ 1 := hL.le

/-- **The thresholds of the good time.** -/
theorem dtExp_thresholds {d : ℕ} (hd : 1 ≤ d) {c α β cE K3 B' arate : ℝ}
    (hα0 : 0 < α) (hcE : 0 < cE) (hK3 : 0 ≤ K3) :
    ∃ L0 : ℝ, 1 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
      Real.sqrt (8 * c) ≤ L ^ (α / 6) ∧
      2 * Real.exp (-(cE / 2 * L ^ (α / 6))) ≤ 1 ∧
      d * Real.sqrt (K3 * Real.exp (cE / (64 * d) * L ^ (α / 6)) ^ (16 * d)) * (2 * L) ^ 8 *
        Real.sqrt (2 * Real.exp (-(cE / 2 * L ^ (α / 6)))) ≤ 1 ∧
      L * (2 * Real.exp (-(cE / 2 * L ^ (α / 6)))) ≤ 1 ∧
      2 * B' ≤ L ∧
      arate ≤ Real.exp (cE / (64 * d) * L ^ (α / 6)) ∧
      L ^ β ≤ Real.exp (cE / (64 * d) * L ^ (α / 6)) := by
  have hd0 : (0 : ℝ) < d := Nat.cast_pos.2 (by omega)
  have hκ : 0 < α / 6 := by positivity
  have hc3 : 0 < cE / (64 * d) := by positivity
  have e1 : ∀ᶠ L : ℝ in atTop, Real.sqrt (8 * c) ≤ L ^ (α / 6) :=
    (tendsto_rpow_atTop hκ).eventually_ge_atTop _
  have e2 : ∀ᶠ L : ℝ in atTop, 2 * Real.exp (-(cE / 2 * L ^ (α / 6))) ≤ 1 := by
    filter_upwards [dtExp_pow_exp_le 2 0 (cE / 2) (α / 6) (by positivity) hκ,
      eventually_gt_atTop 0] with L hL hL0
    simpa [Real.rpow_zero] using hL
  have e3 : ∀ᶠ L : ℝ in atTop, d * Real.sqrt (K3 * Real.exp (cE / (64 * d) * L ^ (α / 6)) ^ (16 * d)) *
      (2 * L) ^ 8 * Real.sqrt (2 * Real.exp (-(cE / 2 * L ^ (α / 6)))) ≤ 1 := by
    filter_upwards [dtExp_pow_exp_le (d * Real.sqrt K3 * Real.sqrt 2 * 2 ^ 8) 8 (cE / 8) (α / 6)
      (by positivity) hκ, eventually_gt_atTop 0] with L hL hL0
    set y := L ^ (α / 6) with hy
    have h1 : Real.exp (cE / (64 * d) * y) ^ (16 * d) = Real.exp (cE / 4 * y) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; field_simp; ring
    have h2 : Real.sqrt (K3 * Real.exp (cE / 4 * y)) = Real.sqrt K3 * Real.exp (cE / 8 * y) := by
      rw [Real.sqrt_mul hK3, annDt_sqrt_exp]; congr 2; ring
    have h3 : Real.sqrt (2 * Real.exp (-(cE / 2 * y))) = Real.sqrt 2 * Real.exp (-(cE / 4 * y)) := by
      rw [Real.sqrt_mul (by norm_num), annDt_sqrt_exp]; congr 2; ring
    have h4 : (L : ℝ) ^ (8 : ℝ) = L ^ 8 := by exact_mod_cast Real.rpow_natCast L 8
    rw [h1, h2, h3]
    refine le_trans (le_of_eq ?_) hL
    rw [h4, mul_pow]
    have : Real.exp (-(cE / 8 * y)) = Real.exp (cE / 8 * y) * Real.exp (-(cE / 4 * y)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [this]; ring
  have e4 : ∀ᶠ L : ℝ in atTop, L * (2 * Real.exp (-(cE / 2 * L ^ (α / 6)))) ≤ 1 := by
    filter_upwards [dtExp_pow_exp_le 2 1 (cE / 2) (α / 6) (by positivity) hκ,
      eventually_gt_atTop 0] with L hL hL0
    rw [Real.rpow_one] at hL
    linarith only [hL, show L * (2 * Real.exp (-(cE / 2 * L ^ (α / 6)))) =
      2 * L * Real.exp (-(cE / 2 * L ^ (α / 6))) by ring]
  have e5 : ∀ᶠ L : ℝ in atTop, 2 * B' ≤ L := eventually_ge_atTop _
  have e6 : ∀ᶠ L : ℝ in atTop, arate ≤ Real.exp (cE / (64 * d) * L ^ (α / 6)) := by
    have : Tendsto (fun L : ℝ => cE / (64 * d) * L ^ (α / 6)) atTop atTop :=
      (tendsto_rpow_atTop hκ).const_mul_atTop hc3
    exact (Real.tendsto_exp_atTop.comp this).eventually_ge_atTop _
  have e7 : ∀ᶠ L : ℝ in atTop, L ^ β ≤ Real.exp (cE / (64 * d) * L ^ (α / 6)) := by
    filter_upwards [dtExp_pow_exp_le 1 β (cE / (64 * d)) (α / 6) hc3 hκ, eventually_gt_atTop 0]
      with L hL hL0
    rw [one_mul] at hL
    have := Real.exp_pos (cE / (64 * d) * L ^ (α / 6))
    have h2 : Real.exp (-(cE / (64 * d) * L ^ (α / 6))) = (Real.exp (cE / (64 * d) * L ^ (α / 6)))⁻¹ :=
      Real.exp_neg _
    rw [h2, ← div_eq_mul_inv, div_le_one this] at hL
    exact hL
  obtain ⟨L0, hL0⟩ := eventually_atTop.1 (e1.and (e2.and (e3.and (e4.and (e5.and (e6.and e7))))))
  refine ⟨max 1 L0, le_max_left _ _, fun L hL => ?_⟩
  exact hL0 L ((le_max_right _ _).trans hL)

/-- A stretched-exponential tail at the scale `r`, rewritten at the scale `L = log t`. -/
theorem dtExp_tail_shift {C β r L : ℝ} (hC : 1 ≤ C) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hL : 1 ≤ L)
    (hLr : L / 2 ≤ Real.log r) :
    C * Real.exp (-(C⁻¹ * Real.log r ^ β)) ≤ C * Real.exp (-(C⁻¹ / 2 * L ^ β)) := by
  have hC0 : 0 < C := by linarith only [hC]
  have hL0 : 0 < L := by linarith only [hL]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC0.le
  have h1 : (L / 2) ^ β ≤ Real.log r ^ β := Real.rpow_le_rpow (by positivity) hLr hβ0.le
  have h2 : L ^ β / 2 ≤ (L / 2) ^ β := by
    rw [Real.div_rpow hL0.le (by norm_num)]
    have h3 : (2 : ℝ) ^ β ≤ 2 := by
      calc (2 : ℝ) ^ β ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hβ1
        _ = 2 := Real.rpow_one 2
    have h4 : 0 < (2 : ℝ) ^ β := by positivity
    rw [div_le_div_iff₀ (by norm_num) h4]
    nlinarith only [h3, Real.rpow_pos_of_pos hL0 β]
  have hCi : 0 ≤ C⁻¹ := inv_nonneg.2 hC0.le
  have := mul_le_mul_of_nonneg_left (h2.trans h1) hCi
  nlinarith only [this]

/-- The Gaussian tail of the growth scale at the scale `L`. -/
theorem dtExp_tail_K {B' β L : ℝ} (hB : 0 < B') (hβ : β ≤ 2) (hL : 1 ≤ L) :
    Real.exp (-((L / (2 * B')) ^ 2)) ≤ Real.exp (-(L ^ β / (4 * B' ^ 2))) := by
  refine Real.exp_le_exp.2 ?_
  have h1 : L ^ β ≤ L ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL hβ
  have h2 : L ^ (2 : ℝ) = L ^ 2 := by exact_mod_cast Real.rpow_natCast L 2
  have h3 : (L / (2 * B')) ^ 2 = L ^ 2 / (4 * B' ^ 2) := by
    rw [div_pow]; ring_nf
  rw [h3]
  have : L ^ β / (4 * B' ^ 2) ≤ L ^ 2 / (4 * B' ^ 2) :=
    div_le_div_of_nonneg_right (h1.trans h2.le) (by positivity)
  linarith only [this]

/-- The Gaussian tail of the gradient scale at the scale `L`. -/
theorem dtExp_tail_G {a s β L : ℝ} (ha : 0 < a) (has : a ≤ s) (hs : L ^ β ≤ s) :
    8 * Real.exp (-((s / a) ^ 2)) ≤ 8 * Real.exp (-(L ^ β / a)) := by
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num)
  have h1 : 1 ≤ s / a := by rw [le_div_iff₀ ha]; linarith only [has]
  have h2 : s / a ≤ (s / a) ^ 2 := by nlinarith only [h1]
  have h3 : L ^ β / a ≤ s / a := div_le_div_of_nonneg_right hs ha.le
  linarith only [h2, h3]

end SuperdiffusionCLT.Section8
