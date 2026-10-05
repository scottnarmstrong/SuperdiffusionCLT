/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Corollary.LowerRatio
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# `cor.lower.ratio`: scale arithmetic

The residuals `m^{-10}`, `m^{-50}` are absorbed into `shom^{-2}` by the crude bound
`shom ≤ Ce m²` (`e.crude.shom.bnd`), and `log²(ν⁻¹ m) ≤ 4 log² m` from `ν⁻¹ ≤ m`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

/-- `m^{-k} ≤ Ce² shom^{-2}` for `k ≥ 4` and `shom ≤ Ce m²`. -/
theorem lowerRatio_mpow_le {m σ Ce : ℝ} (hm : 1 ≤ m) (hCe : 0 < Ce) (k : ℕ) (hk : 4 ≤ k)
    (hσ : 0 < σ) (hs : σ ≤ Ce * m * m) :
    m ^ (-(k : ℝ)) ≤ Ce ^ 2 * σ ^ (-(2 : ℝ)) := by
  have hm0 : 0 < m := by linarith only [hm]
  have h1 : σ ^ 2 ≤ Ce ^ 2 * m ^ k := by
    have h2 : σ ^ 2 ≤ (Ce * m * m) ^ 2 := pow_le_pow_left₀ hσ.le hs 2
    have h3 : m ^ 4 ≤ m ^ k := pow_le_pow_right₀ hm hk
    have h4 : (Ce * m * m) ^ 2 = Ce ^ 2 * m ^ 4 := by ring
    have h5 : Ce ^ 2 * m ^ 4 ≤ Ce ^ 2 * m ^ k :=
      mul_le_mul_of_nonneg_left h3 (sq_nonneg Ce)
    linarith only [h2, h4, h5]
  rw [Real.rpow_neg hm0.le, Real.rpow_natCast, Real.rpow_neg hσ.le, Real.rpow_two]
  have hmk : 0 < m ^ k := pow_pos hm0 k
  have hσ2 : 0 < σ ^ 2 := pow_pos hσ 2
  have hCe2 : 0 < Ce ^ 2 := pow_pos hCe 2
  have h6 : (Ce ^ 2 * m ^ k)⁻¹ ≤ (σ ^ 2)⁻¹ := inv_anti₀ hσ2 h1
  have h7 : (m ^ k)⁻¹ = Ce ^ 2 * (Ce ^ 2 * m ^ k)⁻¹ := by field_simp
  rw [h7]
  exact mul_le_mul_of_nonneg_left h6 hCe2.le

/-- `log²(ν⁻¹ m) ≤ 4 log² m` when `ν⁻¹ ≤ m`. -/
theorem lowerRatio_log_sq_le {nu m : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hm : 1 ≤ m)
    (hnm : nu⁻¹ ≤ m) :
    Real.log (nu⁻¹ * m) ^ (2 : ℝ) ≤ 4 * Real.log m ^ (2 : ℝ) := by
  have hinv : 1 ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
  have hm0 : 0 < m := by linarith only [hm]
  have h1 : nu⁻¹ * m ≤ m * m := mul_le_mul_of_nonneg_right hnm hm0.le
  have hpos : 0 < nu⁻¹ * m := by positivity
  have h2 : Real.log (nu⁻¹ * m) ≤ 2 * Real.log m := by
    have := Real.log_le_log hpos h1
    rw [Real.log_mul hm0.ne' hm0.ne'] at this
    linarith only [this]
  have h3 : 0 ≤ Real.log (nu⁻¹ * m) := Real.log_nonneg (by nlinarith only [hinv, hm])
  rw [Real.rpow_two, Real.rpow_two]
  nlinarith only [h2, h3]

/-- `1 ≤ log m` for `m ≥ 3`. -/
theorem lowerRatio_one_le_log {m : ℝ} (hm : 3 ≤ m) : 1 ≤ Real.log m := by
  have := Real.exp_one_lt_d9
  rw [Real.le_log_iff_exp_le (by linarith only [hm])]
  linarith only [this, hm]

end SuperdiffusionCLT.Section5
