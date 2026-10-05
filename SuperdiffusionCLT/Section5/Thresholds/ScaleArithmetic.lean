/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Thresholds.SequencePasses

/-!
# Scale arithmetic for `e.ass.valid.applied`

Pure real-variable facts for the scales `L = m - h`, `n = ⌊m - h - 100 log₃(ν⁻¹ m)⌋`, `Q = log(ν⁻¹ m)`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

theorem log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have := Real.log_le_rpow_div hx.le (show (0 : ℝ) < 1 / 2 by norm_num)
  rw [← Real.sqrt_eq_rpow] at this
  linarith only [this]

theorem four_le_log_of_large {m : ℝ} (hm : 55 ≤ m) : 4 ≤ Real.log m := by
  rw [Real.le_log_iff_exp_le (by linarith only [hm])]
  have h1 := Real.exp_one_lt_d9
  have h4 : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h4]
  have h0 : 0 < Real.exp 1 := Real.exp_pos 1
  have : Real.exp 1 ^ 4 ≤ 2.7182818286 ^ 4 := pow_le_pow_left₀ h0.le h1.le 4
  nlinarith only [this, hm]

/-- `n ≥ m/2` ("we may further assume `n ≥ m/2`"). -/
theorem scale_half {m h n Q : ℝ} (hm : 1000000 ≤ m) (hh : 400 * h ≤ m)
    (hQ : Q ≤ 2 * Real.log m) (hQ0 : 0 ≤ Q)
    (hn : m - h - 100 * (Q / Real.log 3) < n + 1) : m ≤ 2 * n := by
  have hl3 : 1 < Real.log 3 := one_lt_log_three
  have h1 : Q / Real.log 3 ≤ Q := div_le_self hQ0 hl3.le
  have hm0 : 0 < m := by linarith only [hm]
  have hlog := log_le_two_sqrt hm0
  set s := Real.sqrt m with hs
  have hss : s * s = m := Real.mul_self_sqrt hm0.le
  have hs1 : 1000 ≤ s := by
    by_contra hcon
    push Not at hcon
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    nlinarith only [hcon, hss, hm, hs0]
  nlinarith only [hn, h1, hQ, hlog, hh, hss, hs1]

/-- The scale conditions of `p.homog.below` at `(L, m, α, M) = (m - h, n, 3/4, 401)`, and the size of
`L - n`. -/
theorem scale_cond {m h n Q D : ℝ} (hm : 1000000 ≤ m) (hh : 400 * h ≤ m) (hh1 : 1 ≤ h)
    (hQ1 : Real.log m ≤ Q) (hQ : Q ≤ 2 * Real.log m) (hD : 0 ≤ D)
    (hn : m - h - 100 * (Q / Real.log 3) < n + 1) :
    (m - h) - 401 * (m - h) ^ (3 / 4 : ℝ) * Real.log (m - h) ^ (3 : ℝ) ≤ n ∧
      (m - h) - n + D * Real.log (m - h) ^ (2 : ℝ) ≤ (101 + D) * Q ^ (2 : ℝ) := by
  have hl3 : 1 < Real.log 3 := one_lt_log_three
  have hm0 : 0 < m := by linarith only [hm]
  have hlogm : 1 ≤ Real.log m := by linarith only [four_le_log_of_large (by linarith only [hm])]
  have hQ0 : 0 ≤ Q := by linarith only [hQ1, hlogm]
  have h1 : Q / Real.log 3 ≤ Q := div_le_self hQ0 hl3.le
  have hL3 : 3 ≤ m - h := by linarith only [hm, hh, hh1]
  have hL0 : 0 < m - h := by linarith only [hL3]
  have hLm : m - h ≤ m := by linarith only [hh1]
  have hmL : m ≤ 2 * (m - h) := by linarith only [hh, hh1, hm]
  have hlogL1 : 1 ≤ Real.log (m - h) := by
    have := Real.log_le_log (by norm_num) hL3
    linarith only [this, hl3]
  have hlogm2 : Real.log m ≤ 2 * Real.log (m - h) := by
    have h2 : Real.log m ≤ Real.log (2 * (m - h)) := Real.log_le_log hm0 hmL
    rw [Real.log_mul (by norm_num) hL0.ne'] at h2
    have : Real.log 2 ≤ Real.log (m - h) := Real.log_le_log (by norm_num) (by linarith only [hL3])
    linarith only [h2, this]
  have hLp : 1 ≤ (m - h) ^ (3 / 4 : ℝ) := Real.one_le_rpow (by linarith only [hL3]) (by norm_num)
  have hlog3 : Real.log (m - h) ^ (3 : ℝ) = Real.log (m - h) ^ 3 := by
    rw [← Real.rpow_natCast]; norm_num
  have hlog2 : Real.log (m - h) ^ (2 : ℝ) = Real.log (m - h) ^ 2 := Real.rpow_two _
  have hcube : Real.log (m - h) ≤ Real.log (m - h) ^ 3 := by
    nlinarith only [hlogL1, mul_nonneg (by linarith only [hlogL1] : (0 : ℝ) ≤ Real.log (m - h)) (by linarith only [hlogL1] : (0 : ℝ) ≤ Real.log (m - h) - 1)]
  have hbig : Real.log (m - h) ≤ (m - h) ^ (3 / 4 : ℝ) * Real.log (m - h) ^ 3 := by
    nlinarith only [hLp, hcube, hlogL1]
  constructor
  · rw [hlog3]
    nlinarith only [hn, h1, hQ, hlogm2, hbig, hlogL1]
  · rw [hlog2, Real.rpow_two]
    have hlogLQ : Real.log (m - h) ≤ Q := le_trans (Real.log_le_log hL0 hLm) hQ1
    have hlogL0 : 0 ≤ Real.log (m - h) := by linarith only [hlogL1]
    have hQ2 : Real.log (m - h) ^ 2 ≤ Q ^ 2 := pow_le_pow_left₀ hlogL0 hlogLQ 2
    have hQ1' : 1 ≤ Q := by linarith only [hQ1, hlogm]
    have hQQ : Q ≤ Q ^ 2 := by nlinarith only [hQ1']
    nlinarith only [hn, h1, hQ2, hQQ, hD, hQ1', mul_le_mul_of_nonneg_left hQ2 hD]

/-- The final comparison of `e.ass.valid.applied`: `σ⁻² Q² ≤ m^{-3/4}`. -/
theorem sigma_inv_sq_mul_le {m σ Q : ℝ} (hm : 55 ≤ m) (hQ : Q ≤ 2 * Real.log m) (hQ0 : 0 ≤ Q)
    (hσ : m ^ (3 / 8 : ℝ) * Real.log m ^ (3 / 2 : ℝ) ≤ σ) :
    σ ^ (-(2 : ℝ)) * Q ^ (2 : ℝ) ≤ m ^ (-(3 / 4 : ℝ)) := by
  have hm0 : 0 < m := by linarith only [hm]
  have hl4 := four_le_log_of_large hm
  have hlog0 : 0 < Real.log m := by linarith only [hl4]
  have hT0 : 0 < m ^ (3 / 8 : ℝ) * Real.log m ^ (3 / 2 : ℝ) := by positivity
  have hT2 : (m ^ (3 / 8 : ℝ) * Real.log m ^ (3 / 2 : ℝ)) ^ 2 = m ^ (3 / 4 : ℝ) * Real.log m ^ 3 := by
    have a1 : (m ^ (3 / 8 : ℝ)) ^ 2 = m ^ (3 / 4 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hm0.le]; norm_num
    have a2 : (Real.log m ^ (3 / 2 : ℝ)) ^ 2 = Real.log m ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hlog0.le, ← Real.rpow_natCast]; norm_num
    rw [mul_pow, a1, a2]
  have hσ0 : 0 < σ := lt_of_lt_of_le hT0 hσ
  have hσ2 : m ^ (3 / 4 : ℝ) * Real.log m ^ 3 ≤ σ ^ 2 := by
    rw [← hT2]; exact pow_le_pow_left₀ hT0.le hσ 2
  have hmp : 0 < m ^ (3 / 4 : ℝ) := by positivity
  have hu3 : 0 < Real.log m ^ 3 := by positivity
  have hQ2' : Q ^ 2 ≤ (2 * Real.log m) ^ 2 := pow_le_pow_left₀ hQ0 hQ 2
  have hQ2 : Q ^ 2 ≤ Real.log m ^ 3 := by
    nlinarith only [hQ2', hl4, mul_nonneg (sq_nonneg (Real.log m)) (by linarith only [hl4] : (0 : ℝ) ≤ Real.log m - 4)]
  have e1 : σ ^ (-(2 : ℝ)) = (σ ^ 2)⁻¹ := by
    rw [show (-(2 : ℝ)) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hσ0.le, Real.rpow_natCast]
  rw [e1, Real.rpow_two, Real.rpow_neg hm0.le]
  have h1 : (σ ^ 2)⁻¹ ≤ (m ^ (3 / 4 : ℝ) * Real.log m ^ 3)⁻¹ := inv_anti₀ (by positivity) hσ2
  calc (σ ^ 2)⁻¹ * Q ^ 2 ≤ (m ^ (3 / 4 : ℝ) * Real.log m ^ 3)⁻¹ * Real.log m ^ 3 :=
        mul_le_mul h1 hQ2 (by positivity) (by positivity)
    _ = (m ^ (3 / 4 : ℝ))⁻¹ := by field_simp

end SuperdiffusionCLT.Section5
