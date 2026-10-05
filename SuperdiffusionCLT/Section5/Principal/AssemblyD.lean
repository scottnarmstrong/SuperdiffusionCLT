/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Principal.AssemblyC

/-!
# Constant bookkeeping for the principal-term assembly

The real arithmetic that absorbs `(1 + shom⁻¹ h^{1/2})^8 ≤ 256 m` (from `shom ≥ m^{3/8}`, `h ≤ m`) and
the constants of the Young step into `C m^{-10}`; and the conversions between the `ℝ≥0∞` average
`subcubeAvg` and real averages.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open MeasureTheory Homogenization
open scoped ENNReal

variable {d : ℕ}

theorem pa_one_add_pow_eight_le {w : ℝ} (hw : 0 ≤ w) : (1 + w) ^ 8 ≤ 128 * (1 + w ^ 8) := by
  have h2 : (1 + w) ^ 2 ≤ 2 * (1 + w ^ 2) := by nlinarith only [sq_nonneg (1 - w)]
  have h4 : (1 + w) ^ 4 ≤ 8 * (1 + w ^ 4) := by
    have h0 : 0 ≤ (1 + w) ^ 2 := sq_nonneg _
    calc (1 + w) ^ 4 = ((1 + w) ^ 2) ^ 2 := by ring
      _ ≤ (2 * (1 + w ^ 2)) ^ 2 := pow_le_pow_left₀ h0 h2 2
      _ = 4 * (1 + w ^ 2) ^ 2 := by ring
      _ ≤ 4 * (2 * (1 + (w ^ 2) ^ 2)) := by
          exact mul_le_mul_of_nonneg_left (by nlinarith only [sq_nonneg (1 - w ^ 2)]) (by norm_num)
      _ = 8 * (1 + w ^ 4) := by ring
  have h0 : 0 ≤ (1 + w) ^ 4 := by positivity
  calc (1 + w) ^ 8 = ((1 + w) ^ 4) ^ 2 := by ring
    _ ≤ (8 * (1 + w ^ 4)) ^ 2 := pow_le_pow_left₀ h0 h4 2
    _ = 64 * (1 + w ^ 4) ^ 2 := by ring
    _ ≤ 64 * (2 * (1 + (w ^ 4) ^ 2)) :=
        mul_le_mul_of_nonneg_left (by nlinarith only [sq_nonneg (1 - w ^ 4)]) (by norm_num)
    _ = 128 * (1 + w ^ 8) := by ring

/-- `(1 + σ⁻¹ h^{1/2})^8 ≤ 256 m` when `σ^8 ≥ m^3` and `h ≤ m`. -/
theorem pa_U_pow8 {σ m h : ℝ} (hσ : 0 < σ) (hm : 1 ≤ m) (hh0 : 0 ≤ h) (hhm : h ≤ m)
    (hσ8 : m ^ 3 ≤ σ ^ 8) :
    (1 + σ⁻¹ * h ^ ((1 : ℝ) / 2)) ^ 8 ≤ 256 * m := by
  have hm0 : 0 < m := by linarith only [hm]
  have hw0 : 0 ≤ σ⁻¹ * h ^ ((1 : ℝ) / 2) := by positivity
  have hh8 : (h ^ ((1 : ℝ) / 2)) ^ 8 = h ^ 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hh0, ← Real.rpow_natCast]; norm_num
  have hw8 : (σ⁻¹ * h ^ ((1 : ℝ) / 2)) ^ 8 ≤ m := by
    rw [mul_pow, hh8, inv_pow]
    have h3 : (σ ^ 8)⁻¹ ≤ (m ^ 3)⁻¹ := inv_anti₀ (by positivity) hσ8
    calc (σ ^ 8)⁻¹ * h ^ 4 ≤ (m ^ 3)⁻¹ * h ^ 4 :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ ≤ (m ^ 3)⁻¹ * m ^ 4 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hh0 hhm 4) (by positivity)
      _ = m := by field_simp
  have := pa_one_add_pow_eight_le hw0
  linarith only [this, hw8, hm]

/-- The final constant `(1 + ε)(M³ F + 1/(16 M) + B/(2 M)) ≤ K m^{-10}`. -/
theorem pa_final_real {m σ h Cu C4 ε C0 : ℝ} (hm : 1000000 ≤ m) (hhm : h ≤ m) (hh0 : 0 ≤ h)
    (hσ : 0 < σ) (hσ8 : m ^ 3 ≤ σ ^ 8) (hC4 : 0 ≤ C4) (hε : 0 ≤ ε) (hεC : ε ≤ C0) :
    (1 + ε) * (((m : ℝ) ^ 100) ^ 3 * (C4 * m ^ (-(100 : ℝ))) ^ 4 + 1 / (16 * (m : ℝ) ^ 100) +
        (2 * (Cu * (1 + σ⁻¹ * h ^ ((1 : ℝ) / 2))) ^ 2) ^ 4 / (2 * (m : ℝ) ^ 100)) ≤
      (1 + C0) * (C4 ^ 4 + 1 + 2048 * Cu ^ 8) * m ^ (-(10 : ℝ)) := by
  have hm1 : 1 ≤ m := by linarith only [hm]
  have hm0 : 0 < m := by linarith only [hm]
  set M : ℝ := m ^ 100 with hM
  have hM0 : 0 < M := by positivity
  have hpow : m ^ (-(100 : ℝ)) = M⁻¹ := by
    rw [Real.rpow_neg hm0.le, hM, ← Real.rpow_natCast]; norm_num
  have hpow10 : m ^ (-(10 : ℝ)) = (m ^ 10)⁻¹ := by
    rw [Real.rpow_neg hm0.le, ← Real.rpow_natCast]; norm_num
  have hU := pa_U_pow8 hσ hm1 hh0 hhm hσ8
  set w : ℝ := σ⁻¹ * h ^ ((1 : ℝ) / 2) with hw
  have hB : (2 * (Cu * (1 + w)) ^ 2) ^ 4 ≤ 4096 * Cu ^ 8 * m := by
    have e : (2 * (Cu * (1 + w)) ^ 2) ^ 4 = 16 * Cu ^ 8 * (1 + w) ^ 8 := by ring
    rw [e]
    calc 16 * Cu ^ 8 * (1 + w) ^ 8 ≤ 16 * Cu ^ 8 * (256 * m) :=
          mul_le_mul_of_nonneg_left hU (by positivity)
      _ = 4096 * Cu ^ 8 * m := by ring
  have hE : ((M) ^ 3 * (C4 * M⁻¹) ^ 4 + 1 / (16 * M) +
      (2 * (Cu * (1 + w)) ^ 2) ^ 4 / (2 * M)) ≤ (C4 ^ 4 + 1 + 2048 * Cu ^ 8) * m / M := by
    have e1 : M ^ 3 * (C4 * M⁻¹) ^ 4 = C4 ^ 4 / M := by field_simp
    have e2 : 1 / (16 * M) ≤ 1 / M := by
      apply one_div_le_one_div_of_le hM0; linarith only [hM0]
    have e3 : (2 * (Cu * (1 + w)) ^ 2) ^ 4 / (2 * M) ≤ 2048 * Cu ^ 8 * m / M := by
      rw [div_le_div_iff₀ (by positivity) hM0]
      have := mul_le_mul_of_nonneg_right hB hM0.le
      nlinarith only [this, hM0, mul_nonneg (by positivity : (0 : ℝ) ≤ Cu ^ 8) hM0.le]
    have e4 : (C4 ^ 4 + 1 + 2048 * Cu ^ 8) * m / M =
        C4 ^ 4 * m / M + m / M + 2048 * Cu ^ 8 * m / M := by ring
    have e5 : C4 ^ 4 / M ≤ C4 ^ 4 * m / M := by
      apply div_le_div_of_nonneg_right _ hM0.le
      nlinarith only [hm1, pow_nonneg hC4 4]
    have e6 : 1 / M ≤ m / M := by
      apply div_le_div_of_nonneg_right _ hM0.le
      linarith only [hm1]
    rw [e1, e4]
    linarith only [e2, e3, e5, e6]
  have hmM : m / M ≤ (m ^ 10)⁻¹ := by
    rw [hM, div_le_iff₀ (by positivity)]
    have : m * m ^ 10 = m ^ 11 := by ring
    have h1 : (m ^ 10)⁻¹ * m ^ 100 = m ^ 90 := by field_simp
    rw [h1]
    calc m = m ^ 1 := (pow_one m).symm
      _ ≤ m ^ 90 := pow_le_pow_right₀ hm1 (by norm_num)
  rw [hpow, hpow10]
  have hK : 0 ≤ C4 ^ 4 + 1 + 2048 * Cu ^ 8 := by positivity
  calc (1 + ε) * (M ^ 3 * (C4 * M⁻¹) ^ 4 + 1 / (16 * M) +
        (2 * (Cu * (1 + w)) ^ 2) ^ 4 / (2 * M))
      ≤ (1 + C0) * ((C4 ^ 4 + 1 + 2048 * Cu ^ 8) * m / M) :=
        mul_le_mul (by linarith only [hεC]) hE (by positivity) (by linarith only [hε, hεC])
    _ ≤ (1 + C0) * ((C4 ^ 4 + 1 + 2048 * Cu ^ 8) * (m ^ 10)⁻¹) := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith only [hε, hεC])
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_left hmM hK
    _ = _ := by ring

/-! ## `subcubeAvg` conversions -/

theorem pa_card_pos {Kc n : ℕ} (hn : n ≤ Kc) :
    0 < ((descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ)).card : ℝ) := by
  have hk : (n : ℤ) ≤ (originCube d (Kc : ℤ)).scale := by
    show (n : ℤ) ≤ (Kc : ℤ)
    exact_mod_cast hn
  exact_mod_cast Finset.card_pos.2 (descendantsAtScale_nonempty _ hk)

theorem pa_subcubeAvg_ofReal {Kc n : ℕ} (hn : n ≤ Kc) {r : TriadicCube d → ℝ}
    (hr : ∀ Q, 0 ≤ r Q) :
    subcubeAvg Kc n (fun Q => ENNReal.ofReal (r Q)) =
      ENNReal.ofReal (((descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ)).card : ℝ)⁻¹ *
        ∑ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ), r Q) := by
  have hc := pa_card_pos (d := d) hn
  unfold subcubeAvg
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr hc.le), ENNReal.ofReal_sum_of_nonneg (fun Q _ => hr Q),
    ENNReal.ofReal_inv_of_pos hc, ENNReal.ofReal_natCast]

theorem pa_le_card_mul_subcubeAvg {Kc n : ℕ} (hn : n ≤ Kc) {f : TriadicCube d → ℝ≥0∞}
    {Q : TriadicCube d} (hQ : Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ)) :
    f Q ≤ ((descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ)).card : ℝ≥0∞) *
      subcubeAvg Kc n f := by
  have hc := pa_card_pos (d := d) hn
  have hne : ((descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ)).card : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast hc.ne'
  unfold subcubeAvg
  rw [← mul_assoc, ENNReal.mul_inv_cancel hne (ENNReal.natCast_ne_top _), one_mul]
  exact Finset.single_le_sum (f := f) (fun _ _ => bot_le) hQ

theorem pa_subcubeAvg_ne_top_of_le {Kc n : ℕ} (hn : n ≤ Kc) {f : TriadicCube d → ℝ≥0∞} {B : ℝ}
    (hf : subcubeAvg Kc n f ≤ ENNReal.ofReal B) {Q : TriadicCube d}
    (hQ : Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ)) : f Q ≠ ⊤ := by
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hf)) (pa_le_card_mul_subcubeAvg hn hQ)

/-- From `x^{1/4} ≤ ofReal y` get `x ≤ ofReal (y^4)`. -/
theorem pa_le_of_rpow_quarter {x : ℝ≥0∞} {y : ℝ} (hy : 0 ≤ y)
    (h : x ^ ((1 : ℝ) / 4) ≤ ENNReal.ofReal y) : x ≤ ENNReal.ofReal (y ^ 4) := by
  have h4 := ENNReal.rpow_le_rpow h (show (0 : ℝ) ≤ 4 by norm_num)
  rw [← ENNReal.rpow_mul, show (1 : ℝ) / 4 * 4 = 1 by norm_num, ENNReal.rpow_one] at h4
  rw [ENNReal.ofReal_pow hy]
  simpa using h4

end SuperdiffusionCLT.Section5
