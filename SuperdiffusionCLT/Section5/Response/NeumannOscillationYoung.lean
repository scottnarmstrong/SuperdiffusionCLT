/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Elementary inequalities for the moment bounds of `e.crude.Fz.bound`

Young-type inequalities in `ℝ≥0∞` that replace Hölder in the sample variable: they are used with
a *constant* weight, so they need no measurability of the quantity being integrated (the lower
integral is additive against a constant).

* `le_add_mul_sq`: `x ≤ b/2 + x²/(2b)`, hence `∫ f⁴ ≤ (∫ f⁸)^{1/2}` on a probability space
  (`lintegral_pow_four_le`).
* `pow_four_le_amgm`: `a⁴ ≤ (2t/3) a² + a⁸/(3t²)`, the interpolation of `L⁴` between `L²`, `L⁸`.
* `add_pow_four_le`, `add_pow_eight_le`: convexity of the fourth and eighth powers.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open MeasureTheory
open scoped ENNReal NNReal

section

/-- `x ≤ b/2 + x²/(2b)` for `b > 0`. -/
theorem le_add_mul_sq (x : ℝ≥0∞) {b : ℝ} (hb : 0 < b) :
    x ≤ ENNReal.ofReal (b / 2) + ENNReal.ofReal (1 / (2 * b)) * x ^ 2 := by
  by_cases hx : x = ∞
  · rw [hx]
    have h0 : (0 : ℝ≥0∞) < ENNReal.ofReal (1 / (2 * b)) := ENNReal.ofReal_pos.2 (by positivity)
    rw [ENNReal.top_pow (by norm_num), ENNReal.mul_top h0.ne', add_top]
  · lift x to ℝ≥0 using hx
    have hxr : (x : ℝ≥0∞) = ENNReal.ofReal (x : ℝ) := (ENNReal.ofReal_coe_nnreal).symm
    rw [hxr, ← ENNReal.ofReal_pow (NNReal.coe_nonneg x), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hxn : (0 : ℝ) ≤ x := NNReal.coe_nonneg x
    have h2 : b / 2 + 1 / (2 * b) * (x : ℝ) ^ 2 - x = (b - x) ^ 2 / (2 * b) := by
      field_simp
      ring
    have h3 : 0 ≤ (b - x) ^ 2 / (2 * b) := div_nonneg (sq_nonneg _) (by positivity)
    linarith only [h2, h3]

/-- On a probability space, `∫ f⁴ ≤ B⁴` once `∫ f⁸ ≤ B⁸`, with no measurability of `f`. -/
theorem lintegral_pow_four_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (f : Ω → ℝ≥0∞) {B : ℝ} (hB : 0 < B)
    (h : ∫⁻ ω, f ω ^ 8 ∂μ ≤ ENNReal.ofReal (B ^ 8)) :
    ∫⁻ ω, f ω ^ 4 ∂μ ≤ ENNReal.ofReal (B ^ 4) := by
  have hb : 0 < B ^ 4 := by positivity
  have hpt : ∀ ω, f ω ^ 4 ≤ ENNReal.ofReal (B ^ 4 / 2) +
      ENNReal.ofReal (1 / (2 * B ^ 4)) * f ω ^ 8 := fun ω => by
    refine (le_add_mul_sq (f ω ^ 4) hb).trans (le_of_eq ?_)
    rw [← pow_mul]
  calc ∫⁻ ω, f ω ^ 4 ∂μ
      ≤ ∫⁻ ω, (ENNReal.ofReal (B ^ 4 / 2) +
          ENNReal.ofReal (1 / (2 * B ^ 4)) * f ω ^ 8) ∂μ := lintegral_mono hpt
    _ = ENNReal.ofReal (B ^ 4 / 2) + ENNReal.ofReal (1 / (2 * B ^ 4)) *
          ∫⁻ ω, f ω ^ 8 ∂μ := by
        rw [lintegral_add_left measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        simp
    _ ≤ ENNReal.ofReal (B ^ 4 / 2) + ENNReal.ofReal (1 / (2 * B ^ 4)) *
          ENNReal.ofReal (B ^ 8) := by gcongr
    _ = ENNReal.ofReal (B ^ 4) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
        congr 1
        field_simp
        ring

/-- Weighted AM-GM: `a⁴ ≤ (2t/3) a² + a⁸/(3t²)` for every `t > 0`. -/
theorem pow_four_le_amgm (a : ℝ≥0∞) {t : ℝ} (ht : 0 < t) :
    a ^ 4 ≤ ENNReal.ofReal (2 * t / 3) * a ^ 2 + ENNReal.ofReal (1 / (3 * t ^ 2)) * a ^ 8 := by
  by_cases ha : a = ∞
  · rw [ha]
    have h0 : (0 : ℝ≥0∞) < ENNReal.ofReal (1 / (3 * t ^ 2)) := ENNReal.ofReal_pos.2 (by positivity)
    rw [ENNReal.top_pow (by norm_num), ENNReal.top_pow (by norm_num), ENNReal.top_pow (by norm_num),
      ENNReal.mul_top h0.ne', add_top]
  · lift a to ℝ≥0 using ha
    have har : (a : ℝ≥0∞) = ENNReal.ofReal (a : ℝ) := (ENNReal.ofReal_coe_nnreal).symm
    have han : (0 : ℝ) ≤ a := NNReal.coe_nonneg a
    rw [har, ← ENNReal.ofReal_pow han, ← ENNReal.ofReal_pow han, ← ENNReal.ofReal_pow han,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h2 : 2 * t / 3 * (a : ℝ) ^ 2 + 1 / (3 * t ^ 2) * (a : ℝ) ^ 8 - (a : ℝ) ^ 4 =
        (a : ℝ) ^ 2 * ((a : ℝ) ^ 2 - t) ^ 2 * ((a : ℝ) ^ 2 + 2 * t) / (3 * t ^ 2) := by
      field_simp
      ring
    have h3 : 0 ≤ (a : ℝ) ^ 2 * ((a : ℝ) ^ 2 - t) ^ 2 * ((a : ℝ) ^ 2 + 2 * t) / (3 * t ^ 2) := by
      positivity
    linarith only [h2, h3]

/-- Convexity of the fourth power. -/
theorem add_pow_four_le (a b : ℝ≥0∞) : (a + b) ^ 4 ≤ 8 * (a ^ 4 + b ^ 4) := by
  have h := ENNReal.rpow_add_le_mul_rpow_add_rpow a b (p := 4) (by norm_num)
  have e1 : ∀ x : ℝ≥0∞, x ^ (4 : ℝ) = x ^ (4 : ℕ) := fun x => by
    exact_mod_cast ENNReal.rpow_natCast x 4
  have e2 : (2 : ℝ≥0∞) ^ ((4 : ℝ) - 1) = 8 := by
    rw [show ((4 : ℝ) - 1) = ((3 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
    norm_num
  rw [e1, e1, e1, e2] at h
  exact h

/-- Convexity of the fourth power, three summands. -/
theorem add_add_pow_four_le (a b c : ℝ≥0∞) : (a + b + c) ^ 4 ≤ 64 * (a ^ 4 + b ^ 4 + c ^ 4) := by
  calc (a + b + c) ^ 4 ≤ 8 * ((a + b) ^ 4 + c ^ 4) := add_pow_four_le _ _
    _ ≤ 8 * (8 * (a ^ 4 + b ^ 4) + c ^ 4) := by gcongr; exact add_pow_four_le _ _
    _ ≤ 64 * (a ^ 4 + b ^ 4 + c ^ 4) := by
        have : 8 * (8 * (a ^ 4 + b ^ 4) + c ^ 4) = 64 * (a ^ 4 + b ^ 4) + 8 * c ^ 4 := by ring
        rw [this]
        have h8 : (8 : ℝ≥0∞) * c ^ 4 ≤ 64 * c ^ 4 := by gcongr; norm_num
        calc 64 * (a ^ 4 + b ^ 4) + 8 * c ^ 4 ≤ 64 * (a ^ 4 + b ^ 4) + 64 * c ^ 4 := by gcongr
          _ = 64 * (a ^ 4 + b ^ 4 + c ^ 4) := by ring

/-- Convexity of the eighth power. -/
theorem add_pow_eight_le (a b : ℝ≥0∞) : (a + b) ^ 8 ≤ 128 * (a ^ 8 + b ^ 8) := by
  have h := ENNReal.rpow_add_le_mul_rpow_add_rpow a b (p := 8) (by norm_num)
  have e1 : ∀ x : ℝ≥0∞, x ^ (8 : ℝ) = x ^ (8 : ℕ) := fun x => by
    exact_mod_cast ENNReal.rpow_natCast x 8
  have e2 : (2 : ℝ≥0∞) ^ ((8 : ℝ) - 1) = 128 := by
    rw [show ((8 : ℝ) - 1) = ((7 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
    norm_num
  rw [e1, e1, e1, e2] at h
  exact h

/-- The lower integral of a finite sum dominates the sum of the lower integrals. -/
theorem osc_sum_lintegral_le_lintegral_sum {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (s : Finset ι) (f : ι → Ω → ℝ≥0∞) :
    ∑ i ∈ s, ∫⁻ ω, f i ω ∂μ ≤ ∫⁻ ω, ∑ i ∈ s, f i ω ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t hat ih =>
      rw [Finset.sum_insert hat]
      simp only [Finset.sum_insert hat]
      exact (add_le_add le_rfl ih).trans (le_lintegral_add _ _)


/-- From `X^{1/8} ≤ B` to `X ≤ B⁸`. -/
theorem le_ofReal_pow_eight_of_rpow_le {X : ℝ≥0∞} {B : ℝ} (hB : 0 ≤ B)
    (h : X ^ ((1 : ℝ) / 8) ≤ ENNReal.ofReal B) : X ≤ ENNReal.ofReal (B ^ 8) := by
  have h1 := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 8)
  rw [← ENNReal.rpow_mul, show (1 : ℝ) / 8 * 8 = 1 by norm_num, ENNReal.rpow_one] at h1
  refine h1.trans (le_of_eq ?_)
  rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast, ENNReal.ofReal_pow hB]

/-- `∫ (c Z)⁴ ≤ (c B)⁴` once `∫ Z⁸ ≤ B⁸`, with no measurability of `Z`. -/
theorem lintegral_const_mul_pow_four_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (Z : Ω → ℝ≥0∞) {c B : ℝ} (hc : 0 < c) (hB : 0 < B)
    (h : ∫⁻ ω, Z ω ^ 8 ∂μ ≤ ENNReal.ofReal (B ^ 8)) :
    ∫⁻ ω, (ENNReal.ofReal c * Z ω) ^ 4 ∂μ ≤ ENNReal.ofReal ((c * B) ^ 4) := by
  refine lintegral_pow_four_le (fun ω => ENNReal.ofReal c * Z ω) (mul_pos hc hB) ?_
  have e1 : ∀ ω, (ENNReal.ofReal c * Z ω) ^ 8 = ENNReal.ofReal c ^ 8 * Z ω ^ 8 :=
    fun ω => mul_pow _ _ _
  simp_rw [e1]
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
  calc ENNReal.ofReal c ^ 8 * ∫⁻ ω, Z ω ^ 8 ∂μ
      ≤ ENNReal.ofReal c ^ 8 * ENNReal.ofReal (B ^ 8) := by gcongr
    _ = ENNReal.ofReal (c ^ 8 * B ^ 8) := by
        rw [← ENNReal.ofReal_pow hc.le, ← ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal ((c * B) ^ 8) := by rw [mul_pow]

end

end SuperdiffusionCLT.Section5
