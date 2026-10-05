/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import SuperdiffusionCLT.Section4.LNaught.Monotone

/-!
# Numeric folds for the final assembly

Small real-variable inequalities used to put the pieces of the final assembly under a single
amplitude constant.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.NewMixing

open SuperdiffusionCLT.Section4.LNaught

noncomputable section

/-- `ν⁻¹ ≤ ν^{-4}` for `0 < ν ≤ 1`. -/
theorem newMixAsm_inv_le_rpow_neg_four {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1) :
    nu⁻¹ ≤ nu ^ (-(4 : ℝ)) := by
  have h4 : nu ^ (4 : ℕ) ≤ nu := by
    calc nu ^ (4 : ℕ) = nu * nu ^ 3 := by ring
      _ ≤ nu * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hnu.le hnu1) hnu.le
      _ = nu := mul_one nu
  have hpos : 0 < nu ^ (4 : ℕ) := pow_pos hnu 4
  have hrp : nu ^ (-(4 : ℝ)) = (nu ^ (4 : ℕ))⁻¹ := by
    rw [Real.rpow_neg hnu.le]
    norm_cast
  rw [hrp]
  exact inv_anti₀ hpos h4

/-- Doubling the constant of `L₀` at least doubles it. -/
theorem newMixAsm_two_mul_lNaught_le {C M alpha cStar nu K : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hK : 0 ≤ K) (hcStar : 0 < cStar) (hnu : 0 < nu) (hα0 : 0 ≤ alpha) (hα1 : alpha < 1) :
    2 * SuperdiffusionCLT.Frozen.Section4.lNaught C M alpha cStar nu K ≤
      SuperdiffusionCLT.Frozen.Section4.lNaught (2 * C) M alpha cStar nu K := by
  have hI : 0 ≤ lNaughtInner C M alpha cStar nu K := inner_nonneg hC hM hK hcStar hnu hα1
  have hlin : lNaughtInner (2 * C) M alpha cStar nu K = 2 * lNaughtInner C M alpha cStar nu K := by
    unfold lNaughtInner; ring
  have hp1 : (1 : ℝ) ≤ 1 / (1 - alpha) := by
    rw [le_div_iff₀ (sub_pos.mpr hα1)]
    linarith only [hα0]
  unfold SuperdiffusionCLT.Frozen.Section4.lNaught
  show 2 * (lNaughtInner C M alpha cStar nu K) ^ ((1 : ℝ) / (1 - alpha)) ≤
    (lNaughtInner (2 * C) M alpha cStar nu K) ^ ((1 : ℝ) / (1 - alpha))
  rw [hlin, Real.mul_rpow (by norm_num) hI]
  have h2 : (2 : ℝ) ^ (1 : ℝ) ≤ (2 : ℝ) ^ ((1 : ℝ) / (1 - alpha)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hp1
  rw [Real.rpow_one] at h2
  exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hI _)

/-- `L₀` is at most half of `L₀` with doubled constant (and larger `M`). -/
theorem newMixAsm_lNaught_le_half {C C' M M' alpha cStar nu K : ℝ} (hC : 0 ≤ C)
    (hCC' : 2 * C ≤ C') (hM : 0 ≤ M) (hMM' : M ≤ M') (hK : 0 ≤ K) (hcStar : 0 < cStar)
    (hnu : 0 < nu) (hα0 : 0 ≤ alpha) (hα1 : alpha < 1) :
    SuperdiffusionCLT.Frozen.Section4.lNaught C M alpha cStar nu K ≤
      SuperdiffusionCLT.Frozen.Section4.lNaught C' M' alpha cStar nu K / 2 := by
  have h1 := newMixAsm_two_mul_lNaught_le hC hM hK hcStar hnu hα0 hα1
  have h2 := lNaught_mono_both (by linarith only [hC] : (0 : ℝ) ≤ 2 * C) hCC' hM hMM' hK
    hcStar hnu hα1
  linarith only [h1, h2]

end
end SuperdiffusionCLT.Section4.NewMixing
