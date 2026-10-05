/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
The elementary growth-rate fact
needed for the Step 3 scale arithmetic in the proof of `p.homog.below`: `C₁·log²L`
(the size of `10m₀+⌈Cmix·log L⌉`, up to constants) is dominated by `M·L^α·log³L` (the
headroom `m - m₃` gives, per the "`M` replaced by `2M`" move) once `L ≥ e^{C₁}`.
Elementary: `log L ≥ C₁` gives `log³L =
log L · log²L ≥ C₁·log²L`, and `M·L^α ≥ 1` (since `M≥1`, `L^α≥1` for `α≥0`,
`L≥1`) only helps. -/

@[expose] public section

namespace SuperdiffusionCLT.Section4.HomogBelow

/-- **`C₁·log²L ≤ M·L^α·log³L` once `L ≥ e^{C₁}`.** -/
theorem homogBelow_logSq_le_rpow_logCube
    {C1 M alpha : ℝ} (hC1 : 0 ≤ C1) (hM : 1 ≤ M) (halpha : 0 ≤ alpha)
    {L : ℕ} (hL : Real.exp C1 ≤ (L : ℝ)) :
    C1 * Real.log (L : ℝ) ^ 2 ≤ M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ 3 := by
  have hexp0 : Real.exp (0 : ℝ) ≤ Real.exp C1 := Real.exp_le_exp.mpr hC1
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by
    rw [Real.exp_zero] at hexp0
    linarith only [hexp0, hL]
  have hlogL_ge : C1 ≤ Real.log (L : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos C1) hL
    rwa [Real.log_exp] at h
  have hlogL_nonneg : 0 ≤ Real.log (L : ℝ) := le_trans hC1 hlogL_ge
  have hlogSq_nonneg : 0 ≤ Real.log (L : ℝ) ^ 2 := sq_nonneg _
  have hcube : C1 * Real.log (L : ℝ) ^ 2 ≤ Real.log (L : ℝ) ^ 3 := by
    have heq : Real.log (L : ℝ) ^ 3 = Real.log (L : ℝ) * Real.log (L : ℝ) ^ 2 := by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right hlogL_ge hlogSq_nonneg
  have hLrpow_ge1 : (1 : ℝ) ≤ (L : ℝ) ^ alpha := Real.one_le_rpow hL1 halpha
  have hMLalpha_ge1 : (1 : ℝ) ≤ M * (L : ℝ) ^ alpha := by
    calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
      _ ≤ M * (L : ℝ) ^ alpha := mul_le_mul hM hLrpow_ge1 zero_le_one (by linarith only [hM])
  have hlogCube_nonneg : 0 ≤ Real.log (L : ℝ) ^ 3 := pow_nonneg hlogL_nonneg 3
  have hfinal : Real.log (L : ℝ) ^ 3 ≤ M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ 3 := by
    calc Real.log (L : ℝ) ^ 3 = 1 * Real.log (L : ℝ) ^ 3 := (one_mul _).symm
      _ ≤ M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_right hMLalpha_ge1 hlogCube_nonneg
  linarith only [hcube, hfinal]

end SuperdiffusionCLT.Section4.HomogBelow
