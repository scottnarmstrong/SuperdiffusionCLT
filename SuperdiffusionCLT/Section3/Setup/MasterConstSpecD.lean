/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.ScaleAssembly
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# A common large-cutoff threshold for the three root numeric conditions

The three displays are the numeric premises of
the root theorem of Section 3, immediately after
`CM * Real.sqrt c0 ≤ 1 / 8`. They support the absorptions in the proof of the
master inequality and the Bell comparison.

Unlike a witness at one choice of the parameters, the final theorem applies
to any fixed `CM`, `CB`, `Knd`, and `K`, with positive `nu`, `cStar`, `Cenv`,
and `c0`. The resulting threshold may depend on all these parameters.
It does not assert the uniform dimension-only threshold of the root theorem.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Setup
open scoped Topology

/-- Every fixed power of the scaled logarithm is negligible compared with the scale. -/
theorem masterConstSpecD_log_pow_div_tendsto {nu : ℝ} (hnu : 0 < nu) (n : ℕ) :
    Filter.Tendsto (fun x : ℝ => Real.log (nu⁻¹ * x) ^ n / x)
      Filter.atTop (nhds 0) := by
  have hbase : Filter.Tendsto (fun x : ℝ => Real.log x ^ n / x)
      Filter.atTop (nhds 0) := by
    simpa only [Real.rpow_natCast, Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop (s := (1 : ℝ)) (n : ℝ) one_pos).tendsto_div_nhds_zero
  have hscale : Filter.Tendsto (fun x : ℝ => nu⁻¹ * x) Filter.atTop Filter.atTop :=
    (Filter.tendsto_const_mul_atTop_of_pos (inv_pos.mpr hnu)).mpr Filter.tendsto_id
  have h := (hbase.comp hscale).const_mul nu⁻¹
  have he : (fun x : ℝ => nu⁻¹ * (Real.log (nu⁻¹ * x) ^ n / (nu⁻¹ * x))) =
      (fun x : ℝ => Real.log (nu⁻¹ * x) ^ n / x) := by
    funext x
    rw [← mul_div_assoc, mul_div_mul_left _ _ (inv_ne_zero hnu.ne')]
  simpa only [Function.comp_def, mul_zero, he] using h

end SuperdiffusionCLT.Section3.Setup
