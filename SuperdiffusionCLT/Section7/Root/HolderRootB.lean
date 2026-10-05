/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Root.HolderBallCubeD
public import SuperdiffusionCLT.Section6.Prereq.GrowthSpace
public import SuperdiffusionCLT.Section7.Prereq.RootCarriersApi
public import SuperdiffusionCLT.Section7.Prereq.RootCarriersApiB
public import SuperdiffusionCLT.Section7.Prereq.WhitneyLocalB

/-!
# Bridges between the translated cubes of the interior estimate and the Hölder carriers

* `hr_shiftCube_eq`: the translated triadic cube is the sup-norm ball `h1_cube`.
* `hr_avg_eq`, `hr_lpBar_eq`: the average `⨍` and the normalized `L²` norm `lpBar` of the interior
  estimate are `h1_avg` and `ofReal (h1_l2 ·)`.
* `hr_l2_le_linf`: the normalized `L²` oscillation is at most the `L^∞` oscillation.
-/

@[expose] public section

open MeasureTheory Homogenization
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The translated triadic cube is a sup-norm ball. -/
theorem hr_shiftCube_eq (y : Vec d) (n : ℕ) : shiftCube y (n : ℤ) = h1_cube y n := by
  ext x
  rw [rc_mem_shiftCube, h1_mem_cube_iff]
  simp only [zpow_natCast]

/-- The set average is the average `h1_avg`. -/
theorem hr_avg_eq (S : Set (Vec d)) (u : Vec d → ℝ) : ⨍ z in S, u z = h1_avg S u := by
  rw [setAverage_eq]
  unfold h1_avg
  rw [smul_eq_mul, Measure.real, div_eq_inv_mul]

/-- `lpBar` of the oscillation is `h1_l2`. -/
theorem hr_lpBar_eq {S : Set (Vec d)} {u : Vec d → ℝ} (hS : volume S ≠ ⊤)
    (hv : 0 < (volume S).toReal) (hu : MemLp u 2 (volume.restrict S)) :
    lpBar S 2 (fun x => u x - h1_avg S u) = ENNReal.ofReal (h1_l2 S u) := by
  have hfin := h1_finite_restrict hS
  have hF : MemLp (fun x => u x - h1_avg S u) 2 (volume.restrict S) := hu.sub (memLp_const _)
  rw [rc_lpBar_two_eq S _ hF.aestronglyMeasurable,
    hF.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  have e0 : (volume S)⁻¹ = ENNReal.ofReal (((volume S).toReal)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hv, ENNReal.ofReal_toReal hS]
  have e1 : (volume S)⁻¹ ^ (1 / 2 : ℝ) = ENNReal.ofReal (((volume S).toReal)⁻¹ ^ (1 / 2 : ℝ)) := by
    rw [e0, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
  have hint : ∫ x in S, ‖u x - h1_avg S u‖ ^ (2 : ℝ≥0∞).toReal =
      ∫ x in S, (u x - h1_avg S u) ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards with x
    simp only [Real.norm_eq_abs, ENNReal.toReal_ofNat]
    rw [Real.rpow_two, sq_abs]
  rw [e1, ← ENNReal.ofReal_mul (by positivity), hint]
  congr 1
  unfold h1_l2
  simp only [ENNReal.toReal_ofNat]
  rw [Real.sqrt_eq_rpow, div_eq_inv_mul (∫ x in S, (u x - h1_avg S u) ^ 2),
    Real.mul_rpow (by positivity) (integral_nonneg fun x => by positivity)]
  norm_num

/-- The normalized `L²` oscillation is at most the `L^∞` oscillation. -/
theorem hr_l2_le_linf {S : Set (Vec d)} {u : Vec d → ℝ} (hS : volume S ≠ ⊤)
    (hv : 0 < (volume S).toReal) (hu : MemLp u ⊤ (volume.restrict S)) :
    h1_l2 S u ≤ h1_linf S u (h1_avg S u) := by
  have hfin := h1_finite_restrict hS
  have hsub := h1_memLp_sub (subset_refl S) hS hu (h1_avg S u)
  have hae := h1_ae_le_linf hsub
  have hM : 0 ≤ h1_linf S u (h1_avg S u) := ENNReal.toReal_nonneg
  have hu2 : MemLp u 2 (volume.restrict S) := hu.mono_exponent le_top
  have hF2 : MemLp (fun x => u x - h1_avg S u) 2 (volume.restrict S) := hu2.sub (memLp_const _)
  have hi : Integrable (fun x => (u x - h1_avg S u) ^ 2) (volume.restrict S) := hF2.integrable_sq
  have hle : ∫ x in S, (u x - h1_avg S u) ^ 2 ≤ ∫ x in S, h1_linf S u (h1_avg S u) ^ 2 := by
    refine integral_mono_ae hi (integrable_const _) ?_
    filter_upwards [hae] with x hx
    have := abs_le.1 hx
    nlinarith only [this.1, this.2]
  rw [setIntegral_const, smul_eq_mul] at hle
  unfold h1_l2
  rw [Real.sqrt_le_left hM]
  rw [div_le_iff₀ hv]
  rw [Measure.real] at hle
  linarith only [hle, mul_comm (volume S).toReal (h1_linf S u (h1_avg S u) ^ 2)]

/-- The ball measure is the normalized restriction. -/
theorem hr_ballMeasure_eq (r : ℝ) :
    SuperdiffusionCLT.Section6.ballMeasure (d := d) r =
      (volume (SuperdiffusionCLT.Section6.euclidBall (d := d) r))⁻¹ •
        volume.restrict (SuperdiffusionCLT.Section6.euclidBall (d := d) r) := rfl

/-- The average against the ball measure is `h1_avg`. -/
theorem hr_ballAvg (r : ℝ) (u : Vec d → ℝ) :
    ∫ y, u y ∂(SuperdiffusionCLT.Section6.ballMeasure (d := d) r) =
      h1_avg (SuperdiffusionCLT.Section6.euclidBall (d := d) r) u := by
  rw [hr_ballMeasure_eq, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]
  unfold h1_avg
  rw [div_eq_inv_mul]

/-- The normalized `L²` norm on the ball is `lpBar`. -/
theorem hr_ballL2_eq (r : ℝ) (f : Vec d → ℝ) :
    SuperdiffusionCLT.Section6.ballL2 r f =
      lpBar (SuperdiffusionCLT.Section6.euclidBall (d := d) r) 2 f := rfl

/-- The ball `L²` oscillation, as `ofReal (h1_l2 ·)`. -/
theorem hr_ballL2_osc [NeZero d] {R : ℝ} (hR : 0 < R) {u : Vec d → ℝ}
    (hu2 : MemLp u 2 (volume.restrict (SuperdiffusionCLT.Section6.euclidBall (d := d) R))) :
    SuperdiffusionCLT.Section6.ballL2 R
        (fun x => u x - ∫ y, u y ∂(SuperdiffusionCLT.Section6.ballMeasure (d := d) R)) =
      ENNReal.ofReal (h1_l2 (SuperdiffusionCLT.Section6.euclidBall (d := d) R) u) := by
  rw [hr_ballL2_eq, hr_ballAvg R]
  exact hr_lpBar_eq (h1_vol_ball_ne_top hR)
    (ENNReal.toReal_pos (SuperdiffusionCLT.Section6.volume_euclidBall_ne_zero hR)
      (h1_vol_ball_ne_top hR)) hu2

end SuperdiffusionCLT.Section7
