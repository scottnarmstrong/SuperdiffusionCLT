/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Lipschitz.WitnessBdryB
public import SuperdiffusionCLT.Section7.Lipschitz.InteriorHarmC

/-!
# The boundary Caccioppoli block holds for the Laplacian

For the Laplace field on a uniformly `C^{1,1}` domain, `LipCaccBdry` holds at every scale below the
chart radius.  The test function `η² (u - γ)` is admissible by the localized zero trace; the volume
ratio of the two cubes comes from the inner cube of `lip_inner_ball`.  A right-hand side that is
not almost everywhere measurable is replaced by zero, and a right-hand side outside `L²` makes the
right side infinite.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal Pointwise

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem lip_witness_bdry_cube_ball (z : Vec d) (m : ℤ) :
    shiftCube z m = Metric.ball z ((3 : ℝ) ^ m / 2) := by
  ext x
  have hp : (0 : ℝ) < (3 : ℝ) ^ m / 2 := by positivity
  rw [rc_mem_shiftCube, Metric.mem_ball, dist_eq_norm, pi_norm_lt_iff hp]
  refine forall_congr' fun i => ?_
  rw [Real.norm_eq_abs]
  rfl

theorem lip_witness_bdry_zpow_pred (j : ℕ) : (3 : ℝ) ^ ((j : ℤ) - 1) = (3 : ℝ) ^ j / 3 := by
  rw [zpow_sub₀ (by norm_num), zpow_natCast, zpow_one]

end SuperdiffusionCLT.Section7
