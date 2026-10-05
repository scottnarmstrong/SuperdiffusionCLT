/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.BoundaryDecayChartK

@[expose] public section

open Homogenization MeasureTheory Filter Topology Matrix
open scoped ENNReal NNReal

/-!
# Square integrability of the flat excess

The flattened solution is square integrable on the cube, and so is its excess over any flat affine
function.
-/

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem r3e_cube_subset_ball (i₀ : Fin d) (m : ℤ) :
    openCubeSet (originCube d m) ⊆ Metric.ball (r3c_z0 i₀ m) ((3 : ℝ) ^ m) := fun x hx => by
  rw [Metric.mem_ball, dist_eq_norm]
  exact (r3e_Q_geom i₀ hx).1

theorem r3e_memLp_flat (i₀ : Fin d) (m : ℤ) (v : H1Function (openCubeSet (originCube d m)))
    (a₀ : ℝ) (b : Vec d) :
    MemLp (fun x => v.toFun x - (a₀ + vecDot b (x - r3c_z0 i₀ m))) 2
      (normalizedCubeMeasure (originCube d m)) := by
  have hR : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  have hv : MemLp v.toFun 2 (normalizedCubeMeasure (originCube d m)) :=
    memLp_normalized_of_restrict _ v.memL2
  refine hv.sub ?_
  rw [p12_normalized_eq]
  refine r3e_memLp_bound hR (r3e_cube_subset_ball i₀ m) _
    (r3e_continuous_affine a₀ b (r3c_z0 i₀ m)).aestronglyMeasurable
    (C := |a₀| + d * (‖b‖ * (3 : ℝ) ^ m)) (fun y hy => ?_) (isOpen_openCubeSet _).measurableSet 2
  have hy' : ‖y - r3c_z0 i₀ m‖ ≤ (3 : ℝ) ^ m := (r3e_Q_geom i₀ hy).1.le
  rw [Real.norm_eq_abs]
  calc |a₀ + vecDot b (y - r3c_z0 i₀ m)| ≤ |a₀| + |vecDot b (y - r3c_z0 i₀ m)| := abs_add_le _ _
    _ ≤ |a₀| + d * (‖b‖ * ‖y - r3c_z0 i₀ m‖) := by
      linarith only [p12g_dot_le b (y - r3c_z0 i₀ m)]
    _ ≤ |a₀| + d * (‖b‖ * (3 : ℝ) ^ m) := by
      have h0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      have := mul_le_mul_of_nonneg_left hy' (norm_nonneg b)
      nlinarith only [this, h0]

end SuperdiffusionCLT.Section7
