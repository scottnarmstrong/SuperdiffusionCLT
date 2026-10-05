/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Common.ExcessDecay.CubeSchauderAeSlopeDefect
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.MeasureTheory.Covering.Differentiation

/-!
# Cube Schauder: the sup-metric ball

The almost-everywhere identification `Ψ = ∇w` of the cube Schauder construction is obtained at
every Lebesgue point of the zero extension of the weak gradient, with the average taken over the
**sup-metric** ball, i.e. over the cube of side `3^j` centred at the base point.  The Lebesgue
points come from the Besicovitch Vitali family of the Lebesgue measure on `Vec d = Fin d → ℝ`,
whose closed balls *are* the sup-metric cubes.

## Main results

* `euclideanBall_subset_ball` — the Euclidean ball sits inside the sup-metric ball of the same
  radius.

## References

* ABK26.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.Common.Estimates.Schauder

open MeasureTheory Filter Topology
open Homogenization
open SuperdiffusionCLT.Section8.Common.Support
open SuperdiffusionCLT.Section8.Common.ExcessDecay
open SuperdiffusionCLT.Section8.Common.ExcessDecay.Schauder

noncomputable section

variable {d : ℕ}

/-! ## 1. The sup-metric ball -/

/-- The Euclidean ball sits inside the sup-metric ball of the same radius. -/
theorem euclideanBall_subset_ball (z : Vec d) {r : ℝ} (hr : 0 < r) :
    euclideanBall z r ⊆ Metric.ball z r := by
  intro y hy
  have hsq : euclideanSqDist y z < r ^ 2 := hy
  have hvn : vecNormSq (y - z) = euclideanSqDist y z := rfl
  have hnorm : ‖y - z‖ ≤ Real.sqrt (vecNormSq (y - z)) := norm_le_slopeMagnitude (y - z)
  have hlt : Real.sqrt (vecNormSq (y - z)) < r := by
    rw [hvn]
    exact (Real.sqrt_lt' hr).2 hsq
  rw [Metric.mem_ball, dist_eq_norm]
  exact lt_of_le_of_lt hnorm hlt

end

end SuperdiffusionCLT.Section8.Common.Estimates.Schauder
