/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Common.ExcessDecay.SandwichNondegeneracy
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Order.Compact

/-!
# The affine minimum on the §4.3 consumption class: sup versus Euclidean norm

The §4.3 consumption sites are the truncated windows `U_j = (x + □_j) ∩ □_m`, whose only stated
geometry is the sandwich `x + □_{j-2} ⊆ U_j ⊆ y + □_j`.  Attainment of the affine minimum
`ℓ(u,W) = argmin_{ℓ ∈ 𝕃} ‖u − ℓ‖_{L̲²(W)}` on such a window needs a two-sided **parameter-space**
nondegeneracy, whose parameter norm `‖(c,g)‖ = max(|c|, ‖g‖_∞)` adds an intercept to a slope.
This module records the comparison between the sup norm and the Euclidean norm of a slope that
the argument uses.

## Main results

* `norm_le_slopeMagnitude` — the ambient (sup) norm of a slope is dominated by its Euclidean
  norm.

## References

* ABK26, `e.excess.def` (the `min`/`argmin`).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.Common.ExcessDecay

open MeasureTheory
open Homogenization (Vec vecDot vecNormSq volumeAverage axisCube openCubeSet TriadicCube
  cubeScaleFactor)
open SuperdiffusionCLT.Section8.Common.Support

noncomputable section

variable {d : ℕ}

/-! ### Euclidean versus sup norm on `Vec d` -/

/-- The ambient (sup) norm of a slope is dominated by its Euclidean norm. -/
theorem norm_le_slopeMagnitude (g : Vec d) : ‖g‖ ≤ slopeMagnitude g := by
  refine (pi_norm_le_iff_of_nonneg (slopeMagnitude_nonneg g)).2 fun i => ?_
  rw [Real.norm_eq_abs, slopeMagnitude]
  have hsum : g i * g i ≤ ∑ j, g j * g j :=
    Finset.single_le_sum (f := fun j => g j * g j) (fun j _ => mul_self_nonneg (g j))
      (Finset.mem_univ i)
  have hv : |g i| ^ 2 ≤ vecNormSq g := by
    rw [sq_abs, pow_two, vecNormSq, vecDot]
    exact hsum
  exact (Real.le_sqrt (abs_nonneg _) (Homogenization.vecNormSq_nonneg g)).2 hv

end

end SuperdiffusionCLT.Section8.Common.ExcessDecay
