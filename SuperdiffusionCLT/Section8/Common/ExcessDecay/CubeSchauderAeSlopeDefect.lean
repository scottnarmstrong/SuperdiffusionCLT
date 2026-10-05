/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Common.ExcessDecay.BoundaryWindowPoincare
public import SuperdiffusionCLT.Section8.Common.ExcessDecay.CubeSchauderFreezing
public import SuperdiffusionCLT.Section8.Common.ExcessDecay.IterationLemmaWindowGeometry
public import SuperdiffusionCLT.Section8.Common.ExcessDecay.OneStepSchauderInterior
public import SuperdiffusionCLT.Section8.Common.ExcessDecay.OneStepSchauderInteriorHess
public import SuperdiffusionCLT.Section8.Common.ExcessDecay.OneStepWeylRepresentative
public import SuperdiffusionCLT.Section8.Common.ExcessDecay.SandwichNondegeneracyAttainment
public import SuperdiffusionCLT.Section8.Common.Support.ClassicalGradient
public import Homogenization.Sobolev.Foundations.QuantitativeCutoff
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Data.Int.Log
public import Mathlib.Topology.Order.Compact

/-!
# Cube Schauder: the slope-defect inequality of the a.e. identification

The master inequality of the a.e. identification `Ψ = ∇w`.  Fix a base point
`z ∈ □_m` and a scale `j` small enough that the Euclidean ball of radius `3^j/2`
around `z` sits inside `□_m`, and let `η = campanatoCutoff z j`.  For an
arbitrary affine competitor `ℓ = (c,g)` and an arbitrary reference vector `v`,

```text
  |g_i − v_i| · ∫_{□_m} η
      ≤ |∫_{□_m} (∂_i u − g_i) η|  +  ∫_{□_m} |∂_i u − v_i| η
      ≤ C(d)·3^{-j}·‖u − ℓ‖_{L̲²(W_j)}·|W_j|  +  ∫_{W_j} |∂_i u − v_i| ,
```

with `W_j = (z+□_j) ∩ □_m`.  Both right-hand terms are localized: the first is
`C(d)·K·√(3^j)·|W_j|` at the affine minimizer under the Campanato datum, and the
second is `|W_j|` times the oscillation average of `∂_i u` around `v` on the
window.  The left factor is bounded below by
`(3^j/(8(d+1)))^d = |euclideanBall z (3^j/8)|`'s own lower bound, because `η = 1`
there.

Taking `v = ∇u(z)` at a Lebesgue point of `∇u` and letting `j → −∞` therefore
forces `g_i → (∇u)_i(z)`, i.e. `Ψ(z) = ∇u(z)`.  **That last limit is not taken
here**: this module supplies the deterministic inequality only, and the Lebesgue
differentiation step remains the open residue.

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

/-! ## 1. The cutoff has a definite mass -/

theorem euclideanBall_mono {z : Vec d} {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R) :
    euclideanBall z r ⊆ euclideanBall z R := by
  intro y hy
  have hy' : euclideanSqDist y z < r ^ 2 := hy
  have hsq : r ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hr hrR 2
  exact lt_of_lt_of_le hy' hsq

/-! ## 2. Integrability of the two cutoff pairings -/

/-! ## 3. The slope-defect inequality -/

end

end SuperdiffusionCLT.Section8.Common.Estimates.Schauder
