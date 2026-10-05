/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.DivergenceForm.Decay.Tail
public import SuperdiffusionCLT.Section8.Common.Regularity.Freezing.LocalContrast

/-!
# Resolvent tails from a pointwise estimate by freezing

The Agmon energy estimate only uses uniform ellipticity.  This module freezes
the coefficient at the point where the final interior estimate is read.  Thus
the coefficient may have a continuous skew part of arbitrary size: small
contrast is required only for the normalized freezing of the coefficient on the inner
ball.
-/

@[expose] public section

noncomputable section

namespace SuperdiffusionCLT.Section8.DivergenceForm.Decay

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section8.DivergenceForm
open SuperdiffusionCLT.Section8.Common.Regularity.Ported
open SuperdiffusionCLT.Section8.Common.Regularity.Freezing
open scoped ENNReal

variable {d : ℕ}

/-! ### The two-scale tail function -/

/-- The explicit two-scale tail function.  Its arguments are
`s = sqrt mu * r` and `s₀ = sqrt mu * r₀`, where `r` is the source-free
radius and `r₀` is the radius on which the normalized freezing of the coefficient has
small contrast. -/
def agmonTailFunctionFrozen (d : ℕ) [NeZero d]
    (lam Lam nu alpha s s₀ : ℝ) : ℝ :=
  (agmonTailL2Coefficient d lam Lam / |s| *
        (|s| / (2 * |s₀|)) ^ ((d : ℝ) / 2) +
      agmonTailGradientCoefficient d lam Lam alpha *
        (|s| / (2 * |s₀|)) ^ ((d : ℝ) / 2 - 1) +
      4 * agmonTailForcingCoefficient d alpha * s₀ ^ 2 / nu) *
    Real.exp (-(agmonTailRate d lam Lam alpha * s))

end SuperdiffusionCLT.Section8.DivergenceForm.Decay
