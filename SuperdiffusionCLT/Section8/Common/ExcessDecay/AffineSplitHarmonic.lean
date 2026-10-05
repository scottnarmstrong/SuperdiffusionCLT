/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Common.Support.AffineExcess
public import SuperdiffusionCLT.Section8.Common.Support.ClassicalGradient
public import Homogenization.Book.Ch03.Definitions
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# The tested integrand of the weak Laplacian

Item 2 of the proof of `l.comparison.reduction` defines `w` as the
harmonic function carrying the boundary residual and then *sets*
`v₀ := v - w - ℓ_h`, asserting that `v₀` is harmonic "since `ℓ_h` is affine,
hence harmonic".  In the weak (`H¹`) formulation of this repository,

```text
  IsWeaklyHarmonicOn V ℓ   ⟺   ∀ φ ∈ H¹₀(V),  ∑_i A_i ∫_V ∂_i φ = 0 ,
```

so the integrability of the tested integrand `∇u · ∇φ` on the finite-measure window is the
first ingredient of that sentence.  This module records it.

## Main results

* `integrableOn_vecDot_grad` — the integrand `∇u · ∇φ` of two `H¹` functions is integrable on
  the window.

## What is not done here

The weak divergence theorem `∫_V ∂_i φ = 0` for `φ ∈ H¹₀(V)`, the harmonicity of affine
functions and the split `v = v₀ + w + ℓ_h` are not part of this module, and neither are the
boundary conditions (i) and (ii) of the lemma or the `L^∞` bound on `w`.

## References

* ABK26, `l.excess.decay.good.scales`.
* CoarseGraining, `Homogenization/Sobolev/H1/Definitions.lean` (the
  `H10Function` approximation package),
  `Homogenization/Sobolev/Foundations/MeanZero.lean` (`H1Function.const`,
  `H1Function.affineOnIsSobolevRegularDomain`).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.Common.ExcessDecay

open Homogenization SuperdiffusionCLT.Section8.Common.Support MeasureTheory Filter Topology

noncomputable section

variable {d : ℕ}

/-- The tested integrand of the weak Laplacian is integrable: it is a finite sum
of products of `L²` gradient coordinates. -/
theorem integrableOn_vecDot_grad {V : Set (Vec d)} (u φ : H1Function V) :
    IntegrableOn (fun y => vecDot (u.grad y) (φ.grad y)) V volume := by
  have hsum : (fun y => vecDot (u.grad y) (φ.grad y)) =
      fun y => ∑ i : Fin d, (u.grad y i * φ.grad y i) := by
    funext y
    rw [vecDot]
  rw [IntegrableOn, hsum]
  refine integrable_finsetSum _ fun i _ => ?_
  exact (u.gradMemL2 i).integrable_mul (φ.gradMemL2 i)

/-! ## 4. The affine split -/

end

end SuperdiffusionCLT.Section8.Common.ExcessDecay
