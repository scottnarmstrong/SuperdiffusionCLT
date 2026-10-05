/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Common.Support.NormalizedL2

/-!
# The affine excess `E(u,W)` and the best-affine slope

ABK26, §4.3 opens with two displays.  With `𝕃` the affine functions on `ℝ^d`,

```
E(u,W) := |W|^{-1/d} min_{ℓ ∈ 𝕃} ‖u − ℓ‖_{L̲²(W)},   ℓ(u,W) := argmin_{ℓ ∈ 𝕃} …   (e.excess.def)
E(u,□_m) := 3^{-m} min_{ℓ ∈ 𝕃} ‖u − ℓ‖_{L̲²(□_m)}                              (e.excess.def.cubes)
```

Both normalizers are consumed downstream --- the iteration lemma runs `E_j` at
the `|U_j|^{-1/d}` normalizer on truncated windows, while the §4.4 setup and
the reabsorption constant read `E_j` at `3^{-j}`.  This module records the affine
vocabulary on which both normalizations are built.

## Naming

The identifier `excess` is already taken in this repository by the §4.2
*coarse-grained ellipticity* excess, an unrelated object, so no declaration in this tree is
called `excess`.

## Attainment, honestly

The manuscript writes `min` and `argmin` and never argues attainment.  The excess is therefore
defined by an infimum over the affine parameter space, which is unconditional and agrees with
the minimum wherever it exists.

No uniqueness statement is claimed anywhere.  The `argmin` notation is not backed by an
argument, and none of the §4.3 estimates needs one.

## Main results

* `affineEval` — the affine function `x ↦ c + g · x` with intercept `c` and slope `g`.
* `slopeMagnitude`, `slopeMagnitude_nonneg` — the Euclidean slope magnitude `|∇ℓ| = ‖g‖₂`.

## Scope

This module is a support module for the excess-decay estimates and is importable
anywhere in the Section-4 development.

## References

* The paper, `e.excess.def`, `e.excess.def.cubes`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.Common.Support

open MeasureTheory
open Homogenization (Vec vecDot vecNormSq openCubeSet TriadicCube)

noncomputable section

variable {d : ℕ}

/-! ### Affine functions and the affine distance -/

/-- The affine function `x ↦ c + g · x` with intercept `c` and slope `g = ∇ℓ`. -/
def affineEval (c : ℝ) (g : Vec d) (x : Vec d) : ℝ := c + vecDot g x

/-! ### The excess as an infimum over affine competitors -/

/-! ### The best-affine map `ℓ(u,W)` and its slope -/

/-- The euclidean slope magnitude `|∇ℓ| = ‖g‖₂`: the quantity
`p_j = |∇ℓ(u,U_j)|` of the iteration lemma. -/
def slopeMagnitude (g : Vec d) : ℝ := Real.sqrt (vecNormSq g)

theorem slopeMagnitude_nonneg (g : Vec d) : 0 ≤ slopeMagnitude g := Real.sqrt_nonneg _

/-! ### The two normalizers -/

end

end SuperdiffusionCLT.Section8.Common.Support
