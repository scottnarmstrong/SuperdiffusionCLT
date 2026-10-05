/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Common.ExcessDecay.OneStepSchauderInteriorHess
public import SuperdiffusionCLT.Section8.Common.Support.AffineExcess
public import SuperdiffusionCLT.Section8.Common.Support.ClassicalGradient
public import Homogenization.Book.Ch03.Definitions

/-!
# The ball → window transfer of the interior Schauder atom

The interior Schauder atom gives the gradient-Lipschitz bound for `y, z` inside **one**
Euclidean ball `euclideanBall a (r/2)` on which the harmonic function is controlled.  The §4
consumer needs the bound on a **window** — a truncated triadic cube — which is
*not* contained in any such ball at the available margin: the sup ↔ `ℓ²` loss is
`√d`, while only one triadic scale (a factor `3`) separates the Hölder window
from the harmonicity domain, so for `d ≥ 3` no single admissible ball covers the
window.  (This is a genuine structural point, not a bookkeeping one: the bound
being propagated is a bound on *differences* of `∇v`, and `∇v` itself is **not**
controlled by the excess — adding a linear function changes `∇v` by a constant
and leaves the excess fixed — so the "far pairs" of the window cannot be handled
by a sup bound.  They must be handled by *chaining*.)

The chaining step is local-to-global on a convex set: a bound `‖G p − G q‖ ≤ L ‖p − q‖` valid
only for pairs at sup-distance `< ρ` upgrades, on a convex set, to the same bound for *all*
pairs, by subdividing the segment `[p,q]` (which stays in the set) into `N` steps of length
`< ρ` and telescoping.  The constant is **unchanged**, and no sign hypothesis on it is needed.

## Main results

* `euclideanSqDist_self` — the squared Euclidean distance of a point to itself vanishes.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.Common.ExcessDecay.Schauder

open MeasureTheory InnerProductSpace
open Homogenization (Vec vecNormSq euclideanBall euclideanSqDist)
open SuperdiffusionCLT.Section8.Common.Support

noncomputable section

variable {d : ℕ}

/-! ## 4. Ball geometry at the `Vec d` carrier -/

theorem euclideanSqDist_self (p : Vec d) : euclideanSqDist p p = 0 := by
  simp only [euclideanSqDist, sub_self]
  simp [vecNormSq, Homogenization.vecDot]

end

end SuperdiffusionCLT.Section8.Common.ExcessDecay.Schauder
