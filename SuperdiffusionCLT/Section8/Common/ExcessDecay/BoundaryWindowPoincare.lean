/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Common.ExcessDecay.BoundaryTraceMeasure
public import Homogenization.Book.Ch03.Definitions
public import Homogenization.Sobolev.MatchedPair.ScaledPoincare

/-!
# The translated open cube as an axis cube

The boundary branch of the general clause works on the anchor's own window
`W' = (z + □_{n+3}) ∩ □_m`, under the gate

```text
  (z + □_{n+2}) ∩ ∂□_m ≠ ∅ .
```

Every geometric reading of that window goes through one normal form, proved
here: a translated open triadic cube is the axis-parallel box of its own corner
and side, and membership in either description is the coordinatewise strict
inequality.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.Common.ExcessDecay

open Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The translated open cube as an axis cube -/

/-- Membership in an axis cube, coordinatewise. -/
theorem mem_axisCube_iff {c : Vec d} {L : ℝ} {y : Vec d} :
    y ∈ axisCube c L ↔ ∀ j, c j < y j ∧ y j < c j + L := by
  simp [axisCube, Set.mem_pi, Set.mem_Ioo]

end

end SuperdiffusionCLT.Section8.Common.ExcessDecay
