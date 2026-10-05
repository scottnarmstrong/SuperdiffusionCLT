/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.ConcAssemblyB
public import SuperdiffusionCLT.Section3.Terms.SublatticeIndependence
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1PigeonJensen

/-!
# Term 1: the constant gate

The assembled per-cube concentration of the depth moment `_hConcDepth` of `term1_close` carries
the binder `hCc : (printedSubcollectionCount d : ℝ) ≤ Cc`.  The constant gate is *free*:
the clause's right side is `ENNReal.ofReal (Cc * w) * A` with `w ≥ 0`, hence
monotone in `Cc` (`hConcDepth_gate_upgrade`), and the comparison produces exactly
the factor `printedSubcollectionCount d`.  So the chain's own constant is

`concDepthConstant d := max 1 (printedSubcollectionCount d : ℝ)`,

which meets the gate at its left component and is at least `1`, so it also feeds
the `0`-exponent branch.  Every larger constant absorbs the gate by monotonicity.

## Main results

* `concDepthConstant`: the chain's own depth constant.
* `printedSubcollectionCount_le_concDepthConstant`: it meets the constant gate.
* `one_le_concDepthConstant`: it is at least `1`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory Homogenization
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The explicit constant -/

/-- **The chain's own depth constant.**  The larger of the house normalization
`1` and the printed subcollection count that the restructured comparison
produces.  It meets the assembly's constant gate
`(printedSubcollectionCount d : ℝ) ≤ Cc` and the `0`-exponent branch's `1 ≤ Cc`
simultaneously. -/
def concDepthConstant (d : ℕ) : ℝ := max 1 (printedSubcollectionCount d : ℝ)

/-- The named constant is at least the printed subcollection count, so it
satisfies the constant gate of the assembly. -/
theorem printedSubcollectionCount_le_concDepthConstant (d : ℕ) :
    (printedSubcollectionCount d : ℝ) ≤ concDepthConstant d :=
  le_max_right _ _

/-- The named constant is at least `1`, so it also feeds the `0`-exponent branch
of the concentration (which demands `1 ≤ Cc`). -/
theorem one_le_concDepthConstant (d : ℕ) : 1 ≤ concDepthConstant d :=
  le_max_left _ _

end

end SuperdiffusionCLT.Section3.Terms
