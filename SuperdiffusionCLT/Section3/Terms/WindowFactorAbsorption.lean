/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscCg

/-!
# Window-factor absorption: `(1 + h)^{1/2}` against a geometric rate

The union-bound factor `√(1 + h)` in the
second (Hessian) clause of `l_w_basic_regbounds_window` reaches the
constant `C_B` of `e.RHS.term3.B` as `(1 + h)^{1/2}` through
`oscBoundConst Cpo C C3 h = (Cpo·nablaW3Const C·(1 + h)^{3/2})^{1/3}·C3^{2/3}`.
Since `(1 + h)^{1/2}` grows with the window while the constants of the term-3 estimate
are quantified before the scale selection, that growth is the constant obstruction recorded
in the docstring of `osc_bound_bridge`.

This module is the real-analysis piece of the absorption test: a factor
growing like a power of `1 + h` is absorbed by *weakening the geometric rate one
notch*, at a constant depending on nothing (and on the prefactors in the
`oscBoundConst` bridges).

## Main results

* `oscBoundConst_eq_rpow`: the exact `h`-dependence of `oscBoundConst` is the
  single factor `(1 + h)^{1/2}`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open Homogenization
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

noncomputable section

/-! ## Linear versus geometric -/

/-! ## The absorption of a polynomial factor by a geometric rate -/

/-! ## How the window `S.h` enters `oscBoundConst` -/

/-- The exact `h`-dependence of `oscBoundConst`: because
`oscBoundConst Cpo C C3 h = (Cpo·nablaW3Const C·(1 + h)^{3/2})^{1/3}·C3^{2/3}`
and `(x·y)^{1/3} = x^{1/3}·y^{1/3}`, with `(1 + h)^{(3/2)·(1/3)} = (1 + h)^{1/2}`,
the window enters **only through the single factor `(1 + h)^{1/2}`** — the
union-bound loss `√(1 + h)` raised to the third power by
the third moment and then to the power `1/3` by the Hölder pairing of
`e.RHS.term3.B`.  Everything else in the constant is fixed before the scale
selection. -/
theorem oscBoundConst_eq_rpow {Cpo Co C3 : ℝ} (hCpo : 0 ≤ Cpo) (hCo : 0 ≤ Co)
    (h : ℕ) :
    oscBoundConst Cpo Co C3 h =
      (Cpo * nablaW3Const Co) ^ ((1 : ℝ) / 3) * C3 ^ ((2 : ℝ) / 3) *
        (1 + (h : ℝ)) ^ ((1 : ℝ) / 2) := by
  have hW : 0 ≤ nablaW3Const Co := nablaW3Const_nonneg hCo
  have hnn : (0 : ℝ) ≤ (1 : ℝ) + (h : ℝ) := by positivity
  have hWp : (0 : ℝ) ≤ (1 + (h : ℝ)) ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hnn _
  have h1 : (0 : ℝ) ≤ Cpo * nablaW3Const Co := mul_nonneg hCpo hW
  unfold oscBoundConst
  rw [Real.mul_rpow h1 hWp, ← Real.rpow_mul hnn,
    show ((3 : ℝ) / 2) * ((1 : ℝ) / 3) = (1 : ℝ) / 2 by norm_num]
  ring

end

end SuperdiffusionCLT.Section3.Terms