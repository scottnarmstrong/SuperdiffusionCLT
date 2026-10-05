/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3AnchorsConstFirst
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3LocAnchor
public import SuperdiffusionCLT.Section3.Setup.RootLocalizationBridgesB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3CgPremise
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3PigRatioSelection

/-!
# `_hPigRatio`: the three printed data and a scale package

`_hPigRatio` of the final Term 3 statement is the pigeonhole comparability
`sigmaBarStarInvSeq nu S.LPrime P (S.m - 2 S.h) <= 4 * sigmaBarStarInvSeq nu S.LPrime P S.n`.
It follows from three printed data beyond the scale binders of that statement:

1. `hCT`, the printed largeness `e.L.vs.nu` (`4 * pigRatioCeta d CL <= nu⁻¹ S.L`);
2. `hSa`, the scale-selection identity `S.a = scaleOffset pigRatioK nu S.L`;
3. `hpigL`, the pigeonhole scalar conjunct `e.pigeon.scalar` at cutoff `S.L`.

What each of the three is:

* **`hSa` is exactly a lower bound, not an identity.**  Every use of `hSa` in the
  pigeonhole chain goes through `six_log_le_scaleOffset_mul_log_three`
  (`Section3/Setup/RootLocalizationBridgesB.lean`), which consumes only
  `K log(nu⁻¹L) <= a` via `le_scaleOffset`.  The weakening is strict on the scale
  binders: at `nu = (S.L)⁻¹` the lower bound is trivial (`log 1 = 0`) while the
  identity fails, so the identity is not what the argument needs.
* **`hCT` is a scale largeness on `nu⁻¹L` alone.**  `pigRatioCeta` is increasing in
  `CL`, so with `localizationConst d <= CL` the carried `hCT` forces the
  `CL`-free largeness
  `4 * gammaMomentConst 1 * localizationConst d * (crudeLowerConst d)⁻¹ <= nu⁻¹ L`,
  which is the printed `e.L.vs.nu` in its least admissible form.  The scale
  binders do not supply it: `CL` is a free constant of the statement, and there is
  a scale package satisfying all four scale binders together with a positive `CL`
  and `nu ∈ (0,1]` at which `hCT` fails.
* **`hpigL` is an input.**  The pigeonhole ratio at the selection consumes the cutoff-`L`
  scalar `hpig` as a hypothesis and returns the comparison at `S.LPrime`; nothing
  in the localization argument produces the scalar at cutoff `S.L`.

## Main results

* `exists_frozen_scale_binders`: a scale package carrying all four scale binders of
  the final Term 3 statement, the common witness of the two failures above.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory ProbabilityTheory
open Homogenization
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section3.Setup

noncomputable section

/-! ## The scale binders do not supply `hCT` or the offset lower bound -/

/-- **A scale package carrying all four scale binders.**  The package
`ScaleSelection.ofBase 1213 1200 600 6` has
`(L, m, h, a) = (1213, 1200, 600, 6)`, hence `ScalesOrdering S`, `2 S.h <= S.m`,
`100 S.a <= S.h` and `S.h + 1 <= 3 ^ S.a`.  It is the common witness of the two
failures described in the module header. -/
theorem exists_frozen_scale_binders :
    ∃ S : ScaleSelection,
      ScalesOrdering S ∧ 2 * S.h ≤ S.m ∧ 100 * S.a ≤ S.h ∧
        S.h + 1 ≤ 3 ^ S.a ∧ S.L = 1213 ∧ S.a = 6 := by
  refine ⟨ScaleSelection.ofBase 1213 1200 600 6 (by norm_num), ?_, ?_, ?_, ?_, rfl,
    rfl⟩
  · constructor <;> simp only [ScaleSelection.ofBase] <;> omega
  · show 2 * 600 ≤ 1200
    norm_num
  · show 100 * 6 ≤ 600
    norm_num
  · show 600 + 1 ≤ 3 ^ 6
    norm_num

end

end SuperdiffusionCLT.Section3.Terms
