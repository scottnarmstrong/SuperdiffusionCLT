/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.ScaleAssembly
public import SuperdiffusionCLT.Section2.Annealed.MixingAnchorAssembly
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3AnchorsConstFirst
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3LocAnchor

/-!
# The pigeonhole data block of `_hPigRatio`, at the print's explicit constants

The obligation `_hPigRatio` of the final Term 3 statement reduces to the following data, read
after the scale package `S`:

* the print's `delta <= 1`;
* the `e.L.vs.nu` threshold data `L`, `Ceta`, `K` with `hlog`, `hCeta`, `hCT`,
  `hKlog3`;
* the scale identities `S.L = L` and `S.a = scaleOffset K nu L`;
* the pigeonhole scalar conjunct `hpigL` of `e.pigeon.scalar`.

This module names the annealing constant `Ceta` of that data explicitly, in the form the
print uses it: `Ceta` is taken at its least admissible value, the left side of `_hCeta`
itself, `pigRatioCeta d CL = gammaMomentConst 1 * CL * (crudeLowerConst d)^{-1}`.
`pigRatioCeta_le_self` is the reflexivity, so `_hCeta` is discharged with no hypothesis.

`scaleOffset` is a definition (`Section3/Setup/Parameters.lean`),
`scaleOffset K nu L = ⌈K log(nu^{-1} L)⌉₊`.

## Main results

* `pigRatioCeta` -- the explicit constant.
* `pigRatioCeta_le_self` -- the arithmetic gate `_hCeta`, proved outright.
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

/-! ## The print's constants, named explicitly -/

/-- **The print's annealing constant `Ceta`** (the threshold data of
`e.L.vs.nu`), at the least admissible value: the left side of the datum
`_hCeta`. -/
noncomputable def pigRatioCeta (d : ℕ) (CL : ℝ) : ℝ :=
  IndependentSums.gammaMomentConst 1 * CL * (crudeLowerConst d)⁻¹

/-- **The datum `_hCeta` discharged outright** at the explicit `Ceta`: the
inequality is reflexive. -/
theorem pigRatioCeta_le_self (d : ℕ) (CL : ℝ) :
    IndependentSums.gammaMomentConst 1 * CL * (crudeLowerConst d)⁻¹ ≤
      pigRatioCeta d CL :=
  le_of_eq (by simp [pigRatioCeta])

end

end SuperdiffusionCLT.Section3.Terms
