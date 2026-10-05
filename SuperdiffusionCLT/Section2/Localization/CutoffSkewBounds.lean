/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.LocalizationWitnessPackaging
public import SuperdiffusionCLT.Section2.Localization.UnsymmetricConversion

/-!
# The sandwich witness of the localization statement

The `e.skbounds` step of the printed proof of `l.localization` produces the
bilinear clause `2 p·H q ≤ Y (p·σ_*L p + q·σ_L q)` of conjunct 2 of
`Frozen.Section2.cutoff_localization` from the conjugated comparison

`Hᵗ σ_*^{-1}_L H ≤ c • σ_L`

through the unsymmetric conversion of `UnsymmetricConversion`.
The packaging witness is `Y = sqrt X` of `localizationSkewWitness`.  The bilinear
clause itself is assembled in `CutoffSkewPremises` and `CutoffSkewPremisesB`
(`localizationConjunct2_proved`).

This file proves one input of that step:

* `localizationWitness_nonneg`: the sandwich witness `X = 2 theta (1 + theta)`
  is pointwise nonnegative, the input of the amplitude comparison
  `Real.sqrt c ≤ Y`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section3.ResponseFields
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## The nonnegativity of the sandwich witness -/

/-- The pointwise nonnegativity of the sandwich witness `X = 2 theta (1 +
theta)` of `e.localization.s.star`, with `theta ≥ 0` by
`localizationTheta_nonneg`. -/
theorem localizationWitness_nonneg {nu : ℝ} (hnu : 0 ≤ nu) (n m L : ℕ)
    (omega : ShellSeq d) : 0 ≤ localizationWitness nu n m L omega := by
  have hθ := localizationTheta_nonneg nu hnu n m L omega
  have h1 : (0 : ℝ) ≤ 1 + localizationTheta nu n m L omega := by
    linarith only [hθ]
  unfold localizationWitness localizationD
  exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (mul_nonneg hθ h1)

end

end SuperdiffusionCLT.Section2.Localization