/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.ResponseFields.RegboundsWindowB
public import SuperdiffusionCLT.Section3.Setup.RootLocalizationBridgesB
public import SuperdiffusionCLT.Section3.Setup.WholeSpaceEnergyApriori
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2AnchorsConstFirst
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3AnchorsConstFirst
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
# The arithmetic of the term-3 coarsening in the master inequality

The master inequality of the paper is reduced, by `master_inequality_of_selection`, to the five
term bounds `l.LHS.term1`, `e.RHS.term1`-`e.RHS.term4` and the master identity `e.ellsep.testing`.
This file records the one arithmetical step in which the term-3 bound is coarsened to the shape
that `master_inequality_of_selection` consumes.

## The one coarsening of `e.RHS.term3`

The term-3 bound concludes with the error group

`3^{-(ℓ'-n)/2} + 3^{-(ℓ-n)/8} + 3^{-(ℓ'-ℓ)/4} + 3^{-h/16}`

carrying the prefactor `C(1 + (δ + η_L)^{1/2})`, while `master_inequality_of_selection`
consumes that group with `3^{-h/8}` in the last slot and the bare prefactor
`C`.  `termThreeCoarsenArith` performs the passage, which is legitimate at the
selected scales and nowhere else: `ℓ' − n = 2a` and `100a ≤ h` (the scale
selection `e.scale.selection`) give
`3^{-h/16} ≤ 3^{-a} = 3^{-(ℓ'-n)/2}`, so the `/16` group is at most twice the
`/8` group, and `δ ≤ 1`, `η_L ≤ L^{-1000} ≤ 1` give `1 + (δ + η_L)^{1/2} ≤ 3`.
The constant of term 3 is therefore used at `6 C₃`; nothing else changes.

## Main results

* `termThreeCoarsenArith`: the arithmetic of the term-3 coarsening.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Setup

open MeasureTheory ProbabilityTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Probability.Stationary
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Terms
open scoped BigOperators ENNReal

noncomputable section

/-! ## The arithmetic of the term-3 coarsening -/

/-- The passage from the error group of the term-3 bound,
whose last entry is `3^{-h/16}` and whose prefactor is `C(1 + t)`, to the group
`master_inequality_of_selection` consumes, whose last entry is `3^{-h/8}` and
whose prefactor is `C'`, at `C' = 6C`.  The two inputs are `G₁₆ ≤ A` (at the
selected scales, `3^{-h/16} ≤ 3^{-(ℓ'-n)/2}`, because `100a ≤ h` and
`ℓ' − n = 2a`) and `t ≤ 2` (because `δ ≤ 1` and `η_L ≤ 1`). -/
theorem termThreeCoarsenArith {Y C t Q nu4 LP4 A B Cc G8 G16 : ℝ}
    (hC : 0 ≤ C) (ht : 0 ≤ t) (ht2 : t ≤ 2) (hQ : 0 ≤ Q) (hnu4 : 0 ≤ nu4)
    (hLP4 : 0 ≤ LP4) (hA : 0 ≤ A) (hB : 0 ≤ B) (hCc : 0 ≤ Cc) (hG8 : 0 ≤ G8)
    (hG16nn : 0 ≤ G16) (hG16 : G16 ≤ A)
    (hbound : Y ≤ C * t * Q + C * (1 + t) * nu4 * LP4 * (A + B + Cc + G16)) :
    Y ≤ 6 * C * t * Q + 6 * C * nu4 * LP4 * (A + B + Cc + G8) := by
  have hXnn : (0 : ℝ) ≤ nu4 * LP4 := mul_nonneg hnu4 hLP4
  have hSgnn : (0 : ℝ) ≤ A + B + Cc + G8 := by linarith only [hA, hB, hCc, hG8]
  have hS16 : A + B + Cc + G16 ≤ 2 * (A + B + Cc + G8) := by
    linarith only [hG16, hG8, hA, hB, hCc]
  have hS16nn : (0 : ℝ) ≤ A + B + Cc + G16 := by
    linarith only [hA, hB, hCc, hG16nn]
  have h1 : C * (1 + t) ≤ 3 * C := by
    have := mul_le_mul_of_nonneg_left ht2 hC
    linarith only [this]
  have h2 : nu4 * LP4 * (A + B + Cc + G16) ≤
      nu4 * LP4 * (2 * (A + B + Cc + G8)) :=
    mul_le_mul_of_nonneg_left hS16 hXnn
  have h3 : C * (1 + t) * (nu4 * LP4 * (A + B + Cc + G16)) ≤
      3 * C * (nu4 * LP4 * (2 * (A + B + Cc + G8))) :=
    mul_le_mul h1 h2 (mul_nonneg hXnn hS16nn) (by linarith only [hC])
  have h6 : C * t * Q ≤ 6 * (C * t * Q) := by
    have : (0 : ℝ) ≤ C * t * Q := mul_nonneg (mul_nonneg hC ht) hQ
    linarith only [this]
  linarith only [hbound, h3, h6]

/-! ## The master inequality from the five constant-first term bounds -/

end

end SuperdiffusionCLT.Section3.Setup
