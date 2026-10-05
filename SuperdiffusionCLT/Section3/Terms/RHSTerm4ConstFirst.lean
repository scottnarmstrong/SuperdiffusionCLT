/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5
public import SuperdiffusionCLT.Probability.OrliczMoments
public import SuperdiffusionCLT.Probability.OrliczProduct
public import SuperdiffusionCLT.Section2.Norms.FractionalHs
public import SuperdiffusionCLT.Section2.Norms.NegativeHatFullGradient
public import SuperdiffusionCLT.Section3.ResponseFields.Norms
public import SuperdiffusionCLT.Section3.Setup.Scales
public import Homogenization.Book.Ch02.Matrices
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
# The constant of `l.RHS.term4`

Lemma `l.RHS.term4`, with display `e.RHS.term4`, is stated with a constant `C` fixed before the
section data, that is, before the scale selection `S`, the law `P`, the test vector `p` and the
response `w`. (A constant quantified after these binders would make the statement vacuous: the
left-hand side is a finite real number and the right-hand side
`(sigmaBarStarInvSqrt nu S.LPrime P S.n)^2` is positive, so some `C` always exists.)

This module names the constant: `termFourConst` is the explicit witness `4 C₁ C₂` (with a lower
bound `1`), and `l_RHS_term4_constFirst_ae` (`Section3/Terms/RHSTerm4Join.lean`) proves
`e.RHS.term4` with this constant quantified first.

## Main results

* `termFourConst`: the constant of `e.RHS.term4`.
* `one_le_termFourConst`: it is at least `1`.

## What the constant depends on

`termFourConst C₁ C₂` depends **only** on the two printed amplitude constants:
`C₁`, the clause-(a) constant of the stream-increment scale-estimate gate at
`s = 1/2`, `p = 2`, and `C₂`, the constant of the `H̲^{1/2}` conjunct of `e.nablaw.Lt`.  It does
not depend on the dimension, on the law, on the scale selection, on the test vector or on the
response.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open scoped ENNReal

noncomputable section

/-! ## The constant -/

/-- **The constant of `e.RHS.term4`**: the product `4 C₁ C₂` produced by the closing chain of
the proof of `l.RHS.term4` — the multiplication rule `l.o.gamma2.mult` contributes
`orliczProductConst 2 2 = 2` and the second moment at `k = 2` contributes
`1 + Γ(2) = 2`.  It depends only on the two printed amplitude constants. -/
def termFourConst (C₁ C₂ : ℝ) : ℝ := max 1 (4 * C₁ * C₂)

theorem one_le_termFourConst (C₁ C₂ : ℝ) : 1 ≤ termFourConst C₁ C₂ :=
  le_max_left _ _

/-! ## The constant is fixed before the section data -/

end

end SuperdiffusionCLT.Section3.Terms
