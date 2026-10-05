/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Probability.Independence.Basic
public import Homogenization.Book.Ch02.Theorems.MatrixOperatorNorm
public import SuperdiffusionCLT.Assumptions.ShellField.RestrictionSigma
public import SuperdiffusionCLT.Assumptions.ShellField.SequenceLaw

@[expose] public section

open Homogenization MeasureTheory ProbabilityTheory

/-- Marginal J1 (restriction version): every
natural-number-indexed shell has range of dependence `3^n * sqrt d` for the
pointwise-restriction sigma-fields, using non-strict separation at the stated
range.

This is the successor of `ShellLawJ1`. It differs from `ShellLawJ1` only in
the lane: the separation relation, the range, and the marginal law are the V1
ones, and `ShellField.shellRestrictionSigma`, the comap of the canonical
carrier sigma-algebra along the pointwise restriction `a |-> 1_U a`, replaces
`ShellField.lihLocalSigma`, the pullback of `CoarseGraining`'s
integral-generated `LocalSigmaR`. Because
`ShellField.lihLocalSigma_le_shellRestrictionSigma` puts the integral lane
below the restriction lane, this version implies `ShellLawJ1`. -/
structure SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
    (d : ℕ)
    (P : ProbabilityMeasure
      (ℕ → SuperdiffusionCLT.Frozen.Assumptions.ShellField d)) : Prop where
  restriction_range_dependence : ∀ (n : ℕ) (U V : Set (Vec d))
    (hU : MeasurableSet U) (hV : MeasurableSet V),
      (∀ ⦃x y : Vec d⦄, x ∈ U → y ∈ V →
        (3 : ℝ) ^ n * Real.sqrt (d : ℝ) ≤
          Homogenization.Book.Ch02.vecNorm (x - y)) →
      Indep
        (SuperdiffusionCLT.Frozen.Assumptions.ShellField.shellRestrictionSigma
          U hU)
        (SuperdiffusionCLT.Frozen.Assumptions.ShellField.shellRestrictionSigma
          V hV)
        (SuperdiffusionCLT.Frozen.Assumptions.ShellField.shellMarginalLaw
          P n).toMeasure
