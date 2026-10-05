/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Probability.Independence.Basic
public import Homogenization.Book.Ch02.Theorems.MatrixOperatorNorm
public import SuperdiffusionCLT.Assumptions.ShellField.LIHLocalSigma
public import SuperdiffusionCLT.Assumptions.ShellField.SequenceLaw

@[expose] public section

open Homogenization MeasureTheory ProbabilityTheory

/-- Marginal J1: every natural-number-indexed shell has range of dependence
`3^n * sqrt d` for the integral-generated local
sigma-fields of the CoarseGraining library, using non-strict separation at the stated range. -/
structure SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1
    (d : ℕ)
    (P : ProbabilityMeasure
      (ℕ → SuperdiffusionCLT.Frozen.Assumptions.ShellField d)) : Prop where
  range_dependence : ∀ (n : ℕ) (U V : Set (Vec d)),
    MeasurableSet U → MeasurableSet V →
      (∀ ⦃x y : Vec d⦄, x ∈ U → y ∈ V →
        (3 : ℝ) ^ n * Real.sqrt (d : ℝ) ≤
          Homogenization.Book.Ch02.vecNorm (x - y)) →
      Indep
        (SuperdiffusionCLT.Frozen.Assumptions.ShellField.lihLocalSigma U)
        (SuperdiffusionCLT.Frozen.Assumptions.ShellField.lihLocalSigma V)
        (SuperdiffusionCLT.Frozen.Assumptions.ShellField.shellMarginalLaw
          P n).toMeasure
