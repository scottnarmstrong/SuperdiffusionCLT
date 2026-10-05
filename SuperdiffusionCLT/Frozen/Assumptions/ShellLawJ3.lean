/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import SuperdiffusionCLT.Assumptions.ShellField.J3Observable

@[expose] public section

open MeasureTheory

/-- Marginal J3: at every natural shell, the direct
three-term regularity observable on the natural cube has the stated strict
Gaussian tail. The carrier itself supplies the inherited `C²` regularity. -/
structure SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3
    (d : ℕ)
    (P : ProbabilityMeasure
      (ℕ → SuperdiffusionCLT.Frozen.Assumptions.ShellField d)) : Prop where
  gaussian_tail : ∀ (n : ℕ) (t : ℝ), 1 ≤ t →
    P.toMeasure
        {F : ℕ → SuperdiffusionCLT.Frozen.Assumptions.ShellField d |
          t < SuperdiffusionCLT.Frozen.Assumptions.ShellField.j3Observable
            d n (F n)} ≤
      ENNReal.ofReal (Real.exp (-(t ^ 2)))
