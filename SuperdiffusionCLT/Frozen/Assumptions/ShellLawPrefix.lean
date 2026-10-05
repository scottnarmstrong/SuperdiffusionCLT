/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellField.SequenceLaw

@[expose] public section

open Homogenization MeasureTheory

/-- The paper-wide dimension condition and the standing stationarity of every
natural-number-indexed shell under real spatial translations. -/
structure SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix
    (d : ℕ)
    (P : ProbabilityMeasure
      (ℕ → SuperdiffusionCLT.Frozen.Assumptions.ShellField d)) : Prop where
  dimension : 2 ≤ d
  stationary : ∀ (n : ℕ) (z : Vec d),
    Measure.map
        (SuperdiffusionCLT.Frozen.Assumptions.ShellField.translate z)
        (SuperdiffusionCLT.Frozen.Assumptions.ShellField.shellMarginalLaw
          P n).toMeasure =
      (SuperdiffusionCLT.Frozen.Assumptions.ShellField.shellMarginalLaw
        P n).toMeasure
