/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Frozen.Assumptions.ShellFieldCompactOpenTopology
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

@[expose] public section

@[instance_reducible]
noncomputable def
    SuperdiffusionCLT.Frozen.Assumptions.shellFieldBorelMeasurableSpace
    (d : ℕ) :
    MeasurableSpace
      (SuperdiffusionCLT.Frozen.Assumptions.ShellField d) :=
  @borel
    (SuperdiffusionCLT.Frozen.Assumptions.ShellField d)
    (SuperdiffusionCLT.Frozen.Assumptions.shellFieldCompactOpenTopology d)
