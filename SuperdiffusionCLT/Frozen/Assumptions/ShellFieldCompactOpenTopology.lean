/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Frozen.Assumptions.ShellField

@[expose] public section

@[instance_reducible]
noncomputable def
    SuperdiffusionCLT.Frozen.Assumptions.shellFieldCompactOpenTopology
    (d : ℕ) :
    TopologicalSpace
      (SuperdiffusionCLT.Frozen.Assumptions.ShellField d) := by
  unfold SuperdiffusionCLT.Frozen.Assumptions.ShellField
  infer_instance
