/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Frozen.Section2.StreamCutoff

@[expose] public section

/-- The infrared cutoff `a_L(x) = ν Id + k_L(x)` of the marginal coefficient
field `a = ν Id + k`. -/
noncomputable def SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
    {d : ℕ} (nu : ℝ)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (L : ℕ) :
    Homogenization.RegCoeffField d :=
  Homogenization.RegCoeffField.constRegCoeffField
      (nu • (1 : Homogenization.Mat d)) +
    SuperdiffusionCLT.Frozen.Section2.streamCutoff omega L
