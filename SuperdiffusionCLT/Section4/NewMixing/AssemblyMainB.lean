/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.NewMixing.AssemblyBridge
public import SuperdiffusionCLT.Section4.NewMixing.AssemblyFold
public import SuperdiffusionCLT.Section4.NewMixing.MomentBoundWired
public import SuperdiffusionCLT.Section4.NewMixing.T3Bound

/-!
# The assembly at fixed parameters

At fixed shells, cutoffs and scales this file combines the uniform `T_0` witness, the uniform
energy bound (`AssemblyMainUniform2.lean`), the bridge to the scalar responses
(`AssemblyMain.lean`) and the scalar-max passage (`AssemblyScalarMax.lean`) into the printed
conclusion of `l.new.mixing.parameterized`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.NewMixing

open Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Frozen.Assumptions

noncomputable section

/-- `bfAhom_r^{±1/2} eta`, unfolded. -/
theorem newMixAsm_bfAhomPow_neg_half {d : ℕ} [NeZero d] (nu : ℝ) (r : ℕ)
    (P : MeasureTheory.ProbabilityMeasure (ShellSeq d)) (eta : BlockVec d) :
    newMixParam_bfAhomPow nu r P (-(1 : ℝ) / 2) eta =
      ((sigmaBarInfinite nu r P) ^ (-(1 : ℝ) / 2) • eta.1,
        (sigmaBarInfinite nu r P) ^ ((1 : ℝ) / 2) • eta.2) := by
  unfold newMixParam_bfAhomPow
  have : -(-(1 : ℝ) / 2) = (1 : ℝ) / 2 := by ring
  rw [this]

theorem newMixAsm_bfAhomPow_pos_half {d : ℕ} [NeZero d] (nu : ℝ) (r : ℕ)
    (P : MeasureTheory.ProbabilityMeasure (ShellSeq d)) (eta : BlockVec d) :
    newMixParam_bfAhomPow nu r P ((1 : ℝ) / 2) eta =
      ((sigmaBarInfinite nu r P) ^ ((1 : ℝ) / 2) • eta.1,
        (sigmaBarInfinite nu r P) ^ (-(1 : ℝ) / 2) • eta.2) := by
  unfold newMixParam_bfAhomPow
  have : -((1 : ℝ) / 2) = -(1 : ℝ) / 2 := by ring
  rw [this]

end
end SuperdiffusionCLT.Section4.NewMixing
