/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.CutoffMinimizerClause
public import SuperdiffusionCLT.Section2.Cutoff.Centered
public import SuperdiffusionCLT.Section2.Cutoff.Finite
public import SuperdiffusionCLT.Section2.Localization.BlockGauge

/-!
# The symmetric part of the centered cutoff pair

The minimizers clause of the statement `e.localization.minimizers` uses the volume-average-centered
level-`L` field `â = a_L - (k_L - k_m)_U` together with the level-`m` cutoff field `a_m`.
The block form of a coefficient whose symmetric part is `ν Id` with `ν > 0` is the positive
definite quadratic form `Q_A(x, y) = ν ‖x‖² + ν⁻¹ ‖y - skewPart A x‖²`, so the symmetric
part of the two fields is the input of every block argument about the pair.

## Main results

* `symmPart_centeredPairField_eq_smul_one`: the centered pair field has symmetric part
  `ν Id` at every point, because the subtracted average of the anti-symmetric increment is
  anti-symmetric.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open Homogenization
open MeasureTheory
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-- The symmetric part of the two-cutoff-centered field is `ν Id`: the
subtracted average of the anti-symmetric increment is anti-symmetric. -/
theorem symmPart_centeredPairField_eq_smul_one (nu : ℝ) (omega : ShellSeq d) (m L : ℕ)
    (U : Set (Vec d)) (x : Vec d) :
    symmPart (centeredPairField nu omega m L U x) = nu • (1 : Mat d) := by
  have hH : matTranspose (volumeAverageMat U
      (fun y => finiteShellIncrement omega m L y)) =
    -(volumeAverageMat U (fun y => finiteShellIncrement omega m L y)) := by
    have h := matTranspose_volumeAverageMat U
      (fun y => finiteShellIncrement omega m L y)
      (fun y i k => congrFun (congrFun (finiteShellIncrement_skew omega m L y) k) i)
    simpa only [matTranspose, Matrix.transpose_neg, neg_neg] using h
  have hneg : matTranspose (-(volumeAverageMat U
      (fun y => finiteShellIncrement omega m L y))) =
    -(-(volumeAverageMat U (fun y => finiteShellIncrement omega m L y))) := by
    show -matTranspose (volumeAverageMat U
      (fun y => finiteShellIncrement omega m L y)) = _
    rw [hH]
  exact (symmPart_add_of_skew hneg).trans (symmPart_coefficientCutoff nu omega L x)

/-! ## The pointwise half of the averaging bridges -/

/-! ## The `≤` half of the bridge equalities -/

end

end SuperdiffusionCLT.Section2.Localization
