/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.NewMixing.MomentBound

/-!
# The `k_L - k_ell` moment bound, wired to the printed `(L-m)_+ + K log L` shape

The printed statement (`l.new.mixing.parameterized#kL-kell-L2-bound`) is:
"By `e.kmn.bounds` with `p=2` and the bound `L-ell≤(L-m)_++CKlogL`,
`‖k_L-k_ell‖²_{L2(cu_m)} ≤ O_{Gamma_1}(C((L-m)_++KlogL))`."

`newMixParam_kLkEllMomentBoundRaw` (`MomentBound.lean`) gives the raw
amplitude `L - ell`. This file upgrades that amplitude to
`max 0 (L-m) + C*K*log L` (the gap fact
of the scale construction `newMixAsm_scaleExplicit`) via `IsBigO.mono_scale`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.NewMixing

open MeasureTheory
open Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-- The `k_L - k_ell` `L²(cu_m)` moment bound, wired to the printed
`(L-m)_+ + K log L`-shaped amplitude (up to the fixed positive constant
`finiteShellIncrementPthMomentConst d 2 ^ (2:ℝ)`), given `ScaleConstruction`'s
own gap fact `L - ell ≤ max 0 (L-m) + C K log L` as a hypothesis. -/
theorem newMixParam_kLkEllMomentBoundWired
    {P : MeasureTheory.ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) {ell L m : ℕ} (hellL : ell ≤ L) {C K : ℝ}
    (hgap : (L:ℝ) - (ell:ℝ) ≤ max 0 ((L:ℝ) - (m:ℝ)) + C * K * Real.log (L:ℝ)) :
    ∃ X : ShellSeq d → ℝ, Measurable X ∧
      Homogenization.IndependentSums.IsBigO P.toMeasure
        (Homogenization.IndependentSums.gammaSigma 1) X
        (finiteShellIncrementPthMomentConst d 2 ^ (2 : ℝ) *
          (max 0 ((L:ℝ) - (m:ℝ)) + C * K * Real.log (L:ℝ))) ∧
      ∀ omega : ShellSeq d,
        Homogenization.volumeAverage (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))
            (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ (2 : ℝ)) ≤
          X omega := by
  obtain ⟨X, hXmeas, hXBigO, hXdom⟩ := newMixParam_kLkEllMomentBoundRaw hPrefix hJ2 hJ3 hJ4 ell L m hellL
  refine ⟨X, hXmeas, ?_, hXdom⟩
  have hgm : (0:ℝ) < IndependentSums.gammaMomentConst ((2:ℝ) / 2) :=
    IndependentSums.gammaMomentConst_pos (by norm_num)
  have hbase : (0:ℝ) < Real.exp 1 * IndependentSums.gammaMomentConst ((2:ℝ) / 2) :=
    mul_pos (Real.exp_pos 1) hgm
  have hpow : (0:ℝ) <
      (Real.exp 1 * IndependentSums.gammaMomentConst ((2:ℝ) / 2)) ^ ((2:ℝ)⁻¹) :=
    Real.rpow_pos_of_pos hbase _
  have hstream : (0:ℝ) < streamLinftyConst d := streamLinftyConst_pos hPrefix
  have hcoeffpos : (0:ℝ) < finiteShellIncrementPthMomentConst d 2 := by
    show (0:ℝ) < (Real.exp 1 * IndependentSums.gammaMomentConst ((2:ℝ) / 2)) ^ ((2:ℝ)⁻¹) *
      streamLinftyConst d
    exact mul_pos hpow hstream
  have hcoeffnn : (0:ℝ) ≤ finiteShellIncrementPthMomentConst d 2 ^ (2:ℝ) :=
    Real.rpow_nonneg hcoeffpos.le _
  have hAmp : finiteShellIncrementPthMomentConst d 2 ^ (2:ℝ) * ((L:ℝ) - (ell:ℝ)) ≤
      finiteShellIncrementPthMomentConst d 2 ^ (2:ℝ) *
        (max 0 ((L:ℝ) - (m:ℝ)) + C * K * Real.log (L:ℝ)) :=
    mul_le_mul_of_nonneg_left hgap hcoeffnn
  exact hXBigO.mono_scale hAmp

end
end SuperdiffusionCLT.Section4.NewMixing
