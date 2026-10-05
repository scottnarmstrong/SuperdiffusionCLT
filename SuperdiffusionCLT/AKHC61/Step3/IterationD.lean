/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.Step3.RecursionB
public import SuperdiffusionCLT.AKHC61.WeakNorms.PrimeI
public import Homogenization.Book.Ch02.MultiscaleEllipticity

/-!
# Package E4, part 4: the dimension-only uniform contraction rate

Continues `Step3/RecursionB.lean`. The Step 3 recursion's contraction
factor `θ(m) := 4C(m)/(1+4C(m))`, `C(m) := 4(1+section53CutoffBound(cu_m))^2 + 1/4`, is genuinely
`m`-dependent — an obstacle to invoking `algebraic_decay_induction_core` (`IterationCore.lean:24`
in CoarseGraining), whose `hrec` hypothesis needs a single FIXED `θ` for every `m`. This file
resolves it: `section53CutoffBound (originCube d n) ≤ 2^d` for every scale `n` (CoarseGraining's
own `section53CutoffBound_le_two_pow_card`, a *dimension-only* bound, uniform in the scale), so
`C(m) ≤ Cmax := 4(1+2^d)^2 + 1/4` and (since `x ↦ 4x/(1+4x)` is increasing) `θ(m) ≤ θmax :=
4Cmax/(1+4Cmax) < 1`, uniformly in `m`. Combined with `F(m-Lstep) ≥ 0` (`Θ ≥ 1`, package A2),
the output of the Step 3 recursion can always be weakened to use the fixed `θmax` in place of
`θ(m)`.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.Step3

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.AKHC61.Carrier

noncomputable section

/-- **The dimension-only contraction cap `Cmax d`.** An upper bound, uniform in the scale `m`,
for the Step 3 recursion's `C(m) := 4(1+section53CutoffBound(cu_m))^2 + 1/4`. -/
noncomputable def akhcIter_Cmax (d : ℕ) : ℝ := 4 * (1 + (2 : ℝ) ^ d) ^ 2 + 1 / 4

/-- **The dimension-only contraction rate `θmax d`.** An upper bound, uniform in the scale `m`,
for the Step 3 recursion's `θ(m) := 4C(m)/(1+4C(m))`. -/
noncomputable def akhcIter_thetaMax (d : ℕ) : ℝ :=
  (4 * akhcIter_Cmax d) / (1 + 4 * akhcIter_Cmax d)

theorem akhcIter_Cmax_pos (d : ℕ) : 0 < akhcIter_Cmax d := by
  unfold akhcIter_Cmax; positivity

theorem akhcIter_thetaMax_nonneg (d : ℕ) : 0 ≤ akhcIter_thetaMax d := by
  unfold akhcIter_thetaMax
  have hC := akhcIter_Cmax_pos d
  positivity

theorem akhcIter_thetaMax_lt_one (d : ℕ) : akhcIter_thetaMax d < 1 := by
  unfold akhcIter_thetaMax
  have hC := akhcIter_Cmax_pos d
  rw [div_lt_one (by linarith only [hC])]
  linarith only [hC]

/-- **`x ↦ 4x/(1+4x)` is monotone on `x ≥ 0`.** -/
theorem akhcIter_contraction_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    4 * x / (1 + 4 * x) ≤ 4 * y / (1 + 4 * y) := by
  have hy : 0 ≤ y := hx.trans hxy
  have hxd : 0 < 1 + 4 * x := by linarith only [hx]
  have hyd : 0 < 1 + 4 * y := by linarith only [hy]
  have key : 4 * y / (1 + 4 * y) - 4 * x / (1 + 4 * x) =
      (4 * (y - x)) / ((1 + 4 * x) * (1 + 4 * y)) := by
    field_simp
    ring
  have hnum : 0 ≤ 4 * (y - x) := by linarith only [hxy]
  have hden : 0 < (1 + 4 * x) * (1 + 4 * y) := mul_pos hxd hyd
  have hfrac : 0 ≤ (4 * (y - x)) / ((1 + 4 * x) * (1 + 4 * y)) := div_nonneg hnum hden.le
  linarith only [key, hfrac]

/-- **The Step 3 recursion's contraction factor `θ(m)` is capped by the dimension-only `θmax d`,
uniformly in the scale `m`.** -/
theorem akhcIter_theta_le_thetaMax (d : ℕ) (Q : Homogenization.TriadicCube d) :
    (4 * (4 * (1 +
            Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffBound Q) ^ 2 +
          1 / 4) /
        (1 + 4 * (4 * (1 +
              Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffBound Q) ^ 2 +
            1 / 4))) ≤ akhcIter_thetaMax d := by
  set C := 4 * (1 +
      Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffBound Q) ^ 2 +
    1 / 4 with hC_def
  have hbound := Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffBound_le_two_pow_card Q
  have hbound_nonneg := Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffBound_nonneg Q
  have hC_nonneg : 0 ≤ C := by rw [hC_def]; positivity
  have hC_le : C ≤ akhcIter_Cmax d := by
    rw [hC_def, akhcIter_Cmax]
    nlinarith only [hbound, hbound_nonneg]
  have hmono := akhcIter_contraction_mono hC_nonneg hC_le
  unfold akhcIter_thetaMax
  exact hmono

end

end SuperdiffusionCLT.AKHC61.Step3
