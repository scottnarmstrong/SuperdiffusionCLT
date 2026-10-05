/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.LocalizationAverageT2
public import SuperdiffusionCLT.Probability.ConditionalGammaTailShell
public import SuperdiffusionCLT.Probability.OrliczIndexWeakening

/-!
# The second summand `T2`: positivity of its constants and amplitudes

The second printed summand of `e.localization.average.oneshot` is controlled through the
unified independent-sum constant at `σ = 1` and the weight envelope
`C ν⁻¹ (1∨ℓ)(1∨L)(1∨(m-n)) |P|²`.  Its conditional concentration step (printed steps 1--2) is
carried by the conditional machinery of `Probability/ConditionalGammaTailShell.lean`; summands
that are functionals of a coordinate family *disjoint* from the conditioning family have
conditional concentration following from the unconditional theorem.

## The amplitude

The raw display of the printed proof carries `ν⁻¹` at the index `Γ_{1/2}`; the
envelope `localizationAverageEnvelopeT2` carries `ν⁻³` in the display of
`e.localization.average.oneshot`.  The printed proof adopts the unified `ν⁻³` prefactor
under the standing assumption `ν ≤ 1`.  The concentration constant
`gammaSigmaIndependentSumConst 1 * K` of the independent-sum theorem is absorbed into the
envelope constant, as printed.

## Main results

* `gammaSigmaIndependentSumConst_one_pos`: the unified independent-sum constant at `σ = 1`
  is positive.
* `localizationAverageWbarAmplitude_nonneg`: the printed weight envelope is nonnegative.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open MeasureTheory Homogenization Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff

variable {d : ℕ}

/-! ## Positivity of the constants and amplitudes -/

/-- The unified independent-sum constant at `σ = 1` is positive: at `σ = 1` it
is `2 * gammaOneExpRegimeConst`, a positive multiple of the positive
constant `gammaOneExpRegimeConst`. -/
theorem gammaSigmaIndependentSumConst_one_pos :
    0 < Homogenization.Book.Ch04.gammaSigmaIndependentSumConst 1 := by
  unfold Homogenization.Book.Ch04.gammaSigmaIndependentSumConst
  rw [ite_eq_right (lt_irrefl (1 : ℝ))]
  unfold Homogenization.Book.Ch04.gammaSigmaExpRegimeEndpointConst
    Homogenization.IndependentSums.gammaSigmaExpRegimeEndpointConst
  rw [ite_eq_left rfl]
  exact mul_pos (by norm_num) Homogenization.IndependentSums.gammaOneExpRegimeConst_pos

/-- The printed weight envelope `C ν⁻¹ (1∨ℓ)(1∨L)(1∨(m-n)) |P|²` is
nonnegative. -/
theorem localizationAverageWbarAmplitude_nonneg {C nu : ℝ} (hC : 0 ≤ C) (hnu : 0 ≤ nu)
    (l L m n : ℕ) (Pvec : BlockVec d) :
    0 ≤ localizationAverageWbarAmplitude C nu l L m n Pvec := by
  unfold localizationAverageWbarAmplitude
  refine mul_nonneg (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hnu _))
    (SuperdiffusionCLT.Section2.Carriers.blockVecDot_self_nonneg Pvec)) ?_
  exact mul_nonneg (mul_nonneg (le_trans zero_le_one (le_max_left _ _))
    (le_trans zero_le_one (le_max_left _ _)))
    (le_trans zero_le_one (le_max_left _ _))

end SuperdiffusionCLT.Section2.Localization
