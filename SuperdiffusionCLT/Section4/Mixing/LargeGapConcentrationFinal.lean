/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.Mixing.LargeGapConcentrationMain

/-!
# The entrywise envelope bound for the large-gap case

Final ingredient of the comparable-scale regime `m ≤ 2L` of the large-gap case
`p.mixing.P.three.prime#large-gap-case` (the second, `m > L + C log(ν^{-1}L)`, indicator clause
of `Frozen.Section4.mixing_below_cutoff`): it bounds the entrywise envelope
`mixGap_entryEnvelope` by `C(d) ν^{-1} L`, which together with the deterministic quadratic-form
bound `mixGap_quadraticForm_annealed_le` of `LargeGapConcentrationMain.lean` and the `Γ1`
concentration `mixGap_isBigO_gammaOne_entrySumEnvelope` of the entrywise-`ℓ¹` envelope feeds
the assembly of that clause.

The regime `m > 2L` is not treated here: the case hypothesis alone
(`m − L ≥ K log(ν^{-1}L)`) does not force `m − L` large *relative to `m`* without the extra
`m ≤ 2L` (or a symmetric substitute). -/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

open Homogenization
open Homogenization.IndependentSums
open MeasureTheory ProbabilityTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

variable {d : ℕ}

/-- **The entrywise envelope is `≤ C(d) ν^{-1} L`**, for `0 < ν ≤ 1` and
`L ≥ 1`. -/
theorem mixGap_entryEnvelope_le {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1) (d L : ℕ) (hL : 1 ≤ L) :
    mixGap_entryEnvelope d nu L ≤ (3 + 4 * cutoffL2Const d) * nu⁻¹ * (L : ℝ) := by
  have hL2 : (0 : ℝ) ≤ cutoffL2Const d := by
    unfold cutoffL2Const cutoffSquareConst
    have hmom : (0 : ℝ) < IndependentSums.gammaMomentConst 1 :=
      IndependentSums.gammaMomentConst_pos one_pos
    positivity
  have hLR : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hnuinv : (1 : ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
  have hnu_le : nu ≤ nu⁻¹ := hnu1.trans hnuinv
  have hmax : max 1 (L : ℝ) = (L : ℝ) := max_eq_right hLR
  unfold mixGap_entryEnvelope
  rw [hmax]
  have h1 : nu ≤ nu⁻¹ * (L : ℝ) := le_trans hnu_le (le_mul_of_one_le_right (by positivity) hLR)
  have h2 : 2 * nu⁻¹ * (2 * cutoffL2Const d * (L : ℝ)) = 4 * cutoffL2Const d * nu⁻¹ * (L : ℝ) := by
    ring
  have h3 : 2 * nu⁻¹ ≤ 2 * nu⁻¹ * (L : ℝ) := le_mul_of_one_le_right (by positivity) hLR
  have h2le : 2 * nu⁻¹ * (2 * cutoffL2Const d * (L : ℝ)) ≤ 4 * cutoffL2Const d * nu⁻¹ * (L : ℝ) :=
    le_of_eq h2
  linarith only [h1, h2le, h3]

end

end SuperdiffusionCLT.Section4.Mixing
