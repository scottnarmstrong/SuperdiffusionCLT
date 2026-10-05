/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.RootArith

/-!
# Arithmetic input `hOneScale` for `srootMS_minimal_scales_of_inputs` — first conjunct

In the proof of `p.minimal.scales`
(`e.new.mixing.minscale.one.scale`), `hOneScale`'s full body
has three conjuncts once `sig, m` are fixed (the two tail-parameter floors
`1 ≤ T1`, `1 ≤ T2`, and the big union-bound inequality); this file proves
only the leading conjunct `4 log 3 ≤ hat L₂`, via `LNaught.Threshold.lNaught_ge`
applied to the FIRST `L₀` term of `srootMS_Lhat2` (the same term `RootArith.lean`
uses for `hThr`): `8 < L₀(C, C expon⁻¹ delta⁻² s⁻⁴ M², 1-expon, ...) ≤ hat L₂`,
and `4 log 3 < 8`.

The two tail-parameter floors and the big inequality are proved in
`RootArithOneScaleB.lean` to `RootArithOneScaleE.lean` (tail-parameter floors via the same
`C ≳ CE²` / `C ≳ Cg·CE` route as `hThr`'s `C ≳ CE²`-ish threshold, and the big
inequality via domination through a `C`-dependent `log(hat L₂)` lower bound).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

open SuperdiffusionCLT.Section4.LNaught
open SuperdiffusionCLT.Frozen.Section4 (lNaught)

noncomputable section

/-- `4 log 3 < 8`. -/
theorem srootA_four_log3_lt_eight : 4 * Real.log 3 < 8 := by
  have h1 : Real.log 3 < 2 := by
    have he2 : (3 : ℝ) < Real.exp 2 := by
      have h := Real.add_one_lt_exp (show (2 : ℝ) ≠ 0 by norm_num)
      linarith only [h]
    have h2 := Real.log_lt_log (by norm_num : (0 : ℝ) < 3) he2
    rwa [Real.log_exp] at h2
  linarith only [h1]

/-- **The leading conjunct of `hOneScale`**: `4 log 3 ≤ hat L₂`, via `8 <` the
FIRST `L₀` term of `hat L₂` (`lNaught_ge`) and `4 log 3 < 8`. Existentially
quantifies its own threshold `C0`, absolute (no `CE`/`Cg`/`d` dependence). -/
theorem srootA_hOneScale_fourLog3 :
    ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ C : ℝ, C0 ≤ C →
      ∀ (nu cStar nondeg : ℝ), 0 < nu → nu ≤ 1 → 0 < cStar → cStar ≤ 2 → 0 < nondeg →
        ∀ (expon delta s M : ℝ), 0 < expon → expon < 1 / 2 → 0 < delta → delta ≤ 1 →
          0 < s → s ≤ 1 → 1 ≤ M →
            4 * Real.log 3 ≤ srootMS_Lhat2 C expon delta s M cStar nu nondeg := by
  obtain ⟨C0, hC01, hge⟩ := lNaught_ge
  refine ⟨max C0 1, le_trans hC01 (le_max_left _ _), ?_⟩
  intro C hC0' nu cStar nondeg hnu hnu1 hcStar hcStar2 hnondeg expon delta s M hexp0 hexp1
    hdel0 hdel1 hs0 hs1 hM
  have hC0 : C0 ≤ C := le_trans (le_max_left _ _) hC0'
  have hC1 : (1 : ℝ) ≤ C := le_trans (le_max_right _ _) hC0'
  have hexpinv1 : (1 : ℝ) ≤ expon⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hexp0]; nlinarith only [hexp1, hexp0]
  have hdelta2 : (1 : ℝ) ≤ delta ^ (-(2 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hdel0 hdel1
      (show (-(2 : ℝ)) ≤ (0 : ℝ) by norm_num)
    rwa [Real.rpow_zero] at h
  have hs4 : (1 : ℝ) ≤ s ^ (-(4 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hs0 hs1
      (show (-(4 : ℝ)) ≤ (0 : ℝ) by norm_num)
    rwa [Real.rpow_zero] at h
  have hM2 : (1 : ℝ) ≤ M ^ (2 : ℝ) := by
    calc (1 : ℝ) = (1 : ℝ) ^ (2 : ℝ) := (Real.one_rpow _).symm
      _ ≤ M ^ (2 : ℝ) := Real.rpow_le_rpow (by norm_num) hM (by norm_num)
  have hMarg1 : (1 : ℝ) ≤ C * expon⁻¹ * delta ^ (-(2 : ℝ)) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ) := by
    have h1 : (1 : ℝ) * 1 * 1 * 1 * 1 ≤ C * expon⁻¹ * delta ^ (-(2 : ℝ)) * s ^ (-(4 : ℝ)) *
        M ^ (2 : ℝ) := by
      apply mul_le_mul
      · apply mul_le_mul
        · apply mul_le_mul
          · exact mul_le_mul hC1 hexpinv1 (by norm_num) (by linarith only [hC1])
          · exact hdelta2
          · norm_num
          · positivity
        · exact hs4
        · norm_num
        · positivity
      · exact hM2
      · norm_num
      · positivity
    linarith only [h1]
  have hexpon_mem : (0 : ℝ) ≤ 1 - expon ∧ 1 - expon < 1 := ⟨by linarith only [hexp1], by
    linarith only [hexp0]⟩
  have h8 : (8 : ℝ) < lNaught C (C * expon⁻¹ * delta ^ (-(2 : ℝ)) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ))
      (1 - expon) cStar nu nondeg :=
    hge C hC0 _ hMarg1 (1 - expon) hexpon_mem.1 hexpon_mem.2 cStar hcStar hcStar2 nu hnu hnu1
      nondeg hnondeg.le
  have hle : lNaught C (C * expon⁻¹ * delta ^ (-(2 : ℝ)) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ))
      (1 - expon) cStar nu nondeg ≤ srootMS_Lhat2 C expon delta s M cStar nu nondeg := by
    unfold srootMS_Lhat2; exact le_max_left _ _
  have h8' := srootA_four_log3_lt_eight
  linarith only [h8, hle, h8']

end
end SuperdiffusionCLT.Section4.MinimalScales
