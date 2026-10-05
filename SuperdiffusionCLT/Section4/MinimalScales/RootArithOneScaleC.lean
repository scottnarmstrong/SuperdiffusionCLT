/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.RootArithOneScaleB

/-!
# `hOneScale`'s two tail-parameter floors, assembled

In the proof of `p.minimal.scales`
(`e.new.mixing.minscale.one.scale`), this file wires the
algebra lemmas of `RootArithOneScaleB.lean` together with
`LNaught.Threshold.lNaught_threshold` (the `L₀`-threshold property) and
`RootArithOneScale.lean`'s `srootA_hOneScale_fourLog3` into the first two
conjuncts of `hOneScale`'s body: `1 ≤ T1` and `1 ≤ T2`. The remaining (hard)
conjunct, the big union-bound inequality, is proved in `RootArithOneScaleD.lean` and
`RootArithOneScaleE.lean`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

open SuperdiffusionCLT.Section4.LNaught
open SuperdiffusionCLT.Frozen.Section4 (lNaught)

noncomputable section

/-- **`hOneScale`'s two tail-parameter floors**: `1 ≤ T1` and `1 ≤ T2`, for
every `sig, m` past `Lhat2`. -/
theorem srootA2_hOneScale_floors :
    ∀ CE Cg : ℝ, 1 ≤ CE → 1 ≤ Cg → ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ C : ℝ, C0 ≤ C →
      ∀ (nu cStar nondeg : ℝ), 0 < nu → nu ≤ 1 → 0 < cStar → cStar ≤ 2 → 0 < nondeg →
        ∀ (expon delta s M : ℝ), 0 < expon → expon < 1 / 2 → 0 < delta → delta ≤ 1 →
          0 < s → s ≤ 1 → 1 ≤ M →
            ∀ (sig : ℝ) (m : ℕ), srootMS_Lhat2 C expon delta s M cStar nu nondeg ≤ (m : ℝ) →
              0 < sig → sig ≤ Cg * nu⁻¹ * (1 + (m : ℝ)) →
                1 ≤ (srootMS_target delta sig expon m - srootMS_det CE s (C * M * s⁻¹) sig m) /
                    (2 * srootMS_A1 CE s (C * M * s⁻¹) sig m) ∧
                1 ≤ (srootMS_target delta sig expon m - srootMS_det CE s (C * M * s⁻¹) sig m) /
                    (2 * srootMS_A2 CE m) := by
  intro CE Cg hCE1 hCg1
  obtain ⟨CLT, hCLT1, hthr⟩ := lNaught_threshold
  obtain ⟨CFL, hCFL1, hFL⟩ := srootA_hOneScale_fourLog3
  refine ⟨max (max (max (144 * (CE * CE)) (24 * Cg * CE)) CLT) CFL, ?_, ?_⟩
  · have h144 : (1 : ℝ) ≤ 144 * (CE * CE) := by nlinarith only [hCE1]
    exact le_trans h144
      (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _))
  intro C hC0 nu cStar nondeg hnu hnu1 hcStar hcStar2 hnondeg expon delta s M hexp0 hexp1 hdel0
    hdel1 hs0 hs1 hM
  have hC144 : 144 * (CE * CE) ≤ C :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hC0
  have hC24 : 24 * Cg * CE ≤ C :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hC0
  have hCLT' : CLT ≤ C :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hC0
  have hCFL' : CFL ≤ C := le_trans (le_max_right _ _) hC0
  have hC1 : (1 : ℝ) ≤ C := by nlinarith only [hC144, hCE1]
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC1
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le one_pos hM
  have hLhat2_4log3 : 4 * Real.log 3 ≤ srootMS_Lhat2 C expon delta s M cStar nu nondeg :=
    hFL C hCFL' nu cStar nondeg hnu hnu1 hcStar hcStar2 hnondeg expon delta s M hexp0 hexp1
      hdel0 hdel1 hs0 hs1 hM
  have hMprime1 : (1 : ℝ) ≤ C * expon⁻¹ * delta ^ (-(2 : ℝ)) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ) :=
    srootA2_Mprime_ge_one hC1 hexp0 (by linarith only [hexp1]) hdel0 hdel1 hs0 hs1 hM
  intro sig m hLh hsig0 hsigle
  have hL1m : lNaught C (C * expon⁻¹ * delta ^ (-(2 : ℝ)) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ))
      (1 - expon) cStar nu nondeg ≤ (m : ℝ) := by
    have hle : lNaught C (C * expon⁻¹ * delta ^ (-(2 : ℝ)) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ))
        (1 - expon) cStar nu nondeg ≤ srootMS_Lhat2 C expon delta s M cStar nu nondeg := by
      unfold srootMS_Lhat2; exact le_max_left _ _
    exact le_trans hle hLh
  have hlogm1 : 1 ≤ Real.log (m : ℝ) := srootA2_logm_ge_one hLhat2_4log3 hLh
  have hlogm0 : 0 ≤ Real.log (m : ℝ) := le_trans zero_le_one hlogm1
  have hexpon_mem : (0 : ℝ) ≤ 1 - expon ∧ 1 - expon < 1 :=
    ⟨by linarith only [hexp1], by linarith only [hexp0]⟩
  have hthr' := hthr C hCLT' _ hMprime1 (1 - expon) hexpon_mem.1 hexpon_mem.2 cStar hcStar
    hcStar2 nu hnu hnu1 nondeg hnondeg.le m hL1m
  have heqexp : (1 : ℝ) - (1 - expon) = expon := by ring
  have hthr1 := hthr'.1
  rw [heqexp] at hthr1
  have hR := srootA2_Rprime_le_delta_mexpon hCpos.le hexp0 hdel0 hs0 hMpos.le hcStar hcStar2 hnu
    hlogm0 hthr1
  have hslackM := srootA2_slack_ge_two hexp0 hexp1 hdel0 hdel1 hnu hnu1 hlogm1
  have hBound1 := srootA2_delta_mexpon_ge_Mslot hCpos.le hs0 hMpos.le hslackM hR
  have hslackNu := srootA2_slack_ge_two_nu hexp0 hexp1 hdel0 hdel1 hs0 hs1 hM hlogm1
  have hBound2 := srootA2_delta_mexpon_ge_nu hCpos.le hnu hslackNu hR
  have hKeyT1 := srootA2_key_ineq_T1 hCE1 hC144 hM hs0 hs1
  have hKey2 := srootA2_key_ineq_delta hCE1 hC144 hM hs0 hs1
  have hDeltaTwoThirds := srootA2_Delta_ge_two_thirds hs0 hBound1 hKey2
  have hDeltaT1 := srootA2_Delta_ge_T1bound hBound1 hKeyT1 hDeltaTwoThirds
  have hDeltaNu := srootA2_Delta_ge_nu hDeltaTwoThirds hBound2
  have hT1 := srootA2_T1_ge_one hCpos hMpos hs0 hsig0 hCE1 hlogm1 hDeltaT1
  have hm1r : (1 : ℝ) ≤ (m : ℝ) := by linarith only [srootA2_m_gt_four hLhat2_4log3 hLh]
  have hT2 := srootA2_T2_ge_one hCpos hMpos hs0 hsig0 hCE1 hCg1 hnu hnu1 hm1r hlogm1 hsigle hC24
    hDeltaNu
  exact ⟨hT1, hT2⟩

end
end SuperdiffusionCLT.Section4.MinimalScales
