/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.SstarAnnealedResidue
public import SuperdiffusionCLT.Section3.Setup.RootLocalizationBridgesB
public import SuperdiffusionCLT.Section3.Setup.EnergySandwichBridge
public import SuperdiffusionCLT.Section3.Setup.MasterIdentityAssemblyC
public import SuperdiffusionCLT.Section3.Setup.ShellFluxWitnessesC
public import SuperdiffusionCLT.Section3.Setup.StationaryProjectionBridge
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1StepTwoBridgeB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2MeasurabilityB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3Holder
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscCgB

@[expose] public section

namespace SuperdiffusionCLT.Section3.Setup

open scoped BigOperators ENNReal

/-- The master constant bound makes the work smallness valid for `cStar ≤ 2`. -/
theorem rootChain_smallness {CM cStar : ℝ} (hCM : 1 ≤ CM)
    (hcStar : 0 < cStar) (hcStar2 : cStar ≤ 2) :
    SuperdiffusionCLT.Section3.Setup.smallnessParameter
      (SuperdiffusionCLT.Section3.Terms.sstarWorkC0 CM) cStar ≤ 1 := by
  have hCMpos : 0 < CM := lt_of_lt_of_le zero_lt_one hCM
  have hdiv : 1 / (8 * CM) ≤ (1 / 8 : ℝ) :=
    (div_le_iff₀ (by positivity)).2 (by linarith only [hCM])
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 1 / (8 * CM)) hdiv 2
  have hc0 : SuperdiffusionCLT.Section3.Terms.sstarWorkC0 CM ≤ 1 / 64 := by
    exact le_trans (min_le_right _ _) (by norm_num at hsq ⊢; exact hsq)
  have hcsq : cStar ^ 2 ≤ (4 : ℝ) := by
    have h := pow_le_pow_left₀ hcStar.le hcStar2 2
    norm_num at h
    exact h
  change SuperdiffusionCLT.Section3.Terms.sstarWorkC0 CM * cStar ^ 2 ≤ 1
  calc
    _ ≤ (1 / 64 : ℝ) * 4 := mul_le_mul hc0 hcsq (sq_nonneg _) (by norm_num)
    _ ≤ 1 := by norm_num

end SuperdiffusionCLT.Section3.Setup
