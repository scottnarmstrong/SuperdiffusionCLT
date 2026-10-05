/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Probability.IndependentSums.PsiCalculus

@[expose] public section

/-- **`gammaGrowthConst 1 = 2` exactly**: `(1+1⁻¹)^(1⁻¹) = 2^1 = 2 = max 2 2`.
Needed to match `homogBelow_P2prime_verified`'s `K_{Ψ_S} := gammaGrowthConst
1` against `M0ThresholdB.lean`'s literal `2` (`homogBelowM0_threshold_corrected`'s
docstring: "`K_{Ψ_S} = 2` exact"). -/
theorem SuperdiffusionCLT.Section4.HomogBelow.homogBelow_gammaGrowthConst_one :
    Homogenization.IndependentSums.gammaGrowthConst 1 = 2 := by
  unfold Homogenization.IndependentSums.gammaGrowthConst
  have h1 : (1 : ℝ)⁻¹ = 1 := by norm_num
  rw [h1, Real.rpow_one]
  norm_num
