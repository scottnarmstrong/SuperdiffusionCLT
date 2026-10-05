/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Probability.IndependentSums.PsiCalculus
public import SuperdiffusionCLT.Section4.HomogBelow.GrowthCondition

/-!
The `1 < p ≤ 2` sub-range of the Chapter 4 growth condition for
`Γ_σ`, complementing the `2 ≤ p` case already proved in
`GrowthCondition.lean`.

For `p ∈ (1, 2]` we have `⌈p⌉₊ = 2`, so the exponent `3 * ⌈p⌉₊ ^ 2 = 12`
coincides with the `p = 2` case.  Since `s ≥ 1` and `p ≤ 2` implies
`s ^ p ≤ s ^ 2`, the existing doubling lemma applies directly after
replacing `p` with `2` and noting that `⌈p⌉₊ = ⌈2⌉₊ = 2`. -/

@[expose] public section

namespace SuperdiffusionCLT.Section4.HomogBelow

theorem homogBelow_gammaSigma_growthCondition_small
    {σ : ℝ} (hσ : 0 < σ) :
    ∀ p : ℝ, 1 < p → p ≤ 2 → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
      s ^ p ≤ (Homogenization.IndependentSums.gammaGrowthConst σ) ^
          (3 * ⌈p⌉₊ ^ 2) *
        (Homogenization.IndependentSums.gammaSigma σ (t * s) /
          Homogenization.IndependentSums.gammaSigma σ t) := by
  intro p hp hp2 t s ht hs
  have hceil : ⌈p⌉₊ = (2 : ℕ) := by
    have hle : ⌈p⌉₊ ≤ (2 : ℕ) := (Nat.ceil_le (α := ℝ)).mpr hp2
    have hgt : (1 : ℕ) < ⌈p⌉₊ := by
      by_contra! h
      have hle1 : ⌈p⌉₊ ≤ (1 : ℕ) := h
      have hple1 : p ≤ (1 : ℝ) := by
        simpa using (Nat.ceil_le (α := ℝ)).mp hle1
      linarith only [hple1, hp]
    omega
  have hpow : s ^ p ≤ s ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hs hp2
  have h_existing :=
    homogBelow_gammaSigma_growthCondition_ge_two hσ (2 : ℝ) (by norm_num) t s ht hs
  calc
    s ^ p ≤ s ^ (2 : ℝ) := hpow
    _ ≤ (Homogenization.IndependentSums.gammaGrowthConst σ) ^ (3 * ⌈(2 : ℝ)⌉₊ ^ 2) *
        (Homogenization.IndependentSums.gammaSigma σ (t * s) /
          Homogenization.IndependentSums.gammaSigma σ t) := h_existing
    _ = (Homogenization.IndependentSums.gammaGrowthConst σ) ^ (3 * ⌈p⌉₊ ^ 2) *
        (Homogenization.IndependentSums.gammaSigma σ (t * s) /
          Homogenization.IndependentSums.gammaSigma σ t) := by
      simp [hceil]

end SuperdiffusionCLT.Section4.HomogBelow
