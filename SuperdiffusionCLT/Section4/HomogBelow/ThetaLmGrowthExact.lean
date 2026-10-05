/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.HomogBelow.GammaGrowthSmallP

/-!
The *exact*, `p`-parametrized combination of
`homogBelow_gammaSigma_growthCondition_small` (`1 < p ≤ 2`) and
`homogBelow_gammaSigma_growthCondition_ge_two` (`2 ≤ p`), matching the
growth-condition binder for `Ψ` of [AK, Theorem 6.1] (`akhc_weakerP3`) *literally*:
`∀ p, 1 < p → p ≤ pPsi → ∀ t s, 1 ≤ t → 1 ≤ s → s^p ≤ KPsi^(3⌈p⌉₊²)·(Ψ(ts)/Ψt)`,
with the exponent `⌈p⌉₊` depending on the bound variable `p` itself.

Weakening the exponent to a single `⌈P₀⌉₊` uniform over the whole range `p ≤ P₀`
would give a *different* (looser, not implied by nor implying the target) statement
`s^p ≤ K^(3⌈P₀⌉₊²)·(...)`, which does **not** literally discharge this binder. This file
therefore runs the case split without any final weakening, so the binder of
[AK, Theorem 6.1] can be discharged directly. -/

@[expose] public section

/-- **The exact growth condition, `1 < p`, no upper range needed.** -/
theorem SuperdiffusionCLT.Section4.HomogBelow.homogBelow_gammaSigma_growthCondition_exact
    {σ : ℝ} (hσ : 0 < σ) :
    ∀ p : ℝ, 1 < p → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
      s ^ p ≤ (Homogenization.IndependentSums.gammaGrowthConst σ) ^ (3 * ⌈p⌉₊ ^ 2) *
        (Homogenization.IndependentSums.gammaSigma σ (t * s) /
          Homogenization.IndependentSums.gammaSigma σ t) := by
  intro p hp t s ht hs
  by_cases hp2 : p ≤ 2
  · exact SuperdiffusionCLT.Section4.HomogBelow.homogBelow_gammaSigma_growthCondition_small
      hσ p hp hp2 t s ht hs
  · exact SuperdiffusionCLT.Section4.HomogBelow.homogBelow_gammaSigma_growthCondition_ge_two
      hσ p (not_le.mp hp2).le t s ht hs
