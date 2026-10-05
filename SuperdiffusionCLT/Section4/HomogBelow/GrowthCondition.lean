/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Probability.IndependentSums.PsiCalculus

/-!
Bridges the CoarseGraining library's weak-Orlicz doubling estimate for the
stretched-exponential class `Γ_σ` into the exact growth-condition shape
demanded by `e.checkingp2prime` / `e.checkingp3prime` of the paper (the hypotheses
[AK, Theorem 6.1] places on `Ψ_S`, `Ψ` in `l.we.can.apply.hc`, and consumed identically by
`akhc_weakerP3`): for every real
`p` with `2 ≤ p`, and every `t s ≥ 1`,
`s ^ p ≤ K ^ (3 * ⌈p⌉₊ ^ 2) * (Γ_σ (t * s) / Γ_σ t)`, with the natural
number `⌈p⌉₊ ^ 2` in the exponent (matched via `Real.rpow_natCast`) rather
than the real exponent `p ^ 2` that CoarseGraining's own
`Homogenization.IndependentSums.admissiblePsi_doubling` produces.

CoarseGraining's `admissiblePsi_doubling` is built for the range `2 ≤ q`
only (`PsiCalculus.lean:342`), matching exactly the `Ψ_S = Γ_1` growth
hypothesis of `l.we.can.apply.hc` (`2 ≤ p` there). The companion
`Ψ = Γ_{1/3}` growth hypothesis of the same lemma additionally needs the
range `1 < p < 2`, which is NOT covered here and not available anywhere in
CoarseGraining at the time of writing (checked: no `HasPsiAbstractDoubling`
/ doubling-style lemma for `1 ≤ q < 2` exists in
`Homogenization.Probability.IndependentSums`). Any consumer discharging the
full growth-condition binder of [AK, Theorem 6.1] for `Ψ = Γ_{1/3}` must supply that
sub-range separately. -/

@[expose] public section

theorem SuperdiffusionCLT.Section4.HomogBelow.homogBelow_gammaSigma_growthCondition_ge_two
    {σ : ℝ} (hσ : 0 < σ) :
    ∀ p : ℝ, 2 ≤ p → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
      s ^ p ≤ (Homogenization.IndependentSums.gammaGrowthConst σ) ^
          (3 * ⌈p⌉₊ ^ 2) *
        (Homogenization.IndependentSums.gammaSigma σ (t * s) /
          Homogenization.IndependentSums.gammaSigma σ t) := by
  intro p hp t s ht hs
  have hK2 : (2 : ℝ) ≤ Homogenization.IndependentSums.gammaGrowthConst σ :=
    Homogenization.IndependentSums.two_le_gammaGrowthConst σ
  have hK1 : (1 : ℝ) ≤ Homogenization.IndependentSums.gammaGrowthConst σ :=
    le_trans one_le_two hK2
  have hGrowth := Homogenization.IndependentSums.hasPsiGrowth_gammaSigma hσ
  have hAdm := Homogenization.IndependentSums.admissiblePsi_gammaSigma hσ.le
  have hdoub :=
    Homogenization.IndependentSums.admissiblePsi_doubling hK2 hGrowth hAdm hp ht hs
  have hp0 : (0 : ℝ) ≤ p := le_trans zero_le_two hp
  have hceil : p ≤ (⌈p⌉₊ : ℝ) := Nat.le_ceil p
  have hsq : p ^ (2 : ℕ) ≤ (⌈p⌉₊ : ℝ) ^ (2 : ℕ) := pow_le_pow_left₀ hp0 hceil 2
  have hexp : 3 * p ^ (2 : ℕ) ≤ 3 * (⌈p⌉₊ : ℝ) ^ (2 : ℕ) := by linarith only [hsq]
  have hmono :
      (Homogenization.IndependentSums.gammaGrowthConst σ) ^ (3 * p ^ (2 : ℕ)) ≤
        (Homogenization.IndependentSums.gammaGrowthConst σ) ^
          (3 * (⌈p⌉₊ : ℝ) ^ (2 : ℕ)) :=
    Real.rpow_le_rpow_of_exponent_le hK1 hexp
  have hcast :
      (Homogenization.IndependentSums.gammaGrowthConst σ) ^
          (3 * (⌈p⌉₊ : ℝ) ^ (2 : ℕ)) =
        (Homogenization.IndependentSums.gammaGrowthConst σ) ^ (3 * ⌈p⌉₊ ^ 2) := by
    rw [show (3 * (⌈p⌉₊ : ℝ) ^ (2 : ℕ)) = ((3 * ⌈p⌉₊ ^ 2 : ℕ) : ℝ) by push_cast; ring]
    exact Real.rpow_natCast _ _
  have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one ht
  have hs0 : (0 : ℝ) ≤ s := le_trans zero_le_one hs
  have hΨt_pos : 0 < Homogenization.IndependentSums.gammaSigma σ t :=
    lt_of_lt_of_le zero_lt_one (Homogenization.IndependentSums.one_le_gammaSigma ht0)
  have hΨts_nonneg : 0 ≤ Homogenization.IndependentSums.gammaSigma σ (t * s) :=
    le_trans zero_le_one
      (Homogenization.IndependentSums.one_le_gammaSigma (mul_nonneg ht0 hs0))
  have hratio_nonneg :
      0 ≤ Homogenization.IndependentSums.gammaSigma σ (t * s) /
          Homogenization.IndependentSums.gammaSigma σ t :=
    div_nonneg hΨts_nonneg hΨt_pos.le
  calc
    s ^ p ≤ (Homogenization.IndependentSums.gammaGrowthConst σ) ^ (3 * p ^ (2 : ℕ)) *
        (Homogenization.IndependentSums.gammaSigma σ (t * s) /
          Homogenization.IndependentSums.gammaSigma σ t) := hdoub
    _ ≤ (Homogenization.IndependentSums.gammaGrowthConst σ) ^
          (3 * (⌈p⌉₊ : ℝ) ^ (2 : ℕ)) *
        (Homogenization.IndependentSums.gammaSigma σ (t * s) /
          Homogenization.IndependentSums.gammaSigma σ t) :=
      mul_le_mul_of_nonneg_right hmono hratio_nonneg
    _ = (Homogenization.IndependentSums.gammaGrowthConst σ) ^ (3 * ⌈p⌉₊ ^ 2) *
        (Homogenization.IndependentSums.gammaSigma σ (t * s) /
          Homogenization.IndependentSums.gammaSigma σ t) := by rw [hcast]
