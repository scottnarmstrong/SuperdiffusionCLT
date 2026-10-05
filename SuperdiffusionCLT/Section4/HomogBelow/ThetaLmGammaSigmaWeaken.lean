/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Probability.IndependentSums.PsiCalculus
public import SuperdiffusionCLT.Section2.Cutoff.Finite

/-!
The tail function `Γ_σ`'s
tail function is pointwise monotone increasing in `σ` on `t ≥ 1`, so an
`IsBigO`/`IsBigOWith` bound with respect to a LARGER `σ` implies the same
bound with respect to any SMALLER `σ' ≥ 0`. This is exactly the step needed
to combine `mixing_below_cutoff`'s three witnesses `X1` (`Γ_2`), `X2` (`Γ_1`),
`X3` (`Γ_{1/3}`) into a single tail function `Γ_{1/3}` before applying
`Homogenization.IndependentSums.isBigO_finset_sum_of_isBigO_gammaSigma`, as
the proof of `l.we.can.apply.hc` does ("the `Γ_1` term ... is
absorbed into the `Γ_{1/3}` envelope"). -/

@[expose] public section

/-- **`Γ_σ` is pointwise monotone increasing in `σ`, for `t ≥ 1`.** -/
theorem SuperdiffusionCLT.Section4.HomogBelow.homogBelow_gammaSigma_le_of_le
    {sigma1 sigma2 t : ℝ} (hsigma : sigma2 ≤ sigma1) (ht : 1 ≤ t) :
    Homogenization.IndependentSums.gammaSigma sigma2 t ≤
      Homogenization.IndependentSums.gammaSigma sigma1 t := by
  simp only [Homogenization.IndependentSums.gammaSigma_apply]
  exact Real.exp_le_exp.mpr (Real.rpow_le_rpow_of_exponent_le ht hsigma)

/-- **`IsBigOWith` weakens under a smaller `σ`.** -/
theorem SuperdiffusionCLT.Section4.HomogBelow.homogBelow_isBigOWith_of_gammaSigma_le
    {Omega : Type*} [MeasurableSpace Omega] {mu : MeasureTheory.Measure Omega}
    {sigma1 sigma2 : ℝ} (hsigma : sigma2 ≤ sigma1)
    {X : Omega → ℝ} {A : ℝ}
    (hX : Homogenization.IndependentSums.IsBigOWith mu
      (Homogenization.IndependentSums.gammaSigma sigma1) X A) :
    Homogenization.IndependentSums.IsBigOWith mu
      (Homogenization.IndependentSums.gammaSigma sigma2) X A := by
  intro t ht
  have h1 := hX ht
  have hle :=
    SuperdiffusionCLT.Section4.HomogBelow.homogBelow_gammaSigma_le_of_le hsigma ht
  have hpos1 : 0 < Homogenization.IndependentSums.gammaSigma sigma1 t :=
    lt_of_lt_of_le zero_lt_one
      (Homogenization.IndependentSums.one_le_gammaSigma (le_trans zero_le_one ht))
  have hpos2 : 0 < Homogenization.IndependentSums.gammaSigma sigma2 t :=
    lt_of_lt_of_le zero_lt_one
      (Homogenization.IndependentSums.one_le_gammaSigma (le_trans zero_le_one ht))
  have h2 : (Homogenization.IndependentSums.gammaSigma sigma1 t)⁻¹ ≤
      (Homogenization.IndependentSums.gammaSigma sigma2 t)⁻¹ :=
    (inv_le_inv₀ hpos1 hpos2).2 hle
  exact le_trans h1 h2

/-- **`IsBigO` weakens under a smaller `σ`.** -/
theorem SuperdiffusionCLT.Section4.HomogBelow.homogBelow_isBigO_of_gammaSigma_le
    {d : ℕ} {sigma1 sigma2 : ℝ} (hsigma : sigma2 ≤ sigma1)
    {P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)}
    {X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ} {A : ℝ}
    (hX : Homogenization.IndependentSums.IsBigO P.toMeasure
      (Homogenization.IndependentSums.gammaSigma sigma1) X A) :
    Homogenization.IndependentSums.IsBigO P.toMeasure
      (Homogenization.IndependentSums.gammaSigma sigma2) X A :=
  SuperdiffusionCLT.Section4.HomogBelow.homogBelow_isBigOWith_of_gammaSigma_le hsigma hX
