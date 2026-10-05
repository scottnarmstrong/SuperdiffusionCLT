/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.LocalizationAverageT1Inputs

/-!
# Quadratic localization errors and Gaussian tails

The gradient estimate `e.nabla.kmn.Linfty` has index Γ₂. Thus the quadratic
term in `D_z` has index Γ₁, as asserted in the proof of `l.localization.average`.
The following elementary tail rule
uses the same random variable in both terms and loses no constant.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

/-- A nonnegative linear-plus-quadratic polynomial of a Γ₂ variable has
index Γ₁, with amplitude obtained by applying the polynomial to the
original amplitude. No measurability or independence is needed. -/
theorem localizationDisplayF_quadratic_gaussian_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsFiniteMeasure μ]
    {X : Ω → ℝ} {A a b : ℝ} (hA : 0 ≤ A) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hX : Homogenization.IndependentSums.IsBigO μ
      (Homogenization.IndependentSums.gammaSigma 2) X A) :
    Homogenization.IndependentSums.IsBigO μ
      (Homogenization.IndependentSums.gammaSigma 1)
      (fun ω => a * |X ω| + b * X ω ^ 2) (a * A + b * A ^ 2) := by
  rw [Homogenization.IndependentSums.isBigO_gammaSigma_iff]
  intro t ht
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  have hs1 : 1 ≤ Real.sqrt t := Real.one_le_sqrt.mpr ht
  have hs0 := Real.sqrt_nonneg t
  have hsq := Real.sq_sqrt ht0
  have hst : Real.sqrt t ≤ t := by
    nlinarith only [hs1, hsq]
  have hsub :
      Homogenization.IndependentSums.absTailEvent
        (fun ω => a * |X ω| + b * X ω ^ 2) ((a * A + b * A ^ 2) * t) ⊆
      Homogenization.IndependentSums.absTailEvent X (A * Real.sqrt t) := by
    intro ω hω
    simp only [Homogenization.IndependentSums.mem_absTailEvent] at hω ⊢
    by_contra h
    have hx : |X ω| ≤ A * Real.sqrt t := le_of_not_gt h
    have hx2 : X ω ^ 2 ≤ A ^ 2 * t := by
      have h := mul_self_le_mul_self (abs_nonneg (X ω)) hx
      simpa only [sq_abs, ← pow_two, mul_pow, hsq] using h
    have hlin : a * |X ω| ≤ a * A * t :=
      (mul_le_mul_of_nonneg_left hx ha).trans <| by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left hst (mul_nonneg ha hA)
    have hquad : b * X ω ^ 2 ≤ b * A ^ 2 * t := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hx2 hb
    rw [abs_of_nonneg (add_nonneg (mul_nonneg ha (abs_nonneg _))
      (mul_nonneg hb (sq_nonneg _)))] at hω
    exact (not_lt_of_ge (by
      calc a * |X ω| + b * X ω ^ 2 ≤ a * A * t + b * A ^ 2 * t :=
            add_le_add hlin hquad
        _ = (a * A + b * A ^ 2) * t := (add_mul _ _ _).symm)) hω
  have htail := Homogenization.IndependentSums.isBigO_gammaSigma_iff.mp hX hs1
  rw [Real.rpow_two, hsq] at htail
  rw [Real.rpow_one]
  exact (MeasureTheory.measureReal_mono hsub).trans htail

/-- Absorb both polynomial amplitudes at the small spatial scale `q ≤ 1`
and ellipticity parameter `ν ≤ 1`. -/
theorem localizationDisplayF_quadratic_amplitude_le
    {ν C q : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hC : 0 ≤ C) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    ν⁻¹ * (C * q) + ν⁻¹ ^ 2 * (C * q) ^ 2 ≤
      (C + C ^ 2) * ν⁻¹ ^ 2 * q := by
  have hi : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).mpr hν1
  have hi0 : 0 ≤ ν⁻¹ := inv_nonneg.mpr hν.le
  have hi2 : ν⁻¹ ≤ ν⁻¹ ^ 2 := by
    simpa only [mul_one, ← pow_two] using mul_le_mul_of_nonneg_left hi hi0
  have hq2 : q ^ 2 ≤ q := by
    simpa only [mul_one, ← pow_two] using mul_le_mul_of_nonneg_left hq1 hq
  calc ν⁻¹ * (C * q) + ν⁻¹ ^ 2 * (C * q) ^ 2
      ≤ ν⁻¹ ^ 2 * (C * q) + ν⁻¹ ^ 2 * (C ^ 2 * q) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right hi2 (mul_nonneg hC hq)
        · rw [mul_pow]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hq2 (sq_nonneg C)) (sq_nonneg _)
    _ = (C + C ^ 2) * ν⁻¹ ^ 2 * q := by ring

/-- The complete polynomial tail calculation at the localization scale.
This is a scalar probability lemma, rather than a claim to have derived
the Γ₂ bound on the spatial perturbation from the shell law. -/
theorem localizationDisplayF_scaled_quadratic_gaussian_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsFiniteMeasure μ] {X : Ω → ℝ} {ν C q : ℝ}
    (hν : 0 < ν) (hν1 : ν ≤ 1) (hC : 0 ≤ C) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hX : Homogenization.IndependentSums.IsBigO μ
      (Homogenization.IndependentSums.gammaSigma 2) X (C * q)) :
    Homogenization.IndependentSums.IsBigO μ
      (Homogenization.IndependentSums.gammaSigma 1)
      (fun ω => ν⁻¹ * |X ω| + ν⁻¹ ^ 2 * X ω ^ 2)
      ((C + C ^ 2) * ν⁻¹ ^ 2 * q) :=
  (localizationDisplayF_quadratic_gaussian_tail (mul_nonneg hC hq)
    (inv_nonneg.mpr hν.le) (sq_nonneg _) hX).mono_scale
      (localizationDisplayF_quadratic_amplitude_le hν hν1 hC hq hq1)

end SuperdiffusionCLT.Section2.Localization
