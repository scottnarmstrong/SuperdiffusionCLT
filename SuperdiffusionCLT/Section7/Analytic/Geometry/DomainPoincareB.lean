/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Geometry.DomainPoincare

/-!
# Poincare inequalities on domains: the increment along a segment

`Section7.a10_sq_diff_le`: the square of `u (x + h) - u x` is bounded by `|h|²` times the average of
`|∇u|²` along the segment, for almost every `x` whose segment lies in `W`.
-/

@[expose] public section

open MeasureTheory Homogenization Set

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem a10_jensen_sq {f : ℝ → ℝ} (hf : Measurable f) :
    ENNReal.ofReal ((∫ s in Icc (0 : ℝ) 1, f s) ^ 2) ≤
      ∫⁻ s in Icc (0 : ℝ) 1, ENNReal.ofReal (f s ^ 2) := by
  have h1 : ‖∫ s in Icc (0 : ℝ) 1, f s‖ₑ ≤ ∫⁻ s in Icc (0 : ℝ) 1, ‖f s‖ₑ :=
    enorm_integral_le_lintegral_enorm _
  have h2 : (∫⁻ s in Icc (0 : ℝ) 1, ‖f s‖ₑ) ≤
      (∫⁻ s in Icc (0 : ℝ) 1, ‖f s‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
    have := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Icc (0 : ℝ) 1))
      (Real.HolderConjugate.two_two) (f := fun s => ‖f s‖ₑ) (g := fun _ => (1 : ENNReal))
      hf.enorm.aemeasurable aemeasurable_const
    simpa using this
  have h3 : ENNReal.ofReal ((∫ s in Icc (0 : ℝ) 1, f s) ^ 2) =
      ‖∫ s in Icc (0 : ℝ) 1, f s‖ₑ ^ 2 := by
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  have h4 : ∀ s, ‖f s‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (f s ^ 2) := fun s => by
    rw [Real.enorm_eq_ofReal_abs, ENNReal.rpow_two, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  rw [h3]
  calc ‖∫ s in Icc (0 : ℝ) 1, f s‖ₑ ^ 2 ≤ (∫⁻ s in Icc (0 : ℝ) 1, ‖f s‖ₑ) ^ 2 := by gcongr
    _ ≤ ((∫⁻ s in Icc (0 : ℝ) 1, ‖f s‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ))) ^ 2 := by gcongr
    _ = ∫⁻ s in Icc (0 : ℝ) 1, ENNReal.ofReal (f s ^ 2) := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        simp [h4]

theorem a10_eq_sum_basis (h : Vec d) : h = ∑ i, h i • basisVec i := by
  ext j
  simp [Finset.sum_apply, basisVec_apply]

/-- The weak identity in the direction `h`. -/
theorem a10_weak_dir {W : Set (Vec d)} {U : Vec d → ℝ} {G : Fin d → Vec d → ℝ}
    (hUl : LocallyIntegrable U volume) (hGl : ∀ i, LocallyIntegrable (G i) volume)
    (hweak : ∀ (i : Fin d) (φ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ W → ∫ x, U x * fderiv ℝ φ x (basisVec i) = -∫ x, G i x * φ x)
    (h : Vec d) :
    ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ W →
      ∫ x, U x * fderiv ℝ φ x h = -∫ x, (∑ i, G i x * h i) * φ x := by
  intro φ hφ hφc hφW
  have hcont : ∀ i : Fin d, Continuous fun x => fderiv ℝ φ x (basisVec i) := fun i =>
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcomp : ∀ i : Fin d, HasCompactSupport fun x => fderiv ℝ φ x (basisVec i) := fun i =>
    hφc.fderiv_apply ℝ (basisVec i)
  have hI1 : ∀ i : Fin d, Integrable (fun x => h i * (U x * fderiv ℝ φ x (basisVec i)))
      volume := fun i => by
    have := hUl.integrable_smul_left_of_hasCompactSupport (hcont i) (hcomp i)
    have h2 : Integrable (fun x => U x * fderiv ℝ φ x (basisVec i)) volume := by
      simpa [smul_eq_mul, mul_comm] using this
    exact h2.const_mul _
  have hI2 : ∀ i : Fin d, Integrable (fun x => h i * (G i x * φ x)) volume := fun i => by
    have := (hGl i).integrable_smul_right_of_hasCompactSupport hφ.continuous hφc
    have h2 : Integrable (fun x => G i x * φ x) volume := by simpa [smul_eq_mul] using this
    exact h2.const_mul _
  have e1 : ∀ x, U x * fderiv ℝ φ x h = ∑ i, h i * (U x * fderiv ℝ φ x (basisVec i)) := by
    intro x
    conv_lhs => rw [a10_eq_sum_basis h]
    simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have e2 : ∀ x, (∑ i, G i x * h i) * φ x = ∑ i, h i * (G i x * φ x) := by
    intro x
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  simp only [e1, e2]
  rw [integral_finsetSum _ (fun i _ => hI1 i), integral_finsetSum _ (fun i _ => hI2 i),
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, integral_const_mul, hweak i φ hφ hφc hφW]
  ring

/-- The square of the increment along a segment, pointwise almost everywhere. -/
theorem a10_sq_diff_le {W : Set (Vec d)} (hW : IsOpen W) {U : Vec d → ℝ}
    {G : Fin d → Vec d → ℝ} (hUm : Measurable U) (hGm : ∀ i, Measurable (G i))
    (hUl : LocallyIntegrable U volume) (hGl : ∀ i, LocallyIntegrable (G i) volume)
    (hweak : ∀ (i : Fin d) (φ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ W → ∫ x, U x * fderiv ℝ φ x (basisVec i) = -∫ x, G i x * φ x)
    (h : Vec d) :
    ∀ᵐ x : Vec d, (∀ s ∈ Icc (0 : ℝ) 1, x + s • h ∈ W) →
      ENNReal.ofReal ((U (x + h) - U x) ^ 2) ≤ ENNReal.ofReal (vecNormSq h) *
        ∫⁻ s in Icc (0 : ℝ) 1, ENNReal.ofReal (∑ i, G i (x + s • h) ^ 2) := by
  have hGhm : Measurable fun y : Vec d => ∑ i, G i y * h i :=
    Finset.measurable_sum _ fun i _ => (hGm i).mul_const _
  have hGhl : LocallyIntegrable (fun y : Vec d => ∑ i, G i y * h i) volume :=
    locallyIntegrable_finsetSum _ fun i _ => by
      have e : (fun y : Vec d => G i y * h i) = h i • G i := by
        ext y
        simp [mul_comm]
      rw [e]
      exact (hGl i).smul _
  have hid := a10_translate_identity_dir hW hUm hGhm hUl hGhl h (a10_weak_dir hUl hGl hweak h)
  filter_upwards [hid] with x hx hxO
  rw [hx hxO]
  refine (a10_jensen_sq (f := fun s : ℝ => ∑ i, G i (x + s • h) * h i) ?_).trans ?_
  · refine Finset.measurable_sum _ fun i _ => ((hGm i).comp ?_).mul_const _
    fun_prop
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun s => ?_
    rw [← ENNReal.ofReal_mul (by unfold vecNormSq vecDot; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => G i (x + s • h)) (fun i => h i)
    calc (∑ i, G i (x + s • h) * h i) ^ 2 ≤ (∑ i, G i (x + s • h) ^ 2) * ∑ i, h i ^ 2 := this
      _ = vecNormSq h * ∑ i, G i (x + s • h) ^ 2 := by
        rw [mul_comm]
        congr 1
        unfold vecNormSq vecDot
        exact Finset.sum_congr rfl fun i _ => sq (h i)

end SuperdiffusionCLT.Section7
