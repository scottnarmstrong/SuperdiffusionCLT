/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Geometry.AtlasTransform

/-!
# A cutoff of a `C^{1,1}` graph function

`Section7.g1b_cutoff_mul`: if `ψ` is smooth with `ψ 0 = 0`, gradient bound `M₁` and Lipschitz
gradient `M₂`, and `χ` is a smooth cutoff supported in the ball of radius `ρ₃`, with `0 ≤ χ ≤ 1`,
gradient bound `A₁` and Lipschitz gradient `A₂`, then `χ ψ` is smooth, vanishes (with its gradient)
for `‖y‖ ≥ ρ₃`, and has gradient bound `M₁ ρ₃ A₁ + M₁` and gradient Lipschitz constant
`M₁ ρ₃ A₂ + 2 A₁ M₁ + M₂`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization

variable {d : ℕ}

theorem g1b_fderiv_mul {χ ψ : Vec d → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (y : Vec d) :
    fderiv ℝ (fun z => χ z * ψ z) y = χ y • fderiv ℝ ψ y + ψ y • fderiv ℝ χ y :=
  fderiv_mul (hχ.differentiable (by simp) y) (hψ.differentiable (by simp) y)

theorem g1b_norm_add4 {E : Type*} [NormedAddCommGroup E] (a b c e : E) :
    ‖a + b + c + e‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖e‖ := by
  linarith only [norm_add_le (a + b + c) e, norm_add_le (a + b) c, norm_add_le a b]

theorem g1b_cutoff_core {χ ψ : Vec d → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {A₁ A₂ M₁ M₂ ρ₃ : ℝ}
    (hA₁ : ∀ y, ‖fderiv ℝ χ y‖ ≤ A₁) (hA₂ : ∀ y z, ‖fderiv ℝ χ y - fderiv ℝ χ z‖ ≤ A₂ * ‖y - z‖)
    (hχ01 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1) (hM₁ : ∀ y, ‖fderiv ℝ ψ y‖ ≤ M₁)
    (hM₂ : ∀ y z, ‖fderiv ℝ ψ y - fderiv ℝ ψ z‖ ≤ M₂ * ‖y - z‖) (hψ0 : ψ 0 = 0)
    {y : Vec d} (hy : ‖y‖ < ρ₃) (z : Vec d) :
    ‖fderiv ℝ (fun w => χ w * ψ w) y - fderiv ℝ (fun w => χ w * ψ w) z‖
      ≤ (M₁ * ρ₃ * A₂ + 2 * A₁ * M₁ + M₂) * ‖y - z‖ := by
  have hA0 : 0 ≤ A₁ := (norm_nonneg _).trans (hA₁ 0)
  have hψy : |ψ y| ≤ M₁ * ρ₃ := by
    have h1 := abs_sub_le_of_fderiv_bound hψ hM₁ y 0
    rw [hψ0, sub_zero, sub_zero] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hy.le ((norm_nonneg _).trans (hM₁ 0)))
  have hMρ : 0 ≤ M₁ * ρ₃ := (abs_nonneg _).trans hψy
  have hdiff : fderiv ℝ (fun w => χ w * ψ w) y - fderiv ℝ (fun w => χ w * ψ w) z
      = ψ y • (fderiv ℝ χ y - fderiv ℝ χ z) + (ψ y - ψ z) • fderiv ℝ χ z
        + χ y • (fderiv ℝ ψ y - fderiv ℝ ψ z) + (χ y - χ z) • fderiv ℝ ψ z := by
    rw [g1b_fderiv_mul hχ hψ, g1b_fderiv_mul hχ hψ]
    module
  have t1 : ‖ψ y • (fderiv ℝ χ y - fderiv ℝ χ z)‖ ≤ M₁ * ρ₃ * A₂ * ‖y - z‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |ψ y| * ‖fderiv ℝ χ y - fderiv ℝ χ z‖ ≤ (M₁ * ρ₃) * (A₂ * ‖y - z‖) :=
          mul_le_mul hψy (hA₂ y z) (norm_nonneg _) hMρ
      _ = M₁ * ρ₃ * A₂ * ‖y - z‖ := by ring
  have t2 : ‖(ψ y - ψ z) • fderiv ℝ χ z‖ ≤ A₁ * M₁ * ‖y - z‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |ψ y - ψ z| * ‖fderiv ℝ χ z‖ ≤ (M₁ * ‖y - z‖) * A₁ :=
          mul_le_mul (abs_sub_le_of_fderiv_bound hψ hM₁ y z) (hA₁ z) (norm_nonneg _)
            (mul_nonneg ((norm_nonneg _).trans (hM₁ 0)) (norm_nonneg _))
      _ = A₁ * M₁ * ‖y - z‖ := by ring
  have t3 : ‖χ y • (fderiv ℝ ψ y - fderiv ℝ ψ z)‖ ≤ M₂ * ‖y - z‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hχ01 y).1]
    calc χ y * ‖fderiv ℝ ψ y - fderiv ℝ ψ z‖ ≤ 1 * (M₂ * ‖y - z‖) :=
          mul_le_mul (hχ01 y).2 (hM₂ y z) (norm_nonneg _) zero_le_one
      _ = M₂ * ‖y - z‖ := one_mul _
  have t4 : ‖(χ y - χ z) • fderiv ℝ ψ z‖ ≤ A₁ * M₁ * ‖y - z‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |χ y - χ z| * ‖fderiv ℝ ψ z‖ ≤ (A₁ * ‖y - z‖) * M₁ :=
          mul_le_mul (abs_sub_le_of_fderiv_bound hχ hA₁ y z) (hM₁ z) (norm_nonneg _)
            (mul_nonneg hA0 (norm_nonneg _))
      _ = A₁ * M₁ * ‖y - z‖ := by ring
  rw [hdiff]
  refine (g1b_norm_add4 _ _ _ _).trans ?_
  linarith only [t1, t2, t3, t4]

theorem g1b_cutoff_mul {χ ψ : Vec d → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {A₁ A₂ M₁ M₂ ρ₃ : ℝ} (hρ₃ : 0 ≤ ρ₃) (hA₂0 : 0 ≤ A₂) (hM₂0 : 0 ≤ M₂)
    (hA₁ : ∀ y, ‖fderiv ℝ χ y‖ ≤ A₁) (hA₂ : ∀ y z, ‖fderiv ℝ χ y - fderiv ℝ χ z‖ ≤ A₂ * ‖y - z‖)
    (hχ01 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1) (hχ0 : ∀ y, ρ₃ ≤ ‖y‖ → χ y = 0)
    (hdχ0 : ∀ y, ρ₃ ≤ ‖y‖ → fderiv ℝ χ y = 0) (hM₁ : ∀ y, ‖fderiv ℝ ψ y‖ ≤ M₁)
    (hM₂ : ∀ y z, ‖fderiv ℝ ψ y - fderiv ℝ ψ z‖ ≤ M₂ * ‖y - z‖) (hψ0 : ψ 0 = 0) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => χ y * ψ y) ∧
      (∀ y, ‖fderiv ℝ (fun w => χ w * ψ w) y‖ ≤ M₁ * ρ₃ * A₁ + M₁) ∧
      (∀ y z, ‖fderiv ℝ (fun w => χ w * ψ w) y - fderiv ℝ (fun w => χ w * ψ w) z‖
        ≤ (M₁ * ρ₃ * A₂ + 2 * A₁ * M₁ + M₂) * ‖y - z‖) ∧
      ∀ y, ρ₃ ≤ ‖y‖ → χ y * ψ y = 0 := by
  have hA0 : 0 ≤ A₁ := (norm_nonneg _).trans (hA₁ 0)
  have hM0 : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ 0)
  have hzero : ∀ y, ρ₃ ≤ ‖y‖ → fderiv ℝ (fun w => χ w * ψ w) y = 0 := fun y hy => by
    rw [g1b_fderiv_mul hχ hψ, hχ0 y hy, hdχ0 y hy]
    simp
  refine ⟨hχ.mul hψ, fun y => ?_, fun y z => ?_, fun y hy => by rw [hχ0 y hy, zero_mul]⟩
  · by_cases hy : ‖y‖ < ρ₃
    · have hψy : |ψ y| ≤ M₁ * ρ₃ := by
        have h1 := abs_sub_le_of_fderiv_bound hψ hM₁ y 0
        rw [hψ0, sub_zero, sub_zero] at h1
        exact h1.trans (mul_le_mul_of_nonneg_left hy.le hM0)
      rw [g1b_fderiv_mul hχ hψ]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hχ01 y).1]
      have e1 : χ y * ‖fderiv ℝ ψ y‖ ≤ 1 * M₁ :=
        mul_le_mul (hχ01 y).2 (hM₁ y) (norm_nonneg _) zero_le_one
      have e2 : |ψ y| * ‖fderiv ℝ χ y‖ ≤ (M₁ * ρ₃) * A₁ :=
        mul_le_mul hψy (hA₁ y) (norm_nonneg _) (mul_nonneg hM0 hρ₃)
      linarith only [e1, e2]
    · rw [hzero y (not_lt.1 hy), norm_zero]
      have := mul_nonneg (mul_nonneg hM0 hρ₃) hA0
      linarith only [this, hM0]
  · by_cases hy : ‖y‖ < ρ₃
    · exact g1b_cutoff_core hχ hψ hA₁ hA₂ hχ01 hM₁ hM₂ hψ0 hy z
    · by_cases hz : ‖z‖ < ρ₃
      · rw [norm_sub_rev, norm_sub_rev y z]
        exact g1b_cutoff_core hχ hψ hA₁ hA₂ hχ01 hM₁ hM₂ hψ0 hz y
      · rw [hzero y (not_lt.1 hy), hzero z (not_lt.1 hz), sub_zero, norm_zero]
        refine mul_nonneg ?_ (norm_nonneg _)
        have h1 := mul_nonneg (mul_nonneg hM0 hρ₃) hA₂0
        have h2 := mul_nonneg hA0 hM0
        linarith only [h1, h2, hM₂0]

end SuperdiffusionCLT.Section7
