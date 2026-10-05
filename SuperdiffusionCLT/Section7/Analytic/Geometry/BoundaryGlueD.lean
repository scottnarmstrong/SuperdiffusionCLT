/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Geometry.BoundaryGlueC
public import SuperdiffusionCLT.Section7.Analytic.Geometry.BoundaryRoundedD
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# The shear function of the glued domain

Given a chart function `ψ` with `ψ 0 = 0`, gradient bound `M₁` and Lipschitz gradient `M₂`, a
cutoff `χ` and `L ≥ 0`, the function `Ψ = χ ψ + L χ - L = -L + χ (ψ + L)`

* equals `ψ` where `χ = 1`, and equals the constant `-L` where `χ = 0`;
* satisfies `Ψ ≤ ψ` wherever `ψ + L ≥ 0`;
* is smooth with explicit gradient and gradient-Lipschitz bounds.

`Section7.g1c_exists_cutoff` provides the cutoffs, with bounds depending only on the dimension and
the two radii.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization

variable {d : ℕ}

theorem g1c_exists_cutoff {ρ₁ ρ₃ : ℝ} (h1 : 0 < ρ₁) (h13 : ρ₁ < ρ₃) :
    ∃ (χ : Vec d → ℝ) (A₁ A₂ : ℝ), ContDiff ℝ (⊤ : ℕ∞) χ ∧ 0 ≤ A₁ ∧ 0 ≤ A₂ ∧
      (∀ y, ‖fderiv ℝ χ y‖ ≤ A₁) ∧ (∀ y z, ‖fderiv ℝ χ y - fderiv ℝ χ z‖ ≤ A₂ * ‖y - z‖) ∧
      (∀ y, 0 ≤ χ y ∧ χ y ≤ 1) ∧ (∀ y, ‖y‖ ≤ ρ₁ → χ y = 1) ∧ (∀ y, ρ₃ ≤ ‖y‖ → χ y = 0) ∧
      (∀ y, ρ₃ ≤ ‖y‖ → fderiv ℝ χ y = 0) := by
  let b : ContDiffBump (0 : Vec d) :=
    { rIn := ρ₁
      rOut := ρ₃
      rIn_pos := h1
      rIn_lt_rOut := h13 }
  have hsupp : ∀ z, ρ₃ ≤ ‖z‖ → b z = 0 := fun z hz => by
    by_contra h
    have h' : z ∈ Function.support b := h
    rw [b.support_eq, mem_ball_zero_iff] at h'
    exact absurd hz (not_le.2 h')
  obtain ⟨A₁, A₂, hA₁, hA₂⟩ := exists_gradient_bounds b.contDiff b.hasCompactSupport
  have hA₁0 : 0 ≤ A₁ := (norm_nonneg _).trans (hA₁ 0)
  refine ⟨fun y => b y, A₁, max A₂ 0, b.contDiff, hA₁0, le_max_right _ _, hA₁,
    fun y z => (hA₂ y z).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)),
    fun y => ⟨b.nonneg, b.le_one⟩, fun y hy => b.one_of_mem_closedBall (by
      rw [mem_closedBall_zero_iff]; exact hy), hsupp, fun y hy => ?_⟩
  have hmin : IsLocalMin (fun y => b y) y :=
    Filter.Eventually.of_forall fun z => by
      show b y ≤ b z
      rw [hsupp y hy]
      exact b.nonneg
  exact hmin.fderiv_eq_zero

/-- The shear function of the glued domain. -/
def g1c_Psi (χ ψ : Vec d → ℝ) (L : ℝ) (w : Vec d) : ℝ := χ w * ψ w + L * χ w - L

theorem g1c_Psi_contDiff {χ ψ : Vec d → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (L : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (g1c_Psi χ ψ L) :=
  ((hχ.mul hψ).add (contDiff_const.mul hχ)).sub contDiff_const

theorem g1c_fderiv_Psi {χ ψ : Vec d → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (L : ℝ) (y : Vec d) :
    fderiv ℝ (g1c_Psi χ ψ L) y = fderiv ℝ (fun z => χ z * ψ z) y + L • fderiv ℝ χ y := by
  have h1 : HasFDerivAt (fun z => χ z * ψ z) (fderiv ℝ (fun z => χ z * ψ z) y) y :=
    ((hχ.mul hψ).differentiable (by simp) y).hasFDerivAt
  have h2 : HasFDerivAt χ (fderiv ℝ χ y) y := (hχ.differentiable (by simp) y).hasFDerivAt
  exact ((h1.add (h2.const_mul L)).sub_const L).fderiv

theorem g1c_Psi_eq_of_one {χ ψ : Vec d → ℝ} {L : ℝ} {w : Vec d} (hw : χ w = 1) :
    g1c_Psi χ ψ L w = ψ w := by
  unfold g1c_Psi
  rw [hw]
  ring

theorem g1c_Psi_eq_of_zero {χ ψ : Vec d → ℝ} {L : ℝ} {w : Vec d} (hw : χ w = 0) :
    g1c_Psi χ ψ L w = -L := by
  unfold g1c_Psi
  rw [hw]
  ring

theorem g1c_Psi_le {χ ψ : Vec d → ℝ} {L : ℝ} {w : Vec d} (hχ : χ w ≤ 1) (hψ : 0 ≤ ψ w + L) :
    g1c_Psi χ ψ L w ≤ ψ w := by
  unfold g1c_Psi
  nlinarith only [hχ, hψ]

theorem g1c_abs_Psi_le {χ ψ : Vec d → ℝ} {L B : ℝ} {w : Vec d} (hχ0 : 0 ≤ χ w) (hχ : χ w ≤ 1)
    (hL : 0 ≤ L) (hψ : |ψ w| ≤ B) : |g1c_Psi χ ψ L w| ≤ B + 2 * L := by
  unfold g1c_Psi
  have h1 : |χ w * ψ w| ≤ B := by
    rw [abs_mul, abs_of_nonneg hχ0]
    calc χ w * |ψ w| ≤ 1 * B := mul_le_mul hχ hψ (abs_nonneg _) zero_le_one
      _ = B := one_mul _
  have h2 : |L * χ w| ≤ L := by
    rw [abs_mul, abs_of_nonneg hL, abs_of_nonneg hχ0]
    calc L * χ w ≤ L * 1 := mul_le_mul_of_nonneg_left hχ hL
      _ = L := mul_one _
  have h3 := abs_add_le (χ w * ψ w) (L * χ w)
  have h4 := abs_sub (χ w * ψ w + L * χ w) L
  rw [abs_of_nonneg hL] at h4
  linarith only [h1, h2, h3, h4]

/-- Bounds of the shear function. -/
theorem g1c_Psi_bounds {χ ψ : Vec d → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {A₁ A₂ M₁ M₂ ρ₃ L : ℝ} (hρ₃ : 0 ≤ ρ₃) (hA₂0 : 0 ≤ A₂)
    (hM₂0 : 0 ≤ M₂) (hL : 0 ≤ L) (hA₁ : ∀ y, ‖fderiv ℝ χ y‖ ≤ A₁)
    (hA₂ : ∀ y z, ‖fderiv ℝ χ y - fderiv ℝ χ z‖ ≤ A₂ * ‖y - z‖) (hχ01 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (hχ0 : ∀ y, ρ₃ ≤ ‖y‖ → χ y = 0) (hdχ0 : ∀ y, ρ₃ ≤ ‖y‖ → fderiv ℝ χ y = 0)
    (hM₁ : ∀ y, ‖fderiv ℝ ψ y‖ ≤ M₁) (hM₂ : ∀ y z, ‖fderiv ℝ ψ y - fderiv ℝ ψ z‖ ≤ M₂ * ‖y - z‖)
    (hψ0 : ψ 0 = 0) :
    ContDiff ℝ (⊤ : ℕ∞) (g1c_Psi χ ψ L) ∧
      (∀ y, ‖fderiv ℝ (g1c_Psi χ ψ L) y‖ ≤ (M₁ * ρ₃ * A₁ + M₁) + L * A₁) ∧
      (∀ y z, ‖fderiv ℝ (g1c_Psi χ ψ L) y - fderiv ℝ (g1c_Psi χ ψ L) z‖
        ≤ ((M₁ * ρ₃ * A₂ + 2 * A₁ * M₁ + M₂) + L * A₂) * ‖y - z‖) ∧
      ∀ w, ρ₃ ≤ ‖w‖ → g1c_Psi χ ψ L w = -L := by
  obtain ⟨hs, hb1, hb2, -⟩ := g1b_cutoff_mul hχ hψ hρ₃ hA₂0 hM₂0 hA₁ hA₂ hχ01 hχ0 hdχ0 hM₁ hM₂ hψ0
  refine ⟨g1c_Psi_contDiff hχ hψ L, fun y => ?_, fun y z => ?_, fun w hw => ?_⟩
  · rw [g1c_fderiv_Psi hχ hψ]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hL]
    have := mul_le_mul_of_nonneg_left (hA₁ y) hL
    linarith only [hb1 y, this]
  · rw [g1c_fderiv_Psi hχ hψ, g1c_fderiv_Psi hχ hψ]
    have : fderiv ℝ (fun z => χ z * ψ z) y + L • fderiv ℝ χ y
        - (fderiv ℝ (fun z => χ z * ψ z) z + L • fderiv ℝ χ z)
        = (fderiv ℝ (fun z => χ z * ψ z) y - fderiv ℝ (fun z => χ z * ψ z) z)
          + L • (fderiv ℝ χ y - fderiv ℝ χ z) := by
      rw [smul_sub]; abel
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hL]
    have h1 := mul_le_mul_of_nonneg_left (hA₂ y z) hL
    have h2 := hb2 y z
    linarith only [h1, h2]
  · exact g1c_Psi_eq_of_zero (hχ0 w hw)

end SuperdiffusionCLT.Section7
