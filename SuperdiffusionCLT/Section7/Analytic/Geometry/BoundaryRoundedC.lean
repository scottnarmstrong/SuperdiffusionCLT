/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Geometry.BoundaryRoundedB

/-!
# The shear preimage of a uniformly `C^{1,1}` domain: assembly

`Section7.g1b_isUniformC11Domain_shear_preimage`: the preimage `{y | shear e Ψ y ∈ H}` of a
uniformly `C^{1,1}` domain `H` is uniformly `C^{1,1}`, with explicit data, provided the frontier
charts of `H` over the cylinder `‖P y‖ < ρ + δ` have direction `±e` and `Ψ` is constant outside
the cylinder `‖w‖ < ρ`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization

variable {d : ℕ}

theorem g1b_isUniformC11Domain_shear_preimage {e : Vec d} (he : vecNormSq e = 1)
    {Ψ : Vec d → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) {K₁ K₂ c ρ δ : ℝ}
    (hK₁ : ∀ y, ‖fderiv ℝ Ψ y‖ ≤ K₁) (hK₂ : ∀ y z, ‖fderiv ℝ Ψ y - fderiv ℝ Ψ z‖ ≤ K₂ * ‖y - z‖)
    (hΨc : ∀ w, ρ ≤ ‖w‖ → Ψ w = c) (hδ : 0 < δ)
    {H : Set (Vec d)} {r M₁ M₂ D r₁ M₁' M₂' : ℝ}
    (hH : IsUniformC11Domain H r M₁ M₂ D) (hr₁ : 0 < r₁)
    (hI : ∀ q ∈ frontier H, ‖q - vecDot e q • e‖ < ρ + δ →
      ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ g1b_ChartDir H q r₁ M₁' M₂' (ε • e)) :
    IsUniformC11Domain {y | shear e Ψ y ∈ H}
      (min (r₁ / g1b_Lam d K₁) (min r (δ / (1 + d)))) (max (M₁' + K₁) M₁) (max (M₂' + K₂) M₂)
      (g1b_Lam d K₁ * D) := by
  obtain ⟨hopen, hr, hD, hch⟩ := hH
  have hK0 : 0 ≤ K₁ := (norm_nonneg _).trans (hK₁ 0)
  have hΛ := g1b_Lam_pos (d := d) hK0
  have hd : (0 : ℝ) < 1 + d := by positivity
  have hcont : Continuous Ψ := hΨ.continuous
  refine ⟨hopen.preimage (g1b_shear_continuous hcont), lt_min (div_pos hr₁ hΛ)
    (lt_min hr (div_pos hδ hd)), fun y hy y' hy' => ?_, fun p hp => ?_⟩
  · have h1 := norm_shear_sub_le he hK0 (ψ := -Ψ) (fun a b => by
      have := abs_sub_le_of_fderiv_bound hΨ hK₁ a b
      have e1 : (-Ψ) a - (-Ψ) b = -(Ψ a - Ψ b) := by simp only [Pi.neg_apply]; ring
      rw [e1, abs_neg]
      exact this) (shear e Ψ y) (shear e Ψ y')
    have h2 : ∀ z, shear e (-Ψ) (shear e Ψ z) = z := fun z =>
      congrFun (shear_neg_left_inverse he Ψ) z
    rw [h2, h2] at h1
    unfold g1b_Lam at *
    calc ‖y - y'‖ ≤ (1 + (1 + d) * K₁) * ‖shear e Ψ y - shear e Ψ y'‖ := h1
      _ ≤ (1 + (1 + d) * K₁) * D := mul_le_mul_of_nonneg_left (hD _ hy _ hy') hΛ.le
  · have hq : shear e Ψ p ∈ frontier H := by
      have := (g1b_shearHomeo he hcont).preimage_frontier H
      have h' : p ∈ frontier ((g1b_shearHomeo he hcont) ⁻¹' H) := hp
      rw [← this] at h'
      exact h'
    have hPq : shear e Ψ p - vecDot e (shear e Ψ p) • e = p - vecDot e p • e := proj_shear he Ψ p
    by_cases hz : ‖p - vecDot e p • e‖ < ρ + δ
    · rw [← hPq] at hz
      obtain ⟨ε, hε, hdir⟩ := hI _ hq hz
      have := (g1b_chartDir_shear he hε hΨ hK₁ hK₂ hdir).hasC11ChartAt
      exact this.mono (min_le_left _ _) (le_max_left _ _) (le_max_left _ _)
    · have hz' : ρ + δ ≤ ‖p - vecDot e p • e‖ := not_lt.1 hz
      have := g1b_chart_shear_far he hΨc hδ hz' (hch _ hq)
      exact this.mono (min_le_right _ _) (le_max_right _ _) (le_max_right _ _)

end SuperdiffusionCLT.Section7
