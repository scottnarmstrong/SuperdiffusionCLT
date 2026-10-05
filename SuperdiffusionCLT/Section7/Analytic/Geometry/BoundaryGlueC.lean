/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Geometry.BoundaryGlueB

/-!
# The sheared model domain with explicit data

`Section7.g1c_uniform_shear`: the shear preimage of the model domain is uniformly `C^{1,1}`, with
data computed from the data `(rH, M₁H, M₂H, DH)` of the model domain, the bounds `(K₁, K₂)` of the
shear function and the geometry of the cylinder. The data do not depend on the axis `e` once the
data of the model domain do not.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization

variable {d : ℕ}

/-- The radius of the flat charts. -/
noncomputable def g1c_r₁ (d : ℕ) (h ρ δ ζ : ℝ) : ℝ :=
  min ((ζ - (ρ + δ)) / (1 + d)) (h / (1 + d))

theorem g1c_r₁_pos {h ρ δ ζ : ℝ} (hh : 0 < h) (hζ : ρ + δ < ζ) : 0 < g1c_r₁ d h ρ δ ζ := by
  have hd1 : (0 : ℝ) < 1 + d := by positivity
  exact lt_min (div_pos (by linarith only [hζ]) hd1) (div_pos hh hd1)

theorem g1c_uniform_shear {e : Vec d} (he : vecNormSq e = 1) {a h : ℝ} (ha : 0 < a)
    (hh : 0 < h) {Ψ : Vec d → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) {K₁ K₂ c ρ δ ζ : ℝ}
    (hK₁ : ∀ y, ‖fderiv ℝ Ψ y‖ ≤ K₁) (hK₂ : ∀ y z, ‖fderiv ℝ Ψ y - fderiv ℝ Ψ z‖ ≤ K₂ * ‖y - z‖)
    (hΨc : ∀ w, ρ ≤ ‖w‖ → Ψ w = c) (hδ : 0 < δ) (hζ : ρ + δ < ζ)
    (hζ2 : d * ζ ^ 2 ≤ a ^ 2 / 16) {rH M₁H M₂H DH : ℝ}
    (hH : IsUniformC11Domain (g1b_H e a h) rH M₁H M₂H DH) :
    IsUniformC11Domain {y | shear e Ψ y ∈ g1b_H e a h}
      (min (g1c_r₁ d h ρ δ ζ / g1b_Lam d K₁) (min rH (δ / (1 + d)))) (max (0 + K₁) M₁H)
      (max (0 + K₂) M₂H) (g1b_Lam d K₁ * DH) := by
  have hd1 : (0 : ℝ) < 1 + d := by positivity
  have hr₁ : 0 < g1c_r₁ d h ρ δ ζ := g1c_r₁_pos hh hζ
  have h1 : (1 + (d : ℝ)) * g1c_r₁ d h ρ δ ζ ≤ ζ - (ρ + δ) := by
    have := min_le_left ((ζ - (ρ + δ)) / (1 + d)) (h / (1 + d))
    rw [← g1c_r₁, le_div_iff₀ hd1] at this
    linarith only [this]
  have h2 : (1 + (d : ℝ)) * g1c_r₁ d h ρ δ ζ ≤ h := by
    have := min_le_right ((ζ - (ρ + δ)) / (1 + d)) (h / (1 + d))
    rw [← g1c_r₁, le_div_iff₀ hd1] at this
    linarith only [this]
  have hdr : (d : ℝ) * g1c_r₁ d h ρ δ ζ ≤ h := by
    have : (d : ℝ) * g1c_r₁ d h ρ δ ζ ≤ (1 + d) * g1c_r₁ d h ρ δ ζ := by nlinarith only [hr₁]
    linarith only [this, h2]
  exact g1b_isUniformC11Domain_shear_preimage he hΨ hK₁ hK₂ hΨc hδ hH hr₁
    (M₁' := 0) (M₂' := 0) fun q hq hPq => g1b_flat_chartDir he ha hh hr₁ (by linarith only [h1])
      hζ2 hdr hq hPq

end SuperdiffusionCLT.Section7
