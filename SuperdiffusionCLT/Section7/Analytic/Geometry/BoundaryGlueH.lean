/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Geometry.BoundaryGlueF

/-!
# Rescaling about a boundary point

The maps `F y = s⁻¹ • (y - x₀)` (written `s⁻¹ • y + (-(s⁻¹ • x₀))`) and `G w = s • w + x₀` are
inverse affine homeomorphisms. Their elementary properties (membership in images, balls,
frontiers) used to transport the normalized glued domain back to the scale `s` about `x₀`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization

variable {d : ℕ}

/-- The normalizing map `y ↦ s⁻¹ • y + (-(s⁻¹ • x₀))`. -/
noncomputable def g1c_F (s : ℝ) (x₀ : Vec d) (y : Vec d) : Vec d := s⁻¹ • y + (-(s⁻¹ • x₀))

/-- The inverse map `w ↦ s • w + x₀`. -/
def g1c_G (s : ℝ) (x₀ : Vec d) (w : Vec d) : Vec d := s • w + x₀

theorem g1c_F_eq (s : ℝ) (x₀ y : Vec d) : g1c_F s x₀ y = s⁻¹ • (y - x₀) := by
  unfold g1c_F
  rw [smul_sub, sub_eq_add_neg]

theorem g1c_G_F {s : ℝ} (hs : s ≠ 0) (x₀ y : Vec d) : g1c_G s x₀ (g1c_F s x₀ y) = y := by
  rw [g1c_F_eq]
  unfold g1c_G
  rw [smul_smul, mul_inv_cancel₀ hs, one_smul, sub_add_cancel]

theorem g1c_F_G {s : ℝ} (hs : s ≠ 0) (x₀ w : Vec d) : g1c_F s x₀ (g1c_G s x₀ w) = w := by
  rw [g1c_F_eq]
  unfold g1c_G
  rw [add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hs, one_smul]

theorem g1c_F_x₀ {s : ℝ} (x₀ : Vec d) : g1c_F s x₀ x₀ = 0 := by
  rw [g1c_F_eq, sub_self, smul_zero]

theorem g1c_mem_image_F {s : ℝ} (hs : s ≠ 0) (x₀ : Vec d) (S : Set (Vec d)) (w : Vec d) :
    w ∈ g1c_F s x₀ '' S ↔ g1c_G s x₀ w ∈ S := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [g1c_G_F hs]
  · intro h
    exact ⟨_, h, g1c_F_G hs x₀ w⟩

theorem g1c_mem_image_G {s : ℝ} (hs : s ≠ 0) (x₀ : Vec d) (S : Set (Vec d)) (y : Vec d) :
    y ∈ g1c_G s x₀ '' S ↔ g1c_F s x₀ y ∈ S := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    rwa [g1c_F_G hs]
  · intro h
    exact ⟨_, h, g1c_G_F hs x₀ y⟩

theorem g1c_image_F_G {s : ℝ} (hs : s ≠ 0) (x₀ : Vec d) (S : Set (Vec d)) :
    g1c_F s x₀ '' (g1c_G s x₀ '' S) = S := by
  ext w
  rw [g1c_mem_image_F hs, g1c_mem_image_G hs, g1c_F_G hs]

theorem g1c_norm_F {s : ℝ} (hs : 0 < s) (x₀ y : Vec d) : ‖g1c_F s x₀ y‖ = s⁻¹ * ‖y - x₀‖ := by
  rw [g1c_F_eq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hs)]

theorem g1c_mem_ball_F {s : ℝ} (hs : 0 < s) (x₀ y : Vec d) {c : ℝ} :
    y ∈ Metric.ball x₀ (c * s) ↔ g1c_F s x₀ y ∈ Metric.ball (0 : Vec d) c := by
  rw [mem_ball_zero_iff, g1c_norm_F hs, Metric.mem_ball, dist_eq_norm, ← div_eq_inv_mul,
    div_lt_iff₀ hs]

/-- The affine homeomorphism `G`. -/
noncomputable def g1c_homeoG {s : ℝ} (hs : s ≠ 0) (x₀ : Vec d) : Vec d ≃ₜ Vec d :=
  affineHomeo hs x₀

/-- Frontier points of the rescaled set correspond to frontier points. -/
theorem g1c_frontier_G {s : ℝ} (hs : s ≠ 0) (x₀ : Vec d) (S : Set (Vec d)) :
    frontier (g1c_G s x₀ '' S) = g1c_G s x₀ '' frontier S := by
  have := (g1c_homeoG hs x₀).image_frontier S
  exact this.symm

theorem g1c_frontier_F {s : ℝ} (hs : s ≠ 0) (x₀ : Vec d) (S : Set (Vec d)) :
    frontier (g1c_F s x₀ '' S) = g1c_F s x₀ '' frontier S := by
  have h := (affineHomeo (inv_ne_zero hs) (-(s⁻¹ • x₀))).image_frontier S
  exact h.symm

end SuperdiffusionCLT.Section7
