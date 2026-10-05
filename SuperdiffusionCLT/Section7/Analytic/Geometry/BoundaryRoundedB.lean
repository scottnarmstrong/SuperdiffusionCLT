/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Geometry.BoundaryRounded

/-!
# The shear preimage of a uniformly `C^{1,1}` domain

* `Section7.g1b_hasC11ChartAt_congr`: charts only see the set on a ball.
* `Section7.g1b_isUniformC11Domain_shear_preimage`: if the frontier charts of `H` over the
  cylinder `‖P y‖ < ρ + δ` have direction `±e`, and `Ψ` is constant for `‖w‖ ≥ ρ`, then
  `{y | shear e Ψ y ∈ H}` is a uniformly `C^{1,1}` domain.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization

variable {d : ℕ}

theorem g1b_hasC11ChartAt_congr {U U' : Set (Vec d)} {x : Vec d} {r ρ M₁ M₂ : ℝ}
    (h : HasC11ChartAt U x r M₁ M₂)
    (hUU : ∀ y ∈ Metric.ball x ρ, (y ∈ U ↔ y ∈ U')) :
    HasC11ChartAt U' x (min r ρ) M₁ M₂ := by
  obtain ⟨e, ψ, he, hψ, hb1, hb2, hU⟩ := h
  refine ⟨e, ψ, he, hψ, hb1, hb2, fun y hy => ?_⟩
  rw [← hUU y (Metric.ball_subset_ball (min_le_right _ _) hy)]
  exact hU y (Metric.ball_subset_ball (min_le_left _ _) hy)

/-- Away from the cylinder where `Ψ` varies, the shear is a translation and charts translate. -/
theorem g1b_chart_shear_far {e : Vec d} (he : vecNormSq e = 1) {Ψ : Vec d → ℝ} {c ρ δ : ℝ}
    (hΨc : ∀ w, ρ ≤ ‖w‖ → Ψ w = c) (hδ : 0 < δ) {H : Set (Vec d)} {p : Vec d}
    {r M₁ M₂ : ℝ} (hp : ρ + δ ≤ ‖p - vecDot e p • e‖)
    (h : HasC11ChartAt H (shear e Ψ p) r M₁ M₂) :
    HasC11ChartAt {y | shear e Ψ y ∈ H} p (min r (δ / (1 + d))) M₁ M₂ := by
  have hpc : Ψ (p - vecDot e p • e) = c := hΨc _ (by linarith only [hp, hδ])
  have hq : shear e Ψ p = p - c • e := by unfold shear; rw [hpc]
  have h1 := h.affine (l := 1) one_pos (c • e)
  rw [hq, one_smul, sub_add_cancel] at h1
  have hd : (0 : ℝ) < 1 + d := by positivity
  refine (g1b_hasC11ChartAt_congr (ρ := δ / (1 + d)) h1 ?_).mono (by rw [one_mul]) le_rfl
    (by rw [div_one])
  intro y hy
  have hyc : Ψ (y - vecDot e y • e) = c := by
    refine hΨc _ ?_
    have h2 := norm_proj_sub_le he y p
    have h3 : ‖y - p‖ < δ / (1 + d) := by rwa [Metric.mem_ball, dist_eq_norm] at hy
    have h4 : (1 + d) * ‖y - p‖ < δ := by
      have := (lt_div_iff₀ hd).1 h3
      linarith only [this]
    have h5 := norm_sub_norm_le (p - vecDot e p • e) (y - vecDot e y • e)
    have h6 := norm_sub_rev (p - vecDot e p • e) (y - vecDot e y • e)
    linarith only [h2, h4, h5, h6, hp]
  have hshear : shear e Ψ y = y - c • e := by unfold shear; rw [hyc]
  show y ∈ (fun y => (1 : ℝ) • y + c • e) '' H ↔ shear e Ψ y ∈ H
  rw [hshear]
  constructor
  · rintro ⟨z, hz, hzy⟩
    have : z = y - c • e := by rw [← hzy]; simp
    rw [← this]
    exact hz
  · intro hH
    exact ⟨y - c • e, hH, by simp⟩

end SuperdiffusionCLT.Section7
