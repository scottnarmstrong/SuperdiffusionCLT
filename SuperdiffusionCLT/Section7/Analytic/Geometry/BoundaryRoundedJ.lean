/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Geometry.BoundaryRoundedI
public import SuperdiffusionCLT.Section7.Analytic.Geometry.BoundaryRoundedC

/-!
# The model domain is smooth, and flat near the axis

* `Section7.g1b_isSmoothBoundedDomain_H`: the model domain is a smooth bounded domain.
* `Section7.g1b_flat_chartDir`: over the cylinder `‖P q‖ < κ` the frontier charts are the constant
  graphs in the direction `±e` (these are the charts that survive the shear).
* `Section7.g1b_exists_uniform_H`: uniform `C^{1,1}` data of the model domain.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization

variable {d : ℕ}

theorem g1b_isSmoothBoundedDomain_H {e : Vec d} (he : vecNormSq e = 1) {a h : ℝ} (ha : 0 < a)
    (hh : 0 < h) : IsSmoothBoundedDomain (g1b_H e a h) := by
  refine ⟨g1b_isOpen_H e a h, g1b_isConnected_H he, g1b_isBoundedDomain_H he ha hh, fun x hx => ?_⟩
  by_cases hv : 1 / 8 < g1b_v e h x
  · have hne : vecDot e x + h ≠ 0 := by
      intro h0
      have : g1b_v e h x = 0 := by unfold g1b_v; rw [h0]; simp
      linarith only [hv, this]
    by_cases hpos : 0 < vecDot e x + h
    · obtain ⟨ψ, W, r, hr, hW, hψ, hch⟩ := g1b_S_chart (σ := 1) hh (Or.inl rfl) hx hv
        (by rw [one_mul]; exact hpos)
      exact ⟨(1 : ℝ) • e, ψ, W, r, g1b_vecNormSq_smul (Or.inl rfl) he, hr, hW, hψ, hch⟩
    · have hneg : vecDot e x + h < 0 := lt_of_le_of_ne (not_lt.1 hpos) hne
      obtain ⟨ψ, W, r, hr, hW, hψ, hch⟩ := g1b_S_chart (σ := -1) hh (Or.inr rfl) hx hv
        (by linarith only [hneg])
      exact ⟨(-1 : ℝ) • e, ψ, W, r, g1b_vecNormSq_smul (Or.inr rfl) he, hr, hW, hψ, hch⟩
  · obtain ⟨e', ψ, W, r, he', hr, hW, hψ, hch⟩ := g1b_R_chart he ha hx (not_lt.1 hv)
    exact ⟨e', ψ, W, r, he', hr, hW, hψ, hch⟩

theorem g1b_vecNormSq_le (w : Vec d) : vecNormSq w ≤ d * ‖w‖ ^ 2 := by
  unfold vecNormSq vecDot
  calc ∑ i, w i * w i ≤ ∑ _i : Fin d, ‖w‖ ^ 2 := Finset.sum_le_sum fun i _ => by
        have h1 : |w i| ≤ ‖w‖ := by simpa using norm_le_pi_norm w i
        calc w i * w i = |w i| ^ 2 := by rw [sq_abs]; ring
          _ ≤ ‖w‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    _ = d * ‖w‖ ^ 2 := by simp

theorem g1b_flat_chartDir {e : Vec d} (he : vecNormSq e = 1) {a h : ℝ} (ha : 0 < a) (hh : 0 < h)
    {ζ κ r₁ : ℝ} (hr₁ : 0 < r₁) (hκ : κ + (1 + d) * r₁ ≤ ζ) (hζ : d * ζ ^ 2 ≤ a ^ 2 / 16)
    (hdr : d * r₁ ≤ h) {q : Vec d} (hq : q ∈ frontier (g1b_H e a h))
    (hPq : ‖q - vecDot e q • e‖ < κ) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ g1b_ChartDir (g1b_H e a h) q r₁ 0 0 (ε • e) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hflat : ∀ y : Vec d, ‖y - vecDot e y • e‖ < ζ → g1b_u e a y ≤ 1 / 16 := fun y hy => by
    unfold g1b_u
    rw [div_le_iff₀ (by positivity)]
    have h1 := g1b_vecNormSq_le (y - vecDot e y • e)
    have h2 : ‖y - vecDot e y • e‖ ^ 2 ≤ ζ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hy.le 2
    nlinarith only [h1, h2, hζ, hd0]
  have hq1 : ‖q - vecDot e q • e‖ < ζ := by
    have : 0 ≤ (1 + (d : ℝ)) * r₁ := by positivity
    linarith only [hPq, hκ, this]
  have hQ := g1b_frontier_Q hq
  have hQ' : g1b_phi (g1b_u e a q) + g1b_phi (g1b_v e h q) = 1 := hQ
  rw [g1b_phi_zero (hflat q hq1), zero_add] at hQ'
  have hv1 := g1b_phi_eq_one (g1b_v_nonneg e h q) hQ'
  have hq2 : (vecDot e q + h) ^ 2 = h ^ 2 := by
    unfold g1b_v at hv1
    exact (div_eq_one_iff_eq (by positivity)).1 hv1
  have hdot : ∀ y ∈ Metric.ball q r₁, |vecDot e y - vecDot e q| ≤ h := fun y hy => by
    have h1 := abs_vecDot_le he (y - q)
    rw [vecDot_sub] at h1
    have h2 : ‖y - q‖ < r₁ := by rwa [Metric.mem_ball, dist_eq_norm] at hy
    have : (d : ℝ) * ‖y - q‖ ≤ d * r₁ := mul_le_mul_of_nonneg_left h2.le hd0
    linarith only [h1, this, hdr]
  have hmem : ∀ y ∈ Metric.ball q r₁, (y ∈ g1b_H e a h ↔
      -(2 * h) < vecDot e y ∧ vecDot e y < 0) := fun y hy => by
    refine g1b_mem_H_flat hh (hflat y ?_)
    have h1 := norm_proj_sub_le he y q
    have h2 : ‖y - q‖ < r₁ := by rwa [Metric.mem_ball, dist_eq_norm] at hy
    have h3 : (1 + (d : ℝ)) * ‖y - q‖ ≤ (1 + d) * r₁ :=
      mul_le_mul_of_nonneg_left h2.le (by positivity)
    have h4 := norm_sub_norm_le (y - vecDot e y • e) (q - vecDot e q • e)
    linarith only [h1, h3, h4, hPq, hκ]
  have hcases : vecDot e q = 0 ∨ vecDot e q = -(2 * h) := by
    have : (vecDot e q + h - h) * (vecDot e q + h + h) = 0 := by nlinarith only [hq2]
    rcases mul_eq_zero.1 this with h0 | h0
    · left; linarith only [h0]
    · right; linarith only [h0]
  rcases hcases with h0 | h0
  · refine ⟨1, Or.inl rfl, g1b_vecNormSq_smul (Or.inl rfl) he, fun _ => 0, contDiff_const,
      fun y => by simp, fun y z => by simp, fun y hy => ?_⟩
    rw [hmem y hy, g1b_vecDot_smul]
    have := hdot y hy
    rw [h0, sub_zero] at this
    have h5 := (abs_le.1 this).1
    constructor
    · intro h'; linarith only [h']
    · intro h'; constructor <;> linarith only [h', h5, hh]
  · refine ⟨-1, Or.inr rfl, g1b_vecNormSq_smul (Or.inr rfl) he, fun _ => 2 * h, contDiff_const,
      fun y => by simp, fun y z => by simp, fun y hy => ?_⟩
    rw [hmem y hy, g1b_vecDot_smul]
    have := hdot y hy
    rw [h0] at this
    have h5 := (abs_le.1 this).2
    constructor
    · intro h'; linarith only [h'.1]
    · intro h'; constructor <;> linarith only [h', h5, hh]

/-- Uniform `C^{1,1}` data of the model domain. -/
theorem g1b_exists_uniform_H {e : Vec d} (he : vecNormSq e = 1) {a h : ℝ} (ha : 0 < a)
    (hh : 0 < h) : ∃ r M₁ M₂ D : ℝ, IsUniformC11Domain (g1b_H e a h) r M₁ M₂ D :=
  exists_isUniformC11Domain_of_isSmoothBoundedDomain (g1b_isSmoothBoundedDomain_H he ha hh)

end SuperdiffusionCLT.Section7
