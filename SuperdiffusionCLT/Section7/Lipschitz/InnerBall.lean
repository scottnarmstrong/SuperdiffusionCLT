/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Geometry.AtlasTransform
public import SuperdiffusionCLT.Section7.Analytic.Geometry.CubeFormDomainsB

/-!
# An inner cube of a uniformly `C^{1,1}` domain

In every cube of radius `ρ ≤ r` centred at a point of a uniformly `C^{1,1}` domain there is a
cube of radius `c ρ` contained in the domain; `c` depends on the slope bound only.  The volume of
the domain is therefore bounded below by a constant times `r ^ d`.
-/

@[expose] public section

open MeasureTheory Homogenization

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The point `q = x₀ - t e` has the same projection as `x₀` and height lowered by `t`. -/
theorem lip_inner_ball_shift {e : Vec d} (he : vecNormSq e = 1) (x₀ : Vec d) (t : ℝ) :
    vecDot e (x₀ - t • e) = vecDot e x₀ - t ∧
      (x₀ - t • e) - vecDot e (x₀ - t • e) • e = x₀ - vecDot e x₀ • e := by
  have h1 : vecDot e (x₀ - t • e) = vecDot e x₀ - t := by
    have : vecDot e e = 1 := he
    simp only [vecDot, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub,
      Finset.sum_sub_distrib] at this ⊢
    have h2 : ∑ i, e i * (t * e i) = t * ∑ i, e i * e i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [h2, this, mul_one]
  refine ⟨h1, ?_⟩
  rw [h1]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Points near `q = x₀ - t e` in the chart ball belong to the domain. -/
theorem lip_inner_ball_mem {W : Set (Vec d)} (hW : IsOpen W) {x₀ e : Vec d} {ψ : Vec d → ℝ}
    {R M t : ℝ} (he : vecNormSq e = 1) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hb : ∀ y, ‖fderiv ℝ ψ y‖ ≤ M) (hR : 0 < R)
    (hch : ∀ y ∈ Metric.ball x₀ R, (y ∈ W ↔ vecDot e y < ψ (y - vecDot e y • e)))
    (hx₀ : x₀ ∈ frontier W) {y : Vec d} (hyb : y ∈ Metric.ball x₀ R)
    (hlt : ‖y - (x₀ - t • e)‖ * ((d : ℝ) + (1 + d) * M + 1) < t) : y ∈ W := by
  have hg := vecDot_eq_of_mem_frontier hW hψ.continuous hch hx₀ (Metric.mem_ball_self hR)
  obtain ⟨hq1, hq2⟩ := lip_inner_ball_shift he x₀ t
  have h1 := abs_proj_comp_sub_le he hψ hb y (x₀ - t • e)
  have h2 := abs_vecDot_le he (y - (x₀ - t • e))
  rw [vecDot_sub, hq1] at h2
  rw [hq2] at h1
  have h3 := (abs_le.1 h1).1
  have h4 := (abs_le.1 h2).2
  refine (hch y hyb).2 ?_
  have hn := norm_nonneg (y - (x₀ - t • e))
  have hk : ‖y - (x₀ - t • e)‖ * ((d : ℝ) + (1 + d) * M + 1)
      = d * ‖y - (x₀ - t • e)‖ + (1 + d) * M * ‖y - (x₀ - t • e)‖ + ‖y - (x₀ - t • e)‖ := by
    ring
  linarith only [h3, h4, hg, hlt, hk, hn]

/-- The inner cube. -/
theorem lip_inner_ball (d : ℕ) [NeZero d] (M₁ : ℝ) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ∀ (W : Set (Vec d)) (r M₂ D : ℝ), IsUniformC11Domain W r M₁ M₂ D →
        ∀ z ∈ W, ∀ ρ : ℝ, 0 < ρ → ρ ≤ r →
          ∃ q : Vec d, Metric.ball q (c * ρ) ⊆ Metric.ball z ρ ∩ W := by
  set M : ℝ := max M₁ 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  have hL0 : 0 ≤ (d : ℝ) + (1 + d) * M := by positivity
  refine ⟨1 / (4 * ((d : ℝ) + (1 + d) * M + 1)), by positivity, ?_, ?_⟩
  · rw [div_le_one (by positivity)]
    linarith only [hL0]
  intro W r M₂ D hW z hz ρ hρ hρr
  have hc4 : 1 / (4 * ((d : ℝ) + (1 + d) * M + 1)) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith only [hL0]
  by_cases hin : Metric.ball z (ρ / 4) ⊆ W
  · refine ⟨z, fun y hy => ⟨?_, hin ?_⟩⟩
    · have : Metric.ball z (1 / (4 * ((d : ℝ) + (1 + d) * M + 1)) * ρ) ⊆ Metric.ball z ρ :=
        Metric.ball_subset_ball (by nlinarith only [hc4, hρ])
      exact this hy
    · refine Metric.ball_subset_ball ?_ hy
      nlinarith only [hc4, hρ]
  · obtain ⟨x₀, hx₀f, hx₀b⟩ := g1q_ball_inter_frontier hW.1 hz hin
    obtain ⟨e, ψ, he, hψ, hb, -, hch⟩ := hW.2.2.2 x₀ hx₀f
    have hb' : ∀ y, ‖fderiv ℝ ψ y‖ ≤ M := fun y => (hb y).trans (le_max_left _ _)
    have hx₀d : ‖x₀ - z‖ < ρ / 4 := by
      rw [← dist_eq_norm]; exact Metric.mem_ball.1 hx₀b
    have hqx : ‖(ρ / 4) • e‖ ≤ ρ / 4 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      calc ρ / 4 * ‖e‖ ≤ ρ / 4 * 1 :=
            mul_le_mul_of_nonneg_left (norm_le_one_of_vecNormSq he) (by positivity)
        _ = ρ / 4 := mul_one _
    have hsub : ∀ y, ‖y - (x₀ - (ρ / 4) • e)‖ < 1 / (4 * ((d : ℝ) + (1 + d) * M + 1)) * ρ →
        ‖y - x₀‖ < ρ / 2 := by
      intro y hy
      have : y - x₀ = (y - (x₀ - (ρ / 4) • e)) - (ρ / 4) • e := by abel
      rw [this]
      have h1 := norm_sub_le (y - (x₀ - (ρ / 4) • e)) ((ρ / 4) • e)
      have h2 : 1 / (4 * ((d : ℝ) + (1 + d) * M + 1)) * ρ ≤ 1 / 4 * ρ :=
        mul_le_mul_of_nonneg_right hc4 hρ.le
      linarith only [h1, h2, hqx, hy]
    refine ⟨x₀ - (ρ / 4) • e, fun y hy => ?_⟩
    rw [Metric.mem_ball, dist_eq_norm] at hy
    have hyx := hsub y hy
    have hyb : y ∈ Metric.ball x₀ r := by
      rw [Metric.mem_ball, dist_eq_norm]
      linarith only [hyx, hρr, hρ]
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm]
      have : y - z = (y - x₀) + (x₀ - z) := by abel
      rw [this]
      linarith only [norm_add_le (y - x₀) (x₀ - z), hyx, hx₀d, hρ]
    · refine lip_inner_ball_mem hW.1 he hψ hb' (R := r) (t := ρ / 4) hW.2.1 hch hx₀f hyb ?_
      have hpos : 0 < (d : ℝ) + (1 + d) * M + 1 := by positivity
      have : ‖y - (x₀ - (ρ / 4) • e)‖ * ((d : ℝ) + (1 + d) * M + 1)
          < 1 / (4 * ((d : ℝ) + (1 + d) * M + 1)) * ρ * ((d : ℝ) + (1 + d) * M + 1) :=
        mul_lt_mul_of_pos_right hy hpos
      have h2 : 1 / (4 * ((d : ℝ) + (1 + d) * M + 1)) * ρ * ((d : ℝ) + (1 + d) * M + 1)
          = ρ / 4 := by field_simp
      linarith only [this, h2]

/-- The volume of a uniformly `C^{1,1}` domain is at least a constant times `r ^ d`. -/
theorem lip_inner_ball_volume (d : ℕ) [NeZero d] (M₁ : ℝ) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (W : Set (Vec d)) (r M₂ D : ℝ), IsUniformC11Domain W r M₁ M₂ D → W.Nonempty →
        ENNReal.ofReal (c * r ^ d) ≤ volume W := by
  obtain ⟨c, hc, -, h⟩ := lip_inner_ball d M₁
  refine ⟨(2 * c) ^ d, by positivity, fun W r M₂ D hW ⟨z, hz⟩ => ?_⟩
  obtain ⟨q, hq⟩ := h W r M₂ D hW z hz r hW.2.1 le_rfl
  have hr := hW.2.1
  calc ENNReal.ofReal ((2 * c) ^ d * r ^ d) = volume (Metric.ball q (c * r)) := by
        rw [Real.volume_pi_ball q (by positivity), Fintype.card_fin, ← mul_pow,
          mul_assoc]
      _ ≤ volume W := measure_mono fun y hy => (hq hy).2

/-- Witness: the unit Euclidean ball is a uniformly `C^{1,1}` domain, with a slope bound `M₁`. -/
example [NeZero d] :
    ∃ r M₁ M₂ D : ℝ, IsUniformC11Domain (Section6.euclidBall (d := d) 1) r M₁ M₂ D ∧
      ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ z ∈ Section6.euclidBall (d := d) 1, ∀ ρ : ℝ, 0 < ρ → ρ ≤ r →
        ∃ q : Vec d, Metric.ball q (c * ρ) ⊆ Metric.ball z ρ ∩ Section6.euclidBall (d := d) 1 := by
  obtain ⟨r, M₁, M₂, D, h⟩ := isUniformC11Domain_euclidBall (d := d)
  obtain ⟨c, hc, hc1, hq⟩ := lip_inner_ball d M₁
  exact ⟨r, M₁, M₂, D, h, c, hc, hc1, fun z hz ρ hρ hρr => hq _ r M₂ D h z hz ρ hρ hρr⟩

end SuperdiffusionCLT.Section7
