/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Geometry.DomainPoincareF

/-!
# Rounded cubes of arbitrary real scale

`g1q_V d N l z` is the superellipsoid `{∑ xᵢ^(2N) < 1}` dilated by `l > 0` and translated to `z`.
It lies between the cubes of half-widths `l / 3` and `l` about `z`, carries the mean-value
Poincare inequality with a constant proportional to `l` that does not depend on `l` or `z`,
and its rescaling by any `c > 0` is a dilate of the fixed model, so that its uniform `C^{1,1}` data
are those of the model. The monotonicity of `IsUniformC11Domain` in its parameters is recorded.
-/

@[expose] public section

open MeasureTheory Homogenization Set
open scoped Pointwise

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem g1q_uniform_mono {U : Set (Vec d)} {r M₁ M₂ D : ℝ}
    (h : IsUniformC11Domain U r M₁ M₂ D) {r' M₁' M₂' D' : ℝ} (hr0 : 0 < r') (hr : r' ≤ r)
    (h1 : M₁ ≤ M₁') (h2 : M₂ ≤ M₂') (hD : D ≤ D') : IsUniformC11Domain U r' M₁' M₂' D' := by
  obtain ⟨hopen, -, hdiam, hch⟩ := h
  exact ⟨hopen, hr0, fun x hx y hy => (hdiam x hx y hy).trans hD,
    fun x hx => (hch x hx).mono hr h1 h2⟩

/-- The rounded cube of half-width `l` centred at `z`. -/
def g1q_V (d N : ℕ) (l : ℝ) (z : Vec d) : Set (Vec d) :=
  (fun y => l • y + z) '' g1_superE d N

theorem g1q_isOpen {N : ℕ} {l : ℝ} (hl : 0 < l) (z : Vec d) : IsOpen (g1q_V d N l z) := by
  have : g1q_V d N l z = affineHomeo hl.ne' z '' g1_superE d N := rfl
  rw [this]
  exact (affineHomeo hl.ne' z).isOpenMap _ (g1_isOpen_superE N)

theorem g1q_subset_ball {N : ℕ} (hN : 1 ≤ N) {l : ℝ} (hl : 0 < l) (z : Vec d) :
    g1q_V d N l z ⊆ Metric.ball z l := by
  rintro _ ⟨u, hu, rfl⟩
  have h1 := g1_superE_subset_ball hN hu
  rw [mem_ball_zero_iff] at h1
  rw [mem_ball_iff_norm, add_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_pos hl]
  exact mul_lt_of_lt_one_right hl h1

theorem g1q_ball_subset [NeZero d] {N : ℕ} (hN : 1 ≤ N) (hd : d ≤ 9 ^ N) {l : ℝ} (hl : 0 < l)
    (z : Vec d) : Metric.ball z (l / 3) ⊆ g1q_V d N l z := by
  intro w hw
  refine ⟨l⁻¹ • (w - z), g1_ball_subset_superE hN hd ?_, ?_⟩
  · rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hl)]
    rw [mem_ball_iff_norm] at hw
    rw [inv_mul_lt_iff₀ hl]
    linarith only [hw]
  · show l • (l⁻¹ • (w - z)) + z = w
    rw [smul_smul, mul_inv_cancel₀ hl.ne', one_smul]
    abel

theorem g1q_convex (N : ℕ) (l : ℝ) (z : Vec d) : Convex ℝ (g1q_V d N l z) := by
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ a b ha hb hab
  refine ⟨a • p + b • q, a10_convex_superE N hp hq ha hb hab, ?_⟩
  show l • (a • p + b • q) + z = a • (l • p + z) + b • (l • q + z)
  have hz : z = (a + b) • z := by rw [hab, one_smul]
  conv_lhs => rw [hz]
  simp only [smul_add, add_smul, smul_smul]
  module

theorem g1q_isStarBallDomain [NeZero d] {N : ℕ} (hN : 1 ≤ N) (hd : d ≤ 9 ^ N) {l : ℝ} (hl : 0 < l)
    (z : Vec d) : IsStarBallDomain (g1q_V d N l z) z (l / 3) (2 * l) := by
  refine a10_isStarBallDomain_of_convex (g1q_isOpen hl z) (g1q_convex N l z) (by positivity)
    (g1q_ball_subset hN hd hl z) ?_
  intro x hx y hy
  have h1 := g1q_subset_ball hN hl z hx
  have h2 := g1q_subset_ball hN hl z hy
  rw [Metric.mem_ball, dist_eq_norm] at h1 h2
  calc ‖x - y‖ = ‖(x - z) - (y - z)‖ := by rw [sub_sub_sub_cancel_right]
    _ ≤ ‖x - z‖ + ‖y - z‖ := norm_sub_le _ _
    _ ≤ 2 * l := by linarith only [h1, h2]

/-- **Poincare inequality on the rounded cubes of real scale**, with a constant proportional to
the scale. -/
theorem g1q_poincare [NeZero d] {N : ℕ} (hN : 1 ≤ N) (hd : d ≤ 9 ^ N) {l : ℝ} (hl : 0 < l)
    (z : Vec d) (u : H1Function (g1q_V d N l z)) :
    eLpNorm (fun x => u.toFun x - (∫ y in g1q_V d N l z, u.toFun y) /
        (volume (g1q_V d N l z)).toReal) 2 (volume.restrict (g1q_V d N l z)) ≤
      ENNReal.ofReal (Real.sqrt (4 * (d : ℝ) ^ 2 * 2 ^ d * (1 + 6 ^ d)) * (2 * l)) *
        eLpNorm (fun x => ‖u.grad x‖) 2 (volume.restrict (g1q_V d N l z)) := by
  have h := a10_poincare_starBall (g1q_isStarBallDomain hN hd hl z) u
  have hr : (2 * l) / (l / 3) = 6 := by field_simp; ring
  rwa [hr] at h

theorem g1q_rescale (N : ℕ) {l c : ℝ} (z : Vec d) :
    (fun y => c⁻¹ • (y - z)) '' g1q_V d N l z = (l / c) • g1_superE d N := by
  unfold g1q_V
  rw [Set.image_image, ← Set.image_smul]
  refine Set.image_congr fun u _ => ?_
  simp only [add_sub_cancel_right, smul_smul]
  congr 1
  rw [inv_mul_eq_div]

theorem g1q_uniform {N : ℕ} {r M₁ M₂ D : ℝ} (hE : IsUniformC11Domain (g1_superE d N) r M₁ M₂ D)
    {l c : ℝ} (hl : 0 < l) (hc : 0 < c) (z : Vec d) :
    IsUniformC11Domain ((fun y => c⁻¹ • (y - z)) '' g1q_V d N l z) (l / c * r) M₁ (M₂ / (l / c))
      (l / c * D) := by
  rw [g1q_rescale N z]
  exact hE.smul (div_pos hl hc)

/-- Buffer from the artificial boundary. -/
theorem g1q_buffer [NeZero d] {N : ℕ} (hN : 1 ≤ N) (hd : d ≤ 9 ^ N) {l : ℝ} (hl : 0 < l)
    (z : Vec d) {p q : Vec d} {ρ : ℝ} (hp : p ∈ Metric.ball z ρ)
    (hq : q ∈ frontier (g1q_V d N l z)) : l / 3 - ρ ≤ dist p q := by
  have hqV : q ∉ g1q_V d N l z := by
    rw [(g1q_isOpen hl z).frontier_eq] at hq
    exact hq.2
  have hq' : q ∉ Metric.ball z (l / 3) := fun h => hqV (g1q_ball_subset hN hd hl z h)
  rw [Metric.mem_ball] at hp hq'
  have h1 := dist_triangle z p q
  rw [dist_comm z p] at h1
  have h2 : l / 3 ≤ dist z q := by
    rw [dist_comm]
    exact not_lt.1 hq'
  linarith only [h1, h2, hp]

end SuperdiffusionCLT.Section7
