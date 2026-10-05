/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Geometry.RoundedCubeD

/-!
# The rounded cube of the interior approximation

`ia_V d N m y` is the superellipsoid `{∑ xᵢ^(2N) < 1}` dilated by `3^m / 4` and translated to `y`.
It lies in the sup-ball of radius `3^m / 4` (so the mollification at the scale `3^{m-⌈N log m⌉}`
only sees `u` inside `□_m`) and contains the sup-ball of radius `3^m / 5`, hence `□_{m-1}`
with a margin.  Its rescaling is a fixed model, so the uniform `C^{1,1}` data are independent of
`m` and `y`.
-/

@[expose] public section

open Homogenization Pointwise

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The rounded cube of scale `3^m` centred at `y`. -/
def ia_V (d N m : ℕ) (y : Vec d) : Set (Vec d) :=
  (fun w => ((3 : ℝ) ^ m / 4) • w + y) '' g1_superE d N

theorem ia_V_isOpen {N : ℕ} (m : ℕ) (y : Vec d) : IsOpen (ia_V d N m y) := by
  have hl : ((3 : ℝ) ^ m / 4) ≠ 0 := by positivity
  have : ia_V d N m y = affineHomeo hl y '' g1_superE d N := rfl
  rw [this]
  exact (affineHomeo hl y).isOpenMap _ (g1_isOpen_superE N)

theorem ia_V_subset_ball {N : ℕ} (hN : 1 ≤ N) (m : ℕ) (y : Vec d) :
    ia_V d N m y ⊆ Metric.ball y ((3 : ℝ) ^ m / 4) := by
  rintro _ ⟨u, hu, rfl⟩
  have hl : (0 : ℝ) < (3 : ℝ) ^ m / 4 := by positivity
  have h1 := g1_superE_subset_ball hN hu
  rw [mem_ball_zero_iff] at h1
  rw [mem_ball_iff_norm, add_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_pos hl]
  exact mul_lt_of_lt_one_right hl h1

/-- The exponent: the cube of half-width `4/5` lies in the superellipsoid. -/
theorem ia_exists_exponent (d : ℕ) : ∃ N : ℕ, 1 ≤ N ∧ (d : ℝ) * (4 / 5 : ℝ) ^ (2 * N) < 1 := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (d + 1) by positivity)
    (show (4 / 5 : ℝ) ^ 2 < 1 by norm_num)
  refine ⟨N + 1, by omega, ?_⟩
  have h1 : (4 / 5 : ℝ) ^ (2 * (N + 1)) ≤ ((4 / 5 : ℝ) ^ 2) ^ N := by
    rw [← pow_mul]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have h2 : (d : ℝ) * ((4 / 5 : ℝ) ^ 2) ^ N < 1 := by
    have := mul_lt_mul_of_pos_left hN (show (0 : ℝ) < d + 1 by positivity)
    rw [mul_one_div_cancel (by positivity)] at this
    nlinarith only [this, pow_nonneg (show (0 : ℝ) ≤ (4 / 5 : ℝ) ^ 2 by norm_num) N, (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  calc (d : ℝ) * (4 / 5 : ℝ) ^ (2 * (N + 1)) ≤ d * ((4 / 5 : ℝ) ^ 2) ^ N :=
        mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg d)
    _ < 1 := h2

theorem ia_ball_subset_superE [NeZero d] {N : ℕ} (hN : 1 ≤ N) (hd : (d : ℝ) * (4 / 5 : ℝ) ^ (2 * N) < 1) :
    Metric.ball (0 : Vec d) (4 / 5) ⊆ g1_superE d N := by
  intro y hy
  rw [mem_ball_zero_iff, pi_norm_lt_iff (by norm_num)] at hy
  have hlt : ∀ i, y i ^ (2 * N) < (4 / 5 : ℝ) ^ (2 * N) := fun i => by
    rw [← Even.pow_abs (even_two_mul N)]
    have := hy i
    rw [Real.norm_eq_abs] at this
    exact pow_lt_pow_left₀ this (abs_nonneg _) (by omega)
  have hsum : g1_P N y < ∑ _i : Fin d, (4 / 5 : ℝ) ^ (2 * N) :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => hlt i
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  exact lt_trans hsum hd

theorem ia_ball_subset_V [NeZero d] {N : ℕ} (hN : 1 ≤ N)
    (hd : (d : ℝ) * (4 / 5 : ℝ) ^ (2 * N) < 1) (m : ℕ) (y : Vec d) :
    Metric.ball y ((3 : ℝ) ^ m / 5) ⊆ ia_V d N m y := by
  intro w hw
  have hl : (0 : ℝ) < (3 : ℝ) ^ m / 4 := by positivity
  refine ⟨((3 : ℝ) ^ m / 4)⁻¹ • (w - y), ia_ball_subset_superE hN hd ?_, ?_⟩
  · rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hl)]
    rw [mem_ball_iff_norm] at hw
    rw [inv_mul_lt_iff₀ hl]
    linarith only [hw]
  · show ((3 : ℝ) ^ m / 4) • (((3 : ℝ) ^ m / 4)⁻¹ • (w - y)) + y = w
    rw [smul_smul, mul_inv_cancel₀ hl.ne', one_smul, sub_add_cancel]

/-- The uniform family, constants independent of `m` and `y`. -/
theorem ia_uniform_family [NeZero d] :
    ∃ (N : ℕ) (r M₁ M₂ D : ℝ), 1 ≤ N ∧ (d : ℝ) * (4 / 5 : ℝ) ^ (2 * N) < 1 ∧ 0 < r ∧
      ∀ (m : ℕ) (y : Vec d),
        IsUniformC11Domain (ia_V d N m y) ((3 : ℝ) ^ m / 4 * r) M₁ (M₂ / ((3 : ℝ) ^ m / 4))
          ((3 : ℝ) ^ m / 4 * D) := by
  obtain ⟨N, hN, hd⟩ := ia_exists_exponent d
  obtain ⟨r, M₁, M₂, D, hU⟩ := exists_isUniformC11Domain_of_isSmoothBoundedDomain
    (g1_isSmoothBoundedDomain_superE (d := d) (N := N) hN)
  exact ⟨N, r, M₁, M₂, D, hN, hd, hU.2.1, fun m y => hU.affineImage (by positivity) y⟩

end SuperdiffusionCLT.Section7
