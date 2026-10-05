/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Geometry.BoundaryGlueD

/-!
# Membership in the sheared model domain

Elementary estimates for the glue: the projection `y ↦ y - ⟨e,y⟩ e` and the coordinate `⟨e,y⟩`
control `‖y‖`; membership of `y` in `{shear e Ψ y ∈ g1b_H e 1 1}` is described by the height
`⟨e,y⟩ - Ψ(Py)`, in the flat zone exactly, and in general by a two-sided bound.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization

variable {d : ℕ}

theorem g1c_norm_le_of_vecNormSq_lt {w : Vec d} (hw : vecNormSq w < 1) : ‖w‖ ≤ 1 :=
  (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by
    have h1 := sq_apply_le_vecNormSq w i
    have h2 : |w i| ^ 2 < 1 := by rw [sq_abs]; linarith only [h1, hw]
    rw [Real.norm_eq_abs]
    have h3 : |w i| < 1 := by
      by_contra hc
      have : 1 ≤ |w i| := not_lt.1 hc
      nlinarith only [h2, this]
    exact h3.le

theorem g1c_norm_le_proj_add {e : Vec d} (he : vecNormSq e = 1) (y : Vec d) :
    ‖y‖ ≤ ‖y - vecDot e y • e‖ + |vecDot e y| := by
  have h : y = (y - vecDot e y • e) + vecDot e y • e := by abel
  calc ‖y‖ = ‖(y - vecDot e y • e) + vecDot e y • e‖ := by rw [← h]
    _ ≤ ‖y - vecDot e y • e‖ + ‖vecDot e y • e‖ := norm_add_le _ _
    _ ≤ ‖y - vecDot e y • e‖ + |vecDot e y| := by
        rw [norm_smul, Real.norm_eq_abs]
        have := mul_le_mul_of_nonneg_left (norm_le_one_of_vecNormSq he) (abs_nonneg (vecDot e y))
        linarith only [this]

theorem g1c_norm_proj_le {e : Vec d} (he : vecNormSq e = 1) (y : Vec d) :
    ‖y - vecDot e y • e‖ ≤ (1 + d) * ‖y‖ := by
  have h1 := norm_proj_sub_le he y 0
  have hp0 : (0 : Vec d) - vecDot e 0 • e = 0 := by simp [vecDot]
  rw [hp0, sub_zero, sub_zero] at h1
  exact h1

theorem g1c_abs_le_of_zero {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {M : ℝ}
    (hM : ∀ y, ‖fderiv ℝ ψ y‖ ≤ M) (h0 : ψ 0 = 0) (w : Vec d) : |ψ w| ≤ M * ‖w‖ := by
  have := abs_sub_le_of_fderiv_bound hψ hM w 0
  rwa [h0, sub_zero, sub_zero] at this

/-- Flat zone: membership is the height condition. -/
theorem g1c_mem_flat {e : Vec d} (he : vecNormSq e = 1) {Ψ : Vec d → ℝ} {ζ : ℝ} {y : Vec d}
    (hζ : (d : ℝ) * ζ ^ 2 ≤ 1 ^ 2 / 16) (hy : ‖y - vecDot e y • e‖ ≤ ζ) :
    shear e Ψ y ∈ g1b_H e 1 1 ↔
      -2 < vecDot e y - Ψ (y - vecDot e y • e) ∧ vecDot e y - Ψ (y - vecDot e y • e) < 0 := by
  have hu : g1b_u e 1 (shear e Ψ y) ≤ 1 / 16 := by
    unfold g1b_u
    rw [proj_shear he, one_pow, div_one]
    have h1 := g1b_vecNormSq_le (y - vecDot e y • e)
    have h2 : ‖y - vecDot e y • e‖ ^ 2 ≤ ζ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hy 2
    have h3 := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
    linarith only [h1, h3, hζ]
  rw [g1b_mem_H_flat one_pos hu, vecDot_shear he]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith only [h1, h2]

/-- Points of the sheared model domain: bounds on the projection and the height. -/
theorem g1c_mem_bound {e : Vec d} (he : vecNormSq e = 1) {Ψ : Vec d → ℝ} {y : Vec d}
    (hy : shear e Ψ y ∈ g1b_H e 1 1) :
    ‖y - vecDot e y • e‖ ≤ 1 ∧
      -2 < vecDot e y - Ψ (y - vecDot e y • e) ∧ vecDot e y - Ψ (y - vecDot e y • e) < 0 := by
  obtain ⟨hu, hv⟩ := g1b_mem_H_iff_lt hy
  unfold g1b_u at hu
  rw [proj_shear he, one_pow, div_one] at hu
  unfold g1b_v at hv
  rw [one_pow, div_one, vecDot_shear he] at hv
  refine ⟨g1c_norm_le_of_vecNormSq_lt hu, ?_⟩
  rw [sq_lt_one_iff_abs_lt_one, abs_lt] at hv
  constructor <;> linarith only [hv.1, hv.2]

end SuperdiffusionCLT.Section7
