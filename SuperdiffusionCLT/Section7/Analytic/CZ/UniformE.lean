/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.CZ.UniformD
public import SuperdiffusionCLT.Section7.Analytic.Geometry.AtlasTransform
public import SuperdiffusionCLT.Section7.Analytic.Geometry.LayerPoincareB
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Global `W^{1,p}` estimate: grid and geometry lemmas

* `p13_grid_count`, `p13_grid_cover`: the cells `|x i - k i * s| ≤ s / 2` cover `ℝ^d`, and a point lies
  in the window `|y i - k i * s| < R` of at most `(⌈2R/s⌉ + 1)^d` cells.
* `p13_ball_subset`: a ball around a point of `U` that avoids the frontier lies in `U`.
* `p13_Lam_le`: comparison of the scale factors at two scales.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal NNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- Finitely many grid indices `k` have `|y i - k i * s| < R` for all `i`. -/
theorem p13_grid_count (s R : ℝ) (hs : 0 < s) (y : Vec d) :
    ∃ S : Finset (Fin d → ℤ), (∀ k : Fin d → ℤ, (∀ i, |y i - (k i : ℝ) * s| < R) → k ∈ S) ∧
      S.card ≤ (⌈2 * R / s⌉₊ + 1) ^ d := by
  refine ⟨Fintype.piFinset fun i => Finset.Icc ⌈(y i - R) / s⌉ ⌊(y i + R) / s⌋, ?_, ?_⟩
  · intro k hk
    rw [Fintype.mem_piFinset]
    intro i
    have h := abs_lt.1 (hk i)
    rw [Finset.mem_Icc]
    constructor
    · refine Int.ceil_le.2 ?_
      rw [div_le_iff₀ hs]
      linarith only [h.2]
    · refine Int.le_floor.2 ?_
      rw [le_div_iff₀ hs]
      linarith only [h.1]
  · rw [Fintype.card_piFinset]
    calc ∏ i : Fin d, (Finset.Icc ⌈(y i - R) / s⌉ ⌊(y i + R) / s⌋).card
        ≤ ∏ _i : Fin d, (⌈2 * R / s⌉₊ + 1) := by
          refine Finset.prod_le_prod fun i _ => ?_
          rw [Int.card_Icc]
          have h1 : (⌊(y i + R) / s⌋ : ℝ) ≤ (y i + R) / s := Int.floor_le _
          have h2 : (y i - R) / s ≤ (⌈(y i - R) / s⌉ : ℝ) := Int.le_ceil _
          have h3 : (2 * R / s : ℝ) ≤ ⌈2 * R / s⌉₊ := Nat.le_ceil _
          have h4 : (⌊(y i + R) / s⌋ + 1 - ⌈(y i - R) / s⌉ : ℤ) ≤ ((⌈2 * R / s⌉₊ + 1 : ℕ) : ℤ) := by
            have h5 : ((⌊(y i + R) / s⌋ + 1 - ⌈(y i - R) / s⌉ : ℤ) : ℝ) ≤
                (((⌈2 * R / s⌉₊ + 1 : ℕ) : ℤ) : ℝ) := by
              push_cast
              have h6 : (y i + R) / s - (y i - R) / s = 2 * R / s := by ring
              linarith only [h1, h2, h3, h6]
            exact_mod_cast h5
          omega
      _ = (⌈2 * R / s⌉₊ + 1) ^ d := by simp

/-- Every point lies in the grid cell of side `s` centred at some `k * s`. -/
theorem p13_grid_cover (s : ℝ) (hs : 0 < s) (x : Vec d) :
    ∃ k : Fin d → ℤ, ∀ i, |x i - (k i : ℝ) * s| ≤ s / 2 := by
  refine ⟨fun i => ⌊x i / s + 1 / 2⌋, fun i => ?_⟩
  have h1 : (⌊x i / s + 1 / 2⌋ : ℝ) ≤ x i / s + 1 / 2 := Int.floor_le _
  have h2 : x i / s + 1 / 2 < (⌊x i / s + 1 / 2⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  dsimp only
  rw [abs_le]
  have h3 : (x i / s + 1 / 2) * s = x i + s / 2 := by field_simp
  have h1' := mul_le_mul_of_nonneg_right h1 hs.le
  have h2' := mul_le_mul_of_nonneg_right h2.le hs.le
  have h4 : ((⌊x i / s + 1 / 2⌋ : ℝ) + 1) * s = (⌊x i / s + 1 / 2⌋ : ℝ) * s + s := by ring
  rw [h4] at h2'
  constructor
  · linarith only [h1', h3]
  · linarith only [h2', h3]

/-- A ball around a point of `U` that stays away from the frontier lies in `U`. -/
theorem p13_ball_subset {U : Set (Vec d)} (hU : IsOpen U) {x : Vec d} (hx : x ∈ U) {ρ : ℝ}
    (hρ : 0 < ρ) (h : ∀ x₀ ∈ frontier U, ρ ≤ dist x x₀) : Metric.ball x ρ ⊆ U := by
  refine (convex_ball x ρ).isPreconnected.subset_of_closure_inter_subset hU
    ⟨x, Metric.mem_ball_self hρ, hx⟩ ?_
  · rintro z ⟨hzc, hzb⟩
    by_contra hzU
    have hzf : z ∈ frontier U := by
      rw [frontier, hU.interior_eq]
      exact ⟨hzc, hzU⟩
    have h1 := h z hzf
    have h2 := Metric.mem_ball.1 hzb
    rw [dist_comm] at h2
    linarith only [h1, h2]

theorem p13_box_eq_ball (z : Vec d) {r : ℝ} (hr : 0 < r) :
    {y : Vec d | ∀ i, |y i - z i| < r} = Metric.ball z r := by
  ext y
  rw [Metric.mem_ball, dist_pi_lt_iff hr]
  simp only [Set.mem_ofPred_eq, Real.dist_eq]

theorem p13_Lam_le {ℓ c θ : ℝ} (hℓ : 0 < ℓ) (hc : 1 ≤ c) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ENNReal.ofReal ((ℓ ^ d)⁻¹) ^ θ ≤
      ENNReal.ofReal (c ^ d) * ENNReal.ofReal (((c * ℓ) ^ d)⁻¹) ^ θ := by
  have hc0 : 0 < c := by linarith only [hc]
  have h1 : (ℓ ^ d)⁻¹ = c ^ d * ((c * ℓ) ^ d)⁻¹ := by
    rw [mul_pow]
    field_simp
  have h2 : (1 : ℝ) ≤ c ^ d := one_le_pow₀ hc
  rw [h1, ENNReal.ofReal_mul (by positivity), ENNReal.mul_rpow_of_nonneg _ _ hθ0]
  refine mul_le_mul_left ?_ _
  calc ENNReal.ofReal (c ^ d) ^ θ ≤ ENNReal.ofReal (c ^ d) ^ (1 : ℝ) :=
    ENNReal.rpow_le_rpow_of_exponent_le (by simpa using h2) hθ1
    _ = _ := ENNReal.rpow_one _

end SuperdiffusionCLT.Section7
