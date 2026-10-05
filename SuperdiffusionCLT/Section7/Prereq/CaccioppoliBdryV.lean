/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.CaccioppoliBdryU
public import SuperdiffusionCLT.Section7.Prereq.CaccioppoliK
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The scale-separation arithmetic of the boundary Caccioppoli inequality
-/

@[expose] public section

open scoped ENNReal NNReal
open MeasureTheory Filter Topology Homogenization

namespace SuperdiffusionCLT.Section7

theorem ca2w_params {d : ℕ} (hd : 1 ≤ d) {ν m yy x S Λ Cth Kτ CB : ℝ} {N : ℕ} (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hm1 : 1 ≤ m) (hSm : S ≤ m) (hS0 : 0 ≤ S) (hΛ : Λ ≤ 2 * m ^ 2) (hΛ0 : 0 ≤ Λ) (hyy0 : 0 < yy)
    (hx : x = yy ^ d) (hN : 1 ≤ N) (hsep : m ^ 8 * (ν ^ 8)⁻¹ * yy ≤ (m ^ N)⁻¹) (hKτ1 : 1 ≤ Kτ)
    (hCB : 0 ≤ CB) (hCth0 : 0 ≤ Cth) (hCth : Cth ≤ m) (hKm : Kτ * (1 + 4 * d) ≤ m)
    (hKτdef : 4 * CB * Cth ^ (1 / (d : ℝ)) ≤ Kτ) (hxy : x ≤ yy) :
    (0 ≤ Cth * x ∧ Cth * x ≤ 1) ∧ x ≤ Kτ * m ^ 4 * (ν ^ 2)⁻¹ * yy ∧
      Kτ * m ^ 4 * (ν ^ 2)⁻¹ * yy * (S / ν) ^ 2 ≤ 1 ∧
      Kτ * m ^ 4 * (ν ^ 2)⁻¹ * yy * (1 + d * Λ ^ 2 / ν ^ 2) ≤ 1 ∧
      CB * Λ ^ 2 * (Cth * x) ^ (1 / (d : ℝ)) ≤ ν ^ 2 * (Kτ * m ^ 4 * (ν ^ 2)⁻¹ * yy) := by
  have hm0 : 0 < m := by linarith only [hm1]
  have hd0 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hν2 : 0 < ν ^ 2 := by positivity
  have hν8 : 0 < ν ^ 8 := by positivity
  have hmN : m ≤ m ^ N := by
    calc m = m ^ 1 := (pow_one m).symm
      _ ≤ m ^ N := pow_le_pow_right₀ hm1 hN
  -- `yy ≤ 1/m`
  have hq1 : 1 ≤ m ^ 8 * (ν ^ 8)⁻¹ := by
    have : 1 ≤ m ^ 8 := one_le_pow₀ hm1
    have h2 : 1 ≤ (ν ^ 8)⁻¹ := by
      rw [one_le_inv₀ hν8]; exact pow_le_one₀ hν.le hν1
    nlinarith only [this, h2]
  have hyyN : yy ≤ (m ^ N)⁻¹ := by
    refine le_trans ?_ hsep
    calc yy = 1 * yy := (one_mul _).symm
      _ ≤ (m ^ 8 * (ν ^ 8)⁻¹) * yy := mul_le_mul_of_nonneg_right hq1 hyy0.le
      _ = _ := by ring
  have hyym : yy ≤ m⁻¹ := hyyN.trans (by rw [inv_le_inv₀ (by positivity) hm0]; exact hmN)
  have hxm : x ≤ m⁻¹ := hxy.trans hyym
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  -- the key product bound `m^8 ν^{-4} yy ≤ m⁻¹`
  have hkey : m ^ 8 * (ν ^ 4)⁻¹ * yy ≤ m⁻¹ := by
    have h1 : m ^ 8 * (ν ^ 4)⁻¹ * yy ≤ m ^ 8 * (ν ^ 8)⁻¹ * yy := by
      have : (ν ^ 4)⁻¹ ≤ (ν ^ 8)⁻¹ := by
        rw [inv_le_inv₀ (by positivity) hν8]
        exact pow_le_pow_of_le_one hν.le hν1 (by norm_num)
      gcongr
    exact h1.trans (hsep.trans (by rw [inv_le_inv₀ (by positivity) hm0]; exact hmN))
  refine ⟨⟨by positivity, ?_⟩, ?_, ?_, ?_, ?_⟩
  · calc Cth * x ≤ m * m⁻¹ := mul_le_mul hCth hxm hx0 hm0.le
      _ = 1 := mul_inv_cancel₀ hm0.ne'
  · calc x ≤ yy := hxy
      _ = 1 * 1 * 1 * yy := by ring
      _ ≤ Kτ * m ^ 4 * (ν ^ 2)⁻¹ * yy := by
        have h1 : 1 ≤ m ^ 4 := one_le_pow₀ hm1
        have h2 : 1 ≤ (ν ^ 2)⁻¹ := by rw [one_le_inv₀ hν2]; exact pow_le_one₀ hν.le hν1
        have : 1 ≤ Kτ * m ^ 4 * (ν ^ 2)⁻¹ := by
          have := mul_le_mul hKτ1 h1 zero_le_one (by linarith only [hKτ1])
          have h3 : 1 ≤ Kτ * m ^ 4 := by linarith only [this]
          have := mul_le_mul h3 h2 zero_le_one (by linarith only [h3])
          linarith only [this]
        nlinarith only [this, hyy0]
  · -- `τ (S/ν)² ≤ 1`
    have h1 : (S / ν) ^ 2 ≤ m ^ 2 * (ν ^ 2)⁻¹ := by
      rw [div_pow, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hS0 hSm 2) (inv_nonneg.2 hν2.le)
    have h2 : m ^ 6 * (ν ^ 4)⁻¹ * yy ≤ m ^ 8 * (ν ^ 4)⁻¹ * yy := by
      have : m ^ 6 ≤ m ^ 8 := pow_le_pow_right₀ hm1 (by norm_num)
      gcongr
    have h3 : Kτ * m ^ 4 * (ν ^ 2)⁻¹ * yy * (S / ν) ^ 2 ≤ Kτ * (m ^ 6 * (ν ^ 4)⁻¹ * yy) := by
      calc Kτ * m ^ 4 * (ν ^ 2)⁻¹ * yy * (S / ν) ^ 2
          ≤ Kτ * m ^ 4 * (ν ^ 2)⁻¹ * yy * (m ^ 2 * (ν ^ 2)⁻¹) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = Kτ * (m ^ 6 * (ν ^ 4)⁻¹ * yy) := by
          rw [show (ν ^ 4)⁻¹ = (ν ^ 2)⁻¹ * (ν ^ 2)⁻¹ by rw [← mul_inv, ← pow_add]]
          ring
    have h4 : Kτ * (m ^ 6 * (ν ^ 4)⁻¹ * yy) ≤ Kτ * m⁻¹ := by
      exact mul_le_mul_of_nonneg_left (h2.trans hkey) (by linarith only [hKτ1])
    have h5 : Kτ * m⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hm0]
      nlinarith only [hKm, hKτ1, hd0]
    linarith only [h3, h4, h5]
  · -- `τ (1 + dΛ²/ν²) ≤ 1`
    have hΛ2 : Λ ^ 2 ≤ 4 * m ^ 4 := by
      have := pow_le_pow_left₀ hΛ0 hΛ 2
      nlinarith only [this]
    have h1 : 1 + d * Λ ^ 2 / ν ^ 2 ≤ (1 + 4 * d) * (m ^ 4 * (ν ^ 2)⁻¹) := by
      have e : (d : ℝ) * Λ ^ 2 / ν ^ 2 = d * Λ ^ 2 * (ν ^ 2)⁻¹ := by rw [div_eq_mul_inv]
      rw [e]
      have h2 : 1 ≤ m ^ 4 * (ν ^ 2)⁻¹ := by
        have h3 : 1 ≤ m ^ 4 := one_le_pow₀ hm1
        have h4 : 1 ≤ (ν ^ 2)⁻¹ := by rw [one_le_inv₀ hν2]; exact pow_le_one₀ hν.le hν1
        nlinarith only [h3, h4]
      have h5 : (d : ℝ) * Λ ^ 2 * (ν ^ 2)⁻¹ ≤ (4 * d) * (m ^ 4 * (ν ^ 2)⁻¹) := by
        calc (d : ℝ) * Λ ^ 2 * (ν ^ 2)⁻¹ ≤ (d : ℝ) * (4 * m ^ 4) * (ν ^ 2)⁻¹ := by gcongr
          _ = (4 * d) * (m ^ 4 * (ν ^ 2)⁻¹) := by ring
      nlinarith only [h5, h2]
    have h6 : Kτ * m ^ 4 * (ν ^ 2)⁻¹ * yy * (1 + d * Λ ^ 2 / ν ^ 2) ≤
        Kτ * (1 + 4 * d) * (m ^ 8 * (ν ^ 4)⁻¹ * yy) := by
      calc Kτ * m ^ 4 * (ν ^ 2)⁻¹ * yy * (1 + d * Λ ^ 2 / ν ^ 2)
          ≤ Kτ * m ^ 4 * (ν ^ 2)⁻¹ * yy * ((1 + 4 * d) * (m ^ 4 * (ν ^ 2)⁻¹)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = Kτ * (1 + 4 * d) * (m ^ 8 * (ν ^ 4)⁻¹ * yy) := by
          rw [show (ν ^ 4)⁻¹ = (ν ^ 2)⁻¹ * (ν ^ 2)⁻¹ by rw [← mul_inv, ← pow_add]]
          ring
    have h7 : Kτ * (1 + 4 * d) * (m ^ 8 * (ν ^ 4)⁻¹ * yy) ≤ Kτ * (1 + 4 * d) * m⁻¹ :=
      mul_le_mul_of_nonneg_left hkey (by positivity)
    have h8 : Kτ * (1 + 4 * d) * m⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hm0]; exact hKm
    linarith only [h6, h7, h8]
  · -- the smallness of the layer term
    have hΛ2 : Λ ^ 2 ≤ 4 * m ^ 4 := by
      have := pow_le_pow_left₀ hΛ0 hΛ 2
      nlinarith only [this]
    have hθ : (Cth * x) ^ (1 / (d : ℝ)) = Cth ^ (1 / (d : ℝ)) * yy := by
      rw [Real.mul_rpow hCth0 hx0, hx, ← Real.rpow_natCast, ← Real.rpow_mul hyy0.le]
      have : (d : ℝ) * (1 / (d : ℝ)) = 1 := by field_simp
      rw [this, Real.rpow_one]
    rw [hθ]
    have hr0 : 0 ≤ Cth ^ (1 / (d : ℝ)) := Real.rpow_nonneg hCth0 _
    calc CB * Λ ^ 2 * (Cth ^ (1 / (d : ℝ)) * yy) ≤ CB * (4 * m ^ 4) * (Cth ^ (1 / (d : ℝ)) * yy) := by gcongr
      _ = (4 * CB * Cth ^ (1 / (d : ℝ))) * (m ^ 4 * yy) := by ring
      _ ≤ Kτ * (m ^ 4 * yy) := by gcongr
      _ = ν ^ 2 * (Kτ * m ^ 4 * (ν ^ 2)⁻¹ * yy) := by
        field_simp

end SuperdiffusionCLT.Section7
