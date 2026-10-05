/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.CaccioppoliBdryI
public import Mathlib.Algebra.Ring.IsFormallyReal

/-!
# The final algebra of the boundary Caccioppoli inequality

The algebra of `ca1_alg`, with the extra terms of the edge-and-layer estimate:
`c13 ν τ k²` (absorbed through the crude bound, as the terms carrying `τ`) and `c14 S w²`.
-/

@[expose] public section

open scoped ENNReal NNReal
open MeasureTheory Filter Topology Homogenization

namespace SuperdiffusionCLT.Section7

/-- **The final algebra** of the interior Caccioppoli inequality: from the sum bound and the crude
bound to `ν g² ≤ C (S w² + S⁻¹ f²)`, under the scale separation `τ s² ≤ 1`, `τ Ξ ≤ 1`. -/
theorem ca2_alg {ν S α b τ Λ D Cα c1 c2 c3 c4 c5 c6 c7 c8 c13 c14 g k w f : ℝ} (hν : 0 < ν) (hνS : ν ≤ S)
    (hα : α ^ 2 ≤ Cα * S * ν) (hb : b ≤ 1) (hτ0 : 0 ≤ τ)
    (hD : 1 ≤ D) (hτs : τ * (S / ν) ^ 2 ≤ 1) (hτΞ : τ * (1 + D * Λ ^ 2 / ν ^ 2) ≤ 1)
    (hCα : 0 ≤ Cα) (hc4 : 0 ≤ c4) (hc5 : 0 ≤ c5)
    (hc6 : 0 ≤ c6) (hc7 : 0 ≤ c7) (hc8 : 0 ≤ c8) (hc13 : 0 ≤ c13) (hc14 : 0 ≤ c14) (hk : 0 ≤ k) (hw : 0 ≤ w)
    (hf : 0 ≤ f)
    (hI : ν * g ^ 2 ≤ f * w + c1 * α * g * w + c2 * τ * α * g * k + c3 * τ * α * k * w +
      c4 * b * f * w + c5 * τ * b * f * k + c6 * τ * b * f * w + c7 * Λ * τ ^ 5 * k * w +
      c13 * ν * τ * k ^ 2 + c14 * S * w ^ 2 + ν / 16 * g ^ 2)
    (hII : ν * k ^ 2 ≤ c8 * (ν⁻¹ * f ^ 2 + ν * w ^ 2 + D * Λ ^ 2 * ν⁻¹ * w ^ 2)) :
    ν * g ^ 2 ≤ (16 / 11 * (1 / 2 + 2 * c1 ^ 2 * Cα + 2 * c2 ^ 2 * Cα * c8 + (c8 + c3 ^ 2 * Cα) / 2 +
      c4 / 2 + c5 * (1 + c8) / 2 + c6 / 2 + c7 * (1 + c8) / 2 + c13 * c8 + c14)) * (S * w ^ 2 + S⁻¹ * f ^ 2) := by
  have hS : 0 < S := lt_of_lt_of_le hν hνS
  have hSinv : 0 < S⁻¹ := inv_pos.2 hS
  set T : ℝ := S * w ^ 2 + S⁻¹ * f ^ 2 with hT
  set Ξ : ℝ := 1 + D * Λ ^ 2 / ν ^ 2 with hΞ
  have hSS : S * S⁻¹ = 1 := mul_inv_cancel₀ hS.ne'
  have hνν : ν⁻¹ * ν = 1 := inv_mul_cancel₀ hν.ne'
  have hD0 : 0 ≤ D := by linarith only [hD]
  have hSw : 0 ≤ S * w ^ 2 := mul_nonneg hS.le (sq_nonneg w)
  have hSf : 0 ≤ S⁻¹ * f ^ 2 := mul_nonneg hSinv.le (sq_nonneg f)
  have hν4 : 0 < ν / 4 := div_pos hν (by norm_num)
  have hΞ1 : 1 ≤ Ξ := by
    have : 0 ≤ D * Λ ^ 2 / ν ^ 2 := div_nonneg (mul_nonneg hD0 (sq_nonneg Λ)) (sq_nonneg ν)
    linarith only [this]
  have hτ1 : τ ≤ 1 := by
    have h1 : 1 ≤ (S / ν) ^ 2 := by
      have : 1 ≤ S / ν := by rw [le_div_iff₀ hν]; linarith only [hνS]
      exact one_le_pow₀ this
    exact (le_mul_of_one_le_right hτ0 h1).trans hτs
  have hτ2 : τ ^ 2 ≤ τ := by rw [sq]; exact mul_le_of_le_one_right hτ0 hτ1
  have hT0 : 0 ≤ T := add_nonneg hSw hSf
  -- the crude bound in the form `k² ≤ c8 (ν⁻² f² + Ξ w²)`
  have hk2 : k ^ 2 ≤ c8 * (ν⁻¹ ^ 2 * f ^ 2 + Ξ * w ^ 2) := by
    have h1 := mul_le_mul_of_nonneg_left hII (inv_nonneg.2 hν.le)
    have e1 : ν⁻¹ * (ν * k ^ 2) = k ^ 2 := by rw [← mul_assoc, hνν, one_mul]
    have e2 : ν⁻¹ * (c8 * (ν⁻¹ * f ^ 2 + ν * w ^ 2 + D * Λ ^ 2 * ν⁻¹ * w ^ 2)) =
        c8 * (ν⁻¹ ^ 2 * f ^ 2 + Ξ * w ^ 2) := by
      rw [hΞ]; linear_combination (c8 * w ^ 2) * hνν
    rw [e1, e2] at h1
    exact h1
  -- Q3: τ S k² ≤ c8 T
  have hQ3 : τ * S * k ^ 2 ≤ c8 * T := by
    have h1 := mul_le_mul_of_nonneg_left hk2 (mul_nonneg hτ0 hS.le)
    have e1 : τ * S * (c8 * (ν⁻¹ ^ 2 * f ^ 2 + Ξ * w ^ 2)) =
        c8 * ((τ * (S / ν) ^ 2) * (S⁻¹ * f ^ 2) + (τ * Ξ) * (S * w ^ 2)) := by
      linear_combination (-(c8 * τ * ν⁻¹ ^ 2 * f ^ 2 * S)) * hSS
    rw [e1] at h1
    refine h1.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hc8
    have a1 : (τ * (S / ν) ^ 2) * (S⁻¹ * f ^ 2) ≤ 1 * (S⁻¹ * f ^ 2) :=
      mul_le_mul_of_nonneg_right hτs hSf
    have a2 : (τ * Ξ) * (S * w ^ 2) ≤ 1 * (S * w ^ 2) :=
      mul_le_mul_of_nonneg_right hτΞ hSw
    rw [hT]; linarith only [a1, a2]
  have hQ2 : τ ^ 2 * ν * k ^ 2 ≤ c8 * T := by
    have : τ ^ 2 * ν * k ^ 2 ≤ τ * S * k ^ 2 := by
      have h1 : τ ^ 2 * ν ≤ τ * S := by
        exact calc τ ^ 2 * ν ≤ τ * ν := mul_le_mul_of_nonneg_right hτ2 hν.le
          _ ≤ τ * S := mul_le_mul_of_nonneg_left hνS hτ0
      exact mul_le_mul_of_nonneg_right h1 (sq_nonneg k)
    exact this.trans hQ3
  -- (a)
  have ta : f * w ≤ T / 2 := by
    have := ca1_young (r := S⁻¹) (p := f) (q := w) hSinv
    have e : w ^ 2 / (2 * S⁻¹) = S * w ^ 2 / 2 := by
      rw [div_eq_mul_inv, mul_inv, inv_inv]; ring
    rw [e] at this
    rw [hT]; linarith only [this]
  -- (b)
  have tb : c1 * α * g * w ≤ ν / 8 * g ^ 2 + 2 * c1 ^ 2 * Cα * T := by
    have := ca1_young (r := ν / 4) (p := g) (q := c1 * α * w) hν4
    have e : (c1 * α * w) ^ 2 / (2 * (ν / 4)) = 2 * c1 ^ 2 * (α ^ 2 / ν) * w ^ 2 := by ring
    rw [e] at this
    have h1 : α ^ 2 / ν ≤ Cα * S := by rw [div_le_iff₀ hν]; linarith only [hα]
    have h2 : 2 * c1 ^ 2 * (α ^ 2 / ν) * w ^ 2 ≤ 2 * c1 ^ 2 * (Cα * S) * w ^ 2 := by
      have := mul_le_mul_of_nonneg_left h1 (mul_nonneg zero_le_two (sq_nonneg c1))
      exact mul_le_mul_of_nonneg_right this (sq_nonneg w)
    have h3 : 2 * c1 ^ 2 * (Cα * S) * w ^ 2 ≤ 2 * c1 ^ 2 * Cα * T := by
      rw [hT]
      have : 0 ≤ 2 * c1 ^ 2 * Cα * (S⁻¹ * f ^ 2) :=
        mul_nonneg (mul_nonneg (mul_nonneg zero_le_two (sq_nonneg c1)) hCα) hSf
      linarith only [this]
    have e2 : c1 * α * g * w = g * (c1 * α * w) := by ring
    rw [e2]
    have e3 : ν / 4 / 2 * g ^ 2 = ν / 8 * g ^ 2 := by ring
    rw [e3] at this
    linarith only [this, h2, h3]
  -- (c)
  have tc : c2 * τ * α * g * k ≤ ν / 8 * g ^ 2 + 2 * c2 ^ 2 * Cα * c8 * T := by
    have := ca1_young (r := ν / 4) (p := g) (q := c2 * τ * α * k) hν4
    have e : (c2 * τ * α * k) ^ 2 / (2 * (ν / 4)) = 2 * c2 ^ 2 * (α ^ 2 / ν) * (τ ^ 2 * k ^ 2) := by
      ring
    rw [e] at this
    have h1 : α ^ 2 / ν ≤ Cα * S := by rw [div_le_iff₀ hν]; linarith only [hα]
    have h2 : 2 * c2 ^ 2 * (α ^ 2 / ν) * (τ ^ 2 * k ^ 2) ≤ 2 * c2 ^ 2 * (Cα * S) * (τ ^ 2 * k ^ 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (mul_nonneg zero_le_two (sq_nonneg c2)))
        (mul_nonneg (sq_nonneg τ) (sq_nonneg k))
    have h3 : τ ^ 2 * S * k ^ 2 ≤ c8 * T := by
      exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hτ2 hS.le) (sq_nonneg k)).trans hQ3
    have h4 : 2 * c2 ^ 2 * (Cα * S) * (τ ^ 2 * k ^ 2) ≤ 2 * c2 ^ 2 * Cα * c8 * T := by
      have := mul_le_mul_of_nonneg_left h3 (mul_nonneg (mul_nonneg zero_le_two (sq_nonneg c2)) hCα)
      exact calc 2 * c2 ^ 2 * (Cα * S) * (τ ^ 2 * k ^ 2) = 2 * c2 ^ 2 * Cα * (τ ^ 2 * S * k ^ 2) := by ring
        _ ≤ 2 * c2 ^ 2 * Cα * (c8 * T) := this
        _ = _ := by ring
    have e2 : c2 * τ * α * g * k = g * (c2 * τ * α * k) := by ring
    rw [e2]
    have e3 : ν / 4 / 2 * g ^ 2 = ν / 8 * g ^ 2 := by ring
    rw [e3] at this
    linarith only [this, h2, h4]
  -- (d)
  have td : c3 * τ * α * k * w ≤ (c8 + c3 ^ 2 * Cα) / 2 * T := by
    have := ca1_young (r := ν) (p := τ * k) (q := c3 * α * w) hν
    have e : (c3 * α * w) ^ 2 / (2 * ν) = c3 ^ 2 * (α ^ 2 / ν) * w ^ 2 / 2 := by ring
    rw [e] at this
    have h1 : α ^ 2 / ν ≤ Cα * S := by rw [div_le_iff₀ hν]; linarith only [hα]
    have h2 : c3 ^ 2 * (α ^ 2 / ν) * w ^ 2 ≤ c3 ^ 2 * (Cα * S) * w ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (sq_nonneg c3)) (sq_nonneg w)
    have h3 : c3 ^ 2 * (Cα * S) * w ^ 2 ≤ c3 ^ 2 * Cα * T := by
      rw [hT]
      have : 0 ≤ c3 ^ 2 * Cα * (S⁻¹ * f ^ 2) := mul_nonneg (mul_nonneg (sq_nonneg c3) hCα) hSf
      linarith only [this]
    have e2 : c3 * τ * α * k * w = (τ * k) * (c3 * α * w) := by ring
    rw [e2]
    have e3 : ν / 2 * (τ * k) ^ 2 = τ ^ 2 * ν * k ^ 2 / 2 := by ring
    rw [e3] at this
    linarith only [this, h2, h3, hQ2]
  -- (e), (g)
  have te : c4 * b * f * w ≤ c4 / 2 * T := by
    have h1 : c4 * b * f * w ≤ c4 * (f * w) := by
      have : b * (f * w) ≤ 1 * (f * w) := mul_le_mul_of_nonneg_right hb (mul_nonneg hf hw)
      have := mul_le_mul_of_nonneg_left this hc4
      linarith only [this]
    have := mul_le_mul_of_nonneg_left ta hc4
    linarith only [h1, this]
  have tg : c6 * τ * b * f * w ≤ c6 / 2 * T := by
    have h0 : τ * b ≤ 1 :=
      (mul_le_mul_of_nonneg_left hb hτ0).trans (by rw [mul_one]; exact hτ1)
    have h1 : c6 * τ * b * f * w ≤ c6 * (f * w) := by
      have : (τ * b) * (f * w) ≤ 1 * (f * w) := mul_le_mul_of_nonneg_right h0 (mul_nonneg hf hw)
      have := mul_le_mul_of_nonneg_left this hc6
      linarith only [this]
    have := mul_le_mul_of_nonneg_left ta hc6
    linarith only [h1, this]
  -- (f)
  have tf : c5 * τ * b * f * k ≤ c5 * (1 + c8) / 2 * T := by
    have := ca1_young (r := S⁻¹) (p := f) (q := k) hSinv
    have e : k ^ 2 / (2 * S⁻¹) = S * k ^ 2 / 2 := by
      rw [div_eq_mul_inv, mul_inv, inv_inv]; ring
    rw [e] at this
    have h0 : τ * b ≤ τ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hb hτ0
    have h1 : c5 * τ * b * f * k ≤ c5 * τ * (f * k) := by
      have : (τ * b) * (f * k) ≤ τ * (f * k) := mul_le_mul_of_nonneg_right h0 (mul_nonneg hf hk)
      have := mul_le_mul_of_nonneg_left this hc5
      linarith only [this]
    have h2 : τ * (f * k) ≤ τ * (S⁻¹ / 2 * f ^ 2 + S * k ^ 2 / 2) := mul_le_mul_of_nonneg_left this hτ0
    have h3 : τ * (S⁻¹ / 2 * f ^ 2 + S * k ^ 2 / 2) ≤ T / 2 + c8 * T / 2 := by
      have a1 : τ * (S⁻¹ * f ^ 2) ≤ 1 * (S⁻¹ * f ^ 2) := mul_le_mul_of_nonneg_right hτ1 hSf
      have a2 : S⁻¹ * f ^ 2 ≤ T := by
        rw [hT]; linarith only [hSw]
      have e1 : τ * (S⁻¹ / 2 * f ^ 2 + S * k ^ 2 / 2) = (τ * (S⁻¹ * f ^ 2)) / 2 + (τ * S * k ^ 2) / 2 := by
        ring
      rw [e1]
      linarith only [a1, a2, hQ3]
    have h4 := mul_le_mul_of_nonneg_left (h2.trans h3) hc5
    linarith only [h1, h4]
  -- (h)
  have th : c7 * Λ * τ ^ 5 * k * w ≤ c7 * (1 + c8) / 2 * T := by
    have := ca1_young (r := ν) (p := τ * k) (q := Λ * τ ^ 4 * w) hν
    have e : (Λ * τ ^ 4 * w) ^ 2 / (2 * ν) = Λ ^ 2 / ν * τ ^ 8 * w ^ 2 / 2 := by ring
    rw [e] at this
    have h1 : Λ ^ 2 / ν ≤ ν * Ξ := by
      rw [div_le_iff₀ hν, hΞ]
      have : D * Λ ^ 2 / ν ^ 2 * ν ^ 2 = D * Λ ^ 2 := div_mul_cancel₀ _ (pow_ne_zero 2 hν.ne')
      have h9 := mul_nonneg (sub_nonneg.2 hD) (sq_nonneg Λ)
      linarith only [this, h9, sq_nonneg ν]
    have h2 : Λ ^ 2 / ν * τ ^ 8 * w ^ 2 ≤ S * w ^ 2 := by
      have a1 : τ ^ 8 * Ξ ≤ 1 := by
        have e1 : τ ^ 8 ≤ τ := by
          have : τ ^ 8 ≤ τ ^ 1 := pow_le_pow_of_le_one hτ0 hτ1 (by norm_num)
          simpa only [pow_one] using this
        exact (mul_le_mul_of_nonneg_right e1 (by linarith only [hΞ1])).trans hτΞ
      exact calc Λ ^ 2 / ν * τ ^ 8 * w ^ 2 ≤ (ν * Ξ) * τ ^ 8 * w ^ 2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (pow_nonneg hτ0 8)) (sq_nonneg w)
        _ = ν * (τ ^ 8 * Ξ) * w ^ 2 := by ring
        _ ≤ ν * 1 * w ^ 2 := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left a1 hν.le) (sq_nonneg w)
        _ ≤ S * w ^ 2 := by
            rw [mul_one]; exact mul_le_mul_of_nonneg_right hνS (sq_nonneg w)
    have e2 : c7 * Λ * τ ^ 5 * k * w = c7 * ((τ * k) * (Λ * τ ^ 4 * w)) := by ring
    rw [e2]
    have e3 : ν / 2 * (τ * k) ^ 2 = τ ^ 2 * ν * k ^ 2 / 2 := by ring
    rw [e3] at this
    have h5 : (τ * k) * (Λ * τ ^ 4 * w) ≤ (1 + c8) / 2 * T := by
      have h6 : S * w ^ 2 ≤ T := by rw [hT]; linarith only [hSf]
      linarith only [this, h2, hQ2, h6]
    have := mul_le_mul_of_nonneg_left h5 hc7
    linarith only [this]
  -- the sum
  have ti : c13 * ν * τ * k ^ 2 ≤ c13 * c8 * T := by
    have h1 : ν * τ * k ^ 2 ≤ τ * S * k ^ 2 := by
      have : ν * τ ≤ S * τ := mul_le_mul_of_nonneg_right hνS hτ0
      have := mul_le_mul_of_nonneg_right this (sq_nonneg k)
      linarith only [this]
    have := mul_le_mul_of_nonneg_left (h1.trans hQ3) hc13
    linarith only [this]
  have tj : c14 * S * w ^ 2 ≤ c14 * T := by
    have h6 : S * w ^ 2 ≤ T := by rw [hT]; linarith only [hSf]
    have := mul_le_mul_of_nonneg_left h6 hc14
    linarith only [this]
  have hfinal : ν * g ^ 2 ≤ T / 2 + (c1 * α * g * w) + c2 * τ * α * g * k + c3 * τ * α * k * w +
      c4 * b * f * w + c5 * τ * b * f * k + c6 * τ * b * f * w + c7 * Λ * τ ^ 5 * k * w +
      c13 * ν * τ * k ^ 2 + c14 * S * w ^ 2 + ν / 16 * g ^ 2 := by
    linarith only [hI, ta]
  linarith only [hfinal, tb, tc, td, te, tf, tg, th, ti, tj, hT0]

end SuperdiffusionCLT.Section7
