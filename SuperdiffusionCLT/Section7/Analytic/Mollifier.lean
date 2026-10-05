/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Book.Ch01.Theorems.NegativeBesovLocalize
public import Homogenization.Book.Ch03.Definitions

/-!
# The scaled mollifier kernel and the translated test function

The elementary mollifier estimate of the paper bounds `‖η ∗ F‖_{L^∞(z + cu_n)}` by
`C 3^{-n/4} ‖F‖_{H̲^{-1/4}(z + cu_{n+1})}`.  The estimate is the duality statement that
`y ↦ η_h (x - y)` is a multiple of an admissible test function of the dual negative Besov
norm of the cube `Q'` of side `3h`.

This file records the kernel `a16_kernel` at scale `h`, its pointwise and Lipschitz bounds, and
the vanishing outside the sup-ball of radius `h`.  The test-norm bound is in `MollifierB`, the
estimates in `MollifierC`.
-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Section7

open Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The mollifier `η` at scale `h`: `η_h w = h^{-d} η (w / h)`. -/
def a16_kernel (d : ℕ) (h : ℝ) (η : Vec d → ℝ) (w : Vec d) : ℝ :=
  (h⁻¹) ^ d * η (h⁻¹ • w)

/-- The kernel is bounded by `A h^{-d}`. -/
theorem a16_kernel_abs_le {h : ℝ} (hh : 0 < h) {η : Vec d → ℝ} {A : ℝ}
    (hA : ∀ w, |η w| ≤ A) (w : Vec d) :
    |a16_kernel d h η w| ≤ A * (h⁻¹) ^ d := by
  unfold a16_kernel
  rw [abs_mul, abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hh.le) d), mul_comm]
  exact mul_le_mul_of_nonneg_right (hA _) (pow_nonneg (inv_nonneg.mpr hh.le) d)

/-- The kernel is Lipschitz with constant `L h^{-d-1}`. -/
theorem a16_kernel_dist_le {h : ℝ} (hh : 0 < h) {η : Vec d → ℝ} {L : NNReal}
    (hL : LipschitzWith L η) (w w' : Vec d) :
    |a16_kernel d h η w - a16_kernel d h η w'| ≤ (L : ℝ) * (h⁻¹) ^ d * (h⁻¹ * dist w w') := by
  unfold a16_kernel
  rw [← mul_sub, abs_mul, abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hh.le) d)]
  have h1 : dist (η (h⁻¹ • w)) (η (h⁻¹ • w')) ≤ (L : ℝ) * dist (h⁻¹ • w) (h⁻¹ • w') :=
    hL.dist_le_mul _ _
  have h2 : dist (h⁻¹ • w) (h⁻¹ • w') = h⁻¹ * dist w w' := by
    rw [dist_smul₀, Real.norm_of_nonneg (inv_nonneg.mpr hh.le)]
  rw [Real.dist_eq, h2] at h1
  calc (h⁻¹) ^ d * |η (h⁻¹ • w) - η (h⁻¹ • w')|
      ≤ (h⁻¹) ^ d * ((L : ℝ) * (h⁻¹ * dist w w')) :=
        mul_le_mul_of_nonneg_left h1 (pow_nonneg (inv_nonneg.mpr hh.le) d)
    _ = (L : ℝ) * (h⁻¹) ^ d * (h⁻¹ * dist w w') := by ring

/-- The kernel vanishes outside the sup-ball of radius `h`, when `η` vanishes outside the unit
sup-ball. -/
theorem a16_kernel_eq_zero {h : ℝ} (hh : 0 < h) {η : Vec d → ℝ}
    (hη : ∀ w, (∃ i, 1 < |w i|) → η w = 0) {w : Vec d} {i : Fin d} (hi : h < |w i|) :
    a16_kernel d h η w = 0 := by
  unfold a16_kernel
  rw [hη, mul_zero]
  refine ⟨i, ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hh)]
  rw [← div_eq_inv_mul, lt_div_iff₀ hh]
  linarith only [hi]

/-- The kernel is continuous when `η` is. -/
theorem a16_kernel_continuous {h : ℝ} {η : Vec d → ℝ} (hη : Continuous η) :
    Continuous (a16_kernel d h η) := by
  unfold a16_kernel
  exact continuous_const.mul (hη.comp (continuous_const_smul h⁻¹))

end

end Section7
end SuperdiffusionCLT
