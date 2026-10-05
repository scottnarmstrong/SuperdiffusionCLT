/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.L2Comparison
public import SuperdiffusionCLT.Section7.Analytic.MollifierC
public import SuperdiffusionCLT.Section7.Analytic.OpenH10.H10Limit

/-!
# Mollification by a smooth kernel: smoothness, derivative, locality

For a smooth profile `η` supported in the
unit sup-ball and `h > 0`, the mollification `l2a_moll h η u (x) = ∫ η_h (x - y) u (y) dy` of a
locally integrable `u` is smooth, its coordinate derivatives are the mollifications of the weak
partial derivatives, and its value at `x` depends only on `u` on the sup-ball of radius `h`
around `x`.  A function with a whole-space weak gradient mollifies to an `H¹(W)` function on a
bounded set `W`.
-/

@[expose] public section

open MeasureTheory Set Filter Homogenization
open scoped ENNReal Convolution

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The scalar mollification `x ↦ ∫ η_h (x - y) u (y) dy`. -/
noncomputable def l2a_moll (d : ℕ) (h : ℝ) (η : Vec d → ℝ) (u : Vec d → ℝ) (x : Vec d) : ℝ :=
  ∫ y, a16_kernel d h η (x - y) * u y

/-- The vector mollification of a field is the componentwise scalar mollification. -/
theorem l2a_mollify_apply (h : ℝ) (η : Vec d → ℝ) (F : Vec d → Vec d) (x : Vec d) (i : Fin d) :
    a16_mollify d h η F x i = l2a_moll d h η (fun y => F y i) x := rfl

theorem l2a_kernel_contDiff {h : ℝ} {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) :
    ContDiff ℝ (⊤ : ℕ∞) (a16_kernel d h η) := by
  unfold a16_kernel
  exact contDiff_const.mul (hη.comp (contDiff_id.const_smul h⁻¹))

theorem l2a_kernel_eq_zero_of_norm {h : ℝ} (hh : 0 < h) {η : Vec d → ℝ}
    (hη : ∀ w, (∃ i, 1 < |w i|) → η w = 0) {w : Vec d} (hw : h < ‖w‖) :
    a16_kernel d h η w = 0 := by
  by_contra hne
  apply absurd hw
  rw [not_lt, pi_norm_le_iff_of_nonneg hh.le]
  intro i
  by_contra hi
  exact hne (a16_kernel_eq_zero hh hη (not_le.1 (by simpa [Real.norm_eq_abs] using hi)))

theorem l2a_kernel_compact {h : ℝ} (hh : 0 < h) {η : Vec d → ℝ}
    (hη : ∀ w, (∃ i, 1 < |w i|) → η w = 0) : HasCompactSupport (a16_kernel d h η) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Vec d) h) ?_
  intro w hw
  rw [mem_closedBall_zero_iff]
  by_contra hlt
  exact hw (l2a_kernel_eq_zero_of_norm hh hη (not_le.1 hlt))

/-- The reflected kernel `z ↦ η_h (-z)`. -/
theorem l2a_kernel_neg_contDiff {h : ℝ} {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => a16_kernel d h η (-z)) :=
  (l2a_kernel_contDiff hη).comp contDiff_neg

theorem l2a_kernel_neg_compact {h : ℝ} (hh : 0 < h) {η : Vec d → ℝ}
    (hη : ∀ w, (∃ i, 1 < |w i|) → η w = 0) :
    HasCompactSupport (fun z => a16_kernel d h η (-z)) :=
  (l2a_kernel_compact hh hη).comp_homeomorph (Homeomorph.neg (Vec d))

theorem l2a_moll_eq_conv (h : ℝ) (η : Vec d → ℝ) (u : Vec d → ℝ) :
    l2a_moll d h η u = a16_kernel d h η ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u := by
  funext x
  simp only [l2a_moll, convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have := integral_sub_left_eq_self (fun t => a16_kernel d h η t * u (x - t)) volume x
  simpa only [sub_sub_cancel] using this

theorem l2a_moll_contDiff {h : ℝ} (hh : 0 < h) {η : Vec d → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη0 : ∀ w, (∃ i, 1 < |w i|) → η w = 0) {u : Vec d → ℝ}
    (hu : LocallyIntegrable u volume) : ContDiff ℝ (⊤ : ℕ∞) (l2a_moll d h η u) := by
  rw [l2a_moll_eq_conv]
  exact (l2a_kernel_compact hh hη0).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (l2a_kernel_contDiff hη) hu

/-- **Mollification commutes with weak derivatives**: `∂ᵢ (η_h ∗ u) = η_h ∗ ∂ᵢ u`. -/
theorem l2a_fderiv_moll {h : ℝ} (hh : 0 < h) {η : Vec d → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη0 : ∀ w, (∃ i, 1 < |w i|) → η w = 0) {u g : Vec d → ℝ}
    (hu : LocallyIntegrable u volume) {i : Fin d}
    (hweak : HasWeakPartialDerivOn Set.univ i u g) (x : Vec d) :
    fderiv ℝ (l2a_moll d h η u) x (basisVec i) = l2a_moll d h η g x := by
  rw [l2a_moll_eq_conv, l2a_moll_eq_conv]
  exact fderiv_convolution_eq_of_hasWeakPartialDerivOn (l2a_kernel_compact hh hη0)
    (l2a_kernel_contDiff hη) hu hweak x

/-- Locality: the mollification at `x` only sees values on the sup-ball of radius `h`. -/
theorem l2a_moll_congr {h : ℝ} (hh : 0 < h) {η : Vec d → ℝ}
    (hη0 : ∀ w, (∃ i, 1 < |w i|) → η w = 0) {u u' : Vec d → ℝ} {x : Vec d}
    (hu : ∀ y, dist y x ≤ h → u y = u' y) : l2a_moll d h η u x = l2a_moll d h η u' x := by
  unfold l2a_moll
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  by_cases hy : dist y x ≤ h
  · simp only [hu y hy]
  · have : h < ‖x - y‖ := by rw [← dist_eq_norm, dist_comm]; exact not_le.1 hy
    simp [l2a_kernel_eq_zero_of_norm hh hη0 this]

/-- Linearity of the mollification on integrable functions. -/
theorem l2a_moll_add {h : ℝ} (hh : 0 < h) {η : Vec d → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη0 : ∀ w, (∃ i, 1 < |w i|) → η w = 0) {u v : Vec d → ℝ}
    (hu : LocallyIntegrable u volume) (hv : LocallyIntegrable v volume) (x : Vec d) :
    l2a_moll d h η (fun y => u y + v y) x = l2a_moll d h η u x + l2a_moll d h η v x := by
  have key : ∀ w : Vec d → ℝ, LocallyIntegrable w volume →
      Integrable (fun y => a16_kernel d h η (x - y) * w y) := fun w hw => by
    have hk : Continuous fun y => a16_kernel d h η (x - y) :=
      (l2a_kernel_contDiff hη).continuous.comp (continuous_const.sub continuous_id)
    have hc : HasCompactSupport fun y => a16_kernel d h η (x - y) :=
      (l2a_kernel_compact hh hη0).comp_homeomorph (Homeomorph.subLeft x)
    exact (hw.integrable_smul_left_of_hasCompactSupport hk hc : _)
  unfold l2a_moll
  simp only [mul_add]
  exact integral_add (key u hu) (key v hv)


theorem l2a_moll_const_mul {h : ℝ} {η : Vec d → ℝ} (c : ℝ) (u : Vec d → ℝ) (x : Vec d) :
    l2a_moll d h η (fun y => c * u y) x = c * l2a_moll d h η u x := by
  unfold l2a_moll
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  ring


/-- A smooth profile supported in the unit sup-ball (a bump function). -/
theorem l2a_exists_smooth_profile (d : ℕ) :
    ∃ η : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) η ∧ (∀ w, (∃ i, 1 < |w i|) → η w = 0) := by
  let b : ContDiffBump (0 : Vec d) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  refine ⟨b, b.contDiff, fun w ⟨i, hi⟩ => ?_⟩
  have hw : w ∉ Function.support (b : Vec d → ℝ) := by
    rw [b.support_eq]
    intro hmem
    rw [Metric.mem_ball, dist_zero_right] at hmem
    have := norm_le_pi_norm w i
    rw [Real.norm_eq_abs] at this
    simp only [b] at hmem
    linarith only [this, hi, hmem]
  simpa using hw

end SuperdiffusionCLT.Section7
