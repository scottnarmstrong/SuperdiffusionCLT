/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.BoundaryDecayChartI

@[expose] public section

open Homogenization MeasureTheory Filter Topology Matrix
open scoped ENNReal NNReal

/-!
# The `L²` excess of the chart-flattened function

For `ℓ₀(y) = a₀ + ⟨b₀, y - x₀⟩`, the flattened excess over the flat affine function `a₀ + ⟨O b₀, z⟩`
is bounded by the original excess plus `C M₂ ℓ² |b₀|` (the second order term of the chart).
-/

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem r3e_T_continuous {e : Vec d} {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (x₀ : Vec d) :
    Continuous (r3e_T e ψ x₀) := by
  have h := hψ.continuous
  unfold r3e_T vecDot
  fun_prop

theorem r3e_norm_le_one {e : Vec d} (he : vecNormSq e = 1) : ‖e‖ ≤ 1 := by
  have h := r3d_sup_sq_le e
  rw [he] at h
  by_contra hc
  push Not at hc
  nlinarith only [h, hc]

theorem r3e_flat_sub_eq {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (u x₀ b₀ : Vec d) (a₀ : ℝ) (φ' : Vec d → ℝ) (z : Vec d) :
    φ' (flattenInv e ψ x₀ u z) - (a₀ + vecDot (r3e_O e ψ x₀ u *ᵥ b₀) z) =
      (φ' (flattenInv e ψ x₀ u z) - (a₀ + vecDot b₀ (flattenInv e ψ x₀ u z - x₀))) +
        vecDot b₀ e * r3e_T e ψ x₀ (flattenInv e ψ x₀ u z) := by
  have h := r3e_dot_flatten he hψ u x₀ (r3e_O e ψ x₀ u *ᵥ b₀) (flattenInv e ψ x₀ u z)
  rw [flattenMap_flattenInv he hψ, r3e_mulVec_mulVec] at h
  rw [h]
  ring

theorem r3e_vecDot_le {b e : Vec d} (he : ‖e‖ ≤ 1) : |vecDot b e| ≤ d * ‖b‖ := by
  have := p12g_dot_le b e
  have h2 : ‖b‖ * ‖e‖ ≤ ‖b‖ := mul_le_of_le_one_right (norm_nonneg _) he
  have h3 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  nlinarith only [this, h2, h3]

theorem r3e_memLp_orig {U : Set (Vec d)} (φ : H10Function U) {S : Set (Vec d)} (hSU : S ⊆ U)
    {x₀ : Vec d} {ρ : ℝ} (hρ : 0 < ρ) (hS : S ⊆ Metric.ball x₀ ρ) (ℓ : ℝ) (a₀ : ℝ) (b₀ : Vec d)
    (hSm : MeasurableSet S) :
    MemLp (fun y => φ.toH1Function.toFun y - (a₀ + vecDot b₀ (y - x₀))) 2 (p12_nmeas ℓ S) := by
  have hφ : MemLp φ.toH1Function.toFun 2 (p12_nmeas ℓ S) := by
    unfold p12_nmeas
    exact (φ.toH1Function.memL2.mono_measure (Measure.restrict_mono hSU le_rfl)).smul_measure
      ENNReal.ofReal_ne_top
  refine hφ.sub ?_
  refine r3e_memLp_bound hρ hS ℓ (r3e_continuous_affine a₀ b₀ x₀).aestronglyMeasurable
    (C := |a₀| + d * (‖b₀‖ * ρ)) (fun y hy => ?_) hSm 2
  have hy' : ‖y - x₀‖ ≤ ρ := by
    have := hS hy
    rw [Metric.mem_ball, dist_eq_norm] at this
    exact this.le
  rw [Real.norm_eq_abs]
  calc |a₀ + vecDot b₀ (y - x₀)| ≤ |a₀| + |vecDot b₀ (y - x₀)| := abs_add_le _ _
    _ ≤ |a₀| + d * (‖b₀‖ * ‖y - x₀‖) := by linarith only [p12g_dot_le b₀ (y - x₀)]
    _ ≤ |a₀| + d * (‖b₀‖ * ρ) := by
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      have := mul_le_mul_of_nonneg_left hy' (norm_nonneg b₀)
      nlinarith only [this, ‹(0 : ℝ) ≤ d›]

/-- The `L²` excess of the flattened function over the flat affine function is bounded by the
original excess plus a second order term. -/
theorem r3e_bridge_L2 {U : Set (Vec d)} (hU : IsOpen U) {e : Vec d} (he : vecNormSq e = 1)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {M₂ : ℝ}
    (hb2 : ∀ y z, ‖fderiv ℝ ψ y - fderiv ℝ ψ z‖ ≤ M₂ * ‖y - z‖) {x₀ : Vec d}
    (hx₀ : vecDot e x₀ = ψ (x₀ - vecDot e x₀ • e)) {r : ℝ}
    (hch : ∀ y ∈ Metric.ball x₀ r, (y ∈ U ↔ vecDot e y < ψ (y - vecDot e y • e))) (i₀ : Fin d)
    {K : ℝ} (hK1 : 1 ≤ K)
    (hKlip : ∀ y z : Vec d, ‖flattenInv e ψ x₀ (-(basisVec i₀)) y -
        flattenInv e ψ x₀ (-(basisVec i₀)) z‖ ≤ K * ‖y - z‖)
    (m : ℤ) (hKr : K * (3 : ℝ) ^ m ≤ r) (φ : H10Function U) (a₀ : ℝ) (b₀ : Vec d) :
    (eLpNorm (fun x => φ.toH1Function.toFun (flattenInv e ψ x₀ (-(basisVec i₀)) (x - r3c_z0 i₀ m)) -
        (a₀ + vecDot (r3e_O e ψ x₀ (-(basisVec i₀)) *ᵥ b₀) (x - r3c_z0 i₀ m))) 2
        (normalizedCubeMeasure (originCube d m))).toReal ≤
      (eLpNorm (fun y => φ.toH1Function.toFun y - (a₀ + vecDot b₀ (y - x₀))) 2
        (p12_nmeas ((3 : ℝ) ^ m) (U ∩ Metric.ball x₀ (K * (3 : ℝ) ^ m)))).toReal +
      (2 * (1 + d) * d ^ 2 * K ^ 2 * (2 * K) ^ d) * (M₂ * ((3 : ℝ) ^ m) ^ 2 * ‖b₀‖) := by
  have hR : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  have hK0 : 0 < K := by linarith only [hK1]
  have hM₂ : 0 ≤ M₂ := flatten_nonneg_of_lipschitz hb2 i₀
  set R : ℝ := (3 : ℝ) ^ m with hRd
  set S : Set (Vec d) := U ∩ Metric.ball x₀ (K * R) with hSd
  set μ : Measure (Vec d) := p12_nmeas R S with hμ
  have hKR : 0 < K * R := by positivity
  have hSb : S ⊆ Metric.ball x₀ (K * R) := Set.inter_subset_right
  have hSm : MeasurableSet S := hU.measurableSet.inter Metric.isOpen_ball.measurableSet
  have hF1 := r3e_memLp_orig φ (Set.inter_subset_left) hKR hSb R a₀ b₀ hSm
  set F1 : Vec d → ℝ := fun y => φ.toH1Function.toFun y - (a₀ + vecDot b₀ (y - x₀)) with hF1d
  set F2 : Vec d → ℝ := fun y => vecDot b₀ e * r3e_T e ψ x₀ y with hF2d
  set cF : ℝ := d * ‖b₀‖ * (2 * M₂ * (1 + d) * d * (K * R) ^ 2) with hcF
  have hcF0 : 0 ≤ cF := by positivity
  have hF2b : ∀ y ∈ S, ‖F2 y‖ ≤ cF := by
    intro y hy
    have hyb : ‖y - x₀‖ ≤ K * R := by
      have := hSb hy
      rw [Metric.mem_ball, dist_eq_norm] at this
      exact this.le
    rw [Real.norm_eq_abs, hF2d]
    simp only
    rw [abs_mul]
    have h1 := r3e_vecDot_le (b := b₀) (r3e_norm_le_one he)
    have h2 := r3e_T_abs_le he hψ hM₂ hb2 x₀ y
    have h3 : ‖y - x₀‖ ^ 2 ≤ (K * R) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hyb 2
    have h4 : 2 * M₂ * (1 + d) * d * ‖y - x₀‖ ^ 2 ≤ 2 * M₂ * (1 + d) * d * (K * R) ^ 2 :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    exact mul_le_mul h1 (h2.trans h4) (abs_nonneg _) (by positivity)
  have hF2 : MemLp F2 2 μ := by
    refine r3e_memLp_bound hKR hSb R ?_ hF2b hSm 2
    exact ((r3e_T_continuous hψ x₀).const_mul _).aestronglyMeasurable
  have := r3e_nmeas_finite hKR hSb R
  have hF2sq : (eLpNorm F2 2 μ).toReal ≤ cF * (2 * K) ^ d := by
    have hint : Integrable (fun _ : Vec d => cF ^ 2) μ := integrable_const _
    have hae : ∀ᵐ y ∂μ, ‖F2 y‖ ^ 2 ≤ (fun _ : Vec d => cF ^ 2) y := by
      rw [hμ]
      unfold p12_nmeas
      refine Measure.ae_smul_measure ?_ _
      refine (ae_restrict_iff' hSm).2 (Filter.Eventually.of_forall fun y hy => ?_)
      exact pow_le_pow_left₀ (norm_nonneg _) (hF2b y hy) 2
    have h1 := r3d_eLpNorm_sq_le hint hae
    rw [integral_const, smul_eq_mul, measureReal_def] at h1
    have h2 := r3e_nmeas_univ hKR hSb hR
    have h3 : (μ Set.univ).toReal * cF ^ 2 ≤ (2 * K) ^ d * cF ^ 2 := by
      have : (R ^ d)⁻¹ * (2 * (K * R)) ^ d = (2 * K) ^ d := by
        rw [show 2 * (K * R) = (2 * K) * R by ring, mul_pow]
        field_simp
      rw [this] at h2
      exact mul_le_mul_of_nonneg_right h2 (by positivity)
    have h4 : (1 : ℝ) ≤ (2 * K) ^ d := one_le_pow₀ (by linarith only [hK1])
    have h5 : (eLpNorm F2 2 μ).toReal ^ 2 ≤ (cF * (2 * K) ^ d) ^ 2 := by
      have h6 : (2 * K) ^ d * cF ^ 2 ≤ ((2 * K) ^ d) ^ 2 * cF ^ 2 :=
        mul_le_mul_of_nonneg_right (by nlinarith only [h4]) (by positivity)
      calc (eLpNorm F2 2 μ).toReal ^ 2 ≤ (μ Set.univ).toReal * cF ^ 2 := h1
        _ ≤ (2 * K) ^ d * cF ^ 2 := h3
        _ ≤ ((2 * K) ^ d) ^ 2 * cF ^ 2 := h6
        _ = (cF * (2 * K) ^ d) ^ 2 := by ring
    exact (abs_le_of_sq_le_sq' h5 (by positivity)).2
  have hpull : eLpNorm (fun x => (fun y => F1 y + F2 y) (flattenInv e ψ x₀ (-(basisVec i₀))
      (x - r3c_z0 i₀ m))) 2 (normalizedCubeMeasure (originCube d m)) ≤
      eLpNorm (fun y => F1 y + F2 y) 2 μ := by
    rw [p12_normalized_eq]
    refine p12_eLpNorm_pull_le he hψ (-(basisVec i₀)) x₀ (r3c_z0 i₀ m) (fun y => F1 y + F2 y) 2 R ?_
    rintro _ ⟨x, hx, rfl⟩
    exact r3e_pull_mem he hψ hx₀ hch i₀ hK1 hKlip m hKr hx
  have htri : eLpNorm (fun y => F1 y + F2 y) 2 μ ≤ eLpNorm F1 2 μ + eLpNorm F2 2 μ :=
    eLpNorm_add_le (by norm_num)
  have hfun : (fun x => φ.toH1Function.toFun (flattenInv e ψ x₀ (-(basisVec i₀)) (x - r3c_z0 i₀ m)) -
        (a₀ + vecDot (r3e_O e ψ x₀ (-(basisVec i₀)) *ᵥ b₀) (x - r3c_z0 i₀ m))) =
      fun x => (fun y => F1 y + F2 y) (flattenInv e ψ x₀ (-(basisVec i₀)) (x - r3c_z0 i₀ m)) :=
    funext fun x => r3e_flat_sub_eq he hψ _ x₀ b₀ a₀ φ.toH1Function.toFun _
  rw [hfun]
  have hfin1 : eLpNorm F1 2 μ ≠ ⊤ := hF1.eLpNorm_ne_top
  have hfin2 : eLpNorm F2 2 μ ≠ ⊤ := hF2.eLpNorm_ne_top
  have hle := (hpull.trans htri)
  have h5 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin1, hfin2⟩) hle
  rw [ENNReal.toReal_add hfin1 hfin2] at h5
  refine h5.trans ?_
  have h6 : cF * (2 * K) ^ d = (2 * (1 + d) * d ^ 2 * K ^ 2 * (2 * K) ^ d) * (M₂ * R ^ 2 * ‖b₀‖) := by
    rw [hcF]; ring
  rw [← h6]
  exact add_le_add le_rfl hF2sq

end SuperdiffusionCLT.Section7
