/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.BoundaryDecayChartG
public import SuperdiffusionCLT.Section7.Analytic.Regularity.BoundaryDecayChartC

@[expose] public section

open Homogenization MeasureTheory Filter Topology Matrix
open scoped ENNReal NNReal

/-!
# Points of the chart and points of the flat face box

The chart map with target `-e_i` carries `U ∩ B(x₀, ρ)` into the face box of side `2 K ρ`, and
the cube `Q_m` back into `U ∩ B(x₀, K 3^m)`.
-/

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem r3e_pull_mem {U : Set (Vec d)} {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {x₀ : Vec d}
    (hx₀ : vecDot e x₀ = ψ (x₀ - vecDot e x₀ • e)) {r : ℝ}
    (hch : ∀ y ∈ Metric.ball x₀ r, (y ∈ U ↔ vecDot e y < ψ (y - vecDot e y • e))) (i₀ : Fin d)
    {K : ℝ} (hK1 : 1 ≤ K)
    (hKlip : ∀ y z : Vec d, ‖flattenInv e ψ x₀ (-(basisVec i₀)) y -
        flattenInv e ψ x₀ (-(basisVec i₀)) z‖ ≤ K * ‖y - z‖)
    (m : ℤ) (hKr : K * (3 : ℝ) ^ m ≤ r) {x : Vec d} (hx : x ∈ openCubeSet (originCube d m)) :
    flattenInv e ψ x₀ (-(basisVec i₀)) (x - r3c_z0 i₀ m) ∈
      U ∩ Metric.ball x₀ (K * (3 : ℝ) ^ m) := by
  have hK0 : 0 < K := by linarith only [hK1]
  obtain ⟨h1, h2⟩ := r3e_Q_geom i₀ hx
  have hKn : K * ‖x - r3c_z0 i₀ m‖ < K * (3 : ℝ) ^ m := mul_lt_mul_of_pos_left h1 hK0
  refine ⟨(r3e_chartInv_mem_iff he hψ hx₀ hch i₀ hKlip (hKn.trans_le hKr)).2 h2, ?_⟩
  rw [Metric.mem_ball, dist_eq_norm]
  have h := hKlip (x - r3c_z0 i₀ m) 0
  rw [flattenInv_zero he ψ x₀ (-(basisVec i₀)), sub_zero] at h
  exact lt_of_le_of_lt h hKn

theorem r3e_push_mem {U : Set (Vec d)} {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {x₀ : Vec d}
    (hx₀ : vecDot e x₀ = ψ (x₀ - vecDot e x₀ • e)) {r : ℝ}
    (hch : ∀ y ∈ Metric.ball x₀ r, (y ∈ U ↔ vecDot e y < ψ (y - vecDot e y • e))) (i₀ : Fin d)
    {K : ℝ} (hK1 : 1 ≤ K)
    (hKlip : ∀ y z : Vec d, ‖flattenMap e ψ x₀ (-(basisVec i₀)) y -
        flattenMap e ψ x₀ (-(basisVec i₀)) z‖ ≤ K * ‖y - z‖)
    (m : ℤ) {ρ : ℝ} (hρr : ρ ≤ r) {y : Vec d} (hyU : y ∈ U)
    (hy : y ∈ Metric.ball x₀ ρ) :
    flattenMap e ψ x₀ (-(basisVec i₀)) y + r3c_z0 i₀ m ∈ r3e_F i₀ m (2 * K * ρ) := by
  have hK0 : 0 < K := by linarith only [hK1]
  rw [Metric.mem_ball, dist_eq_norm] at hy
  have hyr : y ∈ Metric.ball x₀ r := by
    rw [Metric.mem_ball, dist_eq_norm]; linarith only [hy, hρr]
  have hΨ : ‖flattenMap e ψ x₀ (-(basisVec i₀)) y‖ < K * ρ := by
    have h := hKlip y x₀
    rw [flattenMap_base, sub_zero] at h
    have h2 : K * ‖y - x₀‖ < K * ρ := mul_lt_mul_of_pos_left hy hK0
    linarith only [h, h2]
  have hpos : 0 < flattenMap e ψ x₀ (-(basisVec i₀)) y i₀ := by
    have h := mem_iff_flattenMap he hψ (r3e_u_unit i₀) hx₀ hch hyr
    rw [r3e_vecDot_u] at h
    have := h.1 hyU
    linarith only [this]
  have hcoord : ∀ i, |flattenMap e ψ x₀ (-(basisVec i₀)) y i| < K * ρ := fun i => by
    have := norm_le_pi_norm (flattenMap e ψ x₀ (-(basisVec i₀)) y) i
    rw [Real.norm_eq_abs] at this
    linarith only [this, hΨ]
  intro i _
  simp only [Set.mem_Ioo, Pi.add_apply, r3c_faceBase, r3e_z0_apply]
  have hb := abs_lt.1 (hcoord i)
  by_cases hi : i = i₀
  · subst hi
    simp only [ite_true, add_zero]
    constructor <;> linarith only [hpos, hb.2]
  · simp only [hi, ite_false]
    constructor <;> linarith only [hb.1, hb.2]

end SuperdiffusionCLT.Section7
