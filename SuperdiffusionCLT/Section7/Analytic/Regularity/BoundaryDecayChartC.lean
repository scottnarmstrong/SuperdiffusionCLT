/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.BoundaryDecayChartB
public import SuperdiffusionCLT.Section7.Analytic.Regularity.BoundaryDecayK

@[expose] public section

open Homogenization MeasureTheory Filter Topology Matrix
open scoped ENNReal NNReal

/-!
# The chart-flattened problem on the cube, with the flat face at the bottom

The flat boundary decay lives on the cube `Q_m` with the face `x_e = -3^m/2`.  The chart map with
target `u = -e_i` takes the solution domain to the side `x_i > -3^m/2` of this face, so a weak
solution in a `C^{1,1}` chart gives a weak solution on `Q_m` with localized zero trace on the
window of the face.
-/

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem r3e_u_unit (i₀ : Fin d) : vecNormSq (-(basisVec i₀) : Vec d) = 1 := by
  simp [vecNormSq, vecDot, basisVec, Pi.single_apply]

theorem r3e_vecDot_u (i₀ : Fin d) (w : Vec d) : vecDot (-(basisVec i₀) : Vec d) w = -w i₀ := by
  simp [vecDot, basisVec, Pi.single_apply]

theorem r3e_z0_apply (i₀ i : Fin d) (m : ℤ) :
    r3c_z0 i₀ m i = if i = i₀ then -((3 : ℝ) ^ m / 2) else 0 := rfl

theorem r3e_chartInv_mem_iff {U : Set (Vec d)} {e : Vec d} (he : vecNormSq e = 1)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {x₀ : Vec d}
    (hx₀ : vecDot e x₀ = ψ (x₀ - vecDot e x₀ • e)) {r : ℝ}
    (hch : ∀ y ∈ Metric.ball x₀ r, (y ∈ U ↔ vecDot e y < ψ (y - vecDot e y • e))) (i₀ : Fin d)
    {K : ℝ}
    (hKlip : ∀ y z : Vec d, ‖flattenInv e ψ x₀ (-(basisVec i₀)) y -
        flattenInv e ψ x₀ (-(basisVec i₀)) z‖ ≤ K * ‖y - z‖) {z : Vec d} (hz : K * ‖z‖ < r) :
    flattenInv e ψ x₀ (-(basisVec i₀)) z ∈ U ↔ 0 < z i₀ := by
  have hy : flattenInv e ψ x₀ (-(basisVec i₀)) z ∈ Metric.ball x₀ r := by
    rw [Metric.mem_ball, dist_eq_norm]
    have h := hKlip z 0
    rw [flattenInv_zero he ψ x₀ (-(basisVec i₀)), sub_zero] at h
    exact lt_of_le_of_lt h hz
  have h := mem_iff_flattenMap he hψ (r3e_u_unit i₀) hx₀ hch hy
  rw [flattenMap_flattenInv he hψ, r3e_vecDot_u, neg_lt_zero] at h
  exact h

theorem r3e_Q_geom {m : ℤ} (i₀ : Fin d) {x : Vec d} (hx : x ∈ openCubeSet (originCube d m)) :
    ‖x - r3c_z0 i₀ m‖ < (3 : ℝ) ^ m ∧ 0 < (x - r3c_z0 i₀ m) i₀ := by
  have hℓ : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  rw [mem_openCubeSet_originCube_iff] at hx
  refine ⟨(pi_norm_lt_iff hℓ).2 fun i => ?_, ?_⟩
  · rw [Real.norm_eq_abs, abs_lt, Pi.sub_apply, r3e_z0_apply]
    have := hx i
    by_cases hi : i = i₀
    · subst hi; simp only [ite_true]; constructor <;> linarith only [this.1, this.2, hℓ]
    · simp only [hi, ite_false]; constructor <;> linarith only [this.1, this.2, hℓ]
  · rw [Pi.sub_apply, r3e_z0_apply]
    simp only [ite_true]
    linarith only [(hx i₀).1]

theorem r3e_window_sub {m : ℤ} (i₀ : Fin d) {x : Vec d}
    (hT : ∀ i, |x i - r3c_z0 i₀ m i| < (3 : ℝ) ^ m / 2) (hpos : 0 < (x - r3c_z0 i₀ m) i₀) :
    x ∈ openCubeSet (originCube d m) := by
  have hℓ : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have h := abs_lt.1 (hT i)
  by_cases hi : i = i₀
  · subst hi
    rw [r3e_z0_apply] at h
    rw [Pi.sub_apply, r3e_z0_apply] at hpos
    simp only [ite_true] at h hpos
    constructor <;> linarith only [h.1, h.2, hℓ, hpos]
  · rw [r3e_z0_apply] at h
    simp only [hi, ite_false] at h
    constructor <;> linarith only [h.1, h.2, hℓ]

theorem r3e_window_norm {m : ℤ} (i₀ : Fin d) {x : Vec d}
    (hT : ∀ i, |x i - r3c_z0 i₀ m i| < (3 : ℝ) ^ m / 2) : ‖x - r3c_z0 i₀ m‖ < (3 : ℝ) ^ m := by
  have hℓ : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  refine (pi_norm_lt_iff hℓ).2 fun i => ?_
  rw [Real.norm_eq_abs, Pi.sub_apply]
  have := hT i
  linarith only [this, hℓ]

/-- **The chart-flattened problem on the cube with the face at the bottom.** -/
theorem r3e_transport [NeZero d] {U : Set (Vec d)} (hU : IsOpen U) {e : Vec d}
    (he : vecNormSq e = 1) {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {M₁ : ℝ}
    (hb1 : ∀ y, ‖fderiv ℝ ψ y‖ ≤ M₁) {x₀ : Vec d}
    (hx₀ : vecDot e x₀ = ψ (x₀ - vecDot e x₀ • e)) {r : ℝ}
    (hch : ∀ y ∈ Metric.ball x₀ r, (y ∈ U ↔ vecDot e y < ψ (y - vecDot e y • e))) (i₀ : Fin d)
    {K : ℝ} (hK1 : 1 ≤ K)
    (hKlip : ∀ y z : Vec d, ‖flattenInv e ψ x₀ (-(basisVec i₀)) y -
        flattenInv e ψ x₀ (-(basisVec i₀)) z‖ ≤ K * ‖y - z‖)
    (m : ℤ) (hKr : K * (3 : ℝ) ^ m ≤ r) (φ : H10Function U) {f : Vec d → ℝ}
    (hw : IsWeakSolutionOn (fun _ => (1 : Mat d)) U φ.toH1Function f (fun _ => 0)) :
    ∃ v : H1Function (openCubeSet (originCube d m)),
      (∀ x, v.toFun x =
        φ.toH1Function.toFun (flattenInv e ψ x₀ (-(basisVec i₀)) (x - r3c_z0 i₀ m))) ∧
      IsWeakSolutionOn
        (fun x => flattenCoeff e ψ x₀ (-(basisVec i₀)) (fun _ => (1 : Mat d)) (x - r3c_z0 i₀ m))
        (openCubeSet (originCube d m)) v
        (fun x => f (flattenInv e ψ x₀ (-(basisVec i₀)) (x - r3c_z0 i₀ m))) (fun _ => 0) ∧
      LocalizedZeroTraceFunctionOn (openCubeSet (originCube d m)) (r3d_window i₀ m) v.toFun := by
  have hℓ : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  have hK0 : 0 < K := by linarith only [hK1]
  have hD := p12_isOpen_chartDom he hψ (-(basisVec i₀)) x₀ (r3c_z0 i₀ m) hU
  have hQD : openCubeSet (originCube d m) ⊆
      p12_chartDom he hψ (-(basisVec i₀)) x₀ (r3c_z0 i₀ m) U := by
    intro x hx
    rw [p12_mem_chartDom]
    obtain ⟨h1, h2⟩ := r3e_Q_geom i₀ hx
    have hKn : K * ‖x - r3c_z0 i₀ m‖ < r :=
      lt_of_lt_of_le (mul_lt_mul_of_pos_left h1 hK0) hKr
    exact (r3e_chartInv_mem_iff he hψ hx₀ hch i₀ hKlip hKn).2 h2
  have hw' := p12_chartFun_weak he hψ hb1 (-(basisVec i₀)) x₀ (r3c_z0 i₀ m) φ hw
  have hg0 : (fun x => matVecMul (flattenLin e (projGradVec e ψ x₀) (-(basisVec i₀)) *
      shearJac e ψ (flattenInv e ψ x₀ (-(basisVec i₀)) (x - r3c_z0 i₀ m))) ((fun _ => (0 : Vec d))
        (flattenInv e ψ x₀ (-(basisVec i₀)) (x - r3c_z0 i₀ m)))) = fun _ => (0 : Vec d) := by
    funext x
    ext i
    simp [matVecMul]
  rw [hg0] at hw'
  refine ⟨(p12_chartFun he hψ hb1 (-(basisVec i₀)) x₀ (r3c_z0 i₀ m) φ).toH1Function.restrict
    (isOpen_openCubeSet _) hQD, fun x => p12_chartFun_toFun he hψ hb1 _ x₀ _ φ x,
    p12_restrict_weak hD (isOpen_openCubeSet _) hQD hw', ?_⟩
  refine p12_localized_zero_trace_restrict (isOpen_openCubeSet _) hQD ?_
    (p12_chartFun he hψ hb1 (-(basisVec i₀)) x₀ (r3c_z0 i₀ m) φ)
  rintro x ⟨hxT, hxD⟩
  have hxT' : ∀ i, |x i - r3c_z0 i₀ m i| < (3 : ℝ) ^ m / 2 := hxT
  have hKn : K * ‖x - r3c_z0 i₀ m‖ < r :=
    lt_of_lt_of_le (mul_lt_mul_of_pos_left (r3e_window_norm i₀ hxT') hK0) hKr
  rw [p12_mem_chartDom] at hxD
  exact r3e_window_sub i₀ hxT' ((r3e_chartInv_mem_iff he hψ hx₀ hch i₀ hKlip hKn).1 hxD)

end SuperdiffusionCLT.Section7
