/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.CZ.LocalD

/-!
# Local `W^{1,P}` estimates at a boundary point, in the original coordinates

The chart map `y ↦ Ψ y + τ` (`τ` the centre of the top face of the origin cube of scale `3^m`) takes
a boundary chart of `U` at `x₀` to a flat boundary.  `p12_transport` carries a weak solution
`φ ∈ H¹₀(U)` of the Laplace equation to a weak solution `v = φ ∘ (chart)⁻¹` on the cube, for the
coefficient `Ã(x - τ)` that is `ε`-close to the identity, with localized zero trace on the face.
`localW1p_boundary` applies `localW1p_flat` to `v` and transports the estimate back.

## Main results

* `localW1p_boundary`: the local `W^{1,P}` estimate at a boundary point.
* `localW1p_interior_domain`: the interior estimate on a triadic cube contained in `U`.
-/

@[expose] public section

open Homogenization MeasureTheory Matrix
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem p12_basis_unit (i : Fin d) : vecNormSq (basisVec i : Vec d) = 1 := by
  simp [vecNormSq, vecDot, basisVec, Pi.single_apply]

/-- The centre of the top face of the origin cube of scale `3^m`, in direction `i₀`. -/
noncomputable def p12_tau (m : ℤ) (i₀ : Fin d) : Vec d := ((3 : ℝ) ^ m / 2) • basisVec i₀

theorem p12_tau_apply (m : ℤ) (i₀ i : Fin d) :
    p12_tau m i₀ i = if i = i₀ then (3 : ℝ) ^ m / 2 else 0 := by
  simp [p12_tau, basisVec, Pi.single_apply]

theorem p12_isOpen_chartDom {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (u x₀ τ : Vec d) {U : Set (Vec d)} (hU : IsOpen U) :
    IsOpen (p12_chartDom he hψ u x₀ τ U) := by
  have : p12_chartDom he hψ u x₀ τ U = (p12_chartHomeo he hψ u x₀ τ).symm ⁻¹' U := by
    ext x
    rw [p12_mem_chartDom]
    rfl
  rw [this]
  exact hU.preimage (p12_chartHomeo he hψ u x₀ τ).symm.continuous

/-- Membership of a chart-flattened point in `U`: inside the chart ball it is the sign of the
vertical coordinate. -/
theorem p12_chartInv_mem_iff {U : Set (Vec d)} {e : Vec d} (he : vecNormSq e = 1)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {x₀ : Vec d}
    (hx₀ : vecDot e x₀ = ψ (x₀ - vecDot e x₀ • e)) {r : ℝ}
    (hch : ∀ y ∈ Metric.ball x₀ r, (y ∈ U ↔ vecDot e y < ψ (y - vecDot e y • e)))
    (i₀ : Fin d) {K : ℝ}
    (hKlip : ∀ y z : Vec d, ‖flattenInv e ψ x₀ (basisVec i₀) y - flattenInv e ψ x₀ (basisVec i₀) z‖ ≤
      K * ‖y - z‖) {z : Vec d} (hz : K * ‖z‖ < r) :
    flattenInv e ψ x₀ (basisVec i₀) z ∈ U ↔ z i₀ < 0 := by
  have hy : flattenInv e ψ x₀ (basisVec i₀) z ∈ Metric.ball x₀ r := by
    rw [Metric.mem_ball, dist_eq_norm]
    have h := hKlip z 0
    rw [flattenInv_zero he ψ x₀ (basisVec i₀), sub_zero] at h
    exact lt_of_le_of_lt h hz
  have h := mem_iff_flattenMap he hψ (p12_basis_unit i₀) hx₀ hch hy
  rw [flattenMap_flattenInv he hψ, vecDot_basisVec_left] at h
  exact h

theorem p12_tau_self (m : ℤ) (i₀ : Fin d) : p12_tau m i₀ i₀ = (3 : ℝ) ^ m / 2 := by
  rw [p12_tau_apply]; simp

theorem p12_tau_ne (m : ℤ) {i₀ i : Fin d} (hi : i ≠ i₀) : p12_tau m i₀ i = 0 := by
  rw [p12_tau_apply]; simp [hi]

theorem p12_Q_geom {m : ℤ} (i₀ : Fin d) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) :
    ‖x - p12_tau m i₀‖ < (3 : ℝ) ^ m ∧ (x - p12_tau m i₀) i₀ < 0 := by
  have hℓ : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  rw [mem_openCubeSet_originCube_iff] at hx
  refine ⟨(pi_norm_lt_iff hℓ).2 fun i => ?_, ?_⟩
  · rw [Real.norm_eq_abs, abs_lt, Pi.sub_apply]
    have := hx i
    by_cases hi : i = i₀
    · subst hi; rw [p12_tau_self]; constructor <;> linarith only [this.1, this.2, hℓ]
    · rw [p12_tau_ne m hi]; constructor <;> linarith only [this.1, this.2, hℓ]
  · rw [Pi.sub_apply, p12_tau_self]
    linarith only [(hx i₀).2]

theorem p12_window_sub {m : ℤ} (i₀ : Fin d) {x : Vec d}
    (hT : ∀ i, |x i - p12_tau m i₀ i| < (3 : ℝ) ^ m / 2) (hlt : (x - p12_tau m i₀) i₀ < 0) :
    x ∈ openCubeSet (originCube d m) := by
  have hℓ : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have h := abs_lt.1 (hT i)
  by_cases hi : i = i₀
  · subst hi
    rw [p12_tau_self] at h
    rw [Pi.sub_apply, p12_tau_self] at hlt
    constructor <;> linarith only [h.1, h.2, hℓ, hlt]
  · rw [p12_tau_ne m hi] at h
    constructor <;> linarith only [h.1, h.2, hℓ]

theorem p12_window_norm {m : ℤ} (i₀ : Fin d) {x : Vec d}
    (hT : ∀ i, |x i - p12_tau m i₀ i| < (3 : ℝ) ^ m / 2) :
    ‖x - p12_tau m i₀‖ < (3 : ℝ) ^ m := by
  have hℓ : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  refine (pi_norm_lt_iff hℓ).2 fun i => ?_
  rw [Real.norm_eq_abs, Pi.sub_apply]
  have := hT i
  linarith only [this, hℓ]

/-- **The chart-flattened problem on the origin cube.**  For a chart `(e, ψ)` of `U` at the boundary
point `x₀`, a weak solution `φ ∈ H¹₀(U)` of the Laplace equation with data `(f, g)` gives, on the
origin cube of scale `3^m` (small compared to the chart), an `H¹` function `v = φ ∘ Ψ'⁻¹`, a weak
solution of the transported equation, with localized zero trace in the window of radius `ℓ/2`
around the centre of the top face. -/
theorem p12_transport [NeZero d] {U : Set (Vec d)} (hU : IsOpen U) {e : Vec d}
    (he : vecNormSq e = 1) {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {M₁ : ℝ}
    (hb1 : ∀ y, ‖fderiv ℝ ψ y‖ ≤ M₁) {x₀ : Vec d}
    (hx₀ : vecDot e x₀ = ψ (x₀ - vecDot e x₀ • e)) {r : ℝ}
    (hch : ∀ y ∈ Metric.ball x₀ r, (y ∈ U ↔ vecDot e y < ψ (y - vecDot e y • e))) (i₀ : Fin d)
    {K : ℝ} (hK1 : 1 ≤ K)
    (hKlip : ∀ y z : Vec d, ‖flattenInv e ψ x₀ (basisVec i₀) y - flattenInv e ψ x₀ (basisVec i₀) z‖ ≤
      K * ‖y - z‖)
    (m : ℤ) (hKr : K * (3 : ℝ) ^ m ≤ r) (φ : H10Function U) {f : Vec d → ℝ} {g : Vec d → Vec d}
    (hw : IsWeakSolutionOn (fun _ => (1 : Mat d)) U φ.toH1Function f g) :
    ∃ v : H1Function (openCubeSet (originCube d m)),
      (∀ x, v.toFun x =
        φ.toH1Function.toFun (flattenInv e ψ x₀ (basisVec i₀) (x - p12_tau m i₀))) ∧
      (∀ x, v.grad x =
        (p12_chartFun he hψ hb1 (basisVec i₀) x₀ (p12_tau m i₀) φ).toH1Function.grad x) ∧
      IsWeakSolutionOn
        (fun x => flattenCoeff e ψ x₀ (basisVec i₀) (fun _ => (1 : Mat d)) (x - p12_tau m i₀))
        (openCubeSet (originCube d m)) v
        (fun x => f (flattenInv e ψ x₀ (basisVec i₀) (x - p12_tau m i₀)))
        (fun x => matVecMul (flattenLin e (projGradVec e ψ x₀) (basisVec i₀) *
            shearJac e ψ (flattenInv e ψ x₀ (basisVec i₀) (x - p12_tau m i₀)))
          (g (flattenInv e ψ x₀ (basisVec i₀) (x - p12_tau m i₀)))) ∧
      LocalizedZeroTraceFunctionOn (openCubeSet (originCube d m))
        {x | ∀ i, |x i - p12_tau m i₀ i| < cubeScaleFactor (originCube d m) / 2} v.toFun := by
  have hℓ : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  have hK0 : 0 < K := by linarith only [hK1]
  have hD := p12_isOpen_chartDom he hψ (basisVec i₀) x₀ (p12_tau m i₀) hU
  have hQD : openCubeSet (originCube d m) ⊆
      p12_chartDom he hψ (basisVec i₀) x₀ (p12_tau m i₀) U := by
    intro x hx
    rw [p12_mem_chartDom]
    obtain ⟨h1, h2⟩ := p12_Q_geom i₀ hx
    have hKn : K * ‖x - p12_tau m i₀‖ < r :=
      lt_of_lt_of_le (mul_lt_mul_of_pos_left h1 hK0) hKr
    exact (p12_chartInv_mem_iff he hψ hx₀ hch i₀ hKlip hKn).2 h2
  refine ⟨(p12_chartFun he hψ hb1 (basisVec i₀) x₀ (p12_tau m i₀) φ).toH1Function.restrict
    (isOpen_openCubeSet _) hQD, fun x => p12_chartFun_toFun he hψ hb1 _ x₀ _ φ x, fun x => rfl,
    p12_restrict_weak hD (isOpen_openCubeSet _) hQD
      (p12_chartFun_weak he hψ hb1 _ x₀ _ φ hw), ?_⟩
  refine p12_localized_zero_trace_restrict (isOpen_openCubeSet _) hQD ?_
    (p12_chartFun he hψ hb1 (basisVec i₀) x₀ (p12_tau m i₀) φ)
  rintro x ⟨hxT, hxD⟩
  have hxT' : ∀ i, |x i - p12_tau m i₀ i| < (3 : ℝ) ^ m / 2 := hxT
  have hKn : K * ‖x - p12_tau m i₀‖ < r :=
    lt_of_lt_of_le (mul_lt_mul_of_pos_left (p12_window_norm i₀ hxT') hK0) hKr
  rw [p12_mem_chartDom] at hxD
  exact p12_window_sub i₀ hxT' ((p12_chartInv_mem_iff he hψ hx₀ hch i₀ hKlip hKn).1 hxD)

theorem p12_smul_le {μ ν : Measure (Vec d)} (h : μ ≤ ν) (c : ℝ≥0∞) : c • μ ≤ c • ν := by
  rw [Measure.le_iff']
  intro s
  simp only [Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul_right (h s) c

/-- The `ℓ^d`-normalized restriction of the volume to a set `S`. -/
noncomputable def p12_nmeas (ℓ : ℝ) (S : Set (Vec d)) : Measure (Vec d) :=
  ENNReal.ofReal ((ℓ ^ d)⁻¹) • volume.restrict S

theorem p12_normalized_eq (m : ℤ) :
    normalizedCubeMeasure (originCube d m) =
      p12_nmeas ((3 : ℝ) ^ m) (openCubeSet (originCube d m)) := by
  rw [normalizedCubeMeasure_eq_smul]
  rfl

theorem p12_normalized_restrict (m : ℤ) {R : Set (Vec d)} (hR : MeasurableSet R) :
    (normalizedCubeMeasure (originCube d m)).restrict R =
      p12_nmeas ((3 : ℝ) ^ m) (R ∩ openCubeSet (originCube d m)) := by
  rw [p12_normalized_eq]
  unfold p12_nmeas
  rw [Measure.restrict_smul, Measure.restrict_restrict hR]

theorem p12_eLpNorm_pull_le {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (u x₀ τ : Vec d) {E : Type*} [NormedAddCommGroup E]
    (F : Vec d → E) (q : ℝ≥0∞) (ℓ : ℝ) {A S : Set (Vec d)}
    (hAS : (fun x => flattenInv e ψ x₀ u (x - τ)) '' A ⊆ S) :
    eLpNorm (fun x => F (flattenInv e ψ x₀ u (x - τ))) q (p12_nmeas ℓ A) ≤
      eLpNorm F q (p12_nmeas ℓ S) := by
  have h1 := p12_eLpNorm_chart he hψ u x₀ τ F q (ENNReal.ofReal ((ℓ ^ d)⁻¹))
    ((fun x => flattenInv e ψ x₀ u (x - τ)) '' A)
  have himg : (fun y => flattenMap e ψ x₀ u y + τ) ''
      ((fun x => flattenInv e ψ x₀ u (x - τ)) '' A) = A := by
    rw [Set.image_image]
    simp [flattenMap_flattenInv he hψ]
  rw [himg] at h1
  unfold p12_nmeas
  rw [h1]
  exact eLpNorm_mono_measure _ (p12_smul_le (Measure.restrict_mono hAS le_rfl) _)

theorem p12_eLpNorm_push_le {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (u x₀ τ : Vec d) {E : Type*} [NormedAddCommGroup E]
    (F : Vec d → E) (q : ℝ≥0∞) (ℓ : ℝ) {S A : Set (Vec d)}
    (hSA : (fun y => flattenMap e ψ x₀ u y + τ) '' S ⊆ A) :
    eLpNorm F q (p12_nmeas ℓ S) ≤
      eLpNorm (fun x => F (flattenInv e ψ x₀ u (x - τ))) q (p12_nmeas ℓ A) := by
  have h1 := p12_eLpNorm_chart he hψ u x₀ τ F q (ENNReal.ofReal ((ℓ ^ d)⁻¹)) S
  unfold p12_nmeas
  rw [← h1]
  exact eLpNorm_mono_measure _ (p12_smul_le (Measure.restrict_mono hSA le_rfl) _)

/-- Points of the cube pull back into `U ∩ B(x₀, Kℓ)`. -/
theorem p12_pull_mem {U : Set (Vec d)} {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {x₀ : Vec d}
    (hx₀ : vecDot e x₀ = ψ (x₀ - vecDot e x₀ • e)) {r : ℝ}
    (hch : ∀ y ∈ Metric.ball x₀ r, (y ∈ U ↔ vecDot e y < ψ (y - vecDot e y • e))) (i₀ : Fin d)
    {K : ℝ} (hK1 : 1 ≤ K)
    (hKlip : ∀ y z : Vec d, ‖flattenInv e ψ x₀ (basisVec i₀) y - flattenInv e ψ x₀ (basisVec i₀) z‖ ≤
      K * ‖y - z‖)
    (m : ℤ) (hKr : K * (3 : ℝ) ^ m ≤ r) {x : Vec d} (hx : x ∈ openCubeSet (originCube d m)) :
    flattenInv e ψ x₀ (basisVec i₀) (x - p12_tau m i₀) ∈ U ∩ Metric.ball x₀ (K * (3 : ℝ) ^ m) := by
  have hK0 : 0 < K := by linarith only [hK1]
  obtain ⟨h1, h2⟩ := p12_Q_geom i₀ hx
  have hKn : K * ‖x - p12_tau m i₀‖ < K * (3 : ℝ) ^ m := mul_lt_mul_of_pos_left h1 hK0
  refine ⟨(p12_chartInv_mem_iff he hψ hx₀ hch i₀ hKlip (hKn.trans_le hKr)).2 h2, ?_⟩
  rw [Metric.mem_ball, dist_eq_norm]
  have h := hKlip (x - p12_tau m i₀) 0
  rw [flattenInv_zero he ψ x₀ (basisVec i₀), sub_zero] at h
  exact lt_of_le_of_lt h hKn

/-- Points of `U` near `x₀` are mapped into the half-width box of the cube. -/
theorem p12_push_mem {U : Set (Vec d)} {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {x₀ : Vec d}
    (hx₀ : vecDot e x₀ = ψ (x₀ - vecDot e x₀ • e)) {r : ℝ}
    (hch : ∀ y ∈ Metric.ball x₀ r, (y ∈ U ↔ vecDot e y < ψ (y - vecDot e y • e))) (i₀ : Fin d)
    {K : ℝ} (hK1 : 1 ≤ K)
    (hKlip : ∀ y z : Vec d, ‖flattenMap e ψ x₀ (basisVec i₀) y - flattenMap e ψ x₀ (basisVec i₀) z‖ ≤
      K * ‖y - z‖)
    (m : ℤ) (hKr : K * (3 : ℝ) ^ m ≤ r) {y : Vec d} (hyU : y ∈ U)
    (hy : y ∈ Metric.ball x₀ ((3 : ℝ) ^ m / (4 * K))) :
    flattenMap e ψ x₀ (basisVec i₀) y + p12_tau m i₀ ∈
      p12_box (p12_tau m i₀) ((3 : ℝ) ^ m / 4) ∩ openCubeSet (originCube d m) := by
  have hℓ : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  have hK0 : 0 < K := by linarith only [hK1]
  rw [Metric.mem_ball, dist_eq_norm] at hy
  have hyr : y ∈ Metric.ball x₀ r := by
    rw [Metric.mem_ball, dist_eq_norm]
    have h4 : (3 : ℝ) ^ m / (4 * K) ≤ (3 : ℝ) ^ m := by
      rw [div_le_iff₀ (by positivity)]; nlinarith only [hℓ, hK1]
    have : (3 : ℝ) ^ m ≤ K * (3 : ℝ) ^ m := by nlinarith only [hℓ, hK1]
    linarith only [hy, h4, this, hKr]
  have hΨ : ‖flattenMap e ψ x₀ (basisVec i₀) y‖ < (3 : ℝ) ^ m / 4 := by
    have h := hKlip y x₀
    rw [flattenMap_base] at h
    simp only [sub_zero] at h
    have h2 : K * ‖y - x₀‖ < K * ((3 : ℝ) ^ m / (4 * K)) := mul_lt_mul_of_pos_left hy hK0
    have h3 : K * ((3 : ℝ) ^ m / (4 * K)) = (3 : ℝ) ^ m / 4 := by field_simp
    linarith only [h, h2, h3]
  have hneg : flattenMap e ψ x₀ (basisVec i₀) y i₀ < 0 := by
    have h := mem_iff_flattenMap he hψ (p12_basis_unit i₀) hx₀ hch hyr
    rw [vecDot_basisVec_left] at h
    exact h.1 hyU
  have hcoord : ∀ i, |flattenMap e ψ x₀ (basisVec i₀) y i| < (3 : ℝ) ^ m / 4 := fun i => by
    have := norm_le_pi_norm (flattenMap e ψ x₀ (basisVec i₀) y) i
    rw [Real.norm_eq_abs] at this
    linarith only [this, hΨ]
  have hsub : flattenMap e ψ x₀ (basisVec i₀) y + p12_tau m i₀ - p12_tau m i₀ =
      flattenMap e ψ x₀ (basisVec i₀) y := by abel
  refine ⟨fun i => ?_, ?_⟩
  · show |(flattenMap e ψ x₀ (basisVec i₀) y + p12_tau m i₀) i - p12_tau m i₀ i| ≤ (3 : ℝ) ^ m / 4
    rw [Pi.add_apply, add_sub_cancel_right]
    exact (hcoord i).le
  · refine p12_window_sub i₀ (fun i => ?_) (by rw [hsub]; exact hneg)
    rw [Pi.add_apply, add_sub_cancel_right]
    linarith only [hcoord i, hℓ]

theorem p12_jacField_continuous {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (u x₀ τ : Vec d) (i j : Fin d) :
    Continuous (fun x => (flattenLin e (projGradVec e ψ x₀) u *
      shearJac e ψ (flattenInv e ψ x₀ u (x - τ))) i j) := by
  have hc : Continuous (fun x => flattenInv e ψ x₀ u (x - τ)) :=
    (p12_chartHomeo he hψ u x₀ τ).symm.continuous
  have hp : ∀ k, Continuous (fun x => projGradVec e ψ (flattenInv e ψ x₀ u (x - τ)) k) :=
    fun k => (contDiff_projGrad hψ k).continuous.comp hc
  simp only [Matrix.mul_apply, shearJac, Matrix.sub_apply, Matrix.one_apply,
    Matrix.vecMulVec_apply]
  refine continuous_finsetSum _ fun k _ => continuous_const.mul ?_
  exact continuous_const.sub (continuous_const.mul (hp j))

theorem p12_memLp_pull {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (u x₀ τ : Vec d) {E : Type*} [NormedAddCommGroup E]
    (F : Vec d → E) (q : ℝ≥0∞) (m : ℤ) {S : Set (Vec d)}
    (hS : (fun x => flattenInv e ψ x₀ u (x - τ)) '' openCubeSet (originCube d m) ⊆ S)
    (hF : MemLp F q (volume.restrict S)) :
    MemLp (fun x => F (flattenInv e ψ x₀ u (x - τ))) q (normalizedCubeMeasure (originCube d m)) := by
  unfold MemLp
  rw [p12_normalized_eq]
  refine lt_of_le_of_lt (p12_eLpNorm_pull_le he hψ u x₀ τ F q ((3 : ℝ) ^ m) hS) ?_
  exact (hF.smul_measure ENNReal.ofReal_ne_top).eLpNorm_lt_top

theorem p12_chartInv_measurePreserving {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (u x₀ τ : Vec d) :
    MeasurePreserving (fun x => flattenInv e ψ x₀ u (x - τ)) volume volume := by
  have h : MeasurePreserving (p12_chartHomeo he hψ u x₀ τ).toMeasurableEquiv volume volume :=
    p12_chartMap_measurePreserving he hψ u x₀ τ
  exact h.symm _

theorem p12_aesm_pull {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (u x₀ τ : Vec d) {U : Set (Vec d)} {E : Type*}
    [NormedAddCommGroup E] {F : Vec d → E} (hF : AEStronglyMeasurable F (volume.restrict U)) :
    AEStronglyMeasurable (fun x => F (flattenInv e ψ x₀ u (x - τ)))
      (volume.restrict (p12_chartDom he hψ u x₀ τ U)) := by
  have hemb : MeasurableEmbedding (fun x => flattenInv e ψ x₀ u (x - τ)) :=
    (p12_chartHomeo he hψ u x₀ τ).symm.measurableEmbedding
  have hmp := (p12_chartInv_measurePreserving he hψ u x₀ τ).restrict_preimage_emb hemb U
  have hset : (fun x => flattenInv e ψ x₀ u (x - τ)) ⁻¹' U = p12_chartDom he hψ u x₀ τ U := by
    ext x; rw [p12_mem_chartDom]; rfl
  rw [hset] at hmp
  exact hF.comp_measurePreserving hmp

theorem p12_aesm_pull_nmeas {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (u x₀ τ : Vec d) {U : Set (Vec d)} {E : Type*}
    [NormedAddCommGroup E] {F : Vec d → E} (hF : AEStronglyMeasurable F (volume.restrict U))
    (ℓ : ℝ) {A : Set (Vec d)} (hA : A ⊆ p12_chartDom he hψ u x₀ τ U) :
    AEStronglyMeasurable (fun x => F (flattenInv e ψ x₀ u (x - τ))) (p12_nmeas ℓ A) := by
  refine (p12_aesm_pull he hψ u x₀ τ hF).mono_ac ?_
  unfold p12_nmeas
  exact (Measure.smul_absolutelyContinuous).trans (Measure.restrict_mono hA le_rfl).absolutelyContinuous

/-- **Local `W^{1,P}` estimate at a boundary point, in the original coordinates.**  Let `U` be open
with a `C^{1,1}` chart `(e, ψ)` (`‖Dψ‖ ≤ M₁`, `Dψ` `M₂`-Lipschitz) of radius `r` at the boundary point
`x₀`, and let `φ ∈ H¹₀(U)` be a weak solution of `-Δφ = f - ∇·g`.  At every triadic scale `ℓ = 3^m`
with `L(d, M₁, M₂) ℓ ≤ ε` and `K ℓ ≤ r` (`ε`, `K` depending only on `d`, `M₁`, `P`), the gradient of `φ`
is in `L̲^P` on `U ∩ B(x₀, ℓ/(4K))`, with
`ℓ ‖∇φ‖_{L̲^P} ≤ C (ℓ ‖∇φ‖_{L̲²} + ‖φ‖_{L̲²} + ℓ² ‖f‖_{L̲^{p_*}} + ℓ ‖g‖_{L̲^P})`,
the right side measured on `U ∩ B(x₀, Kℓ)`, with norms normalized by `ℓ^d`; `1/p_* = 1/P + 1/d`. -/
theorem localW1p_boundary [NeZero d] (hd : 2 ≤ d) {P : ℝ} (hP : 2 ≤ P) (M₁ : ℝ) :
    ∃ ε C K : ℝ, 0 < ε ∧ 0 < C ∧ 1 ≤ K ∧
      ∀ (U : Set (Vec d)) (e : Vec d) (ψ : Vec d → ℝ) (x₀ : Vec d) (r M₂ : ℝ) (m : ℤ),
        IsOpen U → vecNormSq e = 1 → ContDiff ℝ (⊤ : ℕ∞) ψ → (∀ y, ‖fderiv ℝ ψ y‖ ≤ M₁) →
        (∀ y z, ‖fderiv ℝ ψ y - fderiv ℝ ψ z‖ ≤ M₂ * ‖y - z‖) →
        vecDot e x₀ = ψ (x₀ - vecDot e x₀ • e) →
        (∀ y ∈ Metric.ball x₀ r, (y ∈ U ↔ vecDot e y < ψ (y - vecDot e y • e))) →
        flattenLipConst d M₁ M₂ * (3 : ℝ) ^ m ≤ ε → K * (3 : ℝ) ^ m ≤ r →
        ∀ (φ : H10Function U) (f : Vec d → ℝ) (g : Vec d → Vec d),
          IsWeakSolutionOn (fun _ => (1 : Mat d)) U φ.toH1Function f g →
          MemLp f 2 (volume.restrict (U ∩ Metric.ball x₀ (K * (3 : ℝ) ^ m))) →
          MemLp f (ENNReal.ofReal (p12_pstar d P))
            (volume.restrict (U ∩ Metric.ball x₀ (K * (3 : ℝ) ^ m))) →
          MemLp g (ENNReal.ofReal P) (volume.restrict (U ∩ Metric.ball x₀ (K * (3 : ℝ) ^ m))) →
          MemLp φ.toH1Function.grad (ENNReal.ofReal P)
              (p12_nmeas ((3 : ℝ) ^ m) (U ∩ Metric.ball x₀ ((3 : ℝ) ^ m / (4 * K)))) ∧
            ENNReal.ofReal ((3 : ℝ) ^ m) *
                eLpNorm φ.toH1Function.grad (ENNReal.ofReal P)
                  (p12_nmeas ((3 : ℝ) ^ m) (U ∩ Metric.ball x₀ ((3 : ℝ) ^ m / (4 * K)))) ≤
              ENNReal.ofReal C *
                ((ENNReal.ofReal ((3 : ℝ) ^ m) *
                      eLpNorm φ.toH1Function.grad 2
                        (p12_nmeas ((3 : ℝ) ^ m) (U ∩ Metric.ball x₀ (K * (3 : ℝ) ^ m))) +
                    eLpNorm φ.toH1Function.toFun 2
                      (p12_nmeas ((3 : ℝ) ^ m) (U ∩ Metric.ball x₀ (K * (3 : ℝ) ^ m)))) +
                  ENNReal.ofReal ((3 : ℝ) ^ m) ^ 2 *
                    eLpNorm f (ENNReal.ofReal (p12_pstar d P))
                      (p12_nmeas ((3 : ℝ) ^ m) (U ∩ Metric.ball x₀ (K * (3 : ℝ) ^ m))) +
                  ENNReal.ofReal ((3 : ℝ) ^ m) *
                    eLpNorm g (ENNReal.ofReal P)
                      (p12_nmeas ((3 : ℝ) ^ m) (U ∩ Metric.ball x₀ (K * (3 : ℝ) ^ m)))) := by
  obtain ⟨ε, C₀, hε, hC₀, H⟩ := localW1p_flat hd hP
  obtain ⟨Kl, hKl1, HKl⟩ := p12_chart_lip d M₁
  obtain ⟨Kj, hKj1, HKj⟩ := p12_chart_jac_le d M₁
  obtain ⟨Kg, hKg1, HKg⟩ := p12_chartFun_grad_le d M₁
  set Km : ℝ := max Kg Kj with hKm
  have hKm1 : 1 ≤ Km := hKg1.trans (le_max_left _ _)
  refine ⟨ε, Kg * C₀ * Km, Kl, hε, by positivity, hKl1, ?_⟩
  intro U e ψ x₀ r M₂ m hU he hψ hb1 hb2 hx₀ hch hE hKr φ f g hw hf2 hfp hgP
  have hℓ : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  have hu : vecNormSq (basisVec (0 : Fin d) : Vec d) = 1 := p12_basis_unit 0
  have hKlipI : ∀ y z : Vec d, ‖flattenInv e ψ x₀ (basisVec 0) y - flattenInv e ψ x₀ (basisVec 0) z‖ ≤
      Kl * ‖y - z‖ := fun y z => (HKl he hψ hb1 hu x₀ y z).2
  have hKlipF : ∀ y z : Vec d, ‖flattenMap e ψ x₀ (basisVec 0) y - flattenMap e ψ x₀ (basisVec 0) z‖ ≤
      Kl * ‖y - z‖ := fun y z => (HKl he hψ hb1 hu x₀ y z).1
  set ℓ : ℝ := (3 : ℝ) ^ m with hℓdef
  set Q : TriadicCube d := originCube d m with hQ
  set τ : Vec d := p12_tau m 0 with hτ
  set S : Set (Vec d) := U ∩ Metric.ball x₀ (Kl * ℓ) with hS
  have hKl0 : 0 < Kl := by linarith only [hKl1]
  have hDQ : openCubeSet Q ⊆ p12_chartDom he hψ (basisVec 0) x₀ τ U := by
    intro x hx
    rw [p12_mem_chartDom]
    exact (p12_pull_mem he hψ hx₀ hch 0 hKl1 hKlipI m hKr hx).1
  have hpullS : (fun x => flattenInv e ψ x₀ (basisVec 0) (x - τ)) '' openCubeSet Q ⊆ S := by
    rintro _ ⟨x, hx, rfl⟩
    exact p12_pull_mem he hψ hx₀ hch 0 hKl1 hKlipI m hKr hx
  set A : CoeffField d := fun x =>
    flattenCoeff e ψ x₀ (basisVec 0) (fun _ => (1 : Mat d)) (x - τ) with hA
  set Mx : Vec d → Mat d := fun x => flattenLin e (projGradVec e ψ x₀) (basisVec 0) *
    shearJac e ψ (flattenInv e ψ x₀ (basisVec 0) (x - τ)) with hMx
  set f₂ : Vec d → ℝ := fun x => f (flattenInv e ψ x₀ (basisVec 0) (x - τ)) with hf₂
  set g₂ : Vec d → Vec d := fun x =>
    matVecMul (Mx x) (g (flattenInv e ψ x₀ (basisVec 0) (x - τ))) with hg₂
  have hf₂2 : MemLp f₂ 2 (normalizedCubeMeasure Q) :=
    p12_memLp_pull he hψ _ x₀ τ f 2 m hpullS hf2
  have hf₂p : MemLp f₂ (ENNReal.ofReal (p12_pstar d P)) (normalizedCubeMeasure Q) :=
    p12_memLp_pull he hψ _ x₀ τ f _ m hpullS hfp
  have hgc : MemLp (fun x => g (flattenInv e ψ x₀ (basisVec 0) (x - τ))) (ENNReal.ofReal P)
      (normalizedCubeMeasure Q) := p12_memLp_pull he hψ _ x₀ τ g _ m hpullS hgP
  have hMeas : ∀ i j, AEStronglyMeasurable (fun x => Mx x i j) (volume.restrict (openCubeSet Q)) :=
    fun i j => (p12_jacField_continuous he hψ _ x₀ τ i j).aestronglyMeasurable
  have hg₂aesm : AEStronglyMeasurable g₂ (normalizedCubeMeasure Q) :=
    p12_aesm_matVec Q hMeas hgc.aestronglyMeasurable
  have hg₂pt : ∀ x, ‖g₂ x‖ ≤ Kj * ‖g (flattenInv e ψ x₀ (basisVec 0) (x - τ))‖ := fun x =>
    HKj he hψ hb1 hu x₀ _ _
  have hg₂P : MemLp g₂ (ENNReal.ofReal P) (normalizedCubeMeasure Q) :=
    hgc.of_le_mul hg₂aesm (Filter.Eventually.of_forall hg₂pt)
  have hM₁ : 0 ≤ M₁ := (norm_nonneg _).trans (hb1 0)
  have hM₂ : 0 ≤ M₂ := flatten_nonneg_of_lipschitz hb2 (0 : Fin d)
  have hE0 : 0 ≤ flattenLipConst d M₁ M₂ := by unfold flattenLipConst; positivity
  have hAε : ∀ x ∈ openCubeSet Q, ∀ i j, |A x i j - (1 : Mat d) i j| ≤ ε := by
    intro x hx i j
    have h1 := flattenCoeff_one_sub_le he hψ hb1 hb2 (u := basisVec 0) x₀ (x - τ) i j
    have h2 : ‖x - τ‖ < ℓ := (p12_Q_geom 0 hx).1
    calc |A x i j - (1 : Mat d) i j| ≤ flattenLipConst d M₁ M₂ * ‖x - τ‖ := h1
      _ ≤ flattenLipConst d M₁ M₂ * ℓ := mul_le_mul_of_nonneg_left h2.le hE0
      _ ≤ ε := hE
  have hAmeas : ∀ i j, AEStronglyMeasurable (fun x => A x i j) (volume.restrict (openCubeSet Q)) :=
    fun i j => (p12_chartCoeff_continuous he hψ (u := basisVec 0) x₀ τ i j).aestronglyMeasurable
  obtain ⟨v, hvf, hvg, hvw, hvZ⟩ := p12_transport hU he hψ hb1 hx₀ hch 0 hKl1 hKlipI m hKr φ hw
  obtain ⟨hmemv, hbv⟩ := H Q τ A hAmeas hAε f₂ g₂ v hvw hf₂2 hf₂p hg₂P hvZ
  have hμQ : normalizedCubeMeasure Q = p12_nmeas ℓ (openCubeSet Q) := p12_normalized_eq m
  have hvg2 : MemLp v.grad 2 (normalizedCubeMeasure Q) :=
    memLp_normalized_of_memVectorL2 Q v.grad_memVectorL2
  have hφgrad : AEStronglyMeasurable φ.toH1Function.grad (volume.restrict U) :=
    AEMeasurable.aestronglyMeasurable
      (aemeasurable_pi_iff.2 fun i => (φ.toH1Function.gradMemL2 i).aestronglyMeasurable.aemeasurable)
  -- the energy and zeroth order terms
  have hn1 : Section2.Norms.cubeLpENorm Q 2 v.grad ≤
      ENNReal.ofReal Kg * eLpNorm φ.toH1Function.grad 2 (p12_nmeas ℓ S) := by
    unfold Section2.Norms.cubeLpENorm
    have hpt : ∀ x, ‖v.grad x‖ ≤ Kg *
        ‖φ.toH1Function.grad (flattenInv e ψ x₀ (basisVec 0) (x - τ))‖ := fun x => by
      rw [hvg x]; exact (HKg he hψ hb1 hu x₀ τ φ x).1
    refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul hvg2.aestronglyMeasurable
      (Filter.Eventually.of_forall hpt) 2).trans ?_
    refine mul_le_mul_right ?_ _
    rw [hμQ]
    exact p12_eLpNorm_pull_le he hψ _ x₀ τ φ.toH1Function.grad 2 ℓ hpullS
  have hn2 : Section2.Norms.cubeLpENorm Q 2 v.toFun ≤ eLpNorm φ.toH1Function.toFun 2 (p12_nmeas ℓ S) := by
    unfold Section2.Norms.cubeLpENorm
    rw [show v.toFun = fun x => φ.toH1Function.toFun (flattenInv e ψ x₀ (basisVec 0) (x - τ)) from
      funext hvf, hμQ]
    exact p12_eLpNorm_pull_le he hψ _ x₀ τ φ.toH1Function.toFun 2 ℓ hpullS
  have hn3 : Section2.Norms.cubeLpENorm Q (ENNReal.ofReal (p12_pstar d P)) f₂ ≤
      eLpNorm f (ENNReal.ofReal (p12_pstar d P)) (p12_nmeas ℓ S) := by
    unfold Section2.Norms.cubeLpENorm
    rw [hμQ]
    exact p12_eLpNorm_pull_le he hψ _ x₀ τ f _ ℓ hpullS
  have hn4 : Section2.Norms.cubeLpENorm Q (ENNReal.ofReal P) g₂ ≤
      ENNReal.ofReal Kj * eLpNorm g (ENNReal.ofReal P) (p12_nmeas ℓ S) := by
    unfold Section2.Norms.cubeLpENorm
    refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul hg₂aesm (Filter.Eventually.of_forall hg₂pt) _).trans ?_
    refine mul_le_mul_right ?_ _
    rw [hμQ]
    exact p12_eLpNorm_pull_le he hψ _ x₀ τ g _ ℓ hpullS
  -- the left side
  set R : Set (Vec d) := p12_box τ (ℓ / 4) with hR
  have hRm : MeasurableSet R := p12_box_measurable τ _
  have hSout : (fun y => flattenMap e ψ x₀ (basisVec 0) y + τ) ''
      (U ∩ Metric.ball x₀ (ℓ / (4 * Kl))) ⊆ R ∩ openCubeSet Q := by
    rintro _ ⟨y, ⟨hyU, hyb⟩, rfl⟩
    exact p12_push_mem he hψ hx₀ hch 0 hKl1 hKlipF m hKr hyU hyb
  have hl1 : eLpNorm φ.toH1Function.grad (ENNReal.ofReal P)
        (p12_nmeas ℓ (U ∩ Metric.ball x₀ (ℓ / (4 * Kl)))) ≤
      eLpNorm (fun x => φ.toH1Function.grad (flattenInv e ψ x₀ (basisVec 0) (x - τ)))
        (ENNReal.ofReal P) (p12_nmeas ℓ (R ∩ openCubeSet Q)) :=
    p12_eLpNorm_push_le he hψ _ x₀ τ φ.toH1Function.grad _ ℓ hSout
  have hl2 : eLpNorm (fun x => φ.toH1Function.grad (flattenInv e ψ x₀ (basisVec 0) (x - τ)))
        (ENNReal.ofReal P) (p12_nmeas ℓ (R ∩ openCubeSet Q)) ≤
      ENNReal.ofReal Kg * eLpNorm v.grad (ENNReal.ofReal P) ((normalizedCubeMeasure Q).restrict R) := by
    rw [p12_normalized_restrict m hRm]
    have hpt : ∀ x, ‖φ.toH1Function.grad (flattenInv e ψ x₀ (basisVec 0) (x - τ))‖ ≤
        Kg * ‖v.grad x‖ := fun x => by
      rw [hvg x]; exact (HKg he hψ hb1 hu x₀ τ φ x).2
    have hmeas := p12_aesm_pull_nmeas he hψ (basisVec 0) x₀ τ hφgrad ℓ
      (A := R ∩ openCubeSet Q) (Set.inter_subset_right.trans hDQ)
    exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul hmeas (Filter.Eventually.of_forall hpt) _
  have hsc : cubeScaleFactor Q = ℓ := rfl
  rw [hsc] at hmemv hbv
  set L : ℝ≥0∞ := ENNReal.ofReal ℓ with hL
  set a1 : ℝ≥0∞ := eLpNorm φ.toH1Function.grad 2 (p12_nmeas ℓ S) with ha1
  set a2 : ℝ≥0∞ := eLpNorm φ.toH1Function.toFun 2 (p12_nmeas ℓ S) with ha2
  set a3 : ℝ≥0∞ := eLpNorm f (ENNReal.ofReal (p12_pstar d P)) (p12_nmeas ℓ S) with ha3
  set a4 : ℝ≥0∞ := eLpNorm g (ENNReal.ofReal P) (p12_nmeas ℓ S) with ha4
  have hKm1' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal Km := ENNReal.one_le_ofReal.2 hKm1
  have hKgm : ENNReal.ofReal Kg ≤ ENNReal.ofReal Km := ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hKjm : ENNReal.ofReal Kj ≤ ENNReal.ofReal Km := ENNReal.ofReal_le_ofReal (le_max_right _ _)
  have h1 : L * Section2.Norms.cubeLpENorm Q 2 v.grad ≤ ENNReal.ofReal Km * (L * a1) :=
    calc L * Section2.Norms.cubeLpENorm Q 2 v.grad ≤ L * (ENNReal.ofReal Kg * a1) :=
          mul_le_mul_right hn1 _
      _ = ENNReal.ofReal Kg * (L * a1) := by ring
      _ ≤ ENNReal.ofReal Km * (L * a1) := mul_le_mul_left hKgm _
  have h2 : Section2.Norms.cubeLpENorm Q 2 v.toFun ≤ ENNReal.ofReal Km * a2 :=
    hn2.trans (le_mul_of_one_le_left zero_le hKm1')
  have h3 : L ^ 2 * Section2.Norms.cubeLpENorm Q (ENNReal.ofReal (p12_pstar d P)) f₂ ≤
      ENNReal.ofReal Km * (L ^ 2 * a3) :=
    (mul_le_mul_right hn3 _).trans (le_mul_of_one_le_left zero_le hKm1')
  have h4 : L * Section2.Norms.cubeLpENorm Q (ENNReal.ofReal P) g₂ ≤
      ENNReal.ofReal Km * (L * a4) :=
    calc L * Section2.Norms.cubeLpENorm Q (ENNReal.ofReal P) g₂ ≤ L * (ENNReal.ofReal Kj * a4) :=
          mul_le_mul_right hn4 _
      _ = ENNReal.ofReal Kj * (L * a4) := by ring
      _ ≤ ENNReal.ofReal Km * (L * a4) := mul_le_mul_left hKjm _
  have hN : (L * Section2.Norms.cubeLpENorm Q 2 v.grad + Section2.Norms.cubeLpENorm Q 2 v.toFun) +
      L ^ 2 * Section2.Norms.cubeLpENorm Q (ENNReal.ofReal (p12_pstar d P)) f₂ +
      L * Section2.Norms.cubeLpENorm Q (ENNReal.ofReal P) g₂ ≤
      ENNReal.ofReal Km * ((L * a1 + a2) + L ^ 2 * a3 + L * a4) := by
    calc _ ≤ (ENNReal.ofReal Km * (L * a1) + ENNReal.ofReal Km * a2) +
          ENNReal.ofReal Km * (L ^ 2 * a3) + ENNReal.ofReal Km * (L * a4) := by gcongr
      _ = _ := by ring
  have hmain : L * eLpNorm φ.toH1Function.grad (ENNReal.ofReal P)
        (p12_nmeas ℓ (U ∩ Metric.ball x₀ (ℓ / (4 * Kl)))) ≤
      ENNReal.ofReal Kg * (L * eLpNorm v.grad (ENNReal.ofReal P)
        ((normalizedCubeMeasure Q).restrict R)) :=
    calc L * eLpNorm φ.toH1Function.grad (ENNReal.ofReal P)
          (p12_nmeas ℓ (U ∩ Metric.ball x₀ (ℓ / (4 * Kl)))) ≤
        L * (ENNReal.ofReal Kg * eLpNorm v.grad (ENNReal.ofReal P)
          ((normalizedCubeMeasure Q).restrict R)) := mul_le_mul_right (hl1.trans hl2) _
      _ = _ := by ring
  refine ⟨lt_of_le_of_lt (hl1.trans hl2) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hmemv), ?_⟩
  calc L * eLpNorm φ.toH1Function.grad (ENNReal.ofReal P)
        (p12_nmeas ℓ (U ∩ Metric.ball x₀ (ℓ / (4 * Kl)))) ≤
      ENNReal.ofReal Kg * (L * eLpNorm v.grad (ENNReal.ofReal P)
        ((normalizedCubeMeasure Q).restrict R)) := hmain
    _ ≤ ENNReal.ofReal Kg * (ENNReal.ofReal C₀ * ((L * Section2.Norms.cubeLpENorm Q 2 v.grad +
          Section2.Norms.cubeLpENorm Q 2 v.toFun) +
        L ^ 2 * Section2.Norms.cubeLpENorm Q (ENNReal.ofReal (p12_pstar d P)) f₂ +
        L * Section2.Norms.cubeLpENorm Q (ENNReal.ofReal P) g₂)) := mul_le_mul_right hbv _
    _ ≤ ENNReal.ofReal Kg * (ENNReal.ofReal C₀ * (ENNReal.ofReal Km *
          ((L * a1 + a2) + L ^ 2 * a3 + L * a4))) := by gcongr
    _ = ENNReal.ofReal (Kg * C₀ * Km) * ((L * a1 + a2) + L ^ 2 * a3 + L * a4) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]; ring

/-- **Interior estimate for a solution on a domain `U`.**  For a triadic cube `Q` with
`Q ⊆ U`, the gradient of a weak solution `u ∈ H¹(U)` (tested against `H¹₀(U)`) is in `L̲^P` on the
concentric box of radius `ℓ/4`. -/
theorem localW1p_interior_domain [NeZero d] (hd : 2 ≤ d) {P : ℝ} (hP : 2 ≤ P) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ (U : Set (Vec d)) (Q : TriadicCube d) (A : CoeffField d),
      IsOpen U → openCubeSet Q ⊆ U →
      (∀ i j, AEStronglyMeasurable (fun x => A x i j) (volume.restrict (openCubeSet Q))) →
      (∀ x ∈ openCubeSet Q, ∀ i j, |A x i j - (1 : Mat d) i j| ≤ ε) →
      ∀ (f : Vec d → ℝ) (g : Vec d → Vec d) (u : H1Function U),
        IsWeakSolutionOn A U u f g →
        MemLp f 2 (normalizedCubeMeasure Q) →
        MemLp f (ENNReal.ofReal (p12_pstar d P)) (normalizedCubeMeasure Q) →
        MemLp g (ENNReal.ofReal P) (normalizedCubeMeasure Q) →
        MemLp u.grad (ENNReal.ofReal P)
            ((normalizedCubeMeasure Q).restrict
              (p12_box (fun i => (Q.index i : ℝ) * cubeScaleFactor Q) (cubeScaleFactor Q / 4))) ∧
          ENNReal.ofReal (cubeScaleFactor Q) *
              eLpNorm u.grad (ENNReal.ofReal P)
                ((normalizedCubeMeasure Q).restrict
                  (p12_box (fun i => (Q.index i : ℝ) * cubeScaleFactor Q)
                    (cubeScaleFactor Q / 4))) ≤
            ENNReal.ofReal C *
              ((ENNReal.ofReal (cubeScaleFactor Q) * Section2.Norms.cubeLpENorm Q 2 u.grad +
                  Section2.Norms.cubeLpENorm Q 2 u.toFun) +
                ENNReal.ofReal (cubeScaleFactor Q) ^ 2 *
                  Section2.Norms.cubeLpENorm Q (ENNReal.ofReal (p12_pstar d P)) f +
                ENNReal.ofReal (cubeScaleFactor Q) *
                  Section2.Norms.cubeLpENorm Q (ENNReal.ofReal P) g) := by
  obtain ⟨ε, C, hε, hC, H⟩ := localW1p_interior hd hP
  refine ⟨ε, C, hε, hC, fun U Q A hU hQU hA hεA f g u hu hf2 hfp hgP => ?_⟩
  exact H Q A hA hεA f g (u.restrict (isOpen_openCubeSet Q) hQU)
    (p12_restrict_weak hU (isOpen_openCubeSet Q) hQU hu) hf2 hfp hgP

end SuperdiffusionCLT.Section7
