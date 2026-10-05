/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Change.ShearH1B

/-!
# `H¹₀` under the shear

If `w ∈ H¹₀(W)`, then `w ∘ Φ ∈ H¹₀(Φ⁻¹ W)` for the shear `Φ = shear e ψ`; the approximants are
`φₙ ∘ Φ`, whose gradient error is `(hᵢ - ∂ᵢG Σⱼ eⱼ hⱼ) ∘ Φ` with `hⱼ = ∂ⱼφₙ - ∂ⱼw`.

## Main results

* `Section7.H10Function.compShear`
* `Section7.H10Function.compShear_toFun`, `Section7.H10Function.compShear_grad`
-/

@[expose] public section

open MeasureTheory Homogenization
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem tendsto_approx_shear {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {W : Set (Vec d)} (w : H10Function W) :
    Filter.Tendsto (fun n => eLpNorm (fun y => w.approx n (shear e ψ y) - w.toFun (shear e ψ y)) 2
      (volume.restrict (shear e ψ ⁻¹' W))) Filter.atTop (nhds 0) := by
  have hmpW := measurePreserving_restrict_shear he hψ W
  have h : ∀ n, eLpNorm (fun y => w.approx n (shear e ψ y) - w.toFun (shear e ψ y)) 2
      (volume.restrict (shear e ψ ⁻¹' W)) =
      eLpNorm (fun x => w.approx n x - w.toFun x) 2 (volume.restrict W) := fun n =>
    eLpNorm_comp_measurePreserving (g := fun x => w.approx n x - w.toFun x)
      (((w.approx_smooth n).continuous.aestronglyMeasurable).sub w.memL2.aestronglyMeasurable)
      hmpW
  simp only [h]
  exact w.tendsto_approx

theorem tendsto_approx_grad_shear {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hb : ∀ i, ∃ M, ∀ y, |fderiv ℝ ψ y (Pi.single i 1)| ≤ M)
    {W : Set (Vec d)} (w : H10Function W) (i : Fin d) :
    Filter.Tendsto (fun n => eLpNorm (fun y =>
        fderiv ℝ (fun z => w.approx n (shear e ψ z)) y (basisVec i) -
          (H1Function.compShear he hψ hb w.toH1Function).grad y i) 2
      (volume.restrict (shear e ψ ⁻¹' W))) Filter.atTop (nhds 0) := by
  obtain ⟨C, hC⟩ := exists_bound_projGrad (e := e) hψ hb
  have hmpW := measurePreserving_restrict_shear he hψ W
  let h : ℕ → Fin d → Vec d → ℝ := fun n j x =>
    fderiv ℝ (w.approx n) x (basisVec j) - w.toH1Function.grad x j
  have hmeas : ∀ n j, AEStronglyMeasurable (fun y => h n j (shear e ψ y))
      (volume.restrict (shear e ψ ⁻¹' W)) := by
    intro n j
    have hh : AEStronglyMeasurable (h n j) (volume.restrict W) :=
      ((((w.approx_smooth n).continuous_fderiv (by simp)).clm_apply
        continuous_const).aestronglyMeasurable).sub (w.gradMemL2 j).aestronglyMeasurable
    exact hh.comp_measurePreserving hmpW
  have hnorm : ∀ n j, eLpNorm (fun y => h n j (shear e ψ y)) 2
      (volume.restrict (shear e ψ ⁻¹' W)) = eLpNorm (h n j) 2 (volume.restrict W) := by
    intro n j
    refine eLpNorm_comp_measurePreserving (g := h n j) ?_ hmpW
    exact ((((w.approx_smooth n).continuous_fderiv (by simp)).clm_apply
        continuous_const).aestronglyMeasurable).sub (w.gradMemL2 j).aestronglyMeasurable
  have hpoint : ∀ n y, fderiv ℝ (fun z => w.approx n (shear e ψ z)) y (basisVec i) -
      (H1Function.compShear he hψ hb w.toH1Function).grad y i =
        h n i (shear e ψ y) - ∑ j, (projGrad e ψ i y * e j) * h n j (shear e ψ y) := by
    intro n y
    have hchain := fderiv_comp_shear_apply (e := e) hψ
      ((w.approx_smooth n).differentiable (by simp)) y i
    have hch : fderiv ℝ (fun z => w.approx n (shear e ψ z)) y (basisVec i) =
        fderiv ℝ (w.approx n) (shear e ψ y) (basisVec i) -
          projGrad e ψ i y * fderiv ℝ (w.approx n) (shear e ψ y) e := hchain
    have hg : (H1Function.compShear he hψ hb w.toH1Function).grad y i =
        w.toH1Function.grad (shear e ψ y) i -
          vecDot e (w.toH1Function.grad (shear e ψ y)) * projGrad e ψ i y := rfl
    have hs : ∑ j, (projGrad e ψ i y * e j) * h n j (shear e ψ y) =
        projGrad e ψ i y * ∑ j, e j * fderiv ℝ (w.approx n) (shear e ψ y) (basisVec j) -
          projGrad e ψ i y * ∑ j, e j * w.toH1Function.grad (shear e ψ y) j := by
      simp only [h, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hch, hg, clm_apply_eq_sum (fderiv ℝ (w.approx n) (shear e ψ y)) e, hs]
    simp only [h, vecDot]
    ring
  have hle : ∀ n, eLpNorm (fun y => fderiv ℝ (fun z => w.approx n (shear e ψ z)) y (basisVec i) -
        (H1Function.compShear he hψ hb w.toH1Function).grad y i) 2
        (volume.restrict (shear e ψ ⁻¹' W)) ≤
      eLpNorm (h n i) 2 (volume.restrict W) +
        ∑ j, ENNReal.ofReal (C * |e j|) * eLpNorm (h n j) 2 (volume.restrict W) := by
    intro n
    have hfun : (fun y => fderiv ℝ (fun z => w.approx n (shear e ψ z)) y (basisVec i) -
        (H1Function.compShear he hψ hb w.toH1Function).grad y i) =
        (fun y => h n i (shear e ψ y)) -
          ∑ j, (fun y => (projGrad e ψ i y * e j) * h n j (shear e ψ y)) := by
      funext y
      rw [hpoint]
      simp
    have hterm : ∀ j, AEStronglyMeasurable (fun y => (projGrad e ψ i y * e j) *
        h n j (shear e ψ y)) (volume.restrict (shear e ψ ⁻¹' W)) := fun j =>
      (((contDiff_projGrad hψ i).continuous.mul continuous_const).aestronglyMeasurable).mul
        (hmeas n j)
    rw [hfun]
    refine (eLpNorm_sub_le (p := 2) (by norm_num)).trans ?_
    rw [hnorm n i]
    refine add_le_add le_rfl ((eLpNorm_sum_le (p := 2) (by norm_num)).trans
      (Finset.sum_le_sum fun j _ => ?_))
    rw [← hnorm n j]
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hterm j) ?_ 2
    refine Filter.Eventually.of_forall fun y => ?_
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have := hC y i
    calc |projGrad e ψ i y| * |e j| * ‖h n j (shear e ψ y)‖ ≤ C * |e j| * ‖h n j (shear e ψ y)‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this (abs_nonneg _))
            (norm_nonneg _)
      _ = _ := rfl
  have hU : Filter.Tendsto (fun n => eLpNorm (h n i) 2 (volume.restrict W) +
      ∑ j, ENNReal.ofReal (C * |e j|) * eLpNorm (h n j) 2 (volume.restrict W))
      Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun n => eLpNorm (h n i) 2 (volume.restrict W)) Filter.atTop
        (nhds 0) := w.tendsto_approx_grad i
    have hj : ∀ j ∈ (Finset.univ : Finset (Fin d)), Filter.Tendsto
        (fun n => ENNReal.ofReal (C * |e j|) * eLpNorm (h n j) 2 (volume.restrict W))
        Filter.atTop (nhds 0) := by
      intro j _
      have := ENNReal.Tendsto.const_mul (w.tendsto_approx_grad j)
        (Or.inr (ENNReal.ofReal_ne_top (r := C * |e j|)))
      simpa using this
    have := h0.add (tendsto_finsetSum _ hj)
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hU
    (fun _ => zero_le) hle

/-- The pullback of an `H¹₀(W)` function under the shear, an `H¹₀(Φ⁻¹ W)` function whose
approximants are `φₙ ∘ Φ`. -/
noncomputable def H10Function.compShear {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hb : ∀ i, ∃ M, ∀ y, |fderiv ℝ ψ y (Pi.single i 1)| ≤ M)
    {W : Set (Vec d)} (w : H10Function W) : H10Function (shear e ψ ⁻¹' W) where
  toH1Function := H1Function.compShear he hψ hb w.toH1Function
  approx := fun n y => w.approx n (shear e ψ y)
  approx_smooth := fun n => (w.approx_smooth n).comp (contDiff_shear hψ)
  approx_hasCompactSupport := fun n =>
    (w.approx_hasCompactSupport n).comp_homeomorph (shearHomeo he hψ)
  approx_support_subset := fun n y hy => by
    have h := tsupport_comp_eq_preimage (w.approx n) (shearHomeo he hψ)
    have hy' : y ∈ tsupport (w.approx n ∘ shearHomeo he hψ) := hy
    rw [h] at hy'
    exact w.approx_support_subset n hy'
  tendsto_approx := tendsto_approx_shear he hψ w
  tendsto_approx_grad := tendsto_approx_grad_shear he hψ hb w

@[simp]
theorem H10Function.compShear_toFun {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hb : ∀ i, ∃ M, ∀ y, |fderiv ℝ ψ y (Pi.single i 1)| ≤ M)
    {W : Set (Vec d)} (w : H10Function W) (y : Vec d) :
    (H10Function.compShear he hψ hb w).toH1Function.toFun y = w.toH1Function.toFun (shear e ψ y) :=
  rfl

@[simp]
theorem H10Function.compShear_grad {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hb : ∀ i, ∃ M, ∀ y, |fderiv ℝ ψ y (Pi.single i 1)| ≤ M)
    {W : Set (Vec d)} (w : H10Function W) (y : Vec d) (i : Fin d) :
    (H10Function.compShear he hψ hb w).toH1Function.grad y i =
      w.toH1Function.grad (shear e ψ y) i -
        vecDot e (w.toH1Function.grad (shear e ψ y)) * projGrad e ψ i y :=
  rfl

end SuperdiffusionCLT.Section7
