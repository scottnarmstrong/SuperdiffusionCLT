/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Change.ShearH1
public import Homogenization.Ambient.BlockMatrix

/-!
# `H¹` pullback under the shear

For `u ∈ H¹(W)` and the shear `Φ = shear e ψ` (`ψ` smooth with bounded partial derivatives), the
composition `u ∘ Φ` belongs to `H¹(Φ⁻¹ W)` with weak gradient
`∂ᵢ(u ∘ Φ) = (∂ᵢu - ⟨e,∇u⟩ ∂ᵢG) ∘ Φ`, `G = ψ ∘ P`.

The proof tests against `χ = φ ∘ Φ⁻¹` and `(∂ᵢG ∘ Φ⁻¹) χ`; the latter is invariant along `e`,
so the `e`-derivative falls on `χ` alone.

## Main results

* `Section7.shearPullbackH1`
-/

@[expose] public section

open MeasureTheory Homogenization

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem integrableOn_vecDot_grad_mul {W : Set (Vec d)} (u : H1Function W) {ρ : Vec d → ℝ}
    (hρ : Continuous ρ) (hc : HasCompactSupport ρ) (z : Vec d) :
    IntegrableOn (fun x => vecDot (u.grad x) z * ρ x) W volume := by
  have h : ∀ j : Fin d, IntegrableOn (fun x => z j * (u.grad x j * ρ x)) W volume :=
    fun j => (integrableOn_mul_continuous_hasCompactSupport (u.gradMemL2 j) hρ hc).const_mul _
  have := integrable_finsetSum Finset.univ fun j _ => h j
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [vecDot, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem integrableOn_mul_fderiv_apply {W : Set (Vec d)} (u : H1Function W) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (z : Vec d) :
    IntegrableOn (fun x => u x * fderiv ℝ φ x z) W volume :=
  integrableOn_mul_continuous_hasCompactSupport u.memL2
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const) (hc.fderiv_apply ℝ z)

/-- The weak gradient of `u ∘ Φ` on `Φ⁻¹ W`. -/
theorem hasWeakGradientOn_shear {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {W : Set (Vec d)} (u : H1Function W) :
    HasWeakGradientOn (shear e ψ ⁻¹' W) (fun y => u.toFun (shear e ψ y))
      (fun y i => u.grad (shear e ψ y) i -
        vecDot e (u.grad (shear e ψ y)) * projGrad e ψ i y) := by
  intro i φ hφ hc hsub
  let H := shearHomeo he hψ
  have hmp : MeasurePreserving (shear e ψ) volume volume :=
    measurePreserving_shear he (hψ.differentiable (by simp))
  have hemb : MeasurableEmbedding (shear e ψ) := H.measurableEmbedding
  let χ : Vec d → ℝ := fun x => φ (shear e (-ψ) x)
  have hχ : ContDiff ℝ (⊤ : ℕ∞) χ := hφ.comp (contDiff_shear hψ.neg)
  have hχc : HasCompactSupport χ := hc.comp_homeomorph H.symm
  have hχsub : tsupport χ ⊆ W := by
    intro x hx
    have hx' : shear e (-ψ) x ∈ tsupport φ := by
      have h := (tsupport_comp_eq_preimage φ H.symm)
      have : x ∈ tsupport (φ ∘ H.symm) := hx
      rw [h] at this
      exact this
    have := hsub hx'
    simpa [shear_shear_neg he] using this
  let gi := projGradPush e ψ i
  have hgi : ContDiff ℝ (⊤ : ℕ∞) gi := contDiff_projGradPush hψ i
  let ρ : Vec d → ℝ := fun x => gi x * χ x
  have hρ : ContDiff ℝ (⊤ : ℕ∞) ρ := hgi.mul hχ
  have hρc : HasCompactSupport ρ := hχc.mul_left
  have hρsub : tsupport ρ ⊆ W := (tsupport_mul_subset_right).trans hχsub
  have hρd : ∀ x, fderiv ℝ ρ x e = gi x * fderiv ℝ χ x e := by
    intro x
    have h : fderiv ℝ ρ x = gi x • fderiv ℝ χ x + χ x • fderiv ℝ gi x :=
      ((hgi.differentiable (by simp) x).hasFDerivAt.mul
        (hχ.differentiable (by simp) x).hasFDerivAt).fderiv
    rw [h]
    simp [gi, fderiv_projGradPush_self he hψ i x]
  have h1 := u.hasWeakGradient i χ hχ hχc hχsub
  have h2 := integral_mul_fderiv_apply_eq_neg u hρ hρc hρsub e
  have hint1 := integrableOn_mul_fderiv_apply u hχ hχc (Pi.single i 1)
  have hint2 := integrableOn_mul_fderiv_apply u hρ hρc e
  have hint3 := integrableOn_mul_continuous_hasCompactSupport (u.gradMemL2 i)
    hχ.continuous hχc
  have hint4 := integrableOn_vecDot_grad_mul u hρ.continuous hρc e
  have hφχ : ∀ y, φ y = χ (shear e ψ y) := fun y => by simp [χ, shear_neg_shear he]
  have hφfun : φ = fun y => χ (shear e ψ y) := funext hφχ
  have hderiv : ∀ y, fderiv ℝ φ y (basisVec i) =
      fderiv ℝ χ (shear e ψ y) (Pi.single i 1) -
        gi (shear e ψ y) * fderiv ℝ χ (shear e ψ y) e := by
    intro y
    rw [hφfun]
    show fderiv ℝ (fun y => χ (shear e ψ y)) y (Pi.single i 1) = _
    rw [fderiv_comp_shear_apply hψ (hχ.differentiable (by simp)) y i,
      ← projGradPush_shear he ψ i y]
  -- change of variables on the left and on the right
  let F : Vec d → ℝ := fun x => u.toFun x *
    (fderiv ℝ χ x (Pi.single i 1) - gi x * fderiv ℝ χ x e)
  let K : Vec d → ℝ := fun x => (u.grad x i - vecDot e (u.grad x) * gi x) * χ x
  have hL : (∫ y in shear e ψ ⁻¹' W, u.toFun (shear e ψ y) * fderiv ℝ φ y (basisVec i)) =
      ∫ x in W, F x := by
    rw [← hmp.setIntegral_preimage_emb hemb F W]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => by
      simp only [F, hderiv])
  have hR : (∫ y in shear e ψ ⁻¹' W,
      (u.grad (shear e ψ y) i - vecDot e (u.grad (shear e ψ y)) * projGrad e ψ i y) * φ y) =
      ∫ x in W, K x := by
    rw [← hmp.setIntegral_preimage_emb hemb K W]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => by
      simp only [K, hφχ y, gi, projGradPush_shear he])
  rw [hL, hR]
  have hF : (∫ x in W, F x) = (∫ x in W, u.toFun x * fderiv ℝ χ x (Pi.single i 1)) -
      ∫ x in W, u.toFun x * fderiv ℝ ρ x e := by
    rw [← integral_sub hint1 hint2]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
      simp only [F, hρd]; ring)
  have hK : (∫ x in W, K x) = (∫ x in W, u.grad x i * χ x) -
      ∫ x in W, vecDot (u.grad x) e * ρ x := by
    rw [← integral_sub hint3 hint4]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
      simp only [K, ρ, vecDot_comm (u.grad x) e]; ring)
  rw [hF, hK, h2]
  have h1' : (∫ x in W, u.toFun x * fderiv ℝ χ x (Pi.single i 1)) =
      -∫ x in W, u.grad x i * χ x := h1
  rw [h1']
  ring

theorem measurePreserving_restrict_shear {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (W : Set (Vec d)) :
    MeasurePreserving (shear e ψ) (volume.restrict (shear e ψ ⁻¹' W)) (volume.restrict W) :=
  (measurePreserving_shear he (hψ.differentiable (by simp))).restrict_preimage_emb
    (shearHomeo he hψ).measurableEmbedding W

/-- The pulled-back gradient is square integrable. -/
theorem gradMemL2_shear {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hb : ∀ i, ∃ M, ∀ y, |fderiv ℝ ψ y (Pi.single i 1)| ≤ M)
    {W : Set (Vec d)} (u : H1Function W) :
    GradMemL2On (shear e ψ ⁻¹' W) (fun y i => u.grad (shear e ψ y) i -
        vecDot e (u.grad (shear e ψ y)) * projGrad e ψ i y) := by
  obtain ⟨C, hC⟩ := exists_bound_projGrad (e := e) hψ hb
  have hmpW := measurePreserving_restrict_shear he hψ W
  have hA : ∀ j : Fin d, MemL2On (shear e ψ ⁻¹' W) (fun y => u.grad (shear e ψ y) j) :=
    fun j => (u.gradMemL2 j).comp_measurePreserving hmpW
  have hE : MemL2On (shear e ψ ⁻¹' W) (fun y => vecDot e (u.grad (shear e ψ y))) := by
    unfold vecDot
    refine memLp_finsetSum Finset.univ fun j _ => ?_
    exact (hA j).const_mul (e j)
  intro i
  refine (hA i).sub ?_
  refine hE.of_le_mul (c := C) ((hE.aestronglyMeasurable.mul
    (contDiff_projGrad hψ i).continuous.aestronglyMeasurable)) ?_
  refine Filter.Eventually.of_forall fun y => ?_
  rw [norm_mul, mul_comm C]
  exact mul_le_mul_of_nonneg_left (by simpa using hC y i) (norm_nonneg _)

/-- The pullback of an `H¹(W)` function under the shear, as an `H¹(Φ⁻¹ W)` function. -/
noncomputable def H1Function.compShear {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hb : ∀ i, ∃ M, ∀ y, |fderiv ℝ ψ y (Pi.single i 1)| ≤ M)
    {W : Set (Vec d)} (u : H1Function W) : H1Function (shear e ψ ⁻¹' W) where
  toFun := fun y => u.toFun (shear e ψ y)
  grad := fun y i => u.grad (shear e ψ y) i -
    vecDot e (u.grad (shear e ψ y)) * projGrad e ψ i y
  memL2 := u.memL2.comp_measurePreserving (measurePreserving_restrict_shear he hψ W)
  gradMemL2 := gradMemL2_shear he hψ hb u
  hasWeakGradient := hasWeakGradientOn_shear he hψ u

/-- SHEAR-H1: pullback of `H¹` under the volume-preserving shear. -/
theorem shearPullbackH1 {e : Vec d} {ψ : Vec d → ℝ} (he : vecNormSq e = 1)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hb : ∀ i, ∃ M, ∀ y, |fderiv ℝ ψ y (Pi.single i 1)| ≤ M)
    {W : Set (Vec d)} (u : H1Function W) :
    ∃ v : H1Function (shear e ψ ⁻¹' W),
      v.toFun = (fun y => u.toFun (shear e ψ y)) ∧
      ∀ y, v.grad y = fun i =>
        u.grad (shear e ψ y) i -
          vecDot e (u.grad (shear e ψ y)) *
            fderiv ℝ (fun z => ψ (z - vecDot e z • e)) y (Pi.single i 1) :=
  ⟨H1Function.compShear he hψ hb u, rfl, fun _ => rfl⟩

/-- Satisfiability: for `ψ = 0` and `e = e₀` (dimension `2`) every hypothesis holds, and the
conclusion holds for every `u`. -/
example (W : Set (Vec 2)) (u : H1Function W) :
    ∃ v : H1Function (shear (Pi.single (0 : Fin 2) (1 : ℝ)) (0 : Vec 2 → ℝ) ⁻¹' W),
      v.toFun = (fun y => u.toFun (shear (Pi.single (0 : Fin 2) (1 : ℝ)) (0 : Vec 2 → ℝ) y)) ∧
      ∀ y, v.grad y = fun i =>
        u.grad (shear (Pi.single (0 : Fin 2) (1 : ℝ)) (0 : Vec 2 → ℝ) y) i -
          vecDot (Pi.single (0 : Fin 2) (1 : ℝ))
              (u.grad (shear (Pi.single (0 : Fin 2) (1 : ℝ)) (0 : Vec 2 → ℝ) y)) *
            fderiv ℝ (fun z => (0 : Vec 2 → ℝ) (z - vecDot (Pi.single (0 : Fin 2) (1 : ℝ)) z •
              Pi.single (0 : Fin 2) (1 : ℝ))) y (Pi.single i 1) :=
  shearPullbackH1 (by simp [vecNormSq, vecDot, Pi.single_apply]) contDiff_const
    (fun _ => ⟨0, fun y => by simp⟩) u

end SuperdiffusionCLT.Section7
