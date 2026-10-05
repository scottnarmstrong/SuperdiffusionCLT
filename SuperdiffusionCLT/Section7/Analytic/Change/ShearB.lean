/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Change.Shear

/-!
# The shear preserves Lebesgue measure

The derivative of the shear is `id - φ ⊗ e` with `φ e = 0`, whose determinant is `1`.

## Main results

* `Section7.det_id_sub_smulRight`
* `Section7.measurePreserving_shear`
-/

@[expose] public section

open MeasureTheory Homogenization

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- `det (id - φ ⊗ e) = 1 - φ e`, here with `φ e = 0`. -/
theorem det_id_sub_smulRight (e : Vec d) (φ : Vec d →L[ℝ] ℝ) (hφ : φ e = 0) :
    (ContinuousLinearMap.id ℝ (Vec d) - φ.smulRight e).det = 1 := by
  set v : Vec d := fun i => φ (Pi.single i 1) with hv
  have hφx : ∀ x : Vec d, φ x = v ⬝ᵥ x := by
    intro x
    have hx : x = ∑ i, x i • (Pi.single i 1 : Vec d) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hx]
    simp only [map_sum, map_smul, smul_eq_mul, dotProduct, hv]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hM : ((ContinuousLinearMap.id ℝ (Vec d) - φ.smulRight e : Vec d →L[ℝ] Vec d) :
      Vec d →ₗ[ℝ] Vec d) =
      Matrix.toLin' (1 + Matrix.replicateCol Unit (-e) * Matrix.replicateRow Unit v) := by
    apply LinearMap.ext
    intro x
    rw [Matrix.toLin'_apply, Matrix.add_mulVec, Matrix.one_mulVec]
    ext i
    simp [Matrix.mulVec, dotProduct, hφx, Matrix.mul_apply, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  have hdet := Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Unit) (-e) v
  rw [ContinuousLinearMap.det, hM, LinearMap.det_toLin', hdet]
  have : v ⬝ᵥ (-e) = -(φ e) := by rw [hφx, dotProduct_neg]
  rw [this, hφ]; simp

/-- The shear of a differentiable function along a unit vector preserves Lebesgue measure. -/
theorem measurePreserving_shear {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : Differentiable ℝ ψ) :
    MeasurePreserving (shear e ψ) MeasureTheory.volume MeasureTheory.volume := by
  have hcont : Continuous (shear e ψ) := by
    have hd : Differentiable ℝ (shear e ψ) := fun y => (hasFDerivAt_shear hψ y).differentiableAt
    exact hd.continuous
  refine ⟨hcont.measurable, ?_⟩
  ext t ht
  rw [Measure.map_apply hcont.measurable ht]
  have hmeas : MeasurableSet (shear e ψ ⁻¹' t) := hcont.measurable ht
  have hdet : ∀ x ∈ shear e ψ ⁻¹' t, |(ContinuousLinearMap.id ℝ (Vec d) -
      (fderiv ℝ (fun z : Vec d => ψ (z - vecDot e z • e)) x).smulRight e).det| = 1 := by
    intro x _
    rw [det_id_sub_smulRight e _ (fderiv_proj_comp_self he hψ x), abs_one]
  have h := lintegral_abs_det_fderiv_eq_addHaar_image MeasureTheory.volume hmeas
    (f := shear e ψ) (f' := fun x => ContinuousLinearMap.id ℝ (Vec d) -
      (fderiv ℝ (fun z : Vec d => ψ (z - vecDot e z • e)) x).smulRight e)
    (fun x _ => (hasFDerivAt_shear hψ x).hasFDerivWithinAt)
    ((shear_bijective he ψ).injective.injOn)
  have himg : shear e ψ '' (shear e ψ ⁻¹' t) = t :=
    Set.image_preimage_eq t (shear_bijective he ψ).surjective
  rw [himg] at h
  rw [← h]
  rw [MeasureTheory.setLIntegral_congr_fun hmeas (g := fun _ => 1)
    (fun x hx => by rw [hdet x hx]; simp)]
  simp

/-- Satisfiability: for `ψ = 0` the shear is the identity. -/
example (e : Vec d) : shear e (0 : Vec d → ℝ) = id := by
  funext y; simp [shear]

/-- Satisfiability of `measurePreserving_shear`: a witness with `ψ = 0` and `e = (1, 0, ...)`. -/
example : MeasurePreserving (shear (Pi.single (0 : Fin 2) (1 : ℝ)) (0 : Vec 2 → ℝ))
    MeasureTheory.volume MeasureTheory.volume :=
  measurePreserving_shear (by simp [vecNormSq, vecDot, Pi.single_apply]) (differentiable_const _)

/-- Satisfiability of the inverse law: `ψ = 0`, the unit vector `e_0` in dimension `2`. -/
example : shear (Pi.single (0 : Fin 2) (1 : ℝ)) (-(0 : Vec 2 → ℝ)) ∘
    shear (Pi.single (0 : Fin 2) (1 : ℝ)) (0 : Vec 2 → ℝ) = id :=
  shear_neg_left_inverse (by simp [vecNormSq, vecDot, Pi.single_apply]) _

end SuperdiffusionCLT.Section7
