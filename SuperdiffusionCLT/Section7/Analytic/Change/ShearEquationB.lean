/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Change.ShearEquation
public import SuperdiffusionCLT.Section7.Analytic.Defs
public import SuperdiffusionCLT.Section7.Prereq.DirichletExistence

/-!
# Transport of weak solutions under the shear

For `Φ = shear e ψ` the Jacobian matrix is `DΦ = 1 - e ⊗ ∇G` and its inverse is
`1 + e ⊗ ∇G` (`∇G ⟂ e`). Since `det DΦ = 1`, a weak solution `u` of `-∇·(a∇u) = f - ∇·g` in `W`
gives the weak solution `u ∘ Φ` in `Φ⁻¹ W` of the same equation with data
`(Φ-pullback of f, DΦ⁻¹ (g ∘ Φ))` and coefficient `DΦ⁻¹ a(Φ ·) DΦ⁻ᵀ`.
The push-forward form (`Φ` replaced by `Φ⁻¹ = shear e (-ψ)`) has coefficient
`DΦ a(Φ⁻¹ ·) DΦᵀ` evaluated at `Φ⁻¹ y`, as in the change of variables for `Ã`.

## Main results

* `Section7.shearJac`, `Section7.shearJacInv`
* `Section7.IsWeakSolutionOn.shearPullback`
* `Section7.IsWeakSolutionOn.shearPush`
-/

@[expose] public section

open MeasureTheory Homogenization

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The gradient of `G = ψ ∘ P` as a vector. -/
noncomputable def projGradVec (e : Vec d) (ψ : Vec d → ℝ) (y : Vec d) : Vec d :=
  fun i => projGrad e ψ i y

/-- The Jacobian matrix `DΦ(y) = 1 - e ⊗ ∇G(y)` of the shear. -/
noncomputable def shearJac (e : Vec d) (ψ : Vec d → ℝ) (y : Vec d) : Mat d :=
  1 - Matrix.vecMulVec e (projGradVec e ψ y)

/-- The inverse Jacobian matrix `DΦ(y)⁻¹ = 1 + e ⊗ ∇G(y)`. -/
noncomputable def shearJacInv (e : Vec d) (ψ : Vec d → ℝ) (y : Vec d) : Mat d :=
  1 + Matrix.vecMulVec e (projGradVec e ψ y)

/-- `∇G ⟂ e`. -/
theorem vecDot_self_projGradVec {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (y : Vec d) : vecDot e (projGradVec e ψ y) = 0 := by
  have h := fderiv_projComp_self he (hψ.differentiable (by simp)) y
  rw [clm_apply_eq_sum] at h
  rw [← h]
  unfold vecDot projGradVec projGrad
  exact Finset.sum_congr rfl fun j _ => rfl

theorem matVecMul_rankOne (a b w : Vec d) :
    matVecMul (1 + Matrix.vecMulVec a b) w = w + vecDot b w • a := by
  ext i
  simp only [matVecMul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.add_apply,
    Matrix.one_apply, Matrix.vecMulVec_apply, vecDot, add_mul, Finset.sum_add_distrib, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

theorem matVecMul_rankOne_transpose (a b w : Vec d) :
    matVecMul (matTranspose (1 + Matrix.vecMulVec a b)) w = w + vecDot a w • b := by
  ext i
  simp only [matVecMul, matTranspose, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.transpose_apply, Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply, vecDot,
    add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  rw [Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

theorem vecDot_sub_smul_right (a g w : Vec d) (c : ℝ) :
    vecDot a (w - c • g) = vecDot a w - c * vecDot a g := by
  unfold vecDot
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib,
    Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The pulled-back gradient is `DΦᵀ ∇u ∘ Φ`, so `DΦ⁻ᵀ` recovers `∇u ∘ Φ`. -/
theorem matVecMul_transpose_shearJacInv_grad {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (y w : Vec d) :
    matVecMul (matTranspose (shearJacInv e ψ y))
        (fun i => w i - vecDot e w * projGrad e ψ i y) = w := by
  unfold shearJacInv
  rw [matVecMul_rankOne_transpose]
  have h : (fun i => w i - vecDot e w * projGrad e ψ i y) =
      w - vecDot e w • projGradVec e ψ y := by
    ext i; simp [projGradVec]
  rw [h, vecDot_sub_smul_right, vecDot_self_projGradVec he hψ]
  ext i
  simp

theorem projGrad_neg (e : Vec d) (ψ : Vec d → ℝ) (i : Fin d) (y : Vec d) :
    projGrad e (-ψ) i y = -projGrad e ψ i y := by
  have : projComp e (-ψ) = -projComp e ψ := rfl
  simp [projGrad, this, fderiv_neg]

theorem projGrad_shear {e : Vec d} (he : vecNormSq e = 1) (ψ : Vec d → ℝ) (i : Fin d)
    (y : Vec d) : projGrad e ψ i (shear e ψ y) = projGrad e ψ i y := by
  have : shear e ψ y = y + (-ψ (y - vecDot e y • e)) • e := by
    simp [shear, sub_eq_add_neg]
  rw [this, projGrad_add_smul he]

theorem projGrad_shear_neg {e : Vec d} (he : vecNormSq e = 1) (ψ : Vec d → ℝ) (i : Fin d)
    (y : Vec d) : projGrad e ψ i (shear e (-ψ) y) = projGrad e ψ i y := by
  have := projGrad_shear he (-ψ) i y
  rwa [projGrad_neg, projGrad_neg, neg_inj] at this

theorem exists_bound_neg {ψ : Vec d → ℝ}
    (hb : ∀ i, ∃ M, ∀ y, |fderiv ℝ ψ y (Pi.single i 1)| ≤ M) :
    ∀ i, ∃ M, ∀ y, |fderiv ℝ (-ψ) y (Pi.single i 1)| ≤ M := by
  intro i
  obtain ⟨M, hM⟩ := hb i
  refine ⟨M, fun y => ?_⟩
  have : fderiv ℝ (-ψ) y = -fderiv ℝ ψ y := fderiv_neg
  simpa [this] using hM y

/-- Transport of a weak solution under the pullback by the shear `Φ = shear e ψ`. -/
theorem IsWeakSolutionOn.shearPullback {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hb : ∀ i, ∃ M, ∀ y, |fderiv ℝ ψ y (Pi.single i 1)| ≤ M)
    {W : Set (Vec d)} {a : CoeffField d} {u : H1Function W} {f : Vec d → ℝ}
    {g : Vec d → Vec d} (hu : IsWeakSolutionOn a W u f g) :
    IsWeakSolutionOn
      (fun y => shearJacInv e ψ y * a (shear e ψ y) * matTranspose (shearJacInv e ψ y))
      (shear e ψ ⁻¹' W) (H1Function.compShear he hψ hb u) (fun y => f (shear e ψ y))
      (fun y => matVecMul (shearJacInv e ψ y) (g (shear e ψ y))) := by
  intro φ
  have hmp : MeasurePreserving (shear e ψ) volume volume :=
    measurePreserving_shear he (hψ.differentiable (by simp))
  have hemb : MeasurableEmbedding (shear e ψ) := (shearHomeo he hψ).measurableEmbedding
  have hset : shear e (-ψ) ⁻¹' (shear e ψ ⁻¹' W) = W := by
    ext x
    simp [shear_shear_neg he]
  have hneg : ContDiff ℝ (⊤ : ℕ∞) (-ψ) := hψ.neg
  let χ := (H10Function.compShear he hneg (exists_bound_neg hb) φ).castSet hset
  have hcast : χ.toH1Function = (H10Function.compShear he hneg (exists_bound_neg hb)
      φ).toH1Function.castSet hset := H10Function.castSet_toH1Function hset _
  have hχfun : ∀ x, χ.toH1Function.toFun x = φ.toH1Function.toFun (shear e (-ψ) x) := fun x => by
    rw [hcast, H1Function.castSet_toFun]
    rfl
  have hχgrad : ∀ x, χ.toH1Function.grad x = fun i =>
      φ.toH1Function.grad (shear e (-ψ) x) i -
        vecDot e (φ.toH1Function.grad (shear e (-ψ) x)) * projGrad e (-ψ) i x := fun x => by
    rw [hcast, H1Function.castSet_grad]
    rfl
  have hχgradΦ : ∀ y, χ.toH1Function.grad (shear e ψ y) =
      matVecMul (matTranspose (shearJacInv e ψ y)) (φ.toH1Function.grad y) := by
    intro y
    rw [hχgrad, shear_neg_shear he]
    unfold shearJacInv
    rw [matVecMul_rankOne_transpose]
    ext i
    simp [projGrad_neg, projGrad_shear he, projGradVec, sub_eq_add_neg]
  have hugrad : ∀ y, u.grad (shear e ψ y) =
      matVecMul (matTranspose (shearJacInv e ψ y)) ((H1Function.compShear he hψ hb u).grad y) :=
    fun y => (matVecMul_transpose_shearJacInv_grad he hψ y _).symm
  have h := hu χ
  have e1 : (∫ x in W, vecDot (matVecMul (a x) (u.grad x)) (χ.toH1Function.grad x)) =
      ∫ y in shear e ψ ⁻¹' W, vecDot (matVecMul (shearJacInv e ψ y * a (shear e ψ y) *
        matTranspose (shearJacInv e ψ y)) ((H1Function.compShear he hψ hb u).grad y))
          (φ.toH1Function.grad y) := by
    rw [← hmp.setIntegral_preimage_emb hemb]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    rw [hχgradΦ, hugrad, vecDot_matVecMul_transpose _ _ (shearJacInv e ψ y),
      ← matVecMul_mul, ← matVecMul_mul]
  have e2 : (∫ x in W, f x * χ.toH1Function.toFun x) =
      ∫ y in shear e ψ ⁻¹' W, f (shear e ψ y) * φ.toH1Function.toFun y := by
    rw [← hmp.setIntegral_preimage_emb hemb]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hχfun, shear_neg_shear he]
  have e3 : (∫ x in W, vecDot (g x) (χ.toH1Function.grad x)) =
      ∫ y in shear e ψ ⁻¹' W, vecDot (matVecMul (shearJacInv e ψ y) (g (shear e ψ y)))
        (φ.toH1Function.grad y) := by
    rw [← hmp.setIntegral_preimage_emb hemb]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    rw [hχgradΦ, vecDot_matVecMul_transpose]
  rw [e1, e2, e3] at h
  exact h

theorem shearJacInv_neg (e : Vec d) (ψ : Vec d → ℝ) (y : Vec d) :
    shearJacInv e (-ψ) y = shearJac e ψ y := by
  have : projGradVec e (-ψ) y = -projGradVec e ψ y := by
    ext i; simp [projGradVec, projGrad_neg]
  simp [shearJacInv, shearJac, this, sub_eq_add_neg]

theorem shearJac_shear_neg {e : Vec d} (he : vecNormSq e = 1) (ψ : Vec d → ℝ) (y : Vec d) :
    shearJac e ψ (shear e (-ψ) y) = shearJac e ψ y := by
  have : projGradVec e ψ (shear e (-ψ) y) = projGradVec e ψ y := by
    ext i; exact projGrad_shear_neg he ψ i y
  simp [shearJac, this]

/-- Push-forward transport: if `u` solves the equation with coefficient `a` in `U` and
`Φ = shear e ψ`, then `u ∘ Φ⁻¹` solves, in `Φ(U) = Φ⁻¹ ⁻¹' U`, the equation with coefficient
`DΦ a(Φ⁻¹ ·) DΦᵀ` evaluated at `Φ⁻¹ y` (the transported coefficient `Ã`), source `f ∘ Φ⁻¹`
and forcing `DΦ (g ∘ Φ⁻¹)`. No normalization is needed since `det DΦ = 1`. -/
theorem IsWeakSolutionOn.shearPush {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hb : ∀ i, ∃ M, ∀ y, |fderiv ℝ ψ y (Pi.single i 1)| ≤ M)
    {U : Set (Vec d)} {a : CoeffField d} {u : H1Function U} {f : Vec d → ℝ}
    {g : Vec d → Vec d} (hu : IsWeakSolutionOn a U u f g) :
    IsWeakSolutionOn
      (fun y => shearJac e ψ (shear e (-ψ) y) * a (shear e (-ψ) y) *
        matTranspose (shearJac e ψ (shear e (-ψ) y)))
      (shear e (-ψ) ⁻¹' U)
      (H1Function.compShear (ψ := -ψ) he hψ.neg (exists_bound_neg hb) u)
      (fun y => f (shear e (-ψ) y))
      (fun y => matVecMul (shearJac e ψ (shear e (-ψ) y)) (g (shear e (-ψ) y))) := by
  have h := IsWeakSolutionOn.shearPullback (ψ := -ψ) he hψ.neg (exists_bound_neg hb) hu
  have hJ : ∀ y, shearJacInv e (-ψ) y = shearJac e ψ (shear e (-ψ) y) := fun y => by
    rw [shearJacInv_neg, shearJac_shear_neg he]
  simpa only [hJ] using h

end SuperdiffusionCLT.Section7
