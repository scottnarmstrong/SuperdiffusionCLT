/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.CZ.LocalE
public import SuperdiffusionCLT.Section7.Analytic.Geometry.AtlasTransform
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen

@[expose] public section

open Homogenization MeasureTheory Filter Topology Matrix
open scoped ENNReal NNReal

/-!
# The chart map is an orthogonal map up to a second order correction

For a `C^{1,1}` graph function `ψ` the chart map is `Ψ y = O (y - x₀ - T(y) e)` with `O` the
Householder reflection of the chart and `T(y) = ψ(Py) - ψ(Px₀) - ⟨∇(ψ∘P)(x₀), y - x₀⟩` the
Taylor remainder, which is bounded by `M₂ ‖y - x₀‖²`.  Hence an affine function of the chart
variable is an affine function of `y` up to the error `T(y) ⟨O b, e⟩`.
-/

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The Taylor remainder of `ψ ∘ P` at `x₀`. -/
noncomputable def r3e_T (e : Vec d) (ψ : Vec d → ℝ) (x₀ y : Vec d) : ℝ :=
  ψ (y - vecDot e y • e) - ψ (x₀ - vecDot e x₀ • e) - vecDot (projGradVec e ψ x₀) (y - x₀)

theorem r3e_fderiv_projComp_apply {e : Vec d} {ψ : Vec d → ℝ} (z w : Vec d) :
    fderiv ℝ (projComp e ψ) z w = ∑ i, w i * projGrad e ψ i z := by
  rw [clm_apply_eq_sum]
  rfl

/-- Second order Taylor bound for the graph function. -/
theorem r3e_T_abs_le {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {M₂ : ℝ} (hM₂ : 0 ≤ M₂)
    (hb2 : ∀ y z, ‖fderiv ℝ ψ y - fderiv ℝ ψ z‖ ≤ M₂ * ‖y - z‖) (x₀ y : Vec d) :
    |r3e_T e ψ x₀ y| ≤ 2 * M₂ * (1 + d) * d * ‖y - x₀‖ ^ 2 := by
  set g : Vec d := projGradVec e ψ x₀ with hg
  set h : Vec d → ℝ := fun z => projComp e ψ z - dotCLM g z with hh
  have hdiff : Differentiable ℝ (projComp e ψ) :=
    (contDiff_projComp hψ).differentiable (by simp)
  have hhd : ∀ z, HasFDerivAt h (fderiv ℝ (projComp e ψ) z - dotCLM g) z := fun z =>
    (hdiff z).hasFDerivAt.sub (dotCLM g).hasFDerivAt
  have hbound : ∀ z ∈ Metric.closedBall x₀ ‖y - x₀‖,
      ‖fderiv ℝ h z‖ ≤ 2 * M₂ * (1 + d) * d * ‖y - x₀‖ := by
    intro z hz
    rw [(hhd z).fderiv]
    have hzn : ‖z - x₀‖ ≤ ‖y - x₀‖ := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      exact hz
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
    rw [Real.norm_eq_abs, _root_.sub_apply, r3e_fderiv_projComp_apply,
      dotCLM_apply]
    have hsum : ∑ i, w i * projGrad e ψ i z - vecDot g w =
        ∑ i, w i * (projGrad e ψ i z - g i) := by
      unfold vecDot
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsum]
    have hterm : ∀ i, |w i * (projGrad e ψ i z - g i)| ≤
        ‖w‖ * (2 * M₂ * ((1 + d) * ‖y - x₀‖)) := fun i => by
      rw [abs_mul]
      have h1 : |w i| ≤ ‖w‖ := by
        have := norm_le_pi_norm w i
        rwa [Real.norm_eq_abs] at this
      have h2 : |projGrad e ψ i z - g i| ≤ 2 * M₂ * ((1 + d) * ‖y - x₀‖) :=
        (flatten_abs_projGrad_sub_le he hψ hM₂ hb2 z x₀ i).trans
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hzn (by positivity))
            (by positivity))
      exact mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
    calc |∑ i, w i * (projGrad e ψ i z - g i)|
        ≤ ∑ i, |w i * (projGrad e ψ i z - g i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin d, ‖w‖ * (2 * M₂ * ((1 + d) * ‖y - x₀‖)) := Finset.sum_le_sum fun i _ => hterm i
      _ = 2 * M₂ * (1 + d) * d * ‖y - x₀‖ * ‖w‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := h)
    (s := Metric.closedBall x₀ ‖y - x₀‖)
    (fun z _ => (hhd z).differentiableAt) hbound (convex_closedBall _ _)
    (Metric.mem_closedBall_self (norm_nonneg _))
    (by rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev])
  have hT : r3e_T e ψ x₀ y = h y - h x₀ := by
    simp only [r3e_T, hh, dotCLM_apply, projComp, vecDot_sub]
    ring
  rw [hT, ← Real.norm_eq_abs]
  calc ‖h y - h x₀‖ ≤ 2 * M₂ * (1 + d) * d * ‖y - x₀‖ * ‖y - x₀‖ := hmv
    _ = _ := by ring

theorem r3e_vecDot_eq (a b : Vec d) : vecDot a b = a ⬝ᵥ b := rfl

/-- The orthogonal part of the chart map. -/
noncomputable def r3e_O (e : Vec d) (ψ : Vec d → ℝ) (x₀ u : Vec d) : Mat d :=
  flattenHouseholder (flattenNormal e (projGradVec e ψ x₀)) u

/-- The chart map is an orthogonal map up to the Taylor remainder along `e`. -/
theorem r3e_flattenMap_eq {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (u x₀ y : Vec d) :
    flattenMap e ψ x₀ u y = r3e_O e ψ x₀ u *ᵥ (y - x₀ - r3e_T e ψ x₀ y • e) := by
  have hg := vecDot_self_projGradVec he hψ x₀
  have hg' : projGradVec e ψ x₀ ⬝ᵥ e = 0 := by rw [dotProduct_comm]; exact hg
  unfold flattenMap flattenLin r3e_O
  rw [flatten_matVecMul_eq, ← Matrix.mulVec_mulVec]
  congr 1
  have hw : shear e ψ y - shear e ψ x₀ = (y - x₀) -
      (ψ (y - vecDot e y • e) - ψ (x₀ - vecDot e x₀ • e)) • e := by
    unfold shear
    ext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hw]
  unfold flattenTilt
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, flatten_op_smul,
    dotProduct_sub, dotProduct_smul, hg', smul_zero, sub_zero]
  unfold r3e_T
  ext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, r3e_vecDot_eq]
  ring

theorem r3e_O_symm (e : Vec d) (ψ : Vec d → ℝ) (x₀ u : Vec d) :
    (r3e_O e ψ x₀ u)ᵀ = r3e_O e ψ x₀ u := flattenHouseholder_transpose _ _

theorem r3e_O_mul_self (e : Vec d) (ψ : Vec d → ℝ) (x₀ u : Vec d) :
    r3e_O e ψ x₀ u * r3e_O e ψ x₀ u = 1 := flattenHouseholder_mul_self _ _

theorem r3e_dot_mulVec (e : Vec d) (ψ : Vec d → ℝ) (x₀ u b w : Vec d) :
    vecDot b (r3e_O e ψ x₀ u *ᵥ w) = vecDot (r3e_O e ψ x₀ u *ᵥ b) w := by
  rw [r3e_vecDot_eq, r3e_vecDot_eq, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose,
    r3e_O_symm]

theorem r3e_mulVec_mulVec (e : Vec d) (ψ : Vec d → ℝ) (x₀ u b : Vec d) :
    r3e_O e ψ x₀ u *ᵥ (r3e_O e ψ x₀ u *ᵥ b) = b := by
  rw [Matrix.mulVec_mulVec, r3e_O_mul_self, Matrix.one_mulVec]

theorem r3e_O_entry_le (e : Vec d) (ψ : Vec d → ℝ) (x₀ u : Vec d) (i k : Fin d) :
    |r3e_O e ψ x₀ u i k| ≤ 1 :=
  flatten_abs_entry_le_one (flattenHouseholder_mul_transpose _ _) i k

theorem r3e_norm_O_le (e : Vec d) (ψ : Vec d → ℝ) (x₀ u b : Vec d) :
    ‖r3e_O e ψ x₀ u *ᵥ b‖ ≤ d * ‖b‖ :=
  flatten_norm_mulVec_le (r3e_O_entry_le e ψ x₀ u) b

/-- An affine function of the chart variable is affine in `y` up to the Taylor remainder. -/
theorem r3e_dot_flatten {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (u x₀ b y : Vec d) :
    vecDot b (flattenMap e ψ x₀ u y) =
      vecDot (r3e_O e ψ x₀ u *ᵥ b) (y - x₀) -
        r3e_T e ψ x₀ y * vecDot (r3e_O e ψ x₀ u *ᵥ b) e := by
  rw [r3e_flattenMap_eq he hψ, r3e_dot_mulVec]
  simp only [r3e_vecDot_eq, dotProduct_sub, dotProduct_smul, smul_eq_mul]

end SuperdiffusionCLT.Section7
