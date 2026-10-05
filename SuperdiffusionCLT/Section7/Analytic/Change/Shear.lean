/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Homogenization.Ambient.Basic

/-!
# The coordinate shear

For a unit vector `e` and a function `ψ`, the shear `y ↦ y - ψ(Py) e`, with `P y = y - ⟨e,y⟩ e`
the orthogonal projection onto `e^⊥`, preserves Lebesgue measure and has the explicit inverse
`y ↦ y + ψ(Py) e`.

## Main results

* `Section7.shear`
* `Section7.shear_neg_left_inverse`, `Section7.shear_neg_right_inverse`
* `Section7.measurePreserving_shear`
-/

@[expose] public section

open MeasureTheory Homogenization

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The shear `y ↦ y - ψ(Py) e` along the unit vector `e`, `P y = y - ⟨e,y⟩ e`. -/
noncomputable def shear (e : Vec d) (ψ : Vec d → ℝ) (y : Vec d) : Vec d :=
  y - ψ (y - vecDot e y • e) • e

theorem vecDot_sub_smul_self {e : Vec d} (he : vecNormSq e = 1) (y : Vec d) (c : ℝ) :
    vecDot e (y - c • e) = vecDot e y - c := by
  have h : vecDot e (y - c • e) = vecDot e y - c * vecNormSq e := by
    simp only [vecDot, vecNormSq, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub,
      Finset.sum_sub_distrib]
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h, he, mul_one]

theorem proj_shear {e : Vec d} (he : vecNormSq e = 1) (ψ : Vec d → ℝ) (y : Vec d) :
    shear e ψ y - vecDot e (shear e ψ y) • e = y - vecDot e y • e := by
  unfold shear
  rw [vecDot_sub_smul_self he]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- `shear e (-ψ)` is a left inverse of `shear e ψ`. -/
theorem shear_neg_left_inverse {e : Vec d} (he : vecNormSq e = 1) (ψ : Vec d → ℝ) :
    shear e (-ψ) ∘ shear e ψ = id := by
  funext y
  have h := proj_shear he ψ y
  simp only [Function.comp_apply, id]
  have h2 : shear e (-ψ) (shear e ψ y)
      = shear e ψ y - (-ψ) (shear e ψ y - vecDot e (shear e ψ y) • e) • e := rfl
  rw [h2, h]
  unfold shear
  ext i
  simp only [Pi.neg_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- `shear e (-ψ)` is a right inverse of `shear e ψ`. -/
theorem shear_neg_right_inverse {e : Vec d} (he : vecNormSq e = 1) (ψ : Vec d → ℝ) :
    shear e ψ ∘ shear e (-ψ) = id := by
  have := shear_neg_left_inverse he (-ψ)
  rwa [neg_neg] at this

theorem shear_bijective {e : Vec d} (he : vecNormSq e = 1) (ψ : Vec d → ℝ) :
    Function.Bijective (shear e ψ) :=
  Function.bijective_iff_has_inverse.2
    ⟨shear e (-ψ), congrFun (shear_neg_left_inverse he ψ), congrFun (shear_neg_right_inverse he ψ)⟩

theorem vecDot_add_smul_self {e : Vec d} (he : vecNormSq e = 1) (y : Vec d) (c : ℝ) :
    vecDot e (y + c • e) = vecDot e y + c := by
  have := vecDot_sub_smul_self he y (-c)
  simpa [sub_eq_add_neg] using this

/-- The coordinate function `z ↦ ψ(Pz)`, which does not depend on the `e` coordinate. -/
theorem proj_add_smul {e : Vec d} (he : vecNormSq e = 1) (y : Vec d) (t : ℝ) :
    (y + t • e) - vecDot e (y + t • e) • e = y - vecDot e y • e := by
  rw [vecDot_add_smul_self he]
  ext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem differentiable_vecDot_left (e : Vec d) : Differentiable ℝ (fun z : Vec d => vecDot e z) := by
  unfold vecDot
  refine Differentiable.fun_sum fun i _ => ?_
  fun_prop

theorem differentiable_proj_comp {e : Vec d} {ψ : Vec d → ℝ} (hψ : Differentiable ℝ ψ) :
    Differentiable ℝ (fun z : Vec d => ψ (z - vecDot e z • e)) := by
  refine hψ.comp ?_
  exact differentiable_id.sub (Differentiable.smul_const (differentiable_vecDot_left e) e)

/-- The derivative of `z ↦ ψ(Pz)` vanishes in the direction `e`. -/
theorem fderiv_proj_comp_self {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : Differentiable ℝ ψ) (y : Vec d) :
    fderiv ℝ (fun z : Vec d => ψ (z - vecDot e z • e)) y e = 0 := by
  have hG := (differentiable_proj_comp (e := e) hψ) (y + (0 : ℝ) • e)
  have hline : HasDerivAt (fun t : ℝ => y + t • e) e 0 := by
    simpa using (HasDerivAt.const_add y (HasDerivAt.smul_const (hasDerivAt_id (0 : ℝ)) e))
  have h1 := (HasFDerivAt.comp_hasDerivAt (0 : ℝ) hG.hasFDerivAt hline)
  have h2 : HasDerivAt
      (fun t : ℝ => (fun z : Vec d => ψ (z - vecDot e z • e)) (y + t • e)) 0 0 := by
    have : (fun t : ℝ => (fun z : Vec d => ψ (z - vecDot e z • e)) (y + t • e))
        = fun _ => ψ (y - vecDot e y • e) := by
      funext t
      simp only [proj_add_smul he]
    rw [this]
    exact hasDerivAt_const _ _
  have h3 := h1.unique h2
  simpa using h3

theorem hasFDerivAt_shear {e : Vec d} {ψ : Vec d → ℝ} (hψ : Differentiable ℝ ψ) (y : Vec d) :
    HasFDerivAt (shear e ψ)
      (ContinuousLinearMap.id ℝ (Vec d) -
        (fderiv ℝ (fun z : Vec d => ψ (z - vecDot e z • e)) y).smulRight e) y := by
  have hG := ((differentiable_proj_comp (e := e) hψ) y).hasFDerivAt
  exact (hasFDerivAt_id y).sub (HasFDerivAt.smul_const hG e)

end SuperdiffusionCLT.Section7
