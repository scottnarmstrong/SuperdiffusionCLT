/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Change.LinearEquation

/-!
# Scalar dilation of weak solutions with a right-hand side

For `s ≠ 0` the dilated function `u_s(y) = u(s y)` lives on `s⁻¹ • U`. If `u` solves
`-∇·(a∇u) = f - ∇·g` in `U`, then `u_s` solves the same equation in `s⁻¹ • U` with coefficient
`a(s ·)`, source `s² f(s ·)` and forcing `s g(s ·)`. This is the rescaling
`u_R(y) = u^ε(ε y)` of the paper and the `3^K` rescalings of the boundary-value problems
(`s = 3^{-K}`, `s = ε`, `s = T`). The result is obtained from the linear change of variables
with `T = s⁻¹ Id`, followed by multiplication of the equation by `s²`.

## Main results

* `SuperdiffusionCLT.Section7.IsWeakSolutionOn.dilate`
* `SuperdiffusionCLT.Section7.IsWeakSolutionOn.dilate_h10`
* `SuperdiffusionCLT.Section7.lpBar_dilate`
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization MeasureTheory
open scoped ENNReal Pointwise

variable {d : ℕ}

theorem a18_isUnit_smul_one {s : ℝ} (hs : s ≠ 0) : IsUnit ((s⁻¹ : ℝ) • (1 : Mat d)) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  simp [hs]

/-- The continuous linear equivalence `x ↦ s⁻¹ x`. -/
noncomputable def a18Equiv (d : ℕ) {s : ℝ} (hs : s ≠ 0) : Vec d ≃L[ℝ] Vec d :=
  matrixContinuousLinearEquiv ((s⁻¹ : ℝ) • (1 : Mat d)) (a18_isUnit_smul_one hs)

theorem a18_matVecMul_smul_one (c : ℝ) (v : Vec d) : matVecMul (c • (1 : Mat d)) v = c • v := by
  change (c • (1 : Mat d)).mulVec v = c • v
  rw [Matrix.smul_mulVec, Matrix.one_mulVec]

theorem a18Equiv_apply {s : ℝ} (hs : s ≠ 0) (x : Vec d) : a18Equiv d hs x = s⁻¹ • x :=
  a18_matVecMul_smul_one _ _

theorem a18Equiv_symm_apply {s : ℝ} (hs : s ≠ 0) (y : Vec d) :
    (a18Equiv d hs).symm y = s • y := by
  rw [ContinuousLinearEquiv.symm_apply_eq, a18Equiv_apply, smul_smul, inv_mul_cancel₀ hs, one_smul]

theorem a18Equiv_image {s : ℝ} (hs : s ≠ 0) (U : Set (Vec d)) :
    a18Equiv d hs '' U = s⁻¹ • U := by
  rw [← Set.image_smul]
  exact Set.image_congr fun x _ => a18Equiv_apply hs x

/-- Transfer of weak solutions along an equality of the domain and of the data. -/
theorem a18_transfer {U V : Set (Vec d)} (h : U = V) {a a' : CoeffField d} {u : H1Function U}
    {f f' : Vec d → ℝ} {g g' : Vec d → Vec d} (ha : ∀ x, a x = a' x) (hf : ∀ x, f x = f' x)
    (hg : ∀ x, g x = g' x) (hu : IsWeakSolutionOn a U u f g) :
    IsWeakSolutionOn a' V (u.castSet h) f' g' := by
  subst h
  have ha' : a = a' := funext ha
  have hf' : f = f' := funext hf
  have hg' : g = g' := funext hg
  subst ha' hf' hg'
  exact hu

end SuperdiffusionCLT.Section7

namespace Homogenization

open SuperdiffusionCLT.Section7
open scoped Pointwise

variable {d : ℕ}

/-- The dilation `u_s(y) = u(s y)` of an `H¹` function, on `s⁻¹ • U`. -/
noncomputable def H1Function.dilateArg {U : Set (Vec d)} {s : ℝ} (hs : s ≠ 0) (u : H1Function U) :
    H1Function (s⁻¹ • U) :=
  (u.compLinearEquiv (a18Equiv d hs)).castSet (a18Equiv_image hs U)

theorem H1Function.dilateArg_toFun {U : Set (Vec d)} {s : ℝ} (hs : s ≠ 0) (u : H1Function U)
    (y : Vec d) : (u.dilateArg hs).toFun y = u.toFun (s • y) := by
  simp only [H1Function.dilateArg, H1Function.castSet_toFun, H1Function.compLinearEquiv_toFun,
    a18Equiv_symm_apply]

theorem H1Function.dilateArg_grad {U : Set (Vec d)} {s : ℝ} (hs : s ≠ 0) (u : H1Function U)
    (y : Vec d) : (u.dilateArg hs).grad y = s • u.grad (s • y) := by
  ext i
  simp only [H1Function.dilateArg, H1Function.castSet_grad, H1Function.compLinearEquiv_grad,
    a18Equiv_symm_apply, vecDot, Pi.smul_apply, smul_eq_mul, basisVec_apply]
  rw [Finset.sum_eq_single i]
  · simp
    ring
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The dilation of an `H¹₀` function. -/
noncomputable def H10Function.dilateArg {U : Set (Vec d)} {s : ℝ} (hs : s ≠ 0) (u : H10Function U) :
    H10Function (s⁻¹ • U) :=
  (u.compLinearEquiv (a18Equiv d hs)).castSet (a18Equiv_image hs U)

theorem H10Function.dilateArg_toH1Function {U : Set (Vec d)} {s : ℝ} (hs : s ≠ 0)
    (u : H10Function U) : (u.dilateArg hs).toH1Function = u.toH1Function.dilateArg hs := by
  simp only [H10Function.dilateArg, H1Function.dilateArg, H10Function.castSet_toH1Function]
  rfl

end Homogenization

namespace SuperdiffusionCLT.Section7

open Homogenization
open scoped Pointwise

variable {d : ℕ}

/-- **Scalar dilation of weak solutions with a right-hand side.** -/
theorem IsWeakSolutionOn.dilate {U : Set (Vec d)} {a : CoeffField d} {u : H1Function U}
    {f : Vec d → ℝ} {g : Vec d → Vec d} {s : ℝ} (hs : s ≠ 0)
    (hu : IsWeakSolutionOn a U u f g) :
    IsWeakSolutionOn (fun y => a (s • y)) (s⁻¹ • U) (u.dilateArg hs)
      (fun y => s ^ 2 * f (s • y)) (fun y => s • g (s • y)) := by
  have h1 := IsWeakSolutionOn.linearChange ((s⁻¹ : ℝ) • (1 : Mat d)) (a18_isUnit_smul_one hs) hu
  have h2 := IsWeakSolutionOn.smul (s ^ 2) h1
  have h3 := a18_transfer (a18Equiv_image hs U)
    (a' := fun y => a (s • y)) (f' := fun y => s ^ 2 * f (s • y))
    (g' := fun y => s • g (s • y)) ?_ ?_ ?_ h2
  · exact h3
  · intro y
    change (s ^ 2) • ((s⁻¹ • (1 : Mat d)) * a ((a18Equiv d hs).symm y) *
      (s⁻¹ • (1 : Mat d)).transpose) = a (s • y)
    rw [a18Equiv_symm_apply, Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul,
      Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, smul_smul]
    have : s ^ 2 * s⁻¹ * s⁻¹ = 1 := by field_simp
    rw [this, one_smul]
  · intro y
    change s ^ 2 * f ((a18Equiv d hs).symm y) = s ^ 2 * f (s • y)
    rw [a18Equiv_symm_apply]
  · intro y
    change s ^ 2 • matVecMul (s⁻¹ • (1 : Mat d)) (g ((a18Equiv d hs).symm y)) = s • g (s • y)
    rw [a18Equiv_symm_apply, a18_matVecMul_smul_one, smul_smul]
    have : s ^ 2 * s⁻¹ = s := by field_simp
    rw [this]

/-- The dilation of an `H¹₀` weak solution (`IsH10WeakSolution`). -/
theorem IsWeakSolutionOn.dilate_h10 {U : Set (Vec d)} {a : CoeffField d} {u : H10Function U}
    {f : Vec d → ℝ} {g : Vec d → Vec d} {s : ℝ} (hs : s ≠ 0)
    (hu : IsWeakSolutionOn a U u.toH1Function f g) :
    IsWeakSolutionOn (fun y => a (s • y)) (s⁻¹ • U) (u.dilateArg hs).toH1Function
      (fun y => s ^ 2 * f (s • y)) (fun y => s • g (s • y)) := by
  rw [H10Function.dilateArg_toH1Function]
  exact hu.dilate hs

end SuperdiffusionCLT.Section7
