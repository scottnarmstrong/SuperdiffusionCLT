/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.ExitEstimateD
public import SuperdiffusionCLT.Section8.Prereq.DirichletRepresentationD
public import SuperdiffusionCLT.Section7.Prereq.RootCarriersApi

/-!
# The quenched second moment: weak solutions and dilation

Linear combinations of scalar-forced weak solutions, and the dilation of a Dirichlet solution of the
unscaled field `fullCoefficientRecentered` on a ball to a Dirichlet solution of
`opScale c⋆ ε • a^ε` on the dilated ball.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section8.DivergenceForm
open SuperdiffusionCLT.Section7
open scoped Pointwise

variable {d : ℕ}

/-- A scalar multiple of a scalar-forced weak solution. -/
theorem dtExp_forced_smul {U : Set (Vec d)} {a : CoeffField d} {g : Vec d → ℝ} {u : H1Function U}
    (c : ℝ) (h : IsScalarForcedWeakSolution a U g u) :
    IsScalarForcedWeakSolution a U (fun x => c * g x) (c • u) := by
  refine ⟨h.1.const_mul c, fun phi => ?_⟩
  have e1 : (fun x => vecDot (matVecMul (a x) ((c • u).grad x)) (phi.toH1Function.grad x)) =
      fun x => c * vecDot (matVecMul (a x) (u.grad x)) (phi.toH1Function.grad x) := by
    funext x
    simp only [H1Function.smul_grad, vecDot, matVecMul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have e2 : (fun x => c * g x * phi.toH1Function.toFun x) =
      fun x => c * (g x * phi.toH1Function.toFun x) := by
    funext x; ring
  simp only [e1, e2, integral_const_mul, h.2 phi]

/-- A sum of scalar-forced weak solutions. -/
theorem dtExp_forced_add {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a) {g₁ g₂ : Vec d → ℝ} {u₁ u₂ : H1Function U}
    (h₁ : IsScalarForcedWeakSolution a U g₁ u₁) (h₂ : IsScalarForcedWeakSolution a U g₂ u₂) :
    IsScalarForcedWeakSolution a U (fun x => g₁ x + g₂ x) (u₁ + u₂) := by
  have h := IsScalarForcedWeakSolution.sub hEll h₁ h₂.neg
  have e : u₁ - -u₂ = u₁ + u₂ := sub_neg_eq_add u₁ u₂
  rw [e] at h
  have e' : (fun x => g₁ x - -g₂ x) = fun x => g₁ x + g₂ x := by
    funext x; ring
  rwa [e'] at h

/-- **Dilation of a Dirichlet solution** of the unscaled field to the field `opScale c⋆ ε • a^ε`
on the dilated domain. -/
theorem dtExp_dilate_dirichlet (nu cStar : ℝ) (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
    {ε : ℝ} (hε : 0 < ε) {V : Set (Vec d)}
    {f : Vec d → ℝ} {g u : H1Function V}
    (hsol : IsDirichletSolution (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega)
      V f g u) :
    IsDirichletSolution (fun x => opScale cStar ε • epField nu omega ε x) ((ε⁻¹)⁻¹ • V)
        (fun x => opScale cStar ε * (ε⁻¹ ^ 2 * f (ε⁻¹ • x)))
        (g.dilateArg (inv_ne_zero hε.ne')) (u.dilateArg (inv_ne_zero hε.ne')) := by
  have hs : ε⁻¹ ≠ 0 := inv_ne_zero hε.ne'
  have h1 := (IsWeakSolutionOn.dilate hs hsol.1).smul (opScale cStar ε)
  refine ⟨?_, ?_⟩
  · refine rc_isWeakSolutionOn_congr (fun y => ?_) (fun y => rfl) (fun y => ?_) h1
    · rfl
    · simp
  · have h2 := rc_memH10_dilate hs hsol.2
    convert h2 using 1
    funext y
    rw [H1Function.dilateArg_toFun, H1Function.dilateArg_toFun]

/-- The weak equation depends on the forcing only through its values on the domain. -/
theorem dtExp_weak_congr_forcing {U : Set (Vec d)} (hU : MeasurableSet U) {a : CoeffField d}
    {u : H1Function U} {f f' : Vec d → ℝ} (h : ∀ x ∈ U, f x = f' x)
    (hs : IsWeakSolutionOn a U u f (fun _ => 0)) : IsWeakSolutionOn a U u f' (fun _ => 0) := by
  intro φ
  rw [hs φ]
  have : (∫ x in U, f x * φ.toFun x) = ∫ x in U, f' x * φ.toFun x :=
    setIntegral_congr_fun hU fun x hx => by simp only [h x hx]
  rw [this]

end SuperdiffusionCLT.Section8
