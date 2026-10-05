/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Defs

/-!
# The adjoint weak equation

The bilinear form of `a` is the transposed bilinear form of `aᵀ`, and a solution of the
`a`-equation tested against a solution of the `aᵀ`-equation gives the duality identity
`∫ f w = ∫ h u`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section7

noncomputable section

variable {d : ℕ}

/-- The `a`-form of `(u, v)` is the `aᵀ`-form of `(v, u)`, pointwise. -/
theorem adjField_integrand_transpose (a : CoeffField d) (p q : Vec d) (x : Vec d) :
    vecDot (matVecMul (a x) p) q = vecDot (matVecMul (matTranspose (a x)) q) p := by
  rw [vecDot_comm (matVecMul (matTranspose (a x)) q) p, vecDot_matVecMul_transpose]

/-- **(3)** For `u, v` in `H¹(U)`: `∫ a∇u·∇v = ∫ aᵀ∇v·∇u`. -/
theorem adjField_integral_transpose (a : CoeffField d) (U : Set (Vec d))
    (u v : H1Function U) :
    ∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (v.grad x) =
      ∫ x in U, vecDot (matVecMul (matTranspose (a x)) (v.grad x)) (u.grad x) :=
  integral_congr_ae (Filter.Eventually.of_forall fun x =>
    adjField_integrand_transpose a (u.grad x) (v.grad x) x)

/-- **Duality.** If `-∇·(a∇u) = f` and `-∇·(aᵀ∇w) = h` in `U` with `u, w ∈ H¹₀(U)`, then
`∫ f w = ∫ h u`. -/
theorem adjField_duality (a : CoeffField d) (U : Set (Vec d)) (u w : H10Function U)
    (f h : Vec d → ℝ)
    (hu : IsWeakSolutionOn a U u.toH1Function f (fun _ => 0))
    (hw : IsWeakSolutionOn (fun x => matTranspose (a x)) U w.toH1Function h (fun _ => 0)) :
    ∫ x in U, f x * w.toH1Function.toFun x = ∫ x in U, h x * u.toH1Function.toFun x := by
  have h1 := hu w
  have h2 := hw u
  simp only [vecDot, Pi.zero_apply, zero_mul, Finset.sum_const_zero, integral_zero,
    add_zero] at h1 h2
  have h3 := adjField_integral_transpose a U u.toH1Function w.toH1Function
  simp only [vecDot] at h3
  rw [← h1, ← h2, h3]

/-- Satisfiability: zero solutions for the identity field. -/
example (U : Set (Vec d)) :
    ∃ (u w : H10Function U) (f h : Vec d → ℝ),
      IsWeakSolutionOn (fun _ => (1 : Mat d)) U u.toH1Function f (fun _ => 0) ∧
      IsWeakSolutionOn (fun x => matTranspose ((fun _ => (1 : Mat d)) x)) U w.toH1Function h
        (fun _ => 0) := by
  refine ⟨0, 0, fun _ => 0, fun _ => 0, ?_, ?_⟩ <;>
  · intro φ
    have hg : ∀ x, (H10Function.toH1Function (0 : H10Function U)).grad x = 0 := fun _ => rfl
    simp [vecDot, matVecMul, hg]

end

end SuperdiffusionCLT.Section8
