/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Prereq.HarmonicApproxBridge
public import Homogenization.Sobolev.Foundations.CubeCalderonZygmund.H10Adjoint
public import Homogenization.Book.Ch03.Theorems.PublicInternalBridges.H1Casts

/-!
# Zero-trace remainder on a triadic cube

For `u` in `H¹(Q)` there is `w` in `H¹₀(Q)` with the same Dirichlet pairing as `u`, so that
`u - w` is the harmonic function with the boundary values of `u`. This is the Riesz
representation theorem of `CoarseGraining` on the open axis cube, transported to the open
triadic cube.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6.HarmonicApprox

open Homogenization

noncomputable section

variable {d : ℕ}

theorem openCubeSet_eq_axisCube_triadic (Q : TriadicCube d) :
    openCubeSet Q =
      axisCube (fun j => ((Q.index j : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q)
        (cubeScaleFactor Q) := by
  have hupper : ∀ j : Fin d,
      ((Q.index j : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q + cubeScaleFactor Q =
        ((Q.index j : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q := by
    intro j
    ring
  ext x
  simp only [openCubeSet, axisCube, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ,
    forall_true_left, Set.mem_Ioo]
  simp_rw [hupper]

theorem exists_zeroTrace_remainder_of_eq [NeZero d] {U : Set (Vec d)} {z : Vec d} {L sigma : ℝ}
    (hU : U = axisCube z L) (hL : 0 < L) (hsigma : 0 < sigma) (u : H1Function U) :
    ∃ w : H10Function U, ∀ ψ : H10Function U,
      ∫ x in U, vecDot (w.toH1Function.grad x) (ψ.toH1Function.grad x) =
        ∫ x in U, vecDot (u.grad x) (ψ.toH1Function.grad x) := by
  subst hU
  have hG : MemVectorL2 (axisCube z L) (fun x => (-sigma) • u.grad x) :=
    MeasureTheory.MemLp.const_smul u.grad_memVectorL2 (-sigma : ℝ)
  obtain ⟨v, hv, -⟩ := CubeCalderonZygmund.exists_axisCubeScalarDivergenceSolution z hL hsigma
    (fun x => (-sigma) • u.grad x) hG
  refine ⟨v, fun ψ => ?_⟩
  have h := hv ψ
  have h2 : sigma * ∫ x in axisCube z L, vecDot (v.toH1Function.grad x) (ψ.toH1Function.grad x) =
      sigma * ∫ x in axisCube z L, vecDot (u.grad x) (ψ.toH1Function.grad x) := by
    rw [h]
    simp_rw [vecDot_smul_left]
    rw [MeasureTheory.integral_const_mul]
    ring
  exact mul_left_cancel₀ hsigma.ne' h2

/-- The zero-trace remainder: `w ∈ H¹₀(Q)` with the same Dirichlet pairing as `u`. -/
theorem exists_zeroTrace_remainder [NeZero d] (Q : TriadicCube d) {sigma : ℝ}
    (hsigma : 0 < sigma) (u : H1Function (openCubeSet Q)) :
    ∃ w : H10Function (openCubeSet Q), ∀ ψ : H10Function (openCubeSet Q),
      ∫ x in openCubeSet Q, vecDot (w.toH1Function.grad x) (ψ.toH1Function.grad x) =
        ∫ x in openCubeSet Q, vecDot (u.grad x) (ψ.toH1Function.grad x) := by
  have hL : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  exact exists_zeroTrace_remainder_of_eq (openCubeSet_eq_axisCube_triadic Q) hL hsigma u

end

end SuperdiffusionCLT.Section6.HarmonicApprox
