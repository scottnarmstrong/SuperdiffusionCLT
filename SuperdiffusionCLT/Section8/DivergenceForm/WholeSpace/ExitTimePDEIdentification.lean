/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.ExcessiveCubeData
public import Homogenization.Ambient.Basic
public import Homogenization.CoarseGraining.QuadraticStability.Integral
public import Homogenization.Deterministic.ConstantCoefficientDirichletBesov.Basic
public import Homogenization.HighContrast.Coupled.LocalEnergy.Bounds
public import Homogenization.HighContrast.Coupled.Stampacchia.DeGiorgiCore
public import Homogenization.HighContrast.Coupled.Stampacchia.Iteration
public import Homogenization.HighContrast.Coupled.Stampacchia.LevelEnergy
public import Homogenization.HighContrast.Coupled.Stampacchia.LevelRecursion
public import Homogenization.Sobolev.CubeEmbedding.LimitFiniteP
public import Homogenization.Sobolev.Truncation.Basic
public import Homogenization.Sobolev.W1p.FiniteMeasureDowngrade
public import MarkovProcess.Kernel.OnePointKilled
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# From the scalar weak equation to the shifted weak equation

This file records the passage from the scalar weak equation
to the shifted weak equation on the zero-trace graph carrier
(`isAlphaShiftedWeakSolution_of_isScalarForcedWeakSolution`): a solution of
`-div (a grad u) = g` also solves `(lam - div (a grad)) u = g + lam u`, and on
an open bounded convex domain the graph carrier is exhausted by honest
zero-trace Sobolev functions, so the test class is the same one.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.DivergenceForm

open Homogenization MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## From the scalar equation to the shifted equation -/

/-- **The scalar weak equation is a shifted weak equation with shifted
forcing.**  On an open bounded convex domain every element of the zero-trace
graph carrier is an honest zero-trace Sobolev function, so the two test
classes agree. -/
theorem isAlphaShiftedWeakSolution_of_isScalarForcedWeakSolution
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) {a : CoeffField d}
    {alpha : ℝ} (u : H10Function U) {g : Vec d → ℝ}
    (hg : IsScalarForcedWeakSolution a U g u.toH1Function) (G : ScalarL2 U)
    (hG : ∀ᵐ x ∂volumeMeasureOn U,
      G x = g x + alpha * u.toH1Function.toFun x) :
    IsAlphaShiftedWeakSolution a U alpha G
      (ZeroTraceSobolev.ofH10Function u) := by
  intro z
  obtain ⟨φ, hφvalue, hφgrad⟩ := ZeroTraceSobolev.exists_h10Function hU z
  have hvalue : ZeroTraceSobolev.toL2 z = φ.toH1Function.toScalarL2 := hφvalue.symm
  have hgrad : ZeroTraceSobolev.gradient z = φ.toH1Function.gradToHilbertVectorL2 :=
    hφgrad.symm
  have hcoefficient :
      coefficientPairing a U
          (ZeroTraceSobolev.gradient (ZeroTraceSobolev.ofH10Function u))
          (ZeroTraceSobolev.gradient z) =
        ∫ x in U, vecDot (matVecMul (a x) (u.toH1Function.grad x))
          (φ.toH1Function.grad x) ∂volume := by
    rw [ZeroTraceSobolev.gradient_ofH10Function, hgrad, coefficientPairing]
    apply integral_congr_ae
    filter_upwards
      [u.toH1Function.coeFn_gradToHilbertVectorL2,
        φ.toH1Function.coeFn_gradToHilbertVectorL2,
        coeFn_hilbertVectorL2ToVectorL2 (U := U)
          u.toH1Function.gradToHilbertVectorL2,
        coeFn_hilbertVectorL2ToVectorL2 (U := U)
          φ.toH1Function.gradToHilbertVectorL2] with x hu hv hu' hv'
    rw [hu', hv', hu, hv]
    rfl
  have hmass :
      inner ℝ (ZeroTraceSobolev.toL2 (ZeroTraceSobolev.ofH10Function u))
          (ZeroTraceSobolev.toL2 z) =
        ∫ x in U, u.toH1Function.toFun x * φ.toH1Function.toFun x ∂volume := by
    rw [ZeroTraceSobolev.toL2_ofH10Function, hvalue, scalarInner_eq_integral]
    apply integral_congr_ae
    filter_upwards [u.toH1Function.coeFn_toScalarL2,
      φ.toH1Function.coeFn_toScalarL2] with x hu hv
    rw [hu, hv]
  have hforcing : inner ℝ G (ZeroTraceSobolev.toL2 z) =
      ∫ x in U, (g x + alpha * u.toH1Function.toFun x) *
        φ.toH1Function.toFun x ∂volume := by
    rw [hvalue, scalarInner_eq_integral]
    apply integral_congr_ae
    filter_upwards [hG, φ.toH1Function.coeFn_toScalarL2] with x hGx hv
    rw [hGx, hv]
  have hgInt : Integrable (fun x => g x * φ.toH1Function.toFun x)
      (volumeMeasureOn U) := hg.1.integrable_mul φ.toH1Function.memL2
  have huInt : Integrable
      (fun x => alpha * (u.toH1Function.toFun x * φ.toH1Function.toFun x))
      (volumeMeasureOn U) :=
    (u.toH1Function.memL2.integrable_mul φ.toH1Function.memL2).const_mul alpha
  rw [hcoefficient, hmass, hforcing, hg.2 φ]
  calc
    alpha * ∫ x in U, u.toH1Function.toFun x * φ.toH1Function.toFun x ∂volume +
          ∫ x in U, g x * φ.toH1Function.toFun x ∂volume =
        (∫ x in U, alpha *
            (u.toH1Function.toFun x * φ.toH1Function.toFun x) ∂volume) +
          ∫ x in U, g x * φ.toH1Function.toFun x ∂volume := by
      rw [integral_const_mul]
    _ = ∫ x in U, (g x * φ.toH1Function.toFun x +
          alpha * (u.toH1Function.toFun x * φ.toH1Function.toFun x)) ∂volume := by
      rw [integral_add hgInt huInt]
      ring
    _ = ∫ x in U, (g x + alpha * u.toH1Function.toFun x) *
          φ.toH1Function.toFun x ∂volume := by
      apply integral_congr_ae
      filter_upwards with x
      ring

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)

/-! ## The torsion function -/

/-! ## The uniform bound -/

end WholeSpaceAnalyticData

end

end SuperdiffusionCLT.Section8.DivergenceForm
