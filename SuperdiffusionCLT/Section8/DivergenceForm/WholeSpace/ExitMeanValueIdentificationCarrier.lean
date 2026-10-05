/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.ExcessiveCubeData
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.ExitTimePDEIdentification
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.RealResolvent
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
# The zero-trace carrier: ellipticity and the supremum bound

Two facts about the zero-trace value--gradient carrier are isolated here, both used by the
identification of the vanishing-shift limit of the Dirichlet resolvents with a weak solution.

* `mul_norm_gradient_sq_le_coefficientPairing` is the elliptic lower bound of the coefficient
  pairing on the carrier, read off the coercivity estimate of the shifted bilinear form at the
  shift equal to the lower ellipticity constant.
* `norm_scalarL2_le_of_ae_bound` converts an essential supremum bound into an `L²` bound on a
  bounded domain.

None of this is specific to the exhaustion cubes.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.DivergenceForm

open Filter Homogenization MeasureTheory Set Topology
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

variable {d : ℕ}

namespace ZeroTraceSobolev

end ZeroTraceSobolev

/-! ## Ellipticity of the coefficient pairing on the carrier -/

section Coercivity

open ZeroTraceSobolev

variable {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}

/-- The coefficient pairing of two carrier gradients is the value of the unshifted bilinear
form. -/
theorem coefficientPairing_gradient_eq_shiftedBilin
    (hEll : IsEllipticFieldOn lam Lam U a) (u w : ZeroTraceSobolev U) :
    coefficientPairing a U (gradient u) (gradient w) = shiftedBilin hEll (0 : ℝ) u w := by
  rw [shiftedBilin_apply]
  ring

/-- **The elliptic lower bound of the coefficient pairing on the carrier.** -/
theorem mul_norm_gradient_sq_le_coefficientPairing
    (hEll : IsEllipticFieldOn lam Lam U a) (u : ZeroTraceSobolev U) :
    lam * ‖gradient u‖ ^ 2 ≤ coefficientPairing a U (gradient u) (gradient u) := by
  have h := shiftedBilin_lower_bound (α := lam) hEll u
  rw [shiftedBilin_apply, min_self] at h
  have hnorm : ‖u‖ * ‖u‖ = ‖toL2 u‖ ^ 2 + ‖gradient u‖ ^ 2 := by
    rw [← pow_two, ZeroTraceSobolev.norm_sq_eq]
  rw [mul_assoc, hnorm, real_inner_self_eq_norm_sq] at h
  linarith only [h]

end Coercivity

/-! ## The supremum-to-`L²` bound -/

/-- The factor converting an essential supremum bound into an `L²` bound on a domain. -/
def scalarL2Factor (U : Set (Vec d)) : ℝ :=
  (MeasureTheory.volume U).toReal ^ (2 : ℝ)⁻¹

theorem scalarL2Factor_nonneg (U : Set (Vec d)) : 0 ≤ scalarL2Factor U :=
  Real.rpow_nonneg ENNReal.toReal_nonneg _

/-- **An essential supremum bound on a bounded domain is an `L²` bound.** -/
theorem norm_scalarL2_le_of_ae_bound {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (F : ScalarL2 U) {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ᵐ x ∂volumeMeasureOn U, |F x| ≤ C) :
    ‖F‖ ≤ scalarL2Factor U * C := by
  let := hU.isFiniteMeasure_restrict_volume
  have hbound : ∀ᵐ x ∂volumeMeasureOn U, ‖F x‖ ≤ C := by
    filter_upwards [hF] with x hx
    simpa only [Real.norm_eq_abs] using hx
  have h := MeasureTheory.Lp.norm_le_of_ae_bound
    (μ := volumeMeasureOn U) (p := 2) (f := F) hC hbound
  refine h.trans (le_of_eq ?_)
  have hfactor : ((measureUnivNNReal (volumeMeasureOn U) : ℝ)) =
      (MeasureTheory.volume U).toReal := by
    rw [← ENNReal.coe_toReal, coe_measureUnivNNReal, Measure.restrict_apply_univ]
  rw [scalarL2Factor, hfactor, show ((2 : ℝ≥0∞).toReal) = (2 : ℝ) by norm_num]

end

end SuperdiffusionCLT.Section8.DivergenceForm
