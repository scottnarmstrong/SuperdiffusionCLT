/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.ExcessiveCubeData
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.ExitMeanValue
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.ExitTimePDEIdentification
public import Homogenization.Ambient.Basic
public import Homogenization.CoarseGraining.QuadraticStability.Integral
public import Homogenization.HighContrast.Coupled.LocalEnergy.Bounds
public import Homogenization.HighContrast.Coupled.Stampacchia.DeGiorgiCore
public import Homogenization.HighContrast.Coupled.Stampacchia.Iteration
public import Homogenization.HighContrast.Coupled.Stampacchia.LevelEnergy
public import Homogenization.HighContrast.Coupled.Stampacchia.LevelRecursion
public import Homogenization.Sobolev.CubeEmbedding.LimitFiniteP
public import Homogenization.Sobolev.W1p.FiniteMeasureDowngrade
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Differences of harmonic parts

The harmonic parts of the exit decomposition are attached to nonnegative continuous
data vanishing at infinity, because the exit decomposition is an extended-real statement.  A
general datum is a difference of two nonnegative ones: a continuous datum vanishing at infinity
is the difference of its positive and negative parts, both nonnegative and vanishing at
infinity.  This file records the elementary bound on such data, namely that the absolute value
of a continuous datum vanishing at infinity is at most its norm
(`abs_apply_le_norm_zeroAtInfty`).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.StoppedDirichlet

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal NNReal

noncomputable section

section Process

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

end Process

end

end SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.StoppedDirichlet

namespace SuperdiffusionCLT.Section8.DivergenceForm

open Filter Homogenization MeasureTheory Set Topology
open MarkovProcess MarkovProcess.Semigroup
open SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.StoppedDirichlet
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

variable {d : ℕ}

/-! ## The positive part of a continuous datum vanishing at infinity -/

/-- The absolute value of a continuous datum vanishing at infinity is at most its norm. -/
theorem abs_apply_le_norm_zeroAtInfty (g : C₀(Vec d, ℝ)) (y : Vec d) : |g y| ≤ ‖g‖ := by
  rw [← Real.norm_eq_abs, ← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  exact BoundedContinuousFunction.norm_coe_le_norm g.toBCF y

variable [NeZero d]

namespace WholeSpaceAnalyticData

end WholeSpaceAnalyticData

end

end SuperdiffusionCLT.Section8.DivergenceForm
