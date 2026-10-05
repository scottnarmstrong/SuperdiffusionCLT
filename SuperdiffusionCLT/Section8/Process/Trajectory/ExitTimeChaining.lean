/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import MarkovProcess.Trajectory.ResolventExitDecomposition

/-!
# Chaining bounds for exit times

This file defines the discounted finite-time weight of an extended-real time functional, the
building block for chaining the exits of a sequence of stopping times, and shows that it is
measurable, both for the stopped sigma-algebra of a canonical-filtration stopping time and for the
Borel sigma-algebra.

Public declarations:

* `ContinuousPath.discountedStoppingWeight`;
* `ContinuousPath.measurable_discountedStoppingWeight_stopped`;
* `ContinuousPath.measurable_discountedStoppingWeight`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

open MarkovProcess

namespace SuperdiffusionCLT.Section8.Process

namespace ContinuousPath

open MarkovProcess.ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]

/-- The discounted finite-time weight of an extended-real time functional. -/
noncomputable def discountedStoppingWeight (lam : ℝ) (sigma : ContinuousPath alpha → ℝ≥0∞)
    (omega : ContinuousPath alpha) : ℝ≥0∞ :=
  ({omega | sigma omega < ⊤} : Set _).indicator
    (fun omega ↦ ENNReal.ofReal (Real.exp (-lam * (sigma omega).toReal))) omega

section Measurable

variable [TopologicalSpace.PseudoMetrizableSpace alpha] [SecondCountableTopology alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]

omit [TopologicalSpace.PseudoMetrizableSpace alpha] [SecondCountableTopology alpha] in
/-- The discounted finite-time weight of a canonical-filtration stopping time is measurable for
its stopped sigma-algebra. -/
theorem measurable_discountedStoppingWeight_stopped
    (sigma : ContinuousPath alpha → ℝ≥0∞)
    (hsigma : IsStoppingTime (canonicalFiltration (alpha := alpha)) sigma) (lam : ℝ) :
    Measurable[hsigma.measurableSpace] (discountedStoppingWeight lam sigma) := by
  exact (ENNReal.measurable_ofReal.comp
    (Real.continuous_exp.measurable.comp
      (measurable_const.mul (ENNReal.measurable_toReal.comp hsigma.measurable)))).indicator
        (StoppingTime.measurableSet_stoppingTime_lt_top hsigma)

omit [TopologicalSpace.PseudoMetrizableSpace alpha] [SecondCountableTopology alpha] in
/-- The discounted finite-time weight of a canonical-filtration stopping time is Borel
measurable on path space. -/
theorem measurable_discountedStoppingWeight
    (sigma : ContinuousPath alpha → ℝ≥0∞)
    (hsigma : IsStoppingTime (canonicalFiltration (alpha := alpha)) sigma) (lam : ℝ) :
    Measurable (discountedStoppingWeight lam sigma) :=
  (measurable_discountedStoppingWeight_stopped sigma hsigma lam).mono
    hsigma.measurableSpace_le le_rfl

end Measurable

end ContinuousPath

namespace SubMarkovKernelSemigroup

open MarkovProcess.SubMarkovKernelSemigroup

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha] [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

end

end SubMarkovKernelSemigroup

end SuperdiffusionCLT.Section8.Process
