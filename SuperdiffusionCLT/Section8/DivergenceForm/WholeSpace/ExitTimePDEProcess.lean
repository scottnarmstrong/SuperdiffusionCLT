/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.CruxLowerProcess
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.CruxUpperProcess
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.KernelIdentification
public import MarkovProcess.Killed.ExitTimeIdentification
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.ExcessiveCubeData

/-!
# The killed resolvent reads the observable only on the part domain

The expected time the whole-space process spends in a bounded domain before
leaving it is identified through the killed resolvent of the process with the
Dirichlet resolvent of the part domain.  The one fact recorded here is that the
observable may be replaced by another one agreeing with it on the part domain,
which is legitimate because the killed kernels put no mass outside the part
domain (`killedResolvent_congr_of_eqOn`).  In particular the observable may be
replaced by the constant one.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.DivergenceForm

open Filter Homogenization MeasureTheory Set Topology
open MarkovProcess MarkovProcess.Semigroup
open MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal ZeroAtInfty

noncomputable section

/-- **The killed resolvent only reads the observable on the part domain.**
The killed kernels put no mass outside it, so two observables agreeing there
have the same killed resolvent. -/
theorem killedResolvent_congr_of_eqOn {alpha : Type*} [MetricSpace alpha]
    [CompleteSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
    [SecondCountableTopology alpha] [Nonempty alpha]
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (U : Set alpha) (hU : IsOpen U) (lam : ℝ) {f g : alpha → ℝ≥0∞}
    (h : ∀ y ∈ U, f y = g y) (x : alpha) :
    IsConservative.killedResolvent P hP U hU lam f x =
      IsConservative.killedResolvent P hP U hU lam g x := by
  unfold IsConservative.killedResolvent
  refine lintegral_congr fun t => ?_
  refine congrArg _ (lintegral_congr_ae ?_)
  filter_upwards [IsConservative.ae_mem_killedKernel P hP U hU (Real.toNNReal t) x]
    with y hy
  exact h y hy

variable {d : ℕ}

variable [NeZero d]

namespace WholeSpaceAnalyticData

end WholeSpaceAnalyticData

end

end SuperdiffusionCLT.Section8.DivergenceForm
