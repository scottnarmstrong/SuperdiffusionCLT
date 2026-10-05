/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.DivergenceForm.BoundedMeasurableResolvent
public import MarkovProcess.Feller.Resolvent
public import MarkovProcess.Kernel.PositiveC0Resolvent
public import MarkovProcess.Kernel.OnePointExtension
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import Homogenization.Geometry.ConvexDomain

/-!
# The process resolvent and the analytic resolvent agree on `C₀` data

The base case of the comparison between the process resolvent on the one-point
carrier and the analytic resolvent on bounded measurable data.

The conservative model semigroup lives on `OnePoint U`, with observables
extended by `0` at the point at infinity.  For an observable coming from
`C₀(U, ℝ)`, its real kernel resolvent at a point of `U` is the value of the
`C₀` representative of the analytic resolvent, hence the value of the
representative continuous on `U` of the analytic resolvent applied to the same
datum read as a bounded measurable function.

This is the base case of the comparison on bounded measurable observables.
The extension from `C₀` data to all bounded measurable data by a monotone
class argument is not carried out here.

Both statements use the coefficient only through the interior regularity
witness `HasContinuousShiftedResolvents`, so they are stated in that form under
the suffix `_reg`; the small-contrast statements keep their names and are
corollaries.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.DivergenceForm

open Homogenization MeasureTheory
open MarkovProcess MarkovProcess.Semigroup
open SuperdiffusionCLT.Section8.Common.Regularity.Ported
open scoped ZeroAtInfty

noncomputable section

variable {d : ℕ} {U : Set (Vec d)}

/-- The zero extension vanishes outside the domain. -/
theorem domainExtension_of_notMem {f : U → ℝ} {x : Vec d} (hx : x ∉ U) :
    domainExtension f x = 0 := by
  have hnot : ¬ ∃ y : U, (y : Vec d) = x := by
    rintro ⟨y, rfl⟩
    exact hx y.2
  simpa only [domainExtension, Pi.zero_apply] using Function.extend_apply' f (0 : Vec d → ℝ) x hnot

end

end SuperdiffusionCLT.Section8.DivergenceForm
