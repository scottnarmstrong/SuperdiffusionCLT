/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.FieldProcessInputL
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.CruxFieldGeneralDomain
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.CruxFieldInterchange
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.CruxFieldLower
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.ExcessiveCubeData
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.ExitTimePDEIdentification
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.ExitTimePDEProcess
public import Homogenization.Geometry.CubeMeasure

/-!
# Exit-time identification for the marginal field

For a skew field `k` with the process input of `FieldInputData`, the continuous-path process of
the analytic minimal resolvent of `∇·(nu Id + k)∇` has the exit-time identifications of the
coefficient-generic barrier comparison.  The kernel semigroup is the one of
`LogGrowthBounds.resolvent`, the regularity data are those of `LogGrowthBounds.processInput`,
and the operator identification against the barrier resolvent holds by definition.

* `fieldExit_killedResolvent_eq_partResolvent`: on every open bounded convex part domain, the
  killed resolvent of the datum of a barrier datum is the continuous representative of the part
  resolvent.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization Homogenization.Book.Ch02 MeasureTheory Set
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section6
open SuperdiffusionCLT.Section8.DivergenceForm
open SuperdiffusionCLT.Section8.Common.Support
open MarkovProcess MarkovProcess.Semigroup MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal ZeroAtInfty

noncomputable section

variable {d : ℕ} [NeZero d] {nu : ℝ} {k : Vec d → Mat d} (D : FieldInputData d nu k)

/-- **Crux equality for the marginal field.**  On every open bounded convex part domain, the
resolvent of the process killed on leaving the compactified part domain is the continuous
representative of the part resolvent. -/
theorem fieldExit_killedResolvent_eq_partResolvent
    (P : WholeSpaceBarrierData D.analyticData) {x : Vec d} (hx : x ∈ P.V) :
    let hreg := D.logGrowthBounds.processInput.toOnePointRegular
    let := hreg.metricSpace
    let := hreg.completeSpace
    IsConservative.killedResolvent D.logGrowthBounds.resolvent.onePointKernelSemigroup
        D.logGrowthBounds.resolvent.isConservative_onePointKernelSemigroup
        (((↑) : Vec d → OnePoint (Vec d)) '' P.V)
        (OnePoint.isOpen_image_coe.mpr P.hV.isOpen) (P.lam : ℝ)
        (PositiveC0ContractiveResolvent.onePointLiveExtension
          (fun y => ENNReal.ofReal (P.f y))) (x : OnePoint (Vec d)) =
      ENNReal.ofReal (P.utilde x) :=
  P.killedResolvent_eq_partResolvent_general_of_logGrowth D.logGrowthBounds
    D.logGrowthBounds.resolvent D.logGrowthBounds.processInput.toOnePointRegular
    D.logGrowthBounds.isConservative_kernelSemigroup
    D.logGrowthBounds.kernelResolventIdentifiesAnalyticMinimal (fun _ _ => rfl) hx

/-! ## Satisfiability witnesses -/

/-- The barrier data exist for the analytic datum of every admissible field. -/
example : WholeSpaceC0BarrierData D.analyticData := D.logGrowthBounds.c0BarrierData

/-- The fixed-collar profile tends to zero for every admissible field. -/
example (v : ℕ) :
    Filter.Tendsto (D.logGrowthBounds.fixedCollarTailProfile v) Filter.atTop (nhds 0) :=
  D.logGrowthBounds.tendsto_fixedCollarTailProfile_atTop v

/-- The penalization interchange holds for the zero datum on every exhaustion cube. -/
example (v : ℕ) (mu : PositiveShift) {x : Vec d} (hx : x ∈ wholeSpaceCube d v)
    (hzero : ∀ _ : Vec d, |(0 : ℝ)| ≤ 1) :
    (⨅ n : ℕ, ((D.analyticData.analyticPenalizedResolvent
      (isOpenBoundedConvexDomain_wholeSpaceCube d v).isOpen n mu (fun _ ↦ (0 : ℝ))
      measurable_const hzero x).toReal)) ≤
      D.analyticData.analyticCubeResolvent mu (fun _ ↦ (0 : ℝ)) measurable_const
        hzero v x :=
  D.logGrowthBounds.iInf_toReal_analyticPenalizedResolvent_le_cube_of_bound v mu
    measurable_const (fun _ ↦ le_rfl) one_pos hzero
    (Filter.Eventually.of_forall fun _ _ ↦ rfl) hx

end

end SuperdiffusionCLT.Section8
