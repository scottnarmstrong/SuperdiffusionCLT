/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.FieldExitTime
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.ExitTimePDEProcess
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.ExitTimePDEIdentification
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.ExitMeanValueIdentificationGreen
public import MarkovProcess.Trajectory.ExitTimeLaplace

/-!
# The Laplace transform of the exit time from a convex domain, for the marginal field

For an open bounded convex domain `V`, a shift `lam > 0` and a continuous function `w` on `ℝ^d`
which vanishes off `V` and represents the zero-trace weak solution of `lam w - ∇·(a∇w) = 1` in `V`
(the part resolvent of the constant one), the barrier datum of the observable `1_V` exists, and
the crux equality of `FieldExitTime.lean` identifies the killed resolvent of one on the
compactified domain with `w`.  The Laplace transform of the exit time of the one-point process is
then `1 - lam w` by the Chernoff identity of MarkovProcess.

* `ballExit_barrierData`: the barrier datum of the indicator of `V`;
* `ballExit_killedResolvent_one_eq`: the killed resolvent of one at a point of `V` is `w`;
* `ballExit_lintegral_exp_neg_exitTime_onePoint`: the Laplace transform of the one-point exit time
  is `1 - lam w`;
* `ballExit_exists_h10_solution`: `w` is the zero-trace `H¹₀(V)` weak solution of the equation.

The continuity of the zero extension of the part solution is the only boundary input.  On axis
cubes it comes from the boundary reflection of the regularity layer; on a ball it is the boundary
continuity of Section 7 and is carried as an explicit hypothesis here.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization MeasureTheory Set
open SuperdiffusionCLT.Section8.DivergenceForm
open SuperdiffusionCLT.Section8.Common.Support
open MarkovProcess MarkovProcess.Semigroup MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal ZeroAtInfty

noncomputable section

variable {d : ℕ}

/-- The observable `1_V`, the constant datum of the exit-time problem restricted to `V`. -/
def ballExit_datum (V : Set (Vec d)) : Vec d → ℝ :=
  V.indicator fun _ => 1

theorem ballExit_measurable_datum {V : Set (Vec d)} (hV : IsOpen V) :
    Measurable (ballExit_datum V) :=
  measurable_const.indicator hV.measurableSet

theorem ballExit_datum_nonneg (V : Set (Vec d)) (x : Vec d) : 0 ≤ ballExit_datum V x := by
  unfold ballExit_datum
  by_cases hx : x ∈ V
  · rw [Set.indicator_of_mem hx]
    exact zero_le_one
  · rw [Set.indicator_of_notMem hx]

theorem ballExit_abs_datum_le (V : Set (Vec d)) (x : Vec d) : |ballExit_datum V x| ≤ 1 := by
  rw [abs_of_nonneg (ballExit_datum_nonneg V x)]
  unfold ballExit_datum
  by_cases hx : x ∈ V
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx]
    exact zero_le_one

theorem ballExit_datum_of_mem {V : Set (Vec d)} {x : Vec d} (hx : x ∈ V) :
    ballExit_datum V x = 1 :=
  Set.indicator_of_mem hx _

/-- The `L²` class of the constant one on the part domain. -/
def ballExit_datumL2 {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V) : ScalarL2 V :=
  partDatumL2 hV (ballExit_measurable_datum hV.isOpen) (fun x => ballExit_abs_datum_le V x)

theorem ballExit_datumL2_ae {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V) :
    ∀ᵐ y ∂volumeMeasureOn V, ballExit_datumL2 hV y = 1 := by
  filter_upwards [boundedMeasurableToScalarL2_coeFn hV
      ((ballExit_measurable_datum hV.isOpen).comp measurable_subtype_coe)
      (fun y => ballExit_abs_datum_le V y),
    self_mem_ae_restrict hV.isOpen.measurableSet] with y hy hyV
  rw [ballExit_datumL2, partDatumL2, hy, domainExtension_of_mem hyV]
  exact ballExit_datum_of_mem hyV

variable [NeZero d] {nu : ℝ} {k : Vec d → Mat d}

/-- **The barrier datum of the indicator of a convex domain.**  A continuous function `w` which
vanishes off `V` and represents the shifted zero-trace solution of the constant one supplies the
caller obligations of the whole-space barrier. -/
def ballExit_barrierData (A : WholeSpaceAnalyticData d) {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) (lam : PositiveShift) (w : Vec d → ℝ)
    (hw : Continuous w) (hoff : ∀ x, x ∉ V → w x = 0)
    (hrep : w =ᵐ[volumeMeasureOn V] ZeroTraceSobolev.toL2
      (alphaShiftedSolution A.a (show (0 : ℝ) < ((lam : PositiveShift) : ℝ) from lam.property)
        A.hnu (partEllipticity A hV) (ballExit_datumL2 hV))) : WholeSpaceBarrierData A where
  V := V
  hV := hV
  lam := lam
  f := ballExit_datum V
  hf := ballExit_measurable_datum hV.isOpen
  hf0 := ballExit_datum_nonneg V
  D := 1
  hfD := ballExit_abs_datum_le V
  hfV := Filter.EventuallyEq.of_eq (by
    unfold ballExit_datum
    rw [Set.indicator_indicator, Set.inter_self])
  utilde := w
  hutildeCont := hw
  hutildeOff := hoff
  hutildeRep := hrep

variable (D : FieldInputData d nu k)

theorem ballExit_nonneg_on {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) (lam : PositiveShift) {w : Vec d → ℝ}
    (hw : Continuous w)
    (hrep : w =ᵐ[volumeMeasureOn V] ZeroTraceSobolev.toL2
      (alphaShiftedSolution D.analyticData.a
        (show (0 : ℝ) < ((lam : PositiveShift) : ℝ) from lam.property)
        D.analyticData.hnu (partEllipticity D.analyticData hV) (ballExit_datumL2 hV)))
    {x : Vec d} (hx : x ∈ V) : 0 ≤ w x := by
  have hone : ∀ᵐ y ∂volumeMeasureOn V, 0 ≤ ballExit_datumL2 hV y :=
    ae_nonneg_boundedMeasurableToScalarL2 hV (ballExit_measurable_datum hV.isOpen)
      (ballExit_datum_nonneg V) (ballExit_abs_datum_le V)
  have hres := alphaShiftedResolvent_nonneg_ae D.analyticData.a hV
    (show (0 : ℝ) < ((lam : PositiveShift) : ℝ) from lam.property) D.analyticData.hnu
    (partEllipticity D.analyticData hV) (ballExit_datumL2 hV) hone
  refine le_of_ae_le_of_continuousOn hV.isOpen continuousOn_const hw.continuousOn ?_ x hx
  filter_upwards [hrep, hres] with y h1 h2
  rw [h1]
  exact h2

theorem ballExit_killedResolvent_one_eq {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) (lam : PositiveShift) {w : Vec d → ℝ}
    (hw : Continuous w) (hoff : ∀ x, x ∉ V → w x = 0)
    (hrep : w =ᵐ[volumeMeasureOn V] ZeroTraceSobolev.toL2
      (alphaShiftedSolution D.analyticData.a
        (show (0 : ℝ) < ((lam : PositiveShift) : ℝ) from lam.property)
        D.analyticData.hnu (partEllipticity D.analyticData hV) (ballExit_datumL2 hV)))
    {x : Vec d} (hx : x ∈ V) :
    let hreg := D.logGrowthBounds.processInput.toOnePointRegular
    let := hreg.metricSpace
    let := hreg.completeSpace
    IsConservative.killedResolvent D.logGrowthBounds.resolvent.onePointKernelSemigroup
        D.logGrowthBounds.resolvent.isConservative_onePointKernelSemigroup
        (((↑) : Vec d → OnePoint (Vec d)) '' V)
        (OnePoint.isOpen_image_coe.mpr hV.isOpen) (lam : ℝ) (fun _ => 1) (x : OnePoint (Vec d)) =
      ENNReal.ofReal (w x) := by
  intro hreg hm hc
  have h := fieldExit_killedResolvent_eq_partResolvent D
    (ballExit_barrierData D.analyticData hV lam w hw hoff hrep) hx
  refine Eq.trans ?_ h
  refine killedResolvent_congr_of_eqOn _ _ _ _ _ ?_ _
  rintro _ ⟨y, hy, rfl⟩
  simp only [PositiveC0ContractiveResolvent.onePointLiveExtension_coe]
  exact (by rw [ballExit_barrierData]; simp only [ballExit_datum_of_mem hy, ENNReal.ofReal_one])

theorem ballExit_lintegral_exp_neg_exitTime_onePoint {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) (lam : PositiveShift) {w : Vec d → ℝ}
    (hw : Continuous w) (hoff : ∀ x, x ∉ V → w x = 0)
    (hrep : w =ᵐ[volumeMeasureOn V] ZeroTraceSobolev.toL2
      (alphaShiftedSolution D.analyticData.a
        (show (0 : ℝ) < ((lam : PositiveShift) : ℝ) from lam.property)
        D.analyticData.hnu (partEllipticity D.analyticData hV) (ballExit_datumL2 hV)))
    {x : Vec d} (hx : x ∈ V) :
    let hreg := D.logGrowthBounds.processInput.toOnePointRegular
    let := hreg.metricSpace
    let := hreg.completeSpace
    ∫⁻ path, ({path | ContinuousPath.exitTime (((↑) : Vec d → OnePoint (Vec d)) '' V) path < ⊤} :
          Set _).indicator
        (fun path => ENNReal.ofReal (Real.exp (-(lam : ℝ) *
          (ContinuousPath.exitTime (((↑) : Vec d → OnePoint (Vec d)) '' V) path).toReal))) path
        ∂(IsConservative.continuousProcess
          D.logGrowthBounds.resolvent.onePointKernelSemigroup
          D.logGrowthBounds.resolvent.isConservative_onePointKernelSemigroup
          (x : OnePoint (Vec d))) =
      ENNReal.ofReal (1 - (lam : ℝ) * w x) := by
  intro hreg hm hc
  refine (IsConservative.lintegral_exp_neg_exitTime
    D.logGrowthBounds.resolvent.onePointKernelSemigroup
    D.logGrowthBounds.resolvent.isConservative_onePointKernelSemigroup _
    (OnePoint.isOpen_image_coe.mpr hV.isOpen) (lam : ℝ) lam.property _).trans ?_
  rw [ballExit_killedResolvent_one_eq D hV lam hw hoff hrep hx,
    ← ENNReal.ofReal_mul lam.property.le, ENNReal.ofReal_sub _
    (mul_nonneg lam.property.le (ballExit_nonneg_on D hV lam hw hrep hx)),
    ENNReal.ofReal_one]

theorem ballExit_exists_h10_solution (A : WholeSpaceAnalyticData d) {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) (lam : PositiveShift) {w : Vec d → ℝ}
    (hrep : w =ᵐ[volumeMeasureOn V] ZeroTraceSobolev.toL2
      (alphaShiftedSolution A.a
        (show (0 : ℝ) < ((lam : PositiveShift) : ℝ) from lam.property)
        A.hnu (partEllipticity A hV) (ballExit_datumL2 hV))) :
    ∃ u : H10Function V, (∀ᵐ y ∂volumeMeasureOn V, w y = u.toH1Function.toFun y) ∧
      IsScalarForcedWeakSolution A.a V
        (fun y => 1 - (lam : ℝ) * u.toH1Function.toFun y) u.toH1Function := by
  set z := alphaShiftedSolution A.a
        (show (0 : ℝ) < ((lam : PositiveShift) : ℝ) from lam.property)
        A.hnu (partEllipticity A hV) (ballExit_datumL2 hV) with hz
  obtain ⟨u, hu1, hu2⟩ := ZeroTraceSobolev.exists_h10Function hV z
  have hzu : ZeroTraceSobolev.ofH10Function u = z := by
    ext1
    · rw [ZeroTraceSobolev.toL2_ofH10Function, hu1]
    · rw [ZeroTraceSobolev.gradient_ofH10Function, hu2]
  have hweak := alphaShiftedSolution_isAlphaShiftedWeakSolution A.a
    (show (0 : ℝ) < ((lam : PositiveShift) : ℝ) from lam.property)
    A.hnu (partEllipticity A hV) (ballExit_datumL2 hV)
  rw [← hz, ← hzu] at hweak
  refine ⟨u, ?_, ?_⟩
  · filter_upwards [hrep, u.toH1Function.coeFn_toScalarL2] with y h1 h2
    rw [h1, ← h2, hu1]
  · refine (isScalarForcedWeakSolution_sub_alpha_mul_of_isAlphaShiftedWeakSolution u
      hweak).congr_datum ?_
    filter_upwards [ballExit_datumL2_ae hV] with y hy
    rw [hy]

end

end SuperdiffusionCLT.Section8
