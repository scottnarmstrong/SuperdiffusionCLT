/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.ExitMeanValue
public import Homogenization.Geometry.CubeMeasure

/-!
# The Dirichlet resolvent of a bounded part domain, read on a translated triadic cube

The exit decomposition of a resolvent datum needs the Dirichlet resolvent of the domain the
process is killed on.  On the centred exhaustion cubes that object is
`analyticCubeResolvent`, whose index is the exhaustion step; the localized Dirichlet problems
of the field are posed instead on `cubeSetAt y n`, the open cube of side `3 ^ n` centred at `y`,
which is not an exhaustion cube.

This file supplies the Dirichlet resolvent of an arbitrary bounded part domain.

* `partC0Resolvent` is the continuous representative of the Dirichlet resolvent of a bounded
  measurable datum on a bounded convex open set, extended by zero.  It is the domain-generic
  form of `analyticCubeResolvent`: the underlying analytic object,
  `continuousCoeffBoundedResolvent`, already takes an arbitrary such set, and the ellipticity
  certificate is the one `partEllipticity` supplies for it.
* `partC0Resolvent_ae` records that it agrees almost everywhere on the domain with the shifted
  part solution, and `continuousOn_partC0Resolvent` that it is continuous there.
* `partC0Resolvent_nonneg` records that it is nonnegative on a nonnegative datum.

Everything here is analytic: no process, and no hypothesis about one, appears.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.DivergenceForm

open Filter Homogenization MeasureTheory Set Topology
open SuperdiffusionCLT.Section8.Common.Support
open MarkovProcess MarkovProcess.Semigroup
open MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

variable {d : ℕ}

/-! ## The datum of a translated triadic cube -/

variable [NeZero d]

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)

/-! ## The Dirichlet resolvent of a bounded part domain -/

/-- **The Dirichlet resolvent of a bounded part domain.**  The continuous representative
supplied by freezing the skew part, extended by zero off the domain.  This is
`analyticCubeResolvent` with the exhaustion index replaced by the domain itself. -/
def partC0Resolvent {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    (mu : PositiveShift) (f : Vec d → ℝ) (hf : Measurable f) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) : Vec d → ℝ :=
  V.indicator (continuousCoeffBoundedResolvent A.a hV A.hnu A.hnu
    (partEllipticity A hV) A.hsymm (A.hskewContinuous.mono (Set.subset_univ V)) A.hd mu
    (hf.comp measurable_subtype_coe) (fun z => hfD z))

theorem partC0Resolvent_of_mem {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    (mu : PositiveShift) (f : Vec d → ℝ) (hf : Measurable f) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) {x : Vec d} (hx : x ∈ V) :
    A.partC0Resolvent hV mu f hf hfD x =
      continuousCoeffBoundedResolvent A.a hV A.hnu A.hnu (partEllipticity A hV) A.hsymm
        (A.hskewContinuous.mono (Set.subset_univ V)) A.hd mu
        (hf.comp measurable_subtype_coe) (fun z => hfD z) x :=
  Set.indicator_of_mem hx _

theorem partC0Resolvent_of_notMem {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    (mu : PositiveShift) (f : Vec d → ℝ) (hf : Measurable f) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) {x : Vec d} (hx : x ∉ V) :
    A.partC0Resolvent hV mu f hf hfD x = 0 :=
  Set.indicator_of_notMem hx _

theorem continuousOn_partC0Resolvent {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    (mu : PositiveShift) (f : Vec d → ℝ) (hf : Measurable f) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) :
    ContinuousOn (A.partC0Resolvent hV mu f hf hfD) V := by
  refine ContinuousOn.congr (continuousOn_continuousCoeffBoundedResolvent A.a hV A.hnu
    A.hnu (partEllipticity A hV) A.hsymm (A.hskewContinuous.mono (Set.subset_univ V)) A.hd
    mu (hf.comp measurable_subtype_coe) (fun z => hfD z)) fun x hx => ?_
  exact A.partC0Resolvent_of_mem hV mu f hf hfD hx

theorem partC0Resolvent_ae {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    (mu : PositiveShift) (f : Vec d → ℝ) (hf : Measurable f) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) :
    A.partC0Resolvent hV mu f hf hfD =ᵐ[volumeMeasureOn V]
      alphaShiftedResolvent A.a mu.property A.hnu (partEllipticity A hV)
        (partDatumL2 hV hf hfD) := by
  filter_upwards [continuousCoeffBoundedResolvent_ae A.a hV A.hnu A.hnu
      (partEllipticity A hV) A.hsymm (A.hskewContinuous.mono (Set.subset_univ V)) A.hd mu
      (hf.comp measurable_subtype_coe) (fun z => hfD z),
    self_mem_ae_restrict hV.isOpen.measurableSet] with x hx hxV
  rw [A.partC0Resolvent_of_mem hV mu f hf hfD hxV, hx]
  rfl

/-- **The Dirichlet resolvent of a part domain is nonnegative on a nonnegative datum.** -/
theorem partC0Resolvent_nonneg {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    (mu : PositiveShift) (f : Vec d → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    {D : ℝ} (hfD : ∀ x, |f x| ≤ D) (x : Vec d) :
    0 ≤ A.partC0Resolvent hV mu f hf hfD x := by
  by_cases hx : x ∈ V
  · refine le_of_ae_le_of_continuousOn hV.isOpen continuousOn_const
      (A.continuousOn_partC0Resolvent hV mu f hf hfD) ?_ x hx
    filter_upwards [A.partC0Resolvent_ae hV mu f hf hfD,
      alphaShiftedResolvent_nonneg_ae A.a hV mu.property A.hnu (partEllipticity A hV)
        (partDatumL2 hV hf hfD)
        (ae_nonneg_boundedMeasurableToScalarL2 hV hf hf0 hfD)] with z h1 h2
    rw [h1]
    exact h2
  · rw [A.partC0Resolvent_of_notMem hV mu f hf hfD hx]

end WholeSpaceAnalyticData

end

end SuperdiffusionCLT.Section8.DivergenceForm
