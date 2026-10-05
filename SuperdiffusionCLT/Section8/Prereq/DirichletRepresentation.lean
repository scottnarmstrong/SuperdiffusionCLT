/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.BallBoundaryD
public import SuperdiffusionCLT.Section8.Prereq.BallExitTimeC

/-!
# Dirichlet problems on a ball and the process of the marginal field: the shifted resolvent

For the process of `∇·(ν Id + k)∇` started in a Euclidean ball `B`, the discounted occupation
`E^x ∫₀^{T_B} e^{-lam s} f(X_s) ds` of a bounded nonnegative measurable observable `f` is the
continuous representative of the part resolvent of `f`, for every continuous-path law of the kernel
semigroup.  The part resolvent is continuous on the whole space and vanishes off the ball: it is
dominated by a multiple of the part resolvent of one, which vanishes on the boundary.

* `dirRep_one_continuous`: the part resolvent of the indicator of the ball is continuous;
* `dirRep_resolvent_continuous`: the same for a bounded nonnegative measurable datum;
* `dirRep_barrierData`: the barrier datum of such an observable;
* `dirRep_lintegral_resolvent`: the discounted occupation on paths of `ℝ^d`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization MeasureTheory Set
open SuperdiffusionCLT.Section8.DivergenceForm
open MarkovProcess MarkovProcess.Semigroup MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

variable {d : ℕ} [NeZero d] {nu : ℝ} {k : Vec d → Mat d} (D : FieldInputData d nu k)

/-- The part resolvent of the indicator of the ball is continuous on the whole space. -/
theorem dirRep_one_continuous (x₀ : Vec d) {r : ℝ} (hr : 0 < r) (mu : PositiveShift) :
    let hV := SuperdiffusionCLT.Section8.Common.Regularity.Ported.isOpenBoundedConvexDomain_euclideanBall
      x₀ hr
    Continuous (D.analyticData.partC0Resolvent hV mu (ballExit_datum (euclideanBall x₀ r))
      (ballExit_measurable_datum hV.isOpen) (ballExit_abs_datum_le (euclideanBall x₀ r))) := by
  intro hV
  set A := D.analyticData with hA
  have hf := ballExit_measurable_datum (d := d) (V := euclideanBall x₀ r) hV.isOpen
  have hfD := ballExit_abs_datum_le (d := d) (euclideanBall x₀ r)
  set w₀ := A.partC0Resolvent hV mu _ hf hfD with hw₀
  have hrep : w₀ =ᵐ[volumeMeasureOn (euclideanBall x₀ r)] ZeroTraceSobolev.toL2
      (alphaShiftedSolution A.a (show (0 : ℝ) < ((mu : MarkovProcess.Semigroup.PositiveShift) : ℝ) from mu.property)
        A.hnu (partEllipticity A hV) (ballExit_datumL2 hV)) := by
    filter_upwards [A.partC0Resolvent_ae hV mu _ hf hfD] with y hy
    exact hy
  obtain ⟨u, hwu, hsol⟩ := ballExit_exists_h10_solution A hV mu hrep
  have hcontOn : ContinuousOn w₀ (euclideanBall x₀ r) := A.continuousOn_partC0Resolvent hV mu _ hf hfD
  have hoff : ∀ y, y ∉ euclideanBall x₀ r → w₀ y = 0 := fun y hy =>
    A.partC0Resolvent_of_notMem hV mu _ hf hfD hy
  have hnn : ∀ y ∈ euclideanBall x₀ r, 0 ≤ w₀ y := fun y _ =>
    A.partC0Resolvent_nonneg hV mu _ hf (ballExit_datum_nonneg _) hfD y
  refine ballBdry_continuous_of_barriers hV.isOpen hcontOn hoff hnn fun p hp => ?_
  obtain ⟨ψ, hψc, hψp, hψ⟩ := ballBdry_upper D.nu_pos (fun i j => D.contDiff_entry i j)
    (ballBdry_skew_entry D) mu.property hr u hsol (ballBdry_frontier_ball hp)
  refine ⟨ψ, hψc, hψp, fun x hx => ?_⟩
  refine le_of_ae_le_of_continuousOn hV.isOpen hcontOn hψc.continuousOn ?_ x hx
  filter_upwards [hwu, hψ] with y h1 h2
  rw [h1]
  exact h2


/-- **The part resolvent of a bounded nonnegative measurable datum on a ball is continuous on the
whole space.**  It is dominated by a multiple of the part resolvent of one, which vanishes on the
boundary. -/
theorem dirRep_resolvent_continuous (x₀ : Vec d) {r : ℝ} (hr : 0 < r) (mu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) (hf0 : ∀ y, 0 ≤ f y) {M : ℝ}
    (hfM : ∀ y, |f y| ≤ M) :
    let hV := SuperdiffusionCLT.Section8.Common.Regularity.Ported.isOpenBoundedConvexDomain_euclideanBall
      x₀ hr
    Continuous (D.analyticData.partC0Resolvent hV mu f hf hfM) := by
  intro hV
  set A := D.analyticData with hA
  set B := euclideanBall x₀ r with hB
  have h1 := ballExit_measurable_datum (d := d) (V := B) hV.isOpen
  have h1D := ballExit_abs_datum_le (d := d) B
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hfM 0)
  set w₁ := A.partC0Resolvent hV mu _ h1 h1D with hw₁
  have hw₁c : Continuous w₁ := dirRep_one_continuous D x₀ hr mu
  have hoff1 : ∀ y, y ∉ B → w₁ y = 0 := fun y hy => A.partC0Resolvent_of_notMem hV mu _ h1 h1D hy
  have hcM : ∀ y, |M * ballExit_datum B y| ≤ |M| * 1 := fun y => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (h1D y) (abs_nonneg M)
  have hsm : Measurable fun y => M * ballExit_datum B y := h1.const_smul M
  refine ballBdry_continuous_of_barriers hV.isOpen
    (A.continuousOn_partC0Resolvent hV mu f hf hfM)
    (fun y hy => A.partC0Resolvent_of_notMem hV mu f hf hfM hy)
    (fun y _ => A.partC0Resolvent_nonneg hV mu f hf hf0 hfM y) fun p hp => ?_
  have hpB : p ∉ B := by
    have := hp
    rw [frontier, hV.isOpen.interior_eq] at this
    exact this.2
  refine ⟨fun y => M * w₁ y, continuous_const.mul hw₁c, by show M * w₁ p = 0; rw [hoff1 p hpB, mul_zero], fun x hx => ?_⟩
  have hf' : Measurable (B.indicator f) := hf.indicator hV.isOpen.measurableSet
  have hf'M : ∀ y, |B.indicator f y| ≤ M := fun y => by
    by_cases hy : y ∈ B
    · rw [Set.indicator_of_mem hy]; exact hfM y
    · rw [Set.indicator_of_notMem hy, abs_zero]; exact hM0
  have hle : A.partC0Resolvent hV mu f hf hfM x ≤
      A.partC0Resolvent hV mu (fun y => M * ballExit_datum B y) hsm hcM x := by
    refine (A.partC0Resolvent_eq_of_eqOn hV mu hf hf' hfM hf'M
      (fun y hy => (Set.indicator_of_mem hy f).symm) x).le.trans ?_
    refine A.partC0Resolvent_mono hV mu hf' hsm hf'M hcM (fun y => ?_) x
    by_cases hy : y ∈ B
    · rw [Set.indicator_of_mem hy, ballExit_datum_of_mem hy, mul_one]
      exact (le_abs_self _).trans (hfM y)
    · rw [Set.indicator_of_notMem hy]
      unfold ballExit_datum
      rw [Set.indicator_of_notMem hy, mul_zero]
  have := A.partC0Resolvent_smul hV mu M h1 h1D hcM x
  exact hle.trans this.le


open SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.LiveRestriction in
/-- The barrier datum of a bounded nonnegative measurable datum on a ball (the datum is
replaced by its restriction to the ball). -/
def dirRep_barrierData (x₀ : Vec d) {r : ℝ} (hr : 0 < r) (mu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) (hf0 : ∀ y, 0 ≤ f y) {M : ℝ}
    (hfM : ∀ y, |f y| ≤ M) : WholeSpaceBarrierData D.analyticData :=
  let hV := SuperdiffusionCLT.Section8.Common.Regularity.Ported.isOpenBoundedConvexDomain_euclideanBall
      x₀ hr
  { V := euclideanBall x₀ r
    hV := hV
    lam := mu
    f := (euclideanBall x₀ r).indicator f
    hf := hf.indicator hV.isOpen.measurableSet
    hf0 := fun y => Set.indicator_nonneg (fun z _ => hf0 z) y
    D := M
    hfD := fun y => by
      by_cases hy : y ∈ euclideanBall x₀ r
      · rw [Set.indicator_of_mem hy]; exact hfM y
      · rw [Set.indicator_of_notMem hy, abs_zero]; exact (abs_nonneg _).trans (hfM 0)
    hfV := Filter.EventuallyEq.of_eq (by rw [Set.indicator_indicator, Set.inter_self])
    utilde := D.analyticData.partC0Resolvent hV mu f hf hfM
    hutildeCont := dirRep_resolvent_continuous D x₀ hr mu hf hf0 hfM
    hutildeOff := fun y hy => D.analyticData.partC0Resolvent_of_notMem hV mu f hf hfM hy
    hutildeRep := by
      have hf' : Measurable ((euclideanBall x₀ r).indicator f) :=
        hf.indicator hV.isOpen.measurableSet
      have hf'M : ∀ y, |(euclideanBall x₀ r).indicator f y| ≤ M := fun y => by
        by_cases hy : y ∈ euclideanBall x₀ r
        · rw [Set.indicator_of_mem hy]; exact hfM y
        · rw [Set.indicator_of_notMem hy, abs_zero]; exact (abs_nonneg _).trans (hfM 0)
      filter_upwards [D.analyticData.partC0Resolvent_ae hV mu _ hf' hf'M] with y hy
      rw [D.analyticData.partC0Resolvent_eq_of_eqOn hV mu hf hf' hfM hf'M
        (fun z hz => (Set.indicator_of_mem hz f).symm) y]
      exact hy }


open SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.LiveRestriction in
/-- **The killed resolvent of the compactified process, on paths of `ℝ^d`.**  For every
continuous-path law `Q` of the kernel semigroup and every real shift, the killed resolvent on the
ball of the live extension of `f` restricted to the ball is the expected discounted occupation of
the ball before the exit time. -/
theorem dirRep_transfer (x₀ : Vec d) {r : ℝ} (hr : 0 < r) (lam : ℝ)
    {f : Vec d → ℝ} (hf : Measurable f)
    {Q : Vec d → Measure (ContinuousPath (Vec d))}
    (hQ : IsContinuousPathLaw D.logGrowthBounds.resolvent.kernelSemigroup Q) (x : Vec d) :
    let hreg := D.logGrowthBounds.processInput.toOnePointRegular
    let := hreg.metricSpace
    let := hreg.completeSpace
    IsConservative.killedResolvent D.logGrowthBounds.resolvent.onePointKernelSemigroup
        D.logGrowthBounds.resolvent.isConservative_onePointKernelSemigroup
        (((↑) : Vec d → OnePoint (Vec d)) '' euclideanBall x₀ r)
        (OnePoint.isOpen_image_coe.mpr
          (SuperdiffusionCLT.Section8.Common.Regularity.Ported.isOpenBoundedConvexDomain_euclideanBall
            x₀ hr).isOpen) lam
        (PositiveC0ContractiveResolvent.onePointLiveExtension
          (fun y => ENNReal.ofReal ((euclideanBall x₀ r).indicator f y))) (x : OnePoint (Vec d)) =
      ∫⁻ path, (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t)) *
        {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) <
            ContinuousPath.exitTime (euclideanBall x₀ r) path}.indicator
          (fun t => ENNReal.ofReal (f (path (Real.toNNReal t)))) t) ∂(Q x) := by
  intro hreg hm hc
  set B := euclideanBall x₀ r with hB
  have hV := SuperdiffusionCLT.Section8.Common.Regularity.Ported.isOpenBoundedConvexDomain_euclideanBall
    x₀ hr
  have hmap := ballExit_map_pathPostcomp_eq D hQ x
  have hemb : MeasurableEmbedding (pathPostcomp (liveEmbedding (Vec d))) :=
    (continuous_pathPostcomp (liveEmbedding (Vec d))).measurableEmbedding
      (procConstr_injective_pathPostcomp OnePoint.isOpenEmbedding_coe.isEmbedding)
  have hmeasF : Measurable (PositiveC0ContractiveResolvent.onePointLiveExtension
      (fun y => ENNReal.ofReal (B.indicator f y))) :=
    PositiveC0ContractiveResolvent.measurable_onePointLiveExtension
      (ENNReal.measurable_ofReal.comp (hf.indicator hV.isOpen.measurableSet))
  dsimp only at hmap
  rw [IsConservative.killedResolvent_eq_lintegral
    D.logGrowthBounds.resolvent.onePointKernelSemigroup
    D.logGrowthBounds.resolvent.isConservative_onePointKernelSemigroup
    (((↑) : Vec d → OnePoint (Vec d)) '' B)
    (OnePoint.isOpen_image_coe.mpr hV.isOpen) lam hmeasF (x : OnePoint (Vec d))]
  have hpt : ∀ path : ContinuousPath (Vec d),
      (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t)) *
        {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) <
            ContinuousPath.exitTime B path}.indicator
          (fun t => ENNReal.ofReal (f (path (Real.toNNReal t)))) t) =
      ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t)) *
        {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) <
            ContinuousPath.exitTime (((↑) : Vec d → OnePoint (Vec d)) '' B)
              (pathPostcomp (liveEmbedding (Vec d)) path)}.indicator
          (fun t => PositiveC0ContractiveResolvent.onePointLiveExtension
            (fun y => ENNReal.ofReal (B.indicator f y))
            ((pathPostcomp (liveEmbedding (Vec d)) path) (Real.toNNReal t))) t := by
    intro path
    have hexit : ContinuousPath.exitTime (((↑) : Vec d → OnePoint (Vec d)) '' B)
        (pathPostcomp (liveEmbedding (Vec d)) path) = ContinuousPath.exitTime B path :=
      exitTime_image_pathPostcomp (liveEmbedding (Vec d)) injective_liveCoe B path
    rw [hexit]
    refine lintegral_congr fun t => ?_
    by_cases ht : ((Real.toNNReal t : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime B path
    · have hmem : path (Real.toNNReal t) ∈ B := ContinuousPath.mem_of_lt_exitTime B path _ ht
      rw [Set.indicator_of_mem (show t ∈ {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) <
            ContinuousPath.exitTime B path} from ht),
        Set.indicator_of_mem (show t ∈ {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) <
            ContinuousPath.exitTime B path} from ht)]
      show _ * _ = _ * PositiveC0ContractiveResolvent.onePointLiveExtension _
        ((path (Real.toNNReal t) : Vec d) : OnePoint (Vec d))
      rw [PositiveC0ContractiveResolvent.onePointLiveExtension_coe]
      show _ = _ * ENNReal.ofReal (B.indicator f _)
      rw [Set.indicator_of_mem hmem]
    · rw [Set.indicator_of_notMem (show t ∉ {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) <
            ContinuousPath.exitTime B path} from ht),
        Set.indicator_of_notMem (show t ∉ {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) <
            ContinuousPath.exitTime B path} from ht)]
  refine Eq.trans ?_ (lintegral_congr hpt).symm
  rw [← hemb.lintegral_map (fun ω' : ContinuousPath (OnePoint (Vec d)) =>
    ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t)) *
        {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) <
            ContinuousPath.exitTime (((↑) : Vec d → OnePoint (Vec d)) '' B) ω'}.indicator
          (fun t => PositiveC0ContractiveResolvent.onePointLiveExtension
            (fun y => ENNReal.ofReal (B.indicator f y)) (ω' (Real.toNNReal t))) t)]
  exact (congrArg (fun m : Measure (ContinuousPath (OnePoint (Vec d))) => ∫⁻ ω', (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t)) *
        {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) <
            ContinuousPath.exitTime (((↑) : Vec d → OnePoint (Vec d)) '' B) ω'}.indicator
          (fun t => PositiveC0ContractiveResolvent.onePointLiveExtension
            (fun y => ENNReal.ofReal (B.indicator f y)) (ω' (Real.toNNReal t))) t) ∂m) hmap).symm

/-- **The killed resolvent of a bounded nonnegative datum is the part resolvent, on paths of
`ℝ^d`.**  For every continuous-path law `Q` of the kernel semigroup,
`E^x ∫₀^{T_B} e^{-lam s} f(X_s) ds = R^B_lam f (x)` for `x` in the ball `B`. -/
theorem dirRep_lintegral_resolvent (x₀ : Vec d) {r : ℝ} (hr : 0 < r) (mu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) (hf0 : ∀ y, 0 ≤ f y) {M : ℝ}
    (hfM : ∀ y, |f y| ≤ M)
    {Q : Vec d → Measure (ContinuousPath (Vec d))}
    (hQ : IsContinuousPathLaw D.logGrowthBounds.resolvent.kernelSemigroup Q)
    {x : Vec d} (hx : x ∈ euclideanBall x₀ r) :
    ∫⁻ path, (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(mu : ℝ) * t)) *
        {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) <
            ContinuousPath.exitTime (euclideanBall x₀ r) path}.indicator
          (fun t => ENNReal.ofReal (f (path (Real.toNNReal t)))) t) ∂(Q x) =
      ENNReal.ofReal (D.analyticData.partC0Resolvent
        (SuperdiffusionCLT.Section8.Common.Regularity.Ported.isOpenBoundedConvexDomain_euclideanBall
          x₀ hr) mu f hf hfM x) := by
  have hcrux := fieldExit_killedResolvent_eq_partResolvent D
    (dirRep_barrierData D x₀ hr mu hf hf0 hfM) hx
  have htr := dirRep_transfer D x₀ hr (mu : ℝ) hf hQ x
  dsimp only at hcrux htr
  exact htr.symm.trans hcrux

end
end SuperdiffusionCLT.Section8
