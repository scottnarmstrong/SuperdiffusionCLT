/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Probability.StationaryRealizationPoincare
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-!
# The honest-slice step: the deterministic cube-side difference-quotient limit

This module works on the analytic core of the statement `honestSlice` recorded in
`SuperdiffusionCLT/Probability/StationaryRealizationPoincare.lean`: the passage from an
`L²(Ω)` horizontal-gradient hypothesis to the per-sample weak equation

`∫ x in U, φ (x +ᵥ ω) · ∂ᵢψ x = − ∫ x in U, (F (x +ᵥ ω)) i · ψ x`

on the cube `U = openCubeSet (originCube d M)`, for one coordinate `i` and one compactly
supported smooth test function `ψ`.

The sample-wise argument splits into two halves.  The `L²(Ω)` half produces, along a sequence
`hₖ → 0`, convergence to zero of the sample difference-quotient error for almost every `ω`.  The
deterministic half — proved here — converts that convergence, for a *single* sample, into the weak
equation by moving the difference quotient onto the test function and passing to the limit under
the integral sign.  The deterministic half is what
`Homogenization.integral_euclideanForwardDifferenceQuotient_mul_eq_neg_of_integrable`
(`Probability/StationaryRealizationPoincare.lean`) was built for: it needs integrability of the
three products the summation-by-parts expansion produces, not `ContDiff` of the differentiated
factor.
-/

@[expose] public section

open MeasureTheory Homogenization
open scoped ENNReal Topology

namespace SuperdiffusionCLT.Probability.Stationary

noncomputable section

variable {d : ℕ}

/-- **The coordinate backward difference quotient converges to the coordinate derivative.**  This
is the pointwise limit that turns the test-function side of the summation-by-parts identity into
the weak derivative of the test function. -/
theorem tendsto_euclideanBackwardDifferenceQuotient_coordDeriv
    {ψ : Vec d → ℝ} (hψ : Differentiable ℝ ψ) (i : Fin d) (x : Vec d) :
    Filter.Tendsto
      (fun h : ℝ => Homogenization.euclideanBackwardDifferenceQuotient h i ψ x)
      (𝓝[≠] 0) (𝓝 (Homogenization.euclideanCoordDeriv i ψ x)) := by
  have hslope := hasLineDerivAt_iff_tendsto_slope_zero.mp
    ((hψ x).hasFDerivAt.hasLineDerivAt (-(Homogenization.basisVec i)))
  rw [map_neg] at hslope
  have hneg : Filter.Tendsto
      (fun h : ℝ => -(Homogenization.euclideanBackwardDifferenceQuotient h i ψ x))
      (𝓝[≠] 0) (𝓝 (-(Homogenization.euclideanCoordDeriv i ψ x))) := by
    refine hslope.congr' (Filter.Eventually.of_forall fun t => ?_)
    simp only
    rw [Homogenization.euclideanBackwardDifferenceQuotient_apply,
      Homogenization.euclideanCoordShift_apply, smul_neg, ← neg_smul, smul_eq_mul,
      div_eq_mul_inv]
    ring
  simpa using hneg.neg

/-- **The test-function side of the summation-by-parts identity converges.**  For an `L²(U)`
field `u`, a smooth compactly supported test function `ψ` whose topological support lies in the
bounded set `U`, and one coordinate `i`, the integral of `u` against the backward coordinate
difference quotient of `ψ` converges to the integral of `u` against the coordinate derivative
`∂ᵢψ`.

The convergence is dominated: `ψ` is smooth, so the difference quotient is at most the supremum
of `|∂ᵢψ|`, and that supremum is finite because `tsupport ψ` is compact and `∂ᵢψ` is supported in
it.  The dominating function is a constant multiple of `|u|`, which is integrable on `U` because
`u ∈ L²(U)` and `U` carries a finite measure. -/
theorem tendsto_setIntegral_mul_backwardDifferenceQuotient {U : Set (Vec d)}
    [IsFiniteMeasure (MeasureTheory.volume.restrict U)]
    (hUbd : Bornology.IsBounded U)
    {u : Vec d → ℝ} (hu : MemLp u 2 (MeasureTheory.volume.restrict U))
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψU : tsupport ψ ⊆ U) (i : Fin d) :
    Filter.Tendsto
      (fun h : ℝ => ∫ x in U, u x * Homogenization.euclideanBackwardDifferenceQuotient h i ψ x)
      (𝓝[≠] 0)
      (𝓝 (∫ x in U, u x * Homogenization.euclideanCoordDeriv i ψ x)) := by
  have hcpt : IsCompact (tsupport ψ) :=
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_tsupport ψ, hUbd.subset hψU⟩
  have hcont : Continuous (Homogenization.euclideanCoordDeriv i ψ) :=
    (Homogenization.contDiff_euclideanCoordDeriv hψ i).continuous
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn hcont.continuousOn
  have hM : ∀ x : Vec d, ‖Homogenization.euclideanCoordDeriv i ψ x‖ ≤ max C 0 := by
    intro x
    by_cases hx : x ∈ tsupport ψ
    · exact le_trans (hC x hx) (le_max_left C 0)
    · have h0 : Homogenization.euclideanCoordDeriv i ψ x = 0 :=
        image_eq_zero_of_notMem_tsupport
          (fun hmem => hx (Homogenization.tsupport_euclideanCoordDeriv_subset_tsupport i ψ hmem))
      rw [h0, norm_zero]
      exact le_max_right C 0
  have hint : Integrable (fun x : Vec d => ‖u x‖ * max C 0)
      (MeasureTheory.volume.restrict U) :=
    ((MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) hu).norm).mul_const (max C 0)
  have hdiff : Differentiable ℝ ψ := hψ.differentiable (by simp)
  refine tendsto_integral_filter_of_dominated_convergence
    (μ := MeasureTheory.volume.restrict U) (l := 𝓝[≠] (0 : ℝ))
    (F := fun h x => u x * Homogenization.euclideanBackwardDifferenceQuotient h i ψ x)
    (f := fun x => u x * Homogenization.euclideanCoordDeriv i ψ x)
    (fun x => ‖u x‖ * max C 0) ?_ ?_ hint ?_
  · filter_upwards with h
    exact hu.aestronglyMeasurable.mul
      ((Homogenization.contDiff_euclideanBackwardDifferenceQuotient hψ h i).continuous
        |>.aestronglyMeasurable)
  · rw [eventually_nhdsWithin_iff]
    filter_upwards with h hh
    filter_upwards with x
    calc ‖u x * Homogenization.euclideanBackwardDifferenceQuotient h i ψ x‖
        = ‖u x‖ * ‖Homogenization.euclideanBackwardDifferenceQuotient h i ψ x‖ :=
          norm_mul _ _
      _ ≤ ‖u x‖ * max C 0 := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          rw [Real.norm_eq_abs]
          have hseg : Continuous fun t : ℝ => Homogenization.euclideanCoordDeriv i ψ
              (segmentBlend x t (Homogenization.euclideanCoordShift (-h) i x)) :=
            hcont.comp (by
              rw [show (fun t : ℝ => segmentBlend x t
                    (Homogenization.euclideanCoordShift (-h) i x)) =
                  fun t : ℝ => Homogenization.euclideanCoordShift (-h) i x +
                    t • (x - Homogenization.euclideanCoordShift (-h) i x) from
                funext fun t =>
                  segmentBlend_eq_add_smul_sub x (Homogenization.euclideanCoordShift (-h) i x) t]
              exact continuous_const.add (continuous_id.smul continuous_const))
          refine le_trans
            (Homogenization.abs_euclideanBackwardDifferenceQuotient_le_integral_abs_coordDeriv_along_segment
              hψ hh i x) ?_
          calc ∫ t in (0 : ℝ)..1, |Homogenization.euclideanCoordDeriv i ψ
                  (segmentBlend x t (Homogenization.euclideanCoordShift (-h) i x))|
              ≤ ∫ t in (0 : ℝ)..1, max C 0 :=
                intervalIntegral.integral_mono_on zero_le_one
                  (hseg.abs.intervalIntegrable 0 1)
                  intervalIntegrable_const (fun t _ => by
                    simpa only [Real.norm_eq_abs] using hM _)
            _ = max C 0 := by simp [intervalIntegral.integral_const]
  · exact Filter.Eventually.of_forall fun x =>
      (tendsto_euclideanBackwardDifferenceQuotient_coordDeriv hdiff i x).const_mul (u x)

/-- **The backward difference quotient of a test function is supported in a thickening of the
support of the test function.**  If the quotient is nonzero at `x`, at least one of `x` and
`x - h eᵢ` lies in `tsupport ψ`; in the second case `x` is within `‖(-h) • eᵢ‖` of the support. -/
theorem support_euclideanBackwardDifferenceQuotient_subset_cthickening {ψ : Vec d → ℝ}
    (h : ℝ) (i : Fin d) :
    Function.support (Homogenization.euclideanBackwardDifferenceQuotient h i ψ) ⊆
      Metric.cthickening ‖(-h) • Homogenization.basisVec i‖ (tsupport ψ) := by
  intro x hx
  rw [Function.mem_support] at hx
  have hsplit : ψ x ≠ 0 ∨ ψ (Homogenization.euclideanCoordShift (-h) i x) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx (by
      rw [Homogenization.euclideanBackwardDifferenceQuotient_apply, hcon.1, hcon.2, sub_self,
        zero_div])
  rcases hsplit with hx1 | hx2
  · exact Metric.self_subset_cthickening (tsupport ψ) (subset_tsupport ψ hx1)
  · have hdist : dist x (Homogenization.euclideanCoordShift (-h) i x)
        ≤ ‖(-h) • Homogenization.basisVec i‖ := by
      rw [Homogenization.euclideanCoordShift_apply, dist_eq_norm,
        show x - (x + (-h) • Homogenization.basisVec i) = -((-h) • Homogenization.basisVec i)
          from by abel]
      exact le_of_eq (norm_neg _)
    exact Metric.mem_cthickening_of_dist_le x (Homogenization.euclideanCoordShift (-h) i x)
      ‖(-h) • Homogenization.basisVec i‖ (tsupport ψ) (subset_tsupport ψ hx2) hdist

/-- The same containment for the topological support, by closing the previous statement. -/
theorem tsupport_euclideanBackwardDifferenceQuotient_subset_cthickening {ψ : Vec d → ℝ}
    (h : ℝ) (i : Fin d) :
    tsupport (Homogenization.euclideanBackwardDifferenceQuotient h i ψ) ⊆
      Metric.cthickening ‖(-h) • Homogenization.basisVec i‖ (tsupport ψ) :=
  closure_minimal (support_euclideanBackwardDifferenceQuotient_subset_cthickening h i)
    Metric.isClosed_cthickening

/-- **The whole-space integral and the integral over `U` of the difference-quotient pairing
agree, once the thickened support of the test function lies in `U`.**  The integrand vanishes
off `U` because the difference quotient of `ψ` is supported in that thickening.  This is what
lets the whole-space summation-by-parts identity be read on the cube. -/
theorem integral_mul_euclideanBackwardDifferenceQuotient_eq_setIntegral {U : Set (Vec d)}
    {u ψ : Vec d → ℝ} (h : ℝ) (i : Fin d)
    (hhU : Metric.cthickening ‖(-h) • Homogenization.basisVec i‖ (tsupport ψ) ⊆ U) :
    ∫ x, u x * Homogenization.euclideanBackwardDifferenceQuotient h i ψ x =
      ∫ x in U, u x * Homogenization.euclideanBackwardDifferenceQuotient h i ψ x := by
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
  intro x hx
  have hzero : Homogenization.euclideanBackwardDifferenceQuotient h i ψ x = 0 :=
    image_eq_zero_of_notMem_tsupport fun hmem =>
      hx (hhU (tsupport_euclideanBackwardDifferenceQuotient_subset_cthickening h i hmem))
  rw [hzero, mul_zero]

/-- **The support of a shifted test function.**  Precomposition with a coordinate shift moves
the topological support by that shift, hence into the same thickening. -/
theorem tsupport_comp_euclideanCoordShift_subset_cthickening {ψ : Vec d → ℝ}
    (h : ℝ) (i : Fin d) :
    tsupport (fun x => ψ (Homogenization.euclideanCoordShift h i x)) ⊆
      Metric.cthickening ‖h • Homogenization.basisVec i‖ (tsupport ψ) := by
  refine closure_minimal ?_ Metric.isClosed_cthickening
  intro x hx
  rw [Function.mem_support] at hx
  have hdist : dist x (Homogenization.euclideanCoordShift h i x)
      ≤ ‖h • Homogenization.basisVec i‖ := by
    rw [Homogenization.euclideanCoordShift_apply, dist_eq_norm,
      show x - (x + h • Homogenization.basisVec i) = -(h • Homogenization.basisVec i) from by
        abel]
    exact le_of_eq (norm_neg _)
  exact Metric.mem_cthickening_of_dist_le x (Homogenization.euclideanCoordShift h i x)
    ‖h • Homogenization.basisVec i‖ (tsupport ψ) (subset_tsupport ψ hx) hdist

end

end SuperdiffusionCLT.Probability.Stationary
