/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Probability.IndependentSums.GammaSigma.Operations
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Gaussian-tail consequences

This file converts the literal strict Gaussian upper-tail convention used in
the shell assumption into the weak-Orlicz relation of the CoarseGraining library
and into an `L²` membership result for nonnegative measurable observables.
-/

@[expose] public section

namespace SuperdiffusionCLT.Probability

open MeasureTheory Set
open Homogenization IndependentSums
open scoped ENNReal

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A literal Gaussian upper-tail estimate at scale `A` gives the
`Gamma₂` weak-Orlicz estimate of the CoarseGraining library. -/
theorem isBigOWith_gammaSigma_two_of_gaussian_tail
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {A : ℝ}
    (hTail : ∀ t : ℝ, 1 ≤ t →
      μ {ω | A * t < X ω} ≤
        ENNReal.ofReal (Real.exp (-(t ^ (2 : ℝ))))) :
    IsBigOWith μ (gammaSigma 2) X A := by
  rw [isBigOWith_gammaSigma_iff]
  intro t ht
  have hMeasure := hTail t ht
  have hFinite : μ {ω | A * t < X ω} ≠ ⊤ := measure_ne_top _ _
  change (μ {ω | A * t < X ω}).toReal ≤ Real.exp (-(t ^ (2 : ℝ)))
  rw [← ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.exp (-(t ^ (2 : ℝ))))]
  exact (ENNReal.toReal_le_toReal hFinite ENNReal.ofReal_ne_top).2 hMeasure

/-- A nonnegative measurable real random variable with a strict Gaussian upper
tail above level one belongs to `L²`. -/
theorem memLp_two_of_gaussian_tail
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hXmeas : Measurable X)
    (hXnonneg : ∀ ω, 0 ≤ X ω)
    (hTail : ∀ t : ℝ, 1 ≤ t →
      μ {ω | t < X ω} ≤ ENNReal.ofReal (Real.exp (-(t ^ 2)))) :
    MemLp X 2 μ := by
  have hXsq_meas : Measurable (fun ω ↦ X ω ^ 2) := by
    simp only [pow_two]
    exact hXmeas.mul hXmeas
  have hTail_sq : ∀ t : ℝ, 1 ≤ t →
      μ {ω | t < X ω ^ 2} ≤ ENNReal.ofReal (Real.exp (-t)) := by
    intro t ht
    calc
      μ {ω | t < X ω ^ 2} ≤ μ {ω | Real.sqrt t < X ω} := by
        apply measure_mono
        intro ω hω
        change t < X ω ^ 2 at hω
        change Real.sqrt t < X ω
        rw [Real.sqrt_lt (by linarith only [ht]) (hXnonneg ω)]
        exact hω
      _ ≤ ENNReal.ofReal (Real.exp (-(Real.sqrt t) ^ 2)) := by
        apply hTail
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt ht
      _ = ENNReal.ofReal (Real.exp (-t)) := by
        rw [Real.sq_sqrt (by linarith only [ht])]
  have hSmall :
      (∫⁻ t in Ioc (0 : ℝ) 1, μ {ω | t < X ω ^ 2}) < ∞ := by
    calc
      (∫⁻ t in Ioc (0 : ℝ) 1, μ {ω | t < X ω ^ 2}) ≤
          ∫⁻ _t in Ioc (0 : ℝ) 1, (1 : ℝ≥0∞) := by
        apply setLIntegral_mono measurable_const
        intro t _
        exact (measure_mono (by intro ω _; trivial)).trans_eq
          (IsProbabilityMeasure.measure_univ (μ := μ))
      _ < ∞ := by
        simp only [lintegral_one, Measure.restrict_apply, MeasurableSet.univ,
          univ_inter, Real.volume_Ioc]
        exact ENNReal.ofReal_lt_top
  have hLarge :
      (∫⁻ t in Ioi (1 : ℝ), μ {ω | t < X ω ^ 2}) < ∞ := by
    calc
      (∫⁻ t in Ioi (1 : ℝ), μ {ω | t < X ω ^ 2}) ≤
          ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (Real.exp (-t)) := by
        apply setLIntegral_mono
        · exact (Real.continuous_exp.comp continuous_neg).measurable.ennreal_ofReal
        · intro t ht
          exact hTail_sq t ht.le
      _ < ∞ := by
        simpa only [Real.norm_eq_abs] using
          (integrableOn_exp_neg_Ioi (1 : ℝ)).lintegral_lt_top
  have hTail_integral :
      (∫⁻ t in Ioi (0 : ℝ), μ {ω | t < X ω ^ 2}) < ∞ := by
    have hSplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 :=
      (Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)).symm
    rw [hSplit, lintegral_union measurableSet_Ioi (Ioc_disjoint_Ioi le_rfl)]
    exact ENNReal.add_lt_top.mpr ⟨hSmall, hLarge⟩
  have hLayer :
      (∫⁻ ω, ENNReal.ofReal (X ω ^ 2) ∂μ) =
        ∫⁻ t in Ioi (0 : ℝ), μ {ω | t < X ω ^ 2} := by
    exact lintegral_eq_lintegral_meas_lt μ
      (Filter.Eventually.of_forall fun ω ↦ sq_nonneg (X ω))
      hXsq_meas.aemeasurable
  have hSq_integrable : Integrable (fun ω ↦ X ω ^ 2) μ := by
    apply (lintegral_ofReal_ne_top_iff_integrable
      hXsq_meas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω ↦ sq_nonneg (X ω))).mp
    rw [hLayer]
    exact hTail_integral.ne
  exact (memLp_two_iff_integrable_sq hXmeas.aestronglyMeasurable).mpr hSq_integrable

end

end SuperdiffusionCLT.Probability
