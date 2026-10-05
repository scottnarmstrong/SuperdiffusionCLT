/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Convex.Integral
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Integral.Prod
public import Homogenization.CoarseGraining.Definitions
public import Homogenization.Probability.IndependentSums.GammaSigma.Basic

/-!
# Jensen averaging of stretched-exponential tails

This module proves the averaging step used by the manuscript whenever a
pointwise `O_{Gamma_sigma}` estimate is upgraded to a normalized estimate over
a spatial region: if a nonnegative jointly measurable family `Y x` obeys one
common `Gamma_sigma` tail at every point `x`, then its normalized volume
average over a set of positive finite volume obeys the same tail, up to the
universal constants of the moment characterization.

The proof is the manuscript's "Jensen's inequality" made explicit. The tail is
converted to the CoarseGraining library's `p^{1/sigma}` moment growth, Jensen's inequality
for the convex map `t ↦ t ^ p` transfers the `p`-th moment through the normalized
spatial average, Fubini exchanges the spatial and probabilistic integrals, and
the moment bound is converted back to a tail.

## Main results

* `hasGammaMomentGrowthWith_volumeAverage`: moment growth passes to the
  normalized volume average with the same witness.
* `isBigOWith_gammaSigma_volumeAverage`: the tail form.
-/

@[expose] public section

namespace SuperdiffusionCLT.Probability

open Homogenization MeasureTheory
open Homogenization.IndependentSums

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- Elementary comparison used to pass from an `L^p` bound to an `L^1` bound
on a finite measure space. -/
private theorem le_one_add_rpow {y p : ℝ} (hy : 0 ≤ y) (hp : 1 ≤ p) :
    y ≤ 1 + y ^ p := by
  rcases le_or_gt y 1 with hle | hlt
  · exact hle.trans (le_add_of_nonneg_right (Real.rpow_nonneg hy p))
  · have h1 : y ^ (1 : ℝ) ≤ y ^ p :=
      Real.rpow_le_rpow_of_exponent_le hlt.le hp
    rw [Real.rpow_one] at h1
    exact h1.trans (le_add_of_nonneg_left zero_le_one)

/-- The CoarseGraining library's normalized volume average is Mathlib's set average for the Lebesgue
measure. -/
theorem volumeAverage_eq_setAverage {d : ℕ} (U : Set (Vec d)) (f : Vec d → ℝ) :
    volumeAverage U f = ⨍ x in U, f x ∂volume := by
  rw [setAverage_eq, smul_eq_mul, volumeAverage, measureReal_def]

/-- **Jensen averaging at the level of moments.** A jointly measurable
nonnegative family with one common `Gamma_sigma` moment-growth witness keeps
that witness after normalized averaging over a set of positive finite
volume. -/
theorem hasGammaMomentGrowthWith_volumeAverage
    [IsProbabilityMeasure mu] {d : ℕ} {U : Set (Vec d)}
    {Y : Vec d → Omega → ℝ} {sigma M : ℝ}
    (hU0 : volume U ≠ 0) (hUtop : volume U ≠ ⊤)
    (hYnonneg : ∀ x omega, 0 ≤ Y x omega)
    (hYmeas : Measurable (Function.uncurry Y))
    (hY : ∀ x, HasGammaMomentGrowthWith mu sigma (Y x) M) :
    HasGammaMomentGrowthWith mu sigma
      (fun omega ↦ volumeAverage U (fun x ↦ Y x omega)) M := by
  have hnu : IsFiniteMeasure (volume.restrict U : Measure (Vec d)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hUtop
  have hc : 0 < (volume U).toReal := ENNReal.toReal_pos hU0 hUtop
  have hZnonneg : ∀ omega, 0 ≤ volumeAverage U (fun x ↦ Y x omega) := by
    intro omega
    rw [volumeAverage]
    exact mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
      (integral_nonneg fun x ↦ hYnonneg x omega)
  rw [hasGammaMomentGrowthWith_iff_of_nonneg hZnonneg]
  intro p hp
  have hp0 : (0 : ℝ) ≤ p := le_trans zero_le_one hp
  have hYx : ∀ x, Integrable (fun omega ↦ Y x omega ^ p) mu ∧
      ∫ omega, Y x omega ^ p ∂mu ≤ (M * p ^ sigma⁻¹) ^ p := fun x ↦
    ((hasGammaMomentGrowthWith_iff_of_nonneg
      (fun omega ↦ hYnonneg x omega)).1 (hY x)) hp
  have hswap : Measurable (fun q : Omega × Vec d ↦ Y q.2 q.1) :=
    hYmeas.comp measurable_swap
  have hGmeas : Measurable (fun q : Omega × Vec d ↦ Y q.2 q.1 ^ p) :=
    (Real.continuous_rpow_const hp0).measurable.comp hswap
  have hGmeas' : Measurable (fun q : Vec d × Omega ↦ Y q.1 q.2 ^ p) :=
    (Real.continuous_rpow_const hp0).measurable.comp hYmeas
  have hinner_sm : StronglyMeasurable
      (fun x : Vec d ↦ ∫ omega, Y x omega ^ p ∂mu) :=
    hGmeas'.stronglyMeasurable.integral_prod_right'
  have hinner_nonneg : ∀ x : Vec d, 0 ≤ ∫ omega, Y x omega ^ p ∂mu :=
    fun x ↦ integral_nonneg fun omega ↦ Real.rpow_nonneg (hYnonneg x omega) p
  have hinner_int : Integrable (fun x : Vec d ↦ ∫ omega, Y x omega ^ p ∂mu)
      (volume.restrict U) := by
    refine Integrable.mono' (integrable_const ((M * p ^ sigma⁻¹) ^ p))
      hinner_sm.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hinner_nonneg x)]
    exact (hYx x).2
  have hnormEq : (fun x : Vec d ↦ ∫ omega, ‖Y x omega ^ p‖ ∂mu)
      = fun x : Vec d ↦ ∫ omega, Y x omega ^ p ∂mu := by
    funext x
    refine integral_congr_ae ?_
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hYnonneg x omega) p)]
  have hprod : Integrable (fun q : Omega × Vec d ↦ Y q.2 q.1 ^ p)
      (mu.prod (volume.restrict U)) := by
    rw [integrable_prod_iff' hGmeas.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun x ↦ (hYx x).1, ?_⟩
    rw [hnormEq]
    exact hinner_int
  have hswapint := integral_integral_swap
    (f := fun (omega : Omega) (x : Vec d) ↦ Y x omega ^ p) hprod
  have hsplit := (integrable_prod_iff hGmeas.aestronglyMeasurable).1 hprod
  have hZpint : Integrable
      (fun omega ↦ ∫ x, Y x omega ^ p ∂(volume.restrict U)) mu := by
    have h := hsplit.2
    have hcongr : (fun omega ↦ ∫ x, ‖Y x omega ^ p‖ ∂(volume.restrict U))
        = fun omega ↦ ∫ x, Y x omega ^ p ∂(volume.restrict U) := by
      funext omega
      refine integral_congr_ae ?_
      filter_upwards with x
      rw [Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (hYnonneg x omega) p)]
    rwa [hcongr] at h
  have hbound_total :
      ∫ omega, (∫ x, Y x omega ^ p ∂(volume.restrict U)) ∂mu ≤
        (volume U).toReal * (M * p ^ sigma⁻¹) ^ p := by
    rw [hswapint]
    calc ∫ x, (∫ omega, Y x omega ^ p ∂mu) ∂(volume.restrict U)
        ≤ ∫ _x, (M * p ^ sigma⁻¹) ^ p ∂(volume.restrict U) :=
          integral_mono hinner_int (integrable_const _) fun x ↦ (hYx x).2
      _ = (volume U).toReal * (M * p ^ sigma⁻¹) ^ p := by
          rw [integral_const, measureReal_restrict_apply_univ, smul_eq_mul,
            measureReal_def]
  have hjensen : ∀ᵐ omega ∂mu,
      volumeAverage U (fun x ↦ Y x omega) ^ p ≤
        (volume U).toReal⁻¹ * ∫ x, Y x omega ^ p ∂(volume.restrict U) := by
    filter_upwards [hsplit.1] with omega hint
    have hYfix : Measurable (fun x : Vec d ↦ Y x omega) :=
      hYmeas.comp (measurable_id.prodMk measurable_const)
    have hY1 : Integrable (fun x : Vec d ↦ Y x omega) (volume.restrict U) := by
      refine Integrable.mono' ((integrable_const (1 : ℝ)).add hint)
        hYfix.aestronglyMeasurable ?_
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (hYnonneg x omega)]
      exact le_one_add_rpow (hYnonneg x omega) hp
    have hjen := ConvexOn.map_set_average_le (μ := volume) (t := U)
      (g := fun y : ℝ ↦ y ^ p) (s := Set.Ici (0 : ℝ))
      (f := fun x : Vec d ↦ Y x omega)
      (convexOn_rpow hp)
      (Real.continuous_rpow_const hp0).continuousOn
      isClosed_Ici hU0 hUtop
      (Filter.Eventually.of_forall fun x ↦ hYnonneg x omega)
      hY1 hint
    rw [volumeAverage_eq_setAverage]
    refine hjen.trans (le_of_eq ?_)
    rw [setAverage_eq, smul_eq_mul, measureReal_def]
  have hZ0m : Measurable (fun omega ↦ ∫ x, Y x omega ∂(volume.restrict U)) :=
    hswap.stronglyMeasurable.integral_prod_right'.measurable
  have hZpm : Measurable
      (fun omega ↦ volumeAverage U (fun x ↦ Y x omega) ^ p) := by
    have hmul : Measurable
        (fun omega ↦ (volume U).toReal⁻¹ *
          ∫ x, Y x omega ∂(volume.restrict U)) :=
      measurable_const.mul hZ0m
    exact (Real.continuous_rpow_const hp0).measurable.comp hmul
  have hZpIntegrable : Integrable
      (fun omega ↦ volumeAverage U (fun x ↦ Y x omega) ^ p) mu := by
    refine Integrable.mono' (hZpint.const_mul ((volume U).toReal⁻¹))
      hZpm.aestronglyMeasurable ?_
    filter_upwards [hjensen] with omega h
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (hZnonneg omega) p)]
    exact h
  refine ⟨hZpIntegrable, ?_⟩
  calc ∫ omega, volumeAverage U (fun x ↦ Y x omega) ^ p ∂mu
      ≤ ∫ omega, (volume U).toReal⁻¹ *
          (∫ x, Y x omega ^ p ∂(volume.restrict U)) ∂mu :=
        integral_mono_ae hZpIntegrable
          (hZpint.const_mul ((volume U).toReal⁻¹)) hjensen
    _ = (volume U).toReal⁻¹ *
          ∫ omega, (∫ x, Y x omega ^ p ∂(volume.restrict U)) ∂mu :=
        integral_const_mul _ _
    _ ≤ (volume U).toReal⁻¹ *
          ((volume U).toReal * (M * p ^ sigma⁻¹) ^ p) :=
        mul_le_mul_of_nonneg_left hbound_total (inv_nonneg.2 hc.le)
    _ = (M * p ^ sigma⁻¹) ^ p := by
        rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]

/-- **Jensen averaging of a stretched-exponential tail.** A jointly measurable
nonnegative family obeying one common `O_{Gamma_sigma}(A)` bound at every point
has a normalized volume average obeying `O_{Gamma_sigma}` at the scale
`e * gammaMomentConst sigma * A`. -/
theorem isBigOWith_gammaSigma_volumeAverage
    [IsProbabilityMeasure mu] {d : ℕ} {U : Set (Vec d)}
    {Y : Vec d → Omega → ℝ} {sigma A : ℝ}
    (hsigma : 0 < sigma) (hA : 0 < A)
    (hU0 : volume U ≠ 0) (hUtop : volume U ≠ ⊤)
    (hYnonneg : ∀ x omega, 0 ≤ Y x omega)
    (hYmeas : Measurable (Function.uncurry Y))
    (hY : ∀ x, IsBigOWith mu (gammaSigma sigma) (Y x) A) :
    IsBigOWith mu (gammaSigma sigma)
      (fun omega ↦ volumeAverage U (fun x ↦ Y x omega))
      (Real.exp 1 * (gammaMomentConst sigma * A)) := by
  have hZnonneg : ∀ omega, 0 ≤ volumeAverage U (fun x ↦ Y x omega) := by
    intro omega
    rw [volumeAverage]
    exact mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
      (integral_nonneg fun x ↦ hYnonneg x omega)
  have hMoment : ∀ x, HasGammaMomentGrowthWith mu sigma (Y x)
      (gammaMomentConst sigma * A) := by
    intro x
    have hYfix : Measurable (Y x) :=
      hYmeas.comp (measurable_const.prodMk measurable_id)
    exact hasGammaMomentGrowthWith_of_isBigOWith_gammaSigma hsigma hA
      (fun omega ↦ hYnonneg x omega) hYfix.aemeasurable (hY x)
  exact isBigOWith_gammaSigma_of_hasGammaMomentGrowthWith_of_nonneg hsigma
    (mul_pos (gammaMomentConst_pos hsigma) hA) hZnonneg
    (hasGammaMomentGrowthWith_volumeAverage hU0 hUtop hYnonneg hYmeas hMoment)

end

end SuperdiffusionCLT.Probability
