/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Root.AnnealedDt
public import Homogenization.Ambient.Basic
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# The annealed variance bound: splitting along the good and the bad event
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- **Splitting along a good and a bad event.**  If `F ≤ Z ^ p` almost surely, the event
`{θ < Z}` has probability at most `τ`, and `Z ≤ Λ V` with `V` measurable and `∫ V ^ (2p) ≤ Mv`, then
`∫ F ≤ θ ^ p + Λ ^ p * sqrt Mv * sqrt τ`. -/
theorem annDt_split {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : Ω → ℝ≥0∞} {Z V : Ω → ℝ} {p θ Λ τ Mv : ℝ} (hp : 1 ≤ p) (hθ : 0 ≤ θ) (hΛ : 0 ≤ Λ)
    (hτ : 0 ≤ τ) (hMv0 : 0 ≤ Mv)
    (hF : ∀ᵐ ω ∂μ, F ω ≤ ENNReal.ofReal (Z ω ^ p))
    (hZ0 : ∀ᵐ ω ∂μ, 0 ≤ Z ω)
    (hZV : ∀ᵐ ω ∂μ, Z ω ≤ Λ * V ω) (hV : Measurable V)
    (hV0 : ∀ ω, 0 ≤ V ω)
    (hMv : ∫⁻ ω, ENNReal.ofReal (V ω ^ (2 * p)) ∂μ ≤ ENNReal.ofReal Mv)
    (htail : μ {ω | θ < Z ω} ≤ ENNReal.ofReal τ) :
    ∫⁻ ω, F ω ∂μ ≤ ENNReal.ofReal (θ ^ p + Λ ^ p * Real.sqrt Mv * Real.sqrt τ) := by
  set T : Set Ω := toMeasurable μ {ω | θ < Z ω} with hT
  have hTm : MeasurableSet T := measurableSet_toMeasurable _ _
  have hTμ : μ T ≤ ENNReal.ofReal τ := by
    rw [hT, measure_toMeasurable]; exact htail
  have hp0 : 0 < p := by linarith only [hp]
  set g : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (V ω ^ p) with hg
  have hgm : Measurable g := by
    refine ENNReal.measurable_ofReal.comp ?_
    exact hV.pow_const p
  have hpt : ∀ᵐ ω ∂μ, F ω ≤ ENNReal.ofReal (θ ^ p) +
      T.indicator (fun ω => ENNReal.ofReal (Λ ^ p) * g ω) ω := by
    filter_upwards [hF, hZ0, hZV] with ω h1 h2 h3
    by_cases hz : Z ω ≤ θ
    · refine h1.trans (le_trans ?_ le_self_add)
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow h2 hz hp0.le)
    · have hzθ : θ < Z ω := not_le.1 hz
      have hmem : ω ∈ T := subset_toMeasurable _ _ hzθ
      rw [Set.indicator_of_mem hmem]
      refine h1.trans (le_trans ?_ le_add_self)
      have hb : Z ω ^ p ≤ (Λ * V ω) ^ p := Real.rpow_le_rpow h2 h3 hp0.le
      rw [Real.mul_rpow hΛ (hV0 ω)] at hb
      rw [hg]
      simp only
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hΛ _)]
      exact ENNReal.ofReal_le_ofReal hb
  have h1 : ∫⁻ ω, F ω ∂μ ≤ ∫⁻ ω, (ENNReal.ofReal (θ ^ p) +
      T.indicator (fun ω => ENNReal.ofReal (Λ ^ p) * g ω) ω) ∂μ := lintegral_mono_ae hpt
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
    lintegral_indicator hTm] at h1
  have h2 : ∫⁻ ω in T, ENNReal.ofReal (Λ ^ p) * g ω ∂μ ≤
      ENNReal.ofReal (Λ ^ p) * (ENNReal.ofReal (Real.sqrt Mv) * ENNReal.ofReal (Real.sqrt τ)) := by
    rw [lintegral_const_mul _ hgm]
    refine mul_le_mul_right ?_ _
    rw [← lintegral_indicator hTm]
    have hind : (fun ω => T.indicator g ω) = fun ω => (g * T.indicator (fun _ => (1 : ℝ≥0∞))) ω := by
      funext ω
      by_cases hω : ω ∈ T
      · simp [Set.indicator_of_mem hω]
      · simp [Set.indicator_of_notMem hω]
    rw [hind]
    have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq μ (Real.HolderConjugate.two_two)
      (f := g) (g := T.indicator (fun _ => (1 : ℝ≥0∞))) hgm.aemeasurable
      ((measurable_const.indicator hTm).aemeasurable)
    refine hcs.trans (mul_le_mul' ?_ ?_)
    · have : ∫⁻ ω, g ω ^ (2 : ℝ) ∂μ = ∫⁻ ω, ENNReal.ofReal (V ω ^ (2 * p)) ∂μ := by
        refine lintegral_congr fun ω => ?_
        rw [hg]
        simp only
        rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (hV0 ω) _) (by norm_num),
          ← Real.rpow_mul (hV0 ω), mul_comm p 2]
      rw [this]
      calc (∫⁻ ω, ENNReal.ofReal (V ω ^ (2 * p)) ∂μ) ^ (1 / (2 : ℝ)) ≤
          (ENNReal.ofReal Mv) ^ (1 / (2 : ℝ)) := ENNReal.rpow_le_rpow hMv (by norm_num)
        _ = ENNReal.ofReal (Real.sqrt Mv) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hMv0 (by norm_num), Real.sqrt_eq_rpow]
    · have : ∫⁻ ω, (T.indicator (fun _ => (1 : ℝ≥0∞)) ω) ^ (2 : ℝ) ∂μ = μ T := by
        have : (fun ω => (T.indicator (fun _ => (1 : ℝ≥0∞)) ω) ^ (2 : ℝ)) =
            T.indicator (fun _ => (1 : ℝ≥0∞)) := by
          funext ω
          by_cases hω : ω ∈ T
          · simp [Set.indicator_of_mem hω]
          · simp [Set.indicator_of_notMem hω]
        rw [this, lintegral_indicator_const hTm, one_mul]
      rw [this]
      calc (μ T) ^ (1 / (2 : ℝ)) ≤ (ENNReal.ofReal τ) ^ (1 / (2 : ℝ)) :=
          ENNReal.rpow_le_rpow hTμ (by norm_num)
        _ = ENNReal.ofReal (Real.sqrt τ) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hτ (by norm_num), Real.sqrt_eq_rpow]
  refine h1.trans ((add_le_add_right h2 _).trans (le_of_eq ?_))
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), ← ENNReal.ofReal_mul (Real.rpow_nonneg hΛ _),
    ← ENNReal.ofReal_add (Real.rpow_nonneg hθ _) (by positivity)]
  congr 1
  ring

/-- **Jensen for the Euclidean mean.**  For a probability measure with integrable squared norm,
`|∫ y|² ≤ ∫ |y|²`. -/
theorem annDt_vecNormSq_integral_le {d : ℕ} {μ : Measure (Homogenization.Vec d)}
    [IsProbabilityMeasure μ]
    (hint : Integrable (fun y => Homogenization.vecNormSq y) μ) :
    Homogenization.vecNormSq (∫ y, y ∂μ) ≤ ∫ y, Homogenization.vecNormSq y ∂μ := by
  have hsq : ∀ i : Fin d, Integrable (fun y : Homogenization.Vec d => y i ^ 2) μ := by
    intro i
    refine hint.mono' ((measurable_pi_apply i).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    unfold Homogenization.vecNormSq Homogenization.vecDot
    calc y i ^ 2 = y i * y i := sq _
      _ ≤ ∑ j, y j * y j :=
        Finset.single_le_sum (f := fun j => y j * y j) (fun j _ => mul_self_nonneg _)
          (Finset.mem_univ i)
  have hlin : ∀ i : Fin d, Integrable (fun y : Homogenization.Vec d => y i) μ := by
    intro i
    refine ((hsq i).add (integrable_const (1 : ℝ))).mono'
      (measurable_pi_apply i).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs]
    simp only [Pi.add_apply]
    nlinarith only [sq_nonneg (|y i| - 1), sq_abs (y i), abs_nonneg (y i)]
  have hcoord : ∀ i : Fin d, (∫ y, y ∂μ) i ^ 2 ≤ ∫ y, y i ^ 2 ∂μ := by
    intro i
    rw [eval_integral hlin i]
    have := (Even.convexOn_pow (𝕜 := ℝ) (by decide : Even 2)).map_integral_le
      (continuous_pow 2).continuousOn isClosed_univ (Filter.Eventually.of_forall fun _ => mem_univ _)
      (hlin i) (by simpa [Function.comp_def] using hsq i)
    simpa using this
  unfold Homogenization.vecNormSq Homogenization.vecDot
  rw [integral_finsetSum _ (fun i _ => by simpa [sq] using hsq i)]
  refine Finset.sum_le_sum fun i _ => ?_
  simpa [sq] using hcoord i

end

end SuperdiffusionCLT.Section8
