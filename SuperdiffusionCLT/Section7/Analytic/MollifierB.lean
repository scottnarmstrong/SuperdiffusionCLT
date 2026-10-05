/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Mollifier

/-!
# The full dual test norm of a bounded Lipschitz function on a cube

A bounded Lipschitz function `g` satisfies the unit-test conditions of the full dual negative
Besov norm of order `1/4` (`q = 2`) after division by an explicit constant: the fluctuation of `g`
on a descendant of scale `3^{m-j}` is at most `K 3^{m-j}`, and the weights `3^{-(m-j)/4}` turn
this into a geometric series in `j` of ratio `3^{-3/4} ≤ 1/2`.
-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Section7

open Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Almost every point for the normalized cube measure lies in the cube. -/
theorem a16_ae_mem_cube (R : TriadicCube d) :
    ∀ᵐ y ∂(normalizedCubeMeasure R), y ∈ cubeSet R := by
  unfold normalizedCubeMeasure
  refine Measure.ae_smul_measure ?_ _
  unfold cubeMeasure
  exact ae_restrict_mem (measurableSet_cubeSet R)

/-- On a cube, a function of oscillation at most `D` deviates from its average by at most `D`. -/
theorem a16_fluct_abs_le (R : TriadicCube d) {g : Vec d → ℝ} (hmeas : Measurable g) {M D : ℝ}
    (hM : ∀ y, |g y| ≤ M)
    (hD : ∀ y ∈ cubeSet R, ∀ y' ∈ cubeSet R, |g y - g y'| ≤ D) :
    ∀ y ∈ cubeSet R, |cubeFluctuation R g y| ≤ D := by
  intro y hy
  have hD0 : 0 ≤ D := le_trans (abs_nonneg _) (hD y hy y hy)
  have hint : Integrable g (normalizedCubeMeasure R) := by
    refine Integrable.of_bound (C := M) hmeas.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]
      exact hM z
  have hae : ∀ᵐ y' ∂(normalizedCubeMeasure R), y' ∈ cubeSet R := a16_ae_mem_cube R
  have huniv : (normalizedCubeMeasure R).real Set.univ = 1 := by
    rw [Measure.real_def, normalizedCubeMeasure_apply_univ]
    simp
  have hrw : cubeFluctuation R g y = ∫ y', (g y - g y') ∂(normalizedCubeMeasure R) := by
    unfold cubeFluctuation
    rw [cubeAverage_eq_integral_normalizedCubeMeasure,
      integral_sub (integrable_const _) hint, integral_const, huniv]
    simp
  rw [hrw]
  have hb : ∀ᵐ y' ∂(normalizedCubeMeasure R), ‖g y - g y'‖ ≤ D := by
    filter_upwards [hae] with y' hy'
    rw [Real.norm_eq_abs]
    exact hD y hy y' hy'
  have h2 := norm_integral_le_of_norm_le_const (μ := normalizedCubeMeasure R) hb
  rw [Real.norm_eq_abs, huniv, mul_one] at h2
  exact h2

/-- The normalized `L²` oscillation on a cube is bounded by any sup bound of the fluctuation. -/
theorem a16_osc_le (R : TriadicCube d) {g : Vec d → ℝ} (hmeas : Measurable g) {M D : ℝ}
    (hM : ∀ y, |g y| ≤ M)
    (hD : ∀ y ∈ cubeSet R, ∀ y' ∈ cubeSet R, |g y - g y'| ≤ D) :
    cubeBesovOscillation R 2 g ≤ D := by
  have hD0 : 0 ≤ D := by
    have hne : (cubeSet R).Nonempty := by
      by_contra hne
      rw [Set.not_nonempty_iff_eq_empty] at hne
      have h1 := volume_cubeSet_toReal R
      rw [hne] at h1
      simp only [measure_empty, ENNReal.toReal_zero] at h1
      exact (cubeVolume_pos R).ne h1
    obtain ⟨y, hy⟩ := hne
    exact le_trans (abs_nonneg _) (hD y hy y hy)
  have hfl := a16_fluct_abs_le R hmeas hM hD
  have hae : ∀ᵐ y ∂(normalizedCubeMeasure R), ‖cubeFluctuation R g y‖ ≤ D := by
    filter_upwards [a16_ae_mem_cube R] with y hy
    rw [Real.norm_eq_abs]
    exact hfl y hy
  have hfm : AEStronglyMeasurable (cubeFluctuation R g) (normalizedCubeMeasure R) :=
    (hmeas.sub measurable_const).aestronglyMeasurable
  have h1 := eLpNorm_le_of_ae_bound (p := (2 : ℝ≥0∞)) hfm hae
  rw [normalizedCubeMeasure_apply_univ, ENNReal.one_rpow, one_mul] at h1
  unfold cubeBesovOscillation cubeLpNorm
  have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
  rwa [ENNReal.toReal_ofReal hD0] at h2

/-- Two points of a triadic cube are at sup distance at most its side. -/
theorem a16_dist_le_of_mem_cubeSet (R : TriadicCube d) {y y' : Vec d}
    (hy : y ∈ cubeSet R) (hy' : y' ∈ cubeSet R) : dist y y' ≤ cubeScaleFactor R := by
  have hc : 0 ≤ cubeScaleFactor R := by
    unfold cubeScaleFactor
    exact zpow_nonneg (by norm_num) _
  rw [dist_pi_le_iff hc]
  intro i
  obtain ⟨h1, h2⟩ := hy i
  obtain ⟨h3, h4⟩ := hy' i
  rw [Real.dist_eq, abs_le]
  constructor <;> nlinarith only [h1, h2, h3, h4]

/-- The `L²` oscillation depth term of a Lipschitz function. -/
theorem a16_depthSeminorm_le (Q : TriadicCube d) {g : Vec d → ℝ} (hmeas : Measurable g)
    {M K : ℝ} (hK : 0 ≤ K) (hM : ∀ y, |g y| ≤ M)
    (hLip : ∀ y y', |g y - g y'| ≤ K * dist y y') (j : ℕ) :
    cubeBesovDepthSeminorm Q (1 / 4) 2 g j ≤
      K * (cubeScaleFactor Q / (3 : ℝ) ^ j) ^ (3 / 4 : ℝ) := by
  set t : ℝ := cubeScaleFactor Q / (3 : ℝ) ^ j with ht
  have hc : 0 < cubeScaleFactor Q := by
    unfold cubeScaleFactor
    exact zpow_pos (by norm_num) _
  have htpos : 0 < t := div_pos hc (pow_pos (by norm_num) _)
  have hosc : ∀ R ∈ descendantsAtDepth Q j, cubeBesovOscillation R 2 g ≤ K * t := by
    intro R hR
    have hRt : cubeScaleFactor R = t := cubeScaleFactor_descendant_eq_div_pow hR
    refine a16_osc_le R hmeas hM ?_
    intro y hy y' hy'
    calc |g y - g y'| ≤ K * dist y y' := hLip y y'
      _ ≤ K * t := by
        rw [← hRt]
        exact mul_le_mul_of_nonneg_left (a16_dist_le_of_mem_cubeSet R hy hy') hK
  have havg : cubeBesovDepthAverage Q 2 g j ≤ (K * t) ^ (2 : ℝ) := by
    unfold cubeBesovDepthAverage descendantsAverage
    have hne := descendantsAtDepth_nonempty Q j
    have hcard : (0 : ℝ) < ((descendantsAtDepth Q j).card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr (by simpa [Finset.nonempty_iff_ne_empty] using hne)
    have hsum : ∑ R ∈ descendantsAtDepth Q j, cubeBesovOscillation R 2 g ^ (2 : ℝ≥0∞).toReal ≤
        ∑ R ∈ descendantsAtDepth Q j, (K * t) ^ (2 : ℝ) := by
      refine Finset.sum_le_sum fun R hR => ?_
      have h0 : 0 ≤ cubeBesovOscillation R 2 g := by
        unfold cubeBesovOscillation cubeLpNorm
        exact ENNReal.toReal_nonneg
      have : (2 : ℝ≥0∞).toReal = 2 := by norm_num
      rw [this]
      exact Real.rpow_le_rpow h0 (hosc R hR) (by norm_num)
    rw [Finset.sum_const, nsmul_eq_mul] at hsum
    calc ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
          ∑ R ∈ descendantsAtDepth Q j, cubeBesovOscillation R 2 g ^ (2 : ℝ≥0∞).toReal
        ≤ ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
          (((descendantsAtDepth Q j).card : ℝ) * (K * t) ^ (2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hcard.le)
      _ = (K * t) ^ (2 : ℝ) := by
          field_simp
  have havg0 : 0 ≤ cubeBesovDepthAverage Q 2 g j := by
    unfold cubeBesovDepthAverage
    refine descendantsAverage_nonneg Q j _ fun R _ => ?_
    exact Real.rpow_nonneg (by unfold cubeBesovOscillation cubeLpNorm; exact ENNReal.toReal_nonneg) _
  have hroot : (cubeBesovDepthAverage Q 2 g j) ^ (1 / (2 : ℝ≥0∞).toReal) ≤ K * t := by
    have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    rw [h2]
    calc (cubeBesovDepthAverage Q 2 g j) ^ (1 / (2 : ℝ))
        ≤ ((K * t) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
          Real.rpow_le_rpow havg0 havg (by norm_num)
      _ = K * t := by
          rw [← Real.rpow_mul (mul_nonneg hK htpos.le)]
          norm_num
  unfold cubeBesovDepthSeminorm cubeBesovDepthWeight
  rw [← ht]
  calc t ^ (-(1 / 4 : ℝ)) * (cubeBesovDepthAverage Q 2 g j) ^ (1 / (2 : ℝ≥0∞).toReal)
      ≤ t ^ (-(1 / 4 : ℝ)) * (K * t) :=
        mul_le_mul_of_nonneg_left hroot (Real.rpow_nonneg htpos.le _)
    _ = K * t ^ (3 / 4 : ℝ) := by
        have : t ^ (3 / 4 : ℝ) = t ^ (-(1 / 4 : ℝ)) * t := by
          rw [← Real.rpow_add_one htpos.ne']
          norm_num
        rw [this]
        ring

/-- The cube average of a bounded function is bounded by the same constant. -/
theorem a16_avg_abs_le (Q : TriadicCube d) {g : Vec d → ℝ} {M : ℝ} (hM : ∀ y, |g y| ≤ M) :
    |cubeAverage Q g| ≤ M := by
  rw [cubeAverage_eq_integral_normalizedCubeMeasure]
  have hb : ∀ᵐ y ∂(normalizedCubeMeasure Q), ‖g y‖ ≤ M :=
    Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]
      exact hM y
  have h2 := norm_integral_le_of_norm_le_const (μ := normalizedCubeMeasure Q) hb
  have huniv : (normalizedCubeMeasure Q).real Set.univ = 1 := by
    rw [Measure.real_def, normalizedCubeMeasure_apply_univ]
    simp
  rw [Real.norm_eq_abs, huniv, mul_one] at h2
  exact h2

/-- `3^{3/4} ≥ 2`. -/
theorem a16_two_le_three_rpow : (2 : ℝ) ≤ (3 : ℝ) ^ (3 / 4 : ℝ) := by
  by_contra hlt
  push Not at hlt
  have h0 : 0 ≤ (3 : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_nonneg (by norm_num) _
  have h4 : ((3 : ℝ) ^ (3 / 4 : ℝ)) ^ 4 = 27 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have h5 : ((3 : ℝ) ^ (3 / 4 : ℝ)) ^ 4 < 2 ^ 4 :=
    pow_lt_pow_left₀ hlt h0 (by norm_num)
  rw [h4] at h5
  norm_num at h5

/-- A geometric decay of the scale power. -/
theorem a16_scale_rpow_le (c : ℝ) (hc : 0 ≤ c) (j : ℕ) :
    (c / (3 : ℝ) ^ j) ^ (3 / 4 : ℝ) ≤ c ^ (3 / 4 : ℝ) * (1 / 2) ^ j := by
  have h3 : ((3 : ℝ) ^ j) ^ (3 / 4 : ℝ) = ((3 : ℝ) ^ (3 / 4 : ℝ)) ^ j := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_mul (by norm_num), mul_comm]
  have h2 : (2 : ℝ) ^ j ≤ ((3 : ℝ) ^ (3 / 4 : ℝ)) ^ j :=
    pow_le_pow_left₀ (by norm_num) a16_two_le_three_rpow j
  rw [Real.div_rpow hc (pow_nonneg (by norm_num) _), h3, div_eq_mul_inv, one_div, inv_pow]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hc _)
  exact inv_anti₀ (pow_pos (by norm_num) _) h2

/-- Nonnegativity of a depth term. -/
theorem a16_depthSeminorm_nonneg (Q : TriadicCube d) (g : Vec d → ℝ) (j : ℕ) :
    0 ≤ cubeBesovDepthSeminorm Q (1 / 4) 2 g j := by
  have hc : 0 < cubeScaleFactor Q := by
    unfold cubeScaleFactor
    exact zpow_pos (by norm_num) _
  unfold cubeBesovDepthSeminorm cubeBesovDepthWeight cubeBesovDepthAverage
  refine mul_nonneg (Real.rpow_nonneg (div_nonneg hc.le (pow_nonneg (by norm_num) _)) _)
    (Real.rpow_nonneg ?_ _)
  refine descendantsAverage_nonneg Q j _ fun R _ => ?_
  exact Real.rpow_nonneg (by unfold cubeBesovOscillation cubeLpNorm; exact ENNReal.toReal_nonneg) _

/-- The full dual test norm of order `1/4` of a bounded Lipschitz function. -/
theorem a16_testNorm_le (Q : TriadicCube d) {g : Vec d → ℝ} (hmeas : Measurable g)
    {M K : ℝ} (hK : 0 ≤ K) (hM : ∀ y, |g y| ≤ M)
    (hLip : ∀ y y', |g y - g y'| ≤ K * dist y y') (N : ℕ) :
    cubeBesovDualTestNorm Q (1 / 4) 2 2 N g ≤
      2 * (K * cubeScaleFactor Q ^ (3 / 4 : ℝ)) + cubeScaleFactor Q ^ (-(1 / 4 : ℝ)) * M := by
  have hc : 0 < cubeScaleFactor Q := by
    unfold cubeScaleFactor
    exact zpow_pos (by norm_num) _
  have hconj : cubeBesovConjExponent (2 : ℝ≥0∞) = 2 := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  have hne : cubeBesovConjExponent (2 : ℝ≥0∞) ≠ ∞ := by
    rw [hconj]; norm_num
  rw [cubeBesovDualTestNorm_of_conjExponent_ne_top Q _ _ _ N g hne, hconj]
  unfold cubeBesovPartialNorm cubeBesovPartialSeminorm
  set E : ℝ := K * cubeScaleFactor Q ^ (3 / 4 : ℝ) with hE
  have hE0 : 0 ≤ E := mul_nonneg hK (Real.rpow_nonneg hc.le _)
  have hterm : ∀ j ∈ Finset.range (N + 1),
      (cubeBesovDepthSeminorm Q (1 / 4) 2 g j) ^ (2 : ℝ≥0∞).toReal ≤ E ^ 2 * (1 / 2) ^ j := by
    intro j _
    have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    rw [h2]
    have hj := a16_depthSeminorm_le Q hmeas hK hM hLip j
    have hj2 : cubeBesovDepthSeminorm Q (1 / 4) 2 g j ≤ E * (1 / 2) ^ j := by
      refine hj.trans ?_
      calc K * (cubeScaleFactor Q / (3 : ℝ) ^ j) ^ (3 / 4 : ℝ)
          ≤ K * (cubeScaleFactor Q ^ (3 / 4 : ℝ) * (1 / 2) ^ j) :=
            mul_le_mul_of_nonneg_left (a16_scale_rpow_le _ hc.le j) hK
        _ = E * (1 / 2) ^ j := by rw [hE]; ring
    have h0 := a16_depthSeminorm_nonneg Q g j
    have hpow : (cubeBesovDepthSeminorm Q (1 / 4) 2 g j) ^ (2 : ℝ) =
        (cubeBesovDepthSeminorm Q (1 / 4) 2 g j) ^ 2 := by
      rw [← Real.rpow_natCast]; norm_num
    rw [hpow]
    calc (cubeBesovDepthSeminorm Q (1 / 4) 2 g j) ^ 2 ≤ (E * (1 / 2) ^ j) ^ 2 :=
          pow_le_pow_left₀ h0 hj2 2
      _ = E ^ 2 * ((1 / 4) ^ j) := by
          rw [mul_pow, ← pow_mul, mul_comm j 2, pow_mul]; norm_num
      _ ≤ E ^ 2 * (1 / 2) ^ j := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg E)
          exact pow_le_pow_left₀ (by norm_num) (by norm_num) j
  have hsum : ∑ j ∈ Finset.range (N + 1),
      (cubeBesovDepthSeminorm Q (1 / 4) 2 g j) ^ (2 : ℝ≥0∞).toReal ≤ (2 * E) ^ 2 := by
    calc _ ≤ ∑ j ∈ Finset.range (N + 1), E ^ 2 * (1 / 2) ^ j := Finset.sum_le_sum hterm
      _ = E ^ 2 * ∑ j ∈ Finset.range (N + 1), (1 / 2 : ℝ) ^ j := by rw [Finset.mul_sum]
      _ ≤ E ^ 2 * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le _) (sq_nonneg E)
      _ ≤ (2 * E) ^ 2 := by nlinarith only [sq_nonneg E]
  have hsum0 : 0 ≤ ∑ j ∈ Finset.range (N + 1),
      (cubeBesovDepthSeminorm Q (1 / 4) 2 g j) ^ (2 : ℝ≥0∞).toReal :=
    Finset.sum_nonneg fun j _ => Real.rpow_nonneg (a16_depthSeminorm_nonneg Q g j) _
  have hroot : (∑ j ∈ Finset.range (N + 1),
      (cubeBesovDepthSeminorm Q (1 / 4) 2 g j) ^ (2 : ℝ≥0∞).toReal) ^ (1 / (2 : ℝ≥0∞).toReal)
        ≤ 2 * E := by
    have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    rw [h2]
    calc _ ≤ ((2 * E) ^ 2) ^ (1 / (2 : ℝ)) := by
          rw [h2] at hsum0 hsum
          exact Real.rpow_le_rpow hsum0 hsum (by norm_num)
      _ = 2 * E := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
          norm_num
  have hav : ‖cubeAverage Q g‖ ≤ M := by
    rw [Real.norm_eq_abs]
    exact a16_avg_abs_le Q hM
  have hw : 0 ≤ cubeBesovScaleWeight (1 / 4 : ℝ) Q := by
    unfold cubeBesovScaleWeight
    exact Real.rpow_nonneg hc.le _
  have hwe : cubeBesovScaleWeight (1 / 4 : ℝ) Q = cubeScaleFactor Q ^ (-(1 / 4 : ℝ)) := rfl
  rw [← hwe]
  exact add_le_add hroot (mul_le_mul_of_nonneg_left hav hw)

/-- Local `L²` membership of the fluctuations of a bounded measurable function. -/
theorem a16_localMemLp (Q : TriadicCube d) {g : Vec d → ℝ} (hmeas : Measurable g) {M : ℝ}
    (hM : ∀ y, |g y| ≤ M) :
    CubeBesovDualLocalMemLpGlobal Q 2 g := by
  intro j R _
  have hconj : cubeBesovConjExponent (2 : ℝ≥0∞) = 2 := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  rw [hconj]
  refine MemLp.of_bound (C := M + M) (hmeas.sub measurable_const).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun y => ?_
  rw [Real.norm_eq_abs]
  unfold cubeFluctuation
  calc |g y - cubeAverage R g| ≤ |g y| + |cubeAverage R g| := abs_sub _ _
    _ ≤ M + M := add_le_add (hM y) (a16_avg_abs_le R hM)

end

end Section7
end SuperdiffusionCLT
