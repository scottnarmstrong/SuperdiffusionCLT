/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.CutoffSkewPremises
public import SuperdiffusionCLT.Section2.Localization.CutoffSkewBounds

/-!
# The bilinear cutoff clause at the shared constant

The cutoff carrier facts and the conjugated comparison are supplied by
`CutoffSkewPremises`.  The comparison has amplitude `D * (2 + D)`, so the
existential bilinear witness is `sqrt (2 * D + D ^ 2)`.  Its tail estimate is
obtained from the already supplied `Gamma₁` estimate for the witness `2 * D`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.CoarseGraining
open SuperdiffusionCLT.Section3.ResponseFields

noncomputable section

private theorem isBigOWith_half_double {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {Ψ : ℝ → ℝ} {D : Ω → ℝ} {A : ℝ}
    (hD : IndependentSums.IsBigOWith μ Ψ (fun ω => 2 * D ω) A) :
    IndependentSums.IsBigOWith μ Ψ D (A / 2) := by
  intro t ht
  have hset : IndependentSums.upperTailEvent D ((A / 2) * t) =
      IndependentSums.upperTailEvent (fun ω => 2 * D ω) (A * t) := by
    ext ω
    simp only [IndependentSums.mem_upperTailEvent]
    constructor
    · intro hω
      have hscale : A * t = 2 * ((A / 2) * t) := by ring
      rw [hscale]
      linarith only [hω]
    · intro hω
      have hscale : A * t = 2 * ((A / 2) * t) := by ring
      rw [hscale] at hω
      linarith only [hω]
  rw [hset]
  exact hD ht

private theorem isBigOWith_gammaSigma_sqrt_quadratic
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {D : Ω → ℝ} {B : ℝ}
    (hDnn : ∀ ω, 0 ≤ D ω)
    (hD : IndependentSums.IsBigOWith μ (IndependentSums.gammaSigma 1) D B)
    (hB : 0 < B) (A : ℝ) (hA : 0 ≤ A) (h1 : 4 * B ≤ A ^ 2)
    (h2 : Real.sqrt 2 * B ≤ A) :
    IndependentSums.IsBigOWith μ (IndependentSums.gammaSigma 1)
      (fun ω => Real.sqrt (2 * D ω + D ω ^ 2)) A := by
  have h2p : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  have hApos : 0 < A := lt_of_lt_of_le (mul_pos h2p hB) h2
  intro t ht
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hAt0 : 0 ≤ A * t := mul_nonneg hA ht0
  have hAtpos : 0 < A * t := mul_pos hApos htpos
  have hAt2sq : 0 ≤ (A * t) ^ 2 := le_of_lt (pow_pos hAtpos 2)
  have hkey : ∀ ω : Ω, A * t < Real.sqrt (2 * D ω + D ω ^ 2) →
      min ((A * t) ^ 2 / 4) (A * t / Real.sqrt 2) < D ω := by
    intro ω hlt
    have hsq : (A * t) ^ 2 < 2 * D ω + D ω ^ 2 := (Real.lt_sqrt hAt0).mp hlt
    rcases le_or_gt (2 * D ω) ((A * t) ^ 2 / 2) with hc | hc
    · have hDsq : (A * t) ^ 2 / 2 < D ω ^ 2 := by linarith only [hsq, hc]
      have hDpos : 0 < D ω := by
        by_contra hcon
        push Not at hcon
        have h0 : D ω = 0 := le_antisymm hcon (hDnn ω)
        have h2z : D ω ^ 2 = 0 := by rw [h0]; norm_num
        linarith only [hDsq, h2z, hAt2sq]
      have hcalc : (A * t / Real.sqrt 2) ^ 2 = (A * t) ^ 2 / 2 := by
        rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      have hcon2 : ¬ (D ω ≤ A * t / Real.sqrt 2) := by
        intro hle
        have hle2 : D ω ^ 2 ≤ (A * t / Real.sqrt 2) ^ 2 :=
          sq_le_sq' (by linarith only [hDnn ω, hle]) hle
        rw [hcalc] at hle2
        linarith only [hle2, hDsq]
      exact lt_of_le_of_lt (min_le_right _ _) (lt_of_not_ge hcon2)
    · have hDcase : (A * t) ^ 2 / 4 < D ω := by linarith only [hc]
      exact lt_of_le_of_lt (min_le_left _ _) hDcase
  have hcond1 : B ≤ min ((A * t) ^ 2 / 4) (A * t / Real.sqrt 2) := by
    have ht2 : (1 : ℝ) ≤ t ^ 2 := one_le_pow₀ ht
    have hu1 : B ≤ (A * t) ^ 2 / 4 := by
      refine (le_div_iff₀' (by norm_num : (0 : ℝ) < 4)).mpr ?_
      rw [show (A * t) ^ 2 = A ^ 2 * t ^ 2 from by ring]
      simpa only [mul_one] using mul_le_mul h1 ht2 zero_le_one (sq_nonneg A)
    have hu2 : B ≤ A * t / Real.sqrt 2 := by
      refine (le_div_iff₀' h2p).mpr ?_
      have hst1 : Real.sqrt 2 * B * 1 ≤ Real.sqrt 2 * B * t :=
        mul_le_mul_of_nonneg_left ht (mul_nonneg h2p.le (le_of_lt hB))
      rw [mul_one] at hst1
      have hst2 : Real.sqrt 2 * B * t ≤ A * t :=
        mul_le_mul_of_nonneg_right h2 ht0
      linarith only [hst1, hst2]
    exact le_min hu1 hu2
  have hcond2 : B * t ≤ min ((A * t) ^ 2 / 4) (A * t / Real.sqrt 2) := by
    have hBnn : 0 ≤ B := le_of_lt hB
    have htt : t ≤ t ^ 2 := by
      have q := mul_le_mul_of_nonneg_right ht ht0
      simpa only [one_mul, pow_two] using q
    have hu1 : B * t ≤ (A * t) ^ 2 / 4 := by
      refine (le_div_iff₀' (by norm_num : (0 : ℝ) < 4)).mpr ?_
      rw [show (A * t) ^ 2 = A ^ 2 * t ^ 2 from by ring]
      rw [show 4 * (B * t) = (4 * B) * t from by ring]
      exact mul_le_mul h1 htt ht0 (sq_nonneg A)
    have hu2 : B * t ≤ A * t / Real.sqrt 2 := by
      refine (le_div_iff₀' h2p).mpr ?_
      rw [show Real.sqrt 2 * (B * t) = (Real.sqrt 2 * B) * t from by ring]
      exact mul_le_mul_of_nonneg_right h2 ht0
    exact le_min hu1 hu2
  have hstep1 : μ.real (IndependentSums.upperTailEvent
      (fun ω => Real.sqrt (2 * D ω + D ω ^ 2)) (A * t)) ≤
      μ.real (IndependentSums.upperTailEvent D
        (min ((A * t) ^ 2 / 4) (A * t / Real.sqrt 2))) :=
    measureReal_mono (fun ω hω => hkey ω hω)
  have hstep2 : μ.real (IndependentSums.upperTailEvent D
      (min ((A * t) ^ 2 / 4) (A * t / Real.sqrt 2))) ≤
      μ.real (IndependentSums.upperTailEvent D
        (B * (min ((A * t) ^ 2 / 4) (A * t / Real.sqrt 2) / B))) := by
    have hEq : B * (min ((A * t) ^ 2 / 4) (A * t / Real.sqrt 2) / B) =
        min ((A * t) ^ 2 / 4) (A * t / Real.sqrt 2) := by
      rw [← mul_div_assoc B, mul_div_cancel_left₀ _ hB.ne']
    rw [hEq]
  have hstep3 : μ.real (IndependentSums.upperTailEvent D
      (B * (min ((A * t) ^ 2 / 4) (A * t / Real.sqrt 2) / B))) ≤
      (gammaSigma 1 (min ((A * t) ^ 2 / 4) (A * t / Real.sqrt 2) / B))⁻¹ := by
    exact hD ((one_le_div₀ hB).mpr hcond1)
  have hstep4 : (gammaSigma 1
      (min ((A * t) ^ 2 / 4) (A * t / Real.sqrt 2) / B))⁻¹ ≤
      (gammaSigma 1 t)⁻¹ := by
    rw [gammaSigma_inv, gammaSigma_inv, Real.rpow_one, Real.rpow_one]
    exact Real.exp_le_exp_of_le
      (by linarith only [(le_div_iff₀' hB).mpr hcond2])
  exact hstep1.trans (hstep2.trans (hstep3.trans hstep4))

private theorem localizationConst_ge_two {d : ℕ} (hd : 0 < d) :
    (2 : ℝ) ≤ localizationConst d := by
  have hd1 : 1 ≤ d := hd
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have hdn : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
  have hp : (1 : ℝ) ≤ (d : ℝ) ^ 3 := one_le_pow₀ hdn
  have hs : (1 : ℝ) ≤ Real.sqrt (d : ℝ) :=
    Real.le_sqrt_of_sq_le (by simpa only [one_pow] using hdn)
  have hm : (1 : ℝ) ≤ matrixOperatorNorm_diamConst d := by
    unfold matrixOperatorNorm_diamConst
    simpa only [one_mul] using mul_le_mul hp hs zero_le_one (pow_nonneg hd0 3)
  have hg2 : (1 : ℝ) ≤ gammaTriangleConst 2 := by
    rw [gammaTriangleConst_eq_of_one_le (by norm_num : (1 : ℝ) ≤ 2)]
    norm_num [gammaTriangleConst]
  have hK : (1 : ℝ) ≤ gaugeAmplitudeConst d := by
    unfold gaugeAmplitudeConst
    simpa only [one_mul] using
      mul_le_mul hm hg2 zero_le_one (matrixOperatorNorm_diamConst_nonneg d)
  have hg1 : (1 : ℝ) ≤ gammaTriangleConst 1 := by
    rw [gammaTriangleConst_eq_of_one_le (by norm_num : (1 : ℝ) ≤ 1)]
    norm_num [gammaTriangleConst]
  have hKsq : (1 : ℝ) ≤ gaugeAmplitudeConst d ^ 2 := one_le_pow₀ hK
  have hsum : (2 : ℝ) ≤ gaugeAmplitudeConst d + gaugeAmplitudeConst d ^ 2 := by
    calc 2 = 1 + 1 := by norm_num
      _ ≤ gaugeAmplitudeConst d + gaugeAmplitudeConst d ^ 2 := add_le_add hK hKsq
  have hsum1 : (1 : ℝ) ≤ gaugeAmplitudeConst d + gaugeAmplitudeConst d ^ 2 :=
    le_trans (by norm_num) hsum
  have h2g : (2 : ℝ) ≤ 2 * gammaTriangleConst 1 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hg1 (by norm_num : (0 : ℝ) ≤ 2)
  unfold localizationConst
  calc 2 = 2 * 1 := by ring
    _ ≤ (2 * gammaTriangleConst 1) * 1 := by simpa only [mul_one] using h2g
    _ ≤ (2 * gammaTriangleConst 1) *
        (gaugeAmplitudeConst d + gaugeAmplitudeConst d ^ 2) :=
      mul_le_mul_of_nonneg_left hsum1
        (mul_nonneg (by norm_num) (le_trans zero_le_one hg1))

private theorem rpow_neg_two_of_pos {nu : ℝ} (hnu : 0 < nu) :
    nu ^ (-(2 : ℝ)) = nu⁻¹ * nu⁻¹ := by
  rw [Real.rpow_neg hnu.le, Real.rpow_two, pow_two, mul_inv]

private theorem sqrt_three_rpow_sub (a : ℕ) :
    Real.sqrt ((3 : ℝ) ^ (-((a : ℕ) : ℝ))) =
      (3 : ℝ) ^ (-(((a : ℕ) : ℝ) / 2)) := by
  have h3 : (0 : ℝ) ≤ 3 := by norm_num
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul h3]
  rw [show ((-((a : ℕ) : ℝ)) * (1 / 2 : ℝ)) =
      -(((a : ℕ) : ℝ) / 2) from by ring]

private theorem isBigOWith_gammaSigma_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (A : ℝ) (hA : 0 ≤ A) :
    IndependentSums.IsBigOWith μ (IndependentSums.gammaSigma 1)
      (fun _ : Ω => (0 : ℝ)) A := by
  intro t ht
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  have hempty : IndependentSums.upperTailEvent (fun _ : Ω => (0 : ℝ)) (A * t) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro ω hω
    simp only [IndependentSums.mem_upperTailEvent] at hω
    exact absurd hω (not_lt.mpr (mul_nonneg hA ht0))
  rw [hempty, measureReal_empty]
  exact (inv_pos.mpr (Real.exp_pos _)).le

/-- The second localization conjunct, with the carrier and comparison
premises discharged for the cutoff pair. -/
theorem localizationConjunct2_proved (d : ℕ)
    (C : ℝ) (hCX : localizationConst d ≤ C) (hCY : localizationSkewConst d ≤ C)
    (nu : ℝ) (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (P : MeasureTheory.ProbabilityMeasure (ShellSeq d))
    (hJP : ShellLawPrefix d P) (hJ1 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (m n L : ℕ) (hnm : n ≤ m) (hmL : m ≤ L)
    (U : Book.Ch02.Domain d)
    (hU : (U : Set (Vec d)) ⊆ openCubeSet (originCube d (n : ℤ))) :
    ∃ Y : ShellSeq d → ℝ,
      Measurable Y ∧
      IndependentSums.IsBigO P.toMeasure (gammaSigma 1) Y
        (C * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((m - n : ℕ) : ℝ) / 2))) ∧
      ∀ (omega : ShellSeq d) (p q : Vec d),
        2 * vecDot p (matVecMul
            (kappaCoarse (U : Set (Vec d)) (coefficientCutoff nu omega L).toCoeffField -
              kappaCoarse (U : Set (Vec d)) (coefficientCutoff nu omega m).toCoeffField -
              volumeAverageMat (U : Set (Vec d))
                (fun y => finiteShellIncrement omega m L y)) q) ≤
          Y omega *
            (vecDot p (matVecMul
                (sigmaStarCoarse (U : Set (Vec d))
                  (coefficientCutoff nu omega L).toCoeffField) p) +
              vecDot q (matVecMul
                (sigmaCoarse (U : Set (Vec d))
                  (coefficientCutoff nu omega L).toCoeffField) q)) := by
  let Z : ShellSeq d → ℝ := fun omega =>
    Real.sqrt (2 * localizationD nu n m L omega +
      localizationD nu n m L omega ^ 2)
  have hθm : Measurable (localizationTheta nu n m L : ShellSeq d → ℝ) :=
    measurable_localizationTheta nu n m L
  have hDm : Measurable (localizationD nu n m L : ShellSeq d → ℝ) := by
    unfold localizationD
    exact hθm.mul (measurable_const.add hθm)
  have hZmeas : Measurable Z := by
    apply Real.continuous_sqrt.measurable.comp
    exact (measurable_const.mul hDm).add (hDm.pow measurable_const)
  have hA0 : 0 ≤ C * nu ^ (-(2 : ℝ)) *
      Real.sqrt ((3 : ℝ) ^ (-((m - n : ℕ) : ℝ))) := by
    exact mul_nonneg (mul_nonneg (le_trans (localizationConst_nonneg d) hCX)
      (Real.rpow_nonneg hnu.le _)) (Real.sqrt_nonneg _)
  refine ⟨Z, hZmeas, ?_, ?_⟩
  · by_cases hmain : 0 < d ∧ m < L
    · obtain ⟨hd, hmLlt⟩ := hmain
      have hT0 : 0 ≤ (3 : ℝ) ^ (-((m - n : ℕ) : ℝ)) := Real.rpow_nonneg (by norm_num) _
      have hTpos : 0 < (3 : ℝ) ^ (-((m - n : ℕ) : ℝ)) :=
        Real.rpow_pos_of_pos (by norm_num) _
      have hT1 : (3 : ℝ) ^ (-((m - n : ℕ) : ℝ)) ≤ 1 := by
        rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_natCast]
        exact (inv_le_one₀ (pow_pos (by norm_num : (0 : ℝ) < 3) (m - n))).2
          (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3))
      have hT2sq : (Real.sqrt ((3 : ℝ) ^ (-((m - n : ℕ) : ℝ)))) ^ 2 =
          (3 : ℝ) ^ (-((m - n : ℕ) : ℝ)) :=
        Real.sq_sqrt hT0
      have hT2 : 0 ≤ Real.sqrt ((3 : ℝ) ^ (-((m - n : ℕ) : ℝ))) :=
        Real.sqrt_nonneg _
      have hT2le1 : Real.sqrt ((3 : ℝ) ^ (-((m - n : ℕ) : ℝ))) ≤ 1 := by
        by_contra hcon
        push Not at hcon
        have h1t : (1 : ℝ) <
            (Real.sqrt ((3 : ℝ) ^ (-((m - n : ℕ) : ℝ)))) ^ 2 :=
          one_lt_pow₀ hcon (by norm_num : (2 : ℕ) ≠ 0)
        rw [hT2sq] at h1t
        exact (not_lt_of_ge hT1) h1t
      have hTle : (3 : ℝ) ^ (-((m - n : ℕ) : ℝ)) ≤
          Real.sqrt ((3 : ℝ) ^ (-((m - n : ℕ) : ℝ))) := by
        have hq := mul_le_mul_of_nonneg_left hT2le1 hT2
        calc
          (3 : ℝ) ^ (-((m - n : ℕ) : ℝ)) =
              (Real.sqrt ((3 : ℝ) ^ (-((m - n : ℕ) : ℝ)))) ^ 2 := hT2sq.symm
          _ = Real.sqrt ((3 : ℝ) ^ (-((m - n : ℕ) : ℝ))) *
              Real.sqrt ((3 : ℝ) ^ (-((m - n : ℕ) : ℝ))) := by rw [pow_two]
          _ ≤ Real.sqrt ((3 : ℝ) ^ (-((m - n : ℕ) : ℝ))) * 1 := hq
          _ = Real.sqrt ((3 : ℝ) ^ (-((m - n : ℕ) : ℝ))) := by rw [mul_one]
      have hpair := localizationWitness_pair_isBigO P hJ3 nu hnu hnu1 n m L hnm hmL
      have hXnn : ∀ omega : ShellSeq d, 0 ≤ localizationWitness nu n m L omega :=
        fun omega => localizationWitness_nonneg hnu.le n m L omega
      have hXwith : IsBigOWith P.toMeasure (gammaSigma 1)
          (fun omega => 2 * localizationD nu n m L omega)
          (localizationConst d * nu ^ (-(2 : ℝ)) *
            (3 : ℝ) ^ (-((m - n : ℕ) : ℝ))) := by
        exact (isBigOWith_iff_isBigO_of_nonneg hXnn).2 hpair.1
      have hDwith := isBigOWith_half_double hXwith
      have hC0 : 0 < localizationConst d :=
        lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (localizationConst_ge_two hd)
      have hqpos : 0 < nu ^ (-(2 : ℝ)) := Real.rpow_pos_of_pos hnu _
      have hBpos : 0 <
          (localizationConst d * nu ^ (-(2 : ℝ)) *
            (3 : ℝ) ^ (-((m - n : ℕ) : ℝ))) / 2 := by positivity
      have hCpos : 0 < C := lt_of_lt_of_le hC0 hCX
      have hq1 : (1 : ℝ) ≤ nu ^ (-(2 : ℝ)) := by
        rw [rpow_neg_two_of_pos hnu]
        have hi : (1 : ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
        simpa only [one_mul] using
          mul_le_mul hi hi zero_le_one (inv_nonneg.2 hnu.le)
      have hC0sq : 2 * localizationConst d ≤ localizationConst d ^ 2 := by
        have h := mul_le_mul_of_nonneg_right (localizationConst_ge_two hd)
          (localizationConst_nonneg d)
        simpa only [pow_two] using h
      have hC0C : localizationConst d ^ 2 ≤ C ^ 2 := by
        rw [pow_two, pow_two]
        exact mul_le_mul hCX hCX (localizationConst_nonneg d) hCpos.le
      have hquad : 2 * localizationConst d ≤ C ^ 2 * nu ^ (-(2 : ℝ)) := by
        calc 2 * localizationConst d ≤ localizationConst d ^ 2 := hC0sq
          _ ≤ localizationConst d ^ 2 * nu ^ (-(2 : ℝ)) := by
            simpa only [mul_one] using
              mul_le_mul_of_nonneg_left hq1 (sq_nonneg (localizationConst d))
          _ ≤ C ^ 2 * nu ^ (-(2 : ℝ)) :=
            mul_le_mul_of_nonneg_right hC0C (Real.rpow_nonneg hnu.le _)
      have h1 : 4 * ((localizationConst d * nu ^ (-(2 : ℝ)) *
          (3 : ℝ) ^ (-((m - n : ℕ) : ℝ))) / 2) ≤
          (C * nu ^ (-(2 : ℝ)) *
            Real.sqrt ((3 : ℝ) ^ (-((m - n : ℕ) : ℝ)))) ^ 2 := by
        rw [rpow_neg_two_of_pos hnu]
        have hquad' : 2 * localizationConst d ≤
            C ^ 2 * (nu⁻¹ * nu⁻¹) := by
          simpa only [rpow_neg_two_of_pos hnu] using hquad
        calc 4 * (localizationConst d * (nu⁻¹ * nu⁻¹) *
              (3 : ℝ) ^ (-((m - n : ℕ) : ℝ)) / 2) =
              (2 * localizationConst d) * (nu⁻¹ * nu⁻¹) *
                (3 : ℝ) ^ (-((m - n : ℕ) : ℝ)) := by ring
          _ ≤ C ^ 2 * (nu⁻¹ * nu⁻¹) ^ 2 *
                (3 : ℝ) ^ (-((m - n : ℕ) : ℝ)) := by
            have hqnonneg : 0 ≤ nu⁻¹ * nu⁻¹ :=
              mul_nonneg (inv_nonneg.2 hnu.le) (inv_nonneg.2 hnu.le)
            calc
              (2 * localizationConst d) * (nu⁻¹ * nu⁻¹) *
                  (3 : ℝ) ^ (-((m - n : ℕ) : ℝ)) ≤
                  ((C ^ 2 * (nu⁻¹ * nu⁻¹)) * (nu⁻¹ * nu⁻¹)) *
                    (3 : ℝ) ^ (-((m - n : ℕ) : ℝ)) := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hquad' hqnonneg) hT0
              _ = C ^ 2 * (nu⁻¹ * nu⁻¹) ^ 2 *
                    (3 : ℝ) ^ (-((m - n : ℕ) : ℝ)) := by ring
          _ = C ^ 2 * (nu⁻¹ * nu⁻¹) ^ 2 *
                (Real.sqrt ((3 : ℝ) ^ (-((m - n : ℕ) : ℝ)))) ^ 2 := by
            rw [hT2sq]
          _ = (C * (nu⁻¹ * nu⁻¹) *
                Real.sqrt ((3 : ℝ) ^ (-((m - n : ℕ) : ℝ)))) ^ 2 := by
            ring
      have hsqrt2 : Real.sqrt 2 / 2 ≤ (1 : ℝ) := by
        have hs : Real.sqrt 2 ≤ 2 := by
          calc
            Real.sqrt 2 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
            _ = 2 := (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2
              (by norm_num)
        exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
          (by simpa only [one_mul] using hs)
      have hCqT : localizationConst d * nu ^ (-(2 : ℝ)) *
          (3 : ℝ) ^ (-((m - n : ℕ) : ℝ)) ≤
          C * nu ^ (-(2 : ℝ)) *
            Real.sqrt ((3 : ℝ) ^ (-((m - n : ℕ) : ℝ))) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_right hCX (Real.rpow_nonneg hnu.le _)) hTle
          hT0
          (mul_nonneg hCpos.le (Real.rpow_nonneg hnu.le _))
      have h2 : Real.sqrt 2 * ((localizationConst d * nu ^ (-(2 : ℝ)) *
          (3 : ℝ) ^ (-((m - n : ℕ) : ℝ))) / 2) ≤
          C * nu ^ (-(2 : ℝ)) *
            Real.sqrt ((3 : ℝ) ^ (-((m - n : ℕ) : ℝ))) := by
        rw [show Real.sqrt 2 * (localizationConst d * nu ^ (-(2 : ℝ)) *
            (3 : ℝ) ^ (-((m - n : ℕ) : ℝ)) / 2) =
            (Real.sqrt 2 / 2) * (localizationConst d * nu ^ (-(2 : ℝ)) *
              (3 : ℝ) ^ (-((m - n : ℕ) : ℝ))) by ring]
        have hXnonneg : 0 ≤ localizationConst d * nu ^ (-(2 : ℝ)) *
            (3 : ℝ) ^ (-((m - n : ℕ) : ℝ)) :=
          mul_nonneg
            (mul_nonneg (localizationConst_nonneg d)
              (Real.rpow_nonneg hnu.le _)) hT0
        have hfirst : (Real.sqrt 2 / 2) *
            (localizationConst d * nu ^ (-(2 : ℝ)) *
              (3 : ℝ) ^ (-((m - n : ℕ) : ℝ))) ≤
            localizationConst d * nu ^ (-(2 : ℝ)) *
              (3 : ℝ) ^ (-((m - n : ℕ) : ℝ)) := by
          simpa only [one_mul] using
            (mul_le_mul_of_nonneg_right hsqrt2 hXnonneg)
        exact hfirst.trans hCqT
      have htail := isBigOWith_gammaSigma_sqrt_quadratic
        (D := localizationD nu n m L) (hDnn := fun omega => by
          unfold localizationD
          exact mul_nonneg (localizationTheta_nonneg nu hnu.le n m L omega)
            (by linarith only [localizationTheta_nonneg nu hnu.le n m L omega]))
        hDwith hBpos
        (C * nu ^ (-(2 : ℝ)) * Real.sqrt ((3 : ℝ) ^ (-((m - n : ℕ) : ℝ))))
        (by positivity) h1 h2
      have htailO : IsBigO P.toMeasure (gammaSigma 1) Z
          (C * nu ^ (-(2 : ℝ)) * Real.sqrt ((3 : ℝ) ^ (-((m - n : ℕ) : ℝ)))) := by
        exact (isBigOWith_iff_isBigO_of_nonneg (fun omega => Real.sqrt_nonneg _)).1 htail
      change IsBigO P.toMeasure (gammaSigma 1)
        (fun omega => Real.sqrt (2 * localizationD nu n m L omega +
          localizationD nu n m L omega ^ 2))
        (C * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((m - n : ℕ) : ℝ) / 2)))
      simpa only [sqrt_three_rpow_sub] using htailO
    ·
      have hθzero : ∀ omega : ShellSeq d, localizationTheta nu n m L omega = 0 := by
        rcases Nat.lt_or_ge d 1 with hdl | hd1
        · have hd0 : d = 0 := Nat.lt_one_iff.mp hdl
          subst d
          intro omega
          unfold localizationTheta matrixOperatorNorm_diamConst
          norm_num
        · have hnot : ¬ m < L := by
            intro hmlt
            exact hmain ⟨by exact hd1, hmlt⟩
          have hmEq : m = L := Nat.le_antisymm hmL (Nat.le_of_not_gt hnot)
          subst m
          intro omega
          unfold localizationTheta upperShellDerivGauge
          simp only [Finset.Ioc_self, Finset.sum_empty]
          ring
      have hZzero : Z = fun _ => (0 : ℝ) := by
        funext omega
        unfold Z localizationD
        rw [hθzero omega]
        norm_num
      rw [hZzero]
      exact (isBigOWith_iff_isBigO_of_nonneg (fun _ => by positivity)).1
        (isBigOWith_gammaSigma_zero
          (C * nu ^ (-(2 : ℝ)) *
            (3 : ℝ) ^ (-(((m - n : ℕ) : ℝ) / 2)))
          (mul_nonneg (mul_nonneg (le_trans (localizationConst_nonneg d) hCX)
            (Real.rpow_nonneg hnu.le _)) (Real.rpow_nonneg (by norm_num) _)))
  · intro omega p q
    have hpos := cutoffCarrierPositivity nu hnu omega L U
    have hbil := two_vecDot_matVecMul_le_sqrt_mul_inv
      (A := sigmaStarCoarse (U : Set (Vec d))
        (coefficientCutoff nu omega L).toCoeffField)
      (E := sigmaCoarse (U : Set (Vec d))
        (coefficientCutoff nu omega L).toCoeffField)
      hpos.1 hpos.2.1 hpos.2.2
      (cutoffConjugatedComparison nu hnu n m L hmL U hU omega) p q
    have hscalar : localizationD nu n m L omega *
        (2 + localizationD nu n m L omega) =
        2 * localizationD nu n m L omega + localizationD nu n m L omega ^ 2 := by
      ring
    rw [hscalar] at hbil
    exact hbil

end

end SuperdiffusionCLT.Section2.Localization
