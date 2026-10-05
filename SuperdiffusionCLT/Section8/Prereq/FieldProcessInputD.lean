/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.FieldProcessInputC
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.Vanishing
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The localized resolvent-tail profile of a split datum with logarithmic bounds

The logarithmic local constants give a pointwise log-subexponential profile.  This module keeps
the algebraic prefactor explicit.  Everything is stated for a localized split datum `S` of an
analytic datum `A` together with logarithmic-growth bounds `T`, so that it applies to the
marginal field through `FieldInputData.logGrowthBounds`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization Homogenization.Book.Ch02 MeasureTheory Set
open SuperdiffusionCLT.Section8.DivergenceForm
open SuperdiffusionCLT.Section8.DivergenceForm.Decay
open SuperdiffusionCLT.Section8.Common.Regularity.Ported
open MarkovProcess.Semigroup
open scoped Matrix.Norms.Elementwise

noncomputable section

/-- A log-subexponential profile with an explicit algebraic prefactor. -/
def logSubexponentialProfile (C c : ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  C * (1 + max s 0) ^ n *
    Real.exp (-c * max s 0 / (1 + Real.log (1 + max s 0)))

/-- The profile is nonnegative when its amplitude is nonnegative. -/
theorem logSubexponentialProfile_nonneg {C : ℝ} (hC : 0 ≤ C)
    (c : ℝ) (n : ℕ) (s : ℝ) :
    0 ≤ logSubexponentialProfile C c n s := by
  unfold logSubexponentialProfile
  positivity



section Profile

variable {d : ℕ} [NeZero d] {A : WholeSpaceAnalyticData d} {S : WholeSpaceLocalizedSplitData A}

namespace LogGrowthBounds

/-- The point-dependent logarithmic weight. -/
def fieldInput_pointLogWeight (x : Vec d) : ℝ :=
  fieldInput_logWeight (1 + euclideanNorm x)

/-- The radius-independent coefficient in the logarithmic upper bound for the
localized weighted estimate. -/
def upperBase (S : WholeSpaceLocalizedSplitData A) (x : Vec d) : ℝ :=
  localizedAgmonUpper A.nu 1
    (S.roughBound x 0)
    (S.smoothDivBound x 0)

theorem upperBase_pos (S : WholeSpaceLocalizedSplitData A) (x : Vec d) :
    0 < upperBase S x := by
  exact localizedAgmonUpper_pos A.hnu
    (S.roughBound_nonneg x 0 (by norm_num))
    (S.smoothDivBound_nonneg x 0 (by norm_num))

omit [NeZero d] in
private theorem fieldInput_logWeight_observation_le_mul {x : Vec d} {r s : ℝ}
    (hr : 0 ≤ r) (hrs : r ≤ s) :
    fieldInput_logWeight (fieldInput_obsRadius x r) ≤
      fieldInput_pointLogWeight x * fieldInput_logWeight (1 + s) := by
  have hs : 0 ≤ s := hr.trans hrs
  have hx : 0 ≤ euclideanNorm x := euclideanNorm_nonneg x
  have hobs : fieldInput_obsRadius x r ≤
      (1 + euclideanNorm x) * (1 + s) := by
    unfold fieldInput_obsRadius
    nlinarith only [hx, hs, hrs,
      mul_nonneg hx hs]
  have hobsPos : 0 < fieldInput_obsRadius x r := by
    unfold fieldInput_obsRadius
    linarith only [hx, hr]
  have hxPos : 0 < 1 + euclideanNorm x := by linarith only [hx]
  have hsPos : 0 < 1 + s := by linarith only [hs]
  have hlog := Real.strictMonoOn_log.monotoneOn hobsPos
    (mul_pos hxPos hsPos) hobs
  rw [Real.log_mul hxPos.ne' hsPos.ne'] at hlog
  have hlogx : 0 ≤ Real.log (1 + euclideanNorm x) :=
    Real.log_nonneg (by linarith only [hx])
  have hlogs : 0 ≤ Real.log (1 + s) :=
    Real.log_nonneg (by linarith only [hs])
  change 1 + Real.log (fieldInput_obsRadius x r) ≤
    (1 + Real.log (1 + euclideanNorm x)) * (1 + Real.log (1 + s))
  nlinarith only [hlog, hlogx, hlogs, mul_nonneg hlogx hlogs]

private theorem roughBound_le_mul (T : LogGrowthBounds S) {x : Vec d} {r s : ℝ}
    (hr : 0 ≤ r) (hrs : r ≤ s) :
    S.roughBound x r ≤
      S.roughBound x 0 * fieldInput_logWeight (1 + s) := by
  have hw := fieldInput_logWeight_observation_le_mul (x := x) hr hrs
  rw [T.rough_eq x r, T.rough_eq x 0]
  have hmul := mul_le_mul_of_nonneg_left hw T.cs_nonneg
  simpa only [fieldInput_pointLogWeight, fieldInput_obsRadius, add_zero, mul_assoc] using hmul

private theorem smoothDivBound_le_mul (T : LogGrowthBounds S) {x : Vec d} {r s : ℝ}
    (hr : 0 ≤ r) (hrs : r ≤ s) :
    S.smoothDivBound x r ≤
      S.smoothDivBound x 0 * fieldInput_logWeight (1 + s) := by
  have hw := fieldInput_logWeight_observation_le_mul (x := x) hr hrs
  rw [T.smooth_eq x r, T.smooth_eq x 0]
  have hbase : 0 ≤ Real.sqrt d * (d : ℝ) * T.cg :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg d) (Nat.cast_nonneg d)) T.cg_nonneg
  have hmul := mul_le_mul_of_nonneg_left hw hbase
  simpa only [fieldInput_pointLogWeight, fieldInput_obsRadius, add_zero, mul_assoc] using hmul

/-- The effective upper constant at radius `r = s / sqrt mu` is at most its
point-dependent base times `1 + log (1+s)`, uniformly for `mu ≥ 1`. -/
theorem localizedUpper_le (T : LogGrowthBounds S) (x : Vec d)
    {mu r s : ℝ} (hmu : 1 ≤ mu) (hr : 0 ≤ r) (hrs : r ≤ s) :
    localizedAgmonUpper A.nu mu
        (S.roughBound x r)
        (S.smoothDivBound x r) ≤
      upperBase S x * fieldInput_logWeight (1 + s) := by
  have hs : 0 ≤ s := hr.trans hrs
  have hwpos : 0 < fieldInput_logWeight (1 + s) :=
    fieldInput_logWeight_pos (by linarith only [hs])
  have hwone : 1 ≤ fieldInput_logWeight (1 + s) := by
    unfold fieldInput_logWeight
    have hlog : 0 ≤ Real.log (1 + s) :=
      Real.log_nonneg (by linarith only [hs])
    linarith only [hlog]
  have hKs := roughBound_le_mul T (x := x) hr hrs
  have hKl := smoothDivBound_le_mul T (x := x) hr hrs
  have hnu0 : 0 ≤ A.nu := A.hnu.le
  have hdiv : A.nu / mu ≤ A.nu := by
    exact div_le_self hnu0 hmu
  have hsqrt : Real.sqrt (A.nu / mu) ≤ Real.sqrt A.nu :=
    Real.sqrt_le_sqrt hdiv
  have hKl0 := S.smoothDivBound_nonneg x 0 (by norm_num)
  unfold upperBase localizedAgmonUpper
  have hsmooth : 2 * S.smoothDivBound x r *
      Real.sqrt (A.nu / mu) ≤
      2 * (S.smoothDivBound x 0 *
        fieldInput_logWeight (1 + s)) * Real.sqrt A.nu := by
    calc
      2 * S.smoothDivBound x r * Real.sqrt (A.nu / mu) ≤
          2 * (S.smoothDivBound x 0 *
            fieldInput_logWeight (1 + s)) * Real.sqrt (A.nu / mu) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hKl (by norm_num))
          (Real.sqrt_nonneg _)
      _ ≤ 2 * (S.smoothDivBound x 0 *
            fieldInput_logWeight (1 + s)) * Real.sqrt A.nu :=
        mul_le_mul_of_nonneg_left hsqrt
          (mul_nonneg (by positivity) (mul_nonneg hKl0 hwpos.le))
  have hinside :
      A.nu + S.roughBound x r +
          2 * S.smoothDivBound x r * Real.sqrt (A.nu / mu) ≤
        (A.nu + S.roughBound x 0 +
          2 * S.smoothDivBound x 0 * Real.sqrt A.nu) *
            fieldInput_logWeight (1 + s) := by
    calc
      A.nu + S.roughBound x r +
          2 * S.smoothDivBound x r * Real.sqrt (A.nu / mu) ≤
        A.nu + S.roughBound x 0 * fieldInput_logWeight (1 + s) +
          2 * (S.smoothDivBound x 0 *
            fieldInput_logWeight (1 + s)) * Real.sqrt A.nu :=
        add_le_add (add_le_add le_rfl hKs) hsmooth
      _ ≤ A.nu * fieldInput_logWeight (1 + s) +
          S.roughBound x 0 * fieldInput_logWeight (1 + s) +
          2 * (S.smoothDivBound x 0 *
            fieldInput_logWeight (1 + s)) * Real.sqrt A.nu := by
        have hnuScale : A.nu ≤ A.nu * fieldInput_logWeight (1 + s) := by
          simpa only [mul_one] using
            (mul_le_mul_of_nonneg_left hwone A.hnu.le)
        exact add_le_add (add_le_add
          hnuScale le_rfl) le_rfl
      _ = (A.nu + S.roughBound x 0 +
          2 * S.smoothDivBound x 0 * Real.sqrt A.nu) *
            fieldInput_logWeight (1 + s) := by ring
  simpa only [div_one, mul_assoc] using
    (mul_le_mul_of_nonneg_left hinside (Real.sqrt_nonneg 2))

/-- A positive lower floor for the dimensionless freezing radius when the
outer dimensionless scale is beyond one and the mass is at least one. -/
def innerFloor (S : WholeSpaceLocalizedSplitData A) (x : Vec d) : ℝ :=
  min (S.freezingRadius x)
    (1 / 2 : ℝ)

theorem innerFloor_pos (S : WholeSpaceLocalizedSplitData A) (x : Vec d) :
    0 < innerFloor S x := by
  exact lt_min
    (S.freezingRadius_pos x)
    (by norm_num)

/-- The pointwise log-subexponential decay rate. -/
def decayRate (S : WholeSpaceLocalizedSplitData A) (x : Vec d) : ℝ :=
  agmonTailRate d A.nu (upperBase S x) (1 / 2 : ℝ)


/-- The explicit algebraic amplitude.  Its two summands respectively control
the averaged/gradient terms and the bounded-forcing term of the tail estimate by freezing. -/
def algebraicAmplitude (S : WholeSpaceLocalizedSplitData A) (x : Vec d) : ℝ :=
  (agmonTailL2Coefficient d A.nu (upperBase S x) +
      agmonTailGradientCoefficient d A.nu
        (upperBase S x) (1 / 2 : ℝ)) /
      innerFloor S x ^ d +
    4 * agmonTailForcingCoefficient d (1 / 2 : ℝ) / A.nu

/-- The explicit log-subexponential profile of the localized tail. -/
def tailProfile (S : WholeSpaceLocalizedSplitData A) (x : Vec d) : ℝ → ℝ :=
  logSubexponentialProfile (algebraicAmplitude S x)
    (decayRate S x) (d + 1)

theorem algebraicAmplitude_nonneg (S : WholeSpaceLocalizedSplitData A) (x : Vec d) :
    0 ≤ algebraicAmplitude S x := by
  have hB := (upperBase_pos S x).le
  have hb := (innerFloor_pos S x).le
  have h1 := agmonTailL2Coefficient_nonneg d (lam := A.nu) hB
  have h2 := agmonTailGradientCoefficient_nonneg d
    (lam := A.nu) (alpha := (1 / 2 : ℝ)) A.hnu hB
  have h3 := agmonTailForcingCoefficient_nonneg d (1 / 2 : ℝ)
  unfold algebraicAmplitude
  exact add_nonneg
    (div_nonneg (add_nonneg h1 h2) (pow_nonneg hb d))
    (div_nonneg (mul_nonneg (by norm_num) h3) A.hnu.le)

theorem tailProfile_nonneg (S : WholeSpaceLocalizedSplitData A) (x : Vec d) (s : ℝ) :
    0 ≤ tailProfile S x s :=
  logSubexponentialProfile_nonneg (algebraicAmplitude_nonneg S x) _ _ _

private theorem innerFloor_le_scaledClipped (S : WholeSpaceLocalizedSplitData A) (x : Vec d)
    {mu s : ℝ} (hmu : 1 ≤ mu) (hs : 1 ≤ s) :
    innerFloor S x ≤
      Real.sqrt mu *
        S.clippedFreezingRadius x
          (s / Real.sqrt mu) := by
  have hmu0 : 0 ≤ mu := zero_le_one.trans hmu
  have hsqrt : 1 ≤ Real.sqrt mu := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hmu
  have hsqrtPos : 0 < Real.sqrt mu := zero_lt_one.trans_le hsqrt
  have hR0 : 0 < S.freezingRadius x :=
    S.freezingRadius_pos x
  rw [innerFloor, WholeSpaceLocalizedSplitData.clippedFreezingRadius,
    mul_min_of_nonneg _ _ (Real.sqrt_nonneg mu)]
  have hleft : S.freezingRadius x ≤
      Real.sqrt mu * S.freezingRadius x := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hsqrt hR0.le
  have hright : (1 / 2 : ℝ) ≤
      Real.sqrt mu * (s / Real.sqrt mu / 2) := by
    rw [show Real.sqrt mu * (s / Real.sqrt mu / 2) = s / 2 by
      field_simp]
    linarith only [hs]
  exact min_le_min hleft hright

private theorem scaledClipped_le_half (S : WholeSpaceLocalizedSplitData A) (x : Vec d)
    {mu s : ℝ} (hmu : 0 < mu) :
    Real.sqrt mu *
        S.clippedFreezingRadius x
          (s / Real.sqrt mu) ≤ s / 2 := by
  have hsqrtPos : 0 < Real.sqrt mu := Real.sqrt_pos.2 hmu
  have hclip := S.clippedFreezingRadius_le_half
    x (s / Real.sqrt mu)
  have hmul := mul_le_mul_of_nonneg_left hclip hsqrtPos.le
  calc
    Real.sqrt mu *
        S.clippedFreezingRadius x
          (s / Real.sqrt mu) ≤ Real.sqrt mu * (s / Real.sqrt mu / 2) := hmul
    _ = s / 2 := by field_simp

private theorem fieldInput_logWeight_one_add_le {s : ℝ} (hs : 0 ≤ s) :
    fieldInput_logWeight (1 + s) ≤ 1 + s := by
  unfold fieldInput_logWeight
  have hlog := Real.log_le_sub_one_of_pos (show 0 < 1 + s by positivity)
  linarith only [hlog]

omit [NeZero d] in
private theorem agmonTailL2Coefficient_le_scale {lam L B w : ℝ}
    (hLB : L ≤ B * w) :
    agmonTailL2Coefficient d lam L ≤
      agmonTailL2Coefficient d lam B * w := by
  have hscale : ∀ T : ℝ, agmonTailL2Coefficient d lam T =
      agmonTailL2Coefficient d lam 1 * T := by
    intro T
    unfold agmonTailL2Coefficient
    ring
  rw [hscale L, hscale B, mul_assoc]
  exact mul_le_mul_of_nonneg_left hLB
    (agmonTailL2Coefficient_nonneg d (lam := lam) (by norm_num))

private theorem agmonTailGradientCoefficient_le_scale
    {lam L B w alpha : ℝ} (hlam : 0 < lam) (hLB : L ≤ B * w) :
    agmonTailGradientCoefficient d lam L alpha ≤
      agmonTailGradientCoefficient d lam B alpha * w := by
  have hscale : ∀ T : ℝ, agmonTailGradientCoefficient d lam T alpha =
      agmonTailGradientCoefficient d lam 1 alpha * T := by
    intro T
    unfold agmonTailGradientCoefficient
    ring
  rw [hscale L, hscale B, mul_assoc]
  exact mul_le_mul_of_nonneg_left hLB
    (agmonTailGradientCoefficient_nonneg d hlam (by norm_num))

omit [NeZero d] in
private theorem agmonTailRate_div_logWeight_le
    {lam L B w alpha : ℝ} (hlam : 0 < lam) (hL : 0 < L)
    (hB : 0 < B) (hw : 0 < w) (halpha : 0 < alpha)
    (hLB : L ≤ B * w) :
    agmonTailRate d lam B alpha / w ≤ agmonTailRate d lam L alpha := by
  let K : ℝ := 3 * Real.sqrt lam / (16 * Real.sqrt 2)
  let Q : ℝ := alpha / (alpha + (d : ℝ) / 2)
  have hK : 0 < K := by
    unfold K
    positivity
  have hQ : 0 < Q := by
    unfold Q
    positivity
  have hdiv : K / (B * w) ≤ K / L :=
    div_le_div_of_nonneg_left hK.le hL hLB
  have hmul := mul_le_mul_of_nonneg_right hdiv hQ.le
  have hrateB : agmonTailRate d lam B alpha = K / B * Q := by
    unfold agmonTailRate K Q
    field_simp
  have hrateL : agmonTailRate d lam L alpha = K / L * Q := by
    unfold agmonTailRate K Q
    field_simp
  rw [hrateB, hrateL]
  convert hmul using 1
  field_simp

omit [NeZero d] in
private theorem rpow_ratio_le_div_pow {b s s₀ q : ℝ}
    (hb : 0 < b) (hbhalf : b ≤ 1 / 2) (hs : 1 < s) (hbs₀ : b ≤ s₀)
    (hq0 : 0 ≤ q) (hqd : q ≤ d) :
    (s / (2 * s₀)) ^ q ≤ (s / b) ^ d := by
  have hs0 : 0 < s := one_pos.trans hs
  have hs₀ : 0 < s₀ := hb.trans_le hbs₀
  have hden : b ≤ 2 * s₀ := by
    nlinarith only [hbs₀, hb]
  have hratio : s / (2 * s₀) ≤ s / b :=
    div_le_div_of_nonneg_left hs0.le hb hden
  have hratio0 : 0 ≤ s / (2 * s₀) := by positivity
  have hbase : 1 ≤ s / b := by
    apply (le_div_iff₀ hb).2
    linarith only [hs, hbhalf]
  calc
    (s / (2 * s₀)) ^ q ≤ (s / b) ^ q :=
      Real.rpow_le_rpow hratio0 hratio hq0
    _ ≤ (s / b) ^ (d : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hbase hqd
    _ = (s / b) ^ d := Real.rpow_natCast _ _

private theorem frozenTailBracket_le (T : LogGrowthBounds S) (x : Vec d)
    {mu s : ℝ} (hmu : 1 ≤ mu) (hs : 1 < s) :
    let r := s / Real.sqrt mu
    let L := localizedAgmonUpper A.nu mu
      (S.roughBound x r)
      (S.smoothDivBound x r)
    let s₀ := Real.sqrt mu *
      S.clippedFreezingRadius x r
    agmonTailL2Coefficient d A.nu L / |s| *
          (|s| / (2 * |s₀|)) ^ ((d : ℝ) / 2) +
        agmonTailGradientCoefficient d A.nu L (1 / 2 : ℝ) *
          (|s| / (2 * |s₀|)) ^ ((d : ℝ) / 2 - 1) +
        4 * agmonTailForcingCoefficient d (1 / 2 : ℝ) * s₀ ^ 2 / A.nu ≤
      algebraicAmplitude S x * (1 + s) ^ (d + 1) := by
  dsimp only
  let r := s / Real.sqrt mu
  let Ks := S.roughBound x r
  let Kl := S.smoothDivBound x r
  let L := localizedAgmonUpper A.nu mu Ks Kl
  let B := upperBase S x
  let w := fieldInput_logWeight (1 + s)
  let b := innerFloor S x
  let s₀ := Real.sqrt mu *
    S.clippedFreezingRadius x r
  have hmu0 : 0 < mu := zero_lt_one.trans_le hmu
  have hs0 : 0 < s := one_pos.trans hs
  have hsqrt : 1 ≤ Real.sqrt mu := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hmu
  have hr : 0 < r := div_pos hs0 (zero_lt_one.trans_le hsqrt)
  have hrs : r ≤ s := by
    apply (div_le_iff₀ (zero_lt_one.trans_le hsqrt)).2
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hsqrt hs0.le
  have hKs0 : 0 ≤ Ks := S.roughBound_nonneg _ _ hr.le
  have hKl0 : 0 ≤ Kl := S.smoothDivBound_nonneg _ _ hr.le
  have hL : 0 < L := localizedAgmonUpper_pos A.hnu hKs0 hKl0
  have hB : 0 < B := upperBase_pos S x
  have hw : 0 < w := fieldInput_logWeight_pos (by linarith only [hs0.le])
  have hwle : w ≤ 1 + s := fieldInput_logWeight_one_add_le hs0.le
  have hLB : L ≤ B * w := by
    exact localizedUpper_le T x hmu hr.le hrs
  have hb : 0 < b := innerFloor_pos S x
  have hbhalf : b ≤ 1 / 2 := min_le_right _ _
  have hs₀ : 0 < s₀ := mul_pos (Real.sqrt_pos.2 hmu0)
    (S.clippedFreezingRadius_pos x hr)
  have hbs₀ : b ≤ s₀ := by
    exact innerFloor_le_scaledClipped S x hmu hs.le
  have hs₀half : s₀ ≤ s / 2 := scaledClipped_le_half S x hmu0
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast A.hd
  have hq0 : 0 ≤ (d : ℝ) / 2 := by positivity
  have hqd : (d : ℝ) / 2 ≤ d := by linarith only [show 0 ≤ (d : ℝ) by positivity]
  have hp0 : 0 ≤ (d : ℝ) / 2 - 1 := by linarith only [hdR]
  have hpd : (d : ℝ) / 2 - 1 ≤ d := by
    linarith only [show 0 ≤ (d : ℝ) by positivity]
  have hratioQ : (s / (2 * s₀)) ^ ((d : ℝ) / 2) ≤ (s / b) ^ d :=
    rpow_ratio_le_div_pow hb hbhalf hs hbs₀ hq0 hqd
  have hratioP : (s / (2 * s₀)) ^ ((d : ℝ) / 2 - 1) ≤ (s / b) ^ d :=
    rpow_ratio_le_div_pow hb hbhalf hs hbs₀ hp0 hpd
  let A1 := agmonTailL2Coefficient d A.nu L
  let A2 := agmonTailGradientCoefficient d A.nu L (1 / 2 : ℝ)
  let A1B := agmonTailL2Coefficient d A.nu B
  let A2B := agmonTailGradientCoefficient d A.nu B (1 / 2 : ℝ)
  have hA1 : 0 ≤ A1 := agmonTailL2Coefficient_nonneg d hL.le
  have hA2 : 0 ≤ A2 :=
    agmonTailGradientCoefficient_nonneg d A.hnu hL.le
  have hA1B : 0 ≤ A1B := agmonTailL2Coefficient_nonneg d hB.le
  have hA2B : 0 ≤ A2B :=
    agmonTailGradientCoefficient_nonneg d A.hnu hB.le
  have hA1scale : A1 ≤ A1B * w :=
    agmonTailL2Coefficient_le_scale hLB
  have hA2scale : A2 ≤ A2B * w :=
    agmonTailGradientCoefficient_le_scale A.hnu hLB
  have hfirst : A1 / s * (s / (2 * s₀)) ^ ((d : ℝ) / 2) ≤
      A1 * (s / b) ^ d := by
    have hdiv : A1 / s ≤ A1 := div_le_self hA1 hs.le
    calc
      A1 / s * (s / (2 * s₀)) ^ ((d : ℝ) / 2) ≤
          A1 * (s / (2 * s₀)) ^ ((d : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right hdiv (Real.rpow_nonneg (by positivity) _)
      _ ≤ A1 * (s / b) ^ d :=
        mul_le_mul_of_nonneg_left hratioQ hA1
  have hsecond : A2 * (s / (2 * s₀)) ^ ((d : ℝ) / 2 - 1) ≤
      A2 * (s / b) ^ d :=
    mul_le_mul_of_nonneg_left hratioP hA2
  have hab : A1 + A2 ≤ (A1B + A2B) * w := by
    calc
      A1 + A2 ≤ A1B * w + A2B * w := add_le_add hA1scale hA2scale
      _ = (A1B + A2B) * w := by ring
  have hpowRatio : 0 ≤ (s / b) ^ d := pow_nonneg (by positivity) d
  have hradial : w * (s / b) ^ d ≤
      (1 + s) ^ (d + 1) / b ^ d := by
    have hspow : s ^ d ≤ (1 + s) ^ d :=
      pow_le_pow_left₀ hs0.le (by linarith only [hs0]) d
    have hprod : w * s ^ d ≤ (1 + s) ^ (d + 1) := by
      calc
        w * s ^ d ≤ (1 + s) * (1 + s) ^ d :=
          mul_le_mul hwle hspow (pow_nonneg hs0.le d) (by positivity)
        _ = (1 + s) ^ (d + 1) := by rw [pow_succ']
    rw [div_pow]
    rw [show w * (s ^ d / b ^ d) = (w * s ^ d) / b ^ d by ring]
    exact div_le_div_of_nonneg_right hprod (pow_nonneg hb.le d)
  have hmain :
      A1 / s * (s / (2 * s₀)) ^ ((d : ℝ) / 2) +
          A2 * (s / (2 * s₀)) ^ ((d : ℝ) / 2 - 1) ≤
        (A1B + A2B) / b ^ d * (1 + s) ^ (d + 1) := by
    calc
      A1 / s * (s / (2 * s₀)) ^ ((d : ℝ) / 2) +
          A2 * (s / (2 * s₀)) ^ ((d : ℝ) / 2 - 1) ≤
        (A1 + A2) * (s / b) ^ d := by
          nlinarith only [hfirst, hsecond]
      _ ≤ ((A1B + A2B) * w) * (s / b) ^ d :=
        mul_le_mul_of_nonneg_right hab hpowRatio
      _ ≤ (A1B + A2B) * ((1 + s) ^ (d + 1) / b ^ d) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hradial (add_nonneg hA1B hA2B)
      _ = (A1B + A2B) / b ^ d * (1 + s) ^ (d + 1) := by ring
  have hforce0 := agmonTailForcingCoefficient_nonneg d (1 / 2 : ℝ)
  have hsq : s₀ ^ 2 ≤ s ^ 2 := by
    calc
      s₀ ^ 2 ≤ (s / 2) ^ 2 := pow_le_pow_left₀ hs₀.le hs₀half 2
      _ ≤ s ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith only [hs0]) 2
  have hsPower : s ^ 2 ≤ (1 + s) ^ (d + 1) := by
    have hdNat : 2 ≤ d := A.hd
    calc
      s ^ 2 ≤ (1 + s) ^ 2 := pow_le_pow_left₀ hs0.le (by linarith only [hs0]) 2
      _ ≤ (1 + s) ^ (d + 1) :=
        pow_le_pow_right₀ (by linarith only [hs0]) (by omega)
  have hforce : 4 * agmonTailForcingCoefficient d (1 / 2 : ℝ) * s₀ ^ 2 / A.nu ≤
      (4 * agmonTailForcingCoefficient d (1 / 2 : ℝ) / A.nu) *
        (1 + s) ^ (d + 1) := by
    have hsq' := hsq.trans hsPower
    calc
      4 * agmonTailForcingCoefficient d (1 / 2 : ℝ) * s₀ ^ 2 / A.nu ≤
          4 * agmonTailForcingCoefficient d (1 / 2 : ℝ) *
            (1 + s) ^ (d + 1) / A.nu := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsq'
            (mul_nonneg (by norm_num) hforce0)) A.hnu.le
      _ = (4 * agmonTailForcingCoefficient d (1 / 2 : ℝ) / A.nu) *
          (1 + s) ^ (d + 1) := by ring
  rw [abs_of_pos hs0, abs_of_pos hs₀]
  change A1 / s * (s / (2 * s₀)) ^ ((d : ℝ) / 2) +
      A2 * (s / (2 * s₀)) ^ ((d : ℝ) / 2 - 1) +
      4 * agmonTailForcingCoefficient d (1 / 2 : ℝ) * s₀ ^ 2 / A.nu ≤ _
  unfold algebraicAmplitude
  change _ ≤ ((A1B + A2B) / b ^ d +
      4 * agmonTailForcingCoefficient d (1 / 2 : ℝ) / A.nu) *
        (1 + s) ^ (d + 1)
  calc
    _ ≤ (A1B + A2B) / b ^ d * (1 + s) ^ (d + 1) +
        (4 * agmonTailForcingCoefficient d (1 / 2 : ℝ) / A.nu) *
          (1 + s) ^ (d + 1) := add_le_add hmain hforce
    _ = _ := by ring

/-- The exact localized two-scale tail is bounded by the explicit
log-subexponential profile, uniformly in every mass `mu ≥ 1`. -/
theorem tail_le_profile (T : LogGrowthBounds S) (mu : PositiveShift) (x : Vec d)
    (hmu : 1 ≤ (mu : ℝ)) {s : ℝ} (hs : 1 < s) :
    S.tail mu x
        (s / Real.sqrt (mu : ℝ)) ≤
      tailProfile S x s := by
  let r := s / Real.sqrt (mu : ℝ)
  let Ks := S.roughBound x r
  let Kl := S.smoothDivBound x r
  let L := localizedAgmonUpper A.nu (mu : ℝ) Ks Kl
  let B := upperBase S x
  let w := fieldInput_logWeight (1 + s)
  let s₀ := Real.sqrt (mu : ℝ) *
    S.clippedFreezingRadius x r
  let P := agmonTailL2Coefficient d A.nu L / |s| *
          (|s| / (2 * |s₀|)) ^ ((d : ℝ) / 2) +
        agmonTailGradientCoefficient d A.nu L (1 / 2 : ℝ) *
          (|s| / (2 * |s₀|)) ^ ((d : ℝ) / 2 - 1) +
        4 * agmonTailForcingCoefficient d (1 / 2 : ℝ) * s₀ ^ 2 / A.nu
  have hmu0 : 0 < (mu : ℝ) := mu.property
  have hs0 : 0 < s := one_pos.trans hs
  have hsqrt : 0 < Real.sqrt (mu : ℝ) := Real.sqrt_pos.2 hmu0
  have hr : 0 < r := div_pos hs0 hsqrt
  have hKs : 0 ≤ Ks := S.roughBound_nonneg _ _ hr.le
  have hKl : 0 ≤ Kl := S.smoothDivBound_nonneg _ _ hr.le
  have hL : 0 < L := localizedAgmonUpper_pos A.hnu hKs hKl
  have hB : 0 < B := upperBase_pos S x
  have hw : 0 < w := fieldInput_logWeight_pos (by linarith only [hs0.le])
  have hrs : r ≤ s := by
    have hsqrtOne : 1 ≤ Real.sqrt (mu : ℝ) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt hmu
    apply (div_le_iff₀ hsqrt).2
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hsqrtOne hs0.le
  have hLB : L ≤ B * w :=
    localizedUpper_le T x hmu hr.le hrs
  have hrate : decayRate S x / w ≤
      agmonTailRate d A.nu L (1 / 2 : ℝ) := by
    exact agmonTailRate_div_logWeight_le A.hnu hL hB hw (by norm_num) hLB
  have hexp : Real.exp (-(agmonTailRate d A.nu L (1 / 2 : ℝ) * s)) ≤
      Real.exp (-(decayRate S x * s / w)) := by
    apply Real.exp_le_exp.2
    have hmul := mul_le_mul_of_nonneg_right hrate hs0.le
    calc
      -(agmonTailRate d A.nu L (1 / 2 : ℝ) * s) ≤
          -((decayRate S x / w) * s) := neg_le_neg hmul
      _ = -(decayRate S x * s / w) := by ring
  have hP : P ≤ algebraicAmplitude S x * (1 + s) ^ (d + 1) := by
    exact frozenTailBracket_le T x hmu hs
  have hprofilePoly : 0 ≤
      algebraicAmplitude S x * (1 + s) ^ (d + 1) :=
    mul_nonneg (algebraicAmplitude_nonneg S x)
      (pow_nonneg (by linarith only [hs0]) _)
  have hscale : Real.sqrt (mu : ℝ) * r = s := by
    unfold r
    field_simp
  unfold WholeSpaceLocalizedSplitData.tail
  rw [T.holder_eq]
  change agmonTailFunctionFrozen d A.nu L A.nu (1 / 2 : ℝ)
    (Real.sqrt (mu : ℝ) * r) s₀ ≤ _
  unfold agmonTailFunctionFrozen
  rw [hscale]
  change P * Real.exp (-(agmonTailRate d A.nu L (1 / 2 : ℝ) * s)) ≤ _
  calc
    P * Real.exp (-(agmonTailRate d A.nu L (1 / 2 : ℝ) * s)) ≤
        (algebraicAmplitude S x * (1 + s) ^ (d + 1)) *
          Real.exp (-(decayRate S x * s / w)) :=
      mul_le_mul hP hexp (Real.exp_pos _).le hprofilePoly
    _ = tailProfile S x s := by
      unfold tailProfile logSubexponentialProfile
      rw [max_eq_left hs0.le]
      unfold w fieldInput_logWeight
      congr 2
      ring

/-- The analytic minimal resolvent inherits the explicit pointwise
log-subexponential profile.  The estimate is uniform over the exhaustion
cubes used to define the minimal resolvent. -/
theorem mul_toReal_minimalResolvent_le_profile
    (T : LogGrowthBounds S)
    (mu : PositiveShift) (hmu : 1 ≤ (mu : ℝ))
    {f : Vec d → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, |f x| ≤ 1) {x : Vec d} {r : ℝ} (hr : 0 < r)
    (hs : 1 < Real.sqrt (mu : ℝ) * r)
    (hzero : ∀ y ∈ euclideanBall x r, f y = 0) :
    (mu : ℝ) *
        (A.analyticMinimalResolvent
          mu f hf hf1 x).toReal ≤
      tailProfile S x
        (Real.sqrt (mu : ℝ) * r) := by
  have hsqrt : 0 < Real.sqrt (mu : ℝ) := Real.sqrt_pos.2 mu.property
  have hscale :
      (Real.sqrt (mu : ℝ) * r) / Real.sqrt (mu : ℝ) = r := by
    field_simp
  calc
    (mu : ℝ) *
        (A.analyticMinimalResolvent
          mu f hf hf1 x).toReal ≤
        S.tail mu x r :=
      A.mul_toReal_analyticMinimalResolvent_le_localizedTail
          S mu hf hf0 hf1 hr hzero
    _ = S.tail mu x
          ((Real.sqrt (mu : ℝ) * r) / Real.sqrt (mu : ℝ)) := by rw [hscale]
    _ ≤ tailProfile S x
          (Real.sqrt (mu : ℝ) * r) :=
      tail_le_profile T mu x hmu hs

end LogGrowthBounds

/-! ## Satisfiability witnesses -/

/-- The profile bound applies to the marginal split datum of any admissible skew field. -/
example {nu : ℝ} {k : Vec d → Mat d} (D : FieldInputData d nu k) (mu : PositiveShift) (x : Vec d)
    (hmu : 1 ≤ (mu : ℝ)) {s : ℝ} (hs : 1 < s) :
    D.splitData.tail mu x (s / Real.sqrt (mu : ℝ)) ≤ LogGrowthBounds.tailProfile D.splitData x s :=
  D.logGrowthBounds.tail_le_profile mu x hmu hs

/-- A concrete admissible skew field exists (the zero field), and the profile is positive
there. -/
example (hd : 2 ≤ d) :
    ∃ D : FieldInputData d 1 (fun _ : Vec d => (0 : Mat d)),
      0 ≤ LogGrowthBounds.tailProfile D.splitData 0 2 :=
  ⟨{ two_le := hd
     nu_pos := one_pos
     skew := fun _ => by simp [matTranspose]
     contDiff := contDiff_const
     gradConst := 0
     gradConst_nonneg := le_rfl
     grad_le := fun y => by simp }, LogGrowthBounds.tailProfile_nonneg _ _ _⟩

end Profile

end

end SuperdiffusionCLT.Section8
