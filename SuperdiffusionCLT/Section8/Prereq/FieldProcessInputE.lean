/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.FieldProcessInputD

/-!
# Spatial envelopes for the localized tail constants

The local bounds are logarithmic in the Euclidean observation radius.  This file converts them to
the ambient `Vec d` norm and combines them with the algebraic freezing radius.  The resulting
amplitude has polynomial growth, while the decay rate loses one logarithmic weight.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization Homogenization.Book.Ch02 MeasureTheory Set
open SuperdiffusionCLT.Section8.DivergenceForm
open SuperdiffusionCLT.Section8.DivergenceForm.Decay
open SuperdiffusionCLT.Section8.Common.Regularity.Ported
open MarkovProcess.Semigroup

noncomputable section

/-! ## A spatial exhaustion of `Vec d` -/

section Exhaustion

variable {d : ℕ}

/-- The reciprocal affine sup norm used to exhaust `Vec d`. -/
def fieldInput_exhaustionRho (x : Vec d) : ℝ := (1 + ‖x‖)⁻¹

theorem continuous_fieldInput_exhaustionRho : Continuous (fieldInput_exhaustionRho (d := d)) := by
  apply Continuous.inv₀
  · exact continuous_const.add continuous_norm
  · intro x hx
    have : 0 < (1 : ℝ) + ‖x‖ := by positivity
    exact this.ne' hx

theorem fieldInput_exhaustionRho_pos (x : Vec d) : 0 < fieldInput_exhaustionRho x := by
  unfold fieldInput_exhaustionRho
  positivity

theorem fieldInput_exhaustionRho_le_one (x : Vec d) : fieldInput_exhaustionRho x ≤ 1 := by
  unfold fieldInput_exhaustionRho
  exact (inv_le_one₀ (by positivity)).2 (le_add_of_nonneg_right (norm_nonneg x))

theorem lipschitzWith_fieldInput_exhaustionRho :
    LipschitzWith 1 (fieldInput_exhaustionRho (d := d)) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  have hx : 0 < (1 : ℝ) + ‖x‖ := by positivity
  have hy : 0 < (1 : ℝ) + ‖y‖ := by positivity
  have hden : 1 ≤ ((1 : ℝ) + ‖x‖) * (1 + ‖y‖) := by
    nlinarith only [norm_nonneg x, norm_nonneg y]
  have hnorm : |‖x‖ - ‖y‖| ≤ ‖x - y‖ := abs_norm_sub_norm_le x y
  rw [Real.dist_eq]
  unfold fieldInput_exhaustionRho
  rw [inv_sub_inv hx.ne' hy.ne', abs_div, abs_mul, abs_of_pos hx, abs_of_pos hy]
  have hdiv : |‖y‖ - ‖x‖| / (((1 : ℝ) + ‖x‖) * (1 + ‖y‖)) ≤ |‖y‖ - ‖x‖| :=
    div_le_self (abs_nonneg _) hden
  have hxy : |‖y‖ - ‖x‖| ≤ ‖x - y‖ := by
    rw [abs_sub_comm]
    exact hnorm
  simpa only [add_sub_add_left_eq_sub, NNReal.coe_one, one_mul, dist_eq_norm] using
    hdiv.trans hxy

theorem isCompact_fieldInput_exhaustionRho_superlevel {eps : ℝ} (heps : 0 < eps) :
    IsCompact {x : Vec d | eps ≤ fieldInput_exhaustionRho x} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_le continuous_const continuous_fieldInput_exhaustionRho
  · rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨eps⁻¹, fun x hx => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have hden : 0 < (1 : ℝ) + ‖x‖ := by positivity
    have hmul : eps * (1 + ‖x‖) ≤ 1 := by
      change eps ≤ ((1 : ℝ) + ‖x‖)⁻¹ at hx
      rw [inv_eq_one_div] at hx
      exact (le_div_iff₀ hden).mp hx
    rw [inv_eq_one_div]
    apply (le_div_iff₀ heps).2
    nlinarith only [hmul, heps, norm_nonneg x]

/-- Increase a radius when its exhaustion scale forces additional separation. -/
def fieldInput_exhaustionAmp (x : Vec d) (r : ℝ) : ℝ :=
  if 4 * fieldInput_exhaustionRho x ≤ r then max r (2 / 3 * (1 + ‖x‖)) else r

theorem fieldInput_exhaustionAmp_pos {x : Vec d} {r : ℝ} (hr : 0 < r) :
    0 < fieldInput_exhaustionAmp x r := by
  rw [fieldInput_exhaustionAmp]
  split_ifs
  · exact hr.trans_le (le_max_left _ _)
  · exact hr

/-- The amplified radius of an exhaustion tail: a point Euclidean-far from `x`
and in the superlevel set `{rho ≥ r - rho x}` is at distance at least the
amplified radius from `x`. -/
theorem fieldInput_exhaustionAmp_le_dist {x z : Vec d} {r : ℝ}
    (hdist : r ≤ dist z x) (hlevel : r - fieldInput_exhaustionRho x ≤ fieldInput_exhaustionRho z) :
    fieldInput_exhaustionAmp x r ≤ dist z x := by
  rw [fieldInput_exhaustionAmp]
  split_ifs with hamp
  · rw [max_le_iff]
    refine ⟨hdist, ?_⟩
    have hrho : 3 * fieldInput_exhaustionRho x ≤ fieldInput_exhaustionRho z := by
      linarith only [hamp, hlevel]
    have hx : 0 < (1 : ℝ) + ‖x‖ := by positivity
    have hz : 0 < (1 : ℝ) + ‖z‖ := by positivity
    have hnorm : 3 * (1 + ‖z‖) ≤ 1 + ‖x‖ := by
      change 3 * ((1 : ℝ) + ‖x‖)⁻¹ ≤ ((1 : ℝ) + ‖z‖)⁻¹ at hrho
      have hdiv : 3 / (1 + ‖x‖) ≤ 1 / (1 + ‖z‖) := by
        simpa only [div_eq_mul_inv, one_mul] using hrho
      simpa only [one_mul] using (div_le_div_iff₀ hx hz).mp hdiv
    have hreverse : ‖x‖ - ‖z‖ ≤ dist z x := by
      rw [dist_eq_norm, ← norm_neg (z - x), neg_sub]
      exact norm_sub_norm_le x z
    linarith only [hnorm, hreverse]
  · exact hdist

end Exhaustion

variable {d : ℕ} [NeZero d] {A : WholeSpaceAnalyticData d} {S : WholeSpaceLocalizedSplitData A}

/-- The linear coefficient multiplying the effective upper constant in the two non-forcing terms
of the tail amplitude. -/
def fieldInput_linearConst (A : WholeSpaceAnalyticData d) : ℝ :=
  agmonTailL2Coefficient d A.nu 1 +
    agmonTailGradientCoefficient d A.nu 1 (1 / 2 : ℝ)

/-- A dimension factor comparing the Euclidean and ambient norms. -/
def fieldInput_dimFactor (d : ℕ) : ℝ := 1 + d

namespace LogGrowthBounds

/-- The effective upper constant before the spatial logarithmic weight. -/
def rawUpperConst (T : LogGrowthBounds S) : ℝ :=
  Real.sqrt 2 * (A.nu + T.cs +
    2 * (Real.sqrt d * (d : ℝ) * T.cg) *
      Real.sqrt A.nu)

/-- The effective upper constant enlarged by the norm-comparison logarithm. -/
def upperConst (T : LogGrowthBounds S) : ℝ :=
  rawUpperConst T * fieldInput_logWeight (fieldInput_dimFactor d)

/-- The spatially uniform part of the polynomial freezing-radius lower bound. -/
def floorConst (T : LogGrowthBounds S) : ℝ :=
  min
    (Real.rpow (T.amp)
        (T.expo) *
      Real.rpow (fieldInput_dimFactor d) (-T.expo))
    (1 / 2 : ℝ)

/-- The polynomial exponent contributed by one logarithmic field factor and
the `d`-dimensional inverse freezing volume. -/
def amplitudeExponent (T : LogGrowthBounds S) : ℝ :=
  1 + (d : ℝ) * T.expo

/-- A point-independent polynomial envelope constant for the tail amplitude. -/
def amplitudeConst (T : LogGrowthBounds S) : ℝ :=
  fieldInput_linearConst A * upperConst T /
      floorConst T ^ d +
    4 * agmonTailForcingCoefficient d (1 / 2 : ℝ) / A.nu

/-- A point-independent numerator for the logarithmic lower envelope on the
decay rate. -/
def decayConst (T : LogGrowthBounds S) : ℝ :=
  agmonTailRate d A.nu (upperConst T) (1 / 2 : ℝ)

private theorem one_le_dimFactor (d : ℕ) :
    1 ≤ fieldInput_dimFactor d := by
  unfold fieldInput_dimFactor
  exact le_add_of_nonneg_right (Nat.cast_nonneg d)

private theorem fieldInput_dimFactor_pos (d : ℕ) :
    0 < fieldInput_dimFactor d :=
  lt_of_lt_of_le zero_lt_one (one_le_dimFactor d)

private theorem upperConst_pos (T : LogGrowthBounds S) : 0 < upperConst T := by
  unfold upperConst rawUpperConst
  have hCg : 0 ≤ Real.sqrt d * (d : ℝ) * T.cg :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg d) (Nat.cast_nonneg d))
      (T.cg_nonneg)
  have hrest : 0 ≤ T.cs +
      2 * (Real.sqrt d * (d : ℝ) * T.cg) *
        Real.sqrt A.nu :=
    add_nonneg (T.cs_nonneg)
      (mul_nonneg (mul_nonneg (by norm_num) hCg) (Real.sqrt_nonneg A.nu))
  exact mul_pos
    (mul_pos (Real.sqrt_pos.2 (by norm_num)) (by
      linarith only [A.hnu, hrest]))
    (fieldInput_logWeight_pos (one_le_dimFactor d))

omit [NeZero d] in
private theorem one_add_euclideanNorm_le_mul (x : Vec d) :
    1 + euclideanNorm x ≤ fieldInput_dimFactor d * (1 + ‖x‖) := by
  have hE := euclideanNorm_le_dimension_mul_norm x
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hx : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  unfold fieldInput_dimFactor
  nlinarith only [hE, hd, hx, mul_nonneg hd hx]

omit [NeZero d] in
private theorem fieldInput_pointLogWeight_le (x : Vec d) :
    fieldInput_pointLogWeight x ≤
      fieldInput_logWeight (fieldInput_dimFactor d) *
        (1 + Real.log (1 + ‖x‖)) := by
  have hD := one_le_dimFactor d
  have hq : (1 : ℝ) ≤ 1 + ‖x‖ := le_add_of_nonneg_right (norm_nonneg x)
  have hprodPos : 0 < fieldInput_dimFactor d * (1 + ‖x‖) :=
    mul_pos (fieldInput_dimFactor_pos d) (lt_of_lt_of_le zero_lt_one hq)
  have hleftPos : 0 < 1 + euclideanNorm x :=
    lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_right (euclideanNorm_nonneg x))
  have hlog := Real.strictMonoOn_log.monotoneOn hleftPos hprodPos
    (one_add_euclideanNorm_le_mul x)
  rw [Real.log_mul (fieldInput_dimFactor_pos d).ne'
    (lt_of_lt_of_le zero_lt_one hq).ne'] at hlog
  have hlogD : 0 ≤ Real.log (fieldInput_dimFactor d) := Real.log_nonneg hD
  have hlogq : 0 ≤ Real.log (1 + ‖x‖) := Real.log_nonneg hq
  unfold fieldInput_pointLogWeight fieldInput_logWeight
  nlinarith only [hlog, hlogD, hlogq, mul_nonneg hlogD hlogq]

omit [NeZero d] in
private theorem fieldInput_pointLogWeight_ambient_le (x : Vec d) :
    fieldInput_pointLogWeight x ≤
      fieldInput_logWeight (fieldInput_dimFactor d) * (1 + ‖x‖) := by
  have hlog := Real.log_le_sub_one_of_pos (show 0 < (1 : ℝ) + ‖x‖ by positivity)
  have hD : 0 ≤ fieldInput_logWeight (fieldInput_dimFactor d) :=
    (fieldInput_logWeight_pos (one_le_dimFactor d)).le
  exact (fieldInput_pointLogWeight_le x).trans
    (mul_le_mul_of_nonneg_left (by linarith only [hlog]) hD)

private theorem upperBase_le_of_weight (T : LogGrowthBounds S) (x : Vec d) {W : ℝ}
    (hone : 1 ≤ W) (hw : fieldInput_pointLogWeight x ≤ W) :
    upperBase S x ≤
      rawUpperConst T * W := by
  have hCs := T.cs_nonneg
  have hCg : 0 ≤ Real.sqrt d * (d : ℝ) * T.cg := by
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg d) (Nat.cast_nonneg d))
      (T.cg_nonneg)
  have hnu := A.hnu.le
  have hsqrt := Real.sqrt_nonneg A.nu
  unfold upperBase localizedAgmonUpper rawUpperConst
  rw [T.rough_eq x 0, T.smooth_eq x 0]
  simp only [fieldInput_obsRadius, add_zero, div_one]
  change Real.sqrt 2 *
      (A.nu + T.cs * fieldInput_pointLogWeight x +
        2 * (Real.sqrt d * (d : ℝ) * T.cg *
          fieldInput_pointLogWeight x) * Real.sqrt A.nu) ≤
    Real.sqrt 2 *
      (A.nu + T.cs +
        2 * (Real.sqrt d * (d : ℝ) * T.cg) *
          Real.sqrt A.nu) * W
  have hnuScale : A.nu ≤ A.nu * W := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hone hnu
  have hCsScale := mul_le_mul_of_nonneg_left hw hCs
  have hCgScale := mul_le_mul_of_nonneg_left hw hCg
  have hsmooth :
      2 * (Real.sqrt d * (d : ℝ) * T.cg *
          fieldInput_pointLogWeight x) * Real.sqrt A.nu ≤
        2 * (Real.sqrt d * (d : ℝ) * T.cg * W) *
          Real.sqrt A.nu :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hCgScale (by norm_num)) hsqrt
  have hinside := add_le_add (add_le_add hnuScale hCsScale) hsmooth
  calc
    _ ≤ Real.sqrt 2 * (A.nu * W +
        T.cs * W +
        2 * (Real.sqrt d * (d : ℝ) * T.cg * W) *
          Real.sqrt A.nu) :=
      mul_le_mul_of_nonneg_left hinside (Real.sqrt_nonneg 2)
    _ = _ := by ring

private theorem upperBase_le (T : LogGrowthBounds S) (x : Vec d) :
    upperBase S x ≤
      upperConst T * (1 + ‖x‖) := by
  let W := fieldInput_logWeight (fieldInput_dimFactor d) * (1 + ‖x‖)
  have hlogD : 0 ≤ Real.log (fieldInput_dimFactor d) :=
    Real.log_nonneg (one_le_dimFactor d)
  have hWone : 1 ≤ W := by
    unfold W fieldInput_logWeight
    have hx := norm_nonneg x
    nlinarith only [hlogD, hx, mul_nonneg hlogD hx]
  have hbase := upperBase_le_of_weight T x hWone
    (fieldInput_pointLogWeight_ambient_le (d := d) x)
  simpa only [upperConst, W, mul_assoc] using hbase

private theorem floorConst_pos (T : LogGrowthBounds S) : 0 < floorConst T := by
  unfold floorConst
  apply lt_min
  · exact mul_pos
      (Real.rpow_pos_of_pos T.amp_pos _)
      (Real.rpow_pos_of_pos (fieldInput_dimFactor_pos d) _)
  · norm_num

theorem freezingRadius_eq_polynomial (T : LogGrowthBounds S) (x : Vec d) :
    S.freezingRadius x =
      Real.rpow T.amp T.expo * Real.rpow (1 + euclideanNorm x) (-T.expo) := by
  have hx : 0 ≤ 1 + euclideanNorm x := by linarith only [euclideanNorm_nonneg x]
  rw [T.freeze_eq x]
  simp only [Real.rpow_eq_pow]
  rw [Real.div_rpow T.amp_pos.le hx T.expo, Real.rpow_neg hx]
  simp only [div_eq_mul_inv]

private theorem innerFloor_lower (T : LogGrowthBounds S) (x : Vec d) :
    floorConst T *
        Real.rpow (1 + ‖x‖) (-T.expo) ≤
      innerFloor S x := by
  let Am := T.amp
  let e := T.expo
  let D := fieldInput_dimFactor d
  let q : ℝ := 1 + ‖x‖
  have hA : 0 < Am := T.amp_pos
  have he : 0 < e := T.expo_pos
  have hD : 0 < D := fieldInput_dimFactor_pos d
  have hq : 1 ≤ q := le_add_of_nonneg_right (norm_nonneg x)
  change floorConst T * Real.rpow q (-e) ≤
    innerFloor S x
  have hED : (1 : ℝ) + euclideanNorm x ≤ D * q := by
    simpa only [D, q] using one_add_euclideanNorm_le_mul x
  have hpow : Real.rpow (D * q) (-e) ≤
      Real.rpow (1 + euclideanNorm x) (-e) := by
    exact Real.rpow_le_rpow_of_nonpos
      (lt_of_lt_of_le zero_lt_one
        (le_add_of_nonneg_right (euclideanNorm_nonneg x)))
      hED (by linarith only [he])
  have hfactor :
      Real.rpow D (-e) * Real.rpow q (-e) ≤
        Real.rpow (1 + euclideanNorm x) (-e) := by
    calc
      Real.rpow D (-e) * Real.rpow q (-e) = Real.rpow (D * q) (-e) :=
        (Real.mul_rpow hD.le (zero_le_one.trans hq)).symm
      _ ≤ _ := hpow
  have hqpow : Real.rpow q (-e) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hq (by linarith only [he])
  have hqpow0 : 0 ≤ Real.rpow q (-e) :=
    Real.rpow_nonneg (zero_le_one.trans hq) _
  rw [innerFloor, T.freezingRadius_eq_polynomial x]
  apply le_min
  · calc
      floorConst T * Real.rpow q (-e) ≤
          (Real.rpow Am e * Real.rpow D (-e)) * Real.rpow q (-e) :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) hqpow0
      _ = Real.rpow Am e * (Real.rpow D (-e) * Real.rpow q (-e)) := mul_assoc _ _ _
      _ ≤ Real.rpow Am e * Real.rpow (1 + euclideanNorm x) (-e) :=
        mul_le_mul_of_nonneg_left hfactor (Real.rpow_nonneg hA.le _)
      _ = _ := by rfl
  · calc
      floorConst T * Real.rpow q (-e) ≤
          floorConst T * 1 :=
        mul_le_mul_of_nonneg_left hqpow (floorConst_pos T).le
      _ ≤ 1 / 2 := by
        rw [mul_one]
        exact min_le_right _ _

private theorem fieldInput_linearConst_nonneg (A : WholeSpaceAnalyticData d) :
    0 ≤ fieldInput_linearConst A := by
  unfold fieldInput_linearConst
  exact add_nonneg
    (agmonTailL2Coefficient_nonneg d (lam := A.nu) (by norm_num))
    (agmonTailGradientCoefficient_nonneg d (lam := A.nu)
      (alpha := (1 / 2 : ℝ)) A.hnu (by norm_num))

private theorem tail_coefficients_eq_mul (A : WholeSpaceAnalyticData d) (L : ℝ) :
    agmonTailL2Coefficient d A.nu L +
        agmonTailGradientCoefficient d A.nu L (1 / 2 : ℝ) =
      fieldInput_linearConst A * L := by
  unfold fieldInput_linearConst agmonTailL2Coefficient agmonTailGradientCoefficient
  ring

/-- The polynomial envelope amplitude is nonnegative. -/
theorem amplitudeConst_nonneg (T : LogGrowthBounds S) :
    0 ≤ amplitudeConst T := by
  have hU : 0 ≤ upperConst T := by
    exact (upperConst_pos T).le
  have hF := (floorConst_pos T).le
  have hforce := agmonTailForcingCoefficient_nonneg d (1 / 2 : ℝ)
  unfold amplitudeConst
  exact add_nonneg
    (div_nonneg (mul_nonneg (fieldInput_linearConst_nonneg A) hU) (pow_nonneg hF d))
    (div_nonneg (mul_nonneg (by norm_num) hforce) A.hnu.le)

/-- The logarithmic envelope decay numerator is strictly positive. -/
theorem decayConst_pos (T : LogGrowthBounds S) : 0 < decayConst T := by
  apply agmonTailRate_pos d A.hnu _ (by norm_num)
  exact upperConst_pos T

/-- A polynomial envelope for the per-point algebraic amplitude. -/
theorem algebraicAmplitude_le (T : LogGrowthBounds S) (x : Vec d) :
    algebraicAmplitude S x ≤
      amplitudeConst T *
        (1 + ‖x‖) ^ amplitudeExponent T := by
  let q : ℝ := 1 + ‖x‖
  let e := T.expo
  let F := floorConst T
  let U := upperConst T
  let P := fieldInput_linearConst A
  let G := 4 * agmonTailForcingCoefficient d (1 / 2 : ℝ) / A.nu
  have hq : 1 ≤ q := le_add_of_nonneg_right (norm_nonneg x)
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have he : 0 < e := T.expo_pos
  have hF : 0 < F := floorConst_pos T
  have hfloor := innerFloor_lower T x
  have hfloor' : F * Real.rpow q (-e) ≤ innerFloor S x := by
    simpa only [F, q, e] using hfloor
  have hfloorPow :
      (F * Real.rpow q (-e)) ^ d ≤ innerFloor S x ^ d :=
    pow_le_pow_left₀ (mul_nonneg hF.le (Real.rpow_nonneg (zero_le_one.trans hq) _))
      hfloor' d
  have hnum :
      agmonTailL2Coefficient d A.nu (upperBase S x) +
          agmonTailGradientCoefficient d A.nu
            (upperBase S x) (1 / 2 : ℝ) ≤
        P * (U * q) := by
    rw [tail_coefficients_eq_mul]
    exact mul_le_mul_of_nonneg_left (upperBase_le T x)
      (fieldInput_linearConst_nonneg A)
  have hsmallDenPos : 0 < (F * Real.rpow q (-e)) ^ d :=
    pow_pos (mul_pos hF (Real.rpow_pos_of_pos hqpos _)) d
  have hright : 0 ≤ P * (U * q) := by
    exact mul_nonneg (fieldInput_linearConst_nonneg A)
      (mul_nonneg (upperConst_pos T).le (zero_le_one.trans hq))
  have hquot :
      (agmonTailL2Coefficient d A.nu (upperBase S x) +
          agmonTailGradientCoefficient d A.nu
            (upperBase S x) (1 / 2 : ℝ)) /
            innerFloor S x ^ d ≤
        (P * (U * q)) / (F * Real.rpow q (-e)) ^ d := by
    exact div_le_div₀ hright hnum hsmallDenPos hfloorPow
  have hpowIdentity :
      (P * (U * q)) / (F * Real.rpow q (-e)) ^ d =
        (P * U / F ^ d) * Real.rpow q (1 + (d : ℝ) * e) := by
    simp only [Real.rpow_eq_pow]
    rw [mul_pow, ← Real.rpow_mul_natCast (zero_le_one.trans hq) (-e) d,
      show (-e) * (d : ℝ) = -(e * (d : ℝ)) by ring,
      Real.rpow_neg hqpos.le,
      show 1 + (d : ℝ) * e = 1 + e * (d : ℝ) by ring,
      Real.rpow_add hqpos, Real.rpow_one]
    field_simp
  have hqExponent : 1 ≤ Real.rpow q (1 + (d : ℝ) * e) := by
    exact Real.one_le_rpow hq (by positivity)
  have hG : 0 ≤ G := by
    exact div_nonneg
      (mul_nonneg (by norm_num) (agmonTailForcingCoefficient_nonneg d (1 / 2 : ℝ)))
      A.hnu.le
  unfold algebraicAmplitude amplitudeConst
    amplitudeExponent
  change _ ≤ (P * U / F ^ d + G) * Real.rpow q (1 + (d : ℝ) * e)
  calc
    _ ≤ (P * (U * q)) / (F * Real.rpow q (-e)) ^ d + G :=
      add_le_add hquot le_rfl
    _ = (P * U / F ^ d) * Real.rpow q (1 + (d : ℝ) * e) + G := by
      rw [hpowIdentity]
    _ ≤ (P * U / F ^ d) * Real.rpow q (1 + (d : ℝ) * e) +
        G * Real.rpow q (1 + (d : ℝ) * e) :=
      add_le_add le_rfl (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hqExponent hG)
    _ = _ := by ring

/-- A logarithmic envelope for the per-point decay rate. -/
theorem decayRate_ge (T : LogGrowthBounds S) (x : Vec d) :
    decayConst T / (1 + Real.log (1 + ‖x‖)) ≤
      decayRate S x := by
  have hW : 0 < 1 + Real.log (1 + ‖x‖) := by
    have hlog := Real.log_nonneg (le_add_of_nonneg_right (norm_nonneg x))
    linarith only [hlog]
  have hU : 0 < upperConst T := by
    exact upperConst_pos T
  have hbase : upperBase S x ≤
      upperConst T * (1 + Real.log (1 + ‖x‖)) := by
    have hw := fieldInput_pointLogWeight_le (d := d) x
    let W := fieldInput_logWeight (fieldInput_dimFactor d) *
      (1 + Real.log (1 + ‖x‖))
    have hlogD : 0 ≤ Real.log (fieldInput_dimFactor d) :=
      Real.log_nonneg (one_le_dimFactor d)
    have hone : 1 ≤ W := by
      unfold W fieldInput_logWeight
      have hlogx := Real.log_nonneg (le_add_of_nonneg_right (norm_nonneg x))
      nlinarith only [hlogD, hlogx, mul_nonneg hlogD hlogx]
    have hlocal := upperBase_le_of_weight T x hone hw
    simpa only [upperConst, W, mul_assoc] using hlocal
  unfold decayConst decayRate agmonTailRate
  have hLpos := upperBase_pos S x
  have hUWpos : 0 < upperConst T *
      (1 + Real.log (1 + ‖x‖)) := mul_pos hU hW
  have hrecip : 1 / (upperConst T *
      (1 + Real.log (1 + ‖x‖))) ≤
      1 / upperBase S x := by
    exact one_div_le_one_div_of_le hLpos hbase
  have hcoef : 0 ≤
      3 * Real.sqrt A.nu / (16 * Real.sqrt 2) *
        ((1 / 2 : ℝ) / ((1 / 2 : ℝ) + (d : ℝ) / 2)) := by positivity
  calc
    (3 * Real.sqrt A.nu / (16 * Real.sqrt 2 * upperConst T) *
        ((1 / 2 : ℝ) / ((1 / 2 : ℝ) + (d : ℝ) / 2))) /
          (1 + Real.log (1 + ‖x‖)) =
      (3 * Real.sqrt A.nu / (16 * Real.sqrt 2) *
        ((1 / 2 : ℝ) / ((1 / 2 : ℝ) + (d : ℝ) / 2))) *
          (1 / (upperConst T *
            (1 + Real.log (1 + ‖x‖))) ) := by field_simp
    _ ≤ (3 * Real.sqrt A.nu / (16 * Real.sqrt 2) *
        ((1 / 2 : ℝ) / ((1 / 2 : ℝ) + (d : ℝ) / 2))) *
          (1 / upperBase S x) :=
      mul_le_mul_of_nonneg_left hrecip hcoef
    _ = 3 * Real.sqrt A.nu /
          (16 * Real.sqrt 2 * upperBase S x) *
        ((1 / 2 : ℝ) / ((1 / 2 : ℝ) + (d : ℝ) / 2)) := by field_simp

end LogGrowthBounds

/-! ## Satisfiability witnesses -/

/-- The envelope constants are admissible for the marginal split datum. -/
example {nu : ℝ} {k : Vec d → Mat d} (D : FieldInputData d nu k) :
    0 ≤ D.logGrowthBounds.amplitudeConst ∧ 0 < D.logGrowthBounds.decayConst :=
  ⟨LogGrowthBounds.amplitudeConst_nonneg _, LogGrowthBounds.decayConst_pos _⟩

example {nu : ℝ} {k : Vec d → Mat d} (D : FieldInputData d nu k) (x : Vec d) :
    LogGrowthBounds.algebraicAmplitude D.splitData x ≤
      D.logGrowthBounds.amplitudeConst *
        (1 + ‖x‖) ^ D.logGrowthBounds.amplitudeExponent :=
  D.logGrowthBounds.algebraicAmplitude_le x

example : Continuous (fieldInput_exhaustionRho (d := d)) := continuous_fieldInput_exhaustionRho

end

end SuperdiffusionCLT.Section8
