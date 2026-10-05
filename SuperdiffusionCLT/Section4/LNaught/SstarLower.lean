/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Frozen.Section3.SstarLowerBound
public import SuperdiffusionCLT.Section4.LNaught.Threshold
public import SuperdiffusionCLT.Section4.LNaught.Monotone

/-!
# `e.L.vs.Lnaught`: `L ≥ L₀` forces a lower bound on `σ̄²_{L,*}`

This file proves `SuperdiffusionCLT.Section4.LNaught.lNaught_sstar_lower`, the
Lean rendering of display `e.L.vs.Lnaught` of the paper, from
`SuperdiffusionCLT.Frozen.Section3.sigmaBarStar_lower_bound`
(`p.sstar.lower.bound`) and the defining-threshold facts of
`Section4/LNaught/Threshold.lean` (`lNaught_threshold`, `lNaught_absorbs`,
`lNaught_ge`) and `Section4/LNaught/Monotone.lean` (`lNaught_mono_const`,
`lNaughtInner`).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.LNaught

open Real

/-! ## Elementary numeral facts -/

private lemma sstarLower_cStar_neg_three_eq {cStar : ℝ} (hcStar : 0 < cStar) :
    cStar ^ (-(3 : ℝ)) = (cStar⁻¹) ^ (3 : ℕ) := by
  rw [Real.rpow_neg hcStar.le, inv_pow]
  congr 1
  have h3 : (3 : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
  rw [h3, Real.rpow_natCast]

lemma sstarLower_cStar_neg_three_ge_eighth {cStar : ℝ}
    (hcStar : 0 < cStar) (hcStar2 : cStar ≤ 2) :
    (1 : ℝ) / 8 ≤ cStar ^ (-(3 : ℝ)) := by
  have heq := sstarLower_cStar_neg_three_eq hcStar
  have hinv : (1 : ℝ) / 2 ≤ cStar⁻¹ := by
    have h := mul_le_mul_of_nonneg_right hcStar2 (inv_nonneg.mpr hcStar.le)
    rw [mul_inv_cancel₀ hcStar.ne'] at h
    linarith only [h]
  have hpow : ((1 : ℝ) / 2) ^ (3 : ℕ) ≤ (cStar⁻¹) ^ (3 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) hinv 3
  rw [heq]
  linarith only [hpow, show ((1:ℝ)/2)^(3:ℕ) = 1/8 by norm_num]

/-! ## The ARG_full comparison: `2 + (M+1+K)c⋆^{-3}/(ν(1-α))` dominates
`(3+ν⁻¹+c⋆⁻¹+K)/24` -/

private lemma sstarLower_argFull_ge {M alpha cStar nu K : ℝ}
    (hM : 1 ≤ M) (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1)
    (hcStar : 0 < cStar) (hcStar2 : cStar ≤ 2) (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hK : 0 ≤ K) :
    (3 + nu⁻¹ + cStar⁻¹ + K) / 24 ≤
      2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha)) := by
  set Y := (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha)) with hYdef
  have h1ma_pos : 0 < 1 - alpha := by linarith only [halpha1]
  have h1ma_le1 : 1 - alpha ≤ 1 := by linarith only [halpha0]
  have hcube_nonneg : (0:ℝ) ≤ cStar ^ (-(3 : ℝ)) := Real.rpow_nonneg hcStar.le _
  have hcube_ge : (1:ℝ) / 8 ≤ cStar ^ (-(3 : ℝ)) := sstarLower_cStar_neg_three_ge_eighth hcStar hcStar2
  have hM1K1 : (1 : ℝ) ≤ M + 1 + K := by linarith only [hM, hK]
  have hM1Knn : (0 : ℝ) ≤ M + 1 + K := by linarith only [hM1K1]
  -- `Y ≥ (M+1+K) * c⋆^{-3}` since dividing by `ν(1-α) ≤ 1` only increases the value.
  have hnuma_le1 : nu * (1 - alpha) ≤ 1 := by
    have h := mul_le_mul hnu1 h1ma_le1 h1ma_pos.le (by norm_num : (0:ℝ) ≤ 1)
    linarith only [h]
  have hnuma_pos : 0 < nu * (1 - alpha) := mul_pos hnu h1ma_pos
  have hYge0 : (M + 1 + K) * cStar ^ (-(3 : ℝ)) ≤ Y := by
    rw [hYdef, le_div_iff₀ hnuma_pos]
    have hnn : (0:ℝ) ≤ (M + 1 + K) * cStar ^ (-(3 : ℝ)) :=
      mul_nonneg hM1Knn hcube_nonneg
    calc (M + 1 + K) * cStar ^ (-(3 : ℝ)) * (nu * (1 - alpha))
        ≤ (M + 1 + K) * cStar ^ (-(3 : ℝ)) * 1 :=
          mul_le_mul_of_nonneg_left hnuma_le1 hnn
      _ = (M + 1 + K) * cStar ^ (-(3 : ℝ)) := by ring
  -- `K` bound.
  have hK_le : K ≤ 8 * Y := by
    have h1 : (1 + K) * ((1:ℝ)/8) ≤ (M + 1 + K) * cStar ^ (-(3 : ℝ)) := by
      have hle : (1 + K : ℝ) ≤ M + 1 + K := by linarith only [hM]
      calc (1 + K) * ((1:ℝ)/8) ≤ (M + 1 + K) * ((1:ℝ)/8) :=
            mul_le_mul_of_nonneg_right hle (by norm_num)
        _ ≤ (M + 1 + K) * cStar ^ (-(3 : ℝ)) :=
            mul_le_mul_of_nonneg_left hcube_ge hM1Knn
    linarith only [h1, hYge0]
  -- `c⋆⁻¹` bound.
  have hcStarinv_ge : (1:ℝ)/2 ≤ cStar⁻¹ := by
    have h := mul_le_mul_of_nonneg_right hcStar2 (inv_nonneg.mpr hcStar.le)
    rw [mul_inv_cancel₀ hcStar.ne'] at h
    linarith only [h]
  have hcStarinv_nonneg : (0:ℝ) ≤ cStar⁻¹ := by linarith only [hcStarinv_ge]
  have hcube_eq : cStar ^ (-(3 : ℝ)) = (cStar⁻¹) ^ (3 : ℕ) :=
    sstarLower_cStar_neg_three_eq hcStar
  have hYgeCube : cStar ^ (-(3 : ℝ)) ≤ Y := by
    have h1 : cStar ^ (-(3 : ℝ)) ≤ (M + 1 + K) * cStar ^ (-(3 : ℝ)) := by
      calc cStar ^ (-(3 : ℝ)) = 1 * cStar ^ (-(3 : ℝ)) := by ring
        _ ≤ (M + 1 + K) * cStar ^ (-(3 : ℝ)) :=
            mul_le_mul_of_nonneg_right hM1K1 hcube_nonneg
    linarith only [h1, hYge0]
  have hcStarinv_sq_ge : (1:ℝ)/4 ≤ (cStar⁻¹) ^ (2 : ℕ) := by
    have hpow : ((1:ℝ)/2) ^ (2:ℕ) ≤ (cStar⁻¹) ^ (2:ℕ) :=
      pow_le_pow_left₀ (by norm_num) hcStarinv_ge 2
    linarith only [hpow, show ((1:ℝ)/2)^(2:ℕ) = 1/4 by norm_num]
  have hcStarinv_le : cStar⁻¹ ≤ 4 * Y := by
    have hstep : cStar⁻¹ ≤ 4 * (cStar⁻¹) ^ (3 : ℕ) := by
      have h4sq : (1:ℝ) ≤ 4 * (cStar⁻¹) ^ (2 : ℕ) := by linarith only [hcStarinv_sq_ge]
      have h := mul_le_mul_of_nonneg_left h4sq hcStarinv_nonneg
      calc cStar⁻¹ = cStar⁻¹ * 1 := by ring
        _ ≤ cStar⁻¹ * (4 * (cStar⁻¹) ^ (2 : ℕ)) := by linarith only [h]
        _ = 4 * (cStar⁻¹) ^ (3 : ℕ) := by ring
    rw [← hcube_eq] at hstep
    linarith only [hstep, hYgeCube]
  -- `ν⁻¹` bound.
  have hprod18 : (1:ℝ) / 8 ≤ (M + 1 + K) * cStar ^ (-(3 : ℝ)) := by
    have h := mul_le_mul hM1K1 hcube_ge (by norm_num) hM1Knn
    linarith only [h]
  have hnuinv_le : nu⁻¹ ≤ 8 * Y := by
    rw [hYdef, show (8:ℝ) * ((M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) =
        8 * ((M + 1 + K) * cStar ^ (-(3 : ℝ))) / (nu * (1 - alpha)) by ring,
      le_div_iff₀ hnuma_pos]
    have heq : nu⁻¹ * (nu * (1 - alpha)) = 1 - alpha := by
      field_simp
    rw [heq]
    linarith only [h1ma_le1, hprod18]
  have hYnonneg : (0:ℝ) ≤ Y :=
    le_trans (mul_nonneg hM1Knn hcube_nonneg) hYge0
  linarith only [hK_le, hcStarinv_le, hnuinv_le, hYnonneg]

/-! ## The log comparison: `log(ARG_full) ≥ log(3+ν⁻¹+c⋆⁻¹+K) - log 24` -/

private lemma sstarLower_log_argFull_ge {M alpha cStar nu K : ℝ}
    (hM : 1 ≤ M) (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1)
    (hcStar : 0 < cStar) (hcStar2 : cStar ≤ 2) (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hK : 0 ≤ K) :
    Real.log (3 + nu⁻¹ + cStar⁻¹ + K) - Real.log 24 ≤
      Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) := by
  have hsum_pos : (0:ℝ) < 3 + nu⁻¹ + cStar⁻¹ + K := by positivity
  have hge := sstarLower_argFull_ge hM halpha0 halpha1 hcStar hcStar2 hnu hnu1 hK
  have hlog_le : Real.log ((3 + nu⁻¹ + cStar⁻¹ + K) / 24) ≤
      Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) :=
    Real.log_le_log (by positivity) hge
  have hdiv : Real.log ((3 + nu⁻¹ + cStar⁻¹ + K) / 24) =
      Real.log (3 + nu⁻¹ + cStar⁻¹ + K) - Real.log 24 :=
    Real.log_div hsum_pos.ne' (by norm_num)
  rw [hdiv] at hlog_le
  exact hlog_le

/-! ## The `12`th power dominates -/

/-- A generous, non-tight numeral: any positive real works here, the exact
value only weakens the final witness `c`. -/
def sstarLowerKappa0 : ℝ := (10 : ℝ) ^ (18 : ℕ)

lemma sstarLowerKappa0_pos : 0 < sstarLowerKappa0 := by
  unfold sstarLowerKappa0; positivity

/-- Pure real-analysis core: once `g` clears `log(3+ν⁻¹+c⋆⁻¹+K) - log 24`
(`sstarLower_log_argFull_ge`) and the elementary `g ≥ log 2` (`ARG_full ≥ 2`),
`g^12` dominates `ell^3 log(ell) + ell` up to the fixed constant
`2 / sstarLowerKappa0`. Case split on whether `ell ≤ 100` (numeral case, using
`g ≥ log 2 > 0`) or `ell > 100` (using `g ≥ ell - log 24 ≥ ell / 2`). -/
private lemma sstarLower_pow12_dominates {ell g : ℝ}
    (hell : Real.log 3 ≤ ell) (hg1 : ell - Real.log 24 ≤ g) (hg2 : Real.log 2 ≤ g) :
    (2 / sstarLowerKappa0) * (ell ^ (3 : ℕ) * Real.log ell + ell) ≤ g ^ (12 : ℕ) := by
  have hlog3 : (1 : ℝ) < Real.log 3 := by
    have h1 : Real.log (Real.exp 1) < Real.log 3 := by
      apply Real.log_lt_log (Real.exp_pos 1)
      linarith only [Real.exp_one_lt_d9]
    rwa [Real.log_exp] at h1
  have hellpos : (0 : ℝ) < ell := lt_of_lt_of_le (by linarith only [hlog3]) hell
  rcases le_or_gt ell 100 with hcase | hcase
  · -- Case A: `ell` bounded by the numeral `100`.
    have hlogell_le : Real.log ell ≤ 99 := by
      have h := Real.log_le_sub_one_of_pos hellpos
      linarith only [h, hcase]
    have hlog24_le : Real.log 24 ≤ 23 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 24)
      linarith only [h]
    have hlogell_nonneg : (0:ℝ) ≤ Real.log ell := by
      have h1 : (1:ℝ) ≤ ell := by linarith only [hell, hlog3]
      exact Real.log_nonneg h1
    have hsum_le : ell ^ (3 : ℕ) * Real.log ell + ell ≤ (100000000 : ℝ) := by
      have h1 : ell ^ (3 : ℕ) ≤ (100 : ℝ) ^ (3 : ℕ) :=
        pow_le_pow_left₀ hellpos.le hcase 3
      have h2 : ell ^ (3 : ℕ) * Real.log ell ≤ (100 : ℝ) ^ (3 : ℕ) * 99 := by
        have h1' : (0:ℝ) ≤ (100:ℝ) ^ (3:ℕ) := by positivity
        calc ell ^ (3 : ℕ) * Real.log ell ≤ (100:ℝ) ^ (3:ℕ) * Real.log ell :=
              mul_le_mul_of_nonneg_right h1 hlogell_nonneg
          _ ≤ (100:ℝ) ^ (3:ℕ) * 99 := mul_le_mul_of_nonneg_left hlogell_le h1'
      have h3 : ((100:ℝ) ^ (3:ℕ) * 99 : ℝ) = 99000000 := by norm_num
      linarith only [h2, h3, hcase]
    have hg2pos : (0.6 : ℝ) ≤ g := by
      have h6 : (0.6 : ℝ) < Real.log 2 := by linarith only [Real.log_two_gt_d9]
      linarith only [hg2, h6]
    have hgpow : (0.6 : ℝ) ^ (12 : ℕ) ≤ g ^ (12 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) hg2pos 12
    have hgpow_ge : (1 : ℝ) / 1000000000 ≤ g ^ (12 : ℕ) := by
      have h1 : (1:ℝ)/1000000000 ≤ (0.6:ℝ)^(12:ℕ) := by norm_num
      linarith only [h1, hgpow]
    have hfinal : (2 / sstarLowerKappa0) * (100000000 : ℝ) ≤ (1:ℝ)/1000000000 := by
      unfold sstarLowerKappa0
      norm_num
    have hkappa0_nonneg : (0:ℝ) ≤ 2 / sstarLowerKappa0 :=
      div_nonneg (by norm_num) sstarLowerKappa0_pos.le
    linarith only [hsum_le, hgpow_ge, hfinal,
      mul_le_mul_of_nonneg_left hsum_le hkappa0_nonneg]
  · -- Case B: `ell > 100`, so `g ≥ ell - log 24 ≥ ell / 2`.
    have hlog24_le : Real.log 24 ≤ 23 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 24)
      linarith only [h]
    have hghalf : ell / 2 ≤ g := by linarith only [hg1, hlog24_le, hcase]
    have hellhalf_pos : (0:ℝ) < ell / 2 := by linarith only [hcase]
    have hgpow : (ell / 2) ^ (12 : ℕ) ≤ g ^ (12 : ℕ) :=
      pow_le_pow_left₀ hellhalf_pos.le hghalf 12
    have hgpow_eq : (ell / 2) ^ (12 : ℕ) = ell ^ (12 : ℕ) / 4096 := by
      rw [div_pow]; norm_num
    have hlogell_le : Real.log ell ≤ ell := by
      have h := Real.log_le_sub_one_of_pos hellpos
      linarith only [h]
    have hlogell_nonneg : (0:ℝ) ≤ Real.log ell := by
      have h1 : (1:ℝ) ≤ ell := by linarith only [hcase]
      exact Real.log_nonneg h1
    have hpow4 : ell ^ (3 : ℕ) * Real.log ell ≤ ell ^ (4 : ℕ) := by
      have hellnn : (0:ℝ) ≤ ell := hellpos.le
      have h1 : ell ^ (3 : ℕ) * Real.log ell ≤ ell ^ (3 : ℕ) * ell :=
        mul_le_mul_of_nonneg_left hlogell_le (by positivity)
      have h2 : ell ^ (3 : ℕ) * ell = ell ^ (4 : ℕ) := by ring
      linarith only [h1, h2.le, h2.ge]
    have hellle4 : ell ≤ ell ^ (4 : ℕ) := by
      have h1 : ell ^ (1 : ℕ) ≤ ell ^ (4 : ℕ) :=
        pow_le_pow_right₀ (by linarith only [hcase]) (by norm_num)
      simpa using h1
    have hsum_le : ell ^ (3 : ℕ) * Real.log ell + ell ≤ 2 * ell ^ (4 : ℕ) := by
      linarith only [hpow4, hellle4]
    have hell4nn : (0:ℝ) ≤ ell ^ (4 : ℕ) := by positivity
    have hell8 : (100 : ℝ) ^ (8 : ℕ) ≤ ell ^ (8 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) hcase.le 8
    have h100_8kappa : (16384 : ℝ) ≤ (100 : ℝ) ^ (8 : ℕ) * sstarLowerKappa0 := by
      unfold sstarLowerKappa0; norm_num
    have hstep0 : (16384 : ℝ) ≤ ell ^ (8 : ℕ) * sstarLowerKappa0 := by
      have h := mul_le_mul_of_nonneg_right hell8 sstarLowerKappa0_pos.le
      linarith only [h100_8kappa, h]
    have hstep : (16384 : ℝ) * ell ^ (4 : ℕ) ≤ ell ^ (8 : ℕ) * sstarLowerKappa0 * ell ^ (4 : ℕ) :=
      mul_le_mul_of_nonneg_right hstep0 hell4nn
    have hexp : ell ^ (8 : ℕ) * sstarLowerKappa0 * ell ^ (4 : ℕ) =
        ell ^ (12 : ℕ) * sstarLowerKappa0 := by ring
    rw [hexp] at hstep
    have hfinal : (2 / sstarLowerKappa0) * (2 * ell ^ (4 : ℕ)) ≤ ell ^ (12 : ℕ) / 4096 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ sstarLowerKappa0_pos (by norm_num : (0:ℝ) < 4096)]
      nlinarith only [hstep]
    have hkappa0_nonneg : (0:ℝ) ≤ 2 / sstarLowerKappa0 :=
      div_nonneg (by norm_num) sstarLowerKappa0_pos.le
    linarith only [hgpow, hgpow_eq, hsum_le, hfinal,
      mul_le_mul_of_nonneg_left hsum_le hkappa0_nonneg]

/-! ## Dropping `K` from the first bracket term -/

private lemma sstarLower_ellprime_le {nu cStar K : ℝ}
    (hnu : 0 < nu) (hcStar : 0 < cStar) (hK : 0 ≤ K) :
    (Real.log (3 + nu⁻¹ + cStar⁻¹)) ^ (3 : ℕ) * Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹)) ≤
      (Real.log (3 + nu⁻¹ + cStar⁻¹ + K)) ^ (3 : ℕ) *
        Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹ + K)) := by
  have hpos : (0:ℝ) < 3 + nu⁻¹ + cStar⁻¹ := by positivity
  have hle : 3 + nu⁻¹ + cStar⁻¹ ≤ 3 + nu⁻¹ + cStar⁻¹ + K := by linarith only [hK]
  have hellle : Real.log (3 + nu⁻¹ + cStar⁻¹) ≤ Real.log (3 + nu⁻¹ + cStar⁻¹ + K) :=
    Real.log_le_log hpos hle
  have hell3 : (3:ℝ) ≤ 3 + nu⁻¹ + cStar⁻¹ := by
    have h1 := inv_nonneg.mpr hnu.le
    have h2 := inv_nonneg.mpr hcStar.le
    linarith only [h1, h2]
  have hlog3 : (1:ℝ) < Real.log 3 := by
    have h1 : Real.log (Real.exp 1) < Real.log 3 := by
      apply Real.log_lt_log (Real.exp_pos 1)
      linarith only [Real.exp_one_lt_d9]
    rwa [Real.log_exp] at h1
  have hellgt1 : (1:ℝ) < Real.log (3 + nu⁻¹ + cStar⁻¹) := by
    have h1 : Real.log 3 ≤ Real.log (3 + nu⁻¹ + cStar⁻¹) := Real.log_le_log (by norm_num) hell3
    linarith only [h1, hlog3]
  have hellnn : (0:ℝ) ≤ Real.log (3 + nu⁻¹ + cStar⁻¹) := by linarith only [hellgt1]
  have hloglognn : (0:ℝ) ≤ Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹)) :=
    Real.log_nonneg hellgt1.le
  have hloglogle : Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹)) ≤
      Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹ + K)) :=
    Real.log_le_log (by linarith only [hellgt1]) hellle
  have hpow3le : (Real.log (3 + nu⁻¹ + cStar⁻¹)) ^ (3 : ℕ) ≤
      (Real.log (3 + nu⁻¹ + cStar⁻¹ + K)) ^ (3 : ℕ) :=
    pow_le_pow_left₀ hellnn hellle 3
  have hpow3nn : (0:ℝ) ≤ (Real.log (3 + nu⁻¹ + cStar⁻¹)) ^ (3 : ℕ) := by positivity
  have hloglognn' : (0:ℝ) ≤ Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹ + K)) := by
    linarith only [hloglognn, hloglogle]
  calc (Real.log (3 + nu⁻¹ + cStar⁻¹)) ^ (3 : ℕ) * Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹))
      ≤ (Real.log (3 + nu⁻¹ + cStar⁻¹)) ^ (3 : ℕ) *
          Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹ + K)) :=
        mul_le_mul_of_nonneg_left hloglogle hpow3nn
    _ ≤ (Real.log (3 + nu⁻¹ + cStar⁻¹ + K)) ^ (3 : ℕ) *
          Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹ + K)) :=
        mul_le_mul_of_nonneg_right hpow3le hloglognn'

/-! ## `lNaughtInner` dominates the root threshold's bracket, times `C` -/

/-- Pure algebra: weighting the second summand by `1+K` (`K ≥ 0`) only helps
once the first summand is nonnegative. -/
private lemma sstarLower_weight_by_K {A B K : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K) :
    A + (1 + K) * B ≤ (1 + K) * (A + B) := by
  nlinarith only [hA, hK, mul_nonneg hA hK]

private lemma sstarLower_inner_ge {C M alpha cStar nu K : ℝ}
    (hC : 0 ≤ C) (hM : 1 ≤ M) (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1)
    (hcStar : 0 < cStar) (hcStar2 : cStar ≤ 2) (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hK : 0 ≤ K) :
    C * (2 / sstarLowerKappa0) *
        (cStar ^ (-(3 : ℝ)) *
          (Real.log (3 + nu⁻¹ + cStar⁻¹) ^ (3 : ℕ) *
              Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹)) +
            (1 + K) * Real.log (3 + nu⁻¹ + cStar⁻¹ + K))) ≤
      lNaughtInner C M alpha cStar nu K := by
  have hg2 : Real.log 2 ≤
      Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) :=
    Real.log_le_log (by norm_num)
      (log_arg_ge_two (by linarith only [hM]) hK hcStar hnu halpha1)
  have hg1 : Real.log (3 + nu⁻¹ + cStar⁻¹ + K) - Real.log 24 ≤
      Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) :=
    sstarLower_log_argFull_ge hM halpha0 halpha1 hcStar hcStar2 hnu hnu1 hK
  have hlog3 : (1:ℝ) < Real.log 3 := by
    have h1 : Real.log (Real.exp 1) < Real.log 3 := by
      apply Real.log_lt_log (Real.exp_pos 1)
      linarith only [Real.exp_one_lt_d9]
    rwa [Real.log_exp] at h1
  have hell_ge3 : Real.log 3 ≤ Real.log (3 + nu⁻¹ + cStar⁻¹ + K) := by
    have h3le : (3:ℝ) ≤ 3 + nu⁻¹ + cStar⁻¹ + K := by
      have h1 := inv_nonneg.mpr hnu.le
      have h2 := inv_nonneg.mpr hcStar.le
      linarith only [h1, h2, hK]
    exact Real.log_le_log (by norm_num) h3le
  -- The pure `12`th-power domination, instantiated at `ell := log(3+ν⁻¹+c⋆⁻¹+K)`,
  -- `g := log(ARG_full)`.
  have hP := sstarLower_pow12_dominates hell_ge3 hg1 hg2
  have hgR : Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) =
      Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℕ) := by
    rw [show (12:ℝ) = ((12:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  -- The `K`-independent first bracket term is dominated by the `K`-dependent one.
  have hQ := sstarLower_ellprime_le hnu hcStar hK
  have hlogellpos : (0:ℝ) < Real.log (3 + nu⁻¹ + cStar⁻¹ + K) := by
    have h1 : (1:ℝ) < Real.log (3 + nu⁻¹ + cStar⁻¹ + K) := lt_of_lt_of_le hlog3 hell_ge3
    linarith only [h1]
  have hlogloglogellnn : (0:ℝ) ≤
      Real.log (3 + nu⁻¹ + cStar⁻¹ + K) ^ (3:ℕ) * Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹ + K)) := by
    have h1 : (1:ℝ) < Real.log (3 + nu⁻¹ + cStar⁻¹ + K) := lt_of_lt_of_le hlog3 hell_ge3
    have h2 : (0:ℝ) ≤ Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹ + K)) := Real.log_nonneg h1.le
    positivity
  have hK1 : (1:ℝ) ≤ 1 + K := by linarith only [hK]
  have hkappa0_nonneg : (0:ℝ) ≤ 2 / sstarLowerKappa0 :=
    div_nonneg (by norm_num) sstarLowerKappa0_pos.le
  -- Combine `hQ` and `sstarLower_weight_by_K` into the raw `(1+K)`-weighted
  -- bound, THEN scale by `2/κ₀` and invoke `hP`.
  have hstep1 : Real.log (3 + nu⁻¹ + cStar⁻¹) ^ (3:ℕ) * Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹)) +
      (1 + K) * Real.log (3 + nu⁻¹ + cStar⁻¹ + K) ≤
      Real.log (3 + nu⁻¹ + cStar⁻¹ + K) ^ (3:ℕ) *
          Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹ + K)) +
        (1 + K) * Real.log (3 + nu⁻¹ + cStar⁻¹ + K) := by
    linarith only [hQ]
  have hstep2 : Real.log (3 + nu⁻¹ + cStar⁻¹ + K) ^ (3:ℕ) *
      Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹ + K)) +
      (1 + K) * Real.log (3 + nu⁻¹ + cStar⁻¹ + K) ≤
      (1 + K) * (Real.log (3 + nu⁻¹ + cStar⁻¹ + K) ^ (3:ℕ) *
          Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹ + K)) +
        Real.log (3 + nu⁻¹ + cStar⁻¹ + K)) :=
    sstarLower_weight_by_K hlogloglogellnn hK
  have hsum_raw : Real.log (3 + nu⁻¹ + cStar⁻¹) ^ (3:ℕ) *
      Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹)) +
      (1 + K) * Real.log (3 + nu⁻¹ + cStar⁻¹ + K) ≤
      (1 + K) * (Real.log (3 + nu⁻¹ + cStar⁻¹ + K) ^ (3:ℕ) *
          Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹ + K)) +
        Real.log (3 + nu⁻¹ + cStar⁻¹ + K)) :=
    le_trans hstep1 hstep2
  have hsum_raw' : (2 / sstarLowerKappa0) *
      (Real.log (3 + nu⁻¹ + cStar⁻¹) ^ (3:ℕ) * Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹)) +
        (1 + K) * Real.log (3 + nu⁻¹ + cStar⁻¹ + K)) ≤
      (2 / sstarLowerKappa0) * ((1 + K) *
        (Real.log (3 + nu⁻¹ + cStar⁻¹ + K) ^ (3:ℕ) *
            Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹ + K)) +
          Real.log (3 + nu⁻¹ + cStar⁻¹ + K))) :=
    mul_le_mul_of_nonneg_left hsum_raw hkappa0_nonneg
  have heq2 : (2 / sstarLowerKappa0) * ((1 + K) *
      (Real.log (3 + nu⁻¹ + cStar⁻¹ + K) ^ (3:ℕ) *
          Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹ + K)) +
        Real.log (3 + nu⁻¹ + cStar⁻¹ + K))) =
      (1 + K) * ((2 / sstarLowerKappa0) *
        (Real.log (3 + nu⁻¹ + cStar⁻¹ + K) ^ (3:ℕ) *
            Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹ + K)) +
          Real.log (3 + nu⁻¹ + cStar⁻¹ + K))) := by ring
  have hstep4 : (1 + K) * ((2 / sstarLowerKappa0) *
      (Real.log (3 + nu⁻¹ + cStar⁻¹ + K) ^ (3:ℕ) *
          Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹ + K)) +
        Real.log (3 + nu⁻¹ + cStar⁻¹ + K))) ≤ (1 + K) *
      Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℕ) :=
    mul_le_mul_of_nonneg_left hP (by linarith only [hK])
  have hcomb : (2 / sstarLowerKappa0) *
      (Real.log (3 + nu⁻¹ + cStar⁻¹) ^ (3:ℕ) * Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹)) +
        (1 + K) * Real.log (3 + nu⁻¹ + cStar⁻¹ + K)) ≤
      (1 + K) *
        Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℕ) := by
    rw [heq2] at hsum_raw'
    exact le_trans hsum_raw' hstep4
  -- Rewrite the `12`th power to `Real.rpow`, matching `lNaughtInner`'s formula.
  rw [← hgR] at hcomb
  have hCcStar_nonneg : (0:ℝ) ≤ C * cStar ^ (-(3 : ℝ)) :=
    mul_nonneg hC (Real.rpow_nonneg hcStar.le _)
  have hscaled : C * cStar ^ (-(3 : ℝ)) * ((2 / sstarLowerKappa0) *
      (Real.log (3 + nu⁻¹ + cStar⁻¹) ^ (3:ℕ) * Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹)) +
        (1 + K) * Real.log (3 + nu⁻¹ + cStar⁻¹ + K))) ≤
      C * cStar ^ (-(3 : ℝ)) * ((1 + K) *
        Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ)) :=
    mul_le_mul_of_nonneg_left hcomb hCcStar_nonneg
  have hLHSeq : C * (2 / sstarLowerKappa0) *
      (cStar ^ (-(3 : ℝ)) *
        (Real.log (3 + nu⁻¹ + cStar⁻¹) ^ (3 : ℕ) *
            Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹)) +
          (1 + K) * Real.log (3 + nu⁻¹ + cStar⁻¹ + K))) =
      C * cStar ^ (-(3 : ℝ)) * ((2 / sstarLowerKappa0) *
        (Real.log (3 + nu⁻¹ + cStar⁻¹) ^ (3:ℕ) * Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹)) +
          (1 + K) * Real.log (3 + nu⁻¹ + cStar⁻¹ + K))) := by ring
  -- `(M+1+K)/((1-α)^12ν^4) ≥ 1+K` since `(1-α)^12ν^4 ≤ 1`.
  have h1alpha12_le1 : (1 - alpha) ^ (12 : ℝ) ≤ 1 :=
    Real.rpow_le_one (by linarith only [halpha1]) (by linarith only [halpha0]) (by norm_num)
  have hnu4_le1 : nu ^ (4 : ℝ) ≤ 1 := Real.rpow_le_one hnu.le hnu1 (by norm_num)
  have hdenom_pos : (0:ℝ) < (1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ) := denom_pos hnu halpha1
  have hdenom_le1 : (1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ) ≤ 1 := by
    calc (1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ) ≤ 1 * nu ^ (4 : ℝ) :=
          mul_le_mul_of_nonneg_right h1alpha12_le1 (Real.rpow_nonneg hnu.le _)
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hnu4_le1 (by norm_num)
      _ = 1 := by ring
  have hM1Knn : (0:ℝ) ≤ M + 1 + K := by linarith only [hM, hK]
  have hMKdiv_ge : (M + 1 + K) ≤ (M + 1 + K) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) := by
    rw [le_div_iff₀ hdenom_pos]
    calc (M + 1 + K) * ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) ≤ (M + 1 + K) * 1 :=
          mul_le_mul_of_nonneg_left hdenom_le1 hM1Knn
      _ = M + 1 + K := by ring
  have h1K_le : (1 + K) ≤ (M + 1 + K) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) := by
    linarith only [hMKdiv_ge, hM]
  have hg_pos : (0:ℝ) < Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) :=
    lt_of_lt_of_le (Real.log_pos (by norm_num)) hg2
  have hg12_nonneg : (0:ℝ) ≤
      Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) :=
    Real.rpow_nonneg hg_pos.le _
  have hRHSle : C * cStar ^ (-(3 : ℝ)) * ((1 + K) *
      Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ)) ≤
      lNaughtInner C M alpha cStar nu K := by
    unfold lNaughtInner
    have heq : C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) /
        ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) =
        C * cStar ^ (-(3 : ℝ)) * ((M + 1 + K) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ))) := by
      ring
    rw [heq]
    have hfact : (1 + K) *
        Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) ≤
        (M + 1 + K) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) *
          Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) :=
      mul_le_mul_of_nonneg_right h1K_le hg12_nonneg
    have hassoc : C * cStar ^ (-(3 : ℝ)) *
        ((M + 1 + K) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) *
          Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ)) =
        C * cStar ^ (-(3 : ℝ)) * ((M + 1 + K) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ))) *
          Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) := by
      ring
    rw [← hassoc]
    exact mul_le_mul_of_nonneg_left hfact hCcStar_nonneg
  rw [hLHSeq]
  exact le_trans hscaled hRHSle

/-! ## `lNaughtInner C ... ≥ 1` once `C` clears a fixed numeral -/

private lemma sstarLower_inner_ge_one {C M alpha cStar nu K : ℝ}
    (hC : sstarLowerKappa0 ≤ C) (hM : 1 ≤ M) (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1)
    (hcStar : 0 < cStar) (hcStar2 : cStar ≤ 2) (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hK : 0 ≤ K) :
    (1:ℝ) ≤ lNaughtInner C M alpha cStar nu K := by
  unfold lNaughtInner
  have hcube_ge : (1:ℝ) / 8 ≤ cStar ^ (-(3 : ℝ)) := sstarLower_cStar_neg_three_ge_eighth hcStar hcStar2
  have hM1Knn : (1:ℝ) ≤ M + 1 + K := by linarith only [hM, hK]
  have hg2 : Real.log 2 ≤
      Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) :=
    Real.log_le_log (by norm_num)
      (log_arg_ge_two (by linarith only [hM]) hK hcStar hnu halpha1)
  have hlog2gt : (0.6:ℝ) < Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hgpos : (0:ℝ) < Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) := by
    linarith only [hg2, hlog2gt]
  have hg06 : (0.6:ℝ) ≤ Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) := by
    linarith only [hg2, hlog2gt]
  have hgpow : (0.6:ℝ) ^ (12:ℝ) ≤
      Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12:ℝ) :=
    Real.rpow_le_rpow (by norm_num) hg06 (by norm_num)
  have hgpow_num : (1:ℝ) / 1000000000 ≤ (0.6:ℝ) ^ (12:ℝ) := by
    rw [show (12:ℝ) = ((12:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have h1alpha12_le1 : (1 - alpha) ^ (12 : ℝ) ≤ 1 :=
    Real.rpow_le_one (by linarith only [halpha1]) (by linarith only [halpha0]) (by norm_num)
  have hnu4_le1 : nu ^ (4 : ℝ) ≤ 1 := Real.rpow_le_one hnu.le hnu1 (by norm_num)
  have hdenom_pos : (0:ℝ) < (1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ) := denom_pos hnu halpha1
  have hdenom_le1 : (1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ) ≤ 1 := by
    calc (1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ) ≤ 1 * nu ^ (4 : ℝ) :=
          mul_le_mul_of_nonneg_right h1alpha12_le1 (Real.rpow_nonneg hnu.le _)
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hnu4_le1 (by norm_num)
      _ = 1 := by ring
  have hfrac_ge : (C * (M + 1 + K) * cStar ^ (-(3 : ℝ))) / 1 ≤
      C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) := by
    apply div_le_div_of_nonneg_left _ hdenom_pos hdenom_le1
    have hCnn : (0:ℝ) ≤ C := by linarith only [hC, sstarLowerKappa0_pos.le]
    positivity
  have hfrac_eq : (C * (M + 1 + K) * cStar ^ (-(3 : ℝ))) / 1 = C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) := by
    ring
  rw [hfrac_eq] at hfrac_ge
  have hCdiv8 : (100000000000000000:ℝ) ≤ C / 8 := by
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 8)]
    have h := hC
    unfold sstarLowerKappa0 at h
    nlinarith only [h]
  have hprodC : (100000000000000000:ℝ) ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) := by
    have h1 : (C * 1 : ℝ) * (1/8) ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) := by
      have hCnn : (0:ℝ) ≤ C := by linarith only [hC, sstarLowerKappa0_pos.le]
      calc C * 1 * (1/8) ≤ C * (M + 1 + K) * (1/8) := by
            have := mul_le_mul_of_nonneg_left hM1Knn hCnn
            nlinarith only [this]
        _ ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) := by
            have hCM1Knn : (0:ℝ) ≤ C * (M + 1 + K) := mul_nonneg hCnn (by linarith only [hM1Knn])
            exact mul_le_mul_of_nonneg_left hcube_ge hCM1Knn
    have h2 : C * 1 * ((1:ℝ)/8) = C / 8 := by ring
    rw [h2] at h1
    linarith only [h1, hCdiv8]
  have hkey : (100000000000000000:ℝ) * ((1:ℝ)/1000000000) ≤
      (C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ))) *
        Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) := by
    have hA : (100000000000000000:ℝ) ≤
        C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) :=
      le_trans hprodC hfrac_ge
    have hAnn : (0:ℝ) ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) :=
      le_trans (by norm_num) hA
    have hBnn : (0:ℝ) ≤ (1:ℝ)/1000000000 := by norm_num
    exact mul_le_mul hA (le_trans hgpow_num hgpow) hBnn hAnn
  have hval : (100000000000000000:ℝ) * ((1:ℝ)/1000000000) = 100000000 := by norm_num
  rw [hval] at hkey
  linarith only [hkey]

/-! ## Step (a): `h` clears the root's own threshold -/

/-- Once `C ≥ 2 C_r κ₀`, `L ≥ L₀(C,M,α,c⋆,ν,K)` and `L ≤ 2h`, `h` clears the
threshold hypothesis of `sigmaBarStar_lower_bound`, with that theorem's constant `C_r`
in place of the target's own `C`. -/
lemma sstarLower_h_clears_threshold {C M alpha cStar nu K C_r : ℝ} {L h : ℕ}
    (hC_r1 : 1 ≤ C_r) (hC : 2 * C_r * sstarLowerKappa0 ≤ C)
    (hM : 1 ≤ M) (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1)
    (hcStar : 0 < cStar) (hcStar2 : cStar ≤ 2) (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hK : 0 ≤ K)
    (hL : SuperdiffusionCLT.Frozen.Section4.lNaught C M alpha cStar nu K ≤ (L:ℝ))
    (hLh : (L:ℝ) ≤ 2 * (h:ℝ)) :
    C_r * cStar ^ (-(3:ℝ)) *
      (Real.log (3 + nu⁻¹ + cStar⁻¹) ^ (3:ℕ) * Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹)) +
        (1 + K) * Real.log (3 + nu⁻¹ + cStar⁻¹ + K)) ≤ (h:ℝ) := by
  have hCr_kappa0_nonneg : (0:ℝ) ≤ C_r * sstarLowerKappa0 :=
    mul_nonneg (by linarith only [hC_r1]) sstarLowerKappa0_pos.le
  have hstep1 : sstarLowerKappa0 ≤ C_r * sstarLowerKappa0 := by
    nlinarith only [hC_r1, sstarLowerKappa0_pos.le]
  have hCkappa0 : sstarLowerKappa0 ≤ C := by linarith only [hstep1, hCr_kappa0_nonneg, hC]
  have hC0 : (0:ℝ) ≤ C := le_trans sstarLowerKappa0_pos.le hCkappa0
  have hInnerGe1 := sstarLower_inner_ge_one hCkappa0 hM halpha0 halpha1 hcStar hcStar2 hnu hnu1 hK
  have hexp1 : (1:ℝ) ≤ 1 / (1 - alpha) := by
    rw [le_div_iff₀ (by linarith only [halpha1] : (0:ℝ) < 1 - alpha)]
    linarith only [halpha0]
  have hInnerLeL0 : lNaughtInner C M alpha cStar nu K ≤
      SuperdiffusionCLT.Frozen.Section4.lNaught C M alpha cStar nu K := by
    show lNaughtInner C M alpha cStar nu K ≤ (lNaughtInner C M alpha cStar nu K) ^ ((1:ℝ)/(1-alpha))
    calc lNaughtInner C M alpha cStar nu K = (lNaughtInner C M alpha cStar nu K) ^ (1:ℝ) :=
          (Real.rpow_one _).symm
      _ ≤ (lNaughtInner C M alpha cStar nu K) ^ ((1:ℝ)/(1-alpha)) :=
          Real.rpow_le_rpow_of_exponent_le hInnerGe1 hexp1
  have hLgeInner : lNaughtInner C M alpha cStar nu K ≤ (L:ℝ) := le_trans hInnerLeL0 hL
  have hhalf : lNaughtInner C M alpha cStar nu K / 2 ≤ (h:ℝ) := by linarith only [hLgeInner, hLh]
  have hGe := sstarLower_inner_ge hC0 hM halpha0 halpha1 hcStar hcStar2 hnu hnu1 hK
  have hCratio : (4:ℝ) * C_r ≤ C * (2 / sstarLowerKappa0) := by
    have heq : C * (2 / sstarLowerKappa0) = 2 * C / sstarLowerKappa0 := by ring
    rw [heq, le_div_iff₀ sstarLowerKappa0_pos]
    nlinarith only [hC]
  have hlog3 : (1:ℝ) < Real.log 3 := by
    have h1 : Real.log (Real.exp 1) < Real.log 3 := by
      apply Real.log_lt_log (Real.exp_pos 1)
      linarith only [Real.exp_one_lt_d9]
    rwa [Real.log_exp] at h1
  have hell3 : (3:ℝ) ≤ 3 + nu⁻¹ + cStar⁻¹ := by
    have h1 := inv_nonneg.mpr hnu.le
    have h2 := inv_nonneg.mpr hcStar.le
    linarith only [h1, h2]
  have hellgt1 : (1:ℝ) < Real.log (3 + nu⁻¹ + cStar⁻¹) := by
    have h1 : Real.log 3 ≤ Real.log (3 + nu⁻¹ + cStar⁻¹) := Real.log_le_log (by norm_num) hell3
    linarith only [h1, hlog3]
  have hbracket_nonneg : (0:ℝ) ≤
      Real.log (3 + nu⁻¹ + cStar⁻¹) ^ (3:ℕ) * Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹)) +
        (1 + K) * Real.log (3 + nu⁻¹ + cStar⁻¹ + K) := by
    have h1 : (0:ℝ) ≤ Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹)) := Real.log_nonneg hellgt1.le
    have h2 : (0:ℝ) ≤ Real.log (3 + nu⁻¹ + cStar⁻¹) ^ (3:ℕ) := by positivity
    have h3 : (0:ℝ) ≤ 1 + K := by linarith only [hK]
    have h4 : (0:ℝ) ≤ 3 + nu⁻¹ + cStar⁻¹ + K := by linarith only [hell3, hK]
    have h5 : (0:ℝ) ≤ Real.log (3 + nu⁻¹ + cStar⁻¹ + K) := by
      have h6 : (1:ℝ) ≤ 3 + nu⁻¹ + cStar⁻¹ + K := by linarith only [hell3, hK]
      exact Real.log_nonneg h6
    have h7 : (0:ℝ) ≤ (1 + K) * Real.log (3 + nu⁻¹ + cStar⁻¹ + K) := mul_nonneg h3 h5
    positivity
  have hcube_nonneg : (0:ℝ) ≤ cStar ^ (-(3:ℝ)) := Real.rpow_nonneg hcStar.le _
  have hbracketC_nonneg : (0:ℝ) ≤
      cStar ^ (-(3:ℝ)) *
        (Real.log (3 + nu⁻¹ + cStar⁻¹) ^ (3:ℕ) * Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹)) +
          (1 + K) * Real.log (3 + nu⁻¹ + cStar⁻¹ + K)) :=
    mul_nonneg hcube_nonneg hbracket_nonneg
  have hCr_nonneg : (0:ℝ) ≤ C_r := by linarith only [hC_r1]
  have hscaled : (4:ℝ) * C_r *
      (cStar ^ (-(3:ℝ)) *
        (Real.log (3 + nu⁻¹ + cStar⁻¹) ^ (3:ℕ) * Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹)) +
          (1 + K) * Real.log (3 + nu⁻¹ + cStar⁻¹ + K))) ≤
      C * (2 / sstarLowerKappa0) *
        (cStar ^ (-(3:ℝ)) *
          (Real.log (3 + nu⁻¹ + cStar⁻¹) ^ (3:ℕ) * Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹)) +
            (1 + K) * Real.log (3 + nu⁻¹ + cStar⁻¹ + K))) :=
    mul_le_mul_of_nonneg_right hCratio hbracketC_nonneg
  have hchain : (4:ℝ) * C_r *
      (cStar ^ (-(3:ℝ)) *
        (Real.log (3 + nu⁻¹ + cStar⁻¹) ^ (3:ℕ) * Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹)) +
          (1 + K) * Real.log (3 + nu⁻¹ + cStar⁻¹ + K))) ≤
      lNaughtInner C M alpha cStar nu K :=
    le_trans hscaled hGe
  have hhalf2 : (2:ℝ) * C_r *
      (cStar ^ (-(3:ℝ)) *
        (Real.log (3 + nu⁻¹ + cStar⁻¹) ^ (3:ℕ) * Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹)) +
          (1 + K) * Real.log (3 + nu⁻¹ + cStar⁻¹ + K))) ≤ (h:ℝ) := by
    have h8 : (0:ℝ) ≤ C_r *
        (cStar ^ (-(3:ℝ)) *
          (Real.log (3 + nu⁻¹ + cStar⁻¹) ^ (3:ℕ) * Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹)) +
            (1 + K) * Real.log (3 + nu⁻¹ + cStar⁻¹ + K))) :=
      mul_nonneg hCr_nonneg hbracketC_nonneg
    linarith only [hchain, hhalf, h8]
  have heqfinal : C_r * cStar ^ (-(3:ℝ)) *
      (Real.log (3 + nu⁻¹ + cStar⁻¹) ^ (3:ℕ) * Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹)) +
        (1 + K) * Real.log (3 + nu⁻¹ + cStar⁻¹ + K)) =
      (2:ℝ) * C_r *
        (cStar ^ (-(3:ℝ)) *
          (Real.log (3 + nu⁻¹ + cStar⁻¹) ^ (3:ℕ) * Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹)) +
            (1 + K) * Real.log (3 + nu⁻¹ + cStar⁻¹ + K))) / 2 := by ring
  rw [heqfinal]
  linarith only [hhalf2]

end SuperdiffusionCLT.Section4.LNaught
