/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.NewMixing.LogGrowth

/-!
# The `ν⁴`-explicit `L₀` lower bound, and `ν⁻⁴ ≤ C' L` once `L ≥ L₀`

`LogGrowth.lean`'s `newMixParam_lNaughtInner_ge` bounds `lNaughtInner` below by
`(C²/4)(log 2)¹²`, discarding the `ν⁴` denominator's own contribution (via
`ν⁴ ≤ 1`). This file keeps `ν⁻⁴` explicit instead — the same computation with
one inequality reversed — giving `lNaughtInner ≥ (C²/4)(log 2)¹² ν⁻⁴`, hence
(once `lNaught ≥ lNaughtInner`, `LogGrowth.lean`'s own threshold argument)
`L ≥ L₀ ⟹ ν⁻⁴ ≤ (4/(C²(log 2)¹²)) · L`: a **linear-in-`L`** bound on `ν⁻⁴`,
needed for `l.new.mixing.parameterized#T0-refinement` to
absorb the crude growth bound's `ν⁻¹` factor against `m^{-3000}`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.NewMixing

open SuperdiffusionCLT.Section4.LNaught

noncomputable section

/-- **`lNaughtInner` with `ν⁻⁴` kept explicit**: for `M ≥ 2C`, `C ≥ 1`,
`0 < cStar ≤ 2`, `0 < ν ≤ 1`, `alpha < 1`,
`lNaughtInner C M alpha cStar nu K ≥ (C²/4) (log 2)¹² ν⁻⁴`. -/
theorem newMixParam_lNaughtInner_ge_nu4 {C M alpha cStar nu K : ℝ}
    (hC : 1 ≤ C) (hM : 2 * C ≤ M) (hK : 0 ≤ K) (hcStar : 0 < cStar) (hcStar2 : cStar ≤ 2)
    (hnu : 0 < nu) (hα0 : 0 ≤ alpha) (halpha : alpha < 1) :
    (C ^ 2 / 4) * (Real.log 2) ^ (12 : ℝ) * nu ^ (-(4 : ℝ)) ≤
      lNaughtInner C M alpha cStar nu K := by
  have h1ma_pos : (0 : ℝ) < 1 - alpha := one_minus_alpha_pos halpha
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC
  have hMnn : (0 : ℝ) ≤ M := le_trans (by positivity) hM
  have hKnn : (0 : ℝ) ≤ K := hK
  unfold lNaughtInner
  have hcpow : (1 : ℝ) / 8 ≤ cStar ^ (-(3 : ℝ)) := newMixParam_cStar_neg3_ge hcStar hcStar2
  have hcpow_nn : (0 : ℝ) ≤ cStar ^ (-(3 : ℝ)) := le_trans (by norm_num) hcpow
  have hnum : (C ^ 2 / 4 : ℝ) ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) := by
    have h1 : (2 * C : ℝ) ≤ M + 1 + K := by linarith only [hM, hKnn]
    have h2 : C * (2 * C) ≤ C * (M + 1 + K) := mul_le_mul_of_nonneg_left h1 hCpos.le
    have h3 : C * (2 * C) * ((1 : ℝ) / 8) ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) := by
      have h3a : (0 : ℝ) ≤ C * (2 * C) := by positivity
      calc C * (2 * C) * ((1 : ℝ) / 8) ≤ C * (M + 1 + K) * ((1 : ℝ) / 8) :=
            mul_le_mul_of_nonneg_right h2 (by norm_num)
        _ ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) := by
            apply mul_le_mul_of_nonneg_left hcpow
            exact mul_nonneg hCpos.le (by linarith only [hMnn, hKnn])
    have heq : C * (2 * C) * ((1 : ℝ) / 8) = C ^ 2 / 4 := by ring
    linarith only [h3, heq.ge, heq.le]
  have hnum_nn : (0 : ℝ) ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) := le_trans (by positivity) hnum
  -- `(1-alpha)^12 ≤ 1`, so the denominator `(1-alpha)^12 * nu^4 ≤ nu^4`.
  have h1ma12le1 : (1 - alpha) ^ (12 : ℝ) ≤ 1 := by
    have h1a : (1 - alpha) ≤ 1 := by linarith only [hα0]
    calc (1 - alpha) ^ (12 : ℝ) ≤ (1 : ℝ) ^ (12 : ℝ) :=
          Real.rpow_le_rpow h1ma_pos.le h1a (by norm_num)
      _ = 1 := Real.one_rpow _
  have hnu4pos : (0 : ℝ) < nu ^ (4 : ℝ) := Real.rpow_pos_of_pos hnu _
  have hdenle : (1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ) ≤ nu ^ (4 : ℝ) := by
    calc (1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ) ≤ 1 * nu ^ (4 : ℝ) :=
          mul_le_mul_of_nonneg_right h1ma12le1 hnu4pos.le
      _ = nu ^ (4 : ℝ) := one_mul _
  have hdenpos : (0 : ℝ) < (1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ) := denom_pos hnu halpha
  -- `(C²/4)/ν⁴ ≤ (C²/4)/((1-alpha)^12 ν⁴) ≤ numerator/((1-alpha)^12 ν⁴)`.
  have hstep1 : (C ^ 2 / 4 : ℝ) / nu ^ (4 : ℝ) ≤
      (C ^ 2 / 4 : ℝ) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) :=
    div_le_div_of_nonneg_left (by positivity) hdenpos hdenle
  have hstep2 : (C ^ 2 / 4 : ℝ) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) ≤
      C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) :=
    div_le_div_of_nonneg_right hnum hdenpos.le
  have hfrac : (C ^ 2 / 4 : ℝ) / nu ^ (4 : ℝ) ≤
      C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) :=
    le_trans hstep1 hstep2
  -- Log factor ≥ `(log 2)^12`, since the log argument is ≥ 2.
  have hlogarg : (2 : ℝ) ≤ 2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha)) :=
    log_arg_ge_two hMnn hKnn hcStar hnu halpha
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogmono : Real.log 2 ≤
      Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) :=
    Real.log_le_log (by norm_num) hlogarg
  have hlogpow : (Real.log 2) ^ (12 : ℝ) ≤
      Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) :=
    Real.rpow_le_rpow hlog2.le hlogmono (by norm_num)
  have hfracnn : (0 : ℝ) ≤
      C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) :=
    div_nonneg hnum_nn hdenpos.le
  have hlog2pow12nn : (0 : ℝ) ≤ (Real.log 2) ^ (12 : ℝ) := Real.rpow_nonneg hlog2.le _
  have hfracdivnn : (0 : ℝ) ≤ (C ^ 2 / 4 : ℝ) / nu ^ (4 : ℝ) := by positivity
  have hchain : (C ^ 2 / 4 : ℝ) / nu ^ (4 : ℝ) * (Real.log 2) ^ (12 : ℝ) ≤
      (C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ))) *
        Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) := by
    calc (C ^ 2 / 4 : ℝ) / nu ^ (4 : ℝ) * (Real.log 2) ^ (12 : ℝ)
        ≤ (C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ))) *
            (Real.log 2) ^ (12 : ℝ) := mul_le_mul_of_nonneg_right hfrac hlog2pow12nn
      _ ≤ (C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ))) *
            Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) :=
          mul_le_mul_of_nonneg_left hlogpow hfracnn
  have heq : (C ^ 2 / 4 : ℝ) / nu ^ (4 : ℝ) * (Real.log 2) ^ (12 : ℝ) =
      (C ^ 2 / 4) * (Real.log 2) ^ (12 : ℝ) * nu ^ (-(4 : ℝ)) := by
    rw [Real.rpow_neg hnu.le, div_eq_mul_inv]
    ring
  linarith only [hchain, heq.le, heq.ge]

/-- **`ν⁻⁴` grows at most linearly in `L`, once `L ≥ L₀`**: for `M ≥ 2C`,
`C ≥ 100000`, `0 < cStar ≤ 2`, `0 < ν ≤ 1`, `0 ≤ alpha < 1`,
`L ≥ lNaught C M alpha cStar nu K` implies `ν⁻⁴ ≤ (4/(C²(log 2)¹²)) · L`. -/
theorem newMixParam_nu4_le_linear_L {C M alpha cStar nu K : ℝ}
    (hC : (100000 : ℝ) ≤ C) (hM : 2 * C ≤ M) (hK : 0 ≤ K) (hcStar : 0 < cStar)
    (hcStar2 : cStar ≤ 2) (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hα0 : 0 ≤ alpha) (halpha : alpha < 1)
    {L : ℕ} (hL : SuperdiffusionCLT.Frozen.Section4.lNaught C M alpha cStar nu K ≤ (L : ℝ)) :
    nu ^ (-(4 : ℝ)) ≤ (4 / (C ^ 2 * (Real.log 2) ^ (12 : ℝ))) * (L : ℝ) := by
  have hC1 : (1 : ℝ) ≤ C := le_trans (by norm_num) hC
  have hInner := newMixParam_lNaughtInner_ge_nu4 hC1 hM hK hcStar hcStar2 hnu hα0 halpha
  -- `lNaught ≥ lNaughtInner`, exactly as in `newMixParam_logL_ge_sixteen`.
  have hCsqpos : (0 : ℝ) < C ^ 2 / 4 := by positivity
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2pow12pos : (0 : ℝ) < (Real.log 2) ^ (12 : ℝ) := Real.rpow_pos_of_pos hlog2 _
  have hnu4invpos : (0 : ℝ) < nu ^ (-(4 : ℝ)) := Real.rpow_pos_of_pos hnu _
  have hInnerPos : (0 : ℝ) < (C ^ 2 / 4) * (Real.log 2) ^ (12 : ℝ) * nu ^ (-(4 : ℝ)) := by
    positivity
  have hInnerPosV : (0 : ℝ) < lNaughtInner C M alpha cStar nu K :=
    lt_of_lt_of_le hInnerPos hInner
  have h1ma_pos : (0 : ℝ) < 1 - alpha := one_minus_alpha_pos halpha
  have hexpge1 : (1 : ℝ) ≤ (1 : ℝ) / (1 - alpha) := by
    rw [le_div_iff₀ h1ma_pos]; linarith only [hα0]
  have hNaughtGeInner : lNaughtInner C M alpha cStar nu K ≤
      SuperdiffusionCLT.Frozen.Section4.lNaught C M alpha cStar nu K := by
    rw [newMixParam_lNaught_eq_inner_rpow]
    have h1 : lNaughtInner C M alpha cStar nu K ^ (1 : ℝ) ≤
        lNaughtInner C M alpha cStar nu K ^ ((1 : ℝ) / (1 - alpha)) := by
      have hbase1 : (1 : ℝ) ≤ lNaughtInner C M alpha cStar nu K := by
        have hnu4ge1 : (1 : ℝ) ≤ nu ^ (-(4 : ℝ)) := by
          have h := Real.rpow_le_rpow_of_exponent_ge hnu hnu1 (show (-(4 : ℝ)) ≤ 0 by norm_num)
          rwa [Real.rpow_zero] at h
        have hCsq1 : (1 : ℝ) ≤ (C ^ 2 / 4) * (Real.log 2) ^ (12 : ℝ) := by
          have hlog2gt : (69 : ℝ) / 100 < Real.log 2 := by
            have h := Real.log_two_gt_d9; linarith only [h]
          have hlog2nn : (0 : ℝ) ≤ (69 : ℝ) / 100 := by norm_num
          have hlog2pow : ((69 : ℝ) / 100) ^ (12 : ℝ) ≤ (Real.log 2) ^ (12 : ℝ) :=
            Real.rpow_le_rpow hlog2nn hlog2gt.le (by norm_num)
          have hlog2pow_eq : ((69 : ℝ) / 100) ^ (12 : ℝ) = ((69 : ℝ) / 100) ^ (12 : ℕ) := by
            rw [show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          have hClarge : (100000 : ℝ) ^ 2 ≤ C ^ 2 := by nlinarith only [hC]
          have hval : (1 : ℝ) ≤ (100000 : ℝ) ^ 2 / 4 * (((69 : ℝ) / 100) ^ (12 : ℕ)) := by
            norm_num
          nlinarith only [hClarge, hlog2pow, hlog2pow_eq, hval]
        have h1le : (1 : ℝ) ≤ (C ^ 2 / 4) * (Real.log 2) ^ (12 : ℝ) * nu ^ (-(4 : ℝ)) := by
          nlinarith only [hCsq1, hnu4ge1, hlog2pow12pos, hCsqpos]
        linarith only [hInner, h1le]
      exact Real.rpow_le_rpow_of_exponent_le hbase1 hexpge1
    rwa [Real.rpow_one] at h1
  have hL' : lNaughtInner C M alpha cStar nu K ≤ (L : ℝ) := le_trans hNaughtGeInner hL
  have hfinal : (C ^ 2 / 4) * (Real.log 2) ^ (12 : ℝ) * nu ^ (-(4 : ℝ)) ≤ (L : ℝ) :=
    le_trans hInner hL'
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0 : ℝ) < C ^ 2 * (Real.log 2) ^ (12 : ℝ))]
  nlinarith only [hfinal]

end
end SuperdiffusionCLT.Section4.NewMixing
