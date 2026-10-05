/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.LNaught.Threshold
public import SuperdiffusionCLT.Section4.NewMixing.ScaleConstruction

/-!
# `log L` grows without bound as the `L₀` threshold grows: the missing 10th
scale-construction fact

The printed bound is `3^{-h} ≤ m^{-12000}`
(only claimed, and only needed downstream, in the `m ≤ L+h` branch).  This
file supplies the numeric ingredient `Threshold.lean` does not expose
(`lNaught_ge` only gives `L > 8`): a *quantitative* lower bound on
`Real.log L`, growing with the constant `C`, derived directly from
`lNaughtInner`'s public closed form and `lNaught = lNaughtInner ^ (1/(1-α))`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.NewMixing

open SuperdiffusionCLT.Section4.LNaught

noncomputable section

/-- `log 3 > 13/12`, since `e^13 < 2.72^13 < 3^12`. Sharper than
the bound `log 3 > 1`, needed
here to dominate the additive `+ log 2` gap between `log m` and `log L`. -/
theorem newMixParam_log3_gt_13_div_12 : (13:ℝ) / 12 < Real.log 3 := by
  have he13 : Real.exp 13 < (2.72:ℝ) ^ (13:ℕ) := by
    have h1 : Real.exp 1 < 2.72 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have h2 : (0:ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
    have h3 : Real.exp 13 = (Real.exp 1) ^ (13:ℕ) := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [h3]
    exact pow_lt_pow_left₀ h1 h2 (by norm_num)
  have h4 : (2.72:ℝ) ^ (13:ℕ) < 531441 := by norm_num
  have h5 : (531441:ℝ) = (3:ℝ) ^ (12:ℕ) := by norm_num
  have h6 : Real.exp 13 < (3:ℝ) ^ (12:ℕ) := by rw [← h5]; linarith only [he13, h4]
  have h7 : (13:ℝ) = Real.log (Real.exp 13) := (Real.log_exp 13).symm
  have h8 : Real.log (Real.exp 13) < Real.log ((3:ℝ) ^ (12:ℕ)) :=
    Real.log_lt_log (Real.exp_pos 13) h6
  have h9 : Real.log ((3:ℝ) ^ (12:ℕ)) = 12 * Real.log 3 := by
    rw [Real.log_pow]; push_cast; ring
  rw [← h7, h9] at h8
  linarith only [h8]

/-- `cStar ^ (-3) ≥ 1/8` for `0 < cStar ≤ 2`. -/
theorem newMixParam_cStar_neg3_ge {cStar : ℝ} (hcStar : 0 < cStar) (hcStar2 : cStar ≤ 2) :
    (1 : ℝ) / 8 ≤ cStar ^ (-(3 : ℝ)) := by
  have h3 : cStar ^ (-(3 : ℝ)) = (cStar ^ (3 : ℕ))⁻¹ := by
    rw [show (-(3:ℝ)) = -((3:ℕ):ℝ) by norm_num, Real.rpow_neg hcStar.le, Real.rpow_natCast]
  rw [h3]
  have hle8 : cStar ^ (3 : ℕ) ≤ 8 := by
    calc cStar ^ (3:ℕ) ≤ (2:ℝ) ^ (3:ℕ) := pow_le_pow_left₀ hcStar.le hcStar2 3
      _ = 8 := by norm_num
  have hpos : (0:ℝ) < cStar ^ (3:ℕ) := pow_pos hcStar 3
  have hinv := one_div_le_one_div_of_le hpos hle8
  simpa using hinv

/-- The `lNaughtInner` lower bound powering the `log L` growth: for
`M ≥ 2 C` (matching this task's own use, `M := C*(M₀+K₀)` with `M₀, K₀ ≥ 1`)
and `C ≥ 1`, `0 < cStar ≤ 2`, `0 < nu ≤ 1`, `alpha < 1`,
`lNaughtInner C M alpha cStar nu K ≥ (C^2 / 4) * (Real.log 2)^(12:ℝ)`. -/
theorem newMixParam_lNaughtInner_ge {C M alpha cStar nu K : ℝ}
    (hC : 1 ≤ C) (hM : 2 * C ≤ M) (hK : 0 ≤ K) (hcStar : 0 < cStar) (hcStar2 : cStar ≤ 2)
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hα0 : 0 ≤ alpha) (halpha : alpha < 1) :
    (C ^ 2 / 4) * (Real.log 2) ^ (12 : ℝ) ≤ lNaughtInner C M alpha cStar nu K := by
  have h1ma_pos : (0:ℝ) < 1 - alpha := one_minus_alpha_pos halpha
  have hCpos : (0:ℝ) < C := lt_of_lt_of_le one_pos hC
  have hMnn : (0:ℝ) ≤ M := le_trans (by positivity) hM
  have hKnn : (0:ℝ) ≤ K := hK
  unfold lNaughtInner
  have hcpow : (1:ℝ)/8 ≤ cStar ^ (-(3:ℝ)) := newMixParam_cStar_neg3_ge hcStar hcStar2
  have hcpow_nn : (0:ℝ) ≤ cStar ^ (-(3:ℝ)) := le_trans (by norm_num) hcpow
  -- Numerator: `C * (M+1+K) * cStar^{-3} ≥ C * (2C) * (1/8) = C²/4`.
  have hnum : (C ^ 2 / 4 : ℝ) ≤ C * (M + 1 + K) * cStar ^ (-(3:ℝ)) := by
    have h1 : (2 * C : ℝ) ≤ M + 1 + K := by linarith only [hM, hKnn]
    have h2 : C * (2 * C) ≤ C * (M + 1 + K) := mul_le_mul_of_nonneg_left h1 hCpos.le
    have h3 : C * (2 * C) * ((1:ℝ)/8) ≤ C * (M + 1 + K) * cStar ^ (-(3:ℝ)) := by
      have h3a : (0:ℝ) ≤ C * (2 * C) := by positivity
      calc C * (2 * C) * ((1:ℝ)/8) ≤ C * (M+1+K) * ((1:ℝ)/8) :=
            mul_le_mul_of_nonneg_right h2 (by norm_num)
        _ ≤ C * (M+1+K) * cStar ^ (-(3:ℝ)) := by
            apply mul_le_mul_of_nonneg_left hcpow
            exact mul_nonneg hCpos.le (by linarith only [hMnn, hKnn])
    have heq : C * (2 * C) * ((1:ℝ)/8) = C ^ 2 / 4 := by ring
    linarith only [h3, heq.ge, heq.le]
  -- Denominator ≤ 1: `(1-α)^12 * nu^4 ≤ 1`.
  have hdenle1 : (1 - alpha) ^ (12:ℝ) * nu ^ (4:ℝ) ≤ 1 := by
    have h1 : (1 - alpha) ^ (12:ℝ) ≤ 1 := by
      have h1a : (1 - alpha) ≤ 1 := by linarith only [hα0]
      calc (1 - alpha) ^ (12:ℝ) ≤ (1:ℝ) ^ (12:ℝ) :=
            Real.rpow_le_rpow h1ma_pos.le h1a (by norm_num)
        _ = 1 := Real.one_rpow _
    have h2 : nu ^ (4:ℝ) ≤ 1 := by
      calc nu ^ (4:ℝ) ≤ (1:ℝ) ^ (4:ℝ) := Real.rpow_le_rpow hnu.le hnu1 (by norm_num)
        _ = 1 := Real.one_rpow _
    have h1nn : (0:ℝ) ≤ (1 - alpha) ^ (12:ℝ) := Real.rpow_nonneg h1ma_pos.le _
    have h2nn : (0:ℝ) ≤ nu ^ (4:ℝ) := Real.rpow_nonneg hnu.le _
    calc (1 - alpha) ^ (12:ℝ) * nu ^ (4:ℝ) ≤ 1 * nu ^ (4:ℝ) :=
          mul_le_mul_of_nonneg_right h1 h2nn
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = 1 := by ring
  have hdenpos : (0:ℝ) < (1 - alpha) ^ (12:ℝ) * nu ^ (4:ℝ) := denom_pos hnu halpha
  have hfrac : C * (M + 1 + K) * cStar ^ (-(3:ℝ)) ≤
      C * (M + 1 + K) * cStar ^ (-(3:ℝ)) / ((1 - alpha) ^ (12:ℝ) * nu ^ (4:ℝ)) := by
    have hnumnn : (0:ℝ) ≤ C * (M + 1 + K) * cStar ^ (-(3:ℝ)) := by
      apply mul_nonneg (mul_nonneg hCpos.le _) hcpow_nn
      linarith only [hMnn, hKnn]
    calc C * (M + 1 + K) * cStar ^ (-(3:ℝ))
        = C * (M + 1 + K) * cStar ^ (-(3:ℝ)) / 1 := by ring
      _ ≤ C * (M + 1 + K) * cStar ^ (-(3:ℝ)) / ((1 - alpha) ^ (12:ℝ) * nu ^ (4:ℝ)) := by
          apply div_le_div_of_nonneg_left hnumnn hdenpos hdenle1
  -- Log factor ≥ (log 2)^12, since the log argument is ≥ 2.
  have hlogarg : (2:ℝ) ≤ 2 + (M + 1 + K) * cStar ^ (-(3:ℝ)) / (nu * (1 - alpha)) :=
    log_arg_ge_two hMnn hKnn hcStar hnu halpha
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogmono : Real.log 2 ≤
      Real.log (2 + (M + 1 + K) * cStar ^ (-(3:ℝ)) / (nu * (1 - alpha))) :=
    Real.log_le_log (by norm_num) hlogarg
  have hlogpownn : (0:ℝ) ≤ Real.log 2 := hlog2.le
  have hlogpow : (Real.log 2) ^ (12:ℝ) ≤
      Real.log (2 + (M + 1 + K) * cStar ^ (-(3:ℝ)) / (nu * (1 - alpha))) ^ (12:ℝ) :=
    Real.rpow_le_rpow hlogpownn hlogmono (by norm_num)
  have hfracnn : (0:ℝ) ≤ C * (M + 1 + K) * cStar ^ (-(3:ℝ)) / ((1 - alpha) ^ (12:ℝ) * nu ^ (4:ℝ)) := by
    apply div_nonneg _ hdenpos.le
    apply mul_nonneg (mul_nonneg hCpos.le _) hcpow_nn
    linarith only [hMnn, hKnn]
  have hlog2pow12nn : (0:ℝ) ≤ (Real.log 2) ^ (12:ℝ) := Real.rpow_nonneg hlogpownn _
  calc (C ^ 2 / 4) * (Real.log 2) ^ (12:ℝ)
      ≤ (C * (M + 1 + K) * cStar ^ (-(3:ℝ)) / ((1 - alpha) ^ (12:ℝ) * nu ^ (4:ℝ))) *
          (Real.log 2) ^ (12:ℝ) := by
        apply mul_le_mul_of_nonneg_right _ hlog2pow12nn
        linarith only [hnum, hfrac]
    _ ≤ (C * (M + 1 + K) * cStar ^ (-(3:ℝ)) / ((1 - alpha) ^ (12:ℝ) * nu ^ (4:ℝ))) *
          Real.log (2 + (M + 1 + K) * cStar ^ (-(3:ℝ)) / (nu * (1 - alpha))) ^ (12:ℝ) :=
        mul_le_mul_of_nonneg_left hlogpow hfracnn

/-- `lNaught`'s definition literally is `lNaughtInner ^ (1/(1-α))`. -/
theorem newMixParam_lNaught_eq_inner_rpow (C M alpha cStar nu K : ℝ) :
    SuperdiffusionCLT.Frozen.Section4.lNaught C M alpha cStar nu K =
      (lNaughtInner C M alpha cStar nu K) ^ ((1:ℝ) / (1 - alpha)) := by
  unfold SuperdiffusionCLT.Frozen.Section4.lNaught lNaughtInner
  rfl

/-- If `L ≥ lNaught C M alpha cStar nu K` with `M ≥ 2C`, `C ≥ 1`, `0 ≤ alpha < 1`,
`0 < cStar ≤ 2`, `0 < nu ≤ 1`, `0 ≤ K`, and `100000 ≤ C`, then `16 ≤ Real.log L`
(in fact far more, but `16` already suffices downstream — it is used to give
`12 ≤ Real.log L`, itself enough to absorb the `+ log 2` gap between `log m`
and `log L` against the sharp `log 3 > 13/12` bound). -/
theorem newMixParam_logL_ge_sixteen {C M alpha cStar nu K : ℝ}
    (hC : (100000:ℝ) ≤ C) (hM : 2 * C ≤ M) (hK : 0 ≤ K) (hcStar : 0 < cStar)
    (hcStar2 : cStar ≤ 2) (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hα0 : 0 ≤ alpha) (halpha : alpha < 1)
    {L : ℕ} (hL : SuperdiffusionCLT.Frozen.Section4.lNaught C M alpha cStar nu K ≤ (L:ℝ)) :
    (16:ℝ) ≤ Real.log (L:ℝ) := by
  have hC1 : (1:ℝ) ≤ C := le_trans (by norm_num) hC
  have hInner := newMixParam_lNaughtInner_ge hC1 hM hK hcStar hcStar2 hnu hnu1 hα0 halpha
  -- `log 2 > 69/100` and `exp 16 < 3^15`.
  have hlog2 : (69:ℝ)/100 < Real.log 2 := by
    have h := Real.log_two_gt_d9
    linarith only [h]
  have hlog2nn : (0:ℝ) ≤ (69:ℝ)/100 := by norm_num
  have hlog2pow : ((69:ℝ)/100) ^ (12:ℝ) ≤ (Real.log 2) ^ (12:ℝ) :=
    Real.rpow_le_rpow hlog2nn hlog2.le (by norm_num)
  have hlog2pow_eq : ((69:ℝ)/100) ^ (12:ℝ) = ((69:ℝ)/100) ^ (12:ℕ) := by
    rw [show (12:ℝ) = ((12:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have hCsq : (C^2 / 4) * (((69:ℝ)/100) ^ (12:ℕ)) ≤ (C^2/4) * (Real.log 2) ^ (12:ℝ) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith only [hlog2pow, hlog2pow_eq]
  have hCsqval : (14348907:ℝ) ≤ (C^2/4) * (((69:ℝ)/100) ^ (12:ℕ)) := by
    have hCsq' : (100000:ℝ)^2 ≤ C^2 := by nlinarith only [hC]
    nlinarith only [hCsq']
  have hexp16 : Real.exp 16 < (3:ℝ) ^ (15:ℕ) := by
    have he : Real.exp 16 = (Real.exp 1) ^ (16:ℕ) := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [he]
    have h1 : Real.exp 1 < 2.72 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have h2 : (0:ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
    have h3 : (2.72:ℝ) ^ (16:ℕ) < (3:ℝ) ^ (15:ℕ) := by norm_num
    exact lt_trans (pow_lt_pow_left₀ h1 h2 (by norm_num)) h3
  have hexp16val : (3:ℝ) ^ (15:ℕ) = 14348907 := by norm_num
  have hfinal : Real.exp 16 ≤ (C^2/4) * (Real.log 2) ^ (12:ℝ) := by
    rw [hexp16val] at hexp16
    linarith only [hexp16, hCsqval, hCsq]
  have hInnerPos : (0:ℝ) < (C^2/4) * (Real.log 2) ^ (12:ℝ) :=
    lt_of_lt_of_le (Real.exp_pos 16) hfinal
  have hlogInnerGe16 : (16:ℝ) ≤ Real.log (lNaughtInner C M alpha cStar nu K) := by
    have h1 : (16:ℝ) ≤ Real.log ((C^2/4) * (Real.log 2) ^ (12:ℝ)) := by
      have h2 := Real.log_le_log (Real.exp_pos 16) hfinal
      rwa [Real.log_exp] at h2
    have h3 : Real.log ((C^2/4) * (Real.log 2) ^ (12:ℝ)) ≤
        Real.log (lNaughtInner C M alpha cStar nu K) :=
      Real.log_le_log hInnerPos hInner
    linarith only [h1, h3]
  -- `Real.log (lNaught) = (1/(1-α)) * Real.log(lNaughtInner) ≥ Real.log(lNaughtInner)`,
  -- since `1/(1-α) ≥ 1` and `Real.log(lNaughtInner) ≥ 16 ≥ 0`.
  have hInnerPosV : (0:ℝ) < lNaughtInner C M alpha cStar nu K := lt_of_lt_of_le hInnerPos hInner
  have h1ma_pos : (0:ℝ) < 1 - alpha := one_minus_alpha_pos halpha
  have hexppos : (0:ℝ) < (1:ℝ) / (1 - alpha) := outer_exponent_pos halpha
  have hexpge1 : (1:ℝ) ≤ (1:ℝ) / (1 - alpha) := by
    rw [le_div_iff₀ h1ma_pos]
    linarith only [hα0]
  have hlogNaughtEq : Real.log (SuperdiffusionCLT.Frozen.Section4.lNaught C M alpha cStar nu K) =
      ((1:ℝ) / (1 - alpha)) * Real.log (lNaughtInner C M alpha cStar nu K) := by
    rw [newMixParam_lNaught_eq_inner_rpow]
    exact Real.log_rpow hInnerPosV _
  have hlogNaughtGe : Real.log (lNaughtInner C M alpha cStar nu K) ≤
      Real.log (SuperdiffusionCLT.Frozen.Section4.lNaught C M alpha cStar nu K) := by
    rw [hlogNaughtEq]
    have h16nn : (0:ℝ) ≤ Real.log (lNaughtInner C M alpha cStar nu K) :=
      le_trans (by norm_num) hlogInnerGe16
    nlinarith only [hexpge1, h16nn]
  have hNaughtPos : (0:ℝ) < SuperdiffusionCLT.Frozen.Section4.lNaught C M alpha cStar nu K := by
    rw [newMixParam_lNaught_eq_inner_rpow]
    exact Real.rpow_pos_of_pos hInnerPosV _
  have hLpos : (0:ℝ) < (L:ℝ) := lt_of_lt_of_le hNaughtPos hL
  have hlogLge : Real.log (SuperdiffusionCLT.Frozen.Section4.lNaught C M alpha cStar nu K) ≤
      Real.log (L:ℝ) := Real.log_le_log hNaughtPos hL
  linarith only [hlogInnerGe16, hlogNaughtGe, hlogLge]

/-! ## The missing 10th scale-construction fact -/

/-- `K * L^alpha * Real.log L ^ 3 ≤ L / (2*C)` transported down to
`K * Real.log L ≤ L / (2*C)`, reusable outside `ScaleConstruction.lean`
(which proves the identical fact inline). Needs `1 ≤ L` and `1 ≤ Real.log L`. -/
private theorem newMixParam_KlogL_le_slack {C K alpha : ℝ} {L : ℕ}
    (hK : 0 ≤ K) (hα0 : 0 ≤ alpha) (hL1 : (1:ℝ) ≤ (L:ℝ)) (hlogL1 : (1:ℝ) ≤ Real.log (L:ℝ))
    (hKLslack : K * (L:ℝ) ^ alpha * Real.log (L:ℝ) ^ (3:ℝ) ≤ (L:ℝ) / (2 * C)) :
    K * Real.log (L:ℝ) ≤ (L:ℝ) / (2 * C) := by
  have hlogLnn : (0:ℝ) ≤ Real.log (L:ℝ) := le_trans zero_le_one hlogL1
  have hLalpha1 : (1:ℝ) ≤ (L:ℝ) ^ alpha := newMixParam_one_le_rpow hL1 hα0
  have hlog3geLog : Real.log (L:ℝ) ≤ Real.log (L:ℝ) ^ (3:ℝ) :=
    newMixParam_le_rpow_three hlogL1
  have hlog3nn : (0:ℝ) ≤ Real.log (L:ℝ) ^ (3:ℝ) := le_trans hlogLnn hlog3geLog
  have hstepLE : Real.log (L:ℝ) ≤ (L:ℝ) ^ alpha * Real.log (L:ℝ) ^ (3:ℝ) := by
    calc Real.log (L:ℝ) ≤ Real.log (L:ℝ) ^ (3:ℝ) := hlog3geLog
      _ = 1 * Real.log (L:ℝ) ^ (3:ℝ) := (one_mul _).symm
      _ ≤ (L:ℝ) ^ alpha * Real.log (L:ℝ) ^ (3:ℝ) :=
        mul_le_mul_of_nonneg_right hLalpha1 hlog3nn
  have h1 : K * Real.log (L:ℝ) ≤ K * ((L:ℝ) ^ alpha * Real.log (L:ℝ) ^ (3:ℝ)) :=
    mul_le_mul_of_nonneg_left hstepLE hK
  have h2 : K * ((L:ℝ) ^ alpha * Real.log (L:ℝ) ^ (3:ℝ)) =
      K * (L:ℝ) ^ alpha * Real.log (L:ℝ) ^ (3:ℝ) := by ring
  rw [h2] at h1
  exact le_trans h1 hKLslack

/-- `h ≤ L / 4`, reusable outside `ScaleConstruction.lean` (which proves the
identical fact inline for its own local `h`). Needs `C ≥ 100000`, `1 ≤ K`,
`1 ≤ Real.log L`. -/
private theorem newMixParam_h_le_L_div_4 {C K : ℝ} {L : ℕ}
    (hC100000 : (100000:ℝ) ≤ C) (hK1 : (1:ℝ) ≤ K) (hlogL1 : (1:ℝ) ≤ Real.log (L:ℝ))
    (hKlogL_le_slack : K * Real.log (L:ℝ) ≤ (L:ℝ) / (2 * C)) :
    (newMixParam_h K (Real.log (L:ℝ)) : ℝ) ≤ (L:ℝ) / 4 := by
  have hLnn : (0:ℝ) ≤ (L:ℝ) := Nat.cast_nonneg L
  have hx1 : (1:ℝ) ≤ newMixParam_K0 * K * Real.log (L:ℝ) := by
    unfold newMixParam_K0
    nlinarith only [hK1, hlogL1]
  have hhle := newMixParam_h_le hx1
  have hK0eq : newMixParam_K0 = 12000 := rfl
  have h1 : (newMixParam_h K (Real.log (L:ℝ)) : ℝ) ≤ 24000 * (K * Real.log (L:ℝ)) := by
    have heqassoc : newMixParam_K0 * K * Real.log (L:ℝ) =
        newMixParam_K0 * (K * Real.log (L:ℝ)) := by ring
    rw [heqassoc, hK0eq] at hhle
    linarith only [hhle]
  have h2 : (24000:ℝ) * (K * Real.log (L:ℝ)) ≤ 24000 * ((L:ℝ) / (2 * C)) :=
    mul_le_mul_of_nonneg_left hKlogL_le_slack (by norm_num)
  have h3 : (L:ℝ) / (2 * C) ≤ (L:ℝ) / 200000 := by
    apply div_le_div_of_nonneg_left hLnn (by norm_num)
    linarith only [hC100000]
  have h4 : (24000:ℝ) * ((L:ℝ) / 200000) ≤ (L:ℝ) / 4 := by
    have heq : (24000:ℝ) * ((L:ℝ) / 200000) = (L:ℝ) * (24000/200000) := by ring
    rw [heq]
    have heq2 : (L:ℝ) / 4 = (L:ℝ) * (1/4) := by ring
    rw [heq2]
    apply mul_le_mul_of_nonneg_left _ hLnn
    norm_num
  linarith only [h1, h2, h3, h4]

/-- **The missing 10th scale-construction fact**, `3^{-h} ≤ m^{-12000}`, in the `m ≤ L+h` branch
of the case split of `newMixAsm_scaleExplicit`, for
`h := newMixParam_h K (Real.log L)` (the *same* deterministic function of
`K, L` that the scale construction uses). Existentially quantifies its own `C`, exposing
`100000 ≤ C` in addition to the bare `1 ≤ C` of the scale construction
(both built from the *same* `newMixParam_absorbSlack` witness `C₀`, via
`max C₀ 100000`, so a caller combining the two results with the *same*
concrete `C` witness — e.g. by re-deriving both from one shared
`obtain ⟨C0, _, _⟩ := newMixParam_absorbSlack` — gets a consistent picture;
this theorem does not itself force that reuse). -/
theorem newMixParam_threeNegH_le_mNeg12000 :
    ∃ C : ℝ, 1 ≤ C ∧ (100000:ℝ) ≤ C ∧
      ∀ (M K alpha cStar nu nondeg : ℝ),
        1 ≤ M → 1 ≤ K → 0 ≤ alpha → alpha < 1 → 0 < cStar → cStar ≤ 2 → 0 < nu → nu ≤ 1 →
        0 ≤ nondeg →
        ∀ L m : ℕ,
          SuperdiffusionCLT.Frozen.Section4.lNaught C (C * (M + K)) alpha cStar nu nondeg ≤
            (L:ℝ) →
          SuperdiffusionCLT.Frozen.Section4.lNaught C (C * (M + K)) alpha cStar nu nondeg ≤
            (m:ℝ) →
          m ≤ L + newMixParam_h K (Real.log (L:ℝ)) →
          (3:ℝ) ^ (-(newMixParam_h K (Real.log (L:ℝ)) : ℝ)) ≤ (m:ℝ) ^ (-(12000:ℝ)) := by
  obtain ⟨C0, hC0, hslack⟩ := newMixParam_absorbSlack
  refine ⟨max C0 100000, le_trans hC0 (le_max_left _ _), le_max_right _ _, ?_⟩
  intro M K alpha cStar nu nondeg hM hK hα0 hα1 hcStar hcStar2 hnu hnu1 hnondeg L m hL hm hcaseA
  set C := max C0 100000 with hCdef
  have hC0' : C0 ≤ C := le_max_left _ _
  have hC : (100000:ℝ) ≤ C := le_max_right _ _
  have h2CleM : 2 * C ≤ C * (M + K) := by nlinarith only [hC, hM, hK]
  have hlogL16 : (16:ℝ) ≤ Real.log (L:ℝ) :=
    newMixParam_logL_ge_sixteen hC h2CleM hnondeg hcStar hcStar2 hnu hnu1 hα0 hα1 hL
  have hlogL12 : (12:ℝ) ≤ Real.log (L:ℝ) := by linarith only [hlogL16]
  have hL1 : (1:ℝ) < (L:ℝ) := by
    by_contra hcon
    push Not at hcon
    have := Real.log_nonpos (Nat.cast_nonneg L) hcon
    linarith only [hlogL16, this]
  have hKnn : (0:ℝ) ≤ K := le_trans zero_le_one hK
  set h := newMixParam_h K (Real.log (L:ℝ)) with hhdef
  have hCpos : (0:ℝ) < C := lt_of_lt_of_le (by norm_num) hC
  have hMtot : K * (L:ℝ) ^ alpha * Real.log (L:ℝ) ^ (3:ℝ) ≤ (L:ℝ) / (2 * C) := by
    obtain ⟨_, _, hKLslack⟩ := hslack C hC0' M K alpha cStar nu nondeg hM hK hα0 hα1 hcStar
      hcStar2 hnu hnu1 hnondeg L hL
    exact hKLslack
  have hKlogL_le_slack : K * Real.log (L:ℝ) ≤ (L:ℝ) / (2 * C) :=
    newMixParam_KlogL_le_slack hKnn hα0 hL1.le (by linarith only [hlogL12]) hMtot
  have hhleL4 : (h:ℝ) ≤ (L:ℝ) / 4 :=
    newMixParam_h_le_L_div_4 hC hK (by linarith only [hlogL12]) hKlogL_le_slack
  have hmL2 : (m:ℝ) ≤ 2 * (L:ℝ) := by
    have hmL : (m:ℝ) ≤ (L:ℝ) + (h:ℝ) := by exact_mod_cast hcaseA
    linarith only [hmL, hhleL4]
  have hlogm16 : (16:ℝ) ≤ Real.log (m:ℝ) :=
    newMixParam_logL_ge_sixteen hC h2CleM hnondeg hcStar hcStar2 hnu hnu1 hα0 hα1 hm
  have hm1 : (1:ℝ) < (m:ℝ) := by
    by_contra hcon
    push Not at hcon
    have := Real.log_nonpos (Nat.cast_nonneg m) hcon
    linarith only [hlogm16, this]
  -- `log m ≤ log L + log 2`.
  have hlogm_le : Real.log (m:ℝ) ≤ Real.log (L:ℝ) + Real.log 2 := by
    have hstep := Real.log_le_log (by linarith only [hm1] : (0:ℝ) < (m:ℝ)) hmL2
    rw [Real.log_mul (by norm_num) (by linarith only [hL1])] at hstep
    linarith only [hstep]
  have hlog2lt1 : Real.log 2 < 1 := lt_trans Real.log_two_lt_d9 (by norm_num)
  have hhge := @newMixParam_h_ge K (Real.log (L:ℝ))
  have hK0eq : newMixParam_K0 = 12000 := rfl
  have hhge12000K : (12000:ℝ) * K * Real.log (L:ℝ) ≤ (h:ℝ) := by
    rw [hhdef]; rw [hK0eq] at hhge; exact hhge
  have hlog3gt : (13:ℝ)/12 < Real.log 3 := newMixParam_log3_gt_13_div_12
  have hlog3nn : (0:ℝ) ≤ Real.log 3 := le_trans (by norm_num) hlog3gt.le
  -- `log L * (log 3 - 1) ≥ 12 * (1/12) = 1 > log 2`, so `log L * log 3 ≥ log L + log 2 ≥ log m`.
  have hlogLlog3 : Real.log (L:ℝ) + Real.log 2 ≤ Real.log (L:ℝ) * Real.log 3 := by
    have hprod : (12:ℝ) * ((13:ℝ)/12 - 1) ≤ Real.log (L:ℝ) * (Real.log 3 - 1) := by
      apply mul_le_mul hlogL12 (by linarith only [hlog3gt]) (by norm_num) (by linarith only [hlogL12])
    have hprodval : (12:ℝ) * ((13:ℝ)/12 - 1) = 1 := by norm_num
    nlinarith only [hprod, hprodval, hlog2lt1]
  have hlogm_leLlog3 : Real.log (m:ℝ) ≤ Real.log (L:ℝ) * Real.log 3 := by
    linarith only [hlogm_le, hlogLlog3]
  -- `K * (log L * log 3) ≥ log L * log 3 ≥ log m` (using `K ≥ 1`).
  have hKLlog3 : Real.log (L:ℝ) * Real.log 3 ≤ K * (Real.log (L:ℝ) * Real.log 3) := by
    have hLlog3nn : (0:ℝ) ≤ Real.log (L:ℝ) * Real.log 3 := by positivity
    nlinarith only [hK, hLlog3nn]
  have hchain : (12000:ℝ) * Real.log (m:ℝ) ≤ (h:ℝ) * Real.log 3 := by
    have hstep1 : (12000:ℝ) * Real.log (m:ℝ) ≤ 12000 * (K * (Real.log (L:ℝ) * Real.log 3)) := by
      nlinarith only [hlogm_leLlog3, hKLlog3]
    have hstep2 : (12000:ℝ) * (K * (Real.log (L:ℝ) * Real.log 3)) =
        (12000 * K * Real.log (L:ℝ)) * Real.log 3 := by ring
    have hstep3 : (12000 * K * Real.log (L:ℝ)) * Real.log 3 ≤ (h:ℝ) * Real.log 3 :=
      mul_le_mul_of_nonneg_right hhge12000K hlog3nn
    linarith only [hstep1, hstep2.le, hstep2.ge, hstep3]
  -- Convert to `3^{-h} ≤ m^{-12000}` via `Real.exp`/`log` algebra.
  have hmpos : (0:ℝ) < (m:ℝ) := by linarith only [hm1]
  have h3pos : (0:ℝ) < (3:ℝ) := by norm_num
  have heq3 : (3:ℝ) ^ (-(h:ℝ)) = Real.exp (-(h:ℝ) * Real.log 3) := by
    rw [Real.rpow_def_of_pos h3pos]
    congr 1
    ring
  have heqm : (m:ℝ) ^ (-(12000:ℝ)) = Real.exp (-(12000:ℝ) * Real.log (m:ℝ)) := by
    rw [Real.rpow_def_of_pos hmpos]
    congr 1
    ring
  rw [heq3, heqm]
  apply Real.exp_le_exp.mpr
  linarith only [hchain]

end
end SuperdiffusionCLT.Section4.NewMixing
