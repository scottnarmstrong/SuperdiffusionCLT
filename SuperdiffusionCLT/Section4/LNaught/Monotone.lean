/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Frozen.Section4.LNaught

@[expose] public section

open Real

namespace SuperdiffusionCLT.Section4.LNaught

noncomputable def lNaughtInner (C M alpha cStar nu K : ℝ) : ℝ :=
  ((C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) /
        ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ))) *
      Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ))

lemma one_minus_alpha_pos {alpha : ℝ} (halpha : alpha < 1) : 0 < 1 - alpha := by
  linarith only [sub_pos.mpr halpha]

lemma outer_exponent_pos {alpha : ℝ} (halpha : alpha < 1) : 0 < (1 : ℝ) / (1 - alpha) := by
  have hpos : 0 < 1 - alpha := one_minus_alpha_pos halpha
  exact div_pos (by norm_num) hpos

lemma log_arg_ge_two {M K cStar nu alpha : ℝ}
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hcStar : 0 < cStar) (hnu : 0 < nu) (halpha : alpha < 1) :
    2 ≤ 2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha)) := by
  have hnum : 0 ≤ M + 1 + K := by
    linarith only [hM, hK]
  have hpow : 0 ≤ cStar ^ (-(3 : ℝ)) :=
    Real.rpow_nonneg (le_of_lt hcStar) _
  have hden : 0 < nu * (1 - alpha) := by
    have h1ma : 0 < 1 - alpha := one_minus_alpha_pos halpha
    exact mul_pos hnu h1ma
  have hfrac : 0 ≤ (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha)) :=
    div_nonneg (mul_nonneg hnum hpow) (le_of_lt hden)
  linarith only [hfrac]

lemma log_pos {M K cStar nu alpha : ℝ}
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hcStar : 0 < cStar) (hnu : 0 < nu) (halpha : alpha < 1) :
    0 < Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) := by
  have hge2 := log_arg_ge_two hM hK hcStar hnu halpha
  have hone : 1 < 2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha)) := by
    linarith only [hge2]
  exact Real.log_pos hone

lemma log_pow_nonneg {M K cStar nu alpha : ℝ}
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hcStar : 0 < cStar) (hnu : 0 < nu) (halpha : alpha < 1) :
    0 ≤ Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) := by
  have hpos := log_pos hM hK hcStar hnu halpha
  exact Real.rpow_nonneg (le_of_lt hpos) (12 : ℝ)

lemma denom_pos {nu alpha : ℝ} (hnu : 0 < nu) (halpha : alpha < 1) :
    0 < (1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ) := by
  have h1ma : 0 < 1 - alpha := one_minus_alpha_pos halpha
  have h1 : 0 < (1 - alpha) ^ (12 : ℝ) := Real.rpow_pos_of_pos h1ma (12 : ℝ)
  have h2 : 0 < nu ^ (4 : ℝ) := Real.rpow_pos_of_pos hnu (4 : ℝ)
  exact mul_pos h1 h2

lemma inner_nonneg {C M alpha cStar nu K : ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hK : 0 ≤ K) (hcStar : 0 < cStar) (hnu : 0 < nu) (halpha : alpha < 1) :
    0 ≤ lNaughtInner C M alpha cStar nu K := by
  unfold lNaughtInner
  have h1ma_pos : 0 < 1 - alpha := one_minus_alpha_pos halpha
  have h_cpow : 0 ≤ cStar ^ (-(3 : ℝ)) := Real.rpow_nonneg (le_of_lt hcStar) _
  have h_denom_pos : 0 < (1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ) := denom_pos hnu halpha
  have h_denom_nonneg : 0 ≤ (1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ) := le_of_lt h_denom_pos
  have h_num_nonneg : 0 ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) :=
    mul_nonneg (mul_nonneg hC (by linarith only [hM, hK])) h_cpow
  have h_frac_nonneg : 0 ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) :=
    div_nonneg h_num_nonneg h_denom_nonneg
  have h_log_pow_nonneg : 0 ≤ Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) :=
    log_pow_nonneg hM hK hcStar hnu halpha
  exact mul_nonneg h_frac_nonneg h_log_pow_nonneg

lemma frac_mono {a b d : ℝ} (h : a ≤ b) (hd : 0 < d) : a / d ≤ b / d := by
  have h_inv_nonneg : 0 ≤ d⁻¹ := inv_nonneg.mpr (le_of_lt hd)
  calc
    a / d = a * d⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ b * d⁻¹ := mul_le_mul_of_nonneg_right h h_inv_nonneg
    _ = b / d := by rw [div_eq_mul_inv]

lemma inner_mono_const {C C' M alpha cStar nu K : ℝ}
    (hCC' : C ≤ C') (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hcStar : 0 < cStar) (hnu : 0 < nu) (halpha : alpha < 1) :
    lNaughtInner C M alpha cStar nu K ≤ lNaughtInner C' M alpha cStar nu K := by
  unfold lNaughtInner
  have h1ma_pos : 0 < 1 - alpha := one_minus_alpha_pos halpha
  have h_cpow : 0 ≤ cStar ^ (-(3 : ℝ)) := Real.rpow_nonneg (le_of_lt hcStar) _
  have h_denom_pos : 0 < (1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ) := denom_pos hnu halpha
  have hM1K : 0 ≤ M + 1 + K := by linarith only [hM, hK]
  have h_factor_mono : C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) ≤ C' * (M + 1 + K) * cStar ^ (-(3 : ℝ)) := by
    have h_base : C * (M + 1 + K) ≤ C' * (M + 1 + K) := mul_le_mul_of_nonneg_right hCC' hM1K
    exact mul_le_mul_of_nonneg_right h_base h_cpow
  have h_frac_mono : C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) ≤
      C' * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) :=
    frac_mono h_factor_mono h_denom_pos
  have h_log_pow_nonneg : 0 ≤ Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) :=
    log_pow_nonneg hM hK hcStar hnu halpha
  exact mul_le_mul_of_nonneg_right h_frac_mono h_log_pow_nonneg

lemma inner_mono_M {C M M' alpha cStar nu K : ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hMM' : M ≤ M') (hK : 0 ≤ K)
    (hcStar : 0 < cStar) (hnu : 0 < nu) (halpha : alpha < 1) :
    lNaughtInner C M alpha cStar nu K ≤ lNaughtInner C M' alpha cStar nu K := by
  unfold lNaughtInner
  have h1ma_pos : 0 < 1 - alpha := one_minus_alpha_pos halpha
  have h_cpow : 0 ≤ cStar ^ (-(3 : ℝ)) := Real.rpow_nonneg (le_of_lt hcStar) _
  have h_denom_pos : 0 < (1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ) := denom_pos hnu halpha
  have h_denom_nonneg : 0 ≤ (1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ) := le_of_lt h_denom_pos
  have hM1K : 0 ≤ M + 1 + K := by linarith only [hM, hK]
  have hM'1K : 0 ≤ M' + 1 + K := by linarith only [hM, hMM', hK]
  have h_log_pow_nonneg_M : 0 ≤ Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) :=
    log_pow_nonneg hM hK hcStar hnu halpha
  have h_factor_mono : C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) ≤ C * (M' + 1 + K) * cStar ^ (-(3 : ℝ)) := by
    have h_le : M + 1 + K ≤ M' + 1 + K := by linarith only [hMM']
    have h_inner : (M + 1 + K) * cStar ^ (-(3 : ℝ)) ≤ (M' + 1 + K) * cStar ^ (-(3 : ℝ)) :=
      mul_le_mul_of_nonneg_right h_le h_cpow
    have h := mul_le_mul_of_nonneg_left h_inner hC
    simpa [mul_assoc] using h
  have h_frac_mono : C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) ≤
      C * (M' + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) :=
    frac_mono h_factor_mono h_denom_pos
  have hden_pos : 0 < nu * (1 - alpha) := mul_pos hnu h1ma_pos
  have h_log_arg_mono : 2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha)) ≤
      2 + (M' + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha)) := by
    have hdiv : (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha)) ≤
        (M' + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha)) :=
      have h_le : M + 1 + K ≤ M' + 1 + K := by linarith only [hMM']
      frac_mono (mul_le_mul_of_nonneg_right h_le h_cpow) hden_pos
    linarith only [hdiv]
  have h_log_pos_M : 0 < 2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha)) := by
    have hge2 := log_arg_ge_two hM hK hcStar hnu halpha
    linarith only [hge2]
  have h_log_mono : Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ≤
      Real.log (2 + (M' + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) :=
    Real.log_le_log h_log_pos_M h_log_arg_mono
  have h_log_pow_mono : Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) ≤
      Real.log (2 + (M' + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) :=
    Real.rpow_le_rpow (le_of_lt (log_pos hM hK hcStar hnu halpha)) h_log_mono (by norm_num : (0 : ℝ) ≤ 12)
  have hpos : 0 ≤ C * (M' + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) :=
    div_nonneg (mul_nonneg (mul_nonneg hC hM'1K) h_cpow) h_denom_nonneg
  have h_first : C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) *
      Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) ≤
      C * (M' + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) *
      Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) :=
    mul_le_mul_of_nonneg_right h_frac_mono h_log_pow_nonneg_M
  have h_second : C * (M' + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) *
      Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) ≤
      C * (M' + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) *
      Real.log (2 + (M' + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) :=
    mul_le_mul_of_nonneg_left h_log_pow_mono hpos
  linarith only [h_first, h_second]

lemma inner_mono_both {C C' M M' alpha cStar nu K : ℝ}
    (hC : 0 ≤ C) (hCC' : C ≤ C') (hM : 0 ≤ M) (hMM' : M ≤ M') (hK : 0 ≤ K)
    (hcStar : 0 < cStar) (hnu : 0 < nu) (halpha : alpha < 1) :
    lNaughtInner C M alpha cStar nu K ≤ lNaughtInner C' M' alpha cStar nu K := by
  have hC' : 0 ≤ C' := by linarith only [hC, hCC']
  have h1 : lNaughtInner C M alpha cStar nu K ≤ lNaughtInner C' M alpha cStar nu K :=
    inner_mono_const hCC' hM hK hcStar hnu halpha
  have h2 : lNaughtInner C' M alpha cStar nu K ≤ lNaughtInner C' M' alpha cStar nu K :=
    inner_mono_M hC' hM hMM' hK hcStar hnu halpha
  linarith only [h1, h2]

theorem lNaught_nonneg {C M alpha cStar nu K : ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hK : 0 ≤ K) (hcStar : 0 < cStar) (hnu : 0 < nu) (halpha : alpha < 1) :
    0 ≤ SuperdiffusionCLT.Frozen.Section4.lNaught C M alpha cStar nu K := by
  unfold SuperdiffusionCLT.Frozen.Section4.lNaught
  have h_inner_nonneg : 0 ≤ lNaughtInner C M alpha cStar nu K :=
    inner_nonneg hC hM hK hcStar hnu halpha
  have h_exp_pos : 0 ≤ (1 : ℝ) / (1 - alpha) := le_of_lt (outer_exponent_pos halpha)
  exact Real.rpow_nonneg h_inner_nonneg _

theorem lNaught_mono_const {C C' M alpha cStar nu K : ℝ}
    (hC : 0 ≤ C) (hCC' : C ≤ C') (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hcStar : 0 < cStar) (hnu : 0 < nu) (halpha : alpha < 1) :
    SuperdiffusionCLT.Frozen.Section4.lNaught C M alpha cStar nu K ≤
    SuperdiffusionCLT.Frozen.Section4.lNaught C' M alpha cStar nu K := by
  unfold SuperdiffusionCLT.Frozen.Section4.lNaught
  have h_inner_mono : lNaughtInner C M alpha cStar nu K ≤ lNaughtInner C' M alpha cStar nu K :=
    inner_mono_const hCC' hM hK hcStar hnu halpha
  have h_inner_nonneg : 0 ≤ lNaughtInner C M alpha cStar nu K :=
    inner_nonneg hC hM hK hcStar hnu halpha
  have h_exp_pos : 0 ≤ (1 : ℝ) / (1 - alpha) := le_of_lt (outer_exponent_pos halpha)
  exact Real.rpow_le_rpow h_inner_nonneg h_inner_mono h_exp_pos

theorem lNaught_mono_M {C M M' alpha cStar nu K : ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hMM' : M ≤ M') (hK : 0 ≤ K)
    (hcStar : 0 < cStar) (hnu : 0 < nu) (halpha : alpha < 1) :
    SuperdiffusionCLT.Frozen.Section4.lNaught C M alpha cStar nu K ≤
    SuperdiffusionCLT.Frozen.Section4.lNaught C M' alpha cStar nu K := by
  unfold SuperdiffusionCLT.Frozen.Section4.lNaught
  have h_inner_mono : lNaughtInner C M alpha cStar nu K ≤ lNaughtInner C M' alpha cStar nu K :=
    inner_mono_M hC hM hMM' hK hcStar hnu halpha
  have h_inner_nonneg : 0 ≤ lNaughtInner C M alpha cStar nu K :=
    inner_nonneg hC hM hK hcStar hnu halpha
  have h_exp_pos : 0 ≤ (1 : ℝ) / (1 - alpha) := le_of_lt (outer_exponent_pos halpha)
  exact Real.rpow_le_rpow h_inner_nonneg h_inner_mono h_exp_pos

theorem lNaught_mono_both {C C' M M' alpha cStar nu K : ℝ}
    (hC : 0 ≤ C) (hCC' : C ≤ C') (hM : 0 ≤ M) (hMM' : M ≤ M') (hK : 0 ≤ K)
    (hcStar : 0 < cStar) (hnu : 0 < nu) (halpha : alpha < 1) :
    SuperdiffusionCLT.Frozen.Section4.lNaught C M alpha cStar nu K ≤
    SuperdiffusionCLT.Frozen.Section4.lNaught C' M' alpha cStar nu K := by
  unfold SuperdiffusionCLT.Frozen.Section4.lNaught
  have h_inner_mono : lNaughtInner C M alpha cStar nu K ≤ lNaughtInner C' M' alpha cStar nu K :=
    inner_mono_both hC hCC' hM hMM' hK hcStar hnu halpha
  have h_inner_nonneg : 0 ≤ lNaughtInner C M alpha cStar nu K :=
    inner_nonneg hC hM hK hcStar hnu halpha
  have h_exp_pos : 0 ≤ (1 : ℝ) / (1 - alpha) := le_of_lt (outer_exponent_pos halpha)
  exact Real.rpow_le_rpow h_inner_nonneg h_inner_mono h_exp_pos

end SuperdiffusionCLT.Section4.LNaught
