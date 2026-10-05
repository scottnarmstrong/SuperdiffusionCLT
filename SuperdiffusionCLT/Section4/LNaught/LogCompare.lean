/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.LNaught.Threshold

/-!
# Logarithmic comparisons around `L₀`

Three consequences of the defining threshold property of `L₀`
(`SuperdiffusionCLT.Frozen.Section4.lNaught`, display `e.Lnaught.def` of the paper)
used downstream in Section 4's mixing-scale
constructions: once `L ≥ L₀` and `n` is within the absorbed correction of `L`,
a `Cmix`-scaled `log(nu⁻¹ L)` is dominated by `n` (`lNaught_log_le_n`);
`log(nu⁻¹ L)` and `log(nu⁻¹ n)` agree up to a factor `2` (`lNaught_log_ratio`);
and `L₀` is monotone under rescaling `M` by a factor `K' ≥ 1`, at the cost of
an explicit `K'`-dependent inflation of the constant `C` (`lNaught_mul_M_le`).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.LNaught

open Real

/-! ## A fixed positive constant used to calibrate `C`-thresholds -/

/-- `(log 2)^12 / 4`, the constant that appears in the elementary lower bound
`lNaught_ge_c1_div_nu4` on `L₀` in terms of `C` and `ν`. -/
private noncomputable def logCompareC1 : ℝ := (Real.log 2) ^ (12 : ℝ) / 4

private lemma logCompareC1_pos : 0 < logCompareC1 := by
  have hlog2pos : (0 : ℝ) < Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hpow : (0 : ℝ) < (Real.log 2) ^ (12 : ℝ) := Real.rpow_pos_of_pos hlog2pos _
  unfold logCompareC1
  linarith only [hpow]

/-! ## The key lower bound: `L₀ ≥ C · c₁ / ν⁴` once `C` clears a fixed threshold -/

/-- For `C ≥ 4/(log 2)^12`, `L₀(C,M,α,c⋆,ν,K) ≥ C · logCompareC1 / ν⁴`: each factor
of `L₀`'s defining expression is bounded below by its extreme value over the
standing ranges `M ≥ 1`, `K ≥ 0`, `c⋆ ∈ (0,2]`, `α ∈ [0,1)`, except `ν⁴` in the
denominator, which is kept explicit. -/
private lemma lNaught_ge_c1_div_nu4 {C M alpha cStar nu K : ℝ}
    (hC : 4 / (Real.log 2) ^ (12 : ℝ) ≤ C) (hM : 1 ≤ M) (hK : 0 ≤ K)
    (hcStar : 0 < cStar) (hcStar2 : cStar ≤ 2) (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1) :
    C * logCompareC1 / nu ^ (4 : ℝ) ≤
      SuperdiffusionCLT.Frozen.Section4.lNaught C M alpha cStar nu K := by
  have hlog2pos : (0 : ℝ) < Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hlog2powpos : (0 : ℝ) < (Real.log 2) ^ (12 : ℝ) := Real.rpow_pos_of_pos hlog2pos _
  have h1ma_pos : 0 < 1 - alpha := by linarith only [halpha1]
  have h1ma_nonneg : 0 ≤ 1 - alpha := h1ma_pos.le
  have h1ma_le1 : 1 - alpha ≤ 1 := by linarith only [halpha0]
  have hnu4pos : 0 < nu ^ (4 : ℝ) := Real.rpow_pos_of_pos hnu _
  have hC_pos : 0 < C := lt_of_lt_of_le (div_pos (by norm_num) hlog2powpos) hC
  have hC_nonneg : 0 ≤ C := hC_pos.le
  have hcStar3 : (1 / 8 : ℝ) ≤ cStar ^ (-(3 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_nonpos hcStar hcStar2 (by norm_num : (-(3 : ℝ)) ≤ 0)
    have h2 : (2 : ℝ) ^ (-(3 : ℝ)) = 1 / 8 := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    rw [h2] at h
    exact h
  have hcStar3pos : 0 < cStar ^ (-(3 : ℝ)) := Real.rpow_pos_of_pos hcStar _
  have hMK2 : (2 : ℝ) ≤ M + 1 + K := by linarith only [hM, hK]
  have hMK2nonneg : (0 : ℝ) ≤ M + 1 + K := by linarith only [hMK2]
  have h_num_ge : C / 4 ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) := by
    have ha : C * 2 ≤ C * (M + 1 + K) := mul_le_mul_of_nonneg_left hMK2 hC_nonneg
    have hb : C * (M + 1 + K) * (1 / 8 : ℝ) ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) :=
      mul_le_mul_of_nonneg_left hcStar3 (mul_nonneg hC_nonneg hMK2nonneg)
    have hc : C * 2 * (1 / 8 : ℝ) ≤ C * (M + 1 + K) * (1 / 8 : ℝ) :=
      mul_le_mul_of_nonneg_right ha (by norm_num)
    have heq : C * 2 * (1 / 8 : ℝ) = C / 4 := by ring
    linarith only [hc, hb, heq]
  have h_denom_le : (1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ) ≤ nu ^ (4 : ℝ) := by
    have h1ma12_le1 : (1 - alpha) ^ (12 : ℝ) ≤ 1 := by
      calc (1 - alpha) ^ (12 : ℝ) ≤ (1 : ℝ) ^ (12 : ℝ) :=
            Real.rpow_le_rpow h1ma_nonneg h1ma_le1 (by norm_num)
        _ = 1 := Real.one_rpow _
    have hmul : (1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ) ≤ 1 * nu ^ (4 : ℝ) :=
      mul_le_mul_of_nonneg_right h1ma12_le1 hnu4pos.le
    linarith only [hmul]
  have h_denom_pos : 0 < (1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ) := by
    have h1ma12pos : 0 < (1 - alpha) ^ (12 : ℝ) := Real.rpow_pos_of_pos h1ma_pos _
    exact mul_pos h1ma12pos hnu4pos
  have h_coeff_ge : C / 4 / nu ^ (4 : ℝ) ≤
      C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) := by
    have hstep1 : C / 4 / nu ^ (4 : ℝ) ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / nu ^ (4 : ℝ) :=
      div_le_div_of_nonneg_right h_num_ge hnu4pos.le
    have hstep2 : C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / nu ^ (4 : ℝ) ≤
        C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) :=
      div_le_div_of_nonneg_left
        (mul_nonneg (mul_nonneg hC_nonneg hMK2nonneg) hcStar3pos.le) h_denom_pos h_denom_le
    linarith only [hstep1, hstep2]
  have h_log_arg_ge2 : (2 : ℝ) ≤ 2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha)) := by
    have hfrac_nonneg : 0 ≤ (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha)) :=
      div_nonneg (mul_nonneg hMK2nonneg hcStar3pos.le) (mul_nonneg hnu.le h1ma_nonneg)
    linarith only [hfrac_nonneg]
  have h_log_ge_log2 : Real.log 2 ≤
      Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) :=
    Real.log_le_log (by norm_num) h_log_arg_ge2
  have h_log_pow_ge : (Real.log 2) ^ (12 : ℝ) ≤
      Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) :=
    Real.rpow_le_rpow hlog2pos.le h_log_ge_log2 (by norm_num)
  have hcoeff2_nonneg : 0 ≤
      C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) :=
    div_nonneg (mul_nonneg (mul_nonneg hC_nonneg hMK2nonneg) hcStar3pos.le) h_denom_pos.le
  have h_inner_ge : C / 4 / nu ^ (4 : ℝ) * (Real.log 2) ^ (12 : ℝ) ≤
      lNaughtInner C M alpha cStar nu K := by
    unfold lNaughtInner
    calc C / 4 / nu ^ (4 : ℝ) * (Real.log 2) ^ (12 : ℝ)
        ≤ (C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ))) *
            (Real.log 2) ^ (12 : ℝ) :=
          mul_le_mul_of_nonneg_right h_coeff_ge hlog2powpos.le
      _ ≤ (C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ))) *
            Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) :=
          mul_le_mul_of_nonneg_left h_log_pow_ge hcoeff2_nonneg
  have heq2 : C / 4 / nu ^ (4 : ℝ) * (Real.log 2) ^ (12 : ℝ) = C * logCompareC1 / nu ^ (4 : ℝ) := by
    unfold logCompareC1
    ring
  rw [heq2] at h_inner_ge
  have hnu4_le1 : nu ^ (4 : ℝ) ≤ 1 := by
    calc nu ^ (4 : ℝ) ≤ (1 : ℝ) ^ (4 : ℝ) := Real.rpow_le_rpow hnu.le hnu1 (by norm_num)
      _ = 1 := Real.one_rpow _
  have h4 : (4 : ℝ) ≤ C * (Real.log 2) ^ (12 : ℝ) := by
    rw [div_le_iff₀ hlog2powpos] at hC
    linarith only [hC]
  have hClogC1_ge1 : (1 : ℝ) ≤ C * logCompareC1 := by
    have heq3 : C * logCompareC1 = C * (Real.log 2) ^ (12 : ℝ) / 4 := by
      unfold logCompareC1; ring
    rw [heq3]
    linarith only [h4]
  have hCL_nonneg : 0 ≤ C * logCompareC1 := by linarith only [hClogC1_ge1]
  have hcoeff_ge1 : (1 : ℝ) ≤ C * logCompareC1 / nu ^ (4 : ℝ) := by
    have hstep : C * logCompareC1 * nu ^ (4 : ℝ) ≤ C * logCompareC1 := by
      calc C * logCompareC1 * nu ^ (4 : ℝ) ≤ C * logCompareC1 * 1 :=
            mul_le_mul_of_nonneg_left hnu4_le1 hCL_nonneg
        _ = C * logCompareC1 := by ring
    have hdiv : C * logCompareC1 ≤ C * logCompareC1 / nu ^ (4 : ℝ) := by
      rw [le_div_iff₀ hnu4pos]
      linarith only [hstep]
    linarith only [hClogC1_ge1, hdiv]
  have hinner_ge1 : (1 : ℝ) ≤ lNaughtInner C M alpha cStar nu K := by
    linarith only [hcoeff_ge1, h_inner_ge]
  have hexp_ge1 : (1 : ℝ) ≤ (1 : ℝ) / (1 - alpha) := by
    rw [le_div_iff₀ h1ma_pos]
    linarith only [h1ma_le1]
  have hbase_le_rpow : lNaughtInner C M alpha cStar nu K ≤
      (lNaughtInner C M alpha cStar nu K) ^ ((1 : ℝ) / (1 - alpha)) := by
    have h := Real.rpow_le_rpow_of_exponent_le hinner_ge1 hexp_ge1
    rwa [Real.rpow_one] at h
  unfold SuperdiffusionCLT.Frozen.Section4.lNaught
  calc C * logCompareC1 / nu ^ (4 : ℝ)
      ≤ lNaughtInner C M alpha cStar nu K := h_inner_ge
    _ ≤ (lNaughtInner C M alpha cStar nu K) ^ ((1 : ℝ) / (1 - alpha)) := hbase_le_rpow

/-! ## Elementary logarithm bounds -/

/-- `log x ≤ x` for `x > 0`. -/
private lemma logCompare_log_le_x {x : ℝ} (hx : 0 < x) : Real.log x ≤ x := by
  have h := Real.log_le_sub_one_of_pos hx
  linarith only [h]

/-- `log x ≤ 2 √x` for `x > 0`. -/
private lemma logCompare_log_le_two_sqrt {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ 2 * Real.sqrt x := by
  set y := Real.sqrt x with hydef
  have hypos : 0 < y := Real.sqrt_pos.mpr hx
  have hlogy : Real.log y ≤ y - 1 := Real.log_le_sub_one_of_pos hypos
  have hlogx_eq : Real.log x = 2 * Real.log y := by
    calc Real.log x = Real.log (y ^ 2) := by rw [hydef, Real.sq_sqrt hx.le]
      _ = 2 * Real.log y := by rw [Real.log_pow, Nat.cast_ofNat]
  rw [hlogx_eq]
  linarith only [hlogy]

/-- For `ν ∈ (0,1]`, `ν⁻¹ ≤ ν^{-4}`. -/
private lemma logCompare_nu_inv_le_nu_neg_four {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1) :
    nu⁻¹ ≤ nu ^ (-(4 : ℝ)) := by
  have hnuneg3 : (1 : ℝ) ≤ nu ^ (-(3 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_nonpos hnu hnu1 (by norm_num : (-(3 : ℝ)) ≤ 0)
    rwa [Real.one_rpow] at h
  have hnuneg1pos : 0 < nu ^ (-(1 : ℝ)) := Real.rpow_pos_of_pos hnu _
  calc nu⁻¹ = nu ^ (-(1 : ℝ)) := by rw [Real.rpow_neg hnu.le 1, Real.rpow_one]
    _ = nu ^ (-(1 : ℝ)) * 1 := by ring
    _ ≤ nu ^ (-(1 : ℝ)) * nu ^ (-(3 : ℝ)) :=
        mul_le_mul_of_nonneg_left hnuneg3 hnuneg1pos.le
    _ = nu ^ ((-(1 : ℝ)) + (-(3 : ℝ))) := (Real.rpow_add hnu (-(1 : ℝ)) (-(3 : ℝ))).symm
    _ = nu ^ (-(4 : ℝ)) := by norm_num

/-- If `t^2 ≤ L` and `0 ≤ L`, then `t * √L ≤ L`. -/
private lemma logCompare_mul_sqrt_le {t L : ℝ} (hL : 0 ≤ L) (hbound : t ^ 2 ≤ L) :
    t * Real.sqrt L ≤ L := by
  have hsqrt_ge : t ≤ Real.sqrt L := Real.le_sqrt_of_sq_le hbound
  have hsqrt_nonneg : 0 ≤ Real.sqrt L := Real.sqrt_nonneg L
  have hmul : t * Real.sqrt L ≤ Real.sqrt L * Real.sqrt L :=
    mul_le_mul_of_nonneg_right hsqrt_ge hsqrt_nonneg
  rwa [Real.mul_self_sqrt hL] at hmul

/-! ## Theorem 1: `Cmix log(ν⁻¹ L) ≤ n` once `L ≥ L₀` and `n` absorbs the correction -/

theorem lNaught_log_le_n :
    ∀ Cmix : ℝ, 1 ≤ Cmix → ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C →
      ∀ M : ℝ, 1 ≤ M → ∀ alpha : ℝ, 0 ≤ alpha → alpha < 1 →
      ∀ cStar : ℝ, 0 < cStar → cStar ≤ 2 → ∀ nu : ℝ, 0 < nu → nu ≤ 1 → ∀ K : ℝ, 0 ≤ K →
      ∀ L : ℕ, SuperdiffusionCLT.Frozen.Section4.lNaught C M alpha cStar nu K ≤ (L : ℝ) →
        ∀ n : ℕ, (L : ℝ) - M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (n : ℝ) →
          Cmix * Real.log (nu⁻¹ * (L : ℝ)) ≤ (n : ℝ) := by
  intro Cmix hCmix
  have hCmix_nonneg : (0 : ℝ) ≤ Cmix := by linarith only [hCmix]
  obtain ⟨C_absorb, hC_absorb_ge1, h_absorb_body⟩ := lNaught_absorbs
  obtain ⟨C_ge, hC_ge_ge1, h_ge_body⟩ := lNaught_ge
  have hlog2pos : (0 : ℝ) < Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hlog2powpos : (0 : ℝ) < (Real.log 2) ^ (12 : ℝ) := Real.rpow_pos_of_pos hlog2pos _
  have hlogC1pos : 0 < logCompareC1 := logCompareC1_pos
  set term1 : ℝ := 4 / (Real.log 2) ^ (12 : ℝ) with hterm1def
  set term2 : ℝ := 64 * Cmix ^ 2 / logCompareC1 with hterm2def
  set term3 : ℝ := 4 * Cmix / logCompareC1 with hterm3def
  set C0 : ℝ := max (max C_absorb C_ge) (max term1 (max term2 term3)) with hC0def
  have hC0_absorb : C_absorb ≤ C0 := le_trans (le_max_left C_absorb C_ge) (le_max_left _ _)
  have hC0_ge : C_ge ≤ C0 := le_trans (le_max_right C_absorb C_ge) (le_max_left _ _)
  have hC0_term1 : term1 ≤ C0 := le_trans (le_max_left term1 (max term2 term3)) (le_max_right _ _)
  have hC0_term2 : term2 ≤ C0 :=
    le_trans (le_trans (le_max_left term2 term3) (le_max_right term1 (max term2 term3)))
      (le_max_right _ _)
  have hC0_term3 : term3 ≤ C0 :=
    le_trans (le_trans (le_max_right term2 term3) (le_max_right term1 (max term2 term3)))
      (le_max_right _ _)
  have hC0ge1 : (1 : ℝ) ≤ C0 := le_trans hC_absorb_ge1 hC0_absorb
  refine ⟨C0, hC0ge1, ?_⟩
  intro C hC M hM alpha halpha0 halpha1 cStar hcStar hcStar2 nu hnu hnu1 K hK L hL n hn
  have h_absorb := h_absorb_body C (le_trans hC0_absorb hC) M hM alpha halpha0 halpha1 cStar
    hcStar hcStar2 nu hnu hnu1 K hK L hL
  have hn_ge_Lhalf : (L : ℝ) / 2 ≤ (n : ℝ) := by linarith only [hn, h_absorb]
  have hL_gt8 := h_ge_body C (le_trans hC0_ge hC) M hM alpha halpha0 halpha1 cStar hcStar
    hcStar2 nu hnu hnu1 K hK
  have hL_gt8' : (8 : ℝ) < (L : ℝ) := lt_of_lt_of_le hL_gt8 hL
  have hLpos : 0 < (L : ℝ) := by linarith only [hL_gt8']
  have hL_ge_c1 : C * logCompareC1 / nu ^ (4 : ℝ) ≤ (L : ℝ) :=
    le_trans
      (lNaught_ge_c1_div_nu4 (le_trans hC0_term1 hC) hM hK hcStar hcStar2 hnu hnu1 halpha0
        halpha1)
      hL
  have hnu4pos : 0 < nu ^ (4 : ℝ) := Real.rpow_pos_of_pos hnu _
  have hnu4_le1 : nu ^ (4 : ℝ) ≤ 1 := by
    calc nu ^ (4 : ℝ) ≤ (1 : ℝ) ^ (4 : ℝ) := Real.rpow_le_rpow hnu.le hnu1 (by norm_num)
      _ = 1 := Real.one_rpow _
  have hC_nonneg : 0 ≤ C := by linarith only [hC0ge1, hC]
  have hCL_nonneg : 0 ≤ C * logCompareC1 := mul_nonneg hC_nonneg hlogC1pos.le
  have hL_ge_Cc1 : C * logCompareC1 ≤ (L : ℝ) := by
    have hstep : C * logCompareC1 ≤ C * logCompareC1 / nu ^ (4 : ℝ) := by
      rw [le_div_iff₀ hnu4pos]
      have h1 : C * logCompareC1 * nu ^ (4 : ℝ) ≤ C * logCompareC1 * 1 :=
        mul_le_mul_of_nonneg_left hnu4_le1 hCL_nonneg
      linarith only [h1]
    linarith only [hstep, hL_ge_c1]
  have hC_term2 : term2 ≤ C := le_trans hC0_term2 hC
  have hL_ge_64Cmix2 : (64 : ℝ) * Cmix ^ 2 ≤ (L : ℝ) := by
    have h1 : (64 : ℝ) * Cmix ^ 2 ≤ C * logCompareC1 := by
      rw [hterm2def, div_le_iff₀ hlogC1pos] at hC_term2
      linarith only [hC_term2]
    linarith only [h1, hL_ge_Cc1]
  have hC_term3 : term3 ≤ C := le_trans hC0_term3 hC
  have hL_ge_4Cmix_div_nu4 : 4 * Cmix / nu ^ (4 : ℝ) ≤ (L : ℝ) := by
    have h1 : (4 : ℝ) * Cmix ≤ C * logCompareC1 := by
      rw [hterm3def, div_le_iff₀ hlogC1pos] at hC_term3
      linarith only [hC_term3]
    have h2 : 4 * Cmix / nu ^ (4 : ℝ) ≤ C * logCompareC1 / nu ^ (4 : ℝ) :=
      div_le_div_of_nonneg_right h1 hnu4pos.le
    linarith only [h2, hL_ge_c1]
  have hCmix_nu4_le : Cmix * nu ^ (-(4 : ℝ)) ≤ (L : ℝ) / 4 := by
    have hrw : nu ^ (-(4 : ℝ)) = (nu ^ (4 : ℝ))⁻¹ := Real.rpow_neg hnu.le 4
    rw [hrw, ← div_eq_mul_inv]
    have heq : (4 : ℝ) * (Cmix / nu ^ (4 : ℝ)) = 4 * Cmix / nu ^ (4 : ℝ) := by ring
    linarith only [hL_ge_4Cmix_div_nu4, heq]
  have hsq : (8 * Cmix) ^ 2 ≤ (L : ℝ) := by
    have heq : (8 * Cmix) ^ 2 = 64 * Cmix ^ 2 := by ring
    linarith only [heq, hL_ge_64Cmix2]
  have h8Cmix_sqrtL_le : 8 * Cmix * Real.sqrt (L : ℝ) ≤ (L : ℝ) :=
    logCompare_mul_sqrt_le hLpos.le hsq
  have h2Cmix_sqrtL_le : 2 * Cmix * Real.sqrt (L : ℝ) ≤ (L : ℝ) / 4 := by
    have heq : 8 * Cmix * Real.sqrt (L : ℝ) = 4 * (2 * Cmix * Real.sqrt (L : ℝ)) := by ring
    linarith only [h8Cmix_sqrtL_le, heq]
  have hlog_split : Real.log (nu⁻¹ * (L : ℝ)) = Real.log nu⁻¹ + Real.log (L : ℝ) :=
    Real.log_mul (inv_ne_zero hnu.ne') hLpos.ne'
  have hlog_nu_inv_le_nu4 : Real.log nu⁻¹ ≤ nu ^ (-(4 : ℝ)) := by
    have h1 : Real.log nu⁻¹ ≤ nu⁻¹ := logCompare_log_le_x (by positivity)
    have h2 : nu⁻¹ ≤ nu ^ (-(4 : ℝ)) := logCompare_nu_inv_le_nu_neg_four hnu hnu1
    linarith only [h1, h2]
  have hCmix_log_nu_inv_le : Cmix * Real.log nu⁻¹ ≤ Cmix * nu ^ (-(4 : ℝ)) :=
    mul_le_mul_of_nonneg_left hlog_nu_inv_le_nu4 hCmix_nonneg
  have hlog_L_le : Real.log (L : ℝ) ≤ 2 * Real.sqrt (L : ℝ) := logCompare_log_le_two_sqrt hLpos
  have hCmix_logL_le : Cmix * Real.log (L : ℝ) ≤ 2 * Cmix * Real.sqrt (L : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hlog_L_le hCmix_nonneg
    have heq : Cmix * (2 * Real.sqrt (L : ℝ)) = 2 * Cmix * Real.sqrt (L : ℝ) := by ring
    linarith only [h, heq]
  have hfinal : Cmix * Real.log (nu⁻¹ * (L : ℝ)) ≤ (L : ℝ) / 2 := by
    have heq2 : Cmix * (Real.log nu⁻¹ + Real.log (L : ℝ)) =
        Cmix * Real.log nu⁻¹ + Cmix * Real.log (L : ℝ) := by ring
    rw [hlog_split, heq2]
    linarith only [hCmix_log_nu_inv_le, hCmix_nu4_le, hCmix_logL_le, h2Cmix_sqrtL_le]
  linarith only [hfinal, hn_ge_Lhalf]

/-! ## Theorem 2: `log(ν⁻¹ L) ≤ 2 log(ν⁻¹ n)` once `L ≥ L₀` -/

theorem lNaught_log_ratio :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C →
      ∀ M : ℝ, 1 ≤ M → ∀ alpha : ℝ, 0 ≤ alpha → alpha < 1 →
      ∀ cStar : ℝ, 0 < cStar → cStar ≤ 2 → ∀ nu : ℝ, 0 < nu → nu ≤ 1 → ∀ K : ℝ, 0 ≤ K →
      ∀ L : ℕ, SuperdiffusionCLT.Frozen.Section4.lNaught C M alpha cStar nu K ≤ (L : ℝ) →
        ∀ n : ℕ, (L : ℝ) - M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (n : ℝ) →
          Real.log (nu⁻¹ * (L : ℝ)) ≤ 2 * Real.log (nu⁻¹ * (n : ℝ)) := by
  obtain ⟨C_absorb, hC_absorb_ge1, h_absorb_body⟩ := lNaught_absorbs
  obtain ⟨C_ge, hC_ge_ge1, h_ge_body⟩ := lNaught_ge
  set C0 : ℝ := max C_absorb C_ge with hC0def
  have hC0_absorb : C_absorb ≤ C0 := le_max_left _ _
  have hC0_ge : C_ge ≤ C0 := le_max_right _ _
  have hC0ge1 : (1 : ℝ) ≤ C0 := le_trans hC_absorb_ge1 hC0_absorb
  refine ⟨C0, hC0ge1, ?_⟩
  intro C hC M hM alpha halpha0 halpha1 cStar hcStar hcStar2 nu hnu hnu1 K hK L hL n hn
  have h_absorb := h_absorb_body C (le_trans hC0_absorb hC) M hM alpha halpha0 halpha1 cStar
    hcStar hcStar2 nu hnu hnu1 K hK L hL
  have hn_ge_Lhalf : (L : ℝ) / 2 ≤ (n : ℝ) := by linarith only [hn, h_absorb]
  have hL_gt8 := h_ge_body C (le_trans hC0_ge hC) M hM alpha halpha0 halpha1 cStar hcStar
    hcStar2 nu hnu hnu1 K hK
  have hL_gt8' : (8 : ℝ) < (L : ℝ) := lt_of_lt_of_le hL_gt8 hL
  have hLpos : 0 < (L : ℝ) := by linarith only [hL_gt8']
  have hn_gt4 : (4 : ℝ) < (n : ℝ) := by linarith only [hn_ge_Lhalf, hL_gt8']
  have hnu_inv_ge1 : (1 : ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).mpr hnu1
  have hnu_inv_pos : 0 < nu⁻¹ := lt_of_lt_of_le one_pos hnu_inv_ge1
  have hnu_inv_n_gt4 : (4 : ℝ) < nu⁻¹ * (n : ℝ) := by
    have h1 : (1 : ℝ) * (n : ℝ) ≤ nu⁻¹ * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hnu_inv_ge1 (by linarith only [hn_gt4])
    linarith only [h1, hn_gt4]
  have hnu_inv_n_pos : 0 < nu⁻¹ * (n : ℝ) := by linarith only [hnu_inv_n_gt4]
  have h_mul_bound : nu⁻¹ * (L : ℝ) ≤ 2 * (nu⁻¹ * (n : ℝ)) := by
    have h1 : nu⁻¹ * (L : ℝ) ≤ nu⁻¹ * (2 * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith only [hn_ge_Lhalf]) hnu_inv_pos.le
    have heq : nu⁻¹ * (2 * (n : ℝ)) = 2 * (nu⁻¹ * (n : ℝ)) := by ring
    linarith only [h1, heq]
  have h_log_bound : Real.log (nu⁻¹ * (L : ℝ)) ≤ Real.log (2 * (nu⁻¹ * (n : ℝ))) :=
    Real.log_le_log (by positivity) h_mul_bound
  have h_log2_mul : Real.log (2 * (nu⁻¹ * (n : ℝ))) = Real.log 2 + Real.log (nu⁻¹ * (n : ℝ)) :=
    Real.log_mul (by norm_num) hnu_inv_n_pos.ne'
  have h_log2_le : Real.log 2 ≤ Real.log (nu⁻¹ * (n : ℝ)) :=
    Real.log_le_log (by norm_num) (by linarith only [hnu_inv_n_gt4])
  have heq2 : 2 * Real.log (nu⁻¹ * (n : ℝ)) =
      Real.log (nu⁻¹ * (n : ℝ)) + Real.log (nu⁻¹ * (n : ℝ)) := by ring
  rw [heq2]
  linarith only [h_log_bound, h_log2_mul, h_log2_le]

/-! ## Theorem 3: `L₀` under rescaling `M ↦ K' M` -/

/-- The pre-outer-power comparison behind `lNaught_mul_M_le`: rescaling `M` by
`K' ≥ 1` is absorbed into `C` at the cost of the explicit factor
`K' (1 + log K' / log 2)^12`. -/
private lemma lNaught_mul_M_le_inner {C M alpha cStar nu K K' : ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M) (halpha : alpha < 1) (hcStar : 0 < cStar) (hnu : 0 < nu)
    (hK : 0 ≤ K) (hK' : 1 ≤ K') :
    lNaughtInner C (K' * M) alpha cStar nu K ≤
      lNaughtInner (C * K' * (1 + Real.log K' / Real.log 2) ^ (12 : ℝ)) M alpha cStar nu K := by
  have h1ma_pos : 0 < 1 - alpha := by linarith only [halpha]
  have hcStar3pos : 0 < cStar ^ (-(3 : ℝ)) := Real.rpow_pos_of_pos hcStar _
  have hden_pos : 0 < nu * (1 - alpha) := mul_pos hnu h1ma_pos
  have hK'pos : 0 < K' := lt_of_lt_of_le one_pos hK'
  have hlog2pos : (0 : ℝ) < Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hlogK'_nonneg : 0 ≤ Real.log K' := Real.log_nonneg hK'
  have hdenom_pos : 0 < (1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ) := by
    have h1 : 0 < (1 - alpha) ^ (12 : ℝ) := Real.rpow_pos_of_pos h1ma_pos _
    have h2 : 0 < nu ^ (4 : ℝ) := Real.rpow_pos_of_pos hnu _
    exact mul_pos h1 h2
  have h_arg : K' * M + 1 + K ≤ K' * (M + 1 + K) := by
    have hprod : 0 ≤ (K' - 1) * (1 + K) :=
      mul_nonneg (by linarith only [hK']) (by linarith only [hK])
    have heq : K' * (M + 1 + K) - (K' * M + 1 + K) = (K' - 1) * (1 + K) := by ring
    linarith only [hprod, heq]
  have hKM1K_nonneg : 0 ≤ K' * M + 1 + K := by
    have h2 : 0 ≤ K' * M := mul_nonneg hK'pos.le hM
    linarith only [h2, hK]
  unfold lNaughtInner
  set Y := (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha)) with hYdef
  set YK' := (K' * M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha)) with hYK'def
  set X := 2 + Y with hXdef
  set X' := 2 + YK' with hX'def
  have hY_nonneg : 0 ≤ Y := by
    rw [hYdef]
    exact div_nonneg (mul_nonneg (by linarith only [hM, hK]) hcStar3pos.le) hden_pos.le
  have hYK'_nonneg : 0 ≤ YK' := by
    rw [hYK'def]
    exact div_nonneg (mul_nonneg hKM1K_nonneg hcStar3pos.le) hden_pos.le
  have h_YK'_le : YK' ≤ K' * Y := by
    rw [hYK'def, hYdef]
    have h1 : (K' * M + 1 + K) * cStar ^ (-(3 : ℝ)) ≤ K' * (M + 1 + K) * cStar ^ (-(3 : ℝ)) :=
      mul_le_mul_of_nonneg_right h_arg hcStar3pos.le
    have h2 : (K' * M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha)) ≤
        K' * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha)) :=
      div_le_div_of_nonneg_right h1 hden_pos.le
    have heq : K' * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha)) =
        K' * ((M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) := by ring
    linarith only [h2, heq]
  have h_X'_le : X' ≤ K' * X := by
    rw [hX'def, hXdef]
    have h2K' : (2 : ℝ) ≤ 2 * K' := by linarith only [hK']
    have heq : K' * (2 + Y) = 2 * K' + K' * Y := by ring
    linarith only [h_YK'_le, h2K', heq]
  have hX_ge2 : (2 : ℝ) ≤ X := by rw [hXdef]; linarith only [hY_nonneg]
  have hX'_ge2 : (2 : ℝ) ≤ X' := by rw [hX'def]; linarith only [hYK'_nonneg]
  have hXpos : 0 < X := lt_of_lt_of_le (by norm_num) hX_ge2
  have hX'pos : 0 < X' := lt_of_lt_of_le (by norm_num) hX'_ge2
  have hlogX_ge_log2 : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) hX_ge2
  have hlogXpos : 0 < Real.log X := lt_of_lt_of_le hlog2pos hlogX_ge_log2
  have hlogX'pos : 0 < Real.log X' := Real.log_pos (by linarith only [hX'_ge2])
  have hK'X_pos : 0 < K' * X := mul_pos hK'pos hXpos
  have hlogX'_le : Real.log X' ≤ Real.log (K' * X) := Real.log_le_log hX'pos h_X'_le
  have hlogK'X_eq : Real.log (K' * X) = Real.log K' + Real.log X :=
    Real.log_mul hK'pos.ne' hXpos.ne'
  have hratio : Real.log K' ≤ Real.log X * Real.log K' / Real.log 2 := by
    rw [le_div_iff₀ hlog2pos]
    have hprod : 0 ≤ Real.log K' * (Real.log X - Real.log 2) :=
      mul_nonneg hlogK'_nonneg (by linarith only [hlogX_ge_log2])
    have heq : Real.log X * Real.log K' - Real.log K' * Real.log 2 =
        Real.log K' * (Real.log X - Real.log 2) := by ring
    linarith only [hprod, heq]
  have hfactor_le : Real.log K' + Real.log X ≤ Real.log X * (1 + Real.log K' / Real.log 2) := by
    have heq : Real.log X * (1 + Real.log K' / Real.log 2) =
        Real.log X + Real.log X * Real.log K' / Real.log 2 := by ring
    linarith only [heq, hratio]
  have hlogX'_le2 : Real.log X' ≤ Real.log X * (1 + Real.log K' / Real.log 2) := by
    rw [hlogK'X_eq] at hlogX'_le
    linarith only [hlogX'_le, hfactor_le]
  have hRHSfactor_nonneg : 0 ≤ 1 + Real.log K' / Real.log 2 := by
    have h1 : 0 ≤ Real.log K' / Real.log 2 := div_nonneg hlogK'_nonneg hlog2pos.le
    linarith only [h1]
  have hlogX'_pow_le : (Real.log X') ^ (12 : ℝ) ≤
      (Real.log X * (1 + Real.log K' / Real.log 2)) ^ (12 : ℝ) :=
    Real.rpow_le_rpow hlogX'pos.le hlogX'_le2 (by norm_num)
  have hpow_split : (Real.log X * (1 + Real.log K' / Real.log 2)) ^ (12 : ℝ) =
      (Real.log X) ^ (12 : ℝ) * (1 + Real.log K' / Real.log 2) ^ (12 : ℝ) :=
    Real.mul_rpow hlogXpos.le hRHSfactor_nonneg
  rw [hpow_split] at hlogX'_pow_le
  have hcoeff_le : C * (K' * M + 1 + K) * cStar ^ (-(3 : ℝ)) ≤
      C * K' * (M + 1 + K) * cStar ^ (-(3 : ℝ)) := by
    have h1 : C * (K' * M + 1 + K) ≤ C * (K' * (M + 1 + K)) :=
      mul_le_mul_of_nonneg_left h_arg hC
    have heq : C * (K' * (M + 1 + K)) = C * K' * (M + 1 + K) := by ring
    have h2 : C * (K' * M + 1 + K) ≤ C * K' * (M + 1 + K) := by linarith only [h1, heq]
    exact mul_le_mul_of_nonneg_right h2 hcStar3pos.le
  have hLHScoeff_le :
      C * (K' * M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) ≤
      C * K' * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) :=
    div_le_div_of_nonneg_right hcoeff_le hdenom_pos.le
  have hmidCoeff_nonneg :
      0 ≤ C * K' * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) := by
    apply div_nonneg _ hdenom_pos.le
    exact mul_nonneg (mul_nonneg (mul_nonneg hC hK'pos.le) (by linarith only [hM, hK]))
      hcStar3pos.le
  have hlogX'pow_nonneg : 0 ≤ Real.log X' ^ (12 : ℝ) := Real.rpow_nonneg hlogX'pos.le _
  have hstep1 :
      C * (K' * M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) *
          Real.log X' ^ (12 : ℝ) ≤
      C * K' * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) *
          Real.log X' ^ (12 : ℝ) :=
    mul_le_mul_of_nonneg_right hLHScoeff_le hlogX'pow_nonneg
  have hstep2 :
      C * K' * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) *
          Real.log X' ^ (12 : ℝ) ≤
      C * K' * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) *
          (Real.log X ^ (12 : ℝ) * (1 + Real.log K' / Real.log 2) ^ (12 : ℝ)) :=
    mul_le_mul_of_nonneg_left hlogX'_pow_le hmidCoeff_nonneg
  have hstep3 :
      C * K' * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) *
          (Real.log X ^ (12 : ℝ) * (1 + Real.log K' / Real.log 2) ^ (12 : ℝ)) =
      C * K' * (1 + Real.log K' / Real.log 2) ^ (12 : ℝ) * (M + 1 + K) *
          cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) *
          Real.log X ^ (12 : ℝ) := by ring
  linarith only [hstep1, hstep2, hstep3]

/-- **`L₀` under rescaling `M ↦ K' M`**: absorbing a factor `K' ≥ 1` on `M`
into `C` costs an explicit factor `K' (1 + log K' / log 2)^12`. -/
theorem lNaught_mul_M_le (C M alpha cStar nu K K' : ℝ) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (halpha : alpha < 1) (hcStar : 0 < cStar) (hnu : 0 < nu) (hK : 0 ≤ K) (hK' : 1 ≤ K') :
    SuperdiffusionCLT.Frozen.Section4.lNaught C (K' * M) alpha cStar nu K ≤
      SuperdiffusionCLT.Frozen.Section4.lNaught
        (C * K' * (1 + Real.log K' / Real.log 2) ^ (12 : ℝ)) M alpha cStar nu K := by
  have h1ma_pos : 0 < 1 - alpha := by linarith only [halpha]
  have hexp_nonneg : 0 ≤ (1 : ℝ) / (1 - alpha) := (div_pos (by norm_num) h1ma_pos).le
  have hKM_nonneg : 0 ≤ K' * M := mul_nonneg (le_trans zero_le_one hK') hM
  have hInner_nonneg : 0 ≤ lNaughtInner C (K' * M) alpha cStar nu K :=
    inner_nonneg hC hKM_nonneg hK hcStar hnu halpha
  have hInner_le := lNaught_mul_M_le_inner hC hM halpha hcStar hnu hK hK'
  unfold SuperdiffusionCLT.Frozen.Section4.lNaught
  exact Real.rpow_le_rpow hInner_nonneg hInner_le hexp_nonneg

end SuperdiffusionCLT.Section4.LNaught
