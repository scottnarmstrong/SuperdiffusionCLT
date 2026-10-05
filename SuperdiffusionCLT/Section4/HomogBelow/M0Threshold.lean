/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Frozen.Section4.LNaught
public import SuperdiffusionCLT.Section4.LNaught.Threshold
public import SuperdiffusionCLT.Section2.Annealed.Envelope
public import Homogenization.Probability.IndependentSums.PsiCalculus
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
The `m₀` startup-scale threshold of `p.homog.below` Step 1, specialized against the form of
[AK, Theorem 6.1] recorded as `SuperdiffusionCLT.Frozen.Section4.akhc_weakerP3`, at the
parameter choice `D := 1, β := γ := 1/2, L₁ := 4·Cmix, L₂ := ν⁻¹,
H := 8·Cellip·ν⁻²`, with `K_{Ψ_S} = 2` exact and `K_Ψ := gammaGrowthConst(1/3)`,
and with `d ≥ 2` collapsing both `min`-denominators to `1`.

Three different constants play separate roles and must not be conflated: the constant of [AK,
Theorem 6.1] (call it `C₆₁`, appearing inside `Υ₁, Υ₂` and the prefactor `32·C·(Cmix+1)`), the
`m₀` coefficient, and the `L₀` threshold constant. Since `log Υ₂` is *linear* in `C₆₁`,
collapsing all three into one variable would make the statement false: as `C → ∞` the left side
grows quadratically in `C` while `m₀ = ⌈C log²L⌉` grows only linearly. This file therefore
separates `C₆₁` (fixed first, arbitrary) from `C'` (the shared `m₀`/`L₀` constant, chosen large
depending on `C₆₁`), and bounds the input scale `m ≤ L²` (since `log(m+m₀+1)` enters the target
through `X`, `m` cannot be left unconstrained).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.HomogBelow

open Real

/-- A safe rational lower bound on `(log 2)^12`, used only to make
`lNaught`'s log-argument factor `log(2+\cdots)^{12} ≥ \log(2)^{12}` produce a
lower bound independent of `M`. `(log 2)^{12} ≈ 0.01226`; `1/250 = 0.004` is
comfortably below that. -/
private lemma homogBelowM0_pow12_log_two_ge : (1 : ℝ) / 250 ≤ (Real.log 2) ^ (12 : ℝ) := by
  have h1 : (0.69 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have h2 : (0.69 : ℝ) ^ (12 : ℕ) ≤ (Real.log 2) ^ (12 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) h1 12
  have h3 : (1 : ℝ) / 250 ≤ (0.69 : ℝ) ^ (12 : ℕ) := by norm_num
  have h4 : (Real.log 2) ^ (12 : ℕ) = (Real.log 2) ^ (12 : ℝ) := by
    rw [show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [← h4]
  linarith only [h2, h3]

/-- **`lNaught` grows at least linearly in `C`, using only `M ≥ 1`** (not the
stronger `M ≥ C` of `sbIndep_lNaught_ge_linear`,
`Section4/SigmaBarComparison/IndependenceRatioC.lean`): once `C ≥ 1000`,
`C / 1000 ≤ lNaught C M alpha cStar nu K`. The log-argument
`2 + (M+1+K)cStar⁻³/(ν(1-α)) ≥ 2` regardless of `M`, so the `log^12` factor
clears `(log 2)^{12} ≥ 1/250` (`homogBelowM0_pow12_log_two_ge`) independently
of `M`; combined with `(M+1+K)cStar⁻³ ≥ 2·(1/8) = 1/4` and the denominator
`(1-α)^{12}ν^4 ≤ 1`, the inner base clears `C/1000`, and the outer power
`(\cdot)^{1/(1-α)}` (exponent `≥ 1` on a base `≥ 1` once `C ≥ 1000`) only
increases it further. -/
theorem homogBelowM0_lNaught_linear {C M alpha cStar nu K : ℝ}
    (hC1000 : (1000 : ℝ) ≤ C) (hM : 1 ≤ M) (hcStar : 0 < cStar) (hcStar2 : cStar ≤ 2)
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hK : 0 ≤ K) (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1) :
    C / 1000 ≤ SuperdiffusionCLT.Frozen.Section4.lNaught C M alpha cStar nu K := by
  unfold SuperdiffusionCLT.Frozen.Section4.lNaught
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le (by norm_num) hC1000
  have hcStar3ge : (1 / 8 : ℝ) ≤ cStar ^ (-(3 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_nonpos hcStar hcStar2 (by norm_num : (-(3 : ℝ)) ≤ 0)
    have h2 : (2 : ℝ) ^ (-(3 : ℝ)) = 1 / 8 := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
      norm_num
    rw [h2] at h; exact h
  have hcStar3pos : (0 : ℝ) < cStar ^ (-(3 : ℝ)) := Real.rpow_pos_of_pos hcStar _
  have hMK2 : (2 : ℝ) ≤ M + 1 + K := by linarith only [hM, hK]
  have halphapos : (0 : ℝ) < 1 - alpha := by linarith only [halpha1]
  have halphale1 : (1 - alpha) ≤ 1 := by linarith only [halpha0]
  have hD1 : (1 - alpha) ^ (12 : ℝ) ≤ 1 := by
    calc (1 - alpha) ^ (12 : ℝ) ≤ (1 : ℝ) ^ (12 : ℝ) :=
          Real.rpow_le_rpow halphapos.le halphale1 (by norm_num)
      _ = 1 := Real.one_rpow _
  have hD1pos : (0 : ℝ) < (1 - alpha) ^ (12 : ℝ) := Real.rpow_pos_of_pos halphapos _
  have hD2 : nu ^ (4 : ℝ) ≤ 1 := by
    calc nu ^ (4 : ℝ) ≤ (1 : ℝ) ^ (4 : ℝ) := Real.rpow_le_rpow hnu.le hnu1 (by norm_num)
      _ = 1 := Real.one_rpow _
  have hD2pos : (0 : ℝ) < nu ^ (4 : ℝ) := Real.rpow_pos_of_pos hnu _
  have hDpos : (0 : ℝ) < (1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ) := mul_pos hD1pos hD2pos
  have hDle1 : (1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ) ≤ 1 := by
    calc (1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ) ≤ 1 * 1 :=
          mul_le_mul hD1 hD2 hD2pos.le (by norm_num)
      _ = 1 := by norm_num
  have hNumGe : C * 2 * (1 / 8 : ℝ) ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) := by
    have step1 : C * 2 * cStar ^ (-(3 : ℝ)) ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMK2 hCpos.le) hcStar3pos.le
    have step2 : C * 2 * (1 / 8 : ℝ) ≤ C * 2 * cStar ^ (-(3 : ℝ)) :=
      mul_le_mul_of_nonneg_left hcStar3ge (by linarith only [hCpos])
    linarith only [step1, step2]
  have hNumNonneg : (0 : ℝ) ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) := by
    have hMK0 : (0 : ℝ) ≤ M + 1 + K := by linarith only [hMK2]
    positivity
  have hDivGe : C / 4 ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) := by
    have hCge4 : C / 4 ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) := by linarith only [hNumGe]
    calc C / 4 ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) := hCge4
      _ ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) := by
          rw [le_div_iff₀ hDpos]
          exact mul_le_of_le_one_right hNumNonneg hDle1
  have hlogargge2 :
      (2 : ℝ) ≤ 2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha)) := by
    have hfrac_nonneg : (0 : ℝ) ≤ (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha)) := by
      have hMK0 : (0 : ℝ) ≤ M + 1 + K := by linarith only [hMK2]
      have hnua_pos : (0 : ℝ) < nu * (1 - alpha) := mul_pos hnu halphapos
      exact div_nonneg (mul_nonneg hMK0 hcStar3pos.le) hnua_pos.le
    linarith only [hfrac_nonneg]
  have hlogarggelog2 :
      Real.log 2 ≤ Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) :=
    Real.log_le_log (by norm_num) hlogargge2
  have hlog2nonneg : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog12ge :
      (Real.log 2) ^ (12 : ℝ) ≤
        Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) :=
    Real.rpow_le_rpow hlog2nonneg hlogarggelog2 (by norm_num)
  have hlog12geNum :
      (1 : ℝ) / 250 ≤
        Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) :=
    le_trans homogBelowM0_pow12_log_two_ge hlog12ge
  have hlog12nonneg :
      (0 : ℝ) ≤
        Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) := by
    have hlogarg_pos : (0 : ℝ) < 2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha)) := by
      linarith only [hlogargge2]
    exact Real.rpow_nonneg (Real.log_nonneg (by linarith only [hlogargge2])) _
  have hDivNonneg : (0 : ℝ) ≤
      C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) :=
    div_nonneg hNumNonneg hDpos.le
  have hCdiv4nonneg : (0 : ℝ) ≤ C / 4 := by linarith only [hCpos]
  have hInnerGe : C / 1000 ≤
      (C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ))) *
        Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) := by
    have hmul : (C / 4) * (1 / 250) ≤
        (C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ))) *
          Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) :=
      mul_le_mul hDivGe hlog12geNum (by norm_num) hDivNonneg
    linarith only [hmul]
  have hInnerGe1 : (1 : ℝ) ≤
      (C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ))) *
        Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) := by
    have h1000 : (1 : ℝ) ≤ C / 1000 := by linarith only [hC1000]
    linarith only [h1000, hInnerGe]
  have hexp_ge1 : (1 : ℝ) ≤ (1 : ℝ) / (1 - alpha) := by
    rw [le_div_iff₀ halphapos]; linarith only [halphale1]
  calc C / 1000 ≤
      (C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ))) *
        Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) := hInnerGe
    _ = _ ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ _ ^ ((1 : ℝ) / (1 - alpha)) := Real.rpow_le_rpow_of_exponent_le hInnerGe1 hexp_ge1

/-- **`lNaught` grows at least like `C / (1000 ν^4)`**, keeping the `ν^4`
factor explicit (unlike `homogBelowM0_lNaught_linear`, which drops it via
`ν^4 ≤ 1`): for `C ≥ 1000`, `C / (1000 * ν^4) ≤ lNaught C M alpha cStar nu K`.
Same mechanism as `homogBelowM0_lNaught_linear`, except only
`(1-alpha)^12 ≤ 1` is dropped from the denominator, leaving `ν^4` in place.
Used to control `ν⁻¹` in terms of `L` once `L ≥ lNaught(...)`. -/
theorem homogBelowM0_lNaught_nu4_lower {C M alpha cStar nu K : ℝ}
    (hC1000 : (1000 : ℝ) ≤ C) (hM : 1 ≤ M) (hcStar : 0 < cStar) (hcStar2 : cStar ≤ 2)
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hK : 0 ≤ K) (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1) :
    C / (1000 * nu ^ (4 : ℝ)) ≤
      SuperdiffusionCLT.Frozen.Section4.lNaught C M alpha cStar nu K := by
  unfold SuperdiffusionCLT.Frozen.Section4.lNaught
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le (by norm_num) hC1000
  have hcStar3ge : (1 / 8 : ℝ) ≤ cStar ^ (-(3 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_nonpos hcStar hcStar2 (by norm_num : (-(3 : ℝ)) ≤ 0)
    have h2 : (2 : ℝ) ^ (-(3 : ℝ)) = 1 / 8 := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
      norm_num
    rw [h2] at h; exact h
  have hcStar3pos : (0 : ℝ) < cStar ^ (-(3 : ℝ)) := Real.rpow_pos_of_pos hcStar _
  have hMK2 : (2 : ℝ) ≤ M + 1 + K := by linarith only [hM, hK]
  have halphapos : (0 : ℝ) < 1 - alpha := by linarith only [halpha1]
  have halphale1 : (1 - alpha) ≤ 1 := by linarith only [halpha0]
  have hD1 : (1 - alpha) ^ (12 : ℝ) ≤ 1 := by
    calc (1 - alpha) ^ (12 : ℝ) ≤ (1 : ℝ) ^ (12 : ℝ) :=
          Real.rpow_le_rpow halphapos.le halphale1 (by norm_num)
      _ = 1 := Real.one_rpow _
  have hnu4pos : (0 : ℝ) < nu ^ (4 : ℝ) := Real.rpow_pos_of_pos hnu _
  have hDpos : (0 : ℝ) < (1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ) :=
    mul_pos (Real.rpow_pos_of_pos halphapos _) hnu4pos
  have hDle : (1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ) ≤ nu ^ (4 : ℝ) := by
    calc (1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ) ≤ 1 * nu ^ (4 : ℝ) :=
          mul_le_mul_of_nonneg_right hD1 hnu4pos.le
      _ = nu ^ (4 : ℝ) := by ring
  have hNumGe : C / 4 ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) := by
    have step1 : C * 2 * cStar ^ (-(3 : ℝ)) ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMK2 hCpos.le) hcStar3pos.le
    have step2 : C * 2 * (1 / 8 : ℝ) ≤ C * 2 * cStar ^ (-(3 : ℝ)) :=
      mul_le_mul_of_nonneg_left hcStar3ge (by linarith only [hCpos])
    linarith only [step1, step2]
  have hNumNonneg : (0 : ℝ) ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) := by
    have hMK0 : (0 : ℝ) ≤ M + 1 + K := by linarith only [hMK2]
    positivity
  have hDivGe : C / 4 / nu ^ (4 : ℝ) ≤
      C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) := by
    have hstep1 : C / 4 / nu ^ (4 : ℝ) ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / nu ^ (4 : ℝ) :=
      div_le_div_of_nonneg_right hNumGe hnu4pos.le
    have hstep2 : C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / nu ^ (4 : ℝ) ≤
        C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) :=
      div_le_div_of_nonneg_left hNumNonneg hDpos hDle
    linarith only [hstep1, hstep2]
  have hlogargge2 :
      (2 : ℝ) ≤ 2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha)) := by
    have hfrac_nonneg : (0 : ℝ) ≤ (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha)) := by
      have hMK0 : (0 : ℝ) ≤ M + 1 + K := by linarith only [hMK2]
      have hnua_pos : (0 : ℝ) < nu * (1 - alpha) := mul_pos hnu halphapos
      exact div_nonneg (mul_nonneg hMK0 hcStar3pos.le) hnua_pos.le
    linarith only [hfrac_nonneg]
  have hlogarggelog2 :
      Real.log 2 ≤ Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) :=
    Real.log_le_log (by norm_num) hlogargge2
  have hlog2nonneg : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog12ge :
      (Real.log 2) ^ (12 : ℝ) ≤
        Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) :=
    Real.rpow_le_rpow hlog2nonneg hlogarggelog2 (by norm_num)
  have hlog12geNum :
      (1 : ℝ) / 250 ≤
        Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) :=
    le_trans homogBelowM0_pow12_log_two_ge hlog12ge
  have hDivNonneg : (0 : ℝ) ≤
      C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) :=
    div_nonneg hNumNonneg hDpos.le
  have hCdiv4nu4nonneg : (0 : ℝ) ≤ C / 4 / nu ^ (4 : ℝ) := by positivity
  have hInnerGe : C / 4 / nu ^ (4 : ℝ) * (1 / 250) ≤
      (C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ))) *
        Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) :=
    mul_le_mul hDivGe hlog12geNum (by norm_num) hDivNonneg
  have heq : C / 4 / nu ^ (4 : ℝ) * (1 / 250) = C / (1000 * nu ^ (4 : ℝ)) := by
    rw [eq_div_iff (by positivity)]
    field_simp
    norm_num
  rw [heq] at hInnerGe
  have hnu4_le1 : nu ^ (4 : ℝ) ≤ 1 := by
    calc nu ^ (4 : ℝ) ≤ (1 : ℝ) ^ (4 : ℝ) := Real.rpow_le_rpow hnu.le hnu1 (by norm_num)
      _ = 1 := Real.one_rpow _
  have hInnerGe1 : (1 : ℝ) ≤
      (C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ))) *
        Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) := by
    have h1000C : (1 : ℝ) ≤ C / (1000 * nu ^ (4 : ℝ)) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith only [hC1000, hnu4_le1, hnu4pos]
    linarith only [h1000C, hInnerGe]
  have hexp_ge1 : (1 : ℝ) ≤ (1 : ℝ) / (1 - alpha) := by
    rw [le_div_iff₀ halphapos]; linarith only [halphale1]
  calc C / (1000 * nu ^ (4 : ℝ)) ≤
      (C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ))) *
        Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) := hInnerGe
    _ = _ ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ _ ^ ((1 : ℝ) / (1 - alpha)) := Real.rpow_le_rpow_of_exponent_le hInnerGe1 hexp_ge1

/-- **`L` controls `ν⁻¹` and `C`** once `L ≥ lNaught(C, ...)` with `C ≥ 1000`:
`1 ≤ L`, `ν⁻¹ ≤ L`, `ν⁻¹^2 ≤ L`, and `C ≤ 1000 * L`. The `ν`-bounds come from
`homogBelowM0_lNaught_nu4_lower`; the `C`-bound from
`homogBelowM0_lNaught_linear`. -/
theorem homogBelowM0_L_controls {C M alpha cStar nu K : ℝ} {L : ℕ}
    (hC1000 : (1000 : ℝ) ≤ C) (hM : 1 ≤ M) (hcStar : 0 < cStar) (hcStar2 : cStar ≤ 2)
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hK : 0 ≤ K) (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1)
    (hL : SuperdiffusionCLT.Frozen.Section4.lNaught C M alpha cStar nu K ≤ (L : ℝ)) :
    1 ≤ L ∧ nu⁻¹ ≤ (L : ℝ) ∧ nu⁻¹ ^ (2 : ℕ) ≤ (L : ℝ) ∧ C ≤ 1000 * (L : ℝ) := by
  have hnu4 := homogBelowM0_lNaught_nu4_lower hC1000 hM hcStar hcStar2 hnu hnu1 hK halpha0 halpha1
  have hClin := homogBelowM0_lNaught_linear hC1000 hM hcStar hcStar2 hnu hnu1 hK halpha0 halpha1
  have hnu4L : C / (1000 * nu ^ (4 : ℝ)) ≤ (L : ℝ) := le_trans hnu4 hL
  have hClinL : C / 1000 ≤ (L : ℝ) := le_trans hClin hL
  have hCle : C ≤ 1000 * (L : ℝ) := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 1000)] at hClinL
    linarith only [hClinL]
  have hnu4pos : (0 : ℝ) < nu ^ (4 : ℝ) := Real.rpow_pos_of_pos hnu _
  have hstep : C ≤ 1000 * nu ^ (4 : ℝ) * (L : ℝ) := by
    rw [div_le_iff₀ (by positivity)] at hnu4L
    linarith only [hnu4L]
  have hone_le : (1 : ℝ) ≤ nu ^ (4 : ℝ) * (L : ℝ) := by nlinarith only [hstep, hC1000]
  have hpow4eq : nu ^ (4 : ℝ) = nu ^ (4 : ℕ) := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hnu4pos' : (0 : ℝ) < nu ^ (4 : ℕ) := by rw [← hpow4eq]; exact hnu4pos
  have hone_le' : (1 : ℝ) ≤ nu ^ (4 : ℕ) * (L : ℝ) := by rwa [hpow4eq] at hone_le
  have hLpos : (0 : ℝ) < (L : ℝ) := by nlinarith only [hone_le', hnu4pos']
  have hL0 : 0 < L := by exact_mod_cast hLpos
  have hL1 : 1 ≤ L := by omega
  have hone_le'' : (1 : ℝ) ≤ (L : ℝ) * nu ^ (4 : ℕ) := by
    rw [mul_comm]; exact hone_le'
  have hinv4 : (1 : ℝ) / nu ^ (4 : ℕ) ≤ (L : ℝ) := by
    rw [div_le_iff₀ hnu4pos']; exact hone_le''
  have hinvpoweq : nu⁻¹ ^ (4 : ℕ) = (1 : ℝ) / nu ^ (4 : ℕ) := by rw [inv_pow, one_div]
  have hinv4' : nu⁻¹ ^ (4 : ℕ) ≤ (L : ℝ) := by rw [hinvpoweq]; exact hinv4
  have hnuinv_ge1 : (1 : ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).mpr hnu1
  have hnuinv_le4 : nu⁻¹ ≤ nu⁻¹ ^ (4 : ℕ) := by
    calc nu⁻¹ = nu⁻¹ ^ (1 : ℕ) := (pow_one _).symm
      _ ≤ nu⁻¹ ^ (4 : ℕ) := pow_le_pow_right₀ hnuinv_ge1 (by norm_num)
  have hnuinv2_le4 : nu⁻¹ ^ (2 : ℕ) ≤ nu⁻¹ ^ (4 : ℕ) := pow_le_pow_right₀ hnuinv_ge1 (by norm_num)
  exact ⟨hL1, le_trans hnuinv_le4 hinv4', le_trans hnuinv2_le4 hinv4', hCle⟩

/-- **`gammaGrowthConst (1/3) = 64`** exactly: `gammaGrowthConst σ :=
max 2 ((1+σ⁻¹)^(σ⁻¹))` (`Homogenization.Probability.IndependentSums.PsiCalculus`),
and at `σ = 1/3`, `σ⁻¹ = 3`, `(1+3)^3 = 64 ≥ 2`. This is `K_{Ψ}` in the
startup-scale threshold at the paper's own choice `γ = 1/2`, where
`K_Ψ := gammaGrowthConst(1/3)` in the proof of `p.homog.below`. -/
theorem homogBelowM0_gammaGrowthConst_third :
    Homogenization.IndependentSums.gammaGrowthConst ((1 : ℝ) / 3) = 64 := by
  have hinv : ((1 : ℝ) / 3)⁻¹ = 3 := by norm_num
  unfold Homogenization.IndependentSums.gammaGrowthConst
  rw [hinv]
  have hpow : (1 + (3 : ℝ)) ^ (3 : ℝ) = 64 := by
    rw [show (1 + (3 : ℝ)) = 4 by norm_num, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
    norm_num
  rw [hpow]
  exact max_eq_right (by norm_num)

/-- The `Υ₂`-exponent bound: once `ν⁻¹ ≤ L` and `ν⁻¹^2 ≤ L` (as reals) with
`L ≥ 1`, the exponent `(4Cmix+2) log(2ν⁻¹) + 2(1+log(8·Cellip·ν⁻²+2))`
appearing inside `Υ₂` is dominated by a fixed additive constant plus
`(4Cmix+4) log L`. -/
theorem homogBelowM0_upsilon2_exponent_le {Cmix Cellip nu : ℝ} {L : ℕ}
    (hCmix : 1 ≤ Cmix) (hCellip : 1 ≤ Cellip) (hnu : 0 < nu)
    (hL1 : 1 ≤ L) (hnuinv : nu⁻¹ ≤ (L : ℝ)) (hnuinv2 : nu⁻¹ ^ (2 : ℕ) ≤ (L : ℝ)) :
    (4 * Cmix + 2) * Real.log (2 * nu⁻¹) +
        2 * (1 + Real.log (8 * Cellip * nu⁻¹ ^ (2 : ℕ) + 2)) ≤
      ((4 * Cmix + 2) * Real.log 2 + 2 + 2 * Real.log (8 * Cellip + 2)) +
        (4 * Cmix + 4) * Real.log (L : ℝ) := by
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL1
  have hnuinvpos : (0 : ℝ) < nu⁻¹ := inv_pos.mpr hnu
  have hlog2nuinv : Real.log (2 * nu⁻¹) = Real.log 2 + Real.log nu⁻¹ :=
    Real.log_mul (by norm_num) hnuinvpos.ne'
  have hlognuinvL : Real.log nu⁻¹ ≤ Real.log (L : ℝ) := Real.log_le_log hnuinvpos hnuinv
  have hCmixnn : (0 : ℝ) ≤ 4 * Cmix + 2 := by linarith only [hCmix]
  have hterm1 : (4 * Cmix + 2) * Real.log (2 * nu⁻¹) ≤
      (4 * Cmix + 2) * Real.log 2 + (4 * Cmix + 2) * Real.log (L : ℝ) := by
    rw [hlog2nuinv]
    have h := mul_le_mul_of_nonneg_left hlognuinvL hCmixnn
    nlinarith only [h]
  have hL1' : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
  have harg_le : 8 * Cellip * nu⁻¹ ^ (2 : ℕ) + 2 ≤ (8 * Cellip + 2) * (L : ℝ) := by
    have hCellipnn : (0 : ℝ) ≤ 8 * Cellip := by linarith only [hCellip]
    have h1 : 8 * Cellip * nu⁻¹ ^ (2 : ℕ) ≤ 8 * Cellip * (L : ℝ) :=
      mul_le_mul_of_nonneg_left hnuinv2 hCellipnn
    nlinarith only [h1, hL1']
  have hargpos : (0 : ℝ) < 8 * Cellip * nu⁻¹ ^ (2 : ℕ) + 2 := by positivity
  have hlogarg : Real.log (8 * Cellip * nu⁻¹ ^ (2 : ℕ) + 2) ≤
      Real.log (8 * Cellip + 2) + Real.log (L : ℝ) := by
    have hstep : Real.log (8 * Cellip * nu⁻¹ ^ (2 : ℕ) + 2) ≤
        Real.log ((8 * Cellip + 2) * (L : ℝ)) := Real.log_le_log hargpos harg_le
    rwa [Real.log_mul (by linarith only [hCellip]) hLpos.ne'] at hstep
  have hterm2 : 2 * (1 + Real.log (8 * Cellip * nu⁻¹ ^ (2 : ℕ) + 2)) ≤
      2 + 2 * Real.log (8 * Cellip + 2) + 2 * Real.log (L : ℝ) := by
    nlinarith only [hlogarg]
  nlinarith only [hterm1, hterm2]

/-- **`Υ₂ ≤ U₂ · L^{p₂}`** for fixed `U₂ := C₆₁·exp(C₆₁·E₁)` and
`p₂ := C₆₁·(4Cmix+4)` depending only on `C₆₁, Cmix, Cellip` (not on `L`),
once `ν⁻¹ ≤ L`, `ν⁻¹^2 ≤ L`, `L ≥ 1`: the `Υ₂` term of the threshold
collapses to a fixed power of `L`. -/
theorem homogBelowM0_upsilon2_le_pow {C61 Cmix Cellip nu : ℝ} {L : ℕ}
    (hC61 : 1 ≤ C61) (hCmix : 1 ≤ Cmix) (hCellip : 1 ≤ Cellip) (hnu : 0 < nu)
    (hL1 : 1 ≤ L) (hnuinv : nu⁻¹ ≤ (L : ℝ)) (hnuinv2 : nu⁻¹ ^ (2 : ℕ) ≤ (L : ℝ)) :
    C61 * Real.exp (C61 * ((4 * Cmix + 2) * Real.log (2 * nu⁻¹) +
        2 * (1 + Real.log (8 * Cellip * nu⁻¹ ^ (2 : ℕ) + 2)))) ≤
      C61 * Real.exp (C61 * ((4 * Cmix + 2) * Real.log 2 + 2 + 2 * Real.log (8 * Cellip + 2))) *
        (L : ℝ) ^ (C61 * (4 * Cmix + 4)) := by
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL1
  have hexpbound := homogBelowM0_upsilon2_exponent_le hCmix hCellip hnu hL1 hnuinv hnuinv2
  have hC61nn : (0 : ℝ) ≤ C61 := by linarith only [hC61]
  have hstep1 : C61 * ((4 * Cmix + 2) * Real.log (2 * nu⁻¹) +
        2 * (1 + Real.log (8 * Cellip * nu⁻¹ ^ (2 : ℕ) + 2))) ≤
      C61 * (((4 * Cmix + 2) * Real.log 2 + 2 + 2 * Real.log (8 * Cellip + 2)) +
        (4 * Cmix + 4) * Real.log (L : ℝ)) :=
    mul_le_mul_of_nonneg_left hexpbound hC61nn
  have hstep2 : Real.exp (C61 * ((4 * Cmix + 2) * Real.log (2 * nu⁻¹) +
        2 * (1 + Real.log (8 * Cellip * nu⁻¹ ^ (2 : ℕ) + 2)))) ≤
      Real.exp (C61 * (((4 * Cmix + 2) * Real.log 2 + 2 + 2 * Real.log (8 * Cellip + 2)) +
        (4 * Cmix + 4) * Real.log (L : ℝ))) := Real.exp_le_exp.mpr hstep1
  have hrw : C61 * (((4 * Cmix + 2) * Real.log 2 + 2 + 2 * Real.log (8 * Cellip + 2)) +
        (4 * Cmix + 4) * Real.log (L : ℝ)) =
      C61 * ((4 * Cmix + 2) * Real.log 2 + 2 + 2 * Real.log (8 * Cellip + 2)) +
        (C61 * (4 * Cmix + 4)) * Real.log (L : ℝ) := by ring
  rw [hrw, Real.exp_add] at hstep2
  have hrpoweq : (L : ℝ) ^ (C61 * (4 * Cmix + 4)) =
      Real.exp ((C61 * (4 * Cmix + 4)) * Real.log (L : ℝ)) := by
    rw [Real.rpow_def_of_pos hLpos]
    congr 1
    ring
  have hfinal := mul_le_mul_of_nonneg_left hstep2 hC61nn
  rw [hrpoweq]
  calc C61 * Real.exp (C61 * ((4 * Cmix + 2) * Real.log (2 * nu⁻¹) +
        2 * (1 + Real.log (8 * Cellip * nu⁻¹ ^ (2 : ℕ) + 2))))
      ≤ C61 * (Real.exp (C61 * ((4 * Cmix + 2) * Real.log 2 + 2 + 2 * Real.log (8 * Cellip + 2))) *
          Real.exp ((C61 * (4 * Cmix + 4)) * Real.log (L : ℝ))) := hfinal
    _ = C61 * Real.exp (C61 * ((4 * Cmix + 2) * Real.log 2 + 2 + 2 * Real.log (8 * Cellip + 2))) *
          Real.exp ((C61 * (4 * Cmix + 4)) * Real.log (L : ℝ)) := by ring

/-- **`Θ₀`-bound collapses to `Cd' · L²`**: for `Cd ≥ 0` and `ν⁻¹^2 ≤ L`,
`(2Cd+4Cd²)·ν⁻¹²·L ≤ (2Cd+4Cd²)·L²`. -/
theorem homogBelowM0_thetaBound_le_sq {Cd nu : ℝ} {L : ℕ}
    (hCd : 0 ≤ Cd) (hnuinv2 : nu⁻¹ ^ (2 : ℕ) ≤ (L : ℝ)) :
    (2 * Cd + 4 * Cd ^ 2) * nu⁻¹ ^ (2 : ℕ) * (L : ℝ) ≤ (2 * Cd + 4 * Cd ^ 2) * (L : ℝ) ^ 2 := by
  have hLnn : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have hcoeffnn : (0 : ℝ) ≤ 2 * Cd + 4 * Cd ^ 2 := by positivity
  have h1 : nu⁻¹ ^ (2 : ℕ) * (L : ℝ) ≤ (L : ℝ) * (L : ℝ) :=
    mul_le_mul_of_nonneg_right hnuinv2 hLnn
  have h2 : (2 * Cd + 4 * Cd ^ 2) * (nu⁻¹ ^ (2 : ℕ) * (L : ℝ)) ≤
      (2 * Cd + 4 * Cd ^ 2) * ((L : ℝ) * (L : ℝ)) :=
    mul_le_mul_of_nonneg_left h1 hcoeffnn
  nlinarith only [h2]

/-- **`m₀ := ⌈C'·log²L⌉₊` collapses to `1000L³+1`** once `C' ≤ 1000L` and
`L ≥ 1`: crudely bounding `log L ≤ L` turns the ceiling into a cube. -/
theorem homogBelowM0_m0_le_cube {Cprime : ℝ} {L : ℕ}
    (hCprime0 : 0 ≤ Cprime) (hCprimeL : Cprime ≤ 1000 * (L : ℝ)) (hL1 : 1 ≤ L) :
    (⌈Cprime * Real.log (L : ℝ) ^ 2⌉₊ : ℝ) ≤ 1000 * (L : ℝ) ^ 3 + 1 := by
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL1
  have hlogLnn : (0 : ℝ) ≤ Real.log (L : ℝ) := Real.log_nonneg (by exact_mod_cast hL1)
  have hlogLleL : Real.log (L : ℝ) ≤ (L : ℝ) := by
    have h := Real.log_le_sub_one_of_pos hLpos
    linarith only [h]
  have hlogLsq : Real.log (L : ℝ) ^ 2 ≤ (L : ℝ) ^ 2 :=
    pow_le_pow_left₀ hlogLnn hlogLleL 2
  have harg_nn : (0 : ℝ) ≤ Cprime * Real.log (L : ℝ) ^ 2 := by positivity
  have hceil : (⌈Cprime * Real.log (L : ℝ) ^ 2⌉₊ : ℝ) < Cprime * Real.log (L : ℝ) ^ 2 + 1 :=
    Nat.ceil_lt_add_one harg_nn
  have hstep1 : Cprime * Real.log (L : ℝ) ^ 2 ≤ 1000 * (L : ℝ) * (L : ℝ) ^ 2 := by
    have h1 : Cprime * Real.log (L : ℝ) ^ 2 ≤ Cprime * (L : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hlogLsq hCprime0
    have hLsqnn : (0 : ℝ) ≤ (L : ℝ) ^ 2 := by positivity
    have h2 : Cprime * (L : ℝ) ^ 2 ≤ 1000 * (L : ℝ) * (L : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hCprimeL hLsqnn
    linarith only [h1, h2]
  nlinarith only [hceil, hstep1]

/-- **`m + m₀ + 1 ≤ 1003 L³`** once `m ≤ L²`, `C' ≤ 1000L`, `L ≥ 1`. -/
theorem homogBelowM0_mPlusM0_le_cube {Cprime : ℝ} {L m : ℕ}
    (hCprime0 : 0 ≤ Cprime) (hCprimeL : Cprime ≤ 1000 * (L : ℝ)) (hL1 : 1 ≤ L)
    (hm : m ≤ L ^ 2) :
    (m : ℝ) + (⌈Cprime * Real.log (L : ℝ) ^ 2⌉₊ : ℝ) + 1 ≤ 1003 * (L : ℝ) ^ 3 := by
  have hm0 := homogBelowM0_m0_le_cube hCprime0 hCprimeL hL1
  have hmR : (m : ℝ) ≤ (L : ℝ) ^ 2 := by exact_mod_cast hm
  have hL1' : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
  have hcube1 : (L : ℝ) ^ 2 ≤ (L : ℝ) ^ 3 := pow_le_pow_right₀ hL1' (by norm_num)
  have hcube2 : (1 : ℝ) ≤ (L : ℝ) ^ 3 := by
    calc (1 : ℝ) = (1 : ℝ) ^ 3 := by norm_num
      _ ≤ (L : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hL1' 3
  nlinarith only [hm0, hmR, hcube1, hcube2]

end SuperdiffusionCLT.Section4.HomogBelow
