/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.SkeletonRoot
public import SuperdiffusionCLT.Section4.LNaught.Monotone
public import SuperdiffusionCLT.Section4.LNaught.LogCompare
public import SuperdiffusionCLT.Section4.NewMixing.LogGrowth

/-!
# Arithmetic input `hThr` for `srootMS_minimal_scales_of_inputs`

In the proof of `p.minimal.scales`, the
threshold comparison `e.new.mixing.minscale.thresholds`: the
mixing threshold `L₀(C s⁻¹ K, 1/2)` at `K = C M s⁻¹` lies below `hat L₂`. This
holds with `C ≳ CE^{13}`-ish, via the FIRST `L₀`
term (`α = 1-ρ`); the printed attribution to the second `L₀` term
is incorrect for small `ρ` (that term's exponent `1/2+ρ → 1/2` gives
no room as `ρ → 0`, whereas the first term's exponent `1/(1-(1-ρ)) = 1/ρ → ∞`
supplies unbounded room).

**Proof route** (`srootA_hThr`): the naive comparison of `lNaught`'s `M`-slot
at matching scale fails because `CE` multiplies the whole `M`-slot on the
left (`CE * s⁻¹ * (C * M * s⁻¹)`) while the right `M`-slot
(`C * expon⁻¹ * delta⁻² * s⁻⁴ * M²`) carries no companion `CE` factor: at
`s=δ=M=1`, `expon → 1/2⁻`, the right slot's non-`C` content is only `2`, so
`CE > 2` breaks direct `M`-slot monotonicity regardless of `C`. The fix:
first apply `LNaught.LogCompare.lNaught_mul_M_le` (rescaling `M ↦ K'·M`
absorbs `K'` into `C` instead, at the cost of a factor
`K'(1+log K'/log 2)¹²`) with `K' := CE`, converting `lNaught CE (CE·M₀) α`
into `lNaught (CE·CE·(1+log CE/log 2)¹²) M₀ α` — now the *left* `C`-slot
alone carries the `CE`-dependence and `M₀ := C·M·s⁻²` carries none. The
remaining `C`-slot and `M`-slot comparisons are then `CE`-independent and
hold once `C` clears an absolute (`d`-and-`CE`-free) numeric threshold.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

open SuperdiffusionCLT.Section4.LNaught
open SuperdiffusionCLT.Section4.NewMixing
open SuperdiffusionCLT.Frozen.Section4 (lNaught)

noncomputable section

/-! ## `lNaughtInner` is monotone increasing in `alpha` -/

/-- **`lNaughtInner` is monotone in `alpha`** (fixed `C,M,cStar,nu,K`, `C ≥ 0`):
both the coefficient `C(M+1+K)cStar⁻³/((1-α)¹²ν⁴)` and the log-power factor
grow as `α` increases towards `1`. -/
theorem srootA_inner_mono_alpha {C M cStar nu K alpha alpha' : ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hK : 0 ≤ K) (hcStar : 0 < cStar) (hnu : 0 < nu)
    (halpha_le : alpha ≤ alpha') (halpha1' : alpha' < 1) :
    lNaughtInner C M alpha cStar nu K ≤ lNaughtInner C M alpha' cStar nu K := by
  have halpha1 : alpha < 1 := lt_of_le_of_lt halpha_le halpha1'
  have h1ma_pos : 0 < 1 - alpha := one_minus_alpha_pos halpha1
  have h1ma_pos' : 0 < 1 - alpha' := one_minus_alpha_pos halpha1'
  have h1ma_le : 1 - alpha' ≤ 1 - alpha := by linarith only [halpha_le]
  have hcpow_nn : 0 ≤ cStar ^ (-(3 : ℝ)) := Real.rpow_nonneg hcStar.le _
  have hMK_nn : 0 ≤ M + 1 + K := by linarith only [hM, hK]
  have hnum_nn : 0 ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) :=
    mul_nonneg (mul_nonneg hC hMK_nn) hcpow_nn
  -- Denominator: `(1-α')¹² ν⁴ ≤ (1-α)¹² ν⁴`.
  have hnu4_nn : 0 ≤ nu ^ (4 : ℝ) := Real.rpow_nonneg hnu.le _
  have h1ma12_le : (1 - alpha') ^ (12 : ℝ) ≤ (1 - alpha) ^ (12 : ℝ) :=
    Real.rpow_le_rpow h1ma_pos'.le h1ma_le (by norm_num)
  have hdenom_le : (1 - alpha') ^ (12 : ℝ) * nu ^ (4 : ℝ) ≤ (1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ) :=
    mul_le_mul_of_nonneg_right h1ma12_le hnu4_nn
  have hdenom_pos : 0 < (1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ) := denom_pos hnu halpha1
  have hdenom_pos' : 0 < (1 - alpha') ^ (12 : ℝ) * nu ^ (4 : ℝ) := denom_pos hnu halpha1'
  have hcoeff_mono : C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) /
        ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) ≤
      C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha') ^ (12 : ℝ) * nu ^ (4 : ℝ)) :=
    div_le_div_of_nonneg_left hnum_nn hdenom_pos' hdenom_le
  -- Log argument: `2 + (M+1+K)cStar⁻³/(ν(1-α)) ≤ 2 + (M+1+K)cStar⁻³/(ν(1-α'))`.
  have hden2_pos : 0 < nu * (1 - alpha) := mul_pos hnu h1ma_pos
  have hden2_pos' : 0 < nu * (1 - alpha') := mul_pos hnu h1ma_pos'
  have hden2_le : nu * (1 - alpha') ≤ nu * (1 - alpha) :=
    mul_le_mul_of_nonneg_left h1ma_le hnu.le
  have hMKc_nn : 0 ≤ (M + 1 + K) * cStar ^ (-(3 : ℝ)) := mul_nonneg hMK_nn hcpow_nn
  have hargfrac_mono : (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha)) ≤
      (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha')) :=
    div_le_div_of_nonneg_left hMKc_nn hden2_pos' hden2_le
  have harg_mono : 2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha)) ≤
      2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha')) := by
    linarith only [hargfrac_mono]
  have harg_pos : 0 < 2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha)) :=
    lt_of_lt_of_le (by norm_num) (log_arg_ge_two hM hK hcStar hnu halpha1)
  have hlog_mono : Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ≤
      Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha'))) :=
    Real.log_le_log harg_pos harg_mono
  have hlog_nn : 0 ≤ Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) :=
    (log_pos hM hK hcStar hnu halpha1).le
  have hlogpow_mono : Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) ≤
      Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha'))) ^ (12 : ℝ) :=
    Real.rpow_le_rpow hlog_nn hlog_mono (by norm_num)
  have hlogpow_nn' : 0 ≤ Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) :=
    Real.rpow_nonneg hlog_nn _
  have hcoeff_nn' : 0 ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) /
      ((1 - alpha') ^ (12 : ℝ) * nu ^ (4 : ℝ)) := div_nonneg hnum_nn hdenom_pos'.le
  unfold lNaughtInner
  calc C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) *
        Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ)
      ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha') ^ (12 : ℝ) * nu ^ (4 : ℝ)) *
          Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) :=
        mul_le_mul_of_nonneg_right hcoeff_mono hlogpow_nn'
    _ ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha') ^ (12 : ℝ) * nu ^ (4 : ℝ)) *
          Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha'))) ^ (12 : ℝ) :=
        mul_le_mul_of_nonneg_left hlogpow_mono hcoeff_nn'

/-- **`lNaught` is monotone in `alpha`**, once `lNaughtInner` at the target
`alpha'` is already `≥ 1` (so raising it to the larger outer exponent
`1/(1-α') ≥ 1/(1-α)` cannot decrease it). -/
theorem srootA_lNaught_mono_alpha {C M cStar nu K alpha alpha' : ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hK : 0 ≤ K) (hcStar : 0 < cStar) (hnu : 0 < nu)
    (_halpha0 : 0 ≤ alpha) (halpha_le : alpha ≤ alpha') (halpha1' : alpha' < 1)
    (hinner_ge1 : 1 ≤ lNaughtInner C M alpha' cStar nu K) :
    lNaught C M alpha cStar nu K ≤ lNaught C M alpha' cStar nu K := by
  have halpha1 : alpha < 1 := lt_of_le_of_lt halpha_le halpha1'
  have hinner_mono := srootA_inner_mono_alpha hC hM hK hcStar hnu halpha_le halpha1'
  have hinner_nn : 0 ≤ lNaughtInner C M alpha cStar nu K := inner_nonneg hC hM hK hcStar hnu halpha1
  have hp_nn : 0 ≤ (1 : ℝ) / (1 - alpha) := (outer_exponent_pos halpha1).le
  have step1 : lNaughtInner C M alpha cStar nu K ^ ((1 : ℝ) / (1 - alpha)) ≤
      lNaughtInner C M alpha' cStar nu K ^ ((1 : ℝ) / (1 - alpha)) :=
    Real.rpow_le_rpow hinner_nn hinner_mono hp_nn
  have hp_le : (1 : ℝ) / (1 - alpha) ≤ (1 : ℝ) / (1 - alpha') := by
    have h1ma_pos : 0 < 1 - alpha := one_minus_alpha_pos halpha1
    have h1ma_pos' : 0 < 1 - alpha' := one_minus_alpha_pos halpha1'
    have h1ma_le : 1 - alpha' ≤ 1 - alpha := by linarith only [halpha_le]
    exact one_div_le_one_div_of_le h1ma_pos' h1ma_le
  have step2 : lNaughtInner C M alpha' cStar nu K ^ ((1 : ℝ) / (1 - alpha)) ≤
      lNaughtInner C M alpha' cStar nu K ^ ((1 : ℝ) / (1 - alpha')) :=
    Real.rpow_le_rpow_of_exponent_le hinner_ge1 hp_le
  have heq1 : lNaught C M alpha cStar nu K = lNaughtInner C M alpha cStar nu K ^ ((1 : ℝ) / (1 - alpha)) :=
    newMixParam_lNaught_eq_inner_rpow C M alpha cStar nu K
  have heq2 : lNaught C M alpha' cStar nu K = lNaughtInner C M alpha' cStar nu K ^ ((1 : ℝ) / (1 - alpha')) :=
    newMixParam_lNaught_eq_inner_rpow C M alpha' cStar nu K
  rw [heq1, heq2]
  exact le_trans step1 step2

/-! ## `lNaughtInner ≥ 1` once the `M`-slot is large -/

/-- **`lNaughtInner ≥ 1`** once `C ≥ 1` and the `M`-slot is at least
`10 000 000` (crude: `C(M+1+K)cStar⁻³/((1-α)¹²ν⁴) ≥ M/8`, and the log-power
factor is `≥ (log 2)¹²`, so `M ≥ 687` already suffices; `10⁷` is a safe round
threshold). -/
theorem srootA_inner_ge_one {C M alpha cStar nu K : ℝ}
    (hC : 1 ≤ C) (hM : (10000000 : ℝ) ≤ M) (hK : 0 ≤ K) (hcStar : 0 < cStar) (hcStar2 : cStar ≤ 2)
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1) :
    1 ≤ lNaughtInner C M alpha cStar nu K := by
  have hcpow : (1 : ℝ) / 8 ≤ cStar ^ (-(3 : ℝ)) := newMixParam_cStar_neg3_ge hcStar hcStar2
  have hcpow_nn : (0 : ℝ) ≤ cStar ^ (-(3 : ℝ)) := le_trans (by norm_num) hcpow
  have h1ma_pos : 0 < 1 - alpha := one_minus_alpha_pos halpha1
  have h1ma_le1 : (1 - alpha) ^ (12 : ℝ) ≤ 1 := by
    calc (1 - alpha) ^ (12 : ℝ) ≤ (1 : ℝ) ^ (12 : ℝ) :=
          Real.rpow_le_rpow h1ma_pos.le (by linarith only [halpha0]) (by norm_num)
      _ = 1 := Real.one_rpow _
  have hnu4_le1 : nu ^ (4 : ℝ) ≤ 1 := by
    calc nu ^ (4 : ℝ) ≤ (1 : ℝ) ^ (4 : ℝ) := Real.rpow_le_rpow hnu.le hnu1 (by norm_num)
      _ = 1 := Real.one_rpow _
  have hnu4_nn : (0 : ℝ) ≤ nu ^ (4 : ℝ) := Real.rpow_nonneg hnu.le _
  have hdenom_le1 : (1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ) ≤ 1 := by
    calc (1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ) ≤ 1 * nu ^ (4 : ℝ) :=
          mul_le_mul_of_nonneg_right h1ma_le1 hnu4_nn
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hnu4_le1 (by norm_num)
      _ = 1 := by ring
  have hdenom_pos : (0 : ℝ) < (1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ) := denom_pos hnu halpha1
  have hMK_nn : (0 : ℝ) ≤ M + 1 + K := by linarith only [hM, hK]
  have hnumnn : (0 : ℝ) ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) :=
    mul_nonneg (mul_nonneg (by linarith only [hC]) hMK_nn) hcpow_nn
  have hfrac : C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) ≤
      C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) := by
    calc C * (M + 1 + K) * cStar ^ (-(3 : ℝ))
        = C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / 1 := by ring
      _ ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) :=
          div_le_div_of_nonneg_left hnumnn hdenom_pos hdenom_le1
  have hnum_ge : (M : ℝ) / 8 ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) := by
    have h1 : (1 : ℝ) * M * (1 / 8) ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) := by
      have ha : (1 : ℝ) * M ≤ C * (M + 1 + K) := by nlinarith only [hC, hM, hK]
      have hb : (1 : ℝ) * M * (1 / 8) ≤ C * (M + 1 + K) * (1 / 8) :=
        mul_le_mul_of_nonneg_right ha (by norm_num)
      have hc : C * (M + 1 + K) * (1 / 8) ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) :=
        mul_le_mul_of_nonneg_left hcpow (by nlinarith only [hC, hMK_nn])
      linarith only [hb, hc]
    linarith only [h1]
  have hcoeff_ge : (M : ℝ) / 8 ≤
      C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) :=
    le_trans hnum_ge hfrac
  -- Log-power factor `≥ (log 2)¹² ≥ (69/100)¹²`.
  have hlogarg_ge2 := log_arg_ge_two (by linarith only [hM] : (0 : ℝ) ≤ M) hK hcStar hnu halpha1
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogmono : Real.log 2 ≤
      Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) :=
    Real.log_le_log (by norm_num) hlogarg_ge2
  have hlogpow_ge : (Real.log 2) ^ (12 : ℝ) ≤
      Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) :=
    Real.rpow_le_rpow hlog2pos.le hlogmono (by norm_num)
  have hlog2gt : (69 : ℝ) / 100 < Real.log 2 := by
    have h := Real.log_two_gt_d9; linarith only [h]
  have hlog2pow69 : ((69 : ℝ) / 100) ^ (12 : ℝ) ≤ (Real.log 2) ^ (12 : ℝ) :=
    Real.rpow_le_rpow (by norm_num) hlog2gt.le (by norm_num)
  have hlog2pow69eq : ((69 : ℝ) / 100) ^ (12 : ℝ) = ((69 : ℝ) / 100) ^ (12 : ℕ) := by
    rw [show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hlogpow_ge69 : ((69 : ℝ) / 100) ^ (12 : ℕ) ≤
      Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) := by
    linarith only [hlog2pow69, hlog2pow69eq, hlogpow_ge]
  -- Combine: `inner ≥ (M/8) * (69/100)¹²`, and `M ≥ 10⁷` makes this `≥ 1`.
  have hcoeff_nn : (0 : ℝ) ≤ (M : ℝ) / 8 := by linarith only [hM]
  have hlogpow_nn69 : (0 : ℝ) ≤ ((69 : ℝ) / 100) ^ (12 : ℕ) := by positivity
  have hfinal_ge : (M / 8) * ((69 : ℝ) / 100) ^ (12 : ℕ) ≤ lNaughtInner C M alpha cStar nu K := by
    unfold lNaughtInner
    calc (M / 8) * ((69 : ℝ) / 100) ^ (12 : ℕ)
        ≤ (C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ))) *
            ((69 : ℝ) / 100) ^ (12 : ℕ) :=
          mul_le_mul_of_nonneg_right hcoeff_ge hlogpow_nn69
      _ ≤ (C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ))) *
            Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) := by
          apply mul_le_mul_of_nonneg_left hlogpow_ge69
          exact div_nonneg hnumnn hdenom_pos.le
  have h1le : (1 : ℝ) ≤ (M / 8) * ((69 : ℝ) / 100) ^ (12 : ℕ) := by
    have hval : (1 : ℝ) ≤ (10000000 : ℝ) / 8 * ((69 : ℝ) / 100) ^ (12 : ℕ) := by norm_num
    have hMdiv : (10000000 : ℝ) / 8 ≤ M / 8 := by linarith only [hM]
    nlinarith only [hval, hMdiv, hlogpow_nn69]
  linarith only [h1le, hfinal_ge]

/-! ## `hThr` itself -/

/-- **`hThr`** (`SkeletonRoot.lean`'s named hypothesis, `e.new.mixing.minscale.thresholds`): the
mixing threshold at `K = C M s⁻¹` lies below `hat L₂`, via the FIRST `L₀` term of `hat L₂`. -/
theorem srootA_hThr :
    ∀ CE : ℝ, 1 ≤ CE → ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ C : ℝ, C0 ≤ C →
      ∀ (nu cStar nondeg : ℝ), 0 < nu → nu ≤ 1 → 0 < cStar → cStar ≤ 2 → 0 < nondeg →
        ∀ (expon delta s M : ℝ), 0 < expon → expon < 1 / 2 → 0 < delta → delta ≤ 1 →
          0 < s → s ≤ 1 → 1 ≤ M →
            lNaught CE (CE * s⁻¹ * (C * M * s⁻¹)) (1 / 2) cStar nu nondeg ≤
              srootMS_Lhat2 C expon delta s M cStar nu nondeg := by
  intro CE hCE1
  have hCEpos : (0 : ℝ) < CE := lt_of_lt_of_le one_pos hCE1
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set CE' : ℝ := CE * CE * (1 + Real.log CE / Real.log 2) ^ (12 : ℝ) with hCE'def
  have hlogCE_nn : (0 : ℝ) ≤ Real.log CE := Real.log_nonneg hCE1
  have hfactor_ge1 : (1 : ℝ) ≤ 1 + Real.log CE / Real.log 2 := by
    have : (0 : ℝ) ≤ Real.log CE / Real.log 2 := div_nonneg hlogCE_nn hlog2pos.le
    linarith only [this]
  have hfactorpow_ge1 : (1 : ℝ) ≤ (1 + Real.log CE / Real.log 2) ^ (12 : ℝ) := by
    calc (1 : ℝ) = (1 : ℝ) ^ (12 : ℝ) := (Real.one_rpow _).symm
      _ ≤ (1 + Real.log CE / Real.log 2) ^ (12 : ℝ) :=
          Real.rpow_le_rpow (by norm_num) hfactor_ge1 (by norm_num)
  have hCE'_ge1 : (1 : ℝ) ≤ CE' := by
    have h1 : (1 : ℝ) ≤ CE * CE := by nlinarith only [hCE1]
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (CE * CE) * (1 + Real.log CE / Real.log 2) ^ (12 : ℝ) :=
          mul_le_mul h1 hfactorpow_ge1 (by norm_num) (by nlinarith only [hCE1])
      _ = CE' := by rw [hCE'def]
  refine ⟨max CE' 10000000, le_trans hCE'_ge1 (le_max_left _ _), ?_⟩
  intro C hC0 nu cStar nondeg hnu hnu1 hcStar hcStar2 hnondeg expon delta s M hexp0 hexp1
    hdel0 hdel1 hs0 hs1 hM
  have hCC' : CE' ≤ C := le_trans (le_max_left _ _) hC0
  have hC10M : (10000000 : ℝ) ≤ C := le_trans (le_max_right _ _) hC0
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le (by norm_num) hC10M
  have hexpon1 : (1 : ℝ) - expon < 1 := by linarith only [hexp0]
  -- Step A: monotone in `alpha`, from `1/2` up to `1 - expon`.
  set Mslot : ℝ := CE * s⁻¹ * (C * M * s⁻¹) with hMslotdef
  have hMslot_nn : (0 : ℝ) ≤ Mslot := by
    have : (0 : ℝ) < s⁻¹ := inv_pos.2 hs0
    rw [hMslotdef]; positivity
  have hMslot_ge : (10000000 : ℝ) ≤ Mslot := by
    have hsinv1 : (1 : ℝ) ≤ s⁻¹ := one_le_inv₀ hs0 |>.2 hs1
    have h1 : C ≤ C * M := le_mul_of_one_le_right hCpos.le hM
    have h2 : C * M ≤ C * M * s⁻¹ := le_mul_of_one_le_right (by positivity) hsinv1
    have h3 : C * M * s⁻¹ ≤ CE * (C * M * s⁻¹) := le_mul_of_one_le_left (by positivity) hCE1
    have h4 : CE * (C * M * s⁻¹) ≤ CE * (C * M * s⁻¹) * s⁻¹ :=
      le_mul_of_one_le_right (by positivity) hsinv1
    rw [hMslotdef]
    have heq : CE * s⁻¹ * (C * M * s⁻¹) = CE * (C * M * s⁻¹) * s⁻¹ := by ring
    rw [heq]
    linarith only [hC10M, h1, h2, h3, h4]
  have hinner_ge1 : 1 ≤ lNaughtInner CE Mslot (1 - expon) cStar nu nondeg :=
    srootA_inner_ge_one hCE1 hMslot_ge hnondeg.le hcStar hcStar2 hnu hnu1
      (by linarith only [hexp0, hexp1]) hexpon1
  have hStepA : lNaught CE Mslot (1 / 2) cStar nu nondeg ≤
      lNaught CE Mslot (1 - expon) cStar nu nondeg :=
    srootA_lNaught_mono_alpha hCEpos.le hMslot_nn hnondeg.le hcStar hnu (by norm_num)
      (by linarith only [hexp1]) hexpon1 hinner_ge1
  -- Step B: `lNaught_mul_M_le` with `K' := CE`, peeling `CE` off `Mslot`.
  set M0 : ℝ := C * M * (s⁻¹ * s⁻¹) with hM0def
  have hMslot_eq : Mslot = CE * M0 := by rw [hMslotdef, hM0def]; ring
  have hM0_nn : (0 : ℝ) ≤ M0 := by rw [hM0def]; positivity
  have hStepB : lNaught CE (CE * M0) (1 - expon) cStar nu nondeg ≤
      lNaught CE' M0 (1 - expon) cStar nu nondeg := by
    rw [hCE'def]
    exact lNaught_mul_M_le CE M0 (1 - expon) cStar nu nondeg CE hCEpos.le hM0_nn hexpon1 hcStar
      hnu hnondeg.le hCE1
  -- Step C: monotone in `(C,M)`, from `(CE', M0)` up to the target first `L₀` term.
  set Target : ℝ := C * expon⁻¹ * delta ^ (-(2 : ℝ)) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ) with hTargetdef
  have hM0_le_Target : M0 ≤ Target := by
    have hsinv_eq : s ^ (-(1 : ℝ)) = s⁻¹ := by rw [Real.rpow_neg hs0.le, Real.rpow_one]
    have hs2_eq : s⁻¹ * s⁻¹ = s ^ (-(2 : ℝ)) := by
      rw [← hsinv_eq, ← Real.rpow_add hs0]; norm_num
    have hs24 : s ^ (-(2 : ℝ)) ≤ s ^ (-(4 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge hs0 hs1 (by norm_num)
    have hs2_nn : (0 : ℝ) ≤ s ^ (-(2 : ℝ)) := Real.rpow_nonneg hs0.le _
    have hM_le_Msq : M ≤ M ^ (2 : ℝ) := by
      have h2 : M ^ (2 : ℝ) = M ^ (2 : ℕ) := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [h2]; nlinarith only [hM]
    have hMnn : (0 : ℝ) ≤ M := by linarith only [hM]
    have hstep1 : M * (s⁻¹ * s⁻¹) ≤ M ^ (2 : ℝ) * s ^ (-(4 : ℝ)) := by
      rw [hs2_eq]
      calc M * s ^ (-(2 : ℝ)) ≤ M ^ (2 : ℝ) * s ^ (-(2 : ℝ)) :=
            mul_le_mul_of_nonneg_right hM_le_Msq hs2_nn
        _ ≤ M ^ (2 : ℝ) * s ^ (-(4 : ℝ)) :=
            mul_le_mul_of_nonneg_left hs24 (by positivity)
    have hexpinv2 : (2 : ℝ) < expon⁻¹ := by
      rw [inv_eq_one_div, lt_div_iff₀ hexp0]; linarith only [hexp1]
    have hdelta2 : (1 : ℝ) ≤ delta ^ (-(2 : ℝ)) := by
      have h := Real.rpow_le_rpow_of_exponent_ge hdel0 hdel1
        (show (-(2 : ℝ)) ≤ (0 : ℝ) by norm_num)
      rwa [Real.rpow_zero] at h
    have hstep2 : (1 : ℝ) ≤ expon⁻¹ * delta ^ (-(2 : ℝ)) := by nlinarith only [hexpinv2, hdelta2]
    have hMs4_nn : (0 : ℝ) ≤ M ^ (2 : ℝ) * s ^ (-(4 : ℝ)) := by positivity
    have hstep3 : M ^ (2 : ℝ) * s ^ (-(4 : ℝ)) ≤
        (expon⁻¹ * delta ^ (-(2 : ℝ))) * (M ^ (2 : ℝ) * s ^ (-(4 : ℝ))) := by
      nlinarith only [hstep2, hMs4_nn]
    have hCnn : (0 : ℝ) ≤ C := hCpos.le
    calc M0 = C * (M * (s⁻¹ * s⁻¹)) := by rw [hM0def]; ring
      _ ≤ C * (M ^ (2 : ℝ) * s ^ (-(4 : ℝ))) := mul_le_mul_of_nonneg_left hstep1 hCnn
      _ ≤ C * ((expon⁻¹ * delta ^ (-(2 : ℝ))) * (M ^ (2 : ℝ) * s ^ (-(4 : ℝ)))) :=
          mul_le_mul_of_nonneg_left hstep3 hCnn
      _ = Target := by rw [hTargetdef]; ring
  have hCE'_nn : (0 : ℝ) ≤ CE' := le_trans zero_le_one hCE'_ge1
  have hStepC : lNaught CE' M0 (1 - expon) cStar nu nondeg ≤
      lNaught C Target (1 - expon) cStar nu nondeg :=
    lNaught_mono_both hCE'_nn hCC' hM0_nn hM0_le_Target hnondeg.le hcStar hnu hexpon1
  have hStepA' : lNaught CE (CE * M0) (1 / 2) cStar nu nondeg ≤
      lNaught CE (CE * M0) (1 - expon) cStar nu nondeg := by
    rw [← hMslot_eq]; exact hStepA
  have hchain : lNaught CE (CE * M0) (1 / 2) cStar nu nondeg ≤
      lNaught C Target (1 - expon) cStar nu nondeg :=
    le_trans hStepA' (le_trans hStepB hStepC)
  rw [hMslot_eq]
  unfold srootMS_Lhat2
  exact le_trans hchain (le_max_left _ _)

end
end SuperdiffusionCLT.Section4.MinimalScales
