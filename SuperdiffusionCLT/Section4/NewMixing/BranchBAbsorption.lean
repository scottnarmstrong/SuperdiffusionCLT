/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.NewMixing.LogGrowth

/-!
# Branch B's numeric fact: `3^{-(d/2)(m-L)} ≤ m^{-12000}` for `m > L + h`

The `T_0`-refinement step
(`l.new.mixing.parameterized#T0-refinement`), branch `m > L+h`
of the scale construction `newMixAsm_scaleExplicit`
(`ell := L`, `n := L-h`). The numeric inequality is true
with an explicit threshold on `L`, as follows.

Two regimes: `m - L ≤ L` (reuse `LogGrowth.lean`'s branch-A chain, `h`
replaced by `m-L`, times the free `d/2 ≥ 1` slack) and `m - L > L` (a
self-contained `log x ≤ 2√x` bound, once `L` clears an absolute threshold
`10^9`, itself obtained from `newMixParam_lNaughtInner_ge` directly — no
`log`/`exp` detour needed).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.NewMixing

open SuperdiffusionCLT.Section4.LNaught

noncomputable section

/-- `log x ≤ 2√x` for `x > 0`. -/
private theorem newMixParam_log_le_two_sqrt {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ 2 * Real.sqrt x := by
  have ht : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  have h2 : Real.log x = 2 * Real.log (Real.sqrt x) := by
    have hpow : Real.log (Real.sqrt x ^ 2) = 2 * Real.log (Real.sqrt x) := by
      rw [Real.log_pow]; push_cast; ring
    rw [hsq] at hpow
    exact hpow
  have h1 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 := Real.log_le_sub_one_of_pos ht
  rw [h2]
  linarith only [h1]

/-- `L ≥ 10⁹` once `C ≥ 10⁶` and `L ≥ lNaught C M alpha cStar nu K` (with the
usual `M ≥ 2C` slack). Bypasses the `log`/`exp` route of
`newMixParam_logL_ge_sixteen`, going through `lNaughtInner` directly. -/
private theorem newMixParam_L_ge_billion {C M alpha cStar nu K : ℝ}
    (hC : (1000000 : ℝ) ≤ C) (hM : 2 * C ≤ M) (hK : 0 ≤ K) (hcStar : 0 < cStar)
    (hcStar2 : cStar ≤ 2) (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hα0 : 0 ≤ alpha) (halpha : alpha < 1)
    {L : ℕ}
    (hL : SuperdiffusionCLT.Frozen.Section4.lNaught C M alpha cStar nu K ≤ (L : ℝ)) :
    (1000000000 : ℝ) ≤ (L : ℝ) := by
  have hC1 : (1 : ℝ) ≤ C := le_trans (by norm_num) hC
  have hInner := newMixParam_lNaughtInner_ge hC1 hM hK hcStar hcStar2 hnu hnu1 hα0 halpha
  have hval : (1000000000 : ℝ) ≤ (C ^ 2 / 4) * (Real.log 2) ^ (12 : ℝ) := by
    have hlog2gt : (69 : ℝ) / 100 < Real.log 2 := by
      have h := Real.log_two_gt_d9; linarith only [h]
    have hlog2nn : (0 : ℝ) ≤ (69 : ℝ) / 100 := by norm_num
    have hlog2pow : ((69 : ℝ) / 100) ^ (12 : ℝ) ≤ (Real.log 2) ^ (12 : ℝ) :=
      Real.rpow_le_rpow hlog2nn hlog2gt.le (by norm_num)
    have hlog2pow_eq : ((69 : ℝ) / 100) ^ (12 : ℝ) = ((69 : ℝ) / 100) ^ (12 : ℕ) := by
      rw [show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hClarge : (1000000 : ℝ) ^ 2 ≤ C ^ 2 := by nlinarith only [hC]
    have hnum : (1000000000 : ℝ) ≤ (1000000 : ℝ) ^ 2 / 4 * (((69 : ℝ) / 100) ^ (12 : ℕ)) := by
      norm_num
    nlinarith only [hClarge, hlog2pow, hlog2pow_eq, hnum]
  have hInnerGe : (1000000000 : ℝ) ≤ lNaughtInner C M alpha cStar nu K := le_trans hval hInner
  have h1ma_pos : (0 : ℝ) < 1 - alpha := one_minus_alpha_pos halpha
  have hexpge1 : (1 : ℝ) ≤ (1 : ℝ) / (1 - alpha) := by
    rw [le_div_iff₀ h1ma_pos]; linarith only [hα0]
  have hbase1 : (1 : ℝ) ≤ lNaughtInner C M alpha cStar nu K := le_trans (by norm_num) hInnerGe
  have hNaughtGeInner : lNaughtInner C M alpha cStar nu K ≤
      SuperdiffusionCLT.Frozen.Section4.lNaught C M alpha cStar nu K := by
    rw [newMixParam_lNaught_eq_inner_rpow]
    have h1 : lNaughtInner C M alpha cStar nu K ^ (1 : ℝ) ≤
        lNaughtInner C M alpha cStar nu K ^ ((1 : ℝ) / (1 - alpha)) :=
      Real.rpow_le_rpow_of_exponent_le hbase1 hexpge1
    rwa [Real.rpow_one] at h1
  linarith only [hInnerGe, hNaughtGeInner, hL]

/-- **Branch B's numeric fact**: `3^{-(d/2)(m-L)} ≤ m^{-12000}` once `m > L+h`
(`h := newMixParam_h K (Real.log L)`, the same deterministic `h` as
the branch split of `newMixAsm_scaleExplicit`), for `d ≥ 2`. -/
theorem newMixParam_threeNeg_halfd_mMinusL_le_mNeg12000 (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧ (1000000 : ℝ) ≤ C ∧
      ∀ (M K alpha cStar nu nondeg : ℝ),
        1 ≤ M → 1 ≤ K → 0 ≤ alpha → alpha < 1 → 0 < cStar → cStar ≤ 2 → 0 < nu → nu ≤ 1 →
        0 ≤ nondeg →
        ∀ L m : ℕ,
          SuperdiffusionCLT.Frozen.Section4.lNaught C (C * (M + K)) alpha cStar nu nondeg ≤
            (L : ℝ) →
          SuperdiffusionCLT.Frozen.Section4.lNaught C (C * (M + K)) alpha cStar nu nondeg ≤
            (m : ℝ) →
          L + newMixParam_h K (Real.log (L : ℝ)) < m →
          (3 : ℝ) ^ (-((d : ℝ) / 2 * ((m - L : ℕ) : ℝ))) ≤ (m : ℝ) ^ (-(12000 : ℝ)) := by
  obtain ⟨C0, hC0, hslack⟩ := newMixParam_absorbSlack
  refine ⟨max C0 1000000, le_trans hC0 (le_max_left _ _), le_max_right _ _, ?_⟩
  intro M K alpha cStar nu nondeg hM hK hα0 hα1 hcStar hcStar2 hnu hnu1 hnondeg L m hL hm hcaseB
  set C := max C0 1000000 with hCdef
  have hC0' : C0 ≤ C := le_max_left _ _
  have hC : (1000000 : ℝ) ≤ C := le_max_right _ _
  have h2CleM : 2 * C ≤ C * (M + K) := by nlinarith only [hC, hM, hK]
  have hLbig : (1000000000 : ℝ) ≤ (L : ℝ) :=
    newMixParam_L_ge_billion hC h2CleM hnondeg hcStar hcStar2 hnu hnu1 hα0 hα1 hL
  have hLpos : (0 : ℝ) < (L : ℝ) := by linarith only [hLbig]
  set S : ℕ := m - L with hSdef
  have hmL : L < m := by
    have hhnn : 0 ≤ newMixParam_h K (Real.log (L : ℝ)) := Nat.zero_le _
    omega
  have hScast : (S : ℝ) = (m : ℝ) - (L : ℝ) := by
    rw [hSdef]; exact_mod_cast Nat.cast_sub hmL.le
  have hmeqLS : (m : ℝ) = (L : ℝ) + (S : ℝ) := by linarith only [hScast]
  have hSpos : (0 : ℝ) < (S : ℝ) := by
    have : L < m := hmL
    have hS1 : 1 ≤ S := by omega
    exact_mod_cast hS1
  have hlogLlarge : (20 : ℝ) ≤ Real.log (L : ℝ) := by
    have h9 : Real.exp 20 < (L : ℝ) := by
      have hexp20 : Real.exp 20 < (500000000 : ℝ) := by
        have he : Real.exp 20 = (Real.exp 1) ^ (20 : ℕ) := by
          rw [← Real.exp_nat_mul]; norm_num
        rw [he]
        have h1 : Real.exp 1 < 2.72 := lt_trans Real.exp_one_lt_d9 (by norm_num)
        have h2 : (0 : ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
        have h3 : (2.72 : ℝ) ^ (20 : ℕ) < 500000000 := by norm_num
        exact lt_trans (pow_lt_pow_left₀ h1 h2 (by norm_num)) h3
      linarith only [hexp20, hLbig]
    have h10 := Real.log_lt_log (Real.exp_pos 20) h9
    rw [Real.log_exp] at h10
    exact h10.le
  have hL1 : (1 : ℝ) < (L : ℝ) := by linarith only [hlogLlarge, hLpos, hLbig]
  have hKnn : (0 : ℝ) ≤ K := le_trans zero_le_one hK
  set h := newMixParam_h K (Real.log (L : ℝ)) with hhdef
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le (by norm_num) hC
  have hmtot : K * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (L : ℝ) / (2 * C) := by
    obtain ⟨_, _, hKLslack⟩ :=
      hslack C hC0' M K alpha cStar nu nondeg hM hK hα0 hα1 hcStar hcStar2 hnu hnu1 hnondeg L hL
    exact hKLslack
  have hlog3gt : (13 : ℝ) / 12 < Real.log 3 := newMixParam_log3_gt_13_div_12
  have hlog3nn : (0 : ℝ) ≤ Real.log 3 := le_trans (by norm_num) hlog3gt.le
  have hhge : newMixParam_K0 * K * Real.log (L : ℝ) ≤ (h : ℝ) := newMixParam_h_ge
  have hK0eq : newMixParam_K0 = 12000 := rfl
  have hhge12000K : (12000 : ℝ) * K * Real.log (L : ℝ) ≤ (h : ℝ) := by rw [hK0eq] at hhge; exact hhge
  have hSgeh : (h : ℝ) < (S : ℝ) := by
    have : h < S := by omega
    exact_mod_cast this
  have hSge12000K : (12000 : ℝ) * K * Real.log (L : ℝ) ≤ (S : ℝ) := le_trans hhge12000K hSgeh.le
  -- The core chain: `12000 log m ≤ S log3`, regardless of `S` vs `L`.
  have hchain : (12000 : ℝ) * Real.log (m : ℝ) ≤ (S : ℝ) * Real.log 3 := by
    rcases le_or_gt (S : ℝ) (L : ℝ) with hSL | hSL
    · -- Case (i): `S ≤ L`. Branch-A's own chain, `h ↦ S`.
      have hlogm_le : Real.log (m : ℝ) ≤ Real.log (L : ℝ) + Real.log 2 := by
        have hmle2L : (m : ℝ) ≤ 2 * (L : ℝ) := by rw [hmeqLS]; linarith only [hSL]
        have hstep := Real.log_le_log (by linarith only [hL1, hSpos, hmeqLS] : (0 : ℝ) < (m : ℝ)) hmle2L
        rw [Real.log_mul (by norm_num) (by linarith only [hL1])] at hstep
        linarith only [hstep]
      have hlog2lt1 : Real.log 2 < 1 := lt_trans Real.log_two_lt_d9 (by norm_num)
      have hlogL12 : (12 : ℝ) ≤ Real.log (L : ℝ) := by linarith only [hlogLlarge]
      have hlogLlog3 : Real.log (L : ℝ) + Real.log 2 ≤ Real.log (L : ℝ) * Real.log 3 := by
        have hprod : (12 : ℝ) * ((13 : ℝ) / 12 - 1) ≤ Real.log (L : ℝ) * (Real.log 3 - 1) := by
          apply mul_le_mul hlogL12 (by linarith only [hlog3gt]) (by norm_num)
            (by linarith only [hlogL12])
        have hprodval : (12 : ℝ) * ((13 : ℝ) / 12 - 1) = 1 := by norm_num
        nlinarith only [hprod, hprodval, hlog2lt1]
      have hlogm_leLlog3 : Real.log (m : ℝ) ≤ Real.log (L : ℝ) * Real.log 3 := by
        linarith only [hlogm_le, hlogLlog3]
      have hKLlog3 : Real.log (L : ℝ) * Real.log 3 ≤ K * (Real.log (L : ℝ) * Real.log 3) := by
        have hLlog3nn : (0 : ℝ) ≤ Real.log (L : ℝ) * Real.log 3 := by positivity
        nlinarith only [hK, hLlog3nn]
      have hstep1 : (12000 : ℝ) * Real.log (m : ℝ) ≤
          12000 * (K * (Real.log (L : ℝ) * Real.log 3)) := by
        nlinarith only [hlogm_leLlog3, hKLlog3]
      have hstep2 : (12000 : ℝ) * (K * (Real.log (L : ℝ) * Real.log 3)) =
          (12000 * K * Real.log (L : ℝ)) * Real.log 3 := by ring
      have hstep3 : (12000 * K * Real.log (L : ℝ)) * Real.log 3 ≤ (S : ℝ) * Real.log 3 :=
        mul_le_mul_of_nonneg_right hSge12000K hlog3nn
      linarith only [hstep1, hstep2.le, hstep2.ge, hstep3]
    · -- Case (ii): `S > L`. Absolute `log x ≤ 2√x` bound.
      have hlogm_le : Real.log (m : ℝ) ≤ Real.log 2 + Real.log (S : ℝ) := by
        have hmle2S : (m : ℝ) ≤ 2 * (S : ℝ) := by rw [hmeqLS]; linarith only [hSL]
        have hstep := Real.log_le_log (by linarith only [hL1, hSpos, hmeqLS] : (0 : ℝ) < (m : ℝ)) hmle2S
        rwa [Real.log_mul (by norm_num) hSpos.ne'] at hstep
      have hSbig : (1000000000 : ℝ) ≤ (S : ℝ) := le_of_lt (lt_of_le_of_lt hLbig hSL)
      have hlogSle : Real.log (S : ℝ) ≤ 2 * Real.sqrt (S : ℝ) := newMixParam_log_le_two_sqrt hSpos
      have hu : (25000 : ℝ) ≤ Real.sqrt (S : ℝ) := by
        have hSge : (25000 : ℝ) ^ 2 ≤ (S : ℝ) := by nlinarith only [hSbig]
        have := Real.sqrt_le_sqrt hSge
        rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 25000)] at this
      have husq : Real.sqrt (S : ℝ) * Real.sqrt (S : ℝ) = (S : ℝ) :=
        Real.mul_self_sqrt hSpos.le
      have hlog2lt1 : Real.log 2 < 1 := lt_trans Real.log_two_lt_d9 (by norm_num)
      have husqnn : (0:ℝ) ≤ Real.sqrt (S:ℝ) := Real.sqrt_nonneg _
      have hfinal : (12000:ℝ) * (Real.log 2 + Real.log (S:ℝ)) ≤ (S:ℝ) * Real.log 3 := by
        nlinarith only [hlogSle, hu, husq, hlog2lt1, hlog3gt, husqnn, hSbig]
      linarith only [hlogm_le, hfinal]
  have hdhalf : (1 : ℝ) ≤ (d : ℝ) / 2 := by
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith only [this]
  have hSnn : (0:ℝ) ≤ (S:ℝ) := hSpos.le
  have hchain2 : (12000:ℝ) * Real.log (m:ℝ) ≤ (d:ℝ)/2 * ((S:ℝ) * Real.log 3) := by
    have hmul : (S:ℝ) * Real.log 3 ≤ (d:ℝ)/2 * ((S:ℝ) * Real.log 3) := by
      have hSlog3nn : (0:ℝ) ≤ (S:ℝ) * Real.log 3 := mul_nonneg hSnn hlog3nn
      nlinarith only [hdhalf, hSlog3nn]
    linarith only [hchain, hmul]
  -- Convert to `3^{-(d/2)S} ≤ m^{-12000}` via `exp`/`log` algebra.
  have hmpos : (0:ℝ) < (m:ℝ) := by linarith only [hL1, hSpos, hmeqLS]
  have h3pos : (0:ℝ) < (3:ℝ) := by norm_num
  have heq3 : (3:ℝ) ^ (-((d:ℝ)/2 * (S:ℝ))) = Real.exp (-((d:ℝ)/2 * (S:ℝ)) * Real.log 3) := by
    rw [Real.rpow_def_of_pos h3pos]; congr 1; ring
  have heqm : (m:ℝ) ^ (-(12000:ℝ)) = Real.exp (-(12000:ℝ) * Real.log (m:ℝ)) := by
    rw [Real.rpow_def_of_pos hmpos]; congr 1; ring
  rw [heq3, heqm]
  apply Real.exp_le_exp.mpr
  nlinarith only [hchain2]

end
end SuperdiffusionCLT.Section4.NewMixing
