/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Frozen.Section4.HomogenizationBelowCutoff
public import SuperdiffusionCLT.Section5.Thresholds.LVsLnaughtAgain
public import SuperdiffusionCLT.Section5.Thresholds.ScaleArithmetic
public import SuperdiffusionCLT.Section4.LNaught.Threshold
public import SuperdiffusionCLT.Section4.LNaught.Monotone
public import SuperdiffusionCLT.Section2.Localization.LocalizationCubePassage

/-!
# `p.homog.below` at the scales of Section 5 (`e.ass.valid.applied`)

`homogenization_below_cutoff` is applied at `(L, m, α, M) = (m - h, n, 3/4, 401)`.
Besides the standing scale conditions `1 ≤ h`, `400 h ≤ m`, `2 L₀ ≤ m` nothing
beyond the shell laws is assumed: `m ≥ ν⁻²` and `n ≥ m/2` are consequences of `m ≥ 2 L₀`
once the shared constant is large, as is the crude bound `shom ≤ C ν⁻¹ m` of `e.crude.shom.bnd`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section4 (lNaught)

/-- The crude bound `shom_L ≤ C ν⁻¹ max(1, L)` (`e.crude.shom.bnd`). -/
theorem sigmaBarInfinite_crude (d : ℕ) [NeZero d] {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1) (L : ℕ)
    {P : MeasureTheory.ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) :
    sigmaBarInfinite nu L P ≤
      (1 + 2 * cutoffEnvelopeConst d) * nu⁻¹ * max 1 (L : ℝ) :=
  le_trans (sigmaBarInfinite_le_sigmaBarUpperLimit hnu L hPrefix hJ2 hJ3 hJ4)
    (le_trans (sigmaBarUpperLimit_le hnu L hPrefix hJ2 hJ3 hJ4 0)
      (le_trans (sigmaBarSeq_le_envelopeUpperScalar hnu L hPrefix hJ2 hJ3 hJ4 0)
        (SuperdiffusionCLT.Section2.Localization.envelopeUpperScalar_le_nuInv_mul_max
          hnu hnu1 L)))

/-- `m ≥ (C/8)^4` and `ν⁻¹^16 ≤ m` from `L₀(C, C, 3/4, c⋆, ν) ≤ m`. -/
theorem m_large_of_lNaught :
    ∃ C₀ : ℝ, 1000 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∀ cStar : ℝ, 0 < cStar → cStar ≤ 2 →
      ∀ nu : ℝ, 0 < nu → nu ≤ 1 → ∀ K : ℝ, 0 ≤ K → ∀ m : ℕ,
        lNaught C C (3 / 4) cStar nu K ≤ (m : ℝ) →
        (C / 8) ^ 4 ≤ (m : ℝ) ∧ nu⁻¹ ^ 16 ≤ (m : ℝ) := by
  obtain ⟨Cth, hCth1, Hth⟩ := SuperdiffusionCLT.Section4.LNaught.lNaught_threshold
  obtain ⟨Cge, hCge1, Hge⟩ := SuperdiffusionCLT.Section4.LNaught.lNaught_ge
  refine ⟨max 1000 (max Cth Cge), le_max_left _ _, fun C hC cStar hc hc2 nu hnu hnu1 K hK m hm => ?_⟩
  have hCth : Cth ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC
  have hCge : Cge ≤ C := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC
  have hC1000 : 1000 ≤ C := le_trans (le_max_left _ _) hC
  have h8 := Hge C hCge C (by linarith only [hC1000]) (3 / 4) (by norm_num) (by norm_num) cStar hc hc2
    nu hnu hnu1 K hK
  have hm8 : (8 : ℝ) < m := lt_of_lt_of_le h8 hm
  have hth := (Hth C hCth C (by linarith only [hC1000]) (3 / 4) (by norm_num) (by norm_num) cStar hc
    hc2 nu hnu hnu1 K hK m hm).1
  have hm0 : 0 < (m : ℝ) := by linarith only [hm8]
  have hlog : 1 ≤ Real.log (m : ℝ) := by
    have := Real.log_le_log (by norm_num) hm8.le
    have h2 : (2 : ℝ) < Real.log 8 := by
      have heq : Real.log 8 = 3 * Real.log 2 := by
        rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
      rw [heq]; linarith only [Real.log_two_gt_d9]
    linarith only [this, h2]
  have hlog12 : 1 ≤ Real.log (m : ℝ) ^ (12 : ℝ) := Real.one_le_rpow hlog (by norm_num)
  have hc3 : 1 / 8 ≤ cStar ^ (-(3 : ℝ)) := by
    rw [Real.rpow_neg hc.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h3 : cStar ^ 3 ≤ 8 := by nlinarith only [hc, hc2, mul_pos hc hc]
    rw [show (1 : ℝ) / 8 = (8 : ℝ)⁻¹ by norm_num]
    exact inv_anti₀ (by positivity) h3
  have hnu4 : nu ^ (-(4 : ℝ)) = (nu⁻¹) ^ 4 := by
    rw [Real.rpow_neg hnu.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, inv_pow]
  have hnuinv1 : 1 ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
  have hnu41 : 1 ≤ (nu⁻¹) ^ 4 := one_le_pow₀ hnuinv1
  set q : ℝ := (m : ℝ) ^ (1 - 3 / 4 : ℝ) with hq
  have hq4 : q ^ 4 = m := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul hm0.le]; norm_num
  have hq0 : 0 ≤ q := by positivity
  have hmain : C / 8 * (nu⁻¹) ^ 4 ≤ q := by
    rw [hnu4] at hth
    have h1 : C / 8 * (nu⁻¹) ^ 4 * 1 ≤ C * cStar ^ (-(3 : ℝ)) * (nu⁻¹) ^ 4 *
        Real.log (m : ℝ) ^ (12 : ℝ) := by
      have : C / 8 ≤ C * cStar ^ (-(3 : ℝ)) := by nlinarith only [hc3, hC1000]
      have h2 : C / 8 * (nu⁻¹) ^ 4 ≤ C * cStar ^ (-(3 : ℝ)) * (nu⁻¹) ^ 4 :=
        mul_le_mul_of_nonneg_right this (by positivity)
      calc C / 8 * (nu⁻¹) ^ 4 * 1 = C / 8 * (nu⁻¹) ^ 4 := mul_one _
        _ ≤ C * cStar ^ (-(3 : ℝ)) * (nu⁻¹) ^ 4 := h2
        _ = C * cStar ^ (-(3 : ℝ)) * (nu⁻¹) ^ 4 * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hlog12 (by positivity)
    linarith only [h1, hth]
  have hC8 : 1 ≤ C / 8 := by linarith only [hC1000]
  have hA : C / 8 ≤ q := by nlinarith only [hmain, hnu41, hC8]
  have hB : (nu⁻¹) ^ 4 ≤ q := by nlinarith only [hmain, hnu41, hC8]
  refine ⟨?_, ?_⟩
  · rw [← hq4]; exact pow_le_pow_left₀ (by positivity) hA 4
  · rw [← hq4, show (nu⁻¹) ^ 16 = ((nu⁻¹) ^ 4) ^ 4 by ring]
    exact pow_le_pow_left₀ (by positivity) hB 4

/-- The tail `n^{-3000}` is absorbed by `σ^{-2}` once `σ ≤ Ce m²` and `m` is large. -/
theorem tail_absorbed {Ce m σ : ℝ} {n : ℕ} (hCe : 1 ≤ Ce) (hm16 : 16 ≤ m) (hCem : Ce ≤ m)
    (hσ0 : 0 < σ) (hσ : σ ≤ Ce * m * m) (hn : m ≤ 2 * (n : ℝ)) :
    (n : ℝ) ^ (-(3000 : ℝ)) ≤ σ ^ (-(2 : ℝ)) := by
  have hm0 : 0 < m := by linarith only [hm16]
  have hn0 : 0 < (n : ℝ) := by linarith only [hn, hm0]
  have e1 : σ ^ (-(2 : ℝ)) = (σ ^ 2)⁻¹ := by
    rw [show (-(2 : ℝ)) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hσ0.le, Real.rpow_natCast]
  have e2 : (n : ℝ) ^ (-(3000 : ℝ)) = ((n : ℝ) ^ 3000)⁻¹ := by
    rw [show (-(3000 : ℝ)) = -((3000 : ℕ) : ℝ) by norm_num, Real.rpow_neg hn0.le,
      Real.rpow_natCast]
  rw [e1, e2]
  apply inv_anti₀ (by positivity)
  have hbig : (2 : ℝ) ^ 3000 ≤ m ^ 2994 :=
    calc (2 : ℝ) ^ 3000 ≤ 2 ^ (4 * 2994) := pow_le_pow_right₀ (by norm_num) (by norm_num)
      _ = 16 ^ 2994 := by rw [pow_mul]; norm_num
      _ ≤ m ^ 2994 := pow_le_pow_left₀ (by norm_num) hm16 _
  have hσ2 : σ ^ 2 ≤ Ce ^ 2 * m ^ 4 := by
    have := pow_le_pow_left₀ hσ0.le hσ 2
    calc σ ^ 2 ≤ (Ce * m * m) ^ 2 := this
      _ = Ce ^ 2 * m ^ 4 := by ring
  have hCe2 : Ce ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ (by linarith only [hCe]) hCem 2
  have h2n : (m / 2) ^ 3000 ≤ (n : ℝ) ^ 3000 :=
    pow_le_pow_left₀ (by positivity) (by linarith only [hn]) 3000
  have h3 : σ ^ 2 ≤ (m / 2) ^ 3000 := by
    rw [div_pow, le_div_iff₀ (by positivity)]
    calc σ ^ 2 * 2 ^ 3000 ≤ (m ^ 2 * m ^ 4) * m ^ 2994 := by
          apply mul_le_mul (le_trans hσ2 (by
            calc Ce ^ 2 * m ^ 4 ≤ m ^ 2 * m ^ 4 :=
                  mul_le_mul_of_nonneg_right hCe2 (by positivity))) hbig (by positivity)
              (by positivity)
      _ = m ^ 3000 := by ring
  exact le_trans h3 h2n

/-- **`e.ass.valid.applied`**: `p.homog.below` at the scales `(L, m, α, M) = (m - h, n, 3/4, 401)`
of Section 5, with the final comparison `C shom_{m-h}^{-2} log²(ν⁻¹ m) ≤ C m^{-3/4}`. -/
theorem homogBelow_at_scales (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C →
      ∀ cStar nu K : ℝ, 0 < nu → nu ≤ 1 →
      ∀ (P : MeasureTheory.ProbabilityMeasure (ShellSeq d))
        (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P),
        ShellLawJ1Restriction d P → ShellLawJ4 d P → ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
      ∀ m h n : ℕ, 1 ≤ h → 400 * h ≤ m →
        2 * lNaught C C (3 / 4) cStar nu K ≤ (m : ℝ) →
        n = ⌊(m : ℝ) - h - 100 * Real.logb 3 (nu⁻¹ * m)⌋₊ →
        |(sigmaBarInfinite nu (m - h) P)⁻¹ * sigmaBarSeq nu (m - h) P n - 1| +
            |sigmaBarInfinite nu (m - h) P * sigmaBarStarInvSeq nu (m - h) P n - 1| ≤
          C * (sigmaBarInfinite nu (m - h) P) ^ (-(2 : ℝ)) * Real.log (nu⁻¹ * (m : ℝ)) ^ (2 : ℝ) ∧
        C * (sigmaBarInfinite nu (m - h) P) ^ (-(2 : ℝ)) * Real.log (nu⁻¹ * (m : ℝ)) ^ (2 : ℝ) ≤
          C * (m : ℝ) ^ (-(3 / 4 : ℝ)) := by
  obtain ⟨Chb, hChb1, Hhb⟩ := SuperdiffusionCLT.Frozen.Section4.homogenization_below_cutoff d hd
  obtain ⟨Cag, hCag1, Hag⟩ := eLVsLnaughtAgain d hd
  obtain ⟨Cml, hCml, Hml⟩ := m_large_of_lNaught
  obtain ⟨Cge, -, Hge⟩ := SuperdiffusionCLT.Section4.LNaught.lNaught_ge
  set Ce : ℝ := 1 + 2 * cutoffEnvelopeConst d with hCe
  have hCe1 : 1 ≤ Ce := by
    have := one_le_cutoffEnvelopeConst d; rw [hCe]; linarith only [this]
  refine ⟨max (max Cag Cml) (max Cge (max (401 * Chb) (max (Chb * (102 + Chb)) (16 * Ce + 1000)))),
    le_trans hCag1 (le_trans (le_max_left _ _) (le_max_left _ _)), ?_⟩
  intro C hC cStar nu K hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 m h n hh h400 hm hn
  have hC1 : Cag ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hC
  have hC2 : Cml ≤ C := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hC
  have hCg : Cge ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC
  have hC3 : 401 * Chb ≤ C :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hC
  have hC4 : Chb * (102 + Chb) ≤ C :=
    le_trans (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _))
      (le_max_right _ _)) hC
  have hC5 : 16 * Ce + 1000 ≤ C :=
    le_trans (le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _))
      (le_max_right _ _)) hC
  have hcStar := hJ5.cStar_pos
  have hcStar2 := hJ5.cStar_le_two
  have hK := hJ5.K_pos.le
  have hC1000 : 1000 ≤ C := by linarith only [hC5, hCe1]
  have hCpos : 0 < C := by linarith only [hC1000]
  have hChb0 : 0 < Chb := by linarith only [hChb1]
  have h8 := Hge C hCg C (by linarith only [hC1000]) (3 / 4) (by norm_num) (by norm_num) cStar
    hcStar hcStar2 nu hnu hnu1 K hK
  have hmbig := Hml C hC2 cStar hcStar hcStar2 nu hnu hnu1 K hK m (by linarith only [hm, h8])
  obtain ⟨hm4, hnu16⟩ := hmbig
  have hC8 : (125 : ℝ) ≤ C / 8 := by linarith only [hC1000]
  have hmR : (1000000 : ℝ) ≤ m := by
    have : (125 : ℝ) ^ 4 ≤ (C / 8) ^ 4 := pow_le_pow_left₀ (by norm_num) hC8 4
    norm_num at this
    linarith only [this, hm4]
  have hm0 : (0 : ℝ) < m := by linarith only [hmR]
  have hinv1 : 1 ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
  have hinvm : nu⁻¹ ≤ (m : ℝ) := le_trans (le_self_pow₀ hinv1 (by norm_num)) hnu16
  have hnu2 : nu⁻¹ ^ 2 ≤ (m : ℝ) :=
    le_trans (pow_le_pow_right₀ hinv1 (by norm_num)) hnu16
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have h400r : 400 * (h : ℝ) ≤ m := by exact_mod_cast h400
  -- the logarithm `Q = log (ν⁻¹ m)`
  set Q : ℝ := Real.log (nu⁻¹ * (m : ℝ)) with hQdef
  have hQsplit : Q = Real.log nu⁻¹ + Real.log m := by
    rw [hQdef, Real.log_mul (by positivity) hm0.ne']
  have hlognu0 : 0 ≤ Real.log nu⁻¹ := Real.log_nonneg hinv1
  have hlognu1 : Real.log nu⁻¹ ≤ Real.log m := Real.log_le_log (by positivity) hinvm
  have hQ1 : Real.log m ≤ Q := by linarith only [hQsplit, hlognu0]
  have hQ2 : Q ≤ 2 * Real.log m := by linarith only [hQsplit, hlognu1]
  have hlogm4 := four_le_log_of_large (show (55 : ℝ) ≤ m by linarith only [hmR])
  have hQ0 : 0 ≤ Q := by linarith only [hQ1, hlogm4]
  have hQge1 : 1 ≤ Q := by linarith only [hQ1, hlogm4]
  have hnr : (m : ℝ) - h - 100 * (Q / Real.log 3) < n + 1 := by
    have := Nat.lt_floor_add_one ((m : ℝ) - h - 100 * Real.logb 3 (nu⁻¹ * m))
    rw [← hn] at this
    exact this
  have hmnr : (m : ℝ) ≤ 2 * n := scale_half hmR h400r hQ2 hQ0 hnr
  have hmn : m ≤ 2 * n := by exact_mod_cast hmnr
  have hag := Hag C hC1 cStar nu hnu hnu1 K P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 m h n hh h400 hm hnu2 hn hmn
  have hσlow := hag.2
  have hhm : h ≤ m := by omega
  have hLr : (((m - h : ℕ)) : ℝ) = m - h := by rw [Nat.cast_sub hhm]
  -- the anchor
  have hlNL : lNaught Chb (Chb * 401) (3 / 4) cStar nu K ≤ (((m - h : ℕ)) : ℝ) := by
    have hmono := SuperdiffusionCLT.Section4.LNaught.lNaught_mono_both (C := Chb) (C' := C)
      (M := Chb * 401) (M' := C) (alpha := 3 / 4) (cStar := cStar) (nu := nu) (K := K)
      hChb0.le (by linarith only [hC3, hChb0]) (by positivity) (by linarith only [hC3])
      hK hcStar hnu (by norm_num)
    rw [hLr]
    linarith only [hmono, hm, h400r, hh1]
  have hsc := scale_cond (D := Chb) hmR h400r hh1 hQ1 hQ2 hChb0.le hnr
  have hanc := Hhb nu cStar K hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 (3 / 4) 401 (by norm_num)
    (by norm_num) (by norm_num) (m - h) n hlNL (by rw [hLr]; exact hsc.1)
  rw [hLr] at hanc
  set σ := sigmaBarInfinite nu (m - h) P with hσdef
  have hT0 : 0 < (m : ℝ) ^ (3 / 8 : ℝ) * Real.log m ^ (3 / 2 : ℝ) := by
    have : 0 < Real.log (m : ℝ) := by linarith only [hlogm4]
    positivity
  have hσ0 : 0 < σ := lt_of_lt_of_le hT0 hσlow
  have hcrude := sigmaBarInfinite_crude d hnu hnu1 (m - h) hPrefix hJ2 hJ3 hJ4
  have hσm : σ ≤ Ce * m * m := by
    have h1 : max 1 (((m - h : ℕ)) : ℝ) ≤ m := by
      refine max_le (by linarith only [hmR]) ?_
      rw [hLr]; linarith only [hh1]
    calc σ ≤ Ce * nu⁻¹ * max 1 (((m - h : ℕ)) : ℝ) := hcrude
      _ ≤ Ce * m * m := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hinvm (by linarith only [hCe1])) h1
          (by positivity) (by positivity)
  have hCem : Ce ≤ m := by
    have : (C / 8) ≤ (C / 8) ^ 4 := le_self_pow₀ (by linarith only [hC8]) (by norm_num)
    linarith only [this, hm4, hC5, hC8]
  have htail := tail_absorbed hCe1 (by linarith only [hmR]) hCem hσ0 hσm hmnr
  have hS0 : 0 < σ ^ (-(2 : ℝ)) := Real.rpow_pos_of_pos hσ0 _
  have hQ2' : 1 ≤ Q ^ (2 : ℝ) := Real.one_le_rpow hQge1 (by norm_num)
  have hmax : max 0 ((m - h : ℝ) - n + Chb * Real.log (m - h : ℝ) ^ (2 : ℝ)) ≤
      (101 + Chb) * Q ^ (2 : ℝ) :=
    max_le (by positivity) hsc.2
  have hS : |σ⁻¹ * sigmaBarSeq nu (m - h) P n - 1| +
      |σ * sigmaBarStarInvSeq nu (m - h) P n - 1| ≤
      C * σ ^ (-(2 : ℝ)) * Q ^ (2 : ℝ) := by
    refine le_trans hanc ?_
    have h1 : Chb * σ ^ (-(2 : ℝ)) * max 0 ((m - h : ℝ) - n + Chb * Real.log (m - h : ℝ) ^ (2 : ℝ)) ≤
        Chb * σ ^ (-(2 : ℝ)) * ((101 + Chb) * Q ^ (2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hmax (by positivity)
    have h2 : Chb * (n : ℝ) ^ (-(3000 : ℝ)) ≤ Chb * (σ ^ (-(2 : ℝ)) * Q ^ (2 : ℝ)) :=
      mul_le_mul_of_nonneg_left (le_trans htail (by nlinarith only [hS0, hQ2'])) hChb0.le
    have h3 : Chb * (102 + Chb) * (σ ^ (-(2 : ℝ)) * Q ^ (2 : ℝ)) ≤
        C * (σ ^ (-(2 : ℝ)) * Q ^ (2 : ℝ)) :=
      mul_le_mul_of_nonneg_right hC4 (by positivity)
    nlinarith only [h1, h2, h3]
  refine ⟨hS, ?_⟩
  have hfin := sigma_inv_sq_mul_le (show (55 : ℝ) ≤ m by linarith only [hmR]) hQ2 hQ0 hσlow
  calc C * σ ^ (-(2 : ℝ)) * Q ^ (2 : ℝ) = C * (σ ^ (-(2 : ℝ)) * Q ^ (2 : ℝ)) := by ring
    _ ≤ C * (m : ℝ) ^ (-(3 / 4 : ℝ)) := mul_le_mul_of_nonneg_left hfin hCpos.le

/-- Satisfiability of the scale hypotheses of `homogBelow_at_scales` (any constants, `h = 1`). -/
theorem homogBelow_at_scales_scale_witness (C cStar K nu : ℝ) (hnu : 0 < nu) (hnu1 : nu ≤ 1) :
    ∃ m h n : ℕ, 1 ≤ h ∧ 400 * h ≤ m ∧ 2 * lNaught C C (3 / 4) cStar nu K ≤ (m : ℝ) ∧
      n = ⌊(m : ℝ) - h - 100 * Real.logb 3 (nu⁻¹ * m)⌋₊ := by
  obtain ⟨m, h, n, h1, h2, h3, -, h5, -⟩ := eLVsLnaughtAgain_scale_witness C cStar K nu hnu hnu1
  exact ⟨m, h, n, h1, h2, h3, h5⟩

end SuperdiffusionCLT.Section5
