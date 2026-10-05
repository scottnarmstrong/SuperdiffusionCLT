/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Corollary.UpperRatioD
public import SuperdiffusionCLT.Section5.Thresholds.OneStepFromCorollaries

/-!
# `cor.upper.ratio`

The upper one-sided ratio bound `shom_m shom_{m-h}^{-1} ≤ 1 + (c⋆ (log 3) h + C (log² m + K)) shom_{m-h}^{-2}
+ C shom_{m-h}^{-4} h²`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization MeasureTheory Filter Topology
open SuperdiffusionCLT.Frozen.Assumptions SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section3.ResponseFields
open scoped ENNReal

/-- **`cor.upper.ratio`.** -/
theorem upper_ratio (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C₀ C : ℝ, 1 ≤ C₀ ∧ 1 ≤ C ∧
      ∀ (nu cStar K : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
          (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
          (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
          (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
          ∀ m h : ℕ, 1 ≤ h → 400 * h ≤ m →
            2 * SuperdiffusionCLT.Frozen.Section4.lNaught C₀ C₀ (3 / 4) cStar nu K ≤ (m : ℝ) →
            SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P *
                (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu (m - h) P)⁻¹ ≤
              1 + (cStar * Real.log 3 * (h : ℝ) + C * (Real.log (m : ℝ) ^ (2 : ℝ) + K)) *
                  (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu (m - h) P) ^
                    (-(2 : ℝ)) +
                C * (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu (m - h) P) ^
                  (-(4 : ℝ)) * (h : ℝ) ^ (2 : ℝ) := by
  obtain ⟨Cp0, Cp, hCp0, hCp, Hp⟩ := principal_term d hd
  obtain ⟨Cl, hCl, Hl⟩ := cellError_majorant d hd
  obtain ⟨Csf, hCsf, Hsf⟩ := pa_scale_facts
  obtain ⟨Cag, hCag, Hag⟩ := eLVsLnaughtAgain d hd
  have hCc1 : 1 ≤ 1 + 2 * cutoffEnvelopeConst d := by
    have := one_le_cutoffEnvelopeConst d
    linarith only [this]
  set Cc : ℝ := 1 + 2 * cutoffEnvelopeConst d with hCc
  set C₀ : ℝ := max (max Cp0 Cl) (max Csf Cag) with hC₀
  set R0 : ℝ := (Cp + Cl) * Cc ^ 2 with hR0
  have hR00 : 0 ≤ R0 := by positivity
  refine ⟨C₀, 13 * Cp + R0 + 1, ?_, ?_, ?_⟩
  · exact le_trans (le_trans hCp0 (le_max_left _ _)) (le_max_left _ _)
  · linarith only [hCp, hR00]
  intro nu cStar K hnu hnu1 P hPre hJ2 hJ3 hJ1 hJ4 hJ5 m h hh h400 hm
  have hcStar := hJ5.cStar_pos
  have hcStar2 := hJ5.cStar_le_two
  have hK0 := hJ5.K_pos.le
  have hσ0 : 0 < sigmaBarInfinite nu (m - h) P :=
    sigmaBarInfinite_pos hnu (m - h) hPre hJ2 hJ3 hJ4
  have hCpC : Cp0 ≤ C₀ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hClC : Cl ≤ C₀ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCsC : Csf ≤ C₀ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCaC : Cag ≤ C₀ := le_trans (le_max_right _ _) (le_max_right _ _)
  have hmP : 2 * SuperdiffusionCLT.Frozen.Section4.lNaught Cp0 Cp0 (3 / 4) cStar nu K ≤ (m : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_left (upperRatio_lNaught_mono (by linarith only [hCp0]) hCpC hK0
      hcStar hnu) (by norm_num)) hm
  have hmL : 2 * SuperdiffusionCLT.Frozen.Section4.lNaught Cl Cl (3 / 4) cStar nu K ≤ (m : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_left (upperRatio_lNaught_mono (by linarith only [hCl]) hClC hK0
      hcStar hnu) (by norm_num)) hm
  set n : ℕ := ⌊(m : ℝ) - h - 100 * (Real.log (nu⁻¹ * m) / Real.log 3)⌋₊ with hn
  obtain ⟨hmR, hinvm, hnu2, hmn, hnmh⟩ := Hsf C₀ hCsC cStar hcStar hcStar2 nu hnu hnu1 K hK0 m h n
    hh h400 hm (by rw [hn, Real.logb]) 
  have hag := (Hag C₀ hCaC cStar nu hnu hnu1 K P hPre hJ2 hJ3 hJ1 hJ4 hJ5 m h n hh h400 hm hnu2
    hn hmn).2
  obtain ⟨e', he', wN, hwN⟩ := exists_neumann_input_data d hd nu P m h
  have he'1 : vecNormSq e' ≤ 1 := he'.le
  set σ : ℝ := sigmaBarInfinite nu (m - h) P with hσ
  set Zs : ℕ → ℝ≥0∞ := fun Kc => subcubeAvg Kc n (fun Q => ∫⁻ omega, ENNReal.ofReal
    (blockLenSq (ahomSqrtApply nu (m - h) P (principalPhat m h Q omega
      (blockSlope nu (m - h) P Q (0 : Vec d) e'
        (0 : H10Function (openCubeSet (originCube d (Kc : ℤ)))).toH1Function.grad
        (fun y => (wN Kc omega).toH1Function.grad y + hshellFlux nu P m h omega e' y)))))
    ∂P.toMeasure) with hZs
  have hZ : limsup Zs atTop ≤ ENNReal.ofReal (1 + cStar * Real.log 3 * (h : ℝ) * σ ^ (-(2 : ℝ)) +
      K * σ ^ (-(2 : ℝ))) := by
    have := neumann_input d hd nu hnu hnu1 P hPre hJ2 hJ3 hJ1 hJ4 cStar K hJ5 m h hh h400 n e' he'
      wN hwN
    refine le_trans (le_of_eq ?_) this
    refine congrArg (fun F => limsup F atTop) (funext fun Kc => ?_)
    refine congrArg (subcubeAvg Kc n) (funext fun Q => ?_)
    refine lintegral_congr fun omega => ?_
    rw [upperRatio_phat_eq]
  have hper : ∀ Kc : ℕ, 100 * m ≤ Kc →
      ENNReal.ofReal (sigmaBarInfinite nu m P * σ⁻¹) ≤
        ENNReal.ofReal (1 + Cp * σ ^ (-(2 : ℝ)) * Real.log (nu⁻¹ * (m : ℝ)) ^ (2 : ℝ)) * Zs Kc +
          (ENNReal.ofReal (Cp * (m : ℝ) ^ (-(10 : ℝ))) +
            ENNReal.ofReal (Cl * (m : ℝ) ^ (-(50 : ℝ)))) := by
    intro Kc h100
    have hnK : n ≤ Kc := by omega
    have hD : ∀ omega : ShellSeq d, IsCubeDirichletResponse (originCube d (Kc : ℤ))
        (hshellFlux nu P m h omega (0 : Vec d)) (0 : H10Function (openCubeSet (originCube d (Kc : ℤ)))) :=
      fun omega => upperRatio_dirichlet_zero nu P m h Kc omega
    have hX := Hp nu cStar K hnu hnu1 P hPre hJ2 hJ3 hJ1 hJ4 hJ5 m h Kc hh h400 h100 hmP
      (0 : Vec d) e' (by simp [vecNormSq, vecDot]) he'1 n hn (fun _ => 0) (wN Kc) hD (hwN Kc h100)
    obtain ⟨B, hBm, hBp, hBavg⟩ := Hl nu cStar K hnu hnu1 P hPre hJ2 hJ3 hJ1 hJ4 hJ5 m h Kc hh h400
      h100 hmL (0 : Vec d) e' (by simp [vecNormSq, vecDot]) he'1 n hn (fun _ => 0) (wN Kc) hD
      (hwN Kc h100)
    have key := upperRatio_perKc hnu hPre hJ2 hJ3 hJ4 m h Kc n hnK e' (fun _ => 0) (wN Kc) hD
      (hwN Kc h100) B hBm hBp _ _ hX hBavg
    have hv : vecNormSq ((σ ^ (-(1 : ℝ) / 2)) • e') = σ⁻¹ := by
      rw [upperRatio_vecNormSq_smul, he', mul_one, rpow_neg_half_sq hσ0]
    rw [hv] at key
    have hle : sigmaBarInfinite nu m P ≤ sigmaBarSeq nu m P Kc :=
      le_trans (sigmaBarInfinite_le_sigmaBarUpperLimit hnu m hPre hJ2 hJ3 hJ4)
        (sigmaBarUpperLimit_le hnu m hPre hJ2 hJ3 hJ4 Kc)
    refine (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hle (inv_nonneg.2 hσ0.le))).trans
      (key.trans (le_of_eq ?_))
    rw [add_assoc]
  have hm0 : (0 : ℝ) < m := by linarith only [hmR]
  have hlog4 := four_le_log_of_large (show (55 : ℝ) ≤ m by linarith only [hmR])
  have hℓ1 : 1 ≤ Real.log (m : ℝ) := by linarith only [hlog4]
  have hinv1 : 1 ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
  have hΛ0 : 0 ≤ Real.log (nu⁻¹ * (m : ℝ)) :=
    Real.log_nonneg (by nlinarith only [hinv1, hmR])
  have hΛ2 : Real.log (nu⁻¹ * (m : ℝ)) ≤ 2 * Real.log (m : ℝ) := log_inv_mul_le hnu hnu1 hinvm
  have ha0 : 0 ≤ 1 + Cp * σ ^ (-(2 : ℝ)) * Real.log (nu⁻¹ * (m : ℝ)) ^ (2 : ℝ) :=
    add_nonneg zero_le_one (mul_nonneg (mul_nonneg (by linarith only [hCp])
      (Real.rpow_nonneg hσ0.le _)) (Real.rpow_nonneg hΛ0 _))
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hl32 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
    linarith only [this]
  have hY0 : 0 ≤ 1 + cStar * Real.log 3 * (h : ℝ) * σ ^ (-(2 : ℝ)) + K * σ ^ (-(2 : ℝ)) :=
    add_nonneg (add_nonneg zero_le_one (mul_nonneg (mul_nonneg (mul_nonneg hcStar.le hl3.le)
      (Nat.cast_nonneg h)) (Real.rpow_nonneg hσ0.le _))) (mul_nonneg hK0 (Real.rpow_nonneg hσ0.le _))
  have hb1 : 0 ≤ Cp * (m : ℝ) ^ (-(10 : ℝ)) :=
    mul_nonneg (by linarith only [hCp]) (Real.rpow_nonneg hm0.le _)
  have hb2 : 0 ≤ Cl * (m : ℝ) ^ (-(50 : ℝ)) :=
    mul_nonneg (by linarith only [hCl]) (Real.rpow_nonneg hm0.le _)
  have hlim := upperRatio_limsup (N0 := 100 * m) ENNReal.ofReal_ne_top hper hZ
  have hreal : sigmaBarInfinite nu m P * σ⁻¹ ≤
      (1 + Cp * σ ^ (-(2 : ℝ)) * Real.log (nu⁻¹ * (m : ℝ)) ^ (2 : ℝ)) *
        (1 + cStar * Real.log 3 * (h : ℝ) * σ ^ (-(2 : ℝ)) + K * σ ^ (-(2 : ℝ))) +
        (Cp * (m : ℝ) ^ (-(10 : ℝ)) + Cl * (m : ℝ) ^ (-(50 : ℝ))) := by
    rw [← ENNReal.ofReal_mul ha0, ← ENNReal.ofReal_add hb1 hb2,
      ← ENNReal.ofReal_add (mul_nonneg ha0 hY0) (add_nonneg hb1 hb2)] at hlim
    exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg (mul_nonneg ha0 hY0)
      (add_nonneg hb1 hb2))).1 hlim
  have hσc : σ ≤ Cc * m * m := by
    have h1 := sigmaBarInfinite_crude d hnu hnu1 (m - h) hPre hJ2 hJ3 hJ4
    refine h1.trans ?_
    have h2 : max 1 (((m - h : ℕ) : ℝ)) ≤ m :=
      max_le (by linarith only [hmR]) (by exact_mod_cast Nat.sub_le m h)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hinvm (by linarith only [hCc1])) h2
      (le_max_of_le_left zero_le_one) (by positivity)
  obtain ⟨hu1, hu2⟩ := upperRatio_scale_bounds hmR hσ0 hℓ1 hag hσc hCc1
  have e2 : σ ^ (-(2 : ℝ)) = (σ⁻¹) ^ 2 := by simp
  have e4 : σ ^ (-(4 : ℝ)) = (σ⁻¹) ^ 4 := by simp
  have e10 : (m : ℝ) ^ (-(10 : ℝ)) = ((m : ℝ) ^ 10)⁻¹ := by
    rw [Real.rpow_neg hm0.le, show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have e50 : (m : ℝ) ^ (-(50 : ℝ)) = ((m : ℝ) ^ 50)⁻¹ := by
    rw [Real.rpow_neg hm0.le, show (50 : ℝ) = ((50 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h50 : (((m : ℝ) ^ 50)⁻¹) ≤ ((m : ℝ) ^ 10)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_right₀ (by linarith only [hmR]) (by norm_num))
  have hr : Cp * ((m : ℝ) ^ 10)⁻¹ + Cl * ((m : ℝ) ^ 50)⁻¹ ≤ R0 * ((σ⁻¹) ^ 2 * Real.log (m : ℝ) ^ 2) := by
    have h1 : Cp * ((m : ℝ) ^ 10)⁻¹ + Cl * ((m : ℝ) ^ 50)⁻¹ ≤ (Cp + Cl) * ((m : ℝ) ^ 10)⁻¹ := by
      nlinarith only [mul_le_mul_of_nonneg_left h50 (by linarith only [hCl] : (0 : ℝ) ≤ Cl)]
    refine h1.trans ?_
    rw [hR0, mul_assoc]
    exact mul_le_mul_of_nonneg_left hu2 (by linarith only [hCp, hCl])
  have hgoal := upperRatio_algebra (Cp := Cp) (R0 := R0) (u := σ⁻¹) (Λ := Real.log (nu⁻¹ * (m : ℝ)))
    (ℓ := Real.log (m : ℝ)) (h := (h : ℝ)) (cs := cStar) (L3 := Real.log 3) (K := K)
    (r := Cp * ((m : ℝ) ^ 10)⁻¹ + Cl * ((m : ℝ) ^ 50)⁻¹) hCp hR00 (inv_pos.2 hσ0)
    (by nlinarith only [hΛ0, hΛ2]) (Nat.cast_nonneg h) hcStar.le hcStar2 hl3.le hl32 hK0 hu1 hr
  rw [e2, e10, e50, Real.rpow_two] at hreal
  rw [e2, e4, Real.rpow_two, Real.rpow_two]
  exact hreal.trans hgoal

/-- Satisfiability of the scale hypotheses of `upper_ratio`: for every constants and `0 < ν ≤ 1` there are
`m` and `h` with `1 ≤ h`, `400 h ≤ m` and `2 L₀ ≤ m`. -/
example (C cStar K nu : ℝ) (hnu : 0 < nu) (hnu1 : nu ≤ 1) :
    ∃ m h : ℕ, 1 ≤ h ∧ 400 * h ≤ m ∧
      2 * SuperdiffusionCLT.Frozen.Section4.lNaught C C (3 / 4) cStar nu K ≤ (m : ℝ) := by
  obtain ⟨m, h, n, h1, h2, h3, -⟩ := eLVsLnaughtAgain_scale_witness C cStar K nu hnu hnu1
  exact ⟨m, h, h1, h2, h3⟩

end SuperdiffusionCLT.Section5
