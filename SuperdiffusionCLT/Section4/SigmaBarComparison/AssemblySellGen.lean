/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.SigmaBarComparison.AssemblyEighth
public import SuperdiffusionCLT.Section4.SigmaBarComparison.AssemblyQuant
public import SuperdiffusionCLT.Section4.SigmaBarComparison.AssemblyRatioSmall
public import SuperdiffusionCLT.Section4.SigmaBarComparison.AssemblyThreeFactor
public import SuperdiffusionCLT.Section4.SigmaBarComparison.AssemblyLForced
public import SuperdiffusionCLT.Section4.SigmaBarComparison.ComparisonBound

/-!
# `e.sL.vs.sell`, generalized over the outer constant

Assembles the QUANTITATIVE target `e.sL.vs.sell` (`sigmaBar_cutoff_comparison`'s
first conjunct) from `hHomog` and `hIndep` alone, generalized to `∀ C ≥ C0`
(not one fixed `C`) so a consumer (`sbAsm_main`) can apply it at whatever
outer constant `sbAsm_growth_upper`'s own output forces.

Combines: `sbAsm_hb_eighth` (the numeric `≤ 1/8`, giving `c ≥ 7/8` and the
qualitative ratio `shom_ell^{-2} ≤ (9/4) shom_L^{-2}` via
`sbComp_three_factor_bound`/`sbComp_inv_sq_ratio`), `sbAsm_hb_quant` (the
quantitative pieces), `hIndep` (already quantitative), and
`sbAsmF_three_factor_quant` (the quantitative three-factor combination, using
only `c ≥ 7/8` — not needing the `a`-piece numerically small). The residual
`C_I L^{-99}` term is dominated via `sbAsm_residual_dominate` +
`sbAsm_L_forced_large`. Finally `sbAsm_ratio_small` supplies the `≤ 1/2` half.
-/

@[expose] public section

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section4 (lNaught)

namespace SuperdiffusionCLT.Section4.SigmaBarComparison

noncomputable section

theorem sbAsm_sell_gen (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hHomog : ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu cStar K : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : ProbabilityMeasure (ShellSeq d))
          (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P),
          ShellLawJ1Restriction d P → ShellLawJ4 d P → ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
          ∀ alpha M : ℝ, 0 ≤ alpha → alpha < 1 → 1 ≤ M →
            ∀ L m : ℕ,
              lNaught C (C * M) alpha cStar nu K ≤ (L : ℝ) →
              (L : ℝ) - M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (m : ℝ) →
              |(sigmaBarInfinite nu L P)⁻¹ * sigmaBarSeq nu L P m - 1| +
                  |sigmaBarInfinite nu L P * sigmaBarStarInvSeq nu L P m - 1| ≤
                C * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
                    max 0 ((L : ℝ) - (m : ℝ) + C * Real.log (L : ℝ) ^ (2 : ℝ)) +
                  C * (m : ℝ) ^ (-(3000 : ℝ)))
    (hIndep : ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu cStar K : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : ProbabilityMeasure (ShellSeq d))
          (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P),
          ShellLawJ1Restriction d P → ShellLawJ4 d P → ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
          ∀ alpha M : ℝ, 0 ≤ alpha → alpha < 1 → 1 ≤ M →
            ∀ L ell : ℕ, ell ≤ L →
              lNaught C (C * M) alpha cStar nu K ≤ (ell : ℝ) →
              (L : ℝ) - M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (ell : ℝ) →
              ∃ n : ℕ,
                (|sigmaBarSeq nu L P n * (sigmaBarSeq nu ell P n)⁻¹ - 1| ≤
                    C * M * (L : ℝ) ^ alpha *
                        (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
                        Real.log (L : ℝ) ^ (3 : ℝ) +
                      C * (L : ℝ) ^ (-(99 : ℝ)) ∧
                  C * M * (L : ℝ) ^ alpha *
                        (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
                        Real.log (L : ℝ) ^ (3 : ℝ) +
                      C * (L : ℝ) ^ (-(99 : ℝ)) ≤ (1 : ℝ) / 8) ∧
                (n ≤ ell) ∧
                ((ell : ℝ) - (n : ℝ) ≤ 200 * Real.log (L : ℝ) + 1)) :
    ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ C : ℝ, C0 ≤ C →
      ∀ (nu cStar K : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : ProbabilityMeasure (ShellSeq d))
          (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P),
          ShellLawJ1Restriction d P → ShellLawJ4 d P → ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
          ∀ alpha M : ℝ, 0 ≤ alpha → alpha < 1 → 1 ≤ M →
            ∀ L ell : ℕ, ell ≤ L →
              lNaught C (C * M) alpha cStar nu K ≤ (ell : ℝ) →
              (L : ℝ) - M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (ell : ℝ) →
              |(sigmaBarInfinite nu ell P)⁻¹ * sigmaBarInfinite nu L P - 1| ≤
                  C * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
                    Real.log (L : ℝ) ^ (3 : ℝ) ∧
                C * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
                    Real.log (L : ℝ) ^ (3 : ℝ) ≤ (1 : ℝ) / 2 := by
  obtain ⟨C_HB, hCHB1, hHBbody⟩ := sbAsm_hb_eighth d hd hHomog
  obtain ⟨C_Q, hCQ1, hQbody⟩ := sbAsm_hb_quant d hd hHomog
  obtain ⟨C_I, hCI1, hIndepBody⟩ := hIndep
  obtain ⟨C0RS, hC0RS1, hRSbody⟩ := sbAsm_ratio_small d hd
  obtain ⟨C0LF, hC0LF1, hLFbody⟩ := sbAsm_L_forced_large d
  obtain ⟨Ccrude, hCcrude1, hCrudeBody⟩ := sbAsm_crude_growth_bound d
  have hgcpos : (0 : ℝ) < sbAsmGrowthCoeff := by
    have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hpow_pos : (0 : ℝ) < (Real.log 2) ^ (12 : ℝ) := Real.rpow_pos_of_pos hlog2pos _
    unfold sbAsmGrowthCoeff sbAsmGrowthB; positivity
  set Creq99 : ℝ := (4 * Ccrude ^ 2 * C_I + 3) / sbAsmGrowthCoeff with hCreq99def
  have hCreq99nn : (0 : ℝ) ≤ Creq99 := by
    rw [hCreq99def]
    have hCInn : (0 : ℝ) ≤ C_I := le_trans zero_le_one hCI1
    positivity
  have hgcCreq99 : sbAsmGrowthCoeff * Creq99 = 4 * Ccrude ^ 2 * C_I + 3 := by
    rw [hCreq99def]; field_simp
  set CtotalBound : ℝ := 5 * C_Q + 3 * C_I + 2 with hCtotalBounddef
  set M6 : ℝ := max C0LF (max Creq99 CtotalBound) with hM6def
  set M5 : ℝ := max C0RS M6 with hM5def
  set M4 : ℝ := max C_Q M5 with hM4def
  set M3 : ℝ := max C_I M4 with hM3def
  set M2 : ℝ := max C_HB M3 with hM2def
  set C0 : ℝ := max 1 M2 with hC0def
  have hM6M5 : M6 ≤ M5 := le_max_right _ _
  have hM5M4 : M5 ≤ M4 := le_max_right _ _
  have hM4M3 : M4 ≤ M3 := le_max_right _ _
  have hM3M2 : M3 ≤ M2 := le_max_right _ _
  have hM2C0 : M2 ≤ C0 := le_max_right _ _
  refine ⟨C0, le_max_left _ _, ?_⟩
  intro C hCC0 nu cStar K hnu hnu1 P hPrefix hJ2 hJ3 hJ1V2 hJ4 hJ5 alpha M hα0 hα1 hM L ell hellL
    hLnaught hscale
  have hC1 : (1 : ℝ) ≤ C := le_trans (le_max_left _ _) hCC0
  have hCHB_C : C_HB ≤ C := le_trans (le_max_left _ _) (le_trans hM2C0 hCC0)
  have hCI_C : C_I ≤ C :=
    le_trans (le_max_left _ _) (le_trans hM3M2 (le_trans hM2C0 hCC0))
  have hCQ_C : C_Q ≤ C :=
    le_trans (le_max_left _ _) (le_trans hM4M3 (le_trans hM3M2 (le_trans hM2C0 hCC0)))
  have hC0RS_C : C0RS ≤ C :=
    le_trans (le_max_left _ _)
      (le_trans hM5M4 (le_trans hM4M3 (le_trans hM3M2 (le_trans hM2C0 hCC0))))
  have hC0LF_C : C0LF ≤ C :=
    le_trans (le_max_left _ _)
      (le_trans hM6M5 (le_trans hM5M4 (le_trans hM4M3 (le_trans hM3M2 (le_trans hM2C0 hCC0)))))
  have hCreq99_C : Creq99 ≤ C :=
    le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _)
        (le_trans hM6M5 (le_trans hM5M4 (le_trans hM4M3 (le_trans hM3M2 (le_trans hM2C0 hCC0))))))
  have hCtotalBound_C : CtotalBound ≤ C :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _)
        (le_trans hM6M5 (le_trans hM5M4 (le_trans hM4M3 (le_trans hM3M2 (le_trans hM2C0 hCC0))))))
  have hcStar2 := hJ5.cStar_le_two
  have hcStarpos := hJ5.cStar_pos
  have hKnn := hJ5.K_pos.le
  have hellLR : (ell : ℝ) ≤ (L : ℝ) := by exact_mod_cast hellL
  have hLnaughtAtL : lNaught C (C * M) alpha cStar nu K ≤ (L : ℝ) := le_trans hLnaught hellLR
  -- Threshold bridges to `C_HB`, `C_I`, `C_Q` (each `≤ ell`).
  have hCHB_le : lNaught C_HB (C_HB * M) alpha cStar nu K ≤ (ell : ℝ) :=
    (sbAsm_lNaught_mono_simple (le_trans zero_le_one hCHB1) (le_trans zero_le_one hM) hCHB_C
      hKnn hcStarpos hnu hα1).trans hLnaught
  have hCI_le : lNaught C_I (C_I * M) alpha cStar nu K ≤ (ell : ℝ) :=
    (sbAsm_lNaught_mono_simple (le_trans zero_le_one hCI1) (le_trans zero_le_one hM) hCI_C
      hKnn hcStarpos hnu hα1).trans hLnaught
  have hCQ_le : lNaught C_Q (C_Q * M) alpha cStar nu K ≤ (ell : ℝ) :=
    (sbAsm_lNaught_mono_simple (le_trans zero_le_one hCQ1) (le_trans zero_le_one hM) hCQ_C
      hKnn hcStarpos hnu hα1).trans hLnaught
  obtain ⟨n, ⟨hIRbound, hIR18⟩, hNell, hGap⟩ := hIndepBody nu cStar K hnu hnu1 P hPrefix hJ2 hJ3
    hJ1V2 hJ4 hJ5 alpha M hα0 hα1 hM L ell hellL hCI_le hscale
  have hHBsum := hHBbody nu cStar K hnu hnu1 P hPrefix hJ2 hJ3 hJ1V2 hJ4 hJ5 alpha M hα0 hα1 hM L
    ell hellL hCHB_le hscale n hNell hGap
  obtain ⟨hQL, hQEll⟩ := hQbody nu cStar K hnu hnu1 P hPrefix hJ2 hJ3 hJ1V2 hJ4 hJ5 alpha M hα0 hα1
    hM L ell hellL hCQ_le hscale n hNell hGap
  -- Extract `|a-1| ≤ 1/8`, `|c-1| ≤ 1/8` (hence `c ≥ 7/8`) from `hHBsum`.
  have hc18 : |(sigmaBarInfinite nu L P)⁻¹ * sigmaBarSeq nu L P n - 1| ≤ (1 / 8 : ℝ) := by
    have hOtherNonneg : (0 : ℝ) ≤
        |(sigmaBarInfinite nu ell P)⁻¹ * sigmaBarSeq nu ell P n - 1| := abs_nonneg _
    linarith only [hHBsum, hOtherNonneg]
  have ha18 : |(sigmaBarInfinite nu ell P)⁻¹ * sigmaBarSeq nu ell P n - 1| ≤ (1 / 8 : ℝ) := by
    have hOtherNonneg : (0 : ℝ) ≤
        |(sigmaBarInfinite nu L P)⁻¹ * sigmaBarSeq nu L P n - 1| := abs_nonneg _
    linarith only [hHBsum, hOtherNonneg]
  have hc78 : (7 / 8 : ℝ) ≤ (sigmaBarInfinite nu L P)⁻¹ * sigmaBarSeq nu L P n := by
    have := (abs_le.mp hc18).1; linarith only [this]
  -- The QUALITATIVE ratio `shom_ell^{-2} ≤ (9/4) shom_L^{-2}`.
  have hqual := sbComp_three_factor_bound ha18 hIRbound hc18 (le_refl (1 / 8 : ℝ)) hIR18
  have hSLpos : (0 : ℝ) < sigmaBarInfinite nu L P := sigmaBarInfinite_pos hnu L hPrefix hJ2 hJ3 hJ4
  have hSEpos : (0 : ℝ) < sigmaBarInfinite nu ell P :=
    sigmaBarInfinite_pos hnu ell hPrefix hJ2 hJ3 hJ4
  have hSLnpos : (0 : ℝ) < sigmaBarSeq nu L P n := sigmaBarSeq_pos hnu L hPrefix hJ2 hJ3 hJ4 n
  have hSEnpos : (0 : ℝ) < sigmaBarSeq nu ell P n := sigmaBarSeq_pos hnu ell hPrefix hJ2 hJ3 hJ4 n
  have hidentity :
      (sigmaBarInfinite nu ell P)⁻¹ * sigmaBarSeq nu ell P n *
            (sigmaBarSeq nu L P n * (sigmaBarSeq nu ell P n)⁻¹) *
          ((sigmaBarInfinite nu L P)⁻¹ * sigmaBarSeq nu L P n)⁻¹ =
      (sigmaBarInfinite nu ell P)⁻¹ * sigmaBarInfinite nu L P := by
    field_simp
  rw [hidentity] at hqual
  have hratio_qual : |(sigmaBarInfinite nu ell P)⁻¹ * sigmaBarInfinite nu L P - 1| ≤ (1 / 2 : ℝ) :=
    by linarith only [hqual, hIR18]
  have hle32 : sigmaBarInfinite nu L P ≤ (3 / 2 : ℝ) * sigmaBarInfinite nu ell P := by
    have hab := (abs_le.mp hratio_qual).2
    have h2 : (sigmaBarInfinite nu ell P)⁻¹ * sigmaBarInfinite nu L P ≤ 3 / 2 := by
      linarith only [hab]
    have h3 := mul_le_mul_of_nonneg_left h2 hSEpos.le
    rw [← mul_assoc, mul_inv_cancel₀ hSEpos.ne', one_mul] at h3
    linarith only [h3]
  have hratio_sq : (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) ≤
      (9 / 4 : ℝ) * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) :=
    sbComp_inv_sq_ratio hSEpos hSLpos hle32
  -- `L` forced large, and the `L^{-99}` residual dominated.
  have hLGrowth := hLFbody C hC0LF_C nu cStar K hnu hnu1 P hPrefix hJ2 hJ3 hJ1V2 hJ4 hJ5 alpha M
    hα0 hα1 hM L hLnaughtAtL
  have hnu4le1 : nu ^ (4 : ℝ) ≤ 1 :=
    le_trans (Real.rpow_le_rpow hnu.le hnu1 (by norm_num)) (le_of_eq (Real.one_rpow _))
  have hnu4pos : (0 : ℝ) < nu ^ (4 : ℝ) := Real.rpow_pos_of_pos hnu _
  have hgcC_ge3 : (3 : ℝ) ≤ sbAsmGrowthCoeff * C := by
    have h1 : sbAsmGrowthCoeff * Creq99 ≤ sbAsmGrowthCoeff * C :=
      mul_le_mul_of_nonneg_left hCreq99_C hgcpos.le
    have hCcrudeCI_nn : (0 : ℝ) ≤ 4 * Ccrude ^ 2 * C_I := by
      have hCInn : (0 : ℝ) ≤ C_I := le_trans zero_le_one hCI1
      positivity
    linarith only [h1, hgcCreq99, hCcrudeCI_nn]
  have hL3 : (3 : ℝ) ≤ (L : ℝ) := by
    have hstep : sbAsmGrowthCoeff * C ≤ sbAsmGrowthCoeff * C / nu ^ (4 : ℝ) := by
      rw [le_div_iff₀ hnu4pos]
      exact mul_le_of_le_one_right (by linarith only [hgcC_ge3]) hnu4le1
    linarith only [hgcC_ge3, hstep, hLGrowth]
  have hL3nat : (3 : ℕ) ≤ L := by exact_mod_cast hL3
  have hResid99Big : (1 : ℝ) ^ (99 : ℝ) * 4 * Ccrude ^ 2 * C_I ≤ 1 * (sbAsmGrowthCoeff * C) := by
    rw [Real.one_rpow]
    have hCcrudeCI_nn : (0 : ℝ) ≤ 4 * Ccrude ^ 2 * C_I := by
      have hCInn : (0 : ℝ) ≤ C_I := le_trans zero_le_one hCI1
      positivity
    linarith only [hgcC_ge3, hgcCreq99, hCreq99_C, hgcpos,
      mul_le_mul_of_nonneg_left hCreq99_C hgcpos.le, hCcrudeCI_nn]
  have hResid99 := sbAsm_residual_dominate (d := d) (nu := nu) (alpha := alpha) (M := M)
      (rho := (1 : ℝ)) (p := (99 : ℝ)) (Cres := C_I) (eps := (1 : ℝ)) (T := sbAsmGrowthCoeff * C)
      (Ccrude := Ccrude) (L := L) (t := L)
      hPrefix hJ2 hJ3 hJ4 hnu hnu1 hM hα0 hα1 hL3nat (by norm_num)
      (by linarith only [] : (L : ℝ) ≤ 1 * (L : ℝ)) (by norm_num)
      (le_trans zero_le_one hCI1) (by norm_num)
      hCcrude1 (hCrudeBody nu hnu hnu1 P hPrefix hJ2 hJ3 hJ4 L)
      (by linarith only [hgcC_ge3] : (1 : ℝ) ≤ sbAsmGrowthCoeff * C) hLGrowth hResid99Big
  -- The QUANTITATIVE three-factor combination.
  have hquant := sbAsmF_three_factor_quant hQEll hIRbound hQL hc78 hIR18
  rw [hidentity] at hquant
  -- Convert every piece to `(coefficient) * M * L^α * shom_L^{-2} * log³L`.
  have hMnn : (0 : ℝ) ≤ M := le_trans zero_le_one hM
  have hLRpos : (0 : ℝ) < (L : ℝ) := by linarith only [hL3]
  have hLalphann : (0 : ℝ) ≤ (L : ℝ) ^ alpha := Real.rpow_nonneg hLRpos.le _
  have hlogLpos : (0 : ℝ) < Real.log (L : ℝ) := by
    have hlog3 : (1 : ℝ) < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
      linarith only [Real.exp_one_lt_d9]
    have : (1 : ℝ) < Real.log (L : ℝ) := lt_of_lt_of_le hlog3 (Real.log_le_log (by norm_num) hL3)
    linarith only [this]
  have hlog3Lnn : (0 : ℝ) ≤ Real.log (L : ℝ) ^ (3 : ℝ) := Real.rpow_nonneg hlogLpos.le _
  have hCQnn : (0 : ℝ) ≤ C_Q := le_trans zero_le_one hCQ1
  have hCInn : (0 : ℝ) ≤ C_I := le_trans zero_le_one hCI1
  -- Term 1: `(9/7) ea1 ≤ (81/28) C_Q * M * L^α * shom_L^{-2} * log³L`.
  have hpref1nn : (0 : ℝ) ≤ C_Q * M * (L : ℝ) ^ alpha := by
    have := mul_nonneg hCQnn hMnn; exact mul_nonneg this hLalphann
  have hterm1a : C_Q * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) ≤
      C_Q * M * (L : ℝ) ^ alpha * ((9 / 4 : ℝ) * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ))) :=
    mul_le_mul_of_nonneg_left hratio_sq hpref1nn
  have hterm1 : C_Q * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
      Real.log (L : ℝ) ^ (3 : ℝ) ≤
      (9 / 4 : ℝ) * C_Q * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
        Real.log (L : ℝ) ^ (3 : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hterm1a hlog3Lnn
    have heq : C_Q * M * (L : ℝ) ^ alpha * ((9 / 4 : ℝ) * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ))) *
        Real.log (L : ℝ) ^ (3 : ℝ) =
        (9 / 4 : ℝ) * C_Q * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
          Real.log (L : ℝ) ^ (3 : ℝ) := by ring
    linarith only [h, heq.ge, heq.le]
  -- Term 2a: `(8/7) * (C_I*M*L^α*shom_ell^{-2}*log³L) ≤ (18/7) C_I*M*L^α*shom_L^{-2}*log³L`.
  have hpref2nn : (0 : ℝ) ≤ C_I * M * (L : ℝ) ^ alpha := by
    have := mul_nonneg hCInn hMnn; exact mul_nonneg this hLalphann
  have hterm2a : C_I * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) ≤
      C_I * M * (L : ℝ) ^ alpha * ((9 / 4 : ℝ) * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ))) :=
    mul_le_mul_of_nonneg_left hratio_sq hpref2nn
  have hterm2 : C_I * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
      Real.log (L : ℝ) ^ (3 : ℝ) ≤
      (9 / 4 : ℝ) * C_I * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
        Real.log (L : ℝ) ^ (3 : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hterm2a hlog3Lnn
    have heq : C_I * M * (L : ℝ) ^ alpha * ((9 / 4 : ℝ) * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ))) *
        Real.log (L : ℝ) ^ (3 : ℝ) =
        (9 / 4 : ℝ) * C_I * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
          Real.log (L : ℝ) ^ (3 : ℝ) := by ring
    linarith only [h, heq.ge, heq.le]
  -- Term 2b (`hResid99`) and Term 3 (`hQL`) are already in the right shape.
  -- Combine: `|shom_ell⁻¹ shom_L - 1| ≤ (9/7) ea1 + (8/7) eb + (8/7) ea2`, and
  -- each summand is now bounded by a fixed multiple of `M L^α shom_L^{-2} log³L`.
  have hSLinvnn : (0 : ℝ) ≤ (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) :=
    Real.rpow_nonneg (le_of_lt (sigmaBarInfinite_pos hnu L hPrefix hJ2 hJ3 hJ4)) _
  have hUnitnn : (0 : ℝ) ≤ M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
      Real.log (L : ℝ) ^ (3 : ℝ) := by
    have h1 := mul_nonneg hMnn hLalphann
    have h2 := mul_nonneg h1 hSLinvnn
    exact mul_nonneg h2 hlog3Lnn
  have hfinalBound : |(sigmaBarInfinite nu ell P)⁻¹ * sigmaBarInfinite nu L P - 1| ≤
      CtotalBound * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
        Real.log (L : ℝ) ^ (3 : ℝ) := by
    have hCtotalEq : CtotalBound * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
        Real.log (L : ℝ) ^ (3 : ℝ) =
        (5 : ℝ) * (C_Q * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
              Real.log (L : ℝ) ^ (3 : ℝ)) +
          (3 : ℝ) * (C_I * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
              Real.log (L : ℝ) ^ (3 : ℝ)) +
          (2 : ℝ) * (M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
              Real.log (L : ℝ) ^ (3 : ℝ)) := by
      rw [hCtotalBounddef]; ring
    have hQLnn : (0 : ℝ) ≤ C_Q * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
        Real.log (L : ℝ) ^ (3 : ℝ) := by
      have h1 := mul_nonneg hpref1nn hSLinvnn
      exact mul_nonneg h1 hlog3Lnn
    have hCILnn : (0 : ℝ) ≤ C_I * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
        Real.log (L : ℝ) ^ (3 : ℝ) := by
      have h1 := mul_nonneg hpref2nn hSLinvnn
      exact mul_nonneg h1 hlog3Lnn
    have hspare1 : (81 / 28 : ℝ) * (C_Q * M * (L : ℝ) ^ alpha *
        (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) * Real.log (L : ℝ) ^ (3 : ℝ)) ≤
        5 * (C_Q * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
          Real.log (L : ℝ) ^ (3 : ℝ)) := by
      have : (81 / 28 : ℝ) ≤ 5 := by norm_num
      exact mul_le_mul_of_nonneg_right this hQLnn
    have hspare2 : (18 / 7 : ℝ) * (C_I * M * (L : ℝ) ^ alpha *
        (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) * Real.log (L : ℝ) ^ (3 : ℝ)) ≤
        3 * (C_I * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
          Real.log (L : ℝ) ^ (3 : ℝ)) := by
      have : (18 / 7 : ℝ) ≤ 3 := by norm_num
      exact mul_le_mul_of_nonneg_right this hCILnn
    have hspare3 : (8 / 7 : ℝ) * (M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
        Real.log (L : ℝ) ^ (3 : ℝ)) ≤
        2 * (M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
          Real.log (L : ℝ) ^ (3 : ℝ)) := by
      have : (8 / 7 : ℝ) ≤ 2 := by norm_num
      exact mul_le_mul_of_nonneg_right this hUnitnn
    have hterm1' : (9 / 7 : ℝ) * (C_Q * M * (L : ℝ) ^ alpha *
        (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) * Real.log (L : ℝ) ^ (3 : ℝ)) ≤
        (81 / 28 : ℝ) * (C_Q * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
          Real.log (L : ℝ) ^ (3 : ℝ)) := by
      have h := mul_le_mul_of_nonneg_left hterm1 (by norm_num : (0 : ℝ) ≤ 9 / 7)
      nlinarith only [h]
    have hterm2' : (8 / 7 : ℝ) * (C_I * M * (L : ℝ) ^ alpha *
        (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) * Real.log (L : ℝ) ^ (3 : ℝ) +
        C_I * (L : ℝ) ^ (-(99 : ℝ))) ≤
        (18 / 7 : ℝ) * (C_I * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
          Real.log (L : ℝ) ^ (3 : ℝ)) +
        (8 / 7 : ℝ) * (M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
          Real.log (L : ℝ) ^ (3 : ℝ)) := by
      have h1 := mul_le_mul_of_nonneg_left hterm2 (by norm_num : (0 : ℝ) ≤ 8 / 7)
      have h2 := mul_le_mul_of_nonneg_left hResid99 (by norm_num : (0 : ℝ) ≤ 8 / 7)
      nlinarith only [h1, h2]
    have hterm3' : (8 / 7 : ℝ) * (C_Q * M * (L : ℝ) ^ alpha *
        (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) * Real.log (L : ℝ) ^ (3 : ℝ)) ≤
        (8 / 7 : ℝ) * (C_Q * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
          Real.log (L : ℝ) ^ (3 : ℝ)) := le_refl _
    rw [hCtotalEq]
    have hqfinal : |(sigmaBarInfinite nu ell P)⁻¹ * sigmaBarInfinite nu L P - 1| ≤
        (9 / 7 : ℝ) * (C_Q * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
            Real.log (L : ℝ) ^ (3 : ℝ)) +
          (8 / 7 : ℝ) * (C_I * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
              Real.log (L : ℝ) ^ (3 : ℝ) +
            C_I * (L : ℝ) ^ (-(99 : ℝ))) +
          (8 / 7 : ℝ) * (C_Q * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
              Real.log (L : ℝ) ^ (3 : ℝ)) := hquant
    linarith only [hqfinal, hterm1', hterm2', hspare1, hspare2, hspare3]
  refine ⟨le_trans hfinalBound ?_, hRSbody C hC0RS_C nu cStar K hnu hnu1 P hPrefix hJ2 hJ3 hJ1V2 hJ4
    hJ5 alpha M hα0 hα1 hM L hLnaughtAtL⟩
  have hCtotalBound_le : CtotalBound * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
      Real.log (L : ℝ) ^ (3 : ℝ) ≤
      C * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) * Real.log (L : ℝ) ^ (3 : ℝ) := by
    have heqA : CtotalBound * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
        Real.log (L : ℝ) ^ (3 : ℝ) =
        CtotalBound * (M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
          Real.log (L : ℝ) ^ (3 : ℝ)) := by ring
    have heqB : C * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
        Real.log (L : ℝ) ^ (3 : ℝ) =
        C * (M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
          Real.log (L : ℝ) ^ (3 : ℝ)) := by ring
    rw [heqA, heqB]
    exact mul_le_mul_of_nonneg_right hCtotalBound_C hUnitnn
  exact hCtotalBound_le

end

end SuperdiffusionCLT.Section4.SigmaBarComparison
