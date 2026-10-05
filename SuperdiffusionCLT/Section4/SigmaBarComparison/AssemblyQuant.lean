/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.SigmaBarComparison.AssemblyMain
public import SuperdiffusionCLT.Section4.SigmaBarComparison.Growth

/-!
# The QUANTITATIVE `#homog-below-bound` piece

`sbAsm_hb_eighth` (`AssemblyEighth.lean`) only exposes the NUMERIC `≤ 1/8`
consequence of applying `hHomog` at `(L,n)` and `(ell,n)`. Assembling the
actual quantitative target `e.sL.vs.sell` (`C M L^α shom_L^{-2} log³L`, a
shrinking bound, not a fixed constant) needs the QUANTITATIVE form of the two
individual pieces `|shom_L⁻¹ shom_L(cu_n) - 1|` and `|shom_ell⁻¹ shom_ell(cu_n)
- 1|` instead. This file derives that quantitative form directly, WITHOUT the
`lNaught_sstar_lower` `M`-inflation machinery `sbAsm_hb_eighth` needs (not
needed here: the elementary bound `X - n + C_H log²X ≤ (1+C_H) M_X X^α log³X`
already puts each piece in the right SHAPE), using `sbAsm_residual_dominate`
for the `n^{-3000}` residual instead.
-/

@[expose] public section

open MeasureTheory Homogenization
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section4 (lNaught)
open SuperdiffusionCLT.Section4.LNaught (lNaught_mono_const lNaught_mono_M)

namespace SuperdiffusionCLT.Section4.SigmaBarComparison

noncomputable section

/-- **The quantitative `#homog-below-bound` pieces**, from `hHomog` alone. -/
theorem sbAsm_hb_quant (d : ℕ) [NeZero d] (_hd : 2 ≤ d)
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
                  C * (m : ℝ) ^ (-(3000 : ℝ))) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu cStar K : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : ProbabilityMeasure (ShellSeq d))
          (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P),
          ShellLawJ1Restriction d P → ShellLawJ4 d P → ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
          ∀ alpha M : ℝ, 0 ≤ alpha → alpha < 1 → 1 ≤ M →
            ∀ L ell : ℕ, ell ≤ L →
              lNaught C (C * M) alpha cStar nu K ≤ (ell : ℝ) →
              (L : ℝ) - M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (ell : ℝ) →
              ∀ n : ℕ, n ≤ ell → (ell : ℝ) - (n : ℝ) ≤ 200 * Real.log (L : ℝ) + 1 →
                |(sigmaBarInfinite nu L P)⁻¹ * sigmaBarSeq nu L P n - 1| ≤
                    C * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
                      Real.log (L : ℝ) ^ (3 : ℝ) ∧
                  |(sigmaBarInfinite nu ell P)⁻¹ * sigmaBarSeq nu ell P n - 1| ≤
                    C * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
                      Real.log (L : ℝ) ^ (3 : ℝ) := by
  obtain ⟨C_H, hCH1, hHomogBody⟩ := hHomog
  obtain ⟨Ccrude, hCcrude1, hCrudeBody⟩ := sbAsm_crude_growth_bound d
  obtain ⟨CA0, hCA01, hAbsorbs⟩ := SuperdiffusionCLT.Section4.LNaught.lNaught_absorbs
  have hCHpos : (0 : ℝ) < C_H := by
    clear * - C_H hCH1
    exact lt_of_lt_of_le one_pos hCH1
  set MXell : ℝ := C_H * sbAsmGrowthB + 3216 with hMXelldef
  have hsbAsmGrowthBpos : (0 : ℝ) < sbAsmGrowthB := by
    have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hpow_pos : (0 : ℝ) < (Real.log 2) ^ (12 : ℝ) := Real.rpow_pos_of_pos hlog2pos _
    unfold sbAsmGrowthB; positivity
  have hMXell1 : (1 : ℝ) ≤ MXell := by
    have h0 : (0 : ℝ) ≤ C_H * sbAsmGrowthB := by positivity
    rw [hMXelldef]; linarith only [h0]
  set growthCoeff : ℝ := 64 / sbAsmGrowthB with hgrowthCoeffdef
  have hgrowthCoeffpos : (0 : ℝ) < growthCoeff := by rw [hgrowthCoeffdef]; positivity
  set logfacL : ℝ := (1 + Real.log (202 : ℝ) / Real.log 2) ^ (12 : ℝ) with hlogfacLdef
  have hlogfacLnn : (0 : ℝ) ≤ logfacL := by
    rw [hlogfacLdef]
    have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hlog202nn : (0 : ℝ) ≤ Real.log (202 : ℝ) := Real.log_nonneg (by norm_num)
    positivity
  clear hlogfacLdef
  set Creq : ℝ := (4 : ℝ) ^ (3000 : ℝ) * 4 * Ccrude ^ 2 * C_H / growthCoeff with hCreqdef
  have hCreqnn : (0 : ℝ) ≤ Creq := by
    rw [hCreqdef]; positivity
  set CoefL : ℝ := 202 * C_H * (1 + C_H) + 1 with hCoefLdef
  set CoefEll : ℝ := C_H * (1 + C_H) * MXell + 1 with hCoefElldef
  set M8 : ℝ := max CoefEll sbAsmGrowthB with hM8def
  clear hM8def
  set M7 : ℝ := max CoefL M8 with hM7def
  clear hM7def
  set M6 : ℝ := max Creq M7 with hM6def
  clear hM6def
  set M5 : ℝ := max (CA0 * 3216) M6 with hM5def
  clear hM5def
  set M4 : ℝ := max CA0 M5 with hM4def
  clear hM4def
  set M3 : ℝ := max (C_H * MXell) M4 with hM3def
  clear hM3def
  set M2 : ℝ := max (C_H * 202 * logfacL) M3 with hM2def
  clear hM2def
  set M1 : ℝ := max C_H M2 with hM1def
  clear hM1def
  set C : ℝ := max 1 M1 with hCdef
  clear hCdef
  have hM8M7 : M8 ≤ M7 := by
    clear * - M8 M7
    exact le_max_right _ _
  have hM7M6 : M7 ≤ M6 := by
    clear * - M7 M6
    exact le_max_right _ _
  have hM6M5 : M6 ≤ M5 := by
    clear * - M6 M5
    exact le_max_right _ _
  have hM5M4 : M5 ≤ M4 := by
    clear * - M5 M4
    exact le_max_right _ _
  have hM4M3 : M4 ≤ M3 := by
    clear * - M4 M3
    exact le_max_right _ _
  have hM3M2 : M3 ≤ M2 := by
    clear * - M3 M2
    exact le_max_right _ _
  have hM2M1 : M2 ≤ M1 := by
    clear * - M2 M1
    exact le_max_right _ _
  have hM1C : M1 ≤ C := by
    clear * - M1 C
    exact le_max_right _ _
  refine ⟨C, le_max_left _ _, ?_⟩
  intro nu cStar K hnu hnu1 P hPrefix hJ2 hJ3 hJ1V2 hJ4 hJ5 alpha M hα0 hα1 hM L ell hellL
    hLnaught hscale n hNell hGap
  clear hNell
  have hC1 : (1 : ℝ) ≤ C := by
    clear * - C
    exact le_max_left _ _
  have hCpos : (0 : ℝ) < C := by
    clear * - C hC1
    exact lt_of_lt_of_le one_pos hC1
  have hCH_C : C_H ≤ C := by
    clear * - C_H C hM1C
    exact le_trans (le_max_left _ _) hM1C
  have hCHK'Llogfac_C : C_H * 202 * logfacL ≤ C := by
    clear * - C_H logfacL C hM2M1 hM1C
    exact le_trans (le_max_left _ _) (le_trans hM2M1 hM1C)
  have hCHMXell_C : C_H * MXell ≤ C := by
    clear * - C_H MXell C hM3M2 hM2M1 hM1C
    exact le_trans (le_max_left _ _) (le_trans hM3M2 (le_trans hM2M1 hM1C))
  have hCA0_C : CA0 ≤ C := by
    clear * - CA0 C hM4M3 hM3M2 hM2M1 hM1C
    exact le_trans (le_max_left _ _) (le_trans hM4M3 (le_trans hM3M2 (le_trans hM2M1 hM1C)))
  have hCA03216_C : CA0 * 3216 ≤ C := by
    clear * - CA0 C hM5M4 hM4M3 hM3M2 hM2M1 hM1C
    exact le_trans (le_max_left _ _)
        (le_trans hM5M4 (le_trans hM4M3 (le_trans hM3M2 (le_trans hM2M1 hM1C))))
  have hCreq_C : Creq ≤ C := by
    clear * - Creq C hM6M5 hM5M4 hM4M3 hM3M2 hM2M1 hM1C
    exact le_trans (le_max_left _ _)
        (le_trans hM6M5 (le_trans hM5M4 (le_trans hM4M3 (le_trans hM3M2 (le_trans hM2M1 hM1C)))))
  have hCoefL_C : CoefL ≤ C := by
    clear * - CoefL C hM7M6 hM6M5 hM5M4 hM4M3 hM3M2 hM2M1 hM1C
    exact le_trans (le_max_left _ _)
        (le_trans hM7M6
          (le_trans hM6M5 (le_trans hM5M4 (le_trans hM4M3 (le_trans hM3M2 (le_trans hM2M1 hM1C))))))
  have hCoefEll_C : CoefEll ≤ C := by
    clear * - CoefEll C hM8M7 hM7M6 hM6M5 hM5M4 hM4M3 hM3M2 hM2M1 hM1C
    exact le_trans (le_max_left _ _)
        (le_trans hM8M7 (le_trans hM7M6
          (le_trans hM6M5 (le_trans hM5M4 (le_trans hM4M3 (le_trans hM3M2 (le_trans hM2M1 hM1C)))))))
  have hsbAsmGrowthB_C : sbAsmGrowthB ≤ C := by
    clear * - C hM8M7 hM7M6 hM6M5 hM5M4 hM4M3 hM3M2 hM2M1 hM1C
    exact le_trans (le_max_right _ _)
        (le_trans hM8M7 (le_trans hM7M6
          (le_trans hM6M5 (le_trans hM5M4 (le_trans hM4M3 (le_trans hM3M2 (le_trans hM2M1 hM1C)))))))
  clear hM1C hM2M1 hM3M2 hM4M3 hM5M4 hM6M5 hM7M6 hM8M7
  have hcStar2 := hJ5.cStar_le_two
  have hcStarpos := hJ5.cStar_pos
  have hKnn := hJ5.K_pos.le
  have hellLR : (ell : ℝ) ≤ (L : ℝ) := by clear * - ell hellL; exact_mod_cast hellL
  have hLnaughtAtL : lNaught C (C * M) alpha cStar nu K ≤ (L : ℝ) := by
    clear * - C nu cStar K alpha M ell hLnaught hellLR
    exact le_trans hLnaught hellLR
    -- `ell ≥ L/2`.
  have hCM1 : (1 : ℝ) ≤ C * M := by
    clear * - C M hM hC1
    exact le_trans hM (le_mul_of_one_le_left (le_trans zero_le_one hM) hC1)
  have hAbsorbAtL := hAbsorbs C hCA0_C (C * M) hCM1 alpha hα0 hα1 cStar hcStarpos hcStar2 nu hnu
    hnu1 K hKnn L hLnaughtAtL
  clear hCM1
  have hML2 : M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (L : ℝ) / 2 := by
    have heq : C * M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) =
        C * (M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) := by ring
    rw [heq] at hAbsorbAtL
    have hMLnn : (0 : ℝ) ≤ M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) := by
      have hL0 : (0 : ℝ) ≤ (L : ℝ) ^ alpha := Real.rpow_nonneg (Nat.cast_nonneg _) _
      have hlog0 : (0 : ℝ) ≤ Real.log (L : ℝ) := Real.log_natCast_nonneg L
      have hlog30 : (0 : ℝ) ≤ Real.log (L : ℝ) ^ (3 : ℝ) := Real.rpow_nonneg hlog0 _
      have hM0 : (0 : ℝ) ≤ M := le_trans zero_le_one hM
      positivity
    nlinarith only [hAbsorbAtL, hC1, hMLnn]
  clear hAbsorbAtL
  have hL2ell : (L : ℝ) ≤ 2 * (ell : ℝ) := by clear * - growthCoeff C nu ell hscale hML2; linarith only [hscale, hML2]
  -- `L` forced large: `growthCoeff * C / nu^4 ≤ L`.
  clear hML2
  have hsbAsmGrowthB1 : (1 : ℝ) ≤ sbAsmGrowthB := by
    have h0 : (0 : ℝ) ≤ 2048 / (Real.log 2) ^ (12 : ℝ) := by positivity
    unfold sbAsmGrowthB; linarith only [h0]
  have hCdivpos : (0 : ℝ) < C / sbAsmGrowthB := by positivity
  have hCdivge1 : (1 : ℝ) ≤ C / sbAsmGrowthB := by
    clear * - hsbAsmGrowthBpos C hsbAsmGrowthB_C
    rw [le_div_iff₀ hsbAsmGrowthBpos]; linarith only [hsbAsmGrowthB_C]
  clear hsbAsmGrowthB_C
  have hCdivM1 : (C / sbAsmGrowthB) * sbAsmGrowthB ≤ C * M := by
    clear * - hsbAsmGrowthBpos C M hM hCpos
    rw [div_mul_cancel₀ C (ne_of_gt hsbAsmGrowthBpos)]
    exact le_mul_of_one_le_right hCpos.le hM
  have hCdiv_le_C : C / sbAsmGrowthB ≤ C := by
    clear * - hsbAsmGrowthBpos C hCpos hsbAsmGrowthB1
    rw [div_le_iff₀ hsbAsmGrowthBpos]
    exact le_mul_of_one_le_right hCpos.le hsbAsmGrowthB1
  clear hsbAsmGrowthB1
  have hCgrowthLe : lNaught (C / sbAsmGrowthB) (C * M) alpha cStar nu K ≤
      lNaught C (C * M) alpha cStar nu K := by
    clear * - C nu cStar K hnu alpha M hα1 hM hCpos hcStarpos hKnn hCdivpos hCdiv_le_C
    exact lNaught_mono_const hCdivpos.le hCdiv_le_C (mul_nonneg hCpos.le (le_trans zero_le_one hM))
        hKnn hcStarpos hnu hα1
  clear hCdiv_le_C
  have hGrowthNu4 := sbAsm_lNaught_ge_C_div_nu4 (C := C / sbAsmGrowthB) (M := C * M)
    hCdivge1 hCdivM1 hcStarpos hcStar2 hnu hnu1 hKnn hα0 hα1
  clear hCdivM1 hCdivge1
  have hLGrowth0 : (64 : ℝ) * (C / sbAsmGrowthB) / nu ^ (4 : ℝ) ≤ (L : ℝ) := by
    clear * - C nu hLnaughtAtL hCgrowthLe hGrowthNu4
    exact le_trans hGrowthNu4 (le_trans hCgrowthLe hLnaughtAtL)
  clear hGrowthNu4 hCgrowthLe
  have hLGrowth : growthCoeff * C / nu ^ (4 : ℝ) ≤ (L : ℝ) := by
    clear * - C_H Ccrude growthCoeff hgrowthCoeffdef C nu hLGrowth0
    have heq : growthCoeff * C = 64 * (C / sbAsmGrowthB) := by
      rw [hgrowthCoeffdef]; field_simp
    rw [heq]; exact hLGrowth0
  -- `growthCoeff * C ≥ 4^3000 * 4 * Ccrude^2 * C_H =: RHSCreq`, in particular `≥ 4`.
  clear hLGrowth0 hgrowthCoeffdef
  have hgrowthCreq : (4 : ℝ) ^ (3000 : ℝ) * 4 * Ccrude ^ 2 * C_H ≤ growthCoeff * C := by
    clear * - C_H Ccrude growthCoeff hgrowthCoeffpos Creq hCreqdef C hCreq_C
    have h1 : growthCoeff * Creq ≤ growthCoeff * C := mul_le_mul_of_nonneg_left hCreq_C
      hgrowthCoeffpos.le
    have h2 : growthCoeff * Creq = (4 : ℝ) ^ (3000 : ℝ) * 4 * Ccrude ^ 2 * C_H := by
      rw [hCreqdef]; field_simp
    linarith only [h1, h2]
  clear hCreq_C hCreqdef
  have hCcrude2 : (1 : ℝ) ≤ Ccrude ^ 2 := by clear * - Ccrude hCcrude1; nlinarith only [hCcrude1]
  have h8pow_ge8 : (8 : ℝ) ≤ (4 : ℝ) ^ (3000 : ℝ) * 4 * Ccrude ^ 2 * C_H := by
    clear * - C_H hCH1 Ccrude hCcrude2
    have h1 : (2 : ℝ) ≤ (4 : ℝ) ^ (3000 : ℝ) := by
      calc (2 : ℝ) ≤ (4 : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]; norm_num
        _ ≤ (4 : ℝ) ^ (3000 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    have step1 : (2 : ℝ) * 4 ≤ (4 : ℝ) ^ (3000 : ℝ) * 4 :=
      mul_le_mul_of_nonneg_right h1 (by norm_num)
    have step1pos : (0 : ℝ) ≤ (4 : ℝ) ^ (3000 : ℝ) * 4 := by
      have : (0:ℝ) ≤ (2:ℝ)*4 := by norm_num
      exact le_trans this step1
    have step2 : (2 : ℝ) * 4 * 1 ≤ (4 : ℝ) ^ (3000 : ℝ) * 4 * Ccrude ^ 2 :=
      mul_le_mul step1 hCcrude2 (by norm_num) step1pos
    have step2pos : (0 : ℝ) ≤ (4 : ℝ) ^ (3000 : ℝ) * 4 * Ccrude ^ 2 := by
      have : (0:ℝ) ≤ (2:ℝ)*4*1 := by norm_num
      exact le_trans this step2
    have step3 : (2 : ℝ) * 4 * 1 * 1 ≤ (4 : ℝ) ^ (3000 : ℝ) * 4 * Ccrude ^ 2 * C_H :=
      mul_le_mul step2 hCH1 (by norm_num) step2pos
    have step3eq : (2:ℝ)*4*1*1 = 8 := by norm_num
    rw [step3eq] at step3
    exact step3
  have hgrowthC8 : (8 : ℝ) ≤ growthCoeff * C := by
    clear * - growthCoeff C hgrowthCreq h8pow_ge8
    exact le_trans h8pow_ge8 hgrowthCreq
  clear h8pow_ge8
  have hnu4le1 : nu ^ (4 : ℝ) ≤ 1 := by
    clear * - nu hnu hnu1
    exact le_trans (Real.rpow_le_rpow hnu.le hnu1 (by norm_num)) (le_of_eq (Real.one_rpow _))
  have hnu4pos : (0 : ℝ) < nu ^ (4 : ℝ) := by
    clear * - nu hnu
    exact Real.rpow_pos_of_pos hnu _
  have hL8 : (8 : ℝ) ≤ (L : ℝ) := by
    have hstep : growthCoeff * C ≤ growthCoeff * C / nu ^ (4 : ℝ) := by
      rw [le_div_iff₀ hnu4pos]
      exact mul_le_of_le_one_right (by positivity) hnu4le1
    linarith only [hgrowthC8, hstep, hLGrowth]
  clear hnu4le1
  have hL4nat : (4 : ℕ) ≤ L := by
    clear * - hL8
    have : (4 : ℝ) ≤ (L : ℝ) := by linarith only [hL8]
    exact_mod_cast this
  have hL3nat : (3 : ℕ) ≤ L := by
    clear * - CA0 ell n hL4nat
    exact le_trans (by norm_num) hL4nat
    -- `n ≥ ell/2 ≥ L/4`, via `lNaught_absorbs` at `(CA0, CA0*3216)` and the tail
    -- + ratio bounds.
  have hTailL : 200 * Real.log (L : ℝ) + 1 ≤ 201 * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) := by
    clear * - alpha hα0 hL3nat
    exact sbAsm_tail_le hL3nat hα0
  have hell1nat : (1 : ℕ) ≤ ell := by
    clear * - ell hL2ell hL8
    have : (1 : ℝ) ≤ (ell : ℝ) := by linarith only [hL8, hL2ell]
    exact_mod_cast this
  have hRatioAlpha : (L : ℝ) ^ alpha ≤ 2 * (ell : ℝ) ^ alpha := by
    clear * - alpha hα0 hα1 ell hellL hL2ell hell1nat
    exact sbAsm_ratio_alpha_le hell1nat hellL hL2ell hα0 hα1
  clear hellL
  have hRatioLog : Real.log (L : ℝ) ^ (3 : ℝ) ≤ 8 * Real.log (ell : ℝ) ^ (3 : ℝ) := by
    clear * - ell hL2ell hL4nat
    exact sbAsm_ratio_log_le hL4nat hL2ell
  clear hL4nat
  have hlog3Lnn : (0 : ℝ) ≤ Real.log (L : ℝ) ^ (3 : ℝ) :=
    Real.rpow_nonneg (Real.log_natCast_nonneg L) _
  have hellRpos : (0 : ℝ) < (ell : ℝ) := by
    clear * - ell hell1nat
    have : (1 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell1nat
    linarith only [this]
  have hellalphann : (0 : ℝ) ≤ (ell : ℝ) ^ alpha := by
    clear * - alpha ell hellRpos
    exact Real.rpow_nonneg hellRpos.le _
  have hTailToEll : 200 * Real.log (L : ℝ) + 1 ≤ 3216 * ((ell : ℝ) ^ alpha *
      Real.log (ell : ℝ) ^ (3 : ℝ)) := by
    have hstep1 : 201 * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤
        201 * (2 * (ell : ℝ) ^ alpha) * Real.log (L : ℝ) ^ (3 : ℝ) := by
      have h201 : (0 : ℝ) ≤ 201 * Real.log (L : ℝ) ^ (3 : ℝ) := by positivity
      nlinarith only [hRatioAlpha, h201]
    have hstep2 : 201 * (2 * (ell : ℝ) ^ alpha) * Real.log (L : ℝ) ^ (3 : ℝ) ≤
        201 * (2 * (ell : ℝ) ^ alpha) * (8 * Real.log (ell : ℝ) ^ (3 : ℝ)) := by
      have h0 : (0 : ℝ) ≤ 201 * (2 * (ell : ℝ) ^ alpha) := by positivity
      nlinarith only [hRatioLog, h0]
    nlinarith only [hTailL, hstep1, hstep2]
  clear hRatioLog hRatioAlpha
  have hThreshAbsorbEll : lNaught CA0 (CA0 * 3216) alpha cStar nu K ≤ (ell : ℝ) :=
    (sbAsm_inflate_fixed (C0 := CA0) (Mfix := CA0 * 3216) (C := C) (M := M)
      (le_trans zero_le_one hCA01) (by positivity) hM hC1 hα1 hcStarpos hnu hKnn hCA0_C
      hCA03216_C).trans hLnaught
  clear hCA03216_C hCA0_C
  have hAbsorbEll := hAbsorbs CA0 le_rfl (CA0 * 3216) (by nlinarith only [hCA01])
    alpha hα0 hα1 cStar hcStarpos hcStar2 nu hnu hnu1 K hKnn ell hThreshAbsorbEll
  clear hThreshAbsorbEll hcStar2 hAbsorbs
  have hEllHalfBound : 3216 * ((ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ)) ≤
      (ell : ℝ) / 2 := by
    have heq : CA0 * 3216 * (ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ) =
        CA0 * (3216 * ((ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ))) := by ring
    rw [heq] at hAbsorbEll
    have hnn : (0 : ℝ) ≤ 3216 * ((ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ)) := by positivity
    nlinarith only [hAbsorbEll, hCA01, hnn]
  clear hAbsorbEll hCA01
  have hNEllHalf : (ell : ℝ) / 2 ≤ (n : ℝ) := by clear * - ell n hGap hTailToEll hEllHalfBound; linarith only [hGap, hTailToEll, hEllHalfBound]
  clear hEllHalfBound
  have hNL4 : (L : ℝ) / 4 ≤ (n : ℝ) := by clear * - n hL2ell hNEllHalf; linarith only [hNEllHalf, hL2ell]
  have hell3nat : (3 : ℕ) ≤ ell := by
    clear * - ell hL2ell hL8
    have : (3 : ℝ) ≤ (ell : ℝ) := by linarith only [hL8, hL2ell]
    exact_mod_cast this
  have hellLpos : (0 : ℝ) < (L : ℝ) := by clear * - C_H n hL8; linarith only [hL8]
  -- Elementary `X - n + C_H log²X ≤ (1+C_H) M_X X^α log³X`, reused for both `X`.
  clear hL8
  have hlog3 : (1 : ℝ) < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
    linarith only [Real.exp_one_lt_d9]
  have hYbound : ∀ (X n' : ℕ) (M_X : ℝ), 1 ≤ M_X → 3 ≤ X →
      (X : ℝ) - M_X * (X : ℝ) ^ alpha * Real.log (X : ℝ) ^ (3 : ℝ) ≤ (n' : ℝ) →
      (X : ℝ) - (n' : ℝ) + C_H * Real.log (X : ℝ) ^ (2 : ℝ) ≤
        (1 + C_H) * (M_X * (X : ℝ) ^ alpha * Real.log (X : ℝ) ^ (3 : ℝ)) := by
    clear * - C_H hCHpos alpha hα0 ell hlog3
    intro X n' M_X hMX1 hX3 hXGap
    have hX3R : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX3
    have hXRpos : (0 : ℝ) < (X : ℝ) := by linarith only [hX3R]
    have hlogXgt1 : (1 : ℝ) < Real.log (X : ℝ) :=
      lt_of_lt_of_le hlog3 (Real.log_le_log (by norm_num) hX3R)
    have hlogXpos : (0 : ℝ) < Real.log (X : ℝ) := by linarith only [hlogXgt1]
    have hXalpha1 : (1 : ℝ) ≤ (X : ℝ) ^ alpha := Real.one_le_rpow (by linarith only [hX3R]) hα0
    have hlogcube_eq : Real.log (X : ℝ) ^ (3 : ℝ) =
        Real.log (X : ℝ) ^ (2 : ℝ) * Real.log (X : ℝ) := by
      have h : Real.log (X : ℝ) ^ ((2 : ℝ) + (1 : ℝ)) =
          Real.log (X : ℝ) ^ (2 : ℝ) * Real.log (X : ℝ) ^ (1 : ℝ) := Real.rpow_add hlogXpos 2 1
      rw [Real.rpow_one] at h
      rwa [show (2 : ℝ) + (1 : ℝ) = (3 : ℝ) by norm_num] at h
    have hlog2Xnn : (0 : ℝ) ≤ Real.log (X : ℝ) ^ (2 : ℝ) := Real.rpow_nonneg hlogXpos.le _
    have hlog3Xnn : (0 : ℝ) ≤ Real.log (X : ℝ) ^ (3 : ℝ) := Real.rpow_nonneg hlogXpos.le _
    have hlog2_le_log3 : Real.log (X : ℝ) ^ (2 : ℝ) ≤ Real.log (X : ℝ) ^ (3 : ℝ) := by
      rw [hlogcube_eq]
      have hmul := mul_le_mul_of_nonneg_left hlogXgt1.le hlog2Xnn
      rw [mul_one] at hmul
      linarith only [hmul]
    have hMXXalpha1 : (1 : ℝ) ≤ M_X * (X : ℝ) ^ alpha := by nlinarith only [hMX1, hXalpha1]
    have hB : Real.log (X : ℝ) ^ (2 : ℝ) ≤ M_X * (X : ℝ) ^ alpha * Real.log (X : ℝ) ^ (3 : ℝ) := by
      nlinarith only [hMXXalpha1, hlog3Xnn, hlog2_le_log3]
    nlinarith only [hXGap, hB, hCHpos]
  -- `2^3001 ≤ 4^3000` (used for the `ell`-side residual threshold).
  clear hlog3
  have h4eq : (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have h4pow : (4 : ℝ) ^ (3000 : ℝ) = (2 : ℝ) ^ (6000 : ℝ) := by
    clear * - h4eq
    rw [h4eq, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  clear h4eq
  have h2001le4000 : (2 : ℝ) ^ (3001 : ℝ) ≤ (4 : ℝ) ^ (3000 : ℝ) := by
    clear * - h4pow
    rw [h4pow]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  -- ===== The `X = L` piece =====
  clear h4pow
  have hMXL1 : (1 : ℝ) ≤ 202 * M := by clear * - M hM; nlinarith only [hM]
  have hLalpha_log3_nn : (0 : ℝ) ≤ (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) := by
    have h1 : (0 : ℝ) ≤ (L : ℝ) ^ alpha := Real.rpow_nonneg hellLpos.le _
    have h2 : (0 : ℝ) ≤ Real.log (L : ℝ) := Real.log_natCast_nonneg L
    positivity
  have hXGapL : (L : ℝ) - 202 * M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (n : ℝ) := by
    clear * - alpha M hM hscale n hGap hTailL hLalpha_log3_nn
    have h4 : M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) +
        201 * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤
        202 * M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) := by
      nlinarith only [hM, hLalpha_log3_nn]
    linarith only [hscale, hGap, hTailL, h4]
  clear hTailL hscale
  have hThreshHomogL : lNaught C_H (C_H * (202 * M)) alpha cStar nu K ≤ (L : ℝ) := by
    clear * - C_H hCHpos C nu cStar K hnu alpha M hα1 hM hCpos hCH_C hCHK'Llogfac_C hcStarpos hKnn hLnaughtAtL
    exact (sbAsm_inflate_B (Ch := C_H) (K' := 202) (C := C) (M := M)
        hCHpos.le (le_trans zero_le_one hM) hCpos.le hα1 hcStarpos hnu hKnn (by norm_num)
        hCH_C hCHK'Llogfac_C).trans hLnaughtAtL
  clear hLnaughtAtL hCHK'Llogfac_C
  have hHomogAtLn := hHomogBody nu cStar K hnu hnu1 P hPrefix hJ2 hJ3 hJ1V2 hJ4 hJ5 alpha (202 * M)
    hα0 hα1 hMXL1 L n hThreshHomogL hXGapL
  clear hThreshHomogL
  have hYL := hYbound L n (202 * M) hMXL1 hL3nat hXGapL
  clear hXGapL hMXL1
  have hSLpos : (0 : ℝ) < sigmaBarInfinite nu L P := by
    clear * - nu hnu P hPrefix hJ2 hJ3 hJ4
    exact sigmaBarInfinite_pos hnu L hPrefix hJ2 hJ3 hJ4
  have hMaxYL : max (0 : ℝ) ((L : ℝ) - (n : ℝ) + C_H * Real.log (L : ℝ) ^ (2 : ℝ)) ≤
      (1 + C_H) * (202 * M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) := by
    clear * - C_H hCHpos alpha M hM n hlog3Lnn hellLpos hYL
    refine max_le ?_ hYL
    have hM0 : (0 : ℝ) ≤ M := le_trans zero_le_one hM
    have hCH0 : (0 : ℝ) ≤ 1 + C_H := by linarith only [hCHpos]
    have h202M : (0 : ℝ) ≤ 202 * M := by linarith only [hM0]
    have h202ML : (0 : ℝ) ≤ 202 * M * (L : ℝ) ^ alpha :=
      mul_nonneg h202M (Real.rpow_nonneg hellLpos.le _)
    have hfull : (0 : ℝ) ≤ 202 * M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) :=
      mul_nonneg h202ML hlog3Lnn
    exact mul_nonneg hCH0 hfull
  clear hYL
  have hFirstTermL : C_H * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
      max (0 : ℝ) ((L : ℝ) - (n : ℝ) + C_H * Real.log (L : ℝ) ^ (2 : ℝ)) ≤
      202 * C_H * (1 + C_H) * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
        Real.log (L : ℝ) ^ (3 : ℝ) := by
    clear * - C_H hCHpos nu P alpha M n hSLpos hMaxYL
    have hcoef_nn : (0 : ℝ) ≤ C_H * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) :=
      mul_nonneg hCHpos.le (Real.rpow_nonneg hSLpos.le _)
    have h1 := mul_le_mul_of_nonneg_left hMaxYL hcoef_nn
    calc C_H * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
          max (0 : ℝ) ((L : ℝ) - (n : ℝ) + C_H * Real.log (L : ℝ) ^ (2 : ℝ)) ≤
          C_H * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
            ((1 + C_H) * (202 * M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ))) := h1
      _ = 202 * C_H * (1 + C_H) * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
            Real.log (L : ℝ) ^ (3 : ℝ) := by ring
  clear hMaxYL
  have hResidL := sbAsm_residual_dominate (d := d) (nu := nu) (alpha := alpha) (M := M)
      (rho := (4 : ℝ)) (p := (3000 : ℝ)) (Cres := C_H) (eps := (1 : ℝ)) (T := growthCoeff * C)
      (Ccrude := Ccrude) (L := L) (t := n)
      hPrefix hJ2 hJ3 hJ4 hnu hnu1 hM hα0 hα1 hL3nat (by norm_num)
      (by linarith only [hNL4] : (L : ℝ) ≤ 4 * (n : ℝ))
      (by norm_num) hCHpos.le (by norm_num)
      hCcrude1 (hCrudeBody nu hnu hnu1 P hPrefix hJ2 hJ3 hJ4 L)
      (by linarith only [hgrowthC8] : (1 : ℝ) ≤ growthCoeff * C) hLGrowth
      (by nlinarith only [hgrowthCreq] :
        (4 : ℝ) ^ (3000 : ℝ) * 4 * Ccrude ^ 2 * C_H ≤ 1 * (growthCoeff * C))
  clear hNL4 hL3nat
  have hSumL : |(sigmaBarInfinite nu L P)⁻¹ * sigmaBarSeq nu L P n - 1| +
      |sigmaBarInfinite nu L P * sigmaBarStarInvSeq nu L P n - 1| ≤
      CoefL * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
        Real.log (L : ℝ) ^ (3 : ℝ) := by
    clear * - C_H CoefL hCoefLdef nu P alpha M n hHomogAtLn hFirstTermL hResidL
    have hstep := le_trans hHomogAtLn (add_le_add hFirstTermL hResidL)
    have heq : CoefL * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
        Real.log (L : ℝ) ^ (3 : ℝ) =
        202 * C_H * (1 + C_H) * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
            Real.log (L : ℝ) ^ (3 : ℝ) +
          1 * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
            Real.log (L : ℝ) ^ (3 : ℝ) := by rw [hCoefLdef]; ring
    linarith only [hstep, heq]
  clear hResidL hFirstTermL hHomogAtLn hCoefLdef
  have hFirstAbsL : |(sigmaBarInfinite nu L P)⁻¹ * sigmaBarSeq nu L P n - 1| ≤
      CoefL * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
        Real.log (L : ℝ) ^ (3 : ℝ) := by
    clear * - CoefL nu P alpha M ell n hSumL
    have hOtherNonneg : (0 : ℝ) ≤
        |sigmaBarInfinite nu L P * sigmaBarStarInvSeq nu L P n - 1| := abs_nonneg _
    linarith only [hSumL, hOtherNonneg]
  -- ===== The `X = ell` piece =====
  clear hSumL
  have hellalphann : (0 : ℝ) ≤ (ell : ℝ) ^ alpha := by
    clear * - alpha ell hellRpos hellalphann
    exact Real.rpow_nonneg hellRpos.le _
  have hellalpha_log3_nn : (0 : ℝ) ≤ (ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ) := by
    have hlogellnn : (0 : ℝ) ≤ Real.log (ell : ℝ) := Real.log_nonneg (by exact_mod_cast hell1nat)
    positivity
  have hXGapEll : (ell : ℝ) - MXell * (ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ) ≤
      (n : ℝ) := by
    have hle3216 : (3216 : ℝ) ≤ MXell := by
      have h0 : (0 : ℝ) ≤ C_H * sbAsmGrowthB := by positivity
      rw [hMXelldef]; linarith only [h0]
    have h2 : 3216 * ((ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ)) ≤
        MXell * ((ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ)) :=
      mul_le_mul_of_nonneg_right hle3216 hellalpha_log3_nn
    linarith only [hGap, hTailToEll, h2]
  clear hTailToEll hGap hMXelldef
  have hThreshHomogEll : lNaught C_H (C_H * MXell) alpha cStar nu K ≤ (ell : ℝ) :=
    (sbAsm_inflate_fixed (C0 := C_H) (Mfix := C_H * MXell) (C := C) (M := M)
      hCHpos.le (by positivity) hM hC1 hα1 hcStarpos hnu hKnn hCH_C hCHMXell_C).trans hLnaught
  clear hCHMXell_C hCH_C hC1 hLnaught
  have hHomogAtElln := hHomogBody nu cStar K hnu hnu1 P hPrefix hJ2 hJ3 hJ1V2 hJ4 hJ5 alpha MXell
    hα0 hα1 hMXell1 ell n hThreshHomogEll hXGapEll
  clear hThreshHomogEll hJ5 hJ1V2 hHomogBody
  have hYEll := hYbound ell n MXell hMXell1 hell3nat hXGapEll
  clear hXGapEll hYbound
  have hSEllpos : (0 : ℝ) < sigmaBarInfinite nu ell P := by
    clear * - nu hnu P hPrefix hJ2 hJ3 hJ4 ell
    exact sigmaBarInfinite_pos hnu ell hPrefix hJ2 hJ3 hJ4
  have hMaxYEll : max (0 : ℝ) ((ell : ℝ) - (n : ℝ) + C_H * Real.log (ell : ℝ) ^ (2 : ℝ)) ≤
      (1 + C_H) * (MXell * (ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ)) := by
    clear * - C_H hCHpos MXell hMXell1 alpha ell n hell1nat hellRpos hYEll
    refine max_le ?_ hYEll
    have hMXell0 : (0 : ℝ) ≤ MXell := le_trans zero_le_one hMXell1
    have hCH0 : (0 : ℝ) ≤ 1 + C_H := by linarith only [hCHpos]
    have hlogellnn : (0 : ℝ) ≤ Real.log (ell : ℝ) := Real.log_nonneg (by exact_mod_cast hell1nat)
    have hlog3ellnn : (0 : ℝ) ≤ Real.log (ell : ℝ) ^ (3 : ℝ) := Real.rpow_nonneg hlogellnn _
    have hMXellalpha : (0 : ℝ) ≤ MXell * (ell : ℝ) ^ alpha :=
      mul_nonneg hMXell0 (Real.rpow_nonneg hellRpos.le _)
    have hfull : (0 : ℝ) ≤ MXell * (ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ) :=
      mul_nonneg hMXellalpha hlog3ellnn
    exact mul_nonneg hCH0 hfull
  clear hYEll
  have hEllToL : (ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ) ≤
      (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) := by
    have h1 : (ell : ℝ) ^ alpha ≤ (L : ℝ) ^ alpha := Real.rpow_le_rpow hellRpos.le hellLR hα0
    have h2 : Real.log (ell : ℝ) ≤ Real.log (L : ℝ) := Real.log_le_log hellRpos hellLR
    have h3 : Real.log (ell : ℝ) ^ (3 : ℝ) ≤ Real.log (L : ℝ) ^ (3 : ℝ) :=
      Real.rpow_le_rpow (Real.log_nonneg (by exact_mod_cast hell1nat)) h2 (by norm_num)
    have hlog3ellnn : (0 : ℝ) ≤ Real.log (ell : ℝ) ^ (3 : ℝ) := by
      have : (0 : ℝ) ≤ Real.log (ell : ℝ) := Real.log_nonneg (by exact_mod_cast hell1nat)
      positivity
    calc (ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ) ≤
          (L : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ) :=
          mul_le_mul_of_nonneg_right h1 hlog3ellnn
      _ ≤ (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) :=
          mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hellLpos.le _)
  clear hell1nat hellLR
  have hFirstTermEll : C_H * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
      max (0 : ℝ) ((ell : ℝ) - (n : ℝ) + C_H * Real.log (ell : ℝ) ^ (2 : ℝ)) ≤
      C_H * (1 + C_H) * MXell * M * (L : ℝ) ^ alpha *
        (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) * Real.log (L : ℝ) ^ (3 : ℝ) := by
    clear * - C_H hCHpos MXell hMXell1 nu P alpha M hM ell n hLalpha_log3_nn hSEllpos hMaxYEll hEllToL
    have hcoef_nn : (0 : ℝ) ≤ C_H * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) :=
      mul_nonneg hCHpos.le (Real.rpow_nonneg hSEllpos.le _)
    have h1 := mul_le_mul_of_nonneg_left hMaxYEll hcoef_nn
    have hMXellnn : (0 : ℝ) ≤ MXell := le_trans zero_le_one hMXell1
    have h1Cnn : (0 : ℝ) ≤ 1 + C_H := by linarith only [hCHpos]
    have step0 : MXell * ((ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ)) ≤
        MXell * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) :=
      mul_le_mul_of_nonneg_left hEllToL hMXellnn
    have step1 : (1 + C_H) * (MXell * ((ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ))) ≤
        (1 + C_H) * (MXell * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ))) :=
      mul_le_mul_of_nonneg_left step0 h1Cnn
    have h2 : C_H * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
        ((1 + C_H) * (MXell * (ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ))) ≤
        C_H * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
          ((1 + C_H) * (MXell * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)))) := by
      have heq : (1 + C_H) * (MXell * (ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ)) =
          (1 + C_H) * (MXell * ((ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ))) := by ring
      rw [heq]
      exact mul_le_mul_of_nonneg_left step1 hcoef_nn
    have step2 : (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤
        M * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) :=
      le_mul_of_one_le_left hLalpha_log3_nn hM
    have step3 : MXell * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) ≤
        MXell * (M * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ))) :=
      mul_le_mul_of_nonneg_left step2 hMXellnn
    have step4 : (1 + C_H) * (MXell * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ))) ≤
        (1 + C_H) * (MXell * (M * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)))) :=
      mul_le_mul_of_nonneg_left step3 h1Cnn
    have h3 : C_H * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
        ((1 + C_H) * (MXell * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)))) ≤
        C_H * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
          ((1 + C_H) * (MXell * (M * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ))))) :=
      mul_le_mul_of_nonneg_left step4 hcoef_nn
    calc C_H * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
          max (0 : ℝ) ((ell : ℝ) - (n : ℝ) + C_H * Real.log (ell : ℝ) ^ (2 : ℝ)) ≤
          C_H * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
            ((1 + C_H) * (MXell * (ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ))) := h1
      _ ≤ C_H * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
            ((1 + C_H) * (MXell * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)))) := h2
      _ ≤ C_H * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
            ((1 + C_H) * (MXell * (M * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ))))) := h3
      _ = C_H * (1 + C_H) * MXell * M * (L : ℝ) ^ alpha *
            (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) * Real.log (L : ℝ) ^ (3 : ℝ) := by ring
  clear hMaxYEll hMXell1
  have hTellL : (growthCoeff * C / 2) / nu ^ (4 : ℝ) ≤ (ell : ℝ) := by
    clear * - growthCoeff C nu ell hL2ell hLGrowth
    have heq : (growthCoeff * C / 2) / nu ^ (4 : ℝ) = (growthCoeff * C / nu ^ (4 : ℝ)) / 2 := by
      ring
    rw [heq]; linarith only [hLGrowth, hL2ell]
  clear hLGrowth hL2ell
  have h2pow_eq : (2 : ℝ) ^ (3001 : ℝ) = 2 * (2 : ℝ) ^ (3000 : ℝ) := by
    rw [show (3001 : ℝ) = (3000 : ℝ) + 1 by norm_num, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      Real.rpow_one]
    ring
  have hstepA1 : (2 : ℝ) ^ (3001 : ℝ) * 4 ≤ (4 : ℝ) ^ (3000 : ℝ) * 4 := by
    clear * - h2001le4000
    exact mul_le_mul_of_nonneg_right h2001le4000 (by norm_num)
  clear h2001le4000
  have hstepA2 : (2 : ℝ) ^ (3001 : ℝ) * 4 * Ccrude ^ 2 ≤ (4 : ℝ) ^ (3000 : ℝ) * 4 * Ccrude ^ 2 := by
    clear * - Ccrude hCcrude2 hstepA1
    exact mul_le_mul_of_nonneg_right hstepA1 (le_trans zero_le_one hCcrude2)
  clear hstepA1 hCcrude2
  have hstepA : (2 : ℝ) ^ (3001 : ℝ) * 4 * Ccrude ^ 2 * C_H ≤
      (4 : ℝ) ^ (3000 : ℝ) * 4 * Ccrude ^ 2 * C_H := by
    clear * - C_H hCH1 Ccrude hstepA2
    exact mul_le_mul_of_nonneg_right hstepA2 (le_trans zero_le_one hCH1)
  clear hstepA2 hCH1
  have hstepB : (2 : ℝ) ^ (3001 : ℝ) * 4 * Ccrude ^ 2 * C_H ≤ growthCoeff * C := by
    clear * - C_H Ccrude growthCoeff C hgrowthCreq hstepA
    exact le_trans hstepA hgrowthCreq
  clear hstepA hgrowthCreq
  have hEllTbigEq : (2 : ℝ) ^ (3001 : ℝ) * 4 * Ccrude ^ 2 * C_H =
      2 * ((2 : ℝ) ^ (3000 : ℝ) * 4 * Ccrude ^ 2 * C_H) := by clear * - C_H Ccrude h2pow_eq; rw [h2pow_eq]; ring
  clear h2pow_eq
  have hEllTbig : (2 : ℝ) ^ (3000 : ℝ) * 4 * Ccrude ^ 2 * C_H ≤ 1 * (growthCoeff * C / 2) := by
    clear * - C_H Ccrude growthCoeff C hstepB hEllTbigEq
    rw [hEllTbigEq] at hstepB
    linarith only [hstepB]
  clear hEllTbigEq hstepB
  have hResidEll0 := sbAsm_residual_dominate (d := d) (nu := nu) (alpha := alpha) (M := M)
      (rho := (2 : ℝ)) (p := (3000 : ℝ)) (Cres := C_H) (eps := (1 : ℝ)) (T := growthCoeff * C / 2)
      (Ccrude := Ccrude) (L := ell) (t := n)
      hPrefix hJ2 hJ3 hJ4 hnu hnu1 hM hα0 hα1 hell3nat (by norm_num)
      (by linarith only [hNEllHalf] : (ell : ℝ) ≤ 2 * (n : ℝ))
      (by norm_num) hCHpos.le (by norm_num)
      hCcrude1 (hCrudeBody nu hnu hnu1 P hPrefix hJ2 hJ3 hJ4 ell)
      (by linarith only [hgrowthC8] : (1 : ℝ) ≤ growthCoeff * C / 2) hTellL hEllTbig
  clear hEllTbig hTellL hell3nat hNEllHalf hgrowthC8 hα1 hα0 hJ4 hJ3 hJ2 hPrefix hnu1 hnu hCrudeBody hCcrude1
  have hResidEll : C_H * (n : ℝ) ^ (-(3000 : ℝ)) ≤
      M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) * Real.log (L : ℝ) ^ (3 : ℝ) := by
    clear * - C_H nu P alpha M hM ell n hSEllpos hEllToL hResidEll0
    have h2 : (1 : ℝ) * M * (ell : ℝ) ^ alpha * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
        Real.log (ell : ℝ) ^ (3 : ℝ) ≤
        M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) * Real.log (L : ℝ) ^ (3 : ℝ) := by
      have hM0 : (0 : ℝ) ≤ M := le_trans zero_le_one hM
      have hcoefnn : (0 : ℝ) ≤ M * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) :=
        mul_nonneg hM0 (Real.rpow_nonneg hSEllpos.le _)
      have step0 : M * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
          ((ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ)) ≤
          M * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
            ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) :=
        mul_le_mul_of_nonneg_left hEllToL hcoefnn
      have heqL : (1 : ℝ) * M * (ell : ℝ) ^ alpha * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
          Real.log (ell : ℝ) ^ (3 : ℝ) =
          M * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
            ((ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ)) := by ring
      have heqR : M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
          Real.log (L : ℝ) ^ (3 : ℝ) =
          M * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
            ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) := by ring
      rw [heqL, heqR]
      exact step0
    linarith only [hResidEll0, h2]
  clear hResidEll0 hEllToL
  have hSumEll : |(sigmaBarInfinite nu ell P)⁻¹ * sigmaBarSeq nu ell P n - 1| +
      |sigmaBarInfinite nu ell P * sigmaBarStarInvSeq nu ell P n - 1| ≤
      CoefEll * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
        Real.log (L : ℝ) ^ (3 : ℝ) := by
    clear * - C_H MXell CoefEll hCoefElldef nu P alpha M ell n hHomogAtElln hFirstTermEll hResidEll
    have hstep := le_trans hHomogAtElln (add_le_add hFirstTermEll hResidEll)
    have heq : CoefEll * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
        Real.log (L : ℝ) ^ (3 : ℝ) =
        C_H * (1 + C_H) * MXell * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
            Real.log (L : ℝ) ^ (3 : ℝ) +
          M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
            Real.log (L : ℝ) ^ (3 : ℝ) := by rw [hCoefElldef]; ring
    linarith only [hstep, heq]
  clear hResidEll hFirstTermEll hHomogAtElln hCoefElldef
  have hFirstAbsEll : |(sigmaBarInfinite nu ell P)⁻¹ * sigmaBarSeq nu ell P n - 1| ≤
      CoefEll * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
        Real.log (L : ℝ) ^ (3 : ℝ) := by
    clear * - CoefEll nu P alpha M ell n hSumEll
    have hOtherNonneg : (0 : ℝ) ≤
        |sigmaBarInfinite nu ell P * sigmaBarStarInvSeq nu ell P n - 1| := abs_nonneg _
    linarith only [hSumEll, hOtherNonneg]
  clear hSumEll
  have hM0 : (0 : ℝ) ≤ M := by
    clear * - M hM
    exact le_trans zero_le_one hM
  clear hM
  have hLalphann : (0 : ℝ) ≤ (L : ℝ) ^ alpha := by
    clear * - alpha hellLpos
    exact Real.rpow_nonneg hellLpos.le _
  have hfacL_nonneg : (0 : ℝ) ≤
      M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) * Real.log (L : ℝ) ^ (3 : ℝ) := by
    clear * - nu P alpha M hlog3Lnn hSLpos hM0 hLalphann
    have hSinv : (0 : ℝ) ≤ (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) := Real.rpow_nonneg hSLpos.le _
    exact mul_nonneg (mul_nonneg (mul_nonneg hM0 hLalphann) hSinv) hlog3Lnn
  have hfacEll_nonneg : (0 : ℝ) ≤
      M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) * Real.log (L : ℝ) ^ (3 : ℝ) := by
    clear * - nu P alpha M ell hlog3Lnn hSEllpos hM0 hLalphann
    have hSinv : (0 : ℝ) ≤ (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) := Real.rpow_nonneg hSEllpos.le _
    exact mul_nonneg (mul_nonneg (mul_nonneg hM0 hLalphann) hSinv) hlog3Lnn
  clear hM0
  have hFinalL : CoefL * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
      Real.log (L : ℝ) ^ (3 : ℝ) ≤
      C * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) * Real.log (L : ℝ) ^ (3 : ℝ) := by
    clear * - CoefL C nu P alpha M hCoefL_C hfacL_nonneg
    have heqL : CoefL * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
        Real.log (L : ℝ) ^ (3 : ℝ) =
        CoefL * (M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
          Real.log (L : ℝ) ^ (3 : ℝ)) := by ring
    have heqC : C * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
        Real.log (L : ℝ) ^ (3 : ℝ) =
        C * (M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
          Real.log (L : ℝ) ^ (3 : ℝ)) := by ring
    rw [heqL, heqC]
    exact mul_le_mul_of_nonneg_right hCoefL_C hfacL_nonneg
  clear hCoefL_C
  have hFinalEll : CoefEll * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
      Real.log (L : ℝ) ^ (3 : ℝ) ≤
      C * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
        Real.log (L : ℝ) ^ (3 : ℝ) := by
    clear * - CoefEll C nu P alpha M ell hCoefEll_C hfacEll_nonneg
    have heqL : CoefEll * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
        Real.log (L : ℝ) ^ (3 : ℝ) =
        CoefEll * (M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
          Real.log (L : ℝ) ^ (3 : ℝ)) := by ring
    have heqC : C * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
        Real.log (L : ℝ) ^ (3 : ℝ) =
        C * (M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
          Real.log (L : ℝ) ^ (3 : ℝ)) := by ring
    rw [heqL, heqC]
    exact mul_le_mul_of_nonneg_right hCoefEll_C hfacEll_nonneg
  clear hCoefEll_C
  exact ⟨le_trans hFirstAbsL hFinalL, le_trans hFirstAbsEll hFinalEll⟩

end

end SuperdiffusionCLT.Section4.SigmaBarComparison
