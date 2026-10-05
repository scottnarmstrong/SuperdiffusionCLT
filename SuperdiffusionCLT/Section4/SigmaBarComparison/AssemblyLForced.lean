/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.SigmaBarComparison.AssemblyMain

/-!
# `L` is forced large: `growthCoeff * C / nu^4 ≤ L`

Reusable extraction of the "`L` forced large via the outer constant `C`"
mechanism used (inline) in `AssemblyQuant.lean`, generalized to `∀ C ≥ C0`
(not one fixed `C`) so it can be applied at whatever outer constant a
consumer eventually settles on. `growthCoeff := 64 / sbAsmGrowthB`.
-/

@[expose] public section

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section4 (lNaught)
open SuperdiffusionCLT.Section4.LNaught (lNaught_mono_const)

namespace SuperdiffusionCLT.Section4.SigmaBarComparison

noncomputable section

theorem sbAsm_L_forced_large (d : ℕ) [NeZero d] :
    ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ C : ℝ, C0 ≤ C →
      ∀ (nu cStar K : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : ProbabilityMeasure (ShellSeq d))
          (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P),
          ShellLawJ1Restriction d P → ShellLawJ4 d P → ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
          ∀ alpha M : ℝ, 0 ≤ alpha → alpha < 1 → 1 ≤ M →
            ∀ L : ℕ, lNaught C (C * M) alpha cStar nu K ≤ (L : ℝ) →
              sbAsmGrowthCoeff * C / nu ^ (4 : ℝ) ≤ (L : ℝ) := by
  refine ⟨max 1 sbAsmGrowthB, le_max_left _ _, ?_⟩
  intro C hCC0 nu cStar K hnu hnu1 P hPrefix hJ2 hJ3 hJ1V2 hJ4 hJ5 alpha M hα0 hα1 hM L hLnaughtAtL
  have hC1 : (1 : ℝ) ≤ C := le_trans (le_max_left _ _) hCC0
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC1
  have hsbAsmGrowthB_C : sbAsmGrowthB ≤ C := le_trans (le_max_right _ _) hCC0
  have hsbAsmGrowthBpos : (0 : ℝ) < sbAsmGrowthB := by
    have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hpow_pos : (0 : ℝ) < (Real.log 2) ^ (12 : ℝ) := Real.rpow_pos_of_pos hlog2pos _
    unfold sbAsmGrowthB; positivity
  have hsbAsmGrowthB1 : (1 : ℝ) ≤ sbAsmGrowthB := by
    have h0 : (0 : ℝ) ≤ 2048 / (Real.log 2) ^ (12 : ℝ) := by positivity
    unfold sbAsmGrowthB; linarith only [h0]
  have hcStar2 := hJ5.cStar_le_two
  have hcStarpos := hJ5.cStar_pos
  have hKnn := hJ5.K_pos.le
  have hCdivpos : (0 : ℝ) < C / sbAsmGrowthB := by positivity
  have hCdivge1 : (1 : ℝ) ≤ C / sbAsmGrowthB := by
    rw [le_div_iff₀ hsbAsmGrowthBpos]; linarith only [hsbAsmGrowthB_C]
  have hCdivM1 : (C / sbAsmGrowthB) * sbAsmGrowthB ≤ C * M := by
    rw [div_mul_cancel₀ C (ne_of_gt hsbAsmGrowthBpos)]
    exact le_mul_of_one_le_right hCpos.le hM
  have hCdiv_le_C : C / sbAsmGrowthB ≤ C := by
    rw [div_le_iff₀ hsbAsmGrowthBpos]
    exact le_mul_of_one_le_right hCpos.le hsbAsmGrowthB1
  have hCgrowthLe : lNaught (C / sbAsmGrowthB) (C * M) alpha cStar nu K ≤
      lNaught C (C * M) alpha cStar nu K :=
    lNaught_mono_const hCdivpos.le hCdiv_le_C (mul_nonneg hCpos.le (le_trans zero_le_one hM))
      hKnn hcStarpos hnu hα1
  have hGrowthNu4 := sbAsm_lNaught_ge_C_div_nu4 (C := C / sbAsmGrowthB) (M := C * M)
    hCdivge1 hCdivM1 hcStarpos hcStar2 hnu hnu1 hKnn hα0 hα1
  have hLGrowth0 : (64 : ℝ) * (C / sbAsmGrowthB) / nu ^ (4 : ℝ) ≤ (L : ℝ) :=
    le_trans hGrowthNu4 (le_trans hCgrowthLe hLnaughtAtL)
  have heq : sbAsmGrowthCoeff * C = 64 * (C / sbAsmGrowthB) := by
    unfold sbAsmGrowthCoeff; field_simp
  rw [heq]; exact hLGrowth0

end

end SuperdiffusionCLT.Section4.SigmaBarComparison
