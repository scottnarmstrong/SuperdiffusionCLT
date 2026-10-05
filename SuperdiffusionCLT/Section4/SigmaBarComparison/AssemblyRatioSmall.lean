/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.SigmaBarComparison.AssemblyMain
public import SuperdiffusionCLT.Section4.LNaught.SstarLowerB
public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.Assumptions.ShellLaw.J5Consequences

/-!
# `C M L^α shom_L^{-2} log³L ≤ 1/2`

The numeric smallness the target `sigmaBar_cutoff_comparison`'s own display
needs for its own outer constant `C`, via the `lNaught_sstar_lower`
`M`-inflation mechanism (predecessor's route, `K' := 2/c`), independent of
`hHomog`/`hIndep`: applying `lNaught_sstar_lower` at the trivial window
`h := L` (`L ≤ 2L`, `L ≤ L`) with `M`-argument inflated to `K' * (C*M)`
gives `c * K' * (C*M) * L^α log³L ≤ shom_L²`, and `K' := 2/c` makes
`c * K' = 2` exactly, i.e. `C*M*L^α log³L / shom_L² ≤ 1/2`.
-/

@[expose] public section

open MeasureTheory Homogenization
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section4 (lNaught)

namespace SuperdiffusionCLT.Section4.SigmaBarComparison

noncomputable section

theorem sbAsm_ratio_small (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ C : ℝ, C0 ≤ C →
      ∀ (nu cStar K : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : ProbabilityMeasure (ShellSeq d))
          (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P),
          ShellLawJ1Restriction d P → ShellLawJ4 d P → ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
          ∀ alpha M : ℝ, 0 ≤ alpha → alpha < 1 → 1 ≤ M →
            ∀ L : ℕ, lNaught C (C * M) alpha cStar nu K ≤ (L : ℝ) →
              C * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
                  Real.log (L : ℝ) ^ (3 : ℝ) ≤ (1 : ℝ) / 2 := by
  obtain ⟨C0star, hC0star1, c, hcpos, hSstarLower⟩ :=
    SuperdiffusionCLT.Section4.LNaught.lNaught_sstar_lower d hd
  set K' : ℝ := max 1 (2 / c) with hK'def
  have hK'1 : (1 : ℝ) ≤ K' := le_max_left _ _
  have hK'ge : (2 / c : ℝ) ≤ K' := le_max_right _ _
  have hcK'2 : (2 : ℝ) ≤ c * K' := by
    have h := mul_le_mul_of_nonneg_left hK'ge hcpos.le
    have heq : c * (2 / c) = 2 := by field_simp
    linarith only [h, heq]
  set logfac : ℝ := (1 + Real.log K' / Real.log 2) ^ (12 : ℝ) with hlogfacdef
  have hlogfacnn : (0 : ℝ) ≤ logfac := by
    rw [hlogfacdef]
    have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hlogK'nn : (0 : ℝ) ≤ Real.log K' := Real.log_nonneg hK'1
    positivity
  set C0 : ℝ := max 1 (max C0star (C0star * K' * logfac)) with hC0def
  refine ⟨C0, le_max_left _ _, ?_⟩
  intro C hCC0 nu cStar K hnu hnu1 P hPrefix hJ2 hJ3 hJ1V2 hJ4 hJ5 alpha M hα0 hα1 hM L hLnaught
  have hC1 : (1 : ℝ) ≤ C := le_trans (le_max_left _ _) hCC0
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC1
  have hC0star_C : C0star ≤ C :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCC0
  have hC0starK'logfac_C : C0star * K' * logfac ≤ C :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCC0
  have hcStar2 := hJ5.cStar_le_two
  have hcStarpos := hJ5.cStar_pos
  have hKnn := hJ5.K_pos.le
  have hCM1 : (1 : ℝ) ≤ C * M := le_trans hM (le_mul_of_one_le_left (le_trans zero_le_one hM) hC1)
  have hThreshRatio : lNaught C0star (K' * (C * M)) alpha cStar nu K ≤ (L : ℝ) :=
    (sbAsm_inflate_A (C0 := C0star) (K' := K') (C := C) (M := M)
      (le_trans zero_le_one hC0star1) (le_trans zero_le_one hM) hCpos.le hα1
      hcStarpos hnu hKnn hK'1 hC0starK'logfac_C).trans hLnaught
  have hK'CM1 : (1 : ℝ) ≤ K' * (C * M) := le_trans hCM1 (le_mul_of_one_le_left (le_trans zero_le_one hCM1) hK'1)
  have hLR : (L : ℝ) ≤ 2 * (L : ℝ) := by
    have : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg _
    linarith only [this]
  have hSstarAtL := hSstarLower C0star le_rfl (K' * (C * M)) hK'CM1 alpha hα0 hα1 cStar
    hcStarpos hcStar2 nu hnu hnu1 K hKnn P hPrefix hJ2 hJ3 hJ1V2 hJ4 hJ5 L hThreshRatio L hLR
    le_rfl
  have hStarLe := sigmaBarStarScalar_originCube_le_sigmaBarInfinite hnu L hPrefix hJ2 hJ3 hJ4 L
  have hStarPos := SuperdiffusionCLT.Section3.HighContrast.sigmaBarStarScalar_pos hnu L
    hPrefix hJ2 hJ3 hJ4 (L : ℤ)
  have hStarSqLe : sigmaBarStarScalar nu L P (cubeSet (Homogenization.originCube d (L : ℤ))) ^ 2 ≤
      (sigmaBarInfinite nu L P) ^ 2 := pow_le_pow_left₀ hStarPos.le hStarLe 2
  have hSLpos : (0 : ℝ) < sigmaBarInfinite nu L P := sigmaBarInfinite_pos hnu L hPrefix hJ2 hJ3 hJ4
  have hLalpha_log3_nn : (0 : ℝ) ≤ (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) := by
    have h1 : (0 : ℝ) ≤ (L : ℝ) ^ alpha := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have h2 : (0 : ℝ) ≤ Real.log (L : ℝ) := Real.log_natCast_nonneg L
    positivity
  have hCMnn : (0 : ℝ) ≤ C * M := le_trans zero_le_one hCM1
  have hcK'CMge : 2 * (C * M * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ))) ≤
      c * (K' * (C * M)) * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) := by
    have hstep := mul_le_mul_of_nonneg_right hcK'2 (mul_nonneg hCMnn hLalpha_log3_nn)
    nlinarith only [hstep]
  have hCMLsq : 2 * (C * M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) ≤
      (sigmaBarInfinite nu L P) ^ 2 := by
    have hchain : c * (K' * (C * M)) * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤
        (sigmaBarInfinite nu L P) ^ 2 :=
      le_trans hSstarAtL hStarSqLe
    linarith only [hcK'CMge, hchain]
  have hSLnegrpow : (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) = ((sigmaBarInfinite nu L P) ^ 2)⁻¹ := by
    rw [Real.rpow_neg hSLpos.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hSLnegrpow]
  have hSLsqpos : (0 : ℝ) < (sigmaBarInfinite nu L P) ^ 2 := pow_pos hSLpos 2
  rw [show C * M * (L : ℝ) ^ alpha * ((sigmaBarInfinite nu L P) ^ 2)⁻¹ * Real.log (L : ℝ) ^ (3 : ℝ) =
      (C * M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) * ((sigmaBarInfinite nu L P) ^ 2)⁻¹ by
    ring, ← div_eq_mul_inv, div_le_iff₀ hSLsqpos]
  linarith only [hCMLsq]

end

end SuperdiffusionCLT.Section4.SigmaBarComparison
