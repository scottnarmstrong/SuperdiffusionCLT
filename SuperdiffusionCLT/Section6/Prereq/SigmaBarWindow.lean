/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Frozen.Section4.SigmaBarCutoffComparison

/-!
# Comparability of `σ̄` over logarithmic windows

For `ell ≤ L` with `L - K_w log L ≤ ell` and `ell` beyond a threshold depending only on
`(d, ν, c⋆, K, K_w)`,
`σ̄_ell / 2 ≤ σ̄_L ≤ (3/2) σ̄_ell`, and `σ̄_ell > 0`.

The proof applies `sigmaBar_cutoff_comparison` (the display `e.sL.vs.sell`) with
`α = 0` and `M = max 1 K_w`: a window of width `K_w log L` lies inside the window
`M log^3 L` as soon as `log L ≥ 1`, and the growth bound supplies positivity of `σ̄_ell`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6

open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Annealed

/-- `σ̄` is comparable (with absolute constants `1/2`, `3/2`) over windows `[L - K_w log L, L]`. -/
theorem sigmaBar_log_window_comparable (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (nu cStar K Kw : ℝ) (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hcStar : 0 < cStar) :
    ∃ L0 : ℕ,
      ∀ (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
        (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P),
        ShellLawJ1Restriction d P → ShellLawJ4 d P → ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
        ∀ L ell : ℕ, ell ≤ L → L0 ≤ ell → (L : ℝ) - Kw * Real.log (L : ℝ) ≤ (ell : ℝ) →
          0 < sigmaBarInfinite nu ell P ∧
          (1 / 2 : ℝ) * sigmaBarInfinite nu ell P ≤ sigmaBarInfinite nu L P ∧
          sigmaBarInfinite nu L P ≤ (3 / 2 : ℝ) * sigmaBarInfinite nu ell P := by
  obtain ⟨C, hC1, hcomp, hgrow⟩ :=
    SuperdiffusionCLT.Frozen.Section4.sigmaBar_cutoff_comparison d hd
  obtain ⟨Lg, hLg⟩ := hgrow nu hnu hnu1 cStar hcStar K
  set M : ℝ := max 1 Kw with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hKwM : Kw ≤ M := le_max_right _ _
  refine ⟨max 3 (max Lg
    (⌈SuperdiffusionCLT.Frozen.Section4.lNaught C (C * M) 0 cStar nu K⌉₊)), ?_⟩
  intro P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 L ell hle hL0 hwin
  have h3 : 3 ≤ ell := le_trans (le_max_left _ _) hL0
  have hLg' : Lg ≤ ell := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL0
  have hLN : SuperdiffusionCLT.Frozen.Section4.lNaught C (C * M) 0 cStar nu K ≤ (ell : ℝ) :=
    le_trans (Nat.le_ceil _)
      (by exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL0)
  have hL3 : (3 : ℝ) ≤ (L : ℝ) := by exact_mod_cast le_trans h3 hle
  have hlog1 : 1 ≤ Real.log (L : ℝ) := by
    rw [Real.le_log_iff_exp_le (by linarith only [hL3])]
    linarith only [Real.exp_one_lt_d9, hL3]
  have hlog3 : Real.log (L : ℝ) ≤ Real.log (L : ℝ) ^ (3 : ℝ) := by
    calc Real.log (L : ℝ) = Real.log (L : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ Real.log (L : ℝ) ^ (3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hlog1 (by norm_num)
  have hwin' : (L : ℝ) - M * (L : ℝ) ^ (0 : ℝ) * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (ell : ℝ) := by
    rw [Real.rpow_zero, mul_one]
    have : Kw * Real.log (L : ℝ) ≤ M * Real.log (L : ℝ) ^ (3 : ℝ) :=
      mul_le_mul hKwM hlog3 (by linarith only [hlog1]) (by linarith only [hM1])
    linarith only [hwin, this]
  obtain ⟨hrel, hhalf⟩ := hcomp nu cStar K hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 0 M
    le_rfl one_pos hM1 L ell hle hLN hwin'
  have habs := hrel.trans hhalf
  have hpos : 0 < sigmaBarInfinite nu ell P := by
    have hlow := (hLg P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 ell hLg').1
    have hell : (0 : ℝ) < (ell : ℝ) := by
      exact_mod_cast lt_of_lt_of_le (by norm_num) h3
    have hlogell : 0 < Real.log (ell : ℝ) := Real.log_pos (by
      have : (3 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast h3
      linarith only [this])
    refine lt_of_lt_of_le ?_ hlow
    have hCpos : 0 < C := by linarith only [hC1]
    positivity
  refine ⟨hpos, ?_, ?_⟩
  · have h := (abs_le.1 habs).1
    have hr : (1 / 2 : ℝ) ≤ (sigmaBarInfinite nu ell P)⁻¹ * sigmaBarInfinite nu L P := by
      linarith only [h]
    rw [← div_eq_inv_mul, le_div_iff₀ hpos] at hr
    linarith only [hr]
  · have h := (abs_le.1 habs).2
    have hr : (sigmaBarInfinite nu ell P)⁻¹ * sigmaBarInfinite nu L P ≤ 3 / 2 := by
      linarith only [h]
    rw [← div_eq_inv_mul, div_le_iff₀ hpos] at hr
    linarith only [hr]

/-- Satisfiability of the non-law hypotheses: `ell = L` meets the window condition for every
`K_w ≥ 0` and every `L ≥ 1` (so the window is never empty). -/
example (Kw : ℝ) (hKw : 0 ≤ Kw) (L : ℕ) (hL : 1 ≤ L) :
    (L : ℝ) - Kw * Real.log (L : ℝ) ≤ (L : ℝ) := by
  have : 0 ≤ Real.log (L : ℝ) := Real.log_nonneg (by exact_mod_cast hL)
  have := mul_nonneg hKw this
  linarith only [this]

end SuperdiffusionCLT.Section6
