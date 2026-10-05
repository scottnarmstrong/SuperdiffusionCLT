/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.SigmaBarComparison.AssemblySellGen
public import SuperdiffusionCLT.Section4.SigmaBarComparison.GrowthUpper

/-!
# `sbAsm_main`: the proof of `sigmaBar_cutoff_comparison`

Assembles `sbAsm_sell_gen` (`e.sL.vs.sell`, generalized over the outer
constant) with `sbAsm_growth_lower` (unconditional) and `sbAsm_growth_upper`
(needs `e.sL.vs.sell` itself, at a constant `C` chosen first) into
`sigmaBar_cutoff_comparison`. The growth-upper step is genuinely self-referential in `C` (its own
output constant is `8 * C * Cglower + 1`, depending on the input `C`), so the
final outer witness `Cfinal` is chosen AFTER invoking `sbAsm_growth_upper` at
an intermediate `C`, and `sbAsm_sell_gen`'s `∀ C ≥ C0` generality is what
lets `e.sL.vs.sell` be re-derived at `Cfinal ≥ C` directly (no separate
argument needed: the same proof strategy works verbatim for any `C` above
the fixed thresholds baked into `C0`). -/

@[expose] public section

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section4 (lNaught)

namespace SuperdiffusionCLT.Section4.SigmaBarComparison

noncomputable section

/-- **`sbAsm_main`**: `sigmaBar_cutoff_comparison`, from `hHomog` and
`hIndep` alone. -/
theorem sbAsm_main (d : ℕ) [NeZero d] (hd : 2 ≤ d)
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
    ∃ C : ℝ, 1 ≤ C ∧
      (∀ (nu cStar K : ℝ), 0 < nu → nu ≤ 1 →
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
                  Real.log (L : ℝ) ^ (3 : ℝ) ≤
                (1 : ℝ) / 2) ∧
      (∀ nu : ℝ, 0 < nu → nu ≤ 1 →
        ∀ cStar : ℝ, 0 < cStar →
          ∀ K : ℝ,
            ∃ Lg : ℕ,
              ∀ (P : ProbabilityMeasure (ShellSeq d))
                (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P),
                ShellLawJ1Restriction d P → ShellLawJ4 d P → ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
                  ∀ L : ℕ, Lg ≤ L →
                    C⁻¹ * cStar ^ ((3 : ℝ) / 2) * nu ^ (2 : ℝ) * (L : ℝ) ^ ((1 : ℝ) / 2) *
                        Real.log (L : ℝ) ^ (-((9 : ℝ) / 2)) ≤
                      sigmaBarInfinite nu L P ∧
                    sigmaBarInfinite nu L P ≤
                      C * cStar ^ (-((3 : ℝ) / 2)) * nu ^ (-(2 : ℝ)) * (L : ℝ) ^ ((1 : ℝ) / 2) *
                        Real.log (L : ℝ) ^ ((9 : ℝ) / 2)) := by
  obtain ⟨C0, hC01, hSellGen⟩ := sbAsm_sell_gen d hd hHomog hIndep
  obtain ⟨Cglower, hCglower1, hGlowerBody⟩ := sbAsm_growth_lower d hd
  set C : ℝ := max C0 Cglower with hCdef
  have hC1 : (1 : ℝ) ≤ C := le_trans hC01 (le_max_left _ _)
  have hCC0 : C0 ≤ C := le_max_left _ _
  have hCglower_C : Cglower ≤ C := le_max_right _ _
  have hSellFactAtC : ∃ C' : ℝ, 1 ≤ C' ∧
      ∀ (nu cStar K : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : ProbabilityMeasure (ShellSeq d))
          (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P),
          ShellLawJ1Restriction d P → ShellLawJ4 d P → ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
          ∀ alpha M : ℝ, 0 ≤ alpha → alpha < 1 → 1 ≤ M →
            ∀ L ell : ℕ, ell ≤ L →
              lNaught C' (C' * M) alpha cStar nu K ≤ (ell : ℝ) →
              (L : ℝ) - M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (ell : ℝ) →
              |(sigmaBarInfinite nu ell P)⁻¹ * sigmaBarInfinite nu L P - 1| ≤
                  C' * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
                    Real.log (L : ℝ) ^ (3 : ℝ) ∧
                C' * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
                    Real.log (L : ℝ) ^ (3 : ℝ) ≤
                  (1 : ℝ) / 2 :=
    ⟨C, hC1, hSellGen C hCC0⟩
  obtain ⟨Cgrow, hCgrow1, hGrowUpperBody⟩ := sbAsm_growth_upper d hd hSellFactAtC
  set Cfinal : ℝ := max C Cgrow with hCfinaldef
  have hCCfinal : C ≤ Cfinal := le_max_left _ _
  have hCgrowCfinal : Cgrow ≤ Cfinal := le_max_right _ _
  have hCfinal1 : (1 : ℝ) ≤ Cfinal := le_trans hC1 hCCfinal
  have hCglowerCfinal : Cglower ≤ Cfinal := le_trans hCglower_C hCCfinal
  refine ⟨Cfinal, hCfinal1, hSellGen Cfinal (le_trans hCC0 hCCfinal), ?_⟩
  intro nu hnu hnu1 cStar hcStar K
  obtain ⟨Lg1, hGlowerL⟩ := hGlowerBody nu hnu hnu1 cStar hcStar K
  obtain ⟨Lg2, hGrowUpperL⟩ := hGrowUpperBody nu hnu hnu1 cStar hcStar K
  refine ⟨max Lg1 Lg2, ?_⟩
  intro P hPrefix hJ2 hJ3 hJ1V2 hJ4 hJ5 L hLg
  have hLgL1 : Lg1 ≤ L := le_trans (le_max_left _ _) hLg
  have hLgL2 : Lg2 ≤ L := le_trans (le_max_right _ _) hLg
  have hLowerAtCglower := hGlowerL P hPrefix hJ2 hJ3 hJ1V2 hJ4 hJ5 L hLgL1
  have hUpperAtCgrow := hGrowUpperL P hPrefix hJ2 hJ3 hJ1V2 hJ4 hJ5 L hLgL2
  have hCglowerpos : (0 : ℝ) < Cglower := lt_of_lt_of_le one_pos hCglower1
  have hCfinalpos : (0 : ℝ) < Cfinal := lt_of_lt_of_le one_pos hCfinal1
  have hCgrowpos : (0 : ℝ) < Cgrow := lt_of_lt_of_le one_pos hCgrow1
  have hcoefnn : (0 : ℝ) ≤ cStar ^ ((3 : ℝ) / 2) * nu ^ (2 : ℝ) * (L : ℝ) ^ ((1 : ℝ) / 2) *
      Real.log (L : ℝ) ^ (-((9 : ℝ) / 2)) := by
    have h1 : (0 : ℝ) ≤ cStar ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hcStar.le _
    have h2 : (0 : ℝ) ≤ nu ^ (2 : ℝ) := Real.rpow_nonneg hnu.le _
    have h3 : (0 : ℝ) ≤ (L : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have h4 : (0 : ℝ) ≤ Real.log (L : ℝ) ^ (-((9 : ℝ) / 2)) :=
      Real.rpow_nonneg (Real.log_natCast_nonneg L) _
    have h12 := mul_nonneg h1 h2
    have h123 := mul_nonneg h12 h3
    exact mul_nonneg h123 h4
  refine ⟨?_, ?_⟩
  · have hinvle : Cfinal⁻¹ ≤ Cglower⁻¹ := by
      exact inv_anti₀ hCglowerpos hCglowerCfinal
    have h1 : Cfinal⁻¹ * (cStar ^ ((3 : ℝ) / 2) * nu ^ (2 : ℝ) * (L : ℝ) ^ ((1 : ℝ) / 2) *
        Real.log (L : ℝ) ^ (-((9 : ℝ) / 2))) ≤
        Cglower⁻¹ * (cStar ^ ((3 : ℝ) / 2) * nu ^ (2 : ℝ) * (L : ℝ) ^ ((1 : ℝ) / 2) *
          Real.log (L : ℝ) ^ (-((9 : ℝ) / 2))) :=
      mul_le_mul_of_nonneg_right hinvle hcoefnn
    have heq1 : Cfinal⁻¹ * cStar ^ ((3 : ℝ) / 2) * nu ^ (2 : ℝ) * (L : ℝ) ^ ((1 : ℝ) / 2) *
        Real.log (L : ℝ) ^ (-((9 : ℝ) / 2)) =
        Cfinal⁻¹ * (cStar ^ ((3 : ℝ) / 2) * nu ^ (2 : ℝ) * (L : ℝ) ^ ((1 : ℝ) / 2) *
          Real.log (L : ℝ) ^ (-((9 : ℝ) / 2))) := by ring
    have heq2 : Cglower⁻¹ * cStar ^ ((3 : ℝ) / 2) * nu ^ (2 : ℝ) * (L : ℝ) ^ ((1 : ℝ) / 2) *
        Real.log (L : ℝ) ^ (-((9 : ℝ) / 2)) =
        Cglower⁻¹ * (cStar ^ ((3 : ℝ) / 2) * nu ^ (2 : ℝ) * (L : ℝ) ^ ((1 : ℝ) / 2) *
          Real.log (L : ℝ) ^ (-((9 : ℝ) / 2))) := by ring
    rw [heq1]
    rw [heq2] at hLowerAtCglower
    exact le_trans h1 hLowerAtCglower
  · have hcoefnn2 : (0 : ℝ) ≤ cStar ^ (-((3 : ℝ) / 2)) * nu ^ (-(2 : ℝ)) * (L : ℝ) ^ ((1 : ℝ) / 2) *
        Real.log (L : ℝ) ^ ((9 : ℝ) / 2) := by
      have h1 : (0 : ℝ) ≤ cStar ^ (-((3 : ℝ) / 2)) := Real.rpow_nonneg hcStar.le _
      have h2 : (0 : ℝ) ≤ nu ^ (-(2 : ℝ)) := Real.rpow_nonneg hnu.le _
      have h3 : (0 : ℝ) ≤ (L : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      have h4 : (0 : ℝ) ≤ Real.log (L : ℝ) ^ ((9 : ℝ) / 2) := by
        exact Real.rpow_nonneg (Real.log_natCast_nonneg L) _
      have h12 := mul_nonneg h1 h2
      have h123 := mul_nonneg h12 h3
      exact mul_nonneg h123 h4
    have h1 : Cgrow * (cStar ^ (-((3 : ℝ) / 2)) * nu ^ (-(2 : ℝ)) * (L : ℝ) ^ ((1 : ℝ) / 2) *
        Real.log (L : ℝ) ^ ((9 : ℝ) / 2)) ≤
        Cfinal * (cStar ^ (-((3 : ℝ) / 2)) * nu ^ (-(2 : ℝ)) * (L : ℝ) ^ ((1 : ℝ) / 2) *
          Real.log (L : ℝ) ^ ((9 : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_right hCgrowCfinal hcoefnn2
    have heq1 : Cgrow * cStar ^ (-((3 : ℝ) / 2)) * nu ^ (-(2 : ℝ)) * (L : ℝ) ^ ((1 : ℝ) / 2) *
        Real.log (L : ℝ) ^ ((9 : ℝ) / 2) =
        Cgrow * (cStar ^ (-((3 : ℝ) / 2)) * nu ^ (-(2 : ℝ)) * (L : ℝ) ^ ((1 : ℝ) / 2) *
          Real.log (L : ℝ) ^ ((9 : ℝ) / 2)) := by ring
    have heq2 : Cfinal * cStar ^ (-((3 : ℝ) / 2)) * nu ^ (-(2 : ℝ)) * (L : ℝ) ^ ((1 : ℝ) / 2) *
        Real.log (L : ℝ) ^ ((9 : ℝ) / 2) =
        Cfinal * (cStar ^ (-((3 : ℝ) / 2)) * nu ^ (-(2 : ℝ)) * (L : ℝ) ^ ((1 : ℝ) / 2) *
          Real.log (L : ℝ) ^ ((9 : ℝ) / 2)) := by ring
    rw [heq2]
    rw [heq1] at hUpperAtCgrow
    exact le_trans hUpperAtCgrow h1

end

end SuperdiffusionCLT.Section4.SigmaBarComparison
