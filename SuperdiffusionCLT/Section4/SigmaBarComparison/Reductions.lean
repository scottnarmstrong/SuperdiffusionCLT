/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.LocalizationUnconditional
public import SuperdiffusionCLT.Frozen.Section3.SstarLowerBound
public import SuperdiffusionCLT.Frozen.Section4.LNaught

/-!
# Scalar inputs for the cutoff comparison

This module records the scalar consequences of the localization and
root lower-bound results, and separates the two errors in the
homogenization-below-cutoff estimate. These are the local inputs to the
comparison of the infinite-volume diffusivities.
-/

@[expose] public section

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Assumptions

namespace SuperdiffusionCLT.Section4.SigmaBarComparison

noncomputable section

/-- The root lower bound transfers from its finite origin cube to the
infinite-volume scalar. -/
theorem sbComp_root_lower_bound_infinite (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧
      ∀ (nu cStar K : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : ProbabilityMeasure (ShellSeq d))
          (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P),
          ShellLawJ1Restriction d P → ShellLawJ4 d P → ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
          ∀ L m : ℕ, m ≤ L → L ≤ 2 * m →
            C * cStar ^ (-(3 : ℝ)) *
                (Real.log (3 + nu⁻¹ + cStar⁻¹) ^ 3 *
                    Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹)) +
                  (1 + K) * Real.log (3 + nu⁻¹ + cStar⁻¹ + K)) ≤ (m : ℝ) →
            c * cStar ^ ((3 : ℝ) / 2) * nu ^ (2 : ℝ) * (m : ℝ) ^ ((1 : ℝ) / 2) *
                Real.log (nu⁻¹ * (m : ℝ)) ^ (-((9 : ℝ) / 2)) ≤
              SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu L P := by
  rcases SuperdiffusionCLT.Frozen.Section3.sigmaBarStar_lower_bound d hd with
    ⟨C, hC, c, hc, hcHalf, hRoot⟩
  refine ⟨C, hC, c, hc, hcHalf, ?_⟩
  intro nu cStar K hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 L m hmL hL2 hthreshold
  have hroot := hRoot nu cStar K hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
    L m hmL hL2 hthreshold
  exact le_trans hroot.1.2 hroot.1.1

end

end SuperdiffusionCLT.Section4.SigmaBarComparison
