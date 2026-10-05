/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.SstarFinal
public import SuperdiffusionCLT.Frozen.Section3.RHSTerm3

/-!
# The suboptimal lower bound, without further hypotheses

`sstar_closed` is `sstarFinal_main` with its one input, the term-3
proposition, supplied by `rhs_term3_constFirst`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open scoped ENNReal

/-- The conclusion of `sigmaBarStar_lower_bound`, with no further hypotheses. -/
theorem sstar_closed (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧
      ∀ (nu cStar K : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : MeasureTheory.ProbabilityMeasure
          (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
          (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
          (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
          (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K
              hPrefix hJ2 hJ3 →
          ∀ L m : ℕ, m ≤ L → L ≤ 2 * m →
            C * cStar ^ (-(3 : ℝ)) *
                (Real.log (3 + nu⁻¹ + cStar⁻¹) ^ 3 *
                    Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹)) +
                  (1 + K) * Real.log (3 + nu⁻¹ + cStar⁻¹ + K)) ≤ (m : ℝ) →
            (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
                  (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ))) ≤
                SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu L P ∧
              c * cStar ^ ((3 : ℝ) / 2) * nu ^ (2 : ℝ) * (m : ℝ) ^ ((1 : ℝ) / 2) *
                    Real.log (nu⁻¹ * (m : ℝ)) ^ (-((9 : ℝ) / 2)) ≤
                SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
                  (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))) ∧
            ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
              Measurable X ∧
              Homogenization.IndependentSums.IsBigO P.toMeasure
                  (Homogenization.IndependentSums.gammaSigma 2) X
                  (C * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-((m : ℝ) / 8))) ∧
                ∀ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
                  Homogenization.MatLoewnerLE
                    (Homogenization.sigmaStarInvCoarse
                      (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))
                      (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu
                          omega L).toCoeffField)
                    ((C * nu ^ (-(2 : ℝ)) * cStar ^ (-((3 : ℝ) / 2)) *
                            (m : ℝ) ^ (-((1 : ℝ) / 2)) *
                            Real.log (nu⁻¹ * (m : ℝ)) ^ ((9 : ℝ) / 2)) •
                        (1 : Homogenization.Mat d) +
                      X omega • (1 : Homogenization.Mat d)) :=
  sstarFinal_main d hd (SuperdiffusionCLT.Frozen.Section3.rhs_term3_constFirst d hd)

end SuperdiffusionCLT.Section3.Terms
