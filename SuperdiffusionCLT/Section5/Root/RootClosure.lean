/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Thresholds.OneStepFromCorollaries
public import SuperdiffusionCLT.Section5.Root.SharpFromRecurrence
public import SuperdiffusionCLT.Section5.Corollary.UpperRatioE
public import SuperdiffusionCLT.Section5.Corollary.LowerRatioH

/-!
# Section 5 root closure

`p.one.step.sharp` from the two ratio corollaries, and `t.sstar.sharp.bounds` from the recurrence.
The statements are those of the corresponding declarations in `Frozen.Section5`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

/-- `p.one.step.sharp`: the approximate recurrence for `σ̄`. -/
theorem sigmaBar_approximate_recurrence_closed
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
        ∀ cStar : ℝ, 0 < cStar →
          ∀ K : ℝ,
            ∃ M : ℕ,
              ∀ (P : MeasureTheory.ProbabilityMeasure
                    (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
                (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
                (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
                (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K
                    hPrefix hJ2 hJ3 →
                  ∀ n : ℕ, M ≤ n →
                    ∀ h : ℕ, 1 ≤ h →
                      (h : ℝ) ≤ SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu n P →
                        |SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu (n + h) P -
                            SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu n P -
                            cStar * Real.log 3 *
                              (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu n P)⁻¹ *
                                (h : ℝ)| ≤
                          C * (Real.log (n : ℝ) ^ (2 : ℝ) + K) *
                            (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu n P)⁻¹ :=
  sigmaBar_one_step_of_corollaries d hd (upper_ratio d hd) (lower_ratio d hd)

/-- `t.sstar.sharp.bounds`: the sharp bounds for `σ̄`. -/
theorem sigmaBar_sharp_bounds_closed
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
        ∀ cStar : ℝ, 0 < cStar →
          ∀ K : ℝ,
            ∃ M : ℕ,
              ∀ (P : MeasureTheory.ProbabilityMeasure
                    (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
                (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
                (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
                (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K
                    hPrefix hJ2 hJ3 →
                  ∀ m : ℕ, M ≤ m →
                    |SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P -
                        (2 * cStar * Real.log 3 * (m : ℝ)) ^ ((1 : ℝ) / 2)| ≤
                      C * cStar⁻¹ * (Real.log (m : ℝ) ^ (2 : ℝ) + K) :=
  sigmaBar_sharp_bounds_of_recurrence d hd (sigmaBar_approximate_recurrence_closed d hd)

end SuperdiffusionCLT.Section5
