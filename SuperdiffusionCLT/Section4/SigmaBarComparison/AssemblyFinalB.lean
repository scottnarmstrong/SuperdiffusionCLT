/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.SigmaBarComparison.AssemblyFinal
public import SuperdiffusionCLT.Section4.SigmaBarComparison.NearAdditivityD6
public import SuperdiffusionCLT.Section4.SigmaBarComparison.HomogPairOfHomog
public import SuperdiffusionCLT.Section4.SigmaBarComparison.IndependenceRatioF

/-!
# `sbAsm_mainB`: `sigmaBar_cutoff_comparison` from `hHomog` alone

`sbAsm_main` (`AssemblyFinal.lean`) proves the body of `sigmaBar_cutoff_comparison`
from `hHomog` (the body of `homogenization_below_cutoff`) AND
`hIndep` (the conclusion of `sbIndep_mainB`) as two SEPARATE hypotheses. This file
derives `hIndep` from `hHomog` alone, closing the gap between the hypotheses
`hGoodN`/`hHomogPair` (quantified `∀ Cthresh ≥ 1`, stronger than what
`sbIndep_mainB` consumes and stronger than what `hHomog`'s own opaque
threshold constant can supply): chain

* `sbHomogPair_of_homog` (`HomogPairOfHomog.lean`): `hHomog` → `hHomogPair`
  (the weakened `∃ C0, ∀ Cthresh ≥ C0` form);
* `sbNear_goodN_closedB` (`NearAdditivityD6.lean`): `hHomogPair` → `hGoodN`
  (feeding `sbNear_nearAdd`, proved for all `Cthresh ≥ 1`, alongside it);
* `sbIndep_absorption_le_eighth` (`IndependenceRatioC.lean`, `hd : 2 ≤ d`
  only): → `hAbsorb`;
* `sbIndep_mainB` (`IndependenceRatioF.lean`): `hGoodN`, `hAbsorb` → `hIndep`;
* `sbAsm_main` (`AssemblyFinal.lean`): `hHomog`, `hIndep` → `sigmaBar_cutoff_comparison`.

So `sbAsm_mainB` needs only `hHomog` and `hd : 2 ≤ d` (the latter already an
implicit standing hypothesis throughout Section 4's `d`-dependent root). -/

@[expose] public section

namespace SuperdiffusionCLT.Section4.SigmaBarComparison

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section4 (lNaught)

noncomputable section

/-- **`sbAsm_mainB`**: `sigmaBar_cutoff_comparison`, from `hHomog` ALONE
(feeding `sbIndep_mainB`'s conclusion into `sbAsm_main`). -/
theorem sbAsm_mainB (d : ℕ) [NeZero d] (hd : 2 ≤ d)
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
  have hHomogPair := sbHomogPair_of_homog d hd hHomog
  have hGoodN := sbNear_goodN_closedB d hHomogPair
  have hAbsorb := sbIndep_absorption_le_eighth hd
  have hIndep := sbIndep_mainB d hGoodN hAbsorb
  exact sbAsm_main d hd hHomog hIndep

end

end SuperdiffusionCLT.Section4.SigmaBarComparison
