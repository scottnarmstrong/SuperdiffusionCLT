/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.SigmaBarComparison.NearAdditivityB
public import SuperdiffusionCLT.Section4.SigmaBarComparison.NearAdditivityD5

/-!
# `sbNear_goodNB` / `sbNear_goodN_closedB`: `hHomogPair`'s threshold weakened

The near-additivity reduction of `hGoodN` (`NearAdditivityB.lean`) would carry
`hHomogPair`'s `∀ Cthresh : ℝ, 1 ≤ Cthresh →
...` verbatim into its own conclusion. `hHomogPair` reads off
`p.homog.below`'s pair comparison from the `homogenization_below_cutoff`
body (`HomogPairOfHomog.lean`'s `sbHomogPair_of_homog`), whose own threshold
`C0` depends on `homogenization_below_cutoff`'s opaque witness constant and so
can only be guaranteed `≥ C0(d)` for some `C0`, not `≥ 1` outright. This file
weakens `hHomogPair` (and the matching conclusion) to
`∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ Cthresh : ℝ, C0 ≤ Cthresh → ...`, exactly the shape
`sbIndep_mainB`'s `hGoodN` (`IndependenceRatioF.lean`) expects.

`hNearAdd` is UNCHANGED: `sbNear_nearAdd` is proved for every `Cthresh ≥ 1`
(`NearAdditivityD5.lean`), which restricts trivially to `Cthresh ≥ C0` once
`1 ≤ C0` — no new proof content there, just `le_trans`. -/

@[expose] public section

namespace SuperdiffusionCLT.Section4.SigmaBarComparison

open MeasureTheory Homogenization
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed

noncomputable section

variable {d : ℕ} [NeZero d]

/-- **`sbNear_goodNB`**: the reduction of `hGoodN` with `hHomogPair`'s threshold weakened
to `∃ C0, 1 ≤ C0 ∧ ∀ Cthresh ≥ C0, ...`, and the conclusion weakened to
match. -/
theorem sbNear_goodNB (d : ℕ) [NeZero d]
    (hNearAdd : ∃ Cnear : ℝ, 1 ≤ Cnear ∧
      ∀ (nu cStar K : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : ProbabilityMeasure (ShellSeq d))
          (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P),
          ShellLawJ1Restriction d P → ShellLawJ4 d P → ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
          ∀ alpha M : ℝ, 0 ≤ alpha → alpha < 1 → 1 ≤ M →
            ∀ Cthresh : ℝ, 1 ≤ Cthresh →
            ∀ L ell : ℕ, ell < L →
              SuperdiffusionCLT.Frozen.Section4.lNaught Cthresh (Cthresh * M) alpha cStar nu K ≤
                  (ell : ℝ) →
              (L : ℝ) - M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (ell : ℝ) →
                |sigmaBarSeq nu L P (sbNear_witness ell L) -
                      sigmaBarSeq nu ell P (sbNear_witness ell L) -
                      (∫ omega, sbIndep_quadTerm (d := d) nu ell L (sbNear_witness ell L) omega
                        ∂P.toMeasure) -
                      (∫ omega, sbIndep_crossTerm (d := d) nu ell L (sbNear_witness ell L) omega
                        ∂P.toMeasure)| ≤
                  Cnear * (L : ℝ) ^ (-(99 : ℝ)))
    (hHomogPair : ∃ C2 C0 : ℝ, 1 ≤ C2 ∧ 1 ≤ C0 ∧
      ∀ (nu cStar K : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : ProbabilityMeasure (ShellSeq d))
          (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P),
          ShellLawJ1Restriction d P → ShellLawJ4 d P → ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
          ∀ alpha M : ℝ, 0 ≤ alpha → alpha < 1 → 1 ≤ M →
            ∀ Cthresh : ℝ, C0 ≤ Cthresh →
            ∀ L ell : ℕ, ell < L →
              SuperdiffusionCLT.Frozen.Section4.lNaught Cthresh (Cthresh * M) alpha cStar nu K ≤
                  (ell : ℝ) →
              (L : ℝ) - M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (ell : ℝ) →
                (sigmaBarStarInvScalar nu ell P
                    (cubeSet (originCube d (sbNear_witness ell L : ℤ))) ≤
                  C2 * (sigmaBarInfinite nu ell P)⁻¹) ∧
                ((7 / 8 : ℝ) * sigmaBarInfinite nu ell P ≤
                  sigmaBarSeq nu ell P (sbNear_witness ell L))) :
    ∃ Cnear C2 C0 : ℝ, 1 ≤ Cnear ∧ 1 ≤ C2 ∧ 1 ≤ C0 ∧
      ∀ (nu cStar K : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : ProbabilityMeasure (ShellSeq d))
          (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P),
          ShellLawJ1Restriction d P → ShellLawJ4 d P → ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
          ∀ alpha M : ℝ, 0 ≤ alpha → alpha < 1 → 1 ≤ M →
            ∀ Cthresh : ℝ, C0 ≤ Cthresh →
            ∀ L ell : ℕ, ell < L →
              SuperdiffusionCLT.Frozen.Section4.lNaught Cthresh (Cthresh * M) alpha cStar nu K ≤
                  (ell : ℝ) →
              (L : ℝ) - M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (ell : ℝ) →
              ∃ n : ℕ,
                (|sigmaBarSeq nu L P n - sigmaBarSeq nu ell P n -
                      (∫ omega, sbIndep_quadTerm (d := d) nu ell L n omega ∂P.toMeasure) -
                      (∫ omega, sbIndep_crossTerm (d := d) nu ell L n omega ∂P.toMeasure)| ≤
                    Cnear * (L : ℝ) ^ (-(99 : ℝ))) ∧
                (∀ k l : Fin d, Integrable (fun omega => sbIndep_hMat (d := d) ell L n omega k 0 *
                  sbIndep_sInvMat (d := d) nu ell n omega k l *
                  sbIndep_hMat (d := d) ell L n omega l 0) P.toMeasure) ∧
                (0 ≤ sigmaBarStarInvScalar nu ell P (cubeSet (originCube d (n : ℤ)))) ∧
                (sigmaBarStarInvScalar nu ell P (cubeSet (originCube d (n : ℤ))) ≤
                  C2 * (sigmaBarInfinite nu ell P)⁻¹) ∧
                ((7 / 8 : ℝ) * sigmaBarInfinite nu ell P ≤ sigmaBarSeq nu ell P n) ∧
                (n ≤ ell) ∧
                ((ell : ℝ) - (n : ℝ) ≤ 200 * Real.log (L : ℝ) + 1) := by
  obtain ⟨Cnear, hCnear1, hNear⟩ := hNearAdd
  obtain ⟨C2, C0, hC21, hC01, hHomog⟩ := hHomogPair
  refine ⟨Cnear, C2, C0, hCnear1, hC21, hC01, ?_⟩
  intro nu cStar K hnu hnu1 P hPrefix hJ2 hJ3 hJ1V2 hJ4 hJ5 alpha M hα0 hα1 hM Cthresh hCthresh
    L ell hlt hLnaught hscale
  have hCthresh1 : (1 : ℝ) ≤ Cthresh := le_trans hC01 hCthresh
  have hHomogAt := hHomog nu cStar K hnu hnu1 P hPrefix hJ2 hJ3 hJ1V2 hJ4 hJ5 alpha M hα0 hα1 hM
    Cthresh hCthresh L ell hlt hLnaught hscale
  exact ⟨sbNear_witness ell L,
    hNear nu cStar K hnu hnu1 P hPrefix hJ2 hJ3 hJ1V2 hJ4 hJ5 alpha M hα0 hα1 hM Cthresh hCthresh1
      L ell hlt hLnaught hscale,
    fun k l => sbNear_hCI3 hnu hPrefix hJ2 hJ3 hJ4 hlt (sbNear_witness ell L) k l,
    sbNear_sigmaBarStarInvScalar_nonneg hnu hPrefix hJ2 hJ3 hJ4 ell (sbNear_witness ell L),
    hHomogAt.1, hHomogAt.2, sbNear_witness_le ell L, sbNear_witness_gap_le ell L⟩

/-- **`sbNear_goodNB` with near-additivity discharged**: `hGoodN` of
`sbIndep_mainB` (`IndependenceRatioF.lean`) from the weakened `p.homog.below`
pair comparison `hHomogPair` alone. -/
theorem sbNear_goodN_closedB (d : ℕ) [NeZero d]
    (hHomogPair : ∃ C2 C0 : ℝ, 1 ≤ C2 ∧ 1 ≤ C0 ∧
      ∀ (nu cStar K : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : ProbabilityMeasure (ShellSeq d))
          (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P),
          ShellLawJ1Restriction d P → ShellLawJ4 d P → ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
          ∀ alpha M : ℝ, 0 ≤ alpha → alpha < 1 → 1 ≤ M →
            ∀ Cthresh : ℝ, C0 ≤ Cthresh →
            ∀ L ell : ℕ, ell < L →
              SuperdiffusionCLT.Frozen.Section4.lNaught Cthresh (Cthresh * M) alpha cStar nu K ≤
                  (ell : ℝ) →
              (L : ℝ) - M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (ell : ℝ) →
                (sigmaBarStarInvScalar nu ell P
                    (cubeSet (originCube d (sbNear_witness ell L : ℤ))) ≤
                  C2 * (sigmaBarInfinite nu ell P)⁻¹) ∧
                ((7 / 8 : ℝ) * sigmaBarInfinite nu ell P ≤
                  sigmaBarSeq nu ell P (sbNear_witness ell L))) :
    ∃ Cnear C2 C0 : ℝ, 1 ≤ Cnear ∧ 1 ≤ C2 ∧ 1 ≤ C0 ∧
      ∀ (nu cStar K : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : ProbabilityMeasure (ShellSeq d))
          (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P),
          ShellLawJ1Restriction d P → ShellLawJ4 d P → ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
          ∀ alpha M : ℝ, 0 ≤ alpha → alpha < 1 → 1 ≤ M →
            ∀ Cthresh : ℝ, C0 ≤ Cthresh →
            ∀ L ell : ℕ, ell < L →
              SuperdiffusionCLT.Frozen.Section4.lNaught Cthresh (Cthresh * M) alpha cStar nu K ≤
                  (ell : ℝ) →
              (L : ℝ) - M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (ell : ℝ) →
              ∃ n : ℕ,
                (|sigmaBarSeq nu L P n - sigmaBarSeq nu ell P n -
                      (∫ omega, sbIndep_quadTerm (d := d) nu ell L n omega ∂P.toMeasure) -
                      (∫ omega, sbIndep_crossTerm (d := d) nu ell L n omega ∂P.toMeasure)| ≤
                    Cnear * (L : ℝ) ^ (-(99 : ℝ))) ∧
                (∀ k l : Fin d, Integrable (fun omega => sbIndep_hMat (d := d) ell L n omega k 0 *
                  sbIndep_sInvMat (d := d) nu ell n omega k l *
                  sbIndep_hMat (d := d) ell L n omega l 0) P.toMeasure) ∧
                (0 ≤ sigmaBarStarInvScalar nu ell P (cubeSet (originCube d (n : ℤ)))) ∧
                (sigmaBarStarInvScalar nu ell P (cubeSet (originCube d (n : ℤ))) ≤
                  C2 * (sigmaBarInfinite nu ell P)⁻¹) ∧
                ((7 / 8 : ℝ) * sigmaBarInfinite nu ell P ≤ sigmaBarSeq nu ell P n) ∧
                (n ≤ ell) ∧
                ((ell : ℝ) - (n : ℝ) ≤ 200 * Real.log (L : ℝ) + 1) :=
  sbNear_goodNB d (sbNear_nearAdd d) hHomogPair

end

end SuperdiffusionCLT.Section4.SigmaBarComparison
