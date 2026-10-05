/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.SigmaBarComparison.NearAdditivityD3
public import SuperdiffusionCLT.Section4.SigmaBarComparison.NearAdditivityD4
public import SuperdiffusionCLT.Assumptions.ShellLaw.J5Consequences

/-!
# Near-additivity, closed

Near-additivity in the proof of `l.localization`: at the witness
`n = ell - ⌈200 log L⌉`,

`|σ̄_L(cu_n) - σ̄_ell(cu_n) - E[h^t s^{-1} h] - E[cross]| ≤ C L^{-99}`.

`sbNear_nearAdd` is the exact `hNearAdd` input of `sbNear_goodNB`
(`NearAdditivityD6.lean`), proved from the standing shell laws: the first-moment
bound `sbNear_abs_le_moment` (`NearAdditivityD3.lean`) and the scale
arithmetic `sbNear_absorb_arith` (`NearAdditivityD4.lean`).
`sbNear_goodN_closedB` (`NearAdditivityD6.lean`) is `sbNear_goodNB` with that input discharged.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.SigmaBarComparison

open MeasureTheory Homogenization
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed

noncomputable section

/-- The near-additivity constant. -/
def sbNear_Cnear (d : ℕ) : ℝ :=
  max 1 (IndependentSums.gammaMomentConst ((1 : ℝ) / 3) *
    SuperdiffusionCLT.Section2.Localization.localizationAveragePrintedT1Const d * sbNear_B)

/-- **Near-additivity** (proof of `l.localization`), the exact `hNearAdd` input of
`sbNear_goodNB`. -/
theorem sbNear_nearAdd (d : ℕ) [NeZero d] :
    ∃ Cnear : ℝ, 1 ≤ Cnear ∧
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
                  Cnear * (L : ℝ) ^ (-(99 : ℝ)) := by
  refine ⟨sbNear_Cnear d, le_max_left _ _, ?_⟩
  intro nu cStar K hnu hnu1 P hPrefix hJ2 hJ3 _ hJ4 hJ5 alpha M hα0 hα1 hM Cthresh hCthresh
    L ell hlt hLnaught hscale
  have hmom := sbNear_abs_le_moment hnu hnu1 hPrefix hJ2 hJ3 hJ4 hlt
    (sbNear_witness_le ell L)
  have harith := sbNear_absorb_arith hCthresh hM hα0 hα1 hJ5.cStar_pos hJ5.cStar_le_two hnu
    hnu1 hJ5.K_pos.le hlt hLnaught hscale (sbNear_witness ell L) rfl
  have hG : 0 ≤ IndependentSums.gammaMomentConst ((1 : ℝ) / 3) :=
    (IndependentSums.gammaMomentConst_pos (by norm_num)).le
  have hPT : 0 ≤ SuperdiffusionCLT.Section2.Localization.localizationAveragePrintedT1Const d :=
    sbNear_printedT1Const_pos.le
  have hL99 : 0 ≤ (L : ℝ) ^ (-(99 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine hmom.trans ?_
  calc IndependentSums.gammaMomentConst ((1 : ℝ) / 3) *
        (SuperdiffusionCLT.Section2.Localization.localizationAveragePrintedT1Const d *
          nu ^ (-(3 : ℝ)) * ((L : ℝ) * (3 : ℝ) ^ (-((ell - sbNear_witness ell L : ℕ) : ℝ))))
      = IndependentSums.gammaMomentConst ((1 : ℝ) / 3) *
          SuperdiffusionCLT.Section2.Localization.localizationAveragePrintedT1Const d *
          (nu ^ (-(3 : ℝ)) * ((L : ℝ) * (3 : ℝ) ^ (-((ell - sbNear_witness ell L : ℕ) : ℝ)))) := by
        ring
    _ ≤ IndependentSums.gammaMomentConst ((1 : ℝ) / 3) *
          SuperdiffusionCLT.Section2.Localization.localizationAveragePrintedT1Const d *
          (sbNear_B * (L : ℝ) ^ (-(99 : ℝ))) :=
        mul_le_mul_of_nonneg_left harith (mul_nonneg hG hPT)
    _ = (IndependentSums.gammaMomentConst ((1 : ℝ) / 3) *
          SuperdiffusionCLT.Section2.Localization.localizationAveragePrintedT1Const d *
          sbNear_B) * (L : ℝ) ^ (-(99 : ℝ)) := by ring
    _ ≤ sbNear_Cnear d * (L : ℝ) ^ (-(99 : ℝ)) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hL99

end

end SuperdiffusionCLT.Section4.SigmaBarComparison
