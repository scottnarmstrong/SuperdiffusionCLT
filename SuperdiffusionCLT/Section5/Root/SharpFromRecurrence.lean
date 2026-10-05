/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Frozen.Section4.SigmaBarCutoffComparison
public import SuperdiffusionCLT.Assumptions.ShellLaw.J5Consequences
public import SuperdiffusionCLT.Section5.Thresholds.SequenceReduction

@[expose] public section

open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)

namespace SuperdiffusionCLT.Section5

theorem sharp_lower_coeff {Cg cStar nu : ℝ} (hCg : 0 < Cg) (hc : 0 < cStar) (hnu : 0 < nu) :
    (max 1 (Cg * cStar ^ (-((3 : ℝ) / 2)) * nu ^ (-(2 : ℝ))))⁻¹ ≤
      Cg⁻¹ * cStar ^ ((3 : ℝ) / 2) * nu ^ (2 : ℝ) := by
  have hB : 0 < Cg * cStar ^ (-((3 : ℝ) / 2)) * nu ^ (-(2 : ℝ)) := by positivity
  have h1 : (max 1 (Cg * cStar ^ (-((3 : ℝ) / 2)) * nu ^ (-(2 : ℝ))))⁻¹ ≤
      (Cg * cStar ^ (-((3 : ℝ) / 2)) * nu ^ (-(2 : ℝ)))⁻¹ :=
    inv_anti₀ hB (le_max_right _ _)
  refine h1.trans (le_of_eq ?_)
  rw [Real.rpow_neg hc.le, Real.rpow_neg hnu.le, mul_inv, mul_inv, inv_inv, inv_inv]

/-- `t.sstar.sharp.bounds` from the approximate recurrence `p.one.step.sharp`, the
sequence reduction and the Section 4 growth bound; `M` is chosen before the law. -/
theorem sigmaBar_sharp_bounds_of_recurrence (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hRec :
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
                                (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu n P)⁻¹) :
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
                      C * cStar⁻¹ * (Real.log (m : ℝ) ^ (2 : ℝ) + K)
:= by
  obtain ⟨Cr, hCr, hrec⟩ := hRec
  obtain ⟨Chat, hChat, hred⟩ := SuperdiffusionCLT.Section5.sharp_of_recurrence Cr hCr
  obtain ⟨Cg, hCg, -, hgrowth⟩ :=
    SuperdiffusionCLT.Frozen.Section4.sigmaBar_cutoff_comparison d hd
  refine ⟨Chat, hChat, fun nu hnu hnu1 cStar hc K => ?_⟩
  obtain ⟨Lg, hLg⟩ := hgrowth nu hnu hnu1 cStar hc K
  obtain ⟨Mp, hMp⟩ := hrec nu hnu hnu1 cStar hc K
  set A : ℝ := max 1 (Cg * cStar ^ (-((3 : ℝ) / 2)) * nu ^ (-(2 : ℝ))) with hAdef
  by_cases hcK : cStar ≤ 2 ∧ 0 ≤ K
  · obtain ⟨M, hM⟩ := hred cStar K A hc hcK.1 hcK.2 (lt_of_lt_of_le one_pos (le_max_left _ _)) Lg Mp
    refine ⟨M, fun P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 m hm => ?_⟩
    refine hM (fun n => sigmaBarInfinite nu n P) (fun n hn => ?_)
      (fun n hn h h1 hh => hMp P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 n hn h h1 hh) m hm
    obtain ⟨hlo, hhi⟩ := hLg P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 n hn
    have hw : 0 ≤ (n : ℝ) ^ ((1 : ℝ) / 2) * Real.log (n : ℝ) ^ (-((9 : ℝ) / 2)) := by
      have := Real.log_natCast_nonneg n
      positivity
    have hw' : 0 ≤ (n : ℝ) ^ ((1 : ℝ) / 2) * Real.log (n : ℝ) ^ ((9 : ℝ) / 2) := by
      have := Real.log_natCast_nonneg n
      positivity
    have hCg0 : 0 < Cg := lt_of_lt_of_le one_pos hCg
    constructor
    · calc A⁻¹ * (n : ℝ) ^ ((1 : ℝ) / 2) * Real.log (n : ℝ) ^ (-((9 : ℝ) / 2))
          = A⁻¹ * ((n : ℝ) ^ ((1 : ℝ) / 2) * Real.log (n : ℝ) ^ (-((9 : ℝ) / 2))) := by ring
        _ ≤ (Cg⁻¹ * cStar ^ ((3 : ℝ) / 2) * nu ^ (2 : ℝ)) *
              ((n : ℝ) ^ ((1 : ℝ) / 2) * Real.log (n : ℝ) ^ (-((9 : ℝ) / 2))) :=
            mul_le_mul_of_nonneg_right (sharp_lower_coeff hCg0 hc hnu) hw
        _ = _ := by ring
        _ ≤ _ := hlo
    · calc sigmaBarInfinite nu n P ≤ _ := hhi
        _ = (Cg * cStar ^ (-((3 : ℝ) / 2)) * nu ^ (-(2 : ℝ))) *
              ((n : ℝ) ^ ((1 : ℝ) / 2) * Real.log (n : ℝ) ^ ((9 : ℝ) / 2)) := by ring
        _ ≤ A * ((n : ℝ) ^ ((1 : ℝ) / 2) * Real.log (n : ℝ) ^ ((9 : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) hw'
        _ = _ := by ring
  · refine ⟨0, fun P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 m _ => ?_⟩
    exact absurd ⟨hJ5.cStar_le_two, hJ5.K_pos.le⟩ hcK

end SuperdiffusionCLT.Section5
