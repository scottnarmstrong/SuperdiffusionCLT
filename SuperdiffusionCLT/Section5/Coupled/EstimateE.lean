/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Coupled.EstimateD

/-!
# `lem.coupled.input`: the lemma

`coupled_input` is the printed display `e.coupled.estimate.explicit` in the shape consumed by
`cor.lower.ratio`: the scale hypothesis is `2 L₀ ≤ m`, the response family is any selection of the
Dirichlet response on every cube `cu_Kc`, `Kc ≥ 100 m`, and the conclusion is a `limsup` over `Kc`.
The only law hypotheses are the shell laws `Prefix`, `J2`, `J3`, `J1V2`, `J4`, `J5`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open MeasureTheory Homogenization Filter Topology
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)
open SuperdiffusionCLT.Section3.ResponseFields (vecCubeLpENorm)
open scoped ENNReal

variable {d : ℕ}

theorem coupled4_rpow_neg_two {σ : ℝ} (hσ : 0 < σ) : σ ^ (-(2 : ℝ)) = (σ⁻¹) ^ 2 := by
  rw [Real.rpow_neg hσ.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, inv_pow]

theorem coupled4_rpow_neg_four {σ : ℝ} (hσ : 0 < σ) : σ ^ (-(4 : ℝ)) = (σ⁻¹) ^ 4 := by
  rw [Real.rpow_neg hσ.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, inv_pow]

/-- From `X^{1/2} ≤ r` to `X ≤ r²`. -/
theorem coupled4_sq_of_sqrt_le {X : ℝ≥0∞} {r : ℝ} (hr : 0 ≤ r)
    (h : X ^ ((1 : ℝ) / 2) ≤ ENNReal.ofReal r) : X ≤ ENNReal.ofReal (r ^ 2) := by
  have h1 := ENNReal.rpow_le_rpow h (show (0 : ℝ) ≤ 2 by norm_num)
  rw [← ENNReal.rpow_mul, ENNReal.ofReal_rpow_of_nonneg hr (by norm_num), Real.rpow_two] at h1
  simpa using h1

/-- The scale facts of `2 L₀ ≤ m`: `1000000 ≤ m`, `ν⁻¹ ≤ m`, `σ ≤ Ce m²`. -/
theorem coupled4_scales (d : ℕ) [NeZero d] :
    ∃ C₀ Ce : ℝ, 1 ≤ C₀ ∧ 1 ≤ Ce ∧ ∀ (nu cStar K : ℝ), 0 < nu → nu ≤ 1 →
      ∀ (P : ProbabilityMeasure (ShellSeq d)) (hPrefix : ShellLawPrefix d P)
        (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P),
        ShellLawJ4 d P → ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
        ∀ m h : ℕ, 1 ≤ h → 400 * h ≤ m →
        2 * SuperdiffusionCLT.Frozen.Section4.lNaught C₀ C₀ (3 / 4) cStar nu K ≤ (m : ℝ) →
        1000000 ≤ m ∧ nu⁻¹ ≤ (m : ℝ) ∧ sigmaBarInfinite nu (m - h) P ≤ Ce * (m : ℝ) * m := by
  obtain ⟨Cml, hCml, Hml⟩ := m_large_of_lNaught
  obtain ⟨Cge, -, Hge⟩ := SuperdiffusionCLT.Section4.LNaught.lNaught_ge
  set Ce : ℝ := 1 + 2 * SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst d with hCe
  have hCe1 : 1 ≤ Ce := by
    have := SuperdiffusionCLT.Section2.Annealed.one_le_cutoffEnvelopeConst d; rw [hCe]; linarith only [this]
  refine ⟨max Cml Cge, Ce, le_trans (by linarith only [hCml]) (le_max_left _ _), hCe1, ?_⟩
  intro nu cStar K hnu hnu1 P hPre hJ2 hJ3 hJ4 hJ5 m h hh h400 hm
  have hCm : Cml ≤ max Cml Cge := le_max_left _ _
  have hCg : Cge ≤ max Cml Cge := le_max_right _ _
  have hcStar := hJ5.cStar_pos
  have hcStar2 := hJ5.cStar_le_two
  have hK := hJ5.K_pos.le
  have h8 := Hge (max Cml Cge) hCg (max Cml Cge) (by linarith only [hCm, hCml]) (3 / 4)
    (by norm_num) (by norm_num) cStar hcStar hcStar2 nu hnu hnu1 K hK
  obtain ⟨hm4, hnu16⟩ := Hml (max Cml Cge) hCm cStar hcStar hcStar2 nu hnu hnu1 K hK m
    (by linarith only [hm, h8])
  have hC8 : (125 : ℝ) ≤ max Cml Cge / 8 := by linarith only [hCm, hCml]
  have hmR : (1000000 : ℝ) ≤ m := by
    have : (125 : ℝ) ^ 4 ≤ (max Cml Cge / 8) ^ 4 := pow_le_pow_left₀ (by norm_num) hC8 4
    norm_num at this
    linarith only [this, hm4]
  have hinv1 : 1 ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
  have hinvm : nu⁻¹ ≤ (m : ℝ) := le_trans (le_self_pow₀ hinv1 (by norm_num)) hnu16
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have h400r : 400 * (h : ℝ) ≤ m := by exact_mod_cast h400
  have hhm : h ≤ m := by omega
  have hLr : (((m - h : ℕ)) : ℝ) = m - h := by rw [Nat.cast_sub hhm]
  have hcrude := sigmaBarInfinite_crude d hnu hnu1 (m - h) hPre hJ2 hJ3 hJ4
  refine ⟨by exact_mod_cast hmR, hinvm, ?_⟩
  have h1 : max 1 (((m - h : ℕ)) : ℝ) ≤ m := by
    refine max_le (by linarith only [hmR]) ?_
    rw [hLr]; linarith only [hh1]
  calc sigmaBarInfinite nu (m - h) P ≤ Ce * nu⁻¹ * max 1 (((m - h : ℕ)) : ℝ) := hcrude
    _ ≤ Ce * m * m := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hinvm (by linarith only [hCe1])) h1
        (by positivity) (by positivity)

end SuperdiffusionCLT.Section5
