/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Principal.AssemblyD
public import SuperdiffusionCLT.Section5.Thresholds.LVsLnaughtAgain
public import SuperdiffusionCLT.Section5.Thresholds.ScaleArithmetic

/-!
# Scale facts for the principal-term assembly

From `2 L₀(C, C, 3/4, c⋆, ν) ≤ m` (with `C` large), `1 ≤ h` and `400 h ≤ m`: `m ≥ 10^6`, `ν⁻¹ ≤ m`,
`ν⁻² ≤ m`, `m ≤ 2 n` and `n ≤ m - h` for the scale `n` of `e.n.def.recurrence`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open MeasureTheory Homogenization
open SuperdiffusionCLT.Frozen.Section4 (lNaught)
open scoped ENNReal

theorem pa_scale_facts :
    ∃ C₀ : ℝ, 1000 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∀ cStar : ℝ, 0 < cStar → cStar ≤ 2 →
      ∀ nu : ℝ, 0 < nu → nu ≤ 1 → ∀ K : ℝ, 0 ≤ K → ∀ m h n : ℕ, 1 ≤ h → 400 * h ≤ m →
        2 * lNaught C C (3 / 4) cStar nu K ≤ (m : ℝ) →
        n = ⌊(m : ℝ) - h - 100 * Real.logb 3 (nu⁻¹ * m)⌋₊ →
        (1000000 : ℝ) ≤ m ∧ nu⁻¹ ≤ (m : ℝ) ∧ nu⁻¹ ^ 2 ≤ (m : ℝ) ∧ m ≤ 2 * n ∧ n ≤ m - h := by
  obtain ⟨Cml, hCml, Hml⟩ := m_large_of_lNaught
  obtain ⟨Cge, -, Hge⟩ := SuperdiffusionCLT.Section4.LNaught.lNaught_ge
  refine ⟨max Cml Cge, le_trans hCml (le_max_left _ _), ?_⟩
  intro C hC cStar hcStar hcStar2 nu hnu hnu1 K hK m h n hh h400 hm hn
  have hC2 : Cml ≤ C := le_trans (le_max_left _ _) hC
  have hCg : Cge ≤ C := le_trans (le_max_right _ _) hC
  have hC1000 : 1000 ≤ C := le_trans hCml hC2
  have h8 := Hge C hCg C (by linarith only [hC1000]) (3 / 4) (by norm_num) (by norm_num) cStar
    hcStar hcStar2 nu hnu hnu1 K hK
  have hmbig := Hml C hC2 cStar hcStar hcStar2 nu hnu hnu1 K hK m (by linarith only [hm, h8])
  obtain ⟨hm4, hnu16⟩ := hmbig
  have hC8 : (125 : ℝ) ≤ C / 8 := by linarith only [hC1000]
  have hmR : (1000000 : ℝ) ≤ m := by
    have : (125 : ℝ) ^ 4 ≤ (C / 8) ^ 4 := pow_le_pow_left₀ (by norm_num) hC8 4
    norm_num at this
    linarith only [this, hm4]
  have hm0 : (0 : ℝ) < m := by linarith only [hmR]
  have hinv1 : 1 ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
  have hinvm : nu⁻¹ ≤ (m : ℝ) := le_trans (le_self_pow₀ hinv1 (by norm_num)) hnu16
  have hnu2 : nu⁻¹ ^ 2 ≤ (m : ℝ) :=
    le_trans (pow_le_pow_right₀ hinv1 (by norm_num)) hnu16
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have h400r : 400 * (h : ℝ) ≤ m := by exact_mod_cast h400
  set Q : ℝ := Real.log (nu⁻¹ * (m : ℝ)) with hQdef
  have hQsplit : Q = Real.log nu⁻¹ + Real.log m := by
    rw [hQdef, Real.log_mul (by positivity) hm0.ne']
  have hlognu0 : 0 ≤ Real.log nu⁻¹ := Real.log_nonneg hinv1
  have hlognu1 : Real.log nu⁻¹ ≤ Real.log m := Real.log_le_log (by positivity) hinvm
  have hQ2 : Q ≤ 2 * Real.log m := by linarith only [hQsplit, hlognu1]
  have hQ1 : Real.log m ≤ Q := by linarith only [hQsplit, hlognu0]
  have hlogm4 := four_le_log_of_large (show (55 : ℝ) ≤ m by linarith only [hmR])
  have hQ0 : 0 ≤ Q := by linarith only [hQ1, hlogm4]
  have hnr : (m : ℝ) - h - 100 * (Q / Real.log 3) < n + 1 := by
    have := Nat.lt_floor_add_one ((m : ℝ) - h - 100 * Real.logb 3 (nu⁻¹ * m))
    rw [← hn] at this
    exact this
  have hmnr : (m : ℝ) ≤ 2 * n := scale_half hmR h400r hQ2 hQ0 hnr
  have hmn : m ≤ 2 * n := by exact_mod_cast hmnr
  have hnum : nu⁻¹ ≤ (m : ℝ) := hinvm
  have hle := principal_scale_le hnu hnu1 h400 (by exact_mod_cast hmR) hnum hn
  have hhm : h ≤ m := by omega
  have hl3 : 1 < Real.log 3 := one_lt_log_three
  have hy1 : 0 ≤ Real.logb 3 (nu⁻¹ * m) := by
    apply Real.logb_nonneg (by norm_num)
    have : (1 : ℝ) ≤ nu⁻¹ * m := by nlinarith only [hinv1, hmR]
    exact this
  have hnm : (n : ℝ) ≤ ((m - h : ℕ) : ℝ) := by
    rw [Nat.cast_sub hhm]; linarith only [hle, hy1]
  exact ⟨hmR, hinvm, hnu2, hmn, by exact_mod_cast hnm⟩

end SuperdiffusionCLT.Section5
