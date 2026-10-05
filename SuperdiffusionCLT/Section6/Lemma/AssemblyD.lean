/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Lemma.AssemblyC
public import SuperdiffusionCLT.Section6.Lemma.Tail
public import SuperdiffusionCLT.Section6.Lemma.FullGood
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Scales of the assembly of `l.sharp.scale.inputs`

The threshold making `δ_m = ε m^{-(1-ρ)/2} log m` at most `1`, and the maximum rule for two random
scales whose logarithms are `O_{Γ_ρ}` with the scales `A`, `B`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6

open MeasureTheory

/-- Beyond a threshold, `ε m^{-(1-ρ)/2} log m ≤ 1` for `ε ≤ 1` and `ρ < 1`. -/
theorem l9_delta_threshold {ε ρ : ℝ} (hε : ε ≤ 1) (hρ : ρ < 1) :
    ∃ N : ℝ, ∀ m : ℕ, N ≤ (m : ℝ) → 1 ≤ (m : ℝ) →
      ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ) ≤ 1 := by
  have ha : (0 : ℝ) < (1 - ρ) / 2 := by linarith only [hρ]
  have h1 := (isLittleO_log_rpow_atTop ha).def (one_pos : (0 : ℝ) < 1)
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp (h1.and (Filter.eventually_ge_atTop (1 : ℝ)))
  refine ⟨T, fun m hm hm1 => ?_⟩
  obtain ⟨hx1, -⟩ := hT (m : ℝ) hm
  have hm0 : 0 < (m : ℝ) := lt_of_lt_of_le one_pos hm1
  have hlog : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hm1
  have hpow : 0 ≤ (m : ℝ) ^ ((1 - ρ) / 2) := Real.rpow_nonneg hm0.le _
  rw [Real.norm_of_nonneg hlog, Real.norm_of_nonneg hpow, one_mul] at hx1
  have hprod : (m : ℝ) ^ (-((1 - ρ) / 2)) * (m : ℝ) ^ ((1 - ρ) / 2) = 1 := by
    rw [← Real.rpow_add hm0]
    simp only [neg_add_cancel, Real.rpow_zero]
  have hneg : 0 ≤ (m : ℝ) ^ (-((1 - ρ) / 2)) := Real.rpow_nonneg hm0.le _
  have h2 : (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hx1 hneg
    linarith only [this, hprod]
  have h3 : 0 ≤ (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ) := mul_nonneg hneg hlog
  have hε0 : ε ≤ 1 := hε
  calc ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)
      = ε * ((m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)) := by ring
    _ ≤ 1 * 1 := by
        by_cases hε' : 0 ≤ ε
        · exact mul_le_mul hε0 h2 h3 zero_le_one
        · have : ε * ((m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)) ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg (by linarith only [hε']) h3
          linarith only [this]
    _ = 1 := one_mul 1

/-- The maximum of two random scales, the second bounded below by `1`, with `Γ_ρ` tails of the logarithms at
scales `A`, `B`, has `Γ_ρ` tail of the logarithm at any scale `L ≥ c (A + B)`. -/
theorem l9_log_max_bigO {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {ρ A B L : ℝ} {X Y : Ω → ℝ} (hρ : 0 < ρ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hL : (3 * Real.log (2 : ℝ)) ^ ρ⁻¹ * (A + B) ≤ L) (hY : ∀ ω, 1 ≤ Y ω)
    (hXO : Homogenization.IndependentSums.IsBigO μ (Homogenization.IndependentSums.gammaSigma ρ)
      (fun ω => Real.log (X ω)) A)
    (hYO : Homogenization.IndependentSums.IsBigO μ (Homogenization.IndependentSums.gammaSigma ρ)
      (fun ω => Real.log (Y ω)) B) :
    Homogenization.IndependentSums.IsBigO μ (Homogenization.IndependentSums.gammaSigma ρ)
      (fun ω => Real.log (max (X ω) (Y ω))) L := by
  have hmax := isBigO_gammaSigma_max_two_add hρ hA hB hXO hYO
  refine Homogenization.IndependentSums.IsBigO.of_abs_le (hmax.mono_scale hL) fun ω => ?_
  have hX1 : 1 ≤ max (X ω) (Y ω) := le_trans (hY ω) (le_max_right _ _)
  have h0 : 0 ≤ Real.log (max (X ω) (Y ω)) := Real.log_nonneg hX1
  have h1 : Real.log (max (X ω) (Y ω)) ≤ max (Real.log (X ω)) (Real.log (Y ω)) := by
    rcases max_choice (X ω) (Y ω) with h | h
    · rw [h]; exact le_max_left _ _
    · rw [h]; exact le_max_right _ _
  rw [abs_of_nonneg h0, abs_of_nonneg (le_trans h0 h1)]
  exact h1

end SuperdiffusionCLT.Section6
