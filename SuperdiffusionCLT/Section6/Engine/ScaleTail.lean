/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Homogenization.Probability.IndependentSums.WeakOrlicz

@[expose] public section

namespace SuperdiffusionCLT.Section6

open MeasureTheory

/-- The minimal scale `X = 3^{m_* + C0}` with `m_* = m0 + ⌈max L̂ (log_3 X0)⌉₊`: measurability,
the lower bound, the stretched-exponential tail of `log X`, and the covering property. -/
theorem eng_scale_tail {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] (ρ Lhat : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hL : 1 ≤ Lhat) (m0 C0 : ℕ) (X0 : Ω → ℝ) (hX0m : Measurable X0)
    (hX01 : ∀ omega, 1 ≤ X0 omega)
    (hX0 : Homogenization.IndependentSums.IsBigO μ
      (Homogenization.IndependentSums.gammaSigma ρ) (fun omega => Real.log (X0 omega)) Lhat) :
    Measurable (fun omega =>
        (3 : ℝ) ^ (m0 + ⌈max Lhat (Real.logb 3 (X0 omega))⌉₊ + C0)) ∧
      (∀ omega, 1 ≤ (3 : ℝ) ^ (m0 + ⌈max Lhat (Real.logb 3 (X0 omega))⌉₊ + C0)) ∧
      Homogenization.IndependentSums.IsBigOWith μ
        (Homogenization.IndependentSums.gammaSigma ρ)
        (fun omega =>
          Real.log ((3 : ℝ) ^ (m0 + ⌈max Lhat (Real.logb 3 (X0 omega))⌉₊ + C0)))
        (3 * Lhat + ((m0 : ℝ) + (C0 : ℝ) + 1) * Real.log 3) ∧
      ∀ omega,
        X0 omega ≤ (3 : ℝ) ^ (m0 + ⌈max Lhat (Real.logb 3 (X0 omega))⌉₊) ∧
          Lhat ≤ ((m0 + ⌈max Lhat (Real.logb 3 (X0 omega))⌉₊ : ℕ) : ℝ) := by
  have _hρ : 0 < (1 : ℝ) := hρ0.trans hρ1
  have hmax : ∀ omega, 1 ≤ max Lhat (Real.logb 3 (X0 omega)) := fun omega => le_trans hL (le_max_left _ _)
  have hlogX0 : ∀ omega, 0 ≤ Real.log (X0 omega) := fun omega => Real.log_nonneg (hX01 omega)
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 by norm_num)
    linarith only [this]
  have hlog3p : 0 < Real.log 3 := Real.log_pos (by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hn : Measurable (fun omega => m0 + ⌈max Lhat (Real.logb 3 (X0 omega))⌉₊ + C0) := by
      have h1 : Measurable (fun omega => ⌈max Lhat (Real.logb 3 (X0 omega))⌉₊) :=
        Nat.measurable_ceil.comp (measurable_const.max (hX0m.log.div_const (Real.log 3)))
      exact (measurable_const.add h1).add measurable_const
    exact (measurable_from_top (f := fun k : ℕ => (3 : ℝ) ^ k)).comp hn
  · intro omega
    exact one_le_pow₀ (by norm_num)
  · intro t ht
    have ht0 : 0 ≤ t := le_trans zero_le_one ht
    refine le_trans (measureReal_mono ?_) (hX0 ht)
    intro omega hω
    simp only [Homogenization.IndependentSums.mem_upperTailEvent] at hω ⊢
    rw [Real.log_pow] at hω
    have hc : 0 ≤ ((m0 : ℝ) + (C0 : ℝ) + 1) * Real.log 3 := by positivity
    have hceil : (⌈max Lhat (Real.logb 3 (X0 omega))⌉₊ : ℝ) < max Lhat (Real.logb 3 (X0 omega)) + 1 :=
      Nat.ceil_lt_add_one (le_trans zero_le_one (hmax omega))
    have hlb : Real.logb 3 (X0 omega) * Real.log 3 = Real.log (X0 omega) := by
      rw [Real.logb]; field_simp
    have hmx : max Lhat (Real.logb 3 (X0 omega)) * Real.log 3 ≤
        Lhat * Real.log 3 + Real.log (X0 omega) := by
      rcases le_total Lhat (Real.logb 3 (X0 omega)) with h | h
      · rw [max_eq_right h, hlb]
        nlinarith only [mul_nonneg (le_trans zero_le_one hL) hlog3p.le]
      · rw [max_eq_left h]
        linarith only [hlogX0 omega]
    have hup : ((m0 + ⌈max Lhat (Real.logb 3 (X0 omega))⌉₊ + C0 : ℕ) : ℝ) * Real.log 3 ≤
        ((m0 : ℝ) + (C0 : ℝ) + 1) * Real.log 3 + (Lhat * Real.log 3 + Real.log (X0 omega)) := by
      have : ((m0 + ⌈max Lhat (Real.logb 3 (X0 omega))⌉₊ + C0 : ℕ) : ℝ) ≤
          ((m0 : ℝ) + (C0 : ℝ) + 1) + max Lhat (Real.logb 3 (X0 omega)) := by
        push_cast; linarith only [hceil]
      nlinarith only [mul_le_mul_of_nonneg_right this hlog3p.le, hmx]
    rw [abs_of_nonneg (hlogX0 omega)]
    have h1 : (3 * Lhat + ((m0 : ℝ) + (C0 : ℝ) + 1) * Real.log 3) * t =
        3 * Lhat * t + ((m0 : ℝ) + (C0 : ℝ) + 1) * Real.log 3 * t := by ring
    have hct : ((m0 : ℝ) + (C0 : ℝ) + 1) * Real.log 3 ≤
        ((m0 : ℝ) + (C0 : ℝ) + 1) * Real.log 3 * t := by
      nlinarith only [hc, ht]
    have hL0 : 0 ≤ Lhat := le_trans zero_le_one hL
    have h2 : Lhat * Real.log 3 ≤ 2 * Lhat := by nlinarith only [hlog3, hL0]
    have h3 : 2 * Lhat ≤ 2 * Lhat * t := by nlinarith only [hL0, ht]
    nlinarith only [hω, hup, h1, hct, h2, h3]
  · intro omega
    constructor
    · have hl : Real.logb 3 (X0 omega) ≤ (⌈max Lhat (Real.logb 3 (X0 omega))⌉₊ : ℝ) :=
        le_trans (le_max_right _ _) (Nat.le_ceil _)
      have hpos : 0 < X0 omega := lt_of_lt_of_le zero_lt_one (hX01 omega)
      calc X0 omega = (3 : ℝ) ^ (Real.logb 3 (X0 omega)) := (Real.rpow_logb (by norm_num) (by norm_num) hpos).symm
        _ ≤ (3 : ℝ) ^ ((⌈max Lhat (Real.logb 3 (X0 omega))⌉₊ : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hl
        _ = (3 : ℝ) ^ (⌈max Lhat (Real.logb 3 (X0 omega))⌉₊) := Real.rpow_natCast _ _
        _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
    · have : Lhat ≤ (⌈max Lhat (Real.logb 3 (X0 omega))⌉₊ : ℝ) :=
        le_trans (le_max_left _ _) (Nat.le_ceil _)
      push_cast
      linarith only [this, (Nat.cast_nonneg m0 : (0:ℝ) ≤ m0)]

/-- Witness: `X₀ = 1`. -/
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (m0 C0 : ℕ) :
    Measurable (fun _ : Ω => (3 : ℝ) ^ (m0 + ⌈max (1 : ℝ) (Real.logb 3 1)⌉₊ + C0)) :=
  measurable_const

end SuperdiffusionCLT.Section6
