/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Homogenization.Probability.IndependentSums.WeakOrlicz

/-!
# Transfer of stretched-exponential tails to a random scale

If a random scale `W` satisfies `log W ≤ a f + b₀` pointwise and `f` has the upper tail
`P[A t < f] ≤ B exp(-t^σ)` for `t ≥ 1`, then `P[t ≤ W] ≤ C exp(-C⁻¹ (log t)^σ)` for all `t ≥ 1`.
Maxima of two such quantities have such a tail, and the exponent can be lowered.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open MeasureTheory

/-- **Transfer of the tail of `f` to a scale `W` with `log W ≤ a f + b₀`.** -/
theorem ms_transfer {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {W f : Ω → ℝ} {a A b0 B σ : ℝ} (ha : 0 < a) (hA : 0 < A) (hb0 : 0 ≤ b0) (hσ : 0 < σ)
    (hlog : ∀ ω, Real.log (W ω) ≤ a * f ω + b0)
    (hT : ∀ t : ℝ, 1 ≤ t → μ.real {ω | A * t < f ω} ≤ B * Real.exp (-(t ^ σ))) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
      μ.real {ω | t ≤ W ω} ≤ C * Real.exp (-(C⁻¹ * (Real.log t) ^ σ)) := by
  have haA : 0 < 4 * a * A := by positivity
  set T1 : ℝ := 4 * (b0 + a * A) with hT1
  have hT1pos : 0 < T1 := by positivity
  refine ⟨max (max 1 B) (max (Real.exp (T1 ^ σ)) ((4 * a * A) ^ σ)), le_trans (le_max_left _ _)
    (le_max_left _ _), fun t ht => ?_⟩
  set C := max (max 1 B) (max (Real.exp (T1 ^ σ)) ((4 * a * A) ^ σ)) with hC
  have hC1 : 1 ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
  have hCB : B ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCe : Real.exp (T1 ^ σ) ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCa : (4 * a * A) ^ σ ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
  have hC0 : 0 < C := lt_of_lt_of_le one_pos hC1
  have hu0 : 0 ≤ Real.log t := Real.log_nonneg ht
  by_cases hcase : Real.log t ≤ T1
  · have h1 : μ.real {ω | t ≤ W ω} ≤ 1 := measureReal_le_one
    have h2 : (Real.log t) ^ σ ≤ T1 ^ σ := Real.rpow_le_rpow hu0 hcase hσ.le
    have h3 : C⁻¹ * (Real.log t) ^ σ ≤ T1 ^ σ := by
      have hp : 0 ≤ (Real.log t) ^ σ := Real.rpow_nonneg hu0 σ
      have : C⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hC1
      calc C⁻¹ * (Real.log t) ^ σ ≤ 1 * (Real.log t) ^ σ :=
            mul_le_mul_of_nonneg_right this hp
        _ ≤ T1 ^ σ := by linarith only [h2]
    have h4 : Real.exp (-(T1 ^ σ)) ≤ Real.exp (-(C⁻¹ * (Real.log t) ^ σ)) :=
      Real.exp_le_exp.2 (by linarith only [h3])
    have h5 : 1 ≤ C * Real.exp (-(T1 ^ σ)) := by
      have : Real.exp (T1 ^ σ) * Real.exp (-(T1 ^ σ)) = 1 := by
        rw [← Real.exp_add]; simp
      calc (1 : ℝ) = Real.exp (T1 ^ σ) * Real.exp (-(T1 ^ σ)) := this.symm
        _ ≤ C * Real.exp (-(T1 ^ σ)) :=
          mul_le_mul_of_nonneg_right hCe (Real.exp_pos _).le
    calc μ.real {ω | t ≤ W ω} ≤ 1 := h1
      _ ≤ C * Real.exp (-(T1 ^ σ)) := h5
      _ ≤ C * Real.exp (-(C⁻¹ * (Real.log t) ^ σ)) := mul_le_mul_of_nonneg_left h4 hC0.le
  · push Not at hcase
    set u := Real.log t with hu
    have hupos : 0 < u := lt_of_lt_of_le hT1pos hcase.le
    set s := u / (4 * a * A) with hs
    have hs1 : 1 ≤ s := by
      rw [hs, le_div_iff₀ haA]
      have : 4 * a * A ≤ T1 := by rw [hT1]; linarith only [hb0]
      linarith only [this, hcase]
    have hsub : {ω | t ≤ W ω} ⊆ {ω | A * s < f ω} := by
      intro ω hω
      have h1 : u ≤ Real.log (W ω) := Real.log_le_log (by linarith only [ht]) hω
      have h2 := hlog ω
      have h3 : 4 * b0 ≤ T1 := by rw [hT1]; nlinarith only [ha, hA]
      have hAs : A * s = u / (4 * a) := by
        rw [hs]; field_simp
      show A * s < f ω
      rw [hAs, div_lt_iff₀ (by positivity)]
      nlinarith only [h1, h2, h3, hcase, ha, hupos]
    have h6 := (measureReal_mono hsub).trans (hT s hs1)
    have h7 : s ^ σ = u ^ σ / (4 * a * A) ^ σ := by
      rw [hs]; exact Real.div_rpow hupos.le haA.le σ
    have hpw : 0 < (4 * a * A) ^ σ := Real.rpow_pos_of_pos haA σ
    have h8 : C⁻¹ * u ^ σ ≤ s ^ σ := by
      rw [h7, inv_mul_eq_div]
      exact div_le_div_of_nonneg_left (Real.rpow_nonneg hupos.le σ) hpw hCa
    calc μ.real {ω | t ≤ W ω} ≤ B * Real.exp (-(s ^ σ)) := h6
      _ ≤ C * Real.exp (-(C⁻¹ * u ^ σ)) :=
        mul_le_mul hCB (Real.exp_le_exp.2 (by linarith only [h8])) (Real.exp_pos _).le hC0.le

/-- Lowering the exponent of a tail. -/
theorem ms_tail_mono_exp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {f : Ω → ℝ}
    {A B σ ρ : ℝ} (hσρ : σ ≤ ρ)
    (hT : ∀ t : ℝ, 1 ≤ t → μ.real {ω | A * t < f ω} ≤ B * Real.exp (-(t ^ ρ)))
    (hB : 0 ≤ B) :
    ∀ t : ℝ, 1 ≤ t → μ.real {ω | A * t < f ω} ≤ B * Real.exp (-(t ^ σ)) := by
  intro t ht
  refine (hT t ht).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hB)
  have := Real.rpow_le_rpow_of_exponent_le ht hσρ
  linarith only [this]

/-- The `Γ_ρ` relation gives a tail in the form used here. -/
theorem ms_tail_of_isBigO {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f : Ω → ℝ}
    {A ρ : ℝ}
    (h : Homogenization.IndependentSums.IsBigO μ (Homogenization.IndependentSums.gammaSigma ρ)
      f A) :
    ∀ t : ℝ, 1 ≤ t → μ.real {ω | A * t < |f ω|} ≤ 1 * Real.exp (-(t ^ ρ)) := by
  intro t ht
  have := (Homogenization.IndependentSums.isBigO_gammaSigma_iff).1 h ht
  rw [one_mul]
  exact this

end SuperdiffusionCLT.Section7
