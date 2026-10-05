/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Book.Ch05.Theorems.Section57.HomogenizationErrorQuenched

/-!
# Maxima of `Γ_σ` tails with a summed scale

CoarseGraining proves the maximum rule with the scale `C * max A B`
(`Homogenization.Book.Ch05.Section57.isBigO_gammaSigma_max_two_of_scales`) and, for finite
families, `C * sup' a` (`Homogenization.Book.Ch04.isBigO_gammaSigma_finset_sup'_of_scales`). Here
the scale is relaxed to the sum, which is the form used when the two tails are combined:
`max X Y = O_{Γ_σ}(C (A + B))`, with `C = (3 log 2)^{1/σ}` (two terms) and
`C = (3 log n)^{1/σ}` for `n ≥ 2` terms.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6

open MeasureTheory Homogenization Homogenization.IndependentSums

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `max X Y = O_{Γ_σ}(C (A + B))` for nonnegative scales and `C = (3 log 2)^{1/σ}`. -/
theorem isBigO_gammaSigma_max_two_add {μ : Measure Ω} [IsFiniteMeasure μ] {σ A B : ℝ}
    {X Y : Ω → ℝ} (hσ : 0 < σ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hX : IsBigO μ (gammaSigma σ) X A) (hY : IsBigO μ (gammaSigma σ) Y B) :
    IsBigO μ (gammaSigma σ) (fun ω => max (X ω) (Y ω))
      (((3 * Real.log (2 : ℝ)) ^ σ⁻¹) * (A + B)) := by
  have hmax := Homogenization.Book.Ch05.Section57.isBigO_gammaSigma_max_two_of_scales
    hσ hX hY
  refine hmax.mono_scale ?_
  have hC : 0 ≤ (3 * Real.log (2 : ℝ)) ^ σ⁻¹ :=
    Real.rpow_nonneg (by have := Real.log_pos (one_lt_two : (1 : ℝ) < 2); positivity) _
  exact mul_le_mul_of_nonneg_left (max_le (by linarith only [hB]) (by linarith only [hA])) hC

/-- Existential form: a constant depending only on `σ`. -/
theorem exists_isBigO_gammaSigma_max_two_add {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type _} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
      {A B : ℝ} {X Y : Ω → ℝ}, 0 ≤ A → 0 ≤ B →
      IsBigO μ (gammaSigma σ) X A → IsBigO μ (gammaSigma σ) Y B →
      IsBigO μ (gammaSigma σ) (fun ω => max (X ω) (Y ω)) (C * (A + B)) := by
  refine ⟨(3 * Real.log (2 : ℝ)) ^ σ⁻¹, ?_, ?_⟩
  · exact Real.rpow_pos_of_pos
      (by have := Real.log_pos (one_lt_two : (1 : ℝ) < 2); positivity) _
  · intro Ω _ μ _ A B X Y hA hB hX hY
    exact isBigO_gammaSigma_max_two_add hσ hA hB hX hY

/-- Witness: the zero variable is `O_{Γ_σ}(1)` for any finite measure, so the hypotheses are
satisfiable and the maximum rule applies. -/
example : IsBigO (MeasureTheory.Measure.dirac (0 : ℝ)) (gammaSigma 1)
    (fun ω => max ((fun _ : ℝ => (0 : ℝ)) ω) ((fun _ : ℝ => (0 : ℝ)) ω))
    (((3 * Real.log (2 : ℝ)) ^ (1 : ℝ)⁻¹) * (1 + 1)) := by
  have h0 : IsBigO (MeasureTheory.Measure.dirac (0 : ℝ)) (gammaSigma 1)
      (fun _ : ℝ => (0 : ℝ)) 1 := by
    intro t ht
    have hempty : upperTailEvent (fun ω : ℝ => |(fun _ : ℝ => (0 : ℝ)) ω|) (1 * t) = ∅ := by
      ext ω
      simp only [upperTailEvent, Set.mem_ofPred_eq, abs_zero, Set.mem_empty_iff_false,
        iff_false, not_lt]
      linarith only [ht]
    rw [hempty]
    simp only [MeasureTheory.measureReal_empty]
    exact inv_nonneg.2 (Real.exp_pos _).le
  exact isBigO_gammaSigma_max_two_add one_pos zero_le_one zero_le_one h0 h0

end SuperdiffusionCLT.Section6
