/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Probability.OrliczMoments

/-!
# `L^8` norms of `O_{Γ₂}` random variables

The `L⁸(P)` norm of a measurable `X` with `|X| ≤ O_{Γ₂}(A)` is at most `2A`, from the moment bound
`E|X|^k ≤ A^k (1 + Γ(k/2 + 1))` at `k = 8` (`e.moments.OGamma2`), and the `L⁸(P)` triangle
inequality for a constant plus such a variable.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open MeasureTheory Homogenization
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `(∫⁻ ‖X‖ₑ^8)^{1/8} ≤ 2A` for `|X| ≤ O_{Γ₂}(A)`. -/
theorem eLpNorm_eight_le_of_isBigO_gammaSigma_two {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {A : ℝ} (hA : 0 < A) (hXm : Measurable X)
    (hX : IndependentSums.IsBigO μ (IndependentSums.gammaSigma 2) X A) :
    eLpNorm X 8 μ ≤ ENNReal.ofReal (2 * A) := by
  have hmom := SuperdiffusionCLT.Probability.abs_moment_le_of_isBigO_gammaSigma_two
    hA hXm.aemeasurable hX 8
  have hint := SuperdiffusionCLT.Probability.integrable_abs_rpow_of_isBigO_gammaSigma_two
    hA hXm.aemeasurable hX 8
  have hG : Real.Gamma (((8 : ℕ) : ℝ) / 2 + 1) = 24 := by
    have h : ((8 : ℕ) : ℝ) / 2 + 1 = ((4 : ℕ) : ℝ) + 1 := by norm_num
    rw [h, Real.Gamma_nat_eq_factorial]
    norm_num [Nat.factorial]
  have hbound : ∫ ω, |X ω| ^ (((8 : ℕ)) : ℝ) ∂μ ≤ (2 * A) ^ (((8 : ℕ)) : ℝ) := by
    refine hmom.trans ?_
    rw [hG]
    have h1 : (A ^ (((8 : ℕ)) : ℝ)) * (1 + 24) = 25 * A ^ (8 : ℕ) := by
      rw [Real.rpow_natCast]; ring
    have h2 : (2 * A) ^ (((8 : ℕ)) : ℝ) = 256 * A ^ (8 : ℕ) := by
      rw [Real.rpow_natCast]; ring
    rw [h1, h2]
    have : (0 : ℝ) ≤ A ^ (8 : ℕ) := by positivity
    linarith only [this]
  have hq : (8 : ℝ≥0∞) ≠ 0 := by norm_num
  have hqt : (8 : ℝ≥0∞) ≠ ⊤ := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq hqt hXm.aestronglyMeasurable]
  have h8 : (8 : ℝ≥0∞).toReal = 8 := by norm_num
  rw [h8]
  have hl : ∫⁻ ω, ‖X ω‖ₑ ^ (8 : ℝ) ∂μ ≤ ENNReal.ofReal ((2 * A) ^ (8 : ℝ)) := by
    have hnn : ∀ ω, 0 ≤ |X ω| ^ (8 : ℝ) := fun ω => Real.rpow_nonneg (abs_nonneg _) _
    have hcast : (((8 : ℕ)) : ℝ) = 8 := by norm_num
    rw [hcast] at hbound hint
    calc ∫⁻ ω, ‖X ω‖ₑ ^ (8 : ℝ) ∂μ
        = ∫⁻ ω, ENNReal.ofReal (|X ω| ^ (8 : ℝ)) ∂μ := by
          refine lintegral_congr fun ω => ?_
          rw [← ofReal_norm, Real.norm_eq_abs,
            ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
      _ = ENNReal.ofReal (∫ ω, |X ω| ^ (8 : ℝ) ∂μ) :=
          (ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hnn)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hbound
  calc (∫⁻ ω, ‖X ω‖ₑ ^ (8 : ℝ) ∂μ) ^ (1 / (8 : ℝ))
      ≤ (ENNReal.ofReal ((2 * A) ^ (8 : ℝ))) ^ (1 / (8 : ℝ)) :=
        ENNReal.rpow_le_rpow hl (by norm_num)
    _ = ENNReal.ofReal (2 * A) := by
        have hy : 0 ≤ (2 * A) ^ (8 : ℝ) := Real.rpow_nonneg (by positivity) _
        rw [ENNReal.ofReal_rpow_of_nonneg hy (by norm_num : (0 : ℝ) ≤ 1 / 8),
          ← Real.rpow_mul (by positivity)]
        norm_num

/-- The `L⁸(P)` norm of `c + |X|` for a constant `c ≥ 0` and `|X| ≤ O_{Γ₂}(A)`. -/
theorem eLpNorm_eight_const_add_abs_le {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {A c : ℝ} (hA : 0 < A) (hc : 0 ≤ c) (hXm : Measurable X)
    (hX : IndependentSums.IsBigO μ (IndependentSums.gammaSigma 2) X A) :
    eLpNorm (fun ω => c + |X ω|) 8 μ ≤ ENNReal.ofReal (c + 2 * A) := by
  have hsum : (fun ω => c + |X ω|) = (fun _ : Ω => c) + (fun ω => |X ω|) := rfl
  have hq : (1 : ℝ≥0∞) ≤ 8 := by norm_num
  have hXabs : eLpNorm (fun ω => |X ω|) 8 μ = eLpNorm X 8 μ := by
    simpa only [Real.norm_eq_abs] using eLpNorm_norm (p := 8) (μ := μ) X hXm.aestronglyMeasurable
  rw [hsum]
  refine (eLpNorm_add_le (f := fun _ : Ω => c) (g := fun ω => |X ω|) hq).trans ?_
  rw [hXabs]
  have hcn : eLpNorm (fun _ : Ω => c) 8 μ = ENNReal.ofReal c := by
    rw [eLpNorm_const _ (by norm_num) (NeZero.ne _)]
    simp [Real.enorm_eq_ofReal hc]
  rw [hcn, ENNReal.ofReal_add hc (by positivity)]
  exact add_le_add_right (eLpNorm_eight_le_of_isBigO_gammaSigma_two hA hXm hX) _

end SuperdiffusionCLT.Section5
