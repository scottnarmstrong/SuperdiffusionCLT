/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.TailJ3

/-!
# The tail of a weighted row sum

For `R > 0` with `∑ b_p ≤ R` and every cell `k`, the series `∑' p, |ξ (k, p)| * nv_b d p` exceeds
`τ ≥ 0` with probability at most `2 exp (-τ² / (2 R²))`.

## Main results

* `nv_noiseLaw_tail_tsum`: the tail of the extended-real series
* `nv_noiseLaw_tail_rowSum`: the tail of `nv_rowSum`
-/

@[expose] public section

namespace SuperdiffusionCLT.Assumptions.ShellLaw.Model

open Homogenization MeasureTheory ProbabilityTheory

noncomputable section

/-- The partial sum of the series over a finite set of frame indices exceeds the level with
probability at most `2 exp (-τ² / (2 R²))`. -/
theorem nv_noiseLaw_tail_partial (d : ℕ) {R : ℝ} (hR : 0 < R) (hB : ∑' p, nv_b d p ≤ R)
    (k : Fin d → ℤ) (s : Finset (NvFrame d)) {τ : ℝ} (hτ : 0 ≤ τ) :
    nvNoiseLaw d {ξ | τ < ∑ p ∈ s, |ξ (k, p)| * nv_b d p}
      ≤ ENNReal.ofReal (2 * Real.exp (-(τ ^ 2 / (2 * R ^ 2)))) := by
  set lam : ℝ := τ / R ^ 2 with hlam
  have hlam0 : 0 ≤ lam := div_nonneg hτ (by positivity)
  set S : NvNoise d → ℝ := fun ξ ↦ ∑ p ∈ s, |ξ (k, p)| * nv_b d p with hS
  have hSm : Measurable S :=
    Finset.measurable_sum _ fun p _ ↦
      (continuous_abs.measurable.comp (nv_measurable_coord d (k, p))).mul_const _
  have hmark := mul_meas_ge_le_lintegral₀ (μ := nvNoiseLaw d)
    (f := fun ξ ↦ ENNReal.ofReal (Real.exp (lam * S ξ)))
    (Real.measurable_exp.comp (measurable_const.mul hSm)).ennreal_ofReal.aemeasurable
    (ENNReal.ofReal (Real.exp (lam * τ)))
  have hsub : {ξ | τ < S ξ} ⊆
      {ξ | ENNReal.ofReal (Real.exp (lam * τ)) ≤ ENNReal.ofReal (Real.exp (lam * S ξ))} := by
    intro ξ hξ
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2
      (mul_le_mul_of_nonneg_left (le_of_lt hξ) hlam0))
  have hmom := nv_exp_sum_le d hR hB k s lam
  have hinv : ENNReal.ofReal (Real.exp (-(lam * τ))) * ENNReal.ofReal (Real.exp (lam * τ)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    simp
  calc nvNoiseLaw d {ξ | τ < S ξ}
      = ENNReal.ofReal (Real.exp (-(lam * τ))) *
          (ENNReal.ofReal (Real.exp (lam * τ)) * nvNoiseLaw d {ξ | τ < S ξ}) := by
        rw [← mul_assoc, hinv, one_mul]
    _ ≤ ENNReal.ofReal (Real.exp (-(lam * τ))) *
          ∫⁻ ξ, ENNReal.ofReal (Real.exp (lam * S ξ)) ∂(nvNoiseLaw d) := by
        refine mul_le_mul' le_rfl ((mul_le_mul' le_rfl (measure_mono hsub)).trans hmark)
    _ ≤ ENNReal.ofReal (Real.exp (-(lam * τ))) *
          ENNReal.ofReal (2 * Real.exp (lam ^ 2 * R ^ 2 / 2)) := mul_le_mul' le_rfl hmom
    _ = ENNReal.ofReal (2 * Real.exp (-(τ ^ 2 / (2 * R ^ 2)))) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
        congr 1
        have : Real.exp (-(lam * τ)) * (2 * Real.exp (lam ^ 2 * R ^ 2 / 2))
            = 2 * Real.exp (-(lam * τ) + lam ^ 2 * R ^ 2 / 2) := by
          rw [Real.exp_add]; ring
        rw [this]
        congr 2
        rw [hlam]
        field_simp
        ring

theorem nv_directed_partial_events (d : ℕ) (k : Fin d → ℤ) (τ : ℝ) :
    Directed (· ⊆ ·) fun s : Finset (NvFrame d) ↦
      {ξ : NvNoise d | ENNReal.ofReal τ <
        ∑ p ∈ s, ENNReal.ofReal (|ξ (k, p)| * nv_b d p)} := by
  classical
  intro s t
  refine ⟨s ∪ t, ?_, ?_⟩
  · intro ξ hξ
    exact lt_of_lt_of_le (show ENNReal.ofReal τ <
      ∑ p ∈ s, ENNReal.ofReal (|ξ (k, p)| * nv_b d p) from hξ)
      (Finset.sum_le_sum_of_subset Finset.subset_union_left)
  · intro ξ hξ
    exact lt_of_lt_of_le (show ENNReal.ofReal τ <
      ∑ p ∈ t, ENNReal.ofReal (|ξ (k, p)| * nv_b d p) from hξ)
      (Finset.sum_le_sum_of_subset Finset.subset_union_right)

/-- **The tail of the extended-real weighted series.** -/
theorem nv_noiseLaw_tail_tsum (d : ℕ) {R : ℝ} (hR : 0 < R) (hB : ∑' p, nv_b d p ≤ R)
    (k : Fin d → ℤ) {τ : ℝ} (hτ : 0 ≤ τ) :
    nvNoiseLaw d {ξ | ENNReal.ofReal τ < ∑' p, ENNReal.ofReal (|ξ (k, p)| * nv_b d p)}
      ≤ ENNReal.ofReal (2 * Real.exp (-(τ ^ 2 / (2 * R ^ 2)))) := by
  have hset : {ξ : NvNoise d | ENNReal.ofReal τ < ∑' p, ENNReal.ofReal (|ξ (k, p)| * nv_b d p)}
      = ⋃ s : Finset (NvFrame d), {ξ : NvNoise d | ENNReal.ofReal τ <
        ∑ p ∈ s, ENNReal.ofReal (|ξ (k, p)| * nv_b d p)} := by
    ext ξ
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    rw [ENNReal.tsum_eq_iSup_sum, lt_iSup_iff]
  rw [hset, (nv_directed_partial_events d k τ).measure_iUnion]
  refine iSup_le fun s ↦ ?_
  refine le_trans (measure_mono fun ξ hξ ↦ ?_) (nv_noiseLaw_tail_partial d hR hB k s hτ)
  simp only [Set.mem_ofPred_eq] at hξ ⊢
  rw [← ENNReal.ofReal_sum_of_nonneg fun p _ ↦
    mul_nonneg (abs_nonneg _) (nv_b_nonneg d p)] at hξ
  exact (ENNReal.ofReal_lt_ofReal_iff'.1 hξ).1

/-- **The tail of `nv_rowSum`**, uniformly in the cell. -/
theorem nv_noiseLaw_tail_rowSum (d : ℕ) {R : ℝ} (hR : 0 < R) (hB : ∑' p, nv_b d p ≤ R)
    (k : Fin d → ℤ) {τ : ℝ} (hτ : 0 ≤ τ) :
    nvNoiseLaw d {ξ | τ < nv_rowSum ξ k}
      ≤ ENNReal.ofReal (2 * Real.exp (-(τ ^ 2 / (2 * R ^ 2)))) := by
  refine le_trans (measure_mono fun ξ hξ ↦ ?_) (nv_noiseLaw_tail_tsum d hR hB k hτ)
  simp only [Set.mem_ofPred_eq, nv_rowSum] at hξ ⊢
  have hnn : ∀ p, 0 ≤ |ξ (k, p)| * nv_b d p := fun p ↦ mul_nonneg (abs_nonneg _) (nv_b_nonneg d p)
  have hsum : Summable fun p ↦ |ξ (k, p)| * nv_b d p := by
    by_contra h
    rw [tsum_eq_zero_of_not_summable h] at hξ
    linarith only [hξ, hτ]
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsum]
  exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt hτ hξ)).2 hξ

end

/-! ## Satisfiability witness (dimension two) -/

example : ∃ R : ℝ, 0 < R ∧ ∑' p, nv_b 2 p ≤ R ∧
    nvNoiseLaw 2 {ξ | (1 : ℝ) < nv_rowSum ξ 0}
      ≤ ENNReal.ofReal (2 * Real.exp (-((1 : ℝ) ^ 2 / (2 * R ^ 2)))) := by
  have h0 : 0 ≤ ∑' p, nv_b 2 p := tsum_nonneg (nv_b_nonneg 2)
  refine ⟨∑' p, nv_b 2 p + 1, by linarith only [h0], by linarith only, ?_⟩
  exact nv_noiseLaw_tail_rowSum 2 (by linarith only [h0]) (by linarith only) 0 zero_le_one

end SuperdiffusionCLT.Assumptions.ShellLaw.Model
