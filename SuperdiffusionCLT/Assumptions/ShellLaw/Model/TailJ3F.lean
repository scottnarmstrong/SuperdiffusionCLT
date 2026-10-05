/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.TailJ3E

/-!
# The J3 tail of the seed shell law

For `ε > 0` with `2 (1 + 2 G) ε² K₀² R² ≤ 1`, at every shell `n` and every `t ≥ 1`
`P[ t < j3Observable d n (dilate 3^n (assembleSkew ...)) ] ≤ exp (-t²)`.
The proof is a union bound over the entries `i < j` and the cells meeting the unit cube,
using the sub-Gaussian tail of the row sums.

## Main results

* `nv_final_real`: the elementary real inequality closing the estimate
* `nv_rowSum_le_of_tsum_le`
* `nv_inclusion`: the bad event contains the event of a large observable
-/

@[expose] public section

namespace SuperdiffusionCLT.Assumptions.ShellLaw.Model

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Assumptions.ShellField

noncomputable section

variable {d : ℕ}

/-- The elementary inequality closing the union bound. -/
theorem nv_final_real {G N t x : ℝ} (hG : 0 ≤ G) (hN : N ≤ G) (ht : 1 ≤ t)
    (hx : (1 + 2 * G) * t ^ 2 ≤ x) : N * (2 * Real.exp (-x)) ≤ Real.exp (-(t ^ 2)) := by
  have ht2 : 1 ≤ t ^ 2 := by nlinarith only [ht]
  have h1 : Real.exp (-x) ≤ Real.exp (-((1 + 2 * G) * t ^ 2)) :=
    Real.exp_le_exp.2 (by linarith only [hx])
  have h2 : Real.exp (-((1 + 2 * G) * t ^ 2))
      = Real.exp (-(t ^ 2)) * Real.exp (-(2 * G * t ^ 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h3 : Real.exp (-(2 * G * t ^ 2)) ≤ Real.exp (-(2 * G)) :=
    Real.exp_le_exp.2 (by nlinarith only [ht2, hG])
  have h4 : 2 * G * Real.exp (-(2 * G)) ≤ 1 := by
    have := Real.add_one_le_exp (2 * G)
    have e : Real.exp (2 * G) * Real.exp (-(2 * G)) = 1 := by rw [← Real.exp_add]; simp
    have hp := Real.exp_pos (-(2 * G))
    nlinarith only [this, e, hp]
  have hE := Real.exp_pos (-(t ^ 2))
  have h5 : Real.exp (-x) ≤ Real.exp (-(t ^ 2)) * Real.exp (-(2 * G)) :=
    calc Real.exp (-x) ≤ Real.exp (-((1 + 2 * G) * t ^ 2)) := h1
      _ = Real.exp (-(t ^ 2)) * Real.exp (-(2 * G * t ^ 2)) := h2
      _ ≤ Real.exp (-(t ^ 2)) * Real.exp (-(2 * G)) := mul_le_mul_of_nonneg_left h3 hE.le
  calc N * (2 * Real.exp (-x)) ≤ G * (2 * Real.exp (-x)) :=
        mul_le_mul_of_nonneg_right hN (by positivity)
    _ ≤ G * (2 * (Real.exp (-(t ^ 2)) * Real.exp (-(2 * G)))) :=
        mul_le_mul_of_nonneg_left (by linarith only [h5]) hG
    _ = Real.exp (-(t ^ 2)) * (2 * G * Real.exp (-(2 * G))) := by ring
    _ ≤ Real.exp (-(t ^ 2)) := mul_le_of_le_one_right hE.le h4

theorem nv_rowSum_le_of_tsum_le {ξ : NvNoise d} (hξ : ξ ∈ nvGood d) (k : Fin d → ℤ) {τ : ℝ}
    (hτ : 0 ≤ τ)
    (h : ∑' q, ENNReal.ofReal (|ξ (k, q)| * nv_b d q) ≤ ENNReal.ofReal τ) :
    nv_rowSum ξ k ≤ τ := by
  have hnn : ∀ q, 0 ≤ |ξ (k, q)| * nv_b d q := fun q ↦ mul_nonneg (abs_nonneg _) (nv_b_nonneg d q)
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn (nv_summable_of_mem_nvGood hξ k)] at h
  exact (ENNReal.ofReal_le_ofReal_iff hτ).1 h

/-- The event of a bad row sum at the entry `p` and the cell `k`. -/
def nv_badRow (d : ℕ) (τ : ℝ) (k : Fin d → ℤ) : Set (NvNoise d) :=
  {ζ | ENNReal.ofReal τ < ∑' q, ENNReal.ofReal (|ζ (k, q)| * nv_b d q)}

theorem measurableSet_nv_badRow (d : ℕ) (τ : ℝ) (k : Fin d → ℤ) :
    MeasurableSet (nv_badRow d τ k) :=
  measurableSet_lt measurable_const
    (Measurable.tsum fun q ↦
      ENNReal.measurable_ofReal.comp
        ((continuous_abs.measurable.comp (nv_measurable_coord d (k, q))).mul_const _))

/-- **The inclusion.** A large observable forces a bad entry or a bad row. -/
theorem nv_inclusion (hd : 0 < d) {ε : ℝ} (hε : 0 < ε) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    {ξ : SkewIdx d → NvNoise d |
        t < j3Observable d n (dilate (nv_scaleUnit n) (nv_j3_seedShellMap ε ξ))}
      ⊆ (⋃ p : SkewIdx d, {ξ | ξ p ∈ (nvGood d)ᶜ}) ∪
        ⋃ p : SkewIdx d, ⋃ k ∈ nv_cubeCells d,
          {ξ | ξ p ∈ nv_badRow d (t / (ε * nv_K0 d)) k} := by
  intro ξ hξ
  by_contra hbad
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq, not_or, not_exists,
    Set.mem_compl_iff, not_not] at hbad
  obtain ⟨hg, hrow⟩ := hbad
  have hK := nv_K0_pos hd
  have hτ0 : 0 ≤ t / (ε * nv_K0 d) := div_nonneg ht (mul_pos hε hK).le
  have hr : ∀ p, ∀ k ∈ nv_cubeCells d, nv_rowSum (ξ p) k ≤ t / (ε * nv_K0 d) := fun p k hk ↦
    nv_rowSum_le_of_tsum_le (hg p) k hτ0 (not_lt.1 (hrow p k hk))
  have h := nv_obs_le_of_rows ξ hg hε.le hτ0 hr n
  have e : nv_K0 d * ε * (t / (ε * nv_K0 d)) = t := by field_simp
  rw [e] at h
  exact absurd hξ (not_lt.2 h)

end

end SuperdiffusionCLT.Assumptions.ShellLaw.Model
