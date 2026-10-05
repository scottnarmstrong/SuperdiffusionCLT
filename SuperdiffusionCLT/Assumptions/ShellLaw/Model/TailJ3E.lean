/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.TailJ3C
public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.TailJ3D

/-!
# From bounded row sums to a bound on the J3 observable of the seed shell

If every nearby cell of the unit cube has row sum at most `τ` for every entry, then at every shell
`n` the J3 observable of the dilated seed shell field is at most `K₀ ε τ`.

## Main results

* `nv_R`, `nv_K0`, `nv_G`, `nv_epsJ3`: the explicit constants
* `nv_seedMap_bounds`
* `nv_obs_le_of_rows`
-/

@[expose] public section

namespace SuperdiffusionCLT.Assumptions.ShellLaw.Model

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Assumptions.ShellField

noncomputable section

variable {d : ℕ}

/-- The bound `∑ b_p + 1` for the weights, positive. -/
def nv_R (d : ℕ) : ℝ := ∑' p, nv_b d p + 1

/-- The dimensional constant of the J3 observable bound. -/
def nv_K0 (d : ℕ) : ℝ := (d : ℝ) ^ 2 * (1 + Real.sqrt d + d) * 4 ^ d

/-- The number of events in the union bound, a real upper bound. -/
def nv_G (d : ℕ) : ℝ := (d : ℝ) ^ 2 * 5 ^ d

/-- **The amplitude of the seed shell law** for which J3 holds. -/
def nv_epsJ3 (d : ℕ) : ℝ := 1 / (nv_K0 d * nv_R d * (2 * (1 + 2 * nv_G d)))

theorem nv_R_pos (d : ℕ) : 0 < nv_R d := by
  have : 0 ≤ ∑' p, nv_b d p := tsum_nonneg (nv_b_nonneg d)
  unfold nv_R; linarith only [this]

theorem nv_summable_le_R (d : ℕ) : ∑' p, nv_b d p ≤ nv_R d := by
  unfold nv_R; linarith only

theorem nv_K0_pos (hd : 0 < d) : 0 < nv_K0 d := by
  unfold nv_K0
  have : (0 : ℝ) < d := by exact_mod_cast hd
  positivity

theorem nv_G_nonneg (d : ℕ) : 0 ≤ nv_G d := by unfold nv_G; positivity

theorem nv_epsJ3_pos (hd : 0 < d) : 0 < nv_epsJ3 d := by
  unfold nv_epsJ3
  have := nv_K0_pos hd
  have := nv_R_pos d
  have := nv_G_nonneg d
  positivity

/-- Bounds for the seed of scale `ε` on the unit cube. -/
theorem nv_seedMap_bounds {ξ : NvNoise d} (hξ : ξ ∈ nvGood d) {ε : ℝ} (hε : 0 ≤ ε) {τ : ℝ}
    (hτ : ∀ k ∈ nv_cubeCells d, nv_rowSum ξ k ≤ τ) {y : Vec d} (hy : ∀ i, |y i| < 1 / 2) :
    |nv_seedMap ε ξ y| ≤ ε * (4 ^ d * τ) ∧
      ‖ScalarC2Field.deriv (nv_seedMap ε ξ) y‖ ≤ ε * (4 ^ d * τ) ∧
      ‖ScalarC2Field.secondDeriv (nv_seedMap ε ξ) y‖ ≤ ε * (4 ^ d * τ) := by
  have hM : ∀ x ∈ {x : Vec d | ∀ i, |x i| < 1 / 2}, ∀ k ∈ cellsNear x, nv_rowSum ξ k ≤ τ :=
    fun x hx k hk ↦ hτ k (nv_cellsNear_subset_cubeCells hx hk)
  have hyA : y ∈ {x : Vec d | ∀ i, |x i| < 1 / 2} := hy
  refine ⟨?_, ?_, ?_⟩
  · rw [nv_seedMap_apply, abs_mul, abs_of_nonneg hε]
    exact mul_le_mul_of_nonneg_left (nv_seed_abs_le_of_forall hξ hM hyA) hε
  · have e : ScalarC2Field.deriv (nv_seedMap ε ξ) y = ε • fderiv ℝ (nv_seed ξ) y := rfl
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg hε]
    exact mul_le_mul_of_nonneg_left (nv_norm_fderiv_seed_le_of_forall hξ hM hyA) hε
  · have e : ScalarC2Field.secondDeriv (nv_seedMap ε ξ) y
        = ε • fderiv ℝ (fderiv ℝ (nv_seed ξ)) y := rfl
    rw [e]
    refine (ContinuousLinearMap.opNorm_smul_le ε _).trans ?_
    rw [Real.norm_eq_abs, abs_of_nonneg hε]
    exact mul_le_mul_of_nonneg_left (nv_norm_fderiv_fderiv_seed_le_of_forall hξ hM hyA) hε

/-- **The observable bound.** -/
theorem nv_obs_le_of_rows (ξ : SkewIdx d → NvNoise d) (hg : ∀ p, ξ p ∈ nvGood d) {ε : ℝ}
    (hε : 0 ≤ ε) {τ : ℝ} (hτ0 : 0 ≤ τ)
    (hrow : ∀ p, ∀ k ∈ nv_cubeCells d, nv_rowSum (ξ p) k ≤ τ) (n : ℕ) :
    j3Observable d n (dilate (nv_scaleUnit n) (nv_j3_seedShellMap ε ξ)) ≤ nv_K0 d * ε * τ := by
  have hm : 0 ≤ ε * (4 ^ d * τ) := by positivity
  have h := nv_j3Observable_dilate_le n (fun p ↦ nv_seedMap ε (ξ p)) hm
    (fun p y hy ↦ (nv_seedMap_bounds (hg p) hε (hrow p) hy).1)
    (fun p y hy ↦ (nv_seedMap_bounds (hg p) hε (hrow p) hy).2.1)
    (fun p y hy ↦ (nv_seedMap_bounds (hg p) hε (hrow p) hy).2.2)
  refine h.trans (le_of_eq ?_)
  unfold nv_K0
  ring

end

end SuperdiffusionCLT.Assumptions.ShellLaw.Model
