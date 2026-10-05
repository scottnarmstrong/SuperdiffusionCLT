/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.GaussianSeriesC

/-!
# The seed field of the Gaussian series

For `ξ` in the good event the field is `nv_seed ξ x = ∑' k, ∑' p, ξ (k, p) * cellKernelCoeff (k / 2) x p`;
off the good event it is `0`. It is `C^2` for every `ξ`; its iterated derivatives of order at most
two are the termwise series over the at most `4 ^ d` cells of `cellsNear x`, and they are bounded
by the weighted row sums of the noise.

## Main results

* `nv_seed`, `nv_contDiff_seed`
* `nv_iteratedFDeriv_seed`
* `nv_seed_abs_le`, `nv_norm_fderiv_seed_le`, `nv_norm_fderiv_fderiv_seed_le`
* `nv_seed_abs_le_of_forall`, `nv_norm_fderiv_seed_le_of_forall`,
  `nv_norm_fderiv_fderiv_seed_le_of_forall`
-/

@[expose] public section

namespace SuperdiffusionCLT.Assumptions.ShellLaw.Model

open Homogenization Set Real MeasureTheory Filter Topology

noncomputable section

variable {d : ℕ}

/-- The row of the noise belonging to the cell `k`. -/
def nv_rowOf (ξ : NvNoise d) (k : Fin d → ℤ) : NvFrame d → ℝ := fun p ↦ ξ (k, p)

/-- The frame series of the cell `k` (without any good-event convention). -/
def nv_cellFun (ξ : NvNoise d) (k : Fin d → ℤ) : Vec d → ℝ :=
  nv_rowFun (nv_rowOf ξ k) (nv_cen k)

/-- The weighted row sum `∑' p, |ξ (k, p)| * nv_b d p` of the cell `k`. -/
def nv_rowSum (ξ : NvNoise d) (k : Fin d → ℤ) : ℝ := ∑' p, |ξ (k, p)| * nv_b d p

open Classical in
/-- The scalar seed field, without the scale `ε`: on the good event the series
`∑' k, ∑' p, ξ (k, p) * cellKernelCoeff (k / 2) x p`, and `0` off it. -/
def nv_seed (ξ : NvNoise d) (x : Vec d) : ℝ :=
  if ξ ∈ nvGood d then ∑' k, nv_cellFun ξ k x else 0

theorem nv_cellFun_def (ξ : NvNoise d) (k : Fin d → ℤ) (x : Vec d) :
    nv_cellFun ξ k x = ∑' p, ξ (k, p) * cellKernelCoeff (nv_cen k) x p := rfl

theorem nv_cellFun_contDiff {ξ : NvNoise d} (hξ : ξ ∈ nvGood d) (k : Fin d → ℤ) :
    ContDiff ℝ 2 (nv_cellFun ξ k) :=
  nv_row_contDiff (nv_summable_of_mem_nvGood hξ k) (nv_cen k)

theorem nv_cellFun_eq_zero_of_far {ξ : NvNoise d} {k : Fin d → ℤ} {x : Vec d}
    (h : ∃ i, 1 < |x i - (k i : ℝ) / 2|) : nv_cellFun ξ k x = 0 := by
  obtain ⟨i, hi⟩ := h
  rw [nv_cellFun_def]
  refine (tsum_congr fun p ↦ ?_).trans tsum_zero
  rw [show cellKernelCoeff (nv_cen k) x p = 0 from
    cellKernelCoeff_eq_zero_of_one_le_abs_sub (i := i) hi.le p, mul_zero]

theorem nv_iteratedFDeriv_cellFun_eq_zero {ξ : NvNoise d} (hξ : ξ ∈ nvGood d) {k : Fin d → ℤ}
    {x : Vec d} (hk : k ∉ cellsNear x) {i : ℕ} (hi : i ≤ 2) :
    iteratedFDeriv ℝ i (nv_cellFun ξ k) x = 0 := by
  unfold nv_cellFun
  rw [nv_row_iteratedFDeriv (r := nv_rowOf ξ k) (nv_summable_of_mem_nvGood hξ k) (nv_cen k) x hi]
  refine (tsum_congr fun p ↦ ?_).trans tsum_zero
  have hc : ContDiffAt ℝ i (fun x ↦ cellKernelCoeff (nv_cen k) x p) x :=
    ((contDiff_cellKernelCoeff (nv_cen k) p).of_le (by exact_mod_cast le_top)).contDiffAt
  have h2 : iteratedFDeriv ℝ i (fun x ↦ nv_rowOf ξ k p * cellKernelCoeff (nv_cen k) x p) x
      = nv_rowOf ξ k p • iteratedFDeriv ℝ i (fun x ↦ cellKernelCoeff (nv_cen k) x p) x := by
    simpa only [smul_eq_mul] using iteratedFDeriv_const_smul_apply' (a := nv_rowOf ξ k p) hc
  rw [h2, nv_iteratedFDeriv_eq_zero_of_not_mem_cellsNear hk p i, smul_zero]

theorem nv_eventually_box (x0 : Vec d) : ∀ᶠ x in 𝓝 x0, ∀ i, |x i - x0 i| < 1 / 2 := by
  refine Filter.eventually_all.2 fun i ↦ ?_
  have hc : ContinuousAt (fun x : Vec d ↦ |x i - x0 i|) x0 :=
    (continuous_abs.comp ((continuous_apply i).sub continuous_const)).continuousAt
  exact hc.eventually_lt continuousAt_const (by simp)

/-- Near `x0` the seed is the finite sum over the cells of `nv_cellsAround x0`. -/
theorem nv_seed_eventuallyEq {ξ : NvNoise d} (hξ : ξ ∈ nvGood d) (x0 : Vec d) :
    nv_seed ξ =ᶠ[𝓝 x0] ∑ k ∈ nv_cellsAround x0, nv_cellFun ξ k := by
  filter_upwards [nv_eventually_box x0] with x hx
  simp only [nv_seed, hξ, ↓reduceIte, Finset.sum_apply]
  refine tsum_eq_sum fun k hk ↦ ?_
  exact nv_cellFun_eq_zero_of_far (nv_far_of_not_mem_around hk hx)

theorem nv_contDiff_seed (ξ : NvNoise d) : ContDiff ℝ 2 (nv_seed ξ) := by
  by_cases hξ : ξ ∈ nvGood d
  · rw [contDiff_iff_contDiffAt]
    intro x0
    have e : (∑ k ∈ nv_cellsAround x0, nv_cellFun ξ k)
        = fun x ↦ ∑ k ∈ nv_cellsAround x0, nv_cellFun ξ k x := by
      funext x; simp only [Finset.sum_apply]
    have h : ContDiffAt ℝ 2 (∑ k ∈ nv_cellsAround x0, nv_cellFun ξ k) x0 := by
      rw [e]
      exact (ContDiff.sum fun k _ ↦ nv_cellFun_contDiff hξ k).contDiffAt
    exact h.congr_of_eventuallyEq (nv_seed_eventuallyEq hξ x0)
  · have : nv_seed ξ = fun _ ↦ 0 := by funext x; simp [nv_seed, hξ]
    rw [this]; exact contDiff_const

/-- **Termwise iterated derivatives.** At every point only the cells of `cellsNear x` contribute. -/
theorem nv_iteratedFDeriv_seed {ξ : NvNoise d} (hξ : ξ ∈ nvGood d) (x : Vec d) {i : ℕ}
    (hi : i ≤ 2) :
    iteratedFDeriv ℝ i (nv_seed ξ) x = ∑ k ∈ cellsNear x, iteratedFDeriv ℝ i (nv_cellFun ξ k) x := by
  have h1 := ((nv_seed_eventuallyEq hξ x).iteratedFDeriv ℝ i).eq_of_nhds
  have hc : ∀ k ∈ nv_cellsAround x, ContDiffAt ℝ i (nv_cellFun ξ k) x := fun k _ ↦
    ((nv_cellFun_contDiff hξ k).of_le (by exact_mod_cast hi)).contDiffAt
  rw [h1, iteratedFDeriv_sum_apply hc]
  symm
  refine Finset.sum_subset (nv_cellsNear_subset_around x) fun k hk hkn ↦ ?_
  exact nv_iteratedFDeriv_cellFun_eq_zero hξ hkn hi

theorem nv_norm_iteratedFDeriv_seed_le {ξ : NvNoise d} (hξ : ξ ∈ nvGood d) (x : Vec d) {i : ℕ}
    (hi : i ≤ 2) : ‖iteratedFDeriv ℝ i (nv_seed ξ) x‖ ≤ ∑ k ∈ cellsNear x, nv_rowSum ξ k := by
  rw [nv_iteratedFDeriv_seed hξ x hi]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
  exact nv_row_norm_iteratedFDeriv_le (nv_summable_of_mem_nvGood hξ k) (nv_cen k) x hi

/-- Bound of the value by the row sums of the at most `4 ^ d` nearby cells. -/
theorem nv_seed_abs_le {ξ : NvNoise d} (hξ : ξ ∈ nvGood d) (x : Vec d) :
    |nv_seed ξ x| ≤ ∑ k ∈ cellsNear x, nv_rowSum ξ k := by
  have h := nv_norm_iteratedFDeriv_seed_le hξ x (i := 0) (by norm_num)
  rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h

theorem nv_norm_fderiv_seed_le {ξ : NvNoise d} (hξ : ξ ∈ nvGood d) (x : Vec d) :
    ‖fderiv ℝ (nv_seed ξ) x‖ ≤ ∑ k ∈ cellsNear x, nv_rowSum ξ k := by
  have h := nv_norm_iteratedFDeriv_seed_le hξ x (i := 1) (by norm_num)
  rwa [norm_iteratedFDeriv_one] at h

theorem nv_norm_fderiv_fderiv_seed_le {ξ : NvNoise d} (hξ : ξ ∈ nvGood d) (x : Vec d) :
    ‖fderiv ℝ (fderiv ℝ (nv_seed ξ)) x‖ ≤ ∑ k ∈ cellsNear x, nv_rowSum ξ k := by
  have h := nv_norm_iteratedFDeriv_seed_le hξ x (i := 2) (by norm_num)
  rwa [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one] at h

/-- The form used for tails: if every nearby cell of every point of `A` has row sum at most `M`,
then value, first and second derivative on `A` are bounded by `4 ^ d * M`. -/
theorem nv_seed_abs_le_of_forall {ξ : NvNoise d} (hξ : ξ ∈ nvGood d) {A : Set (Vec d)} {M : ℝ}
    (hM : ∀ x ∈ A, ∀ k ∈ cellsNear x, nv_rowSum ξ k ≤ M) {x : Vec d} (hx : x ∈ A) :
    |nv_seed ξ x| ≤ 4 ^ d * M := by
  refine (nv_seed_abs_le hξ x).trans ?_
  have := Finset.sum_le_card_nsmul (cellsNear x) (nv_rowSum ξ) M (hM x hx)
  rwa [card_cellsNear, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at this

theorem nv_norm_fderiv_seed_le_of_forall {ξ : NvNoise d} (hξ : ξ ∈ nvGood d) {A : Set (Vec d)}
    {M : ℝ} (hM : ∀ x ∈ A, ∀ k ∈ cellsNear x, nv_rowSum ξ k ≤ M) {x : Vec d} (hx : x ∈ A) :
    ‖fderiv ℝ (nv_seed ξ) x‖ ≤ 4 ^ d * M := by
  refine (nv_norm_fderiv_seed_le hξ x).trans ?_
  have := Finset.sum_le_card_nsmul (cellsNear x) (nv_rowSum ξ) M (hM x hx)
  rwa [card_cellsNear, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at this

theorem nv_norm_fderiv_fderiv_seed_le_of_forall {ξ : NvNoise d} (hξ : ξ ∈ nvGood d)
    {A : Set (Vec d)} {M : ℝ} (hM : ∀ x ∈ A, ∀ k ∈ cellsNear x, nv_rowSum ξ k ≤ M) {x : Vec d}
    (hx : x ∈ A) : ‖fderiv ℝ (fderiv ℝ (nv_seed ξ)) x‖ ≤ 4 ^ d * M := by
  refine (nv_norm_fderiv_fderiv_seed_le hξ x).trans ?_
  have := Finset.sum_le_card_nsmul (cellsNear x) (nv_rowSum ξ) M (hM x hx)
  rwa [card_cellsNear, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at this

end

end SuperdiffusionCLT.Assumptions.ShellLaw.Model
