/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.GaussianSeriesD

/-!
# The seed field: termwise formulas for value and derivatives

For `ξ` in the good event, the value, the first and the second derivative of `nv_seed ξ` are the
termwise double series over the cell `k` and the frame index `p`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Assumptions.ShellLaw.Model

open Homogenization Set Real MeasureTheory Filter Topology

noncomputable section

variable {d : ℕ}

theorem nv_seed_eq_sum {ξ : NvNoise d} (hξ : ξ ∈ nvGood d) (x : Vec d) :
    nv_seed ξ x = ∑ k ∈ cellsNear x, nv_cellFun ξ k x := by
  simp only [nv_seed, hξ, ↓reduceIte]
  refine tsum_eq_sum fun k hk ↦ ?_
  rw [nv_cellFun_def]
  refine (tsum_congr fun p ↦ ?_).trans tsum_zero
  have h0 : cellKernelCoeff (nv_cen k) x p = 0 := cellKernelCoeff_eq_zero_of_not_mem_cellsNear hk p
  rw [h0, mul_zero]

/-- **The first derivative of the seed is the termwise series.** -/
theorem nv_seed_fderiv_apply_sum {ξ : NvNoise d} (hξ : ξ ∈ nvGood d) (x v : Vec d) :
    fderiv ℝ (nv_seed ξ) x v
      = ∑ k ∈ cellsNear x, ∑' p, ξ (k, p) * fderiv ℝ (fun y ↦ cellKernelCoeff (nv_cen k) y p) x v := by
  have h := nv_iteratedFDeriv_seed hξ x (i := 1) (by norm_num)
  have h2 := congrArg (fun L : ContinuousMultilinearMap ℝ (fun _ : Fin 1 ↦ Vec d) ℝ ↦
    L (fun _ ↦ v)) h
  simp only [iteratedFDeriv_one_apply] at h2
  rw [h2]
  have := map_sum (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 ↦ Vec d) ℝ (fun _ ↦ v))
    (fun k ↦ iteratedFDeriv ℝ 1 (nv_cellFun ξ k) x) (cellsNear x)
  refine this.trans (Finset.sum_congr rfl fun k _ ↦ ?_)
  show iteratedFDeriv ℝ 1 (nv_cellFun ξ k) x (fun _ ↦ v) = _
  rw [iteratedFDeriv_one_apply]
  exact nv_row_fderiv_apply (nv_summable_of_mem_nvGood hξ k) (nv_cen k) x v

theorem nv_seed_fderiv_fderiv_apply_sum {ξ : NvNoise d} (hξ : ξ ∈ nvGood d) (x v w : Vec d) :
    fderiv ℝ (fderiv ℝ (nv_seed ξ)) x v w
      = ∑ k ∈ cellsNear x, ∑' p,
          ξ (k, p) * fderiv ℝ (fderiv ℝ (fun y ↦ cellKernelCoeff (nv_cen k) y p)) x v w := by
  have h := nv_iteratedFDeriv_seed hξ x (i := 2) (by norm_num)
  have h2 := congrArg (fun L : ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ Vec d) ℝ ↦
    L ![v, w]) h
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h2
  rw [h2]
  have := map_sum (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 ↦ Vec d) ℝ ![v, w])
    (fun k ↦ iteratedFDeriv ℝ 2 (nv_cellFun ξ k) x) (cellsNear x)
  refine this.trans (Finset.sum_congr rfl fun k _ ↦ ?_)
  show iteratedFDeriv ℝ 2 (nv_cellFun ξ k) x ![v, w] = _
  rw [iteratedFDeriv_two_apply]
  exact nv_row_fderiv_fderiv_apply (nv_summable_of_mem_nvGood hξ k) (nv_cen k) x v w

end

end SuperdiffusionCLT.Assumptions.ShellLaw.Model
