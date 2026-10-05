/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.GaussianSeries

/-!
# One cell: the frame series is `C^2` with termwise derivatives

For a row `r : NvFrame d → ℝ` with `∑ p, |r p| * nv_b d p < ∞` and a cell centre `c`, the function
`x ↦ ∑' p, r p * cellKernelCoeff c x p` is `C^2`, its first two Fréchet derivatives are the
termwise series, and the iterated derivatives are bounded by `∑' p, |r p| * nv_b d p`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Assumptions.ShellLaw.Model

open Homogenization Set Real MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The cell centre `k / 2`. -/
def nv_cen (k : Fin d → ℤ) : Vec d := fun i ↦ (k i : ℝ) / 2

/-- The frame series of one cell with coefficient row `r`. -/
def nv_rowFun (r : NvFrame d → ℝ) (c : Vec d) (x : Vec d) : ℝ :=
  ∑' p, r p * cellKernelCoeff c x p

theorem nv_term_contDiff (r : NvFrame d → ℝ) (c : Vec d) (p : NvFrame d) :
    ContDiff ℝ 2 fun x ↦ r p * cellKernelCoeff c x p :=
  contDiff_const.mul
    ((contDiff_cellKernelCoeff c p).of_le (WithTop.coe_le_coe.2 le_top))

theorem nv_norm_term_le (r : NvFrame d → ℝ) (c x : Vec d) (p : NvFrame d) (i : ℕ) (hi : i ≤ 2) :
    ‖iteratedFDeriv ℝ i (fun x ↦ r p * cellKernelCoeff c x p) x‖ ≤ |r p| * nv_b d p := by
  have hc : ContDiffAt ℝ i (fun x ↦ cellKernelCoeff c x p) x :=
    ((contDiff_cellKernelCoeff c p).of_le (by exact_mod_cast le_top)).contDiffAt
  have h := iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (a := r p) hc
  have h2 : iteratedFDeriv ℝ i (fun x ↦ r p * cellKernelCoeff c x p) x
      = r p • iteratedFDeriv ℝ i (fun x ↦ cellKernelCoeff c x p) x := by
    simpa only [smul_eq_mul] using h
  rw [h2, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (nv_b_bound d c x p i hi) (abs_nonneg _)

theorem nv_row_contDiff {r : NvFrame d → ℝ} (hr : Summable fun p ↦ |r p| * nv_b d p) (c : Vec d) :
    ContDiff ℝ 2 (nv_rowFun r c) :=
  contDiff_tsum (v := fun _ p ↦ |r p| * nv_b d p) (fun p ↦ nv_term_contDiff r c p)
    (fun _ _ ↦ hr) (fun i p x hi ↦ nv_norm_term_le r c x p i (by exact_mod_cast hi))

theorem nv_row_iteratedFDeriv {r : NvFrame d → ℝ} (hr : Summable fun p ↦ |r p| * nv_b d p)
    (c x : Vec d) {i : ℕ} (hi : i ≤ 2) :
    iteratedFDeriv ℝ i (nv_rowFun r c) x
      = ∑' p, iteratedFDeriv ℝ i (fun x ↦ r p * cellKernelCoeff c x p) x :=
  iteratedFDeriv_tsum_apply (v := fun _ p ↦ |r p| * nv_b d p) (fun p ↦ nv_term_contDiff r c p)
    (fun _ _ ↦ hr) (fun i p x hi ↦ nv_norm_term_le r c x p i (by exact_mod_cast hi))
    (by exact_mod_cast hi) x

theorem nv_row_summable_iteratedFDeriv {r : NvFrame d → ℝ}
    (hr : Summable fun p ↦ |r p| * nv_b d p) (c x : Vec d) {i : ℕ} (hi : i ≤ 2) :
    Summable fun p ↦ iteratedFDeriv ℝ i (fun x ↦ r p * cellKernelCoeff c x p) x :=
  Summable.of_norm_bounded hr fun p ↦ nv_norm_term_le r c x p i hi

/-- Bound on the iterated derivatives of one row series. -/
theorem nv_row_norm_iteratedFDeriv_le {r : NvFrame d → ℝ}
    (hr : Summable fun p ↦ |r p| * nv_b d p) (c x : Vec d) {i : ℕ} (hi : i ≤ 2) :
    ‖iteratedFDeriv ℝ i (nv_rowFun r c) x‖ ≤ ∑' p, |r p| * nv_b d p := by
  rw [nv_row_iteratedFDeriv hr c x hi]
  exact tsum_of_norm_bounded hr.hasSum fun p ↦ nv_norm_term_le r c x p i hi

/-- First derivative of a row series, termwise. -/
theorem nv_row_fderiv_apply {r : NvFrame d → ℝ} (hr : Summable fun p ↦ |r p| * nv_b d p)
    (c x v : Vec d) :
    fderiv ℝ (nv_rowFun r c) x v = ∑' p, r p * fderiv ℝ (fun x ↦ cellKernelCoeff c x p) x v := by
  have h1 := nv_row_iteratedFDeriv hr c x (i := 1) (by norm_num)
  have hs := nv_row_summable_iteratedFDeriv hr c x (i := 1) (by norm_num)
  have h2 := congrArg (fun L : ContinuousMultilinearMap ℝ (fun _ : Fin 1 ↦ Vec d) ℝ ↦
    L (fun _ ↦ v)) h1
  simp only [iteratedFDeriv_one_apply] at h2
  rw [h2]
  have := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 ↦ Vec d) ℝ (fun _ ↦ v)).map_tsum hs
  refine this.trans (tsum_congr fun p ↦ ?_)
  have hc : DifferentiableAt ℝ (fun x ↦ cellKernelCoeff c x p) x :=
    ((contDiff_cellKernelCoeff c p).differentiable (by simp)) x
  show iteratedFDeriv ℝ 1 (fun x ↦ r p * cellKernelCoeff c x p) x (fun _ ↦ v) = _
  rw [iteratedFDeriv_one_apply, fderiv_const_mul hc]
  rfl

/-- Second derivative of a row series, termwise. -/
theorem nv_row_fderiv_fderiv_apply {r : NvFrame d → ℝ} (hr : Summable fun p ↦ |r p| * nv_b d p)
    (c x v w : Vec d) :
    fderiv ℝ (fderiv ℝ (nv_rowFun r c)) x v w
      = ∑' p, r p * fderiv ℝ (fderiv ℝ (fun x ↦ cellKernelCoeff c x p)) x v w := by
  have h1 := nv_row_iteratedFDeriv hr c x (i := 2) (by norm_num)
  have hs := nv_row_summable_iteratedFDeriv hr c x (i := 2) (by norm_num)
  have h2 := congrArg (fun L : ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ Vec d) ℝ ↦
    L ![v, w]) h1
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h2
  rw [h2]
  have := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 ↦ Vec d) ℝ ![v, w]).map_tsum hs
  refine this.trans (tsum_congr fun p ↦ ?_)
  have hc : ContDiffAt ℝ 2 (fun x ↦ cellKernelCoeff c x p) x :=
    ((contDiff_cellKernelCoeff c p).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt
  show iteratedFDeriv ℝ 2 (fun x ↦ r p * cellKernelCoeff c x p) x ![v, w] = _
  have h3 : iteratedFDeriv ℝ 2 (fun x ↦ r p * cellKernelCoeff c x p) x
      = r p • iteratedFDeriv ℝ 2 (fun x ↦ cellKernelCoeff c x p) x := by
    simpa only [smul_eq_mul] using iteratedFDeriv_const_smul_apply' (a := r p) hc
  rw [h3, smul_apply, iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul]

end

end SuperdiffusionCLT.Assumptions.ShellLaw.Model
