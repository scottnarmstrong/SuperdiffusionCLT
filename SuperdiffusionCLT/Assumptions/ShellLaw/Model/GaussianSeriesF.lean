/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.GaussianSeriesE
public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.LawUniquenessC

/-!
# Measurability of the seed field and the scalar seed law

Value, first and second derivative of the seed at a point (and directions) are measurable
functions of the noise. Hence `ξ ↦ nv_seedMap ε ξ` into `ScalarC2Field d` is measurable and the
scalar seed law `nv_seedLaw ε` is the push-forward of the noise law, a probability measure.

## Main results

* `nv_measurable_seed`, `nv_measurable_fderiv_seed`, `nv_measurable_fderiv_fderiv_seed`
* `nv_seedField`, `nv_seedMap`, `nv_measurable_seedMap`
* `nv_seedLaw`, `nv_seedLaw.isProbabilityMeasure`
-/

@[expose] public section

namespace SuperdiffusionCLT.Assumptions.ShellLaw.Model

open Homogenization Set Real MeasureTheory Filter Topology

noncomputable section

variable {d : ℕ}

open Classical in
/-- A good-event-truncated row series with coefficients `a p` is measurable in the noise. -/
theorem nv_measurable_row_tsum (k : Fin d → ℤ) (a : NvFrame d → ℝ) (C : ℝ)
    (ha : ∀ p, |a p| ≤ C * nv_b d p) :
    Measurable fun ξ : NvNoise d ↦ if ξ ∈ nvGood d then ∑' p, ξ (k, p) * a p else 0 := by
  have hu : ∀ s : Finset (NvFrame d), Measurable fun ξ : NvNoise d ↦
      if ξ ∈ nvGood d then ∑ p ∈ s, ξ (k, p) * a p else 0 := fun s ↦
    Measurable.ite (measurableSet_nvGood d)
      (Finset.measurable_sum _ fun p _ ↦ (nv_measurable_coord d (k, p)).mul_const (a p))
      measurable_const
  refine measurable_of_tendsto_metrizable' (atTop : Filter (Finset (NvFrame d))) hu ?_
  rw [tendsto_pi_nhds]
  intro ξ
  by_cases hξ : ξ ∈ nvGood d
  · simp only [hξ, ↓reduceIte]
    have hs : Summable fun p ↦ ξ (k, p) * a p := by
      refine Summable.of_norm_bounded ((nv_summable_of_mem_nvGood hξ k).mul_left C) fun p ↦ ?_
      rw [Real.norm_eq_abs, abs_mul]
      calc |ξ (k, p)| * |a p| ≤ |ξ (k, p)| * (C * nv_b d p) :=
            mul_le_mul_of_nonneg_left (ha p) (abs_nonneg _)
        _ = C * (|ξ (k, p)| * nv_b d p) := by ring
    exact hs.hasSum
  · simp only [hξ, ↓reduceIte]
    exact tendsto_const_nhds

theorem nv_abs_coeff_le (c x : Vec d) (p : NvFrame d) : |cellKernelCoeff c x p| ≤ nv_b d p := by
  have h := nv_b_bound d c x p 0 (by norm_num)
  rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h

theorem nv_abs_fderiv_coeff_le (c x v : Vec d) (p : NvFrame d) :
    |fderiv ℝ (fun y ↦ cellKernelCoeff c y p) x v| ≤ ‖v‖ * nv_b d p := by
  have h := nv_b_bound d c x p 1 (by norm_num)
  rw [norm_iteratedFDeriv_one] at h
  have h2 := (fderiv ℝ (fun y ↦ cellKernelCoeff c y p) x).le_opNorm v
  rw [Real.norm_eq_abs] at h2
  nlinarith only [h, h2, norm_nonneg v]

theorem nv_abs_fderiv_fderiv_coeff_le (c x v w : Vec d) (p : NvFrame d) :
    |fderiv ℝ (fderiv ℝ (fun y ↦ cellKernelCoeff c y p)) x v w| ≤ ‖v‖ * ‖w‖ * nv_b d p := by
  have h := nv_b_bound d c x p 2 (by norm_num)
  rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one] at h
  set L := fderiv ℝ (fderiv ℝ (fun y ↦ cellKernelCoeff c y p)) x with hL
  have h1 := L.le_opNorm v
  have h2 := (L v).le_opNorm w
  rw [Real.norm_eq_abs] at h2
  have h3 : ‖L v‖ * ‖w‖ ≤ ‖L‖ * ‖v‖ * ‖w‖ :=
    mul_le_mul_of_nonneg_right h1 (norm_nonneg w)
  have h4 : ‖L‖ * ‖v‖ * ‖w‖ ≤ nv_b d p * ‖v‖ * ‖w‖ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h (norm_nonneg v)) (norm_nonneg w)
  linarith only [h2, h3, h4, show nv_b d p * ‖v‖ * ‖w‖ = ‖v‖ * ‖w‖ * nv_b d p by ring]

theorem nv_seed_of_not_mem {ξ : NvNoise d} (hξ : ξ ∉ nvGood d) : nv_seed ξ = fun _ ↦ 0 := by
  funext x; simp [nv_seed, hξ]

open Classical in
theorem nv_measurable_seed (x : Vec d) : Measurable fun ξ : NvNoise d ↦ nv_seed ξ x := by
  have hm : Measurable fun ξ : NvNoise d ↦ ∑ k ∈ cellsNear x,
      (if ξ ∈ nvGood d then ∑' p, ξ (k, p) * cellKernelCoeff (nv_cen k) x p else 0) :=
    Finset.measurable_sum _ fun k _ ↦
      nv_measurable_row_tsum k _ 1 fun p ↦ by rw [one_mul]; exact nv_abs_coeff_le _ x p
  convert hm using 1
  funext ξ
  by_cases hξ : ξ ∈ nvGood d
  · simp only [hξ, ↓reduceIte]
    rw [nv_seed_eq_sum hξ x]
    rfl
  · simp [nv_seed_of_not_mem hξ, hξ]

open Classical in
theorem nv_measurable_fderiv_seed (x v : Vec d) :
    Measurable fun ξ : NvNoise d ↦ fderiv ℝ (nv_seed ξ) x v := by
  have hm : Measurable fun ξ : NvNoise d ↦ ∑ k ∈ cellsNear x,
      (if ξ ∈ nvGood d then ∑' p, ξ (k, p) *
        fderiv ℝ (fun y ↦ cellKernelCoeff (nv_cen k) y p) x v else 0) :=
    Finset.measurable_sum _ fun k _ ↦
      nv_measurable_row_tsum k _ ‖v‖ fun p ↦ nv_abs_fderiv_coeff_le _ x v p
  convert hm using 1
  funext ξ
  by_cases hξ : ξ ∈ nvGood d
  · simp only [hξ, ↓reduceIte]
    exact nv_seed_fderiv_apply_sum hξ x v
  · simp [nv_seed_of_not_mem hξ, hξ]

open Classical in
theorem nv_measurable_fderiv_fderiv_seed (x v w : Vec d) :
    Measurable fun ξ : NvNoise d ↦ fderiv ℝ (fderiv ℝ (nv_seed ξ)) x v w := by
  have hm : Measurable fun ξ : NvNoise d ↦ ∑ k ∈ cellsNear x,
      (if ξ ∈ nvGood d then ∑' p, ξ (k, p) *
        fderiv ℝ (fderiv ℝ (fun y ↦ cellKernelCoeff (nv_cen k) y p)) x v w else 0) :=
    Finset.measurable_sum _ fun k _ ↦
      nv_measurable_row_tsum k _ (‖v‖ * ‖w‖) fun p ↦ nv_abs_fderiv_fderiv_coeff_le _ x v w p
  convert hm using 1
  funext ξ
  by_cases hξ : ξ ∈ nvGood d
  · simp only [hξ, ↓reduceIte]
    exact nv_seed_fderiv_fderiv_apply_sum hξ x v w
  · simp [nv_seed_of_not_mem hξ, hξ]

/-! ## Bundling into the scalar carrier -/

/-- The seed field of the noise `ξ` as an element of the scalar `C^2` carrier. -/
def nv_seedField (ξ : NvNoise d) : ScalarC2Field d :=
  ScalarC2Field.ofContDiff (nv_seed ξ) (nv_contDiff_seed ξ)

/-- The seed field with the scale `ε`. -/
def nv_seedMap (ε : ℝ) (ξ : NvNoise d) : ScalarC2Field d :=
  ScalarC2Field.smulConst ε (nv_seedField ξ)

theorem nv_seedMap_apply (ε : ℝ) (ξ : NvNoise d) (x : Vec d) :
    nv_seedMap ε ξ x = ε * nv_seed ξ x := rfl

theorem nv_measurable_seedField : Measurable (nv_seedField (d := d)) := by
  rw [nv_measurable_scalar_iff_eval]
  refine ⟨fun x ↦ nv_measurable_seed x, fun x v ↦ nv_measurable_fderiv_seed x v,
    fun x v w ↦ nv_measurable_fderiv_fderiv_seed x v w⟩

theorem nv_measurable_seedMap (ε : ℝ) : Measurable (nv_seedMap (d := d) ε) :=
  (ScalarC2Field.measurable_smulConst ε).comp nv_measurable_seedField

/-- The scalar seed law: the push-forward of the noise law under the series field. -/
def nv_seedLaw (d : ℕ) (ε : ℝ) : Measure (ScalarC2Field d) :=
  (nvNoiseLaw d).map (nv_seedMap ε)

instance nv_seedLaw.isProbabilityMeasure (d : ℕ) (ε : ℝ) : IsProbabilityMeasure (nv_seedLaw d ε) :=
  (Measure.isProbabilityMeasure_map_iff (nv_measurable_seedMap ε).aemeasurable).2 inferInstance

end

end SuperdiffusionCLT.Assumptions.ShellLaw.Model
