/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.SeedCovarianceB

/-!
# Finite linear combinations of the seed field are centred Gaussians

For points `x j` and real coefficients `t j` (`j` in a finite type) the combination
`∑ j, t j * nv_seed ξ (x j)` is the sum of the series `∑ i, nv_comb t x i * ξ i` over the noise
index, with `nv_comb` square summable of total `nvVar t x = ∑ j, ∑ l, t j * t l * nvCov (x j) (x l)`.

## Main results

* `nv_sum_cell_integral`: the squares of the cell weights integrate to the covariance
* `nv_hasSum_comb_sq`: `∑ i, nv_comb t x i ^ 2 = nvVar t x`
* `nv_hasSum_comb_mul`: the series representation of the combination on the good event
* `nv_map_comb_eq_gaussianReal`: the law of the combination is `gaussianReal 0 (nvVar t x)`
-/

@[expose] public section

namespace SuperdiffusionCLT.Assumptions.ShellLaw.Model

open Homogenization MeasureTheory ProbabilityTheory

noncomputable section

variable {d : ℕ}

theorem nv_mem_cellsNear_of_support {x z : Vec d} {k : Fin d → ℤ}
    (hz : radialBump d (x - z) ≠ 0) (hk : cellWeight d (z - nv_cen k) ≠ 0) :
    k ∈ cellsNear x := by
  refine nv_mem_cellsNear_of_lt fun i ↦ ?_
  have h1 := abs_lt_half_of_radialBump_ne_zero hz i
  have h2 := abs_lt_half_of_cellWeight_ne_zero hk i
  simp only [Pi.sub_apply, nv_cen] at h1 h2
  have h3 : x i - (k i : ℝ) / 2 = (x i - z i) + (z i - (k i : ℝ) / 2) := by ring
  rw [h3]
  exact lt_of_le_of_lt (abs_add_le _ _) (by linarith only [h1, h2])

theorem nv_sum_cellWeight_sq {x z : Vec d} (K : Finset (Fin d → ℤ)) (hK : cellsNear x ⊆ K)
    (hz : radialBump d (x - z) ≠ 0) :
    ∑ k ∈ K, cellWeight d (z - nv_cen k) ^ 2 = 1 := by
  have h1 : HasSum (fun k : Fin d → ℤ ↦ cellWeight d (z - nv_cen k) ^ 2) 1 :=
    hasSum_cellWeight_sq z
  have h2 : HasSum (fun k : Fin d → ℤ ↦ cellWeight d (z - nv_cen k) ^ 2)
      (∑ k ∈ K, cellWeight d (z - nv_cen k) ^ 2) :=
    hasSum_sum_of_ne_finset_zero (fun k hk ↦ by
      have : cellWeight d (z - nv_cen k) = 0 := by
        by_contra hne
        exact hk (hK (nv_mem_cellsNear_of_support hz hne))
      rw [this]; norm_num)
  exact h2.unique h1

theorem nv_integrable_cell (k : Fin d → ℤ) (x y : Vec d) :
    Integrable fun z : Vec d ↦
      cellWeight d (z - nv_cen k) ^ 2 * (radialBump d (x - z) * radialBump d (y - z)) := by
  have hw : Continuous fun z : Vec d ↦ cellWeight d (z - nv_cen k) ^ 2 :=
    (cellWeight_contDiff.continuous.comp (continuous_id.sub continuous_const)).pow 2
  exact (hw.mul ((nv_continuous_bump_sub x).mul (nv_continuous_bump_sub y))).integrable_of_hasCompactSupport
    (((nv_hasCompactSupport_bump_sub x).mul_right).mul_left)

/-- **The cell kernels add up to the covariance.** -/
theorem nv_sum_cell_integral (x y : Vec d) (K : Finset (Fin d → ℤ)) (hK : cellsNear x ⊆ K) :
    ∑ k ∈ K, ∫ z, cellWeight d (z - nv_cen k) ^ 2 *
        (radialBump d (x - z) * radialBump d (y - z)) = nvCov x y := by
  rw [← integral_finsetSum _ fun k _ ↦ nv_integrable_cell k x y]
  unfold nvCov
  refine integral_congr_ae (Filter.Eventually.of_forall fun z ↦ ?_)
  simp only
  rw [← Finset.sum_mul]
  by_cases hz : radialBump d (x - z) = 0
  · simp [hz]
  · rw [nv_sum_cellWeight_sq K hK hz, one_mul]

theorem nv_hasSum_idx {f : NvIdx d → ℝ} (K : Finset (Fin d → ℤ))
    (hK : ∀ k ∉ K, ∀ p, f (k, p) = 0) (hf : ∀ k, Summable fun p ↦ |f (k, p)|) :
    HasSum f (∑ k ∈ K, ∑' p, f (k, p)) := by
  have hs : Summable f := by
    refine Summable.of_norm ?_
    have : Summable fun i : NvIdx d ↦ |f i| := by
      refine (summable_prod_of_nonneg (fun _ ↦ abs_nonneg _)).2 ⟨hf, ?_⟩
      refine summable_of_ne_finset_zero (s := K) fun k hk ↦ ?_
      simp [hK k hk]
    simpa [Real.norm_eq_abs] using this
  have h1 := hs.hasSum.prod_fiberwise (g := fun k ↦ ∑' p, f (k, p))
    (fun k ↦ ((hf k).of_abs).hasSum)
  have h2 : HasSum (fun k ↦ ∑' p, f (k, p)) (∑ k ∈ K, ∑' p, f (k, p)) :=
    hasSum_sum_of_ne_finset_zero (fun k hk ↦ by simp [hK k hk])
  rw [← h1.unique h2]
  exact hs.hasSum

variable {ι : Type*} [Fintype ι]

/-- The coefficient of the noise `ξ (k, p)` in the combination `∑ j, t j * seed (x j)`. -/
def nv_comb (t : ι → ℝ) (x : ι → Vec d) (i : NvIdx d) : ℝ :=
  ∑ j, t j * cellKernelCoeff (nv_cen i.1) (x j) i.2

/-- The variance of the combination `∑ j, t j * seed (x j)` of the seed field. -/
def nvVar (t : ι → ℝ) (x : ι → Vec d) : ℝ := ∑ j, ∑ l, t j * t l * nvCov (x j) (x l)

/-- The cells meeting the supports at one of the points. -/
def nv_cells (x : ι → Vec d) : Finset (Fin d → ℤ) :=
  Finset.univ.biUnion fun j ↦ cellsNear (x j)

theorem nv_comb_eq_zero (t : ι → ℝ) (x : ι → Vec d) {k : Fin d → ℤ} (hk : k ∉ nv_cells x)
    (p : NvFrame d) : nv_comb t x (k, p) = 0 := by
  unfold nv_comb
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  have hk' : k ∉ cellsNear (x j) := fun h ↦
    hk (Finset.mem_biUnion.2 ⟨j, Finset.mem_univ j, h⟩)
  simp only
  have h0 : cellKernelCoeff (nv_cen k) (x j) p = 0 :=
    cellKernelCoeff_eq_zero_of_not_mem_cellsNear hk' p
  rw [h0, mul_zero]

theorem nv_abs_comb_le (t : ι → ℝ) (x : ι → Vec d) (i : NvIdx d) :
    |nv_comb t x i| ≤ (∑ j, |t j|) * nv_b d i.2 := by
  unfold nv_comb
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ ↦ ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (nv_abs_coeff_le _ _ _) (abs_nonneg _)

theorem nv_hasSum_comb_sq_fiber (t : ι → ℝ) (x : ι → Vec d) (k : Fin d → ℤ) :
    HasSum (fun p ↦ nv_comb t x (k, p) ^ 2)
      (∑ j, ∑ l, t j * t l * ∫ z, cellWeight d (z - nv_cen k) ^ 2 *
        (radialBump d (x j - z) * radialBump d (x l - z))) := by
  have h : ∀ p, nv_comb t x (k, p) ^ 2 = ∑ j, ∑ l, t j * t l *
      (cellKernelCoeff (nv_cen k) (x j) p * cellKernelCoeff (nv_cen k) (x l) p) := by
    intro p
    unfold nv_comb
    simp only
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun l _ ↦ by ring
  simp_rw [h]
  exact hasSum_sum fun j _ ↦ hasSum_sum fun l _ ↦
    (hasSum_cellKernelCoeff_mul (nv_cen k) (x j) (x l)).mul_left (t j * t l)

/-- **Parseval for the combination**: `∑ i, nv_comb t x i ^ 2 = nvVar t x`. -/
theorem nv_hasSum_comb_sq (t : ι → ℝ) (x : ι → Vec d) :
    HasSum (fun i ↦ nv_comb t x i ^ 2) (nvVar t x) := by
  have h := nv_hasSum_idx (f := fun i : NvIdx d ↦ nv_comb t x i ^ 2) (nv_cells x)
    (fun k hk p ↦ by simp [nv_comb_eq_zero t x hk p])
    (fun k ↦ (nv_hasSum_comb_sq_fiber t x k).summable.abs)
  convert h using 1
  simp_rw [(nv_hasSum_comb_sq_fiber t x _).tsum_eq]
  unfold nvVar
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [← Finset.mul_sum, nv_sum_cell_integral (x j) (x l) (nv_cells x)
    (Finset.subset_biUnion_of_mem (fun j ↦ cellsNear (x j)) (Finset.mem_univ j))]

theorem nvVar_nonneg (t : ι → ℝ) (x : ι → Vec d) : 0 ≤ nvVar t x :=
  (nv_hasSum_comb_sq t x).nonneg fun _ ↦ sq_nonneg _

/-- On the good event the combination of seed values is the series over the noise index. -/
theorem nv_hasSum_comb_mul {ξ : NvNoise d} (hξ : ξ ∈ nvGood d) (t : ι → ℝ) (x : ι → Vec d) :
    HasSum (fun i : NvIdx d ↦ nv_comb t x i * ξ i) (∑ j, t j * nv_seed ξ (x j)) := by
  have hfib : ∀ (k : Fin d → ℤ) (j : ι), Summable fun p : NvFrame d ↦
      ξ (k, p) * cellKernelCoeff (nv_cen k) (x j) p := fun k j ↦
    Summable.of_norm_bounded (nv_summable_of_mem_nvGood hξ k) fun p ↦ by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (nv_abs_coeff_le _ _ _) (abs_nonneg _) |>.trans_eq rfl
  have h := nv_hasSum_idx (f := fun i : NvIdx d ↦ nv_comb t x i * ξ i) (nv_cells x)
    (fun k hk p ↦ by simp [nv_comb_eq_zero t x hk p])
    (fun k ↦ by
      refine Summable.of_nonneg_of_le (fun p ↦ abs_nonneg _) (fun p ↦ ?_)
        ((nv_summable_of_mem_nvGood hξ k).mul_left (∑ j, |t j|))
      rw [abs_mul]
      have := nv_abs_comb_le t x (k, p)
      nlinarith only [this, abs_nonneg (ξ (k, p))])
  convert h using 1
  have hcell : ∀ k : Fin d → ℤ, ∑' p, nv_comb t x (k, p) * ξ (k, p)
      = ∑ j, t j * nv_cellFun ξ k (x j) := by
    intro k
    unfold nv_comb
    simp only [nv_cellFun_def]
    have e : ∀ p, (∑ j, t j * cellKernelCoeff (nv_cen k) (x j) p) * ξ (k, p)
        = ∑ j, t j * (ξ (k, p) * cellKernelCoeff (nv_cen k) (x j) p) := by
      intro p
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    simp_rw [e]
    rw [Summable.tsum_finsetSum fun j _ ↦ (hfib k j).mul_left (t j)]
    exact Finset.sum_congr rfl fun j _ ↦ (tsum_mul_left)
  simp_rw [hcell]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← Finset.mul_sum, nv_seed_eq_sum hξ (x j)]
  congr 1
  refine Finset.sum_subset
    (Finset.subset_biUnion_of_mem (fun j ↦ cellsNear (x j)) (Finset.mem_univ j)) fun k _ hk ↦ ?_
  rw [nv_cellFun_def]
  refine (tsum_congr fun p ↦ ?_).trans tsum_zero
  have h0 : cellKernelCoeff (nv_cen k) (x j) p = 0 :=
    cellKernelCoeff_eq_zero_of_not_mem_cellsNear hk p
  rw [h0, mul_zero]

theorem nv_measurable_comb (t : ι → ℝ) (x : ι → Vec d) :
    Measurable fun ξ : NvNoise d ↦ ∑ j, t j * nv_seed ξ (x j) :=
  Finset.measurable_sum _ fun j _ ↦ (nv_measurable_seed (x j)).const_mul (t j)

/-- **Gaussianity of finite combinations.** Under the noise law, `∑ j, t j * nv_seed ξ (x j)`
is a centred real Gaussian with variance `∑ j, ∑ l, t j * t l * nvCov (x j) (x l)`. -/
theorem nv_map_comb_eq_gaussianReal (t : ι → ℝ) (x : ι → Vec d) :
    (nvNoiseLaw d).map (fun ξ ↦ ∑ j, t j * nv_seed ξ (x j))
      = gaussianReal 0 (nvVar t x).toNNReal := by
  have h := nv_map_eq_gaussianReal_of_hasSum (nv_comb t x)
    (by simpa only using (nv_hasSum_comb_sq t x).summable) _ (nv_measurable_comb t x)
    ((nv_ae_mem_nvGood d).mono fun ξ hξ ↦ nv_hasSum_comb_mul hξ t x)
  rw [(nv_hasSum_comb_sq t x).tsum_eq] at h
  exact h

end

end SuperdiffusionCLT.Assumptions.ShellLaw.Model
