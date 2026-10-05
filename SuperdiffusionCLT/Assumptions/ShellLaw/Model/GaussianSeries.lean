/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.CoeffDecayC
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# The noise space and the good event of the Gaussian series

The noise space is `nvNoise d := (Fin d → ℤ) × ((Fin d → ℤ) ⊕ (Fin d → ℤ)) → ℝ` (cell, frame
index) with the product of standard Gaussians. The good event `nvGood d` is the set where for
every cell the series `∑ p, |ξ (k, p)| * nv_b p` converges; it is measurable and has probability one.

## Main results

* `nvNoiseLaw`, `nvNoiseLaw.isProbabilityMeasure`
* `nvGood`, `measurableSet_nvGood`, `nvNoiseLaw_nvGood`
* `nv_summable_of_mem_nvGood`
-/

@[expose] public section

namespace SuperdiffusionCLT.Assumptions.ShellLaw.Model

open Homogenization Set Real MeasureTheory ProbabilityTheory

noncomputable section

/-- The frame index of one cell. -/
abbrev NvFrame (d : ℕ) := (Fin d → ℤ) ⊕ (Fin d → ℤ)

/-- The index of the noise: a cell `k` and a frame index `p`. -/
abbrev NvIdx (d : ℕ) := (Fin d → ℤ) × NvFrame d

/-- The noise space. -/
abbrev NvNoise (d : ℕ) := NvIdx d → ℝ

/-- The law of the noise: iid standard Gaussians. -/
def nvNoiseLaw (d : ℕ) : Measure (NvNoise d) :=
  Measure.infinitePi fun _ : NvIdx d ↦ gaussianReal 0 1

instance nvNoiseLaw.isProbabilityMeasure (d : ℕ) : IsProbabilityMeasure (nvNoiseLaw d) := by
  unfold nvNoiseLaw; infer_instance

/-- The summable dominating sequence over the frame index. -/
def nv_b (d : ℕ) : NvFrame d → ℝ :=
  Classical.choose (exists_summable_bound_iteratedFDeriv_cellKernelCoeff (d := d))

theorem nv_b_summable (d : ℕ) : Summable (nv_b d) :=
  (Classical.choose_spec (exists_summable_bound_iteratedFDeriv_cellKernelCoeff (d := d))).1

theorem nv_b_nonneg (d : ℕ) (p : NvFrame d) : 0 ≤ nv_b d p :=
  (Classical.choose_spec (exists_summable_bound_iteratedFDeriv_cellKernelCoeff (d := d))).2.1 p

theorem nv_b_bound (d : ℕ) (c x : Vec d) (p : NvFrame d) (i : ℕ) (hi : i ≤ 2) :
    ‖iteratedFDeriv ℝ i (fun x ↦ cellKernelCoeff c x p) x‖ ≤ nv_b d p :=
  (Classical.choose_spec (exists_summable_bound_iteratedFDeriv_cellKernelCoeff (d := d))).2.2
    c x p i hi

/-- The good event: for every cell the weighted series of the noise is finite. -/
def nvGood (d : ℕ) : Set (NvNoise d) :=
  {ξ | ∀ k : Fin d → ℤ, ∑' p : NvFrame d, ENNReal.ofReal (|ξ (k, p)| * nv_b d p) ≠ ⊤}

theorem nv_measurable_coord (d : ℕ) (i : NvIdx d) : Measurable fun ξ : NvNoise d ↦ ξ i :=
  measurable_pi_apply i

theorem measurableSet_nvGood (d : ℕ) : MeasurableSet (nvGood d) := by
  have : nvGood d = ⋂ k : Fin d → ℤ,
      {ξ : NvNoise d | ∑' p : NvFrame d, ENNReal.ofReal (|ξ (k, p)| * nv_b d p) ≠ ⊤} := by
    ext ξ; simp [nvGood]
  rw [this]
  refine MeasurableSet.iInter fun k ↦ ?_
  have hm : Measurable fun ξ : NvNoise d ↦
      ∑' p : NvFrame d, ENNReal.ofReal (|ξ (k, p)| * nv_b d p) :=
    Measurable.tsum fun p ↦
      ENNReal.measurable_ofReal.comp
        ((continuous_abs.measurable.comp (nv_measurable_coord d (k, p))).mul_const (nv_b d p))
  exact (hm (measurableSet_singleton ⊤)).compl

theorem nv_summable_of_mem_nvGood {d : ℕ} {ξ : NvNoise d} (hξ : ξ ∈ nvGood d) (k : Fin d → ℤ) :
    Summable fun p : NvFrame d ↦ |ξ (k, p)| * nv_b d p := by
  have h := ENNReal.summable_toReal (hξ k)
  refine h.congr fun p ↦ ?_
  exact ENNReal.toReal_ofReal (mul_nonneg (abs_nonneg _) (nv_b_nonneg d p))

/-- For a fixed cell, the weighted series is almost surely finite. -/
theorem nv_ae_tsum_ne_top (d : ℕ) (k : Fin d → ℤ) :
    ∀ᵐ ξ ∂(nvNoiseLaw d), ∑' p : NvFrame d, ENNReal.ofReal (|ξ (k, p)| * nv_b d p) ≠ ⊤ := by
  have hint : Integrable (id : ℝ → ℝ) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable le_rfl
  have hfin : ∫⁻ y, ‖y‖ₑ ∂(gaussianReal 0 1) < ⊤ := hint.hasFiniteIntegral
  have hmeas : ∀ p : NvFrame d, Measurable fun ξ : NvNoise d ↦
      ENNReal.ofReal (|ξ (k, p)| * nv_b d p) := fun p ↦
    ENNReal.measurable_ofReal.comp ((continuous_abs.measurable.comp (nv_measurable_coord d (k, p))).mul_const (nv_b d p))
  have hpp : ∀ p : NvFrame d, ∫⁻ ξ, ENNReal.ofReal (|ξ (k, p)| * nv_b d p) ∂(nvNoiseLaw d)
      = (∫⁻ y, ‖y‖ₑ ∂(gaussianReal 0 1)) * ENNReal.ofReal (nv_b d p) := by
    intro p
    have hmp := measurePreserving_eval_infinitePi (fun _ : NvIdx d ↦ gaussianReal 0 1) (k, p)
    have h1 : ∫⁻ ξ, ENNReal.ofReal (|ξ (k, p)| * nv_b d p) ∂(nvNoiseLaw d)
        = ∫⁻ ξ, ‖ξ (k, p)‖ₑ * ENNReal.ofReal (nv_b d p) ∂(nvNoiseLaw d) := by
      refine lintegral_congr fun ξ ↦ ?_
      rw [ENNReal.ofReal_mul (abs_nonneg _), ← ofReal_norm, Real.norm_eq_abs]
    rw [h1, lintegral_mul_const _ ((nv_measurable_coord d (k, p)).enorm)]
    congr 1
    have := hmp.lintegral_comp (f := fun y : ℝ ↦ ‖y‖ₑ) measurable_enorm
    exact this
  have htot : ∫⁻ ξ, ∑' p : NvFrame d, ENNReal.ofReal (|ξ (k, p)| * nv_b d p) ∂(nvNoiseLaw d) < ⊤ := by
    rw [lintegral_tsum fun p ↦ (hmeas p).aemeasurable]
    simp_rw [hpp]
    rw [ENNReal.tsum_mul_left]
    refine ENNReal.mul_lt_top hfin ?_
    have := (nv_b_summable d).toNNReal.hasSum
    have h2 : ∑' p : NvFrame d, ENNReal.ofReal (nv_b d p) = ∑' p, (↑((nv_b d p).toNNReal) : ENNReal) :=
      rfl
    rw [h2]
    exact (ENNReal.tsum_coe_ne_top_iff_summable.2 (nv_b_summable d).toNNReal).lt_top
  exact (ae_lt_top (Measurable.tsum hmeas) htot.ne).mono fun ξ hξ ↦ hξ.ne

/-- The good event has probability one. -/
theorem nv_ae_mem_nvGood (d : ℕ) : ∀ᵐ ξ ∂(nvNoiseLaw d), ξ ∈ nvGood d := by
  have := (ae_all_iff (μ := nvNoiseLaw d)).2 (nv_ae_tsum_ne_top d)
  exact this

theorem nvNoiseLaw_nvGood (d : ℕ) : nvNoiseLaw d (nvGood d) = 1 := by
  have h := nv_ae_mem_nvGood d
  rw [ae_iff] at h
  have h0 : nvNoiseLaw d (nvGood d)ᶜ = 0 := h
  exact (prob_compl_eq_zero_iff (measurableSet_nvGood d)).1 h0

end

end SuperdiffusionCLT.Assumptions.ShellLaw.Model
