/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.SeedCovarianceE
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-!
# The covariance of the seed field in Mathlib's notation

The seed field `x ↦ nv_seed ξ x` is a centred Gaussian process under `nvNoiseLaw d` with
covariance `nvCov`. Here the bridge to Mathlib's `cov[·, ·; μ]` is proved, by polarisation of the
variance of `X_x + X_y`. Consequently the covariance vanishes at Euclidean distance at least one.

## Main results

* `nv_memLp_seed`: each `X_x` is in `L²`
* `nv_covariance_seed`: `cov[X_x, X_y; nvNoiseLaw d] = nvCov x y`
* `nv_covariance_seed_eq_zero_of_one_le_vecNorm`
-/

@[expose] public section

namespace SuperdiffusionCLT.Assumptions.ShellLaw.Model

open Homogenization MeasureTheory ProbabilityTheory

noncomputable section

variable {d : ℕ}

theorem nv_memLp_seed (x : Vec d) : MemLp (fun ξ : NvNoise d ↦ nv_seed ξ x) 2 (nvNoiseLaw d) :=
  (nv_isGaussianProcess_seed.hasGaussianLaw_eval x).memLp_two

/-- The variance of a finite combination is the covariance form, as a real number. -/
theorem nv_variance_comb {ι : Type*} [Fintype ι] (t : ι → ℝ) (x : ι → Vec d) :
    Var[fun ξ : NvNoise d ↦ ∑ j, t j * nv_seed ξ (x j); nvNoiseLaw d] = nvVar t x := by
  have hm := nv_map_comb_eq_gaussianReal t x
  have h1 : Var[id; (nvNoiseLaw d).map (fun ξ ↦ ∑ j, t j * nv_seed ξ (x j))] =
      Var[(id : ℝ → ℝ) ∘ fun ξ ↦ ∑ j, t j * nv_seed ξ (x j); nvNoiseLaw d] :=
    variance_map aemeasurable_id (nv_measurable_comb t x).aemeasurable
  rw [hm, variance_id_gaussianReal] at h1
  rw [Real.coe_toNNReal _ (nvVar_nonneg t x)] at h1
  exact h1.symm

theorem nv_variance_seed (x : Vec d) :
    Var[fun ξ : NvNoise d ↦ nv_seed ξ x; nvNoiseLaw d] = nvCov x x := by
  have h := nv_variance_comb (ι := Fin 1) (fun _ ↦ 1) (fun _ ↦ x)
  simpa [nvVar] using h

theorem nv_variance_seed_add (x y : Vec d) :
    Var[fun ξ : NvNoise d ↦ nv_seed ξ x + nv_seed ξ y; nvNoiseLaw d] =
      nvCov x x + 2 * nvCov x y + nvCov y y := by
  have h := nv_variance_comb (ι := Fin 2) (fun _ ↦ 1) ![x, y]
  simp only [Fin.sum_univ_two, nvVar, one_mul, mul_one, Matrix.cons_val_zero,
    Matrix.cons_val_one] at h
  rw [h, nvCov_comm y x]
  ring

/-- **The covariance bridge.** -/
theorem nv_covariance_seed (x y : Vec d) :
    cov[fun ξ : NvNoise d ↦ nv_seed ξ x, fun ξ : NvNoise d ↦ nv_seed ξ y; nvNoiseLaw d] =
      nvCov x y := by
  have h := variance_add (nv_memLp_seed x) (nv_memLp_seed y)
  have e : (fun ξ : NvNoise d ↦ nv_seed ξ x) + (fun ξ ↦ nv_seed ξ y) =
      fun ξ ↦ nv_seed ξ x + nv_seed ξ y := rfl
  rw [e, nv_variance_seed_add, nv_variance_seed, nv_variance_seed] at h
  linarith only [h]

theorem nv_covariance_seed_eq_zero_of_one_le_vecNorm {x y : Vec d}
    (h : 1 ≤ Book.Ch02.vecNorm (x - y)) :
    cov[fun ξ : NvNoise d ↦ nv_seed ξ x, fun ξ : NvNoise d ↦ nv_seed ξ y; nvNoiseLaw d] = 0 := by
  rw [nv_covariance_seed]
  exact nvCov_eq_zero_of_one_le_vecNorm h

end

end SuperdiffusionCLT.Assumptions.ShellLaw.Model
