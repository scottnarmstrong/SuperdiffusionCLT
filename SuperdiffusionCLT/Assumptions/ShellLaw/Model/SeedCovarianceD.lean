/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.SeedCovarianceC
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence

/-!
# The seed field is a Gaussian process with covariance `nvCov`

The evaluation vector `nv_vec c x` of the seed field at finitely many points has a law that
depends only on the matrix `c j * c l * nvCov (x j) (x l)`: it is the centred multivariate Gaussian
with this covariance. Consequently the seed field is a Gaussian process in the sense of Mathlib
and its finite-dimensional marginals on the scalar carrier are determined by `nvCov`.

## Main results

* `nv_vec`, `nv_charFunDual_vec`: characteristic function of the evaluation vector
* `nv_map_vec_eq`: equal covariance matrices give equal laws of evaluation vectors
* `nv_isGaussianProcess_seed`: `IsGaussianProcess (fun x ξ ↦ nv_seed ξ x) (nvNoiseLaw d)`
* `nv_seedLaw_marginal_eq`: the marginals of `nv_seedLaw d ε` on `Finset (Vec d)`
-/

@[expose] public section

namespace SuperdiffusionCLT.Assumptions.ShellLaw.Model

open Homogenization MeasureTheory ProbabilityTheory

noncomputable section

variable {d : ℕ} {ι : Type*}

/-- The scaled evaluation vector `(c j * seed ξ (x j))_j`. -/
def nv_vec (c : ι → ℝ) (x : ι → Vec d) (ξ : NvNoise d) : ι → ℝ := fun j ↦ c j * nv_seed ξ (x j)

theorem nv_measurable_vec (c : ι → ℝ) (x : ι → Vec d) : Measurable (nv_vec c x) :=
  measurable_pi_iff.2 fun j ↦ (nv_measurable_seed (x j)).const_mul (c j)

theorem nv_dual_apply [Fintype ι] [DecidableEq ι] (L : StrongDual ℝ (ι → ℝ)) (v : ι → ℝ) :
    L v = ∑ j, L (Pi.single j 1) * v j := by
  have hv : v = ∑ j, v j • (Pi.single j (1 : ℝ) : ι → ℝ) := by
    ext i; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  simp [map_sum, mul_comm]

/-- A continuous linear functional of the evaluation vector is a combination of seed values. -/
theorem nv_dual_vec [Fintype ι] [DecidableEq ι] (L : StrongDual ℝ (ι → ℝ)) (c : ι → ℝ) (x : ι → Vec d) (ξ : NvNoise d) :
    L (nv_vec c x ξ) = ∑ j, (L (Pi.single j 1) * c j) * nv_seed ξ (x j) := by
  rw [nv_dual_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [nv_vec]
  ring

/-- Under the noise law, every continuous linear functional of the evaluation vector is a centred
real Gaussian. -/
theorem nv_map_dual_vec [Fintype ι] [DecidableEq ι] (L : StrongDual ℝ (ι → ℝ)) (c : ι → ℝ) (x : ι → Vec d) :
    ((nvNoiseLaw d).map (nv_vec c x)).map L
      = gaussianReal 0 (nvVar (fun j ↦ L (Pi.single j 1) * c j) x).toNNReal := by
  rw [Measure.map_map L.continuous.measurable (nv_measurable_vec c x)]
  have : (⇑L ∘ nv_vec c x) = fun ξ ↦ ∑ j, (L (Pi.single j 1) * c j) * nv_seed ξ (x j) := by
    funext ξ; exact nv_dual_vec L c x ξ
  rw [this]
  exact nv_map_comb_eq_gaussianReal _ x

/-- **The characteristic function of the evaluation vector.** -/
theorem nv_charFunDual_vec [Fintype ι] [DecidableEq ι] (L : StrongDual ℝ (ι → ℝ)) (c : ι → ℝ) (x : ι → Vec d) :
    charFunDual ((nvNoiseLaw d).map (nv_vec c x)) L
      = Complex.exp (-(nvVar (fun j ↦ L (Pi.single j 1) * c j) x : ℂ) / 2) := by
  rw [charFunDual_eq_charFun_map_one, nv_map_dual_vec, charFun_gaussianReal,
    Real.coe_toNNReal _ (nvVar_nonneg _ _)]
  congr 1
  push_cast
  ring

theorem nvVar_eq_sum [Fintype ι] (L : ι → ℝ) (c : ι → ℝ) (x : ι → Vec d) :
    nvVar (fun j ↦ L j * c j) x = ∑ j, ∑ l, L j * L l * (c j * c l * nvCov (x j) (x l)) := by
  unfold nvVar
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
  ring

/-- **Equal covariance matrices give equal laws.** The law of the evaluation vector
`(c j * seed (x j))_j` depends only on the matrix `c j * c l * nvCov (x j) (x l)`. -/
theorem nv_map_vec_eq [Fintype ι] [DecidableEq ι] (c c' : ι → ℝ) (x x' : ι → Vec d)
    (h : ∀ j l, c j * c l * nvCov (x j) (x l) = c' j * c' l * nvCov (x' j) (x' l)) :
    (nvNoiseLaw d).map (nv_vec c x) = (nvNoiseLaw d).map (nv_vec c' x') := by
  refine Measure.ext_of_charFunDual (funext fun L ↦ ?_)
  rw [nv_charFunDual_vec, nv_charFunDual_vec, nvVar_eq_sum, nvVar_eq_sum]
  simp_rw [h]

/-- The seed field is a Gaussian process under the noise law. -/
theorem nv_isGaussianProcess_seed :
    IsGaussianProcess (fun (x : Vec d) (ξ : NvNoise d) ↦ nv_seed ξ x) (nvNoiseLaw d) := by
  classical
  refine ⟨fun I ↦ ?_⟩
  have hm : Measurable fun ξ : NvNoise d ↦ I.restrict (fun x ↦ nv_seed ξ x) :=
    measurable_pi_iff.2 fun x ↦ nv_measurable_seed (x : Vec d)
  refine ⟨hm.aemeasurable, ?_⟩
  refine isGaussian_of_map_eq_gaussianReal fun L ↦ ?_
  have e : (fun ξ : NvNoise d ↦ I.restrict (fun x ↦ nv_seed ξ x))
      = nv_vec (fun _ : I ↦ (1 : ℝ)) (fun x : I ↦ (x : Vec d)) := by
    funext ξ x; simp [nv_vec]
  rw [e]
  exact ⟨0, _, nv_map_dual_vec L _ _⟩

/-! ## Marginals of the scalar seed law -/

theorem nv_seedLaw_marginal_eq (ε : ℝ) (s : Finset (Vec d)) :
    (nv_seedLaw d ε).map (fun (f : ScalarC2Field d) (x : s) ↦ f (x : Vec d))
      = (nvNoiseLaw d).map (nv_vec (fun _ : s ↦ ε) (fun x : s ↦ (x : Vec d))) := by
  unfold nv_seedLaw
  have hg : Measurable fun (f : ScalarC2Field d) (x : s) ↦ f (x : Vec d) :=
    measurable_pi_iff.2 fun x ↦ ScalarC2Field.measurable_eval (x : Vec d)
  rw [Measure.map_map hg (nv_measurable_seedMap ε)]
  rfl

end

end SuperdiffusionCLT.Assumptions.ShellLaw.Model
