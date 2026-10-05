/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.GaussianSeriesF

/-!
# Almost surely convergent series of independent standard Gaussians

If `ξ` is an iid family of standard Gaussians indexed by a countable type and `F` is a measurable
function equal almost surely to the (unconditionally convergent) series `∑ i, a i * ξ i`, with
`a` square summable, then `F` is a centred real Gaussian of variance `∑ i, a i ^ 2` (characteristic
function of the finite partial sums, then dominated convergence).

## Main results

* `nv_integral_exp_finset_sum`: the characteristic function of a finite partial sum
* `nv_map_eq_gaussianReal_of_hasSum`: the limit is the centred Gaussian of variance `∑' a i ^ 2`
-/

@[expose] public section

namespace SuperdiffusionCLT.Assumptions.ShellLaw.Model

open MeasureTheory ProbabilityTheory Filter Complex
open scoped Topology

noncomputable section

variable {ι : Type*}

/-- The characteristic function of a finite partial sum of an iid standard Gaussian family. -/
theorem nv_integral_exp_finset_sum (a : ι → ℝ) (s : Finset ι) (u : ℝ) :
    ∫ ξ, cexp (((u * ∑ i ∈ s, a i * ξ i : ℝ) : ℂ) * I)
        ∂(Measure.infinitePi fun _ : ι ↦ gaussianReal 0 1)
      = cexp (-((u ^ 2 * ∑ i ∈ s, a i ^ 2 : ℝ) : ℂ) / 2) := by
  classical
  have hf : ∀ y : s → ℝ, cexp (((u * ∑ i : s, a i * y i : ℝ) : ℂ) * I)
      = ∏ i : s, cexp (((u * a i * y i : ℝ) : ℂ) * I) := by
    intro y
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  have hmeas : AEStronglyMeasurable
      (fun y : s → ℝ ↦ cexp (((u * ∑ i : s, a i * y i : ℝ) : ℂ) * I))
      (Measure.pi fun i : s ↦ gaussianReal 0 1) := by
    refine Continuous.aestronglyMeasurable ?_
    fun_prop
  have h1 := integral_restrict_infinitePi (μ := fun _ : ι ↦ gaussianReal 0 1) (s := s)
    (f := fun y : s → ℝ ↦ cexp (((u * ∑ i : s, a i * y i : ℝ) : ℂ) * I)) hmeas
  have h2 : ∀ ξ : ι → ℝ, cexp (((u * ∑ i ∈ s, a i * ξ i : ℝ) : ℂ) * I)
      = cexp (((u * ∑ i : s, a i * s.restrict ξ i : ℝ) : ℂ) * I) := by
    intro ξ
    rw [← Finset.sum_coe_sort s]
    rfl
  simp_rw [h2]
  rw [h1]
  simp_rw [hf]
  rw [integral_fintype_prod_eq_prod (f := fun (i : s) (x : ℝ) ↦
    cexp (((u * a i * x : ℝ) : ℂ) * I))]
  have h3 : ∀ i : s, ∫ x, cexp (((u * a i * x : ℝ) : ℂ) * I) ∂(gaussianReal 0 1)
      = cexp (-((u ^ 2 * a i ^ 2 : ℝ) : ℂ) / 2) := by
    intro i
    have := charFun_gaussianReal (μ := 0) (v := 1) (u * a i)
    rw [charFun_apply_real] at this
    have e : ∀ x : ℝ, ((u * a i * x : ℝ) : ℂ) = ((u * a i : ℝ) : ℂ) * (x : ℂ) := by
      intro x; push_cast; ring
    simp_rw [e]
    rw [this]
    congr 1
    push_cast
    ring
  simp_rw [h3]
  rw [← Complex.exp_sum, ← Finset.sum_coe_sort s]
  congr 1
  push_cast
  rw [← Finset.sum_div, Finset.sum_neg_distrib, ← Finset.mul_sum]

/-- **A convergent Gaussian series is Gaussian.** -/
theorem nv_map_eq_gaussianReal_of_hasSum [Countable ι] (a : ι → ℝ)
    (ha : Summable fun i ↦ a i ^ 2) (F : (ι → ℝ) → ℝ) (hF : Measurable F)
    (hlim : ∀ᵐ ξ ∂(Measure.infinitePi fun _ : ι ↦ gaussianReal 0 1),
      HasSum (fun i ↦ a i * ξ i) (F ξ)) :
    (Measure.infinitePi fun _ : ι ↦ gaussianReal 0 1).map F
      = gaussianReal 0 (∑' i, a i ^ 2).toNNReal := by
  set P : Measure (ι → ℝ) := Measure.infinitePi fun _ : ι ↦ gaussianReal 0 1 with hP
  refine Measure.ext_of_charFun (funext fun u ↦ ?_)
  rw [charFun_apply_real, charFun_gaussianReal,
    integral_map hF.aemeasurable (Continuous.aestronglyMeasurable (by fun_prop))]
  have hmeasS : ∀ s : Finset ι, AEStronglyMeasurable
      (fun ξ : ι → ℝ ↦ cexp (((u * ∑ i ∈ s, a i * ξ i : ℝ) : ℂ) * I)) P := fun s ↦
    Continuous.aestronglyMeasurable (by fun_prop)
  have hT : Tendsto (fun s : Finset ι ↦ ∫ ξ, cexp (((u * ∑ i ∈ s, a i * ξ i : ℝ) : ℂ) * I) ∂P)
      atTop (𝓝 (∫ ξ, cexp (((u * F ξ : ℝ) : ℂ) * I) ∂P)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ ↦ (1 : ℝ))
      (Eventually.of_forall hmeasS) (Eventually.of_forall fun s ↦ ?_) (integrable_const _) ?_
    · refine Eventually.of_forall fun ξ ↦ ?_
      rw [Complex.norm_exp_ofReal_mul_I]
    · filter_upwards [hlim] with ξ hξ
      refine (Complex.continuous_exp.tendsto _).comp ?_
      refine (Continuous.tendsto (f := fun r : ℝ ↦ ((u * r : ℝ) : ℂ) * I) (by fun_prop) _).comp ?_
      exact hξ
  have hT2 : Tendsto (fun s : Finset ι ↦ ∫ ξ, cexp (((u * ∑ i ∈ s, a i * ξ i : ℝ) : ℂ) * I) ∂P)
      atTop (𝓝 (cexp (-((u ^ 2 * ∑' i, a i ^ 2 : ℝ) : ℂ) / 2))) := by
    simp_rw [hP, nv_integral_exp_finset_sum]
    refine (Complex.continuous_exp.tendsto _).comp ?_
    refine (Continuous.tendsto (f := fun r : ℝ ↦ -((u ^ 2 * r : ℝ) : ℂ) / 2) (by fun_prop) _).comp ?_
    exact ha.hasSum
  have := tendsto_nhds_unique hT hT2
  convert this using 1
  · congr 1
    funext ξ
    push_cast
    ring_nf
  · congr 1
    rw [Real.coe_toNNReal _ (tsum_nonneg fun i ↦ sq_nonneg (a i))]
    push_cast
    ring

end

end SuperdiffusionCLT.Assumptions.ShellLaw.Model
