/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Brownian.HeatCore
public import SuperdiffusionCLT.Section8.Convergence.InvariancePrinciple

/-!
# The heat resolvent as an average over the Gaussian shift

For a `C₀` function `g` and the positive shift `mu`, the resolvent `R_mu g` of the heat
semigroup is the average of `g` over the product measure on `(0, ∞) × ℝ^d` of Lebesgue measure
and the standard Gaussian, with weight `exp (-mu t)` and shift `sqrt t • z`
(`heatCore_resolvent_apply`).  Together with the differentiation lemmas of
`SuperdiffusionCLT.Section8.Brownian.HeatCore` this makes the resolvent of a smooth
compactly supported function a `C²` function whose second derivative vanishes at infinity
(`heatCore_resolvent_mem`).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.Brownian

open Filter Homogenization MeasureTheory Topology
open MarkovProcess.Semigroup
open scoped ContDiff NNReal ZeroAtInfty

noncomputable section

section Resolvent

variable {d : ℕ}

/-- The parameter measure: Lebesgue measure on `(0, ∞)` times the standard Gaussian. -/
def heatCore_measure (d : ℕ) : Measure (ℝ × Vec d) :=
  (volume.restrict (Set.Ioi (0 : ℝ))).prod (stdGaussian d)

instance heatCore_sigmaFinite (d : ℕ) : SigmaFinite (heatCore_measure d) := by
  unfold heatCore_measure
  infer_instance

/-- The weight `exp (-mu t)`. -/
def heatCore_weight (mu : ℝ) (p : ℝ × Vec d) : ℝ := Real.exp (-mu * p.1)

/-- The Gaussian shift `sqrt t • z`. -/
def heatCore_shift (p : ℝ × Vec d) : Vec d := Real.sqrt p.1 • p.2

theorem heatCore_measurable_shift : Measurable (heatCore_shift (d := d)) := by
  unfold heatCore_shift
  fun_prop

theorem heatCore_integrable_weight {mu : ℝ} (hmu : 0 < mu) :
    Integrable (heatCore_weight (d := d) mu) (heatCore_measure d) := by
  have h := (exp_neg_integrableOn_Ioi 0 hmu).comp_fst (stdGaussian d)
  exact h

/-- Evaluation at a point, as a bounded linear functional on `C₀`. -/
def heatCore_eval (x : Vec d) : C₀(Vec d, ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ f x
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
    1 (fun f ↦ by simpa using norm_apply_le_norm_c0 f x)

theorem heatCore_integrable_integrand {mu : ℝ} (hmu : 0 < mu) (g : C₀(Vec d, ℝ)) (x : Vec d) :
    Integrable (fun p : ℝ × Vec d ↦ heatCore_weight mu p • g (x + heatCore_shift p))
      (heatCore_measure d) :=
  heatCore_integrable (heatCore_integrable_weight hmu) heatCore_measurable_shift g.continuous
    (fun y ↦ by simpa using norm_apply_le_norm_c0 g y) x

/-- **The heat resolvent is the average over the Gaussian shift.** -/
theorem heatCore_resolvent_apply (mu : PositiveShift) (g : C₀(Vec d, ℝ)) (x : Vec d) :
    (Convergence.heatC0Semigroup d).resolvent mu g x
      = heatCore_avg (heatCore_measure d) (heatCore_weight (mu : ℝ)) heatCore_shift
          (g : Vec d → ℝ) x := by
  have hmu : 0 < (mu : ℝ) := mu.2
  have h1 : (Convergence.heatC0Semigroup d).resolvent mu g x
      = ∫ t in Set.Ioi (0 : ℝ), heatCore_eval x
          ((Convergence.heatC0Semigroup d).laplaceIntegrand mu g t) := by
    rw [StronglyContinuousContractionSemigroup.resolvent_apply]
    exact (ContinuousLinearMap.integral_comp_comm (heatCore_eval x)
      ((Convergence.heatC0Semigroup d).integrableOn_laplaceIntegrand hmu g)).symm
  rw [h1, heatCore_avg, heatCore_measure, integral_prod _ (heatCore_integrable_integrand hmu g x)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
  have ht' : (Real.toNNReal t : ℝ) = t := Real.coe_toNNReal t (le_of_lt ht)
  simp only [StronglyContinuousContractionSemigroup.laplaceIntegrand_apply, heatCore_eval,
    LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk, ZeroAtInftyContinuousMap.smul_apply]
  have e : ∫ y, g y ∂(heatKernel d t.toNNReal x)
      = ∫ z, g (x + Real.sqrt (t.toNNReal : ℝ) • z) ∂(stdGaussian d) :=
    integral_heatKernel_eq g.continuous _ _
  rw [Convergence.heatC0Semigroup, c0Semigroup_heatSemigroup_apply, gaussianAverage_apply, e,
    ht']
  simp only [heatCore_weight, heatCore_shift]
  rw [integral_smul]

/-- **The heat resolvent of a smooth compactly supported function lies in the differentiable
class of the heat generator**: it is `C²` and its second derivative vanishes at infinity. -/
theorem heatCore_resolvent_mem (mu : PositiveShift) (g : C₀(Vec d, ℝ))
    (hg : ContDiff ℝ ∞ (g : Vec d → ℝ)) (hc : HasCompactSupport (g : Vec d → ℝ)) :
    (Convergence.heatC0Semigroup d).resolvent mu g ∈ Convergence.heatCore d := by
  have hmu : 0 < (mu : ℝ) := mu.2
  have hfun : ⇑((Convergence.heatC0Semigroup d).resolvent mu g)
      = heatCore_avg (heatCore_measure d) (heatCore_weight (mu : ℝ)) heatCore_shift
          (g : Vec d → ℝ) :=
    funext fun x ↦ heatCore_resolvent_apply mu g x
  rw [Convergence.heatCore, Set.mem_ofPred_eq, hfun]
  exact heatCore_avg_regular (heatCore_integrable_weight hmu) heatCore_measurable_shift hg hc
    (fun y ↦ by simpa using norm_apply_le_norm_c0 g y)

end Resolvent

end

end SuperdiffusionCLT.Section8.Brownian
