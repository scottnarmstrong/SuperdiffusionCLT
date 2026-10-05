/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.ExcessiveCubeData
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.ExitMeanValueIdentificationWhole
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.PartResolventAlgebra

/-!
# The whole-space weak equation of the minimal resolvent

For a bounded measurable datum `g` and a positive shift `μ`, the analytic minimal resolvent
`u = R^A_μ g` of a whole-space coefficient field is an `H¹` function of every open subset `U` of
an exhaustion cube, with `|u| ≤ D / μ`, and it satisfies

  `∫_U (a ∇u) · ∇φ + μ ∫_U u φ = ∫_U g φ`

for every smooth compactly supported `φ` with `tsupport φ ⊆ U`.  The `H¹` structure and the weak
equation against `H¹₀` tests are the cube statements
(`exists_h1Function_analyticMinimalResolventReal`); the present file only specialises to smooth
tests and open subsets.
-/

@[expose] public section

open MeasureTheory Homogenization
open SuperdiffusionCLT.Section8.DivergenceForm
open MarkovProcess.Semigroup

namespace SuperdiffusionCLT.Section8

variable {d : ℕ}

/-- **The weak equation of the minimal resolvent on open subsets of an exhaustion cube.** -/
theorem resWeak_exists [NeZero d] (A : WholeSpaceAnalyticData d) (m : ℕ) (mu : PositiveShift)
    {g : Vec d → ℝ} (hgm : Measurable g) {D : ℝ} (hD : 0 ≤ D) (hgD : ∀ x, |g x| ≤ D)
    {U : Set (Vec d)} (hU : IsOpen U) (hUm : U ⊆ wholeSpaceCube d m) :
    ∃ u : H1Function U,
      u.toFun = A.analyticMinimalResolventReal mu g hgm hgD ∧
      (∀ x, |u.toFun x| ≤ D / (mu : ℝ)) ∧
      ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
        (∫ x in U, vecDot (matVecMul (A.a x) (u.grad x)) (fun i ↦ fderiv ℝ φ x (basisVec i))) +
          (mu : ℝ) * ∫ x in U, u.toFun x * φ x = ∫ x in U, g x * φ x := by
  obtain ⟨z, hzval, hzsol⟩ := A.exists_h1Function_analyticMinimalResolventReal m mu hgm hD hgD
  have hsol := hzsol.restrictSubset hU hUm
  refine ⟨z.restrict hU hUm, hzval, fun x ↦ ?_, fun φ hφ hc hs ↦ ?_⟩
  · rw [show (z.restrict hU hUm).toFun = z.toFun from rfl, hzval]
    exact A.abs_analyticMinimalResolventReal_le mu hgm hgD x
  · have h := hsol.2 (H10Function.ofContDiff hU hφ hc hs)
    have hg : (H10Function.ofContDiff hU hφ hc hs).toH1Function.grad =
        fun x i ↦ fderiv ℝ φ x (basisVec i) := rfl
    have hf : (H10Function.ofContDiff hU hφ hc hs).toH1Function.toFun = φ := rfl
    rw [hg, hf] at h
    have hφ2 : MemLp φ 2 (volume.restrict U) :=
      (hφ.continuous.memLp_of_hasCompactSupport hc).restrict U
    have i1 : Integrable (fun x ↦ A.wholeSpaceResidual mu hgm hgD x * φ x)
        (volume.restrict U) := hsol.1.integrable_mul hφ2
    have i2 : Integrable (fun x ↦ (z.restrict hU hUm).toFun x * φ x) (volume.restrict U) :=
      (z.restrict hU hUm).memL2.integrable_mul hφ2
    have e : ∫ x in U, g x * φ x =
        (∫ x in U, A.wholeSpaceResidual mu hgm hgD x * φ x) +
          (mu : ℝ) * ∫ x in U, (z.restrict hU hUm).toFun x * φ x := by
      rw [← integral_const_mul, ← integral_add i1 (i2.const_mul _)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
      simp only [WholeSpaceAnalyticData.wholeSpaceResidual]
      rw [show (z.restrict hU hUm).toFun x = A.analyticMinimalResolventReal mu g hgm hgD x from
        congrFun hzval x]
      ring
    rw [e, h]

end SuperdiffusionCLT.Section8

namespace SuperdiffusionCLT.Section8

/-- Witness: the heat field `a = I` (`nu = 1`) is whole-space analytic data in every dimension
`d ≥ 2`, and the theorem applies to it with the datum `g = 1`. -/
example : ∃ A : DivergenceForm.WholeSpaceAnalyticData 2, A.a = fun _ ↦ (1 : Mat 2) := by
  refine ⟨⟨fun _ ↦ 1, 1, one_pos, fun y ↦ ?_, ?_, le_refl _, measurable_const⟩, rfl⟩
  · funext i j
    simp only [symmPart, Matrix.one_apply, one_smul]
    by_cases h : i = j
    · subst h; norm_num
    · have h' : ¬ j = i := fun e ↦ h e.symm
      simp [h, h']
  · simp only [one_smul, sub_self]
    exact continuousOn_const

end SuperdiffusionCLT.Section8
