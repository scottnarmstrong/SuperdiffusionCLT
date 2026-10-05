/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.ShellDilation
public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.ShellAssemblyB
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Shell laws as dilations of a seed law

For a probability measure `ν₀` on shell fields the shell laws are
`ν_n = (D_{3^n})_* ν₀`. This file records that each `ν_n` is a probability measure,
the evaluation marginals, the transfer of translation, negation and signed-permutation
invariance from `ν₀` to every `ν_n`, and the commutation of dilation with the assembly of
a skew field from scalar fields.
-/

@[expose] public section

namespace SuperdiffusionCLT.Assumptions.ShellLaw.Model

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-- The shell law `ν_n = (D_{3^n})_* ν₀` of the seed law `ν₀`. -/
def scaledShellLaw (ν : ProbabilityMeasure (ShellField d)) (n : ℕ) :
    ProbabilityMeasure (ShellField d) :=
  ν.map (dilate (nv_scaleUnit n))

theorem scaledShellLaw_toMeasure (ν : ProbabilityMeasure (ShellField d)) (n : ℕ) :
    (scaledShellLaw ν n).toMeasure = Measure.map (dilate (nv_scaleUnit n)) ν.toMeasure :=
  ProbabilityMeasure.toMeasure_map _

theorem scaledShellLaw_zero (ν : ProbabilityMeasure (ShellField d)) :
    scaledShellLaw ν 0 = ν := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [scaledShellLaw_toMeasure, nv_scaleUnit_zero]
  have : dilate (1 : ℝˣ) = (id : ShellField d → ShellField d) := funext dilate_one
  rw [this, Measure.map_id]

theorem measurable_eval_deriv_entry (x v : Vec d) (i k : Fin d) :
    Measurable (fun F : ShellField d ↦ ShellField.deriv F x v i k) :=
  ((continuous_apply k).comp ((continuous_apply i).comp
    ((ContinuousLinearMap.apply ℝ (Mat d) v).continuous.comp
      (ShellField.continuous_eval_deriv x)))).measurable

/-! ## Transfer of invariances from the seed law -/

theorem rotate_dilate (R : Mat d) (hR : IsSignedPermutationMatrix R) (c : ℝˣ)
    (j : ShellField d) :
    ShellField.rotate R hR (dilate c j) = dilate c (ShellField.rotate R hR j) := by
  ext x a b
  have hm : matVecMul R (((c⁻¹ : ℝˣ) : ℝ) • x) = ((c⁻¹ : ℝˣ) : ℝ) • matVecMul R x := by
    ext i
    simp [matVecMul, Finset.mul_sum, mul_left_comm]
  simp only [ShellField.rotate_apply, dilate_apply, hm]

/-- Translation invariance of the seed law passes to every `ν_n`. -/
theorem map_translate_scaledShellLaw (ν : ProbabilityMeasure (ShellField d))
    (hν : ∀ z : Vec d, Measure.map (ShellField.translate z) ν.toMeasure = ν.toMeasure)
    (n : ℕ) (z : Vec d) :
    Measure.map (ShellField.translate z) (scaledShellLaw ν n).toMeasure =
      (scaledShellLaw ν n).toMeasure := by
  rw [scaledShellLaw_toMeasure, Measure.map_map (ShellField.measurable_translate z)
    (measurable_dilate _)]
  have h : (ShellField.translate z ∘ dilate (nv_scaleUnit n)) =
      dilate (nv_scaleUnit n) ∘
        ShellField.translate ((((nv_scaleUnit n)⁻¹ : ℝˣ) : ℝ) • z) :=
    funext fun j ↦ translate_dilate z _ j
  rw [h, ← Measure.map_map (measurable_dilate _) (ShellField.measurable_translate _),
    hν]

/-- Negation invariance of the seed law passes to every `ν_n`. -/
theorem map_negate_scaledShellLaw (ν : ProbabilityMeasure (ShellField d))
    (hν : Measure.map ShellField.negate ν.toMeasure = ν.toMeasure) (n : ℕ) :
    Measure.map ShellField.negate (scaledShellLaw ν n).toMeasure =
      (scaledShellLaw ν n).toMeasure := by
  rw [scaledShellLaw_toMeasure, Measure.map_map ShellField.measurable_negate
    (measurable_dilate _)]
  have h : (ShellField.negate ∘ dilate (nv_scaleUnit n)) =
      dilate (nv_scaleUnit n) ∘ (ShellField.negate : ShellField d → ShellField d) :=
    funext fun j ↦ negate_dilate _ j
  rw [h, ← Measure.map_map (measurable_dilate _) ShellField.measurable_negate, hν]

/-- Signed-permutation invariance of the seed law passes to every `ν_n`. -/
theorem map_rotate_scaledShellLaw (ν : ProbabilityMeasure (ShellField d))
    (R : Mat d) (hR : IsSignedPermutationMatrix R)
    (hν : Measure.map (ShellField.rotate R hR) ν.toMeasure = ν.toMeasure) (n : ℕ) :
    Measure.map (ShellField.rotate R hR) (scaledShellLaw ν n).toMeasure =
      (scaledShellLaw ν n).toMeasure := by
  rw [scaledShellLaw_toMeasure, Measure.map_map (ShellField.measurable_rotate R hR)
    (measurable_dilate _)]
  have h : (ShellField.rotate R hR ∘ dilate (nv_scaleUnit n)) =
      dilate (nv_scaleUnit n) ∘ ShellField.rotate R hR :=
    funext fun j ↦ rotate_dilate R hR _ j
  rw [h, ← Measure.map_map (measurable_dilate _) (ShellField.measurable_rotate R hR), hν]

/-! ## Dilation of an assembled field -/

/-! ## Satisfiability witnesses -/

end

end SuperdiffusionCLT.Assumptions.ShellLaw.Model
