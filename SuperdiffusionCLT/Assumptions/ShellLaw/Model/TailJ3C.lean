/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.ShellDilationB
public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.GaussianSeriesF

/-!
# The seed shell law

`nv_j3_seedShellLaw d ε` is the law of the skew field whose entries `(i, j)`, `i < j`, are independent
copies of the scalar seed field of scale `ε`:
the image of the product of the scalar seed laws under `assembleSkew`.
Equivalently it is the image of the product of the noise laws under `nv_j3_seedShellMap ε`.

## Main results

* `nv_j3_seedShellLaw`, `nv_j3_seedShellLaw_toMeasure`
* `nv_j3_seedShellMap`, `measurable_nv_j3_seedShellMap`
* `nv_j3_seedShellLaw_eq_map`
-/

@[expose] public section

namespace SuperdiffusionCLT.Assumptions.ShellLaw.Model

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions

noncomputable section

variable {d : ℕ}

/-- The seed shell law: independent scalar seed fields in the entries `i < j`. -/
def nv_j3_seedShellLaw (d : ℕ) (ε : ℝ) : ProbabilityMeasure (ShellField d) :=
  ⟨(Measure.pi fun _ : SkewIdx d ↦ nv_seedLaw d ε).map assembleSkew,
    (Measure.isProbabilityMeasure_map_iff measurable_assembleSkew.aemeasurable).2 inferInstance⟩

theorem nv_j3_seedShellLaw_toMeasure (d : ℕ) (ε : ℝ) :
    (nv_j3_seedShellLaw d ε).toMeasure
      = (Measure.pi fun _ : SkewIdx d ↦ nv_seedLaw d ε).map assembleSkew := rfl

theorem nv_j3_measurable_seedFamily (ε : ℝ) :
    Measurable fun (ξ : SkewIdx d → NvNoise d) (p : SkewIdx d) ↦ nv_seedMap ε (ξ p) :=
  Measurable.of_eval fun p ↦ (nv_measurable_seedMap ε).comp (measurable_pi_apply p)

/-- The skew field assembled from the seed fields of a family of independent noises. -/
def nv_j3_seedShellMap (ε : ℝ) (ξ : SkewIdx d → NvNoise d) : ShellField d :=
  assembleSkew fun p ↦ nv_seedMap ε (ξ p)

theorem measurable_nv_j3_seedShellMap (ε : ℝ) : Measurable (nv_j3_seedShellMap (d := d) ε) :=
  measurable_assembleSkew.comp (nv_j3_measurable_seedFamily ε)

/-- The seed shell law as the image of the product of the noise laws. -/
theorem nv_j3_seedShellLaw_eq_map (d : ℕ) (ε : ℝ) :
    (nv_j3_seedShellLaw d ε).toMeasure
      = (Measure.pi fun _ : SkewIdx d ↦ nvNoiseLaw d).map (nv_j3_seedShellMap ε) := by
  rw [nv_j3_seedShellLaw_toMeasure]
  have h := Measure.pi_map_pi (μ := fun _ : SkewIdx d ↦ nvNoiseLaw d)
    (f := fun _ : SkewIdx d ↦ nv_seedMap (d := d) ε)
    (fun _ ↦ (nv_measurable_seedMap ε).aemeasurable)
  have e : (fun _ : SkewIdx d ↦ (nvNoiseLaw d).map (nv_seedMap (d := d) ε))
      = fun _ : SkewIdx d ↦ nv_seedLaw d ε := rfl
  rw [e] at h
  rw [← h, Measure.map_map measurable_assembleSkew (nv_j3_measurable_seedFamily ε)]
  rfl

end

end SuperdiffusionCLT.Assumptions.ShellLaw.Model
