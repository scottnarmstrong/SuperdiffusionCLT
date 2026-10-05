/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.GaussLaw

/-!
# The Gaussian shell law is not the Dirac law, and the combined statement

The value at the origin of an off-diagonal entry of the seed shell law is a centred Gaussian
of positive variance, hence not a point mass.  So `nv_gaussLaw d` differs from the Dirac law at
zero, and for `2 ≤ d` it satisfies the prefix, J1 version 2, J2, J3 and J4 simultaneously.

Certified: all shell-law conditions except J5, for a nonzero Gaussian law.  Not yet certified
here: J5.

## Main results

* `nv_gaussLaw_ne_dirac`
-/

@[expose] public section

namespace SuperdiffusionCLT.Assumptions.ShellLaw.Model

open Homogenization MeasureTheory ProbabilityTheory
open SuperdiffusionCLT.Frozen.Assumptions

noncomputable section

variable {d : ℕ}

/-- The origin value of a seed entry is a Gaussian of variance `ε² · nvCov 0 0`. -/
theorem nv_seedLaw_eval_zero (ε : ℝ) :
    (nv_seedLaw d ε).map (fun f : ScalarC2Field d ↦ f 0) =
      gaussianReal 0 (nvVar (fun _ : Unit ↦ ε) (fun _ : Unit ↦ (0 : Vec d))).toNNReal := by
  rw [← nv_map_comb_eq_gaussianReal, nv_seedLaw,
    Measure.map_map (ScalarC2Field.measurable_eval 0) (nv_measurable_seedMap ε)]
  congr 1
  funext ξ
  simp [nv_seedMap_apply]

theorem nv_nvVar_unit (ε : ℝ) :
    nvVar (fun _ : Unit ↦ ε) (fun _ : Unit ↦ (0 : Vec d)) = ε ^ 2 * nvCov (0 : Vec d) 0 := by
  simp [nvVar, sq]

theorem nv_gaussLaw_ne_dirac (hd : 2 ≤ d) : nv_gaussLaw d ≠ diracZeroLaw d := by
  intro h
  set ε := nv_epsJ3 d
  have hε : 0 < ε := nv_epsJ3_pos (by omega)
  have h0 : (⟨0, by omega⟩ : Fin d) < ⟨1, by omega⟩ := by simp
  have hmarg : nv_seedShellLaw d ε = ShellField.shellMarginalLaw (diracZeroLaw d) 0 := by
    rw [← h]
    have := nv_shellMarginalLaw_productLaw (nv_seedShellLaw d ε) 0
    rw [scaledShellLaw_zero] at this
    exact this.symm
  have hmeas : Measurable (fun F : ShellField d ↦ F 0 ⟨0, by omega⟩ ⟨1, by omega⟩) :=
    ShellField.measurable_eval_entry 0 _ _
  have h1 : (nv_seedShellLaw d ε).toMeasure.map
      (fun F : ShellField d ↦ F 0 ⟨0, by omega⟩ ⟨1, by omega⟩) =
      gaussianReal 0 (ε ^ 2 * nvCov (0 : Vec d) 0).toNNReal := by
    rw [nv_seedShellLaw_map_eq d ε _ hmeas, ← nv_nvVar_unit, ← nv_seedLaw_eval_zero]
    have : (fun φ : SkewIdx d → ScalarC2Field d ↦
        assembleSkew φ 0 ⟨0, by omega⟩ ⟨1, by omega⟩) = fun φ ↦ φ ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), h0⟩ 0 := by
      funext φ
      exact assembleSkew_apply_lt φ 0 h0
    rw [this]
    unfold nv_seedProduct
    have hm : Measurable (fun f : ScalarC2Field d ↦ f 0) := ScalarC2Field.measurable_eval 0
    have hc : (fun φ : SkewIdx d → ScalarC2Field d ↦ φ ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), h0⟩ 0) =
        (fun f : ScalarC2Field d ↦ f 0) ∘
          (fun φ : SkewIdx d → ScalarC2Field d ↦ φ ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), h0⟩) := rfl
    have key := (measurePreserving_eval (fun _ : SkewIdx d ↦ nv_seedLaw d ε)
      (⟨(⟨0, by omega⟩, ⟨1, by omega⟩), h0⟩ : SkewIdx d)).map_eq
    rw [hc, ← Measure.map_map hm (measurable_pi_apply (⟨(⟨0, by omega⟩, ⟨1, by omega⟩), h0⟩ : SkewIdx d)), key]
  have h2 : (nv_seedShellLaw d ε).toMeasure.map
      (fun F : ShellField d ↦ F 0 ⟨0, by omega⟩ ⟨1, by omega⟩) = Measure.dirac 0 := by
    rw [hmarg, shellMarginalLaw_diracZeroLaw, Measure.map_dirac' hmeas]
    simp [ShellField.zero]
  have hv : (ε ^ 2 * nvCov (0 : Vec d) 0).toNNReal ≠ 0 := by
    have := nvCov_self_pos (0 : Vec d)
    have : 0 < ε ^ 2 * nvCov (0 : Vec d) 0 := by positivity
    simpa using this
  have hac := gaussianReal_absolutelyContinuous 0 hv
  rw [h1] at h2
  have := hac (show (volume : Measure ℝ) {0} = 0 by simp)
  rw [h2] at this
  simp at this

end

end SuperdiffusionCLT.Assumptions.ShellLaw.Model
