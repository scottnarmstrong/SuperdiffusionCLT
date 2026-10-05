/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellField.Actions
public import SuperdiffusionCLT.Assumptions.ShellField.LIHLocalSigma
public import Homogenization.CoarseGraining.Definitions
public import Homogenization.Geometry.CubeMetric
public import Homogenization.Geometry.Translation
public import Homogenization.Probability.RegCoeffField.Differentiation

/-!
# Spatial averages of marginal shell fields

This file defines the spatial average of one shell over a translated triadic
cube. The internal definition uses the CoarseGraining library's half-open cubes, while the
comparison theorem identifies it with the paper's normalized integral over the open
translated cube.

The average is also proved measurable from the local integral sigma-field of
its exact read region. This is a deterministic carrier API: it assumes no shell
law, independence, stationarity, or concentration estimate.

## Main definitions

* `translatedShellCubeAverage`: average of `j (x + y)` over a triadic cube.
* `shellSpatialAverage`: the preceding average over the centered cube at an
  integer scale.

## Main results

* `translatedShellCubeAverage_eq_volumeAverageMat_translateSet_openCubeSet`:
  equality with the manuscript's open translated-cube average.
* `measurable_translatedShellCubeAverage_lihLocalSigma`: locality of the
  average in the exact translated read region.
* `translatedShellCubeAverage_negate`: compatibility with shell negation.
-/

@[expose] public section

namespace SuperdiffusionCLT.Frozen.Assumptions.ShellField

open Homogenization MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The matrix average of a shell over a translated triadic cube, written on
the untranslated internal cube as `j (x + y)`. -/
noncomputable def translatedShellCubeAverage
    (y : Vec d) (Q : TriadicCube d) (j : ShellField d) : Mat d :=
  cubeAverageMat Q (fun x ↦ j (x + y))

/-- The spatial average of a shell over the centered cube of scale `3 ^ h`,
translated by `y`. -/
noncomputable def shellSpatialAverage
    (h : ℤ) (y : Vec d) (j : ShellField d) : Mat d :=
  translatedShellCubeAverage y (originCube d h) j

/-- The internal half-open cube average is the CoarseGraining carrier average over its
exact translated read region. -/
theorem translatedShellCubeAverage_eq_avgMat_translateSet_cubeSet
    (y : Vec d) (Q : TriadicCube d) (j : ShellField d) :
    translatedShellCubeAverage y Q j =
      avgMat (translateSet y (cubeSet Q)) (forgetShell j) := by
  ext i k
  calc
    translatedShellCubeAverage y Q j i k =
        (cubeVolume Q)⁻¹ *
          ∫ x in cubeSet Q, j (x + y) i k ∂volume := rfl
    _ = (volume (translateSet y (cubeSet Q))).toReal⁻¹ *
          ∫ x in translateSet y (cubeSet Q), j x i k ∂volume := by
      rw [volume_translateSet_eq, volume_cubeSet_toReal,
        ← setIntegral_comp_addRight_translateSet y (cubeSet Q)
          (fun x ↦ j x i k)]
    _ = avgMat (translateSet y (cubeSet Q)) (forgetShell j) i k := by
      rw [avgMat, smul_eq_mul]
      rfl

/-- The translated half-open cube average equals the manuscript's normalized
average over the corresponding open translated cube. -/
theorem translatedShellCubeAverage_eq_volumeAverageMat_translateSet_openCubeSet
    (y : Vec d) (Q : TriadicCube d) (j : ShellField d) :
    translatedShellCubeAverage y Q j =
      volumeAverageMat (translateSet y (openCubeSet Q)) j := by
  ext i k
  calc
    translatedShellCubeAverage y Q j i k =
        (cubeVolume Q)⁻¹ *
          ∫ x in cubeSet Q, j (x + y) i k ∂volume := rfl
    _ = (cubeVolume Q)⁻¹ *
          ∫ x in openCubeSet Q, j (x + y) i k ∂volume := by
      rw [setIntegral_cubeSet_eq_setIntegral_openCubeSet]
    _ = (volume (translateSet y (openCubeSet Q))).toReal⁻¹ *
          ∫ x in translateSet y (openCubeSet Q), j x i k ∂volume := by
      rw [volume_translateSet_eq, volume_openCubeSet_toReal,
        ← setIntegral_comp_addRight_translateSet y (openCubeSet Q)
          (fun x ↦ j x i k)]
    _ = volumeAverageMat (translateSet y (openCubeSet Q)) j i k := by
      rfl

/-- The centered-scale specialization of the open translated-cube identity. -/
theorem shellSpatialAverage_eq_volumeAverageMat_translateSet_openCubeSet
    (h : ℤ) (y : Vec d) (j : ShellField d) :
    shellSpatialAverage h y j =
      volumeAverageMat
        (translateSet y (openCubeSet (originCube d h))) j := by
  exact
    translatedShellCubeAverage_eq_volumeAverageMat_translateSet_openCubeSet
      y (originCube d h) j

private theorem measurableSet_translateSet_cubeSet
    (y : Vec d) (Q : TriadicCube d) :
    MeasurableSet (translateSet y (cubeSet Q)) := by
  rw [← preimage_subRight_eq_translateSet]
  exact (continuous_id.sub continuous_const).measurable (measurableSet_cubeSet Q)

private theorem translateSet_cubeSet_subset_closedBall
    (y : Vec d) (Q : TriadicCube d) :
    translateSet y (cubeSet Q) ⊆
      Metric.closedBall (cubeCenter Q + y) (cubeRadius Q) := by
  rintro _ ⟨x, hx, rfl⟩
  simpa only [Metric.mem_closedBall, dist_add_right] using
    (cubeSet_subset_closedBall Q hx)

private theorem isProbeR_indicator_translateSet_cubeSet
    (y : Vec d) (Q : TriadicCube d) :
    IsProbeR
      (Set.indicator (translateSet y (cubeSet Q))
        (fun _ : Vec d ↦ (1 : ℝ))) := by
  let B : Set (Vec d) := translateSet y (cubeSet Q)
  have hBmeas : MeasurableSet B := measurableSet_translateSet_cubeSet y Q
  refine ⟨measurable_const.indicator hBmeas, ⟨1, fun x ↦ ?_⟩, ?_⟩
  · change |Set.indicator B (fun _ : Vec d ↦ (1 : ℝ)) x| ≤ 1
    by_cases hx : x ∈ B
    · simp only [Set.indicator_of_mem hx, abs_one, le_refl]
    · simp only [Set.indicator_of_notMem hx, abs_zero, zero_le_one]
  · have hsub : closure
        (Function.support (Set.indicator B (fun _ : Vec d ↦ (1 : ℝ)))) ⊆
        Metric.closedBall (cubeCenter Q + y) (cubeRadius Q) :=
      closure_minimal
        ((support_indicator_one_subset B).trans
          (translateSet_cubeSet_subset_closedBall y Q))
        Metric.isClosed_closedBall
    exact IsCompact.of_isClosed_subset
      (isCompact_closedBall _ _) isClosed_closure hsub

/-- The translated cube average is measurable from the local integral
sigma-field of the exact translated half-open cube that it reads. -/
theorem measurable_translatedShellCubeAverage_lihLocalSigma
    (y : Vec d) (Q : TriadicCube d) :
    @Measurable (ShellField d) (Mat d)
      (lihLocalSigma (translateSet y (cubeSet Q))) inferInstance
      (translatedShellCubeAverage y Q) := by
  let B : Set (Vec d) := translateSet y (cubeSet Q)
  refine @measurable_matrix_of_entries d (ShellField d)
    (lihLocalSigma B) (translatedShellCubeAverage y Q) ?_
  intro i k
  have hBmeas : MeasurableSet B := measurableSet_translateSet_cubeSet y Q
  have hprobe : IsProbeR
      (Set.indicator B (fun _ : Vec d ↦ (1 : ℝ))) :=
    isProbeR_indicator_translateSet_cubeSet y Q
  have hentry : @Measurable (ShellField d) ℝ (lihLocalSigma B) (borel ℝ)
      (fun j ↦ entryTestR i k
        (Set.indicator B (fun _ : Vec d ↦ (1 : ℝ)))
        (forgetShell j)) :=
    measurable_entryTestR_forgetShell_lihLocalSigma B i k hprobe
      (support_indicator_one_subset B)
  have heq : (fun j : ShellField d ↦ translatedShellCubeAverage y Q j i k) =
      fun j : ShellField d ↦ (volume B).toReal⁻¹ •
        entryTestR i k (Set.indicator B (fun _ : Vec d ↦ (1 : ℝ)))
          (forgetShell j) := by
    funext j
    rw [translatedShellCubeAverage_eq_avgMat_translateSet_cubeSet,
      avgMat_entry_eq_smul_entryTestR i k B hBmeas]
  rw [heq]
  exact hentry.const_smul ((volume B).toReal⁻¹)

/-- The translated cube average is Borel measurable on the shell carrier. -/
theorem measurable_translatedShellCubeAverage
    (y : Vec d) (Q : TriadicCube d) :
    Measurable (translatedShellCubeAverage y Q) :=
  (measurable_translatedShellCubeAverage_lihLocalSigma y Q).mono
    (lihLocalSigma_le_borel (translateSet y (cubeSet Q))) le_rfl

/-- The centered-scale shell average is Borel measurable. -/
theorem measurable_shellSpatialAverage (h : ℤ) (y : Vec d) :
    Measurable (shellSpatialAverage h y) :=
  measurable_translatedShellCubeAverage y (originCube d h)

/-- Spatial averaging commutes with the shell negation action. -/
@[simp]
theorem translatedShellCubeAverage_negate
    (y : Vec d) (Q : TriadicCube d) (j : ShellField d) :
    translatedShellCubeAverage y Q (negate j) =
      -translatedShellCubeAverage y Q j := by
  ext i k
  change cubeAverage Q (fun x ↦ negate j (x + y) i k) =
    -cubeAverage Q (fun x ↦ j (x + y) i k)
  simp only [negate_apply, Matrix.neg_apply]
  rw [cubeAverage, cubeAverage, MeasureTheory.integral_neg, mul_neg]

/-- Centered-scale spatial averaging commutes with shell negation. -/
@[simp]
theorem shellSpatialAverage_negate
    (h : ℤ) (y : Vec d) (j : ShellField d) :
    shellSpatialAverage h y (negate j) = -shellSpatialAverage h y j :=
  translatedShellCubeAverage_negate y (originCube d h) j

end

end SuperdiffusionCLT.Frozen.Assumptions.ShellField
