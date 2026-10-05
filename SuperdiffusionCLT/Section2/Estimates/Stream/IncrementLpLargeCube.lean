/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.Average
public import SuperdiffusionCLT.Probability.VolumeAverageOrlicz
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementLinftyLargeCube

/-!
# Integrability of the finite-increment size on a large cube

This module collects the two analytic facts about the increment `k_m - k_n` that the `L^p`
clause of the paper's estimates (display `e.kmn.Lp`) needs on a large cube `cu_l`: the pointwise
size, the exact Euclidean matrix operator norm of the increment, is continuous in the spatial
variable (every shell of the carrier stores a continuous value map), and hence its `p`-th power
is integrable on the open realization `openCubeSet (originCube d l)` of the cube. In particular
the normalized average of the `p`-th power on the cube is finite, so the `L^p` carrier has no
junk values.

## Main results

* `continuous_matrixOperatorNorm_finiteShellIncrement`: continuity of the increment size.
* `integrableOn_matrixOperatorNorm_rpow_finiteShellIncrement`: the integrability
  of the `p`-th power on the cube.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Estimates.Stream

open Set
open MeasureTheory
open Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open scoped ENNReal

noncomputable section

variable {d : ℕ}
variable {P : ProbabilityMeasure (ShellSeq d)}

/-! ## Continuity of the increment size -/

/-- The pointwise size of the natural-shell increment is continuous in the
spatial variable: every shell of the carrier stores a continuous value map,
and the matrix operator norm is continuous. -/
theorem continuous_matrixOperatorNorm_finiteShellIncrement
    (omega : ShellSeq d) (n m : ℕ) :
    Continuous fun x : Vec d ↦
      matrixOperatorNorm (finiteShellIncrement omega n m x) := by
  have hsum : Continuous fun x : Vec d ↦ ∑ k ∈ Finset.Ioc n m, (omega k) x :=
    continuous_finsetSum _ fun k _ ↦ (omega k).1.1.continuous
  refine ShellField.continuous_matrixOperatorNorm.comp (hsum.congr ?_)
  intro x
  rw [finiteShellIncrement_apply]
  rfl

/-! ## The normalized `L^p` carrier on the large cube -/

/-- The `p`-th power of the pointwise increment size is integrable on the open
large cube: the size is continuous, hence measurable, and bounded there by the
finite `L∞` carrier. -/
theorem integrableOn_matrixOperatorNorm_rpow_finiteShellIncrement
    (omega : ShellSeq d) (n m l : ℕ) {p : ℝ} (hp : (0 : ℝ) ≤ p) :
    IntegrableOn
      (fun x : Vec d ↦
        matrixOperatorNorm (finiteShellIncrement omega n m x) ^ p)
      (openCubeSet (originCube d (l : ℤ))) volume := by
  set U : Set (Vec d) := openCubeSet (originCube d (l : ℤ)) with hU
  set S : ℝ := finiteShellIncrementLinftyNormLargeCube n m l omega with hS
  have hS0 : 0 ≤ S := finiteShellIncrementLinftyNormLargeCube_nonneg n m l omega
  have hpoint : ∀ x ∈ U,
      matrixOperatorNorm (finiteShellIncrement omega n m x) ≤ S :=
    fun x hx ↦
      matrixOperatorNorm_finiteShellIncrement_le_linftyNormLargeCube omega n m l hx
  have hbound : ∀ x ∈ U,
      matrixOperatorNorm (finiteShellIncrement omega n m x) ^ p ≤ S ^ p :=
    fun x hx ↦ Real.rpow_le_rpow (matrixOperatorNorm_nonneg _) (hpoint x hx) hp
  have hUopen : IsOpen U := by
    rw [hU, ← ball_cubeCenter_eq_openCubeSet]
    exact Metric.isOpen_ball
  have hcont : Continuous
      (fun x : Vec d ↦
        matrixOperatorNorm (finiteShellIncrement omega n m x) ^ p) :=
    (continuous_matrixOperatorNorm_finiteShellIncrement omega n m).rpow_const
      fun _ ↦ Or.inr hp
  show Integrable
    (fun x : Vec d ↦
      matrixOperatorNorm (finiteShellIncrement omega n m x) ^ p)
    (volume.restrict U)
  refine Integrable.mono' (integrable_const (S ^ p)) hcont.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem hUopen.measurableSet] with x hx
  rw [Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (matrixOperatorNorm_nonneg _) p)]
  exact hbound x hx

/-! ## The normalized `L^p`-by-`L∞` domination -/

/-! ## The source display `e.kmn.Lp` -/

end

end SuperdiffusionCLT.Section2.Estimates.Stream