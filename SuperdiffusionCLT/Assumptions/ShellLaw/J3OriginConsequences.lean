/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellLaw.J3Consequences

/-!
# Origin consequences of the marginal J3 tail

This module records the deterministic domination chain from the direct J3
observable to the shell value norm, the matrix operator norm at the origin,
and each scalar matrix entry at the origin. It then transfers the J3
`L²` control to these observables under the canonical natural-indexed shell
law.

No centering or independence property is used.
-/

@[expose] public section

namespace SuperdiffusionCLT.Frozen.Assumptions.ShellField

open Homogenization
open Homogenization.Book.Ch02

noncomputable section

variable {d : ℕ}

/-- The value term of the scale-`n` cube norm is dominated by the complete J3
observable. -/
theorem shellCubeValueNorm_le_j3Observable (n : ℕ) (j : ShellField d) :
    shellCubeValueNorm n j ≤ j3Observable d n j := by
  calc
    shellCubeValueNorm n j ≤
        shellCubeValueNorm n j +
          (Real.sqrt d * (3 : ℝ) ^ n) * shellCubeDerivNorm n j :=
      le_add_of_nonneg_right
        (mul_nonneg
          (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg (by norm_num) n))
          (shellCubeDerivNorm_nonneg n j))
    _ ≤ shellCubeValueNorm n j +
          (Real.sqrt d * (3 : ℝ) ^ n) * shellCubeDerivNorm n j +
          ((d : ℝ) * (3 : ℝ) ^ (2 * n)) * shellCubeSecondDerivNorm n j :=
      le_add_of_nonneg_right
        (mul_nonneg
          (mul_nonneg (Nat.cast_nonneg d) (pow_nonneg (by norm_num) (2 * n)))
          (shellCubeSecondDerivNorm_nonneg n j))
    _ = j3Observable d n j := rfl

private theorem zero_mem_shellOpenCube (d n : ℕ) :
    (0 : Vec d) ∈ openCubeSet (originCube d (n : ℤ)) := by
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have hpow : (0 : ℝ) < (3 : ℝ) ^ (n : ℤ) :=
    zpow_pos (by norm_num) (n : ℤ)
  constructor
  · exact mul_neg_of_neg_of_pos (by norm_num) hpow
  · exact mul_pos (by norm_num) hpow

/-- The natural-cube value norm controls the shell's Euclidean matrix operator
norm at the spatial origin. -/
theorem matrixOperatorNorm_zero_le_shellCubeValueNorm
    (n : ℕ) (j : ShellField d) :
    matrixOperatorNorm (j 0) ≤ shellCubeValueNorm n j :=
  matrixOperatorNorm_apply_le_shellCubeValueNorm n j
    ⟨0, zero_mem_shellOpenCube d n⟩

/-- The complete scale-`n` J3 observable controls the shell's Euclidean matrix
operator norm at the spatial origin. -/
theorem matrixOperatorNorm_zero_le_j3Observable
    (n : ℕ) (j : ShellField d) :
    matrixOperatorNorm (j 0) ≤ j3Observable d n j :=
  (matrixOperatorNorm_zero_le_shellCubeValueNorm n j).trans
    (shellCubeValueNorm_le_j3Observable n j)

/-- The complete scale-`n` J3 observable controls every scalar matrix entry at
the spatial origin. -/
theorem abs_entry_zero_le_j3Observable
    (n : ℕ) (j : ShellField d) (i k : Fin d) :
    |j 0 i k| ≤ j3Observable d n j :=
  (abs_entry_le_matrixOperatorNorm (j 0) i k).trans
    (matrixOperatorNorm_zero_le_j3Observable n j)

end

end SuperdiffusionCLT.Frozen.Assumptions.ShellField

namespace SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3

open Homogenization MeasureTheory

noncomputable section

variable {d : ℕ}
variable {P : ProbabilityMeasure (ℕ → ShellField d)}

private theorem measurable_matrixOperatorNorm_zero_coordinate (n : ℕ) :
    Measurable
      (fun F : ℕ → ShellField d ↦
        Homogenization.Book.Ch02.matrixOperatorNorm ((F n) 0)) :=
  ShellField.continuous_matrixOperatorNorm.measurable.comp
    ((ShellField.measurable_eval 0).comp
      (ShellField.measurable_shellCoordinate n))

/-- The matrix operator norm of shell `n` at the origin belongs to `L²` under
a J3 law. -/
theorem memLp_two_matrixOperatorNorm_zero_coordinate
    (hJ3 : ShellLawJ3 d P) (n : ℕ) :
    MemLp
      (fun F : ℕ → ShellField d ↦
        Homogenization.Book.Ch02.matrixOperatorNorm ((F n) 0))
      2 P.toMeasure := by
  apply (hJ3.memLp_two_j3Observable_coordinate n).mono'
  · exact (measurable_matrixOperatorNorm_zero_coordinate n).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun F ↦ by
      rw [Real.norm_eq_abs,
        abs_of_nonneg
          (Homogenization.Book.Ch02.matrixOperatorNorm_nonneg ((F n) 0))]
      exact ShellField.matrixOperatorNorm_zero_le_j3Observable n (F n)

end

end SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3
