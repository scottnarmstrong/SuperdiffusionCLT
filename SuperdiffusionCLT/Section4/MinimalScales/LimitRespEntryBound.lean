/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Cutoff.CenteredCoeffOn

/-!
# A raw-`Set`-domain entry bound for the centered cutoff field

`SuperdiffusionCLT.Section2.Cutoff.abs_centeredEntryBound` gives an entry
bound for `centeredCoefficientCutoff` on a Chapter 2 `Book.Ch02.Domain d`
(whose set-coercion is an *open* triadic cube). `srootE_field`
(`SuperdiffusionCLT.Section4.MinimalScales.SkeletonMathcalE`) recenters
over the raw, half-open `cubeSet (originCube d m)`, which is not itself
representable as a `Book.Ch02.Domain d`. This module reproves the same entry
bound directly for a raw `cubeSet`, using the same raw-`Set` ingredients
(`streamCutoffEntryBound`, `abs_streamCutoffEntryBound`,
`abs_volumeAverageMat_streamCutoff_entry_le`) that the Chapter 2 wrapper
itself is built from.

## Main result

* `srootL3_exists_centeredEntryBound`: an entry bound for
  `centeredCoefficientCutoff nu omega L (cubeSet (originCube d m))` on that
  same cube.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2

noncomputable section

/-- An entry bound for the level-`L` centered field
`ν Id + (k_L - (k_L)_U)` on the recentering cube `U = cubeSet (originCube d m)`
itself, with no `Book.Ch02.Domain` wrapper. -/
theorem srootL3_exists_centeredEntryBound {d : ℕ} (nu : ℝ) (hnu : 0 ≤ nu)
    (omega : ShellSeq d) (L m : ℕ) :
    ∃ C : ℝ, ∀ x ∈ cubeSet (originCube d (m : ℤ)), ∀ i j : Fin d,
      |(centeredCoefficientCutoff nu omega L
          (cubeSet (originCube d (m : ℤ)))).toCoeffField x i j| ≤ C := by
  classical
  set U : Set (Vec d) := cubeSet (originCube d (m : ℤ)) with hUdef
  have hUb : Bornology.IsBounded U := isBounded_cubeSet _
  have hUmeas : MeasurableSet U := measurableSet_cubeSet _
  have hUvol : 0 < (volume U).toReal := by
    rw [hUdef, volume_cubeSet_toReal]
    exact cubeVolume_pos _
  set CS : ℝ := ∑ p : Fin d × Fin d, |streamCutoffEntryBound hUb omega L p| with hCSdef
  have hstream : ∀ x ∈ U, ∀ i j : Fin d, |streamCutoff omega L x i j| ≤ CS := by
    intro x hx i j
    calc |streamCutoff omega L x i j|
        ≤ |streamCutoffEntryBound hUb omega L (i, j)| :=
          (abs_streamCutoffEntryBound hUb omega L (i, j) x hx).trans (le_abs_self _)
      _ ≤ CS := Finset.single_le_sum
          (f := fun p : Fin d × Fin d => |streamCutoffEntryBound hUb omega L p|)
          (fun p _ => abs_nonneg _) (Finset.mem_univ (i, j))
  have havg : ∀ i j : Fin d,
      |volumeAverageMat U (streamCutoff omega L) i j| ≤ CS :=
    fun i j => abs_volumeAverageMat_streamCutoff_entry_le hUb hUmeas hUvol hstream i j
  refine ⟨nu + 2 * CS, fun x hx i j => ?_⟩
  have hone : |(nu • (1 : Mat d)) i j| ≤ nu := by
    by_cases hij : i = j
    · subst hij
      have heq : (nu • (1 : Mat d)) i i = nu := by
        simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
      rw [heq, abs_of_nonneg hnu]
    · have heq : (nu • (1 : Mat d)) i j = 0 := by
        simp only [Matrix.smul_apply, Matrix.one_apply_ne hij, smul_eq_mul, mul_zero]
      rw [heq, abs_zero]
      exact hnu
  have hcentered : (centeredCoefficientCutoff nu omega L U).toCoeffField x i j =
      (nu • (1 : Mat d)) i j +
        (streamCutoff omega L x i j - volumeAverageMat U (streamCutoff omega L) i j) := by
    rw [RegCoeffField.toCoeffField_apply, centeredCoefficientCutoff_apply,
      centeredStreamCutoff_apply, Matrix.add_apply, Matrix.sub_apply]
  rw [hcentered]
  calc |(nu • (1 : Mat d)) i j +
        (streamCutoff omega L x i j - volumeAverageMat U (streamCutoff omega L) i j)|
      ≤ |(nu • (1 : Mat d)) i j| +
          |streamCutoff omega L x i j - volumeAverageMat U (streamCutoff omega L) i j| :=
        abs_add_le _ _
    _ ≤ nu + (|streamCutoff omega L x i j| + |volumeAverageMat U (streamCutoff omega L) i j|) :=
        add_le_add hone (abs_sub _ _)
    _ ≤ nu + 2 * CS := by
        have h1 := hstream x hx i j
        have h2 := havg i j
        linarith only [h1, h2]

end

end SuperdiffusionCLT.Section4.MinimalScales
