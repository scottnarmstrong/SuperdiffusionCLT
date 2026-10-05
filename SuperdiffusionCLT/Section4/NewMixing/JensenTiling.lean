/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.Mixing.TermGaugeAssembly
public import SuperdiffusionCLT.Section3.Terms.ConcentrationComparisonB
public import SuperdiffusionCLT.Section2.Estimates.Stream.ShellHminusEndpointOrderOneC

/-!
# `hJensen`: proving the Jensen/tiling fact `T3Bound.lean` had carried as a hypothesis

Per-cube square-Jensen (`SuperdiffusionCLT.Section3.Terms.sq_volumeAverage_le_volumeAverage_sq`)
composed with the linear (`d`-scaled) Jensen bound on `matrixOperatorNorm ∘ volumeAverageMat`
(`SuperdiffusionCLT.Section4.Mixing.mixTail_matrixOperatorNorm_volumeAverageMat_le`,
`TermGaugeAssembly.lean`'s own `hchain` reproved standalone here) gives the per-cube bound;
the tower property of nested volume averages
(`volumeAverage_eq_descendantsAverage_integrableOn`, from `Section2`)
gives the tiling identity. Combined via `descendantsAverage_le_descendantsAverage`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.NewMixing

open Homogenization
open Homogenization.Book.Ch02
open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section4.Mixing

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- `MemLp` of the pointwise increment size on the normalized cube measure
(the identical fact is `private` as
`SuperdiffusionCLT.Section4.Mixing.mixTail_memLp_matrixOperatorNorm_finiteShellIncrement`;
reproved standalone here from the same public ingredients). -/
private theorem newMixParam_memLp_matrixOperatorNorm_finiteShellIncrement
    (omega : ShellSeq d) (ell L : ℕ) (R : Homogenization.TriadicCube d) (l : ℕ)
    (hl : R.scale = (l : ℤ)) :
    MemLp (fun x ↦ matrixOperatorNorm (finiteShellIncrement omega ell L x)) 2
      (normalizedCubeMeasure R) := by
  have hAEmeas : AEStronglyMeasurable
      (fun x ↦ matrixOperatorNorm (finiteShellIncrement omega ell L x))
      (normalizedCubeMeasure R) :=
    Measurable.aestronglyMeasurable
      (continuous_matrixOperatorNorm_finiteShellIncrement omega ell L).measurable
  rw [memLp_two_iff_integrable_sq hAEmeas]
  have hIntOn := mixTail_integrableOn_matrixOperatorNorm_rpow_finiteShellIncrement_cubeSet
    omega ell L (p := 2) (by norm_num) R l hl
  have hIntSq : Integrable
      (fun x ↦ matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ 2)
      (volume.restrict (cubeSet R)) := by
    have heq : (fun x : Vec d ↦ matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ (2 : ℝ))
        = fun x ↦ matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ (2 : ℕ) := by
      funext x
      norm_num [Real.rpow_natCast]
    rwa [heq] at hIntOn
  have hcvol : Homogenization.cubeVolume R ≠ 0 := (Homogenization.cubeVolume_pos R).ne'
  have hc0 : ENNReal.ofReal ((Homogenization.cubeVolume R)⁻¹) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact inv_pos.2 (Homogenization.cubeVolume_pos R)
  have hctop : ENNReal.ofReal ((Homogenization.cubeVolume R)⁻¹) ≠ ⊤ := ENNReal.ofReal_ne_top
  show Integrable (fun x ↦ matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ 2)
    (normalizedCubeMeasure R)
  show Integrable (fun x ↦ matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ 2)
    (ENNReal.ofReal ((Homogenization.cubeVolume R)⁻¹) • Homogenization.cubeMeasure R)
  rwa [integrable_smul_measure hc0 hctop]

/-- **Per-cube Jensen**: `matrixOperatorNorm (volumeAverageMat (cubeSet R) f)² ≤ d² *
volumeAverage (cubeSet R) (fun x => matrixOperatorNorm (f x))²`, for `f := fun y =>
finiteShellIncrement omega ell L y`. -/
private theorem newMixParam_matrixOperatorNorm_sq_volumeAverageMat_le
    (omega : ShellSeq d) (ell L : ℕ) (R : Homogenization.TriadicCube d) (l : ℕ)
    (hl : R.scale = (l : ℤ)) :
    matrixOperatorNorm
        (volumeAverageMat (cubeSet R) (fun y ↦ finiteShellIncrement omega ell L y)) ^ 2 ≤
      (d : ℝ) ^ 2 * volumeAverage (cubeSet R)
        (fun x ↦ matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ 2) := by
  have hle := mixTail_matrixOperatorNorm_volumeAverageMat_le omega ell L R l hl
  have hVnn : (0 : ℝ) ≤
      volumeAverage (cubeSet R) (fun x ↦ matrixOperatorNorm (finiteShellIncrement omega ell L x)) :=
    volumeAverage_nonneg_of_nonneg_on (measurableSet_cubeSet R)
      fun x _ ↦ matrixOperatorNorm_nonneg _
  have h1 : (0 : ℝ) ≤ matrixOperatorNorm
      (volumeAverageMat (cubeSet R) (fun y ↦ finiteShellIncrement omega ell L y)) :=
    matrixOperatorNorm_nonneg _
  have hsq : matrixOperatorNorm
        (volumeAverageMat (cubeSet R) (fun y ↦ finiteShellIncrement omega ell L y)) ^ 2 ≤
      (d : ℝ) ^ 2 *
        volumeAverage (cubeSet R)
          (fun x ↦ matrixOperatorNorm (finiteShellIncrement omega ell L x)) ^ 2 := by
    nlinarith only [hle, h1, hVnn, Nat.cast_nonneg (α := ℝ) d,
      mul_le_mul_of_nonneg_left hle (mul_nonneg (Nat.cast_nonneg (α := ℝ) d) hVnn)]
  have hJensenSq :
      volumeAverage (cubeSet R)
          (fun x ↦ matrixOperatorNorm (finiteShellIncrement omega ell L x)) ^ 2 ≤
        volumeAverage (cubeSet R)
          (fun x ↦ matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ 2) :=
    SuperdiffusionCLT.Section3.Terms.sq_volumeAverage_le_volumeAverage_sq R
      (newMixParam_memLp_matrixOperatorNorm_finiteShellIncrement omega ell L R l hl)
  calc matrixOperatorNorm (volumeAverageMat (cubeSet R)
        (fun y ↦ finiteShellIncrement omega ell L y)) ^ 2
      ≤ (d : ℝ) ^ 2 * volumeAverage (cubeSet R)
          (fun x ↦ matrixOperatorNorm (finiteShellIncrement omega ell L x)) ^ 2 := hsq
    _ ≤ (d : ℝ) ^ 2 * volumeAverage (cubeSet R)
          (fun x ↦ matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ 2) :=
        mul_le_mul_of_nonneg_left hJensenSq (sq_nonneg _)

/-- **`hJensen`, proved**: the averaged, tiled Jensen bound `T3Bound.lean` had carried as a
named hypothesis. Every triadic cube in `descendantsAtDepth (originCube d m) (m-n)` has
scale `n` (`scale_eq_sub_of_mem_descendantsAtDepth`, using `n ≤ m`), so
`newMixParam_matrixOperatorNorm_sq_volumeAverageMat_le` applies uniformly, and
`volumeAverage_eq_descendantsAverage_integrableOn` supplies the tiling identity. -/
theorem newMixParam_jensenTiling (omega : ShellSeq d) (ell L m n : ℕ) (hnm : n ≤ m) :
    Homogenization.descendantsAverage (originCube d (m : ℤ)) (m - n)
        (fun R => matrixOperatorNorm (Homogenization.volumeAverageMat (cubeSet R)
            (fun y => finiteShellIncrement omega ell L y)) ^ 2) ≤
      (d : ℝ) ^ 2 * Homogenization.volumeAverage (cubeSet (originCube d (m : ℤ)))
        (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ (2 : ℝ)) := by
  have hscale : ∀ R ∈ Homogenization.descendantsAtDepth (originCube d (m : ℤ)) (m - n),
      R.scale = (n : ℤ) := by
    intro R hR
    have h := Homogenization.scale_eq_sub_of_mem_descendantsAtDepth hR
    have hQscale : (Homogenization.originCube d (m : ℤ)).scale = (m : ℤ) := by
      simp [Homogenization.originCube]
    rw [hQscale] at h
    rw [h]
    have : ((m - n : ℕ) : ℤ) = (m : ℤ) - (n : ℤ) := by
      have := Int.natCast_sub hnm
      simpa using this
    rw [this]
    ring
  have hpt : ∀ R ∈ Homogenization.descendantsAtDepth (originCube d (m : ℤ)) (m - n),
      matrixOperatorNorm (Homogenization.volumeAverageMat (cubeSet R)
          (fun y => finiteShellIncrement omega ell L y)) ^ 2 ≤
        (d : ℝ) ^ 2 * volumeAverage (cubeSet R)
          (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ 2) :=
    fun R hR => newMixParam_matrixOperatorNorm_sq_volumeAverageMat_le omega ell L R n (hscale R hR)
  have hstep := Homogenization.descendantsAverage_le_descendantsAverage
    (originCube d (m : ℤ)) (m - n) hpt
  have hconst : Homogenization.descendantsAverage (originCube d (m : ℤ)) (m - n)
      (fun R => (d : ℝ) ^ 2 * volumeAverage (cubeSet R)
        (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ 2)) =
      (d : ℝ) ^ 2 * Homogenization.descendantsAverage (originCube d (m : ℤ)) (m - n)
        (fun R => volumeAverage (cubeSet R)
          (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ 2)) :=
    Homogenization.descendantsAverage_smul (originCube d (m : ℤ)) (m - n) ((d : ℝ) ^ 2) _
  rw [hconst] at hstep
  have hIntOn := mixTail_integrableOn_matrixOperatorNorm_rpow_finiteShellIncrement_cubeSet
    omega ell L (p := 2) (by norm_num) (originCube d (m : ℤ)) m rfl
  have hIntOnSq : IntegrableOn
      (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ 2)
      (cubeSet (originCube d (m : ℤ))) volume := by
    have heq : (fun x : Vec d ↦ matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ (2 : ℝ))
        = fun x ↦ matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ (2 : ℕ) := by
      funext x
      norm_num [Real.rpow_natCast]
    rwa [heq] at hIntOn
  have htile : volumeAverage (cubeSet (originCube d (m : ℤ)))
      (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ 2) =
      Homogenization.descendantsAverage (originCube d (m : ℤ)) (m - n)
        (fun R => volumeAverage (cubeSet R)
          (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ 2)) :=
    volumeAverage_eq_descendantsAverage_integrableOn (originCube d (m : ℤ)) (m - n) hIntOnSq
  rw [← htile] at hstep
  have hcast : volumeAverage (cubeSet (originCube d (m : ℤ)))
      (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ 2) =
      volumeAverage (cubeSet (originCube d (m : ℤ)))
        (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ (2 : ℝ)) := by
    congr 1
    funext x
    norm_num [Real.rpow_natCast]
  rw [hcast] at hstep
  exact hstep

end
end SuperdiffusionCLT.Section4.NewMixing
