/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.Mixing.TermGaugeIntegrable
public import SuperdiffusionCLT.Section4.Mixing.TermGaugeBilinear
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementPthMoment
public import SuperdiffusionCLT.Section3.Terms.ConcentrationComparisonB
public import SuperdiffusionCLT.Probability.GammaSigmaHelpers
public import SuperdiffusionCLT.Frozen.Section2.CutoffLocalization
public import SuperdiffusionCLT.Section4.Mixing.AnnealedFinal
public import SuperdiffusionCLT.Section4.Mixing.TermTailEllipticity

/-!
# mixTail: the probabilistic assembly of `hGaugeBound`

This module supplies
Jensen bounds for `matrixOperatorNorm (volumeAverageMat R f)` in terms of
`volumeAverage R (matrixOperatorNorm ∘ f)` and its square, combines them with
the `p`-th moment bound `isBigO_gammaSigma_finiteShellIncrementPthMoment`
(`p = 1, 2`) to get per-cube `Γ2`/`Γ1` control of the gauge term's
`matrixOperatorNorm ‖h_R‖`/`‖h_R‖²`, and combines with
`TermGaugeBilinear.lean`'s deterministic bilinear bound. All constants are
explicit (no bare exponents without a constant).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

open MeasureTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff (ShellSeq finiteShellIncrement)
open SuperdiffusionCLT.Section2.Estimates.Stream

noncomputable section

variable {d : ℕ}

/-! ## Scalar Jensen for `volumeAverage` -/

/-- The scalar Jensen inequality `|volumeAverage U g| ≤ volumeAverage U |g|`,
unconditional (both sides are `0` in the junk-value convention when `g` is not
integrable). -/
theorem mixTail_abs_volumeAverage_le (U : Set (Vec d)) (g : Vec d → ℝ) :
    |volumeAverage U g| ≤ volumeAverage U (fun x ↦ |g x|) := by
  show |(volume U).toReal⁻¹ * ∫ x in U, g x ∂volume| ≤
    (volume U).toReal⁻¹ * ∫ x in U, |g x| ∂volume
  rw [abs_mul, abs_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 ENNReal.toReal_nonneg)
  simpa only [Real.norm_eq_abs] using
    MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict U) g

/-! ## The linear (`d`-scaled) Jensen bound for `matrixOperatorNorm ∘ volumeAverageMat` -/

/-- **The linear Jensen bound.** `matrixOperatorNorm (volumeAverageMat R f) ≤ d *
volumeAverage R (matrixOperatorNorm ∘ f)`, for `f := fun y => finiteShellIncrement
omega n m y`, at an arbitrary triadic cube `R` of natural-number scale `l`. -/
theorem mixTail_matrixOperatorNorm_volumeAverageMat_le [NeZero d] (omega : ShellSeq d)
    (n m : ℕ) (R : Homogenization.TriadicCube d) (l : ℕ) (hl : R.scale = (l : ℤ)) :
    matrixOperatorNorm
        (volumeAverageMat (cubeSet R) (fun y ↦ finiteShellIncrement omega n m y)) ≤
      (d : ℝ) *
        volumeAverage (cubeSet R)
          (fun x ↦ matrixOperatorNorm (finiteShellIncrement omega n m x)) := by
  have hMnn : (0 : ℝ) ≤
      volumeAverage (cubeSet R)
        (fun x ↦ matrixOperatorNorm (finiteShellIncrement omega n m x)) := by
    have hInt := mixTail_integrableOn_matrixOperatorNorm_rpow_finiteShellIncrement_cubeSet
      omega n m (p := 1) (by norm_num) R l hl
    simp only [Real.rpow_one] at hInt
    refine volumeAverage_nonneg_of_nonneg_on (measurableSet_cubeSet R) fun x _ ↦ ?_
    exact matrixOperatorNorm_nonneg _
  refine matrixOperatorNorm_le_of_entry_bound _ hMnn fun i j ↦ ?_
  have hentry :
      volumeAverageMat (cubeSet R) (fun y ↦ finiteShellIncrement omega n m y) i j =
        volumeAverage (cubeSet R)
          (fun x ↦ finiteShellIncrement omega n m x i j) := rfl
  rw [hentry]
  refine (mixTail_abs_volumeAverage_le (cubeSet R)
    (fun x ↦ finiteShellIncrement omega n m x i j)).trans ?_
  have hIntNorm : IntegrableOn
      (fun x ↦ matrixOperatorNorm (finiteShellIncrement omega n m x))
      (cubeSet R) volume := by
    have hInt := mixTail_integrableOn_matrixOperatorNorm_rpow_finiteShellIncrement_cubeSet
      omega n m (p := 1) (by norm_num) R l hl
    simpa only [Real.rpow_one] using hInt
  have hIntEntry : IntegrableOn
      (fun x ↦ |finiteShellIncrement omega n m x i j|) (cubeSet R) volume := by
    refine Integrable.mono' hIntNorm.integrable
      ((continuous_abs.measurable.comp ((finiteShellIncrement omega n m).entry_measurable i j)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x ↦ ?_)
    rw [Real.norm_eq_abs, abs_abs]
    exact abs_entry_le_matrixOperatorNorm (finiteShellIncrement omega n m x) i j
  refine volumeAverage_le_volumeAverage_of_le_on (measurableSet_cubeSet R) hIntEntry
    hIntNorm fun x _ ↦ ?_
  exact abs_entry_le_matrixOperatorNorm (finiteShellIncrement omega n m x) i j

/-! ## The `Γ2` (linear) Orlicz bound on `matrixOperatorNorm ‖h_R‖` -/

variable {P : ProbabilityMeasure (ShellSeq d)}

/-- **The `Γ2` Orlicz bound on `matrixOperatorNorm (volumeAverageMat R (Δk))`**,
at the explicit constant `d * finiteShellIncrementPthMomentConst d 1`. -/
theorem mixTail_isBigO_matrixOperatorNorm_volumeAverageMat [NeZero d]
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (ell L : ℕ) (hellL : ell < L) (R : Homogenization.TriadicCube d)
    (l : ℕ) (hl : R.scale = (l : ℤ)) :
    IsBigO P.toMeasure (gammaSigma 2)
      (fun omega ↦ matrixOperatorNorm
        (volumeAverageMat (cubeSet R) (fun y ↦ finiteShellIncrement omega ell L y)))
      ((d : ℝ) * finiteShellIncrementPthMomentConst d 1 *
        Real.sqrt (((L - ell : ℕ) : ℕ) : ℝ)) := by
  have hmom := isBigO_gammaSigma_finiteShellIncrementPthMoment (P := P) hPrefix hJ2 hJ3 hJ4
    (p := 1) (le_refl (1 : ℝ)) hellL R
  simp only [Real.rpow_one, div_one] at hmom
  have hscaled := hmom.const_mul (Nat.cast_nonneg (α := ℝ) d)
  rw [show (d : ℝ) * (finiteShellIncrementPthMomentConst d 1 * Real.sqrt (((L - ell : ℕ) : ℕ) : ℝ))
      = (d : ℝ) * finiteShellIncrementPthMomentConst d 1 * Real.sqrt (((L - ell : ℕ) : ℕ) : ℝ) by
    ring] at hscaled
  refine hscaled.of_abs_le fun omega ↦ ?_
  have hle := mixTail_matrixOperatorNorm_volumeAverageMat_le omega ell L R l hl
  have hVnn : (0:ℝ) ≤
      volumeAverage (cubeSet R) (fun x ↦ matrixOperatorNorm (finiteShellIncrement omega ell L x)) :=
    volumeAverage_nonneg_of_nonneg_on (measurableSet_cubeSet R)
      fun x _ ↦ matrixOperatorNorm_nonneg _
  rw [abs_of_nonneg (matrixOperatorNorm_nonneg _),
    abs_of_nonneg (mul_nonneg (Nat.cast_nonneg d) hVnn)]
  refine hle.trans_eq ?_
  ring

/-! ## The `Γ1` (quadratic) Orlicz bound on `matrixOperatorNorm ‖h_R‖²` -/

/-- `MemLp` of the pointwise increment size on the normalized cube measure,
from its samplewise `L²` integrability on `cubeSet R`. -/
private theorem mixTail_memLp_matrixOperatorNorm_finiteShellIncrement [NeZero d]
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

/-- **The `Γ1` Orlicz bound on `matrixOperatorNorm (volumeAverageMat R (Δk))²`**,
at the explicit constant `d² * finiteShellIncrementPthMomentConst d 2 ²`. -/
theorem mixTail_isBigO_matrixOperatorNorm_sq_volumeAverageMat [NeZero d]
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (ell L : ℕ) (hellL : ell < L) (R : Homogenization.TriadicCube d)
    (l : ℕ) (hl : R.scale = (l : ℤ)) :
    IsBigO P.toMeasure (gammaSigma 1)
      (fun omega ↦ matrixOperatorNorm
        (volumeAverageMat (cubeSet R) (fun y ↦ finiteShellIncrement omega ell L y)) ^ 2)
      ((d : ℝ) ^ 2 * finiteShellIncrementPthMomentConst d 2 ^ 2 *
        (((L - ell : ℕ) : ℕ) : ℝ)) := by
  have hmom := isBigO_gammaSigma_finiteShellIncrementPthMoment (P := P) hPrefix hJ2 hJ3 hJ4
    (p := 2) (by norm_num) hellL R
  rw [show (2 : ℝ) / 2 = 1 by norm_num] at hmom
  have hfuneq :
      (fun omega : ShellSeq d ↦
          volumeAverage (cubeSet R)
            (fun x ↦ matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ (2 : ℝ))) =
        fun omega : ShellSeq d ↦
          volumeAverage (cubeSet R)
            (fun x ↦ matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ (2 : ℕ)) := by
    funext omega
    congr 1
    funext x
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hfuneq] at hmom
  have hsqrt2 : Real.sqrt (((L - ell : ℕ) : ℕ) : ℝ) ^ (2 : ℝ) = (((L - ell : ℕ) : ℕ) : ℝ) := by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast, Real.sq_sqrt (by positivity)]
  rw [hsqrt2] at hmom
  have hscaled := hmom.const_mul (show (0 : ℝ) ≤ (d : ℝ) ^ 2 from sq_nonneg _)
  rw [show (d : ℝ) ^ 2 * (finiteShellIncrementPthMomentConst d 2 ^ (2:ℝ) * (((L - ell : ℕ) : ℕ) : ℝ))
      = (d : ℝ) ^ 2 * finiteShellIncrementPthMomentConst d 2 ^ 2 * (((L - ell : ℕ) : ℕ) : ℝ) by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]; ring] at hscaled
  refine hscaled.of_abs_le fun omega ↦ ?_
  have hle := mixTail_matrixOperatorNorm_volumeAverageMat_le omega ell L R l hl
  have hVnn : (0 : ℝ) ≤
      volumeAverage (cubeSet R) (fun x ↦ matrixOperatorNorm (finiteShellIncrement omega ell L x)) :=
    volumeAverage_nonneg_of_nonneg_on (measurableSet_cubeSet R)
      fun x _ ↦ matrixOperatorNorm_nonneg _
  have hsq : matrixOperatorNorm
        (volumeAverageMat (cubeSet R) (fun y ↦ finiteShellIncrement omega ell L y)) ^ 2 ≤
      (d : ℝ) ^ 2 *
        volumeAverage (cubeSet R)
          (fun x ↦ matrixOperatorNorm (finiteShellIncrement omega ell L x)) ^ 2 := by
    have h1 : (0:ℝ) ≤ matrixOperatorNorm
        (volumeAverageMat (cubeSet R) (fun y ↦ finiteShellIncrement omega ell L y)) :=
      matrixOperatorNorm_nonneg _
    nlinarith only [hle, h1, hVnn, Nat.cast_nonneg (α := ℝ) d,
      mul_le_mul_of_nonneg_left hle (mul_nonneg (Nat.cast_nonneg (α := ℝ) d) hVnn)]
  have hJensenSq :
      volumeAverage (cubeSet R)
          (fun x ↦ matrixOperatorNorm (finiteShellIncrement omega ell L x)) ^ 2 ≤
        volumeAverage (cubeSet R)
          (fun x ↦ matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ 2) :=
    SuperdiffusionCLT.Section3.Terms.sq_volumeAverage_le_volumeAverage_sq R
      (mixTail_memLp_matrixOperatorNorm_finiteShellIncrement omega ell L R l hl)
  have hXnn : (0:ℝ) ≤ (d:ℝ)^2 *
      volumeAverage (cubeSet R) (fun x ↦ matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ 2) :=
    mul_nonneg (sq_nonneg _)
      (volumeAverage_nonneg_of_nonneg_on (measurableSet_cubeSet R)
        fun x _ ↦ sq_nonneg _)
  have hchain : matrixOperatorNorm (volumeAverageMat (cubeSet R)
        (fun y ↦ finiteShellIncrement omega ell L y)) ^ 2 ≤
      (d:ℝ)^2 * volumeAverage (cubeSet R)
        (fun x ↦ matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ 2) := by
    calc matrixOperatorNorm (volumeAverageMat (cubeSet R)
          (fun y ↦ finiteShellIncrement omega ell L y)) ^ 2
        ≤ (d:ℝ)^2 * volumeAverage (cubeSet R)
            (fun x ↦ matrixOperatorNorm (finiteShellIncrement omega ell L x)) ^ 2 := hsq
      _ ≤ (d:ℝ)^2 * volumeAverage (cubeSet R)
            (fun x ↦ matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ 2) :=
          mul_le_mul_of_nonneg_left hJensenSq (sq_nonneg _)
  rw [abs_of_nonneg (sq_nonneg (matrixOperatorNorm (volumeAverageMat (cubeSet R)
    (fun y ↦ finiteShellIncrement omega ell L y))))]
  exact hchain.trans (le_abs_self ((d:ℝ)^2 * volumeAverage (cubeSet R)
    (fun x ↦ matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ 2)))

end

end SuperdiffusionCLT.Section4.Mixing
