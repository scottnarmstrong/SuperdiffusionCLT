/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.NewMixing.T3Pointwise
public import SuperdiffusionCLT.Section4.NewMixing.Splitting
public import SuperdiffusionCLT.Section4.NewMixing.JensenTiling
public import Homogenization.CoarseGraining.Subadditivity
public import Homogenization.Besov.Negative

/-!
# **The `T_3` bound** (`l.new.mixing.parameterized#T3-bound`)

Averages `T3Pointwise.lean`'s pointwise bound over the depth-`(m-n)` triadic
descendants of `cu_m` (`Homogenization.descendantsAverage`), using
`Homogenization.descendantsAverage_le_descendantsAverage` for the pointwise
step and `descendantsAverage_add`/`_const`/`_smul` to isolate the one
genuinely `z`-dependent piece, `matrixOperatorNorm (volumeAverageMat (cubeSet
R) (finiteShellIncrement omega ell L))`. That piece is bounded by `d² ×` the
global `L²(cu_m)` average via `JensenTiling.lean`'s `newMixParam_jensenTiling`
(square-Jensen per sub-cube, `sq_volumeAverage_le_volumeAverage_sq`, plus the
tower/tiling identity `volumeAverage_eq_descendantsAverage_integrableOn`); the
`d²` loss comes from that file's own `d`-scaled linear Jensen step
(`mixTail_matrixOperatorNorm_volumeAverageMat_le`, an entrywise bound, not the
sharp `‖∫f‖≤∫‖f‖`), so the amplitude below carries an explicit `d²` factor on
the `L²`-norm term.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.NewMixing

open Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Assumptions

noncomputable section

/-- The volume average of the finite shell increment is anti-symmetric
(re-derived locally: the identical private fact
`SuperdiffusionCLT.Section2.Localization.CutoffMinimizerPremises.matTranspose_volumeAverageMat_finiteShellIncrement`
is not importable under that name). -/
private theorem newMixParam_volumeAverageMat_finiteShellIncrement_skew {d : ℕ}
    (omega : ShellSeq d) (ell L : ℕ) (U : Set (Vec d)) :
    matTranspose (Homogenization.volumeAverageMat U (fun y => finiteShellIncrement omega ell L y)) =
      -(Homogenization.volumeAverageMat U (fun y => finiteShellIncrement omega ell L y)) := by
  refine SuperdiffusionCLT.Section2.Cutoff.matTranspose_volumeAverageMat U _ fun y i k => ?_
  have hsk := congrFun (congrFun (finiteShellIncrement_skew omega ell L y) k) i
  simpa only [Matrix.transpose_apply, Matrix.neg_apply, Pi.neg_apply] using hsk

/-- **`l.new.mixing.parameterized#T3-bound`**: the averaged
`T_3` bound, for `P = P_e^sigma`. -/
theorem newMixParam_t3Bound (d : ℕ) [NeZero d]
    {nu K : ℝ} (hnu : 0 < nu) (hK1 : 1 ≤ K)
    {P : MeasureTheory.ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P)
    {Cref : ℝ} (hCref1 : 1 ≤ Cref)
    {L m ell r n : ℕ} (hnm : n ≤ m)
    (hRC : |(sigmaBarInfinite nu r P)⁻¹ * sigmaBarSeq nu ell P n - 1| +
        |sigmaBarInfinite nu r P * sigmaBarStarInvSeq nu ell P n - 1| ≤
      Cref * (sigmaBarInfinite nu r P) ^ (-(2 : ℝ)) *
        (max 0 ((L : ℝ) - (m : ℝ)) + K * Real.log (L : ℝ) ^ (2 : ℝ)))
    {e : Vec d} (he : vecNormSq e ≤ 1) {sigma : ℝ} (hsigma2 : sigma ^ 2 = 1)
    {h0 : Mat d} (hh0 : matTranspose h0 = -h0) (omega : ShellSeq d) :
    Homogenization.descendantsAverage (originCube d (m : ℤ)) (m - n)
        (fun R => blockVecDot
          (blockMatVecMul
            (blockG (-(Homogenization.volumeAverageMat (cubeSet R)
                  (fun y => finiteShellIncrement omega ell L y) + h0)))
            ((sigma * Real.sqrt (sigmaBarInfinite nu r P)⁻¹) • e,
              Real.sqrt (sigmaBarInfinite nu r P) • e))
          (blockMatVecMul (annealedBlockMatrix nu ell P (cubeSet (originCube d (n : ℤ))))
            (blockMatVecMul
              (blockG (-(Homogenization.volumeAverageMat (cubeSet R)
                    (fun y => finiteShellIncrement omega ell L y) + h0)))
              ((sigma * Real.sqrt (sigmaBarInfinite nu r P)⁻¹) • e,
                Real.sqrt (sigmaBarInfinite nu r P) • e)))) ≤
      2 * vecNormSq e +
        2 * Cref * (sigmaBarInfinite nu r P) ^ (-(2 : ℝ)) *
          (max 0 ((L : ℝ) - (m : ℝ)) + K * Real.log (L : ℝ) ^ (2 : ℝ)) +
        (sigmaBarInfinite nu r P)⁻¹ * sigmaBarStarInvSeq nu ell P n *
          (2 * (d : ℝ) ^ 2 * Homogenization.volumeAverage (cubeSet (originCube d (m : ℤ)))
                (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ (2 : ℝ)) +
            2 * matrixOperatorNorm h0 ^ 2) := by
  set shomr := sigmaBarInfinite nu r P with hshomrdef
  have hshomr : 0 < shomr := sigmaBarInfinite_pos hnu r hPrefix hJ2 hJ3 hJ4
  set shomEllStarInv := sigmaBarStarInvSeq nu ell P n with hshomEllSIdef
  have hshomEllSIpos : 0 < shomEllStarInv :=
    sigmaBarStarInvSeq_pos hnu ell hPrefix hJ2 hJ3 hJ4 n
  set G := Cref * shomr ^ (-(2 : ℝ)) *
      (max 0 ((L : ℝ) - (m : ℝ)) + K * Real.log (L : ℝ) ^ (2 : ℝ)) with hGdef
  set CONST := 2 * vecNormSq e + 2 * G + shomr⁻¹ * shomEllStarInv * (2 * matrixOperatorNorm h0 ^ 2)
    with hCONSTdef
  -- Step 1: the pointwise bound, regrouped to `CONST + coef * matrixOperatorNorm(hz R)²`.
  have hpt : ∀ R ∈ Homogenization.descendantsAtDepth (originCube d (m : ℤ)) (m - n),
      blockVecDot
          (blockMatVecMul
            (blockG (-(Homogenization.volumeAverageMat (cubeSet R)
                  (fun y => finiteShellIncrement omega ell L y) + h0)))
            ((sigma * Real.sqrt shomr⁻¹) • e, Real.sqrt shomr • e))
          (blockMatVecMul (annealedBlockMatrix nu ell P (cubeSet (originCube d (n : ℤ))))
            (blockMatVecMul
              (blockG (-(Homogenization.volumeAverageMat (cubeSet R)
                    (fun y => finiteShellIncrement omega ell L y) + h0)))
              ((sigma * Real.sqrt shomr⁻¹) • e, Real.sqrt shomr • e))) ≤
        CONST + shomr⁻¹ * shomEllStarInv * 2 *
          matrixOperatorNorm (Homogenization.volumeAverageMat (cubeSet R)
            (fun y => finiteShellIncrement omega ell L y)) ^ 2 := by
    intro R _
    have hbase := newMixParam_t3Pointwise d hnu hK1 hPrefix hJ2 hJ3 hJ4 hCref1 hRC he hsigma2 hh0
      (newMixParam_volumeAverageMat_finiteShellIncrement_skew omega ell L (cubeSet R))
    rw [← hshomrdef] at hbase
    have hreg : 2 * vecNormSq e + 2 * G +
        shomr⁻¹ * shomEllStarInv *
          (2 * matrixOperatorNorm (Homogenization.volumeAverageMat (cubeSet R)
              (fun y => finiteShellIncrement omega ell L y)) ^ 2 + 2 * matrixOperatorNorm h0 ^ 2) =
        CONST + shomr⁻¹ * shomEllStarInv * 2 *
          matrixOperatorNorm (Homogenization.volumeAverageMat (cubeSet R)
            (fun y => finiteShellIncrement omega ell L y)) ^ 2 := by
      rw [hCONSTdef]; ring
    linarith only [hbase, hreg.le, hreg.ge]
  -- Step 2: average.
  have hstep2 := Homogenization.descendantsAverage_le_descendantsAverage
    (originCube d (m : ℤ)) (m - n) hpt
  -- Step 3: split the averaged RHS.
  have hsplit : Homogenization.descendantsAverage (originCube d (m : ℤ)) (m - n)
      (fun R => CONST + shomr⁻¹ * shomEllStarInv * 2 *
        matrixOperatorNorm (Homogenization.volumeAverageMat (cubeSet R)
          (fun y => finiteShellIncrement omega ell L y)) ^ 2) =
      CONST + shomr⁻¹ * shomEllStarInv * 2 *
        Homogenization.descendantsAverage (originCube d (m : ℤ)) (m - n)
          (fun R => matrixOperatorNorm (Homogenization.volumeAverageMat (cubeSet R)
            (fun y => finiteShellIncrement omega ell L y)) ^ 2) := by
    rw [Homogenization.descendantsAverage_add, Homogenization.descendantsAverage_const,
      Homogenization.descendantsAverage_smul]
  rw [hsplit] at hstep2
  -- Step 4: `newMixParam_jensenTiling` (`JensenTiling.lean`).
  have hcoefnn : (0 : ℝ) ≤ shomr⁻¹ * shomEllStarInv * 2 := by
    have h1 : (0 : ℝ) ≤ shomr⁻¹ := inv_nonneg.mpr hshomr.le
    have h2 : (0 : ℝ) ≤ shomEllStarInv := hshomEllSIpos.le
    positivity
  have hJensen := newMixParam_jensenTiling omega ell L m n hnm
  have hjstep : shomr⁻¹ * shomEllStarInv * 2 *
      Homogenization.descendantsAverage (originCube d (m : ℤ)) (m - n)
        (fun R => matrixOperatorNorm (Homogenization.volumeAverageMat (cubeSet R)
          (fun y => finiteShellIncrement omega ell L y)) ^ 2) ≤
      shomr⁻¹ * shomEllStarInv * 2 *
        ((d : ℝ) ^ 2 * Homogenization.volumeAverage (cubeSet (originCube d (m : ℤ)))
          (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ (2 : ℝ))) :=
    mul_le_mul_of_nonneg_left hJensen hcoefnn
  have hfinal : CONST + shomr⁻¹ * shomEllStarInv * 2 *
      ((d : ℝ) ^ 2 * Homogenization.volumeAverage (cubeSet (originCube d (m : ℤ)))
        (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ (2 : ℝ))) =
      2 * vecNormSq e + 2 * G + shomr⁻¹ * shomEllStarInv *
        (2 * (d : ℝ) ^ 2 * Homogenization.volumeAverage (cubeSet (originCube d (m : ℤ)))
              (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ (2 : ℝ)) +
          2 * matrixOperatorNorm h0 ^ 2) := by
    rw [hCONSTdef]; ring
  linarith only [hstep2, hjstep, hfinal.le, hfinal.ge]

end
end SuperdiffusionCLT.Section4.NewMixing
