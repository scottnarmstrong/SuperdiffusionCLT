/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.SigmaBarComparison.NearAdditivityC

/-!
# Near-additivity, the pointwise identity

The paper (proof of `l.localization`, near-additivity step) takes the upper-left block of
`e.localization.ml` at `P = (e_0, 0)`. This file proves the resulting pointwise
identity: for every shell sequence,

`bfA_L(cu_n)_{00} - bfA_ell(cu_n)_{00} - h^t s_{ell,*}^{-1} h - (cross) = Err`,

where `Err` is `localizationT1CubeError` at `P = (e_0, 0)` and `(cross)` is the
printed cross term `kcg^t s^{-1} h + h^t s^{-1} kcg`, read off the raw blocks
of `bfA_ell(cu_n)` (`sbNear_crossRaw`). In this development's block convention
the lower-left block is `-s^{-1} kcg`, so the printed cross term is
`-(upperRight h e_0)_0 - (h e_0) . (lowerLeft e_0)`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.SigmaBarComparison

open MeasureTheory Homogenization Homogenization.Book.Ch02
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The test vector `P = (e_0, 0)`. -/
def sbNear_e0 : BlockVec d := (Pi.single (0 : Fin d) (1 : ℝ), 0)

/-- The quadratic form of a block matrix at `(e_0, 0)` is its `(0,0)` upper-left entry. -/
theorem sbNear_blockVecDot_e0 (A : BlockMat d) :
    blockVecDot (sbNear_e0 (d := d)) (blockMatVecMul A (sbNear_e0 (d := d))) =
      A.upperLeft 0 0 := by
  simp [sbNear_e0, blockVecDot, blockMatVecMul, vecDot, matVecMul, Pi.single_apply]

/-- The quadratic form of a block matrix at `G_{-h}(e_0, 0) = (e_0, -h e_0)`. -/
theorem sbNear_blockVecDot_gauge_e0 (A : BlockMat d) (h : Mat d) :
    blockVecDot (blockMatVecMul (blockG (-h)) (sbNear_e0 (d := d)))
        (blockMatVecMul A (blockMatVecMul (blockG (-h)) (sbNear_e0 (d := d)))) =
      A.upperLeft 0 0 - (∑ l : Fin d, A.upperRight 0 l * h l 0) -
        (∑ k : Fin d, h k 0 * A.lowerLeft k 0) +
        ∑ k : Fin d, ∑ l : Fin d, h k 0 * A.lowerRight k l * h l 0 := by
  simp [sbNear_e0, blockVecDot, blockMatVecMul, vecDot, matVecMul, Pi.single_apply, blockG,
    Matrix.one_apply, Finset.sum_neg_distrib]
  simp only [mul_add, mul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.mul_sum,
    mul_assoc]
  ring

/-- The printed cross term `kcg^t s^{-1} h + h^t s^{-1} kcg` at the `(0,0)` entry,
read off the raw blocks of `bfA_ell(cu_n)`. -/
def sbNear_crossRaw (nu : ℝ) (ell L n : ℕ) (omega : ShellSeq d) : ℝ :=
  -(∑ l : Fin d, (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
      (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega ell).toFun).upperRight 0 l *
      sbIndep_hMat (d := d) ell L n omega l 0) -
    ∑ k : Fin d, sbIndep_hMat (d := d) ell L n omega k 0 *
      sbIndep_kcgMat (d := d) nu ell n omega k 0

/-- The raw `(0,0)` upper-left entry of `bfA_m(cu_n)`. -/
def sbNear_ul (nu : ℝ) (m n : ℕ) (omega : ShellSeq d) : ℝ :=
  (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
    (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega m).toFun).upperLeft 0 0

/-- **The pointwise near-additivity identity**: the upper-left block of
`e.localization.ml` at `P = (e_0, 0)`. -/
theorem sbNear_pointwise_identity (nu : ℝ) (ell L n : ℕ) (omega : ShellSeq d) :
    sbNear_ul nu L n omega - sbNear_ul nu ell n omega -
        sbIndep_quadTerm (d := d) nu ell L n omega - sbNear_crossRaw nu ell L n omega =
      SuperdiffusionCLT.Section2.Localization.localizationT1CubeError nu ell L
        (originCube d (n : ℤ)) (sbNear_e0 (d := d)) omega := by
  rw [SuperdiffusionCLT.Section2.Localization.localizationT1CubeError,
    blockVecDot_blockMatVecMul_ofFullBlockMat_sub,
    show SuperdiffusionCLT.Section2.Localization.localizationGaugeVector ell L
        (originCube d (n : ℤ)) (sbNear_e0 (d := d)) omega =
      blockMatVecMul (blockG (-(SuperdiffusionCLT.Section2.Localization.localizationGaugeAverage
        ell L (originCube d (n : ℤ)) omega))) (sbNear_e0 (d := d)) from rfl,

    ← SuperdiffusionCLT.Section2.Localization.blockVecDot_blockG_conj_eq,
    sbNear_blockVecDot_e0, sbNear_blockVecDot_gauge_e0,
    ← sbNear_hMat_eq_localizationGaugeAverage]
  have hA : ∀ m : ℕ, SuperdiffusionCLT.Section2.Localization.localizationCoarseAt nu m
      (originCube d (n : ℤ)) omega = coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
        (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega m).toFun :=
    fun _ => rfl
  simp only [hA, sbNear_ul, sbNear_crossRaw, sbIndep_quadTerm, sbIndep_sInvMat, sbIndep_kcgMat]
  ring

end

end SuperdiffusionCLT.Section4.SigmaBarComparison
