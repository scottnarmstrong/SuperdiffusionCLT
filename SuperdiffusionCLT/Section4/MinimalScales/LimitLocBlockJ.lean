/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.LimitLocDescendant
public import SuperdiffusionCLT.Section2.CoarseGraining.Correspondence

/-!
# `BlockJ` as a sum of two quadratic forms of the coarse block matrix

For an everywhere elliptic field on `cubeSet R`, the block response
`BlockJ (cubeSet R) (p, q) (qStar, pStar) a` equals
`(1/4) Q(X₁) + (1/4) Q(X₂) - (p·qStar + pStar·q)` where `Q` is the quadratic form of
`coarseBlockMatrix (openCubeSet R) a`, `X₁ = (-(p - pStar), qStar - q)` and
`X₂ = (pStar + p, qStar + q)`. Only the two quadratic forms depend on `a`.
Together with the quadratic-form sandwich of `LimitLocDescendant.lean` this controls
`BlockJ` at every fixed pair of block vectors.

## Main results

* `srootL4_blockJ_eq_quadratic`: the identity above.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

open Homogenization MeasureTheory Filter
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Assumptions

noncomputable section

/-- **`BlockJ` as two quadratic forms of the coarse block matrix.** -/
theorem srootL4_blockJ_eq_quadratic {d : ℕ} [NeZero d] (R : TriadicCube d) {nu Lam : ℝ}
    (hnu : 0 < nu) (a : Homogenization.CoeffField d)
    (hEll : Homogenization.IsEllipticFieldOn nu Lam (Homogenization.cubeSet R) a)
    (p pStar q qStar : Vec d) :
    Homogenization.BlockJ (Homogenization.cubeSet R) (p, q) (qStar, pStar) a =
      (1 / 4 : ℝ) * blockVecDot (-(p - pStar), qStar - q)
          (blockMatVecMul (Homogenization.coarseBlockMatrix (Homogenization.openCubeSet R) a)
            (-(p - pStar), qStar - q)) +
        (1 / 4 : ℝ) * blockVecDot (pStar + p, qStar + q)
          (blockMatVecMul (Homogenization.coarseBlockMatrix (Homogenization.openCubeSet R) a)
            (pStar + p, qStar + q)) -
        (vecDot p qStar + vecDot pStar q) := by
  let aC : Homogenization.Book.Ch02.CoeffOn (Homogenization.Book.Ch02.cubeDomain R) :=
    srootL4_coeffOnCube R hnu (srootL4_nu_le_Lam_cube R hEll) a hEll
  have haC : aC.toCoeffField = a := rfl
  have hEllOpen : Homogenization.IsEllipticFieldOn aC.lam aC.Lam
      (Homogenization.openCubeSet R) aC.toCoeffField :=
    hEll.mono (measurableSet_openCubeSet R) (openCubeSet_subset_cubeSet R)
  have h0 := Homogenization.Book.Ch02.BlockJ_cubeSet_eq_half_ResponseJ_adjoint_sum_of_isEllipticFieldOn
    R aC hEllOpen p pStar q qStar
  rw [haC] at h0
  rw [h0, Homogenization.ResponseJ_cubeSet_eq_openCubeSet_of_triadicCube_reproved,
    Homogenization.ResponseJ_cubeSet_eq_openCubeSet_of_triadicCube_reproved]
  have h1 := SuperdiffusionCLT.Section2.CoarseGraining.responseJ_eq_blockQuadratic
    (Homogenization.Book.Ch02.cubeDomain R) aC (p - pStar) (qStar - q)
  have h2 := SuperdiffusionCLT.Section2.CoarseGraining.adjointResponseJ_eq_blockQuadratic
    (Homogenization.Book.Ch02.cubeDomain R) aC (pStar + p) (qStar + q)
  have hconv := SuperdiffusionCLT.Section2.Localization.coarseBlockMatrix_toCoeffField
    (Homogenization.Book.Ch02.cubeDomain R) aC
  rw [haC] at hconv
  simp only [Homogenization.Book.Ch02.cubeDomain_coe] at h1 h2 hconv
  rw [haC] at h1 h2
  rw [hconv] at *
  have hadj : Homogenization.adjointCoeffField a = fun x => matTranspose (a x) := rfl
  rw [hadj, h1, h2]
  have hdot : vecDot (p - pStar) (qStar - q) + vecDot (pStar + p) (qStar + q) =
      2 * (vecDot p qStar + vecDot pStar q) := by
    simp only [sub_eq_add_neg, vecDot_add_left, vecDot_add_right, vecDot_neg_left,
      vecDot_neg_right, vecDot_comm pStar qStar]
    ring
  linarith only [hdot]

end

end SuperdiffusionCLT.Section4.MinimalScales
