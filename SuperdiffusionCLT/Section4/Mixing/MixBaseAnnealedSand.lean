/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.Mixing.AnnealedFinal
public import SuperdiffusionCLT.Section4.Mixing.InvertB

/-!
# Packaging `mixFin_annealedComparison` as `InvertB.lean`'s `hsand`

`Section4/Mixing/InvertB.lean`'s `mixMain_invertB_scalar_bounds` needs a
sandwich-form hypothesis `hsand` on the *block-matrix-valued* difference
`H := bfAhom_L(cu_n) - bfAhom_ell(cu_n)` against `A := bfAhom_ell(cu_n)`, but
`BlockMat d` carries no `Sub` instance (see `Term2ScaleComparison.lean`'s
docstring), so `H` cannot literally be written as a matrix subtraction.
`Section4/Mixing/AnnealedFinal.lean`'s `mixFin_annealedComparison` already
supplies the deterministic sandwich bound in *difference-of-bilinear-forms*
form (never naming `H` as a matrix), which is exactly what is needed: this
file bridges the two by constructing `H` directly from its four block
components (all scalar matrices, via `e.homs.defs.U`,
`Section2/Annealed/Symmetry.lean`) and showing its bilinear form agrees with
the difference `mixFin_annealedComparison` bounds.

`mixBase_invertB_of_annealedComparison` is the resulting composite: any
`mixFin_annealedComparison`-shaped hypothesis (the difference-of-bilinear-form
sandwich, at some rate `t < 1`) yields the four scalar annealed-comparison
bounds `sL ≤ (1+t) sell`, `sell ≤ sL/(1-t)`, and their lower-block analogues,
ready for `ConvertNormalization.lean`'s
`mixMain_quadraticForm_dom_of_scalar_bounds`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

open Homogenization
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff (ShellSeq)
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-- **General (cross-term) bilinear bridge for `annealedBlockMatrix`.** The
`p = q` special case is `Section4/Mixing/AnnealedComparison.lean`'s
`mixMain_annealedBilinear_eq`; this is the same bridge for a general pair
`p, q`, needed to unfold `mixFin_annealedComparison`'s conclusion (which is
stated at `p ≠ q` in general) into the two annealed scalars. -/
theorem mixBase_annealedBilinear_cross_eq [NeZero d] {nu : ℝ} (hnu : 0 < nu) (m : ℕ)
    {P : MeasureTheory.ProbabilityMeasure (ShellSeq d)}
    (hJ4 : ShellLawJ4 d P) (n : ℤ) (p q : BlockVec d) :
    blockVecDot p
        (blockMatVecMul (annealedBlockMatrix nu m P (cubeSet (originCube d n))) q) =
      sigmaBarScalar nu m P (cubeSet (originCube d n)) * vecDot p.1 q.1 +
        sigmaBarStarInvScalar nu m P (cubeSet (originCube d n)) * vecDot p.2 q.2 :=
  mixMain_blockDiagScalar_bilinear_cross_eq
    (annealedBlockMatrix_originCube_upperRight_eq_zero hnu m hJ4 n)
    (annealedBlockMatrix_originCube_lowerLeft_eq_zero hnu m hJ4 n)
    (annealedBlockMatrix_originCube_upperLeft_eq_sigmaBar hnu m hJ4 n |>.trans
      (sigmaBar_originCube_eq_smul_one hnu m hJ4 n))
    (sigmaBarStarInv_originCube_eq_smul_one hnu m hJ4 n) p q

/-- **`mixFin_annealedComparison`'s conclusion, repackaged as `InvertB.lean`'s
`hsand`, applied.** Given the deterministic sandwich bound on the difference
of the `L`- and `ell`-annealed bilinear forms at rate `t < 1` (exactly
`mixFin_annealedComparison`'s conclusion shape), produces the four annealed
scalar comparison bounds: both directions of `#annealed-comparison`
(`sL ≤ (1+t) sell`, `uL ≤ (1+t) uell`) and both directions of `#invert-B`
(`sell ≤ sL/(1-t)`, `uell ≤ uL/(1-t)`). -/
theorem mixBase_invertB_of_annealedComparison [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : MeasureTheory.ProbabilityMeasure (ShellSeq d)} (hJ4 : ShellLawJ4 d P)
    (ell L : ℕ) (n : ℤ) {t : ℝ} (ht1 : t < 1)
    (hcomp : ∀ p q : BlockVec d,
      2 * (blockVecDot p
              (blockMatVecMul (annealedBlockMatrix nu L P (cubeSet (originCube d n))) q) -
            blockVecDot p
              (blockMatVecMul (annealedBlockMatrix nu ell P (cubeSet (originCube d n))) q)) ≤
        t * (blockVecDot p
                (blockMatVecMul (annealedBlockMatrix nu ell P (cubeSet (originCube d n))) p) +
              blockVecDot q
                (blockMatVecMul (annealedBlockMatrix nu ell P (cubeSet (originCube d n))) q))) :
    sigmaBarScalar nu L P (cubeSet (originCube d n)) ≤
        (1 + t) * sigmaBarScalar nu ell P (cubeSet (originCube d n)) ∧
      sigmaBarScalar nu ell P (cubeSet (originCube d n)) ≤
        sigmaBarScalar nu L P (cubeSet (originCube d n)) / (1 - t) ∧
      sigmaBarStarInvScalar nu L P (cubeSet (originCube d n)) ≤
        (1 + t) * sigmaBarStarInvScalar nu ell P (cubeSet (originCube d n)) ∧
      sigmaBarStarInvScalar nu ell P (cubeSet (originCube d n)) ≤
        sigmaBarStarInvScalar nu L P (cubeSet (originCube d n)) / (1 - t) := by
  have hAul : (annealedBlockMatrix nu ell P (cubeSet (originCube d n))).upperLeft =
      sigmaBarScalar nu ell P (cubeSet (originCube d n)) • (1 : Mat d) :=
    (annealedBlockMatrix_originCube_upperLeft_eq_sigmaBar hnu ell hJ4 n).trans
      (sigmaBar_originCube_eq_smul_one hnu ell hJ4 n)
  have hAur : (annealedBlockMatrix nu ell P (cubeSet (originCube d n))).upperRight = 0 :=
    annealedBlockMatrix_originCube_upperRight_eq_zero hnu ell hJ4 n
  have hAll : (annealedBlockMatrix nu ell P (cubeSet (originCube d n))).lowerLeft = 0 :=
    annealedBlockMatrix_originCube_lowerLeft_eq_zero hnu ell hJ4 n
  have hAlr : (annealedBlockMatrix nu ell P (cubeSet (originCube d n))).lowerRight =
      sigmaBarStarInvScalar nu ell P (cubeSet (originCube d n)) • (1 : Mat d) :=
    sigmaBarStarInv_originCube_eq_smul_one hnu ell hJ4 n
  have hsand : ∀ p q : BlockVec d,
      2 * blockVecDot p
            (blockMatVecMul
              ({ upperLeft :=
                    (sigmaBarScalar nu L P (cubeSet (originCube d n)) -
                        sigmaBarScalar nu ell P (cubeSet (originCube d n))) • (1 : Mat d),
                 upperRight := 0, lowerLeft := 0,
                 lowerRight :=
                    (sigmaBarStarInvScalar nu L P (cubeSet (originCube d n)) -
                        sigmaBarStarInvScalar nu ell P (cubeSet (originCube d n))) •
                      (1 : Mat d) } : BlockMat d) q) ≤
        t * (blockVecDot p
                (blockMatVecMul (annealedBlockMatrix nu ell P (cubeSet (originCube d n))) p) +
              blockVecDot q
                (blockMatVecMul (annealedBlockMatrix nu ell P (cubeSet (originCube d n))) q)) := by
    intro p q
    have hHeq : blockVecDot p
          (blockMatVecMul
            ({ upperLeft :=
                  (sigmaBarScalar nu L P (cubeSet (originCube d n)) -
                      sigmaBarScalar nu ell P (cubeSet (originCube d n))) • (1 : Mat d),
               upperRight := 0, lowerLeft := 0,
               lowerRight :=
                  (sigmaBarStarInvScalar nu L P (cubeSet (originCube d n)) -
                      sigmaBarStarInvScalar nu ell P (cubeSet (originCube d n))) •
                    (1 : Mat d) } : BlockMat d) q) =
        (sigmaBarScalar nu L P (cubeSet (originCube d n)) -
              sigmaBarScalar nu ell P (cubeSet (originCube d n))) * vecDot p.1 q.1 +
          (sigmaBarStarInvScalar nu L P (cubeSet (originCube d n)) -
                sigmaBarStarInvScalar nu ell P (cubeSet (originCube d n))) * vecDot p.2 q.2 :=
      mixMain_blockDiagScalar_bilinear_cross_eq rfl rfl rfl rfl p q
    have hALeq := mixBase_annealedBilinear_cross_eq hnu L hJ4 n p q
    have hAelleq := mixBase_annealedBilinear_cross_eq hnu ell hJ4 n p q
    have hcompPQ := hcomp p q
    rw [hALeq, hAelleq] at hcompPQ
    rw [hHeq]
    linarith only [hcompPQ]
  exact mixMain_invertB_scalar_bounds ht1 _ _ rfl rfl rfl rfl hAul hAur hAll hAlr hsand

end

end SuperdiffusionCLT.Section4.Mixing
