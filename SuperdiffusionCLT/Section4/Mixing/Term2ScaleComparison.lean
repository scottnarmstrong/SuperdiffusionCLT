/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.Mixing.GaugeAlgebra
public import SuperdiffusionCLT.Section2.Annealed.Symmetry
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4

/-!
# `p.mixing.P.three.prime#term2-scale-comparison`

In the proof of Proposition `p.mixing.P.three.prime`, the printed conclusion has two parts:
the explicit block form of the gauge term `G_{-h_z}^t bfAhom_ℓ(cu_n) G_{-h_z}
- bfAhom_ℓ(cu_n)` (using that `bfAhom_ℓ(cu_n)` is block
diagonal with scalar blocks by `e.homs.defs.U` and the hyperoctahedral half
of `J4`), and the balanced comparison `σ̄_{ℓ,*}^{-1}(cu_n) ≤ σ̄_{L,*}^{-1}(cu_n)
+ m^{-6000}` (from the balanced comparison
`e.localization.s.star` of `l.localization`
(`Frozen/Section2/CutoffLocalization.lean`), taking expectations,
integrating the `Γ₁` tail, and using `e.CG.bounds.1`).

This file proves the block-diagonal-scalar structure of `bfAhom_ℓ(cu_n)` from
`ShellLawJ4` (`SuperdiffusionCLT.Section2.Annealed.Symmetry`'s
scalarization lemmas) and the block form identity from that structure and
`GaugeAlgebra.lean`'s conjugation identity. The `Γ₁`-tail integration
producing the numeric comparison is not part of this file; it is treated in
`TermTailEllipticity.lean`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

open Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Frozen.Assumptions

variable {d : ℕ}

/-- The block components of `ofFullBlockMat (toFullBlockMat A - toFullBlockMat B)`
are the entrywise (matrix) differences of the block components of `A` and `B`.
This is the block-decomposition half of the `BlockMat`-has-no-`Sub`-instance
idiom used throughout this development. -/
theorem mixTerms_ofFullBlockMat_sub_blocks (A B : BlockMat d) :
    ofFullBlockMat (toFullBlockMat A - toFullBlockMat B) =
      { upperLeft := A.upperLeft - B.upperLeft
        upperRight := A.upperRight - B.upperRight
        lowerLeft := A.lowerLeft - B.lowerLeft
        lowerRight := A.lowerRight - B.lowerRight } := by
  refine blockMat_ext ?_ ?_ ?_ ?_ <;>
    · ext i j
      simp [ofFullBlockMat, toFullBlockMat, Matrix.sub_apply]

/-- **The block-diagonal-scalar structure of `bfAhom_ℓ(cu_n)`**, `e.homs.defs.U`
together with the hyperoctahedral half of `J4`: under `ShellLawJ4`, the
annealed block matrix on an origin cube is `blockDiag` of two scalar
matrices. Assembled from `SuperdiffusionCLT.Section2.Annealed.Symmetry`'s
four scalarization lemmas. -/
theorem mixTerms_annealedBlockDiag [NeZero d] {nu : ℝ} (hnu : 0 < nu) (ell : ℕ)
    {P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)}
    (hJ4 : ShellLawJ4 d P) (n : ℤ) :
    annealedBlockMatrix nu ell P (Homogenization.cubeSet (Homogenization.originCube d n)) =
      blockDiag (sigmaBarScalar nu ell P (Homogenization.cubeSet (Homogenization.originCube d n)) • (1 : Mat d))
        (sigmaBarStarInvScalar nu ell P (Homogenization.cubeSet (Homogenization.originCube d n)) •
          (1 : Mat d)) := by
  refine blockMat_ext ?_ ?_ ?_ ?_
  · rw [annealedBlockMatrix_originCube_upperLeft_eq_sigmaBar hnu ell hJ4 n,
      sigmaBar_originCube_eq_smul_one hnu ell hJ4 n]
    rfl
  · rw [annealedBlockMatrix_originCube_upperRight_eq_zero hnu ell hJ4 n]
    rfl
  · rw [annealedBlockMatrix_originCube_lowerLeft_eq_zero hnu ell hJ4 n]
    rfl
  · show (annealedBlockMatrix nu ell P (Homogenization.cubeSet (Homogenization.originCube d n))).lowerRight =
        sigmaBarStarInvScalar nu ell P (Homogenization.cubeSet (Homogenization.originCube d n)) • (1 : Mat d)
    rw [show (annealedBlockMatrix nu ell P
            (Homogenization.cubeSet (Homogenization.originCube d n))).lowerRight =
          sigmaBarStarInv nu ell P (Homogenization.cubeSet (Homogenization.originCube d n)) from rfl,
      sigmaBarStarInv_originCube_eq_smul_one hnu ell hJ4 n]

/-- **The explicit block form of the gauge term**: for a block-diagonal-scalar base
matrix `blockDiag (s • 1) (t • 1)`, the gauge term
`G_{-h}^t (blockDiag (s•1)(t•1)) G_{-h} - blockDiag (s•1)(t•1)` is the explicit
off-diagonal-plus-quadratic block matrix. This
combines `mixBelow_gaugeBlockConjugation`
(`SuperdiffusionCLT/Section4/Mixing/GaugeAlgebra.lean`) with
`mixTerms_ofFullBlockMat_sub_blocks`. -/
theorem mixTerms_gaugeTermBlockForm (h : Mat d) (s t : ℝ) :
    ofFullBlockMat
        (toFullBlockMat
            (blockMatMul (blockMatTranspose (blockG (-h)))
              (blockMatMul (blockDiag (s • (1 : Mat d)) (t • (1 : Mat d))) (blockG (-h)))) -
          toFullBlockMat (blockDiag (s • (1 : Mat d)) (t • (1 : Mat d)))) =
      { upperLeft := t • (matTranspose h * h)
        upperRight := -(t • matTranspose h)
        lowerLeft := -(t • h)
        lowerRight := 0 } := by
  rw [mixBelow_gaugeBlockConjugation, mixTerms_ofFullBlockMat_sub_blocks]
  refine blockMat_ext ?_ ?_ ?_ ?_
  · show s • (1 : Mat d) + t • (matTranspose h * h) - s • (1 : Mat d) = t • (matTranspose h * h)
    abel
  · show -(t • matTranspose h) - (0 : Mat d) = -(t • matTranspose h)
    abel
  · show -(t • h) - (0 : Mat d) = -(t • h)
    abel
  · show t • (1 : Mat d) - t • (1 : Mat d) = (0 : Mat d)
    abel

end SuperdiffusionCLT.Section4.Mixing
