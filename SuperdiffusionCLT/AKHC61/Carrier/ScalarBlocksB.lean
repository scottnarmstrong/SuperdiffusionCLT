/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.Frozen.Section4.ThetaCutoff
public import Homogenization.Book.Ch02.Block
public import Homogenization.CoarseGraining.SharpBlockBounds.DiagonalSandwich
public import Homogenization.Book.Ch04.Theorems.ScalarizationDefinitions

/-!
# Package A2 continued: the block-diagonal bridge

This file finishes package A2 of the [AK, Theorem 6.1] argument. Unlike
the antitonicity/positivity facts of `ScalarBlocks.lean`, none of the results
here consume the (P2') clause at all: they need only `0 < nu` and, for the
`ShellLawJ4`-dependent scalar reduction, `ShellLawJ4`.

## Main results

* `akhc_annealedBlockMatrix_originCube_eq_blockDiag`: `bfAhom_L(cu_n)` is the
  block-diagonal matrix `diag(sigmaBarScalar, sigmaBarStarInvScalar)`, using
  the `Section2.Annealed.Symmetry` bridges
  (`annealedBlockMatrix_originCube_upperLeft_eq_sigmaBar`,
  `..._upperRight_eq_zero`, `..._lowerLeft_eq_zero`,
  `sigmaBar_originCube_eq_smul_one`, `sigmaBarStarInv_originCube_eq_smul_one`).
* `akhc_blockMatLoewnerLE_blockDiag_smul_one_iff`: the general, hypothesis-free
  bridge `BlockMatLoewnerLE (diag(a•1,b•1)) (diag(a'•1,b'•1)) ↔ a ≤ a' ∧ b ≤ b'`.
* `akhc_blockMatLoewnerLE_annealedBlockMatrix_smul_iff`: the target iff,
  `BlockMatLoewnerLE (bfAhom_L(cu_k')) ((1+δ) • bfAhom_L(cu_k)) ↔
    sigmaBarScalar(cu_k') ≤ (1+δ) sigmaBarScalar(cu_k) ∧
    sigmaBarStarInvScalar(cu_k') ≤ (1+δ) sigmaBarStarInvScalar(cu_k)`.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.Carrier

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-! ## The general block-diagonal Löwner bridge

Fully general: no shell law, no `NeZero d` beyond what `Book.Ch04`'s scalar
lemmas need. -/

/-- **The block-Löwner order between two scalar-diagonal block matrices is the
conjunction of the two scalar orders.** The forward direction is the
unconditional `Homogenization.Book.Ch04.matLoewnerLE_upperLeft/lowerRight_of_blockMatLoewnerLE`;
the reverse direction adds the two scalar comparisons lifted to `MatLoewnerLE`
by `Homogenization.Book.Ch04.matLoewnerLE_smul_one_of_scalar_le`. -/
theorem akhc_blockMatLoewnerLE_blockDiag_smul_one_iff
    [NeZero d] {a a' b b' : ℝ} :
    BlockMatLoewnerLE (Book.Ch02.blockDiag (a • (1 : Mat d)) (b • (1 : Mat d)))
        (Book.Ch02.blockDiag (a' • (1 : Mat d)) (b' • (1 : Mat d))) ↔
      a ≤ a' ∧ b ≤ b' := by
  constructor
  · intro h
    have hUL := Book.Ch04.matLoewnerLE_upperLeft_of_blockMatLoewnerLE h
    have hLR := Book.Ch04.matLoewnerLE_lowerRight_of_blockMatLoewnerLE h
    exact ⟨Book.Ch04.scalar_le_of_matLoewnerLE_smul_one (d := d) hUL,
      Book.Ch04.scalar_le_of_matLoewnerLE_smul_one (d := d) hLR⟩
  · rintro ⟨ha, hb⟩
    intro X
    obtain ⟨p, q⟩ := X
    have hUL := Book.Ch04.matLoewnerLE_smul_one_of_scalar_le (d := d) ha p
    have hLR := Book.Ch04.matLoewnerLE_smul_one_of_scalar_le (d := d) hb q
    show (1 / 2 : ℝ) * blockVecDot (p, q)
        (blockMatVecMul (Book.Ch02.blockDiag (a • (1 : Mat d)) (b • (1 : Mat d))) (p, q)) ≤
      (1 / 2 : ℝ) * blockVecDot (p, q)
        (blockMatVecMul (Book.Ch02.blockDiag (a' • (1 : Mat d)) (b' • (1 : Mat d))) (p, q))
    have hzeroL : matVecMul (0 : Mat d) q = 0 := by
      funext i
      simp [matVecMul]
    have hzeroR : matVecMul (0 : Mat d) p = 0 := by
      funext i
      simp [matVecMul]
    simp only [blockVecDot, blockMatVecMul, Book.Ch02.blockDiag, hzeroL, hzeroR, add_zero,
      zero_add]
    linarith only [hUL, hLR]

/-! ## The block-diagonal decomposition of `bfAhom_L(cu_n)`

`ShellLawJ4` alone: the negation half gives `khom_L(cu_n) = 0`, so the
upper-right and lower-left blocks vanish, and the hyperoctahedral half makes
each diagonal block a scalar matrix. -/

variable {nu : ℝ} (hnu : 0 < nu) (L : ℕ) {P : ProbabilityMeasure (ShellSeq d)}
  (hJ4 : ShellLawJ4 d P)

include hnu hJ4

/-- **`bfAhom_L(cu_n)` is the block-diagonal matrix
`diag(sigmaBarScalar(cu_n) • 1, sigmaBarStarInvScalar(cu_n) • 1)`.** Uses only
the `ShellLawJ4` bridges of `Section2.Annealed.Symmetry`, no (P2'). -/
theorem akhc_annealedBlockMatrix_originCube_eq_blockDiag [NeZero d] (n : ℤ) :
    annealedBlockMatrix nu L P (cubeSet (originCube d n)) =
      Book.Ch02.blockDiag
        (sigmaBarScalar nu L P (cubeSet (originCube d n)) • (1 : Mat d))
        (sigmaBarStarInvScalar nu L P (cubeSet (originCube d n)) • (1 : Mat d)) := by
  have hUL := annealedBlockMatrix_originCube_upperLeft_eq_sigmaBar hnu L hJ4 n
  have hUR := annealedBlockMatrix_originCube_upperRight_eq_zero hnu L hJ4 n
  have hLL := annealedBlockMatrix_originCube_lowerLeft_eq_zero hnu L hJ4 n
  have hLR : (annealedBlockMatrix nu L P (cubeSet (originCube d n))).lowerRight =
      sigmaBarStarInv nu L P (cubeSet (originCube d n)) := rfl
  rw [sigmaBar_originCube_eq_smul_one hnu L hJ4 n] at hUL
  rw [sigmaBarStarInv_originCube_eq_smul_one hnu L hJ4 n] at hLR
  cases hA : annealedBlockMatrix nu L P (cubeSet (originCube d n)) with
  | mk a b c e =>
      rw [hA] at hUL hUR hLL hLR
      simp only [Book.Ch02.blockDiag]
      simp_all

/-- **The target iff (§5, package A2, bullet 4).** `BlockMatLoewnerLE
(bfAhom_L(cu_k')) ((1+δ) • bfAhom_L(cu_k)) ↔ sigmaBarScalar(cu_k') ≤ (1+δ) *
sigmaBarScalar(cu_k) ∧ sigmaBarStarInvScalar(cu_k') ≤ (1+δ) *
sigmaBarStarInvScalar(cu_k)`. No (P2') is used, only `hnu` and `ShellLawJ4`. -/
theorem akhc_blockMatLoewnerLE_annealedBlockMatrix_smul_iff [NeZero d]
    (kprime k : ℤ) (delta : ℝ) :
    BlockMatLoewnerLE (annealedBlockMatrix nu L P (cubeSet (originCube d kprime)))
        (delta • annealedBlockMatrix nu L P (cubeSet (originCube d k))) ↔
      sigmaBarScalar nu L P (cubeSet (originCube d kprime)) ≤
          delta * sigmaBarScalar nu L P (cubeSet (originCube d k)) ∧
        sigmaBarStarInvScalar nu L P (cubeSet (originCube d kprime)) ≤
          delta * sigmaBarStarInvScalar nu L P (cubeSet (originCube d k)) := by
  rw [akhc_annealedBlockMatrix_originCube_eq_blockDiag hnu L hJ4 kprime,
    akhc_annealedBlockMatrix_originCube_eq_blockDiag hnu L hJ4 k,
    blockSMul_blockDiag_smul_one]
  exact akhc_blockMatLoewnerLE_blockDiag_smul_one_iff

end

end SuperdiffusionCLT.AKHC61.Carrier
