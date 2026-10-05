/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.CoarseGraining.QuadraticStability.CauchySchwarz
public import Homogenization.Book.Ch02.Block
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# The Euclidean operator norm of a doubled block matrix

Throughout the paper, the notation `|A|` for a rectangular real matrix is fixed as follows:

> Unless otherwise indicated, the norm we use for `R^{m×n}`, denoted by `|A|`,
> is the square root of the largest eigenvalue of `A^t A`.

that is, the Euclidean operator norm. The manuscript applies it to the doubled
`2d`-by-`2d` matrices `bfA_m(U)` in `e.Enaught.vs.A.and.Ahom`
and again in the Section 3 estimate, where `|bfA_m(U)|` bounds
`|b_m(U)|`. `CoarseGraining` provides the Euclidean operator norm of a `d`-by-`d`
matrix (`Homogenization.Book.Ch02.matrixOperatorNorm`) but none for the doubled
block matrices; this module is the local realization of that norm.

`blockMatrixOperatorNorm A` is `‖·‖` of `toFullBlockMat A` read as an operator
on `EuclideanSpace ℝ (BlockCoord d)`, exactly as
`Book.Ch02.matrixOperatorNorm` is defined for `Mat d`. The `EuclideanSpace`
carrier appears only inside the definition and inside the private bridge
`norm_toLp_toFullBlockVec`, which identifies its norm with the repository's
`vecNormSq`/`Real.sqrt` form `blockVecNorm`; every exported statement is in
terms of `blockVecNorm`, `blockVecDot` and `blockMatVecMul`.

## Main definitions

* `blockVecNorm`: the Euclidean length `√(|p|² + |q|²)` of a doubled vector.
* `blockMatrixOperatorNorm`: `|A|` for `A : BlockMat d`.

## Main results

* `blockMatrixOperatorNorm_nonneg`.
* `blockVecNorm_blockMatVecMul_le`: the defining bound
  `|A X| ≤ |A| · |X|`.
* `blockMatrixOperatorNorm_le_bound`: `|A|` is the least such bound.
* `blockMatrixOperatorNorm_le_of_blockMatLoewnerLE_blockIdentity`: for a
  symmetric positive semidefinite block matrix, `0 ≤ A ≤ c I_{2d}` in the
  Loewner order gives `|A| ≤ c`. This is the form used by the first assertion
  of `l.bfAm.ellip` and by the Section 3 estimate.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Carriers

open Homogenization
open Homogenization.Book.Ch02

noncomputable section

variable {d : ℕ}

/-! ## The Euclidean length of a doubled vector -/

/-- The Euclidean length of a doubled block vector, written with the
repository's `vecNormSq`. -/
def blockVecNorm (X : BlockVec d) : ℝ :=
  Real.sqrt (vecNormSq X.1 + vecNormSq X.2)

theorem blockVecDot_self (X : BlockVec d) :
    blockVecDot X X = vecNormSq X.1 + vecNormSq X.2 :=
  rfl

theorem blockVecDot_self_nonneg (X : BlockVec d) : 0 ≤ blockVecDot X X :=
  add_nonneg (vecNormSq_nonneg X.1) (vecNormSq_nonneg X.2)

theorem blockVecNorm_eq_sqrt_blockVecDot (X : BlockVec d) :
    blockVecNorm X = Real.sqrt (blockVecDot X X) :=
  rfl

theorem blockVecNorm_nonneg (X : BlockVec d) : 0 ≤ blockVecNorm X :=
  Real.sqrt_nonneg _

theorem blockVecNorm_sq (X : BlockVec d) :
    blockVecNorm X ^ 2 = blockVecDot X X :=
  Real.sq_sqrt (blockVecDot_self_nonneg X)

/-! ## The operator norm -/

/-- **The Euclidean operator norm `|A|` of a doubled block matrix**, read on
`EuclideanSpace ℝ (BlockCoord d)` in the same way `Book.Ch02.matrixOperatorNorm`
is read on `EuclideanSpace ℝ (Fin d)`. -/
def blockMatrixOperatorNorm (A : BlockMat d) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) (toFullBlockMat A)‖

theorem blockMatrixOperatorNorm_nonneg (A : BlockMat d) :
    0 ≤ blockMatrixOperatorNorm A :=
  norm_nonneg _

/-- The bridge between the `EuclideanSpace` norm used in the definition and the
repository's `vecNormSq`/`Real.sqrt` form. -/
private theorem norm_toLp_toFullBlockVec (X : BlockVec d) :
    ‖(WithLp.toLp 2 (toFullBlockVec X) :
        EuclideanSpace ℝ (BlockCoord d))‖ = blockVecNorm X := by
  rw [PiLp.norm_eq_of_L2, blockVecNorm]
  congr 1
  rw [Fintype.sum_sum_type]
  congr 1
  · simp only [toFullBlockVec, Real.norm_eq_abs, sq_abs]
    simp only [vecNormSq, vecDot, pow_two]
  · simp only [toFullBlockVec, Real.norm_eq_abs, sq_abs]
    simp only [vecNormSq, vecDot, pow_two]

/-- **The defining bound `|A X| ≤ |A| · |X|`.** -/
theorem blockVecNorm_blockMatVecMul_le (A : BlockMat d) (X : BlockVec d) :
    blockVecNorm (blockMatVecMul A X) ≤ blockMatrixOperatorNorm A *
      blockVecNorm X := by
  have h :=
    (Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) (toFullBlockMat A)).le_opNorm
      (WithLp.toLp 2 (toFullBlockVec X) : EuclideanSpace ℝ (BlockCoord d))
  rw [Matrix.toEuclideanCLM_toLp, ← toFullBlockVec_blockMatVecMul,
    norm_toLp_toFullBlockVec, norm_toLp_toFullBlockVec] at h
  exact h

/-- **`|A|` is the least constant in the defining bound.** -/
theorem blockMatrixOperatorNorm_le_bound {A : BlockMat d} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ X : BlockVec d,
      blockVecNorm (blockMatVecMul A X) ≤ C * blockVecNorm X) :
    blockMatrixOperatorNorm A ≤ C := by
  refine ContinuousLinearMap.opNorm_le_bound _ hC ?_
  have key : ∀ X : BlockVec d,
      ‖(Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) (toFullBlockMat A))
          (WithLp.toLp 2 (toFullBlockVec X) :
            EuclideanSpace ℝ (BlockCoord d))‖ ≤
        C * ‖(WithLp.toLp 2 (toFullBlockVec X) :
          EuclideanSpace ℝ (BlockCoord d))‖ := by
    intro X
    rw [Matrix.toEuclideanCLM_toLp, ← toFullBlockVec_blockMatVecMul,
      norm_toLp_toFullBlockVec, norm_toLp_toFullBlockVec]
    exact h X
  intro x
  have hx : (WithLp.toLp 2 (toFullBlockVec (ofFullBlockVec x.ofLp)) :
      EuclideanSpace ℝ (BlockCoord d)) = x := by
    rw [toFullBlockVec_ofFullBlockVec]
  simpa only [hx] using key (ofFullBlockVec x.ofLp)

/-! ## The value on the doubled identity -/

/-! ## The Loewner comparison -/

/-- The doubled identity acts as the identity on doubled vectors. -/
theorem blockMatVecMul_blockIdentity (X : BlockVec d) :
    blockMatVecMul (blockIdentity d) X = X := by
  ext <;>
    simp [blockMatVecMul, blockIdentity, blockDiag, matVecMul, Matrix.one_apply]

/-- **`0 ≤ A ≤ c I_{2d}` in the Loewner order forces `|A| ≤ c`**, for a
symmetric positive semidefinite doubled block matrix. This is the passage from
the Loewner form of the ellipticity bounds to the printed norm form of
`e.Enaught.vs.A.and.Ahom`. The proof is the Cauchy-Schwarz
inequality for the positive semidefinite form `X ↦ X · A X`, applied to `X` and
`A X`; no matrix square root is used. -/
theorem blockMatrixOperatorNorm_le_of_blockMatLoewnerLE_blockIdentity
    {A : BlockMat d} {c : ℝ} (hc : 0 ≤ c) (hsymm : IsSymmetricBlockMat A)
    (hpsd : ∀ Z : BlockVec d, 0 ≤ blockVecDot Z (blockMatVecMul A Z))
    (hle : BlockMatLoewnerLE A (c • blockIdentity d)) :
    blockMatrixOperatorNorm A ≤ c := by
  have hquad : ∀ X : BlockVec d,
      blockVecDot X (blockMatVecMul A X) ≤ c * blockVecNorm X ^ 2 := by
    intro X
    have h := blockVecDot_le_smul_of_blockMatLoewnerLE hle X
    rwa [blockMatVecMul_blockIdentity, ← blockVecNorm_sq] at h
  have hsqrt : ∀ X : BlockVec d,
      Real.sqrt (blockVecDot X (blockMatVecMul A X)) ≤
        Real.sqrt c * blockVecNorm X := by
    intro X
    calc
      Real.sqrt (blockVecDot X (blockMatVecMul A X)) ≤
          Real.sqrt (c * blockVecNorm X ^ 2) := Real.sqrt_le_sqrt (hquad X)
      _ = Real.sqrt c * blockVecNorm X := by
          rw [Real.sqrt_mul hc, Real.sqrt_sq (blockVecNorm_nonneg X)]
  refine blockMatrixOperatorNorm_le_bound hc ?_
  intro X
  set Y : BlockVec d := blockMatVecMul A X with hY
  have hYY : blockVecDot Y Y = blockVecDot X (blockMatVecMul A Y) := by
    rw [blockVecDot_blockMatVecMul_comm_of_isSymmetricBlockMat hsymm X Y, hY]
  have hCS : |blockVecDot X (blockMatVecMul A Y)| ≤
      Real.sqrt (blockVecDot X (blockMatVecMul A X)) *
        Real.sqrt (blockVecDot Y (blockMatVecMul A Y)) :=
    abs_blockVecDot_blockMatVecMul_le_of_isSymmetricBlockMat hsymm hpsd X Y
  have hprod : Real.sqrt (blockVecDot X (blockMatVecMul A X)) *
      Real.sqrt (blockVecDot Y (blockMatVecMul A Y)) ≤
        c * blockVecNorm X * blockVecNorm Y := by
    have hx := hsqrt X
    have hy := hsqrt Y
    have hmul := mul_le_mul hx hy (Real.sqrt_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg c) (blockVecNorm_nonneg X))
    have hcc : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc
    calc
      Real.sqrt (blockVecDot X (blockMatVecMul A X)) *
          Real.sqrt (blockVecDot Y (blockMatVecMul A Y)) ≤
            (Real.sqrt c * blockVecNorm X) * (Real.sqrt c * blockVecNorm Y) :=
        hmul
      _ = (Real.sqrt c * Real.sqrt c) * (blockVecNorm X * blockVecNorm Y) := by
          ring
      _ = c * blockVecNorm X * blockVecNorm Y := by rw [hcc, mul_assoc]
  have hkey : blockVecNorm Y ^ 2 ≤ c * blockVecNorm X * blockVecNorm Y := by
    calc
      blockVecNorm Y ^ 2 = blockVecDot Y Y := blockVecNorm_sq Y
      _ = blockVecDot X (blockMatVecMul A Y) := hYY
      _ ≤ |blockVecDot X (blockMatVecMul A Y)| := le_abs_self _
      _ ≤ c * blockVecNorm X * blockVecNorm Y := hCS.trans hprod
  rcases eq_or_lt_of_le (blockVecNorm_nonneg Y) with hzero | hpos
  · rw [← hzero]
    exact mul_nonneg hc (blockVecNorm_nonneg X)
  · refine le_of_mul_le_mul_right ?_ hpos
    calc
      blockVecNorm Y * blockVecNorm Y = blockVecNorm Y ^ 2 := (pow_two _).symm
      _ ≤ c * blockVecNorm X * blockVecNorm Y := hkey

end

end SuperdiffusionCLT.Section2.Carriers
