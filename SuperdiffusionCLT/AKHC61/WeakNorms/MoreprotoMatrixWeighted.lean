/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Carriers.BlockOperatorNorm
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Homogenization.Book.Ch05.Theorems.Section53.WeakNormsMaximizer.AssemblyFinal

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.WeakNorms

noncomputable section

/-! ## Small real-analysis helpers -/

/-- Subadditivity of `Real.sqrt` on nonnegative reals. -/
theorem akhcWeak_sqrt_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have hsum : 0 ≤ Real.sqrt x + Real.sqrt y := add_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)
  have hxy : x + y ≤ (Real.sqrt x + Real.sqrt y) ^ 2 := by
    have hx2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
    have hy2 : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy
    have hcross : 0 ≤ 2 * Real.sqrt x * Real.sqrt y :=
      mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg x)) (Real.sqrt_nonneg y)
    nlinarith only [hx2, hy2, hcross]
  calc
    Real.sqrt (x + y) ≤ Real.sqrt ((Real.sqrt x + Real.sqrt y) ^ 2) := Real.sqrt_le_sqrt hxy
    _ = Real.sqrt x + Real.sqrt y := Real.sqrt_sq hsum

/-! ## Cauchy-Schwarz and the operator-norm quadratic-form bound -/

/-- Cauchy-Schwarz for `Homogenization.blockVecDot`, via the `Matrix.dotProduct` bridge. -/
theorem akhcWeak_sq_blockVecDot_le {d : ℕ} (X Y : Homogenization.BlockVec d) :
    Homogenization.blockVecDot X Y ^ 2 ≤
      Homogenization.blockVecDot X X * Homogenization.blockVecDot Y Y := by
  classical
  have hcs :
      (∑ i : Homogenization.BlockCoord d,
          Homogenization.toFullBlockVec X i * Homogenization.toFullBlockVec Y i) ^ 2 ≤
        (∑ i : Homogenization.BlockCoord d, Homogenization.toFullBlockVec X i ^ 2) *
          ∑ i : Homogenization.BlockCoord d, Homogenization.toFullBlockVec Y i ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (Homogenization.toFullBlockVec X) (Homogenization.toFullBlockVec Y)
  have hXY :
      (∑ i : Homogenization.BlockCoord d,
          Homogenization.toFullBlockVec X i * Homogenization.toFullBlockVec Y i) =
        Homogenization.blockVecDot X Y := by
    have h := Homogenization.dotProduct_toFullBlockVec X Y
    simpa [dotProduct] using h
  have hXX :
      (∑ i : Homogenization.BlockCoord d, Homogenization.toFullBlockVec X i ^ 2) =
        Homogenization.blockVecDot X X := by
    have h := Homogenization.dotProduct_toFullBlockVec X X
    simpa [dotProduct, sq] using h
  have hYY :
      (∑ i : Homogenization.BlockCoord d, Homogenization.toFullBlockVec Y i ^ 2) =
        Homogenization.blockVecDot Y Y := by
    have h := Homogenization.dotProduct_toFullBlockVec Y Y
    simpa [dotProduct, sq] using h
  rwa [hXY, hXX, hYY] at hcs

/-- **The sqrt-free operator-norm quadratic-form bound**: for any doubled block matrix `M`
(no symmetry or positivity needed), `X · M X ≤ |M| · (X · X)`. This is the reading of the
`M^{1/2}(\cdots)` weighting inside a Besov seminorm without constructing a matrix square root,
in the style of `blockMatrixOperatorNorm_le_of_blockMatLoewnerLE_blockIdentity`. -/
theorem akhcWeak_blockVecDot_blockMatVecMul_le_operatorNorm_mul {d : ℕ}
    (M : Homogenization.BlockMat d) (X : Homogenization.BlockVec d) :
    Homogenization.blockVecDot X (Homogenization.blockMatVecMul M X) ≤
      SuperdiffusionCLT.Section2.Carriers.blockMatrixOperatorNorm M *
        Homogenization.blockVecDot X X := by
  set Y : Homogenization.BlockVec d := Homogenization.blockMatVecMul M X with hYdef
  have hcs := akhcWeak_sq_blockVecDot_le X Y
  have hXXnn : 0 ≤ Homogenization.blockVecDot X X :=
    SuperdiffusionCLT.Section2.Carriers.blockVecDot_self_nonneg X
  have hXnorm : Homogenization.blockVecDot X X =
      SuperdiffusionCLT.Section2.Carriers.blockVecNorm X ^ 2 :=
    (SuperdiffusionCLT.Section2.Carriers.blockVecNorm_sq X).symm
  have hYnorm : Homogenization.blockVecDot Y Y =
      SuperdiffusionCLT.Section2.Carriers.blockVecNorm Y ^ 2 :=
    (SuperdiffusionCLT.Section2.Carriers.blockVecNorm_sq Y).symm
  have hYbound :
      SuperdiffusionCLT.Section2.Carriers.blockVecNorm Y ≤
        SuperdiffusionCLT.Section2.Carriers.blockMatrixOperatorNorm M *
          SuperdiffusionCLT.Section2.Carriers.blockVecNorm X :=
    SuperdiffusionCLT.Section2.Carriers.blockVecNorm_blockMatVecMul_le M X
  have hnormMnn : 0 ≤ SuperdiffusionCLT.Section2.Carriers.blockMatrixOperatorNorm M :=
    SuperdiffusionCLT.Section2.Carriers.blockMatrixOperatorNorm_nonneg M
  have hXnn : 0 ≤ SuperdiffusionCLT.Section2.Carriers.blockVecNorm X :=
    SuperdiffusionCLT.Section2.Carriers.blockVecNorm_nonneg X
  have hbound2 :
      Homogenization.blockVecDot X X * Homogenization.blockVecDot Y Y ≤
        (SuperdiffusionCLT.Section2.Carriers.blockMatrixOperatorNorm M *
            Homogenization.blockVecDot X X) ^ 2 := by
    rw [hXnorm, hYnorm]
    have hsq :
        SuperdiffusionCLT.Section2.Carriers.blockVecNorm Y ^ 2 ≤
          (SuperdiffusionCLT.Section2.Carriers.blockMatrixOperatorNorm M *
              SuperdiffusionCLT.Section2.Carriers.blockVecNorm X) ^ 2 :=
      pow_le_pow_left₀ (SuperdiffusionCLT.Section2.Carriers.blockVecNorm_nonneg Y) hYbound 2
    calc
      SuperdiffusionCLT.Section2.Carriers.blockVecNorm X ^ 2 *
          SuperdiffusionCLT.Section2.Carriers.blockVecNorm Y ^ 2 ≤
          SuperdiffusionCLT.Section2.Carriers.blockVecNorm X ^ 2 *
            (SuperdiffusionCLT.Section2.Carriers.blockMatrixOperatorNorm M *
                SuperdiffusionCLT.Section2.Carriers.blockVecNorm X) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
      _ = (SuperdiffusionCLT.Section2.Carriers.blockMatrixOperatorNorm M *
              (SuperdiffusionCLT.Section2.Carriers.blockVecNorm X ^ 2)) ^ 2 := by
        ring
  have hle :
      Homogenization.blockVecDot X Y ^ 2 ≤
        (SuperdiffusionCLT.Section2.Carriers.blockMatrixOperatorNorm M *
            Homogenization.blockVecDot X X) ^ 2 :=
    hcs.trans hbound2
  have hrhsnn : 0 ≤ SuperdiffusionCLT.Section2.Carriers.blockMatrixOperatorNorm M *
      Homogenization.blockVecDot X X := mul_nonneg hnormMnn hXXnn
  have hfin : Homogenization.blockVecDot X Y ≤
      SuperdiffusionCLT.Section2.Carriers.blockMatrixOperatorNorm M *
        Homogenization.blockVecDot X X :=
    (abs_le_of_sq_le_sq' hle hrhsnn).2
  calc
    Homogenization.blockVecDot X (Homogenization.blockMatVecMul M X) =
        Homogenization.blockVecDot X Y := by rw [hYdef]
    _ ≤ SuperdiffusionCLT.Section2.Carriers.blockMatrixOperatorNorm M *
          Homogenization.blockVecDot X X := hfin

/-! ## The joint (gradient, flux) response and its `M`-weighted weak norm -/

end

end SuperdiffusionCLT.AKHC61.WeakNorms
