/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import SuperdiffusionCLT.AKHC61.WeakNorms.MoreprotoMatrixWeighted

/-!
# The block-matrix square root and the sharp `E`-relative prefactor

Lemma `l.weaknorms.moreproto` of [AK] weights its Besov seminorm by `M^{1/2}` and its
right-hand side by the sharp `E`-relative prefactor `|M^{-1/2} E M^{-1/2}|^{1/2}`, for a
symmetric positive
matrix `E` and a doubled block matrix `M` built from a positive symmetric `m` and an
antisymmetric `h`.

This file builds a genuine positive-semidefinite square root of a doubled `2d`-by-`2d`
block matrix, via the continuous functional calculus square root `CFC.sqrt` already used
in this repository for plain `d`-by-`d` matrices
(`SuperdiffusionCLT/Section2/Localization/PsdSqrtQuadratic.lean`), applied to the full
`2d`-by-`2d` representation `Homogenization.FullBlockMat d = Matrix (BlockCoord d)
(BlockCoord d) ℝ` (the same `Matrix n n ℝ` carrier `CFC.sqrt` already supports, just at a
different index type). It then builds the inverse square root of a positive-definite block
matrix from the ordinary matrix inverse of the square root, and proves the sharp `E`-relative
quadratic-form bound this licenses.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.WeakNorms

open scoped MatrixOrder Matrix

noncomputable section

/-! ## The square root of a `2d`-by-`2d` matrix -/

/-- `M^{1/2}` at the level of the full `2d`-by-`2d` representation, via `CFC.sqrt`. -/
noncomputable def akhcWeak_fullSqrt {d : ℕ} (Mfull : Homogenization.FullBlockMat d) :
    Homogenization.FullBlockMat d :=
  CFC.sqrt Mfull

theorem akhcWeak_fullSqrt_mul_self {d : ℕ} {Mfull : Homogenization.FullBlockMat d}
    (hM : Mfull.PosSemidef) :
    akhcWeak_fullSqrt Mfull * akhcWeak_fullSqrt Mfull = Mfull :=
  CFC.sqrt_mul_sqrt_self Mfull hM.nonneg

theorem akhcWeak_fullSqrt_posSemidef {d : ℕ} (Mfull : Homogenization.FullBlockMat d) :
    (akhcWeak_fullSqrt Mfull).PosSemidef :=
  (Matrix.nonneg_iff_posSemidef (A := akhcWeak_fullSqrt Mfull)).mp (CFC.sqrt_nonneg Mfull)

theorem akhcWeak_fullSqrt_isSymm {d : ℕ} (Mfull : Homogenization.FullBlockMat d) :
    (akhcWeak_fullSqrt Mfull).IsSymm := by
  simpa [Matrix.IsHermitian, Matrix.IsSymm] using
    (akhcWeak_fullSqrt_posSemidef Mfull).isHermitian

/-! ## The inverse square root of a positive-definite `2d`-by-`2d` matrix -/

/-- `M^{-1/2}` at the level of the full `2d`-by-`2d` representation: the ordinary matrix
inverse of `M^{1/2}`. -/
noncomputable def akhcWeak_fullInvSqrt {d : ℕ} (Mfull : Homogenization.FullBlockMat d) :
    Homogenization.FullBlockMat d :=
  (akhcWeak_fullSqrt Mfull)⁻¹

theorem akhcWeak_isUnit_det_fullSqrt {d : ℕ} {Mfull : Homogenization.FullBlockMat d}
    (hM : Mfull.PosDef) :
    IsUnit (akhcWeak_fullSqrt Mfull).det := by
  have hMunit : IsUnit Mfull.det := (Matrix.isUnit_iff_isUnit_det Mfull).mp hM.isUnit
  have hMne : Mfull.det ≠ 0 := isUnit_iff_ne_zero.mp hMunit
  have hsq : (akhcWeak_fullSqrt Mfull).det * (akhcWeak_fullSqrt Mfull).det = Mfull.det := by
    rw [← Matrix.det_mul, akhcWeak_fullSqrt_mul_self hM.posSemidef]
  have hsqne : (akhcWeak_fullSqrt Mfull).det ≠ 0 := by
    intro h0
    exact hMne (by rw [← hsq, h0, zero_mul])
  exact isUnit_iff_ne_zero.mpr hsqne

theorem akhcWeak_fullInvSqrt_mul_fullSqrt {d : ℕ} {Mfull : Homogenization.FullBlockMat d}
    (hM : Mfull.PosDef) :
    akhcWeak_fullInvSqrt Mfull * akhcWeak_fullSqrt Mfull = 1 :=
  Matrix.nonsing_inv_mul _ (akhcWeak_isUnit_det_fullSqrt hM)

theorem akhcWeak_fullInvSqrt_isSymm {d : ℕ} (Mfull : Homogenization.FullBlockMat d) :
    (akhcWeak_fullInvSqrt Mfull).IsSymm := by
  have hSsymm : (akhcWeak_fullSqrt Mfull)ᵀ = akhcWeak_fullSqrt Mfull := akhcWeak_fullSqrt_isSymm Mfull
  show (akhcWeak_fullInvSqrt Mfull)ᵀ = akhcWeak_fullInvSqrt Mfull
  rw [akhcWeak_fullInvSqrt, Matrix.transpose_nonsing_inv, hSsymm]

/-! ## The quadratic-form identity and the sharp `E`-relative bound -/

/-- Symmetry-commutation of the `dotProduct`/`mulVec` pairing, the generic Mathlib fact
behind the repository's `vecDot_matVecMul_comm_of_isSymm` (`Ambient/CoefficientField.lean`,
used for `Mat d`), here at the `2d`-by-`2d` level. -/
theorem akhcWeak_dotProduct_mulVec_comm_of_isSymm {d : ℕ}
    {A : Homogenization.FullBlockMat d} (hA : A.IsSymm)
    (x y : Homogenization.FullBlockVec d) :
    dotProduct x (A *ᵥ y) = dotProduct y (A *ᵥ x) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA, dotProduct_comm]

/-- **`|M^{1/2} x|² = x · M x`** at the `2d`-by-`2d` level, for a positive-semidefinite `M`. -/
theorem akhcWeak_dotProduct_fullSqrt_mulVec_self {d : ℕ} {Mfull : Homogenization.FullBlockMat d}
    (hM : Mfull.PosSemidef) (x : Homogenization.FullBlockVec d) :
    dotProduct (akhcWeak_fullSqrt Mfull *ᵥ x) (akhcWeak_fullSqrt Mfull *ᵥ x) =
      dotProduct x (Mfull *ᵥ x) := by
  rw [akhcWeak_dotProduct_mulVec_comm_of_isSymm (akhcWeak_fullSqrt_isSymm Mfull)
      (akhcWeak_fullSqrt Mfull *ᵥ x) x,
    Matrix.mulVec_mulVec, akhcWeak_fullSqrt_mul_self hM]

/-- The cancellation `M^{-1/2} (M^{1/2} x) = x`, for `M` positive-definite. -/
theorem akhcWeak_fullInvSqrt_mulVec_fullSqrt_mulVec {d : ℕ} {Mfull : Homogenization.FullBlockMat d}
    (hM : Mfull.PosDef) (x : Homogenization.FullBlockVec d) :
    akhcWeak_fullInvSqrt Mfull *ᵥ (akhcWeak_fullSqrt Mfull *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, akhcWeak_fullInvSqrt_mul_fullSqrt hM, Matrix.one_mulVec]

/-- **The sharp `E`-relative quadratic-form bound**: `x · E x ≤ |M^{-1/2} E M^{-1/2}| · (x · M x)`,
for `M` positive-definite (no symmetry or positivity needed of `E`). This is the `2d`-by-`2d`
level of the sharp prefactor `|M^{-1/2} E M^{-1/2}|^{1/2}` inside `l.weaknorms.moreproto`:
applying it with `x` a unit-scaled vector reads off the operator-norm form. -/
theorem akhcWeak_dotProduct_mulVec_le_relOpNorm_mul_dotProduct_fullSqrt_mulVec {d : ℕ}
    {Mfull Efull : Homogenization.FullBlockMat d} (hM : Mfull.PosDef)
    (x : Homogenization.FullBlockVec d) :
    dotProduct x (Efull *ᵥ x) ≤
      ‖Matrix.toEuclideanCLM (n := Homogenization.BlockCoord d) (𝕜 := ℝ)
          (akhcWeak_fullInvSqrt Mfull * Efull * akhcWeak_fullInvSqrt Mfull)‖ *
        dotProduct x (Mfull *ᵥ x) := by
  set A : Homogenization.FullBlockMat d :=
    akhcWeak_fullInvSqrt Mfull * Efull * akhcWeak_fullInvSqrt Mfull with hAdef
  set Z : Homogenization.FullBlockVec d := akhcWeak_fullSqrt Mfull *ᵥ x with hZdef
  have hmatEq : A * akhcWeak_fullSqrt Mfull = akhcWeak_fullInvSqrt Mfull * Efull := by
    rw [hAdef, Matrix.mul_assoc, akhcWeak_fullInvSqrt_mul_fullSqrt hM, Matrix.mul_one]
  have hAZ : A *ᵥ Z = akhcWeak_fullInvSqrt Mfull *ᵥ (Efull *ᵥ x) := by
    rw [hZdef, Matrix.mulVec_mulVec, hmatEq, Matrix.mulVec_mulVec]
  have hZAZ : dotProduct Z (A *ᵥ Z) = dotProduct x (Efull *ᵥ x) := by
    rw [hAZ, hZdef,
      akhcWeak_dotProduct_mulVec_comm_of_isSymm (akhcWeak_fullInvSqrt_isSymm Mfull)
        (akhcWeak_fullSqrt Mfull *ᵥ x) (Efull *ᵥ x),
      akhcWeak_fullInvSqrt_mulVec_fullSqrt_mulVec hM, dotProduct_comm]
  have hZZ : dotProduct Z Z = dotProduct x (Mfull *ᵥ x) :=
    akhcWeak_dotProduct_fullSqrt_mulVec_self hM.posSemidef x
  have hbasic :
      dotProduct Z (A *ᵥ Z) ≤
        ‖Matrix.toEuclideanCLM (n := Homogenization.BlockCoord d) (𝕜 := ℝ) A‖ *
          dotProduct Z Z := by
    have hbase :=
      akhcWeak_blockVecDot_blockMatVecMul_le_operatorNorm_mul (Homogenization.ofFullBlockMat A)
        (Homogenization.ofFullBlockVec Z)
    have hlhs :
        Homogenization.blockVecDot (Homogenization.ofFullBlockVec Z)
            (Homogenization.blockMatVecMul (Homogenization.ofFullBlockMat A)
              (Homogenization.ofFullBlockVec Z)) =
          dotProduct Z (A *ᵥ Z) := by
      rw [← Homogenization.dotProduct_toFullBlockVec, Homogenization.toFullBlockVec_blockMatVecMul,
        Homogenization.toFullBlockVec_ofFullBlockVec, Homogenization.toFullBlockMat_ofFullBlockMat]
    have hrhs :
        Homogenization.blockVecDot (Homogenization.ofFullBlockVec Z)
            (Homogenization.ofFullBlockVec Z) = dotProduct Z Z := by
      rw [← Homogenization.dotProduct_toFullBlockVec, Homogenization.toFullBlockVec_ofFullBlockVec]
    have hnorm :
        SuperdiffusionCLT.Section2.Carriers.blockMatrixOperatorNorm
            (Homogenization.ofFullBlockMat A) =
          ‖Matrix.toEuclideanCLM (n := Homogenization.BlockCoord d) (𝕜 := ℝ) A‖ := by
      rw [SuperdiffusionCLT.Section2.Carriers.blockMatrixOperatorNorm,
        Homogenization.toFullBlockMat_ofFullBlockMat]
    rwa [hlhs, hrhs, hnorm] at hbase
  rw [← hZAZ, ← hZZ]
  exact hbasic

/-! ## The `BlockMat d` carrier -/

/-- **The sharp `E`-relative prefactor `|M^{-1/2} E M^{-1/2}|`** of `l.weaknorms.moreproto`,
for doubled block matrices `M, E`. -/
noncomputable def akhcWeak_relativeOperatorNorm {d : ℕ} (M E : Homogenization.BlockMat d) : ℝ :=
  SuperdiffusionCLT.Section2.Carriers.blockMatrixOperatorNorm
    (Homogenization.ofFullBlockMat
      (akhcWeak_fullInvSqrt (Homogenization.toFullBlockMat M) * Homogenization.toFullBlockMat E *
        akhcWeak_fullInvSqrt (Homogenization.toFullBlockMat M)))

/-- **The sharp `E`-relative quadratic-form bound, at the `BlockMat d` carrier**:
`X · E X ≤ |M^{-1/2} E M^{-1/2}| · (X · M X)`, for `M` positive-definite (no symmetry or
positivity needed of `E`). -/
theorem akhcWeak_blockVecDot_le_relativeOperatorNorm_mul {d : ℕ} {M E : Homogenization.BlockMat d}
    (hM : (Homogenization.toFullBlockMat M).PosDef) (X : Homogenization.BlockVec d) :
    Homogenization.blockVecDot X (Homogenization.blockMatVecMul E X) ≤
      akhcWeak_relativeOperatorNorm M E *
        Homogenization.blockVecDot X (Homogenization.blockMatVecMul M X) := by
  have hbase :=
    akhcWeak_dotProduct_mulVec_le_relOpNorm_mul_dotProduct_fullSqrt_mulVec
      (Efull := Homogenization.toFullBlockMat E) hM (Homogenization.toFullBlockVec X)
  have hE :
      Homogenization.blockVecDot X (Homogenization.blockMatVecMul E X) =
        dotProduct (Homogenization.toFullBlockVec X)
          (Homogenization.toFullBlockMat E *ᵥ Homogenization.toFullBlockVec X) := by
    rw [← Homogenization.dotProduct_toFullBlockVec, Homogenization.toFullBlockVec_blockMatVecMul]
  have hMq :
      Homogenization.blockVecDot X (Homogenization.blockMatVecMul M X) =
        dotProduct (Homogenization.toFullBlockVec X)
          (Homogenization.toFullBlockMat M *ᵥ Homogenization.toFullBlockVec X) := by
    rw [← Homogenization.dotProduct_toFullBlockVec, Homogenization.toFullBlockVec_blockMatVecMul]
  have hnorm :
      akhcWeak_relativeOperatorNorm M E =
        ‖Matrix.toEuclideanCLM (n := Homogenization.BlockCoord d) (𝕜 := ℝ)
            (akhcWeak_fullInvSqrt (Homogenization.toFullBlockMat M) *
              Homogenization.toFullBlockMat E *
              akhcWeak_fullInvSqrt (Homogenization.toFullBlockMat M))‖ := by
    rw [akhcWeak_relativeOperatorNorm, SuperdiffusionCLT.Section2.Carriers.blockMatrixOperatorNorm,
      Homogenization.toFullBlockMat_ofFullBlockMat]
  rw [hE, hMq, hnorm]
  exact hbase

end

end SuperdiffusionCLT.AKHC61.WeakNorms
