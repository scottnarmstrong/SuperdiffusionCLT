/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Deterministic.MultiscaleQuantities
public import Homogenization.Deterministic.MultiscaleQuantitiesBasic.Response
public import SuperdiffusionCLT.Section2.Carriers.BlockOperatorNorm
public import Mathlib.Data.Matrix.Block
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Scalar bridge: `normalizedBlockResponseMax` at a scalar envelope `a0 = c • Id`

This module is a self-contained ingredient of `hNear`
(`Section4/MinimalScales/SkeletonMathcalE.lean`), the bridge between two formulations:
`srootE_term` uses
`Homogenization.normalizedBlockResponseMax`, defined as the supremum of
`BlockJ (cubeSet Q) P Q' a` over the *whole* Euclidean unit sphere of
`FullBlockVec d` (via `constantFullBlockMatrixSqrt`/`constantFullBlockMatrixInvSqrt`), while the
mixing-lemma family `l.new.mixing.parameterized` (`hParam`,
`Section4/NewMixing/ParamStatement.lean`) only bounds the *two* scalar-block
test vectors `bfAhom_m^{∓1/2} eta` for `eta : BlockVec d` with `blockVecNorm eta = 1`.

Since the envelope `a0` used throughout `hNear` is always the *scalar* matrix
`sigmaBarInfinite nu m P • (1 : Mat d)` (never a genuine tensor), the full
sSup over `FullBlockVec d` collapses to exactly this family of two test vectors: for
`a0 = c • 1`, `constantFullBlockMatrixSqrt a0` and `constantFullBlockMatrixInvSqrt
a0` act on `ofFullBlockVec e` (`e` ranging over the unit sphere of
`FullBlockVec d`, in bijection with `eta : BlockVec d`, `blockVecNorm eta = 1`,
via `ofFullBlockVec`) by the scalars `c^{1/2}`/`c^{-1/2}` on the two `Vec d`
components. This module proves that collapse (`srootN_constantFullBlockMatrixSqrt_smul_one`,
`srootN_ofFullBlockVec_mulVec_sqrt_smul_one`, `srootN_ofFullBlockVec_mulVec_invSqrt_smul_one`)
and the resulting bound on `normalizedBlockResponseMax`
(`srootN_normalizedBlockResponseMax_le_of_forall_probe`), entirely in terms of
the bare `BlockJ`/`CoeffField` carrier `normalizedBlockResponseMax` actually
uses -- **not** the `doubledResponseJ`/`CoeffOn` carrier `hParam` is stated
with. Bridging `hParam`'s `doubledResponseJ` bound to a `BlockJ` bound (via
`Homogenization.Book.Ch02.doubledResponseJ_eq_BlockJ_of_isEllipticFieldOn`) is
a separate step, left to the consumer of this file.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

open scoped MatrixOrder

noncomputable section

/-! ## The scalar computation `constantFullBlockMatrixSqrt (c • 1)` -/

private theorem srootN_symmPart_smul_one (d : ℕ) (c : ℝ) :
    Homogenization.symmPart (c • (1 : Homogenization.Mat d)) = c • (1 : Homogenization.Mat d) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [Homogenization.symmPart, Matrix.smul_apply, Matrix.one_apply_eq]
  · simp [Homogenization.symmPart, Matrix.smul_apply, Matrix.one_apply_ne h,
      Matrix.one_apply_ne (Ne.symm h)]

private theorem srootN_skewPart_smul_one (d : ℕ) (c : ℝ) :
    Homogenization.skewPart (c • (1 : Homogenization.Mat d)) = 0 := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [Homogenization.skewPart, Matrix.smul_apply, Matrix.one_apply_eq]
  · simp [Homogenization.skewPart, Matrix.smul_apply, Matrix.one_apply_ne h,
      Matrix.one_apply_ne (Ne.symm h)]

/-- For `c ≠ 0`, `blockMatrixOfCoeff (c • 1)` is the block-diagonal matrix
`{c•1, 0, 0, c⁻¹•1}`: the skew part of a scalar multiple of the identity
vanishes, so the off-diagonal correction terms of `blockMatrixOfCoeff` drop
out entirely. -/
private theorem srootN_blockMatrixOfCoeff_smul_one (d : ℕ) {c : ℝ} (hc : c ≠ 0) :
    Homogenization.blockMatrixOfCoeff (c • (1 : Homogenization.Mat d)) =
      { upperLeft := c • (1 : Homogenization.Mat d)
        upperRight := 0
        lowerLeft := 0
        lowerRight := c⁻¹ • (1 : Homogenization.Mat d) } := by
  have hdet : IsUnit (1 : Homogenization.Mat d).det := by
    rw [Matrix.det_one]; exact isUnit_one
  have hinv : (c • (1 : Homogenization.Mat d))⁻¹ = c⁻¹ • (1 : Homogenization.Mat d) := by
    rw [Homogenization.nonsing_inv_smul c hc hdet,
      Matrix.inv_eq_right_inv (show (1 : Homogenization.Mat d) * 1 = 1 from Matrix.one_mul 1)]
  have htr : Homogenization.matTranspose (0 : Homogenization.Mat d) = 0 := by
    simp [Homogenization.matTranspose]
  simp only [Homogenization.blockMatrixOfCoeff, srootN_symmPart_smul_one,
    srootN_skewPart_smul_one, htr, Matrix.zero_mul, Matrix.mul_zero, neg_zero, add_zero, hinv]

/-- `toFullBlockMat` unfolds, on all four `BlockCoord` cases, to
`Matrix.fromBlocks` of its components. -/
private theorem srootN_toFullBlockMat_eq_fromBlocks {d : ℕ} (A : Homogenization.BlockMat d) :
    Homogenization.toFullBlockMat A =
      Matrix.fromBlocks A.upperLeft A.upperRight A.lowerLeft A.lowerRight := by
  ext (i | i) (j | j) <;> rfl

private theorem srootN_smul_one_eq_diagonal (d : ℕ) (c : ℝ) :
    c • (1 : Homogenization.Mat d) = Matrix.diagonal (fun _ : Fin d => c) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.smul_apply, Matrix.one_apply_eq, Matrix.diagonal_apply_eq]
  · simp [Matrix.smul_apply, Matrix.one_apply_ne h, Matrix.diagonal_apply_ne _ h]

/-- `constantFullBlockMatrix (c • 1)` is the full diagonal matrix with value
`c` on the `Sum.inl` block and `c⁻¹` on the `Sum.inr` block. -/
private theorem srootN_constantFullBlockMatrix_smul_one (d : ℕ) {c : ℝ} (hc : c ≠ 0) :
    Homogenization.constantFullBlockMatrix (c • (1 : Homogenization.Mat d)) =
      Matrix.diagonal (Sum.elim (fun _ : Fin d => c) (fun _ : Fin d => c⁻¹)) := by
  unfold Homogenization.constantFullBlockMatrix
  rw [srootN_blockMatrixOfCoeff_smul_one d hc, srootN_toFullBlockMat_eq_fromBlocks,
    srootN_smul_one_eq_diagonal d c, srootN_smul_one_eq_diagonal d c⁻¹,
    Matrix.fromBlocks_diagonal]

/-- **The scalar square root.** For `c > 0`, `constantFullBlockMatrixSqrt (c • 1)`
is the diagonal matrix with value `c^{1/2}` on the `Sum.inl` block and
`c^{-1/2}` on the `Sum.inr` block: the unique positive semidefinite square
root, identified via `CFC.sqrt_unique`. -/
theorem srootN_constantFullBlockMatrixSqrt_smul_one (d : ℕ) {c : ℝ} (hc : 0 < c) :
    Homogenization.constantFullBlockMatrixSqrt (c • (1 : Homogenization.Mat d)) =
      Matrix.diagonal
        (Sum.elim (fun _ : Fin d => c ^ ((1 : ℝ) / 2)) (fun _ : Fin d => c ^ (-(1 : ℝ) / 2))) := by
  have hc' : c ≠ 0 := hc.ne'
  have hsq : c ^ ((1 : ℝ) / 2) * c ^ ((1 : ℝ) / 2) = c := by
    rw [← Real.rpow_add hc]
    norm_num
  have hsqinv : c ^ (-(1 : ℝ) / 2) * c ^ (-(1 : ℝ) / 2) = c⁻¹ := by
    rw [← Real.rpow_add hc]
    rw [show (-(1 : ℝ) / 2 + -(1 : ℝ) / 2) = -1 by ring, Real.rpow_neg_one]
  set T : Matrix (Homogenization.BlockCoord d) (Homogenization.BlockCoord d) ℝ :=
    Matrix.diagonal
      (Sum.elim (fun _ : Fin d => c ^ ((1 : ℝ) / 2)) (fun _ : Fin d => c ^ (-(1 : ℝ) / 2)))
    with hTdef
  have hTsq : T * T = Homogenization.constantFullBlockMatrix (c • (1 : Homogenization.Mat d)) := by
    rw [hTdef, Matrix.diagonal_mul_diagonal, srootN_constantFullBlockMatrix_smul_one d hc']
    congr 1
    funext x
    cases x with
    | inl i => simpa using hsq
    | inr i => simpa using hsqinv
  have hTnonneg : (0 : Matrix (Homogenization.BlockCoord d) (Homogenization.BlockCoord d) ℝ) ≤ T := by
    rw [Matrix.nonneg_iff_posSemidef, hTdef]
    refine Matrix.PosSemidef.diagonal (fun x => ?_)
    cases x with
    | inl i => exact Real.rpow_nonneg hc.le _
    | inr i => exact Real.rpow_nonneg hc.le _
  unfold Homogenization.constantFullBlockMatrixSqrt
  exact CFC.sqrt_unique hTsq hTnonneg

/-- **The scalar inverse square root**, dually to
`srootN_constantFullBlockMatrixSqrt_smul_one`: value `c^{-1/2}` on the
`Sum.inl` block and `c^{1/2}` on the `Sum.inr` block. -/
theorem srootN_constantFullBlockMatrixInvSqrt_smul_one (d : ℕ) {c : ℝ} (hc : 0 < c) :
    Homogenization.constantFullBlockMatrixInvSqrt (c • (1 : Homogenization.Mat d)) =
      Matrix.diagonal
        (Sum.elim (fun _ : Fin d => c ^ (-(1 : ℝ) / 2)) (fun _ : Fin d => c ^ ((1 : ℝ) / 2))) := by
  unfold Homogenization.constantFullBlockMatrixInvSqrt
  rw [srootN_constantFullBlockMatrixSqrt_smul_one d hc]
  have hmul : c ^ ((1 : ℝ) / 2) * c ^ (-(1 : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add hc]
    norm_num
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext x
  cases x with
  | inl i => simpa using hmul
  | inr i => simpa [mul_comm] using hmul

/-! ## The `mulVec` action on `FullBlockVec d`, read via `ofFullBlockVec` -/

/-- **The scalar square root acts by `c^{1/2}`/`c^{-1/2}` on the two `Vec d`
components** of `ofFullBlockVec e`. -/
theorem srootN_ofFullBlockVec_mulVec_sqrt_smul_one (d : ℕ) {c : ℝ} (hc : 0 < c)
    (e : Homogenization.FullBlockVec d) :
    Homogenization.ofFullBlockVec
        (Matrix.mulVec
          (Homogenization.constantFullBlockMatrixSqrt (c • (1 : Homogenization.Mat d))) e) =
      (c ^ ((1 : ℝ) / 2) • (Homogenization.ofFullBlockVec e).1,
        c ^ (-(1 : ℝ) / 2) • (Homogenization.ofFullBlockVec e).2) := by
  rw [srootN_constantFullBlockMatrixSqrt_smul_one d hc]
  refine Prod.ext ?_ ?_ <;> funext i <;>
    simp [Homogenization.ofFullBlockVec, Matrix.mulVec_diagonal]

/-- **The scalar inverse square root acts by `c^{-1/2}`/`c^{1/2}`** on the two
`Vec d` components of `ofFullBlockVec e`. -/
theorem srootN_ofFullBlockVec_mulVec_invSqrt_smul_one (d : ℕ) {c : ℝ} (hc : 0 < c)
    (e : Homogenization.FullBlockVec d) :
    Homogenization.ofFullBlockVec
        (Matrix.mulVec
          (Homogenization.constantFullBlockMatrixInvSqrt (c • (1 : Homogenization.Mat d))) e) =
      (c ^ (-(1 : ℝ) / 2) • (Homogenization.ofFullBlockVec e).1,
        c ^ ((1 : ℝ) / 2) • (Homogenization.ofFullBlockVec e).2) := by
  rw [srootN_constantFullBlockMatrixInvSqrt_smul_one d hc]
  refine Prod.ext ?_ ?_ <;> funext i <;>
    simp [Homogenization.ofFullBlockVec, Matrix.mulVec_diagonal]

/-! ## The `normalizedBlockResponseMax` bound -/

/-- **The per-cube bridge.** For the scalar envelope `a0 = c • 1` (`c > 0`),
if the bare `BlockJ` value at the two test vectors `(c^{-1/2}•eta.1, c^{1/2}•eta.2)`
and `(c^{1/2}•eta.1, c^{-1/2}•eta.2)` is `≤ B` for *every* unit
`eta : BlockVec d` -- exactly the shape `hParam`'s conclusion gives once
bridged from `doubledResponseJ` to `BlockJ`
(`Homogenization.Book.Ch02.doubledResponseJ_eq_BlockJ_of_isEllipticFieldOn`) --
then `normalizedBlockResponseMax Q a a0 ≤ B`: the full supremum over the
`FullBlockVec d` unit sphere collapses to this family of two test vectors because `a0`
is scalar. -/
theorem srootN_normalizedBlockResponseMax_le_of_forall_probe {d : ℕ} [NeZero d]
    (Q : Homogenization.TriadicCube d) (a : Homogenization.CoeffField d) {c B : ℝ} (hc : 0 < c)
    (hbd : ∀ eta : Homogenization.BlockVec d,
        SuperdiffusionCLT.Section2.Carriers.blockVecNorm eta = 1 →
        Homogenization.BlockJ (Homogenization.cubeSet Q)
            (c ^ (-(1 : ℝ) / 2) • eta.1, c ^ ((1 : ℝ) / 2) • eta.2)
            (c ^ ((1 : ℝ) / 2) • eta.1, c ^ (-(1 : ℝ) / 2) • eta.2) a ≤ B) :
    Homogenization.normalizedBlockResponseMax Q a (c • (1 : Homogenization.Mat d)) ≤ B := by
  unfold Homogenization.normalizedBlockResponseMax
  refine csSup_le
    (Homogenization.normalizedBlockResponseValueSet_nonempty Q a (c • (1 : Homogenization.Mat d)))
    ?_
  rintro x ⟨e, he, rfl⟩
  have hnorm : SuperdiffusionCLT.Section2.Carriers.blockVecNorm
      (Homogenization.ofFullBlockVec e) = 1 := by
    rw [SuperdiffusionCLT.Section2.Carriers.blockVecNorm_eq_sqrt_blockVecDot,
      Homogenization.blockVecDot_ofFullBlockVec_self_eq_fullBlockVecNormSq, he, Real.sqrt_one]
  have hkey := hbd (Homogenization.ofFullBlockVec e) hnorm
  rwa [← srootN_ofFullBlockVec_mulVec_invSqrt_smul_one d hc e,
    ← srootN_ofFullBlockVec_mulVec_sqrt_smul_one d hc e] at hkey
