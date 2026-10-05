/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.CoarseGraining.SharpBlockBounds.DiagonalSandwich

/-!
# Loewner order under block congruence

The gauge-conjugation step S6 of `ss.localization`: the block Loewner order
`Homogenization.BlockMatLoewnerLE` is preserved under congruence by a block
matrix.  This is the one quadratic-form line that the gauge conjugation of the
localization proof needs: the sandwich of `e.ratio.fields` is conjugated by the
block gauge `G_{-ħ}`, and congruence is what transports the order through the
conjugation.

The statement is given in full generality: no invertibility is needed, because
the block Loewner order is a quadratic-form order and congruence by *any*
block matrix `G` is precomposition of quadratic forms,

`X · (Gᵗ A G) X = (G X) · A (G X)`,

which is the adjunction `blockVecDot_blockMatVecMul_transpose` (the block form
of `vecDot_matVecMul_transpose`, `x · hᵗ y = h x · y`) composed with the
composition law `blockMatVecMul_blockMatMul`.

## Main results

* `blockVecDot_blockMatVecMul_transpose`: the block adjunction
  `X · (Gᵗ Y) = (G X) · Y` for an arbitrary block matrix `G`.
* `blockVecDot_conj_blockMatMul`: the conjugated quadratic form is the
  quadratic form at the pushed-forward block vector.
* `blockMatLoewnerLE_congr_blockMatMul`: congruence preserves the block
  Loewner order, with no invertibility hypothesis.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open Homogenization
open Homogenization.Book.Ch02

noncomputable section

variable {d : ℕ}

/-! ## The transpose identity for the block pairing -/

/-- The block pairing with the transpose of `A` acting on the right is the
pairing with `A` acting on the left:

`X · (Aᵗ Y) = (A X) · Y`,

the block form of `x · (hᵗ y) = (h x) · y` (`vecDot_matVecMul_transpose`).
This is the adjunction that makes a congruence `Gᵗ A G` act on a block vector
`X` as `A` acts on the pushed-forward block vector `G X`. -/
theorem blockVecDot_blockMatVecMul_transpose (A : BlockMat d) (X Y : BlockVec d) :
    blockVecDot X (blockMatVecMul (blockMatTranspose A) Y) =
      blockVecDot (blockMatVecMul A X) Y := by
  rcases X with ⟨x₁, x₂⟩
  rcases Y with ⟨y₁, y₂⟩
  have e1 : blockVecDot (x₁, x₂) (blockMatVecMul (blockMatTranspose A) (y₁, y₂))
      = vecDot x₁ (matVecMul (matTranspose A.upperLeft) y₁
            + matVecMul (matTranspose A.lowerLeft) y₂)
          + vecDot x₂ (matVecMul (matTranspose A.upperRight) y₁
            + matVecMul (matTranspose A.lowerRight) y₂) := by
    simp only [blockMatTranspose, blockMatVecMul_fst, blockMatVecMul_snd, blockVecDot]
  have e2 : blockVecDot (blockMatVecMul A (x₁, x₂)) (y₁, y₂)
      = vecDot (matVecMul A.upperLeft x₁ + matVecMul A.upperRight x₂) y₁
          + vecDot (matVecMul A.lowerLeft x₁ + matVecMul A.lowerRight x₂) y₂ := by
    simp only [blockMatVecMul_fst, blockMatVecMul_snd, blockVecDot]
  rw [e1, e2, vecDot_add_right, vecDot_add_right, vecDot_add_left, vecDot_add_left,
    vecDot_matVecMul_transpose, vecDot_matVecMul_transpose,
    vecDot_matVecMul_transpose, vecDot_matVecMul_transpose]
  ring

/-! ## The transpose of the gauge block -/

/-! ## Congruence and the block Loewner order -/

/-- The conjugated quadratic form is the quadratic form at the pushed-forward
block vector: `X · (Gᵗ (A G)) X = (G X) · A (G X)`. -/
theorem blockVecDot_conj_blockMatMul (A G : BlockMat d) (X : BlockVec d) :
    blockVecDot X
        (blockMatVecMul
          (blockMatMul (blockMatTranspose G) (blockMatMul A G)) X) =
      blockVecDot (blockMatVecMul G X) (blockMatVecMul A (blockMatVecMul G X)) := by
  rw [blockMatVecMul_blockMatMul, blockMatVecMul_blockMatMul,
    blockVecDot_blockMatVecMul_transpose]

/-- **Congruence preserves the block Loewner order.**  For any block matrix
`G` (invertibility is not needed: the order is a quadratic-form order and the
conjugated form is the original form precomposed with `X ↦ G X`),

`A ≤ B` in the block Loewner order implies `Gᵗ A G ≤ Gᵗ B G`.

This is the transport used by the gauge conjugation of the localization proof
(`ss.localization`, step S6): the sandwich of `e.ratio.fields` is
conjugated by the block gauge without leaving the order. -/
theorem blockMatLoewnerLE_congr_blockMatMul {A B G : BlockMat d}
    (h : BlockMatLoewnerLE A B) :
    BlockMatLoewnerLE
      (blockMatMul (blockMatTranspose G) (blockMatMul A G))
      (blockMatMul (blockMatTranspose G) (blockMatMul B G)) := by
  intro X
  rw [blockVecDot_conj_blockMatMul, blockVecDot_conj_blockMatMul]
  exact h (blockMatVecMul G X)

end

end SuperdiffusionCLT.Section2.Localization