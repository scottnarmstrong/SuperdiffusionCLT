/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.CoarseGraining.SharpBlockBounds.DiagonalSandwich
public import Homogenization.CoarseGraining.QuadraticStability.CauchySchwarz
public import SuperdiffusionCLT.Section2.Localization.BlockLoewnerCongruence

/-!
# Block-sandwich extraction

The extraction package of the localization proof `ss.localization`, step S7: from a block
Loewner sandwich between block-diagonal matrices one reads off the scalar
(`MatLoewnerLE`) comparisons of the diagonal blocks, and from the *conjugated*
sandwich

`G_{-ħ}ᵗ diag(σ_L, σ_*^{-1}_L) G_{-ħ} ≤ (1+D) · diag(σ_m, σ_*^{-1}_m)`

one concludes the un-conjugated comparisons

`σ_*^{-1}_L ≤ (1+D) σ_*^{-1}_m`  and  `σ_L ≤ (1+D) σ_m`.

The second display is `e.lh.fs.matrix.cra.bound` of the manuscript: the
upper-left block of the conjugated matrix is `σ_L + ħᵗ σ_*^{-1}_L ħ`, and the
`ħ`-term is dropped because `σ_*^{-1}_L` is positive semidefinite (as a
quadratic form).  The block-to-scalar transport is the quadratic-form
comparison `blockVecDot_le_smul_of_blockMatLoewnerLE` tested on block vectors
with one component zero, together with the block adjunction
`blockVecDot_conj_blockMatMul` of `BlockLoewnerCongruence`.

## Main results

* `blockVecDot_blockMatVecMul_blockDiag`: the quadratic form of a
  block-diagonal matrix splits into the two scalar quadratic forms.
* `matLoewnerLE_lowerRight_of_blockMatLoewnerLE_conj_blockG` and
  `matLoewnerLE_upperLeft_add_of_blockMatLoewnerLE_conj_blockG`: the same
  extractions at the gauge-conjugated sandwich; the upper-left block of
  `G_ħᵗ (blockDiag A B) G_ħ` is `A + ħᵗ B ħ`.
* `matLoewnerLE_of_matLoewnerLE_add_conj`: dropping a nonnegative conjugate
  term `ħᵗ B ħ` from a scalar Loewner comparison, given that `B` is
  positive semidefinite as a quadratic form.
* `matLoewnerLE_of_blockMatLoewnerLE_conj_blockG`: the `ħ`-absorption
  (`e.lh.fs.matrix.cra.bound`), `A ≤ c • A'`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open Homogenization
open Homogenization.Book.Ch02

noncomputable section

variable {d : ℕ}

/-! ## The quadratic form of a block-diagonal matrix -/

/-- The block quadratic form of a block-diagonal matrix is the sum of the two
scalar quadratic forms:

`(p, q) · (blockDiag A B) (p, q) = p·Ap + q·Bq`. -/
theorem blockVecDot_blockMatVecMul_blockDiag (A B : Mat d) (p q : Vec d) :
    blockVecDot (p, q) (blockMatVecMul (blockDiag A B) (p, q)) =
      vecDot p (matVecMul A p) + vecDot q (matVecMul B q) := by
  simp only [blockDiag, blockMatVecMul_fst, blockMatVecMul_snd, blockVecDot,
    zero_matVecMul, add_zero, zero_add]

/-- The action of the block gauge `blockG h = [[1, 0], [h, 1]]` on a block
vector with zero second component: `blockG h (p, 0) = (p, h p)`. -/
theorem blockMatVecMul_blockG_first (h : Mat d) (p : Vec d) :
    blockMatVecMul (blockG h) (p, (0 : Vec d)) = (p, matVecMul h p) := by
  refine Prod.ext ?_ ?_
  · simp only [blockMatVecMul_fst, blockG, matVecMul_one, zero_matVecMul, add_zero]
  · simp only [blockMatVecMul_snd, blockG, matVecMul_one, add_zero]

/-- The action of the block gauge `blockG h = [[1, 0], [h, 1]]` on a block
vector with zero first component: `blockG h (0, q) = (0, q)`. -/
theorem blockMatVecMul_blockG_second (h : Mat d) (q : Vec d) :
    blockMatVecMul (blockG h) ((0 : Vec d), q) = ((0 : Vec d), q) := by
  refine Prod.ext ?_ ?_
  · simp only [blockMatVecMul_fst, blockG, matVecMul_one, zero_matVecMul, add_zero]
  · simp only [blockMatVecMul_snd, blockG, matVecMul_one, matVecMul_zero, zero_add]

/-- The conjugate-square quadratic form: with `r = h p`,

`p · (A + hᵗ B h) p = p·Ap + r·Br`. -/
theorem vecDot_matVecMul_add_conj_mul (A B h : Mat d) (p : Vec d) :
    vecDot p (matVecMul (A + matTranspose h * B * h) p) =
      vecDot p (matVecMul A p) + vecDot (matVecMul h p) (matVecMul B (matVecMul h p)) := by
  rw [add_matVecMul, vecDot_add_right, ← matVecMul_mul, ← matVecMul_mul,
    vecDot_matVecMul_transpose]

/-- The upper-left quadratic form of the gauge conjugate of a block-diagonal
matrix: with `r = h p`,

`p · (G_hᵗ (blockDiag A B) G_h) (p, 0) = p·Ap + r·Br`. -/
theorem blockVecDot_first_conj_blockG (A B h : Mat d) (p : Vec d) :
    blockVecDot (p, (0 : Vec d))
        (blockMatVecMul
          (blockMatMul (blockMatTranspose (blockG h)) (blockMatMul (blockDiag A B) (blockG h)))
          (p, (0 : Vec d))) =
      vecDot p (matVecMul A p) + vecDot (matVecMul h p) (matVecMul B (matVecMul h p)) := by
  rw [blockVecDot_conj_blockMatMul, blockMatVecMul_blockG_first,
    blockVecDot_blockMatVecMul_blockDiag]

/-- The lower-right quadratic form of the gauge conjugate of a block-diagonal
matrix: `q · (G_hᵗ (blockDiag A B) G_h) (0, q) = q·Bq`. -/
theorem blockVecDot_second_conj_blockG (A B h : Mat d) (q : Vec d) :
    blockVecDot ((0 : Vec d), q)
        (blockMatVecMul
          (blockMatMul (blockMatTranspose (blockG h)) (blockMatMul (blockDiag A B) (blockG h)))
          ((0 : Vec d), q)) =
      vecDot q (matVecMul B q) := by
  rw [blockVecDot_conj_blockMatMul, blockMatVecMul_blockG_second,
    blockVecDot_blockMatVecMul_blockDiag, vecDot_zero_left, zero_add]

/-! ## The diagonal extractions -/

/-! ## Extraction at the gauge-conjugated sandwich -/

/-- **Lower-right extraction at the conjugated sandwich.**  The lower-right
block of `G_ħᵗ (blockDiag A B) G_ħ` is `B` itself, so the conjugated sandwich
`G_ħᵗ (blockDiag A B) G_ħ ≤ c • blockDiag A' B'` gives `B ≤ c • B'` with no
trace of the gauge block. -/
theorem matLoewnerLE_lowerRight_of_blockMatLoewnerLE_conj_blockG
    {A B A' B' : Mat d} {c : ℝ} (h : Mat d)
    (hsand : BlockMatLoewnerLE
      (blockMatMul (blockMatTranspose (blockG h)) (blockMatMul (blockDiag A B) (blockG h)))
      (c • blockDiag A' B')) :
    MatLoewnerLE B (c • B') := by
  intro q
  have hx := blockVecDot_le_smul_of_blockMatLoewnerLE hsand ((0 : Vec d), q)
  rw [blockVecDot_second_conj_blockG, blockVecDot_blockMatVecMul_blockDiag,
    vecDot_zero_left, zero_add] at hx
  rw [smul_matVecMul, vecDot_smul_right]
  linarith only [hx]

/-- **Upper-left extraction at the conjugated sandwich.**  The upper-left block
of `G_ħᵗ (blockDiag A B) G_ħ` is `A + ħᵗ B ħ`, so the conjugated sandwich gives
`A + ħᵗ B ħ ≤ c • A'`. -/
theorem matLoewnerLE_upperLeft_add_of_blockMatLoewnerLE_conj_blockG
    {A B A' B' : Mat d} {c : ℝ} (h : Mat d)
    (hsand : BlockMatLoewnerLE
      (blockMatMul (blockMatTranspose (blockG h)) (blockMatMul (blockDiag A B) (blockG h)))
      (c • blockDiag A' B')) :
    MatLoewnerLE (A + matTranspose h * B * h) (c • A') := by
  intro p
  have hx := blockVecDot_le_smul_of_blockMatLoewnerLE hsand (p, (0 : Vec d))
  rw [blockVecDot_first_conj_blockG, blockVecDot_blockMatVecMul_blockDiag,
    vecDot_zero_left, add_zero] at hx
  rw [vecDot_matVecMul_add_conj_mul (A := A) (B := B) h p, smul_matVecMul,
    vecDot_smul_right]
  linarith only [hx]

/-! ## The `ħ`-absorption (`e.lh.fs.matrix.cra.bound`) -/

/-- Dropping a conjugate square from a scalar Loewner comparison: if
`A + ħᵗ B ħ ≤ c • E` and `B` is positive semidefinite as a quadratic form,
then `A ≤ c • E`.  This is the "first inequality due to the fact that
`σ_*^{-1}` is positive definite and symmetric" of `e.lh.fs.matrix.cra.bound`. -/
theorem matLoewnerLE_of_matLoewnerLE_add_conj {A B E : Mat d} {c : ℝ} (h : Mat d)
    (hsand : MatLoewnerLE (A + matTranspose h * B * h) (c • E))
    (hB : ∀ x : Vec d, 0 ≤ vecDot x (matVecMul B x)) :
    MatLoewnerLE A (c • E) := by
  intro p
  have hx := hsand p
  have hpsd := hB (matVecMul h p)
  rw [vecDot_matVecMul_add_conj_mul (A := A) (B := B) h p, smul_matVecMul,
    vecDot_smul_right] at hx
  rw [smul_matVecMul, vecDot_smul_right]
  linarith only [hx, hpsd]

/-- **The `ħ`-absorption.**  From the conjugated sandwich
`G_ħᵗ (blockDiag A B) G_ħ ≤ c • blockDiag A' B'` and positive semidefiniteness
of `B` as a quadratic form, the un-conjugated upper-left comparison
`A ≤ c • A'` follows: this is `e.lh.fs.matrix.cra.bound`,
`σ_L ≤ σ_L + ħᵗ σ_*^{-1}_L ħ ≤ (1+D) σ_m`. -/
theorem matLoewnerLE_of_blockMatLoewnerLE_conj_blockG
    {A B A' B' : Mat d} {c : ℝ} (h : Mat d)
    (hsand : BlockMatLoewnerLE
      (blockMatMul (blockMatTranspose (blockG h)) (blockMatMul (blockDiag A B) (blockG h)))
      (c • blockDiag A' B'))
    (hB : ∀ x : Vec d, 0 ≤ vecDot x (matVecMul B x)) :
    MatLoewnerLE A (c • A') :=
  matLoewnerLE_of_matLoewnerLE_add_conj h
    (matLoewnerLE_upperLeft_add_of_blockMatLoewnerLE_conj_blockG h hsand) hB

end

end SuperdiffusionCLT.Section2.Localization