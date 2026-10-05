/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Book.Ch02.Theorems.MatrixOperatorNorm
public import SuperdiffusionCLT.Section2.Annealed.Envelope
public import SuperdiffusionCLT.Section2.CoarseGraining.SkewShift

/-!
# Pure algebra for the `T_3` bound: block-diagonal expansion, cross-term vanishing

This is part of the proof of
`l.new.mixing.parameterized` ("Step 1" continued). No probability, no measure
theory, no cutoff-specific objects: this is the abstract computation

`G_{-hSum} P . diag(a,b) . G_{-hSum} P = a c² |e|² + b s² |e|² + b c² |hSum e|²`

for `P = (c•e, s•e)`, `hSum` skew-symmetric, using that the cross term
`vecDot (matVecMul hSum e) e` vanishes by skew-symmetry (the paper: "the cross term
vanishes because `e . (h_z+h_0) e = 0`"), followed by the operator-norm bound
`|hSum e|² ≤ ‖hSum‖² |e|²` and the triangle-square bound
`‖hz+h0‖² ≤ 2‖hz‖² + 2‖h0‖²`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.NewMixing

open Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.CoarseGraining

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- **Block-diagonal expansion, cross-term vanishing**: the
exact quadratic form `G_{-hSum} P . diag(a•1,b•1) . G_{-hSum} P`, for
`P = (c•e, s•e)` and `hSum` skew-symmetric, equals
`a*c²*|e|² + b*s²*|e|² + b*c²*|hSum e|²` — no cross term. -/
theorem newMixParam_blockQuad_expand {a b c s : ℝ} {e : Vec d} {hSum : Mat d}
    (hSumSkew : matTranspose hSum = -hSum) :
    blockVecDot
        (blockMatVecMul (blockG (-hSum)) (c • e, s • e))
        (blockMatVecMul (Book.Ch02.blockDiag (a • (1 : Mat d)) (b • (1 : Mat d)))
          (blockMatVecMul (blockG (-hSum)) (c • e, s • e))) =
      a * c ^ 2 * vecNormSq e + b * s ^ 2 * vecNormSq e +
        b * c ^ 2 * vecNormSq (matVecMul hSum e) := by
  have h1 : matVecMul (1 : Mat d) (c • e) = c • e := by
    funext i; simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]
  have h2 : matVecMul (0 : Mat d) (s • e) = 0 := by funext i; simp [matVecMul]
  have h3a : matVecMul (-hSum) (c • e) = -(matVecMul hSum (c • e)) := by
    funext i; simp [matVecMul, Matrix.neg_apply, Finset.sum_neg_distrib]
  have h3b : matVecMul hSum (c • e) = c • matVecMul hSum e := matVecMul_smul hSum c e
  have h3 : matVecMul (-hSum) (c • e) = (-c) • matVecMul hSum e := by
    rw [h3a, h3b, neg_smul]
  have h4 : matVecMul (1 : Mat d) (s • e) = s • e := by
    funext i; simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]
  have hGP : blockMatVecMul (blockG (-hSum)) (c • e, s • e) =
      (c • e, (-c) • matVecMul hSum e + s • e) := by
    show (matVecMul (1 : Mat d) (c • e) + matVecMul (0 : Mat d) (s • e),
        matVecMul (-hSum) (c • e) + matVecMul (1 : Mat d) (s • e)) =
      (c • e, (-c) • matVecMul hSum e + s • e)
    rw [h1, h2, h3, h4, add_zero]
  rw [hGP, blockVecDot_blockDiag_smul_one]
  have hcNormSq : vecNormSq (c • e) = c ^ 2 * vecNormSq e := vecNormSq_smul c e
  have hqexpand : vecDot ((-c) • matVecMul hSum e + s • e) ((-c) • matVecMul hSum e + s • e) =
      (-c) * ((-c) * vecDot (matVecMul hSum e) (matVecMul hSum e)) +
        (-c) * (s * vecDot (matVecMul hSum e) e) +
        (s * ((-c) * vecDot e (matVecMul hSum e)) + s * (s * vecDot e e)) := by
    simp only [vecDot_add_left, vecDot_add_right, vecDot_smul_left, vecDot_smul_right]
    ring
  have hcross0' : vecDot e (matVecMul hSum e) = 0 := vecDot_matVecMul_self_of_skew hSumSkew e
  have hcross0 : vecDot (matVecMul hSum e) e = 0 := by
    rw [vecDot_comm]; exact hcross0'
  have hqNormSq : vecNormSq ((-c) • matVecMul hSum e + s • e) =
      c ^ 2 * vecNormSq (matVecMul hSum e) + s ^ 2 * vecNormSq e := by
    show vecDot ((-c) • matVecMul hSum e + s • e) ((-c) • matVecMul hSum e + s • e) = _
    rw [hqexpand, hcross0, hcross0']
    show _ = c ^ 2 * vecDot (matVecMul hSum e) (matVecMul hSum e) + s ^ 2 * vecDot e e
    ring
  rw [hcNormSq, hqNormSq]
  ring

omit [NeZero d] in
/-- The operator-norm bound on the perturbed quadratic term: `|hSum e|² ≤
‖hSum‖² |e|²`, restated with the `matVecMul`/`vecNormSq` names of this
development. -/
theorem newMixParam_vecNormSq_matVecMul_le (hSum : Mat d) (e : Vec d) :
    vecNormSq (matVecMul hSum e) ≤ matrixOperatorNorm hSum ^ 2 * vecNormSq e :=
  vecNormSq_matVecMul_le_matrixOperatorNorm_sq_mul_vecNormSq hSum e

omit [NeZero d] in
/-- **The triangle-square bound** `‖hz + h0‖² ≤ 2‖hz‖² + 2‖h0‖²`, from the
operator-norm triangle inequality (via
`matrixOperatorNorm_le_matrixOperatorNorm_add_matrixOperatorNorm_sub`) and
`(x+y)² ≤ 2x² + 2y²`. -/
theorem newMixParam_matrixOperatorNorm_add_sq_le (hz h0 : Mat d) :
    matrixOperatorNorm (hz + h0) ^ 2 ≤ 2 * matrixOperatorNorm hz ^ 2 + 2 * matrixOperatorNorm h0 ^ 2 := by
  have htri : matrixOperatorNorm (hz + h0) ≤ matrixOperatorNorm h0 + matrixOperatorNorm hz := by
    have h := matrixOperatorNorm_le_matrixOperatorNorm_add_matrixOperatorNorm_sub (hz + h0) h0
    have heq : (hz + h0) - h0 = hz := by abel
    rwa [heq] at h
  have hnn1 : (0:ℝ) ≤ matrixOperatorNorm (hz + h0) := matrixOperatorNorm_nonneg _
  have hnn2 : (0:ℝ) ≤ matrixOperatorNorm hz := matrixOperatorNorm_nonneg _
  have hnn3 : (0:ℝ) ≤ matrixOperatorNorm h0 := matrixOperatorNorm_nonneg _
  have hsq : matrixOperatorNorm (hz + h0) ^ 2 ≤ (matrixOperatorNorm h0 + matrixOperatorNorm hz) ^ 2 :=
    pow_le_pow_left₀ hnn1 htri 2
  nlinarith only [hsq, hnn2, hnn3, sq_nonneg (matrixOperatorNorm hz - matrixOperatorNorm h0)]

end
end SuperdiffusionCLT.Section4.NewMixing
