/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.Envelope
public import SuperdiffusionCLT.Section2.Localization.LocalizationEnvelopeCarrier

/-!
# The sqrt-free bilinear sandwich for the envelope rescaling

The generic Cauchy-Schwarz/AM-GM conversion from an operator norm bound to a relative
bilinear bound, specialised to the doubled block matrices of
`Section2/Annealed/Envelope.lean`: from a Euclidean operator norm bound
`|bfE_L^{-1/2} H bfE_L^{-1/2}| ≤ t` on the envelope-rescaled matrix `H`, the
relative bilinear bound `2 p·Hq ≤ t (p·bfE_L p + q·bfE_L q)` follows, for every
pair of doubled block vectors `p, q`. No matrix square root of `bfE_L` itself
is constructed; only the scalar `envelopeInvSqrt` conjugation
(via `envelopeRescale_eq`) and the block Cauchy-Schwarz
`abs_blockVecDot_le_blockVecNorm_mul` are used.

## Main result

* `ellipBelow_sandwich_of_opNorm`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Ellipticity

open Homogenization
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Carriers
open SuperdiffusionCLT.Section2.Localization

noncomputable section

variable {d : ℕ}

/-- The doubled bilinear pairing of a block matrix, written out in the four
blocks -- the bilinear (two-vector) generalisation of
`blockQuadratic_eq` (`Section2/Annealed/BlockAverageBound.lean`). -/
theorem ellipBelow_blockBilinear_eq (A : BlockMat d) (p1 p2 q1 q2 : Vec d) :
    blockVecDot (p1, p2) (blockMatVecMul A (q1, q2)) =
      vecDot p1 (matVecMul A.upperLeft q1) + vecDot p1 (matVecMul A.upperRight q2)
        + vecDot p2 (matVecMul A.lowerLeft q1) + vecDot p2 (matVecMul A.lowerRight q2) := by
  show vecDot p1 (matVecMul A.upperLeft q1 + matVecMul A.upperRight q2)
      + vecDot p2 (matVecMul A.lowerLeft q1 + matVecMul A.lowerRight q2) = _
  rw [vecDot_add_right, vecDot_add_right]
  ring

/-- The bilinear generalisation of `blockVecDot_envelopeRescale`
(`Section2/Annealed/Envelope.lean`): the rescaled bilinear pairing is the raw
bilinear pairing at the two rescaled vectors. -/
theorem ellipBelow_blockVecDot_envelopeRescale_bilinear (d : ℕ) (nu : ℝ) (m : ℕ)
    (M : BlockMat d) (p1 p2 q1 q2 : Vec d) :
    blockVecDot (p1, p2) (blockMatVecMul (envelopeRescale d nu m M) (q1, q2)) =
      blockVecDot ((Real.sqrt (envelopeUpperScalar d nu m))⁻¹ • p1,
          (Real.sqrt (envelopeLowerScalar d nu))⁻¹ • p2)
        (blockMatVecMul M ((Real.sqrt (envelopeUpperScalar d nu m))⁻¹ • q1,
          (Real.sqrt (envelopeLowerScalar d nu))⁻¹ • q2)) := by
  rw [envelopeRescale_eq, ellipBelow_blockBilinear_eq, ellipBelow_blockBilinear_eq]
  simp only [smul_matVecMul, matVecMul_smul, vecDot_smul_left, vecDot_smul_right]
  ring

/-- The squared Euclidean length of a scaled vector by a nonnegative square
root, written as the scale itself times the squared length. -/
private theorem ellipBelow_vecNormSq_sqrt_smul {c : ℝ} (hc : 0 ≤ c) (x : Vec d) :
    vecNormSq (Real.sqrt c • x) = c * vecNormSq x := by
  show vecDot (Real.sqrt c • x) (Real.sqrt c • x) = c * vecDot x x
  rw [vecDot_smul_left, vecDot_smul_right, ← mul_assoc, Real.mul_self_sqrt hc]

/-- The quadratic form of `bfE_L` (`envelopeBlockMat`) is the sum of the
squared lengths of its two blocks' square-root rescalings. -/
theorem ellipBelow_blockVecDot_envelopeBlockMat_eq_sqrt_normSq {nu : ℝ} (hnu : 0 < nu)
    (d m : ℕ) (p1 p2 : Vec d) :
    blockVecDot (p1, p2) (blockMatVecMul (envelopeBlockMat d nu m) (p1, p2)) =
      vecNormSq (Real.sqrt (envelopeUpperScalar d nu m) • p1) +
        vecNormSq (Real.sqrt (envelopeLowerScalar d nu) • p2) := by
  rw [envelopeBlockMat, blockVecDot_blockDiag_smul_one,
    ellipBelow_vecNormSq_sqrt_smul (envelopeUpperScalar_pos hnu d m).le,
    ellipBelow_vecNormSq_sqrt_smul (envelopeLowerScalar_pos hnu d).le]

/-- **The sqrt-free bilinear sandwich.** From an Euclidean operator norm bound
`|bfE_L^{-1/2} H bfE_L^{-1/2}| ≤ t` on the envelope-rescaled matrix `H`
(`envelopeRescale d nu L H`), the relative bilinear bound
`2 p·Hq ≤ t (p·bfE_L p + q·bfE_L q)` holds for every pair of doubled block
vectors `p, q : BlockVec d`. This is the generic Cauchy-Schwarz/AM-GM
conversion, specialised to `A = bfE_L = envelopeBlockMat d nu L`
(the same matrix on both quadratic forms), and proved from the block
Cauchy-Schwarz `abs_blockVecDot_le_blockVecNorm_mul` and the AM-GM step
`2ab ≤ a² + b²`; no matrix square root of `bfE_L` is constructed. -/
theorem ellipBelow_sandwich_of_opNorm {nu : ℝ} (hnu : 0 < nu) (L : ℕ) (H : BlockMat d)
    {t : ℝ} (hnorm : blockMatrixOperatorNorm (envelopeRescale d nu L H) ≤ t)
    (p q : BlockVec d) :
    2 * blockVecDot p (blockMatVecMul H q) ≤
      t * (blockVecDot p (blockMatVecMul (envelopeBlockMat d nu L) p) +
        blockVecDot q (blockMatVecMul (envelopeBlockMat d nu L) q)) := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  have ht0 : 0 ≤ t := le_trans (blockMatrixOperatorNorm_nonneg _) hnorm
  set su : ℝ := Real.sqrt (envelopeUpperScalar d nu L) with hsu
  set sl : ℝ := Real.sqrt (envelopeLowerScalar d nu) with hsl
  have hsu0 : 0 < su := Real.sqrt_pos.2 (envelopeUpperScalar_pos hnu d L)
  have hsl0 : 0 < sl := Real.sqrt_pos.2 (envelopeLowerScalar_pos hnu d)
  set U : BlockVec d := (su • p1, sl • p2) with hUdef
  set V : BlockVec d := (su • q1, sl • q2) with hVdef
  set M : BlockMat d := envelopeRescale d nu L H with hMdef
  have hUV : blockVecDot U (blockMatVecMul M V) =
      blockVecDot (p1, p2) (blockMatVecMul H (q1, q2)) := by
    rw [hMdef, hUdef, hVdef,
      ellipBelow_blockVecDot_envelopeRescale_bilinear d nu L H (su • p1) (sl • p2)
        (su • q1) (sl • q2)]
    have hu1 : (Real.sqrt (envelopeUpperScalar d nu L))⁻¹ • (su • p1) = p1 := by
      rw [smul_smul, ← hsu, inv_mul_cancel₀ hsu0.ne', one_smul]
    have hl1 : (Real.sqrt (envelopeLowerScalar d nu))⁻¹ • (sl • p2) = p2 := by
      rw [smul_smul, ← hsl, inv_mul_cancel₀ hsl0.ne', one_smul]
    have hu2 : (Real.sqrt (envelopeUpperScalar d nu L))⁻¹ • (su • q1) = q1 := by
      rw [smul_smul, ← hsu, inv_mul_cancel₀ hsu0.ne', one_smul]
    have hl2 : (Real.sqrt (envelopeLowerScalar d nu))⁻¹ • (sl • q2) = q2 := by
      rw [smul_smul, ← hsl, inv_mul_cancel₀ hsl0.ne', one_smul]
    rw [hu1, hl1, hu2, hl2]
  have hUU : blockVecDot U U =
      blockVecDot (p1, p2) (blockMatVecMul (envelopeBlockMat d nu L) (p1, p2)) := by
    rw [ellipBelow_blockVecDot_envelopeBlockMat_eq_sqrt_normSq hnu d L p1 p2, hUdef]
    rfl
  have hVV : blockVecDot V V =
      blockVecDot (q1, q2) (blockMatVecMul (envelopeBlockMat d nu L) (q1, q2)) := by
    rw [ellipBelow_blockVecDot_envelopeBlockMat_eq_sqrt_normSq hnu d L q1 q2, hVdef]
    rfl
  have hcs : |blockVecDot U (blockMatVecMul M V)| ≤
      blockVecNorm U * blockVecNorm (blockMatVecMul M V) :=
    abs_blockVecDot_le_blockVecNorm_mul U (blockMatVecMul M V)
  have hop : blockVecNorm (blockMatVecMul M V) ≤ blockMatrixOperatorNorm M * blockVecNorm V :=
    blockVecNorm_blockMatVecMul_le M V
  have hUnn := blockVecNorm_nonneg U
  have hVnn := blockVecNorm_nonneg V
  have hstep1 : blockVecNorm U * blockVecNorm (blockMatVecMul M V) ≤
      blockVecNorm U * (blockMatrixOperatorNorm M * blockVecNorm V) :=
    mul_le_mul_of_nonneg_left hop hUnn
  have hstep2 : blockVecNorm U * (blockMatrixOperatorNorm M * blockVecNorm V) ≤
      blockVecNorm U * (t * blockVecNorm V) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hnorm hVnn) hUnn
  have hcs2 : blockVecDot U (blockMatVecMul M V) ≤ t * (blockVecNorm U * blockVecNorm V) := by
    calc blockVecDot U (blockMatVecMul M V)
        ≤ |blockVecDot U (blockMatVecMul M V)| := le_abs_self _
      _ ≤ blockVecNorm U * blockVecNorm (blockMatVecMul M V) := hcs
      _ ≤ blockVecNorm U * (blockMatrixOperatorNorm M * blockVecNorm V) := hstep1
      _ ≤ blockVecNorm U * (t * blockVecNorm V) := hstep2
      _ = t * (blockVecNorm U * blockVecNorm V) := by ring
  have hamgm : 2 * (blockVecNorm U * blockVecNorm V) ≤ blockVecNorm U ^ 2 + blockVecNorm V ^ 2 := by
    have hsq := sq_nonneg (blockVecNorm U - blockVecNorm V)
    have hexpand : (blockVecNorm U - blockVecNorm V) ^ 2 =
        blockVecNorm U ^ 2 - 2 * (blockVecNorm U * blockVecNorm V) + blockVecNorm V ^ 2 := by ring
    linarith only [hsq, hexpand]
  have h6 := mul_le_mul_of_nonneg_left hamgm ht0
  have h7 : t * (2 * (blockVecNorm U * blockVecNorm V)) =
      2 * (t * (blockVecNorm U * blockVecNorm V)) := by ring
  have hfinal : 2 * blockVecDot U (blockMatVecMul M V) ≤
      t * (blockVecNorm U ^ 2 + blockVecNorm V ^ 2) := by
    linarith only [hcs2, h6, h7]
  have hUsq : blockVecNorm U ^ 2 = blockVecDot U U := blockVecNorm_sq U
  have hVsq : blockVecNorm V ^ 2 = blockVecDot V V := blockVecNorm_sq V
  rw [hUV, hUsq, hVsq, hUU, hVV] at hfinal
  exact hfinal

end

end SuperdiffusionCLT.Section4.Ellipticity
