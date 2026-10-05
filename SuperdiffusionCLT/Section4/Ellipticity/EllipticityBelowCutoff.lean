/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.EnvelopeMinimalScale
public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolumeBelow
public import SuperdiffusionCLT.Section2.Annealed.Symmetry
public import SuperdiffusionCLT.Frozen.Section2.BfAmEllipticity
public import SuperdiffusionCLT.Frozen.Section2.CoefficientCutoff
public import SuperdiffusionCLT.Section2.Carriers.BlockOperatorNorm

/-!
# Ellipticity below the cutoff

The source-level crude envelope comparison used by Proposition
`p.ellipticity.Ptwoprime`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Ellipticity

open Homogenization
open MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

/-- A dimension-only constant for the comparison of the envelope with the
annealed block matrix on an origin cube. -/
def ellipBelow_crudeConst (d : ℕ) : ℝ :=
  2 * cutoffEnvelopeConst d + 4 * (cutoffEnvelopeConst d) ^ 2

/-- The crude comparison `e.Enaught.vs.Ahom.L.crude` in block Loewner form.
The scale condition `L ≥ 1` and the standing range `0 < nu ≤ 1` convert the
product of the upper and lower envelope scalars into the printed
`C(d) nu⁻² L` bound. -/
theorem ellipBelow_crude_comparison (d : ℕ) [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (L n : ℕ) (hL : 1 ≤ L) :
    BlockMatLoewnerLE (envelopeBlockMat d nu L)
      ((ellipBelow_crudeConst d * (nu⁻¹) ^ 2 * (L : ℝ)) •
        annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) := by
  let U := envelopeUpperScalar d nu L
  let D := envelopeLowerScalar d nu
  let A := annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))
  have hU : 0 < U := envelopeUpperScalar_pos hnu d L
  have hD : 0 < D := envelopeLowerScalar_pos hnu d
  have hAupper : sigmaBarSeq nu L P n ≤ U :=
    sigmaBarSeq_le_envelopeUpperScalar hnu L hPrefix hJ2 hJ3 hJ4 n
  have hAlower : D⁻¹ ≤ sigmaBarSeq nu L P n :=
    inv_envelopeLowerScalar_le_sigmaBarSeq hnu L hPrefix hJ2 hJ3 hJ4 n
  have hcontrast :
      1 ≤ sigmaBarScalar nu L P (cubeSet (originCube d (n : ℤ))) *
        sigmaBarStarInvScalar nu L P (cubeSet (originCube d (n : ℤ))) :=
    one_le_sigmaBarScalar_mul_sigmaBarStarInvScalar hnu L hPrefix hJ2 hJ3 hJ4
      (n : ℤ)
  have hstarPos : 0 < sigmaBarStarInvSeq nu L P n :=
    sigmaBarStarInvSeq_pos hnu L hPrefix hJ2 hJ3 hJ4 n
  have hstarLower : U⁻¹ ≤ sigmaBarStarInvSeq nu L P n := by
    have hprod : 1 ≤ U * sigmaBarStarInvSeq nu L P n := by
      have hmul := mul_le_mul_of_nonneg_right hAupper hstarPos.le
      have hcontrastSeq : 1 ≤ sigmaBarSeq nu L P n * sigmaBarStarInvSeq nu L P n := by
        simpa only [sigmaBarSeq, sigmaBarStarInvSeq] using hcontrast
      exact hcontrastSeq.trans hmul
    have hdiv : 1 / U ≤ sigmaBarStarInvSeq nu L P n := by
      apply (div_le_iff₀ hU).2
      simpa only [mul_comm, one_mul] using hprod
    simpa only [one_div] using hdiv
  have hscale : 1 ≤ (nu⁻¹) ^ 2 * (L : ℝ) := by
    have hinv : 1 ≤ nu⁻¹ := by
      simpa only [inv_one] using
        (inv_le_inv₀ (by norm_num : (0 : ℝ) < 1) hnu).2 hnu1
    have hpow : 1 ≤ (nu⁻¹) ^ 2 := one_le_pow₀ hinv
    have hLcast : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    calc
      1 = 1 * 1 := by ring
      _ ≤ (nu⁻¹) ^ 2 * (L : ℝ) :=
        mul_le_mul hpow hLcast (by norm_num) (by positivity)
  have hDprod : U * D =
      2 * cutoffEnvelopeConst d +
        4 * (cutoffEnvelopeConst d) ^ 2 * (nu⁻¹) ^ 2 * (L : ℝ) := by
    have hmax : max 1 (L : ℝ) = (L : ℝ) := max_eq_right (by exact_mod_cast hL)
    dsimp only [U, D]
    rw [envelopeUpperScalar, envelopeLowerScalar, hmax]
    field_simp [hnu.ne']
    ring
  have hbound : U * D ≤ ellipBelow_crudeConst d * (nu⁻¹) ^ 2 * (L : ℝ) := by
    rw [hDprod, ellipBelow_crudeConst]
    have hC : 0 ≤ cutoffEnvelopeConst d := (cutoffEnvelopeConst_pos d).le
    have h2C : 0 ≤ 2 * cutoffEnvelopeConst d := mul_nonneg (by norm_num) hC
    calc
      2 * cutoffEnvelopeConst d +
          4 * (cutoffEnvelopeConst d) ^ 2 * (nu⁻¹) ^ 2 * (L : ℝ) =
        (2 * cutoffEnvelopeConst d) * 1 +
          4 * (cutoffEnvelopeConst d) ^ 2 * (nu⁻¹) ^ 2 * (L : ℝ) := by ring
      _ ≤ 2 * cutoffEnvelopeConst d * ((nu⁻¹) ^ 2 * (L : ℝ)) +
          4 * (cutoffEnvelopeConst d) ^ 2 * (nu⁻¹) ^ 2 * (L : ℝ) := by
        exact add_le_add (mul_le_mul_of_nonneg_left hscale h2C) le_rfl
      _ = (2 * cutoffEnvelopeConst d + 4 * (cutoffEnvelopeConst d) ^ 2) *
          ((nu⁻¹) ^ 2 * (L : ℝ)) := by ring
      _ = (2 * cutoffEnvelopeConst d + 4 * (cutoffEnvelopeConst d) ^ 2) *
          (nu⁻¹) ^ 2 * (L : ℝ) := by ring
  have hDsig : 1 ≤ D * sigmaBarSeq nu L P n := by
    calc
      1 = D * D⁻¹ := (mul_inv_cancel₀ hD.ne').symm
      _ ≤ D * sigmaBarSeq nu L P n := mul_le_mul_of_nonneg_left hAlower hD.le
  have hDAupper : U ≤ (U * D) * sigmaBarSeq nu L P n := by
    calc
      U = U * 1 := by ring
      _ ≤ U * (D * sigmaBarSeq nu L P n) := mul_le_mul_of_nonneg_left hDsig hU.le
      _ = (U * D) * sigmaBarSeq nu L P n := by ring
  have hUsigStar : 1 ≤ U * sigmaBarStarInvSeq nu L P n := by
    calc
      1 = U * U⁻¹ := (mul_inv_cancel₀ hU.ne').symm
      _ ≤ U * sigmaBarStarInvSeq nu L P n :=
        mul_le_mul_of_nonneg_left hstarLower hU.le
  have hDAlower : D ≤ (U * D) * sigmaBarStarInvSeq nu L P n := by
    calc
      D = D * 1 := by ring
      _ ≤ D * (U * sigmaBarStarInvSeq nu L P n) := mul_le_mul_of_nonneg_left hUsigStar hD.le
      _ = (U * D) * sigmaBarStarInvSeq nu L P n := by ring
  have hblock : BlockMatLoewnerLE (envelopeBlockMat d nu L) ((U * D) • A) := by
    rintro ⟨p, q⟩
    rw [envelopeBlockMat, blockVecDot_blockDiag_smul_one,
      blockMatVecMul_blockSMul, blockVecDot_smul_right,
      blockVecDot_annealedBlockMatrix_originCube hnu L hJ4 n p q]
    have hp := vecNormSq_nonneg p
    have hq := vecNormSq_nonneg q
    have hu := mul_le_mul_of_nonneg_right hDAupper hp
    have hd := mul_le_mul_of_nonneg_right hDAlower hq
    linarith only [hu, hd]
  have hfinalStep : BlockMatLoewnerLE ((U * D) • A)
      ((ellipBelow_crudeConst d * (nu⁻¹) ^ 2 * (L : ℝ)) • A) := by
    intro X
    rw [blockMatVecMul_blockSMul, blockVecDot_smul_right,
      blockMatVecMul_blockSMul, blockVecDot_smul_right]
    have hquad : 0 ≤ blockVecDot X (blockMatVecMul A X) := by
      rcases X with ⟨p, q⟩
      rw [blockVecDot_annealedBlockMatrix_originCube hnu L hJ4 n p q]
      exact add_nonneg
        (mul_nonneg (sigmaBarSeq_pos hnu L hPrefix hJ2 hJ3 hJ4 n).le
          (vecNormSq_nonneg p))
        (mul_nonneg (sigmaBarStarInvSeq_pos hnu L hPrefix hJ2 hJ3 hJ4 n).le
          (vecNormSq_nonneg q))
    calc
      (1 / 2 : ℝ) * ((U * D) * blockVecDot X (blockMatVecMul A X)) =
          (U * D) * ((1 / 2 : ℝ) * blockVecDot X (blockMatVecMul A X)) := by ring
      _ ≤ (ellipBelow_crudeConst d * (nu⁻¹) ^ 2 * (L : ℝ)) *
          ((1 / 2 : ℝ) * blockVecDot X (blockMatVecMul A X)) :=
        mul_le_mul_of_nonneg_right hbound
          (mul_nonneg (by norm_num) hquad)
      _ = (1 / 2 : ℝ) * ((ellipBelow_crudeConst d * (nu⁻¹) ^ 2 *
          (L : ℝ)) * blockVecDot X (blockMatVecMul A X)) := by ring
  exact BlockMatLoewnerLE.trans hblock hfinalStep

end

end SuperdiffusionCLT.Section4.Ellipticity
