/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Localization.IdentitiesB
public import SuperdiffusionCLT.Section5.Localization.SubcubeAvg
public import SuperdiffusionCLT.Section2.Annealed.Envelope
public import SuperdiffusionCLT.Section2.Annealed.CutoffRealizationPackage
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2Displays

/-!
# The pointwise bound for `S_z` in the crude estimate `e.crude.Sz.bound`

For `Q = z + cu_n`, the energy of the constant-offset minimizer is `⟪S_z, S_z⟫ = P_z · A(Q) P_z`
(`blockPairingAverage_self_eq_coarseBlockMatrix`), bounded through the ellipticity ratio
`envelopeRatio` of `l.bfAm.ellip` and the envelope `bfE_m`
(`blockVecDot_le_envelope`); then `ofReal_pairing_le` bounds it by the ellipticity ratio times the
`L̲²` norms of the two fields.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization MeasureTheory SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Frozen.Section2

variable {d : ℕ}

theorem blockVecDot_blockIdentity' (p q : Vec d) :
    blockVecDot (p, q) (blockMatVecMul (Book.Ch02.blockIdentity d) (p, q)) =
      vecNormSq p + vecNormSq q := by
  rw [blockQuadratic_eq]
  show vecDot p (matVecMul (1 : Mat d) p) + vecDot p (matVecMul (0 : Mat d) q) +
      vecDot q (matVecMul (0 : Mat d) p) + vecDot q (matVecMul (1 : Mat d) q) = _
  have h1 : ∀ x : Vec d, matVecMul (1 : Mat d) x = x := by
    intro x; funext i; simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]
  have h0 : ∀ x : Vec d, matVecMul (0 : Mat d) x = 0 := by
    intro x; funext i; simp [matVecMul]
  rw [h1, h1, h0, h0, vecDot_zero_right, vecDot_zero_right]
  show vecDot p p + 0 + 0 + vecDot q q = vecDot p p + vecDot q q
  ring

theorem blockVecDot_le_envelope [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (m : ℕ) (Q : TriadicCube d)
    (x y : Vec d) :
    blockVecDot (x, y) (blockMatVecMul (coarseBlockMatrix (cubeSet Q)
        (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega m).toFun) (x, y)) ≤
      envelopeRatio m Q omega *
        (envelopeUpperScalar d nu m * vecNormSq x + envelopeLowerScalar d nu * vecNormSq y) := by
  have hL := blockMatLoewnerLE_envelopeRescale_coarseBlockMatrix hnu omega m Q
    (Real.sqrt (envelopeUpperScalar d nu m) • x, Real.sqrt (envelopeLowerScalar d nu) • y)
  have hu := envelopeUpperScalar_pos hnu d m
  have hl := envelopeLowerScalar_pos hnu d
  have e1 : (Real.sqrt (envelopeUpperScalar d nu m))⁻¹ • (Real.sqrt (envelopeUpperScalar d nu m) • x) = x := by
    rw [smul_smul, inv_mul_cancel₀ (Real.sqrt_pos.2 hu).ne', one_smul]
  have e2 : (Real.sqrt (envelopeLowerScalar d nu))⁻¹ • (Real.sqrt (envelopeLowerScalar d nu) • y) = y := by
    rw [smul_smul, inv_mul_cancel₀ (Real.sqrt_pos.2 hl).ne', one_smul]
  rw [blockVecDot_envelopeRescale, e1, e2] at hL
  have hL' : blockVecDot (x, y) (blockMatVecMul (coarseBlockMatrix (cubeSet Q)
        (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega m).toFun) (x, y)) ≤
      blockVecDot (Real.sqrt (envelopeUpperScalar d nu m) • x, Real.sqrt (envelopeLowerScalar d nu) • y)
        (blockMatVecMul (envelopeRatio m Q omega • Book.Ch02.blockIdentity d)
          (Real.sqrt (envelopeUpperScalar d nu m) • x, Real.sqrt (envelopeLowerScalar d nu) • y)) := by
    linarith only [hL]
  refine hL'.trans (le_of_eq ?_)
  rw [blockMatVecMul_blockSMul, blockVecDot_smul_right, blockVecDot_blockIdentity',
    vecNormSq_smul, vecNormSq_smul, Real.sq_sqrt hu.le, Real.sq_sqrt hl.le]

theorem exists_isEllipticFieldOn_coefficientCutoff_cubeSet {nu : ℝ} (hnu : 0 < nu)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (L : ℕ) (Q : TriadicCube d) :
    ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (cubeSet Q)
      (coefficientCutoff nu omega L).toCoeffField := by
  obtain ⟨C, hC⟩ := exists_entryBound_coefficientCutoff nu omega L Q
  refine ⟨nu, ((d : ℝ) * (d : ℝ) * C ^ 2 + nu ^ 2) / nu, ⟨?_, fun x hx => ?_⟩⟩
  · exact measurable_matrix_of_entries fun i j =>
      Measurable.ite (measurableSet_cubeSet Q)
        ((coefficientCutoff nu omega L).entry_measurable i j) measurable_const
  · exact SuperdiffusionCLT.Section2.CoarseGraining.isEllipticMatrix_of_symmPart_eq_smul_one hnu
      (SuperdiffusionCLT.Section2.Cutoff.symmPart_coefficientCutoff nu omega L x)
      (hC x hx)

theorem rpow_neg_half_sq {s : ℝ} (hs : 0 < s) : (s ^ (-(1 : ℝ) / 2)) ^ 2 = s⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]
  norm_num
  exact Real.rpow_neg_one s

theorem rpow_half_sq {s : ℝ} (hs : 0 < s) : (s ^ ((1 : ℝ) / 2)) ^ 2 = s := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]
  norm_num

end SuperdiffusionCLT.Section5
