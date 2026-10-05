/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3Integrable
public import SuperdiffusionCLT.Section2.Localization.CenteredIncrementQuadratic
public import SuperdiffusionCLT.Section2.CoarseGraining.SkewShiftCutoff

/-!
# Localization of the blow-up remainder

The coefficient perturbation is centered by its volume average before
localization. The resulting quadratic comparison holds for every doubled
vector, so it can subsequently be used uniformly on the unit sphere.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open scoped BigOperators

/-- The averaged increment and its negative are skew matrices. -/
theorem rhsTerm3BlowupLocal_average_skew {d : ℕ} (ω : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (ell L : ℕ)
    (U : Set (Homogenization.Vec d)) :
    Homogenization.matTranspose (Homogenization.volumeAverageMat U (fun y => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement ω ell L y)) =
      -Homogenization.volumeAverageMat U (fun y => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement ω ell L y) := by
  exact SuperdiffusionCLT.Section2.Cutoff.matTranspose_volumeAverageMat U _ (fun y i j => by
    have h := congrFun (congrFun (SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement_skew ω ell L y) j) i
    simpa only [Matrix.transpose_apply, Matrix.neg_apply, Pi.neg_apply] using h)

/-- The localized gauge remainder on the origin cube, with no assumed
localization estimate. The oscillation amplitude uses the cube diameter. -/
theorem rhsTerm3BlowupLocal_localized_origin {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (ω : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (ell L n : ℕ) (hL : ell ≤ L) (Q : Homogenization.BlockVec d) :
    let R := Homogenization.originCube d (n : ℤ)
    let H := Homogenization.volumeAverageMat (Homogenization.openCubeSet R) (fun y => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement ω ell L y)
    let M := SuperdiffusionCLT.Section2.Localization.matrixOperatorNorm_diamConst d * (3 : ℝ) ^ n * SuperdiffusionCLT.Section3.ResponseFields.upperShellDerivGauge n ell L ω
    |Homogenization.blockVecDot Q (Homogenization.blockMatVecMul
        (Homogenization.Book.Ch02.blockMatMul (Homogenization.Book.Ch02.blockMatTranspose (Homogenization.Book.Ch02.blockG H))
          (Homogenization.Book.Ch02.blockMatMul (translatedBlockMat nu L ω R) (Homogenization.Book.Ch02.blockG H))) Q) -
      Homogenization.blockVecDot Q (Homogenization.blockMatVecMul (translatedBlockMat nu ell ω R) Q)| ≤
      (nu⁻¹ * M + nu⁻¹ ^ 2 * M ^ 2) *
        Homogenization.blockVecDot Q (Homogenization.blockMatVecMul (translatedBlockMat nu ell ω R) Q) := by
  dsimp only
  let R := Homogenization.originCube d (n : ℤ)
  let U := Homogenization.Book.Ch02.cubeDomain R
  let H := Homogenization.volumeAverageMat (Homogenization.openCubeSet R) (fun y => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement ω ell L y)
  let M := SuperdiffusionCLT.Section2.Localization.matrixOperatorNorm_diamConst d * (3 : ℝ) ^ n * SuperdiffusionCLT.Section3.ResponseFields.upperShellDerivGauge n ell L ω
  let a := SuperdiffusionCLT.Section3.Setup.cutoffCoeffOnCh02 nu hnu ω ell R
  let aL := SuperdiffusionCLT.Section3.Setup.cutoffCoeffOnCh02 nu hnu ω L R
  have ha : a.toCoeffField = (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu ω ell).toCoeffField := rfl
  have haL : aL.toCoeffField = (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu ω L).toCoeffField := rfl
  have hH : Homogenization.matTranspose H = -H := rhsTerm3BlowupLocal_average_skew ω ell L _
  change Matrix.transpose H = -H at hH
  have hneg : Homogenization.matTranspose (-H) = -(-H) := by
    change Matrix.transpose (-H) = -(-H)
    rw [Matrix.transpose_neg, hH]
  let b := SuperdiffusionCLT.Section2.CoarseGraining.addConstSkewCoeffOn aL hneg
  have hb : ∀ᵐ x ∂(Homogenization.volumeMeasureOn (U : Set (Homogenization.Vec d))),
      b.toCoeffField x = a.toCoeffField x + (SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement ω ell L x - H) := by
    refine Filter.Eventually.of_forall fun x => ?_
    change aL.toCoeffField x + -H = a.toCoeffField x + (SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement ω ell L x - H)
    rw [ha, haL, ← SuperdiffusionCLT.Section2.Localization.coefficientCutoff_toCoeffField_sub nu ω hL x]
    abel
  have hs : ∀ᵐ x ∂(Homogenization.volumeMeasureOn (U : Set (Homogenization.Vec d))),
      Homogenization.symmPart (a.toCoeffField x) = nu • (1 : Homogenization.Mat d) :=
    Filter.Eventually.of_forall fun x => by rw [ha]; exact SuperdiffusionCLT.Section2.Cutoff.symmPart_coefficientCutoff nu ω ell x
  have hskew : ∀ᵐ x ∂(Homogenization.volumeMeasureOn (U : Set (Homogenization.Vec d))),
      Homogenization.matTranspose (SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement ω ell L x - H) = -(SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement ω ell L x - H) := by
    refine Filter.Eventually.of_forall fun x => ?_
    change Matrix.transpose (SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement ω ell L x - H) = _
    rw [Matrix.transpose_sub, SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement_skew, hH]
    abel
  have hM : 0 ≤ M := mul_nonneg
    (mul_nonneg (SuperdiffusionCLT.Section2.Localization.matrixOperatorNorm_diamConst_nonneg d) (by positivity))
    (SuperdiffusionCLT.Section3.ResponseFields.upperShellDerivGauge_nonneg n ell L ω)
  have hnorm : ∀ᵐ x ∂(Homogenization.volumeMeasureOn (U : Set (Homogenization.Vec d))), ∀ v : Homogenization.Vec d,
      Homogenization.vecNormSq (Homogenization.matVecMul (SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement ω ell L x - H) v) ≤ M ^ 2 * Homogenization.vecNormSq v := by
    exact SuperdiffusionCLT.Section2.Localization.ae_vecNormSq_centeredFiniteShellIncrement_le ω ell L n U (by
      rw [Homogenization.Book.Ch02.cubeDomain_coe])
  obtain ⟨hlo, hhi⟩ := SuperdiffusionCLT.Section2.Localization.coarseBlockMatrix_localization_scalar_two_sided hnu hM hs hb hskew hnorm
  have hloQ := hlo Q
  have hhiQ := hhi Q
  rw [Homogenization.blockMatVecMul_blockSMul, Homogenization.blockVecDot_smul_right,
    Homogenization.blockVecDot_blockMatVecMul_ofFullBlockMat_sub] at hloQ hhiQ
  have hconj := SuperdiffusionCLT.Section2.CoarseGraining.coarseBlockMatrix_addConstSkewCoeffOn aL hneg
  have hAm := SuperdiffusionCLT.Section3.Setup.translatedBlockMat_eq_ch02_coarseBlockMatrix hnu ell ω R
  have hAL := SuperdiffusionCLT.Section3.Setup.translatedBlockMat_eq_ch02_coarseBlockMatrix hnu L ω R
  change translatedBlockMat nu ell ω R = Homogenization.Book.Ch02.coarseBlockMatrix U a at hAm
  change translatedBlockMat nu L ω R = Homogenization.Book.Ch02.coarseBlockMatrix U aL at hAL
  have hconj' : Homogenization.Book.Ch02.coarseBlockMatrix U b =
      Homogenization.Book.Ch02.blockMatMul (Homogenization.Book.Ch02.blockMatTranspose (Homogenization.Book.Ch02.blockG H))
        (Homogenization.Book.Ch02.blockMatMul (translatedBlockMat nu L ω R) (Homogenization.Book.Ch02.blockG H)) := by
    rw [hAL]
    simpa only [neg_neg] using hconj
  rw [hconj', ← hAm] at hloQ hhiQ
  exact abs_le.mpr ⟨by linarith only [hloQ], by linarith only [hhiQ]⟩

/-- The transported coarse energy is bounded uniformly over unit directions. -/
theorem rhsTerm3BlowupLocal_gauge_energy_le {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (ell L : ℕ) (ω : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (R : Homogenization.TriadicCube d) (e : Homogenization.Vec d) (he : Homogenization.vecNormSq e = 1) :
    let H := SuperdiffusionCLT.Section3.Setup.translatedStreamIncrementAvg ω ell L R
    Homogenization.blockVecDot (Homogenization.blockMatVecMul (Homogenization.Book.Ch02.blockG (-H)) ((e, 0) : Homogenization.BlockVec d))
      (Homogenization.blockMatVecMul (translatedBlockMat nu ell ω R)
        (Homogenization.blockMatVecMul (Homogenization.Book.Ch02.blockG (-H)) ((e, 0) : Homogenization.BlockVec d))) ≤
      2 * translatedBlockNorm nu ell ω R + 2 * translatedStreamSlot nu ell L ω R := by
  let A := SuperdiffusionCLT.Section3.Setup.cutoffCoeffOnCh02 nu hnu ω ell R
  let V := Homogenization.Book.Ch02.cubeDomain R
  let K := Homogenization.Book.Ch02.kappaCoarse V A
  let T := Homogenization.Book.Ch02.sigmaStarInvCoarse V A
  let W := SuperdiffusionCLT.Section3.Setup.translatedSigmaStarInvHalf nu ell ω R
  let H := SuperdiffusionCLT.Section3.Setup.translatedStreamIncrementAvg ω ell L R
  have hGram : Homogenization.matTranspose W * W = T := by
    have h := gramSqrt_sigmaStarInvCoarse_cutoffCube_forall hnu ell ω R
    have hT : Homogenization.sigmaStarInvCoarse (Homogenization.cubeSet R) (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu ω ell).toCoeffField = T := by
      rw [sigmaStarInvCoarse_cubeSet_eq_openCubeSet R
        (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu ω ell).toCoeffField, ← Homogenization.Book.Ch02.cubeDomain_coe]
      exact SuperdiffusionCLT.Section2.CoarseGraining.sigmaStarInvCoarse_toCoeffField V A
    exact h.trans hT
  have hKB : Homogenization.vecNormSq (Homogenization.matVecMul W (Homogenization.matVecMul K e)) ≤
      Homogenization.vecDot e (Homogenization.matVecMul (translatedCoarseBlock nu ell ω R) e) := by
    have h := kappaUpperLeft_quadratic_le_bCoarse V A e
    rw [← SuperdiffusionCLT.Section3.Setup.translatedCoarseBlock_eq_ch02_bCoarse hnu ell ω R,
      ← SuperdiffusionCLT.Section3.Setup.translatedSigmaStarInvHalf_eq_ch02_sqrt hnu ell ω R] at h
    exact h
  have hform := gauge_shift_sqrt (translatedCoarseBlock nu ell ω R) K T W H e hGram
  have hAM := SuperdiffusionCLT.Section3.Setup.translatedBlockMat_eq_blockRecord hnu ell ω R
  rw [← hAM] at hform
  have hy := abs_gauge_shift_le 1 (by norm_num) (translatedCoarseBlock nu ell ω R) K W H e he hKB
  have hb := Homogenization.Book.Ch02.abs_vecDot_matVecMul_le_matrixOperatorNorm_mul_vecNormSq
    (translatedCoarseBlock nu ell ω R) e
  rw [he, mul_one] at hb
  have hb' := (le_abs_self (Homogenization.vecDot e (Homogenization.matVecMul (translatedCoarseBlock nu ell ω R) e))).trans hb
  have hy' := (le_abs_self _).trans hy
  dsimp only
  rw [hform, SuperdiffusionCLT.Section3.Setup.translatedStreamSlot_eq_halfMul_avg,
    translatedBlockNorm]
  dsimp only [W, H] at hy'
  norm_num only [inv_one, one_mul, one_add_one_eq_two] at hy'
  linarith only [hb', hy']

/-- The printed operator-slot inequality on the origin cube, with the
localization remainder constructed explicitly and no remainder premise. -/
theorem rhsTerm3BlowupLocal_printedSlot_origin {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (S : SuperdiffusionCLT.Section3.Setup.ScaleSelection) (hL : S.ell ≤ S.LPrime)
    (ω : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) :
    let R := Homogenization.originCube d (S.n : ℤ)
    let M := SuperdiffusionCLT.Section2.Localization.matrixOperatorNorm_diamConst d * (3 : ℝ) ^ S.n * SuperdiffusionCLT.Section3.ResponseFields.upperShellDerivGauge S.n S.ell S.LPrime ω
    Homogenization.Book.Ch02.matrixOperatorNorm (translatedCoarseBlock nu S.LPrime ω R - translatedCoarseBlock nu S.ell ω R) ≤
      1 * translatedBlockNorm nu S.ell ω R +
        (1 + (1 : ℝ)⁻¹) * translatedStreamSlot nu S.ell S.LPrime ω R +
        (nu⁻¹ * M + nu⁻¹ ^ 2 * M ^ 2) *
          (2 * translatedBlockNorm nu S.ell ω R + 2 * translatedStreamSlot nu S.ell S.LPrime ω R) := by
  dsimp only
  let R := Homogenization.originCube d (S.n : ℤ)
  let M := SuperdiffusionCLT.Section2.Localization.matrixOperatorNorm_diamConst d * (3 : ℝ) ^ S.n * SuperdiffusionCLT.Section3.ResponseFields.upperShellDerivGauge S.n S.ell S.LPrime ω
  let D := nu⁻¹ * M + nu⁻¹ ^ 2 * M ^ 2
  have hM : 0 ≤ M := mul_nonneg
    (mul_nonneg (SuperdiffusionCLT.Section2.Localization.matrixOperatorNorm_diamConst_nonneg d) (by positivity))
    (SuperdiffusionCLT.Section3.ResponseFields.upperShellDerivGauge_nonneg S.n S.ell S.LPrime ω)
  have hD : 0 ≤ D := add_nonneg (mul_nonneg (inv_nonneg.mpr hnu.le) hM)
    (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  apply SuperdiffusionCLT.Section3.Setup.rootSlotDisplay_of_operatorNormCore hnu S ω R
    (fun _ _ => D * (2 * translatedBlockNorm nu S.ell ω R + 2 * translatedStreamSlot nu S.ell S.LPrime ω R))
  intro e he
  have hloc := rhsTerm3BlowupLocal_localized_origin hnu ω S.ell S.LPrime S.n hL
    (Homogenization.blockMatVecMul (Homogenization.Book.Ch02.blockG (-(SuperdiffusionCLT.Section3.Setup.translatedStreamIncrementAvg ω S.ell S.LPrime R)))
      ((e, 0) : Homogenization.BlockVec d))
  dsimp only at hloc
  rw [← SuperdiffusionCLT.Section2.Estimates.Stream.volumeAverageMat_cubeSet_eq_openCubeSet] at hloc
  have hout := hloc.trans (mul_le_mul_of_nonneg_left
    (rhsTerm3BlowupLocal_gauge_energy_le hnu S.ell S.LPrime ω R e he) hD)
  simp only [blockGT, Homogenization.Book.Ch02.blockMatTranspose, Homogenization.Book.Ch02.blockG, Homogenization.matTranspose, Matrix.transpose_one,
    Matrix.transpose_zero] at hout ⊢
  exact hout

/-- Translation covariance of the printed operator slot. -/
theorem rhsTerm3BlowupLocal_slot_translate {d : ℕ} (nu : ℝ) (ell L : ℕ)
    (ω : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (R : Homogenization.TriadicCube d) :
    translatedStreamSlot nu ell L ω R = translatedStreamSlot nu ell L
      (SuperdiffusionCLT.Frozen.Assumptions.ShellField.translateSequence (Homogenization.triadicCubeShift R) ω)
      (Homogenization.originCube d R.scale) := by
  unfold translatedStreamSlot
  rw [sigmaStarInvCoarse_cubeSet_translate,
    volumeAverageMat_cubeSet_finiteShellIncrement_translate]

/-- The pointwise printed inequality on every cube of the selected scale.
No pointwise or remainder estimate is assumed. -/
theorem rhsTerm3BlowupLocal_printedSlot_cube {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (S : SuperdiffusionCLT.Section3.Setup.ScaleSelection) (hL : S.ell ≤ S.LPrime)
    (ω : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (R : Homogenization.TriadicCube d) (hR : R.scale = (S.n : ℤ)) :
    let M := SuperdiffusionCLT.Section2.Localization.matrixOperatorNorm_diamConst d * (3 : ℝ) ^ S.n * SuperdiffusionCLT.Section3.ResponseFields.upperShellDerivGauge S.n S.ell S.LPrime
      (SuperdiffusionCLT.Frozen.Assumptions.ShellField.translateSequence (Homogenization.triadicCubeShift R) ω)
    Homogenization.Book.Ch02.matrixOperatorNorm (translatedCoarseBlock nu S.LPrime ω R - translatedCoarseBlock nu S.ell ω R) ≤
      1 * translatedBlockNorm nu S.ell ω R +
        (1 + (1 : ℝ)⁻¹) * translatedStreamSlot nu S.ell S.LPrime ω R +
        (nu⁻¹ * M + nu⁻¹ ^ 2 * M ^ 2) *
          (2 * translatedBlockNorm nu S.ell ω R + 2 * translatedStreamSlot nu S.ell S.LPrime ω R) := by
  have h := rhsTerm3BlowupLocal_printedSlot_origin hnu S hL
    (SuperdiffusionCLT.Frozen.Assumptions.ShellField.translateSequence (Homogenization.triadicCubeShift R) ω)
  dsimp only at h ⊢
  rw [translatedCoarseBlock_eq_originCube nu S.LPrime ω R,
    translatedCoarseBlock_eq_originCube nu S.ell ω R,
    translatedBlockNorm_eq_originCube nu S.ell ω R,
    rhsTerm3BlowupLocal_slot_translate nu S.ell S.LPrime ω R, hR]
  exact h

/-- The uniform gauge-energy envelope is dominated by the sum of the
coordinate-direction envelopes already carrying stretched-exponential tails. -/
theorem rhsTerm3BlowupLocal_energy_le_basisEnvelopes {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (ell L : ℕ) (ω : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (R : Homogenization.TriadicCube d) :
    2 * translatedBlockNorm nu ell ω R + 2 * translatedStreamSlot nu ell L ω R ≤
      ∑ i : Fin d, blupQuadCarrier nu ell L (Homogenization.basisVec i) ω R := by
  have hslot := (translatedStreamSlot_le_basisSum hnu ell L ω R).trans
    (Finset.sum_le_sum fun i _ => translatedStreamQuadFormLower_le_nuInv_mul hnu ell L (Homogenization.basisVec i) ω R)
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast (NeZero.one_le : 1 ≤ d)
  have hb : 0 ≤ 2 * translatedBlockNorm nu ell ω R :=
    mul_nonneg (by norm_num) (Homogenization.Book.Ch02.matrixOperatorNorm_nonneg _)
  have hdim := mul_le_mul_of_nonneg_right hd hb
  simp only [one_mul] at hdim
  simp only [blupQuadCarrier, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp_rw [show ∀ i : Fin d, 2 * nu⁻¹ * translatedStreamNormSq ell L (Homogenization.basisVec i) ω R =
    2 * (nu⁻¹ * translatedStreamNormSq ell L (Homogenization.basisVec i) ω R) from fun _ => by ring]
  rw [← Finset.mul_sum]
  linarith only [hslot, hdim]

/-- The diameter-based localization scalar costs only a dimensional factor
relative to the existing center-based scalar. -/
theorem rhsTerm3BlowupLocal_diameterD_le {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (z : Homogenization.Vec d) (n ell L : ℕ) (ω : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) :
    let M := SuperdiffusionCLT.Section2.Localization.matrixOperatorNorm_diamConst d * (3 : ℝ) ^ n * SuperdiffusionCLT.Section3.ResponseFields.upperShellDerivGauge n ell L
      (SuperdiffusionCLT.Frozen.Assumptions.ShellField.translateSequence z ω)
    nu⁻¹ * M + nu⁻¹ ^ 2 * M ^ 2 ≤
      (2 * (d : ℝ)) ^ 2 * translatedIncrementD nu z n ell L ω := by
  let B := translatedIncrementOscBound z n ell L ω
  have hB : 0 ≤ B := translatedIncrementOscBound_nonneg z n ell L ω
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast (NeZero.one_le : 1 ≤ d)
  have hc : (1 : ℝ) ≤ 2 * (d : ℝ) := by linarith only [hd]
  have hcc : 2 * (d : ℝ) ≤ (2 * (d : ℝ)) ^ 2 := by
    simpa only [one_mul, pow_two] using mul_le_mul_of_nonneg_right hc (by positivity : (0 : ℝ) ≤ 2 * (d : ℝ))
  have hlin := mul_le_mul_of_nonneg_right hcc (mul_nonneg (inv_nonneg.mpr hnu.le) hB)
  have hM : SuperdiffusionCLT.Section2.Localization.matrixOperatorNorm_diamConst d * (3 : ℝ) ^ n * SuperdiffusionCLT.Section3.ResponseFields.upperShellDerivGauge n ell L
      (SuperdiffusionCLT.Frozen.Assumptions.ShellField.translateSequence z ω) = 2 * (d : ℝ) * B := by
    dsimp [B, translatedIncrementOscBound, SuperdiffusionCLT.Section2.Localization.matrixOperatorNorm_diamConst, SuperdiffusionCLT.Section3.ResponseFields.upperShellFluxConst]
    ring
  dsimp only
  rw [hM, translatedIncrementD, Real.rpow_neg (by positivity : 0 ≤ nu), Real.rpow_two, ← inv_pow]
  change nu⁻¹ * (2 * (d : ℝ) * B) + nu⁻¹ ^ 2 * (2 * (d : ℝ) * B) ^ 2 ≤
    (2 * (d : ℝ)) ^ 2 * (nu⁻¹ * B + nu⁻¹ ^ 2 * B ^ 2)
  calc
    _ = (2 * (d : ℝ)) * (nu⁻¹ * B) + (2 * (d : ℝ)) ^ 2 * (nu⁻¹ ^ 2 * B ^ 2) := by ring
    _ ≤ (2 * (d : ℝ)) ^ 2 * (nu⁻¹ * B) + (2 * (d : ℝ)) ^ 2 * (nu⁻¹ ^ 2 * B ^ 2) :=
      add_le_add hlin le_rfl
    _ = _ := by ring

/-- The printed slot bound with an explicit remainder made from the existing
coordinate-direction remainders, uniformly over all selected-scale cubes. -/
theorem rhsTerm3BlowupLocal_printedSlot_basisRemainder {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (S : SuperdiffusionCLT.Section3.Setup.ScaleSelection) (hL : S.ell ≤ S.LPrime)
    (ω : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (R : Homogenization.TriadicCube d) (hR : R.scale = (S.n : ℤ)) :
    Homogenization.Book.Ch02.matrixOperatorNorm (translatedCoarseBlock nu S.LPrime ω R - translatedCoarseBlock nu S.ell ω R) ≤
      1 * translatedBlockNorm nu S.ell ω R +
        (1 + (1 : ℝ)⁻¹) * translatedStreamSlot nu S.ell S.LPrime ω R +
        (2 * (d : ℝ)) ^ 2 * ∑ i : Fin d, blupRemainderZrem nu S.n S.ell S.LPrime (Homogenization.basisVec i) ω R := by
  have h := rhsTerm3BlowupLocal_printedSlot_cube hnu S hL ω R hR
  dsimp only at h
  refine h.trans (add_le_add le_rfl ?_)
  have hEnergy := rhsTerm3BlowupLocal_energy_le_basisEnvelopes hnu S.ell S.LPrime ω R
  have hD := rhsTerm3BlowupLocal_diameterD_le hnu (Homogenization.triadicCubeShift R) S.n S.ell S.LPrime ω
  have hB : 0 ≤ 2 * translatedBlockNorm nu S.ell ω R + 2 * translatedStreamSlot nu S.ell S.LPrime ω R :=
    add_nonneg (mul_nonneg (by norm_num) (Homogenization.Book.Ch02.matrixOperatorNorm_nonneg _))
      (mul_nonneg (by norm_num) (sq_nonneg _))
  have hD0 : 0 ≤ translatedIncrementD nu (Homogenization.triadicCubeShift R) S.n S.ell S.LPrime ω := by
    unfold translatedIncrementD
    exact add_nonneg
      (mul_nonneg (inv_nonneg.mpr hnu.le) (translatedIncrementOscBound_nonneg _ _ _ _ _))
      (mul_nonneg (Real.rpow_nonneg hnu.le _) (sq_nonneg _))
  have hmul := mul_le_mul hD hEnergy hB (mul_nonneg (sq_nonneg _) hD0)
  simpa only [blupRemainderZrem, Finset.mul_sum, mul_assoc] using hmul

/-- The direction-free remainder has a stretched-exponential tail on every cube. -/
theorem rhsTerm3BlowupLocal_basisRemainder_tail {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (hnu1 : nu ≤ 1) {P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)}
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ1V2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    (S : SuperdiffusionCLT.Section3.Setup.ScaleSelection)
    (hS : SuperdiffusionCLT.Section3.Setup.ScalesOrdering S) (R : Homogenization.TriadicCube d) :
    Homogenization.IndependentSums.IsBigO P.toMeasure
      (Homogenization.IndependentSums.gammaSigma ((1 : ℝ) / 3))
      (fun ω => (2 * (d : ℝ)) ^ 2 * ∑ i : Fin d, blupRemainderZrem nu S.n S.ell S.LPrime (Homogenization.basisVec i) ω R)
      (((2 * (d : ℝ)) ^ 2 * Homogenization.IndependentSums.gammaTriangleConst ((1 : ℝ) / 3) *
          (d : ℝ) * max 1 (blupRemainderConstAll d)) *
        nu ^ (-(3 : ℝ)) * (S.LPrime : ℝ) * 3 ^ (-((S.ell - S.n : ℕ) : ℝ))) := by
  let A := max 1 (blupRemainderConstAll d) * nu ^ (-(3 : ℝ)) * (S.LPrime : ℝ) *
    3 ^ (-((S.ell - S.n : ℕ) : ℝ))
  have hC : 0 < max 1 (blupRemainderConstAll d) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hL : (0 : ℝ) < S.LPrime := by exact_mod_cast (Nat.zero_le S.m).trans_lt hS.m_lt_LPrime
  have hA : 0 < A := mul_pos (mul_pos (mul_pos hC (Real.rpow_pos_of_pos hnu _)) hL)
    (Real.rpow_pos_of_pos (by norm_num) _)
  have hi : ∀ i : Fin d, Homogenization.IndependentSums.IsBigO P.toMeasure
      (Homogenization.IndependentSums.gammaSigma ((1 : ℝ) / 3))
      (fun ω => blupRemainderZrem nu S.n S.ell S.LPrime (Homogenization.basisVec i) ω R) A := fun i =>
    blup_tail_allCubes hnu hnu1 hPrefix
      (SuperdiffusionCLT.Section3.HighContrast.shellLawJ1_of_shellLawJ1Restriction hJ1V2)
      hJ2 hJ3 hJ4 S hS (Homogenization.basisVec i) (Homogenization.vecNormSq_basisVec i) (le_max_right _ _) R
  have hsum := Homogenization.IndependentSums.isBigO_finset_sum_of_isBigO_gammaSigma
    (s := Finset.univ) (a := fun _ : Fin d => A)
    (by norm_num : (0 : ℝ) < 1 / 3) Finset.univ_nonempty
    (fun _ _ => hA) (fun i _ => hi i)
    (fun i _ => measurable_blupRemainderZrem hnu S.n S.ell S.LPrime (Homogenization.basisVec i) R)
  have hout := hsum.const_mul (sq_nonneg (2 * (d : ℝ)))
  have hamp : (2 * (d : ℝ)) ^ 2 * (Homogenization.IndependentSums.gammaTriangleConst ((1 : ℝ) / 3) *
      ∑ _i : Fin d, A) =
      ((2 * (d : ℝ)) ^ 2 * Homogenization.IndependentSums.gammaTriangleConst ((1 : ℝ) / 3) *
        (d : ℝ) * max 1 (blupRemainderConstAll d)) *
        nu ^ (-(3 : ℝ)) * (S.LPrime : ℝ) * 3 ^ (-((S.ell - S.n : ℕ) : ℝ)) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    dsimp [A]
    ring
  rw [hamp] at hout
  exact hout

/-- The direction-free blow-up data at the printed cube scale. The pointwise
clause is proved, rather than supplied as an input. -/
theorem rhsTerm3BlowupLocal_blup_printed {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (hnu1 : nu ≤ 1) {P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)}
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ1V2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    (S : SuperdiffusionCLT.Section3.Setup.ScaleSelection)
    (hS : SuperdiffusionCLT.Section3.Setup.ScalesOrdering S)
    (e : Homogenization.Vec d) (he : Homogenization.vecNormSq e = 1)
    (w : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → Homogenization.H10Function (Homogenization.openCubeSet (Homogenization.originCube d (S.m : ℤ))))
    (hw : ∀ ω, SuperdiffusionCLT.Section3.Setup.IsDirichletResponse ω S.LPrime S.ellPrime S.m
      (SuperdiffusionCLT.Section3.Setup.testVector nu S.LPrime P S.n e) (w ω)) :
    ∃ Z : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → Homogenization.TriadicCube d → ℝ,
      (∀ R, Measurable (fun ω => Z ω R)) ∧
      (∀ R, Homogenization.IndependentSums.IsBigO P.toMeasure
        (Homogenization.IndependentSums.gammaSigma ((1 : ℝ) / 3)) (fun ω => Z ω R)
        (((2 * (d : ℝ)) ^ 2 * Homogenization.IndependentSums.gammaTriangleConst ((1 : ℝ) / 3) *
          (d : ℝ) * max 1 (blupRemainderConstAll d)) *
          nu ^ (-(3 : ℝ)) * (S.LPrime : ℝ) * 3 ^ (-((S.ell - S.n : ℕ) : ℝ)))) ∧
      (∀ ω R, R.scale = (S.n : ℤ) →
        Homogenization.Book.Ch02.matrixOperatorNorm (translatedCoarseBlock nu S.LPrime ω R - translatedCoarseBlock nu S.ell ω R) ≤
          1 * translatedBlockNorm nu S.ell ω R +
            (1 + (1 : ℝ)⁻¹) * translatedStreamSlot nu S.ell S.LPrime ω R + Z ω R) ∧
      MeasureTheory.Integrable (fun ω => weightedBlockAverage d S.n (coarseBlockScale d S) S.m
        (w ω).toH1Function.grad (Z ω)) P.toMeasure := by
  have hsq : ∀ R ∈ SuperdiffusionCLT.Section2.Estimates.Stream.largeCubeSubcubes d (coarseBlockScale d S) S.m,
      MeasureTheory.MemLp (fun ω => Homogenization.vecNormSq (Homogenization.volumeAverageVec (Homogenization.openCubeSet R) (w ω).toH1Function.grad)) 2 P.toMeasure := by
    intro R hR
    apply memLp_vecNormSq_volumeAverageVec_grad_of_containment hPrefix.dimension hnu hnu1
      hPrefix hJ1V2 hJ2 hJ3 hJ4 S hS he w hw
    rw [largeCubeSubcubes_eq_descendantsAtDepth] at hR
    exact Homogenization.openCubeSet_subset_of_mem_descendantsAtDepth hR
  let Z := fun (ω : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (R : Homogenization.TriadicCube d) =>
    (2 * (d : ℝ)) ^ 2 * ∑ i : Fin d, blupRemainderZrem nu S.n S.ell S.LPrime (Homogenization.basisVec i) ω R
  obtain ⟨hnl, hlL, hkn, hkm⟩ := blup_scales_of_ordering d hS
  refine ⟨Z, ?_, ?_, ?_, ?_⟩
  · intro R
    exact (Finset.measurable_sum _ (fun i _ =>
      measurable_blupRemainderZrem hnu S.n S.ell S.LPrime (Homogenization.basisVec i) R)).const_mul _
  · exact rhsTerm3BlowupLocal_basisRemainder_tail hnu hnu1 hPrefix hJ1V2 hJ2 hJ3 hJ4 S hS
  · intro ω R hR
    exact rhsTerm3BlowupLocal_printedSlot_basisRemainder hnu S hlL.le ω R hR
  · dsimp only [Z]
    simp_rw [weightedBlockAverage_const_mul, weightedBlockAverage_univ_sum]
    exact (MeasureTheory.integrable_finsetSum _ (fun i _ =>
      integrable_weightedBlockAverage_blupRemainderZrem hnu hnu1 hPrefix hJ2 hJ3 hJ4
        S.n S.ell S.LPrime (coarseBlockScale d S) S.m hnl hlL hkn hkm
        (Homogenization.basisVec i) (Homogenization.vecNormSq_basisVec i) w hsq)).const_mul _

/-- A dimension-only constant fixed before the section data supplies all four
printed blow-up inputs. No pointwise hypothesis remains in this surface. -/
theorem rhsTerm3BlowupLocal_blup_constantFirst (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (nu : ℝ) (_hnu : 0 < nu)
    (_hnu1 : nu ≤ 1) (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (_hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (_hJ1V2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P)
    (_hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (_hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    (_hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    (S : SuperdiffusionCLT.Section3.Setup.ScaleSelection)
    (_hS : SuperdiffusionCLT.Section3.Setup.ScalesOrdering S)
    (e : Homogenization.Vec d) (_he : Homogenization.vecNormSq e = 1)
    (w : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → Homogenization.H10Function (Homogenization.openCubeSet (Homogenization.originCube d (S.m : ℤ))))
    (_hw : ∀ ω, SuperdiffusionCLT.Section3.Setup.IsDirichletResponse ω S.LPrime S.ellPrime S.m
      (SuperdiffusionCLT.Section3.Setup.testVector nu S.LPrime P S.n e) (w ω)),
    ∃ Z : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → Homogenization.TriadicCube d → ℝ,
      (∀ R, Measurable (fun ω => Z ω R)) ∧
      (∀ R, Homogenization.IndependentSums.IsBigO P.toMeasure
        (Homogenization.IndependentSums.gammaSigma ((1 : ℝ) / 3)) (fun ω => Z ω R)
        (C *
          nu ^ (-(3 : ℝ)) * (S.LPrime : ℝ) * 3 ^ (-((S.ell - S.n : ℕ) : ℝ)))) ∧
      (∀ ω R, R.scale = (S.n : ℤ) →
        Homogenization.Book.Ch02.matrixOperatorNorm (translatedCoarseBlock nu S.LPrime ω R - translatedCoarseBlock nu S.ell ω R) ≤
          1 * translatedBlockNorm nu S.ell ω R +
            (1 + (1 : ℝ)⁻¹) * translatedStreamSlot nu S.ell S.LPrime ω R + Z ω R) ∧
      MeasureTheory.Integrable (fun ω => weightedBlockAverage d S.n (coarseBlockScale d S) S.m
        (w ω).toH1Function.grad (Z ω)) P.toMeasure := by
  let C0 := (2 * (d : ℝ)) ^ 2 * Homogenization.IndependentSums.gammaTriangleConst ((1 : ℝ) / 3) *
    (d : ℝ) * max 1 (blupRemainderConstAll d)
  refine ⟨max 1 C0, le_max_left _ _, ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hS e he w hw
  obtain ⟨Z, hm, ht, hp, hi⟩ := rhsTerm3BlowupLocal_blup_printed hnu hnu1 hPrefix hJ1V2 hJ2 hJ3 hJ4 S hS e he w hw
  refine ⟨Z, hm, fun R => (ht R).mono_scale ?_, hp, hi⟩
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) C0) (Real.rpow_nonneg hnu.le _))
      (Nat.cast_nonneg S.LPrime)) (Real.rpow_nonneg (by norm_num) _)

/-- Weighted lattice averages only consume inequalities on cubes of scale n. -/
theorem rhsTerm3BlowupLocal_weighted_mono_at_scale {d n k m : ℕ} (hnk : n ≤ k) (hkm : k ≤ m)
    (g : Homogenization.Vec d → Homogenization.Vec d) {F G : Homogenization.TriadicCube d → ℝ}
    (hFG : ∀ R, R.scale = (n : ℤ) → F R ≤ G R) :
    weightedBlockAverage d n k m g F ≤ weightedBlockAverage d n k m g G := by
  unfold weightedBlockAverage
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun R hR => ?_) (by positivity)
  refine mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun T hT => ?_) (by positivity))
    (Homogenization.vecNormSq_nonneg _)
  apply hFG T
  rw [largeCubeSubcubes_eq_descendantsAtDepth] at hR
  have hscale := Homogenization.scale_eq_sub_of_mem_descendantsAtDepth hR
  change R.scale = (m : ℤ) - ((m - k : ℕ) : ℤ) at hscale
  rw [Homogenization.scale_eq_sub_of_mem_descendantsAtDepth hT, hscale]
  omega

end SuperdiffusionCLT.Section3.Terms
