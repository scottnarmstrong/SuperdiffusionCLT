/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.NewMixing.T3Algebra
public import SuperdiffusionCLT.AKHC61.Carrier.ScalarBlocksB
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5
public import SuperdiffusionCLT.Section4.NewMixing.ScaleConstruction

/-!
# The pointwise `T_3` bound (before averaging over `z`)

This is part of the proof of
`l.new.mixing.parameterized`. Combines the block-diagonal expansion
(`T3Algebra.lean`) with the block-diagonal characterization of
`bfAhom_ell(cu_n)` under `ShellLawJ4`
(`SuperdiffusionCLT.AKHC61.Carrier.akhc_annealedBlockMatrix_originCube_eq_blockDiag`)
and a single application of the reference comparison `hRefCompare` (`e.mixing.reference.compare`,
`newMixAsm_refCompare_of_homog`), for the vector `P = P_e^sigma`, at a single
(not-yet-averaged) shift matrix `hSum = hz + h0`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.NewMixing

open Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Assumptions

noncomputable section

/-- **The pointwise `T_3` bound**, for a single shift matrix
`hz` (not yet averaged over `z`): the quadratic form
`G_{-(hz+h0)}P_e^sigma . bfAhom_ell(cu_n) . G_{-(hz+h0)}P_e^sigma` is bounded
by `2|e|^2 + 2*Cref*shomr^{-2}*gap + shomr^{-1}*shomEllStarInv*(2‖hz‖²+2‖h0‖²)`. -/
theorem newMixParam_t3Pointwise (d : ℕ) [NeZero d]
    {nu K : ℝ} (hnu : 0 < nu) (hK1 : 1 ≤ K)
    {P : MeasureTheory.ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P)
    {Cref : ℝ} (hCref1 : 1 ≤ Cref)
    {L m ell r n : ℕ}
    (hRC : |(sigmaBarInfinite nu r P)⁻¹ * sigmaBarSeq nu ell P n - 1| +
        |sigmaBarInfinite nu r P * sigmaBarStarInvSeq nu ell P n - 1| ≤
      Cref * (sigmaBarInfinite nu r P) ^ (-(2 : ℝ)) *
        (max 0 ((L : ℝ) - (m : ℝ)) + K * Real.log (L : ℝ) ^ (2 : ℝ)))
    {e : Vec d} (he : vecNormSq e ≤ 1) {sigma : ℝ} (hsigma2 : sigma ^ 2 = 1)
    {h0 : Mat d} (hh0 : matTranspose h0 = -h0) {hz : Mat d} (hzSkew : matTranspose hz = -hz) :
    blockVecDot
        (blockMatVecMul (blockG (-(hz + h0)))
          ((sigma * Real.sqrt (sigmaBarInfinite nu r P)⁻¹) • e,
            Real.sqrt (sigmaBarInfinite nu r P) • e))
        (blockMatVecMul (annealedBlockMatrix nu ell P (cubeSet (originCube d (n : ℤ))))
          (blockMatVecMul (blockG (-(hz + h0)))
            ((sigma * Real.sqrt (sigmaBarInfinite nu r P)⁻¹) • e,
              Real.sqrt (sigmaBarInfinite nu r P) • e))) ≤
      2 * vecNormSq e +
        2 * Cref * (sigmaBarInfinite nu r P) ^ (-(2 : ℝ)) *
          (max 0 ((L : ℝ) - (m : ℝ)) + K * Real.log (L : ℝ) ^ (2 : ℝ)) +
        (sigmaBarInfinite nu r P)⁻¹ * sigmaBarStarInvSeq nu ell P n *
          (2 * matrixOperatorNorm hz ^ 2 + 2 * matrixOperatorNorm h0 ^ 2) := by
  set shomr := sigmaBarInfinite nu r P with hshomrdef
  have hshomr : 0 < shomr := sigmaBarInfinite_pos hnu r hPrefix hJ2 hJ3 hJ4
  set shomEll := sigmaBarSeq nu ell P n with hshomElldef
  set shomEllStarInv := sigmaBarStarInvSeq nu ell P n with hshomEllSIdef
  have hshomEllSIpos : 0 < shomEllStarInv :=
    sigmaBarStarInvSeq_pos hnu ell hPrefix hJ2 hJ3 hJ4 n
  set G := Cref * shomr ^ (-(2 : ℝ)) *
      (max 0 ((L : ℝ) - (m : ℝ)) + K * Real.log (L : ℝ) ^ (2 : ℝ)) with hGdef
  set c := sigma * Real.sqrt shomr⁻¹ with hcdef
  set s := Real.sqrt shomr with hsdef
  have hc2 : c ^ 2 = shomr⁻¹ := by
    rw [hcdef, mul_pow, hsigma2, one_mul, Real.sq_sqrt (inv_nonneg.mpr hshomr.le)]
  have hs2 : s ^ 2 = shomr := by rw [hsdef, Real.sq_sqrt hshomr.le]
  have hSumSkew : matTranspose (hz + h0) = -(hz + h0) := by
    have hzij : ∀ i j, hz i j = -(hz j i) := fun i j => by
      have := congrFun (congrFun hzSkew j) i
      simpa [matTranspose, Matrix.transpose_apply] using this
    have hh0ij : ∀ i j, h0 i j = -(h0 j i) := fun i j => by
      have := congrFun (congrFun hh0 j) i
      simpa [matTranspose, Matrix.transpose_apply] using this
    ext i j
    simp only [matTranspose, Matrix.transpose_apply, Matrix.add_apply, Matrix.neg_apply,
      hzij i j, hh0ij i j]
    ring
  have hexpand := newMixParam_blockQuad_expand (a := shomEll) (b := shomEllStarInv)
    (c := c) (s := s) (e := e) (hSum := hz + h0) hSumSkew
  rw [hc2, hs2] at hexpand
  have hbd : annealedBlockMatrix nu ell P (cubeSet (originCube d (n : ℤ))) =
      Book.Ch02.blockDiag (shomEll • (1 : Mat d)) (shomEllStarInv • (1 : Mat d)) :=
    SuperdiffusionCLT.AKHC61.Carrier.akhc_annealedBlockMatrix_originCube_eq_blockDiag
      hnu ell hJ4 (n : ℤ)
  show blockVecDot (blockMatVecMul (blockG (-(hz + h0))) (c • e, s • e))
      (blockMatVecMul (annealedBlockMatrix nu ell P (cubeSet (originCube d (n : ℤ))))
        (blockMatVecMul (blockG (-(hz + h0))) (c • e, s • e))) ≤ _
  rw [hbd, hexpand]
  have hnn_e : (0 : ℝ) ≤ vecNormSq e := vecNormSq_nonneg e
  have hnn_shomrinv : (0 : ℝ) ≤ shomr⁻¹ := inv_nonneg.mpr hshomr.le
  have hnn_G : (0 : ℝ) ≤ G := by
    have h1 : (0 : ℝ) ≤ Cref := le_trans zero_le_one hCref1
    have h2 : (0 : ℝ) ≤ shomr ^ (-(2 : ℝ)) := Real.rpow_nonneg hshomr.le _
    have h3 : (0 : ℝ) ≤ max 0 ((L : ℝ) - (m : ℝ)) + K * Real.log (L : ℝ) ^ (2 : ℝ) := by
      have hmax0 : (0 : ℝ) ≤ max 0 ((L : ℝ) - (m : ℝ)) := le_max_left _ _
      have hKnn : (0 : ℝ) ≤ K := le_trans zero_le_one hK1
      have hlognn : (0 : ℝ) ≤ Real.log (L : ℝ) ^ (2 : ℝ) := Real.rpow_nonneg (by positivity) _
      have := mul_nonneg hKnn hlognn
      linarith only [hmax0, this]
    rw [hGdef]
    exact mul_nonneg (mul_nonneg h1 h2) h3
  have hratio1 : shomr⁻¹ * shomEll ≤ 1 + G := by
    have hnn : (0 : ℝ) ≤ |shomr * shomEllStarInv - 1| := abs_nonneg _
    have h1 : |shomr⁻¹ * shomEll - 1| ≤ G := by rw [hGdef]; linarith only [hRC, hnn]
    linarith only [(abs_le.mp h1).2]
  have hratio2 : shomr * shomEllStarInv ≤ 1 + G := by
    have hnn : (0 : ℝ) ≤ |shomr⁻¹ * shomEll - 1| := abs_nonneg _
    have h1 : |shomr * shomEllStarInv - 1| ≤ G := by rw [hGdef]; linarith only [hRC, hnn]
    linarith only [(abs_le.mp h1).2]
  -- Terms 1+2: `shomEll*shomr⁻¹*|e|² + shomEllStarInv*shomr*|e|² ≤ 2|e|² + 2G`.
  have hstepA : shomEll * shomr⁻¹ * vecNormSq e + shomEllStarInv * shomr * vecNormSq e ≤
      2 * vecNormSq e + 2 * G := by
    have h1 : shomEll * shomr⁻¹ * vecNormSq e ≤ (1 + G) * vecNormSq e := by
      have heq : shomEll * shomr⁻¹ = shomr⁻¹ * shomEll := by ring
      rw [heq]
      exact mul_le_mul_of_nonneg_right hratio1 hnn_e
    have h2 : shomEllStarInv * shomr * vecNormSq e ≤ (1 + G) * vecNormSq e := by
      have heq : shomEllStarInv * shomr = shomr * shomEllStarInv := by ring
      rw [heq]
      exact mul_le_mul_of_nonneg_right hratio2 hnn_e
    have h3 : (1 + G) * vecNormSq e + (1 + G) * vecNormSq e ≤ 2 * vecNormSq e + 2 * G := by
      nlinarith only [he, hnn_G, hnn_e]
    linarith only [h1, h2, h3]
  -- Term 3: `shomEllStarInv*shomr⁻¹*|hSum e|² ≤ shomEllStarInv*shomr⁻¹*(2‖hz‖²+2‖h0‖²)`.
  have hstepB : shomEllStarInv * shomr⁻¹ * vecNormSq (matVecMul (hz + h0) e) ≤
      shomEllStarInv * shomr⁻¹ * (2 * matrixOperatorNorm hz ^ 2 + 2 * matrixOperatorNorm h0 ^ 2) := by
    have hcoefnn : (0 : ℝ) ≤ shomEllStarInv * shomr⁻¹ := mul_nonneg hshomEllSIpos.le hnn_shomrinv
    have h1 : vecNormSq (matVecMul (hz + h0) e) ≤ matrixOperatorNorm (hz + h0) ^ 2 * vecNormSq e :=
      newMixParam_vecNormSq_matVecMul_le (hz + h0) e
    have h2 : matrixOperatorNorm (hz + h0) ^ 2 * vecNormSq e ≤ matrixOperatorNorm (hz + h0) ^ 2 := by
      have hnn3 : (0 : ℝ) ≤ matrixOperatorNorm (hz + h0) ^ 2 := by positivity
      nlinarith only [he, hnn3]
    have h3 : matrixOperatorNorm (hz + h0) ^ 2 ≤
        2 * matrixOperatorNorm hz ^ 2 + 2 * matrixOperatorNorm h0 ^ 2 :=
      newMixParam_matrixOperatorNorm_add_sq_le hz h0
    have h4 : vecNormSq (matVecMul (hz + h0) e) ≤
        2 * matrixOperatorNorm hz ^ 2 + 2 * matrixOperatorNorm h0 ^ 2 := by
      linarith only [h1, h2, h3]
    exact mul_le_mul_of_nonneg_left h4 hcoefnn
  linarith only [hstepA, hstepB]

end
end SuperdiffusionCLT.Section4.NewMixing
