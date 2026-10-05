/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.NewMixing.MomentBoundWired
public import SuperdiffusionCLT.Section4.NewMixing.T3Bound

/-!
# The energy bound with `X1` chosen before the skew shift

The witness `X1` does not depend on `h0`; the `T_0` term enters through a fixed random variable `Z`
multiplied by `1 + shom⁻¹ ‖h0‖²`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.NewMixing

open Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Frozen.Assumptions

noncomputable section

/-- **`l.new.mixing.parameterized#main-bound`** `T_0` bound
supplied generically as `hXT0BigO`/`hT0bound` (the shape both
`newMixAsm_t0Strong_branchA` and `newMixAsm_t0Strong_branchB` produce), and the residual
`shom_r shom_{ell,*}^{-1}(cu_n) ≤ Cratio` display carried as the
explicit hypothesis `hRatio` (see the module docstring). -/
theorem newMixAsm_mainBound_uniform2 (d : ℕ) [NeZero d]
    {nu K Cref Cratio C' : ℝ} (hnu : 0 < nu) (hK1 : 1 ≤ K)
    {P : MeasureTheory.ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P)
    (hCref1 : 1 ≤ Cref)
    {L m ell r n : ℕ} (hnm : n ≤ m) (hellL : ell ≤ L)
    (hRC : |(sigmaBarInfinite nu r P)⁻¹ * sigmaBarSeq nu ell P n - 1| +
        |sigmaBarInfinite nu r P * sigmaBarStarInvSeq nu ell P n - 1| ≤
      Cref * (sigmaBarInfinite nu r P) ^ (-(2 : ℝ)) *
        (max 0 ((L : ℝ) - (m : ℝ)) + K * Real.log (L : ℝ) ^ (2 : ℝ)))
    (hCratio0 : 0 ≤ Cratio)
    (hRatio : sigmaBarInfinite nu r P * sigmaBarStarInvSeq nu ell P n ≤ Cratio)
    (hC'1 : 1 ≤ C')
    (hgap : (L : ℝ) - (ell : ℝ) ≤ max 0 ((L : ℝ) - (m : ℝ)) + C' * K * Real.log (L : ℝ))
    {C : ℝ}
    (hCa : Cratio * 2 * (d : ℝ) ^ 2 * finiteShellIncrementPthMomentConst d 2 ^ (2 : ℝ) * C' ≤ C)
    (hCc : 2 * Cref + 2 * Cratio ≤ C)
    {Z : ShellSeq d → ℝ}
    (hT0bound : ∀ (h0 : Mat d) (hh0 : matTranspose h0 = -h0),
      ∀ e : Vec d, vecNormSq e ≤ 1 → ∀ sigma : ℝ, sigma ^ 2 = 1 →
      ∀ omega : ShellSeq d,
      blockVecDot
          ((sigma * Real.sqrt (sigmaBarInfinite nu r P)⁻¹) • e,
            Real.sqrt (sigmaBarInfinite nu r P) • e)
          (blockMatVecMul
            (Homogenization.Book.Ch02.coarseBlockMatrix (Homogenization.Book.Ch02.cubeDomain (originCube d (m : ℤ)))
              (newMixParam_aLplusH0 nu hnu omega L m h0 hh0))
            ((sigma * Real.sqrt (sigmaBarInfinite nu r P)⁻¹) • e,
              Real.sqrt (sigmaBarInfinite nu r P) • e)) ≤
        (1 + (sigmaBarInfinite nu r P)⁻¹ * matrixOperatorNorm h0 ^ 2) * Z omega +
          Homogenization.descendantsAverage (originCube d (m : ℤ)) (m - n)
            (fun R => blockVecDot
              (blockMatVecMul
                (blockG (-(Homogenization.volumeAverageMat (cubeSet R)
                      (fun y => finiteShellIncrement omega ell L y) + h0)))
                ((sigma * Real.sqrt (sigmaBarInfinite nu r P)⁻¹) • e,
                  Real.sqrt (sigmaBarInfinite nu r P) • e))
              (blockMatVecMul (annealedBlockMatrix nu ell P (cubeSet (originCube d (n : ℤ))))
                (blockMatVecMul
                  (blockG (-(Homogenization.volumeAverageMat (cubeSet R)
                        (fun y => finiteShellIncrement omega ell L y) + h0)))
                  ((sigma * Real.sqrt (sigmaBarInfinite nu r P)⁻¹) • e,
                    Real.sqrt (sigmaBarInfinite nu r P) • e))))) :
    ∃ X1 : ShellSeq d → ℝ, Measurable X1 ∧
        Homogenization.IndependentSums.IsBigO P.toMeasure
            (Homogenization.IndependentSums.gammaSigma 1) X1
            (C * (sigmaBarInfinite nu r P) ^ (-(2 : ℝ)) *
              (max 0 ((L : ℝ) - (m : ℝ)) + K * Real.log (L : ℝ))) ∧
        ∀ (h0 : Mat d) (hh0 : matTranspose h0 = -h0),
        ∀ e : Vec d, vecNormSq e ≤ 1 → ∀ sigma : ℝ, sigma ^ 2 = 1 →
        ∀ omega : ShellSeq d,
          blockVecDot
              ((sigma * Real.sqrt (sigmaBarInfinite nu r P)⁻¹) • e,
                Real.sqrt (sigmaBarInfinite nu r P) • e)
              (blockMatVecMul
                (Homogenization.Book.Ch02.coarseBlockMatrix (Homogenization.Book.Ch02.cubeDomain (originCube d (m : ℤ)))
                  (newMixParam_aLplusH0 nu hnu omega L m h0 hh0))
                ((sigma * Real.sqrt (sigmaBarInfinite nu r P)⁻¹) • e,
                  Real.sqrt (sigmaBarInfinite nu r P) • e)) ≤
            2 * vecNormSq e +
              C * (sigmaBarInfinite nu r P) ^ (-(2 : ℝ)) *
                (matrixOperatorNorm h0 ^ 2 + max 0 ((L : ℝ) - (m : ℝ)) +
                  K * Real.log (L : ℝ) ^ (2 : ℝ)) +
              X1 omega +
              (1 + (sigmaBarInfinite nu r P)⁻¹ * matrixOperatorNorm h0 ^ 2) * Z omega := by
  set shomr := sigmaBarInfinite nu r P with hshomrdef
  have hshomr : 0 < shomr := sigmaBarInfinite_pos hnu r hPrefix hJ2 hJ3 hJ4
  set shomEllStarInv := sigmaBarStarInvSeq nu ell P n with hshomEllSIdef
  have hshomEllSIpos : 0 < shomEllStarInv :=
    sigmaBarStarInvSeq_pos hnu ell hPrefix hJ2 hJ3 hJ4 n
  have hshomrneg2nn : (0 : ℝ) ≤ shomr ^ (-(2 : ℝ)) := Real.rpow_nonneg hshomr.le _
  -- `shomr ^ (-(2:ℝ)) = shomr⁻¹ * shomr⁻¹`.
  have hrpow2 : shomr ^ (-(2 : ℝ)) = shomr⁻¹ * shomr⁻¹ := by
    rw [Real.rpow_neg hshomr.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      pow_two, mul_inv]
  -- The residual display: `shomr⁻¹ * shomEllStarInv ≤ Cratio * shomr ^ (-(2:ℝ))`.
  have hratio_inv : shomr⁻¹ * shomEllStarInv ≤ Cratio * shomr ^ (-(2 : ℝ)) := by
    rw [hrpow2]
    have hnn : (0 : ℝ) ≤ shomr⁻¹ * shomr⁻¹ := mul_nonneg (inv_nonneg.mpr hshomr.le)
      (inv_nonneg.mpr hshomr.le)
    have hmul := mul_le_mul_of_nonneg_left hRatio hnn
    calc shomr⁻¹ * shomEllStarInv = shomr⁻¹ * shomr⁻¹ * (shomr * shomEllStarInv) := by
          field_simp
      _ ≤ shomr⁻¹ * shomr⁻¹ * Cratio := hmul
      _ = Cratio * (shomr⁻¹ * shomr⁻¹) := by ring
  -- Nonnegativity of the printed log-amplitudes (`L : ℕ`, so `Real.log L ≥ 0`).
  have hlogLnn : (0 : ℝ) ≤ Real.log (L : ℝ) := Real.log_natCast_nonneg L
  have hgapnn : (0 : ℝ) ≤ max 0 ((L : ℝ) - (m : ℝ)) + K * Real.log (L : ℝ) := by
    have h1 : (0 : ℝ) ≤ max 0 ((L : ℝ) - (m : ℝ)) := le_max_left _ _
    have h2 : (0 : ℝ) ≤ K * Real.log (L : ℝ) := mul_nonneg (le_trans zero_le_one hK1) hlogLnn
    linarith only [h1, h2]
  have hgapnn' : (0 : ℝ) ≤ max 0 ((L : ℝ) - (m : ℝ)) + C' * K * Real.log (L : ℝ) := by
    have h1 : (0 : ℝ) ≤ max 0 ((L : ℝ) - (m : ℝ)) := le_max_left _ _
    have h2 : (0 : ℝ) ≤ C' * K * Real.log (L : ℝ) :=
      mul_nonneg (mul_nonneg (le_trans zero_le_one hC'1) (le_trans zero_le_one hK1)) hlogLnn
    linarith only [h1, h2]
  have hgap_le : max 0 ((L : ℝ) - (m : ℝ)) + C' * K * Real.log (L : ℝ) ≤
      C' * (max 0 ((L : ℝ) - (m : ℝ)) + K * Real.log (L : ℝ)) := by
    have h1 : max 0 ((L : ℝ) - (m : ℝ)) ≤ C' * max 0 ((L : ℝ) - (m : ℝ)) :=
      le_mul_of_one_le_left (le_max_left _ _) hC'1
    have h2 : C' * (max 0 ((L : ℝ) - (m : ℝ)) + K * Real.log (L : ℝ)) =
        C' * max 0 ((L : ℝ) - (m : ℝ)) + C' * K * Real.log (L : ℝ) := by ring
    rw [h2]; linarith only [h1]
  -- The `k_L - k_ell` moment bound, wired to the printed gap shape.
  obtain ⟨Xmom, hXmomMeas, hXmomBigO, hXmomDom⟩ :=
    newMixParam_kLkEllMomentBoundWired hPrefix hJ2 hJ3 hJ4 hellL hgap
  have hAmomCoeffnn : (0 : ℝ) ≤ finiteShellIncrementPthMomentConst d 2 ^ (2 : ℝ) :=
    Real.rpow_nonneg (finiteShellIncrementPthMomentConst_nonneg d (p := (2 : ℝ)) (by norm_num)) _
  set coef : ℝ := shomr⁻¹ * shomEllStarInv * 2 * (d : ℝ) ^ 2 with hcoefdef
  have hcoefnn : (0 : ℝ) ≤ coef := by
    have h1 : (0 : ℝ) ≤ shomr⁻¹ := inv_nonneg.mpr hshomr.le
    have h2 : (0 : ℝ) ≤ shomEllStarInv := hshomEllSIpos.le
    have h3 : (0 : ℝ) ≤ (2 : ℝ) * (d : ℝ) ^ 2 := by positivity
    rw [hcoefdef]
    calc (0 : ℝ) ≤ shomr⁻¹ * shomEllStarInv * (2 * (d : ℝ) ^ 2) := by
          exact mul_nonneg (mul_nonneg h1 h2) h3
      _ = shomr⁻¹ * shomEllStarInv * 2 * (d : ℝ) ^ 2 := by ring
  set X1 : ShellSeq d → ℝ := fun omega => coef * Xmom omega with hX1def
  have hX1meas : Measurable X1 := hXmomMeas.const_mul _
  have hX1BigO0 : Homogenization.IndependentSums.IsBigO P.toMeasure
      (Homogenization.IndependentSums.gammaSigma 1) X1
      (coef * (finiteShellIncrementPthMomentConst d 2 ^ (2 : ℝ) *
        (max 0 ((L : ℝ) - (m : ℝ)) + C' * K * Real.log (L : ℝ)))) :=
    hXmomBigO.const_mul hcoefnn
  -- The shared final constant.
  set C1 : ℝ := Cratio * 2 * (d : ℝ) ^ 2 * finiteShellIncrementPthMomentConst d 2 ^ (2 : ℝ) * C'
    with hC1def
  have hC1nn : (0 : ℝ) ≤ C1 := by
    rw [hC1def]
    have h3 : (0 : ℝ) ≤ (2 : ℝ) * (d : ℝ) ^ 2 := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCratio0 (by norm_num : (0:ℝ) ≤ 2))
      (by positivity : (0:ℝ) ≤ (d:ℝ)^2)) hAmomCoeffnn) (le_trans zero_le_one hC'1)
  set C3 : ℝ := 2 * Cref + 2 * Cratio with hC3def
  have hC3nn : (0 : ℝ) ≤ C3 := by
    rw [hC3def]
    have h1 : (0:ℝ) ≤ 2 * Cref := mul_nonneg (by norm_num) (le_trans zero_le_one hCref1)
    have h2 : (0:ℝ) ≤ 2 * Cratio := mul_nonneg (by norm_num) hCratio0
    linarith only [h1, h2]
  have hC3_le_C : C3 ≤ C := hCc
  have hC1_le_C : C1 ≤ C := hCa
  have hC2Cref_le_C : 2 * Cref ≤ C := by
    have h1 : (0:ℝ) ≤ 2 * Cratio := mul_nonneg (by norm_num) hCratio0
    have h2 : 2 * Cref ≤ C3 := by rw [hC3def]; linarith only [h1]
    exact le_trans h2 hC3_le_C
  have hC2Cratio_le_C : 2 * Cratio ≤ C := by
    have h1 : (0:ℝ) ≤ 2 * Cref := mul_nonneg (by norm_num) (le_trans zero_le_one hCref1)
    have h2 : 2 * Cratio ≤ C3 := by rw [hC3def]; linarith only [h1]
    exact le_trans h2 hC3_le_C
  refine ⟨X1, hX1meas, ?_, ?_⟩
  · -- `X1`'s `IsBigO` bound, upgraded to the shared `C`.
    refine hX1BigO0.mono_scale ?_
    calc coef * (finiteShellIncrementPthMomentConst d 2 ^ (2 : ℝ) *
          (max 0 ((L : ℝ) - (m : ℝ)) + C' * K * Real.log (L : ℝ)))
        = (shomr⁻¹ * shomEllStarInv) * (2 * (d : ℝ) ^ 2) *
            (finiteShellIncrementPthMomentConst d 2 ^ (2 : ℝ) *
              (max 0 ((L : ℝ) - (m : ℝ)) + C' * K * Real.log (L : ℝ))) := by
          rw [hcoefdef]; ring
      _ ≤ (Cratio * shomr ^ (-(2 : ℝ))) * (2 * (d : ℝ) ^ 2) *
            (finiteShellIncrementPthMomentConst d 2 ^ (2 : ℝ) *
              (C' * (max 0 ((L : ℝ) - (m : ℝ)) + K * Real.log (L : ℝ)))) := by
          have h1 : (shomr⁻¹ * shomEllStarInv) * (2 * (d : ℝ) ^ 2) ≤
              (Cratio * shomr ^ (-(2 : ℝ))) * (2 * (d : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_right hratio_inv (by positivity)
          have h2 : finiteShellIncrementPthMomentConst d 2 ^ (2 : ℝ) *
              (max 0 ((L : ℝ) - (m : ℝ)) + C' * K * Real.log (L : ℝ)) ≤
              finiteShellIncrementPthMomentConst d 2 ^ (2 : ℝ) *
                (C' * (max 0 ((L : ℝ) - (m : ℝ)) + K * Real.log (L : ℝ))) :=
            mul_le_mul_of_nonneg_left hgap_le hAmomCoeffnn
          have hB : (0 : ℝ) ≤ finiteShellIncrementPthMomentConst d 2 ^ (2 : ℝ) *
              (max 0 ((L : ℝ) - (m : ℝ)) + C' * K * Real.log (L : ℝ)) :=
            mul_nonneg hAmomCoeffnn hgapnn'
          have hA' : (0 : ℝ) ≤ (Cratio * shomr ^ (-(2 : ℝ))) * (2 * (d : ℝ) ^ 2) :=
            mul_nonneg (mul_nonneg hCratio0 hshomrneg2nn) (by positivity)
          exact mul_le_mul h1 h2 hB hA'
      _ = C1 * shomr ^ (-(2 : ℝ)) * (max 0 ((L : ℝ) - (m : ℝ)) + K * Real.log (L : ℝ)) := by
          rw [hC1def]; ring
      _ ≤ C * shomr ^ (-(2 : ℝ)) * (max 0 ((L : ℝ) - (m : ℝ)) + K * Real.log (L : ℝ)) := by
          have hnn : (0 : ℝ) ≤ shomr ^ (-(2 : ℝ)) * (max 0 ((L : ℝ) - (m : ℝ)) +
              K * Real.log (L : ℝ)) := mul_nonneg hshomrneg2nn hgapnn
          have := mul_le_mul_of_nonneg_right hC1_le_C hnn
          linarith only [this]
  · intro h0 hh0 e he sigma hsigma2 omega
    have hT3 := newMixParam_t3Bound d hnu hK1 hPrefix hJ2 hJ3 hJ4 hCref1 hnm hRC he hsigma2 hh0
      omega
    rw [← hshomrdef, ← hshomEllSIdef] at hT3
    have hT0 := hT0bound h0 hh0 e he sigma hsigma2 omega
    have hXm := hXmomDom omega
    set Jensen : ℝ := Homogenization.volumeAverage (cubeSet (originCube d (m : ℤ)))
      (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ (2 : ℝ))
      with hJensendef
    have hstep1 :
        shomr⁻¹ * shomEllStarInv * (2 * (d : ℝ) ^ 2 * Jensen + 2 * matrixOperatorNorm h0 ^ 2) =
          coef * Jensen + shomr⁻¹ * shomEllStarInv * 2 * matrixOperatorNorm h0 ^ 2 := by
      rw [hcoefdef]; ring
    have hcoefJensen_le : coef * Jensen ≤ X1 omega := by
      show coef * Jensen ≤ coef * Xmom omega
      exact mul_le_mul_of_nonneg_left hXm hcoefnn
    have hh0term_le : shomr⁻¹ * shomEllStarInv * 2 * matrixOperatorNorm h0 ^ 2 ≤
        C * shomr ^ (-(2 : ℝ)) * matrixOperatorNorm h0 ^ 2 := by
      have hstep : shomr⁻¹ * shomEllStarInv * 2 * matrixOperatorNorm h0 ^ 2 =
          (shomr⁻¹ * shomEllStarInv) * (2 * matrixOperatorNorm h0 ^ 2) := by ring
      rw [hstep]
      have h1 : (shomr⁻¹ * shomEllStarInv) * (2 * matrixOperatorNorm h0 ^ 2) ≤
          (Cratio * shomr ^ (-(2 : ℝ))) * (2 * matrixOperatorNorm h0 ^ 2) :=
        mul_le_mul_of_nonneg_right hratio_inv (by positivity)
      have h2 : (Cratio * shomr ^ (-(2 : ℝ))) * (2 * matrixOperatorNorm h0 ^ 2) ≤
          C * shomr ^ (-(2 : ℝ)) * matrixOperatorNorm h0 ^ 2 := by
        have heq : (Cratio * shomr ^ (-(2 : ℝ))) * (2 * matrixOperatorNorm h0 ^ 2) =
            (2 * Cratio) * (shomr ^ (-(2 : ℝ)) * matrixOperatorNorm h0 ^ 2) := by ring
        rw [heq]
        have hnn : (0 : ℝ) ≤ shomr ^ (-(2 : ℝ)) * matrixOperatorNorm h0 ^ 2 :=
          mul_nonneg hshomrneg2nn (sq_nonneg _)
        have := mul_le_mul_of_nonneg_right hC2Cratio_le_C hnn
        linarith only [this]
      linarith only [h1, h2]
    have hdetterm_le :
        2 * Cref * shomr ^ (-(2 : ℝ)) * (max 0 ((L : ℝ) - (m : ℝ)) + K * Real.log (L : ℝ) ^ (2 : ℝ)) ≤
          C * shomr ^ (-(2 : ℝ)) * (max 0 ((L : ℝ) - (m : ℝ)) + K * Real.log (L : ℝ) ^ (2 : ℝ)) := by
      have hnn : (0 : ℝ) ≤ shomr ^ (-(2 : ℝ)) *
          (max 0 ((L : ℝ) - (m : ℝ)) + K * Real.log (L : ℝ) ^ (2 : ℝ)) := by
        have h1 : (0:ℝ) ≤ max 0 ((L : ℝ) - (m : ℝ)) := le_max_left _ _
        have h2 : (0:ℝ) ≤ K * Real.log (L : ℝ) ^ (2 : ℝ) :=
          mul_nonneg (le_trans zero_le_one hK1) (Real.rpow_nonneg hlogLnn _)
        exact mul_nonneg hshomrneg2nn (by linarith only [h1, h2])
      have := mul_le_mul_of_nonneg_right hC2Cref_le_C hnn
      linarith only [this]
    have hRHS_eq : C * shomr ^ (-(2 : ℝ)) *
        (matrixOperatorNorm h0 ^ 2 + max 0 ((L : ℝ) - (m : ℝ)) + K * Real.log (L : ℝ) ^ (2 : ℝ)) =
        C * shomr ^ (-(2 : ℝ)) * matrixOperatorNorm h0 ^ 2 +
          C * shomr ^ (-(2 : ℝ)) *
            (max 0 ((L : ℝ) - (m : ℝ)) + K * Real.log (L : ℝ) ^ (2 : ℝ)) := by ring
    linarith only [hT0, hT3, hstep1, hcoefJensen_le, hh0term_le, hdetterm_le, hRHS_eq]

end
end SuperdiffusionCLT.Section4.NewMixing
