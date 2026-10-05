/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.NewMixing.AssemblyMainB
public import SuperdiffusionCLT.Section4.NewMixing.AssemblyMainUniform2

/-!
# The assembly at fixed parameters, uniform in the skew shift

The assembly at fixed parameters, in which the witnesses `X1, X2` are chosen before `h0`.
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

/-- Folding the quadratic prefactor into `m^{-5000}`. -/
theorem newMixAsm_vFold5000 {Cv C3 Cenv nu m L r : ℝ} (hCv : 0 ≤ Cv) (hC3 : 0 ≤ C3)
    (hCenv : 0 ≤ Cenv) (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (hm1 : 1 ≤ m) (hL : L ≤ 2 * m) (hr : r ≤ 2 * L) (hr0 : 0 ≤ r)
    (hnu4 : nu ^ (-(4 : ℝ)) ≤ C3 * L) :
    (Cv * nu⁻¹ * (1 + r) + 1) * (Cenv * m ^ (-(6000 : ℝ))) ≤
      (Cenv * (10 * Cv * C3 + 1)) * m ^ (-(5000 : ℝ)) := by
  have hmpos : 0 < m := lt_of_lt_of_le one_pos hm1
  have hL0 : 0 ≤ L := by linarith only [hr, hr0, hL, hm1]
  have hinv : nu⁻¹ ≤ C3 * L := le_trans (newMixAsm_inv_le_rpow_neg_four hnu hnu1) hnu4
  have hprod : nu⁻¹ * (1 + r) ≤ 10 * C3 * m ^ 2 := by
    have h1 : nu⁻¹ ≤ C3 * (2 * m) :=
      le_trans hinv (mul_le_mul_of_nonneg_left hL hC3)
    have h2 : 1 + r ≤ 5 * m := by linarith only [hr, hL, hm1]
    calc nu⁻¹ * (1 + r) ≤ (C3 * (2 * m)) * (5 * m) :=
          mul_le_mul h1 h2 (by linarith only [hr0]) (by positivity)
      _ = 10 * C3 * m ^ 2 := by ring
  have ha : 0 ≤ m ^ (-(6000 : ℝ)) := Real.rpow_nonneg hmpos.le _
  have hb : 0 ≤ m ^ (-(5000 : ℝ)) := Real.rpow_nonneg hmpos.le _
  have hsq' : m ^ (-(6000 : ℝ)) * m ^ 2 ≤ m ^ (-(5000 : ℝ)) :=
    by
      rw [show m ^ 2 = m ^ (2 : ℝ) from (Real.rpow_two m).symm, ← Real.rpow_add hmpos]
      exact Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
  have hab : m ^ (-(6000 : ℝ)) ≤ m ^ (-(5000 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
  have h1 : Cv * nu⁻¹ * (1 + r) * m ^ (-(6000 : ℝ)) ≤ 10 * Cv * C3 * m ^ (-(5000 : ℝ)) := by
    have h2 := mul_le_mul_of_nonneg_left hprod hCv
    have h3 := mul_le_mul_of_nonneg_right h2 ha
    have h4 := mul_le_mul_of_nonneg_left hsq' (by positivity : 0 ≤ 10 * Cv * C3)
    nlinarith only [h3, h4]
  have h5 : (Cv * nu⁻¹ * (1 + r) + 1) * (Cenv * m ^ (-(6000 : ℝ))) =
      Cenv * (Cv * nu⁻¹ * (1 + r) * m ^ (-(6000 : ℝ)) + m ^ (-(6000 : ℝ))) := by ring
  rw [h5]
  have h6 : Cv * nu⁻¹ * (1 + r) * m ^ (-(6000 : ℝ)) + m ^ (-(6000 : ℝ)) ≤
      (10 * Cv * C3 + 1) * m ^ (-(5000 : ℝ)) := by linarith only [h1, hab]
  have := mul_le_mul_of_nonneg_left h6 hCenv
  linarith only [this]

/-- **The assembly at fixed parameters, uniform in `h0`.** -/
theorem newMixAsm_fixed_uniform (d : ℕ) [NeZero d]
    {nu K Cref Cratio Cs Cenv Cv C3 C : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hK1 : 1 ≤ K)
    {P : MeasureTheory.ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (hCref1 : 1 ≤ Cref)
    {L m ell r n : ℕ} (hnm : n ≤ m) (hellL : ell ≤ L)
    (hRC : |(sigmaBarInfinite nu r P)⁻¹ * sigmaBarSeq nu ell P n - 1| +
        |sigmaBarInfinite nu r P * sigmaBarStarInvSeq nu ell P n - 1| ≤
      Cref * (sigmaBarInfinite nu r P) ^ (-(2 : ℝ)) *
        (max 0 ((L : ℝ) - (m : ℝ)) + K * Real.log (L : ℝ) ^ (2 : ℝ)))
    (hCratio0 : 0 ≤ Cratio)
    (hRatio : sigmaBarInfinite nu r P * sigmaBarStarInvSeq nu ell P n ≤ Cratio)
    (hCs1 : 1 ≤ Cs)
    (hgap : (L : ℝ) - (ell : ℝ) ≤ max 0 ((L : ℝ) - (m : ℝ)) + Cs * K * Real.log (L : ℝ))
    (hCenv0 : 0 ≤ Cenv) (hCv0 : 0 ≤ Cv) (hC30 : 0 ≤ C3)
    (hm1 : (1 : ℝ) ≤ (m : ℝ)) (hL2m : (L : ℝ) ≤ 2 * (m : ℝ)) (hr2L : (r : ℝ) ≤ 2 * (L : ℝ))
    (hnu4 : nu ^ (-(4 : ℝ)) ≤ C3 * (L : ℝ))
    (hCa : Cratio * 2 * (d : ℝ) ^ 2 * finiteShellIncrementPthMomentConst d 2 ^ (2 : ℝ) * Cs ≤ C)
    (hCb : Cenv * (10 * Cv * C3 + 1) ≤ C) (hCc : 2 * Cref + 2 * Cratio ≤ C)
    (hVb : ∀ (h0 : Mat d), matTranspose h0 = -h0 → ∀ e : Vec d, vecNormSq e ≤ 1 → ∀ sigma : ℝ, sigma ^ 2 = 1 →
      blockVecDot
          (blockMatVecMul (blockG (-h0))
            ((sigma * Real.sqrt (sigmaBarInfinite nu r P)⁻¹) • e,
              Real.sqrt (sigmaBarInfinite nu r P) • e))
          (blockMatVecMul (blockG (-h0))
            ((sigma * Real.sqrt (sigmaBarInfinite nu r P)⁻¹) • e,
              Real.sqrt (sigmaBarInfinite nu r P) • e)) ≤
        Cv * nu⁻¹ * (1 + (r : ℝ)) + (sigmaBarInfinite nu r P)⁻¹ * matrixOperatorNorm h0 ^ 2)
    {X0 : ShellSeq d → ℝ} (hX0meas : Measurable X0)
    (hX0BigO : Homogenization.IndependentSums.IsBigO P.toMeasure
        (Homogenization.IndependentSums.gammaSigma ((1 : ℝ) / 3)) X0
        (Cenv * (m : ℝ) ^ (-(6000 : ℝ))))
    (hX0bound : ∀ (h0 : Mat d) (hh0 : matTranspose h0 = -h0),
      ∀ e : Vec d, vecNormSq e ≤ 1 → ∀ sigma : ℝ, sigma ^ 2 = 1 →
      ∀ omega : ShellSeq d,
        blockVecDot
            ((sigma * Real.sqrt (sigmaBarInfinite nu r P)⁻¹) • e,
              Real.sqrt (sigmaBarInfinite nu r P) • e)
            (blockMatVecMul
              (Homogenization.Book.Ch02.coarseBlockMatrix
                (Homogenization.Book.Ch02.cubeDomain (originCube d (m : ℤ)))
                (newMixParam_aLplusH0 nu hnu omega L m h0 hh0))
              ((sigma * Real.sqrt (sigmaBarInfinite nu r P)⁻¹) • e,
                Real.sqrt (sigmaBarInfinite nu r P) • e)) ≤
          blockVecDot
              (blockMatVecMul (blockG (-h0))
                ((sigma * Real.sqrt (sigmaBarInfinite nu r P)⁻¹) • e,
                  Real.sqrt (sigmaBarInfinite nu r P) • e))
              (blockMatVecMul (blockG (-h0))
                ((sigma * Real.sqrt (sigmaBarInfinite nu r P)⁻¹) • e,
                  Real.sqrt (sigmaBarInfinite nu r P) • e)) * X0 omega +
            descendantsAverage (originCube d (m : ℤ)) (m - n)
              (fun R => blockVecDot
                (blockMatVecMul
                  (blockG (-(volumeAverageMat (cubeSet R)
                        (fun y => finiteShellIncrement omega ell L y) + h0)))
                  ((sigma * Real.sqrt (sigmaBarInfinite nu r P)⁻¹) • e,
                    Real.sqrt (sigmaBarInfinite nu r P) • e))
                (blockMatVecMul (annealedBlockMatrix nu ell P (cubeSet (originCube d (n : ℤ))))
                  (blockMatVecMul
                    (blockG (-(volumeAverageMat (cubeSet R)
                          (fun y => finiteShellIncrement omega ell L y) + h0)))
                    ((sigma * Real.sqrt (sigmaBarInfinite nu r P)⁻¹) • e,
                      Real.sqrt (sigmaBarInfinite nu r P) • e))))) :
    ∃ X1 X2 : ShellSeq d → ℝ,
      Measurable X1 ∧
      Homogenization.IndependentSums.IsBigO P.toMeasure
          (Homogenization.IndependentSums.gammaSigma 1) X1
          (C * (sigmaBarInfinite nu r P) ^ (-(2 : ℝ)) *
            (max 0 ((L : ℝ) - (m : ℝ)) + K * Real.log (L : ℝ))) ∧
      Measurable X2 ∧
      Homogenization.IndependentSums.IsBigO P.toMeasure
          (Homogenization.IndependentSums.gammaSigma ((1 : ℝ) / 3)) X2
          (C * (m : ℝ) ^ (-(5000 : ℝ))) ∧
      ∀ (h0 : Mat d) (hh0 : matTranspose h0 = -h0),
      ∀ omega : ShellSeq d, ∀ eta : BlockVec d,
        SuperdiffusionCLT.Section2.Carriers.blockVecNorm eta = 1 →
          doubledResponseJ (cubeDomain (originCube d (m : ℤ)))
              (newMixParam_aLplusH0 nu hnu omega L m h0 hh0)
              (newMixParam_bfAhomPow nu r P (-(1 : ℝ) / 2) eta)
              (newMixParam_bfAhomPow nu r P ((1 : ℝ) / 2) eta) ≤
            C * (sigmaBarInfinite nu r P) ^ (-(2 : ℝ)) *
                (matrixOperatorNorm h0 ^ 2 + max 0 ((L : ℝ) - (m : ℝ)) +
                  K * Real.log (L : ℝ) ^ (2 : ℝ)) +
              X1 omega +
              (1 + (sigmaBarInfinite nu r P) ^ (-(1 : ℝ)) * matrixOperatorNorm h0 ^ 2) *
                X2 omega := by
  set s := sigmaBarInfinite nu r P with hsdef
  have hs : 0 < s := sigmaBarInfinite_pos hnu r hPrefix hJ2 hJ3 hJ4
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  set Vb : ℝ := Cv * nu⁻¹ * (1 + (r : ℝ)) with hVbdef
  have hVb0 : 0 ≤ Vb := mul_nonneg (mul_nonneg hCv0 (inv_nonneg.mpr hnu.le)) (by linarith only [hr0])
  set Z : ShellSeq d → ℝ := fun omega => (Vb + 1) * |X0 omega| with hZdef
  have hZmeas : Measurable Z := (continuous_abs.measurable.comp hX0meas).const_mul _
  have hZBigO : Homogenization.IndependentSums.IsBigO P.toMeasure
      (Homogenization.IndependentSums.gammaSigma ((1 : ℝ) / 3)) Z
      ((Cenv * (10 * Cv * C3 + 1)) * (m : ℝ) ^ (-(5000 : ℝ))) := by
    have habs : Homogenization.IndependentSums.IsBigO P.toMeasure
        (Homogenization.IndependentSums.gammaSigma ((1 : ℝ) / 3)) (fun omega => |X0 omega|)
        (Cenv * (m : ℝ) ^ (-(6000 : ℝ))) := hX0BigO.of_abs_le (fun omega => by simp)
    refine (habs.const_mul (by linarith only [hVb0] : (0 : ℝ) ≤ Vb + 1)).mono_scale ?_
    exact newMixAsm_vFold5000 hCv0 hC30 hCenv0 hnu hnu1 hm1 hL2m hr2L hr0 hnu4
  have hT0bound : ∀ (h0 : Mat d) (hh0 : matTranspose h0 = -h0),
      ∀ e : Vec d, vecNormSq e ≤ 1 → ∀ sigma : ℝ, sigma ^ 2 = 1 →
      ∀ omega : ShellSeq d,
      blockVecDot
          ((sigma * Real.sqrt s⁻¹) • e, Real.sqrt s • e)
          (blockMatVecMul
            (Homogenization.Book.Ch02.coarseBlockMatrix
              (Homogenization.Book.Ch02.cubeDomain (originCube d (m : ℤ)))
              (newMixParam_aLplusH0 nu hnu omega L m h0 hh0))
            ((sigma * Real.sqrt s⁻¹) • e, Real.sqrt s • e)) ≤
        (1 + s⁻¹ * matrixOperatorNorm h0 ^ 2) * Z omega +
          Homogenization.descendantsAverage (originCube d (m : ℤ)) (m - n)
            (fun R => blockVecDot
              (blockMatVecMul
                (blockG (-(Homogenization.volumeAverageMat (cubeSet R)
                      (fun y => finiteShellIncrement omega ell L y) + h0)))
                ((sigma * Real.sqrt s⁻¹) • e, Real.sqrt s • e))
              (blockMatVecMul (annealedBlockMatrix nu ell P (cubeSet (originCube d (n : ℤ))))
                (blockMatVecMul
                  (blockG (-(Homogenization.volumeAverageMat (cubeSet R)
                        (fun y => finiteShellIncrement omega ell L y) + h0)))
                  ((sigma * Real.sqrt s⁻¹) • e, Real.sqrt s • e)))) := by
    intro h0 hh0 e he sigma hsigma2 omega
    have h1 := hX0bound h0 hh0 e he sigma hsigma2 omega
    have hV := hVb h0 hh0 e he sigma hsigma2
    have hV0 := blockVecDot_nonneg
      (blockMatVecMul (blockG (-h0)) ((sigma * Real.sqrt s⁻¹) • e, Real.sqrt s • e))
    have hN : 0 ≤ s⁻¹ * matrixOperatorNorm h0 ^ 2 :=
      mul_nonneg (inv_nonneg.mpr hs.le) (sq_nonneg _)
    have habs0 := abs_nonneg (X0 omega)
    have h2 := mul_le_mul_of_nonneg_left (le_abs_self (X0 omega)) hV0
    have h3 := mul_le_mul_of_nonneg_right hV habs0
    have h4 : (Vb + s⁻¹ * matrixOperatorNorm h0 ^ 2) * |X0 omega| ≤
        (1 + s⁻¹ * matrixOperatorNorm h0 ^ 2) * ((Vb + 1) * |X0 omega|) := by
      have : 0 ≤ (s⁻¹ * matrixOperatorNorm h0 ^ 2) * Vb * |X0 omega| := by positivity
      nlinarith only [this, habs0, hN]
    show _ ≤ (1 + s⁻¹ * matrixOperatorNorm h0 ^ 2) * ((Vb + 1) * |X0 omega|) + _
    linarith only [h1, h2, h3, h4]
  obtain ⟨X1, hX1meas, hX1B, hbd⟩ :=
    newMixAsm_mainBound_uniform2 d hnu hK1 hPrefix hJ2 hJ3 hJ4 hCref1 hnm hellL hRC hCratio0
      hRatio hCs1 hgap (Z := Z) (C := C) hCa hCc hT0bound
  have hC0 : 0 ≤ C := by linarith only [hCc, hCref1, hCratio0]
  have hsneg2 : 0 ≤ s ^ (-(2 : ℝ)) := Real.rpow_nonneg hs.le _
  have hlogL : 0 ≤ Real.log (L : ℝ) := Real.log_natCast_nonneg L
  have hgapnn : 0 ≤ max 0 ((L : ℝ) - (m : ℝ)) := le_max_left _ _
  have hK0 : 0 ≤ K := by linarith only [hK1]
  have hlog2nn : 0 ≤ K * Real.log (L : ℝ) ^ (2 : ℝ) := mul_nonneg hK0 (Real.rpow_nonneg hlogL _)
  have hlog1nn : 0 ≤ K * Real.log (L : ℝ) := mul_nonneg hK0 hlogL
  have hamp1 : 0 ≤ C * s ^ (-(2 : ℝ)) * (max 0 ((L : ℝ) - (m : ℝ)) + K * Real.log (L : ℝ)) :=
    mul_nonneg (mul_nonneg hC0 hsneg2) (by linarith only [hgapnn, hlog1nn])
  have hCb' : 0 ≤ Cenv * (10 * Cv * C3 + 1) := by positivity
  have hamp2 : 0 ≤ C * (m : ℝ) ^ (-(5000 : ℝ)) :=
    mul_nonneg hC0 (Real.rpow_nonneg (Nat.cast_nonneg m) _)
  refine ⟨fun omega => (1 / 2 : ℝ) * X1 omega, fun omega => (1 / 2 : ℝ) * Z omega,
    hX1meas.const_mul _, ?_, hZmeas.const_mul _, ?_, ?_⟩
  · refine (hX1B.const_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)).mono_scale ?_
    linarith only [hamp1]
  · refine (hZBigO.const_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)).mono_scale ?_
    have := mul_le_mul_of_nonneg_right hCb (Real.rpow_nonneg (Nat.cast_nonneg m) (-(5000 : ℝ)))
    linarith only [this, hamp2]
  · intro h0 hh0 omega eta heta
    rw [Real.rpow_neg_one, newMixAsm_bfAhomPow_neg_half, newMixAsm_bfAhomPow_pos_half]
    have hA0 : 0 ≤ C * s ^ (-(2 : ℝ)) *
        (matrixOperatorNorm h0 ^ 2 + max 0 ((L : ℝ) - (m : ℝ)) +
          K * Real.log (L : ℝ) ^ (2 : ℝ)) :=
      mul_nonneg (mul_nonneg hC0 hsneg2) (by linarith only [sq_nonneg (matrixOperatorNorm h0), hgapnn, hlog2nn])
    have hMain : ∀ e : Vec d, vecNormSq e ≤ 1 → ∀ sigma : ℝ, sigma ^ 2 = 1 →
        blockVecDot ((sigma * Real.sqrt s⁻¹) • e, Real.sqrt s • e)
          (blockMatVecMul
            (Homogenization.Book.Ch02.coarseBlockMatrix (cubeDomain (originCube d (m : ℤ)))
              (newMixParam_aLplusH0 nu hnu omega L m h0 hh0))
            ((sigma * Real.sqrt s⁻¹) • e, Real.sqrt s • e)) ≤
          2 * vecNormSq e + (C * s ^ (-(2 : ℝ)) *
            (matrixOperatorNorm h0 ^ 2 + max 0 ((L : ℝ) - (m : ℝ)) +
              K * Real.log (L : ℝ) ^ (2 : ℝ)) + X1 omega +
            (1 + s⁻¹ * matrixOperatorNorm h0 ^ 2) * Z omega) := by
      intro e he sigma hsigma2
      have := hbd h0 hh0 e he sigma hsigma2 omega
      linarith only [this]
    obtain ⟨hJ, hJs⟩ := newMixAsm_scalarJ_of_mainBound hnu hs omega L m h0 hh0 hMain
    have hfin := newMixAsm_doubledResponseJ_le_of_scalar_bounds hnu omega L m h0 hh0
      (shomr := s) (R := (C * s ^ (-(2 : ℝ)) *
            (matrixOperatorNorm h0 ^ 2 + max 0 ((L : ℝ) - (m : ℝ)) +
              K * Real.log (L : ℝ) ^ (2 : ℝ)) + X1 omega +
            (1 + s⁻¹ * matrixOperatorNorm h0 ^ 2) * Z omega) / 2) hJ hJs eta heta
    have hrw : (1 + s⁻¹ * matrixOperatorNorm h0 ^ 2) * ((1 / 2 : ℝ) * Z omega) =
        ((1 + s⁻¹ * matrixOperatorNorm h0 ^ 2) * Z omega) / 2 := by ring
    show _ ≤ _ + (1 / 2 : ℝ) * X1 omega + (1 + s⁻¹ * matrixOperatorNorm h0 ^ 2) * ((1 / 2 : ℝ) * Z omega)
    linarith only [hfin, hA0, hrw]

end
end SuperdiffusionCLT.Section4.NewMixing
