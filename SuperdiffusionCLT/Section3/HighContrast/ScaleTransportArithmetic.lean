/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.HighContrast.CutoffLinftyEnvelope
public import Homogenization.Book.Ch05.Theorems.Section51.EntryScale

/-!
# Pure arithmetic of the high-contrast entry threshold

This module collects the parts of the scale bookkeeping of the high-contrast
entry bound that are arithmetic rather than transport: the explicit constants
and the `log^2` threshold comparison, none of which mentions the rebased cutoff
law or its cubes, and the dimensional polynomial
`cutoffContrastBound` bounding the initial-scale contrast, which depends on the
cutoff index only through the amplitude of the envelope.

`Section3/HighContrast/ScaleTransport.lean` imports this module and combines
these ingredients with the scale shift of the annealed blocks.

## Main definitions

* `entryScaleLogSqConst`, `cutoffLargeCubeAmpConst`, `cutoffContrastBound`: the
  three explicit constants of the bookkeeping.

## Main results

* `annealedEntryScale_le_mul_logSq`: the entry scale is dominated by a multiple
  of `log^2` of any bound on the initial-scale contrast.
* `cutoffLargeCubeAmp_le`: the envelope amplitude is linear in the cutoff
  index; the statement is dimensional and its positivity needs no probabilistic
  data, only `0 < d`.
* `cutoffContrastBound_nonneg`: the dimensional polynomial is nonnegative.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.HighContrast

open Homogenization MeasureTheory ProbabilityTheory
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Probability

noncomputable section

variable {d : ℕ}

/-! ## The threshold comparison

The entry scale is a sum of two ceilings governed by
`log (2 + widetildeTheta_0)`, so a bound `widetildeTheta_0 <= B` dominates it by
a multiple of `log^2 (2 + B)`, the shape of the threshold in the paper. -/

/-- The explicit constant of the threshold comparison: the multiple of
`log^2 (2 + B)` that dominates `Book.Ch05.annealedEntryScale`. It depends on the
ellipticity exponent, the entry constant and the accuracy, not on the law. -/
def entryScaleLogSqConst (xi : ℕ) (C sigma : ℝ) : ℝ :=
  8 + C + C * (xi : ℝ) * sigma⁻¹ ^ (4 : ℕ) * |Real.log sigma| *
    (4 * Real.log (2 + sigma⁻¹ ^ (4 : ℕ) * (xi : ℝ)) + 2)

/-- **The entry scale is dominated by `log^2` of any bound on the initial-scale
contrast.** -/
theorem annealedEntryScale_le_mul_logSq [NeZero d] {P : Book.Ch04.RestrictionCoeffLaw d}
    (hP4 : Book.Ch05.QuantitativeCoarseGrainedEllipticity P) {C sigma B : ℝ}
    (hC : 0 < C) (hB : 0 ≤ B)
    (hW : Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4 ≤ B) :
    ((Book.Ch05.annealedEntryScale P hP4 C sigma : ℕ) : ℝ) ≤
      entryScaleLogSqConst hP4.xi C sigma * Real.log (2 + B) ^ (2 : ℕ) := by
  set W : ℝ := Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4 with hW_def
  set L : ℝ := Real.log (2 + B) with hL_def
  set G : ℝ := Real.log (2 + sigma⁻¹ ^ (4 : ℕ) * (hP4.xi : ℝ)) with hG_def
  set Q : ℝ := C * (hP4.xi : ℝ) * sigma⁻¹ ^ (4 : ℕ) * |Real.log sigma| with hQ_def
  have hWnn : 0 ≤ W := Book.Ch05.Section51.widetildeThetaAtScale_nonneg P hP4 0
  have hLhalf : (1 / 2 : ℝ) ≤ L := Book.Ch05.Section51.log_two_add_ge_half hB
  have hLnn : 0 ≤ L := le_trans (by norm_num) hLhalf
  have hLsq : (1 : ℝ) ≤ 4 * L ^ (2 : ℕ) := by nlinarith only [hLhalf]
  have hLlin : L ≤ 2 * L ^ (2 : ℕ) := by nlinarith only [hLhalf]
  have hcoef : (0 : ℝ) ≤ sigma⁻¹ ^ (4 : ℕ) * (hP4.xi : ℝ) := by positivity
  have hGnn : 0 ≤ G := Book.Ch05.Section51.log_two_add_nonneg hcoef
  have hQnn : 0 ≤ Q := by
    rw [hQ_def]; positivity
  -- the first ceiling
  have hlogW : Real.log (2 + W) ≤ L := by
    rw [hL_def]
    exact Real.log_le_log (by linarith only [hWnn]) (by linarith only [hW])
  have hlogWnn : 0 ≤ Real.log (2 + W) := Book.Ch05.Section51.log_two_add_nonneg hWnn
  have hfirst : C * Real.log (2 + W) ^ (2 : ℕ) ≤ C * L ^ (2 : ℕ) :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlogWnn hlogW 2) hC.le
  have hxnn : (0 : ℝ) ≤ C * Real.log (2 + W) ^ (2 : ℕ) := by positivity
  have hceil1 : ((Book.Ch05.annealedConvergenceEntryScaleBound P hP4 C : ℕ) : ℝ) ≤
      C * Real.log (2 + W) ^ (2 : ℕ) + 1 :=
    Book.Ch05.Section51.natCeil_le_add_one hxnn
  -- the second ceiling
  have harg : 2 + sigma⁻¹ ^ (4 : ℕ) * (hP4.xi : ℝ) * W ≤
      (2 + sigma⁻¹ ^ (4 : ℕ) * (hP4.xi : ℝ)) * (1 + B) := by
    have hle : sigma⁻¹ ^ (4 : ℕ) * (hP4.xi : ℝ) * W ≤
        sigma⁻¹ ^ (4 : ℕ) * (hP4.xi : ℝ) * B := mul_le_mul_of_nonneg_left hW hcoef
    nlinarith only [hle, hcoef, hB]
  have hlogY : Real.log (2 + sigma⁻¹ ^ (4 : ℕ) * (hP4.xi : ℝ) * W) ≤ G + L := by
    have hpos1 : (0 : ℝ) < 2 + sigma⁻¹ ^ (4 : ℕ) * (hP4.xi : ℝ) := by linarith only [hcoef]
    have hpos2 : (0 : ℝ) < 1 + B := by linarith only [hB]
    have hsplit : Real.log ((2 + sigma⁻¹ ^ (4 : ℕ) * (hP4.xi : ℝ)) * (1 + B)) =
        G + Real.log (1 + B) := by
      rw [hG_def, Real.log_mul hpos1.ne' hpos2.ne']
    have hmono := Real.log_le_log
      (by linarith only [hcoef, hWnn, mul_nonneg hcoef hWnn] :
        (0 : ℝ) < 2 + sigma⁻¹ ^ (4 : ℕ) * (hP4.xi : ℝ) * W) harg
    have hlast : Real.log (1 + B) ≤ L :=
      Real.log_le_log hpos2 (by linarith only [])
    rw [hsplit] at hmono
    linarith only [hmono, hlast]
  have hynn : (0 : ℝ) ≤ Q * Real.log (2 + sigma⁻¹ ^ (4 : ℕ) * (hP4.xi : ℝ) * W) :=
    mul_nonneg hQnn (Book.Ch05.Section51.log_two_add_nonneg
      (mul_nonneg hcoef hWnn))
  have hceil2 : ((Book.Ch05.annealedConvergenceSigmaTailScale P hP4 C sigma : ℕ) : ℝ) ≤
      Q * Real.log (2 + sigma⁻¹ ^ (4 : ℕ) * (hP4.xi : ℝ) * W) + 1 :=
    Book.Ch05.Section51.natCeil_le_add_one hynn
  have hsecond : Q * Real.log (2 + sigma⁻¹ ^ (4 : ℕ) * (hP4.xi : ℝ) * W) ≤
      Q * (4 * G + 2) * L ^ (2 : ℕ) := by
    have hstep : Q * Real.log (2 + sigma⁻¹ ^ (4 : ℕ) * (hP4.xi : ℝ) * W) ≤ Q * (G + L) :=
      mul_le_mul_of_nonneg_left hlogY hQnn
    have hGL : G + L ≤ (4 * G + 2) * L ^ (2 : ℕ) := by
      have h1 : G ≤ G * (4 * L ^ (2 : ℕ)) := le_mul_of_one_le_right hGnn hLsq
      nlinarith only [h1, hLlin]
    have hfin : Q * (G + L) ≤ Q * ((4 * G + 2) * L ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_left hGL hQnn
    calc Q * Real.log (2 + sigma⁻¹ ^ (4 : ℕ) * (hP4.xi : ℝ) * W) ≤ Q * (G + L) := hstep
      _ ≤ Q * ((4 * G + 2) * L ^ (2 : ℕ)) := hfin
      _ = Q * (4 * G + 2) * L ^ (2 : ℕ) := by ring
  have htwo : (2 : ℝ) ≤ 8 * L ^ (2 : ℕ) := by linarith only [hLsq]
  have hsum : ((Book.Ch05.annealedEntryScale P hP4 C sigma : ℕ) : ℝ) =
      ((Book.Ch05.annealedConvergenceEntryScaleBound P hP4 C : ℕ) : ℝ) +
        ((Book.Ch05.annealedConvergenceSigmaTailScale P hP4 C sigma : ℕ) : ℝ) := by
    rw [Book.Ch05.annealedEntryScale, Nat.cast_add]
  rw [hsum, entryScaleLogSqConst, ← hQ_def, ← hG_def]
  linarith only [hceil1, hceil2, hfirst, hsecond, htwo]

/-! ## The size of the envelope amplitude

The amplitude grows linearly in `m`: the two `sqrt` factors multiply to
`m` up to the dimensional offset. -/

/-- The dimensional constant in the linear bound on the amplitude of the
`L^infinity` envelope of the cutoff on the rebasing cube. -/
def cutoffLargeCubeAmpConst (d : ℕ) : ℝ :=
  IndependentSums.gammaTriangleConst 2 * Real.sqrt (1 + (triadicOffset d : ℝ)) *
    (shellZeroLargeCubeConst d + largeCubeLinftyConst d)

/-- **The amplitude of the envelope is linear in the cutoff index.** The
statement is dimensional: both constants depend on `d` alone, so the bound needs
no probabilistic data, only `0 < d`. -/
theorem cutoffLargeCubeAmp_le (hd : 0 < d) (m : ℕ) :
    cutoffLargeCubeAmp d m ≤ cutoffLargeCubeAmpConst d * (1 + (m : ℝ)) := by
  have hz : 0 ≤ shellZeroLargeCubeConst d := (shellZeroLargeCubeConst_pos_of_pos hd).le
  have hl : 0 ≤ largeCubeLinftyConst d := (largeCubeLinftyConst_pos_of_pos hd).le
  have hgamma : 0 ≤ IndependentSums.gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos.le
  have hT : (0 : ℝ) ≤ 1 + (triadicOffset d : ℝ) := by positivity
  have hone_le : (1 : ℝ) ≤ 1 + (m : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg m)
  have hR : Real.sqrt (1 + (m : ℝ)) * Real.sqrt (1 + (m : ℝ)) = 1 + (m : ℝ) :=
    Real.mul_self_sqrt (by linarith only [hone_le])
  have hRnn : 0 ≤ Real.sqrt (1 + (m : ℝ)) := Real.sqrt_nonneg _
  have hRle : Real.sqrt (1 + (m : ℝ)) ≤ 1 + (m : ℝ) :=
    calc Real.sqrt (1 + (m : ℝ))
        ≤ Real.sqrt ((1 + (m : ℝ)) * (1 + (m : ℝ))) :=
          Real.sqrt_le_sqrt (by nlinarith only [hone_le])
      _ = 1 + (m : ℝ) := Real.sqrt_mul_self (by linarith only [hone_le])
  have hbig : ((m + triadicOffset d : ℕ) : ℝ) ≤
      (1 + (triadicOffset d : ℝ)) * (1 + (m : ℝ)) := by
    have hprod : (0 : ℝ) ≤ (triadicOffset d : ℝ) * (m : ℝ) :=
      mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg m)
    push_cast
    nlinarith only [hprod]
  have hsqbig : Real.sqrt ((m + triadicOffset d : ℕ) : ℝ) ≤
      Real.sqrt (1 + (triadicOffset d : ℝ)) * Real.sqrt (1 + (m : ℝ)) := by
    calc Real.sqrt ((m + triadicOffset d : ℕ) : ℝ)
        ≤ Real.sqrt ((1 + (triadicOffset d : ℝ)) * (1 + (m : ℝ))) := Real.sqrt_le_sqrt hbig
      _ = Real.sqrt (1 + (triadicOffset d : ℝ)) * Real.sqrt (1 + (m : ℝ)) :=
          Real.sqrt_mul hT _
  have hsqm : Real.sqrt ((m : ℕ) : ℝ) ≤ Real.sqrt (1 + (m : ℝ)) := by
    refine Real.sqrt_le_sqrt ?_
    linarith only [zero_le_one (α := ℝ)]
  have hTnn : 0 ≤ Real.sqrt (1 + (triadicOffset d : ℝ)) := Real.sqrt_nonneg _
  have hfirst : shellZeroLargeCubeConst d * Real.sqrt ((m + triadicOffset d : ℕ) : ℝ) ≤
      shellZeroLargeCubeConst d *
        (Real.sqrt (1 + (triadicOffset d : ℝ)) * (1 + (m : ℝ))) := by
    refine mul_le_mul_of_nonneg_left (le_trans hsqbig ?_) hz
    exact mul_le_mul_of_nonneg_left hRle hTnn
  have hsecond : largeCubeLinftyConst d *
      (Real.sqrt ((m : ℕ) : ℝ) * Real.sqrt ((m + triadicOffset d : ℕ) : ℝ)) ≤
      largeCubeLinftyConst d *
        (Real.sqrt (1 + (triadicOffset d : ℝ)) * (1 + (m : ℝ))) := by
    refine mul_le_mul_of_nonneg_left ?_ hl
    calc Real.sqrt ((m : ℕ) : ℝ) * Real.sqrt ((m + triadicOffset d : ℕ) : ℝ)
        ≤ Real.sqrt (1 + (m : ℝ)) *
            (Real.sqrt (1 + (triadicOffset d : ℝ)) * Real.sqrt (1 + (m : ℝ))) :=
          mul_le_mul hsqm hsqbig (Real.sqrt_nonneg _) hRnn
      _ = Real.sqrt (1 + (triadicOffset d : ℝ)) *
            (Real.sqrt (1 + (m : ℝ)) * Real.sqrt (1 + (m : ℝ))) := by ring
      _ = Real.sqrt (1 + (triadicOffset d : ℝ)) * (1 + (m : ℝ)) := by rw [hR]
  have hsum : shellZeroLargeCubeConst d * Real.sqrt ((m + triadicOffset d : ℕ) : ℝ) +
      largeCubeLinftyConst d *
        (Real.sqrt ((m : ℕ) : ℝ) * Real.sqrt ((m + triadicOffset d : ℕ) : ℝ)) ≤
      Real.sqrt (1 + (triadicOffset d : ℝ)) *
        (shellZeroLargeCubeConst d + largeCubeLinftyConst d) * (1 + (m : ℝ)) := by
    linarith only [add_le_add hfirst hsecond]
  rw [cutoffLargeCubeAmp, cutoffLargeCubeAmpConst]
  calc IndependentSums.gammaTriangleConst 2 *
        (shellZeroLargeCubeConst d * Real.sqrt ((m + triadicOffset d : ℕ) : ℝ) +
          largeCubeLinftyConst d *
            (Real.sqrt ((m : ℕ) : ℝ) * Real.sqrt ((m + triadicOffset d : ℕ) : ℝ)))
      ≤ IndependentSums.gammaTriangleConst 2 *
          (Real.sqrt (1 + (triadicOffset d : ℝ)) *
            (shellZeroLargeCubeConst d + largeCubeLinftyConst d) * (1 + (m : ℝ))) :=
        mul_le_mul_of_nonneg_left hsum hgamma
    _ = IndependentSums.gammaTriangleConst 2 * Real.sqrt (1 + (triadicOffset d : ℝ)) *
          (shellZeroLargeCubeConst d + largeCubeLinftyConst d) * (1 + (m : ℝ)) := by ring

/-! ## The dimensional contrast polynomial -/

/-- **The dimensional polynomial bounding the initial-scale contrast**:
`4 (1 + Gamma(xi + 1)) (1 + 2 nu^{-2}) (1 + (C(d)(1 + m))^2)`, of size
`C(d, xi) nu^{-2} m^2`. -/
def cutoffContrastBound (d xi : ℕ) (nu : ℝ) (m : ℕ) : ℝ :=
  4 * (1 + Real.Gamma ((xi : ℝ) + 1)) * (1 + 2 * nu⁻¹ ^ (2 : ℕ)) *
    (1 + (cutoffLargeCubeAmpConst d * (1 + (m : ℝ))) ^ (2 : ℕ))

/-- The dimensional polynomial is nonnegative. -/
theorem cutoffContrastBound_nonneg (d xi : ℕ) (nu : ℝ) (m : ℕ) :
    0 ≤ cutoffContrastBound d xi nu m := by
  have hG : (0 : ℝ) ≤ Real.Gamma ((xi : ℝ) + 1) :=
    Real.Gamma_nonneg_of_nonneg (by positivity)
  rw [cutoffContrastBound]
  have h1 : (0 : ℝ) ≤ 4 * (1 + Real.Gamma ((xi : ℝ) + 1)) := by linarith only [hG]
  have h2 : (0 : ℝ) ≤ 1 + 2 * nu⁻¹ ^ (2 : ℕ) := by positivity
  have h3 : (0 : ℝ) ≤ 1 + (cutoffLargeCubeAmpConst d * (1 + (m : ℝ))) ^ (2 : ℕ) := by
    positivity
  exact mul_nonneg (mul_nonneg h1 h2) h3

end

end SuperdiffusionCLT.Section3.HighContrast