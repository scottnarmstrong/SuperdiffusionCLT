/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.Mixing.LargeGapAboveQuadratic
public import SuperdiffusionCLT.Section4.Mixing.LargeGapConcentrationFinal

/-!
# Amplitude constants pulled uniform

The entry-sum amplitude bounds of the concentration argument
(`LargeGapConcentrationFinal.lean`) and of the above-lattice argument
both produce their `∃ C` witness as a fixed product `coef(d) * base(d)`,
without any hypothesis-dependent case split — the returned constant, by
inspection of each proof, never uses the specific `ν, L, m` (or `nn`) passed
in. This file states both with the `∃ C` moved in front of `∀ ν L (nn) m`,
so the same `C(d)` demonstrably works for every valid input; needed so the
final `n ≤ L` / `L < n` assembly (`LargeGapAboveMainUniform.lean`) can expose
one `C(d)` for the whole `X4` clause, matching the `∃ C`
binder order of the statement. -/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

open Homogenization
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

/-- **The entry-sum amplitude bound, uniform in `ν, L, m`.** -/
theorem mixGap_entrySumAmp_le_uniform (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {nu : ℝ} {L m : ℕ}, 0 < nu → nu ≤ 1 → 1 ≤ L →
        mixGap_entrySumAmp d nu L m ≤
          C * nu⁻¹ * (L : ℝ) * (3 : ℝ) ^ (-((d : ℝ) * ((m - L : ℕ) : ℝ)) / 2) := by
  set base : ℝ := (2 * gammaTriangleConst 1 * gammaOneExpRegimeConst *
      Real.sqrt (((ShellField.shellColorPeriod d : ℕ) : ℝ) ^ d) *
      ((1 + IndependentSums.gammaMomentConst 1) * (3 + 4 * cutoffL2Const d))) with hbase
  have hbase_nn : 0 ≤ base := by
    have h1 : (0 : ℝ) < gammaTriangleConst (1 : ℝ) := gammaTriangleConst_pos
    have h2 : (0 : ℝ) < gammaOneExpRegimeConst := gammaOneExpRegimeConst_pos
    have h3 : (0 : ℝ) < IndependentSums.gammaMomentConst 1 :=
      IndependentSums.gammaMomentConst_pos one_pos
    have h4 : (0 : ℝ) ≤ cutoffL2Const d := by
      unfold cutoffL2Const cutoffSquareConst; positivity
    rw [hbase]; positivity
  have hgtc_nn : (0 : ℝ) ≤ gammaTriangleConst (1 : ℝ) := gammaTriangleConst_pos.le
  have hd2_nn : (0 : ℝ) ≤ (d : ℝ) * (d : ℝ) := by positivity
  set coef : ℝ := gammaTriangleConst 1 * (gammaTriangleConst 1 * (gammaTriangleConst 1 * 2 + 1) + 1) *
    (gammaTriangleConst 1 * ((d : ℝ) * (d : ℝ))) with hcoef
  have hcoef_nn : 0 ≤ coef := by rw [hcoef]; positivity
  refine ⟨coef * base, mul_nonneg hcoef_nn hbase_nn, ?_⟩
  intro nu L m hnu hnu1 hL
  have hpe : mixGap_perEntryAmp d nu L m ≤
      base * nu⁻¹ * (L : ℝ) * (3 : ℝ) ^ (-((d : ℝ) * ((m - L : ℕ) : ℝ)) / 2) := by
    have hEnv := mixGap_entryEnvelope_le hnu hnu1 d L hL
    have hmom : (0 : ℝ) < IndependentSums.gammaMomentConst 1 :=
      IndependentSums.gammaMomentConst_pos one_pos
    have hcomb : mixGap_entryEnvelope d nu L +
        IndependentSums.gammaMomentConst 1 * mixGap_entryEnvelope d nu L ≤
        (1 + IndependentSums.gammaMomentConst 1) * ((3 + 4 * cutoffL2Const d) * nu⁻¹ * (L : ℝ)) := by
      have hm := mul_le_mul_of_nonneg_left hEnv hmom.le
      nlinarith only [hEnv, hm]
    have hcoefpos : (0 : ℝ) ≤ 2 * gammaTriangleConst 1 * gammaOneExpRegimeConst *
        Real.sqrt (((ShellField.shellColorPeriod d : ℕ) : ℝ) ^ d) := by
      have h1 : (0 : ℝ) < gammaTriangleConst (1 : ℝ) := gammaTriangleConst_pos
      have h2 : (0 : ℝ) < gammaOneExpRegimeConst := gammaOneExpRegimeConst_pos
      positivity
    have hpow_pos : (0 : ℝ) < (3 : ℝ) ^ (-((d : ℝ) * ((m - L : ℕ) : ℝ)) / 2) :=
      Real.rpow_pos_of_pos (by norm_num) _
    unfold mixGap_perEntryAmp
    have hstep := mul_le_mul_of_nonneg_left hcomb hcoefpos
    have hstep2 := mul_le_mul_of_nonneg_right hstep hpow_pos.le
    refine hstep2.trans_eq ?_
    rw [hbase]; ring
  have heq : mixGap_entrySumAmp d nu L m = coef * mixGap_perEntryAmp d nu L m := by
    unfold mixGap_entrySumAmp mixGap_blockSumAmp
    rw [hcoef]; ring
  rw [heq]
  calc coef * mixGap_perEntryAmp d nu L m
      ≤ coef * (base * nu⁻¹ * (L : ℝ) * (3 : ℝ) ^ (-((d : ℝ) * ((m - L : ℕ) : ℝ)) / 2)) :=
        mul_le_mul_of_nonneg_left hpe hcoef_nn
    _ = coef * base * nu⁻¹ * (L : ℝ) * (3 : ℝ) ^ (-((d : ℝ) * ((m - L : ℕ) : ℝ)) / 2) := by ring

/-- **The above-lattice entry-sum amplitude bound, uniform in `ν, L, nn, m`.** -/
theorem mixGapAbove_entrySumAmp_le_uniform (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {nu : ℝ} {L nn m : ℕ}, 0 < nu → nu ≤ 1 → 1 ≤ L →
        mixGapAbove_entrySumAmp d nu L nn m ≤
          C * nu⁻¹ * (L : ℝ) * (3 : ℝ) ^ (-((d : ℝ) * ((m - nn : ℕ) : ℝ)) / 2) := by
  set base : ℝ := (2 * gammaTriangleConst 1 * gammaOneExpRegimeConst *
      Real.sqrt (((ShellField.shellColorPeriod d : ℕ) : ℝ) ^ d) *
      ((1 + IndependentSums.gammaMomentConst 1) * (3 + 4 * cutoffL2Const d))) with hbase
  have hbase_nn : 0 ≤ base := by
    have h1 : (0 : ℝ) < gammaTriangleConst (1 : ℝ) := gammaTriangleConst_pos
    have h2 : (0 : ℝ) < gammaOneExpRegimeConst := gammaOneExpRegimeConst_pos
    have h3 : (0 : ℝ) < IndependentSums.gammaMomentConst 1 :=
      IndependentSums.gammaMomentConst_pos one_pos
    have h4 : (0 : ℝ) ≤ cutoffL2Const d := by
      unfold cutoffL2Const cutoffSquareConst; positivity
    rw [hbase]; positivity
  have hgtc_nn : (0 : ℝ) ≤ gammaTriangleConst (1 : ℝ) := gammaTriangleConst_pos.le
  have hd2_nn : (0 : ℝ) ≤ (d : ℝ) * (d : ℝ) := by positivity
  set coef : ℝ := gammaTriangleConst 1 * (gammaTriangleConst 1 * (gammaTriangleConst 1 * 2 + 1) + 1) *
    (gammaTriangleConst 1 * ((d : ℝ) * (d : ℝ))) with hcoef
  have hcoef_nn : 0 ≤ coef := by rw [hcoef]; positivity
  refine ⟨coef * base, mul_nonneg hcoef_nn hbase_nn, ?_⟩
  intro nu L nn m hnu hnu1 hL
  have hpe : mixGapAbove_perEntryAmp d nu L nn m ≤
      base * nu⁻¹ * (L : ℝ) * (3 : ℝ) ^ (-((d : ℝ) * ((m - nn : ℕ) : ℝ)) / 2) := by
    have hEnv := mixGap_entryEnvelope_le hnu hnu1 d L hL
    have hmom : (0 : ℝ) < IndependentSums.gammaMomentConst 1 :=
      IndependentSums.gammaMomentConst_pos one_pos
    have hcomb : mixGap_entryEnvelope d nu L +
        IndependentSums.gammaMomentConst 1 * mixGap_entryEnvelope d nu L ≤
        (1 + IndependentSums.gammaMomentConst 1) * ((3 + 4 * cutoffL2Const d) * nu⁻¹ * (L : ℝ)) := by
      have hm := mul_le_mul_of_nonneg_left hEnv hmom.le
      nlinarith only [hEnv, hm]
    have hcoefpos : (0 : ℝ) ≤ 2 * gammaTriangleConst 1 * gammaOneExpRegimeConst *
        Real.sqrt (((ShellField.shellColorPeriod d : ℕ) : ℝ) ^ d) := by
      have h1 : (0 : ℝ) < gammaTriangleConst (1 : ℝ) := gammaTriangleConst_pos
      have h2 : (0 : ℝ) < gammaOneExpRegimeConst := gammaOneExpRegimeConst_pos
      positivity
    have hpow_pos : (0 : ℝ) < (3 : ℝ) ^ (-((d : ℝ) * ((m - nn : ℕ) : ℝ)) / 2) :=
      Real.rpow_pos_of_pos (by norm_num) _
    unfold mixGapAbove_perEntryAmp
    have hstep := mul_le_mul_of_nonneg_left hcomb hcoefpos
    have hstep2 := mul_le_mul_of_nonneg_right hstep hpow_pos.le
    refine hstep2.trans_eq ?_
    rw [hbase]; ring
  have heq : mixGapAbove_entrySumAmp d nu L nn m = coef * mixGapAbove_perEntryAmp d nu L nn m := by
    unfold mixGapAbove_entrySumAmp mixGapAbove_blockSumAmp
    rw [hcoef]; ring
  rw [heq]
  calc coef * mixGapAbove_perEntryAmp d nu L nn m
      ≤ coef * (base * nu⁻¹ * (L : ℝ) * (3 : ℝ) ^ (-((d : ℝ) * ((m - nn : ℕ) : ℝ)) / 2)) :=
        mul_le_mul_of_nonneg_left hpe hcoef_nn
    _ = coef * base * nu⁻¹ * (L : ℝ) * (3 : ℝ) ^ (-((d : ℝ) * ((m - nn : ℕ) : ℝ)) / 2) := by ring

end

end SuperdiffusionCLT.Section4.Mixing
