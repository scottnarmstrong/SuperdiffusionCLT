/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
**The bigLog condition is
monotone increasing in the input-scale factor of [AK, Theorem 6.1], `mm0 := (m:ℝ)+(m0:ℝ)+1`,
at fixed `m0`.**

Rather than re-deriving the `M0Threshold`
bound separately at each of the two input scales `m̃` and `m̃'` of [AK, Theorem 6.1]
(which would force `m0` itself to depend on which of `m̃, m̃'` is being
discharged — circular, since `m̃, m̃'` are themselves defined using `m0`),
this lemma lets a single application of `M0ThresholdB`/`M0ThresholdC` **at
the outer scale `m`** (`hThetaLm`'s own scale — fixed, available before `m0`
is chosen) be pushed down to any smaller input scale (`m̃ ≤ m̃' ≤ m`)
at the very same `m0`, since `mm0 = (m:ℝ)+(m0:ℝ)+1` is monotone increasing
in the natural-number `m`-argument (fixed `m0`), and the whole bigLog
expression is monotone increasing in `mm0` (proved here). This is the exact
analogue of `M0ThresholdB.lean`'s `homogBelowM0_monotone_in_Theta0` (which is
monotone in the OTHER factor, `Theta0`, at fixed `mm0`); the proof pattern is
the mirror image, adapted since `Theta0` also multiplies the *second* log's
outer factor while `mm0` only ever appears inside the shared inner
argument `Ups12 * mm0 * Theta0`, which makes this direction slightly simpler.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.HomogBelow

/-- **Monotone in `mm0`, `Theta0` fixed.** The shared M0-threshold expression
(`M0ThresholdB.lean`/`M0ThresholdC.lean`/`ThetaLmFinalBigLog.lean`'s `hM0`
shape) is monotone increasing in `mm0` at fixed `Ups12, Theta0, C61, Cmix`. -/
theorem homogBelow_bigLog_monotone_in_mm0
    {C61 Cmix Ups12 mm0 mm0' Theta0 : ℝ}
    (hC61 : 1 ≤ C61) (hCmix : 1 ≤ Cmix)
    (hUps12ge1 : 1 ≤ Ups12) (hTheta0ge1 : 1 ≤ Theta0)
    (hmm0ge1 : 1 ≤ mm0) (hmm0le : mm0 ≤ mm0') :
    32 * C61 * (Cmix + 1) *
        Real.log (Ups12 * mm0 * Theta0) *
        Real.log (3 * Theta0 * (2 + 4 * Cmix * Real.log (Ups12 * mm0 * Theta0))) ≤
      32 * C61 * (Cmix + 1) *
        Real.log (Ups12 * mm0' * Theta0) *
        Real.log (3 * Theta0 * (2 + 4 * Cmix * Real.log (Ups12 * mm0' * Theta0))) := by
  have hTheta0pos : (0 : ℝ) < Theta0 := lt_of_lt_of_le one_pos hTheta0ge1
  have hUps12Theta0pos : (0 : ℝ) < Ups12 * Theta0 := by
    have h1 : (0 : ℝ) < Ups12 := lt_of_lt_of_le one_pos hUps12ge1
    exact mul_pos h1 hTheta0pos
  have hUps12mm0ge1 : (1 : ℝ) ≤ Ups12 * mm0 * Theta0 := by
    nlinarith only [hUps12ge1, hmm0ge1, hTheta0ge1,
      mul_nonneg (by linarith only [hUps12ge1] : (0 : ℝ) ≤ Ups12 - 1)
        (by linarith only [hmm0ge1] : (0 : ℝ) ≤ mm0 - 1),
      mul_nonneg (by nlinarith only [hUps12ge1, hmm0ge1] : (0 : ℝ) ≤ Ups12 * mm0 - 1)
        (by linarith only [hTheta0ge1] : (0 : ℝ) ≤ Theta0 - 1)]
  -- argument of the first log is monotone in `mm0`, and `≥ 1`
  have hargmono : Ups12 * mm0 * Theta0 ≤ Ups12 * mm0' * Theta0 := by
    have h := mul_le_mul_of_nonneg_right hmm0le hUps12Theta0pos.le
    calc Ups12 * mm0 * Theta0 = (Ups12 * Theta0) * mm0 := by ring
      _ ≤ (Ups12 * Theta0) * mm0' := by
          have h' := mul_le_mul_of_nonneg_left hmm0le hUps12Theta0pos.le
          linarith only [h']
      _ = Ups12 * mm0' * Theta0 := by ring
  have harg'_ge1 : (1 : ℝ) ≤ Ups12 * mm0' * Theta0 := le_trans hUps12mm0ge1 hargmono
  have hlogargmono : Real.log (Ups12 * mm0 * Theta0) ≤ Real.log (Ups12 * mm0' * Theta0) :=
    Real.log_le_log (lt_of_lt_of_le one_pos hUps12mm0ge1) hargmono
  have hlogarg_nn : (0 : ℝ) ≤ Real.log (Ups12 * mm0 * Theta0) :=
    Real.log_nonneg hUps12mm0ge1
  -- second log's argument is monotone in `mm0`, and `≥ 1`
  have hCmixnn : (0 : ℝ) ≤ Cmix := by linarith only [hCmix]
  have harg2part_mono : 2 + 4 * Cmix * Real.log (Ups12 * mm0 * Theta0) ≤
      2 + 4 * Cmix * Real.log (Ups12 * mm0' * Theta0) := by
    have h := mul_le_mul_of_nonneg_left hlogargmono
      (by linarith only [hCmixnn] : (0 : ℝ) ≤ 4 * Cmix)
    linarith only [h]
  have harg2part_ge2 : (2 : ℝ) ≤ 2 + 4 * Cmix * Real.log (Ups12 * mm0 * Theta0) := by
    nlinarith only [hlogarg_nn, hCmixnn]
  have hsecmono : 3 * Theta0 * (2 + 4 * Cmix * Real.log (Ups12 * mm0 * Theta0)) ≤
      3 * Theta0 * (2 + 4 * Cmix * Real.log (Ups12 * mm0' * Theta0)) := by
    have hTheta0nn3 : (0 : ℝ) ≤ 3 * Theta0 := by linarith only [hTheta0pos]
    exact mul_le_mul_of_nonneg_left harg2part_mono hTheta0nn3
  have hsec_ge1 : (1 : ℝ) ≤ 3 * Theta0 * (2 + 4 * Cmix * Real.log (Ups12 * mm0 * Theta0)) := by
    have h3Theta0ge3 : (3 : ℝ) ≤ 3 * Theta0 := by linarith only [hTheta0ge1]
    nlinarith only [h3Theta0ge3, harg2part_ge2,
      mul_nonneg (by linarith only [h3Theta0ge3] : (0 : ℝ) ≤ 3 * Theta0 - 3)
        (by linarith only [harg2part_ge2] : (0 : ℝ) ≤
          2 + 4 * Cmix * Real.log (Ups12 * mm0 * Theta0) - 2)]
  have hlog2mono : Real.log (3 * Theta0 * (2 + 4 * Cmix * Real.log (Ups12 * mm0 * Theta0))) ≤
      Real.log (3 * Theta0 * (2 + 4 * Cmix * Real.log (Ups12 * mm0' * Theta0))) :=
    Real.log_le_log (lt_of_lt_of_le one_pos hsec_ge1) hsecmono
  have hlog2_nn : (0 : ℝ) ≤
      Real.log (3 * Theta0 * (2 + 4 * Cmix * Real.log (Ups12 * mm0 * Theta0))) :=
    Real.log_nonneg hsec_ge1
  have hlogarg'_nn : (0 : ℝ) ≤ Real.log (Ups12 * mm0' * Theta0) := Real.log_nonneg harg'_ge1
  have hprodmono : Real.log (Ups12 * mm0 * Theta0) *
      Real.log (3 * Theta0 * (2 + 4 * Cmix * Real.log (Ups12 * mm0 * Theta0))) ≤
      Real.log (Ups12 * mm0' * Theta0) *
      Real.log (3 * Theta0 * (2 + 4 * Cmix * Real.log (Ups12 * mm0' * Theta0))) :=
    mul_le_mul hlogargmono hlog2mono hlog2_nn hlogarg'_nn
  have hPrefnn : (0 : ℝ) ≤ 32 * C61 * (Cmix + 1) := by nlinarith only [hC61, hCmix]
  calc 32 * C61 * (Cmix + 1) *
      Real.log (Ups12 * mm0 * Theta0) *
      Real.log (3 * Theta0 * (2 + 4 * Cmix * Real.log (Ups12 * mm0 * Theta0)))
      = 32 * C61 * (Cmix + 1) *
        (Real.log (Ups12 * mm0 * Theta0) *
          Real.log (3 * Theta0 * (2 + 4 * Cmix * Real.log (Ups12 * mm0 * Theta0)))) := by ring
    _ ≤ 32 * C61 * (Cmix + 1) *
        (Real.log (Ups12 * mm0' * Theta0) *
          Real.log (3 * Theta0 * (2 + 4 * Cmix * Real.log (Ups12 * mm0' * Theta0)))) :=
        mul_le_mul_of_nonneg_left hprodmono hPrefnn
    _ = 32 * C61 * (Cmix + 1) *
        Real.log (Ups12 * mm0' * Theta0) *
        Real.log (3 * Theta0 * (2 + 4 * Cmix * Real.log (Ups12 * mm0' * Theta0))) := by ring

/-- **Corollary: monotone in the natural-number input scale, fixed
`m0`.** If the bigLog condition holds at input scale `m₂ : ℕ`, it holds at
any smaller natural input scale `m₁ ≤ m₂` (same `m0`). -/
theorem homogBelow_bigLog_monotone_in_m
    {C61 Cmix Ups12 Theta0 : ℝ}
    (hC61 : 1 ≤ C61) (hCmix : 1 ≤ Cmix) (hUps12ge1 : 1 ≤ Ups12) (hTheta0ge1 : 1 ≤ Theta0)
    {m0 m1 m2 : ℕ} (hm12 : m1 ≤ m2) :
    32 * C61 * (Cmix + 1) *
        Real.log (Ups12 * ((m1 : ℝ) + (m0 : ℝ) + 1) * Theta0) *
        Real.log (3 * Theta0 *
          (2 + 4 * Cmix * Real.log (Ups12 * ((m1 : ℝ) + (m0 : ℝ) + 1) * Theta0))) ≤
      32 * C61 * (Cmix + 1) *
        Real.log (Ups12 * ((m2 : ℝ) + (m0 : ℝ) + 1) * Theta0) *
        Real.log (3 * Theta0 *
          (2 + 4 * Cmix * Real.log (Ups12 * ((m2 : ℝ) + (m0 : ℝ) + 1) * Theta0))) := by
  have hmm0ge1 : (1 : ℝ) ≤ (m1 : ℝ) + (m0 : ℝ) + 1 := by
    have h1 : (0 : ℝ) ≤ (m1 : ℝ) := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ (m0 : ℝ) := Nat.cast_nonneg _
    linarith only [h1, h2]
  have hmm0le : (m1 : ℝ) + (m0 : ℝ) + 1 ≤ (m2 : ℝ) + (m0 : ℝ) + 1 := by
    have : (m1 : ℝ) ≤ (m2 : ℝ) := by exact_mod_cast hm12
    linarith only [this]
  exact homogBelow_bigLog_monotone_in_mm0 hC61 hCmix hUps12ge1 hTheta0ge1 hmm0ge1 hmm0le

end SuperdiffusionCLT.Section4.HomogBelow
