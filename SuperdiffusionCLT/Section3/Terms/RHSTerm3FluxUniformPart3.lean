/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3FluxUniformPart0
public import SuperdiffusionCLT.Section3.Terms.BlockConcentrationInputs
public import SuperdiffusionCLT.Probability.OrliczPower
public import SuperdiffusionCLT.Probability.OrliczIndexWeakening
public import SuperdiffusionCLT.Probability.GammaSigmaTsum

/-!
# The Γ₁ bound on the printed multiscale block weight

At every fixed depth, the block maximum costs its logarithmic cardinality in
the Γ₁ scale. Raising that maximum to power `3/4` gives a Γ₄/₃ bound, which
weakens to Γ₁. The depth weights `3^{-k}` sum these estimates, and their scalar
majorant has finite first moment. This proves clause (2) of
`fluxUniform_of_gaps` for the fixed weight of `RHSTerm3FluxUniformPart0`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open Homogenization
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal NNReal

noncomputable section

private def fluxOrlicz_depthGrowthConst (d : ℕ) : ℝ :=
  3 * (d : ℝ) * Real.log 3

private def fluxOrlicz_seriesFactor (d : ℕ) : ℝ :=
  max 1 (fluxOrlicz_depthGrowthConst d)

private def fluxOrlicz_seriesMoment : ℝ :=
  ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * ((1 / 3 : ℝ) ^ k)

private theorem fluxOrlicz_depthGrowthConst_pos {d : ℕ} (hd : 0 < d) :
    0 < fluxOrlicz_depthGrowthConst d := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  exact mul_pos (mul_pos (by norm_num) hdR) hlog

private theorem fluxOrlicz_seriesMoment_summable :
    Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * ((1 / 3 : ℝ) ^ k)) := by
  have hq : ‖(1 / 3 : ℝ)‖ < 1 := by norm_num
  have hgeom : Summable (fun k : ℕ => (1 / 3 : ℝ) ^ k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hnat := summable_pow_mul_geometric_of_norm_lt_one 1 hq
  convert hnat.add hgeom using 1 with k
  push_cast
  ring_nf

private theorem fluxOrlicz_seriesMoment_pos : 0 < fluxOrlicz_seriesMoment := by
  have h := fluxOrlicz_seriesMoment_summable.sum_le_tsum ({0} : Finset ℕ)
    (fun k _ => mul_nonneg (by positivity) (by positivity))
  have h' : (1 : ℝ) ≤ fluxOrlicz_seriesMoment := by
    simpa [fluxOrlicz_seriesMoment] using h
  exact lt_of_lt_of_le zero_lt_one h'

private theorem fluxOrlicz_card_depth {d : ℕ} (R : TriadicCube d) (k : ℕ) :
    (descendantsAtDepth R k).card = (3 ^ d) ^ k :=
  Homogenization.descendantsAtDepth_card R k

private theorem fluxOrlicz_log_card_depth {d : ℕ} (R : TriadicCube d) (k : ℕ) :
    Real.log ((descendantsAtDepth R k).card : ℝ) =
      (k : ℝ) * ((d : ℝ) * Real.log 3) := by
  have hcard : ((descendantsAtDepth R k).card : ℝ) = ((3 : ℝ) ^ d) ^ k := by
    rw [fluxOrlicz_card_depth]
    norm_cast
  rw [hcard, Real.log_pow, Real.log_pow]

private theorem fluxOrlicz_two_le_card_depth {d : ℕ} (hd : 0 < d)
    {R : TriadicCube d} {k : ℕ} (hk : 0 < k) :
    2 ≤ (descendantsAtDepth R k).card := by
  have hbase : 2 ≤ 3 ^ d := by
    calc (2 : ℕ) ≤ 3 ^ 1 := by norm_num
      _ ≤ 3 ^ d := Nat.pow_le_pow_right (by norm_num) hd
  rw [fluxOrlicz_card_depth]
  exact hbase.trans (Nat.le_self_pow (Nat.ne_of_gt hk) _)

private theorem fluxOrlicz_nu_le_envelopeScale {d : ℕ} {nu : ℝ}
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (L : ℕ) (hL : 1 ≤ L) :
    nu ≤ cutoffEnvelopeConst d * nu⁻¹ * (L : ℝ) := by
  have hC1 : (1 : ℝ) ≤ cutoffEnvelopeConst d :=
    SuperdiffusionCLT.Section2.Annealed.one_le_cutoffEnvelopeConst d
  have hC0 : 0 ≤ cutoffEnvelopeConst d := le_of_lt (cutoffEnvelopeConst_pos d)
  have hsq : nu * nu ≤ 1 := by
    have h1 : nu * nu ≤ 1 * nu := mul_le_mul_of_nonneg_right hnu1 hnu.le
    have h2 : 1 * nu ≤ 1 * 1 := mul_le_mul_of_nonneg_left hnu1 zero_le_one
    linarith only [h1, h2]
  have e1 : (1 : ℝ) ≤ cutoffEnvelopeConst d * (L : ℝ) :=
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ cutoffEnvelopeConst d * 1 := mul_le_mul_of_nonneg_right hC1 zero_le_one
      _ ≤ cutoffEnvelopeConst d * (L : ℝ) :=
        mul_le_mul_of_nonneg_left (Nat.one_le_cast.2 hL) hC0
  have h2 : nu * nu ≤ cutoffEnvelopeConst d * (L : ℝ) := by
    linarith only [hsq, e1]
  have h3 : nu ≤ cutoffEnvelopeConst d * (L : ℝ) / nu := (le_div_iff₀ hnu).2 h2
  calc nu ≤ cutoffEnvelopeConst d * (L : ℝ) / nu := h3
    _ = cutoffEnvelopeConst d * nu⁻¹ * (L : ℝ) := by ring

private theorem fluxOrlicz_envelope_le {d : ℕ} {nu : ℝ}
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (L : ℕ) (hL : 1 ≤ L) :
    envelopeUpperScalar d nu L ≤
      (3 * cutoffEnvelopeConst d) * ((L : ℝ) * nu⁻¹) := by
  have hC0 : 0 ≤ cutoffEnvelopeConst d := le_of_lt (cutoffEnvelopeConst_pos d)
  have hmax : max 1 (L : ℝ) ≤ (L : ℝ) :=
    max_le (Nat.one_le_cast.2 hL) (le_refl _)
  have hterm : 2 * cutoffEnvelopeConst d * nu⁻¹ * max 1 (L : ℝ) ≤
      2 * cutoffEnvelopeConst d * nu⁻¹ * (L : ℝ) :=
    mul_le_mul_of_nonneg_left hmax (by positivity)
  have hnuScale := fluxOrlicz_nu_le_envelopeScale (d := d) hnu hnu1 L hL
  unfold envelopeUpperScalar
  calc nu + 2 * cutoffEnvelopeConst d * nu⁻¹ * max 1 (L : ℝ)
      ≤ nu + 2 * cutoffEnvelopeConst d * nu⁻¹ * (L : ℝ) := add_le_add_right hterm nu
    _ ≤ 3 * (cutoffEnvelopeConst d * nu⁻¹ * (L : ℝ)) := by
      have hterm' : 2 * cutoffEnvelopeConst d * nu⁻¹ * (L : ℝ) =
          2 * (cutoffEnvelopeConst d * nu⁻¹ * (L : ℝ)) := by ring
      linarith only [hnuScale, hterm']
    _ = (3 * cutoffEnvelopeConst d) * ((L : ℝ) * nu⁻¹) := by ring

private theorem fluxOrlicz_measurable_blockMax {d : ℕ} [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (L : ℕ) (R : TriadicCube d) (k : ℕ) :
    Measurable (fun omega : ShellSeq d =>
      (fluxUniformBlockMax nu L omega R k : ℝ)) := by
  let s := descendantsAtDepth R k
  have hs : s.Nonempty := descendantsAtDepth_nonempty R k
  have hmax : Measurable (s.sup' hs fun Q omega =>
      (translatedBlockNorm nu L omega Q).toNNReal) :=
    Finset.measurable_sup' hs (fun Q _ =>
      (measurable_translatedBlockNorm hnu L Q).real_toNNReal)
  have heq : (s.sup' hs fun Q omega =>
      (translatedBlockNorm nu L omega Q).toNNReal) =
    fun omega => fluxUniformBlockMax nu L omega R k := by
    funext omega
    change (s.sup' hs (fun Q omega' =>
      (translatedBlockNorm nu L omega' Q).toNNReal) omega) =
        s.sup (fun Q => (translatedBlockNorm nu L omega Q).toNNReal)
    simp only [Finset.sup'_apply, Finset.sup'_eq_sup hs]
  have hmeasNN : Measurable (fun omega : ShellSeq d => fluxUniformBlockMax nu L omega R k) := by
    rw [← heq]
    exact hmax
  exact NNReal.continuous_coe.measurable.comp hmeasNN

private theorem fluxOrlicz_blockMax_isBigO {d : ℕ} [NeZero d]
    {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (L : ℕ) (R : TriadicCube d) (k : ℕ) :
    IsBigO P.toMeasure (gammaSigma 1)
      (fun omega : ShellSeq d => (fluxUniformBlockMax nu L omega R k : ℝ))
      ((1 + fluxOrlicz_depthGrowthConst d * (k : ℝ)) * envelopeUpperScalar d nu L) := by
  classical
  let s := descendantsAtDepth R k
  have hs : s.Nonempty := descendantsAtDepth_nonempty R k
  have hEpos : 0 < envelopeUpperScalar d nu L := envelopeUpperScalar_pos hnu d L
  have henv : ∀ Q ∈ s,
      IsBigO P.toMeasure (gammaSigma 1)
        (fun omega : ShellSeq d => translatedBlockNorm nu L omega Q)
        (envelopeUpperScalar d nu L) := by
    intro Q hQ
    exact isBigO_gammaSigma_translatedBlockNorm_envelope hnu hPrefix hJ2 hJ3 hJ4 L Q
  by_cases hk : k = 0
  · subst k
    have hQ : R ∈ descendantsAtDepth R 0 := by simp
    have hbase := henv R hQ
    have heq : (fun omega : ShellSeq d =>
        (fluxUniformBlockMax nu L omega R 0 : ℝ)) =
        (fun omega : ShellSeq d => translatedBlockNorm nu L omega R) := by
      funext omega
      simp only [fluxUniformBlockMax, descendantsAtDepth_zero, Finset.sup_singleton]
      exact Real.coe_toNNReal _ (Book.Ch02.matrixOperatorNorm_nonneg _)
    rw [heq]
    simpa using hbase
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hcard := fluxOrlicz_two_le_card_depth (R := R) (NeZero.pos d) hkpos
    let X : TriadicCube d → ShellSeq d → ℝ := fun Q omega =>
      translatedBlockNorm nu L omega Q
    have hsup := IndependentSums.isBigO_gammaSigma_finset_sup'_of_scales
      (μ := P.toMeasure) (s := s) (hs := hs)
      (X := X) (a := fun _ => envelopeUpperScalar d nu L) (σ := 1)
      (by norm_num) hcard (fun Q hQ => henv Q hQ)
    have hsup' : IsBigO P.toMeasure (gammaSigma 1)
        (fun omega : ShellSeq d => s.sup' hs (fun Q => X Q omega))
        ((3 * Real.log (s.card : ℝ)) * envelopeUpperScalar d nu L) := by
      simpa only [Finset.sup'_const, inv_one, Real.rpow_one] using hsup
    have hmax_nonneg : ∀ omega : ShellSeq d,
        0 ≤ s.sup' hs (fun Q => X Q omega) := by
      intro omega
      rcases hs with ⟨Q, hQ⟩
      exact (Book.Ch02.matrixOperatorNorm_nonneg _).trans
        (Finset.le_sup' (fun Q : TriadicCube d => X Q omega) hQ)
    have hblock_le : ∀ omega : ShellSeq d,
        (fluxUniformBlockMax nu L omega R k : ℝ) ≤ s.sup' hs (fun Q => X Q omega) := by
      intro omega
      have hsupNN : s.sup (fun Q => (translatedBlockNorm nu L omega Q).toNNReal) ≤
          (s.sup' hs (fun Q => X Q omega)).toNNReal := by
        apply Finset.sup_le
        intro Q hQ
        apply (Real.toNNReal_le_toNNReal_iff (hmax_nonneg omega)).2
        exact Finset.le_sup' _ hQ
      rw [fluxUniformBlockMax]
      rw [← Real.coe_toNNReal _ (hmax_nonneg omega)]
      exact_mod_cast hsupNN
    have hdom : IsBigO P.toMeasure (gammaSigma 1)
        (fun omega : ShellSeq d => (fluxUniformBlockMax nu L omega R k : ℝ))
        ((3 * Real.log (s.card : ℝ)) * envelopeUpperScalar d nu L) := by
      refine hsup'.of_abs_le fun omega => ?_
      rw [abs_of_nonneg (NNReal.coe_nonneg _), abs_of_nonneg (hmax_nonneg omega)]
      exact hblock_le omega
    have hlog : 3 * Real.log (s.card : ℝ) =
        fluxOrlicz_depthGrowthConst d * (k : ℝ) := by
      dsimp [s, fluxOrlicz_depthGrowthConst]
      rw [fluxOrlicz_log_card_depth]
      ring
    have hscale :
        (3 * Real.log (s.card : ℝ)) * envelopeUpperScalar d nu L ≤
          (1 + fluxOrlicz_depthGrowthConst d * (k : ℝ)) * envelopeUpperScalar d nu L := by
      rw [hlog]
      exact mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left (show 0 ≤ (1 : ℝ) by norm_num)) hEpos.le
    exact hdom.mono_scale hscale

private theorem fluxOrlicz_blockMax_power_isBigO {d : ℕ} [NeZero d]
    {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (L : ℕ) (R : TriadicCube d) (k : ℕ) :
    IsBigO P.toMeasure (gammaSigma 1)
      (fun omega : ShellSeq d =>
        (fluxUniformBlockMax nu L omega R k : ℝ) ^ ((3 : ℝ) / 4))
      (fluxOrlicz_seriesFactor d * ((k + 1 : ℕ) : ℝ) *
        (envelopeUpperScalar d nu L) ^ ((3 : ℝ) / 4)) := by
  have hD1 : (1 : ℝ) ≤ fluxOrlicz_seriesFactor d := le_max_left _ _
  have hcpos : 0 < fluxOrlicz_depthGrowthConst d :=
    fluxOrlicz_depthGrowthConst_pos (NeZero.pos d)
  have hcD : fluxOrlicz_depthGrowthConst d ≤ fluxOrlicz_seriesFactor d := le_max_right _ _
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
  have hk1' : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  have hDk1 : (1 : ℝ) ≤ fluxOrlicz_seriesFactor d * ((k + 1 : ℕ) : ℝ) := by
    calc (1 : ℝ) ≤ fluxOrlicz_seriesFactor d := hD1
      _ = fluxOrlicz_seriesFactor d * 1 := by ring
      _ ≤ fluxOrlicz_seriesFactor d * ((k + 1 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hk1' (le_trans zero_le_one hD1)
  have hbase : 1 + fluxOrlicz_depthGrowthConst d * (k : ℝ) ≤
      fluxOrlicz_seriesFactor d * ((k + 1 : ℕ) : ℝ) := by
    have hfirst : (1 : ℝ) ≤ fluxOrlicz_seriesFactor d := hD1
    have hsecond := mul_le_mul_of_nonneg_right hcD hk0
    calc 1 + fluxOrlicz_depthGrowthConst d * (k : ℝ)
        ≤ fluxOrlicz_seriesFactor d + fluxOrlicz_seriesFactor d * (k : ℝ) :=
          add_le_add hfirst hsecond
      _ = fluxOrlicz_seriesFactor d * ((k + 1 : ℕ) : ℝ) := by push_cast; ring
  have hEpos := envelopeUpperScalar_pos hnu d L
  have hE0 := hEpos.le
  have hmax := fluxOrlicz_blockMax_isBigO hnu P hPrefix hJ2 hJ3 hJ4 L R k
  have hscale0 : 0 ≤ 1 + fluxOrlicz_depthGrowthConst d * (k : ℝ) :=
    le_trans zero_le_one (le_add_of_nonneg_right (mul_nonneg hcpos.le hk0))
  have hpowered := SuperdiffusionCLT.Probability.isBigO_gammaSigma_rpow_fwd
    (mu := P.toMeasure) (hp := (by norm_num : (0 : ℝ) < (3 : ℝ) / 4))
    (hK := mul_nonneg hscale0 hE0)
    (hX := fun omega => NNReal.coe_nonneg (fluxUniformBlockMax nu L omega R k)) hmax
  have hindex : (1 : ℝ) ≤ (1 : ℝ) / ((3 : ℝ) / 4) := by norm_num
  have hweak := SuperdiffusionCLT.Probability.isBigO_gammaSigma_of_exponent_le
    hindex hpowered
  have hpowScale :
      ((1 + fluxOrlicz_depthGrowthConst d * (k : ℝ)) * envelopeUpperScalar d nu L) ^
          ((3 : ℝ) / 4) ≤
        fluxOrlicz_seriesFactor d * ((k + 1 : ℕ) : ℝ) *
          (envelopeUpperScalar d nu L) ^ ((3 : ℝ) / 4) := by
    have hleft : 0 ≤ 1 + fluxOrlicz_depthGrowthConst d * (k : ℝ) := hscale0
    have hmono := Real.rpow_le_rpow hleft hbase (by norm_num : 0 ≤ (3 : ℝ) / 4)
    have hfac := Real.rpow_le_self_of_one_le hDk1 (by norm_num : (3 : ℝ) / 4 ≤ 1)
    rw [Real.mul_rpow hleft hE0]
    exact mul_le_mul_of_nonneg_right (hmono.trans hfac) (Real.rpow_nonneg hE0 _)
  exact hweak.mono_scale hpowScale

private theorem fluxOrlicz_depthTerm_eq_ofReal {d : ℕ} (nu : ℝ) (L : ℕ)
    (R : TriadicCube d) (k : ℕ) (omega : ShellSeq d) :
    ENNReal.ofReal ((3 : ℝ) ^ (-(k : ℝ))) *
        ((fluxUniformBlockMax nu L omega R k : ℝ≥0∞) ^ ((3 : ℝ) / 4)) =
      ENNReal.ofReal (((3 : ℝ) ^ (-(k : ℝ))) *
        (fluxUniformBlockMax nu L omega R k : ℝ) ^ ((3 : ℝ) / 4)) := by
  have hbase : (fluxUniformBlockMax nu L omega R k : ℝ≥0∞) =
      ENNReal.ofReal (fluxUniformBlockMax nu L omega R k : ℝ) := by simp
  rw [hbase, ENNReal.ofReal_rpow_of_nonneg (NNReal.coe_nonneg _) (by norm_num)]
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]

private def fluxOrlicz_depthTerm {d : ℕ} (nu : ℝ) (L : ℕ)
    (R : TriadicCube d) (k : ℕ) (omega : ShellSeq d) : ℝ :=
  ((3 : ℝ) ^ (-(k : ℝ))) *
    (fluxUniformBlockMax nu L omega R k : ℝ) ^ ((3 : ℝ) / 4)

private theorem fluxOrlicz_depthTerm_measurable {d : ℕ} [NeZero d]
    {nu : ℝ} (hnu : 0 < nu) (L : ℕ) (R : TriadicCube d) (k : ℕ) :
    Measurable (fun omega : ShellSeq d => fluxOrlicz_depthTerm nu L R k omega) := by
  have hmax := fluxOrlicz_measurable_blockMax hnu L R k
  have hpow : Measurable (fun omega : ShellSeq d =>
      (fluxUniformBlockMax nu L omega R k : ℝ) ^ ((3 : ℝ) / 4)) :=
    (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ (3 : ℝ) / 4)).measurable.comp hmax
  exact measurable_const.mul hpow

private theorem fluxOrlicz_depthTerm_isBigO {d : ℕ} [NeZero d]
    {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (L : ℕ) (R : TriadicCube d) (k : ℕ) :
    IsBigO P.toMeasure (gammaSigma 1) (fun omega => fluxOrlicz_depthTerm nu L R k omega)
      (((1 / 3 : ℝ) ^ k) * fluxOrlicz_seriesFactor d * ((k + 1 : ℕ) : ℝ) *
        (envelopeUpperScalar d nu L) ^ ((3 : ℝ) / 4)) := by
  have hpow := fluxOrlicz_blockMax_power_isBigO hnu P hPrefix hJ2 hJ3 hJ4 L R k
  have hcoef : (3 : ℝ) ^ (-(k : ℝ)) = (1 / 3 : ℝ) ^ k := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3) (k : ℝ),
      Real.rpow_natCast, ← inv_pow]
    norm_num
  have hcoefpos : 0 < (1 / 3 : ℝ) ^ k := by positivity
  change IsBigO P.toMeasure (gammaSigma 1)
    (fun omega : ShellSeq d => ((3 : ℝ) ^ (-(k : ℝ))) *
      (fluxUniformBlockMax nu L omega R k : ℝ) ^ ((3 : ℝ) / 4)) _
  rw [hcoef]
  simpa only [abs_of_pos hcoefpos, mul_assoc] using
    hpow.const_mul hcoefpos.le

private theorem fluxOrlicz_depthTerm_amplitude_summable {d : ℕ} {E : ℝ} :
    Summable (fun k : ℕ => ((1 / 3 : ℝ) ^ k) * fluxOrlicz_seriesFactor d *
      ((k + 1 : ℕ) : ℝ) * E ^ ((3 : ℝ) / 4)) := by
  have hmoment := fluxOrlicz_seriesMoment_summable
  convert hmoment.mul_left (fluxOrlicz_seriesFactor d * E ^ ((3 : ℝ) / 4)) using 1 with k
  funext k
  ring

private theorem fluxOrlicz_depthTerm_amplitude_sum {d : ℕ} {E : ℝ} :
    (∑' k : ℕ, ((1 / 3 : ℝ) ^ k) * fluxOrlicz_seriesFactor d *
      ((k + 1 : ℕ) : ℝ) * E ^ ((3 : ℝ) / 4)) =
      (fluxOrlicz_seriesFactor d * E ^ ((3 : ℝ) / 4)) * fluxOrlicz_seriesMoment := by
  have hEq : (fun k : ℕ => ((1 / 3 : ℝ) ^ k) * fluxOrlicz_seriesFactor d *
      ((k + 1 : ℕ) : ℝ) * E ^ ((3 : ℝ) / 4)) =
      (fun k => (fluxOrlicz_seriesFactor d * E ^ ((3 : ℝ) / 4)) *
        (((k + 1 : ℕ) : ℝ) * ((1 / 3 : ℝ) ^ k))) := by
    funext k
    ring
  rw [hEq, tsum_mul_left]
  rfl

/-- **Clause (2) of `fluxUniform_of_gaps`, at the fixed Part0 block weight.**
The bound holds on every triadic cube, so in particular on the selected
`largeCubeSubcubes`. Its constant depends only on dimension. -/
theorem fluxOrlicz_main (d : ℕ) [NeZero d] :
    ∃ Cb : ℝ, 0 < Cb ∧
      ∀ (nu : ℝ) (_hnu : 0 < nu) (_hnu1 : nu ≤ 1)
        (P : ProbabilityMeasure (ShellSeq d))
        (_hPrefix : ShellLawPrefix d P) (_hJ1V2 : ShellLawJ1Restriction d P)
        (_hJ2 : ShellLawJ2 d P) (_hJ3 : ShellLawJ3 d P) (_hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (_hSorder : ScalesOrdering S)
        (_e : Vec d) (_he : vecNormSq _e = 1)
        (R : TriadicCube d), R ∈ largeCubeSubcubes d S.n S.m →
        IsBigO P.toMeasure (gammaSigma 1)
          (fun omega : ShellSeq d => fluxUniformBlockWeight nu S P _e omega R)
          (Cb * (((S.LPrime : ℕ) : ℝ) * nu⁻¹) ^ ((3 : ℝ) / 4)) := by
  classical
  refine ⟨IndependentSums.gammaTriangleConst 1 *
      (fluxOrlicz_seriesFactor d * fluxOrlicz_seriesMoment) *
      (3 * cutoffEnvelopeConst d) ^ ((3 : ℝ) / 4), ?_, ?_⟩
  · have hgamma := IndependentSums.gammaTriangleConst_pos (σ := (1 : ℝ))
    have hfactor : 0 < fluxOrlicz_seriesFactor d := by
      exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hseries := fluxOrlicz_seriesMoment_pos
    have henv : 0 < 3 * cutoffEnvelopeConst d :=
      mul_pos (by norm_num) (cutoffEnvelopeConst_pos d)
    have hpow : 0 < (3 * cutoffEnvelopeConst d) ^ ((3 : ℝ) / 4) :=
      Real.rpow_pos_of_pos henv _
    exact mul_pos (mul_pos hgamma (mul_pos hfactor hseries)) hpow
  · intro nu hnu hnu1 P hPrefix _hJ1V2 hJ2 hJ3 hJ4 S hSorder e _he R _hR
    have hLPrime : 1 ≤ S.LPrime := by
      have hmLP := hSorder.m_lt_LPrime
      omega
    have hEpos := envelopeUpperScalar_pos hnu d S.LPrime
    have hEnv := fluxOrlicz_envelope_le (d := d) hnu hnu1 S.LPrime hLPrime
    have hdepthMeas : ∀ k : ℕ, Measurable (fun omega : ShellSeq d =>
        fluxOrlicz_depthTerm nu S.LPrime R k omega) := by
      intro k
      exact fluxOrlicz_depthTerm_measurable hnu S.LPrime R k
    have hdepthBigO : ∀ k : ℕ,
        IsBigO P.toMeasure (gammaSigma 1)
          (fun omega : ShellSeq d => fluxOrlicz_depthTerm nu S.LPrime R k omega)
          (((1 / 3 : ℝ) ^ k) * fluxOrlicz_seriesFactor d * ((k + 1 : ℕ) : ℝ) *
            (envelopeUpperScalar d nu S.LPrime) ^ ((3 : ℝ) / 4)) := by
      intro k
      exact fluxOrlicz_depthTerm_isBigO hnu P hPrefix hJ2 hJ3 hJ4 S.LPrime R k
    have hApos : ∀ k : ℕ, 0 ≤
        ((1 / 3 : ℝ) ^ k) * fluxOrlicz_seriesFactor d * ((k + 1 : ℕ) : ℝ) *
          (envelopeUpperScalar d nu S.LPrime) ^ ((3 : ℝ) / 4) := by
      intro k
      have hfactor : 0 ≤ fluxOrlicz_seriesFactor d :=
        le_trans zero_le_one (le_max_left _ _)
      positivity
    have hAsum := fluxOrlicz_depthTerm_amplitude_summable (d := d)
      (E := envelopeUpperScalar d nu S.LPrime)
    have htsum := SuperdiffusionCLT.Probability.isBigO_gammaSigma_tsum
      (mu := P.toMeasure) (hsigma := (by norm_num : (0 : ℝ) < 1))
      (hA := hAsum) (hApos := hApos) (hmeas := hdepthMeas) (hbigO := hdepthBigO)
    have hweight : IsBigO P.toMeasure (gammaSigma 1)
        (fun omega : ShellSeq d => fluxUniformBlockWeight nu S P e omega R)
        (IndependentSums.gammaTriangleConst 1 *
          ((fluxOrlicz_seriesFactor d *
            (envelopeUpperScalar d nu S.LPrime) ^ ((3 : ℝ) / 4)) *
            fluxOrlicz_seriesMoment)) := by
      have heq : (fun omega : ShellSeq d => fluxUniformBlockWeight nu S P e omega R) =
          (fun omega : ShellSeq d => ∑' k : ℕ, fluxOrlicz_depthTerm nu S.LPrime R k omega) := by
        funext omega
        unfold fluxUniformBlockWeight fluxUniformBlockWeightE
        rw [ENNReal.tsum_toReal_eq (fun k => by
          rw [fluxOrlicz_depthTerm_eq_ofReal]
          exact ENNReal.ofReal_ne_top)]
        refine tsum_congr fun k => ?_
        rw [fluxOrlicz_depthTerm_eq_ofReal]
        exact ENNReal.toReal_ofReal (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
          (Real.rpow_nonneg (NNReal.coe_nonneg _) _))
      rw [heq]
      have hsum := fluxOrlicz_depthTerm_amplitude_sum (d := d)
        (E := envelopeUpperScalar d nu S.LPrime)
      rw [hsum] at htsum
      simpa only [mul_assoc] using htsum
    have hEpow : (envelopeUpperScalar d nu S.LPrime) ^ ((3 : ℝ) / 4) ≤
        (3 * cutoffEnvelopeConst d) ^ ((3 : ℝ) / 4) *
          (((S.LPrime : ℕ) : ℝ) * nu⁻¹) ^ ((3 : ℝ) / 4) := by
      have hA0 : 0 ≤ ((S.LPrime : ℕ) : ℝ) * nu⁻¹ := by positivity
      have hC0 : 0 ≤ 3 * cutoffEnvelopeConst d :=
        mul_nonneg (by norm_num) (le_of_lt (cutoffEnvelopeConst_pos d))
      have hEnv0 : 0 ≤ envelopeUpperScalar d nu S.LPrime := hEpos.le
      rw [← Real.mul_rpow hC0 hA0]
      exact Real.rpow_le_rpow hEnv0 hEnv (by norm_num)
    have hscale :
        IndependentSums.gammaTriangleConst 1 *
            ((fluxOrlicz_seriesFactor d *
              (envelopeUpperScalar d nu S.LPrime) ^ ((3 : ℝ) / 4)) *
              fluxOrlicz_seriesMoment) ≤
          (IndependentSums.gammaTriangleConst 1 *
            (fluxOrlicz_seriesFactor d * fluxOrlicz_seriesMoment) *
            (3 * cutoffEnvelopeConst d) ^ ((3 : ℝ) / 4)) *
            (((S.LPrime : ℕ) : ℝ) * nu⁻¹) ^ ((3 : ℝ) / 4) := by
      have hgamma0 : 0 ≤ IndependentSums.gammaTriangleConst 1 :=
        IndependentSums.gammaTriangleConst_pos (σ := (1 : ℝ)).le
      have hfactor0 : 0 ≤ fluxOrlicz_seriesFactor d :=
        le_trans zero_le_one (le_max_left _ _)
      have hseries0 : 0 ≤ fluxOrlicz_seriesMoment :=
        le_of_lt fluxOrlicz_seriesMoment_pos
      have hcoef : 0 ≤ IndependentSums.gammaTriangleConst 1 *
          (fluxOrlicz_seriesFactor d * fluxOrlicz_seriesMoment) :=
        mul_nonneg hgamma0 (mul_nonneg hfactor0 hseries0)
      calc IndependentSums.gammaTriangleConst 1 *
              ((fluxOrlicz_seriesFactor d *
                (envelopeUpperScalar d nu S.LPrime) ^ ((3 : ℝ) / 4)) *
                fluxOrlicz_seriesMoment)
          = (IndependentSums.gammaTriangleConst 1 *
              (fluxOrlicz_seriesFactor d * fluxOrlicz_seriesMoment)) *
              (envelopeUpperScalar d nu S.LPrime) ^ ((3 : ℝ) / 4) := by ring
        _ ≤ (IndependentSums.gammaTriangleConst 1 *
              (fluxOrlicz_seriesFactor d * fluxOrlicz_seriesMoment)) *
              ((3 * cutoffEnvelopeConst d) ^ ((3 : ℝ) / 4) *
                (((S.LPrime : ℕ) : ℝ) * nu⁻¹) ^ ((3 : ℝ) / 4)) :=
          mul_le_mul_of_nonneg_left hEpow hcoef
        _ = (IndependentSums.gammaTriangleConst 1 *
              (fluxOrlicz_seriesFactor d * fluxOrlicz_seriesMoment) *
              (3 * cutoffEnvelopeConst d) ^ ((3 : ℝ) / 4)) *
              (((S.LPrime : ℕ) : ℝ) * nu⁻¹) ^ ((3 : ℝ) / 4) := by ring
    exact hweight.mono_scale hscale

end

end SuperdiffusionCLT.Section3.Terms
