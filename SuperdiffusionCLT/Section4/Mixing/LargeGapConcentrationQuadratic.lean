/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.Mixing.LargeGapConcentrationEntrySum
public import SuperdiffusionCLT.Section4.Mixing.Term1PolarizedBound
public import SuperdiffusionCLT.Probability.GammaSigmaHelpers

/-!
# The entrywise sum envelope, and the deterministic quadratic-form bound

The uniform-in-`(p,q)` witness `X4` that the main statement
`Frozen.Section4.mixing_below_cutoff` needs cannot come from the
polarization trick `Section4.Mixing.mixTerms_term1PolarizedBound` uses (there
the witnesses `X1,X2,X3` are chosen *after* `p, q`, inside their quantifier);
it must instead be a genuine matrix-size witness, uniform over all `(p,q)`.
This file builds it as the entrywise-`ℓ¹` sum of the four blocks' entry
deviations,

`E(ω) := ∑_{i,j}|ΔUL(i,j)(ω)| + ∑_{i,j}|ΔUR(i,j)(ω)| + ∑_{i,j}|ΔLL(i,j)(ω)| +
  ∑_{i,j}|ΔLR(i,j)(ω)|`,

each block's double sum concentrated by `mixGap_entryDeviation_concentration`
and combined by the `Γ1` triangle inequality
(`Homogenization.IndependentSums.isBigO_finset_sum_of_isBigO_gammaSigma`
within a block, `SuperdiffusionCLT.Probability.isBigO_gammaSigma_add_of_isBigO`
across the four blocks), and proves the deterministic bound

`2 · avg_z (p·H(z)q) ≤ E(ω) · (p·Ahom p + q·Ahom q)`

via the elementary two-real fact `2abc ≤ |c|(a²+b²)` applied entrywise. -/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

open Homogenization
open Homogenization.IndependentSums
open MeasureTheory ProbabilityTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Probability (isBigO_gammaSigma_add_of_isBigO)

noncomputable section

variable {d : ℕ}

/-! ## The averaged entry deviation and the entrywise-`ℓ¹` sum envelope -/

/-- The lattice average of the centred entry `bfA_L(z+cu_n)_{αβ} -
bfAhom_L(cu_n)_{αβ}` over `z ∈ 3^nℤ^d ∩ cu_m`. -/
def mixGap_avgEntryDeviation [NeZero d] (nu : ℝ) (L : ℕ) (P : ProbabilityMeasure (ShellSeq d))
    (nn m : ℕ) (alpha beta : BlockCoord d) (omega : ShellSeq d) : ℝ :=
  ((descendantsAtDepth (originCube d (m : ℤ)) (m - nn)).card : ℝ)⁻¹ *
    ∑ z ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - nn),
      (blockMatEntry (coarseBlockMatrix (cubeSet z) (coefficientCutoff nu omega L).toCoeffField)
          alpha beta -
        blockMatEntry (annealedBlockMatrix nu L P (cubeSet (originCube d (nn : ℤ)))) alpha beta)

/-- **The entrywise-`ℓ¹` sum envelope**, the uniform-in-`(p,q)` witness. -/
def mixGap_entrySumEnvelope [NeZero d] (nu : ℝ) (L : ℕ) (P : ProbabilityMeasure (ShellSeq d))
    (nn m : ℕ) (omega : ShellSeq d) : ℝ :=
  (∑ i : Fin d, ∑ j : Fin d, |mixGap_avgEntryDeviation nu L P nn m (Sum.inl i) (Sum.inl j) omega|) +
    (∑ i : Fin d, ∑ j : Fin d, |mixGap_avgEntryDeviation nu L P nn m (Sum.inl i) (Sum.inr j) omega|) +
    (∑ i : Fin d, ∑ j : Fin d, |mixGap_avgEntryDeviation nu L P nn m (Sum.inr i) (Sum.inl j) omega|) +
    (∑ i : Fin d, ∑ j : Fin d, |mixGap_avgEntryDeviation nu L P nn m (Sum.inr i) (Sum.inr j) omega|)

theorem mixGap_measurable_avgEntryDeviation [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)} (L nn m : ℕ) (alpha beta : BlockCoord d) :
    Measurable fun omega : ShellSeq d => mixGap_avgEntryDeviation nu L P nn m alpha beta omega := by
  unfold mixGap_avgEntryDeviation
  refine Measurable.const_mul ?_ _
  exact Finset.measurable_sum _ fun z _ =>
    (measurable_blockMatEntry_coarseBlockMatrix hnu L z alpha beta).sub measurable_const

theorem mixGap_measurable_entrySumEnvelope [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)} (L nn m : ℕ) :
    Measurable fun omega : ShellSeq d => mixGap_entrySumEnvelope nu L P nn m omega := by
  unfold mixGap_entrySumEnvelope
  refine ((Measurable.add ?_ ?_).add ?_).add ?_
  · exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
      continuous_abs.measurable.comp (mixGap_measurable_avgEntryDeviation (P := P) hnu L nn m (Sum.inl i) (Sum.inl j))
  · exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
      continuous_abs.measurable.comp (mixGap_measurable_avgEntryDeviation (P := P) hnu L nn m (Sum.inl i) (Sum.inr j))
  · exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
      continuous_abs.measurable.comp (mixGap_measurable_avgEntryDeviation (P := P) hnu L nn m (Sum.inr i) (Sum.inl j))
  · exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
      continuous_abs.measurable.comp (mixGap_measurable_avgEntryDeviation (P := P) hnu L nn m (Sum.inr i) (Sum.inr j))

/-! ## The `Γ1` concentration of the envelope -/

/-- The per-entry concentration amplitude, one lattice-scale and colour-count
factor. -/
def mixGap_perEntryAmp (d : ℕ) (nu : ℝ) (L m : ℕ) : ℝ :=
  2 * gammaTriangleConst 1 * gammaOneExpRegimeConst *
    Real.sqrt (((ShellField.shellColorPeriod d : ℕ) : ℝ) ^ d) *
    (mixGap_entryEnvelope d nu L +
      IndependentSums.gammaMomentConst 1 * mixGap_entryEnvelope d nu L) *
    (3 : ℝ) ^ (-((d : ℝ) * ((m - L : ℕ) : ℝ)) / 2)

theorem mixGap_perEntryAmp_pos {nu : ℝ} (hnu : 0 < nu) (d L m : ℕ) :
    0 < mixGap_perEntryAmp d nu L m := by
  have h1 : (0 : ℝ) < mixGap_entryEnvelope d nu L := mixGap_entryEnvelope_pos hnu d L
  have h2 : (0 : ℝ) ≤ IndependentSums.gammaMomentConst 1 * mixGap_entryEnvelope d nu L := by
    have := IndependentSums.gammaMomentConst_pos (σ := (1 : ℝ)) one_pos
    positivity
  have h3 : (0 : ℝ) < gammaTriangleConst (1 : ℝ) := gammaTriangleConst_pos
  have h4 : (0 : ℝ) < gammaOneExpRegimeConst := gammaOneExpRegimeConst_pos
  have h5 : (0 : ℝ) < Real.sqrt (((ShellField.shellColorPeriod d : ℕ) : ℝ) ^ d) := by
    have : (0 : ℝ) < ((ShellField.shellColorPeriod d : ℕ) : ℝ) ^ d := by
      have hcp : 0 < ShellField.shellColorPeriod d := ShellField.shellColorPeriod_pos d
      positivity
    exact Real.sqrt_pos.2 this
  have h6 : (0 : ℝ) < (3 : ℝ) ^ (-((d : ℝ) * ((m - L : ℕ) : ℝ)) / 2) :=
    Real.rpow_pos_of_pos (by norm_num) _
  unfold mixGap_perEntryAmp
  positivity

/-- The per-block concentration amplitude, one lattice-scale, colour-count and
`d²`-entry factor. -/
def mixGap_blockSumAmp (d : ℕ) (nu : ℝ) (L m : ℕ) : ℝ :=
  gammaTriangleConst 1 * ((d : ℝ) * (d : ℝ)) * mixGap_perEntryAmp d nu L m

theorem mixGap_blockSumAmp_pos {nu : ℝ} (hnu : 0 < nu) (d L m : ℕ) [NeZero d] :
    0 < mixGap_blockSumAmp d nu L m := by
  have h1 := mixGap_perEntryAmp_pos hnu d L m
  have h3 : (0 : ℝ) < gammaTriangleConst (1 : ℝ) := gammaTriangleConst_pos
  have hdpos : (0 : ℝ) < (d : ℝ) * (d : ℝ) := by
    have hdN : 0 < d := (NeZero.ne d).bot_lt
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdN
    positivity
  unfold mixGap_blockSumAmp
  positivity

/-- The four-block combined concentration amplitude. -/
def mixGap_entrySumAmp (d : ℕ) (nu : ℝ) (L m : ℕ) : ℝ :=
  gammaTriangleConst 1 * (gammaTriangleConst 1 * (gammaTriangleConst 1 *
      (mixGap_blockSumAmp d nu L m + mixGap_blockSumAmp d nu L m) + mixGap_blockSumAmp d nu L m) +
    mixGap_blockSumAmp d nu L m)

/-- One block's double sum of absolute entry deviations is `O_{Γ1}`, via the
`Γ1` triangle inequality over its `d²` entries. -/
theorem mixGap_isBigO_gammaOne_blockSum [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) {nn L m : ℕ} (hnl : nn ≤ L) (hlm : L ≤ m)
    (sgn1 sgn2 : Fin d → BlockCoord d) :
    IsBigO P.toMeasure (gammaSigma 1)
      (fun omega : ShellSeq d =>
        ∑ i : Fin d, ∑ j : Fin d, |mixGap_avgEntryDeviation nu L P nn m (sgn1 i) (sgn2 j) omega|)
      (mixGap_blockSumAmp d nu L m) := by
  classical
  set amp : ℝ := mixGap_perEntryAmp d nu L m with hamp
  have hampPos : 0 < amp := mixGap_perEntryAmp_pos hnu d L m
  set g : Fin d × Fin d → ShellSeq d → ℝ :=
    fun p omega => mixGap_avgEntryDeviation nu L P nn m (sgn1 p.1) (sgn2 p.2) omega
  have hentry : ∀ p : Fin d × Fin d, IsBigO P.toMeasure (gammaSigma 1) (fun omega => g p omega) amp := by
    intro p
    have hd : (originCube d (m : ℤ)).scale = (m : ℤ) := rfl
    exact mixGap_entryDeviation_concentration hnu hPrefix hJ1 hJ2 hJ3 hJ4 hnl hlm
      (sgn1 p.1) (sgn2 p.2) hd
  have htri := isBigO_finset_sum_of_isBigO_gammaSigma (μ := P.toMeasure)
    (Finset.univ : Finset (Fin d × Fin d)) (X := fun p => fun omega => |g p omega|) (a := fun _ => amp)
    (σ := 1) one_pos Finset.univ_nonempty (fun p _ => hampPos)
    (fun p _ => by
      have h := hentry p
      simpa only [IsBigO, IsBigOWith, abs_abs, ProbabilityMeasure.measureReal_eq_coe_coeFn, gammaSigma_apply, Real.rpow_one] using h)
    (fun p _ => continuous_abs.measurable.comp
      (mixGap_measurable_avgEntryDeviation (P := P) hnu L nn m (sgn1 p.1) (sgn2 p.2)))
  have hsum : (∑ p : Fin d × Fin d, amp) = (d : ℝ) * (d : ℝ) * amp := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  rw [hsum] at htri
  have hfun : (fun omega : ShellSeq d => ∑ p ∈ (Finset.univ : Finset (Fin d × Fin d)), |g p omega|) =
      fun omega : ShellSeq d =>
        ∑ i : Fin d, ∑ j : Fin d, |mixGap_avgEntryDeviation nu L P nn m (sgn1 i) (sgn2 j) omega| := by
    funext omega
    rw [← Finset.sum_product']
    rfl
  rw [hfun] at htri
  refine htri.mono_scale (le_of_eq ?_)
  unfold mixGap_blockSumAmp
  ring

/-- **The `Γ1` concentration of the entrywise sum envelope.** Combines the
four blocks' `mixGap_isBigO_gammaOne_blockSum` via the two-term `Γ1` triangle
inequality `SuperdiffusionCLT.Probability.isBigO_gammaSigma_add_of_isBigO`. -/
theorem mixGap_isBigO_gammaOne_entrySumEnvelope [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) {nn L m : ℕ} (hnl : nn ≤ L) (hlm : L ≤ m) :
    IsBigO P.toMeasure (gammaSigma 1)
      (fun omega : ShellSeq d => mixGap_entrySumEnvelope nu L P nn m omega)
      (mixGap_entrySumAmp d nu L m) := by
  have hb1 := mixGap_isBigO_gammaOne_blockSum hnu hPrefix hJ1 hJ2 hJ3 hJ4 hnl hlm Sum.inl Sum.inl
  have hb2 := mixGap_isBigO_gammaOne_blockSum hnu hPrefix hJ1 hJ2 hJ3 hJ4 hnl hlm Sum.inl Sum.inr
  have hb3 := mixGap_isBigO_gammaOne_blockSum hnu hPrefix hJ1 hJ2 hJ3 hJ4 hnl hlm Sum.inr Sum.inl
  have hb4 := mixGap_isBigO_gammaOne_blockSum hnu hPrefix hJ1 hJ2 hJ3 hJ4 hnl hlm Sum.inr Sum.inr
  have hamp1pos : 0 < mixGap_blockSumAmp d nu L m := mixGap_blockSumAmp_pos hnu d L m
  have hM1 : Measurable fun omega : ShellSeq d =>
      ∑ i : Fin d, ∑ j : Fin d, |mixGap_avgEntryDeviation nu L P nn m (Sum.inl i) (Sum.inl j) omega| :=
    Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
      continuous_abs.measurable.comp
        (mixGap_measurable_avgEntryDeviation (P := P) hnu L nn m (Sum.inl i) (Sum.inl j))
  have hM2 : Measurable fun omega : ShellSeq d =>
      ∑ i : Fin d, ∑ j : Fin d, |mixGap_avgEntryDeviation nu L P nn m (Sum.inl i) (Sum.inr j) omega| :=
    Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
      continuous_abs.measurable.comp
        (mixGap_measurable_avgEntryDeviation (P := P) hnu L nn m (Sum.inl i) (Sum.inr j))
  have hM3 : Measurable fun omega : ShellSeq d =>
      ∑ i : Fin d, ∑ j : Fin d, |mixGap_avgEntryDeviation nu L P nn m (Sum.inr i) (Sum.inl j) omega| :=
    Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
      continuous_abs.measurable.comp
        (mixGap_measurable_avgEntryDeviation (P := P) hnu L nn m (Sum.inr i) (Sum.inl j))
  have hM4 : Measurable fun omega : ShellSeq d =>
      ∑ i : Fin d, ∑ j : Fin d, |mixGap_avgEntryDeviation nu L P nn m (Sum.inr i) (Sum.inr j) omega| :=
    Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
      continuous_abs.measurable.comp
        (mixGap_measurable_avgEntryDeviation (P := P) hnu L nn m (Sum.inr i) (Sum.inr j))
  have h12 := isBigO_gammaSigma_add_of_isBigO (mu := P.toMeasure) one_pos hamp1pos hamp1pos hb1 hb2
    hM1 hM2
  have hgtc : (0:ℝ) < gammaTriangleConst (1:ℝ) := gammaTriangleConst_pos
  have hpos12 : (0:ℝ) < gammaTriangleConst 1 *
      (mixGap_blockSumAmp d nu L m + mixGap_blockSumAmp d nu L m) := by
    have : (0:ℝ) < mixGap_blockSumAmp d nu L m + mixGap_blockSumAmp d nu L m := by linarith only [hamp1pos]
    exact mul_pos hgtc this
  have h123 := isBigO_gammaSigma_add_of_isBigO (mu := P.toMeasure) one_pos hpos12 hamp1pos h12 hb3
    (hM1.add hM2) hM3
  have hpos123 : (0:ℝ) < gammaTriangleConst 1 *
      (gammaTriangleConst 1 * (mixGap_blockSumAmp d nu L m + mixGap_blockSumAmp d nu L m) +
        mixGap_blockSumAmp d nu L m) := by
    have : (0:ℝ) < gammaTriangleConst 1 * (mixGap_blockSumAmp d nu L m + mixGap_blockSumAmp d nu L m) +
        mixGap_blockSumAmp d nu L m := by linarith only [hpos12, hamp1pos]
    exact mul_pos hgtc this
  have h1234 := isBigO_gammaSigma_add_of_isBigO (mu := P.toMeasure) one_pos hpos123 hamp1pos
    h123 hb4 ((hM1.add hM2).add hM3) hM4
  unfold mixGap_entrySumAmp
  exact h1234

end

end SuperdiffusionCLT.Section4.Mixing
