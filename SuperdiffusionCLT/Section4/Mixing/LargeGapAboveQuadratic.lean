/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.Mixing.LargeGapAboveEll
public import SuperdiffusionCLT.Section4.Mixing.LargeGapConcentrationQuadratic

/-!
# The entrywise sum envelope, colouring scale `nn` (the `n > L` route)

`p.mixing.P.three.prime#large-gap-case`'s `n > L` regime: the exact analogue of
`Section4.Mixing.LargeGapConcentrationQuadratic`'s amplitude/envelope chain
(`mixGap_perEntryAmp`, `mixGap_blockSumAmp`, `mixGap_entrySumAmp`,
`mixGap_isBigO_gammaOne_blockSum`, `mixGap_isBigO_gammaOne_entrySumEnvelope`),
with the decay exponent `(m - nn)` (colouring scale `ell := nn`) in place of
`(m - L)`, under `L ≤ nn ≤ m` in place of `nn ≤ L ≤ m`. The underlying
witness `mixGap_entrySumEnvelope` (and its measurability) is already
scale-agnostic (`LargeGapConcentrationQuadratic.lean`), so it is reused
unchanged: only the concentration amplitude changes. -/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

open Homogenization
open Homogenization.IndependentSums
open MeasureTheory ProbabilityTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Probability (isBigO_gammaSigma_add_of_isBigO)

noncomputable section

variable {d : ℕ}

/-- The per-entry concentration amplitude at colouring scale `nn`, decay
`(m - nn)`. -/
def mixGapAbove_perEntryAmp (d : ℕ) (nu : ℝ) (L nn m : ℕ) : ℝ :=
  2 * gammaTriangleConst 1 * gammaOneExpRegimeConst *
    Real.sqrt (((ShellField.shellColorPeriod d : ℕ) : ℝ) ^ d) *
    (mixGap_entryEnvelope d nu L +
      IndependentSums.gammaMomentConst 1 * mixGap_entryEnvelope d nu L) *
    (3 : ℝ) ^ (-((d : ℝ) * ((m - nn : ℕ) : ℝ)) / 2)

theorem mixGapAbove_perEntryAmp_pos {nu : ℝ} (hnu : 0 < nu) (d L nn m : ℕ) :
    0 < mixGapAbove_perEntryAmp d nu L nn m := by
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
  have h6 : (0 : ℝ) < (3 : ℝ) ^ (-((d : ℝ) * ((m - nn : ℕ) : ℝ)) / 2) :=
    Real.rpow_pos_of_pos (by norm_num) _
  unfold mixGapAbove_perEntryAmp
  positivity

/-- The per-block concentration amplitude at colouring scale `nn`. -/
def mixGapAbove_blockSumAmp (d : ℕ) (nu : ℝ) (L nn m : ℕ) : ℝ :=
  gammaTriangleConst 1 * ((d : ℝ) * (d : ℝ)) * mixGapAbove_perEntryAmp d nu L nn m

theorem mixGapAbove_blockSumAmp_pos {nu : ℝ} (hnu : 0 < nu) (d L nn m : ℕ) [NeZero d] :
    0 < mixGapAbove_blockSumAmp d nu L nn m := by
  have h1 := mixGapAbove_perEntryAmp_pos hnu d L nn m
  have h3 : (0 : ℝ) < gammaTriangleConst (1 : ℝ) := gammaTriangleConst_pos
  have hdpos : (0 : ℝ) < (d : ℝ) * (d : ℝ) := by
    have hdN : 0 < d := (NeZero.ne d).bot_lt
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdN
    positivity
  unfold mixGapAbove_blockSumAmp
  positivity

/-- The four-block combined concentration amplitude at colouring scale `nn`. -/
def mixGapAbove_entrySumAmp (d : ℕ) (nu : ℝ) (L nn m : ℕ) : ℝ :=
  gammaTriangleConst 1 * (gammaTriangleConst 1 * (gammaTriangleConst 1 *
      (mixGapAbove_blockSumAmp d nu L nn m + mixGapAbove_blockSumAmp d nu L nn m) +
        mixGapAbove_blockSumAmp d nu L nn m) +
    mixGapAbove_blockSumAmp d nu L nn m)

/-- One block's double sum of absolute entry deviations is `O_{Γ1}`, colouring
scale `ell := nn` (`L ≤ nn ≤ m`). -/
theorem mixGapAbove_isBigO_gammaOne_blockSum [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) {nn L m : ℕ} (hLn : L ≤ nn) (hnm : nn ≤ m)
    (sgn1 sgn2 : Fin d → BlockCoord d) :
    IsBigO P.toMeasure (gammaSigma 1)
      (fun omega : ShellSeq d =>
        ∑ i : Fin d, ∑ j : Fin d, |mixGap_avgEntryDeviation nu L P nn m (sgn1 i) (sgn2 j) omega|)
      (mixGapAbove_blockSumAmp d nu L nn m) := by
  classical
  set amp : ℝ := mixGapAbove_perEntryAmp d nu L nn m with hamp
  have hampPos : 0 < amp := mixGapAbove_perEntryAmp_pos hnu d L nn m
  set g : Fin d × Fin d → ShellSeq d → ℝ :=
    fun p omega => mixGap_avgEntryDeviation nu L P nn m (sgn1 p.1) (sgn2 p.2) omega
  have hentry : ∀ p : Fin d × Fin d, IsBigO P.toMeasure (gammaSigma 1) (fun omega => g p omega) amp := by
    intro p
    have hd : (originCube d (m : ℤ)).scale = (m : ℤ) := rfl
    exact mixGapAbove_entryDeviation_concentration_ell hnu hPrefix hJ1 hJ2 hJ3 hJ4
      le_rfl hLn hnm (sgn1 p.1) (sgn2 p.2) hd
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
  unfold mixGapAbove_blockSumAmp
  ring

/-- **The `Γ1` concentration of the entrywise sum envelope, colouring scale
`nn`.** Combines the four blocks' `mixGapAbove_isBigO_gammaOne_blockSum` via
the two-term `Γ1` triangle inequality. -/
theorem mixGapAbove_isBigO_gammaOne_entrySumEnvelope [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) {nn L m : ℕ} (hLn : L ≤ nn) (hnm : nn ≤ m) :
    IsBigO P.toMeasure (gammaSigma 1)
      (fun omega : ShellSeq d => mixGap_entrySumEnvelope nu L P nn m omega)
      (mixGapAbove_entrySumAmp d nu L nn m) := by
  have hb1 := mixGapAbove_isBigO_gammaOne_blockSum hnu hPrefix hJ1 hJ2 hJ3 hJ4 hLn hnm Sum.inl Sum.inl
  have hb2 := mixGapAbove_isBigO_gammaOne_blockSum hnu hPrefix hJ1 hJ2 hJ3 hJ4 hLn hnm Sum.inl Sum.inr
  have hb3 := mixGapAbove_isBigO_gammaOne_blockSum hnu hPrefix hJ1 hJ2 hJ3 hJ4 hLn hnm Sum.inr Sum.inl
  have hb4 := mixGapAbove_isBigO_gammaOne_blockSum hnu hPrefix hJ1 hJ2 hJ3 hJ4 hLn hnm Sum.inr Sum.inr
  have hamp1pos : 0 < mixGapAbove_blockSumAmp d nu L nn m := mixGapAbove_blockSumAmp_pos hnu d L nn m
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
      (mixGapAbove_blockSumAmp d nu L nn m + mixGapAbove_blockSumAmp d nu L nn m) := by
    have : (0:ℝ) < mixGapAbove_blockSumAmp d nu L nn m + mixGapAbove_blockSumAmp d nu L nn m := by
      linarith only [hamp1pos]
    exact mul_pos hgtc this
  have h123 := isBigO_gammaSigma_add_of_isBigO (mu := P.toMeasure) one_pos hpos12 hamp1pos h12 hb3
    (hM1.add hM2) hM3
  have hpos123 : (0:ℝ) < gammaTriangleConst 1 *
      (gammaTriangleConst 1 * (mixGapAbove_blockSumAmp d nu L nn m + mixGapAbove_blockSumAmp d nu L nn m) +
        mixGapAbove_blockSumAmp d nu L nn m) := by
    have : (0:ℝ) < gammaTriangleConst 1 *
        (mixGapAbove_blockSumAmp d nu L nn m + mixGapAbove_blockSumAmp d nu L nn m) +
          mixGapAbove_blockSumAmp d nu L nn m := by linarith only [hpos12, hamp1pos]
    exact mul_pos hgtc this
  have h1234 := isBigO_gammaSigma_add_of_isBigO (mu := P.toMeasure) one_pos hpos123 hamp1pos
    h123 hb4 ((hM1.add hM2).add hM3) hM4
  unfold mixGapAbove_entrySumAmp
  exact h1234

end

end SuperdiffusionCLT.Section4.Mixing
