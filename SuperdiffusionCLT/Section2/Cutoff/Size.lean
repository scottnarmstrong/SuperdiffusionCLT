/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Probability.GammaSigmaHelpers
public import SuperdiffusionCLT.Probability.VolumeAverageOrlicz
public import SuperdiffusionCLT.Section2.Cutoff.StreamCutoffAPI
public import SuperdiffusionCLT.Section2.Estimates.Stream.OriginConcentration

/-!
# Size estimates for the marginal cutoff field

This module proves the size estimates of the infrared cutoff `k_m` used by the
ellipticity envelope of Section 2.5.

At a fixed point the cutoff is the sum of the `m + 1` shells `j_0, ..., j_m`.
These are mutually independent by J2, centred by J4, and each has the
unit-scale `Gamma_2` tail supplied by J3 and transported to the point by the
per-shell stationarity of the shell law. The CoarseGraining library's centred
independent-sum concentration therefore gives the entrywise `sqrt (m + 1)` estimate, and the
finite triangle inequality over the `d ^ 2` matrix entries gives the matrix
operator norm estimate. The power rule for stretched-exponential tails turns
this into the squared display, and Jensen averaging turns the squared display
into the normalized `L^2` display.

Nothing here uses a scaling law, an infinite cutoff, or a spatial average of a
single shell.

## Main definitions

* `cutoffValueConst`, `cutoffSquareConst`, `cutoffL2Const`: the explicit
  dimension-only constants.

## Main results

* `isBigOWith_gammaSigma_matrixOperatorNorm_streamCutoff`: the pointwise value
  tail `|k_m(x)| ≤ O_{Γ₂}(C √(m + 1))`.
* `isBigOWith_gammaSigma_sq_streamCutoff`: the squared display
  `|k_m(x)|² ≤ O_{Γ₁}(C (1 ∨ m))`.
* `isBigOWith_gammaSigma_volumeAverage_sq_streamCutoff`,
  `isBigOWith_gammaSigma_volumeAverage_sq_streamCutoff_max`: the normalized
  `L²(U)` display `e.km.Ltwo.size`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Cutoff

open Homogenization MeasureTheory
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Section2.Estimates.Stream
open scoped BigOperators

noncomputable section

variable {d : ℕ}
variable {P : ProbabilityMeasure (ShellSeq d)}

/-! ## The explicit constants -/

/-- The dimension-only constant of the pointwise value tail: the CoarseGraining
library's finite triangle constant, the number of matrix entries, and its
independent-sum constant. -/
def cutoffValueConst (d : ℕ) : ℝ :=
  IndependentSums.gammaTriangleConst 2 *
    ((d : ℝ) ^ 2 * Book.Ch04.gammaSigmaIndependentSumConst 2)

/-- The dimension-only constant of the squared display. -/
def cutoffSquareConst (d : ℕ) : ℝ :=
  cutoffValueConst d ^ 2

/-- The dimension-only constant of the normalized `L²` display, carrying in
addition the two universal constants of the moment characterization used by
the Jensen averaging step. -/
def cutoffL2Const (d : ℕ) : ℝ :=
  Real.exp 1 *
    (IndependentSums.gammaMomentConst 1 * cutoffSquareConst d)

/-- The value constant is positive in every positive dimension. The three
constants of this section depend on `d` alone, so their positivity needs no
probabilistic data. -/
theorem cutoffValueConst_pos_of_pos (hd : 0 < d) : 0 < cutoffValueConst d := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  exact mul_pos IndependentSums.gammaTriangleConst_pos
    (mul_pos (pow_pos hdR 2) gammaSigmaIndependentSumConst_two_pos)

/-- The squared constant is positive in every positive dimension. -/
theorem cutoffSquareConst_pos_of_pos (hd : 0 < d) : 0 < cutoffSquareConst d :=
  pow_pos (cutoffValueConst_pos_of_pos hd) 2

/-- The normalized `L²` constant is positive in every positive dimension. -/
theorem cutoffL2Const_pos_of_pos (hd : 0 < d) : 0 < cutoffL2Const d :=
  mul_pos (Real.exp_pos 1)
    (mul_pos (IndependentSums.gammaMomentConst_pos (by norm_num))
      (cutoffSquareConst_pos_of_pos hd))

/-- The value constant is positive under the standing dimension condition of
the shell law. -/
theorem cutoffValueConst_pos (hPrefix : ShellLawPrefix d P) :
    0 < cutoffValueConst d :=
  cutoffValueConst_pos_of_pos (lt_of_lt_of_le (by norm_num) hPrefix.dimension)

/-- The squared constant is positive under the standing dimension condition. -/
theorem cutoffSquareConst_pos (hPrefix : ShellLawPrefix d P) :
    0 < cutoffSquareConst d :=
  cutoffSquareConst_pos_of_pos (lt_of_lt_of_le (by norm_num) hPrefix.dimension)

/-- The normalized `L²` constant is positive under the standing dimension
condition. -/
theorem cutoffL2Const_pos (hPrefix : ShellLawPrefix d P) :
    0 < cutoffL2Const d :=
  cutoffL2Const_pos_of_pos (lt_of_lt_of_le (by norm_num) hPrefix.dimension)

/-! ## Measurability and continuity of the cutoff value -/

/-- The cutoff is continuous in the spatial variable, because every shell of
the carrier stores a continuous value map. -/
theorem continuous_streamCutoff_apply (omega : ShellSeq d) (m : ℕ) :
    Continuous (fun x : Vec d ↦ streamCutoff omega m x) := by
  have hfun : (fun x : Vec d ↦ streamCutoff omega m x) =
      fun x : Vec d ↦ ∑ l ∈ Finset.range (m + 1), (omega l) x := by
    funext x
    rw [streamCutoff_apply]
  rw [hfun]
  exact continuous_finsetSum _ fun l _ ↦ (omega l).1.1.continuous

/-- The matrix value of the cutoff at a fixed point is measurable in the shell
sequence. -/
theorem measurable_streamCutoff_apply (m : ℕ) (x : Vec d) :
    Measurable (fun omega : ShellSeq d ↦ streamCutoff omega m x) :=
  measurable_matrix_of_entries fun i k ↦
    (measurable_apply_entry x i k).comp (measurable_streamCutoff m)

/-- The Euclidean matrix operator norm of the cutoff value is measurable in the
shell sequence. -/
theorem measurable_matrixOperatorNorm_streamCutoff (m : ℕ) (x : Vec d) :
    Measurable (fun omega : ShellSeq d ↦
      matrixOperatorNorm (streamCutoff omega m x)) :=
  ShellField.continuous_matrixOperatorNorm.measurable.comp
    (measurable_streamCutoff_apply m x)

/-- Joint measurability of the cutoff size in the sample and the point. The
map is continuous in the point and measurable in the sample, so it is a
Caratheodory function. -/
theorem measurable_uncurry_matrixOperatorNorm_streamCutoff (m : ℕ) :
    Measurable (Function.uncurry
      (fun (x : Vec d) (omega : ShellSeq d) ↦
        matrixOperatorNorm (streamCutoff omega m x))) :=
  measurable_uncurry_of_continuous_of_measurable
    (fun omega ↦
      ShellField.continuous_matrixOperatorNorm.comp
        (continuous_streamCutoff_apply omega m))
    (fun x ↦ measurable_matrixOperatorNorm_streamCutoff m x)

/-! ## The pointwise value tail -/

/-- Entrywise form of the pointwise value tail: every scalar entry of `k_m` at
every fixed point obeys the exact `sqrt (m + 1)` concentration scale. -/
theorem isBigO_gammaSigma_streamCutoff_entry
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (m : ℕ) (x : Vec d) (i k : Fin d) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d ↦ streamCutoff omega m x i k)
      (Book.Ch04.gammaSigmaIndependentSumConst 2 * Real.sqrt ((m : ℝ) + 1)) := by
  have h :=
    Book.Ch04.isBigO_gammaSigma_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero
      (μ := P.toMeasure)
      (X := fun (l : ℕ) (omega : ShellSeq d) ↦ (omega l) x i k)
      (s := Finset.range (m + 1)) (σ := 2) (K := 1)
      (hJ2.iIndepFun_entry_coordinate x i k)
      (fun l ↦ ShellLawConsequences.measurable_entry_coordinate l x i k)
      Finset.nonempty_range_add_one (by norm_num) (by norm_num) (by norm_num)
      (fun l _ ↦
        ShellLawConsequences.isBigO_gammaSigma_entry_coordinate
          hPrefix hJ3 l x i k)
      (fun l _ ↦
        ShellLawConsequences.integral_entry_coordinate_eq_zero hJ4 l x i k)
  have hcard : ((Finset.range (m + 1)).card : ℝ) = (m : ℝ) + 1 := by
    rw [Finset.card_range]
    push_cast
    ring
  rw [hcard, mul_one] at h
  have hfun :
      (fun omega : ShellSeq d ↦ ∑ l ∈ Finset.range (m + 1), (omega l) x i k)
        = fun omega : ShellSeq d ↦ streamCutoff omega m x i k := by
    funext omega
    rw [streamCutoff_apply_entry]
  rwa [hfun] at h

/-- **The pointwise value tail of the cutoff field.** For every point `x` and
every `m`, the Euclidean matrix operator norm of `k_m(x)` obeys
`|k_m(x)| ≤ O_{Γ₂}(C √(m + 1))` with the explicit dimension-only constant
`cutoffValueConst d`. -/
theorem isBigOWith_gammaSigma_matrixOperatorNorm_streamCutoff
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (m : ℕ) (x : Vec d) :
    IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d ↦
        matrixOperatorNorm (streamCutoff omega m x))
      (cutoffValueConst d * Real.sqrt ((m : ℝ) + 1)) := by
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) hPrefix.dimension
  have hAmp : 0 < Book.Ch04.gammaSigmaIndependentSumConst 2 *
      Real.sqrt ((m : ℝ) + 1) :=
    mul_pos gammaSigmaIndependentSumConst_two_pos
      (Real.sqrt_pos.2 (by positivity))
  have hne : (Finset.univ : Finset (Fin d × Fin d)).Nonempty :=
    ⟨(⟨0, hd⟩, ⟨0, hd⟩), Finset.mem_univ _⟩
  have hentry : ∀ q : Fin d × Fin d,
      IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
        (fun omega : ShellSeq d ↦ |streamCutoff omega m x q.1 q.2|)
        (Book.Ch04.gammaSigmaIndependentSumConst 2 *
          Real.sqrt ((m : ℝ) + 1)) := by
    intro q
    have h := isBigO_gammaSigma_streamCutoff_entry hPrefix hJ2 hJ3 hJ4 m x q.1 q.2
    simpa only [IndependentSums.IsBigO, abs_abs] using h
  have hmeas : ∀ q : Fin d × Fin d, Measurable (fun omega : ShellSeq d ↦
      |streamCutoff omega m x q.1 q.2|) := by
    intro q
    have hsum : Measurable (fun omega : ShellSeq d ↦
        streamCutoff omega m x q.1 q.2) := by
      have hentryMeas := Finset.measurable_sum (Finset.range (m + 1))
        (fun l (_ : l ∈ Finset.range (m + 1)) ↦
          ShellLawConsequences.measurable_entry_coordinate (d := d) l x q.1 q.2)
      simpa only [streamCutoff_apply_entry] using hentryMeas
    simpa only [Real.norm_eq_abs] using hsum.norm
  have htriangle := IndependentSums.isBigO_finset_sum_of_isBigO_gammaSigma
    (μ := P.toMeasure) (Finset.univ : Finset (Fin d × Fin d))
    (X := fun q omega ↦ |streamCutoff omega m x q.1 q.2|)
    (a := fun _ : Fin d × Fin d ↦
      Book.Ch04.gammaSigmaIndependentSumConst 2 * Real.sqrt ((m : ℝ) + 1))
    (σ := 2) (by norm_num) hne (fun _ _ ↦ hAmp)
    (fun q _ ↦ hentry q) (fun q _ ↦ hmeas q)
  have hcard : IndependentSums.gammaTriangleConst 2 *
      ∑ _q : Fin d × Fin d,
        (Book.Ch04.gammaSigmaIndependentSumConst 2 *
          Real.sqrt ((m : ℝ) + 1)) =
      cutoffValueConst d * Real.sqrt ((m : ℝ) + 1) := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, cutoffValueConst]
    push_cast
    ring
  rw [hcard] at htriangle
  refine htriangle.of_le fun omega ↦ ?_
  exact (matrixOperatorNorm_le_sum_univ_abs_entry _).trans (le_abs_self _)

/-! ## The squared display -/

private theorem rpow_ofNat_two (y : ℝ) : y ^ (2 : ℝ) = y ^ (2 : ℕ) := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- **The squared pointwise display** in the form
`|k_m(x)|² ≤ O_{Γ₁}(C (m + 1))`. It is the value tail read through the power
rule for stretched-exponential tails with exponent `2`. -/
theorem isBigOWith_gammaSigma_sq_streamCutoff
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (m : ℕ) (x : Vec d) :
    IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 1)
      (fun omega : ShellSeq d ↦
        matrixOperatorNorm (streamCutoff omega m x) ^ 2)
      (cutoffSquareConst d * ((m : ℝ) + 1)) := by
  have hpos : 0 < cutoffValueConst d := cutoffValueConst_pos hPrefix
  have hA : 0 ≤ cutoffValueConst d * Real.sqrt ((m : ℝ) + 1) :=
    mul_nonneg hpos.le (Real.sqrt_nonneg _)
  have hpower := (Book.Ch04.isBigOWith_gammaSigma_rpow_iff
    (μ := P.toMeasure)
    (X := fun omega : ShellSeq d ↦
      matrixOperatorNorm (streamCutoff omega m x))
    (A := cutoffValueConst d * Real.sqrt ((m : ℝ) + 1)) (σ := 2) (p := 2)
    (by norm_num) hA
    (fun omega ↦ matrixOperatorNorm_nonneg _)).1
      (isBigOWith_gammaSigma_matrixOperatorNorm_streamCutoff
        hPrefix hJ2 hJ3 hJ4 m x)
  rw [show (2 : ℝ) / 2 = 1 by norm_num] at hpower
  have hscale : (cutoffValueConst d * Real.sqrt ((m : ℝ) + 1)) ^ (2 : ℕ) =
      cutoffSquareConst d * ((m : ℝ) + 1) := by
    rw [mul_pow, Real.sq_sqrt (by positivity), cutoffSquareConst]
  rw [← hscale]
  simpa only [rpow_ofNat_two] using hpower

/-! ## The normalized `L²` display -/

/-- **Manuscript display `e.km.Ltwo.size`.** For every set `U` of positive
finite volume, the normalized `L²(U)` size of the cutoff field obeys
`⨍_U |k_m|² ≤ O_{Γ₁}(C (m + 1))` with the explicit dimension-only constant
`cutoffL2Const d`. The step from the pointwise display is Jensen's
inequality, carried out through the CoarseGraining library's moment characterization of
`Γ₁`. -/
theorem isBigOWith_gammaSigma_volumeAverage_sq_streamCutoff
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (m : ℕ) {U : Set (Vec d)} (hU0 : volume U ≠ 0) (hUtop : volume U ≠ ⊤) :
    IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 1)
      (fun omega : ShellSeq d ↦
        volumeAverage U
          (fun x ↦ matrixOperatorNorm (streamCutoff omega m x) ^ 2))
      (cutoffL2Const d * ((m : ℝ) + 1)) := by
  have hA : 0 < cutoffSquareConst d * ((m : ℝ) + 1) :=
    mul_pos (cutoffSquareConst_pos hPrefix) (by positivity)
  have hjoint : Measurable (Function.uncurry
      (fun (x : Vec d) (omega : ShellSeq d) ↦
        matrixOperatorNorm (streamCutoff omega m x) ^ 2)) :=
    (continuous_pow 2).measurable.comp
      (measurable_uncurry_matrixOperatorNorm_streamCutoff m)
  have haverage :=
    SuperdiffusionCLT.Probability.isBigOWith_gammaSigma_volumeAverage
      (mu := P.toMeasure) (U := U)
      (Y := fun (x : Vec d) (omega : ShellSeq d) ↦
        matrixOperatorNorm (streamCutoff omega m x) ^ 2)
      (by norm_num) hA hU0 hUtop
      (fun x omega ↦ pow_nonneg (matrixOperatorNorm_nonneg _) 2)
      hjoint
      (fun x ↦ isBigOWith_gammaSigma_sq_streamCutoff hPrefix hJ2 hJ3 hJ4 m x)
  have hconst : Real.exp 1 *
      (IndependentSums.gammaMomentConst 1 *
        (cutoffSquareConst d * ((m : ℝ) + 1))) =
      cutoffL2Const d * ((m : ℝ) + 1) := by
    rw [cutoffL2Const]
    ring
  rwa [hconst] at haverage

/-- The `1 ∨ m` form of the normalized `L²` display, exactly as printed in the
manuscript. -/
theorem isBigOWith_gammaSigma_volumeAverage_sq_streamCutoff_max
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (m : ℕ) {U : Set (Vec d)} (hU0 : volume U ≠ 0) (hUtop : volume U ≠ ⊤) :
    IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 1)
      (fun omega : ShellSeq d ↦
        volumeAverage U
          (fun x ↦ matrixOperatorNorm (streamCutoff omega m x) ^ 2))
      (2 * cutoffL2Const d * max 1 (m : ℝ)) := by
  refine (isBigOWith_gammaSigma_volumeAverage_sq_streamCutoff
    hPrefix hJ2 hJ3 hJ4 m hU0 hUtop).mono_scale ?_
  have hL2 : 0 ≤ cutoffL2Const d := (cutoffL2Const_pos hPrefix).le
  have hle : (m : ℝ) + 1 ≤ 2 * max 1 (m : ℝ) := by
    have h1 : (1 : ℝ) ≤ max 1 (m : ℝ) := le_max_left _ _
    have h2 : (m : ℝ) ≤ max 1 (m : ℝ) := le_max_right _ _
    linarith only [h1, h2]
  calc cutoffL2Const d * ((m : ℝ) + 1)
      ≤ cutoffL2Const d * (2 * max 1 (m : ℝ)) :=
        mul_le_mul_of_nonneg_left hle hL2
    _ = 2 * cutoffL2Const d * max 1 (m : ℝ) := by ring

end

end SuperdiffusionCLT.Section2.Cutoff
