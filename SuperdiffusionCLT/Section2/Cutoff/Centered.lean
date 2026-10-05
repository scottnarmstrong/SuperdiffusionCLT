/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Cutoff.CoefficientCutoffAPI
public import Homogenization.Probability.RegCoeffField.Differentiation

/-!
# Centered representatives of the marginal infrared cutoff

This module defines the representatives of the cutoff stream matrix and the
cutoff coefficient field that have been recentered by their volume average over
a set `U`, and proves the identities that justify the notation: the centered
stream matrix is still anti-symmetric, the centered coefficient field still has
symmetric part `ν Id`, the two coefficient fields differ by a constant matrix,
and the centered stream matrix has zero average over `U`.

The average is `Homogenization.volumeAverageMat`, the entrywise Lebesgue
average with the normalizing factor `(volume U).toReal⁻¹`; it is the average
already used by the shell spatial averages of this repository. The definitions
take an arbitrary `U : Set (Vec d)` and contain no case split; the manuscript's
hypotheses on `U` are stated on the theorems that need them.

## Main definitions

* `centeredStreamCutoff`: the field `k_L - (k_L)_U`.
* `centeredCoefficientCutoff`: the field `ν Id + (k_L - (k_L)_U)`.

## Main results

* `centeredStreamCutoff_apply`, `centeredCoefficientCutoff_apply`: evaluation.
* `centeredStreamCutoff_skew`, `symmPart_centeredCoefficientCutoff`: the
  anti-symmetry and the symmetric part.
* `measurable_volumeAverageMat_of_isBounded`: the volume average over a bounded
  measurable set depends measurably on the field.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Cutoff

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Section2
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-! ## The centered stream matrix -/

/-- The volume average of an anti-symmetric matrix field is anti-symmetric. -/
theorem matTranspose_volumeAverageMat (U : Set (Vec d)) (f : Vec d → Mat d)
    (hf : ∀ x i k, f x i k = -f x k i) :
    matTranspose (volumeAverageMat U f) = -volumeAverageMat U f := by
  ext i k
  simp only [matTranspose, Matrix.transpose_apply, Matrix.neg_apply,
    volumeAverageMat, volumeAverage]
  rw [show (fun x ↦ f x k i) = fun x ↦ -f x i k from funext fun x ↦ hf x k i,
    MeasureTheory.integral_neg, mul_neg]

/-- The centered representative `k_L - (k_L)_U` of the cutoff stream matrix on
a set `U`, the cutoff level of the manuscript's `k^U = k - (k)_U`, intended for a bounded
measurable `U` of nonzero volume.

The average `(k_L)_U` is a constant matrix, so the subtraction is written as
the addition of a constant field, `RegCoeffField d` being an additive monoid
without negation; `centeredStreamCutoff_apply` records the literal
subtraction. -/
def centeredStreamCutoff (omega : ShellSeq d) (L : ℕ) (U : Set (Vec d)) :
    RegCoeffField d :=
  streamCutoff omega L +
    RegCoeffField.constRegCoeffField
      (-volumeAverageMat U (streamCutoff omega L))

/-- The literal reading of the centered cutoff stream matrix. -/
@[simp]
theorem centeredStreamCutoff_apply (omega : ShellSeq d) (L : ℕ)
    (U : Set (Vec d)) (x : Vec d) :
    centeredStreamCutoff omega L U x =
      streamCutoff omega L x - volumeAverageMat U (streamCutoff omega L) := by
  simp only [centeredStreamCutoff, RegCoeffField.add_apply,
    RegCoeffField.constRegCoeffField_apply]
  abel

/-- The centered cutoff stream matrix is still anti-symmetric. -/
theorem centeredStreamCutoff_skew (omega : ShellSeq d) (L : ℕ)
    (U : Set (Vec d)) (x : Vec d) :
    matTranspose (centeredStreamCutoff omega L U x) =
      -centeredStreamCutoff omega L U x := by
  have havg := matTranspose_volumeAverageMat U (fun y ↦ streamCutoff omega L y)
    fun y i k ↦ streamCutoff_skew_entry omega L y i k
  ext i k
  have hentry := congrFun (congrFun havg i) k
  simp only [matTranspose, Matrix.transpose_apply, Matrix.neg_apply] at hentry ⊢
  simp only [centeredStreamCutoff_apply, Matrix.sub_apply]
  rw [streamCutoff_skew_entry omega L x k i, hentry]
  ring

/-! ## The centered coefficient field -/

/-- The centered representative `ν Id + (k_L - (k_L)_U)` of the cutoff
coefficient field on a set `U`, the cutoff level of the manuscript's
`a^U = ν Id + k^U`,
intended for a bounded measurable `U` of nonzero volume. -/
def centeredCoefficientCutoff (nu : ℝ) (omega : ShellSeq d) (L : ℕ)
    (U : Set (Vec d)) : RegCoeffField d :=
  RegCoeffField.constRegCoeffField (nu • (1 : Mat d)) +
    centeredStreamCutoff omega L U

/-- Matrix-valued evaluation of the centered cutoff coefficient field. -/
@[simp]
theorem centeredCoefficientCutoff_apply (nu : ℝ) (omega : ShellSeq d) (L : ℕ)
    (U : Set (Vec d)) (x : Vec d) :
    centeredCoefficientCutoff nu omega L U x =
      nu • (1 : Mat d) + centeredStreamCutoff omega L U x :=
  rfl

/-- The centered coefficient field differs from `a_L` by the constant
anti-symmetric matrix `(k_L)_U`. -/
theorem centeredCoefficientCutoff_eq_coefficientCutoff_sub (nu : ℝ)
    (omega : ShellSeq d) (L : ℕ) (U : Set (Vec d)) (x : Vec d) :
    centeredCoefficientCutoff nu omega L U x =
      coefficientCutoff nu omega L x -
        volumeAverageMat U (streamCutoff omega L) := by
  simp only [centeredCoefficientCutoff_apply, centeredStreamCutoff_apply,
    coefficientCutoff_apply]
  abel

/-- The symmetric part of the centered coefficient field is again `ν Id`. -/
theorem symmPart_centeredCoefficientCutoff (nu : ℝ) (omega : ShellSeq d)
    (L : ℕ) (U : Set (Vec d)) (x : Vec d) :
    symmPart (centeredCoefficientCutoff nu omega L U x) = nu • (1 : Mat d) := by
  ext i k
  have hskew := congrFun (congrFun (centeredStreamCutoff_skew omega L U x) i) k
  simp only [matTranspose, Matrix.transpose_apply, Matrix.neg_apply] at hskew
  simp only [symmPart, centeredCoefficientCutoff_apply, Matrix.add_apply,
    Matrix.smul_apply]
  rw [hskew]
  by_cases hik : i = k
  · subst k
    simp only [Matrix.one_apply, smul_eq_mul]
    ring
  · have hki : k ≠ i := Ne.symm hik
    simp only [Matrix.one_apply, ite_eq_right hik, ite_eq_right hki, smul_eq_mul]
    ring

/-! ## The defining property: zero average over `U` -/

/-- Entries of a regular coefficient field are integrable on a bounded set. -/
theorem integrableOn_entry_of_isBounded (a : RegCoeffField d) {U : Set (Vec d)}
    (hUb : Bornology.IsBounded U) (i k : Fin d) :
    IntegrableOn (fun x ↦ a x i k) U volume :=
  ((a.entry_locInt i k).integrableOn_isCompact
    hUb.isCompact_closure).mono_set subset_closure

/-- A bounded set has finite Lebesgue measure. -/
theorem volume_ne_top_of_isBounded {U : Set (Vec d)}
    (hUb : Bornology.IsBounded U) :
    volume U ≠ ⊤ :=
  ne_of_lt (lt_of_le_of_lt (measure_mono subset_closure)
    hUb.isCompact_closure.measure_lt_top)

/-- Subtracting a constant matrix subtracts it from the volume average. -/
theorem volumeAverageMat_sub_const (a : RegCoeffField d) {U : Set (Vec d)}
    (hUb : Bornology.IsBounded U) (hUpos : volume U ≠ 0) (C : Mat d) :
    volumeAverageMat U (fun x ↦ a x - C) = volumeAverageMat U a - C := by
  have hfin : volume U ≠ ⊤ := volume_ne_top_of_isBounded hUb
  have hvol : (volume U).toReal ≠ 0 := by
    simp only [ne_eq, ENNReal.toReal_eq_zero_iff, hUpos, hfin, or_self,
      not_false_eq_true]
  ext i k
  have hint : IntegrableOn (fun x ↦ a x i k) U volume :=
    integrableOn_entry_of_isBounded a hUb i k
  have hconst : IntegrableOn (fun _ : Vec d ↦ C i k) U volume :=
    integrableOn_const (C := C i k) hfin
  simp only [volumeAverageMat, volumeAverage, Matrix.sub_apply]
  rw [MeasureTheory.integral_sub hint hconst, MeasureTheory.setIntegral_const,
    MeasureTheory.Measure.real, smul_eq_mul, mul_sub]
  field_simp

/-! ## Measurability in the shell sequence -/

/-- The constant-one indicator of a bounded measurable set is an enriched
test function. -/
private theorem isProbeR_indicator_of_isBounded {U : Set (Vec d)}
    (hUb : Bornology.IsBounded U) (hUmeas : MeasurableSet U) :
    IsProbeR (Set.indicator U (fun _ : Vec d ↦ (1 : ℝ))) := by
  refine ⟨measurable_const.indicator hUmeas, ⟨1, fun x ↦ ?_⟩, ?_⟩
  · by_cases hx : x ∈ U
    · simp only [Set.indicator_of_mem hx, abs_one, le_refl]
    · simp only [Set.indicator_of_notMem hx, abs_zero, zero_le_one]
  · exact IsCompact.of_isClosed_subset hUb.isCompact_closure isClosed_closure
      (closure_mono (support_indicator_one_subset U))

/-- Each entry of the volume average over a measurable set is the entry test
against the indicator of that set, rescaled. -/
theorem volumeAverageMat_apply_eq_smul_entryTestR (a : RegCoeffField d)
    {U : Set (Vec d)} (hUmeas : MeasurableSet U) (i k : Fin d) :
    volumeAverageMat U a i k =
      (volume U).toReal⁻¹ •
        entryTestR i k (Set.indicator U (fun _ : Vec d ↦ (1 : ℝ))) a := by
  rw [entryTestR_indicator_one i k U hUmeas, smul_eq_mul]
  rfl

/-- The volume average over a bounded measurable set depends measurably on a
measurable family of regular coefficient fields. The corresponding
CoarseGraining theorem covers compact sets; the indicator of a bounded
measurable set is again an enriched test function, so the same argument applies. -/
theorem measurable_volumeAverageMat_of_isBounded {alpha : Type*}
    [MeasurableSpace alpha] {U : Set (Vec d)}
    (hUb : Bornology.IsBounded U) (hUmeas : MeasurableSet U)
    {a : alpha → RegCoeffField d} (ha : Measurable a) :
    Measurable (fun y ↦ volumeAverageMat U (a y)) := by
  refine measurable_matrix_of_entries ?_
  intro i k
  have hfun : (fun y ↦ volumeAverageMat U (a y) i k) =
      fun y ↦ (volume U).toReal⁻¹ •
        entryTestR i k (Set.indicator U (fun _ : Vec d ↦ (1 : ℝ))) (a y) := by
    funext y
    exact volumeAverageMat_apply_eq_smul_entryTestR (a y) hUmeas i k
  rw [hfun]
  exact ((measurable_entryTestR i k
    (isProbeR_indicator_of_isBounded hUb hUmeas)).comp ha).const_smul
    ((volume U).toReal⁻¹)

/-- The volume average of the infrared cutoff over a bounded measurable set is
measurable in the shell sequence. -/
theorem measurable_volumeAverageMat_streamCutoff {U : Set (Vec d)}
    (hUb : Bornology.IsBounded U) (hUmeas : MeasurableSet U) (L : ℕ) :
    Measurable
      (fun omega : ShellSeq d ↦ volumeAverageMat U (streamCutoff omega L)) :=
  measurable_volumeAverageMat_of_isBounded hUb hUmeas (measurable_streamCutoff L)

end

end SuperdiffusionCLT.Section2.Cutoff
