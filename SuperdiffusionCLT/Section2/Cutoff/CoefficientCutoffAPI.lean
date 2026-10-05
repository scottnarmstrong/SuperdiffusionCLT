/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Frozen.Section2.CoefficientCutoff
public import SuperdiffusionCLT.Section2.Cutoff.StreamCutoffAPI
public import Homogenization.CoarseGraining.Definitions

/-!
# The infrared cutoff of the marginal coefficient field

This module is the deterministic API of the cutoff coefficient field
`a_L = ν Id + k_L`. It evaluates the field, records its measurability in the
shell sequence, identifies its symmetric part with `ν Id` and its skew part
with `k_L`, and exhibits the bridge by which the coarse-graining layer consumes
it: the raw coefficient field of `a_L` is literally `x ↦ ν Id + k_L(x)`.

The symmetric-part identity is a consequence of the anti-symmetry of the
shells, not an ellipticity assumption; the range `ν ∈ (0, 1]` of the manuscript
belongs to the theorems that consume `a_L`, and appears nowhere here.

## Main results

* `coefficientCutoff_apply`: evaluation.
* `measurable_coefficientCutoff`: measurability in the shell sequence.
* `symmPart_coefficientCutoff`, `skewPart_coefficientCutoff`: the symmetric and
  skew parts.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Cutoff

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Section2
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-! ## Evaluation and measurability -/

/-- Matrix-valued evaluation of the cutoff coefficient field. -/
@[simp]
theorem coefficientCutoff_apply (nu : ℝ) (omega : ShellSeq d) (L : ℕ)
    (x : Vec d) :
    coefficientCutoff nu omega L x = nu • (1 : Mat d) + streamCutoff omega L x :=
  rfl

/-- The cutoff coefficient field is measurable on the shell-sequence
carrier. -/
theorem measurable_coefficientCutoff (nu : ℝ) (L : ℕ) :
    Measurable (fun omega : ShellSeq d ↦ coefficientCutoff nu omega L) :=
  measurable_const.add (measurable_streamCutoff L)

/-! ## The symmetric and skew parts -/

/-- The symmetric part of `a_L` is exactly `ν Id`; this is a pointwise identity
proved from the anti-symmetry of the shells, not an added ellipticity
hypothesis. -/
theorem symmPart_coefficientCutoff (nu : ℝ) (omega : ShellSeq d) (L : ℕ)
    (x : Vec d) :
    symmPart (coefficientCutoff nu omega L x) = nu • (1 : Mat d) := by
  ext i k
  have hskew : streamCutoff omega L x k i = -streamCutoff omega L x i k :=
    streamCutoff_skew_entry omega L x k i
  simp only [symmPart, coefficientCutoff_apply, Matrix.add_apply,
    Matrix.smul_apply]
  rw [hskew]
  by_cases hik : i = k
  · subst k
    simp only [Matrix.one_apply, smul_eq_mul]
    ring
  · have hki : k ≠ i := Ne.symm hik
    simp only [Matrix.one_apply, ite_eq_right hik, ite_eq_right hki, smul_eq_mul]
    ring

/-- The skew part of `a_L` is exactly `k_L`. -/
theorem skewPart_coefficientCutoff (nu : ℝ) (omega : ShellSeq d) (L : ℕ)
    (x : Vec d) :
    skewPart (coefficientCutoff nu omega L x) = streamCutoff omega L x := by
  ext i k
  have hskew : streamCutoff omega L x k i = -streamCutoff omega L x i k :=
    streamCutoff_skew_entry omega L x k i
  simp only [skewPart, coefficientCutoff_apply, Matrix.add_apply,
    Matrix.smul_apply]
  rw [hskew]
  by_cases hik : i = k
  · subst k
    simp only [Matrix.one_apply, smul_eq_mul]
    ring
  · have hki : k ≠ i := Ne.symm hik
    simp only [Matrix.one_apply, ite_eq_right hik, ite_eq_right hki, smul_eq_mul]
    ring

/-! ## The bridge to the coarse-graining layer

The coarse-grained matrices of `Homogenization.CoarseGraining` take a raw
`CoeffField d`. The cutoff coefficient field reaches them through
`RegCoeffField.toCoeffField`, and the field they then see is the manuscript's
`x ↦ ν Id + k_L(x)`. -/

/-- Entrywise reading of the raw coefficient field of `a_L`. -/
@[simp]
theorem coefficientCutoff_toCoeffField_apply (nu : ℝ) (omega : ShellSeq d)
    (L : ℕ) (x : Vec d) :
    (coefficientCutoff nu omega L).toCoeffField x =
      nu • (1 : Mat d) + streamCutoff omega L x :=
  rfl

end

end SuperdiffusionCLT.Section2.Cutoff
