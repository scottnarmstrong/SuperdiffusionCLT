/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.LocalizationEnvelopeCarrier
public import SuperdiffusionCLT.Section2.Localization.LocalizationAverageT2Inputs

/-!
# Lower-shell measurability of the cutoff coarse block matrix

The printed `T2` estimate works with the envelope `bfE_ℓ`, which is the printed `bfE_m` at cutoff
scale `m = ℓ`, that is `envelopeBlockMat d nu ℓ`.  Its square root `envelopeSqrt d nu ℓ` and the
sandwich identity `blockVecDot_envelopeRescale_sandwich` live in
`LocalizationEnvelopeCarrier.lean`, and `localizationW_eq_envelopeBlockMat` identifies the printed
weight `W_z = |bfE_ℓ^{1/2}G_{-h_z}P|^2` with the `bfE_ℓ` quadratic form of the gauge vector.

This file supplies the measurability input of the `T2` chain.  The coarse block-matrix entries of
the cutoff field are measurable in the lower-shell σ-algebra
`shellSigma (localizationLowerShells l)`.  The generic entry lemmas
`measurable_coarseBlockMatrix_*_apply` of `Section2/Annealed/Measurability.lean` are
σ-algebra-parametric, so they are instantiated with this σ-algebra once the cutoff field is
known to be measurable there as a full `RegCoeffField`-valued function.

## Main results

* `measurable_SS_shellReg`, `measurable_SS_streamCutoff`, `measurable_SS_coefficientCutoff`
* `measurable_SS_coarseBlockMatrix_lowerLeft`, `measurable_SS_coarseBlockMatrix_lowerRight`
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open MeasureTheory Homogenization Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Carriers
open SuperdiffusionCLT.Section2.Cutoff

variable {d : ℕ}

/-- `shellSigma T` as an abbreviation, so the relative-measurability statements
below read as measurability in a σ-algebra that is a coordinate family. -/
noncomputable abbrev shellSigmaFamily (T : Set ℕ) : MeasurableSpace (ShellSeq d) :=
  SuperdiffusionCLT.Probability.shellSigma (d := d) T

/-! ## The cutoff field is measurable in the lower-shell σ-algebra -/

/-- The single shell field is measurable for any coordinate family containing its
coordinate. -/
theorem measurable_SS_shellReg {S : Set ℕ} {n : ℕ} (hn : n ∈ S) :
    Measurable[shellSigmaFamily (d := d) S] (fun omega : ShellSeq d => shellReg omega n) :=
  ShellField.measurable_forgetShell.comp (shellSigma_coordinate_measurable hn)

/-- The finite cutoff sum is measurable for a coordinate family containing the
shells `0, …, L`. -/
theorem measurable_SS_streamCutoff {S : Set ℕ} {L : ℕ} (hS : ∀ n ≤ L, n ∈ S) :
    Measurable[shellSigmaFamily (d := d) S] (fun omega : ShellSeq d => streamCutoff omega L) := by
  unfold streamCutoff
  exact Finset.measurable_sum _ fun n hn =>
    measurable_SS_shellReg (hS n (Nat.le_of_lt_succ (Finset.mem_range.mp hn)))

/-- The full `RegCoeffField`-valued cutoff field is measurable in a coordinate
family containing the shells `0, …, L`.  This is the full-field measurability that
`measurable_coarseBlockMatrix_*_apply` consumes. -/
theorem measurable_SS_coefficientCutoff {S : Set ℕ} {L : ℕ} (hS : ∀ n ≤ L, n ∈ S) (nu : ℝ) :
    Measurable[shellSigmaFamily (d := d) S] (fun omega : ShellSeq d => coefficientCutoff nu omega L) := by
  have hstr := measurable_SS_streamCutoff (d := d) (S := S) hS (L := L)
  have hconst : Measurable[shellSigmaFamily (d := d) S]
      (fun _ : ShellSeq d => nu • (1 : RegCoeffField d)) := measurable_const
  have heq : (fun omega : ShellSeq d => coefficientCutoff nu omega L) =
      fun omega => nu • (1 : RegCoeffField d) + streamCutoff omega L := by
    funext omega; rfl
  rw [heq]
  exact hconst.add hstr

/-! ## The four blocks of the coarse block matrix at the lower shells -/

/-- The lower-left block entries of the cutoff-`ℓ` coarse block matrix are
measurable in the lower-shell σ-algebra. -/
theorem measurable_SS_coarseBlockMatrix_lowerLeft {l : ℕ} {nu : ℝ} (hnu : 0 < nu)
    (R : TriadicCube d) (i j : Fin d) :
    Measurable[shellSigmaFamily (d := d) (localizationLowerShells l)]
      (fun omega : ShellSeq d =>
        (coarseBlockMatrix (cubeSet R) (coefficientCutoff nu omega l).toCoeffField).lowerLeft i j) := by
  let : MeasurableSpace (ShellSeq d) := shellSigmaFamily (d := d) (localizationLowerShells l)
  exact measurable_coarseBlockMatrix_lowerLeft_apply
    (A := fun omega : ShellSeq d => coefficientCutoff nu omega l)
    (measurable_SS_coefficientCutoff (S := localizationLowerShells l)
      (fun n hn => by simp only [localizationLowerShells, Set.mem_ofPred_eq]; exact hn) nu)
    (fun omega => aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega l) R i j

/-- The lower-right block entries of the cutoff-`ℓ` coarse block matrix are
measurable in the lower-shell σ-algebra. -/
theorem measurable_SS_coarseBlockMatrix_lowerRight {l : ℕ} {nu : ℝ} (hnu : 0 < nu)
    (R : TriadicCube d) (i j : Fin d) :
    Measurable[shellSigmaFamily (d := d) (localizationLowerShells l)]
      (fun omega : ShellSeq d =>
        (coarseBlockMatrix (cubeSet R) (coefficientCutoff nu omega l).toCoeffField).lowerRight i j) := by
  let : MeasurableSpace (ShellSeq d) := shellSigmaFamily (d := d) (localizationLowerShells l)
  exact measurable_coarseBlockMatrix_lowerRight_apply
    (A := fun omega : ShellSeq d => coefficientCutoff nu omega l)
    (measurable_SS_coefficientCutoff (S := localizationLowerShells l)
      (fun n hn => by simp only [localizationLowerShells, Set.mem_ofPred_eq]; exact hn) nu)
    (fun omega => aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega l) R i j

end SuperdiffusionCLT.Section2.Localization
