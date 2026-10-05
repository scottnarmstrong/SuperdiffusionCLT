/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.Conj3AveragedData2
public import SuperdiffusionCLT.Section2.Localization.Conj3RatioSandwich
public import SuperdiffusionCLT.Section2.Localization.CutoffMinimizerClause
public import SuperdiffusionCLT.Section2.Localization.CutoffMinimizerPremises
public import SuperdiffusionCLT.Section2.CoarseGraining.CutoffCorrespondence
public import SuperdiffusionCLT.Section2.Localization.BlockScalarCorrespondence

/-!
# The Chapter 2 coefficient objects of the cutoff pair

This module packages the two coefficient fields of the cutoff pair as Chapter 2 coefficient
objects on a domain `U`: the level-`m` cutoff field `a_m` and the centered cutoff-pair
field, each with its uniform ellipticity constants.

## Main definitions

* `levelMCoeffOn`: the level-`m` cutoff field as a Chapter 2 coefficient object.
* `centeredPairCoeffOn`: the centered cutoff-pair field as a Chapter 2 coefficient object.

## Main results

* `levelMCoeffOn_toCoeffField`, `centeredPairCoeffOn_toCoeffField`: the underlying raw
  coefficient fields.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section3.Terms
open scoped BigOperators

noncomputable section

/-! ## The two Chapter 2 coefficient objects of the cutoff pair -/

/-- The uniform entry bound of the level-`k` cutoff stream on a Chapter 2
domain: the shellwise bounds of `abs_streamCutoffEntryBound`, summed. -/
theorem abs_streamCutoff_entry_le_domain_local {d : ℕ} (U : Book.Ch02.Domain d)
    (omega : ShellSeq d) (k : ℕ) (y : Vec d) (hy : y ∈ (U : Set (Vec d))) (i j : Fin d) :
    |streamCutoff omega k y i j| ≤
      ∑ p : Fin d × Fin d,
        |streamCutoffEntryBound U.isDomain.isBoundedDomain.isBounded omega k p| := by
  calc |streamCutoff omega k y i j| ≤
      |streamCutoffEntryBound U.isDomain.isBoundedDomain.isBounded omega k (i, j)| :=
        (abs_streamCutoffEntryBound U.isDomain.isBoundedDomain.isBounded omega k
          (i, j) y hy).trans (le_abs_self _)
    _ ≤ ∑ p : Fin d × Fin d,
        |streamCutoffEntryBound U.isDomain.isBoundedDomain.isBounded omega k p| :=
        Finset.single_le_sum
          (f := fun p => |streamCutoffEntryBound U.isDomain.isBoundedDomain.isBounded
            omega k p|)
          (fun p _ => abs_nonneg _) (Finset.mem_univ _)

/-- The Chapter 2 coefficient object of the level-`m` cutoff field `a_m` on a
domain `U`.  Its field is definitionally `(coefficientCutoff nu omega m).toCoeffField`,
so every statement about `a_m` that names the field directly transfers. -/
noncomputable def levelMCoeffOn {d : ℕ} (U : Book.Ch02.Domain d) (nu : ℝ) (hnu : 0 < nu)
    (omega : ShellSeq d) (m : ℕ) : Book.Ch02.CoeffOn U :=
  SuperdiffusionCLT.Section2.CoarseGraining.coefficientCutoffCoeffOn U hnu omega m
    (fun x hx i j =>
      SuperdiffusionCLT.Section2.CoarseGraining.abs_coefficientCutoff_entry_le
        hnu.le omega m x
        (fun i j => abs_streamCutoff_entry_le_domain_local U omega m x hx i j) i j)

@[simp] theorem levelMCoeffOn_toCoeffField {d : ℕ} (U : Book.Ch02.Domain d) (nu : ℝ)
    (hnu : 0 < nu) (omega : ShellSeq d) (m : ℕ) :
    (levelMCoeffOn U nu hnu omega m).toCoeffField =
      (coefficientCutoff nu omega m).toCoeffField :=
  rfl

/-- The Chapter 2 coefficient object of the two-cutoff-centered field
`â = a_L - (k_L - k_m)_U` on a domain `U`.  Its field is definitionally
`centeredPairField nu omega m L (U : Set (Vec d))`; the lower ellipticity
constant is `nu` and the upper one is the entry bound converted to the
inverse-side bound. -/
noncomputable def centeredPairCoeffOn {d : ℕ} (U : Book.Ch02.Domain d) (nu : ℝ)
    (hnu : 0 < nu) (omega : ShellSeq d) (m L : ℕ) (hmL : m ≤ L) : Book.Ch02.CoeffOn U where
  toCoeffField := centeredPairField nu omega m L (U : Set (Vec d))
  lam := nu
  Lam := ((d : ℝ) * (d : ℝ) * centeredPairEntryBound U nu omega m L ^ 2 + nu ^ 2) / nu
  lam_pos := hnu
  lam_le_Lam := by
    rw [le_div_iff₀ hnu, ← pow_two]
    linarith only [show (0 : ℝ) ≤ (d : ℝ) * (d : ℝ) *
      centeredPairEntryBound U nu omega m L ^ 2 by positivity]
  aeStronglyMeasurable := by
    classical
    intro i j
    have hEq : (fun x : Vec d => restrictCoeffField (U : Set (Vec d))
        (centeredPairField nu omega m L (U : Set (Vec d))) x i j) =
        fun x : Vec d => if x ∈ (U : Set (Vec d)) then
          (coefficientCutoff nu omega L).toCoeffField x i j -
            volumeAverageMat (U : Set (Vec d))
              (fun y => finiteShellIncrement omega m L y) i j else 0 := by
      funext x
      by_cases hx : x ∈ (U : Set (Vec d)) <;>
        simp [restrictCoeffField, centeredPairField, hx]
    rw [hEq]
    have h1 : Measurable (fun x : Vec d => (coefficientCutoff nu omega L).toCoeffField x i j) :=
      (coefficientCutoff nu omega L).entry_measurable i j
    have h2 : Measurable (fun _ : Vec d => volumeAverageMat (U : Set (Vec d))
        (fun y => finiteShellIncrement omega m L y) i j) := measurable_const
    exact ((h1.sub h2).ite U.measurableSet measurable_const).aestronglyMeasurable
  aeElliptic := by
    filter_upwards [MeasureTheory.ae_restrict_mem U.measurableSet] with x hx
    exact isEllipticMatrix_centeredPairField_domain U nu hnu omega m L hmL x hx

@[simp] theorem centeredPairCoeffOn_toCoeffField {d : ℕ} (U : Book.Ch02.Domain d) (nu : ℝ)
    (hnu : 0 < nu) (omega : ShellSeq d) (m L : ℕ) (hmL : m ≤ L) :
    (centeredPairCoeffOn U nu hnu omega m L hmL).toCoeffField =
      centeredPairField nu omega m L (U : Set (Vec d)) :=
  rfl

end

end SuperdiffusionCLT.Section2.Localization
