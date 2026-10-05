/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.CutoffComparison
public import SuperdiffusionCLT.Section2.Cutoff.CenteredCoeffOn
public import SuperdiffusionCLT.Section2.Localization.BlockSandwichExtraction
public import SuperdiffusionCLT.Section2.Localization.BlockGaugeGroup
public import SuperdiffusionCLT.Section2.Localization.BlockPerturbation
public import SuperdiffusionCLT.Section2.Localization.CenteredIncrementQuadratic
public import SuperdiffusionCLT.Section2.Localization.LocalizationWitnessPackaging
public import SuperdiffusionCLT.Section2.Localization.ShellWindowDomination
public import Homogenization.CoarseGraining.ResponseIdentities.Foundations.Algebra
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementMoreoverBlockE
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2
public import SuperdiffusionCLT.Section2.Localization.BlockScalarCorrespondence

/-!
# The minimizers clause of the localization statement (`e.localization.minimizers`)

The third conjunct of the statement `Frozen.Section2.cutoff_localization`
(`l.localization`): for every `omega`, `p`, `q` and every
pair of maximizers `u` (for the volume-average-centered level-`L` cutoff field
`â = a_L - (k_L - k_m)_U`) and `v` (for the level-`m` cutoff field `a_m`),
the squared gradient difference satisfies

`⨍_U ‖∇u - ∇v|² ≤ C ν⁻² 3^n · window · (J(U,p,q;â) + J(U,p,q;a_m) + 2 p·q)`,

with the window the exact `L^∞(cu_n)` carrier `Section3.Terms.anchorDerivSup`.

This module supplies the carriers of the clause: the volume-average-centered cutoff field
and the pointwise two-sided ellipticity of the two fields on `U`, assembled from the
entry bounds of `CenteredCoeffOn`.

## Main results

* `centeredPairField`: the volume-average-centered level-`L` cutoff field
  `â = a_L - (k_L - k_m)_U` of the statement.
* `centeredPairEntryBound`: the entry bound of the centered field on a Chapter 2 domain.
* `isEllipticMatrix_coefficientCutoff_domain`,
  `isEllipticMatrix_centeredPairField_domain`: the pointwise two-sided
  ellipticity of the two fields on a Chapter 2 domain inside `cu_n`.
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
open SuperdiffusionCLT.Section2.CoarseGraining
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Terms
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## The volume-average-centered cutoff pair -/

/-- **The two-cutoff-centered cutoff field** `â = a_L - (k_L - k_m)_U` of the
third conjunct: the level-`L` cutoff field minus the volume average of
the finite shell increment over `U`.  Definitionally the field of the
statement. -/
def centeredPairField (nu : ℝ) (omega : ShellSeq d) (m L : ℕ) (U : Set (Vec d)) :
    CoeffField d :=
  fun x => (coefficientCutoff nu omega L).toCoeffField x -
    volumeAverageMat U (fun y => finiteShellIncrement omega m L y)

/-- The symmetric part of the two-cutoff-centered field is again `ν Id`: the
subtracted average of the anti-symmetric increment is anti-symmetric
(`matTranspose_volumeAverageMat`). -/
private theorem symmPart_centeredPairField (nu : ℝ) (omega : ShellSeq d) (m L : ℕ)
    (U : Set (Vec d)) (x : Vec d) :
    symmPart (centeredPairField nu omega m L U x) = nu • (1 : Mat d) := by
  have hH : matTranspose (volumeAverageMat U
      (fun y => finiteShellIncrement omega m L y)) =
    -(volumeAverageMat U (fun y => finiteShellIncrement omega m L y)) := by
    have h := matTranspose_volumeAverageMat U
      (fun y => finiteShellIncrement omega m L y)
      (fun y i k => congrFun (congrFun (finiteShellIncrement_skew omega m L y) k) i)
    simpa only [matTranspose, Matrix.transpose_neg, neg_neg] using h
  have hneg : matTranspose (-(volumeAverageMat U
      (fun y => finiteShellIncrement omega m L y))) =
    -(-(volumeAverageMat U (fun y => finiteShellIncrement omega m L y))) := by
    show -matTranspose (volumeAverageMat U
      (fun y => finiteShellIncrement omega m L y)) = _
    rw [hH]
  exact (symmPart_add_of_skew hneg).trans
    (symmPart_coefficientCutoff nu omega L x)

/-! ## The entry bounds and the two-sided ellipticity on `U` -/

/-- The uniform entry bound of the level-`k` cutoff stream on a Chapter 2
domain: the shellwise bounds of `abs_streamCutoffEntryBound`, summed. -/
private theorem abs_streamCutoff_entry_le_domain (U : Book.Ch02.Domain d)
    (omega : ShellSeq d) (k : ℕ) (y : Vec d) (hy : y ∈ (U : Set (Vec d)))
    (i j : Fin d) :
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

/-- The volume average of the finite shell increment inherits the uniform
entry bound of the increment on `U` (the averaging argument of
`abs_volumeAverageMat_streamCutoff_entry_le`). -/
private theorem abs_volumeAverageMat_entry_le {omega : ShellSeq d} {m L : ℕ}
    (U : Book.Ch02.Domain d) {C : ℝ}
    (hC : ∀ y ∈ (U : Set (Vec d)), ∀ i j : Fin d,
      |finiteShellIncrement omega m L y i j| ≤ C)
    (i j : Fin d) :
    |volumeAverageMat (U : Set (Vec d))
        (fun y => finiteShellIncrement omega m L y) i j| ≤ C := by
  have hUb : Bornology.IsBounded (U : Set (Vec d)) :=
    U.isDomain.isBoundedDomain.isBounded
  have hUtop : volume (U : Set (Vec d)) ≠ ⊤ := volume_ne_top_of_isBounded hUb
  have hvol : 0 < (volume (U : Set (Vec d))).toReal :=
    ENNReal.toReal_pos (IsOpen.measure_pos volume U.isOpen U.nonempty).ne' hUtop
  have hint : IntegrableOn (fun y => finiteShellIncrement omega m L y i j)
      (U : Set (Vec d)) volume :=
    integrableOn_entry_of_isBounded (finiteShellIncrement omega m L) hUb i j
  have hintneg : IntegrableOn (fun y => (-(C : ℝ))) (U : Set (Vec d)) volume :=
    integrableOn_const (C := (-(C : ℝ))) hUtop
  have hintC : IntegrableOn (fun y => (C : ℝ)) (U : Set (Vec d)) volume :=
    integrableOn_const (C := C) hUtop
  have hconst : ∫ y in (U : Set (Vec d)), (C : ℝ) ∂volume =
      (volume (U : Set (Vec d))).toReal * C := by
    rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real, smul_eq_mul]
  have hconstneg : ∫ y in (U : Set (Vec d)), (-(C : ℝ)) ∂volume =
      -((volume (U : Set (Vec d))).toReal * C) := by
    rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real, smul_eq_mul,
      mul_neg]
  have hun : NullMeasurableSet (U : Set (Vec d)) volume :=
    U.measurableSet.nullMeasurableSet
  have habs : |∫ y in (U : Set (Vec d)), finiteShellIncrement omega m L y i j ∂volume| ≤
      (volume (U : Set (Vec d))).toReal * C := by
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · have hlow : ∫ y in (U : Set (Vec d)), (-(C : ℝ)) ∂volume ≤
          ∫ y in (U : Set (Vec d)), finiteShellIncrement omega m L y i j ∂volume :=
        MeasureTheory.setIntegral_mono_on₀ hintneg hint hun
          fun y hy => (abs_le.mp (hC y hy i j)).1
      rwa [hconstneg] at hlow
    · have hhigh : ∫ y in (U : Set (Vec d)), finiteShellIncrement omega m L y i j ∂volume ≤
          ∫ y in (U : Set (Vec d)), (C : ℝ) ∂volume :=
        le_trans (MeasureTheory.setIntegral_mono_on₀ hint hint.abs hun
          fun y _ => le_abs_self _)
          (MeasureTheory.setIntegral_mono_on₀ hint.abs hintC hun
            fun y hy => hC y hy i j)
      rwa [hconst] at hhigh
  have hval : volumeAverageMat (U : Set (Vec d))
      (fun y => finiteShellIncrement omega m L y) i j =
    (volume (U : Set (Vec d))).toReal⁻¹ *
      ∫ y in (U : Set (Vec d)), finiteShellIncrement omega m L y i j ∂volume := by
    simp only [volumeAverageMat, volumeAverage]
  rw [hval, abs_mul, abs_of_pos (inv_pos.mpr hvol)]
  calc (volume (U : Set (Vec d))).toReal⁻¹ *
      |∫ y in (U : Set (Vec d)), finiteShellIncrement omega m L y i j ∂volume| ≤
      (volume (U : Set (Vec d))).toReal⁻¹ * ((volume (U : Set (Vec d))).toReal * C) :=
        mul_le_mul_of_nonneg_left habs (inv_nonneg.2 hvol.le)
    _ = C := by field_simp

/-- The uniform entry bound of the finite shell increment on a Chapter 2
domain: the level-`L` stream bound plus the level-`m` stream bound, from the
subtraction form of the increment. -/
private theorem abs_finiteShellIncrement_entry_le (omega : ShellSeq d) (m L : ℕ)
    (hmL : m ≤ L) (U : Book.Ch02.Domain d) (y : Vec d) (hy : y ∈ (U : Set (Vec d)))
    (i j : Fin d) :
    |finiteShellIncrement omega m L y i j| ≤
      ∑ p : Fin d × Fin d,
        |streamCutoffEntryBound U.isDomain.isBoundedDomain.isBounded omega L p| +
      ∑ p : Fin d × Fin d,
        |streamCutoffEntryBound U.isDomain.isBoundedDomain.isBounded omega m p| := by
  have happly : finiteShellIncrement omega m L y i j =
      streamCutoff omega L y i j - streamCutoff omega m y i j := by
    rw [finiteShellIncrement_apply_eq_streamCutoff_sub omega hmL y]
    rfl
  rw [happly]
  have hL := abs_streamCutoff_entry_le_domain U omega L y hy i j
  have hM := abs_streamCutoff_entry_le_domain U omega m y hy i j
  exact (abs_sub _ _).trans (by linarith only [hL, hM])

/-- **The entry bound of the two-cutoff-centered field** on a Chapter 2 domain:
one `ν` for the diagonal of `ν Id`, two level-`L` stream bounds (the field and
its averaged subtraction) and one level-`m` stream bound. -/
noncomputable def centeredPairEntryBound (U : Book.Ch02.Domain d) (nu : ℝ)
    (omega : ShellSeq d) (m L : ℕ) : ℝ :=
  nu + 2 * ∑ p : Fin d × Fin d,
      |streamCutoffEntryBound U.isDomain.isBoundedDomain.isBounded omega L p| +
    ∑ p : Fin d × Fin d,
      |streamCutoffEntryBound U.isDomain.isBoundedDomain.isBounded omega m p|

/-- The two-cutoff-centered field satisfies the entry bound on `U`. -/
private theorem abs_centeredPairField_entry_le (U : Book.Ch02.Domain d) (nu : ℝ)
    (hnu : 0 < nu) (omega : ShellSeq d) (m L : ℕ) (hmL : m ≤ L) (x : Vec d)
    (hx : x ∈ (U : Set (Vec d))) (i j : Fin d) :
    |centeredPairField nu omega m L (U : Set (Vec d)) x i j| ≤
      centeredPairEntryBound U nu omega m L := by
  have hL : ∀ y ∈ (U : Set (Vec d)), ∀ p q : Fin d,
      |streamCutoff omega L y p q| ≤ ∑ p : Fin d × Fin d,
        |streamCutoffEntryBound U.isDomain.isBoundedDomain.isBounded omega L p| :=
    fun y hy => abs_streamCutoff_entry_le_domain U omega L y hy
  have hinc := abs_volumeAverageMat_entry_le U (C := ∑ p : Fin d × Fin d,
      |streamCutoffEntryBound U.isDomain.isBoundedDomain.isBounded omega L p| +
        ∑ p : Fin d × Fin d,
          |streamCutoffEntryBound U.isDomain.isBoundedDomain.isBounded omega m p|)
    (fun y hy k l => abs_finiteShellIncrement_entry_le omega m L hmL U y hy k l) i j
  have hsub : |(coefficientCutoff nu omega L).toCoeffField x i j -
      volumeAverageMat (U : Set (Vec d))
        (fun y => finiteShellIncrement omega m L y) i j| ≤
      |(coefficientCutoff nu omega L).toCoeffField x i j| +
        |volumeAverageMat (U : Set (Vec d))
          (fun y => finiteShellIncrement omega m L y) i j| := abs_sub _ _
  have hcut := abs_coefficientCutoff_entry_le (le_of_lt hnu)
    omega L x (fun i j => hL x hx i j) i j
  unfold centeredPairEntryBound
  show |(coefficientCutoff nu omega L).toCoeffField x i j -
      volumeAverageMat (U : Set (Vec d))
        (fun y => finiteShellIncrement omega m L y) i j| ≤
    nu + 2 * ∑ p : Fin d × Fin d,
        |streamCutoffEntryBound U.isDomain.isBoundedDomain.isBounded omega L p| +
      ∑ p : Fin d × Fin d,
        |streamCutoffEntryBound U.isDomain.isBoundedDomain.isBounded omega m p|
  linarith only [hsub, hcut, hinc]

/-! ## The two-sided ellipticity on `U` -/

/-- **The pointwise two-sided ellipticity of the level-`m` cutoff field on
`U`**: symmetric part `ν Id` and the compactness entry bound
(`isEllipticMatrix_of_symmPart_eq_smul_one`), with the uniform entry bound of
the level-`m` stream. -/
theorem isEllipticMatrix_coefficientCutoff_domain (U : Book.Ch02.Domain d)
    (nu : ℝ) (hnu : 0 < nu) (omega : ShellSeq d) (m : ℕ) (x : Vec d)
    (hx : x ∈ (U : Set (Vec d))) :
    IsEllipticMatrix nu
      (((d : ℝ) * (d : ℝ) *
          (nu + ∑ p : Fin d × Fin d,
            |streamCutoffEntryBound U.isDomain.isBoundedDomain.isBounded omega m p|) ^
            2 + nu ^ 2) / nu)
      ((coefficientCutoff nu omega m).toCoeffField x) :=
  isEllipticMatrix_of_symmPart_eq_smul_one hnu
    (symmPart_coefficientCutoff nu omega m x) fun i j =>
    abs_coefficientCutoff_entry_le (le_of_lt hnu) omega m x
      (fun i j => abs_streamCutoff_entry_le_domain U omega m x hx i j) i j

/-- **The pointwise two-sided ellipticity of the two-cutoff-centered field on
`U`**: symmetric part `ν Id` and the entry bound
`centeredPairEntryBound`. -/
theorem isEllipticMatrix_centeredPairField_domain (U : Book.Ch02.Domain d)
    (nu : ℝ) (hnu : 0 < nu) (omega : ShellSeq d) (m L : ℕ) (hmL : m ≤ L)
    (x : Vec d) (hx : x ∈ (U : Set (Vec d))) :
    IsEllipticMatrix nu
      (((d : ℝ) * (d : ℝ) * centeredPairEntryBound U nu omega m L ^ 2 + nu ^ 2) /
        nu)
      (centeredPairField nu omega m L (U : Set (Vec d)) x) := by
  refine isEllipticMatrix_of_symmPart_eq_smul_one hnu
    (symmPart_centeredPairField nu omega m L U x) fun i j => ?_
  exact abs_centeredPairField_entry_le U nu hnu omega m L hmL x hx i j

end

end SuperdiffusionCLT.Section2.Localization