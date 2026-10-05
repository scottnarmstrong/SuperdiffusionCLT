/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.Mixing.LargeGapConcentrationEntries
public import SuperdiffusionCLT.Section3.Terms.CoarseBlockLocalityB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3InputsC

/-!
# Locality and colour-partition independence of the entrywise deviation

Generalizes `SuperdiffusionCLT.Section3.Terms.CoarseBlockLocalityB`'s
lane-measurability argument (there specialized to the upper-left block only,
`translatedCoarseBlock`) to *every* entry of `bfA_L(z + cu_n)`, using the same
two ingredients: the deterministic locality
`coarseBlockMatrix_restrictedCoefficientCutoff_eq`
(`Section3/Terms/CoarseBlockLocality.lean`) and the general (any measurable
space) block measurability engine
`SuperdiffusionCLT.Section2.Annealed.measurable_coarseBlockMatrix_{upperLeft,upperRight,lowerLeft,lowerRight}_apply`.
No hypothesis beyond the standing shell laws is carried: unlike
`Section3.Terms.BlockConcentrationInputs`'s `hYlocal` (a hypothesis there,
since only the upper-left block's lane-measurability was available there), the
four-block engine closes the general-entry case outright.

The independence package then reuses
`SuperdiffusionCLT.Section3.Terms.iIndepFun_of_shellRestrictionLocal` and
the colour-partition machinery of `Section3/Terms/RHSTerm3InputsC.lean`
(`blockSublattice`, `biUnion_blockSublattice`, `disjoint_blockSublattice`,
`card_univ_blockClass`, `areShellSeparated_of_subset_cubeSet`) verbatim.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

open Homogenization
open MeasureTheory ProbabilityTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section3.Terms
open SuperdiffusionCLT.Section3.HighContrast (blockLane)

noncomputable section

variable {d : ℕ}

/-! ## Lane-measurability of a general entry -/

/-- **Every entry of `bfA_L(z + cu_n)` is an observable of the joined
restriction lane of any measurable set containing the cube.** The
four-block generalization of
`Section3.Terms.measurable_blockLane_translatedCoarseBlock_apply`. -/
theorem mixGap_measurable_blockLane_blockMatEntry [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {U : Set (Vec d)} (hU : MeasurableSet U) {ell L : ℕ} (hL : L ≤ ell)
    {z : TriadicCube d} (hz : cubeSet z ⊆ U) (alpha beta : BlockCoord d) :
    @Measurable (ShellSeq d) ℝ
      (blockLane ell (ShellField.shellRestrictionSigma U hU)) inferInstance
      (fun omega : ShellSeq d => blockMatEntry
        (coarseBlockMatrix (cubeSet z) (coefficientCutoff nu omega L).toCoeffField) alpha beta) := by
  have hA := measurable_blockLane_restrictedCoefficientCutoff nu hU hL
  have hEll := fun omega : ShellSeq d =>
    aeLocallyUniformlyEllipticField_restrictedCoefficientCutoff hnu hU omega L
  have hfun : (fun omega : ShellSeq d => blockMatEntry
      (coarseBlockMatrix (cubeSet z) (coefficientCutoff nu omega L).toCoeffField) alpha beta) =
      fun omega : ShellSeq d => blockMatEntry
        (coarseBlockMatrix (cubeSet z) (restrictedCoefficientCutoff nu hU omega L).toFun)
        alpha beta := by
    funext omega
    rw [show (coefficientCutoff nu omega L).toCoeffField = (coefficientCutoff nu omega L).toFun
        from rfl,
      coarseBlockMatrix_restrictedCoefficientCutoff_eq nu hU (measurableSet_cubeSet z) hz omega L]
  rw [hfun]
  cases alpha with
  | inl i =>
      cases beta with
      | inl j =>
          exact @measurable_coarseBlockMatrix_upperLeft_apply d (ShellSeq d)
            (blockLane ell (ShellField.shellRestrictionSigma U hU))
            (fun omega => restrictedCoefficientCutoff nu hU omega L) hA hEll z i j
      | inr j =>
          exact @measurable_coarseBlockMatrix_upperRight_apply d (ShellSeq d)
            (blockLane ell (ShellField.shellRestrictionSigma U hU))
            (fun omega => restrictedCoefficientCutoff nu hU omega L) hA hEll z i j
  | inr i =>
      cases beta with
      | inl j =>
          exact @measurable_coarseBlockMatrix_lowerLeft_apply d (ShellSeq d)
            (blockLane ell (ShellField.shellRestrictionSigma U hU))
            (fun omega => restrictedCoefficientCutoff nu hU omega L) hA hEll z i j
      | inr j =>
          exact @measurable_coarseBlockMatrix_lowerRight_apply d (ShellSeq d)
            (blockLane ell (ShellField.shellRestrictionSigma U hU))
            (fun omega => restrictedCoefficientCutoff nu hU omega L) hA hEll z i j

/-- **The centred entry deviation `bfA_L(z+cu_n)_{αβ} - bfAhom_L(cu_n)_{αβ}`
is lane-measurable**, the `hYlocal` shape `iIndepFun_of_shellRestrictionLocal`
takes, at the printed neighbourhood `nbhd z = cu`-ancestor of `z`. -/
theorem mixGap_measurable_blockLane_entryDeviation_nbhd [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)} {ell L : ℕ} (hL : L ≤ ell) (nn : ℕ)
    (alpha beta : BlockCoord d)
    {nbhd : TriadicCube d → Set (Vec d)} (hnbhd : ∀ z, MeasurableSet (nbhd z))
    (hsub : ∀ z : TriadicCube d, cubeSet z ⊆ nbhd z) :
    ∀ z : TriadicCube d,
      @Measurable (ShellSeq d) ℝ
        (blockLane ell (ShellField.shellRestrictionSigma (nbhd z) (hnbhd z)))
        inferInstance
        (fun omega : ShellSeq d => blockMatEntry
          (coarseBlockMatrix (cubeSet z) (coefficientCutoff nu omega L).toCoeffField) alpha beta -
          blockMatEntry (annealedBlockMatrix nu L P (cubeSet (originCube d (nn : ℤ)))) alpha beta) := by
  intro z
  exact (mixGap_measurable_blockLane_blockMatEntry hnu (hnbhd z) hL (hsub z) alpha beta).sub
    measurable_const

/-! ## `hIndep` from the colour partition -/

/-- **The colour-partition independence of the entrywise deviation, within one
sublattice.** The four-block generalization of
`Section3.Terms.iIndepFun_blockDeviation`. -/
theorem mixGap_iIndepFun_entryDeviation [NeZero d] {nu : ℝ} (hnu : 0 < nu) {kappa : Type*}
    {P : ProbabilityMeasure (ShellSeq d)}
    (hJ1 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P) {ell L : ℕ} (hL : L ≤ ell) (nn : ℕ)
    (alpha beta : BlockCoord d) (J : Finset kappa) (part : kappa → Finset (TriadicCube d))
    {nbhd : TriadicCube d → Set (Vec d)} (hnbhd : ∀ z, MeasurableSet (nbhd z))
    (hsub : ∀ z : TriadicCube d, cubeSet z ⊆ nbhd z)
    (hsep : ∀ j ∈ J, ∀ z ∈ part j, ∀ z' ∈ part j, z ≠ z' →
      ShellField.AreShellSeparated ell (nbhd z) (nbhd z')) :
    ∀ j ∈ J, iIndepFun
      (fun z : {z // z ∈ part j} => fun omega : ShellSeq d => blockMatEntry
        (coarseBlockMatrix (cubeSet (z : TriadicCube d))
          (coefficientCutoff nu omega L).toCoeffField) alpha beta -
        blockMatEntry (annealedBlockMatrix nu L P (cubeSet (originCube d (nn : ℤ)))) alpha beta)
      P.toMeasure :=
  iIndepFun_of_shellRestrictionLocal hJ1 hJ2 ell J part
    (fun omega z => blockMatEntry
      (coarseBlockMatrix (cubeSet z) (coefficientCutoff nu omega L).toCoeffField) alpha beta -
      blockMatEntry (annealedBlockMatrix nu L P (cubeSet (originCube d (nn : ℤ)))) alpha beta)
    hnbhd (mixGap_measurable_blockLane_entryDeviation_nbhd hnu hL nn alpha beta hnbhd hsub) hsep

end

end SuperdiffusionCLT.Section4.Mixing
