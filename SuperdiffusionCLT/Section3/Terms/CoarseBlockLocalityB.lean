/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.CoarseBlockLocality

/-!
# `hYlocal`: the coarse block is a restriction-lane observable

Step 3 of the proof of `l.RHS.term3` states: *"each `Y_z` is a function
only of the cutoff-`ℓ` environment in a `C3^ℓ` neighbourhood of `z + cu_n`; this
follows from the definition of the localized coarse-grained matrix and
`a.j.frd`.  Hence the family has range of dependence `C3^ℓ`."*

`Section3/Terms/BlockConcentrationInputs.lean` separates that sentence into the
geometric half `hsep`, which is proved there, and the analytic half `hYlocal`,
which was left as a hypothesis: the centred coarse block
`Y_z = e·(b_L(z + cu_n) − shom_L(cu_n))e` has to be measurable for the lane
`blockLane ell (ShellField.shellRestrictionSigma (nbhd z))`.

This module proves `hYlocal`.  The two ingredients are

* the deterministic locality of the coarse-graining functional, packaged in
  `Section3/Terms/CoarseBlockLocality.lean`: the coarse block matrix on the cube
  is unchanged when the shells are replaced by their restrictions to any
  measurable set containing the cube, and the restricted cutoff is an observable
  of the joined restriction lane; and
* the measurability engine
  `SuperdiffusionCLT.Section2.Annealed.measurable_coarseBlockMatrix_upperLeft_apply`,
  which is stated for an *arbitrary* measurable space on the sample carrier — the
  countable `AEE` ellipticity slices cover the carrier whatever the sigma-field
  is, and on each slice `CoarseGraining`'s slice engine makes `Mu` measurable
  from the localized entry tests.  It is therefore applied here verbatim at the
  restriction lane instead of at the ambient sigma-field.

No new measurability of a variational value is assumed: the passage from the
point evaluations to the coarse block is carried by the same slice engine that
produced the ambient measurability, and the localization is the exact
`Mu`-congruence `Homogenization.coarseBlockMatrix_congr_of_ae_eq`.

## Main results

* `measurable_blockLane_translatedCoarseBlock_apply`: each entry of
  `b_L(z + cu_n)` is an observable of the joined restriction lane of any
  measurable set containing the cube, once `L ≤ ell`.
* `measurable_blockLane_blockDeviation`,
  `measurable_blockLane_blockDeviation_nbhd`: the same for `Y_z`; the second is
  `hYlocal` in the exact shape `iIndepFun_of_shellRestrictionLocal` takes.
* `iIndepFun_blockDeviation`: `hIndep` of `block_concentration` with the
  locality discharged, the separation still supplied.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory ProbabilityTheory
open Homogenization
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section3.HighContrast

noncomputable section

variable {d : ℕ}

/-! ## The entries of the coarse block -/

/-- **Each entry of `b_L(z + cu_n)` is an observable of the joined restriction
lane of any measurable set containing the cube.**  The coarse block matrix on the
cube is the one of the restricted cutoff
(`coarseBlockMatrix_restrictedCoefficientCutoff_eq`), the restricted cutoff is
lane-measurable (`measurable_blockLane_restrictedCoefficientCutoff`) and
admissible at every sample
(`aeLocallyUniformlyEllipticField_restrictedCoefficientCutoff`), so the
slice engine applies at the lane. -/
theorem measurable_blockLane_translatedCoarseBlock_apply [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) {U : Set (Vec d)} (hU : MeasurableSet U) {ell L : ℕ} (hL : L ≤ ell)
    {z : TriadicCube d} (hz : cubeSet z ⊆ U) (i j : Fin d) :
    @Measurable (ShellSeq d) ℝ
      (blockLane ell (ShellField.shellRestrictionSigma U hU)) inferInstance
      (fun omega : ShellSeq d ↦ translatedCoarseBlock nu L omega z i j) := by
  have h := @measurable_coarseBlockMatrix_upperLeft_apply d (ShellSeq d)
    (blockLane ell (ShellField.shellRestrictionSigma U hU))
    (fun omega : ShellSeq d ↦ restrictedCoefficientCutoff nu hU omega L)
    (measurable_blockLane_restrictedCoefficientCutoff nu hU hL)
    (fun omega ↦ aeLocallyUniformlyEllipticField_restrictedCoefficientCutoff hnu hU omega L)
    z i j
  have hfun : (fun omega : ShellSeq d ↦ translatedCoarseBlock nu L omega z i j) =
      fun omega : ShellSeq d ↦
        (coarseBlockMatrix (cubeSet z)
          (restrictedCoefficientCutoff nu hU omega L).toFun).upperLeft i j := by
    funext omega
    rw [translatedCoarseBlock_apply,
      coarseBlockMatrix_restrictedCoefficientCutoff_eq nu hU (measurableSet_cubeSet z) hz
        omega L]
  rw [hfun]
  exact h

/-! ## `hYlocal` -/

private theorem vecDot_matVecMul_eq_sum_aux (e : Vec d) (M : Mat d) :
    vecDot e (matVecMul M e) = ∑ i, ∑ j, e i * (M i j * e j) := by
  rw [vecDot]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [matVecMul, Finset.mul_sum]

/-- **`Y_z` is an observable of the joined restriction lane of any measurable set
containing the cube.**  It is a fixed real quadratic form in the entries of
`b_L(z + cu_n)`, shifted by the deterministic constant `shom_L(cu_n)`. -/
theorem measurable_blockLane_blockDeviation [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)} {U : Set (Vec d)} (hU : MeasurableSet U)
    {ell L : ℕ} (hL : L ≤ ell) (nn : ℕ) (e : Vec d)
    {z : TriadicCube d} (hz : cubeSet z ⊆ U) :
    @Measurable (ShellSeq d) ℝ
      (blockLane ell (ShellField.shellRestrictionSigma U hU)) inferInstance
      (fun omega : ShellSeq d ↦ blockDeviation nu L P nn e omega z) := by
  have hfun : (fun omega : ShellSeq d ↦ blockDeviation nu L P nn e omega z) =
      fun omega : ShellSeq d ↦
        (∑ i, ∑ j, e i * (translatedCoarseBlock nu L omega z i j * e j)) -
          sigmaBarSeq nu L P nn := by
    funext omega
    rw [blockDeviation, vecDot_matVecMul_eq_sum_aux e]
  rw [hfun]
  refine Measurable.sub ?_ measurable_const
  refine Finset.measurable_sum _ fun i _ ↦ Finset.measurable_sum _ fun j _ ↦ ?_
  exact ((measurable_blockLane_translatedCoarseBlock_apply hnu hU hL hz i j).mul_const
    (e j)).const_mul (e i)

/-- **`hYlocal` of `iIndepFun_of_shellRestrictionLocal`, for the centred coarse
blocks.**  The observation regions are any measurable sets containing their
cubes; the printed choice is the `C3^ℓ` neighbourhood of `z + cu_n`. -/
theorem measurable_blockLane_blockDeviation_nbhd [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)} {ell L : ℕ} (hL : L ≤ ell) (nn : ℕ) (e : Vec d)
    {nbhd : TriadicCube d → Set (Vec d)} (hnbhd : ∀ z, MeasurableSet (nbhd z))
    (hsub : ∀ z : TriadicCube d, cubeSet z ⊆ nbhd z) :
    ∀ z : TriadicCube d,
      @Measurable (ShellSeq d) ℝ
        (blockLane ell (ShellField.shellRestrictionSigma (nbhd z) (hnbhd z)))
        inferInstance (fun omega : ShellSeq d ↦ blockDeviation nu L P nn e omega z) :=
  fun z ↦ measurable_blockLane_blockDeviation hnu (hnbhd z) hL nn e (hsub z)

/-! ## `hIndep` of `block_concentration` -/

section Independence

variable {P : ProbabilityMeasure (ShellSeq d)}

/-- **`hIndep` of `block_concentration` with the locality discharged.**  Only the
geometric separation of the observation regions inside each sublattice is left
as a hypothesis; it is the printed splitting of the fine lattice into
sublattices of mutual distance at least `C3^ℓ`. -/
theorem iIndepFun_blockDeviation [NeZero d] {nu : ℝ} (hnu : 0 < nu) {kappa : Type*}
    (hJ1 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P) {ell L : ℕ} (hL : L ≤ ell) (nn : ℕ)
    (e : Vec d) (J : Finset kappa) (part : kappa → Finset (TriadicCube d))
    {nbhd : TriadicCube d → Set (Vec d)} (hnbhd : ∀ z, MeasurableSet (nbhd z))
    (hsub : ∀ z : TriadicCube d, cubeSet z ⊆ nbhd z)
    (hsep : ∀ j ∈ J, ∀ z ∈ part j, ∀ z' ∈ part j, z ≠ z' →
      ShellField.AreShellSeparated ell (nbhd z) (nbhd z')) :
    ∀ j ∈ J, iIndepFun
      (fun z : {z // z ∈ part j} =>
        fun omega : ShellSeq d ↦ blockDeviation nu L P nn e omega (z : TriadicCube d))
      P.toMeasure :=
  iIndepFun_blockDeviation_of_local hJ1 hJ2 ell L nn e J part hnbhd
    (measurable_blockLane_blockDeviation_nbhd hnu hL nn e hnbhd hsub) hsep

end Independence

end

end SuperdiffusionCLT.Section3.Terms
