/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.BlockConcentrationInputs

/-!
# The infrared cutoff read only on an observation set

Step 3 of the proof of `l.RHS.term3` states: *"each `Y_z` is a function only of the cutoff-`ℓ`
environment in a `C3^ℓ` neighbourhood of `z + cu_n`; this follows from the definition of the
localized coarse-grained matrix and `a.j.frd`."*

The coarse block `b_L(z + cu_n)` is the upper-left block of
`coarseBlockMatrix (openCubeSet z) a_L`, a variational quantity: it is the value
of the Chapter 2 energy `Mu` on the cube, and no finite set of point evaluations
determines it.  What *is* true, and is proved here, is that the coefficient
field only enters through its values on the cube: `Mu U P a` is defined from the
volume averages over `U` of the block energy density of `a`, so it is unchanged
when `a` is modified off `U` (`Homogenization.Mu_congr_of_ae_eq` and its
corollary `Homogenization.coarseBlockMatrix_congr_of_ae_eq`).

This module turns that observation into a factorization through the restriction
lane.  The cutoff `a_L = ν Id + ∑_{n ≤ L} j_n` is replaced by

`restrictedCoefficientCutoff nu hU omega L = ν Id + ∑_{n ≤ L} 1_U j_n`,

in which every shell has been passed through `Homogenization.restrictReg U hU`,
the endomorphism whose comap *defines* the restriction lane
`ShellField.shellRestrictionSigma`.  The restricted cutoff

* agrees with `a_L` on `U`, hence has the same coarse matrices on every subset
  of `U` (`coarseBlockMatrix_restrictedCoefficientCutoff_eq`);
* is still admissible at every sample — its symmetric part is the constant
  `ν Id` because an indicator multiple of a skew matrix stays skew, and its
  entries are still bounded on every cube
  (`aeLocallyUniformlyEllipticField_restrictedCoefficientCutoff`); and
* is, as a map into `Homogenization.RegCoeffField d`, measurable for the joined
  restriction lane `blockLane ell (ShellField.shellRestrictionSigma U hU)`
  whenever `L ≤ ell` (`measurable_blockLane_restrictedCoefficientCutoff`).

The companion module `Section3/Terms/CoarseBlockLocalityB.lean` feeds this into
the measurability engine `measurable_coarseBlockMatrix_upperLeft_apply`,
which is stated for an arbitrary measurable space on the sample carrier and is
therefore applied verbatim at the restriction lane.

## Main definitions

* `restrictedCoefficientCutoff`: `ν Id + ∑_{n ≤ L} 1_U j_n`.

## Main results

* `restrictedCoefficientCutoff_eq_of_mem`, `restrictedCoefficientCutoff_eq_of_notMem`:
  the two pointwise values.
* `symmPart_restrictedCoefficientCutoff`: the symmetric part is `ν Id`.
* `aeLocallyUniformlyEllipticField_restrictedCoefficientCutoff`: admissibility at
  every sample.
* `shellLane_shellRestrictionSigma_eq_comap`,
  `measurable_shellLane_restrictReg_shellReg`: the restricted shell generates its
  own shell lane.
* `measurable_blockLane_restrictedCoefficientCutoff`: measurability for the
  joined restriction lane of `U`.
* `coarseBlockMatrix_restrictedCoefficientCutoff_eq`: the coarse block matrix on
  a subset of `U` is unchanged.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open Homogenization
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.CoarseGraining
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section3.HighContrast

noncomputable section

variable {d : ℕ}

/-! ## The restricted cutoff -/

/-- **The infrared cutoff whose shells are read only on `U`**: the field
`ν Id + ∑_{n ≤ L} 1_U j_n`, in which every shell of
`SuperdiffusionCLT.Frozen.Section2.coefficientCutoff` has been passed
through the restriction endomorphism `Homogenization.restrictReg U hU`.  The
constant part is left untouched, so the field stays uniformly elliptic off
`U`. -/
def restrictedCoefficientCutoff (nu : ℝ) {U : Set (Vec d)} (hU : MeasurableSet U)
    (omega : ShellSeq d) (L : ℕ) : RegCoeffField d :=
  RegCoeffField.constRegCoeffField (nu • (1 : Mat d)) +
    ∑ n ∈ Finset.range (L + 1), restrictReg U hU (shellReg omega n)

/-- On the observation set the restricted cutoff is the cutoff. -/
theorem restrictedCoefficientCutoff_eq_of_mem (nu : ℝ) {U : Set (Vec d)}
    (hU : MeasurableSet U) (omega : ShellSeq d) (L : ℕ) {x : Vec d} (hx : x ∈ U) :
    (restrictedCoefficientCutoff nu hU omega L).toFun x =
      (coefficientCutoff nu omega L).toFun x := by
  have hshell : ∀ n : ℕ, (restrictReg U hU (shellReg omega n)).toFun x =
      (shellReg omega n).toFun x := by
    intro n
    rw [restrictReg_apply, Set.indicator_of_mem hx]
  simp only [restrictedCoefficientCutoff, RegCoeffField.add_apply,
    RegCoeffField.finset_sum_apply, RegCoeffField.constRegCoeffField_apply, hshell,
    coefficientCutoff, streamCutoff]

/-- Off the observation set the restricted cutoff is the constant `ν Id`. -/
theorem restrictedCoefficientCutoff_eq_of_notMem (nu : ℝ) {U : Set (Vec d)}
    (hU : MeasurableSet U) (omega : ShellSeq d) (L : ℕ) {x : Vec d} (hx : x ∉ U) :
    (restrictedCoefficientCutoff nu hU omega L).toFun x = nu • (1 : Mat d) := by
  have hshell : ∀ n : ℕ, (restrictReg U hU (shellReg omega n)).toFun x = 0 := by
    intro n
    rw [restrictReg_apply, Set.indicator_of_notMem hx]
  simp only [restrictedCoefficientCutoff, RegCoeffField.add_apply,
    RegCoeffField.finset_sum_apply, RegCoeffField.constRegCoeffField_apply, hshell,
    Finset.sum_const_zero, add_zero]

/-! ## Admissibility at every sample -/

private theorem symmPart_smul_one (nu : ℝ) :
    symmPart (nu • (1 : Mat d)) = nu • (1 : Mat d) := by
  ext i k
  simp only [symmPart, Matrix.smul_apply, smul_eq_mul]
  by_cases hik : i = k
  · subst hik
    simp only [Matrix.one_apply_eq]
    ring
  · have hki : k ≠ i := Ne.symm hik
    simp only [Matrix.one_apply_ne hik, Matrix.one_apply_ne hki]
    ring

/-- **The symmetric part of the restricted cutoff is `ν Id`.** On `U` this is
the pointwise identity `symmPart_coefficientCutoff`; off `U` the field is the
constant `ν Id` itself. -/
theorem symmPart_restrictedCoefficientCutoff (nu : ℝ) {U : Set (Vec d)}
    (hU : MeasurableSet U) (omega : ShellSeq d) (L : ℕ) (x : Vec d) :
    symmPart ((restrictedCoefficientCutoff nu hU omega L).toFun x) = nu • (1 : Mat d) := by
  by_cases hx : x ∈ U
  · rw [restrictedCoefficientCutoff_eq_of_mem nu hU omega L hx]
    exact symmPart_coefficientCutoff nu omega L x
  · rw [restrictedCoefficientCutoff_eq_of_notMem nu hU omega L hx]
    exact symmPart_smul_one nu

/-- The restricted cutoff is bounded on every triadic cube, with a
sample-dependent constant: on `U` it is the cutoff, which is bounded by
continuity, and off `U` it is the constant `ν Id`. -/
theorem exists_entryBound_restrictedCoefficientCutoff (nu : ℝ) {U : Set (Vec d)}
    (hU : MeasurableSet U) (omega : ShellSeq d) (L : ℕ) (Q : TriadicCube d) :
    ∃ C : ℝ, ∀ x ∈ cubeSet Q, ∀ i j : Fin d,
      |(restrictedCoefficientCutoff nu hU omega L).toFun x i j| ≤ C := by
  obtain ⟨C, hC⟩ := exists_entryBound_coefficientCutoff nu omega L Q
  refine ⟨max C |nu|, fun x hx i j ↦ ?_⟩
  by_cases hxU : x ∈ U
  · rw [restrictedCoefficientCutoff_eq_of_mem nu hU omega L hxU]
    exact le_trans (hC x hx i j) (le_max_left _ _)
  · rw [restrictedCoefficientCutoff_eq_of_notMem nu hU omega L hxU]
    refine le_trans ?_ (le_max_right C |nu|)
    have hone : |(1 : Mat d) i j| ≤ 1 := by
      by_cases hij : i = j
      · subst hij
        simp only [Matrix.one_apply_eq, abs_one, le_refl]
      · simp only [Matrix.one_apply_ne hij, abs_zero]
        norm_num
    calc |(nu • (1 : Mat d)) i j| = |nu| * |(1 : Mat d) i j| := by
          rw [Matrix.smul_apply, smul_eq_mul, abs_mul]
      _ ≤ |nu| * 1 := mul_le_mul_of_nonneg_left hone (abs_nonneg nu)
      _ = |nu| := mul_one _

/-- **The restricted cutoff is admissible at every sample.** Its symmetric part
is the constant `ν Id` and its entries are bounded on every triadic cube, so the
argument of `aeLocallyUniformlyEllipticField_coefficientCutoff` applies
verbatim. -/
theorem aeLocallyUniformlyEllipticField_restrictedCoefficientCutoff {nu : ℝ}
    (hnu : 0 < nu) {U : Set (Vec d)} (hU : MeasurableSet U) (omega : ShellSeq d)
    (L : ℕ) :
    Book.Ch04.AELocallyUniformlyEllipticField (restrictedCoefficientCutoff nu hU omega L) := by
  classical
  intro Q
  obtain ⟨C, hC⟩ := exists_entryBound_restrictedCoefficientCutoff nu hU omega L Q
  refine ⟨nu, ((d : ℝ) * (d : ℝ) * C ^ 2 + nu ^ 2) / nu, hnu, ?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hnu, ← pow_two]
    linarith only [show (0 : ℝ) ≤ (d : ℝ) * (d : ℝ) * C ^ 2 by positivity]
  · exact measurableSet_openCubeSet Q
  · intro i j
    have hEq : (fun x : Vec d ↦
        restrictCoeffField (openCubeSet Q)
          (restrictedCoefficientCutoff nu hU omega L).toFun x i j) =
        fun x : Vec d ↦ if x ∈ openCubeSet Q
          then (restrictedCoefficientCutoff nu hU omega L).toFun x i j else 0 := by
      funext x
      by_cases hx : x ∈ openCubeSet Q <;> simp [restrictCoeffField, hx]
    rw [hEq]
    exact (((restrictedCoefficientCutoff nu hU omega L).entry_measurable i j).ite
      (measurableSet_openCubeSet Q) measurable_const).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
    exact isEllipticMatrix_of_symmPart_eq_smul_one hnu
      (symmPart_restrictedCoefficientCutoff nu hU omega L x)
      (hC x (openCubeSet_subset_cubeSet Q hx))

/-! ## Measurability for the joined restriction lane -/

/-- The shell-`n` restriction lane is exactly the comap of the `n`-th restricted
shell: this is the definition of `ShellField.shellRestrictionSigma`, read on the
sequence carrier. -/
theorem shellLane_shellRestrictionSigma_eq_comap {U : Set (Vec d)}
    (hU : MeasurableSet U) (n : ℕ) :
    shellLane n (ShellField.shellRestrictionSigma U hU) =
      MeasurableSpace.comap
        (fun omega : ShellSeq d ↦ restrictReg U hU (shellReg omega n)) inferInstance := by
  rw [shellLane, ShellField.shellRestrictionSigma, MeasurableSpace.comap_comp]
  rfl

/-- The `n`-th restricted shell is an observable of the shell-`n` restriction
lane. -/
theorem measurable_shellLane_restrictReg_shellReg {U : Set (Vec d)}
    (hU : MeasurableSet U) (n : ℕ) :
    @Measurable (ShellSeq d) (RegCoeffField d)
      (shellLane n (ShellField.shellRestrictionSigma U hU)) inferInstance
      (fun omega : ShellSeq d ↦ restrictReg U hU (shellReg omega n)) :=
  Measurable.of_comap_le (le_of_eq (shellLane_shellRestrictionSigma_eq_comap hU n).symm)

/-- **The restricted cutoff is an observable of the joined restriction lane of
`U`.** It is a finite sum of restricted shells of index at most `L`, and each of
them lives in one shell lane below the cutoff scale. -/
theorem measurable_blockLane_restrictedCoefficientCutoff (nu : ℝ) {U : Set (Vec d)}
    (hU : MeasurableSet U) {ell L : ℕ} (hL : L ≤ ell) :
    @Measurable (ShellSeq d) (RegCoeffField d)
      (blockLane ell (ShellField.shellRestrictionSigma U hU)) inferInstance
      (fun omega : ShellSeq d ↦ restrictedCoefficientCutoff nu hU omega L) := by
  refine Measurable.add measurable_const ?_
  refine Finset.measurable_sum _ fun n hn ↦ ?_
  refine (measurable_shellLane_restrictReg_shellReg hU n).mono ?_ le_rfl
  exact shellLane_le_blockLane
    (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)) hL) _

/-! ## The coarse block matrix does not see the change -/

/-- **The coarse block matrix on a subset of the observation set is unchanged by
the restriction.**  The two fields agree on `V`, and `Mu V P a` is a volume
average over `V` of a pointwise density in `a`. -/
theorem coarseBlockMatrix_restrictedCoefficientCutoff_eq (nu : ℝ) {U V : Set (Vec d)}
    (hU : MeasurableSet U) (hV : MeasurableSet V) (hVU : V ⊆ U)
    (omega : ShellSeq d) (L : ℕ) :
    coarseBlockMatrix V (restrictedCoefficientCutoff nu hU omega L).toFun =
      coarseBlockMatrix V (coefficientCutoff nu omega L).toFun := by
  refine coarseBlockMatrix_congr_of_ae_eq ?_
  filter_upwards [MeasureTheory.ae_restrict_mem hV] with x hx
  exact restrictedCoefficientCutoff_eq_of_mem nu hU omega L (hVU hx)

end

end SuperdiffusionCLT.Section3.Terms
