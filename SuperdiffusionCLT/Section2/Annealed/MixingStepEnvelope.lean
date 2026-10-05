/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Book.Ch04.Theorems.Concentration
public import SuperdiffusionCLT.Probability.OrliczInterpolationMin
public import SuperdiffusionCLT.Section2.Annealed.CutoffRealizationPackage
public import SuperdiffusionCLT.Section2.Localization.CoarseCentering
public import SuperdiffusionCLT.Section2.Localization.LoewnerMinAlgebra
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementCubeMomentLocality
public import SuperdiffusionCLT.Section3.Setup.CrudeBounds
public import SuperdiffusionCLT.Section3.Terms.CoarseBlockLocalityB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3Inputs

/-!
# Step E of the minscale proof: the envelope of the centred descendant observables

Step E of the printed proof of the main statement
`sigmaStarInv_mixing_minscale` (the printed lemma `l.mixing.minscale` of the paper) partitions
the `3^{d (n - h)}` depth-`(n - h)` descendants of `cu_n` into sublattices and applies the
centered `Gamma_2` concentration rule to the sublattice averages of the translated
starred-inverse observables.  This module supplies the per-variable inputs of that step.

* the entry envelope: every entry of `s^-1_{L,*}(Q)` is a.s. bounded by `nu^-1`
  (the crude ellipticity bound read entrywise), so the centred entry observable
  `s^-1_{L,*}(Q) i j - shom^-1_{L,*}(cu_m) i j` is `O_{Gamma_2}(2 nu^-1)`;
* the centring: each such observable has expectation `0`, by the stationarity
  centering of the descendant family.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Annealed

open Homogenization MeasureTheory
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.CoarseGraining
open SuperdiffusionCLT.Section2.Localization
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section3.Terms

noncomputable section

variable {d : ℕ}

/-! ## The entrywise reading of the crude ellipticity bound -/

/-- **Every entry of `s^-1_{L,*}(Q)` is bounded by `nu^-1`**: the crude
ellipticity bound `s^-1_{L,*}(Q) <= nu^-1 Id` of the sentence before
`e.v.ky.energy`, read entrywise through the symmetric
positive-semidefinite entry inequality. -/
private theorem abs_entry_sigmaStarInvCoarse_cubeSet_coefficientCutoff_le [NeZero d]
    {nu : ℝ} (hnu : 0 < nu) (omega : ShellSeq d) (L : ℕ) (Q : TriadicCube d)
    (i j : Fin d) :
    |sigmaStarInvCoarse (cubeSet Q)
      (coefficientCutoff nu omega L).toCoeffField i j| ≤ nu⁻¹ := by
  have hsymm : (sigmaStarInvCoarse (cubeSet Q)
      (coefficientCutoff nu omega L).toCoeffField).IsSymm := by
    rw [SuperdiffusionCLT.Section3.Terms.sigmaStarInvCoarse_cubeSet_eq_openCubeSet]
    have h := Book.Ch02.sigmaStarInvCoarse_isSymm (Book.Ch02.cubeDomain Q)
      ((Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
        (coefficientCutoff nu omega L)
        (aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega L)).coeffOn Q)
    rw [← sigmaStarInvCoarse_toCoeffField,
      Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField_coeffOn_toCoeffField,
      Book.Ch02.cubeDomain_coe] at h
    exact h
  have hpsd := SuperdiffusionCLT.Section3.Terms.posSemidef_sigmaStarInvCoarse_cutoffCube
    hnu L omega Q
  have hLoew : MatLoewnerLE (sigmaStarInvCoarse (cubeSet Q)
      (coefficientCutoff nu omega L).toCoeffField) (nu⁻¹ • (1 : Mat d)) := by
    rw [SuperdiffusionCLT.Section3.Terms.sigmaStarInvCoarse_cubeSet_eq_openCubeSet]
    show MatLoewnerLE (sigmaStarInvCoarse (openCubeSet Q)
      (coefficientCutoff nu omega L).toFun) (nu⁻¹ • (1 : Mat d))
    exact matLoewnerLE_sigmaStarInvCoarse_cutoffCube hnu omega L Q
  have hpos : ∀ x : Vec d, 0 ≤ vecDot x (matVecMul (sigmaStarInvCoarse (cubeSet Q)
      (coefficientCutoff nu omega L).toCoeffField) x) := by
    intro x
    simpa only [dotProduct, Matrix.mulVec, vecDot, matVecMul, RCLike.star_def,
      conj_trivial, star_trivial] using hpsd.dotProduct_mulVec_nonneg x
  have hentry := abs_entry_le_of_isSymm_of_nonneg hsymm hpos i j
  have hdiag : ∀ i : Fin d, (nu⁻¹ • (1 : Mat d)) i i = nu⁻¹ := by
    intro i; simp
  have hi := diag_le_of_matLoewnerLE hLoew i
  have hj := diag_le_of_matLoewnerLE hLoew j
  rw [hdiag i] at hi
  rw [hdiag j] at hj
  linarith only [hentry, hi, hj]

/-- **The annealed entry at an origin cube is bounded by `nu^-1`**: the scalar
form `shom^-1_{L,*}(cu_m) <= nu^-1` of the crude ellipticity bound, transported
through the `J4` scalarization of the annealed block at the origin cube. -/
private theorem abs_sigmaBarStarInv_originCube_entry_le [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (L : ℕ) (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (m : ℕ) (i j : Fin d) :
    |sigmaBarStarInv nu L P (cubeSet (originCube d (m : ℤ))) i j| ≤ nu⁻¹ := by
  have hseq : sigmaBarStarInvScalar nu L P (cubeSet (originCube d (m : ℤ)))
      ≤ nu⁻¹ := sigmaBarStarInvSeq_le_nuInv hnu L hPrefix hJ2 hJ3 hJ4 m
  have hpos : 0 ≤ sigmaBarStarInvScalar nu L P (cubeSet (originCube d (m : ℤ))) :=
    le_of_lt (sigmaBarStarInvSeq_pos hnu L hPrefix hJ2 hJ3 hJ4 m)
  rw [sigmaBarStarInv_originCube_eq_smul_one hnu L hJ4 (m : ℤ)]
  by_cases hij : i = j
  · have h1 : ((sigmaBarStarInvScalar nu L P (cubeSet (originCube d (m : ℤ))) •
        (1 : Mat d)) i j) = sigmaBarStarInvScalar nu L P
          (cubeSet (originCube d (m : ℤ))) := by
      simp [hij]
    rw [h1, abs_of_nonneg hpos]
    exact hseq
  · have h0 : ((sigmaBarStarInvScalar nu L P (cubeSet (originCube d (m : ℤ))) •
        (1 : Mat d)) i j) = (0 : ℝ) := by
      simp [hij]
    rw [h0, abs_zero]
    exact (inv_pos.2 hnu).le

/-! ## The per-variable envelope of the centred descendant observables -/

/-- **The per-variable envelope of the Step-E centred summands.**  For every
triadic cube `Q` and every entry, the centred observable
`s^-1_{L,*}(Q) i j - shom^-1_{L,*}(cu_m) i j` is measurable and
`O_{Gamma_2}(2 nu^-1)`: the crude ellipticity bound gives
`|s^-1_{L,*}(Q) i j| <= nu^-1` a.s. and `|shom^-1_{L,*}(cu_m) i j| <= nu^-1`,
so the centred entry is a.s. bounded by the deterministic `2 nu^-1`.  This is
the per-variable amplitude the sublattice concentration of Step E
consumes, with the printed remark that the rate comes from the concentration
gain and not from the per-variable bound. -/
theorem measurable_isBigO_gammaSigma_entry_sub_sigmaBarStarInv [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (L : ℕ) (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (m : ℕ) (Q : TriadicCube d) (i j : Fin d) :
    Measurable (fun omega : ShellSeq d =>
        sigmaStarInvCoarse (cubeSet Q) (coefficientCutoff nu omega L).toCoeffField i j -
          sigmaBarStarInv nu L P (cubeSet (originCube d (m : ℤ))) i j) ∧
    IsBigO P.toMeasure (gammaSigma 2)
      (fun omega : ShellSeq d =>
        sigmaStarInvCoarse (cubeSet Q) (coefficientCutoff nu omega L).toCoeffField i j -
          sigmaBarStarInv nu L P (cubeSet (originCube d (m : ℤ))) i j)
      (nu⁻¹ + nu⁻¹) := by
  have hq : ∀ omega : ShellSeq d, |sigmaStarInvCoarse (cubeSet Q)
      (coefficientCutoff nu omega L).toCoeffField i j| ≤ nu⁻¹ := fun omega =>
    abs_entry_sigmaStarInvCoarse_cubeSet_coefficientCutoff_le hnu omega L Q i j
  have hbar : |sigmaBarStarInv nu L P (cubeSet (originCube d (m : ℤ))) i j| ≤ nu⁻¹ :=
    abs_sigmaBarStarInv_originCube_entry_le hnu L P hPrefix hJ2 hJ3 hJ4 m i j
  refine ⟨?_, ?_⟩
  · have hEq : (fun omega : ShellSeq d =>
        sigmaStarInvCoarse (cubeSet Q) (coefficientCutoff nu omega L).toCoeffField i j) =
        fun omega : ShellSeq d =>
          sigmaStarInvCoarse (openCubeSet Q) (coefficientCutoff nu omega L).toFun i j := by
      funext omega
      exact congrArg (fun M : Mat d => M i j)
        (SuperdiffusionCLT.Section3.Terms.sigmaStarInvCoarse_cubeSet_eq_openCubeSet
          Q _)
    have hmeas : Measurable (fun omega : ShellSeq d =>
        sigmaStarInvCoarse (cubeSet Q) (coefficientCutoff nu omega L).toCoeffField i j) := by
      rw [hEq]
      exact measurable_sigmaStarInvCoarse_apply (measurable_coefficientCutoff nu L)
        (fun omega => aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega L) Q i j
    exact hmeas.sub measurable_const
  · have hcnu : (0 : ℝ) ≤ nu⁻¹ := (inv_pos.2 hnu).le
    have hX : IsBigO P.toMeasure (gammaSigma 2)
        (fun omega : ShellSeq d =>
          sigmaStarInvCoarse (cubeSet Q) (coefficientCutoff nu omega L).toCoeffField i j)
        nu⁻¹ :=
      (isBigO_gammaSigma_of_abs_le_add_const (c := nu⁻¹) hcnu
        (fun omega => (hq omega).trans (by rw [abs_zero, zero_add]))
        (isBigO_gammaSigma_const_apply (c := 0) le_rfl)).mono_scale
        (by rw [zero_add])
    refine isBigO_gammaSigma_of_abs_le_add_const hcnu ?_ hX
    intro omega
    have hkey := abs_add_le
      (sigmaStarInvCoarse (cubeSet Q) (coefficientCutoff nu omega L).toCoeffField i j)
      (-(sigmaBarStarInv nu L P (cubeSet (originCube d (m : ℤ))) i j))
    rw [abs_neg] at hkey
    exact hkey.trans (by linarith only [hbar])

/-! ## The centring `E = 0` of the Step-E summands -/

/-- **The centring `E = 0` of the Step-E summands.**  For every depth-`(n - h)`
descendant `R` of `cu_n` and every entry, the centred observable
`s^-1_{L,*}(R) i j - shom^-1_{L,*}(cu_h) i j` has expectation `0`: each
translated summand has the same expectation, namely the annealed block at the
centred cube `cu_h` — the stationarity centering of the Step-A average of
`l.mixing.minscale`, proved as
`integral_sigmaStarInvCoarse_descendant_eq_sigmaBarStarInv`. -/
theorem integral_entry_sub_sigmaBarStarInv_descendant [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (L : ℕ) (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P)
    {n h : ℕ} (hhn : h < n) {R : TriadicCube d}
    (hR : R ∈ descendantsAtDepth (originCube d (n : ℤ)) (n - h)) (i j : Fin d) :
    ∫ omega : ShellSeq d, sigmaStarInvCoarse (cubeSet R)
        (coefficientCutoff nu omega L).toCoeffField i j -
        sigmaBarStarInv nu L P (cubeSet (originCube d (h : ℤ))) i j ∂P.toMeasure = 0 := by
  have hEq : ∀ omega : ShellSeq d,
      sigmaStarInvCoarse (cubeSet R) (coefficientCutoff nu omega L).toCoeffField i j =
        sigmaStarInvCoarse (openCubeSet R) (coefficientCutoff nu omega L).toFun i j :=
    fun omega => congrArg (fun M : Mat d => M i j)
      (SuperdiffusionCLT.Section3.Terms.sigmaStarInvCoarse_cubeSet_eq_openCubeSet R _)
  have hint : Integrable (fun omega : ShellSeq d =>
      sigmaStarInvCoarse (cubeSet R) (coefficientCutoff nu omega L).toCoeffField i j)
      P.toMeasure :=
    (integrable_sigmaStarInvCoarse_apply hnu L hPrefix hJ2 hJ3 hJ4 R i j).congr
      (Filter.Eventually.of_forall fun omega ↦ (hEq omega).symm)
  rw [integral_sub hint (integrable_const _),
    integral_sigmaStarInvCoarse_descendant_eq_sigmaBarStarInv hnu L P hPrefix hJ2 hhn R hR i j]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, sub_self]

/-! ## The restriction-lane locality of the cutoff coarse matrix -/

/-- The ambient coarse matrix on a cube, in the Chapter 2 vocabulary of the
canonical triadic coefficient family. -/
private theorem sigmaStarInvCoarse_cubeSet_toCh02 [NeZero d]
    (Q : TriadicCube d) (a : RegCoeffField d)
    (ha : Book.Ch04.AELocallyUniformlyEllipticField a) :
    sigmaStarInvCoarse (cubeSet Q) a.toCoeffField
      = Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain Q)
        ((Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q) := by
  rw [sigmaStarInvCoarse_cubeSet_eq_openCubeSet]
  exact sigmaStarInvCoarse_toCoeffField (Book.Ch02.cubeDomain Q)
    ((Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)

/-- The coarse matrix `s^-1_{L,*}(Q)` does not see the cutoff off the cube: on
any measurable set containing the cube, replacing every shell of the cutoff by
its restriction to that set leaves `s^-1_{L,*}(Q)` unchanged.  This is the
`sigmaStarInvCoarse` twin of `coarseBlockMatrix_restrictedCoefficientCutoff_eq`:
the two fields agree on the cube, and `sigmaStarInvCoarse` is invariant under
a.e. changes of the coefficient representative on the cube
(`Book.Ch02.sigmaStarInvCoarse_eq_ofAEEq`). -/
private theorem sigmaStarInvCoarse_cubeSet_coefficientCutoff_eq_restricted [NeZero d]
    {nu : ℝ} (hnu : 0 < nu) {U : Set (Vec d)} (hU : MeasurableSet U)
    (omega : ShellSeq d) (L : ℕ) (Q : TriadicCube d) (hQU : cubeSet Q ⊆ U) :
    sigmaStarInvCoarse (cubeSet Q) (coefficientCutoff nu omega L).toCoeffField
      = sigmaStarInvCoarse (cubeSet Q)
        (restrictedCoefficientCutoff nu hU omega L).toCoeffField := by
  have hAEq : (coefficientCutoff nu omega L).toFun
      =ᵐ[volumeMeasureOn (openCubeSet Q)] (restrictedCoefficientCutoff nu hU omega L).toFun := by
    filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
    exact (restrictedCoefficientCutoff_eq_of_mem nu hU omega L
      (hQU (openCubeSet_subset_cubeSet Q hx))).symm
  rw [sigmaStarInvCoarse_cubeSet_toCh02 Q _
    (aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega L),
    sigmaStarInvCoarse_cubeSet_toCh02 Q _
      (aeLocallyUniformlyEllipticField_restrictedCoefficientCutoff hnu hU omega L)]
  exact Book.Ch02.sigmaStarInvCoarse_eq_ofAEEq
    (Book.Ch04.coeffOnOfAELocallyUniformlyEllipticField_aeeq_of_ae_eq_on_openCubeSet
      (aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega L)
      (aeLocallyUniformlyEllipticField_restrictedCoefficientCutoff hnu hU omega L) Q hAEq)

/-- **The lane measurability twin for the `σ⁻¹` entries.**  Each entry of
`s^-1_{L,*}(Q)` is an observable of the joined restriction lane of any
measurable set containing the cube, once `L ≤ ell`: the coarse matrix is
unchanged by the restriction (`sigmaStarInvCoarse_cubeSet_coefficientCutoff_eq_restricted`)
and the restricted cutoff is an observable of the lane
(`measurable_blockLane_restrictedCoefficientCutoff`), so the proved
measurability engine applies at the lane. -/
private theorem measurable_blockLane_sigmaStarInvCoarse_entry [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) {U : Set (Vec d)} (hU : MeasurableSet U)
    {ell L : ℕ} (hL : L ≤ ell) (Q : TriadicCube d) (hQU : cubeSet Q ⊆ U)
    (i j : Fin d) :
    @Measurable (ShellSeq d) ℝ
      (Section3.HighContrast.blockLane ell (ShellField.shellRestrictionSigma U hU)) inferInstance
      (fun omega : ShellSeq d ↦ sigmaStarInvCoarse (cubeSet Q)
        (coefficientCutoff nu omega L).toCoeffField i j) := by
  have hmeas : @Measurable (ShellSeq d) ℝ
      (Section3.HighContrast.blockLane ell (ShellField.shellRestrictionSigma U hU)) inferInstance
      (fun omega : ShellSeq d ↦ sigmaStarInvCoarse (cubeSet Q)
        (restrictedCoefficientCutoff nu hU omega L).toCoeffField i j) := by
    have h := @measurable_sigmaStarInvCoarse_apply d inferInstance (ShellSeq d)
      (Section3.HighContrast.blockLane ell (ShellField.shellRestrictionSigma U hU))
      (fun omega : ShellSeq d ↦ restrictedCoefficientCutoff nu hU omega L)
      (measurable_blockLane_restrictedCoefficientCutoff nu hU hL)
      (fun omega ↦ aeLocallyUniformlyEllipticField_restrictedCoefficientCutoff hnu hU omega L)
      Q i j
    have hEq : (fun omega : ShellSeq d ↦ sigmaStarInvCoarse (cubeSet Q)
          (restrictedCoefficientCutoff nu hU omega L).toCoeffField i j)
        = fun omega : ShellSeq d ↦
          sigmaStarInvCoarse (openCubeSet Q)
            (restrictedCoefficientCutoff nu hU omega L).toFun i j := by
      funext omega
      exact congrArg (fun M : Mat d => M i j)
        (sigmaStarInvCoarse_cubeSet_eq_openCubeSet Q _)
    rw [hEq]
    exact h
  have hfun : (fun omega : ShellSeq d ↦ sigmaStarInvCoarse (cubeSet Q)
        (coefficientCutoff nu omega L).toCoeffField i j)
      = fun omega : ShellSeq d ↦ sigmaStarInvCoarse (cubeSet Q)
        (restrictedCoefficientCutoff nu hU omega L).toCoeffField i j := by
    funext omega
    exact congrArg (fun M : Mat d => M i j)
      (sigmaStarInvCoarse_cubeSet_coefficientCutoff_eq_restricted hnu hU omega L Q hQU)
  rw [hfun]
  exact hmeas

/-! ## The sublattice concentration of the Step-E summands -/

/-- **The sublattice concentration of Step E.**  For a nonempty finset `s` of
pairwise shell-separated triadic cubes, all depth-`(n - h)` descendants of
`cu_n`, the finset average of the centred entries of `s^-1_{L,*}(R)` is
measurable and `O_{Gamma_2}` with the CoarseGraining finset-average amplitude

`gammaSigmaIndependentSumConst 2 * (sqrt (s.card) / s.card) * 2 nu^-1`:

* the per-variable envelope and measurability are the first theorem of this
  module (the crude ellipticity bound read entrywise);
* the centring `E = 0` is the second theorem of this module;
* the mutual independence is the restriction-lane independence over the
  pairwise-separated observation cubes, with the lane measurability of the
  `σ⁻¹` entries discharged by the restriction-lane locality of the cutoff
  coarse matrix.

The separation is carried at the lane level `ell >= L`, matching the shape
`iIndepFun_blockDeviation` of the coarse-block twin: the sublattice partition
of the descendant family supplies it. -/
theorem isBigO_gammaSigma_finsetAverage_entry_sub_sigmaBarStarInv [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (L : ℕ) (P : ProbabilityMeasure (ShellSeq d))
    (hJ1 : ShellLawJ1Restriction d P) (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (ell : ℕ) (hL : L ≤ ell)
    {s : Finset (TriadicCube d)} (hs : s.Nonempty)
    (hsep : ∀ R ∈ s, ∀ R' ∈ s, R ≠ R' →
      ShellField.AreShellSeparated ell (cubeSet R) (cubeSet R'))
    {n h : ℕ} (hhn : h < n)
    (hsub : ∀ R ∈ s, R ∈ descendantsAtDepth (originCube d (n : ℤ)) (n - h))
    (i j : Fin d) :
    IsBigO P.toMeasure (gammaSigma 2)
      (fun omega : ShellSeq d => ((s.card : ℝ)⁻¹) * ∑ R ∈ s,
        (sigmaStarInvCoarse (cubeSet R) (coefficientCutoff nu omega L).toCoeffField i j -
          sigmaBarStarInv nu L P (cubeSet (originCube d (h : ℤ))) i j))
      (Book.Ch04.gammaSigmaIndependentSumConst 2 *
        (Real.sqrt (s.card : ℝ) / (s.card : ℝ)) * (nu⁻¹ + nu⁻¹)) := by
  have hIndep : ProbabilityTheory.iIndepFun
      (fun (R : {R : TriadicCube d // R ∈ s}) (omega : ShellSeq d) =>
        sigmaStarInvCoarse (cubeSet (R : TriadicCube d))
          (coefficientCutoff nu omega L).toCoeffField i j -
        sigmaBarStarInv nu L P (cubeSet (originCube d (h : ℤ))) i j)
      P.toMeasure := by
    refine SuperdiffusionCLT.Section2.Estimates.Stream.iIndepFun_of_blockLane_shellRestrictionSigma
      hJ1 hJ2 ell
      (U := fun R : {R : TriadicCube d // R ∈ s} => cubeSet (R : TriadicCube d))
      (fun R => measurableSet_cubeSet (R : TriadicCube d)) ?_ ?_
    · intro R
      exact (measurable_blockLane_sigmaStarInvCoarse_entry hnu
        (measurableSet_cubeSet (R : TriadicCube d)) hL (R : TriadicCube d) subset_rfl i j).sub
        measurable_const
    · intro R R' hne
      exact hsep (R : TriadicCube d) R.2 (R' : TriadicCube d) R'.2
        (fun hcon => hne (Subtype.ext hcon))
  have hmeas : ∀ R : {R : TriadicCube d // R ∈ s}, Measurable (fun omega : ShellSeq d =>
      sigmaStarInvCoarse (cubeSet (R : TriadicCube d))
        (coefficientCutoff nu omega L).toCoeffField i j -
      sigmaBarStarInv nu L P (cubeSet (originCube d (h : ℤ))) i j) := fun R =>
    (measurable_isBigO_gammaSigma_entry_sub_sigmaBarStarInv hnu L P hPrefix hJ2 hJ3 hJ4 h
      (R : TriadicCube d) i j).1
  have hX : ∀ R : {R : TriadicCube d // R ∈ s}, IsBigO P.toMeasure (gammaSigma 2)
      (fun omega : ShellSeq d =>
        sigmaStarInvCoarse (cubeSet (R : TriadicCube d))
          (coefficientCutoff nu omega L).toCoeffField i j -
      sigmaBarStarInv nu L P (cubeSet (originCube d (h : ℤ))) i j)
      (nu⁻¹ + nu⁻¹) := fun R =>
    (measurable_isBigO_gammaSigma_entry_sub_sigmaBarStarInv hnu L P hPrefix hJ2 hJ3 hJ4 h
      (R : TriadicCube d) i j).2
  have hK : (0 : ℝ) < nu⁻¹ + nu⁻¹ := by linarith only [(inv_pos.2 hnu)]
  have hmean : ∀ R : {R : TriadicCube d // R ∈ s}, ∫ omega : ShellSeq d,
      sigmaStarInvCoarse (cubeSet (R : TriadicCube d))
        (coefficientCutoff nu omega L).toCoeffField i j -
      sigmaBarStarInv nu L P (cubeSet (originCube d (h : ℤ))) i j ∂P.toMeasure = 0 :=
    fun R => integral_entry_sub_sigmaBarStarInv_descendant hnu L P hPrefix hJ2 hJ3 hJ4 hhn
      (hsub (R : TriadicCube d) R.2) i j
  have hmain := Book.Ch04.isBigO_gammaSigma_finsetAverage_of_iIndepFun_of_isBigO_of_integral_eq_zero
    (μ := P.toMeasure)
    (X := fun (R : {R : TriadicCube d // R ∈ s}) (omega : ShellSeq d) =>
      sigmaStarInvCoarse (cubeSet (R : TriadicCube d))
        (coefficientCutoff nu omega L).toCoeffField i j -
      sigmaBarStarInv nu L P (cubeSet (originCube d (h : ℤ))) i j)
    (s := s.attach) (σ := 2) (K := nu⁻¹ + nu⁻¹)
    hIndep hmeas hs.attach (by norm_num : (0 : ℝ) < 2) le_rfl hK
      (fun R (_ : R ∈ s.attach) => hX R) (fun R (_ : R ∈ s.attach) => hmean R)
  have hcard : ((s.attach.card : ℝ)) = ((s.card : ℝ)) := by rw [Finset.card_attach]
  have hsum : ∀ omega : ShellSeq d,
      ∑ x ∈ s.attach,
        (fun (R : {R : TriadicCube d // R ∈ s}) (omega : ShellSeq d) =>
          sigmaStarInvCoarse (cubeSet (R : TriadicCube d))
            (coefficientCutoff nu omega L).toCoeffField i j -
          sigmaBarStarInv nu L P (cubeSet (originCube d (h : ℤ))) i j) x omega
      = ∑ R ∈ s,
        (sigmaStarInvCoarse (cubeSet R) (coefficientCutoff nu omega L).toCoeffField i j -
          sigmaBarStarInv nu L P (cubeSet (originCube d (h : ℤ))) i j) := by
    intro omega
    exact Finset.sum_attach (s := s) (f := fun (R : TriadicCube d) =>
      sigmaStarInvCoarse (cubeSet R) (coefficientCutoff nu omega L).toCoeffField i j -
        sigmaBarStarInv nu L P (cubeSet (originCube d (h : ℤ))) i j)
  have hfunEq : (fun omega : ShellSeq d => ((s.card : ℝ)⁻¹) * ∑ x ∈ s.attach,
        (fun (R : {R : TriadicCube d // R ∈ s}) (omega : ShellSeq d) =>
          sigmaStarInvCoarse (cubeSet (R : TriadicCube d))
            (coefficientCutoff nu omega L).toCoeffField i j -
          sigmaBarStarInv nu L P (cubeSet (originCube d (h : ℤ))) i j) x omega)
      = (fun omega : ShellSeq d => ((s.card : ℝ)⁻¹) * ∑ R ∈ s,
        (sigmaStarInvCoarse (cubeSet R) (coefficientCutoff nu omega L).toCoeffField i j -
          sigmaBarStarInv nu L P (cubeSet (originCube d (h : ℤ))) i j)) := by
    funext omega
    exact congrArg (fun t : ℝ => ((s.card : ℝ))⁻¹ * t) (hsum omega)
  have hmain' := hmain
  rw [hcard, hfunEq] at hmain'
  exact hmain'

end

end SuperdiffusionCLT.Section2.Annealed