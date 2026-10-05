/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.ConcFinalItems
public import SuperdiffusionCLT.Section3.Terms.CoarseBlockLocality
public import SuperdiffusionCLT.Section3.Terms.ConcentrationMean
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1ConcDepthC
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1InputsF
public import SuperdiffusionCLT.Section3.Terms.SublatticeCardinality

/-!
# Term 1's lane measurability, and the lane variant

The per-subcollection independence rule of the concentration step is a statement about one
family of subcubes `{ X_z }_{z ∈ 3^ℓ ℤ^d ∩ cu_m}`, blocks of the pairing scale `ℓ`, broken
into subcollections.  The lane measurability of the observable on such a block `B` is the
statement that it depends on the coefficient only inside `B`.  It is proved here on the printed
range `j + ℓ ≤ m` of depths, **unconditionally**.

## Main results

* `HlaneConcOn`: the lane binder narrowed to the printed range `j + ℓ ≤ m`, and
  `hlaneConcOn_holds`, that it holds with no hypotheses.
* `measurable_blockLane_concDepthField_subcollection_of_add_le`: the narrowed
  binder, no residual hypotheses.  This is the "variant at block scale `ℓ`,
  gluing scale `n`" of the lane measurability.
* The route is the *variational locality* of the observable.  On a scale-`ℓ`
  block `B` the glued field is the maximizer of each aligned scale-`n` sub-block
  `z ⊆ B`, so the block average is the `descendantsAverage` of the single-block
  flux pairings (`volumeAverageVec_fluxPairing_glued_eq_descendantsAverage_maximizer`),
  and each single-block pairing is the restricted coarse-matrix expression
  `F − κ(z)^t s_*(z)^{-1} F` (`maximizerFluxPairing_eq_restrictedCoarseMatrix`).
  Since `z ⊆ B`, the cutoff restricted to `cubeSet B` agrees with the cutoff on
  `z`, so the coarse matrices are those of the *restricted* cutoff
  (`sigmaStarInvCoarse_restrictedCoefficientCutoff_eq_of_subset`,
  `kappaCoarse_restrictedCoefficientCutoff_eq_of_subset`), which is an observable
  of `blockLane ℓ (shellRestrictionSigma (cubeSet B))`
  (`measurable_blockLane_restrictedCoefficientCutoff`) and therefore so is the
  whole expression (the entry engines `measurable_kappaCoarse_apply`,
  `measurable_sigmaStarInvCoarse_apply`).  In other words: the observable on a
  scale-`ℓ` block depends on the coefficient **only inside that block** — the
  printed locality step, proved rather than assumed.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open Homogenization
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.CoarseGraining
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The lane variant: the restriction is read on the enclosing block

The assembly's blocks `B` are scale-`ℓ` cubes, while the observable is glued at
scale `S.n ≤ S.ℓ`.  The two restriction-invariance lemmas below are the
`U ⊇ V` generalization of the `U = V` form in
`RHSTerm1ConcDepthC.lean`: the coarse matrices on a scale-`n` sub-block
`z ⊆ B` of the cutoff and of the cutoff restricted to `B` agree, because the two
fields agree on `z`. -/

section LaneVariant

/-- **The coarse matrix `s_*^{-1}(z)` of the restriction to an enclosing
observation set is that of the cutoff.**  The two fields agree on `cubeSet z`,
and the lower-right block of the coarse block matrix on `cubeSet z` sees only
those values. -/
theorem sigmaStarInvCoarse_restrictedCoefficientCutoff_eq_of_subset [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (omega : ShellSeq d) {ell : ℕ} {B z : TriadicCube d}
    (hzB : cubeSet z ⊆ cubeSet B) :
    sigmaStarInvCoarse (openCubeSet z)
        (restrictedCoefficientCutoff nu (measurableSet_cubeSet B) omega ell).toFun =
      sigmaStarInvCoarse (openCubeSet z) (coefficientCutoff nu omega ell).toFun := by
  rw [← coarseBlockMatrix_cubeSet_lowerRight_eq
        (aeLocallyUniformlyEllipticField_restrictedCoefficientCutoff
          hnu (measurableSet_cubeSet B) omega ell) z,
    ← coarseBlockMatrix_cubeSet_lowerRight_eq
        (aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega ell) z,
    coarseBlockMatrix_restrictedCoefficientCutoff_eq nu (measurableSet_cubeSet B)
      (measurableSet_cubeSet z) hzB omega ell]

/-- **The coarse matrix `κ(z)` of the restriction to an enclosing observation
set is that of the cutoff**: `κ = s_* (− (lower-left block))`, and both `s_*` and
the lower-left block are functions of the coarse block matrix on `cubeSet z`. -/
theorem kappaCoarse_restrictedCoefficientCutoff_eq_of_subset [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (omega : ShellSeq d) {ell : ℕ} {B z : TriadicCube d}
    (hzB : cubeSet z ⊆ cubeSet B) :
    kappaCoarse (openCubeSet z)
        (restrictedCoefficientCutoff nu (measurableSet_cubeSet B) omega ell).toFun =
      kappaCoarse (openCubeSet z) (coefficientCutoff nu omega ell).toFun := by
  have hσ : sigmaStarCoarse (openCubeSet z)
        (restrictedCoefficientCutoff nu (measurableSet_cubeSet B) omega ell).toFun =
      sigmaStarCoarse (openCubeSet z) (coefficientCutoff nu omega ell).toFun := by
    rw [sigmaStarCoarse, sigmaStarCoarse,
      sigmaStarInvCoarse_restrictedCoefficientCutoff_eq_of_subset hnu omega hzB]
  rw [kappaCoarse_eq_sigmaStarCoarse_mul_neg_lowerLeft
        (aeLocallyUniformlyEllipticField_restrictedCoefficientCutoff
          hnu (measurableSet_cubeSet B) omega ell) z,
    kappaCoarse_eq_sigmaStarCoarse_mul_neg_lowerLeft
        (aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega ell) z,
    hσ, coarseBlockMatrix_restrictedCoefficientCutoff_eq nu (measurableSet_cubeSet B)
      (measurableSet_cubeSet z) hzB omega ell]

/-- **The single-block flux pairing as a restricted coarse-matrix expression.**
For a scale-`n` block `z` contained in the scale-`ℓ` block `B`, the flux pairing
of the cube maximizer of `z` is `F − κ(z)^t s_*(z)^{-1} F` computed from the
cutoff *restricted to `B`*: the maximizer of `z` sees the coefficient only on
`z ⊆ B`. -/
theorem maximizerFluxPairing_eq_restrictedCoarseMatrix [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (omega : ShellSeq d) {ell : ℕ} (F : Vec d) (i : Fin d) {B z : TriadicCube d}
    (hzB : cubeSet z ⊆ cubeSet B) :
    maximizerFluxPairing hnu ell F i omega z =
      (F - matVecMul (matTranspose (kappaCoarse (openCubeSet z)
            (restrictedCoefficientCutoff nu (measurableSet_cubeSet B) omega ell).toFun))
          (matVecMul (sigmaStarInvCoarse (openCubeSet z)
            (restrictedCoefficientCutoff nu (measurableSet_cubeSet B) omega ell).toFun) F)) i := by
  have hpair : maximizerFluxPairing hnu ell F i omega z =
      volumeAverageVec (openCubeSet z) (fun x => matVecMul
        ((coefficientCutoff nu omega ell).toCoeffField x)
        (cubeMaximizerGradient hnu omega ell F z x)) i := rfl
  rw [hpair, volumeAverageVec_cubeMaximizerFlux hnu omega ell F z]
  simp only [RegCoeffField.toCoeffField]
  rw [← kappaCoarse_restrictedCoefficientCutoff_eq_of_subset hnu omega hzB,
    ← sigmaStarInvCoarse_restrictedCoefficientCutoff_eq_of_subset hnu omega hzB]

/-- The restricted coarse-matrix flux expression is an observable of the joined
restriction lane of the observation set.  This is the common core of
`measurable_blockLane_maximizerFluxPairing` and of the lane measurability of the flux block
observable. -/
private theorem measurable_blockLane_coarseFluxExpression [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {ell : ℕ} (F : Vec d) (i : Fin d) {U : Set (Vec d)} (hU : MeasurableSet U)
    (z : TriadicCube d) :
    @Measurable (ShellSeq d) ℝ
      (SuperdiffusionCLT.Section3.HighContrast.blockLane ell
        (ShellField.shellRestrictionSigma U hU)) inferInstance
      (fun omega : ShellSeq d =>
        (F - matVecMul (matTranspose (kappaCoarse (openCubeSet z)
              (restrictedCoefficientCutoff nu hU omega ell).toFun))
            (matVecMul (sigmaStarInvCoarse (openCubeSet z)
              (restrictedCoefficientCutoff nu hU omega ell).toFun) F)) i) := by
  have hκ : ∀ p q : Fin d, @Measurable (ShellSeq d) ℝ
      (SuperdiffusionCLT.Section3.HighContrast.blockLane ell
        (ShellField.shellRestrictionSigma U hU)) inferInstance
      (fun omega : ShellSeq d => kappaCoarse (openCubeSet z)
        (restrictedCoefficientCutoff nu hU omega ell).toFun p q) :=
    fun p q => @measurable_kappaCoarse_apply d _
      (ShellSeq d)
      (SuperdiffusionCLT.Section3.HighContrast.blockLane ell
        (ShellField.shellRestrictionSigma U hU))
      (fun omega : ShellSeq d => restrictedCoefficientCutoff nu hU omega ell)
      (measurable_blockLane_restrictedCoefficientCutoff nu hU (le_refl ell))
      (fun omega => aeLocallyUniformlyEllipticField_restrictedCoefficientCutoff hnu hU omega ell)
      z p q
  have hσ : ∀ p q : Fin d, @Measurable (ShellSeq d) ℝ
      (SuperdiffusionCLT.Section3.HighContrast.blockLane ell
        (ShellField.shellRestrictionSigma U hU)) inferInstance
      (fun omega : ShellSeq d => sigmaStarInvCoarse (openCubeSet z)
        (restrictedCoefficientCutoff nu hU omega ell).toFun p q) :=
    fun p q => @measurable_sigmaStarInvCoarse_apply d _
      (ShellSeq d)
      (SuperdiffusionCLT.Section3.HighContrast.blockLane ell
        (ShellField.shellRestrictionSigma U hU))
      (fun omega : ShellSeq d => restrictedCoefficientCutoff nu hU omega ell)
      (measurable_blockLane_restrictedCoefficientCutoff nu hU (le_refl ell))
      (fun omega => aeLocallyUniformlyEllipticField_restrictedCoefficientCutoff hnu hU omega ell)
      z p q
  refine Measurable.sub measurable_const ?_
  have hfun : (fun omega : ShellSeq d => matVecMul (matTranspose
        (kappaCoarse (openCubeSet z) (restrictedCoefficientCutoff nu hU omega ell).toFun))
        (matVecMul (sigmaStarInvCoarse (openCubeSet z)
          (restrictedCoefficientCutoff nu hU omega ell).toFun) F) i) =
      fun omega : ShellSeq d => ∑ j : Fin d,
        kappaCoarse (openCubeSet z) (restrictedCoefficientCutoff nu hU omega ell).toFun j i *
          ∑ k : Fin d, sigmaStarInvCoarse (openCubeSet z)
            (restrictedCoefficientCutoff nu hU omega ell).toFun j k * F k := by
    funext omega
    simp only [matVecMul, matTranspose, Matrix.transpose_apply]
  rw [hfun]
  refine Finset.measurable_sum _ fun j _ => ?_
  refine Measurable.mul (hκ j i) ?_
  exact Finset.measurable_sum _ fun k _ => (hσ j k).mul_const (F k)

/-- **The lane measurability of a single-block flux pairing, in the lane of any
enclosing scale-`ℓ` block.**  The pairing of the maximizer of the scale-`n` block
`z` is an observable of `blockLane ℓ (shellRestrictionSigma (cubeSet B))`: it is
the restricted coarse-matrix expression of
`maximizerFluxPairing_eq_restrictedCoarseMatrix`. -/
theorem measurable_blockLane_maximizerFluxPairing [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {ell : ℕ} (F : Vec d) (i : Fin d) {B z : TriadicCube d} (hzB : cubeSet z ⊆ cubeSet B) :
    @Measurable (ShellSeq d) ℝ
      (SuperdiffusionCLT.Section3.HighContrast.blockLane ell
        (ShellField.shellRestrictionSigma (cubeSet B) (measurableSet_cubeSet B)))
      inferInstance (fun omega : ShellSeq d => maximizerFluxPairing hnu ell F i omega z) := by
  have hEq : (fun omega : ShellSeq d => maximizerFluxPairing hnu ell F i omega z) =
      fun omega : ShellSeq d =>
        (F - matVecMul (matTranspose (kappaCoarse (openCubeSet z)
              (restrictedCoefficientCutoff nu (measurableSet_cubeSet B) omega ell).toFun))
            (matVecMul (sigmaStarInvCoarse (openCubeSet z)
              (restrictedCoefficientCutoff nu (measurableSet_cubeSet B) omega ell).toFun) F)) i := by
    funext omega
    exact maximizerFluxPairing_eq_restrictedCoarseMatrix hnu omega F i hzB
  rw [hEq]
  exact measurable_blockLane_coarseFluxExpression hnu F i (measurableSet_cubeSet B) z

/-- **The lane measurability of the glued block pairing at block scale `ℓ` and
gluing scale `n`.**  On an aligned scale-`ℓ` block `B` of `cu_m` with `n ≤ ℓ ≤ m`,
the glued pairing is the `descendantsAverage` over the aligned scale-`n`
sub-blocks `z ⊆ B` of the single-block pairings, each of which is an observable of
the lane of `B`; the average is measurable.  This is the "variant at block scale
`ℓ`, gluing scale `n`" required by the assembly, for a block that
is not also the gluing block. -/
theorem measurable_blockLane_gluedFluxPairing_of_mem [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {ell n m : ℕ} (hnell : n ≤ ell) (hellm : ell ≤ m) (F : Vec d) (i : Fin d)
    {B : TriadicCube d} (hB : B ∈ largeCubeSubcubes d ell m) :
    @Measurable (ShellSeq d) ℝ
      (SuperdiffusionCLT.Section3.HighContrast.blockLane ell
        (ShellField.shellRestrictionSigma (cubeSet B) (measurableSet_cubeSet B)))
      inferInstance (fun omega : ShellSeq d => gluedFluxPairing hnu ell n m F i omega B) := by
  have hdesc : B ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - ell) := hB
  have hEq : (fun omega : ShellSeq d => gluedFluxPairing hnu ell n m F i omega B) =
      fun omega : ShellSeq d => descendantsAverage B (ell - n)
        (fun z => maximizerFluxPairing hnu ell F i omega z) :=
    funext fun omega => volumeAverageVec_fluxPairing_glued_eq_descendantsAverage_maximizer
      hnu hnell hellm F omega hdesc i
  rw [hEq]
  simp only [descendantsAverage]
  refine Measurable.const_mul ?_ _
  exact Finset.measurable_sum _ fun z hz =>
    measurable_blockLane_maximizerFluxPairing hnu F i
      (cubeSet_subset_of_mem_descendantsAtDepth hz)

/-- **The assembly's lane binder at the printed range, proved unconditionally.**
For every depth `j` with `j + ℓ ≤ m` — exactly the range in which the blocks
`B ∈ subcollectionAtDepth R (m - j - ℓ) c` are the scale-`ℓ` blocks of the
printed rule — and every printed class `c ∈ shellColorSet R (m - j - ℓ)` and
member `B`, the coordinate cube average of the depth observable is an observable
of the joined restriction lane of `B`.  No residual hypothesis. -/
theorem measurable_blockLane_concDepthField_subcollection_of_add_le [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) (e : Vec d)
    {j : ℕ} {R : TriadicCube d} (hR : R ∈ descendantsAtDepth (originCube d (S.m : ℤ)) j)
    (hjell : j + S.ell ≤ S.m)
    {c : ShellField.ShellCubeColor d} (_hc : c ∈ shellColorSet R (S.m - j - S.ell))
    {i : Fin d} {B : TriadicCube d} (hB : B ∈ subcollectionAtDepth R (S.m - j - S.ell) c) :
    @Measurable (ShellSeq d) ℝ
      (SuperdiffusionCLT.Section3.HighContrast.blockLane S.ell
        (ShellField.shellRestrictionSigma (cubeSet B) (measurableSet_cubeSet B)))
      inferInstance
      (fun omega : ShellSeq d => volumeAverage (cubeSet B)
        (fun x => concDepthField hnu P S e omega x i)) := by
  have hBdesc : B ∈ descendantsAtDepth R (S.m - j - S.ell) := (mem_subcollectionAtDepth.mp hB).1
  have hBmem : B ∈ largeCubeSubcubes d S.ell S.m := by
    rw [largeCubeSubcubes_eq_descendantsAtDepth]
    have h := mem_descendantsAtDepth_trans hR hBdesc
    rwa [show j + (S.m - j - S.ell) = S.m - S.ell from by omega] at h
  have hnℓ : S.n ≤ S.ell := by have := S.n_add_a; omega
  have hℓm : S.ell ≤ S.m := by have := S.ell_add_a; have := S.ellPrime_add_h; omega
  have hEq : (fun omega : ShellSeq d => volumeAverage (cubeSet B)
        (fun x => concDepthField hnu P S e omega x i)) =
      fun omega : ShellSeq d => fluxBlockObservable hnu P S.ell S.n S.m
        (fluxSlot nu S.LPrime P S.n e) i B omega :=
    funext fun omega =>
      volumeAverage_coord_concDepthField_eq_fluxBlockObservable hnu P S e omega i B
  rw [hEq]
  have hEq2 : (fun omega : ShellSeq d => fluxBlockObservable hnu P S.ell S.n S.m
        (fluxSlot nu S.LPrime P S.n e) i B omega) =
      fun omega : ShellSeq d => gluedFluxPairing hnu S.ell S.n S.m
        (fluxSlot nu S.LPrime P S.n e) i omega B -
        qVector hnu P S.ell S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e) i :=
    funext fun omega => fluxBlockObservable_eq_gluedFluxPairing_sub hnu P S.ell S.n S.m
      (fluxSlot nu S.LPrime P S.n e) i B omega
  rw [hEq2]
  exact (measurable_blockLane_gluedFluxPairing_of_mem hnu hnℓ hℓm
    (fluxSlot nu S.LPrime P S.n e) i hBmem).sub measurable_const

end LaneVariant

section PrintedRange

end PrintedRange

/-! ## The two shapes of the lane binder

The lane binder quantifies over every depth `j` and every descendant `R`; its excess
instances (`m < j + ℓ`) are a strengthening of the printed rule.  `HlaneConcOn` narrows the
quantifier to the printed range `j + ℓ ≤ m`; that is the shape proved above. -/

/-- **The assembly's lane binder narrowed to the printed range** `j + ℓ ≤ m`. -/
def HlaneConcOn [NeZero d] {nu : ℝ} (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d))
    (S : ScaleSelection) (e : Vec d) : Prop :=
  ∀ j : ℕ, ∀ R ∈ descendantsAtDepth (originCube d (S.m : ℤ)) j, j + S.ell ≤ S.m →
    ∀ c ∈ shellColorSet R (S.m - j - S.ell), ∀ i : Fin d,
    ∀ B ∈ subcollectionAtDepth R (S.m - j - S.ell) c,
    @Measurable (ShellSeq d) ℝ
      (SuperdiffusionCLT.Section3.HighContrast.blockLane S.ell
        (ShellField.shellRestrictionSigma (cubeSet B) (measurableSet_cubeSet B)))
      inferInstance
      (fun omega : ShellSeq d => volumeAverage (cubeSet B)
        (fun x => concDepthField hnu P S e omega x i))

/-- **The narrowed lane binder holds, with no hypotheses.**  This is the exact
shape the assembly consumes on its positive branch, and it is a theorem: the
lane slot of the bundle is discharged. -/
theorem hlaneConcOn_holds [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) (e : Vec d) :
    HlaneConcOn hnu P S e :=
  fun _ _ hR hjell _ hc _ _ hB =>
    measurable_blockLane_concDepthField_subcollection_of_add_le hnu P S e hR hjell hc hB

end

end SuperdiffusionCLT.Section3.Terms
