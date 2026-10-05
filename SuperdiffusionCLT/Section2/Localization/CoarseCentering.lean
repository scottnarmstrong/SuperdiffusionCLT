/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.CoarseGraining.OriginCubeOpenBridge
public import Homogenization.Geometry.TriadicPartition
public import SuperdiffusionCLT.Section2.Annealed.Blocks
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementMoreoverBlockD
public import SuperdiffusionCLT.Section3.Terms.TranslatedBlocks

/-!
# Stationarity centering of the coarse matrices on translated cubes

The stationarity half of Step A of the proof of the statement
`sigmaStarInv_mixing_minscale` (the printed lemma `l.mixing.minscale` of the paper): the
average over the depth-`(n - h)` descendants of `cu_n` in the printed subadditivity
decomposition of Step A is *centred*, and the centring rests on the identity

`E[ s^-1_{L,*}(z + cu) ] = shom^-1_{L,*}(cu)`

for a lattice translate `z + cu = translateCube shift Q` of a triadic cube:
every translated summand has the *same* expectation, namely the annealed block
at the centred cube.

The identity splits into a deterministic half and a probabilistic half.

* The expectation of an entry of `s^-1_{L,*}(Q)` on *any* triadic cube `Q` is
  the annealed entry at the same cube
  (`integral_sigmaStarInvCoarse_cubeSet_eq_sigmaBarStarInv`): this is the
  definition of the annealed block
  (`sigmaBarStarInv_eq_integral_sigmaStarInvCoarse`) transported from the open
  realization, where the Chapter 2 vocabulary and the measurability engine of
  `CoarseGraining` live, to the half-open realization in which
  `l.mixing.minscale` is stated.  It needs no stationarity.
* The annealed block is invariant under a lattice translate of the cube
  (`sigmaBarStarInv_translateCube_eq_originCube`): the coarse matrix on a
  translate is the coarse matrix at the centred cube for the translated shell
  sequence (`sigmaStarInvCoarse_openCubeSet_coefficientCutoff`), and the
  shell-sequence law is invariant under that translation
  (`ShellField.map_translateSequence_eq`, from the prefix and J2 hypotheses),
  moved through the Bochner integral by
  `integral_of_translationCovariant`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open Homogenization
open MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.Terms

noncomputable section

/-! ## The half-open and the open realization of the coarse matrix -/

/-- The half-open and the open realization of a triadic cube give the same
coarse matrix `s^-1_{L,*}`.  Both entry formulas of `sigmaStarInvCoarse` are
values of `ResponseJ` at the two cubes, and those agree by
`responseJ_cubeSet_eq_openCubeSet_of_triadicCube`; no ellipticity or coarse
data is needed.  This is the bridge between the carrier in which
`l.mixing.minscale` is stated (`cubeSet`) and the carrier in which the Chapter 2
positivity and the measurability engine work (`openCubeSet`). -/
private theorem sigmaStarInvCoarse_cubeSet_eq_openCubeSet {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : CoeffField d) :
    sigmaStarInvCoarse (cubeSet Q) a = sigmaStarInvCoarse (openCubeSet Q) a := by
  funext i j
  by_cases h : i = j
  · subst h
    rw [sigmaStarInvCoarse_apply_same, sigmaStarInvCoarse_apply_same,
      responseJ_cubeSet_eq_openCubeSet_of_triadicCube]
  · rw [sigmaStarInvCoarse_apply_of_ne _ _ h, sigmaStarInvCoarse_apply_of_ne _ _ h,
      responseJ_cubeSet_eq_openCubeSet_of_triadicCube,
      responseJ_cubeSet_eq_openCubeSet_of_triadicCube,
      responseJ_cubeSet_eq_openCubeSet_of_triadicCube]

/-! ## The stationarity centering -/

/-- The expectation of an entry of the inverse coarse matrix `s^-1_{L,*}(Q)` of
the infrared cutoff on any triadic cube `Q` is the annealed entry at `Q`.  This
is the half-open realization of `sigmaBarStarInv_eq_integral_sigmaStarInvCoarse`
and needs no stationarity. -/
theorem integral_sigmaStarInvCoarse_cubeSet_eq_sigmaBarStarInv {d : ℕ} [NeZero d]
    {nu : ℝ} (hnu : 0 < nu) (L : ℕ) (P : ProbabilityMeasure (ShellSeq d))
    (Q : TriadicCube d) (i j : Fin d) :
    ∫ omega : ShellSeq d, sigmaStarInvCoarse (cubeSet Q)
        (coefficientCutoff nu omega L).toCoeffField i j ∂P.toMeasure
      = sigmaBarStarInv nu L P (cubeSet Q) i j := by
  rw [sigmaBarStarInv_eq_integral_sigmaStarInvCoarse hnu L P Q i j]
  refine integral_congr_ae (Filter.Eventually.of_forall fun omega ↦ ?_)
  show sigmaStarInvCoarse (cubeSet Q) (coefficientCutoff nu omega L).toCoeffField i j =
    sigmaStarInvCoarse (openCubeSet Q) (coefficientCutoff nu omega L).toFun i j
  rw [sigmaStarInvCoarse_cubeSet_eq_openCubeSet]
  rfl

/-- The annealed inverse coarse matrix is invariant under a lattice translate
of the cube: `shom^-1_{L,*}(z + cu) = shom^-1_{L,*}(cu)` for a translate of the
form `translateCube shift Q`, i.e. `z = 3^Q.scale * shift`.  This is the
stationarity centering `integral_sigmaStarInvCoarse_translateCube_eq_sigmaBarStarInv`
of the plan's cross-cutting section, in annealed form. -/
theorem sigmaBarStarInv_translateCube_eq_originCube {d : ℕ} [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (L : ℕ) (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (shift : Fin d → ℤ) (Q : TriadicCube d) (i j : Fin d) :
    sigmaBarStarInv nu L P (cubeSet (translateCube shift Q)) i j
      = sigmaBarStarInv nu L P (cubeSet Q) i j := by
  have hmeas : AEStronglyMeasurable (fun omega : ShellSeq d ↦
      sigmaStarInvCoarse (openCubeSet (originCube d Q.scale))
        (coefficientCutoff nu omega L).toFun i j) P.toMeasure :=
    (measurable_sigmaStarInvCoarse_apply
      (measurable_coefficientCutoff (d := d) nu L)
      (fun omega ↦ aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega L)
      (originCube d Q.scale) i j).aestronglyMeasurable
  have hcovT : ∀ omega : ShellSeq d,
      sigmaStarInvCoarse (openCubeSet (translateCube shift Q))
        (coefficientCutoff nu omega L).toFun i j =
        sigmaStarInvCoarse (openCubeSet (originCube d Q.scale))
          (coefficientCutoff nu
            (ShellField.translateSequence
              (triadicCubeShift (translateCube shift Q)) omega) L).toFun i j :=
    fun omega ↦ congrArg (fun M : Mat d => M i j)
      (sigmaStarInvCoarse_openCubeSet_coefficientCutoff nu L omega (translateCube shift Q))
  have hcovQ : ∀ omega : ShellSeq d,
      sigmaStarInvCoarse (openCubeSet Q)
        (coefficientCutoff nu omega L).toFun i j =
        sigmaStarInvCoarse (openCubeSet (originCube d Q.scale))
          (coefficientCutoff nu
            (ShellField.translateSequence (triadicCubeShift Q) omega) L).toFun i j :=
    fun omega ↦ congrArg (fun M : Mat d => M i j)
      (sigmaStarInvCoarse_openCubeSet_coefficientCutoff nu L omega Q)
  calc sigmaBarStarInv nu L P (cubeSet (translateCube shift Q)) i j
      = ∫ omega : ShellSeq d, sigmaStarInvCoarse (openCubeSet (translateCube shift Q))
          (coefficientCutoff nu omega L).toFun i j ∂P.toMeasure :=
        sigmaBarStarInv_eq_integral_sigmaStarInvCoarse hnu L P (translateCube shift Q) i j
    _ = ∫ omega : ShellSeq d, sigmaStarInvCoarse (openCubeSet (originCube d Q.scale))
          (coefficientCutoff nu omega L).toFun i j ∂P.toMeasure :=
        integral_of_translationCovariant
          (F := fun (omega : ShellSeq d) (R : TriadicCube d) =>
            sigmaStarInvCoarse (openCubeSet R) (coefficientCutoff nu omega L).toFun i j)
          hPrefix hJ2 hcovT hmeas
    _ = ∫ omega : ShellSeq d, sigmaStarInvCoarse (openCubeSet Q)
          (coefficientCutoff nu omega L).toFun i j ∂P.toMeasure :=
        (integral_of_translationCovariant
          (F := fun (omega : ShellSeq d) (R : TriadicCube d) =>
            sigmaStarInvCoarse (openCubeSet R) (coefficientCutoff nu omega L).toFun i j)
          hPrefix hJ2 hcovQ hmeas).symm
    _ = sigmaBarStarInv nu L P (cubeSet Q) i j :=
        (sigmaBarStarInv_eq_integral_sigmaStarInvCoarse hnu L P Q i j).symm

/-- **The stationarity centering of the translated coarse matrix.**  For a
lattice translate `z + cu` of a triadic cube (spelled `translateCube shift Q`),
the expectation of an entry of `s^-1_{L,*}(z + cu)` of the cutoff field is the
annealed entry at the centred cube `cu`:

`E[ s^-1_{L,*}(z + cu) ] = shom^-1_{L,*}(cu)`.

This is the centring of the Step-A average of `l.mixing.minscale`: each translated summand has the
same expectation,
namely the annealed block at `cu_h`. -/
theorem integral_sigmaStarInvCoarse_translateCube_eq_sigmaBarStarInv {d : ℕ} [NeZero d]
    {nu : ℝ} (hnu : 0 < nu) (L : ℕ) (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (shift : Fin d → ℤ) (Q : TriadicCube d) (i j : Fin d) :
    ∫ omega : ShellSeq d,
        sigmaStarInvCoarse (cubeSet (translateCube shift Q))
          (coefficientCutoff nu omega L).toCoeffField i j ∂P.toMeasure
      = sigmaBarStarInv nu L P (cubeSet Q) i j := by
  rw [integral_sigmaStarInvCoarse_cubeSet_eq_sigmaBarStarInv hnu L P _ i j,
    sigmaBarStarInv_translateCube_eq_originCube hnu L P hPrefix hJ2 shift Q i j]

/-! ## The Step-A descendant family: lattice translates of the centred cube -/

/-- The depth-`(n - h)` descendants of the centred cube `cu_n` are its
scale-`h` sub-cube family.  This is the canonicalization of the index set
`3^h ℤ^d ∩ cu_n` of the Step-A average of `l.mixing.minscale`,
from `descendantsAtDepth_originCube_eq`. -/
theorem descendantsAtDepth_originCube_eq_largeCubeSubcubes {d : ℕ} {n h : ℕ} :
    descendantsAtDepth (originCube d (n : ℤ)) (n - h) = largeCubeSubcubes d h n := by
  rw [largeCubeSubcubes]

/-- The depth-`(n - h)` descendant family of `cu_n` has exactly `3^{d (n - h)}`
members. -/
theorem card_descendantsAtDepth_originCube (d : ℕ) {n h : ℕ} :
    (descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card = (3 ^ d) ^ (n - h) :=
  descendantsAtDepth_card _ _

/-- Every triadic cube is a lattice translate of the centred cube of its
scale. -/
private theorem triadicCube_eq_translateCube_origin {d : ℕ} (R : TriadicCube d) :
    R = translateCube R.index (originCube d R.scale) := by
  obtain ⟨s, idx⟩ := R
  show TriadicCube.mk s idx = TriadicCube.mk s (fun i : Fin d => (0 : ℤ) + idx i)
  rw [TriadicCube.mk.injEq]
  exact ⟨rfl, funext fun i ↦ (Int.zero_add _).symm⟩

/-- Every depth-`(n - h)` descendant of the centred cube `cu_n` is a lattice
translate `z' + cu_h` of the centred cube `cu_h`, `z' = 3^h * R.index ∈
3^h ℤ^d`: the translate spelling of the index set `3^h ℤ^d ∩ cu_n` of the
Step-A average of `l.mixing.minscale`. -/
theorem mem_descendantsAtDepth_originCube_eq_translateCube {d : ℕ} {n h : ℕ}
    (hhn : h < n) {R : TriadicCube d}
    (hR : R ∈ descendantsAtDepth (originCube d (n : ℤ)) (n - h)) :
    R = translateCube R.index (originCube d (h : ℤ)) := by
  have hscale : R.scale = (h : ℤ) := by
    have h1 : R.scale = (originCube d (n : ℤ)).scale - ((n - h : ℕ) : ℤ) :=
      scale_eq_sub_of_mem_descendantsAtDepth hR
    rw [show (originCube d (n : ℤ)).scale = (n : ℤ) from rfl,
      show ((n - h : ℕ) : ℤ) = (n : ℤ) - (h : ℤ) from by omega] at h1
    omega
  calc R = translateCube R.index (originCube d R.scale) :=
      triadicCube_eq_translateCube_origin R
    _ = translateCube R.index (originCube d (h : ℤ)) := by rw [hscale]

/-- The stationarity centering on the Step-A descendant family: for every
depth-`(n - h)` descendant `R` of `cu_n`, spelled as a lattice translate
`z' + cu_h` with `z' ∈ 3^h ℤ^d`, the expectation of an entry of
`s^-1_{L,*}(R)` of the infrared cutoff is the annealed entry at the centred
cube `cu_h`.  This is the per-summand centring of the Step-A average of
`l.mixing.minscale`. -/
theorem integral_sigmaStarInvCoarse_descendant_eq_sigmaBarStarInv {d : ℕ} [NeZero d]
    {nu : ℝ} (hnu : 0 < nu) (L : ℕ) (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) {n h : ℕ} (hhn : h < n)
    (R : TriadicCube d) (hR : R ∈ descendantsAtDepth (originCube d (n : ℤ)) (n - h))
    (i j : Fin d) :
    ∫ omega : ShellSeq d, sigmaStarInvCoarse (cubeSet R)
        (coefficientCutoff nu omega L).toCoeffField i j ∂P.toMeasure
      = sigmaBarStarInv nu L P (cubeSet (originCube d (h : ℤ))) i j := by
  rw [mem_descendantsAtDepth_originCube_eq_translateCube hhn hR,
    integral_sigmaStarInvCoarse_translateCube_eq_sigmaBarStarInv hnu L P hPrefix hJ2 R.index]

end