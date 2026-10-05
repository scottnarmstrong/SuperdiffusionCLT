/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.MasterIdentityAssemblyC
public import SuperdiffusionCLT.Section3.Setup.MasterIdentityResidue
public import SuperdiffusionCLT.Section3.Setup.MasterIdentityResidueC
public import SuperdiffusionCLT.Section3.Setup.RootIdentityClose
public import SuperdiffusionCLT.Section3.Setup.ResponseMeasurabilitySelection
public import SuperdiffusionCLT.Section2.Localization.Conj3AveragedRoute

/-!
# `rootTestingId_main`: the annealed testing identity, conjunct (2) of `hOpenSelection`

The master identity `e.ellsep.testing` of the paper is obtained by testing
`e.def.w` against the response itself and `e.ellsep` against the response, then
decomposing the flux at the scale-`n` glued field.  The root statement is
assembled in `Section3/Terms/SstarWithAnchors.lean`;
its `hOpenSelection` binder is an existential
`∃ e, ... ∧ ∃ w, hResponse ∧ hT3 ∧ hIdentity` — the response condition is
conjunct (1), the term-3 estimate is a separate hypothesis of the root, and
`hIdentity` is conjunct (2), proved here for an arbitrary `w` satisfying
the response condition (not only the canonical selection of
`DirichletResponseUnique.lean`), at every admissible law and scale selection,
with **no** hypothesis beyond the standing scale/law data and the response
condition itself.

## What is already available, and what this file adds

Every analytic ingredient of the identity is already proved somewhere in the
tree:

* the pointwise display `e.ellsep.testing` at the maximizer carrier, with
  **no weak Hessian of the maximizer** (a route through a
  weak Hessian of the maximizer genuinely needs one, which is not available from the
  carrier of the underlying regularity theory; the route used here,
  `ellsep_testing_of_h1_field` in `Terms/SkewWeakDivergenceB.lean`,
  proves the same display for an arbitrary `H¹` field with no such datum) —
  wrapped at the maximizer carrier by `MasterIdentityResidue.master_residue_ellsep`;
* the two carrier-rewriting side conditions `hIntSub`, `hIntCoord`
  (`MasterIdentityResidue.master_residue_intSub`, `master_residue_intCoord`);
* the annealed energy integrability `hEnergy`
  (`MasterIdentityResidue.master_residue_energy`), fed by the sample
  measurability of the cube-energy map of *any* Dirichlet response
  (`ResponseMeasurabilitySelection.measurable_vecCubeLpENorm_grad_of_isDirichletResponse`,
  which needs only the response condition, not canonicity);
* the four annealed integrability binders `hI1`-`hI4`
  (`MasterIdentityResidueC.master_residue_hI1`,
  `RootIdentityClose.master_residue_hI2`, `master_residue_hI3`,
  `MasterIdentityResidue.master_residue_hI4`);
* the final assembly into the exact `.toReal`-lintegral display
  (`MasterIdentityAssemblyC.master_identity_of_ellsep`).

The one genuine gap is a bookkeeping one: the root's `uMgrad` conjunct is the
*self-glued* field `gluedGradientField hnu S.LPrime S.m S.m F` (gluing the
scale-`m` cube over its own trivial one-cube partition), while the
`hI3`/`hEllsep` statements are available at the plain maximizer gradient
`cubeMaximizerGradient hnu omega S.LPrime F cu_m`.  `rootTestingId_uMgrad_eq_on_cube`
below records that the two agree *exactly* on `cu_m` (not just a.e.) — the
self-glued field is defined as an indicator of the maximizer gradient on the
unique cube of `largeCubeSubcubes d S.m S.m`
(`largeCubeSubcubes_self` in `Terms/GluedField.lean`) — and the two carrier-transport
theorems `rootTestingId_hEllsep`, `rootTestingId_hI3` use it, through
`Section2/Localization/Conj3AveragedRoute.lean`'s `volumeAverage_congr_on`, to
restate the maximizer-carrier statements at the root's own `uMgrad`.  `H1Function.grad`
(`CoarseGraining`'s `Homogenization.Sobolev.H1.Definitions`) is an unconstrained
witness outside its domain, so this on-cube transport — not a global function
equality — is the honest form of the bridge.

## Main result

* `rootTestingId_main` — the identity in exactly the shape `hOpenSelection`
  needs it, for every `nu`, admissible law `P`, scale selection `S`, unit
  direction `e`, and response family `w` satisfying the response condition.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Setup

open MeasureTheory ProbabilityTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Probability.Stationary
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Terms
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The on-cube pin bridge -/

/-- **`uMgrad` at the root's own carrier is the plain maximizer gradient, on
`cu_m` exactly.**  `gluedGradientField hnu S.LPrime S.m S.m F` glues the
maximizer gradient over `largeCubeSubcubes d S.m S.m`, which is the singleton
`{cu_m}` (`GluedField.largeCubeSubcubes_self`), so on `cu_m` the indicator sum
collapses to the single term `cubeMaximizerGradient hnu omega S.LPrime F cu_m`.
This is an equality of *values on the cube*, not a global function equality:
`H1Function.grad` carries no constraint off its domain, so the self-glued
field (zero off `cu_m`, by construction) need not agree with the maximizer's
own gradient witness there. -/
theorem rootTestingId_uMgrad_eq_on_cube [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (S : ScaleSelection) (F : Vec d) (omega : ShellSeq d) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d (S.m : ℤ))) :
    gluedGradientField hnu S.LPrime S.m S.m F omega x =
      cubeMaximizerGradient hnu omega S.LPrime F (originCube d (S.m : ℤ)) x :=
  gluedGradientField_apply_of_mem_openCubeSet hnu S.LPrime S.m S.m F omega
    (by rw [SuperdiffusionCLT.Section3.Terms.largeCubeSubcubes_self]
        exact Finset.mem_singleton_self _) hx

/-! ## `hEllsep` at the root's own carriers -/

/-- **`hEllsep` in the exact shape `hOpenSelection` needs it**: the pointwise
display `e.ellsep.testing` with `uMgrad := gluedGradientField hnu S.LPrime
S.m S.m F` (the root's self-glued scale-`m` field) and `uNGlued :=
gluedGradientField hnu S.LPrime S.n S.m F`, `F := fluxSlot nu S.LPrime P S.n e`.
Obtained from `MasterIdentityResidue.master_residue_ellsep` at the maximizer
carrier (`hUgrad := rfl`, since the carrier is chosen to be
`cubeMaximizerGradient` literally) and transported to the root's `uMgrad` by
`rootTestingId_uMgrad_eq_on_cube`; no hypothesis beyond the response
condition `hw`. -/
theorem rootTestingId_hEllsep [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) (e : Vec d)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega)) :
    ∀ omega : ShellSeq d,
      volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => vecNormSq ((w omega).toH1Function.grad x)) =
        volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
            (fun x => vecDot ((w omega).toH1Function.grad x)
              (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
                  (gluedGradientField hnu S.LPrime S.n S.m
                      (fluxSlot nu S.LPrime P S.n e) omega x) -
                qVector hnu P S.LPrime S.ell S.n S.m
                  (fluxSlot nu S.LPrime P S.n e))) +
          volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
            (fun x => vecDot ((w omega).toH1Function.grad x)
              (matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x)
                (gluedGradientField hnu S.LPrime S.n S.m
                    (fluxSlot nu S.LPrime P S.n e) omega x -
                  testVector nu S.LPrime P S.n e))) +
          volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
            (fun x => vecDot ((w omega).toH1Function.grad x)
              (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x)
                (gluedGradientField hnu S.LPrime S.m S.m
                    (fluxSlot nu S.LPrime P S.n e) omega x -
                  gluedGradientField hnu S.LPrime S.n S.m
                      (fluxSlot nu S.LPrime P S.n e) omega x))) -
          vecDot (testVector nu S.LPrime P S.n e)
            (volumeAverageVec (openCubeSet (originCube d (S.m : ℤ)))
              (fun x => matVecMul
                (streamCutoff omega S.ellPrime x - streamCutoff omega S.ell x)
                ((w omega).toH1Function.grad x))) := by
  have hUL2 : ∀ omega : ShellSeq d, MemVectorL2 (openCubeSet (originCube d (S.m : ℤ)))
      (gluedGradientField hnu S.LPrime S.n S.m (fluxSlot nu S.LPrime P S.n e) omega) :=
    fun omega => memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.n S.m
      (fluxSlot nu S.LPrime P S.n e) omega (originCube d (S.m : ℤ))
  have hbase := master_residue_ellsep nu hnu S (testVector nu S.LPrime P S.n e)
    (qVector hnu P S.LPrime S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e))
    (fluxSlot nu S.LPrime P S.n e) w
    (fun omega => cubeMaximizerGradient hnu omega S.LPrime
      (fluxSlot nu S.LPrime P S.n e) (originCube d (S.m : ℤ)))
    (gluedGradientField hnu S.LPrime S.n S.m (fluxSlot nu S.LPrime P S.n e))
    hw hUL2 (fun _ => rfl)
  intro omega
  have hC : volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
      (fun x => vecDot ((w omega).toH1Function.grad x)
        (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x)
          (cubeMaximizerGradient hnu omega S.LPrime (fluxSlot nu S.LPrime P S.n e)
              (originCube d (S.m : ℤ)) x -
            gluedGradientField hnu S.LPrime S.n S.m (fluxSlot nu S.LPrime P S.n e)
              omega x))) =
      volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
      (fun x => vecDot ((w omega).toH1Function.grad x)
        (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x)
          (gluedGradientField hnu S.LPrime S.m S.m (fluxSlot nu S.LPrime P S.n e) omega x -
            gluedGradientField hnu S.LPrime S.n S.m (fluxSlot nu S.LPrime P S.n e)
              omega x))) :=
    SuperdiffusionCLT.Section2.Localization.volumeAverage_congr_on
      (measurableSet_openCubeSet (originCube d (S.m : ℤ)))
      (fun x hx => by
        rw [rootTestingId_uMgrad_eq_on_cube hnu S (fluxSlot nu S.LPrime P S.n e) omega hx])
  rw [hbase omega, hC]

/-! ## `hI3` at the root's own carriers -/

/-- **`hI3` in the exact shape `hOpenSelection` needs it**, transported from
the maximizer carrier of `RootIdentityClose.master_residue_hI3` by
`rootTestingId_uMgrad_eq_on_cube` and `volumeAverage_congr_on`, applied
pointwise in `omega` and lifted through function equality. -/
theorem rootTestingId_hI3 {d : ℕ} [NeZero d] (hd : 2 ≤ d) (nu : ℝ) (hnu : 0 < nu)
    (hnu1 : nu ≤ 1) (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P) (hJ1V2 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (hSorder : ScalesOrdering S)
    (e : Vec d) (he : vecNormSq e = 1)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega)) :
    Integrable (fun omega : ShellSeq d =>
      volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => vecDot ((w omega).toH1Function.grad x)
          (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x)
            (gluedGradientField hnu S.LPrime S.m S.m
                (fluxSlot nu S.LPrime P S.n e) omega x -
              gluedGradientField hnu S.LPrime S.n S.m
                (fluxSlot nu S.LPrime P S.n e) omega x)))) P.toMeasure := by
  have hbase := master_residue_hI3 hd nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder
    e he (testVector nu S.LPrime P S.n e) rfl w hw
  have heq : (fun omega : ShellSeq d =>
      volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => vecDot ((w omega).toH1Function.grad x)
          (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x)
            (cubeMaximizerGradient hnu omega S.LPrime (fluxSlot nu S.LPrime P S.n e)
                (originCube d (S.m : ℤ)) x -
              gluedGradientField hnu S.LPrime S.n S.m (fluxSlot nu S.LPrime P S.n e)
                omega x)))) =
    (fun omega : ShellSeq d =>
      volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => vecDot ((w omega).toH1Function.grad x)
          (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x)
            (gluedGradientField hnu S.LPrime S.m S.m (fluxSlot nu S.LPrime P S.n e) omega x -
              gluedGradientField hnu S.LPrime S.n S.m (fluxSlot nu S.LPrime P S.n e)
                omega x)))) := by
    funext omega
    exact SuperdiffusionCLT.Section2.Localization.volumeAverage_congr_on
      (measurableSet_openCubeSet (originCube d (S.m : ℤ)))
      (fun x hx => by
        rw [rootTestingId_uMgrad_eq_on_cube hnu S (fluxSlot nu S.LPrime P S.n e) omega hx])
  rwa [heq] at hbase

/-! ## The assembled identity -/

/-- **`rootTestingId_main`: conjunct (2) of `hOpenSelection`**, the annealed
testing identity `e.ellsep.testing` (under the expectation), in exactly the shape
the root assembly consumes it, for every admissible law and scale
selection and every response family `w` satisfying the response condition.
No hypothesis beyond the standing scale/law data, `hd`, and `hw` remains: every
integrability and measurability side condition is discharged by citation. -/
theorem rootTestingId_main {d : ℕ} [NeZero d] (hd : 2 ≤ d) (nu : ℝ) (hnu : 0 < nu)
    (hnu1 : nu ≤ 1) (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P) (hJ1V2 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (hSorder : ScalesOrdering S)
    (e : Vec d) (he : vecNormSq e = 1)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega)) :
    (∫⁻ omega : ShellSeq d,
        vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (w omega).toH1Function.grad ^ (2 : ℕ) ∂P.toMeasure : ℝ≥0∞).toReal =
      ((∫ omega : ShellSeq d,
            volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
              (fun x => vecDot ((w omega).toH1Function.grad x)
                (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
                    (gluedGradientField hnu S.LPrime S.n S.m
                        (fluxSlot nu S.LPrime P S.n e) omega x) -
                  qVector hnu P S.LPrime S.ell S.n S.m
                    (fluxSlot nu S.LPrime P S.n e))) ∂P.toMeasure +
          ∫ omega : ShellSeq d,
            ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
              ∑ z ∈ largeCubeSubcubes d S.n S.m,
                volumeAverage (openCubeSet z)
                  (fun y => vecDot ((w omega).toH1Function.grad y)
                    (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
                      (coefficientCutoff nu omega S.ell).toCoeffField y)
                      (gluedGradientField hnu S.LPrime S.n S.m
                          (fluxSlot nu S.LPrime P S.n e) omega y -
                        testVector nu S.LPrime P S.n e))) ∂P.toMeasure) +
          ∫ omega : ShellSeq d,
            volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
              (fun y => vecDot ((w omega).toH1Function.grad y)
                (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
                  (gluedGradientField hnu S.LPrime S.m S.m
                      (fluxSlot nu S.LPrime P S.n e) omega y -
                    gluedGradientField hnu S.LPrime S.n S.m
                      (fluxSlot nu S.LPrime P S.n e) omega y))) ∂P.toMeasure) -
        ∫ omega : ShellSeq d,
          volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
            (fun y => vecDot (testVector nu S.LPrime P S.n e)
              (matVecMul (streamCutoff omega S.ellPrime y -
                  streamCutoff omega S.ell y) ((w omega).toH1Function.grad y)))
          ∂P.toMeasure := by
  have hIntSub := master_residue_intSub nu S (testVector nu S.LPrime P S.n e) w
    (gluedGradientField hnu S.LPrime S.n S.m (fluxSlot nu S.LPrime P S.n e))
    (fun omega => memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.n S.m
      (fluxSlot nu S.LPrime P S.n e) omega (originCube d (S.m : ℤ)))
  have hIntCoord := master_residue_intCoord S w
  have hEnergyMeas : AEMeasurable (fun omega : ShellSeq d =>
      vecCubeLpENorm (originCube d (S.m : ℤ)) 2 (w omega).toH1Function.grad)
      P.toMeasure :=
    (measurable_vecCubeLpENorm_grad_of_isDirichletResponse hw).aemeasurable
  have hEnergy := master_residue_energy hd nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S
    hSorder e he (testVector nu S.LPrime P S.n e) rfl w hw hEnergyMeas
  have hI1 := master_residue_hI1 hd nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder
    e he (testVector nu S.LPrime P S.n e) rfl
    (qVector hnu P S.LPrime S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e)) w
    (gluedGradientField hnu S.LPrime S.n S.m (fluxSlot nu S.LPrime P S.n e)) rfl hw
  have hI2 := master_residue_hI2 hd nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder
    e he (testVector nu S.LPrime P S.n e) rfl w hw
  have hI3 := rootTestingId_hI3 hd nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder e he w hw
  have hI4 := master_residue_hI4 hd nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder
    e he (testVector nu S.LPrime P S.n e) rfl w hw
  exact master_identity_of_ellsep nu P S (testVector nu S.LPrime P S.n e)
    (qVector hnu P S.LPrime S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e)) w
    (gluedGradientField hnu S.LPrime S.m S.m (fluxSlot nu S.LPrime P S.n e))
    (gluedGradientField hnu S.LPrime S.n S.m (fluxSlot nu S.LPrime P S.n e))
    (rootTestingId_hEllsep hnu P S e w hw) hIntSub hIntCoord hEnergy hI1 hI2 hI3 hI4

end

end SuperdiffusionCLT.Section3.Setup
