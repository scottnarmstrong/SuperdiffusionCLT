/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscFluxEnergy
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3MemFluxB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3IntegrabilityC

/-!
# The `P`-integrability leaf `_hXint` of `_hOscBound`

The display `_hOscBound` carries, on the sample side of its Hölder step, three
membership conditions:

* `_hXint`: the oscillation lattice average
  `card⁻¹ ∑_R ⍍_R (∇w − ⍍_R ∇w) · a_{L'}(∇ũ_m − ∇ũ_n)` is `P`-integrable;
* `_hMemOsc`: the oscillation carrier is in `L³(P)`, per sub-cube;
* `_hMemFlux`: the flux carrier is in `L^{3/2}(P)`, per sub-cube.

This module discharges `_hXint`.  The conclusion of `sideCondition_hosc_final`
(`RHSTerm3SideFinal.lean`) is this integrand **verbatim**.  That theorem carries
two side inputs beyond the ambient telescope: the per-sub-cube square-integrability
of the cutoff-flux cube mean, and the large-cube pairing.  Both are theorems with
the ambient telescope as their only inputs — `hMemFlux_discharged_B`
(`RHSTerm3MemFluxB.lean`) and `hPair_discharged_B` (`RHSTerm3IntegrabilityC.lean`)
— so `_hXint` is discharged here from `hd`, `nu`, `hnu`, `hnu1`, the five shell
laws, `S`, `hSorder`, `e`, `he`, `w`, `hw` alone.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory ProbabilityTheory
open Homogenization
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## `_hXint`, discharged -/

/-- **`_hXint` of `_hOscBound`, discharged.**  The integrand is the conclusion
of `sideCondition_hosc_final` verbatim, and the two side inputs that theorem
carries are theorems of the ambient telescope: the flux-cube-mean square
integrability `hMemFlux_discharged_B` and the large-cube pairing
`hPair_discharged_B`.  No hypothesis of `_hOscBound` is used beyond `hd`, `nu`,
`hnu`, `hnu1`, the five shell laws, `S`, `hSorder`, `e`, `he`, `w`, `hw`. -/
theorem hXint_discharged [NeZero d] (hd : 2 ≤ d) {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ1V2 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (S : ScaleSelection) (hSorder : ScalesOrdering S)
    {e : Vec d} (he : vecNormSq e = 1)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      SuperdiffusionCLT.Section3.Setup.IsDirichletResponse
        omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega)) :
    Integrable (fun omega : ShellSeq d =>
      ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
        ∑ R ∈ largeCubeSubcubes d S.n S.m,
          volumeAverage (openCubeSet R)
            (fun y => vecDot ((w omega).toH1Function.grad y -
                volumeAverageVec (openCubeSet R) ((w omega).toH1Function.grad))
              (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
                (gluedGradientField hnu S.LPrime S.m S.m
                    (fluxSlot nu S.LPrime P S.n e) omega y -
                  gluedGradientField hnu S.LPrime S.n S.m
                    (fluxSlot nu S.LPrime P S.n e) omega y)))) P.toMeasure :=
  sideCondition_hosc_final hd hnu hnu1 hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder he w hw
    (hMemFlux_discharged_B hnu hPrefix hJ2 hJ3 hJ4 S hSorder e)
    (hPair_discharged_B hd hnu hnu1 hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder he w hw)

/-! ## The display with `_hXint` discharged -/

end

end SuperdiffusionCLT.Section3.Terms
