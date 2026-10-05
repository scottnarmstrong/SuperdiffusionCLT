/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3CgCloseB

/-!
# `term3_cgBound_closeB`: the display `e.RHS.term3.A` at the reduced package

This module carries the display half of the term-3 coarse-graining split.  It
states `term3_cgBound_closeB`, the conclusion `_hCgBound` of the term-3 final assembly
copied verbatim, from the binders of that
statement together with the residual package of `term3_cgBound_close`
(in `Section3/Terms/RHSTerm3CgClose.lean`) *after* the nine side conditions
discharged in `RHSTerm3CgCloseB`.

The membership and integrability block lives in `RHSTerm3CgCloseB`; the split
keeps the files short and mirrors the printed structure:
`RHSTerm3CgCloseB` is the side-condition block of the two Cauchy-Schwarz steps
and the Hoelder pair, this module is the display `e.RHS.term3.A`
itself.
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

/-- **`term3_cgBound_closeB`.**  The printed display `e.RHS.term3.A`
(`_hCgBound` of the term-3 final assembly) — verbatim — from
the binders together with the *reduced* residual package of
`term3_cgBound_close`: nine of the twenty-six residuals are discharged here, with
no hypothesis of their own — the membership and integrability side conditions
`hMemDiff`, `hXmeas`, `hMembCS`, `hMembDiff`, `hInt1`, `hInt2`, `hEnergyCube`
and the two Cauchy-Schwarz pairings `hProdCS`, `hProdDiff`.  The seventeen that
remain are the analytic package `Cp`, `hCp`, `Cw`, `hCw`, `hessianL4`,
`hPoincare`, `hNablaw`, `hde1`, `hCerr`, `hFluxInt`, `hEnergyIntDiff`,
`hAnnealedSub`, `hAnnealedBig`, `hJsubInt`, `hEnergyInt`, `hPigeon`, `hMemf`.

The `Cerr` binder is *not* removed: the display carries `Cerr` with the positive
slope `3^{-(ℓ'−ℓ)/4}(L')²ν^{-5/2}`, so a free `Cerr` has false instances and
`hCerr` is part of the honest statement. -/
theorem term3_cgBound_closeB
    (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (nu : ℝ) (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P) (hJ1V2 : ShellLawJ1Restriction d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (hSorder : ScalesOrdering S)
    (hTwoHLeM : 2 * S.h ≤ S.m) (hHundredALeH : 100 * S.a ≤ S.h)
    (hWindowVsOffset : S.h + 1 ≤ 3 ^ S.a)
    (e : Vec d) (he : vecNormSq e = 1)
    (delta etaL : ℝ) (hdelta : 0 ≤ delta) (hetaL : 0 ≤ etaL)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      SuperdiffusionCLT.Section3.Setup.IsDirichletResponse
        omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega))
    (Cerr : ℝ)
    (Cp Cw : ℝ) (hCp : 0 ≤ Cp) (hCw : 0 ≤ Cw)
    (hessianL4 : ShellSeq d → ℝ)
    (hde1 : delta + etaL ≤ 1)
    (hCerr : cgBoundConst Cp Cw (bEllipConst d) ≤ Cerr)
    (hFluxInt : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      Integrable (fun omega : ShellSeq d =>
        gluedFluxNorm hnu S (fluxSlot nu S.LPrime P S.n e) omega R) P.toMeasure)
    (hEnergyIntDiff : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      Integrable (fun omega : ShellSeq d =>
        volumeAverage (openCubeSet R)
          (fun y => nu * vecNormSq
            (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e) omega y -
              gluedSubcubeGrad hnu S (fluxSlot nu S.LPrime P S.n e) omega y)))
        P.toMeasure)
    (hAnnealedSub : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      ∫ omega : ShellSeq d,
          energySubQCarrier nu P S e (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e))
            (gluedSubcubeGrad hnu S (fluxSlot nu S.LPrime P S.n e)) omega R
        ∂P.toMeasure =
        (1 / 2 : ℝ) * sigmaBarStarInvSeq nu S.LPrime P S.n *
          vecNormSq (fluxSlot nu S.LPrime P S.n e))
    (hAnnealedBig : ∫ omega : ShellSeq d,
          energyBigQCarrier nu P S e
            (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e)) omega
        ∂P.toMeasure =
        (1 / 2 : ℝ) * sigmaBarStarInvSeq nu S.LPrime P S.m *
          vecNormSq (fluxSlot nu S.LPrime P S.n e))
    (hJsubInt : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      Integrable (fun omega : ShellSeq d =>
        energySubQCarrier nu P S e (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e))
          (gluedSubcubeGrad hnu S (fluxSlot nu S.LPrime P S.n e)) omega R) P.toMeasure)
    (hEnergyInt : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      Integrable (fun omega : ShellSeq d =>
        volumeAverage (openCubeSet R)
          (fun y => -(nu / 2) * vecNormSq
              (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e) omega y) +
            vecDot (fluxSlot nu S.LPrime P S.n e)
              (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e) omega y)))
        P.toMeasure)
    (hPigeon : |1 - (sigmaBarStarInvSeq nu S.LPrime P S.n)⁻¹ *
      sigmaBarStarInvSeq nu S.LPrime P S.m| ≤ delta + etaL)
    (hPoincare : (((coarsePairs d S.n (coarseBlockScale d S) S.m).card : ℝ)⁻¹ *
          ∑ q ∈ coarsePairs d S.n (coarseBlockScale d S) S.m,
            ∫ omega : ShellSeq d,
              vecNormSq (volumeAverageVec (openCubeSet q.2) ((w omega).toH1Function.grad) -
                  volumeAverageVec (openCubeSet q.1) ((w omega).toH1Function.grad)) ^ (2 : ℝ)
              ∂P.toMeasure) ^ ((1 : ℝ) / 4) ≤
      Cp * (3 : ℝ) ^ ((coarseBlockScale d S : ℕ) : ℝ) *
        (∫ omega : ShellSeq d, hessianL4 omega ∂P.toMeasure) ^ ((1 : ℝ) / 4))
    (hNablaw : (∫ omega : ShellSeq d, hessianL4 omega ∂P.toMeasure) ^ ((1 : ℝ) / 4) ≤
      Cw * (3 : ℝ) ^ (-((S.ellPrime : ℕ) : ℝ)) * nu ^ (-(1 : ℝ) / 2))
    (hMemf : ∀ q ∈ coarsePairs d S.n (coarseBlockScale d S) S.m,
      MemLp (fun omega : ShellSeq d =>
        gluedFluxNorm hnu S (fluxSlot nu S.LPrime P S.n e) omega q.2 ^ ((1 : ℝ) / 2))
        (ENNReal.ofReal (2 : ℝ)) P.toMeasure) :
    ∫ omega : ShellSeq d,
        ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
          ∑ R ∈ largeCubeSubcubes d S.n S.m,
            vecDot (volumeAverageVec (openCubeSet R) ((w omega).toH1Function.grad))
              (volumeAverageVec (openCubeSet R)
                (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
                  (gluedGradientField hnu S.LPrime S.m S.m
                      (fluxSlot nu S.LPrime P S.n e) omega y -
                    gluedGradientField hnu S.LPrime S.n S.m
                      (fluxSlot nu S.LPrime P S.n e) omega y))) ∂P.toMeasure ≤
      (((largeCubeSubcubes d (coarseBlockScale d S) S.m).card : ℝ)⁻¹ *
          ∑ z' ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
            (((descendantsAtDepth z' (coarseBlockScale d S - S.n)).card : ℕ) : ℝ)⁻¹ *
              ∑ z ∈ descendantsAtDepth z' (coarseBlockScale d S - S.n),
                ∫ omega : ShellSeq d,
                  translatedBlockHalfWeight nu S.LPrime w omega z' z
                  ∂P.toMeasure) ^ ((1 : ℝ) / 2) *
          (delta + etaL) ^ ((1 : ℝ) / 2) +
        Cerr * (3 : ℝ) ^ (-(((S.ellPrime - S.ell : ℕ) : ℝ) / 4)) *
          ((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ) * nu ^ (-(5 : ℝ) / 2) := by
  refine term3_cgBound_close d hd nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder
    hTwoHLeM hHundredALeH hWindowVsOffset e he delta etaL hdelta hetaL w hw Cerr Cp Cw hCp
    hCw hessianL4 hde1 hCerr hFluxInt hEnergyIntDiff hAnnealedSub hAnnealedBig hJsubInt
    hEnergyInt ?_ hPigeon ?_ ?_ hPoincare hNablaw ?_ ?_ ?_ ?_ ?_ ?_ hMemf
  · exact integrableOn_energyCube_discharged hnu P S e
  · exact memLp_two_vecNormSq_cubeMeanDiff_coarsePairs_discharged (d := d) hd hnu hnu1 hPrefix
      hJ1V2 hJ2 hJ3 hJ4 S hSorder he w hw
  · exact aemeasurable_halfWeightDiff_coarsePairs_discharged hnu P S w hw
  · exact integrable_hInt1_discharged hd hnu hnu1 hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder he w hw
  · exact integrable_hInt2_discharged hd hnu hnu1 hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder he w hw
  · intro q hq
    have h1 : MemLp (fun omega : ShellSeq d =>
        translatedBlockHalfWeight nu S.LPrime w omega q.1 q.2 ^ ((1 : ℝ) / 2)) 2
        P.toMeasure := by
      simpa using memLp_two_halfWeight_sqrt_coarsePairs_discharged (d := d) hd hnu hnu1 hPrefix
        hJ1V2 hJ2 hJ3 hJ4 S hSorder he w hw q hq
    have h2 : MemLp (fun omega : ShellSeq d =>
        gluedFluxNorm hnu S (fluxSlot nu S.LPrime P S.n e) omega q.2 ^ ((1 : ℝ) / 2)) 2
        P.toMeasure := by simpa using hMemf q hq
    exact h1.integrable_mul h2
  · exact memLp_two_halfWeight_sqrt_coarsePairs_discharged (d := d) hd hnu hnu1 hPrefix
      hJ1V2 hJ2 hJ3 hJ4 S hSorder he w hw
  · intro q hq
    have h1 : MemLp (fun omega : ShellSeq d =>
        translatedBlockHalfWeightDiff nu S.LPrime w omega q.1 q.2 ^ ((1 : ℝ) / 2)) 2
        P.toMeasure := by
      simpa using memLp_two_halfWeightDiff_sqrt_coarsePairs_discharged (d := d) hd hnu hnu1
        hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder he w hw q hq
    have h2 : MemLp (fun omega : ShellSeq d =>
        gluedFluxNorm hnu S (fluxSlot nu S.LPrime P S.n e) omega q.2 ^ ((1 : ℝ) / 2)) 2
        P.toMeasure := by simpa using hMemf q hq
    exact h1.integrable_mul h2
  · exact memLp_two_halfWeightDiff_sqrt_coarsePairs_discharged (d := d) hd hnu hnu1 hPrefix
      hJ1V2 hJ2 hJ3 hJ4 S hSorder he w hw

end

end SuperdiffusionCLT.Section3.Terms
