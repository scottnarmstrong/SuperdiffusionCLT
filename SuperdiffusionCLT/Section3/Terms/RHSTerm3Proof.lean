/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3Windowed
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3FluxUniformPart3
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3FluxUniformPart4

/-!
# The V6 term-3 conclusion from the pointwise flux estimate

`rhsTerm3Proof_of_pointwise` proves the conclusion of
`rhs_term3_constFirst` from the single remaining input `hPointwise`
(the pointwise flux estimate at the printed block weight): the cg constant is fed by
`cgConstant_windowed` inside `v6Windowed_closedCg`, the block envelope by
`fluxOrlicz_main`, and the sample-side clauses by
`fluxSample_fluxUniform_main`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open Homogenization
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.Setup

/-- The V6 conclusion, carrying only the pointwise flux estimate. -/
theorem rhsTerm3Proof_of_pointwise (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hPointwise : ∃ C1 : ℝ, 0 ≤ C1 ∧
      ∀ (nu : ℝ) (hnu : 0 < nu) (_hnu1 : nu ≤ 1)
        (P : ProbabilityMeasure (ShellSeq d))
        (_hPrefix : ShellLawPrefix d P) (_hJ1V2 : ShellLawJ1Restriction d P)
        (_hJ2 : ShellLawJ2 d P) (_hJ3 : ShellLawJ3 d P) (_hJ4 : ShellLawJ4 d P)
        (S : ScaleSelection) (_hSorder : ScalesOrdering S)
        (_hTwoHLeM : 2 * S.h ≤ S.m) (_hHundredALeH : 100 * S.a ≤ S.h)
        (_hWindowVsOffset : S.h + 1 ≤ 3 ^ S.a)
        (_hOffsetLower :
          (8056 / Real.log 3) * Real.log (nu⁻¹ * ((S.L : ℕ) : ℝ)) ≤ ((S.a : ℕ) : ℝ))
        (e : Vec d) (_he : vecNormSq e = 1),
        ∀ omega : ShellSeq d, ∀ R ∈ largeCubeSubcubes d S.n S.m,
          seminormFluxNeg nu hnu S P e omega R ^ ((3 : ℝ) / 2) ≤
            C1 * (3 : ℝ) ^ ((3 * (S.n : ℝ)) / 2) *
              (oscEnergy nu hnu S P e omega R ^ ((3 : ℝ) / 4) *
                fluxUniformBlockWeight nu S P e omega R)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (nu : ℝ) (hnu : 0 < nu) (_hnu1 : nu ≤ 1) (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
  (_hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P) (_hJ1V2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P) (_hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P) (_hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P) (_hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P) (S : SuperdiffusionCLT.Section3.Setup.ScaleSelection) (_hSorder : SuperdiffusionCLT.Section3.Setup.ScalesOrdering S) (_hTwoHLeM : 2 * S.h ≤ S.m)
  (_hHundredALeH : 100 * S.a ≤ S.h) (_hWindowVsOffset : S.h + 1 ≤ 3 ^ S.a) (_hOffsetLower : (8056 / Real.log 3) * Real.log (nu⁻¹ * ((S.L : ℕ) : ℝ)) ≤ ((S.a : ℕ) : ℝ)) (e : Homogenization.Vec d) (_he : Homogenization.vecNormSq e = 1) (delta etaL : ℝ) (_hdelta : 0 ≤ delta) (_hetaL : 0 ≤ etaL) (_hPigeonScalar : SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.L P (S.m - 2 * S.h) ≤ (1 + delta) * SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.L P S.m)
  (_hDeltaEtaLeOne : delta + etaL ≤ 1) (_hEtaL : C * nu ^ (-(5 : ℝ)) * ((S.L : ℕ) : ℝ) * (3 : ℝ) ^ (-(((S.LPrime - S.m : ℕ) : ℝ))) ≤ etaL) (w : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → Homogenization.H10Function (Homogenization.openCubeSet (Homogenization.originCube d (S.m : ℤ)))) (_hw : ∀ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d, SuperdiffusionCLT.Section3.Setup.IsDirichletResponse omega S.LPrime S.ellPrime S.m (SuperdiffusionCLT.Section3.Setup.testVector
  nu S.LPrime P S.n e) (w omega)), ∫ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d, Homogenization.volumeAverage (Homogenization.openCubeSet (Homogenization.originCube d (S.m : ℤ))) (fun y => Homogenization.vecDot ((w omega).toH1Function.grad y) (Homogenization.matVecMul ((SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega S.LPrime).toCoeffField y) (SuperdiffusionCLT.Section3.Terms.gluedGradientField hnu S.LPrime S.m S.m
  (SuperdiffusionCLT.Section3.Setup.fluxSlot nu S.LPrime P S.n e) omega y - SuperdiffusionCLT.Section3.Terms.gluedGradientField hnu S.LPrime S.n S.m (SuperdiffusionCLT.Section3.Setup.fluxSlot nu S.LPrime P S.n e) omega y))) ∂P.toMeasure ≤ C * (delta + etaL) ^ ((1 : ℝ) / 2) * Real.sqrt (((S.LPrime - S.ell : ℕ) : ℝ) ^ (2 : ℕ) * (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.LPrime P S.n) ^ (2 : ℕ) + (SuperdiffusionCLT.Section2.Annealed.sigmaBarSeq nu S.ell P
  S.n) ^ (2 : ℕ)) + C * (1 + (delta + etaL) ^ ((1 : ℝ) / 2)) * nu ^ (-(4 : ℝ)) * (((S.LPrime : ℕ) : ℝ) ^ (4 : ℕ)) * ((3 : ℝ) ^ (-((((S.ellPrime - S.n : ℕ) : ℝ)) / 2)) + (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 8)) + (3 : ℝ) ^ (-((((S.ellPrime - S.ell : ℕ) : ℝ)) / 4)) + (3 : ℝ) ^ (-((((S.h : ℕ) : ℝ)) / 16)))  := by
  obtain ⟨Cb, hCb, hO⟩ := fluxOrlicz_main d
  exact v6Windowed_closedCg d hd (fluxSample_fluxUniform_main d hd hPointwise
    ⟨Cb, hCb, fun nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder _ _ _ _ e he R hR =>
      hO nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder e he R hR⟩)

end SuperdiffusionCLT.Section3.Terms
