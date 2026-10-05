/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3Proof
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3FluxUniformPart2

/-!
# The V6 term-3 conclusion, closed

`rhsTerm3_closed` is `rhsTerm3Proof_of_pointwise` with its one input,
the pointwise flux estimate of the paper (the flux estimate in the proof of `l.RHS.term3`),
supplied by `fluxPointwise_main`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open Homogenization
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.Setup

/-- The conclusion of `rhs_term3_constFirst`, with no hypotheses. -/
theorem rhsTerm3_closed (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (nu : ℝ) (hnu : 0 < nu) (_hnu1 : nu ≤ 1) (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
  (_hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P) (_hJ1V2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P) (_hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P) (_hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P) (_hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P) (S : SuperdiffusionCLT.Section3.Setup.ScaleSelection) (_hSorder : SuperdiffusionCLT.Section3.Setup.ScalesOrdering S) (_hTwoHLeM : 2 * S.h ≤ S.m)
  (_hHundredALeH : 100 * S.a ≤ S.h) (_hWindowVsOffset : S.h + 1 ≤ 3 ^ S.a) (_hOffsetLower : (8056 / Real.log 3) * Real.log (nu⁻¹ * ((S.L : ℕ) : ℝ)) ≤ ((S.a : ℕ) : ℝ)) (e : Homogenization.Vec d) (_he : Homogenization.vecNormSq e = 1) (delta etaL : ℝ) (_hdelta : 0 ≤ delta) (_hetaL : 0 ≤ etaL) (_hPigeonScalar : SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.L P (S.m - 2 * S.h) ≤ (1 + delta) * SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.L P S.m)
  (_hDeltaEtaLeOne : delta + etaL ≤ 1) (_hEtaL : C * nu ^ (-(5 : ℝ)) * ((S.L : ℕ) : ℝ) * (3 : ℝ) ^ (-(((S.LPrime - S.m : ℕ) : ℝ))) ≤ etaL) (w : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → Homogenization.H10Function (Homogenization.openCubeSet (Homogenization.originCube d (S.m : ℤ)))) (_hw : ∀ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d, SuperdiffusionCLT.Section3.Setup.IsDirichletResponse omega S.LPrime S.ellPrime S.m (SuperdiffusionCLT.Section3.Setup.testVector
  nu S.LPrime P S.n e) (w omega)), ∫ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d, Homogenization.volumeAverage (Homogenization.openCubeSet (Homogenization.originCube d (S.m : ℤ))) (fun y => Homogenization.vecDot ((w omega).toH1Function.grad y) (Homogenization.matVecMul ((SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega S.LPrime).toCoeffField y) (SuperdiffusionCLT.Section3.Terms.gluedGradientField hnu S.LPrime S.m S.m
  (SuperdiffusionCLT.Section3.Setup.fluxSlot nu S.LPrime P S.n e) omega y - SuperdiffusionCLT.Section3.Terms.gluedGradientField hnu S.LPrime S.n S.m (SuperdiffusionCLT.Section3.Setup.fluxSlot nu S.LPrime P S.n e) omega y))) ∂P.toMeasure ≤ C * (delta + etaL) ^ ((1 : ℝ) / 2) * Real.sqrt (((S.LPrime - S.ell : ℕ) : ℝ) ^ (2 : ℕ) * (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.LPrime P S.n) ^ (2 : ℕ) + (SuperdiffusionCLT.Section2.Annealed.sigmaBarSeq nu S.ell P
  S.n) ^ (2 : ℕ)) + C * (1 + (delta + etaL) ^ ((1 : ℝ) / 2)) * nu ^ (-(4 : ℝ)) * (((S.LPrime : ℕ) : ℝ) ^ (4 : ℕ)) * ((3 : ℝ) ^ (-((((S.ellPrime - S.n : ℕ) : ℝ)) / 2)) + (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 8)) + (3 : ℝ) ^ (-((((S.ellPrime - S.ell : ℕ) : ℝ)) / 4)) + (3 : ℝ) ^ (-((((S.h : ℕ) : ℝ)) / 16))) :=
  rhsTerm3Proof_of_pointwise d hd (fluxPointwise_main d)

end SuperdiffusionCLT.Section3.Terms
