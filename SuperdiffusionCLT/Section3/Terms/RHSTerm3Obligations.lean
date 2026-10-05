/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3CgFinalC
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscSurvivors
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3AnchorsConstFirst
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3BlupTransport
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3PigTailClose2
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3QuadZc
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3SideConditionsB

/-!
# The constant-first V4 conclusion with explicit open obligations

The conclusion below is copied verbatim from the statement of the V4 theorem.
All additional premises precede its existential constant. In particular,
the two remaining uniform constants are chosen before any section data.
The coarse-graining display and the flux moment are supplied by existing
proofs. The energy estimate follows from the same scalar pigeonhole input
as the coarse-graining step. The other premises remain open obligations.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open Homogenization
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section3.Setup

private theorem rhsTerm3Obligations_responseValue {d : ℕ} {nu : ℝ} (hnu : 0 < nu)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (L : ℕ)
    (R : Homogenization.TriadicCube d) (F : Homogenization.Vec d)
    (v : Homogenization.Book.Ch02.Solution (Homogenization.Book.Ch02.cubeDomain R)
      (cubeCutoffCoeffOn hnu omega L R)) :
    Homogenization.Book.Ch02.responseValue (Homogenization.Book.Ch02.cubeDomain R)
      (cubeCutoffCoeffOn hnu omega L R) 0 F v =
    Homogenization.volumeAverage (Homogenization.openCubeSet R)
      (fun y => -(nu / 2) * Homogenization.vecNormSq (v.toH1.grad y) +
        Homogenization.vecDot F (v.toH1.grad y)) := by
  apply congrArg (Homogenization.volumeAverage (Homogenization.openCubeSet R))
  funext y
  dsimp only [Homogenization.Book.Ch02.responseIntegrand]
  rw [Homogenization.vecDot_zero_left, sub_zero]
  rw [SuperdiffusionCLT.Section2.Localization.vecDot_symmPart_eq_mul_vecNormSq
    (show Homogenization.symmPart ((cubeCutoffCoeffOn hnu omega L R).toCoeffField y) =
      nu • (1 : Homogenization.Mat d) from
      SuperdiffusionCLT.Section2.Cutoff.symmPart_coefficientCutoff nu omega L y)]
  ring

private theorem rhsTerm3Obligations_bigValue {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)) (S : SuperdiffusionCLT.Section3.Setup.ScaleSelection) (e : Homogenization.Vec d)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) :
    energyBigQCarrier nu P S e
      (gluedMaximizerGrad hnu S (SuperdiffusionCLT.Section3.Setup.fluxSlot nu S.LPrime P S.n e)) omega =
      (1 / 2 : ℝ) * Homogenization.vecDot (SuperdiffusionCLT.Section3.Setup.fluxSlot nu S.LPrime P S.n e)
        (Homogenization.matVecMul (Homogenization.sigmaStarInvCoarse (Homogenization.openCubeSet (Homogenization.originCube d (S.m : ℤ)))
          (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega S.LPrime).toCoeffField)
          (SuperdiffusionCLT.Section3.Setup.fluxSlot nu S.LPrime P S.n e)) := by
  let F := SuperdiffusionCLT.Section3.Setup.fluxSlot nu S.LPrime P S.n e
  let R := Homogenization.originCube d (S.m : ℤ)
  have hgrad := cubeMaximizerGradient_largeCube_aeEq hnu S.LPrime S.m S.m F omega
    (show R ∈ SuperdiffusionCLT.Section2.Estimates.Stream.largeCubeSubcubes d S.m S.m by
      rw [SuperdiffusionCLT.Section2.Estimates.Stream.largeCubeSubcubes_self]; exact Finset.mem_singleton_self _)
  have heq : energyBigQCarrier nu P S e (gluedMaximizerGrad hnu S F) omega =
      Homogenization.Book.Ch02.responseValue (Homogenization.Book.Ch02.cubeDomain R)
        (cubeCutoffCoeffOn hnu omega S.LPrime R) 0 F
        (cubeMaximizer hnu omega S.LPrime F R).toSolution := by
    rw [rhsTerm3Obligations_responseValue]
    exact volumeAverage_congr_ae (hgrad.symm.mono fun y hy =>
      congrArg (fun v => -(nu / 2) * Homogenization.vecNormSq v + Homogenization.vecDot F v) hy)
  rw [heq, ← (cubeMaximizer hnu omega S.LPrime F R).responseJ_eq,
    SuperdiffusionCLT.Section3.Setup.responseJ_setupMaximizer]
  rfl

private theorem rhsTerm3Obligations_subValue {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)) (S : SuperdiffusionCLT.Section3.Setup.ScaleSelection) (e : Homogenization.Vec d)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (R : Homogenization.TriadicCube d) (hR : R ∈ SuperdiffusionCLT.Section2.Estimates.Stream.largeCubeSubcubes d S.n S.m) :
    energySubQCarrier nu P S e
      (gluedMaximizerGrad hnu S (SuperdiffusionCLT.Section3.Setup.fluxSlot nu S.LPrime P S.n e))
      (gluedSubcubeGrad hnu S (SuperdiffusionCLT.Section3.Setup.fluxSlot nu S.LPrime P S.n e)) omega R =
      (1 / 2 : ℝ) * Homogenization.vecDot (SuperdiffusionCLT.Section3.Setup.fluxSlot nu S.LPrime P S.n e)
        (Homogenization.matVecMul (Homogenization.sigmaStarInvCoarse (Homogenization.openCubeSet R)
          (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega S.LPrime).toCoeffField)
          (SuperdiffusionCLT.Section3.Setup.fluxSlot nu S.LPrime P S.n e)) := by
  let F := SuperdiffusionCLT.Section3.Setup.fluxSlot nu S.LPrime P S.n e
  obtain ⟨lam, Lam, hEll⟩ :=
    SuperdiffusionCLT.Section2.Annealed.exists_isEllipticFieldOn_coefficientCutoff_openCubeSet
      hnu omega S.LPrime (Homogenization.originCube d (S.m : ℤ))
  let v := cubeMaximizer hnu omega S.LPrime F R
  let u : Homogenization.Book.Ch02.Solution (Homogenization.Book.Ch02.cubeDomain R)
      (cubeCutoffCoeffOn hnu omega S.LPrime R) :=
    Homogenization.AHarmonicFunction.restrictToOpenSubcube
      (cubeMaximizer hnu omega S.LPrime F (Homogenization.originCube d (S.m : ℤ))).toSolution hEll hR
  have hM : u.toH1.grad =ᵐ[Homogenization.volumeMeasureOn (Homogenization.openCubeSet R)]
      gluedMaximizerGrad hnu S F omega :=
    cubeMaximizerGradient_largeCube_aeEq hnu S.LPrime S.n S.m F omega hR
  have hN : v.toSolution.toH1.grad =ᵐ[Homogenization.volumeMeasureOn (Homogenization.openCubeSet R)]
      gluedSubcubeGrad hnu S F omega :=
    cubeMaximizerGradient_subcube_aeEq hnu S.LPrime S.n S.m F omega hR
  have hval := rhsTerm3Obligations_responseValue hnu omega S.LPrime R F u
  have hval' : Homogenization.Book.Ch02.responseValue (Homogenization.Book.Ch02.cubeDomain R)
      (cubeCutoffCoeffOn hnu omega S.LPrime R) 0 F u =
      Homogenization.volumeAverage (Homogenization.openCubeSet R) (fun y => -(nu / 2) *
        Homogenization.vecNormSq (gluedMaximizerGrad hnu S F omega y) +
          Homogenization.vecDot F (gluedMaximizerGrad hnu S F omega y)) := by
    rw [hval]
    exact volumeAverage_congr_ae (hM.mono fun y hy =>
      congrArg (fun v => -(nu / 2) * Homogenization.vecNormSq v + Homogenization.vecDot F v) hy)
  have hvar : Homogenization.Book.Ch02.secondVariationEnergyValue
      (Homogenization.Book.Ch02.cubeDomain R) (cubeCutoffCoeffOn hnu omega S.LPrime R)
      v.toSolution u = (1 / 2 : ℝ) * Homogenization.volumeAverage (Homogenization.openCubeSet R)
        (fun y => nu * Homogenization.vecNormSq
          (gluedMaximizerGrad hnu S F omega y - gluedSubcubeGrad hnu S F omega y)) := by
    rw [← SuperdiffusionCLT.Section2.Estimates.Stream.volumeAverage_const_mul]
    apply volumeAverage_congr_ae
    filter_upwards [hM, hN] with y hyM hyN
    rw [SuperdiffusionCLT.Section2.Localization.vecDot_symmPart_eq_mul_vecNormSq
      (show Homogenization.symmPart ((cubeCutoffCoeffOn hnu omega S.LPrime R).toCoeffField y) =
        nu • (1 : Homogenization.Mat d) from
        SuperdiffusionCLT.Section2.Cutoff.symmPart_coefficientCutoff nu omega S.LPrime y),
      hyM, hyN]
    congr 2
    simp only [Homogenization.vecNormSq, Homogenization.vecDot, Pi.sub_apply]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hsecond := Homogenization.Book.Ch02.secondVariation_eq_of_isResponseMaximizer
    v.isMaximizer u
  rw [hval', hvar] at hsecond
  have hJ := SuperdiffusionCLT.Section3.Setup.responseJ_setupMaximizer
    (Homogenization.Book.Ch02.cubeDomain R) (cubeCutoffCoeffOn hnu omega S.LPrime R) F
  rw [← SuperdiffusionCLT.Section2.CoarseGraining.sigmaStarInvCoarse_toCoeffField] at hJ
  have hresult := (eq_add_of_sub_eq hsecond).symm.trans hJ
  change energySubQCarrier nu P S e _ _ omega R = _
  exact (add_comm _ _).trans hresult

/-- The oscillation energy premise follows from the scalar pigeonhole error
at the actual glued fields, with all response values and integrability supplied. -/
theorem rhsTerm3Obligations_energy_of_pigeon
    {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)}
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    (S : SuperdiffusionCLT.Section3.Setup.ScaleSelection)
    (hSorder : SuperdiffusionCLT.Section3.Setup.ScalesOrdering S)
    {e : Homogenization.Vec d} (he : Homogenization.vecNormSq e = 1)
    {delta etaL : ℝ}
    (hPigeon : |1 - (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq
        nu S.LPrime P S.n)⁻¹ *
        SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.LPrime P S.m| ≤
      delta + etaL) :
    ((SuperdiffusionCLT.Section2.Estimates.Stream.largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
      ∑ R ∈ SuperdiffusionCLT.Section2.Estimates.Stream.largeCubeSubcubes d S.n S.m,
        ∫ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
          oscEnergy nu hnu S P e omega R ∂P.toMeasure ≤ delta + etaL := by
  have hnm : S.n < S.m :=
    (hSorder.n_lt_ell.trans hSorder.ell_lt_ellPrime).trans hSorder.ellPrime_lt_m
  have hInt := integrable_hEnergyInt_discharged d hnu P S hnm.le e
  exact hEnergy_at_carriers hnu hPrefix hJ2 hJ3 hJ4 S he
    (gluedMaximizerGrad hnu S (SuperdiffusionCLT.Section3.Setup.fluxSlot nu S.LPrime P S.n e))
    (gluedSubcubeGrad hnu S (SuperdiffusionCLT.Section3.Setup.fluxSlot nu S.LPrime P S.n e))
    (hAnnealedSub_of_quenchedResponseValue hnu hPrefix hJ2 hJ4 S hnm _ _
      (rhsTerm3Obligations_subValue hnu P S e))
    (hAnnealedBig_of_quenchedResponseValue hnu hJ4 S _ (rhsTerm3Obligations_bigValue hnu P S e))
    (integrable_hJsubInt_discharged d hnu P S e
      (integrable_hEnergyIntDiff_discharged d hnu P S hnm.le e) hInt)
    hInt (integrableOn_energyCube_discharged hnu P S e) hPigeon

end SuperdiffusionCLT.Section3.Terms
