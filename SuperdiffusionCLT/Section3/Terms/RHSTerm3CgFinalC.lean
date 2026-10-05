/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3CgFinalB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3Energy

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

private theorem cgFinalC_responseValue {d : ℕ} {nu : ℝ} (hnu : 0 < nu)
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

private theorem cgFinalC_bigValue {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
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
      rw [largeCubeSubcubes_self]; exact Finset.mem_singleton_self _)
  have heq : energyBigQCarrier nu P S e (gluedMaximizerGrad hnu S F) omega =
      Homogenization.Book.Ch02.responseValue (Homogenization.Book.Ch02.cubeDomain R)
        (cubeCutoffCoeffOn hnu omega S.LPrime R) 0 F
        (cubeMaximizer hnu omega S.LPrime F R).toSolution := by
    rw [cgFinalC_responseValue]
    exact volumeAverage_congr_ae (hgrad.symm.mono fun y hy =>
      congrArg (fun v => -(nu / 2) * Homogenization.vecNormSq v + Homogenization.vecDot F v) hy)
  rw [heq, ← (cubeMaximizer hnu omega S.LPrime F R).responseJ_eq,
    SuperdiffusionCLT.Section3.Setup.responseJ_setupMaximizer]
  rfl

private theorem cgFinalC_subValue {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
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
  have hval := cgFinalC_responseValue hnu omega S.LPrime R F u
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

private theorem cgFinalC_small
    (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (nu : ℝ) (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P) (hJ1V2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P) (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P) (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    (S : SuperdiffusionCLT.Section3.Setup.ScaleSelection) (hSorder : SuperdiffusionCLT.Section3.Setup.ScalesOrdering S)
    (hTwoHLeM : 2 * S.h ≤ S.m) (hHundredALeH : 100 * S.a ≤ S.h)
    (hWindowVsOffset : S.h + 1 ≤ 3 ^ S.a)
    (e : Homogenization.Vec d) (he : Homogenization.vecNormSq e = 1)
    (delta etaL : ℝ) (hdelta : 0 ≤ delta) (hetaL : 0 ≤ etaL)
    (w : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → Homogenization.H10Function (Homogenization.openCubeSet (Homogenization.originCube d (S.m : ℤ))))
    (hw : ∀ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
      SuperdiffusionCLT.Section3.Setup.IsDirichletResponse
        omega S.LPrime S.ellPrime S.m
        (SuperdiffusionCLT.Section3.Setup.testVector nu S.LPrime P S.n e) (w omega))
    (Cerr : ℝ)
    (hde1 : delta + etaL ≤ 1)
    (hCerr : cgBoundConst (cgBoundAmpP d P S w) (cgBoundAmpW nu S) (bEllipConst d) ≤ Cerr)
    (hPigeon : |1 - (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.LPrime P S.n)⁻¹ *
      SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.LPrime P S.m| ≤ delta + etaL) :
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
  exact term3_cgBound_finalB d hd nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder
    hTwoHLeM hHundredALeH hWindowVsOffset e he delta etaL hdelta hetaL w hw Cerr
    hde1 hCerr
    (hAnnealedSub_of_quenchedResponseValue hnu hPrefix hJ2 hJ4 S
      ((hSorder.n_lt_ell.trans hSorder.ell_lt_ellPrime).trans hSorder.ellPrime_lt_m)
      _ _ (cgFinalC_subValue hnu P S e))
    (hAnnealedBig_of_quenchedResponseValue hnu hJ4 S _ (cgFinalC_bigValue hnu P S e))
    hPigeon

/-- The display `e.RHS.term3.A`, with the annealed
energy identities and the absorbability restriction discharged. -/
theorem term3_cgBound_finalC
    (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (nu : ℝ) (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P) (hJ1V2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P) (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P) (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    (S : SuperdiffusionCLT.Section3.Setup.ScaleSelection) (hSorder : SuperdiffusionCLT.Section3.Setup.ScalesOrdering S)
    (hTwoHLeM : 2 * S.h ≤ S.m) (hHundredALeH : 100 * S.a ≤ S.h)
    (hWindowVsOffset : S.h + 1 ≤ 3 ^ S.a)
    (e : Homogenization.Vec d) (he : Homogenization.vecNormSq e = 1)
    (delta etaL : ℝ) (hdelta : 0 ≤ delta) (hetaL : 0 ≤ etaL)
    (w : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → Homogenization.H10Function (Homogenization.openCubeSet (Homogenization.originCube d (S.m : ℤ))))
    (hw : ∀ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
      SuperdiffusionCLT.Section3.Setup.IsDirichletResponse
        omega S.LPrime S.ellPrime S.m
        (SuperdiffusionCLT.Section3.Setup.testVector nu S.LPrime P S.n e) (w omega))
    (Cerr : ℝ)
    (hCerr : cgBoundConst (cgBoundAmpP d P S w) (cgBoundAmpW nu S) (bEllipConst d) ≤ Cerr)
    (hPigeon : |1 - (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.LPrime P S.n)⁻¹ *
      SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.LPrime P S.m| ≤ delta + etaL) :
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
  have hnm : S.n ≤ S.m :=
    ((hSorder.n_lt_ell.trans hSorder.ell_lt_ellPrime).trans hSorder.ellPrime_lt_m).le
  have hpos := SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq_pos
    hnu S.LPrime hPrefix hJ2 hJ3 hJ4
  have hone : |1 - (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.LPrime P S.n)⁻¹ *
      SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.LPrime P S.m| ≤ 1 :=
    abs_one_sub_inv_mul_le_of_le_mul (hpos S.n)
      (SuperdiffusionCLT.Section2.Annealed.antitone_sigmaBarStarInvSeq
        hnu S.LPrime hPrefix hJ2 hJ3 hJ4 hnm)
      (by simpa only [sub_self, zero_mul] using (hpos S.m).le)
  have hbound := cgFinalC_small d hd nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder
    hTwoHLeM hHundredALeH hWindowVsOffset e he (min (delta + etaL) 1) 0
    (le_min (add_nonneg hdelta hetaL) zero_le_one) le_rfl w hw Cerr
    (by simpa only [add_zero] using min_le_right (delta + etaL) (1 : ℝ)) hCerr
    (by simpa only [add_zero] using le_min hPigeon hone)
  simp only [add_zero, ← Real.sqrt_eq_rpow] at hbound ⊢
  exact hbound.trans (_root_.add_le_add
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (min_le_left (delta + etaL) 1))
      (Real.sqrt_nonneg _)) le_rfl)

end

end SuperdiffusionCLT.Section3.Terms
