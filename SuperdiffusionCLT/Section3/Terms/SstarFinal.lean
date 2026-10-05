/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.SstarJoint
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3CgPremise
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3CgFinalE
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3DeltaEtaClose
public import SuperdiffusionCLT.Section3.Setup.DirichletResponseUnique
public import SuperdiffusionCLT.Section3.Setup.RootTestingIdentity

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open scoped ENNReal

/-- The V3 lower bound assembled from the V6 term-three estimate. -/
theorem sstarFinal_main (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hV6 : ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu : ℝ) (hnu : 0 < nu) (_hnu1 : nu ≤ 1)
        (P : MeasureTheory.ProbabilityMeasure
          (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
        (_hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
        (_hJ1V2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P)
        (_hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
        (_hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
        (_hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
        (S : SuperdiffusionCLT.Section3.Setup.ScaleSelection)
        (_hSorder : SuperdiffusionCLT.Section3.Setup.ScalesOrdering S)
        (_hTwoHLeM : 2 * S.h ≤ S.m) (_hHundredALeH : 100 * S.a ≤ S.h)
        (_hWindowVsOffset : S.h + 1 ≤ 3 ^ S.a)
        (_hOffsetLower :
          (8056 / Real.log 3) *
            Real.log (nu⁻¹ * ((S.L : ℕ) : ℝ)) ≤ ((S.a : ℕ) : ℝ))
        (e : Homogenization.Vec d) (_he : Homogenization.vecNormSq e = 1)
        (delta etaL : ℝ) (_hdelta : 0 ≤ delta) (_hetaL : 0 ≤ etaL)
        (_hPigeonScalar :
          SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.L P
              (S.m - 2 * S.h) ≤
            (1 + delta) *
              SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.L P S.m)
        (_hDeltaEtaLeOne : delta + etaL ≤ 1)
        (_hEtaL : C * nu ^ (-(5 : ℝ)) * ((S.L : ℕ) : ℝ) *
          (3 : ℝ) ^ (-(((S.LPrime - S.m : ℕ) : ℝ))) ≤ etaL)
        (w : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d →
          Homogenization.H10Function
            (Homogenization.openCubeSet (Homogenization.originCube d (S.m : ℤ))))
        (_hw : ∀ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
          SuperdiffusionCLT.Section3.Setup.IsDirichletResponse
            omega S.LPrime S.ellPrime S.m
            (SuperdiffusionCLT.Section3.Setup.testVector nu S.LPrime P S.n e)
            (w omega)),
        ∫ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
          Homogenization.volumeAverage
            (Homogenization.openCubeSet (Homogenization.originCube d (S.m : ℤ)))
            (fun y => Homogenization.vecDot ((w omega).toH1Function.grad y)
              (Homogenization.matVecMul
                ((SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega
                    S.LPrime).toCoeffField y)
                (SuperdiffusionCLT.Section3.Terms.gluedGradientField hnu
                    S.LPrime S.m S.m
                    (SuperdiffusionCLT.Section3.Setup.fluxSlot nu S.LPrime P S.n e)
                    omega y -
                  SuperdiffusionCLT.Section3.Terms.gluedGradientField hnu
                    S.LPrime S.n S.m
                    (SuperdiffusionCLT.Section3.Setup.fluxSlot nu S.LPrime P S.n e)
                    omega y))) ∂P.toMeasure ≤
          C * (delta + etaL) ^ ((1 : ℝ) / 2) *
              Real.sqrt (((S.LPrime - S.ell : ℕ) : ℝ) ^ (2 : ℕ) *
                  (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu
                    S.LPrime P S.n) ^ (2 : ℕ) +
                (SuperdiffusionCLT.Section2.Annealed.sigmaBarSeq nu S.ell P S.n) ^
                  (2 : ℕ)) +
            C * (1 + (delta + etaL) ^ ((1 : ℝ) / 2)) * nu ^ (-(4 : ℝ)) *
              (((S.LPrime : ℕ) : ℝ) ^ (4 : ℕ)) *
              ((3 : ℝ) ^ (-((((S.ellPrime - S.n : ℕ) : ℝ)) / 2)) +
                (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 8)) +
                (3 : ℝ) ^ (-((((S.ellPrime - S.ell : ℕ) : ℝ)) / 4)) +
                (3 : ℝ) ^ (-((((S.h : ℕ) : ℝ)) / 16)))) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧
      ∀ (nu cStar K : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : MeasureTheory.ProbabilityMeasure
          (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
          (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
          (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
          (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K
              hPrefix hJ2 hJ3 →
          ∀ L m : ℕ, m ≤ L → L ≤ 2 * m →
            C * cStar ^ (-(3 : ℝ)) *
                (Real.log (3 + nu⁻¹ + cStar⁻¹) ^ 3 *
                    Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹)) +
                  (1 + K) * Real.log (3 + nu⁻¹ + cStar⁻¹ + K)) ≤ (m : ℝ) →
            (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
                  (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ))) ≤
                SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu L P ∧
              c * cStar ^ ((3 : ℝ) / 2) * nu ^ (2 : ℝ) * (m : ℝ) ^ ((1 : ℝ) / 2) *
                    Real.log (nu⁻¹ * (m : ℝ)) ^ (-((9 : ℝ) / 2)) ≤
                SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
                  (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))) ∧
            ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
              Measurable X ∧
              Homogenization.IndependentSums.IsBigO P.toMeasure
                  (Homogenization.IndependentSums.gammaSigma 2) X
                  (C * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-((m : ℝ) / 8))) ∧
                ∀ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
                  Homogenization.MatLoewnerLE
                    (Homogenization.sigmaStarInvCoarse
                      (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))
                      (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu
                          omega L).toCoeffField)
                    ((C * nu ^ (-(2 : ℝ)) * cStar ^ (-((3 : ℝ) / 2)) *
                            (m : ℝ) ^ (-((1 : ℝ) / 2)) *
                            Real.log (nu⁻¹ * (m : ℝ)) ^ ((9 : ℝ) / 2)) •
                        (1 : Homogenization.Mat d) +
                      X omega • (1 : Homogenization.Mat d)) := by
  obtain ⟨C, hC1, hV6'⟩ := hV6
  let Ceta : ℝ := max (sstarAnchored_Ceta d hd) C
  have hC3 : 0 ≤ C := le_trans zero_le_one hC1
  have hCetaLower : sstarAnchored_Ceta d hd ≤ Ceta := by
    exact le_max_left _ _
  have hC_le_Ceta : C ≤ Ceta := by
    exact le_max_right _ _
  refine SuperdiffusionCLT.Section3.Terms.sstarJoint_lower_bound
    d hd C Ceta hC3 hCetaLower ?_
  intro nu cStar Knd hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 hJ5
    CM delta L S hSL _hSh hSa hord htwo hhundred _h10 _hn4 _hmlo _hmhi
    hPigeonScalar hCT4
  let etaL : ℝ := SuperdiffusionCLT.Section3.Setup.localizationEta Ceta nu S.L (2 * S.a)
  have hCM1 : 1 ≤ CM :=
    SuperdiffusionCLT.Section3.Terms.sstarAnchored_CM_ge_one d hd hC3
  have hCM : 0 < CM := lt_of_lt_of_le zero_lt_one hCM1
  have hCeta_pos : 0 < Ceta :=
    lt_of_lt_of_le (SuperdiffusionCLT.Section3.Terms.sstarAnchored_Ceta_pos d hd)
      hCetaLower
  have hCeta0 : 0 ≤ Ceta := hCeta_pos.le
  have hprem : SuperdiffusionCLT.Section3.Terms.CStarLeTwo cStar :=
    SuperdiffusionCLT.Section3.Terms.cStarLeTwo_of_shellLawJ5 hJ5
  have hL2 : 2 ≤ S.L :=
    SuperdiffusionCLT.Section3.Terms.two_le_SL_of_scalesOrdering hord
  have hL1 : 1 ≤ L := by
    rw [← hSL]
    exact le_trans (by norm_num : 1 ≤ 2) hL2
  have hCT4S : 4 * Ceta ≤ nu⁻¹ * (S.L : ℝ) := by
    rw [hSL]
    exact hCT4
  have hnuInv1 : 1 ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
  have hL1S : 1 ≤ S.L := le_trans (by norm_num : 1 ≤ 2) hL2
  have hL1SR : 1 ≤ (S.L : ℝ) := by
    exact_mod_cast hL1S
  have hprod : (1 : ℝ) * 1 ≤ nu⁻¹ * (S.L : ℝ) :=
    mul_le_mul hnuInv1 hL1SR (by norm_num) (by linarith only [hnuInv1])
  have hT1S : (1 : ℝ) ≤ nu⁻¹ * (S.L : ℝ) := by
    simpa only [one_mul] using hprod
  have hlog0S : 0 ≤ Real.log (nu⁻¹ * (S.L : ℝ)) := Real.log_nonneg hT1S
  have hlog0L : 0 ≤ Real.log (nu⁻¹ * (L : ℝ)) := by
    rw [← hSL]
    exact hlog0S
  have hlog3pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hcoef_le_K : (8056 / Real.log 3 : ℝ) ≤
      SuperdiffusionCLT.Section3.Terms.sstarWorkScaleConst := by
    rw [div_le_iff₀ hlog3pos]
    exact SuperdiffusionCLT.Section3.Terms.sstarWorkScaleConst_klog3
  have hOffsetLower :
      (8056 / Real.log 3) * Real.log (nu⁻¹ * ((S.L : ℕ) : ℝ)) ≤
        ((S.a : ℕ) : ℝ) := by
    rw [hSL, hSa]
    calc
      (8056 / Real.log 3) * Real.log (nu⁻¹ * (L : ℝ)) ≤
          SuperdiffusionCLT.Section3.Terms.sstarWorkScaleConst *
            Real.log (nu⁻¹ * (L : ℝ)) :=
        mul_le_mul_of_nonneg_right hcoef_le_K hlog0L
      _ ≤ (SuperdiffusionCLT.Section3.Setup.scaleOffset
            SuperdiffusionCLT.Section3.Terms.sstarWorkScaleConst nu L : ℝ) :=
        SuperdiffusionCLT.Section3.Setup.le_scaleOffset _ _ _
  have hhL : S.h < L := by
    rw [← hSL]
    omega
  have hWindowBound := SuperdiffusionCLT.Section3.Terms.cgFinalE_window_bound
    hnu hnu1 hL1 hhL hlog0L
    SuperdiffusionCLT.Section3.Terms.sstarWorkScaleConst_klog3
  have hWindow : S.h + 1 ≤ 3 ^ S.a := by
    rw [hSa]
    exact hWindowBound
  have hScaleOffsetLower :
      SuperdiffusionCLT.Section3.Terms.sstarWorkScaleConst *
          Real.log (nu⁻¹ * (S.L : ℝ)) ≤ (S.a : ℝ) := by
    rw [hSa, hSL]
    exact SuperdiffusionCLT.Section3.Setup.le_scaleOffset _ _ _
  have hdelta : 0 ≤ delta :=
    SuperdiffusionCLT.Section3.Setup.smallnessParameter_nonneg
      (SuperdiffusionCLT.Section3.Terms.sstarWorkC0_nonneg CM)
  have hEta0 : 0 ≤ etaL :=
    SuperdiffusionCLT.Section3.Setup.localizationEta_nonneg hCeta0 hnu S.L (2 * S.a)
  have hDeltaEta : delta + etaL ≤ 1 :=
    SuperdiffusionCLT.Section3.Terms.deltaEtaL_le_one_of_cStarLeTwo
      hCM1 (SuperdiffusionCLT.Section3.Terms.sstarWorkC0_sqrt_le hCM)
      (SuperdiffusionCLT.Section3.Terms.sstarWorkC0_nonneg CM) hJ5.cStar_pos.le hprem
      hnu hnu1 hL2 hCeta0 hCT4S
      SuperdiffusionCLT.Section3.Terms.sstarWorkScaleConst_klog3
      hScaleOffsetLower
  have hGap : S.LPrime - S.m = 2 * S.a := by
    have h := S.LPrime_eq
    omega
  have hEtaLower : C * nu ^ (-(5 : ℝ)) * ((S.L : ℕ) : ℝ) *
      (3 : ℝ) ^ (-(((S.LPrime - S.m : ℕ) : ℝ))) ≤ etaL := by
    change C * nu ^ (-(5 : ℝ)) * ((S.L : ℕ) : ℝ) *
        (3 : ℝ) ^ (-(((S.LPrime - S.m : ℕ) : ℝ))) ≤
      SuperdiffusionCLT.Section3.Setup.localizationEta Ceta nu S.L (2 * S.a)
    rw [hGap, SuperdiffusionCLT.Section3.Setup.localizationEta]
    have hfactor : (0 : ℝ) ≤ nu ^ (-(5 : ℝ)) * ((S.L : ℕ) : ℝ) *
        (3 : ℝ) ^ (-(((2 * S.a : ℕ) : ℝ))) := by
      positivity
    have hmul := mul_le_mul_of_nonneg_right hC_le_Ceta hfactor
    have hleft : C * nu ^ (-(5 : ℝ)) * ((S.L : ℕ) : ℝ) *
        (3 : ℝ) ^ (-(((2 * S.a : ℕ) : ℝ))) =
      C * (nu ^ (-(5 : ℝ)) * ((S.L : ℕ) : ℝ) *
        (3 : ℝ) ^ (-(((2 * S.a : ℕ) : ℝ)))) := by ring
    have hright : Ceta * nu ^ (-(5 : ℝ)) * ((S.L : ℕ) : ℝ) *
        (3 : ℝ) ^ (-(((2 * S.a : ℕ) : ℝ))) =
      Ceta * (nu ^ (-(5 : ℝ)) * ((S.L : ℕ) : ℝ) *
        (3 : ℝ) ^ (-(((2 * S.a : ℕ) : ℝ)))) := by ring
    rw [hleft, hright]
    exact hmul
  let i : Fin d := ⟨0, by omega⟩
  let e : Homogenization.Vec d := Homogenization.basisVec i
  have he : Homogenization.vecNormSq e = 1 := Homogenization.vecNormSq_basisVec i
  let p := SuperdiffusionCLT.Section3.Setup.testVector nu S.LPrime P S.n e
  obtain ⟨w, hw⟩ :=
    SuperdiffusionCLT.Section3.Setup.exists_dirichletResponse_family
      (LPrime := S.LPrime) (ellPrime := S.ellPrime) (m := S.m) (p := p)
  refine ⟨e, he, w, hw, ?_, ?_⟩
  · exact hV6' nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hord htwo hhundred
      hWindow hOffsetLower e he delta etaL hdelta hEta0 hPigeonScalar hDeltaEta
      hEtaLower w hw
  · exact SuperdiffusionCLT.Section3.Setup.rootTestingId_main hd nu hnu hnu1 P
      hPrefix hJ1V2 hJ2 hJ3 hJ4 S hord e he w hw

end SuperdiffusionCLT.Section3.Terms
