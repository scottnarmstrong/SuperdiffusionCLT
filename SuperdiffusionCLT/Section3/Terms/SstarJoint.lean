/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.SstarWithAnchors
public import SuperdiffusionCLT.Section3.Setup.RootChainAbsorptionC
public import SuperdiffusionCLT.Section3.Setup.RootPigeonThreadedB

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms
open scoped ENNReal

noncomputable def sstarJoint_jointLogTerm (nu cStar K : ℝ) : ℝ :=
  Real.log (3 + nu⁻¹ + cStar⁻¹) ^ 3 *
      Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹)) +
    (1 + K) * Real.log (3 + nu⁻¹ + cStar⁻¹ + K)

/-- The joint threshold bracket dominates the older bracket. -/
private theorem sstarJoint_eLvsNu_le_jointLogTerm {nu cStar K : ℝ}
    (hnu : 0 < nu) (hcStar : 0 < cStar) (hK : 0 ≤ K) :
    SuperdiffusionCLT.Section3.Setup.eLvsNuTerm nu cStar K ≤
      sstarJoint_jointLogTerm nu cStar K := by
  have hcInv := inv_pos.mpr hcStar
  have harg : 3 + nu⁻¹ + K ≤ 3 + nu⁻¹ + cStar⁻¹ + K := by
    linarith only [hcInv]
  have hlog := Real.log_le_log (by positivity) harg
  have hprod := mul_le_mul_of_nonneg_left hlog
    (by linarith only [hK] : (0 : ℝ) ≤ 1 + K)
  change
    Real.log (3 + nu⁻¹ + cStar⁻¹) ^ 3 *
        Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹)) +
      (1 + K) * Real.log (3 + nu⁻¹ + K) ≤
    Real.log (3 + nu⁻¹ + cStar⁻¹) ^ 3 *
        Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹)) +
      (1 + K) * Real.log (3 + nu⁻¹ + cStar⁻¹ + K)
  linarith only [hprod]

/-- Nonnegativity of the joint logarithmic threshold bracket. -/
private theorem sstarJoint_jointLogTerm_nonneg {nu cStar K : ℝ}
    (hnu : 0 < nu) (hcStar : 0 < cStar) (hK : 0 ≤ K) :
    0 ≤ sstarJoint_jointLogTerm nu cStar K := by
  exact (SuperdiffusionCLT.Section3.Setup.eLvsNuTerm_pos hnu hcStar hK).le.trans
    (sstarJoint_eLvsNu_le_jointLogTerm hnu hcStar hK)

/-- Lowering the coefficient preserves a joint-threshold hypothesis. -/
private theorem sstarJoint_joint_threshold_mono {A B nu cStar K : ℝ} {m : ℕ}
    (hAB : A ≤ B)
    (hnu : 0 < nu) (hcStar : 0 < cStar) (hK : 0 ≤ K)
    (hthr : B * cStar ^ (-(3 : ℝ)) * sstarJoint_jointLogTerm nu cStar K ≤ (m : ℝ)) :
    A * cStar ^ (-(3 : ℝ)) * sstarJoint_jointLogTerm nu cStar K ≤ (m : ℝ) := by
  have hterm := sstarJoint_jointLogTerm_nonneg hnu hcStar hK
  have hfactor : 0 ≤ cStar ^ (-(3 : ℝ)) * sstarJoint_jointLogTerm nu cStar K :=
    mul_nonneg (Real.rpow_nonneg hcStar.le _) hterm
  calc
    _ = A * (cStar ^ (-(3 : ℝ)) * sstarJoint_jointLogTerm nu cStar K) := by ring
    _ ≤ B * (cStar ^ (-(3 : ℝ)) * sstarJoint_jointLogTerm nu cStar K) :=
      mul_le_mul_of_nonneg_right hAB hfactor
    _ = B * cStar ^ (-(3 : ℝ)) * sstarJoint_jointLogTerm nu cStar K := by ring
    _ ≤ _ := hthr

/-- The joint threshold also supplies the old mixed-error threshold. -/
private theorem sstarJoint_eL_threshold_of_joint {A B nu cStar K : ℝ} {m : ℕ}
    (hA : 0 ≤ A) (hAB : A ≤ B)
    (hnu : 0 < nu) (hcStar : 0 < cStar) (hK : 0 ≤ K)
    (hthr : B * cStar ^ (-(3 : ℝ)) * sstarJoint_jointLogTerm nu cStar K ≤ (m : ℝ)) :
    A * cStar ^ (-(3 : ℝ)) * SuperdiffusionCLT.Section3.Setup.eLvsNuTerm nu cStar K ≤
      (m : ℝ) := by
  have hE := sstarJoint_eLvsNu_le_jointLogTerm hnu hcStar hK
  have hthrJ := sstarJoint_joint_threshold_mono hAB hnu hcStar hK hthr
  have hfactor : 0 ≤ cStar ^ (-(3 : ℝ)) := Real.rpow_nonneg hcStar.le _
  have hscaled := mul_le_mul_of_nonneg_left hE hfactor
  calc
    _ = A * (cStar ^ (-(3 : ℝ)) * SuperdiffusionCLT.Section3.Setup.eLvsNuTerm nu cStar K) := by ring
    _ ≤ A * (cStar ^ (-(3 : ℝ)) * sstarJoint_jointLogTerm nu cStar K) :=
      mul_le_mul_of_nonneg_left hscaled hA
    _ = A * cStar ^ (-(3 : ℝ)) * sstarJoint_jointLogTerm nu cStar K := by ring
    _ ≤ _ := hthrJ

theorem sstarJoint_quenched (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    {CM CB : ℝ} (hCM : 0 < CM) (hCB : 0 < CB)
    (T C : ℝ)
    (hCbase : sstarCloseBThrConst d hd (sstarCloseConst d CB CM) ≤ C)
    (hCTlarge : 16 * T + 16 ≤ C)
    (hAnnealed : ∀ (nu cStar K : ℝ), 0 < nu → nu ≤ 1 →
      ∀ (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)) (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
        (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P) (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P → SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
        ∀ L m : ℕ, m ≤ L → L ≤ 2 * m →
          T * cStar ^ (-(3 : ℝ)) * sstarJoint_jointLogTerm nu cStar K ≤ (m : ℝ) →
          sstarPackConst d CM CB * cStar ^ ((3 : ℝ) / 2) * nu ^ (2 : ℝ) *
                (m : ℝ) ^ ((1 : ℝ) / 2) *
                Real.log (nu⁻¹ * (m : ℝ)) ^ (-((9 : ℝ) / 2)) ≤
            SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))) :
    ∀ (nu cStar K : ℝ), 0 < nu → nu ≤ 1 →
      ∀ (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)) (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
        (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P) (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P → SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
        ∀ L m : ℕ, m ≤ L → L ≤ 2 * m →
          C * cStar ^ (-(3 : ℝ)) *
              sstarJoint_jointLogTerm nu cStar K ≤ (m : ℝ) →
          ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ, Measurable X ∧
            Homogenization.IndependentSums.IsBigO P.toMeasure (Homogenization.IndependentSums.gammaSigma 2) X
                (C * nu ^ (-(2 : ℝ)) *
                  (3 : ℝ) ^ (-((m : ℝ) / 8))) ∧
            ∀ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
              Homogenization.MatLoewnerLE
                (Homogenization.sigmaStarInvCoarse (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))
                  (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField)
                ((C * nu ^ (-(2 : ℝ)) *
                        cStar ^ (-((3 : ℝ) / 2)) * (m : ℝ) ^ (-((1 : ℝ) / 2)) *
                        Real.log (nu⁻¹ * (m : ℝ)) ^ ((9 : ℝ) / 2)) •
                    (1 : Homogenization.Mat d) + X omega • (1 : Homogenization.Mat d)) := by
  intro nu cStar K hnu hnu1 P hPrefix hJ2 hJ3 hJ1V2 hJ4 hJ5 L m hm hmL2 hthrJOINT
  have hc0pos : (0 : ℝ) < sstarCloseConst d CB CM := sstarCloseConst_pos d hCB hCM
  have hcStar : 0 < cStar := hJ5.cStar_pos
  have hcStar2 : cStar ≤ 2 := hJ5.cStar_le_two
  have hKpos : 0 < K := hJ5.K_pos
  have hB1e8 : (100000000 : ℝ) ≤
      C :=
    (hundred_million_le_sstarCloseBThrConst d hd _).trans hCbase
  have hBpos : (0 : ℝ) < C :=
    lt_of_lt_of_le (by norm_num) hB1e8
  have hB16 : 16 * T + 16 ≤
      C :=
    hCTlarge
  have hthrE := sstarJoint_eL_threshold_of_joint hBpos.le le_rfl
    hnu hcStar hKpos.le hthrJOINT
  have hBCeta : 16 * (Homogenization.IndependentSums.gammaMomentConst 1 * sstarCloseCL d hd *
      (SuperdiffusionCLT.Section3.Setup.crudeLowerConst d)⁻¹) + 1 ≤
      C :=
    (sixteen_mul_Ceta_le_BThrConst d hd _).trans hCbase
  have hm125 : (12500000 : ℝ) ≤ (m : ℝ) :=
    sstarCloseB_scale_le_m hnu hnu1 hcStar hcStar2 hKpos hB1e8 hthrE
  have hm2 : (2 : ℕ) ≤ m := by
    have hcast : (12500000 : ℕ) ≤ m := by exact_mod_cast hm125
    omega
  have hn0pos := sstarCloseB_quenchedInner_log_pos hnu hnu1 hcStar hcStar2 hKpos hB1e8 hthrE
  have hk := sstarCloseB_six_log_le_inner hnu hnu1 hcStar hcStar2 hKpos hB1e8 hthrE hm hmL2
  have hJointInner : T * cStar ^ (-(3 : ℝ)) * sstarJoint_jointLogTerm nu cStar K ≤
      ((SuperdiffusionCLT.Section3.Setup.quenchedInnerScale m : ℕ) : ℝ) := by
    have hJnn := sstarJoint_jointLogTerm_nonneg hnu hcStar hKpos.le
    have hrJ : 0 ≤ cStar ^ (-(3 : ℝ)) * sstarJoint_jointLogTerm nu cStar K :=
      mul_nonneg (Real.rpow_nonneg hcStar.le _) hJnn
    have hthrJ : C * (cStar ^ (-(3 : ℝ)) * sstarJoint_jointLogTerm nu cStar K) ≤ (m : ℝ) := by
      simpa only [mul_assoc] using hthrJOINT
    have hthr16 : T ≤ C / 16 := by linarith only [hB16]
    have h1 := mul_le_mul_of_nonneg_right hthr16 hrJ
    have h3 : (C * (cStar ^ (-(3 : ℝ)) * sstarJoint_jointLogTerm nu cStar K)) / 16 ≤ (m : ℝ) / 16 := by
      have hh := mul_le_mul_of_nonneg_right hthrJ (by norm_num : (0 : ℝ) ≤ 1 / 16)
      linarith only [hh]
    have h4 : (m : ℝ) / 16 ≤ (m : ℝ) / 2 - 1 / 2 := by
      have hm2' : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
      linarith only [hm2']
    have hle : (m : ℝ) / 2 - 1 / 2 ≤
        ((SuperdiffusionCLT.Section3.Setup.quenchedInnerScale m : ℕ) : ℝ) := by
      have hle' : m ≤ 2 * SuperdiffusionCLT.Section3.Setup.quenchedInnerScale m + 1 := by
        simp only [SuperdiffusionCLT.Section3.Setup.quenchedInnerScale]; omega
      have hcast := Nat.cast_le (α := ℝ).2 hle'
      push_cast at hcast
      linarith only [hcast]
    calc
      _ = T * (cStar ^ (-(3 : ℝ)) * sstarJoint_jointLogTerm nu cStar K) := by ring
      _ ≤ (C / 16) * (cStar ^ (-(3 : ℝ)) * sstarJoint_jointLogTerm nu cStar K) := h1
      _ = (C * (cStar ^ (-(3 : ℝ)) * sstarJoint_jointLogTerm nu cStar K)) / 16 := by ring
      _ ≤ (m : ℝ) / 16 := h3
      _ ≤ (m : ℝ) / 2 - 1 / 2 := h4
      _ ≤ ((SuperdiffusionCLT.Section3.Setup.quenchedInnerScale m : ℕ) : ℝ) := hle
  have hcu2 : SuperdiffusionCLT.Section3.Setup.quenchedCutoffScale m ≤ 2 * SuperdiffusionCLT.Section3.Setup.quenchedInnerScale m :=
    le_of_eq (by simp only [SuperdiffusionCLT.Section3.Setup.quenchedCutoffScale])
  have hann := hAnnealed nu cStar K hnu hnu1 P hPrefix hJ2 hJ3 hJ1V2 hJ4 hJ5
      (SuperdiffusionCLT.Section3.Setup.quenchedCutoffScale m) (SuperdiffusionCLT.Section3.Setup.quenchedInnerScale m)
      (SuperdiffusionCLT.Section3.Setup.quenchedInnerScale_le_quenchedCutoffScale m) hcu2 hJointInner
  have hAnn : sstarCloseConst d CB CM * cStar ^ ((3 : ℝ) / 2) * nu ^ (2 : ℝ) *
        ((SuperdiffusionCLT.Section3.Setup.quenchedInnerScale m : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
        Real.log (nu⁻¹ * ((SuperdiffusionCLT.Section3.Setup.quenchedInnerScale m : ℕ) : ℝ)) ^ (-((9 : ℝ) / 2)) ≤
      SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu (SuperdiffusionCLT.Section3.Setup.quenchedCutoffScale m) P
        (Homogenization.cubeSet (Homogenization.originCube d ((SuperdiffusionCLT.Section3.Setup.quenchedInnerScale m : ℕ) : ℤ))) :=
    sstarCloseConst_mul_le_of_packConst_mul_le hCM hCB hCM (le_refl CB) (le_refl CM) hcStar hnu
      (Nat.cast_nonneg (SuperdiffusionCLT.Section3.Setup.quenchedInnerScale m))
      (log_nonneg_inv_mul_nat hnu hnu1 (SuperdiffusionCLT.Section3.Setup.quenchedInnerScale m)) hann
  have hT1 : (1 : ℝ) ≤ SuperdiffusionCLT.Section3.Setup.eLvsNuTerm nu cStar K :=
    sstarCloseB_eLvsNuTerm_ge_one hnu hnu1 hcStar hKpos
  have hCetaExp_pos : (0 : ℝ) < Homogenization.IndependentSums.gammaMomentConst 1 * sstarCloseCL d hd *
      (SuperdiffusionCLT.Section3.Setup.crudeLowerConst d)⁻¹ := by
    have h1 := Homogenization.IndependentSums.gammaMomentConst_pos (σ := (1 : ℝ)) one_pos
    have h2 := sstarCloseCL_pos d hd
    have h3 := SuperdiffusionCLT.Section3.Setup.crudeLowerConst_pos d
    positivity
  have hCT : Homogenization.IndependentSums.gammaMomentConst 1 * sstarCloseCL d hd * (SuperdiffusionCLT.Section3.Setup.crudeLowerConst d)⁻¹ ≤
      nu⁻¹ * (L : ℝ) := by
    have hBU : C *
        (cStar ^ (-(3 : ℝ)) * SuperdiffusionCLT.Section3.Setup.eLvsNuTerm nu cStar K) ≤ (m : ℝ) := by linarith only [hthrE]
    have h8 : (1 / 8 : ℝ) ≤ cStar ^ (-(3 : ℝ)) * SuperdiffusionCLT.Section3.Setup.eLvsNuTerm nu cStar K := by
      have hscale := sstarCloseB_rpow_neg_three_ge hcStar hcStar2
      have h := mul_le_mul hscale hT1 (by norm_num : (0 : ℝ) ≤ 1)
        (by linarith only [hscale])
      linarith only [h]
    have h1 : (16 * (Homogenization.IndependentSums.gammaMomentConst 1 * sstarCloseCL d hd *
        (SuperdiffusionCLT.Section3.Setup.crudeLowerConst d)⁻¹) + 1) * (1 / 8) ≤
        C * (1 / 8) :=
      mul_le_mul_of_nonneg_right hBCeta (by norm_num)
    have h2 : C * (1 / 8) ≤
        C *
          (cStar ^ (-(3 : ℝ)) * SuperdiffusionCLT.Section3.Setup.eLvsNuTerm nu cStar K) :=
      mul_le_mul_of_nonneg_left h8 hBpos.le
    have hCeta_le : Homogenization.IndependentSums.gammaMomentConst 1 * sstarCloseCL d hd *
        (SuperdiffusionCLT.Section3.Setup.crudeLowerConst d)⁻¹ ≤ (m : ℝ) := by
      linarith only [h1, h2, hBU, hCetaExp_pos]
    have hnuinv1 : (1 : ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
    have hmL' : (m : ℝ) ≤ (L : ℝ) := by exact_mod_cast hm
    have hprod : (1 : ℝ) * (m : ℝ) ≤ nu⁻¹ * (L : ℝ) :=
      mul_le_mul hnuinv1 hmL' (by positivity) (by linarith only [hnuinv1])
    linarith only [hCeta_le, hprod]
  exact SuperdiffusionCLT.Section3.Setup.sstar_lower_bound_quenched_of_anchors hnu hnu1 hcStar hc0pos
    (sstarCloseBMixConst_pos d).le ((sstarCloseBMixConst_le_BThrConst d hd _).trans hCbase)
    ((quenchedConst_le_BThrConst d hd _).trans hCbase) hPrefix hJ2 hJ3 hJ4 hm2 hm hn0pos
    (sstarCloseCL_pos d hd) le_rfl hCT hk hAnn
    (sstarCloseCL_anchor d hd nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4)
    (sstarCloseBMixConst_anchor d nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4)

/-- The lower bound at the joint logarithmic threshold, with absorption
proved inside the assembly. -/
theorem sstarJoint_lower_bound (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (C3 Ceta : ℝ) (hC3 : 0 ≤ C3)
    (hCeta_lower : sstarAnchored_Ceta d hd ≤ Ceta)
    (hOpenSelection : ∀
    (nu cStar Knd : ℝ) (hnu : 0 < nu) (_hnu1 : nu ≤ 1)
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (_hJ1 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    (_hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    (_hJ5 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar Knd hPrefix hJ2 hJ3),
      let CM := sstarAnchored_CM d hd C3
      let delta := SuperdiffusionCLT.Section3.Setup.smallnessParameter (sstarWorkC0 CM) cStar
      ∀ (L : ℕ) (S : SuperdiffusionCLT.Section3.Setup.ScaleSelection), S.L = L →
        S.h = SuperdiffusionCLT.Section3.Setup.optimalWindow (sstarWorkEnvelopeConst d) delta nu L →
        S.a = SuperdiffusionCLT.Section3.Setup.scaleOffset sstarWorkScaleConst nu L →
        SuperdiffusionCLT.Section3.Setup.ScalesOrdering S →
        2 * S.h ≤ S.m → 100 * S.a ≤ S.h → 10 ≤ S.h → L / 4 < S.n →
        L / 4 + 2 * S.h ≤ S.m → S.m ≤ L / 2 →
        SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.L P
            (S.m - 2 * S.h) ≤
          (1 + SuperdiffusionCLT.Section3.Setup.smallnessParameter
            (sstarWorkC0 CM) cStar) *
            SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.L P S.m →
        4 * Ceta ≤ nu⁻¹ * (L : ℝ) →
      ∃ (e : Homogenization.Vec d), Homogenization.vecNormSq e = 1 ∧
      ∃ w : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d →
          Homogenization.H10Function (Homogenization.openCubeSet (Homogenization.originCube d (S.m : ℤ))),
      let p := SuperdiffusionCLT.Section3.Setup.testVector nu S.LPrime P S.n e
      let q := qVector hnu P S.LPrime S.ell S.n S.m (SuperdiffusionCLT.Section3.Setup.fluxSlot nu S.LPrime P S.n e)
      let uNGlued := gluedGradientField hnu S.LPrime S.n S.m (SuperdiffusionCLT.Section3.Setup.fluxSlot nu S.LPrime P S.n e)
      let uMgrad := gluedGradientField hnu S.LPrime S.m S.m (SuperdiffusionCLT.Section3.Setup.fluxSlot nu S.LPrime P S.n e)
      (∀ omega, SuperdiffusionCLT.Section3.Setup.IsDirichletResponse omega S.LPrime S.ellPrime S.m p (w omega)) ∧
      (∫ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
          Homogenization.volumeAverage (Homogenization.openCubeSet (Homogenization.originCube d (S.m : ℤ)))
            (fun y => Homogenization.vecDot ((w omega).toH1Function.grad y)
              (Homogenization.matVecMul ((SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega S.LPrime).toCoeffField y)
                (uMgrad omega y - uNGlued omega y))) ∂P.toMeasure ≤
        C3 * (delta + SuperdiffusionCLT.Section3.Setup.localizationEta Ceta nu S.L (2 * S.a)) ^ ((1 : ℝ) / 2) *
            Real.sqrt (((S.LPrime - S.ell : ℕ) : ℝ) ^ (2 : ℕ) *
                (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.LPrime P S.n) ^ (2 : ℕ) +
              (SuperdiffusionCLT.Section2.Annealed.sigmaBarSeq nu S.ell P S.n) ^ (2 : ℕ)) +
          C3 * (1 + (delta + SuperdiffusionCLT.Section3.Setup.localizationEta Ceta nu S.L (2 * S.a)) ^ ((1 : ℝ) / 2)) * nu ^ (-(4 : ℝ)) * (((S.LPrime : ℕ) : ℝ) ^ (4 : ℕ)) *
            ((3 : ℝ) ^ (-((((S.ellPrime - S.n : ℕ) : ℝ)) / 2)) +
              (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 8)) +
              (3 : ℝ) ^ (-((((S.ellPrime - S.ell : ℕ) : ℝ)) / 4)) +
              (3 : ℝ) ^ (-((((S.h : ℕ) : ℝ)) / 16)))) ∧
      ((∫⁻ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
          SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm (Homogenization.originCube d (S.m : ℤ)) 2
            (w omega).toH1Function.grad ^ (2 : ℕ) ∂P.toMeasure : ℝ≥0∞).toReal =
        ((∫ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
              Homogenization.volumeAverage (Homogenization.openCubeSet (Homogenization.originCube d (S.m : ℤ)))
                (fun x => Homogenization.vecDot ((w omega).toH1Function.grad x)
                  (Homogenization.matVecMul ((SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega S.ell).toCoeffField x)
                      (uNGlued omega x) - q)) ∂P.toMeasure +
            ∫ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
              ((SuperdiffusionCLT.Section2.Estimates.Stream.largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
                ∑ z ∈ SuperdiffusionCLT.Section2.Estimates.Stream.largeCubeSubcubes d S.n S.m,
                  Homogenization.volumeAverage (Homogenization.openCubeSet z)
                    (fun y => Homogenization.vecDot ((w omega).toH1Function.grad y)
                      (Homogenization.matVecMul ((SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega S.LPrime).toCoeffField y -
                        (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega S.ell).toCoeffField y)
                        (uNGlued omega y - p))) ∂P.toMeasure) +
            ∫ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
              Homogenization.volumeAverage (Homogenization.openCubeSet (Homogenization.originCube d (S.m : ℤ)))
                (fun y => Homogenization.vecDot ((w omega).toH1Function.grad y)
                  (Homogenization.matVecMul ((SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega S.LPrime).toCoeffField y)
                    (uMgrad omega y - uNGlued omega y))) ∂P.toMeasure) -
          ∫ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
            Homogenization.volumeAverage (Homogenization.openCubeSet (Homogenization.originCube d (S.m : ℤ)))
              (fun y => Homogenization.vecDot p (Homogenization.matVecMul (SuperdiffusionCLT.Frozen.Section2.streamCutoff omega S.ellPrime y -
                  SuperdiffusionCLT.Frozen.Section2.streamCutoff omega S.ell y) ((w omega).toH1Function.grad y)))
            ∂P.toMeasure)) :
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
  let CM := sstarAnchored_CM d hd C3
  let CB := Classical.choose
    (SuperdiffusionCLT.Section3.Setup.rootPig_assembled_of_anchors d)
  have hCeta_pos : 0 < Ceta := lt_of_lt_of_le (sstarAnchored_Ceta_pos d hd) hCeta_lower
  have hCM1 : 1 ≤ CM := sstarAnchored_CM_ge_one d hd hC3
  have hCM : 0 < CM := lt_of_lt_of_le zero_lt_one hCM1
  have hCB : 0 < CB := (Classical.choose_spec
    (SuperdiffusionCLT.Section3.Setup.rootPig_assembled_of_anchors d)).1
  let A := SuperdiffusionCLT.Section3.Setup.optimalWindowConst (sstarWorkEnvelopeConst d)
    (sstarWorkC0 CM)
  have hA : 0 < A := SuperdiffusionCLT.Section3.Setup.optimalWindowConst_pos
    (sstarWorkEnvelopeConst_pos d) (sstarWorkC0_pos hCM)
  have hKs : 0 < sstarWorkScaleConst := lt_of_lt_of_le zero_lt_one one_le_sstarWorkScaleConst
  obtain ⟨CAbs, hCAbs, hAbsorption⟩ :=
    SuperdiffusionCLT.Section3.Setup.rootChainAbsorptionC_full_joint_log_threshold
      hCM hKs hA
  obtain ⟨T8, hT8, hEight⟩ := SuperdiffusionCLT.Section3.Setup.rootChainComposedB_eight_conditions
    CM (sstarWorkEnvelopeConst d) Ceta (2 * sstarAnchored_C1 d hd + sstarAnchored_C2 d hd + 4 * (6*C3))
    sstarWorkScaleConst CB (sstarWorkC0 CM) hCM.le (sstarWorkEnvelopeConst_pos d)
    (le_trans zero_le_one one_le_sstarWorkScaleConst) hCB.le (sstarWorkC0_pos hCM)
  let T := max CAbs T8
  have hT : 1 ≤ T := hCAbs.trans (le_max_left _ _)
  have hAnn : ∀ nu cStar Knd : ℝ, 0 < nu → nu ≤ 1 →
      ∀ (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
        (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
        (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
        (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar Knd hPrefix hJ2 hJ3 →
      ∀ L m : ℕ, m ≤ L → L ≤ 2 * m →
        T * cStar ^ (-(3 : ℝ)) * sstarJoint_jointLogTerm nu cStar Knd ≤ (m : ℝ) →
        sstarPackConst d CM CB * cStar ^ ((3 : ℝ) / 2) * nu ^ (2 : ℝ) *
          (m : ℝ) ^ ((1 : ℝ) / 2) * Real.log (nu⁻¹ * (m : ℝ)) ^ (-((9 : ℝ) / 2)) ≤
        SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
          (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ))) := by
    intro nu cStar Knd hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 L m hm hmL hthr
    have hthr8 := sstarJoint_eL_threshold_of_joint (le_trans zero_le_one hT8)
      (le_max_right CAbs T8)
      hnu hJ5.cStar_pos hJ5.K_pos.le hthr
    have hthrA := sstarJoint_joint_threshold_mono (le_max_left CAbs T8)
      hnu hJ5.cStar_pos hJ5.K_pos.le hthr
    obtain ⟨hL,hlog,hlogC,hwindow,hdepth,hbell,hCT4,hCT⟩ :=
      hEight nu cStar Knd hnu hnu1 hJ5.cStar_pos hJ5.cStar_le_two hJ5.K_pos L m hm hthr8
    have habs := hAbsorption nu cStar Knd hnu hnu1 hJ5.cStar_pos hJ5.cStar_le_two hJ5.K_pos
      L m hm hthrA
    have hscale : Ceta ≤ nu⁻¹ * (L : ℝ) := by linarith only [hCT4,hCeta_pos]
    have hMaster : ∀ S : SuperdiffusionCLT.Section3.Setup.ScaleSelection, S.L = L →
        S.h = SuperdiffusionCLT.Section3.Setup.optimalWindow (sstarWorkEnvelopeConst d)
          (SuperdiffusionCLT.Section3.Setup.smallnessParameter (sstarWorkC0 CM) cStar) nu L →
        S.a = SuperdiffusionCLT.Section3.Setup.scaleOffset sstarWorkScaleConst nu L →
        SuperdiffusionCLT.Section3.Setup.ScalesOrdering S → 2*S.h ≤ S.m → 100*S.a ≤ S.h →
        10 ≤ S.h → L/4 < S.n → L/4+2*S.h ≤ S.m → S.m ≤ L/2 →
        SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.L P
            (S.m - 2 * S.h) ≤
          (1 + SuperdiffusionCLT.Section3.Setup.smallnessParameter
            (sstarWorkC0 CM) cStar) *
            SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.L P S.m →
        cStar * (S.h : ℝ) * SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.LPrime P S.n ≤
          CM * (SuperdiffusionCLT.Section3.Setup.smallnessParameter (sstarWorkC0 CM) cStar +
            (S.L : ℝ) ^ (-(1000 : ℝ))) ^ ((1 : ℝ)/2) *
            (SuperdiffusionCLT.Section2.Annealed.sigmaBarSeq nu S.ell P S.n +
              (S.h : ℝ) * SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.LPrime P S.n) +
          CM * (1 + Knd + sstarWorkScaleConst * Real.log (nu⁻¹ * (S.L : ℝ))) *
            SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.LPrime P S.n := by
      intro S hSL hSh hSa hord hhm hha h10 hn4 hmlow hmhigh hPigeonScalar
      obtain ⟨e,he,w,hw,h3,hi⟩ := hOpenSelection nu cStar Knd hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 hJ5
        L S hSL hSh hSa hord hhm hha h10 hn4 hmlow hmhigh hPigeonScalar hCT4
      apply sstarAnchored_master hd C3 Ceta sstarWorkScaleConst hC3 hCeta_pos.le
        one_le_sstarWorkScaleConst sstarWorkScaleConst_klog3 nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4
        cStar Knd _ hJ5 (mul_nonneg (sstarWorkC0_nonneg CM) (sq_nonneg cStar))
        (SuperdiffusionCLT.Section3.Setup.rootChain_smallness hCM1 hJ5.cStar_pos hJ5.cStar_le_two) S
        (by simpa only [hSL] using hL) (by simpa only [hSL] using (le_trans (by norm_num) hlog))
        hord hha hhm (by simpa only [hSL] using hSa)
        (by simpa only [hSL] using hscale) (by simpa only [hSL] using hCT)
        e he _ rfl _ w _ _ rfl rfl hw h3 hi
    have hCL : 0 < sstarCloseCL d hd := sstarCloseCL_pos d hd
    have hCetaAnchor : Homogenization.IndependentSums.gammaMomentConst 1 *
        sstarCloseCL d hd * (SuperdiffusionCLT.Section3.Setup.crudeLowerConst d)⁻¹ ≤ Ceta := by
      change sstarAnchored_Ceta d hd ≤ Ceta
      exact hCeta_lower
    have hLocAnchor := sstarCloseCL_anchor d hd nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4
    have hres := (Classical.choose_spec
      (SuperdiffusionCLT.Section3.Setup.rootPig_assembled_of_anchors d)).2
      CM (sstarWorkC0 CM) (sstarWorkEnvelopeConst d) sstarWorkScaleConst cStar Knd nu
      (sstarCloseCL d hd) Ceta L P hCM.le (sstarWorkC0_pos hCM)
      (le_sstarWorkEnvelopeConst d) (sstarWorkEnvelopeConst_large d) one_le_sstarWorkScaleConst
      hJ5.cStar_pos hnu hnu1 hL hPrefix hJ1 hJ2 hJ3 hJ4
      (SuperdiffusionCLT.Section3.Setup.rootChain_smallness hCM1 hJ5.cStar_pos hJ5.cStar_le_two)
      hlog hlogC hwindow (sstarWorkC0_sqrt_le hCM) hdepth habs hbell
      hCL hCetaAnchor hscale sstarWorkScaleConst_klog3 hLocAnchor hMaster m hm hmL
    have hmdata := hEight nu cStar Knd hnu hnu1 hJ5.cStar_pos hJ5.cStar_le_two hJ5.K_pos m m le_rfl hthr8
    exact (sstarPackConst_bracket_of_assembled hnu hJ5.cStar_pos
      (Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hmdata.1)) (le_trans (by norm_num) hmdata.2.1) hres.1 hres.2).2
  let c := sstarCloseConst d CB CM
  let C := max (sstarCloseBThrConst d hd c) (16*T+16)
  have hCbase : sstarCloseBThrConst d hd c ≤ C := le_max_left _ _
  have hCTlarge : 16*T+16 ≤ C := le_max_right _ _
  have hTC : T ≤ C := by linarith only [hT,hCTlarge]
  have hCone : 1 ≤ C := (one_le_sstarCloseBThrConst d hd c).trans hCbase
  refine ⟨C, hCone, c,
    sstarCloseConst_pos d hCB hCM, sstarCloseConst_le_half d CB CM, ?_⟩
  intro nu cStar Knd hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 L m hm hmL hthr
  change C * cStar ^ (-(3 : ℝ)) * sstarJoint_jointLogTerm nu cStar Knd ≤ (m : ℝ) at hthr
  have ht := sstarJoint_joint_threshold_mono hTC hnu hJ5.cStar_pos hJ5.K_pos.le hthr
  refine ⟨⟨sigmaBarStarScalar_originCube_le_sigmaBarInfinite_frozen
    hnu hPrefix hJ2 hJ3 hJ4 L m, ?_⟩, ?_⟩
  · exact sstarCloseConst_mul_le_of_packConst_mul_le hCM hCB hCM (le_refl CB) (le_refl CM)
      hJ5.cStar_pos hnu (Nat.cast_nonneg m) (log_nonneg_inv_mul_nat hnu hnu1 m)
      (hAnn nu cStar Knd hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 L m hm hmL ht)
  · exact sstarJoint_quenched d hd hCM hCB T C hCbase hCTlarge hAnn
      nu cStar Knd hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 L m hm hmL hthr

end SuperdiffusionCLT.Section3.Terms
