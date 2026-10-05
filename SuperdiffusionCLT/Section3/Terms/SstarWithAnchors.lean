/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.RootChainComposedB
public import SuperdiffusionCLT.Section3.Setup.MasterAssembly
public import SuperdiffusionCLT.Section3.Setup.MasterConstSpecD
public import SuperdiffusionCLT.Section3.Terms.SstarWorkBracket
public import SuperdiffusionCLT.Section3.Terms.SstarAnnealedResidue
public import SuperdiffusionCLT.Section3.Setup.MasterWithLHS
public import SuperdiffusionCLT.Frozen.Section3.RHSTerm1
public import SuperdiffusionCLT.Frozen.Section3.RHSTerm2
public import SuperdiffusionCLT.Frozen.Section3.RHSTerm4
public import SuperdiffusionCLT.Frozen.Section2.LocalizationAverage

/-! # The lower-bound composition with the term estimates
This file follows the proof of `p.sstar.lower.bound` (Section 3).
The signed third term and the testing identity remain explicit.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms
open scoped ENNReal

/-- The dimension-only constant of right-hand-side term 1. -/
noncomputable def sstarAnchored_C1 (d : ℕ) [NeZero d] (hd : 2 ≤ d) : ℝ :=
  Classical.choose (SuperdiffusionCLT.Frozen.Section3.rhs_term1 d hd)

/-- The selected constant has the required normalization. -/
theorem sstarAnchored_C1_ge_one (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    1 ≤ sstarAnchored_C1 d hd :=
  (Classical.choose_spec (SuperdiffusionCLT.Frozen.Section3.rhs_term1 d hd)).1

/-- The dimension-only constant of right-hand-side term 2. -/
noncomputable def sstarAnchored_C2 (d : ℕ) [NeZero d] (hd : 2 ≤ d) : ℝ :=
  Classical.choose (SuperdiffusionCLT.Frozen.Section3.rhs_term2 d hd)

/-- The selected constant has the required normalization. -/
theorem sstarAnchored_C2_ge_one (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    1 ≤ sstarAnchored_C2 d hd :=
  (Classical.choose_spec (SuperdiffusionCLT.Frozen.Section3.rhs_term2 d hd)).1

/-- The dimension-only constant of right-hand-side term 4. -/
noncomputable def sstarAnchored_C4 (d : ℕ) [NeZero d] (hd : 2 ≤ d) : ℝ :=
  Classical.choose (SuperdiffusionCLT.Frozen.Section3.rhs_term4_constFirst d hd)

/-- The selected constant has the required normalization. -/
theorem sstarAnchored_C4_ge_one (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    1 ≤ sstarAnchored_C4 d hd :=
  (Classical.choose_spec (SuperdiffusionCLT.Frozen.Section3.rhs_term4_constFirst d hd)).1

/-- Apply LHS and RHS terms one, two and four to the master inequality. -/
theorem sstarAnchored_master {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (C3 Ceta K : ℝ) (hC3 : 0 ≤ C3) (hCeta : 0 ≤ Ceta)
    (hK : (1 : ℝ) ≤ K) (hKlog3 : 8056 ≤ K * Real.log 3)
    (nu : ℝ) (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ1V2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    (cStar Knd delta : ℝ) (hJ5 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar Knd hPrefix hJ2 hJ3)
    (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (S : SuperdiffusionCLT.Section3.Setup.ScaleSelection) (hL : 1 ≤ S.L)
    (hlog1 : (1 : ℝ) ≤ Real.log (nu⁻¹ * (S.L : ℝ)))
    (hord : SuperdiffusionCLT.Section3.Setup.ScalesOrdering S) (hha : 100 * S.a ≤ S.h) (hhm : 2 * S.h ≤ S.m)
    (haeq : S.a = SuperdiffusionCLT.Section3.Setup.scaleOffset K nu S.L)
    (hCT1 : Ceta ≤ nu⁻¹ * (S.L : ℝ))
    (hCT2 : 2 * sstarAnchored_C1 d hd + sstarAnchored_C2 d hd + 4 * (6 * C3) ≤ nu⁻¹ * (S.L : ℝ))
    (e : Homogenization.Vec d) (he : Homogenization.vecNormSq e = 1)
    (p : Homogenization.Vec d) (hp : p = SuperdiffusionCLT.Section3.Setup.testVector nu S.LPrime P S.n e) (q : Homogenization.Vec d)
    (w : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → Homogenization.H10Function (Homogenization.openCubeSet (Homogenization.originCube d (S.m : ℤ))))
    (uMgrad uNGlued : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → Homogenization.Vec d → Homogenization.Vec d)
    (huN : uNGlued = gluedGradientField hnu S.LPrime S.n S.m (SuperdiffusionCLT.Section3.Setup.fluxSlot nu S.LPrime P S.n e))
    (hq : q = qVector hnu P S.LPrime S.ell S.n S.m (SuperdiffusionCLT.Section3.Setup.fluxSlot nu S.LPrime P S.n e))
    (hResponse : ∀ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
      SuperdiffusionCLT.Section3.ResponseFields.IsCubeDirichletResponse (Homogenization.originCube d (S.m : ℤ))
        (fun x => Homogenization.matVecMul (SuperdiffusionCLT.Frozen.Section2.streamCutoff omega S.LPrime x -
          SuperdiffusionCLT.Frozen.Section2.streamCutoff omega S.ellPrime x) p) (w omega))
    (hT3 :
      ∫ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
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
              (3 : ℝ) ^ (-((((S.h : ℕ) : ℝ)) / 16))))
    (hIdentity :
      (∫⁻ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
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
            ∂P.toMeasure) :
    cStar * (S.h : ℝ) * SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.LPrime P S.n ≤
      SuperdiffusionCLT.Section3.Terms.masterConst (SuperdiffusionCLT.Section3.Setup.masterWithLHS_lhsConst d hd) (6 * C3) (sstarAnchored_C4 d hd) (SuperdiffusionCLT.Section3.Setup.crudeLowerConst d) *
          (delta + (S.L : ℝ) ^ (-(1000 : ℝ))) ^ ((1 : ℝ) / 2) *
          (SuperdiffusionCLT.Section2.Annealed.sigmaBarSeq nu S.ell P S.n +
            (S.h : ℝ) * SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.LPrime P S.n) +
        SuperdiffusionCLT.Section3.Terms.masterConst (SuperdiffusionCLT.Section3.Setup.masterWithLHS_lhsConst d hd) (6 * C3) (sstarAnchored_C4 d hd) (SuperdiffusionCLT.Section3.Setup.crudeLowerConst d) *
          (1 + Knd + K * Real.log (nu⁻¹ * (S.L : ℝ))) *
          SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.LPrime P S.n := by
  have hLHS := (Classical.choose_spec
    (SuperdiffusionCLT.Frozen.Section3.l_LHS_term1_constFirst d hd)).2
    nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 cStar Knd hJ5 S hord
    e he (SuperdiffusionCLT.Section3.Setup.masterWithLHS_unitNorm he) p hp
    (fun omega x => Homogenization.matVecMul (SuperdiffusionCLT.Frozen.Section2.streamCutoff omega S.LPrime x -
      SuperdiffusionCLT.Frozen.Section2.streamCutoff omega S.ellPrime x) p) (fun _ => rfl) w hResponse
  have hw : ∀ omega, SuperdiffusionCLT.Section3.Setup.IsDirichletResponse omega S.LPrime S.ellPrime S.m p (w omega) := hResponse
  have hw' : ∀ omega, SuperdiffusionCLT.Section3.Setup.IsDirichletResponse omega S.LPrime S.ellPrime S.m
      (SuperdiffusionCLT.Section3.Setup.testVector nu S.LPrime P S.n e) (w omega) := by simpa only [hp] using hw
  have ht1 := (Classical.choose_spec (SuperdiffusionCLT.Frozen.Section3.rhs_term1 d hd)).2
    nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hord e he w hw' hhm
  have ht2 := (Classical.choose_spec (SuperdiffusionCLT.Frozen.Section3.rhs_term2 d hd)).2
    nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hord e he w hw'
  have ht4 := (Classical.choose_spec (SuperdiffusionCLT.Frozen.Section3.rhs_term4_constFirst d hd)).2
    nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hord e he p hp w hw
  rw [← SuperdiffusionCLT.Section3.Setup.sq_sigmaBarStarInvSqrt hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n] at ht4
  have heta0 := SuperdiffusionCLT.Section3.Setup.localizationEta_nonneg hCeta hnu S.L (2*S.a)
  have ha : K * Real.log (nu⁻¹ * (S.L : ℝ)) ≤ (S.a : ℝ) := by
    rw [haeq]
    exact SuperdiffusionCLT.Section3.Setup.le_scaleOffset K nu S.L
  have heta := SuperdiffusionCLT.Section3.Setup.localizationEta_le hnu hnu1 hL hCeta hCT1 hKlog3 ha
  have hpow : (S.L : ℝ) ^ (-(1000 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hL) (by norm_num)
  have hsum0 : 0 ≤ delta + SuperdiffusionCLT.Section3.Setup.localizationEta Ceta nu S.L (2*S.a) :=
    add_nonneg hdelta heta0
  have hsum4 : delta + SuperdiffusionCLT.Section3.Setup.localizationEta Ceta nu S.L (2*S.a) ≤ 4 := by
    linarith only [hdelta1,heta,hpow]
  have htHalf : (delta + SuperdiffusionCLT.Section3.Setup.localizationEta Ceta nu S.L (2*S.a)) ^ ((1 : ℝ)/2) ≤ 2 := by
    have h := Real.rpow_le_rpow hsum0 hsum4 (by norm_num : (0 : ℝ) ≤ (1 : ℝ)/2)
    have heq : (4 : ℝ) ^ ((1 : ℝ)/2) = 2 := by norm_num [← Real.sqrt_eq_rpow]
    rwa [heq] at h
  have hG16 : (3 : ℝ) ^ (-((S.h : ℝ)/16)) ≤ (3 : ℝ) ^ (-(((S.ellPrime-S.n : ℕ) : ℝ)/2)) := by
    have hpn : ((S.ellPrime-S.n : ℕ) : ℝ) = 2 * (S.a : ℝ) := by
      rw [S.ellPrime_sub_n]
      push_cast
      ring
    have hah : 16 * (S.a : ℝ) ≤ (S.h : ℝ) := by
      exact_mod_cast (show 16 * S.a ≤ S.h by omega)
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    rw [hpn]
    linarith only [hah]
  have hT3coarse := SuperdiffusionCLT.Section3.Setup.termThreeCoarsenArith hC3
    (Real.rpow_nonneg hsum0 ((1 : ℝ)/2)) htHalf (Real.sqrt_nonneg _)
    (Real.rpow_nonneg hnu.le (-(4 : ℝ)))
    (by positivity : (0 : ℝ) ≤ (S.LPrime : ℝ)^4)
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (-(((S.ellPrime-S.n : ℕ) : ℝ)/2)))
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (-(((S.ell-S.n : ℕ) : ℝ)/8)))
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (-(((S.ellPrime-S.ell : ℕ) : ℝ)/4)))
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (-((S.h : ℝ)/8)))
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (-((S.h : ℝ)/16))) hG16 hT3
  apply SuperdiffusionCLT.Section3.Setup.master_inequality_of_selection (SuperdiffusionCLT.Section3.Setup.masterWithLHS_lhsConst d hd)
    (sstarAnchored_C1 d hd) (sstarAnchored_C2 d hd) (6 * C3) (sstarAnchored_C4 d hd) Ceta K
    (SuperdiffusionCLT.Section3.Setup.masterWithLHS_lhsConst_ge_one d hd) (le_trans zero_le_one (sstarAnchored_C1_ge_one d hd))
    (le_trans zero_le_one (sstarAnchored_C2_ge_one d hd)) (mul_nonneg (by norm_num) hC3)
    (le_trans zero_le_one (sstarAnchored_C4_ge_one d hd)) hCeta hK hKlog3
    nu hnu hnu1 P hPrefix hJ2 hJ3 hJ4 cStar Knd delta hJ5.cStar_pos.le hJ5.K_pos.le hdelta
    S hL hlog1 hord hha hhm haeq hCT1 hCT2 e he p hp q w uMgrad uNGlued hLHS
  · simp only [huN, hq]
    exact ht1
  · simp only [huN, hp]
    exact ht2
  · exact hT3coarse
  · exact ht4
  · exact hIdentity

/-- The master coefficient after the four estimates have been supplied. -/
noncomputable def sstarAnchored_CM (d : ℕ) [NeZero d] (hd : 2 ≤ d) (C3 : ℝ) : ℝ :=
  masterConst (SuperdiffusionCLT.Section3.Setup.masterWithLHS_lhsConst d hd)
    (6*C3) (sstarAnchored_C4 d hd) (SuperdiffusionCLT.Section3.Setup.crudeLowerConst d)

/-- The master coefficient has the normalization required by the root. -/
theorem sstarAnchored_CM_ge_one (d : ℕ) [NeZero d] (hd : 2 ≤ d) {C3 : ℝ} (hC3 : 0 ≤ C3) :
    1 ≤ sstarAnchored_CM d hd C3 :=
  one_le_masterConst (SuperdiffusionCLT.Section3.Setup.masterWithLHS_lhsConst_ge_one d hd)
    (mul_nonneg (by norm_num) hC3) (le_trans zero_le_one (sstarAnchored_C4_ge_one d hd))
    (SuperdiffusionCLT.Section3.Setup.crudeLowerConst_pos d)

/-- The localization coefficient supplied by the cutoff-localization estimate. -/
noncomputable def sstarAnchored_Ceta (d : ℕ) [NeZero d] (hd : 2 ≤ d) : ℝ :=
  Homogenization.IndependentSums.gammaMomentConst 1 * sstarCloseCL d hd *
    (SuperdiffusionCLT.Section3.Setup.crudeLowerConst d)⁻¹

/-- Positivity of the supplied localization coefficient. -/
theorem sstarAnchored_Ceta_pos (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    0 < sstarAnchored_Ceta d hd :=
  mul_pos (mul_pos (Homogenization.IndependentSums.gammaMomentConst_pos (σ := (1 : ℝ))
    zero_lt_one) (sstarCloseCL_pos d hd))
    (inv_pos.mpr (SuperdiffusionCLT.Section3.Setup.crudeLowerConst_pos d))

end SuperdiffusionCLT.Section3.Terms
