/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3Statement
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3ConstFirst
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3CgConstant

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms
open MeasureTheory
open Homogenization
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section2.Annealed
open scoped BigOperators ENNReal
noncomputable section
private theorem v6Windowed_rpowEnvelopeT3 {nu L A t kk : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hL : 1 ≤ L) (hk : kk ≤ 4) (hA : 0 ≤ A) (hAL : A ≤ L ^ 2) (ht : 0 ≤ t) : nu ^ (-kk) * A * t ≤ nu ^ (-(4 : ℝ)) * L ^ 4 * t := by
  have hnupow : nu ^ (-kk) ≤ nu ^ (-(4 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hnu hnu1 (by linarith only [hk])
  have hnu4pos : (0 : ℝ) < nu ^ (-(4 : ℝ)) := Real.rpow_pos_of_pos hnu _
  have h0 : (0 : ℝ) ≤ L := le_trans zero_le_one hL
  have hLsq : (1 : ℝ) ≤ L ^ 2 := by nlinarith only [hL, h0, sq_nonneg (L - 1)]
  have hL4 : L ^ 2 ≤ L ^ 4 := by nlinarith only [hLsq, sq_nonneg (L ^ 2 - 1)]
  exact mul_le_mul_of_nonneg_right (mul_le_mul hnupow (hAL.trans hL4) hA hnu4pos.le) ht
private theorem v6Windowed_sqrtRpowThree (x : ℝ) : Real.sqrt ((3 : ℝ) ^ x) = (3 : ℝ) ^ (x / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]; congr 1; ring
private theorem v6Windowed_tripleMulLe {a b c a' b' c' : ℝ} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) (ha'0 : 0 ≤ a') (hb'0 : 0 ≤ b') : a * b * c ≤ a' * b' * c' := by
  exact mul_le_mul (mul_le_mul ha hb hb0 ha'0) hc hc0 (mul_nonneg ha'0 hb'0)

private theorem v6Windowed_envelopeCombineT3 {nu sb sg LL LP hhv W e1 e2 e3 f1 T1 T2 T3 X C1 C2 C3a C3b Cz Cs Cw : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hLP : 1 ≤ LP) (hLL : LL ≤ LP) (hLLnn : 0 ≤ LL) (hhh : hhv ≤ LP) (hhhnn : 0 ≤ hhv) (he1nn
  : 0 ≤ e1) (he2nn : 0 ≤ e2) (he3nn : 0 ≤ e3) (hf1nn : 0 ≤ f1) (hf1e1 : f1 ≤ e1) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hC3a : 0 ≤ C3a) (hC3b : 0 ≤ C3b) (hCz : 0 ≤ Cz) (hCs : 0 ≤ Cs) (hCw : 0 ≤ Cw) (hcrude : sg ≤ nu⁻¹) (hHolder : X ≤ T1 + T2 + T3 + Cz * nu ^ (-(3 : ℝ)) * LP * f1 * W + Cs * nu ^ (-(4 : ℝ)) * LP ^ 4 * e1) (hDisp1 : T1 ≤ C1 * (sb * (LL * sg))) (hDisp2 : T3 ≤ C2 * nu ^ (-(2 : ℝ)) * (hhv * LP) * e2) (hDisp3 : T2 ≤ C3a * (LL ^ 2 * sg ^ 2) + C3b * nu ^ (-(3 : ℝ)) * LL ^ 2 * e3) (hDisp4 : W ≤
  Cw * LL * sg) : X ≤ bLToBhomellConst C1 C2 C3a C3b Cz Cs Cw * (LL ^ 2 * sg ^ 2 + sb ^ 2 + nu ^ (-(4 : ℝ)) * LP ^ 4 * (e1 + e2 + e3)) := by
  have hLPnn : (0 : ℝ) ≤ LP := le_trans zero_le_one hLP
  have hnu4pos : (0 : ℝ) < nu ^ (-(4 : ℝ)) := Real.rpow_pos_of_pos hnu _
  have hnu3pos : (0 : ℝ) < nu ^ (-(3 : ℝ)) := Real.rpow_pos_of_pos hnu _
  set E1 : ℝ := nu ^ (-(4 : ℝ)) * LP ^ 4 * e1 with hE1def
  set E2 : ℝ := nu ^ (-(4 : ℝ)) * LP ^ 4 * e2 with hE2def
  set E3 : ℝ := nu ^ (-(4 : ℝ)) * LP ^ 4 * e3 with hE3def
  have hE1nn : (0 : ℝ) ≤ E1 := by rw [hE1def]; positivity
  have hE2nn : (0 : ℝ) ≤ E2 := by rw [hE2def]; positivity
  have hE3nn : (0 : ℝ) ≤ E3 := by rw [hE3def]; positivity
  have hLL2 : LL ^ 2 ≤ LP ^ 2 := by nlinarith only [hLL, hLLnn, hLPnn]
  have hT1 : T1 ≤ C1 * (sb ^ 2 + LL ^ 2 * sg ^ 2) := by
    refine hDisp1.trans (mul_le_mul_of_nonneg_left ?_ hC1)
    nlinarith only [sq_nonneg (sb - LL * sg), sq_nonneg sb, sq_nonneg (LL * sg)]
  have hT2 : T2 ≤ C3a * (LL ^ 2 * sg ^ 2) + C3b * E3 := by
    refine hDisp3.trans (add_le_add le_rfl ?_)
    have habs : nu ^ (-(3 : ℝ)) * LL ^ 2 * e3 ≤ nu ^ (-(4 : ℝ)) * LP ^ 4 * e3 :=
      v6Windowed_rpowEnvelopeT3 hnu hnu1 hLP (by norm_num) (by positivity) hLL2 he3nn
    rw [show C3b * nu ^ (-(3 : ℝ)) * LL ^ 2 * e3 =
      C3b * (nu ^ (-(3 : ℝ)) * LL ^ 2 * e3) from by ring, hE3def]
    exact mul_le_mul_of_nonneg_left habs hC3b
  have hT3 : T3 ≤ C2 * E2 := by
    refine hDisp2.trans ?_
    have hAL : hhv * LP ≤ LP ^ 2 := by nlinarith only [hhh, hhhnn, hLPnn]
    have habs : nu ^ (-(2 : ℝ)) * (hhv * LP) * e2 ≤ nu ^ (-(4 : ℝ)) * LP ^ 4 * e2 :=
      v6Windowed_rpowEnvelopeT3 hnu hnu1 hLP (by norm_num) (by positivity) hAL he2nn
    rw [show C2 * nu ^ (-(2 : ℝ)) * (hhv * LP) * e2 =
      C2 * (nu ^ (-(2 : ℝ)) * (hhv * LP) * e2) from by ring, hE2def]
    exact mul_le_mul_of_nonneg_left habs hC2
  have hCzCw : (0 : ℝ) ≤ Cz * Cw := mul_nonneg hCz hCw
  have hT4 : Cz * nu ^ (-(3 : ℝ)) * LP * f1 * W ≤ Cz * Cw * E1 := by
    have hcoeff : (0 : ℝ) ≤ Cz * nu ^ (-(3 : ℝ)) * LP * f1 := by positivity
    have hcoeff2 : (0 : ℝ) ≤ Cz * Cw * (nu ^ (-(3 : ℝ)) * (LP * LL) * f1) := by positivity
    have hnuprod : nu ^ (-(3 : ℝ)) * nu⁻¹ = nu ^ (-(4 : ℝ)) := by
      rw [show nu⁻¹ = nu ^ (-(1 : ℝ)) from (Real.rpow_neg_one nu).symm, ← Real.rpow_add hnu]
      norm_num
    have hAL : LP * LL ≤ LP ^ 2 := by nlinarith only [hLL, hLLnn, hLPnn]
    have habs : nu ^ (-(4 : ℝ)) * (LP * LL) * f1 ≤ nu ^ (-(4 : ℝ)) * LP ^ 4 * f1 :=
      v6Windowed_rpowEnvelopeT3 hnu hnu1 hLP (le_refl _) (by positivity) hAL hf1nn
    have habs2 : nu ^ (-(4 : ℝ)) * LP ^ 4 * f1 ≤ E1 := by
      rw [hE1def]
      exact mul_le_mul_of_nonneg_left hf1e1 (by positivity)
    calc Cz * nu ^ (-(3 : ℝ)) * LP * f1 * W
        ≤ Cz * nu ^ (-(3 : ℝ)) * LP * f1 * (Cw * LL * sg) :=
          mul_le_mul_of_nonneg_left hDisp4 hcoeff
      _ = Cz * Cw * (nu ^ (-(3 : ℝ)) * (LP * LL) * f1) * sg := by ring
      _ ≤ Cz * Cw * (nu ^ (-(3 : ℝ)) * (LP * LL) * f1) * nu⁻¹ :=
          mul_le_mul_of_nonneg_left hcrude hcoeff2
      _ = Cz * Cw * (nu ^ (-(4 : ℝ)) * (LP * LL) * f1) := by rw [← hnuprod]; ring
      _ ≤ Cz * Cw * E1 := mul_le_mul_of_nonneg_left (habs.trans habs2) hCzCw
  have hT5 : Cs * nu ^ (-(4 : ℝ)) * LP ^ 4 * e1 = Cs * E1 := by rw [hE1def]; ring
  set Cbh : ℝ := bLToBhomellConst C1 C2 C3a C3b Cz Cs Cw with hCbhdef
  have hCbhval : Cbh = C1 + C3a + C3b + C2 + Cz * Cw + Cs := by rw [hCbhdef, bLToBhomellConst]
  have hq : (0 : ℝ) ≤ LL ^ 2 * sg ^ 2 := by positivity
  have hs2 : (0 : ℝ) ≤ sb ^ 2 := sq_nonneg sb
  have p1 : C1 * sb ^ 2 ≤ Cbh * sb ^ 2 := mul_le_mul_of_nonneg_right
    (by rw [hCbhval]; linarith only [hC2, hC3a, hC3b, hCzCw, hCs]) hs2
  have p2 : (C1 + C3a) * (LL ^ 2 * sg ^ 2) ≤ Cbh * (LL ^ 2 * sg ^ 2) :=
    mul_le_mul_of_nonneg_right
      (by rw [hCbhval]; linarith only [hC2, hC3b, hCzCw, hCs]) hq
  have p3 : (Cz * Cw + Cs) * E1 ≤ Cbh * E1 := mul_le_mul_of_nonneg_right
    (by rw [hCbhval]; linarith only [hC1, hC2, hC3a, hC3b]) hE1nn
  have p4 : C2 * E2 ≤ Cbh * E2 := mul_le_mul_of_nonneg_right
    (by rw [hCbhval]; linarith only [hC1, hC3a, hC3b, hCzCw, hCs]) hE2nn
  have p5 : C3b * E3 ≤ Cbh * E3 := mul_le_mul_of_nonneg_right
    (by rw [hCbhval]; linarith only [hC1, hC2, hC3a, hCzCw, hCs]) hE3nn
  have htarget : Cbh * (LL ^ 2 * sg ^ 2 + sb ^ 2 +
      nu ^ (-(4 : ℝ)) * LP ^ 4 * (e1 + e2 + e3)) =
      Cbh * (LL ^ 2 * sg ^ 2) + Cbh * sb ^ 2 + Cbh * E1 + Cbh * E2 + Cbh * E3 := by
    rw [hE1def, hE2def, hE3def]; ring
  rw [htarget]
  have hyoung1 : C1 * (sb ^ 2 + LL ^ 2 * sg ^ 2) =
      C1 * sb ^ 2 + C1 * (LL ^ 2 * sg ^ 2) := by ring
  linarith only [hHolder, hT1, hT2, hT3, hT4, hT5, p1, p2, p3, p4, p5, hyoung1]
theorem v6Windowed_l_RHS_term3_constFirst (d : ℕ) [NeZero d] (hd : 2 ≤ d) (C0 Cz Cs C1 C2 C3a C3b Cw CB Cerr : ℝ) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hC3a : 0 ≤ C3a) (hC3b : 0 ≤ C3b) (hCz : 0 ≤ Cz) (hCs : 0 ≤ Cs) (hCw : 0 ≤ Cw) : ∃ C : ℝ, 1 ≤ C ∧ ∀ (nu : ℝ) (_hnu : 0 < nu) (_hnu1 : nu ≤ 1) (P : ProbabilityMeasure (ShellSeq d)) (_hPrefix : ShellLawPrefix d P) (_hJ1V2 : ShellLawJ1Restriction d P) (_hJ2 : ShellLawJ2 d P) (_hJ3 : ShellLawJ3 d P) (_hJ4 : ShellLawJ4 d P) (S : ScaleSelection) (_hSorder :
  ScalesOrdering S) (e : Vec d) (_he : vecNormSq e = 1) (p : Vec d) (_hp : p = testVector nu S.LPrime P S.n e) (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ)))) (_hw : ∀ omega : ShellSeq d, IsDirichletResponse omega S.LPrime S.ellPrime S.m p (w omega)) (uMgrad uNGlued : ShellSeq d → Vec d → Vec d) (delta etaL : ℝ) (_hdelta : 0 ≤ delta) (_hetaL : 0 ≤ etaL) (k : ℕ) (bHalfW : ShellSeq d → TriadicCube d → TriadicCube d → ℝ) (bLnorm : ShellSeq d → TriadicCube d → ℝ) (WL2 WL4
  quadMoment devMoment : ℝ) (_hcrude : sigmaBarStarInvSeq nu S.LPrime P S.n ≤ nu⁻¹) (_hF : ∀ omega : ShellSeq d, ∀ R ∈ largeCubeSubcubes d S.n S.m, ∀ i : Fin d, IntegrableOn (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y) (uMgrad omega y - uNGlued omega y) i) (cubeSet R) volume) (_hgF : ∀ omega : ShellSeq d, ∀ R ∈ largeCubeSubcubes d S.n S.m, IntegrableOn (fun y => vecDot ((w omega).toH1Function.grad y) (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
  (uMgrad omega y - uNGlued omega y))) (cubeSet R) volume) (_hosc : Integrable (fun omega : ShellSeq d => ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ * ∑ R ∈ largeCubeSubcubes d S.n S.m, volumeAverage (openCubeSet R) (fun y => vecDot ((w omega).toH1Function.grad y - volumeAverageVec (openCubeSet R) ((w omega).toH1Function.grad)) (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y) (uMgrad omega y - uNGlued omega y)))) P.toMeasure) (_hcg : Integrable (fun omega : ShellSeq d =>
  ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ * ∑ R ∈ largeCubeSubcubes d S.n S.m, vecDot (volumeAverageVec (openCubeSet R) ((w omega).toH1Function.grad)) (volumeAverageVec (openCubeSet R) (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y) (uMgrad omega y - uNGlued omega y)))) P.toMeasure) (_hOscBound : ∫ omega : ShellSeq d, ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ * ∑ R ∈ largeCubeSubcubes d S.n S.m, volumeAverage (openCubeSet R) (fun y => vecDot ((w
  omega).toH1Function.grad y - volumeAverageVec (openCubeSet R) ((w omega).toH1Function.grad)) (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y) (uMgrad omega y - uNGlued omega y))) ∂P.toMeasure ≤ CB * nu ^ (-(3 / 2 : ℝ)) * (delta + etaL) ^ ((1 : ℝ) / 2) * ((S.LPrime : ℕ) : ℝ) ^ ((1 : ℝ) / 2) * (3 : ℝ) ^ (-((((S.ellPrime - S.n : ℕ) : ℝ)) / 2))) (_hCgBound : ∫ omega : ShellSeq d, ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ * ∑ R ∈ largeCubeSubcubes d S.n S.m, vecDot
  (volumeAverageVec (openCubeSet R) ((w omega).toH1Function.grad)) (volumeAverageVec (openCubeSet R) (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y) (uMgrad omega y - uNGlued omega y))) ∂P.toMeasure ≤ (((largeCubeSubcubes d k S.m).card : ℝ)⁻¹ * ∑ z' ∈ largeCubeSubcubes d k S.m, (((descendantsAtDepth z' (k - S.n)).card : ℕ) : ℝ)⁻¹ * ∑ z ∈ descendantsAtDepth z' (k - S.n), ∫ omega : ShellSeq d, bHalfW omega z' z ∂P.toMeasure) ^ ((1 : ℝ) / 2) * (delta + etaL) ^ ((1 : ℝ) /
  2) + Cerr * nu ^ (-(4 : ℝ)) * (((S.LPrime : ℕ) : ℝ) ^ (4 : ℕ)) * (3 : ℝ) ^ (-(((S.ellPrime - S.ell : ℕ) : ℝ) / 4))) (_hbHalfLe : ∀ (omega : ShellSeq d) (z' z : TriadicCube d), bHalfW omega z' z ≤ vecNormSq (volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad)) * bLnorm omega z) (_hbHalfInt : ∀ z' z : TriadicCube d, openCubeSet z' ⊆ openCubeSet (originCube d (S.m : ℤ)) → openCubeSet z ⊆ openCubeSet z' → Integrable (fun omega => bHalfW omega z' z) P.toMeasure) (_hIntB : Integrable
  (fun omega : ShellSeq d => weightedBlockAverage d S.n k S.m ((w omega).toH1Function.grad) (bLnorm omega)) P.toMeasure) (_hHolder : ∫ omega : ShellSeq d, weightedBlockAverage d S.n k S.m ((w omega).toH1Function.grad) (bLnorm omega) ∂P.toMeasure ≤ C0 * ((d : ℝ) * sigmaBarSeq nu S.ell P S.n) * WL2 + C0 * (quadMoment * WL4 ^ ((1 : ℝ) / 2)) + C0 * (devMoment * WL4 ^ ((1 : ℝ) / 2)) + Cz * nu ^ (-(3 : ℝ)) * ((S.LPrime : ℕ) : ℝ) * (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ))) * WL4 ^ ((1 : ℝ) / 2) + Cs * nu
  ^ (-(4 : ℝ)) * ((S.LPrime : ℕ) : ℝ) ^ 4 * (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ)) / 4)) (_hDisp1 : C0 * ((d : ℝ) * sigmaBarSeq nu S.ell P S.n) * WL2 ≤ C1 * (sigmaBarSeq nu S.ell P S.n * (((S.LPrime - S.ell : ℕ) : ℝ) * sigmaBarStarInvSeq nu S.LPrime P S.n))) (_hBlockDev : ShellLawJ1Restriction d P → C0 * (devMoment * WL4 ^ ((1 : ℝ) / 2)) ≤ C2 * nu ^ (-(2 : ℝ)) * (((S.m - S.ellPrime : ℕ) : ℝ) * ((S.LPrime : ℕ) : ℝ)) * (3 : ℝ) ^ (-(2 * (d : ℝ) / ((d : ℝ) + 4) * ((S.ellPrime - S.ell : ℕ) : ℝ)))) (_hDisp3 :
  C0 * (quadMoment * WL4 ^ ((1 : ℝ) / 2)) ≤ C3a * (((S.LPrime - S.ell : ℕ) : ℝ) ^ 2 * sigmaBarStarInvSeq nu S.LPrime P S.n ^ 2) + C3b * nu ^ (-(3 : ℝ)) * ((S.LPrime - S.ell : ℕ) : ℝ) ^ 2 * (3 : ℝ) ^ (-((S.h : ℕ) : ℝ) / 8)) (_hNablaW4 : (∀ omega : ShellSeq d, IsDirichletResponse omega S.LPrime S.ellPrime S.m p (w omega)) → WL4 ^ ((1 : ℝ) / 2) ≤ Cw * ((S.LPrime - S.ell : ℕ) : ℝ) * vecNormSq p), ∫ omega : ShellSeq d, volumeAverage (openCubeSet (originCube d (S.m : ℤ))) (fun y => vecDot ((w
  omega).toH1Function.grad y) (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y) (uMgrad omega y - uNGlued omega y))) ∂P.toMeasure ≤ C * (delta + etaL) ^ ((1 : ℝ) / 2) * Real.sqrt (((S.LPrime - S.ell : ℕ) : ℝ) ^ (2 : ℕ) * (sigmaBarStarInvSeq nu S.LPrime P S.n) ^ (2 : ℕ) + (sigmaBarSeq nu S.ell P S.n) ^ (2 : ℕ)) + C * (1 + (delta + etaL) ^ ((1 : ℝ) / 2)) * nu ^ (-(4 : ℝ)) * (((S.LPrime : ℕ) : ℝ) ^ (4 : ℕ)) * ((3 : ℝ) ^ (-((((S.ellPrime - S.n : ℕ) : ℝ)) / 2)) + (3 : ℝ) ^ (-((((S.ell
  - S.n : ℕ) : ℝ)) / 8)) + (3 : ℝ) ^ (-((((S.ellPrime - S.ell : ℕ) : ℝ)) / 4)) + (3 : ℝ) ^ (-((((S.h : ℕ) : ℝ)) / 16))) := by
  refine ⟨termThreeConst C1 C2 C3a C3b Cz Cs Cw CB Cerr,
    one_le_termThreeConst C1 C2 C3a C3b Cz Cs Cw CB Cerr, ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder ee he p hp w hw
    uMgrad uNGlued delta etaL hdelta hetaL k bHalfW bLnorm
    WL2 WL4 quadMoment devMoment hcrude hF hgF hosc hcg hOscBound hCgBound
    hbHalfLe hbHalfInt hIntB hHolder hDisp1 hBlockDev hDisp3 hNablaW4
  classical
  have hLPnat : 1 ≤ S.LPrime := by have := hSorder.m_lt_LPrime; omega
  have hLP : (1 : ℝ) ≤ ((S.LPrime : ℕ) : ℝ) := by exact_mod_cast hLPnat
  have hLPnn : (0 : ℝ) ≤ ((S.LPrime : ℕ) : ℝ) := le_trans zero_le_one hLP
  have hLL : ((S.LPrime - S.ell : ℕ) : ℝ) ≤ ((S.LPrime : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_le S.LPrime S.ell
  have hhh : ((S.m - S.ellPrime : ℕ) : ℝ) ≤ ((S.LPrime : ℕ) : ℝ) :=
    Nat.cast_le.2 (by have := hSorder.m_lt_LPrime; omega)
  have hpsq : vecNormSq p = sigmaBarStarInvSeq nu S.LPrime P S.n := by
    rw [hp]; exact vecNormSq_testVector hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n he
  have hDisp4 : WL4 ^ ((1 : ℝ) / 2) ≤
      Cw * ((S.LPrime - S.ell : ℕ) : ℝ) * sigmaBarStarInvSeq nu S.LPrime P S.n := by
    have h := hNablaW4 hw; rwa [hpsq] at h
  have hDisp2 : C0 * (devMoment * WL4 ^ ((1 : ℝ) / 2)) ≤
      C2 * nu ^ (-(2 : ℝ)) * (((S.m - S.ellPrime : ℕ) : ℝ) * ((S.LPrime : ℕ) : ℝ)) *
        (3 : ℝ) ^ (-(((S.ellPrime - S.ell : ℕ) : ℝ)) / 2) := by
    refine (hBlockDev hJ1V2).trans ?_
    have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hhalf : (1 : ℝ) / 2 ≤ 2 * (d : ℝ) / ((d : ℝ) + 4) := by
      rw [le_div_iff₀ (by linarith only [hdR] : (0 : ℝ) < (d : ℝ) + 4)]; linarith only [hdR]
    have hE2nn : (0 : ℝ) ≤ ((S.ellPrime - S.ell : ℕ) : ℝ) := Nat.cast_nonneg _
    have hexp : -(2 * (d : ℝ) / ((d : ℝ) + 4) * ((S.ellPrime - S.ell : ℕ) : ℝ)) ≤
        -(((S.ellPrime - S.ell : ℕ) : ℝ)) / 2 := by
      have hstep := mul_le_mul_of_nonneg_right hhalf hE2nn
      linarith only [hstep]
    have hcoeff : (0 : ℝ) ≤ C2 * nu ^ (-(2 : ℝ)) *
        (((S.m - S.ellPrime : ℕ) : ℝ) * ((S.LPrime : ℕ) : ℝ)) := by
      have h1 : (0 : ℝ) < nu ^ (-(2 : ℝ)) := Real.rpow_pos_of_pos hnu _
      exact mul_nonneg (mul_nonneg hC2 h1.le) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexp) hcoeff
  have hIntInner : ∀ z' ∈ largeCubeSubcubes d k S.m, Integrable (fun omega : ShellSeq d =>
      (((descendantsAtDepth z' (k - S.n)).card : ℕ) : ℝ)⁻¹ *
        ∑ z ∈ descendantsAtDepth z' (k - S.n), bHalfW omega z' z) P.toMeasure := fun z' hz' =>
    (MeasureTheory.integrable_finsetSum _ fun z hz =>
      hbHalfInt z' z (openCubeSet_subset_of_mem_descendantsAtDepth hz')
        (openCubeSet_subset_of_mem_descendantsAtDepth hz)).const_mul _
  have hEq : ((largeCubeSubcubes d k S.m).card : ℝ)⁻¹ *
      ∑ z' ∈ largeCubeSubcubes d k S.m,
        (((descendantsAtDepth z' (k - S.n)).card : ℕ) : ℝ)⁻¹ *
          ∑ z ∈ descendantsAtDepth z' (k - S.n),
            ∫ omega : ShellSeq d, bHalfW omega z' z ∂P.toMeasure =
      ∫ omega : ShellSeq d, ((largeCubeSubcubes d k S.m).card : ℝ)⁻¹ *
        ∑ z' ∈ largeCubeSubcubes d k S.m,
          (((descendantsAtDepth z' (k - S.n)).card : ℕ) : ℝ)⁻¹ *
            ∑ z ∈ descendantsAtDepth z' (k - S.n), bHalfW omega z' z ∂P.toMeasure := by
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_finsetSum _ hIntInner]
    refine congrArg (fun t => ((largeCubeSubcubes d k S.m).card : ℝ)⁻¹ * t) ?_
    refine Finset.sum_congr rfl fun z' hz' => ?_
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_finsetSum _ fun z hz =>
        hbHalfInt z' z (openCubeSet_subset_of_mem_descendantsAtDepth hz')
          (openCubeSet_subset_of_mem_descendantsAtDepth hz)]
  have hIntLeft : Integrable (fun omega : ShellSeq d =>
      ((largeCubeSubcubes d k S.m).card : ℝ)⁻¹ *
        ∑ z' ∈ largeCubeSubcubes d k S.m,
          (((descendantsAtDepth z' (k - S.n)).card : ℕ) : ℝ)⁻¹ *
            ∑ z ∈ descendantsAtDepth z' (k - S.n), bHalfW omega z' z) P.toMeasure :=
    (MeasureTheory.integrable_finsetSum _ hIntInner).const_mul _
  have hptw : ∀ omega : ShellSeq d, ((largeCubeSubcubes d k S.m).card : ℝ)⁻¹ *
        ∑ z' ∈ largeCubeSubcubes d k S.m,
          (((descendantsAtDepth z' (k - S.n)).card : ℕ) : ℝ)⁻¹ *
            ∑ z ∈ descendantsAtDepth z' (k - S.n), bHalfW omega z' z ≤
      weightedBlockAverage d S.n k S.m ((w omega).toH1Function.grad) (bLnorm omega) := by
    intro omega
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun z' _ => ?_)
      (inv_nonneg.2 (Nat.cast_nonneg _))
    have hinner : ∑ z ∈ descendantsAtDepth z' (k - S.n), bHalfW omega z' z ≤
        ∑ z ∈ descendantsAtDepth z' (k - S.n),
          vecNormSq (volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad)) *
            bLnorm omega z :=
      Finset.sum_le_sum fun z _ => hbHalfLe omega z' z
    calc (((descendantsAtDepth z' (k - S.n)).card : ℕ) : ℝ)⁻¹ *
          ∑ z ∈ descendantsAtDepth z' (k - S.n), bHalfW omega z' z
        ≤ (((descendantsAtDepth z' (k - S.n)).card : ℕ) : ℝ)⁻¹ *
            ∑ z ∈ descendantsAtDepth z' (k - S.n),
              vecNormSq (volumeAverageVec (openCubeSet z')
                ((w omega).toH1Function.grad)) * bLnorm omega z :=
          mul_le_mul_of_nonneg_left hinner (inv_nonneg.2 (Nat.cast_nonneg _))
      _ = vecNormSq (volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad)) *
            ((((descendantsAtDepth z' (k - S.n)).card : ℕ) : ℝ)⁻¹ *
              ∑ z ∈ descendantsAtDepth z' (k - S.n), bLnorm omega z) := by
          rw [← Finset.mul_sum]; ring
  have hbridge : ((largeCubeSubcubes d k S.m).card : ℝ)⁻¹ *
      ∑ z' ∈ largeCubeSubcubes d k S.m,
        (((descendantsAtDepth z' (k - S.n)).card : ℕ) : ℝ)⁻¹ *
          ∑ z ∈ descendantsAtDepth z' (k - S.n),
            ∫ omega : ShellSeq d, bHalfW omega z' z ∂P.toMeasure ≤
      ∫ omega : ShellSeq d,
        weightedBlockAverage d S.n k S.m ((w omega).toH1Function.grad) (bLnorm omega)
        ∂P.toMeasure := by
    rw [hEq]
    exact MeasureTheory.integral_mono hIntLeft hIntB hptw
  have he1nn : (0 : ℝ) ≤ (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ)) / 4) :=
    Real.rpow_nonneg zero_le_three _
  have he2nn : (0 : ℝ) ≤ (3 : ℝ) ^ (-(((S.ellPrime - S.ell : ℕ) : ℝ)) / 2) :=
    Real.rpow_nonneg zero_le_three _
  have he3nn : (0 : ℝ) ≤ (3 : ℝ) ^ (-((S.h : ℕ) : ℝ) / 8) := Real.rpow_nonneg zero_le_three _
  have hf1nn : (0 : ℝ) ≤ (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ))) :=
    Real.rpow_nonneg zero_le_three _
  have hf1e1 : (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ))) ≤
      (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ)) / 4) := by
    have hnn : (0 : ℝ) ≤ ((S.ell - S.n : ℕ) : ℝ) := Nat.cast_nonneg _
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) (by linarith only [hnn])
  have hLLnn : (0 : ℝ) ≤ ((S.LPrime - S.ell : ℕ) : ℝ) := Nat.cast_nonneg _
  have hhhnn : (0 : ℝ) ≤ ((S.m - S.ellPrime : ℕ) : ℝ) := Nat.cast_nonneg _
  have hMom := hbridge.trans (v6Windowed_envelopeCombineT3 hnu hnu1 hLP hLL hLLnn hhh hhhnn
    he1nn he2nn he3nn hf1nn hf1e1 hC1 hC2 hC3a hC3b hCz hCs hCw hcrude
    hHolder hDisp1 hDisp2 hDisp3 hDisp4)
  have hsplit := additivity_defect_splitting nu P S w uMgrad uNGlued hF hgF hosc hcg
  set G : ℝ := (3 : ℝ) ^ (-((((S.ellPrime - S.n : ℕ) : ℝ)) / 2)) +
      (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 8)) +
      (3 : ℝ) ^ (-((((S.ellPrime - S.ell : ℕ) : ℝ)) / 4)) +
      (3 : ℝ) ^ (-((((S.h : ℕ) : ℝ)) / 16)) with hGdef
  set EnvG : ℝ := nu ^ (-(4 : ℝ)) * ((S.LPrime : ℕ) : ℝ) ^ (4 : ℕ) * G with hEnvdef
  set BM : ℝ := ((largeCubeSubcubes d k S.m).card : ℝ)⁻¹ *
      ∑ z' ∈ largeCubeSubcubes d k S.m,
        (((descendantsAtDepth z' (k - S.n)).card : ℕ) : ℝ)⁻¹ *
          ∑ z ∈ descendantsAtDepth z' (k - S.n),
            ∫ omega : ShellSeq d, bHalfW omega z' z ∂P.toMeasure with hBMdef
  set dq : ℝ := (delta + etaL) ^ ((1 : ℝ) / 2) with hdqdef
  have hdqnn : (0 : ℝ) ≤ dq := by
    rw [hdqdef]; exact Real.rpow_nonneg (add_nonneg hdelta hetaL) _
  set Qv : ℝ := ((S.LPrime - S.ell : ℕ) : ℝ) ^ 2 *
      sigmaBarStarInvSeq nu S.LPrime P S.n ^ 2 + sigmaBarSeq nu S.ell P S.n ^ 2 with hQdef
  set PRv : ℝ := nu ^ (-(4 : ℝ)) * ((S.LPrime : ℕ) : ℝ) ^ 4 *
      ((3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ)) / 4) +
        (3 : ℝ) ^ (-(((S.ellPrime - S.ell : ℕ) : ℝ)) / 2) +
        (3 : ℝ) ^ (-((S.h : ℕ) : ℝ) / 8)) with hPRdef
  have hCbh0nn : (0 : ℝ) ≤ bLToBhomellConst C1 C2 C3a C3b Cz Cs Cw :=
    bLToBhomellConst_nonneg hC1 hC2 hC3a hC3b hCz hCs hCw
  have hnu4pos : (0 : ℝ) < nu ^ (-(4 : ℝ)) := Real.rpow_pos_of_pos hnu _
  have hQnn : (0 : ℝ) ≤ Qv := by
    rw [hQdef]; exact add_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
  have hPRnn : (0 : ℝ) ≤ PRv := by
    rw [hPRdef]
    exact mul_nonneg (mul_nonneg hnu4pos.le (pow_nonneg (Nat.cast_nonneg _) 4))
      (by linarith only [he1nn, he2nn, he3nn])
  have hMomRoot : BM ^ ((1 : ℝ) / 2) ≤
      Real.sqrt (bLToBhomellConst C1 C2 C3a C3b Cz Cs Cw) *
        (Real.sqrt Qv + Real.sqrt PRv) := by
    rw [← Real.sqrt_eq_rpow]; refine (Real.sqrt_le_sqrt hMom).trans ?_
    rw [Real.sqrt_mul hCbh0nn]
    exact mul_le_mul_of_nonneg_left (sqrt_add_le_add_sqrt hQnn hPRnn) (Real.sqrt_nonneg _)
  have hg1nn : (0 : ℝ) ≤ (3 : ℝ) ^ (-((((S.ellPrime - S.n : ℕ) : ℝ)) / 2)) :=
    Real.rpow_nonneg zero_le_three _
  have hg2nn : (0 : ℝ) ≤ (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 8)) :=
    Real.rpow_nonneg zero_le_three _
  have hg3nn : (0 : ℝ) ≤ (3 : ℝ) ^ (-((((S.ellPrime - S.ell : ℕ) : ℝ)) / 4)) :=
    Real.rpow_nonneg zero_le_three _
  have hg4nn : (0 : ℝ) ≤ (3 : ℝ) ^ (-((((S.h : ℕ) : ℝ)) / 16)) :=
    Real.rpow_nonneg zero_le_three _
  have hGnn : (0 : ℝ) ≤ G := by rw [hGdef]; linarith only [hg1nn, hg2nn, hg3nn, hg4nn]
  have hEnvnn : (0 : ℝ) ≤ EnvG := by
    rw [hEnvdef]; exact mul_nonneg (mul_nonneg hnu4pos.le (pow_nonneg (Nat.cast_nonneg _) 4)) hGnn
  have hbase2 : (0 : ℝ) ≤ nu ^ (-(2 : ℝ)) * ((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ) :=
    mul_nonneg (Real.rpow_nonneg hnu.le _) (sq_nonneg _)
  have hPRroot : Real.sqrt PRv ≤ nu ^ (-(2 : ℝ)) * ((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ) *
      ((3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 8)) +
        (3 : ℝ) ^ (-((((S.ellPrime - S.ell : ℕ) : ℝ)) / 4)) +
        (3 : ℝ) ^ (-((((S.h : ℕ) : ℝ)) / 16))) := by
    have h1 : (nu ^ (-(2 : ℝ))) ^ (2 : ℕ) = nu ^ (-(4 : ℝ)) := by
      rw [← Real.rpow_natCast (nu ^ (-(2 : ℝ))) 2, ← Real.rpow_mul hnu.le]
      norm_num
    have hfac : nu ^ (-(4 : ℝ)) * ((S.LPrime : ℕ) : ℝ) ^ 4 =
        (nu ^ (-(2 : ℝ)) * ((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ)) ^ (2 : ℕ) := by
      calc nu ^ (-(4 : ℝ)) * ((S.LPrime : ℕ) : ℝ) ^ 4
          = (nu ^ (-(2 : ℝ))) ^ (2 : ℕ) *
            (((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ)) ^ (2 : ℕ) := by rw [h1]; ring
        _ = (nu ^ (-(2 : ℝ)) * ((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
    rw [hPRdef, hfac, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hbase2]
    refine mul_le_mul_of_nonneg_left ?_ hbase2
    calc Real.sqrt ((3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ)) / 4) +
          (3 : ℝ) ^ (-(((S.ellPrime - S.ell : ℕ) : ℝ)) / 2) +
          (3 : ℝ) ^ (-((S.h : ℕ) : ℝ) / 8))
        ≤ Real.sqrt ((3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ)) / 4) +
              (3 : ℝ) ^ (-(((S.ellPrime - S.ell : ℕ) : ℝ)) / 2)) +
            Real.sqrt ((3 : ℝ) ^ (-((S.h : ℕ) : ℝ) / 8)) :=
          sqrt_add_le_add_sqrt (by linarith only [he1nn, he2nn]) he3nn
      _ ≤ Real.sqrt ((3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ)) / 4)) +
            Real.sqrt ((3 : ℝ) ^ (-(((S.ellPrime - S.ell : ℕ) : ℝ)) / 2)) +
            Real.sqrt ((3 : ℝ) ^ (-((S.h : ℕ) : ℝ) / 8)) := by
          have hstep := sqrt_add_le_add_sqrt he1nn he2nn
          linarith only [hstep]
      _ = (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 8)) +
            (3 : ℝ) ^ (-((((S.ellPrime - S.ell : ℕ) : ℝ)) / 4)) +
            (3 : ℝ) ^ (-((((S.h : ℕ) : ℝ)) / 16)) := by
          rw [v6Windowed_sqrtRpowThree, v6Windowed_sqrtRpowThree, v6Windowed_sqrtRpowThree]
          congr 3 <;> ring
  have hnu2le : nu ^ (-(2 : ℝ)) ≤ nu ^ (-(4 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hnu hnu1 (by norm_num)
  have hnu32le : nu ^ (-(3 / 2 : ℝ)) ≤ nu ^ (-(4 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hnu hnu1 (by norm_num)
  have hnu52le : nu ^ (-(5 : ℝ) / 2) ≤ nu ^ (-(4 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hnu hnu1 (by norm_num)
  have hLPsq : (1 : ℝ) ≤ ((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ) := by
    nlinarith only [hLP, hLPnn, sq_nonneg (((S.LPrime : ℕ) : ℝ) - 1)]
  have hLP24 : ((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ) ≤ ((S.LPrime : ℕ) : ℝ) ^ (4 : ℕ) := by
    nlinarith only [hLPsq, sq_nonneg (((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ) - 1)]
  have hLPhalf : ((S.LPrime : ℕ) : ℝ) ^ ((1 : ℝ) / 2) ≤ ((S.LPrime : ℕ) : ℝ) ^ (4 : ℕ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hLP (by norm_num : (1 : ℝ) / 2 ≤ (4 : ℝ))
    have hcast : ((S.LPrime : ℕ) : ℝ) ^ (4 : ℝ) = ((S.LPrime : ℕ) : ℝ) ^ (4 : ℕ) := by
      rw [← Real.rpow_natCast (((S.LPrime : ℕ) : ℝ)) 4]; norm_num
    rwa [hcast] at h
  have hg1le : (3 : ℝ) ^ (-((((S.ellPrime - S.n : ℕ) : ℝ)) / 2)) ≤ G := by
    rw [hGdef]; linarith only [hg2nn, hg3nn, hg4nn]
  have hg3le : (3 : ℝ) ^ (-(((S.ellPrime - S.ell : ℕ) : ℝ) / 4)) ≤ G := by
    rw [hGdef]; linarith only [hg1nn, hg2nn, hg4nn]
  have hPRle : Real.sqrt PRv ≤ EnvG := by
    refine hPRroot.trans ?_
    rw [hEnvdef]
    exact v6Windowed_tripleMulLe hnu2le hLP24 (by rw [hGdef]; linarith only [hg1nn])
      (pow_nonneg (Nat.cast_nonneg _) _) (by linarith only [hg2nn, hg3nn, hg4nn])
      (Real.rpow_nonneg hnu.le _) (pow_nonneg (Nat.cast_nonneg _) _)
  have hCG := hCgBound.trans (show BM ^ ((1 : ℝ) / 2) * dq +
      Cerr * nu ^ (-(4 : ℝ)) * (((S.LPrime : ℕ) : ℝ) ^ (4 : ℕ)) * (3 : ℝ) ^ (-(((S.ellPrime - S.ell : ℕ) : ℝ) / 4)) ≤
      Real.sqrt (bLToBhomellConst C1 C2 C3a C3b Cz Cs Cw) * dq * Real.sqrt Qv +
        (Real.sqrt (bLToBhomellConst C1 C2 C3a C3b Cz Cs Cw) * Real.sqrt PRv * dq +
          Cerr * nu ^ (-(4 : ℝ)) * (((S.LPrime : ℕ) : ℝ) ^ (4 : ℕ)) * (3 : ℝ) ^ (-(((S.ellPrime - S.ell : ℕ) : ℝ) / 4))) from by
    have h1 := mul_le_mul_of_nonneg_right hMomRoot hdqnn
    have hring : Real.sqrt (bLToBhomellConst C1 C2 C3a C3b Cz Cs Cw) *
        (Real.sqrt Qv + Real.sqrt PRv) * dq =
        Real.sqrt (bLToBhomellConst C1 C2 C3a C3b Cz Cs Cw) * dq * Real.sqrt Qv +
          Real.sqrt (bLToBhomellConst C1 C2 C3a C3b Cz Cs Cw) * Real.sqrt PRv * dq := by ring
    linarith only [h1, hring])
  set MM : ℝ := max 1 (max (Real.sqrt (bLToBhomellConst C1 C2 C3a C3b Cz Cs Cw))
    (max CB Cerr)) with hMMdef
  have hMM1 : (1 : ℝ) ≤ MM := by rw [hMMdef]; exact le_max_left _ _
  have hMMnn : (0 : ℝ) ≤ MM := le_trans zero_le_one hMM1
  have hCbhMM : Real.sqrt (bLToBhomellConst C1 C2 C3a C3b Cz Cs Cw) ≤ MM := by
    rw [hMMdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hCBMM : CB ≤ MM := by
    rw [hMMdef]; exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hCerrMM : Cerr ≤ MM := by
    rw [hMMdef]; exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  have hb1 : Real.sqrt (bLToBhomellConst C1 C2 C3a C3b Cz Cs Cw) * dq * Real.sqrt Qv ≤
      MM * dq * Real.sqrt Qv :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCbhMM hdqnn)
      (Real.sqrt_nonneg _)
  have hb2 : Real.sqrt (bLToBhomellConst C1 C2 C3a C3b Cz Cs Cw) * Real.sqrt PRv * dq ≤
      MM * dq * EnvG := by
    have h := mul_le_mul hCbhMM hPRle (Real.sqrt_nonneg PRv) hMMnn
    calc Real.sqrt (bLToBhomellConst C1 C2 C3a C3b Cz Cs Cw) * Real.sqrt PRv * dq
        ≤ MM * EnvG * dq := mul_le_mul_of_nonneg_right h hdqnn
      _ = MM * dq * EnvG := by ring
  have hb3 : Cerr * nu ^ (-(4 : ℝ)) * (((S.LPrime : ℕ) : ℝ) ^ (4 : ℕ)) *
      (3 : ℝ) ^ (-(((S.ellPrime - S.ell : ℕ) : ℝ) / 4)) ≤ MM * EnvG := by
    have hrate : (3 : ℝ) ^ (-(((S.ellPrime - S.ell : ℕ) : ℝ) / 4)) ≤ G := by
      rw [hGdef]
      linarith only [hg1nn, hg2nn, hg4nn]
    have hrate0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(((S.ellPrime - S.ell : ℕ) : ℝ) / 4)) :=
      Real.rpow_nonneg zero_le_three _
    have hcg : Cerr * (3 : ℝ) ^ (-(((S.ellPrime - S.ell : ℕ) : ℝ) / 4)) ≤ MM * G :=
      mul_le_mul hCerrMM hrate hrate0 hMMnn
    calc Cerr * nu ^ (-(4 : ℝ)) * (((S.LPrime : ℕ) : ℝ) ^ (4 : ℕ)) *
          (3 : ℝ) ^ (-(((S.ellPrime - S.ell : ℕ) : ℝ) / 4))
        = (Cerr * (3 : ℝ) ^ (-(((S.ellPrime - S.ell : ℕ) : ℝ) / 4))) *
            (nu ^ (-(4 : ℝ)) * ((S.LPrime : ℕ) : ℝ) ^ (4 : ℕ)) := by ring
      _ ≤ (MM * G) * (nu ^ (-(4 : ℝ)) * ((S.LPrime : ℕ) : ℝ) ^ (4 : ℕ)) :=
        mul_le_mul_of_nonneg_right hcg (mul_nonneg hnu4pos.le (pow_nonneg (Nat.cast_nonneg _) _))
      _ = MM * EnvG := by rw [hEnvdef]; ring
  have hOsc2 := hOscBound.trans (show CB * nu ^ (-(3 / 2 : ℝ)) * dq *
      ((S.LPrime : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
      (3 : ℝ) ^ (-((((S.ellPrime - S.n : ℕ) : ℝ)) / 2)) ≤ MM * dq * EnvG from by
    have hA : nu ^ (-(3 / 2 : ℝ)) * ((S.LPrime : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
        (3 : ℝ) ^ (-((((S.ellPrime - S.n : ℕ) : ℝ)) / 2)) ≤ EnvG := by
      rw [hEnvdef]
      exact v6Windowed_tripleMulLe hnu32le hLPhalf hg1le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (Real.rpow_nonneg zero_le_three _) (Real.rpow_nonneg hnu.le _)
        (pow_nonneg (Nat.cast_nonneg _) _)
    calc CB * nu ^ (-(3 / 2 : ℝ)) * dq * ((S.LPrime : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
          (3 : ℝ) ^ (-((((S.ellPrime - S.n : ℕ) : ℝ)) / 2))
        = CB * dq * (nu ^ (-(3 / 2 : ℝ)) * ((S.LPrime : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
            (3 : ℝ) ^ (-((((S.ellPrime - S.n : ℕ) : ℝ)) / 2))) := by ring
      _ ≤ MM * dq * EnvG := mul_le_mul (mul_le_mul_of_nonneg_right hCBMM hdqnn) hA
            (mul_nonneg (mul_nonneg (Real.rpow_nonneg hnu.le _)
              (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (Real.rpow_nonneg zero_le_three _))
            (mul_nonneg hMMnn hdqnn))
  have hCeq : termThreeConst C1 C2 C3a C3b Cz Cs Cw CB Cerr = 2 * MM := by
    rw [hMMdef, termThreeConst]
  have hgoal : 2 * MM * (1 + dq) * nu ^ (-(4 : ℝ)) * (((S.LPrime : ℕ) : ℝ) ^ (4 : ℕ)) * G =
      2 * (MM * EnvG) + 2 * (MM * dq * EnvG) := by rw [hEnvdef]; ring
  have hslack1 : (0 : ℝ) ≤ MM * dq * Real.sqrt Qv :=
    mul_nonneg (mul_nonneg hMMnn hdqnn) (Real.sqrt_nonneg _)
  have hslack2 : (0 : ℝ) ≤ MM * EnvG := mul_nonneg hMMnn hEnvnn
  rw [hCeq, hsplit]
  linarith only [hOsc2, hCG, hb1, hb2, hb3, hslack1, hslack2, hgoal]
theorem v6Windowed_printedSlot_of_estimates (d : ℕ) [NeZero d] (hd : 2 ≤ d) (CB Cerr : ℝ) : ∃ C : ℝ, 1 ≤ C ∧ ∀ (nu : ℝ) (hnu : 0 < nu) (_hnu1 : nu ≤ 1) (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)) (_hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P) (_hJ1V2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P) (_hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P) (_hJ3 :
  SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P) (_hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P) (S : SuperdiffusionCLT.Section3.Setup.ScaleSelection) (_hSorder : SuperdiffusionCLT.Section3.Setup.ScalesOrdering S) (_hTwoHLeM : 2 * S.h ≤ S.m) (_hHundredALeH : 100 * S.a ≤ S.h) (_hWindowVsOffset : S.h + 1 ≤ 3 ^ S.a) (e : Homogenization.Vec d) (_he : Homogenization.vecNormSq e = 1) (delta etaL : ℝ) (_hdelta : 0 ≤ delta) (_hetaL : 0 ≤ etaL) (w :
  SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → Homogenization.H10Function (Homogenization.openCubeSet (Homogenization.originCube d (S.m : ℤ)))) (_hw : ∀ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d, SuperdiffusionCLT.Section3.Setup.IsDirichletResponse omega S.LPrime S.ellPrime S.m (SuperdiffusionCLT.Section3.Setup.testVector nu S.LPrime P S.n e) (w omega)) (_hPigRatio : SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.LPrime P (S.m - 2 * S.h) ≤ 4 *
  SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.LPrime P S.n) (_hOscBound : ∫ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d, ((SuperdiffusionCLT.Section2.Estimates.Stream.largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ * ∑ R ∈ SuperdiffusionCLT.Section2.Estimates.Stream.largeCubeSubcubes d S.n S.m, Homogenization.volumeAverage (Homogenization.openCubeSet R) (fun y => Homogenization.vecDot ((w omega).toH1Function.grad y - Homogenization.volumeAverageVec
  (Homogenization.openCubeSet R) ((w omega).toH1Function.grad)) (Homogenization.matVecMul ((SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega S.LPrime).toCoeffField y) (gluedGradientField hnu S.LPrime S.m S.m (SuperdiffusionCLT.Section3.Setup.fluxSlot nu S.LPrime P S.n e) omega y - gluedGradientField hnu S.LPrime S.n S.m (SuperdiffusionCLT.Section3.Setup.fluxSlot nu S.LPrime P S.n e) omega y))) ∂P.toMeasure ≤ CB * nu ^ (-(3 / 2 : ℝ)) * (delta + etaL) ^ ((1 : ℝ) / 2) *
  ((S.LPrime : ℕ) : ℝ) ^ ((1 : ℝ) / 2) * (3 : ℝ) ^ (-((((S.ellPrime - S.n : ℕ) : ℝ)) / 2))) (_hCgBound : ∫ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d, ((SuperdiffusionCLT.Section2.Estimates.Stream.largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ * ∑ R ∈ SuperdiffusionCLT.Section2.Estimates.Stream.largeCubeSubcubes d S.n S.m, Homogenization.vecDot (Homogenization.volumeAverageVec (Homogenization.openCubeSet R) ((w omega).toH1Function.grad)) (Homogenization.volumeAverageVec
  (Homogenization.openCubeSet R) (fun y => Homogenization.matVecMul ((SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega S.LPrime).toCoeffField y) (gluedGradientField hnu S.LPrime S.m S.m (SuperdiffusionCLT.Section3.Setup.fluxSlot nu S.LPrime P S.n e) omega y - gluedGradientField hnu S.LPrime S.n S.m (SuperdiffusionCLT.Section3.Setup.fluxSlot nu S.LPrime P S.n e) omega y))) ∂P.toMeasure ≤ (((SuperdiffusionCLT.Section2.Estimates.Stream.largeCubeSubcubes d
  (coarseBlockScale d S) S.m).card : ℝ)⁻¹ * ∑ z' ∈ SuperdiffusionCLT.Section2.Estimates.Stream.largeCubeSubcubes d (coarseBlockScale d S) S.m, (((Homogenization.descendantsAtDepth z' (coarseBlockScale d S - S.n)).card : ℕ) : ℝ)⁻¹ * ∑ z ∈ Homogenization.descendantsAtDepth z' (coarseBlockScale d S - S.n), ∫ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d, translatedBlockHalfWeight nu S.LPrime w omega z' z ∂P.toMeasure) ^ ((1 : ℝ) / 2) * (delta + etaL) ^ ((1 : ℝ) / 2) + Cerr * nu ^
  (-(4 : ℝ)) * (((S.LPrime : ℕ) : ℝ) ^ (4 : ℕ)) * (3 : ℝ) ^ (-(((S.ellPrime - S.ell : ℕ) : ℝ) / 4))), ∫ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d, Homogenization.volumeAverage (Homogenization.openCubeSet (Homogenization.originCube d (S.m : ℤ))) (fun y => Homogenization.vecDot ((w omega).toH1Function.grad y) (Homogenization.matVecMul ((SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega S.LPrime).toCoeffField y)
  (SuperdiffusionCLT.Section3.Terms.gluedGradientField hnu S.LPrime S.m S.m (SuperdiffusionCLT.Section3.Setup.fluxSlot nu S.LPrime P S.n e) omega y - SuperdiffusionCLT.Section3.Terms.gluedGradientField hnu S.LPrime S.n S.m (SuperdiffusionCLT.Section3.Setup.fluxSlot nu S.LPrime P S.n e) omega y))) ∂P.toMeasure ≤ C * (delta + etaL) ^ ((1 : ℝ) / 2) * Real.sqrt (((S.LPrime - S.ell : ℕ) : ℝ) ^ (2 : ℕ) * (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.LPrime P
  S.n) ^ (2 : ℕ) + (SuperdiffusionCLT.Section2.Annealed.sigmaBarSeq nu S.ell P S.n) ^ (2 : ℕ)) + C * (1 + (delta + etaL) ^ ((1 : ℝ) / 2)) * nu ^ (-(4 : ℝ)) * (((S.LPrime : ℕ) : ℝ) ^ (4 : ℕ)) * ((3 : ℝ) ^ (-((((S.ellPrime - S.n : ℕ) : ℝ)) / 2)) + (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 8)) + (3 : ℝ) ^ (-((((S.ellPrime - S.ell : ℕ) : ℝ)) / 4)) + (3 : ℝ) ^ (-((((S.h : ℕ) : ℝ)) / 16))) := by
  classical
  obtain ⟨Czero, hCzero1, hblup⟩ := rhsTerm3BlowupLocal_blup_constantFirst d
  have hCzero : 0 < Czero := lt_of_lt_of_le zero_lt_one hCzero1
  let Cms := term3PigTailMixConst d
  have hCms : 0 < Cms := term3PigTailMixConst_pos d
  let CL := |SuperdiffusionCLT.Section2.Localization.localizationConst d| + 1
  have hCL : 0 < CL := by
    dsimp only [CL]
    linarith only [abs_nonneg (SuperdiffusionCLT.Section2.Localization.localizationConst d)]
  have hloc : SuperdiffusionCLT.Section2.Localization.localizationConst d ≤ CL := by
    dsimp only [CL]
    linarith only [le_abs_self (SuperdiffusionCLT.Section2.Localization.localizationConst d)]
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hC0 : (0 : ℝ) ≤ 2 := by norm_num
  have hgm : (0 : ℝ) ≤ Homogenization.IndependentSums.gammaMomentConst 1 :=
    le_of_lt (Homogenization.IndependentSums.gammaMomentConst_pos (show (0 : ℝ) < 1 by norm_num))
  have hst : (0 : ℝ) ≤ streamTailConst d := le_of_lt (streamTailConst_pos hd0)
  obtain ⟨Creg, hCreg, hregw⟩ := SuperdiffusionCLT.Section3.ResponseFields.l_w_basic_regbounds_window d hd
  have hnw : (0 : ℝ) ≤ nablaW4SqrtConst Creg := nablaW4SqrtConst_nonneg Creg
  have hswap0 : (0 : ℝ) ≤ 2 * ((d : ℝ) * swapConst d Creg CL) := by
    have h16 : (0 : ℝ) ≤ 16 * Homogenization.IndependentSums.gammaMomentConst 1 ^ (2 : ℕ) :=
      mul_nonneg (by norm_num) (pow_nonneg hgm _)
    rw [swapConst]
    exact mul_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg d)
      (mul_nonneg (mul_nonneg (mul_nonneg h16 (le_of_lt hCL)) hst) hnw))
  obtain ⟨C, hC1, hmain⟩ := v6Windowed_l_RHS_term3_constFirst d hd 2
    (holderRemainderConst Czero) (2 * ((d : ℝ) * swapConst d Creg CL))
    (2 * (d : ℝ) * nablaW2Const Creg) (blockDevConst d 2 (nablaW4SqrtConst Creg))
    ((d : ℝ) * (2 * quadTailConstMain (streamTailConst d) (nablaW4SqrtConst Creg) 4))
    ((d : ℝ) * (2 * quadTailConstError Cms (streamTailConst d) (nablaW4SqrtConst Creg)))
    (nablaW4SqrtConst Creg) CB Cerr
    (termThreeDisp1Const_nonneg d hC0 hCreg)
    (termThreeBlockConst_nonneg d hC0)
    (mul_nonneg (Nat.cast_nonneg d) (termThreeQuadMainConst_nonneg d hd0 hC0))
    (mul_nonneg (Nat.cast_nonneg d) (termThreeQuadErrConst_nonneg d hd0 hC0 hCms))
    (holderRemainderConst_nonneg (le_of_lt hCzero)) hswap0 hnw
  refine ⟨C, hC1, ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder hm2h h100 _hWinOff e he
    delta etaL hdelta hetaL w hw hPigRatio hOscBound hCgBound
  obtain ⟨Zw, hZwmeas, hZwbigO, hZwbound⟩ :=
    (hregw nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder e he
      (SuperdiffusionCLT.Section3.Setup.testVector nu S.LPrime P S.n e) rfl w hw).1
  have hfin := rhsTerm3PrintedSlot_gradTwo_finite hnu hPrefix hJ2 hJ3 hJ4 S hSorder he rfl w
    hCreg hZwmeas hZwbigO hZwbound
  have hfin4 := lintegral_gradFour_pow_ne_top hnu hPrefix hJ2 hJ3 hJ4 S hSorder he rfl w
    hCreg hZwmeas hZwbigO hZwbound
  have hsigma : 0 ≤ SuperdiffusionCLT.Section2.Annealed.sigmaBarSeq nu S.ell P S.n :=
    le_of_lt (SuperdiffusionCLT.Section2.Annealed.sigmaBarSeq_pos hnu S.ell hPrefix hJ2 hJ3 hJ4 S.n)
  have hsq := fun z' hz' => sideCondition_hsq P S w hw hfin4 z' hz'
  obtain ⟨Zrem, hZremMeas, hZremTail, hBlup, hInt4⟩ :=
    hblup nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder e he w hw
  let zc : Homogenization.TriadicCube d := Homogenization.originCube d ((coarseBlockScale d S : ℕ) : ℤ)
  have hzc : zc.scale = ((coarseBlockScale d S : ℕ) : ℤ) := rfl
  have hnl : S.n ≤ S.ell := le_of_lt hSorder.n_lt_ell
  have hellP : S.ell ≤ S.ellPrime := le_of_lt hSorder.ell_lt_ellPrime
  have hlL : S.ell < S.LPrime :=
    lt_trans hSorder.ell_lt_ellPrime
      (lt_trans hSorder.ellPrime_lt_m hSorder.m_lt_LPrime)
  obtain ⟨hlk, hkl, -, -⟩ := coarse_block_scale_choice d S hellP
  have hnk : S.n ≤ coarseBlockScale d S := le_trans hnl hlk
  have hkm : coarseBlockScale d S ≤ S.m :=
    le_trans hkl (le_of_lt hSorder.ellPrime_lt_m)
  have hDscale : ∀ z ∈ Homogenization.descendantsAtDepth zc (coarseBlockScale d S - S.n),
      z.scale = ((S.n : ℕ) : ℤ) := by
    intro z hz
    have h := Homogenization.scale_eq_sub_of_mem_descendantsAtDepth hz
    rw [hzc] at h
    rw [h, Nat.cast_sub hnk]
    ring
  have hpsq : Homogenization.vecNormSq (SuperdiffusionCLT.Section3.Setup.testVector nu S.LPrime P S.n e) =
      SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.LPrime P S.n :=
    SuperdiffusionCLT.Section3.Setup.vecNormSq_testVector hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n he
  have hnabla := nablaW4_of_regbounds d nu hnu P hPrefix hJ2 hJ3 hJ4 S hSorder e he
    (SuperdiffusionCLT.Section3.Setup.testVector nu S.LPrime P S.n e) rfl w hCreg hZwmeas hZwbigO hZwbound
  obtain ⟨Xms, hXmsmeas, hXmstail, hXquenched⟩ :=
    term3_pigTail_of_mixAnchor d nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder hm2h
  have hKlog : 4 * ((S.a : ℕ) : ℝ) ≤ ((S.h : ℕ) : ℝ) := by
    have h4 : 4 * S.a ≤ S.h := by omega
    exact_mod_cast h4
  have htail := fun i : Fin d => averaged_quadratic_tail_translated (Cpig := 4) hnu hPrefix hJ2 hJ3 hJ4
    S hSorder (Homogenization.descendantsAtDepth zc (coarseBlockScale d S - S.n))
    (Homogenization.descendantsAtDepth_nonempty zc (coarseBlockScale d S - S.n)) hDscale (Homogenization.basisVec i)
    hCms (streamTailConst_pos hd0) hnw hXmsmeas hXmstail hXquenched
    (isBigO_gammaSigma_translatedStreamNormSq_originCube hPrefix hJ2 hJ3 hJ4 hnl hlL (Homogenization.vecNormSq_basisVec i))
    (gradResponseMoment_nonneg 4 4 P w) (by rw [← hpsq]; exact hnabla)
    hPigRatio (scaleId_sub_pigeonRange hSorder hm2h) hKlog
  obtain ⟨Xloc, hXlocm, hXloctail, hXlocLoew⟩ :=
    term3_locAnchor_of_conjunct1 d CL hloc nu hnu hnu1 P hJ3 S.ell S.n S.LPrime hnl hlL.le
      (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d (S.n : ℤ))) (by rw [Homogenization.Book.Ch02.cubeDomain_coe])
  rw [Homogenization.Book.Ch02.cubeDomain_coe] at hXlocLoew
  have hZwBasis : ∀ i : Fin d, Homogenization.IndependentSums.IsBigO P.toMeasure (Homogenization.IndependentSums.gammaSigma 2) Zw
      (Creg * (Real.sqrt (Homogenization.vecNormSq (SuperdiffusionCLT.Section3.Setup.testVector nu S.LPrime P S.n (Homogenization.basisVec i))) * (S.h : ℝ) ^ ((1 : ℝ) / 2))) := by
    intro i
    rw [SuperdiffusionCLT.Section3.Setup.vecNormSq_testVector hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n (Homogenization.vecNormSq_basisVec i)]
    simpa only [hpsq] using hZwbigO
  have hSwap := fun i : Fin d => swap_bridge hnu hPrefix hJ2 hJ3 hJ4 S hSorder (Homogenization.vecNormSq_basisVec i) rfl w hCreg hZwmeas
    (hZwBasis i) hZwbound hCL ⟨Xloc, hXlocm, hXloctail, hXlocLoew⟩ hsq
  have hTerms := fun i : Fin d => holder_terms_bridge hnu hPrefix hJ2 hJ3 hJ4 S hSorder (Homogenization.vecNormSq_basisVec i) rfl w hCreg
    hZwmeas (hZwBasis i) hZwbound hzc Zrem hCzero hZremMeas hZremTail hsq
    (memLp_two_descendantAverage_translatedStreamQuadForm_originCube hnu hPrefix hJ2 hJ3 hJ4 S hSorder (Homogenization.vecNormSq_basisVec i))
  have hTerm1 := holder_term_one S.n (coarseBlockScale d S) P w hfin
  have hTerm3 := holder_term_three hnu hPrefix hJ2 hJ3 hJ4 S hSorder w hzc hfin4 hsq
  have hIntB := sideCondition_hIntB hnu P hPrefix hJ2 hJ3 hJ4 S w hsq
  have hInt1 := sideCondition_hInt1 P S w hw hfin4
  have hInt2 := fun i : Fin d => sideCondition_hInt2 hnu P hPrefix hJ2 hJ3 hJ4 S hSorder (Homogenization.vecNormSq_basisVec i) w hsq
  have hInt3 := sideCondition_hInt3 hnu P hPrefix hJ2 hJ3 hJ4 S hSorder w hsq
  have hIntSwap := fun i : Fin d => sideCondition_hIntSwap hnu P hPrefix hJ2 hJ3 hJ4 S hSorder (Homogenization.vecNormSq_basisVec i) w hsq
  let qm := fun i : Fin d => Real.sqrt (∫ ω : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
    |(((Homogenization.descendantsAtDepth zc (coarseBlockScale d S - S.n)).card : ℝ))⁻¹ *
      ∑ z ∈ Homogenization.descendantsAtDepth zc (coarseBlockScale d S - S.n),
        translatedStreamQuadForm nu S.ell S.LPrime (Homogenization.basisVec i) ω z| ^ 2 ∂P.toMeasure)
  have hHolder := rhsTerm3PrintedSlot_integral_split P S hnk hkm (fun ω => (w ω).toH1Function.grad) Zrem
    (fun ω R hR => by
      have htri := Homogenization.Book.Ch02.matrixOperatorNorm_le_matrixOperatorNorm_add_matrixOperatorNorm_sub
        (translatedCoarseBlock nu S.LPrime ω R) (translatedCoarseBlock nu S.ell ω R)
      have hb := hBlup ω R hR
      have hc := translatedBlockNorm_le_blockDevSumSigned hnu S.ell S.n P ω R
      have hs := blupChain_slotTriangle_basisSum hnu S.ell S.LPrime ω R
      norm_num only [one_mul, inv_one, one_add_one_eq_two] at hb
      change translatedBlockNorm nu S.LPrime ω R ≤ translatedBlockNorm nu S.ell ω R + _ at htri
      linarith only [htri, hb, hc, hs])
    hIntB hInt1 hInt2 hIntSwap hInt3 hInt4
  have hQsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => (hTerms i).1)
  have hGsum := basisSum_le_card_mul hSwap
  have hZ := (hTerms (0 : Fin d)).2
  have hOne := mul_le_mul_of_nonneg_left hTerm1
    (mul_nonneg hC0 (mul_nonneg (Nat.cast_nonneg d) hsigma))
  simp only [← Finset.sum_mul] at hQsum
  have hHolder' : (∫ ω, weightedBlockAverage d S.n (coarseBlockScale d S) S.m
      (w ω).toH1Function.grad (translatedBlockNorm nu S.LPrime ω) ∂P.toMeasure) ≤
      2 * ((d : ℝ) * SuperdiffusionCLT.Section2.Annealed.sigmaBarSeq nu S.ell P S.n) * gradResponseMoment (m := S.m) 2 2 P w +
      2 * ((∑ i, qm i) * gradResponseMoment (m := S.m) 4 4 P w ^ ((1 : ℝ) / 2)) +
      2 * (coarseBlockDevMoment nu S.ell S.n P (Homogenization.descendantsAtDepth zc (coarseBlockScale d S - S.n)) *
        gradResponseMoment (m := S.m) 4 4 P w ^ ((1 : ℝ) / 2)) +
      holderRemainderConst Czero * nu ^ (-(3 : ℝ)) * (S.LPrime : ℝ) *
        3 ^ (-((S.ell - S.n : ℕ) : ℝ)) * gradResponseMoment (m := S.m) 4 4 P w ^ ((1 : ℝ) / 2) +
      (2 * ((d : ℝ) * swapConst d Creg CL)) * nu ^ (-(4 : ℝ)) * (S.LPrime : ℝ) ^ 4 *
        3 ^ (-((S.ell - S.n : ℕ) : ℝ) / 4) := by
    dsimp only [qm]
    rw [← neg_div] at hGsum
    linarith only [hHolder, hQsum, hGsum, hZ, hOne, hTerm3]
  have hDisp3 := basisSum_le_card_mul (fun i => disp3_of_quadTail hC0 (htail i))
  simp only [← Finset.mul_sum, ← Finset.sum_mul] at hDisp3
  have hMemFlux := hMemFlux_discharged_B (d := d) hnu hPrefix hJ2 hJ3 hJ4 S hSorder e
  have hPair := hPair_discharged_B (d := d) hd hnu hnu1 (P := P) hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder he w hw
  apply hmain nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder e he
    (SuperdiffusionCLT.Section3.Setup.testVector nu S.LPrime P S.n e) rfl w hw
    (fun ω y => gluedGradientField hnu S.LPrime S.m S.m (SuperdiffusionCLT.Section3.Setup.fluxSlot nu S.LPrime P S.n e) ω y)
    (fun ω y => gluedGradientField hnu S.LPrime S.n S.m (SuperdiffusionCLT.Section3.Setup.fluxSlot nu S.LPrime P S.n e) ω y)
    delta etaL hdelta hetaL (coarseBlockScale d S)
    (translatedBlockHalfWeight nu S.LPrime w) (translatedBlockNorm nu S.LPrime)
    (gradResponseMoment (m := S.m) 2 2 P w) (gradResponseMoment (m := S.m) 4 4 P w)
    (∑ i, qm i) (coarseBlockDevMoment nu S.ell S.n P (Homogenization.descendantsAtDepth zc (coarseBlockScale d S - S.n)))
    (SuperdiffusionCLT.Section3.Setup.sigmaBarStarInvSeq_le_nuInv hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n)
    (fun ω R hR i => sideCondition_hF hnu P S e ω R hR i)
    (fun ω R hR => sideCondition_hgF hnu P S e w ω R hR)
    (sideCondition_hosc_final (d := d) hd hnu hnu1 hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder he w hw hMemFlux hPair)
    (sideCondition_hcg_final (d := d) hd hnu hnu1 hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder he w hw hMemFlux)
    hOscBound hCgBound
    (fun ω z' z => translatedBlockHalfWeight_le hnu S.LPrime w ω z' z)
    (hbHalfInt_discharged (d := d) hd hnu hnu1 (P := P) hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder he w hw)
    hIntB hHolder'
    (disp1_of_regbounds d nu hnu P hPrefix hJ2 hJ3 hJ4 S hSorder e he
      (SuperdiffusionCLT.Section3.Setup.testVector nu S.LPrime P S.n e) rfl w hC0 hCreg hZwmeas hZwbigO hZwbound)
    (fun _ => blockDev_of_concentration hnu hnu1 hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder
      he rfl w hCreg hC0 hZwmeas hZwbigO hZwbound hKlog hzc)
    ?_ (fun _ => hnabla)
  dsimp only [qm]
  convert hDisp3 using 1
  ring
theorem v6Windowed_main (d : ℕ) [NeZero d] (hd : 2 ≤ d) (hFluxUniform : ∃ C3 : ℝ, 0 ≤ C3 ∧ ∀ (nu : ℝ) (hnu : 0 < nu) (_hnu1 : nu ≤ 1) (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)) (_hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P) (_hJ1V2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P) (_hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P) (_hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
  (_hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P) (S : SuperdiffusionCLT.Section3.Setup.ScaleSelection) (_hSorder : SuperdiffusionCLT.Section3.Setup.ScalesOrdering S) (_hTwoHLeM : 2 * S.h ≤ S.m) (_hHundredALeH : 100 * S.a ≤ S.h) (_hWindowVsOffset : S.h + 1 ≤ 3 ^ S.a) (_hOffsetLower : (8056 / Real.log 3) * Real.log (nu⁻¹ * ((S.L : ℕ) : ℝ)) ≤ ((S.a : ℕ) : ℝ)) (e : Homogenization.Vec d) (_he : Homogenization.vecNormSq e = 1) (delta etaL : ℝ) (_hdelta : 0 ≤ delta) (_hetaL
  : 0 ≤ etaL) (w : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → Homogenization.H10Function (Homogenization.openCubeSet (Homogenization.originCube d (S.m : ℤ)))) (_hw : ∀ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d, SuperdiffusionCLT.Section3.Setup.IsDirichletResponse omega S.LPrime S.ellPrime S.m (SuperdiffusionCLT.Section3.Setup.testVector nu S.LPrime P S.n e) (w omega)), ∀ R ∈ SuperdiffusionCLT.Section2.Estimates.Stream.largeCubeSubcubes d S.n S.m, ∫ omega :
  SuperdiffusionCLT.Section2.Cutoff.ShellSeq d, seminormFluxNeg nu hnu S P e omega R ^ ((3 : ℝ) / 2) ∂P.toMeasure ≤ C3 * (3 : ℝ) ^ ((3 * (S.n : ℝ)) / 2) * (((S.LPrime : ℕ) : ℝ) * nu⁻¹) ^ ((3 : ℝ) / 4) * (∫ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d, oscEnergy nu hnu S P e omega R ∂P.toMeasure) ^ ((3 : ℝ) / 4)) (hCgWindowed : ∃ Cerr : ℝ, ∀ (nu : ℝ) (_hnu : 0 < nu) (_hnu1 : nu ≤ 1) (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
  (_hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P) (_hJ1V2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P) (_hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P) (_hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P) (_hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P) (S : SuperdiffusionCLT.Section3.Setup.ScaleSelection) (_hSorder : SuperdiffusionCLT.Section3.Setup.ScalesOrdering S) (_hTwoHLeM : 2 * S.h ≤ S.m)
  (_hHundredALeH : 100 * S.a ≤ S.h) (_hWindowVsOffset : S.h + 1 ≤ 3 ^ S.a) (_hOffsetLower : (8056 / Real.log 3) * Real.log (nu⁻¹ * ((S.L : ℕ) : ℝ)) ≤ ((S.a : ℕ) : ℝ)) (e : Homogenization.Vec d) (_he : Homogenization.vecNormSq e = 1) (delta etaL : ℝ) (_hdelta : 0 ≤ delta) (_hetaL : 0 ≤ etaL) (w : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → Homogenization.H10Function (Homogenization.openCubeSet (Homogenization.originCube d (S.m : ℤ)))) (_hw : ∀ omega :
  SuperdiffusionCLT.Section2.Cutoff.ShellSeq d, SuperdiffusionCLT.Section3.Setup.IsDirichletResponse omega S.LPrime S.ellPrime S.m (SuperdiffusionCLT.Section3.Setup.testVector nu S.LPrime P S.n e) (w omega)), cgBoundConst (cgBoundAmpP d P S w) (cgBoundAmpW nu S) (bEllipConst d) ≤ Cerr * ((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ) * nu ^ (-((3 : ℝ) / 2))) : ∃ C : ℝ, 1 ≤ C ∧ ∀ (nu : ℝ) (hnu : 0 < nu) (_hnu1 : nu ≤ 1) (P : MeasureTheory.ProbabilityMeasure
  (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)) (_hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P) (_hJ1V2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P) (_hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P) (_hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P) (_hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P) (S : SuperdiffusionCLT.Section3.Setup.ScaleSelection) (_hSorder :
  SuperdiffusionCLT.Section3.Setup.ScalesOrdering S) (_hTwoHLeM : 2 * S.h ≤ S.m) (_hHundredALeH : 100 * S.a ≤ S.h) (_hWindowVsOffset : S.h + 1 ≤ 3 ^ S.a) (_hOffsetLower : (8056 / Real.log 3) * Real.log (nu⁻¹ * ((S.L : ℕ) : ℝ)) ≤ ((S.a : ℕ) : ℝ)) (e : Homogenization.Vec d) (_he : Homogenization.vecNormSq e = 1) (delta etaL : ℝ) (_hdelta : 0 ≤ delta) (_hetaL : 0 ≤ etaL) (_hPigeonScalar : SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.L P (S.m - 2 * S.h) ≤ (1 + delta) *
  SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.L P S.m) (_hDeltaEtaLeOne : delta + etaL ≤ 1) (_hEtaL : C * nu ^ (-(5 : ℝ)) * ((S.L : ℕ) : ℝ) * (3 : ℝ) ^ (-(((S.LPrime - S.m : ℕ) : ℝ))) ≤ etaL) (w : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → Homogenization.H10Function (Homogenization.openCubeSet (Homogenization.originCube d (S.m : ℤ)))) (_hw : ∀ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d, SuperdiffusionCLT.Section3.Setup.IsDirichletResponse omega
  S.LPrime S.ellPrime S.m (SuperdiffusionCLT.Section3.Setup.testVector nu S.LPrime P S.n e) (w omega)), ∫ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d, Homogenization.volumeAverage (Homogenization.openCubeSet (Homogenization.originCube d (S.m : ℤ))) (fun y => Homogenization.vecDot ((w omega).toH1Function.grad y) (Homogenization.matVecMul ((SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega S.LPrime).toCoeffField y)
  (SuperdiffusionCLT.Section3.Terms.gluedGradientField hnu S.LPrime S.m S.m (SuperdiffusionCLT.Section3.Setup.fluxSlot nu S.LPrime P S.n e) omega y - SuperdiffusionCLT.Section3.Terms.gluedGradientField hnu S.LPrime S.n S.m (SuperdiffusionCLT.Section3.Setup.fluxSlot nu S.LPrime P S.n e) omega y))) ∂P.toMeasure ≤ C * (delta + etaL) ^ ((1 : ℝ) / 2) * Real.sqrt (((S.LPrime - S.ell : ℕ) : ℝ) ^ (2 : ℕ) * (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.LPrime P
  S.n) ^ (2 : ℕ) + (SuperdiffusionCLT.Section2.Annealed.sigmaBarSeq nu S.ell P S.n) ^ (2 : ℕ)) + C * (1 + (delta + etaL) ^ ((1 : ℝ) / 2)) * nu ^ (-(4 : ℝ)) * (((S.LPrime : ℕ) : ℝ) ^ (4 : ℕ)) * ((3 : ℝ) ^ (-((((S.ellPrime - S.n : ℕ) : ℝ)) / 2)) + (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 8)) + (3 : ℝ) ^ (-((((S.ellPrime - S.ell : ℕ) : ℝ)) / 4)) + (3 : ℝ) ^ (-((((S.h : ℕ) : ℝ)) / 16))) := by
  obtain ⟨C3, hC3, hFlux⟩ := hFluxUniform
  obtain ⟨Cerr, hCerr⟩ := hCgWindowed
  obtain ⟨CB, _hCB, hOsc⟩ := term3_oscBound_seminorm_measurable d hd C3 hC3
  obtain ⟨C0, hC0, hmain⟩ := v6Windowed_printedSlot_of_estimates d hd CB Cerr
  set CL : ℝ := |SuperdiffusionCLT.Section2.Localization.localizationConst d| + 1
    with hCLdef
  have hCL : 0 < CL := by
    rw [hCLdef]
    linarith only [abs_nonneg (SuperdiffusionCLT.Section2.Localization.localizationConst d)]
  have hloc : SuperdiffusionCLT.Section2.Localization.localizationConst d ≤ CL := by
    rw [hCLdef]
    linarith only [le_abs_self (SuperdiffusionCLT.Section2.Localization.localizationConst d)]
  have hCeta0 : (0 : ℝ) ≤ pigRatioCeta d CL := pigRatioCeta_nonneg d hCL.le
  refine ⟨max C0 (6 * pigRatioCeta d CL), le_trans hC0 (le_max_left _ _), ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder hTwoHLeM hHundredALeH
    hWindowVsOffset hOffsetLower e he delta etaL hdelta hetaL hPigScalar hde1 htieC w hw
  have htie : 6 * SuperdiffusionCLT.Section3.Setup.localizationEta
      (pigRatioCeta d CL) nu S.L (S.LPrime - S.m) ≤ etaL := by
    have hfac : (0 : ℝ) ≤ nu ^ (-(5 : ℝ)) * ((S.L : ℕ) : ℝ) *
        (3 : ℝ) ^ (-(((S.LPrime - S.m : ℕ) : ℝ))) := by
      have h1 : (0 : ℝ) ≤ nu ^ (-(5 : ℝ)) := Real.rpow_nonneg hnu.le _
      have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(((S.LPrime - S.m : ℕ) : ℝ))) :=
        Real.rpow_nonneg zero_le_three _
      positivity
    have hle := mul_le_mul_of_nonneg_right
      (le_max_right C0 (6 * pigRatioCeta d CL)) hfac
    have e1 : 6 * SuperdiffusionCLT.Section3.Setup.localizationEta
        (pigRatioCeta d CL) nu S.L (S.LPrime - S.m) =
        6 * pigRatioCeta d CL * (nu ^ (-(5 : ℝ)) * ((S.L : ℕ) : ℝ) *
          (3 : ℝ) ^ (-(((S.LPrime - S.m : ℕ) : ℝ)))) := by
      rw [SuperdiffusionCLT.Section3.Setup.localizationEta]; ring
    have e2 : max C0 (6 * pigRatioCeta d CL) * nu ^ (-(5 : ℝ)) * ((S.L : ℕ) : ℝ) *
          (3 : ℝ) ^ (-(((S.LPrime - S.m : ℕ) : ℝ))) =
        max C0 (6 * pigRatioCeta d CL) * (nu ^ (-(5 : ℝ)) * ((S.L : ℕ) : ℝ) *
          (3 : ℝ) ^ (-(((S.LPrime - S.m : ℕ) : ℝ)))) := by ring
    linarith only [hle, e1, e2, htieC]
  have hscal := rhsTerm3Statement_pigeonScalar S hnu hnu1 hCL hloc hPrefix hJ2 hJ3 hJ4 hSorder hTwoHLeM
    hdelta hetaL hde1 htie hPigScalar
  have heps : 0 ≤ delta + etaL := add_nonneg hdelta hetaL
  have hpig := rhsTerm3Statement_pigeon S hnu hPrefix hJ2 hJ3 hJ4 hSorder heps hde1 hscal
  have hPigRatio := rhsTerm3Statement_pigRatio S hnu hPrefix hJ2 hJ3 hJ4 hSorder heps hde1 hscal
  have hmeasFlux := fun R hR => rhsTerm3Measurable_aestronglyMeasurable_flux hnu S P e (R := R) hR
  refine le_trans (hmain nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder hTwoHLeM
    hHundredALeH hWindowVsOffset e he delta etaL hdelta hetaL w hw hPigRatio ?_ ?_) ?_
  · apply hOsc nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder hWindowVsOffset
      e he delta etaL hdelta hetaL w hw
    · exact hFlux nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder hTwoHLeM
        hHundredALeH hWindowVsOffset hOffsetLower e he delta etaL hdelta hetaL w hw
    · exact rhsTerm3Obligations_energy_of_pigeon hnu hPrefix hJ2 hJ3 hJ4 S hSorder he hpig
    · intro R hR
      exact rhsTerm3Measurable_aestronglyMeasurable_osc hd hSorder w hw hR
    · exact hmeasFlux
    · intro R hR
      exact integrable_seminormFluxNeg_rpow_of_aestronglyMeasurable hnu P hPrefix
        hJ2 hJ3 hJ4 S hSorder e hR (hmeasFlux R hR)
  ·
    have hlocal := term3_cgBound_finalC d hd nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S
      hSorder hTwoHLeM hHundredALeH hWindowVsOffset e he delta etaL hdelta hetaL w hw
      (Cerr * ((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ) * nu ^ (-((3 : ℝ) / 2)))
      (hCerr nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder hTwoHLeM
        hHundredALeH hWindowVsOffset hOffsetLower e he delta etaL hdelta hetaL w hw) hpig
    have hpow : nu ^ (-((3 : ℝ) / 2)) * nu ^ (-(5 : ℝ) / 2) = nu ^ (-(4 : ℝ)) := by
      rw [← Real.rpow_add hnu]
      congr 1
      norm_num
    have hscale :
        (Cerr * ((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ) * nu ^ (-((3 : ℝ) / 2))) *
          (3 : ℝ) ^ (-(((S.ellPrime - S.ell : ℕ) : ℝ) / 4)) *
          ((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ) * nu ^ (-(5 : ℝ) / 2) =
        Cerr * nu ^ (-(4 : ℝ)) * (((S.LPrime : ℕ) : ℝ) ^ (4 : ℕ)) *
          (3 : ℝ) ^ (-(((S.ellPrime - S.ell : ℕ) : ℝ) / 4)) := by
      calc _ = Cerr * (3 : ℝ) ^ (-(((S.ellPrime - S.ell : ℕ) : ℝ) / 4)) *
            ((((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ)) ^ (2 : ℕ)) *
            (nu ^ (-((3 : ℝ) / 2)) * nu ^ (-(5 : ℝ) / 2)) := by ring
        _ = _ := by rw [hpow]; ring
    simpa only [hscale] using hlocal
  · -- monotonicity of the right side in the constant
    have hCle : C0 ≤ max C0 (6 * pigRatioCeta d CL) := le_max_left _ _
    have hp : 0 ≤ (delta + etaL) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg heps _
    have hq : 0 ≤ Real.sqrt (((S.LPrime - S.ell : ℕ) : ℝ) ^ (2 : ℕ) *
        (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.LPrime P S.n) ^
          (2 : ℕ) +
        (SuperdiffusionCLT.Section2.Annealed.sigmaBarSeq nu S.ell P S.n) ^ (2 : ℕ)) :=
      Real.sqrt_nonneg _
    have hr : 0 ≤ 1 + (delta + etaL) ^ ((1 : ℝ) / 2) := by linarith only [hp]
    have hs : 0 ≤ nu ^ (-(4 : ℝ)) := Real.rpow_nonneg hnu.le _
    have ht : 0 ≤ (((S.LPrime : ℕ) : ℝ) ^ (4 : ℕ)) := pow_nonneg (Nat.cast_nonneg _) _
    have hu : 0 ≤ (3 : ℝ) ^ (-((((S.ellPrime - S.n : ℕ) : ℝ)) / 2)) +
        (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 8)) +
        (3 : ℝ) ^ (-((((S.ellPrime - S.ell : ℕ) : ℝ)) / 4)) +
        (3 : ℝ) ^ (-((((S.h : ℕ) : ℝ)) / 16)) := by positivity
    have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCle hp) hq
    have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCle hr) hs) ht) hu
    exact add_le_add h1 h2
theorem v6Windowed_closedCg (d : ℕ) [NeZero d] (hd : 2 ≤ d) (hFluxUniform : ∃ C3 : ℝ, 0 ≤ C3 ∧ ∀ (nu : ℝ) (hnu : 0 < nu) (_hnu1 : nu ≤ 1) (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)) (_hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P) (_hJ1V2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P) (_hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P) (_hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3
  d P) (_hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P) (S : SuperdiffusionCLT.Section3.Setup.ScaleSelection) (_hSorder : SuperdiffusionCLT.Section3.Setup.ScalesOrdering S) (_hTwoHLeM : 2 * S.h ≤ S.m) (_hHundredALeH : 100 * S.a ≤ S.h) (_hWindowVsOffset : S.h + 1 ≤ 3 ^ S.a) (_hOffsetLower : (8056 / Real.log 3) * Real.log (nu⁻¹ * ((S.L : ℕ) : ℝ)) ≤ ((S.a : ℕ) : ℝ)) (e : Homogenization.Vec d) (_he : Homogenization.vecNormSq e = 1) (delta etaL : ℝ) (_hdelta : 0 ≤ delta)
  (_hetaL : 0 ≤ etaL) (w : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → Homogenization.H10Function (Homogenization.openCubeSet (Homogenization.originCube d (S.m : ℤ)))) (_hw : ∀ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d, SuperdiffusionCLT.Section3.Setup.IsDirichletResponse omega S.LPrime S.ellPrime S.m (SuperdiffusionCLT.Section3.Setup.testVector nu S.LPrime P S.n e) (w omega)), ∀ R ∈ SuperdiffusionCLT.Section2.Estimates.Stream.largeCubeSubcubes d S.n S.m, ∫
  omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d, seminormFluxNeg nu hnu S P e omega R ^ ((3 : ℝ) / 2) ∂P.toMeasure ≤ C3 * (3 : ℝ) ^ ((3 * (S.n : ℝ)) / 2) * (((S.LPrime : ℕ) : ℝ) * nu⁻¹) ^ ((3 : ℝ) / 4) * (∫ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d, oscEnergy nu hnu S P e omega R ∂P.toMeasure) ^ ((3 : ℝ) / 4)) : ∃ C : ℝ, 1 ≤ C ∧ ∀ (nu : ℝ) (hnu : 0 < nu) (_hnu1 : nu ≤ 1) (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
  (_hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P) (_hJ1V2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P) (_hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P) (_hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P) (_hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P) (S : SuperdiffusionCLT.Section3.Setup.ScaleSelection) (_hSorder : SuperdiffusionCLT.Section3.Setup.ScalesOrdering S) (_hTwoHLeM : 2 * S.h ≤ S.m)
  (_hHundredALeH : 100 * S.a ≤ S.h) (_hWindowVsOffset : S.h + 1 ≤ 3 ^ S.a) (_hOffsetLower : (8056 / Real.log 3) * Real.log (nu⁻¹ * ((S.L : ℕ) : ℝ)) ≤ ((S.a : ℕ) : ℝ)) (e : Homogenization.Vec d) (_he : Homogenization.vecNormSq e = 1) (delta etaL : ℝ) (_hdelta : 0 ≤ delta) (_hetaL : 0 ≤ etaL) (_hPigeonScalar : SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.L P (S.m - 2 * S.h) ≤ (1 + delta) * SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.L P S.m)
  (_hDeltaEtaLeOne : delta + etaL ≤ 1) (_hEtaL : C * nu ^ (-(5 : ℝ)) * ((S.L : ℕ) : ℝ) * (3 : ℝ) ^ (-(((S.LPrime - S.m : ℕ) : ℝ))) ≤ etaL) (w : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → Homogenization.H10Function (Homogenization.openCubeSet (Homogenization.originCube d (S.m : ℤ)))) (_hw : ∀ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d, SuperdiffusionCLT.Section3.Setup.IsDirichletResponse omega S.LPrime S.ellPrime S.m (SuperdiffusionCLT.Section3.Setup.testVector
  nu S.LPrime P S.n e) (w omega)), ∫ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d, Homogenization.volumeAverage (Homogenization.openCubeSet (Homogenization.originCube d (S.m : ℤ))) (fun y => Homogenization.vecDot ((w omega).toH1Function.grad y) (Homogenization.matVecMul ((SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega S.LPrime).toCoeffField y) (SuperdiffusionCLT.Section3.Terms.gluedGradientField hnu S.LPrime S.m S.m
  (SuperdiffusionCLT.Section3.Setup.fluxSlot nu S.LPrime P S.n e) omega y - SuperdiffusionCLT.Section3.Terms.gluedGradientField hnu S.LPrime S.n S.m (SuperdiffusionCLT.Section3.Setup.fluxSlot nu S.LPrime P S.n e) omega y))) ∂P.toMeasure ≤ C * (delta + etaL) ^ ((1 : ℝ) / 2) * Real.sqrt (((S.LPrime - S.ell : ℕ) : ℝ) ^ (2 : ℕ) * (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.LPrime P S.n) ^ (2 : ℕ) + (SuperdiffusionCLT.Section2.Annealed.sigmaBarSeq nu S.ell P
  S.n) ^ (2 : ℕ)) + C * (1 + (delta + etaL) ^ ((1 : ℝ) / 2)) * nu ^ (-(4 : ℝ)) * (((S.LPrime : ℕ) : ℝ) ^ (4 : ℕ)) * ((3 : ℝ) ^ (-((((S.ellPrime - S.n : ℕ) : ℝ)) / 2)) + (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 8)) + (3 : ℝ) ^ (-((((S.ellPrime - S.ell : ℕ) : ℝ)) / 4)) + (3 : ℝ) ^ (-((((S.h : ℕ) : ℝ)) / 16))) := by
  exact v6Windowed_main d hd hFluxUniform (cgConstant_windowed d hd)
end

end SuperdiffusionCLT.Section3.Terms
