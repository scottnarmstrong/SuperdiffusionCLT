/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.WeakNorms.PrimeG

/-!
# Package C6, part 8: the Step 2 `Θ` bound from node 7

`akhcPrime_step2_thetaBound_src` is the Step 2 closing display,
`Θ_k − 1 ≤ C (1 + √K_w + K_w)(σ δ^{1/2} + 3^{-ℓ}) Θ_m`, from the weak-norm estimate in the
source's normalization, `W_src ≤ K_w δσ² Θ_m` (`akhcPrime_srcEnergy`), with the two
square-integrability inputs of the skeleton discharged (package WeakNormSqE).
`akhcPrime_srcEnergy_eq_integral` identifies `W_src` with the expectation bounded by
`akhcPrime_step2_energy_le`.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.WeakNorms

open Homogenization MeasureTheory

noncomputable section

section Law

variable {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
  (P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)) (L : ℕ)
  (gamma H D : ℝ) (m2 : ℕ) (PsiS : ℝ → ℝ) (KPsiS pPsiS : ℝ)
  (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1) (hH : 1 ≤ H) (hD : 0 ≤ D)
  (hPsiSMono : MonotoneOn PsiS (Set.Ici 0)) (hPsiSOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ PsiS t)
  (hKPsiS : 1 ≤ KPsiS) (hpPsiS : 2 < pPsiS)
  (hGrowth : ∀ p : ℝ, 2 ≤ p → p ≤ pPsiS → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
    s ^ p ≤ KPsiS ^ (3 * ⌈p⌉₊ ^ 2) * (PsiS (t * s) / PsiS t))
  (hP2 : ∀ j : ℕ, m2 ≤ j →
    ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
      Measurable X ∧
      Homogenization.IndependentSums.IsBigO P.toMeasure PsiS X
        (H * (j : ℝ) ^ D) ∧
      ∀ (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
        (Q : Homogenization.TriadicCube d),
        Q.scale ≤ (j : ℤ) →
        Homogenization.cubeCenter Q ∈
            Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)) →
          Homogenization.BlockMatLoewnerLE
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q)
              (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu
                  omega L).toCoeffField)
            ((1 + (3 : ℝ) ^ (-(gamma * ((Q.scale : ℝ) - (j : ℝ)))) *
                  X omega) •
              SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                (Homogenization.cubeSet
                  (Homogenization.originCube d (j : ℤ)))))
  (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)

include hnu hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hJ4 in
/-- `W_src` is the expectation of the samplewise energy `akhcPrime_energy` (package B4's special
vectors coincide with package B1's). -/
theorem akhcPrime_srcEnergy_eq_integral
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    {k : ℕ} (hk2 : m2 ≤ k) (hk : 0 < k) (e : Vec d) :
    akhcPrime_srcEnergy nu L P k e =
      ∫ a, akhcPrime_energy nu L P k e a
        ∂(SuperdiffusionCLT.Section2.Annealed.cutoffLaw (d := d) nu L P) := by
  have hσ : SuperdiffusionCLT.AKHC61.Response.akhc_sigmaHatScalar nu L P k =
      SuperdiffusionCLT.AKHC61.Response.akhcSigmaHatAtScale nu L P (k : ℤ) := by
    unfold SuperdiffusionCLT.AKHC61.Response.akhc_sigmaHatScalar
      SuperdiffusionCLT.AKHC61.Response.akhcSigmaHatAtScale
    rw [div_eq_mul_inv]
    rfl
  have hp : SuperdiffusionCLT.AKHC61.Response.akhc_specialP nu L P k e =
      SuperdiffusionCLT.AKHC61.Response.akhcSpecialPAtScale nu L P (k : ℤ) e := by
    unfold SuperdiffusionCLT.AKHC61.Response.akhc_specialP
      SuperdiffusionCLT.AKHC61.Response.akhcSpecialPAtScale
    rw [hσ]
    rfl
  have hq : SuperdiffusionCLT.AKHC61.Response.akhc_specialQ nu L P k e =
      SuperdiffusionCLT.AKHC61.Response.akhcSpecialQAtScale nu L P (k : ℤ) e := by
    unfold SuperdiffusionCLT.AKHC61.Response.akhc_specialQ
      SuperdiffusionCLT.AKHC61.Response.akhcSpecialQAtScale
    rw [hσ]
    rfl
  have hG := akhcWNSq_integrable_gradientWeakNorm_sq hnu hPrefix hJ2 hJ4 gamma H D m2 PsiS KPsiS
    pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hk2 hk
    (SuperdiffusionCLT.AKHC61.Response.akhcSpecialPAtScale nu L P (k : ℤ) e)
    (SuperdiffusionCLT.AKHC61.Response.akhcSpecialQAtScale nu L P (k : ℤ) e)
    (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvScalar nu L P
        (cubeSet (originCube d (k : ℤ))) •
      SuperdiffusionCLT.AKHC61.Response.akhcSpecialQAtScale nu L P (k : ℤ) e -
      SuperdiffusionCLT.AKHC61.Response.akhcSpecialPAtScale nu L P (k : ℤ) e)
  have hF := akhcWNSq_integrable_fluxWeakNorm_sq hnu hPrefix hJ2 hJ4 gamma H D m2 PsiS KPsiS
    pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hk2 hk
    (SuperdiffusionCLT.AKHC61.Response.akhcSpecialPAtScale nu L P (k : ℤ) e)
    (SuperdiffusionCLT.AKHC61.Response.akhcSpecialQAtScale nu L P (k : ℤ) e)
    (SuperdiffusionCLT.AKHC61.Response.akhcSpecialQAtScale nu L P (k : ℤ) e -
      SuperdiffusionCLT.Section2.Annealed.sigmaBarScalar nu L P
          (cubeSet (originCube d (k : ℤ))) •
        SuperdiffusionCLT.AKHC61.Response.akhcSpecialPAtScale nu L P (k : ℤ) e)
  unfold akhcPrime_energy
  rw [integral_add (hG.const_mul _) (hF.const_mul _), integral_const_mul, integral_const_mul]
  unfold akhcPrime_srcEnergy SuperdiffusionCLT.AKHC61.Step2.akhc_step2P0
    SuperdiffusionCLT.AKHC61.Step2.akhc_step2Q0
  rw [hσ, hp, hq]
  rfl

include hnu hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hJ4 in
/-- **The Step 2 bound `Θ_k − 1 ≤ C (σ δ^{1/2} + 3^{-ℓ}) Θ_m` from `W_src`**.
The skeleton's `hWeak` is replaced by `hWeakSrc : W_src ≤ K_w δσ² Θ_m`, the manuscript's
normalization; `hGradSq`, `hFluxSq` are discharged. -/
theorem akhcPrime_step2_thetaBound_src
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (m k ell : ℕ) (hmk : m ≤ k) (hell : ell ≤ k) (hk2 : m2 ≤ k) (hk : 0 < k)
    (delta sigma : ℝ) (hdelta : 0 ≤ delta) (hsigma : 0 ≤ sigma)
    (hsmall : delta * sigma ^ 2 ≤ 1)
    (hPigeon :
      Homogenization.BlockMatLoewnerLE
        (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
          (Homogenization.cubeSet (Homogenization.originCube d ((k - ell : ℕ) : ℤ))))
        ((1 + delta * sigma ^ 2) •
          SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
            (Homogenization.cubeSet (Homogenization.originCube d (k : ℤ)))))
    (e : Vec d) (he : vecNormSq e = 1)
    (Kw : ℝ) (hKw : 0 ≤ Kw)
    (hWeakSrc : akhcPrime_srcEnergy nu L P k e ≤
      Kw * (delta * sigma ^ 2) * SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m) :
    SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P k - 1 ≤
      2 * SuperdiffusionCLT.AKHC61.Step2.akhcJB_const d * (1 + Real.sqrt Kw + Kw) *
        (sigma * Real.sqrt delta + ((3 : ℝ) ^ ell)⁻¹) *
        SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m := by
  have hGradSq := akhcWNSq_integrable_gradientWeakNorm_sq hnu hPrefix hJ2 hJ4 gamma H D m2 PsiS
    KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hk2 hk
    (SuperdiffusionCLT.AKHC61.Response.akhc_specialP nu L P k e)
    (SuperdiffusionCLT.AKHC61.Response.akhc_specialQ nu L P k e)
    (SuperdiffusionCLT.AKHC61.Step2.akhc_step2P0 nu L P k e)
  have hFluxSq := akhcWNSq_integrable_fluxWeakNorm_sq hnu hPrefix hJ2 hJ4 gamma H D m2 PsiS
    KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hk2 hk
    (SuperdiffusionCLT.AKHC61.Response.akhc_specialP nu L P k e)
    (SuperdiffusionCLT.AKHC61.Response.akhc_specialQ nu L P k e)
    (SuperdiffusionCLT.AKHC61.Step2.akhc_step2Q0 nu L P k e)
  have hJ := akhcPrime_jBound_src hnu P L gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD
    hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hJ4 hPrefix hJ2 k ell hell delta sigma hdelta
    hsigma hsmall hPigeon e he hGradSq hFluxSq
  have hT : SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P k - 1 ≤
      2 * SuperdiffusionCLT.AKHC61.Step2.akhcJB_const d *
        (sigma * Real.sqrt delta *
            Real.sqrt (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P k) +
          ((3 : ℝ) ^ ell)⁻¹ *
            Real.sqrt (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P k) +
          Real.sqrt (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P k *
            akhcPrime_srcEnergy nu L P k e) +
          akhcPrime_srcEnergy nu L P k e) := by
    rw [SuperdiffusionCLT.AKHC61.Response.akhc_thetaCutoff_sub_one_eq_two_centeredResponse_special
      hnu P L gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS
      hpPsiS hGrowth hP2 hJ4 k e he, mul_assoc]
    exact mul_le_mul_of_nonneg_left hJ (by norm_num)
  have hTheta1 := SuperdiffusionCLT.AKHC61.Carrier.akhc_one_le_thetaCutoff_of_P2 hnu hJ4
    gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth
    hP2 k
  have hanti := SuperdiffusionCLT.AKHC61.Carrier.akhc_antitone_thetaCutoff_of_P2 hnu hPrefix
    hJ2 hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS
    hGrowth hP2 hmk
  have hA := SuperdiffusionCLT.AKHC61.Carrier.akhc_sigmaBarStarInvSeq_pos_of_P2 hnu hJ4 gamma
    H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 k
  have hB := SuperdiffusionCLT.AKHC61.Carrier.akhc_sigmaBarSeq_pos_of_P2 hnu hJ4 gamma
    H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 k
  have hW0 : 0 ≤ akhcPrime_srcEnergy nu L P k e :=
    add_nonneg (mul_nonneg (Real.sqrt_nonneg _)
        (MeasureTheory.integral_nonneg fun _ => sq_nonneg _))
      (mul_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))
        (MeasureTheory.integral_nonneg fun _ => sq_nonneg _))
  have hss : sigma * Real.sqrt delta * (sigma * Real.sqrt delta) = delta * sigma ^ 2 := by
    have h := Real.mul_self_sqrt hdelta
    calc sigma * Real.sqrt delta * (sigma * Real.sqrt delta) =
        sigma ^ 2 * (Real.sqrt delta * Real.sqrt delta) := by ring
      _ = delta * sigma ^ 2 := by rw [h, mul_comm]
  have hs0 : 0 ≤ sigma * Real.sqrt delta := mul_nonneg hsigma (Real.sqrt_nonneg _)
  have hs1 : sigma * Real.sqrt delta ≤ 1 := by
    have h := Real.sqrt_le_sqrt hsmall
    rwa [← hss, Real.sqrt_mul_self hs0, Real.sqrt_one] at h
  rw [← hss] at hWeakSrc
  have hK0 : 0 ≤ SuperdiffusionCLT.AKHC61.Step2.akhcJB_const d := by
    have hg := quantitativeCubeCutoffGradientConst_nonneg d
    have hlin : 0 ≤ SuperdiffusionCLT.AKHC61.Step2.akhcJB_linConst d :=
      (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg (by positivity)
        (Homogenization.cubeBesovScaleWeight_nonneg _ _))
        (Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffDualBound_nonneg
          (Homogenization.originCube d (0 : ℤ)) (1 / 2 : ℝ)))).trans
      (Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53_linearCutoffCoeff_le_dimensional
        (Homogenization.originCube d (0 : ℤ)) (r := 1 / 2) (by norm_num) (by norm_num))
    have hprod : 0 ≤ SuperdiffusionCLT.AKHC61.Step2.akhcJB_prodConst d :=
      (Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffProductCoeff_nonneg
        (Homogenization.originCube d ((0 : ℕ) : ℤ)) (1 / 2 : ℝ) (1 / 2 : ℝ)).trans
      (Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffProductCoeff_origin_le_dimensional
        (d := d) 0 (s := 1 / 2) (t := 1 / 2) (by norm_num) (by norm_num))
    have h4 : 0 ≤ 4 * (1 + (2 : ℝ) ^ d) := by positivity
    have h8 : 0 ≤ 8 * quantitativeCubeCutoffGradientConst d * (2 : ℝ) ^ d :=
      mul_nonneg (mul_nonneg (by norm_num) hg) (by positivity)
    have hK : SuperdiffusionCLT.AKHC61.Step2.akhcJB_const d = 4 * (1 + (2 : ℝ) ^ d) +
        8 * quantitativeCubeCutoffGradientConst d * (2 : ℝ) ^ d + SuperdiffusionCLT.AKHC61.Step2.akhcJB_linConst d +
          SuperdiffusionCLT.AKHC61.Step2.akhcJB_prodConst d := rfl
    linarith only [hK, h4, h8, hlin, hprod]
  have hclose := SuperdiffusionCLT.AKHC61.Step2.akhcJB_close_arith hK0 hKw hs0 hs1
    (t := ((3 : ℝ) ^ ell)⁻¹) (by positivity) hTheta1 hanti hW0 hWeakSrc
  calc _ ≤ _ := hT
    _ = 2 * (SuperdiffusionCLT.AKHC61.Step2.akhcJB_const d *
        (sigma * Real.sqrt delta *
            Real.sqrt (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P k) +
          ((3 : ℝ) ^ ell)⁻¹ *
            Real.sqrt (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P k) +
          Real.sqrt (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P k *
            akhcPrime_srcEnergy nu L P k e) +
          akhcPrime_srcEnergy nu L P k e)) := by ring
    _ ≤ 2 * (SuperdiffusionCLT.AKHC61.Step2.akhcJB_const d * (1 + Real.sqrt Kw + Kw) *
          (sigma * Real.sqrt delta + ((3 : ℝ) ^ ell)⁻¹) *
        SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m) :=
        mul_le_mul_of_nonneg_left hclose (by norm_num)
    _ = _ := by ring

include hnu hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hJ4 in
/-- **Step 2 of Theorem 6.1 closed through node 7**, route W: under the
pigeonhole closeness at the lag `ℓ` (`hPigeon`, node 28), the three-scale variance bound
`V ≤ c_V δσ²` (`e.variance.HC.prime`, node 30, in the operator-norm fluctuation form), and the
smallness of the node-7 tail terms (`hMsmall`: package C3's second-moment bound, `hT1small`,
`hT2small`: the low-scale and constant tails; the source's `e.omegan.small` and definition of
`L`), `Θ_k − 1 ≤ C (1 + √K_w + K_w)(σ δ^{1/2} + 3^{-ℓ}) Θ_m` with
`K_w = K(d, s', ρ)(c_V + 5)`. -/
theorem akhcPrime_step2_thetaBound
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    -- (P3′) `a.CFS.weaker`, the clauses used, copied verbatim from
    -- `SuperdiffusionCLT.Frozen.Section4.akhc_weakerP3`
    (beta L1 L2 : ℝ) (m3 : ℕ) (omegaSeq : ℕ → ℝ) (Psi : ℝ → ℝ) (KPsi pPsi : ℝ)
    (hbeta0 : 0 ≤ beta) (hL1 : 1 ≤ L1) (hL2 : 1 ≤ L2) (homega : ∀ k : ℕ, 0 < omegaSeq k)
    (hPsiOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ Psi t) (hKPsi : 1 ≤ KPsi)
    (hGrowthPsi : ∀ p : ℝ, 1 < p → p ≤ pPsi → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
      s ^ p ≤ KPsi ^ (3 * ⌈p⌉₊ ^ 2) * (Psi (t * s) / Psi t))
    (hP3 : ∀ j n : ℕ, m3 ≤ n → beta * (j : ℝ) < (n : ℝ) →
      (n : ℝ) < (j : ℝ) - L1 * Real.log (L2 * (n : ℝ)) →
      ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
        Measurable X ∧
        Homogenization.IndependentSums.IsBigO P.toMeasure Psi X (omegaSeq n) ∧
        ∀ (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (p q : Homogenization.BlockVec d),
          2 *
              (((Homogenization.descendantsAtDepth
                      (Homogenization.originCube d (j : ℤ)) (j - n)).card : ℝ)⁻¹ *
                ∑ R ∈ Homogenization.descendantsAtDepth
                    (Homogenization.originCube d (j : ℤ)) (j - n),
                  Homogenization.blockVecDot p
                    (Homogenization.blockMatVecMul
                      (Homogenization.ofFullBlockMat
                        (Homogenization.toFullBlockMat
                            (Homogenization.coarseBlockMatrix
                              (Homogenization.cubeSet R)
                              (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                  nu omega L).toCoeffField) -
                          Homogenization.toFullBlockMat
                            (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix
                              nu L P
                              (Homogenization.cubeSet
                                (Homogenization.originCube d (n : ℤ))))))
                      q)) ≤
            X omega *
              (Homogenization.blockVecDot p
                  (Homogenization.blockMatVecMul
                    (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                      (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ))))
                    p) +
                Homogenization.blockVecDot q
                  (Homogenization.blockMatVecMul
                    (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                      (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ))))
                    q)))
    {m k ell k0 : ℕ} (hmk : m ≤ k) (hell : 1 ≤ ell) (hellk : ell ≤ k) (hk2 : m2 ≤ k)
    (hk0k : k0 ≤ k) (hm3 : m3 ≤ k - ell) (hbeta : beta * (k : ℝ) < ((k - ell : ℕ) : ℝ))
    (hwin : ((k - ell : ℕ) : ℝ) < (k0 : ℝ) - L1 * Real.log (L2 * ((k - ell : ℕ) : ℝ)))
    {s' ρ η : ℝ} (hlo : 1 / 4 ≤ s') (hhi : s' < 1 / 2) (hgap : ρ / 2 < s')
    (hgammarho : gamma ≤ ρ) (heta2 : 2 < η) (hetaPsi : η ≤ pPsi)
    (hc : 0 < 2 * ρ - 2 * (d : ℝ) / η)
    (delta sigma : ℝ) (hdelta : 0 ≤ delta) (hsigma : 0 ≤ sigma)
    (hsmall : delta * sigma ^ 2 ≤ 1)
    (hPigeon :
      Homogenization.BlockMatLoewnerLE
        (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
          (Homogenization.cubeSet (Homogenization.originCube d ((k - ell : ℕ) : ℤ))))
        ((1 + delta * sigma ^ 2) •
          SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
            (Homogenization.cubeSet (Homogenization.originCube d (k : ℤ)))))
    (e : Vec d) (he : vecNormSq e = 1)
    {V cV : ℝ} (hV0 : 0 ≤ V) (hcV : 0 ≤ cV) (hVsmall : V ≤ cV * (delta * sigma ^ 2))
    (hV : ∀ n ∈ Finset.Icc (((k - ell : ℕ) : ℤ) + 1) (k : ℤ),
      ∫ a, SuperdiffusionCLT.AKHC61.Response.akhcFullBlockNormalizedFluctuationAtScale
          nu L P (k : ℤ) (originCube d n) a
        ∂(SuperdiffusionCLT.Section2.Annealed.cutoffLaw (d := d) nu L P) ≤ V)
    (hMsmall : 3 * KPsiS ^ 36 * (H * (k : ℝ) ^ D) ^ (2 : ℝ) *
            (3 : ℝ) ^ (-2 * (ρ - gamma) * ((k : ℝ) - ((k0 : ℝ) - 1))) / (min 3 pPsiS - 2) +
          (η / (η - 2)) * KPsi ^ (3 * ⌈η⌉₊ ^ 2) *
            KPsi ^ (2 * (3 * (⌈η⌉₊ : ℝ) ^ 2) / η) * omegaSeq (k - ell) ^ 2 *
            (1 - (3 : ℝ) ^ (-(2 * ρ - 2 * (d : ℝ) / η)))⁻¹ ≤ delta * sigma ^ 2)
    (hT1small : Real.rpow (3 : ℝ) (-(1 / 2 - s') * (ell : ℝ)) ^ 2 ≤ delta * sigma ^ 2)
    (hT2small : Real.rpow (3 : ℝ) (-(ell : ℝ)) ≤ delta * sigma ^ 2) :
    SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P k - 1 ≤
      2 * SuperdiffusionCLT.AKHC61.Step2.akhcJB_const d *
        (1 + Real.sqrt (akhcPrime_Kst d s' ρ * (cV + 5)) + akhcPrime_Kst d s' ρ * (cV + 5)) *
        (sigma * Real.sqrt delta + ((3 : ℝ) ^ ell)⁻¹) *
        SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m := by
  have hk : 0 < k := by omega
  have hPig := (SuperdiffusionCLT.AKHC61.Carrier.akhc_blockMatLoewnerLE_annealedBlockMatrix_smul_iff
    hnu L hJ4 ((k - ell : ℕ) : ℤ) (k : ℤ) (1 + delta * sigma ^ 2)).1 hPigeon
  have hη : 0 ≤ delta * sigma ^ 2 := mul_nonneg hdelta (sq_nonneg sigma)
  have hEn := akhcPrime_step2_energy_le_of_P3 hnu P L gamma H D m2 PsiS KPsiS pPsiS hgamma0
    hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hJ4 hPrefix hJ2 beta L1 L2 m3
    omegaSeq Psi KPsi pPsi hbeta0 hL1 hL2 homega hPsiOne hKPsi hGrowthPsi hP3 hell hellk hk2 hk0k
    hm3 hbeta hwin hlo hhi hgap hgammarho heta2 hetaPsi hc e he hη hsmall hPig.1 hPig.2 hV0 hV
  set Mx := 3 * KPsiS ^ 36 * (H * (k : ℝ) ^ D) ^ (2 : ℝ) *
            (3 : ℝ) ^ (-2 * (ρ - gamma) * ((k : ℝ) - ((k0 : ℝ) - 1))) / (min 3 pPsiS - 2) +
          (η / (η - 2)) * KPsi ^ (3 * ⌈η⌉₊ ^ 2) *
            KPsi ^ (2 * (3 * (⌈η⌉₊ : ℝ) ^ 2) / η) * omegaSeq (k - ell) ^ 2 *
            (1 - (3 : ℝ) ^ (-(2 * ρ - 2 * (d : ℝ) / η)))⁻¹ with hMxdef
  set T1 := Real.rpow (3 : ℝ) (-(1 / 2 - s') * (ell : ℝ)) ^ 2
  set T2 := Real.rpow (3 : ℝ) (-(ell : ℝ))
  set θk := SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P k
  set θm := SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m
  have hθk1 : 1 ≤ θk := SuperdiffusionCLT.AKHC61.Carrier.akhc_one_le_thetaCutoff_of_P2 hnu
    hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS
    hGrowth hP2 k
  have hanti : θk ≤ θm := SuperdiffusionCLT.AKHC61.Carrier.akhc_antitone_thetaCutoff_of_P2
    hnu hPrefix hJ2 hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne
    hKPsiS hpPsiS hGrowth hP2 hmk
  have hKst : 0 ≤ akhcPrime_Kst d s' ρ := by
    unfold akhcPrime_Kst akhcWeakC2_maximizerConst
    positivity
  have hT1 : 0 ≤ T1 := sq_nonneg _
  have hsum : V + delta * sigma ^ 2 + Mx + T1 * (1 + Mx) + T2 ≤
      (cV + 5) * (delta * sigma ^ 2) := by
    have h1 : T1 * (1 + Mx) ≤ T1 * 2 :=
      mul_le_mul_of_nonneg_left (by linarith only [hMsmall, hsmall]) hT1
    nlinarith only [hVsmall, hMsmall, h1, hT1small, hT2small]
  have hKw : 0 ≤ akhcPrime_Kst d s' ρ * (cV + 5) := mul_nonneg hKst (by linarith only [hcV])
  have hWsrc : akhcPrime_srcEnergy nu L P k e ≤
      akhcPrime_Kst d s' ρ * (cV + 5) * (delta * sigma ^ 2) * θm := by
    rw [akhcPrime_srcEnergy_eq_integral hnu P L gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH
      hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hJ4 hPrefix hJ2 hk2 hk e]
    refine hEn.trans ?_
    have hKθ : 0 ≤ akhcPrime_Kst d s' ρ * θk := mul_nonneg hKst (by linarith only [hθk1])
    calc akhcPrime_Kst d s' ρ * θk * (V + delta * sigma ^ 2 + Mx + T1 * (1 + Mx) + T2)
        ≤ akhcPrime_Kst d s' ρ * θk * ((cV + 5) * (delta * sigma ^ 2)) :=
          mul_le_mul_of_nonneg_left hsum hKθ
      _ = akhcPrime_Kst d s' ρ * (cV + 5) * (delta * sigma ^ 2) * θk := by ring
      _ ≤ akhcPrime_Kst d s' ρ * (cV + 5) * (delta * sigma ^ 2) * θm :=
          mul_le_mul_of_nonneg_left hanti (mul_nonneg hKw hη)
  exact akhcPrime_step2_thetaBound_src hnu P L gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH
    hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hJ4 hPrefix hJ2 m k ell hmk hellk hk2 hk delta
    sigma hdelta hsigma hsmall hPigeon e he _ hKw hWsrc

end Law

end

end SuperdiffusionCLT.AKHC61.WeakNorms
