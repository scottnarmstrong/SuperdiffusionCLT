/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.Step3.RecursionWB

/-!
# The weighted Step 3 recursion, part 3: `akhcRV2_weighted_recursion`

The Step 3 recursion with C6's weighted sums kept at a fixed base scale `k`:

`Θ_m - 1 ≤ θ_m (Θ_{m-Lstep} - 1) + (linConst/2)(Θ_m - 1)² + B_w · (Σ_{n ∈ (k,m]} w_n (Θ_n - Θ_m)
  + Σ_{n ∈ (k,m]} w_n (Θ_{n-ℓ(n)} - 1)² + Υ^{port} ω_{k-ℓ(k)}² + (P2′ tail at k₀)
  + 3^{-(1-2s')(m-k)})`, `w_n = 3^{-(1/2-s')(m-n)}`.

It composes `akhcRec_dropBound_of_P2` and `akhcRec_hrec_of_dropBound` (`Step3/Recursion*.lean`),
the sharp weak-norm sum `akhcRV2_weakSum_le` (`Step3/RecursionLinearWeakNorm.lean`), and the weighted energy
bound `akhcRW_energy_le` (`Step3/RecursionWB.lean`). The constants `akhcRW_Bw` and
`akhcRW_UpsPort` are the explicit definitions of `Step3/RecursionW.lean`.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.Step3

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.AKHC61.Carrier
open SuperdiffusionCLT.AKHC61.Response

noncomputable section

section Weighted

variable {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
  (P : ProbabilityMeasure (ShellSeq d)) (L : ℕ)
  (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ4 : ShellLawJ4 d P)
  (gamma H D : ℝ) (m2 : ℕ) (PsiS : ℝ → ℝ) (KPsiS pPsiS : ℝ)
  (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1) (hH : 1 ≤ H) (hD : 0 ≤ D)
  (hPsiSMono : MonotoneOn PsiS (Set.Ici 0)) (hPsiSOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ PsiS t)
  (hKPsiS : 1 ≤ KPsiS) (hpPsiS : 2 < pPsiS)
  (hGrowth : ∀ p : ℝ, 2 ≤ p → p ≤ pPsiS → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
    s ^ p ≤ KPsiS ^ (3 * ⌈p⌉₊ ^ 2) * (PsiS (t * s) / PsiS t))
  (hP2 : ∀ j : ℕ, m2 ≤ j →
    ∃ X : ShellSeq d → ℝ, Measurable X ∧
      Homogenization.IndependentSums.IsBigO P.toMeasure PsiS X (H * (j : ℝ) ^ D) ∧
      ∀ (omega : ShellSeq d) (Q : Homogenization.TriadicCube d),
        Q.scale ≤ (j : ℤ) →
        Homogenization.cubeCenter Q ∈
            Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)) →
          Homogenization.BlockMatLoewnerLE
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q)
              (coefficientCutoff nu omega L).toCoeffField)
            ((1 + (3 : ℝ) ^ (-(gamma * ((Q.scale : ℝ) - (j : ℝ)))) * X omega) •
              SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                (Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)))))
  (beta L1 L2 : ℝ) (m3 : ℕ) (omegaSeq : ℕ → ℝ) (Psi : ℝ → ℝ) (KPsi pPsi : ℝ)
  (hbeta0 : 0 ≤ beta) (hL1 : 1 ≤ L1) (hL2 : 1 ≤ L2) (homega : ∀ k : ℕ, 0 < omegaSeq k)
  (hPsiOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ Psi t) (hKPsi : 1 ≤ KPsi)
  (hGrowthPsi : ∀ p : ℝ, 1 < p → p ≤ pPsi → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
    s ^ p ≤ KPsi ^ (3 * ⌈p⌉₊ ^ 2) * (Psi (t * s) / Psi t))
  (hP3 : ∀ j n : ℕ, m3 ≤ n → beta * (j : ℝ) < (n : ℝ) →
    (n : ℝ) < (j : ℝ) - L1 * Real.log (L2 * (n : ℝ)) →
    ∃ X : ShellSeq d → ℝ,
      Measurable X ∧
      Homogenization.IndependentSums.IsBigO P.toMeasure Psi X (omegaSeq n) ∧
      ∀ (omega : ShellSeq d) (p q : Homogenization.BlockVec d),
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
                            (coefficientCutoff nu omega L).toCoeffField) -
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

include hnu hPrefix hJ2 hJ4 hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2
  hbeta0 hL1 hL2 homega hPsiOne hKPsi hGrowthPsi hP3

/-- **The weighted Step 3 recursion.** The Step 3 recursion's binders, with the
window data (`ell`, `δ₁`, `V`, the pigeonhole bounds) replaced by a fixed base scale `k`, the
(P3′) window at `k` for C3's `M⁺` moment (`m₃ ≤ k`, `β m < k`, `k < k₀ - L₁ log(L₂ k)`), the
per-scale (P3′) windows for the variance at every `n ∈ (k, m]`, `L₁ ≤ k`, and
`Θ_{k-ℓ(k)} ≤ 2`. With `w_n = 3^{-(1/2-s')(m-n)}`:
`Θ_m - 1 ≤ θ_m (Θ_{m-Lstep} - 1) + (linConst/2)(Θ_m - 1)² + B_w (Σ_n w_n (Θ_n - Θ_m) +
Σ_n w_n (Θ_{n-ℓ(n)} - 1)² + Υ^{port} ω_{k-ℓ(k)}² + (P2′ tail) + 3^{-(1-2s')(m-k)})`. -/
theorem akhcRV2_weighted_recursion (hd : 2 ≤ d) (homegaAnti : Antitone omegaSeq)
    {m k Lstep : ℕ} (hm2 : m2 ≤ m) (hkm : k < m) (hLstep : Lstep ≤ m)
    (e : Vec d) (he : vecNormSq e = 1)
    (hScaleSep :
      Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffOscillationConstant
          (Homogenization.originCube d (m : ℤ)) *
        Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffScaleSep
          (Homogenization.originCube d (m : ℤ)) Lstep ≤ (1 / 4 : ℝ))
    {s' rho eta : ℝ} (hlo : 1 / 4 ≤ s') (hhi : s' < 1 / 2) (hgap : rho / 2 < s')
    (hgammarho : gamma ≤ rho) (heta2 : 2 < eta) (hetaPsi : eta ≤ pPsi)
    (hc : 0 < 2 * rho - 2 * (d : ℝ) / eta)
    {k0 : ℕ} (hk0m : k0 ≤ m) (hm3 : m3 ≤ k) (hbeta : beta * (m : ℝ) < (k : ℝ))
    (hwin : (k : ℝ) < (k0 : ℝ) - L1 * Real.log (L2 * (k : ℝ)))
    (hkL1 : L1 ≤ (k : ℝ))
    (hwinE2 : ∀ n ∈ Finset.Icc (k + 1) m, 1 < L2 * (n : ℝ) ∧
      beta * (n : ℝ) <
        (n : ℝ) - (SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 n : ℝ) ∧
      m3 ≤ n - SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 n)
    (hΘ2 : SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P
      (k - SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 k) ≤ 2) :
    SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1 ≤
      (4 * (4 * (1 + Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffBound
              (Homogenization.originCube d (m : ℤ))) ^ 2 + 1 / 4) /
          (1 + 4 * (4 * (1 + Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffBound
              (Homogenization.originCube d (m : ℤ))) ^ 2 + 1 / 4))) *
        (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P (m - Lstep) - 1) +
      SuperdiffusionCLT.AKHC61.Step2.akhcJB_linConst d / 2 *
        (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1) ^ 2 +
      akhcRW_Bw d s' rho *
        (∑ n ∈ Finset.Icc (k + 1) m, (3 : ℝ) ^ (-(1 / 2 - s') * ((m : ℝ) - (n : ℝ))) *
            (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P n -
              SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m) +
          ∑ n ∈ Finset.Icc (k + 1) m, (3 : ℝ) ^ (-(1 / 2 - s') * ((m : ℝ) - (n : ℝ))) *
            (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P
              (n - SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 n) - 1) ^ 2 +
          akhcRW_UpsPort d eta rho KPsi *
            omegaSeq (k - SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 k) ^ 2 +
          3 * KPsiS ^ 36 * (H * (m : ℝ) ^ D) ^ (2 : ℝ) *
            (3 : ℝ) ^ (-2 * (rho - gamma) * ((m : ℝ) - ((k0 : ℝ) - 1))) / (min 3 pPsiS - 2) +
          (3 : ℝ) ^ (-(1 - 2 * s') * ((m : ℝ) - (k : ℝ)))) := by
  have hm0 : 0 < m := by omega
  have hEnergy := akhcRW_energy_le hnu P L hPrefix hJ2 hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0
    hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 beta L1 L2 m3 omegaSeq Psi KPsi
    pPsi hbeta0 hL1 hL2 homega hPsiOne hKPsi hGrowthPsi hP3 hd homegaAnti hm2 hkm hk0m hm3 hbeta
    hwin hkL1 hwinE2 hlo hhi hgap hgammarho heta2 hetaPsi hc e he hΘ2
  have hEqEnergy := SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_srcEnergy_eq_integral hnu P
    L gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth
    hP2 hJ4 hPrefix hJ2 (k := m) hm2 hm0 e
  rw [← hEqEnergy] at hEnergy
  set W := SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_srcEnergy nu L P m e with hW_def
  set Θm := SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m with hΘm_def
  set S := ∑ n ∈ Finset.Icc (k + 1) m, (3 : ℝ) ^ (-(1 / 2 - s') * ((m : ℝ) - (n : ℝ))) *
            (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P n - Θm) +
          ∑ n ∈ Finset.Icc (k + 1) m, (3 : ℝ) ^ (-(1 / 2 - s') * ((m : ℝ) - (n : ℝ))) *
            (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P
              (n - SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 n) - 1) ^ 2 +
          akhcRW_UpsPort d eta rho KPsi *
            omegaSeq (k - SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 k) ^ 2 +
          3 * KPsiS ^ 36 * (H * (m : ℝ) ^ D) ^ (2 : ℝ) *
            (3 : ℝ) ^ (-2 * (rho - gamma) * ((m : ℝ) - ((k0 : ℝ) - 1))) / (min 3 pPsiS - 2) +
          (3 : ℝ) ^ (-(1 - 2 * s') * ((m : ℝ) - (k : ℝ))) with hS_def
  set bound := 16 * akhcRW_Benergy d s' rho * S with hbound_def
  have hW_le : W ≤ bound := hEnergy
  have hW_nonneg : 0 ≤ W := by
    rw [hW_def, SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_srcEnergy]
    have hσ := akhcRec_sigmaHatScalar_pos hnu P L gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH
      hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hJ4 m
    have h1 : (0 : ℝ) ≤ akhc_sigmaHatScalar nu L P m *
        ∫ a, (Homogenization.Book.Ch04.canonicalScalarResponseGradientWeakNormCubeSet
            (Homogenization.originCube d (m : ℤ)) (1 / 2 : ℝ)
            (akhc_specialP nu L P m e)
            (akhc_specialQ nu L P m e)
            (SuperdiffusionCLT.AKHC61.Step2.akhc_step2P0 nu L P m e) a.toFun) ^ 2
          ∂(cutoffLaw (d := d) nu L P) :=
      mul_nonneg hσ.le (MeasureTheory.integral_nonneg fun _ => sq_nonneg _)
    have h2 : (0 : ℝ) ≤ (akhc_sigmaHatScalar nu L P m)⁻¹ *
        ∫ a, (Homogenization.Book.Ch04.canonicalScalarResponseFluxWeakNormCubeSet
            (Homogenization.originCube d (m : ℤ)) (1 / 2 : ℝ)
            (akhc_specialP nu L P m e)
            (akhc_specialQ nu L P m e)
            (SuperdiffusionCLT.AKHC61.Step2.akhc_step2Q0 nu L P m e) a.toFun) ^ 2
          ∂(cutoffLaw (d := d) nu L P) :=
      mul_nonneg (inv_nonneg.2 hσ.le) (MeasureTheory.integral_nonneg fun _ => sq_nonneg _)
    linarith only [h1, h2]
  have hbound_nonneg : 0 ≤ bound := hW_nonneg.trans hW_le
  have hlin_nonneg : 0 ≤ SuperdiffusionCLT.AKHC61.Step2.akhcJB_linConst d := by
    have hb := Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53_linearCutoffCoeff_le_dimensional
      (Homogenization.originCube d (m : ℤ)) (r := (1 : ℝ) / 2) (by norm_num) (by norm_num)
    have hc0 : (0 : ℝ) ≤ (Fintype.card (Fin d) : ℝ) *
        ((3 : ℝ) ^ ((d : ℝ) + (1 : ℝ) / 2) *
            Homogenization.cubeBesovScaleWeight (-(1 / 2 : ℝ))
              (Homogenization.originCube d (m : ℤ)) *
          Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffDualBound
            (Homogenization.originCube d (m : ℤ)) (1 / 2 : ℝ)) :=
      mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg (by positivity)
        (Homogenization.cubeBesovScaleWeight_nonneg _ _))
        (Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffDualBound_nonneg
          _ _))
    exact hc0.trans hb
  have hprod_nonneg : 0 ≤ SuperdiffusionCLT.AKHC61.Step2.akhcJB_prodConst d :=
    (Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffProductCoeff_nonneg
      (Homogenization.originCube d (m : ℤ)) (1 / 2 : ℝ) (1 / 2 : ℝ)).trans
      (Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffProductCoeff_origin_le_dimensional
        (d := d) m (s := 1 / 2) (t := 1 / 2) (by norm_num) (by norm_num))
  set source := SuperdiffusionCLT.AKHC61.Step2.akhcJB_linConst d / 2 * (Θm - 1) ^ 2 +
    (SuperdiffusionCLT.AKHC61.Step2.akhcJB_linConst d / 2 +
      SuperdiffusionCLT.AKHC61.Step2.akhcJB_prodConst d) * bound with hsource_def
  have hsource0 : 0 ≤ source := by
    have h1 : (0 : ℝ) ≤ SuperdiffusionCLT.AKHC61.Step2.akhcJB_linConst d / 2 * (Θm - 1) ^ 2 :=
      mul_nonneg (by linarith only [hlin_nonneg]) (sq_nonneg _)
    have h2 : (0 : ℝ) ≤ (SuperdiffusionCLT.AKHC61.Step2.akhcJB_linConst d / 2 +
        SuperdiffusionCLT.AKHC61.Step2.akhcJB_prodConst d) * bound :=
      mul_nonneg (by linarith only [hlin_nonneg, hprod_nonneg]) hbound_nonneg
    rw [hsource_def]
    linarith only [h1, h2]
  have hdropRaw := akhcRec_dropBound_of_P2 hnu P L hPrefix hJ2 hJ4 gamma H D m2 PsiS KPsiS pPsiS
    hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hm2 hm0 hLstep e he
    hScaleSep hsource0 (by
      dsimp only
      have hmain := akhcRV2_weakSum_le hnu P L hPrefix hJ2 hJ4 gamma H D m2 PsiS KPsiS pPsiS
        hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 m hm2 hm0 e he
      dsimp only at hmain
      unfold SuperdiffusionCLT.AKHC61.Step2.akhc_step2P0
        SuperdiffusionCLT.AKHC61.Step2.akhc_step2Q0 at hmain
      rw [← hΘm_def, ← hW_def] at hmain
      unfold Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.jUpperWeakNormManuscriptExpectedRHSAtScale
      dsimp only
      have hamgm := akhcRV2_mul_sqrt_le (x := Θm - 1) hW_nonneg
      have hlin_mono : SuperdiffusionCLT.AKHC61.Step2.akhcJB_linConst d *
            ((Θm - 1) * Real.sqrt W) ≤
          SuperdiffusionCLT.AKHC61.Step2.akhcJB_linConst d *
            ((1 / 2 : ℝ) * (Θm - 1) ^ 2 + (1 / 2 : ℝ) * W) :=
        mul_le_mul_of_nonneg_left hamgm hlin_nonneg
      have hlinW : SuperdiffusionCLT.AKHC61.Step2.akhcJB_linConst d * W ≤
          SuperdiffusionCLT.AKHC61.Step2.akhcJB_linConst d * bound :=
        mul_le_mul_of_nonneg_left hW_le hlin_nonneg
      have hprod_mono : SuperdiffusionCLT.AKHC61.Step2.akhcJB_prodConst d * W ≤
          SuperdiffusionCLT.AKHC61.Step2.akhcJB_prodConst d * bound :=
        mul_le_mul_of_nonneg_left hW_le hprod_nonneg
      rw [hsource_def]
      linarith only [hmain, hlin_mono, hlinW, hprod_mono])
  have hCbound_nonneg :
      0 ≤ Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffBound
        (Homogenization.originCube d (m : ℤ)) :=
    Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffBound_nonneg _
  set Ctotal := 4 * (1 + Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffBound
    (Homogenization.originCube d (m : ℤ))) ^ 2 + 1 / 4 with hCtotal_def
  have hCge1 : (1 : ℝ) ≤ 1 +
      Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffBound
        (Homogenization.originCube d (m : ℤ)) := by linarith only [hCbound_nonneg]
  have hCtotal_ge1 : (1 : ℝ) ≤ Ctotal := by rw [hCtotal_def]; nlinarith only [hCge1]
  have hCtotal_pos : 0 < Ctotal := by linarith only [hCtotal_ge1]
  have hdrop : (1 / 4 : ℝ) * (Θm - 1) ≤
      Ctotal * ((SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P (m - Lstep) - 1) -
        (Θm - 1) + ((0 : ℝ) + source)) := by
    have hsc : source ≤ Ctotal * source := by nlinarith only [hsource0, hCtotal_ge1]
    nlinarith only [hdropRaw, hsc]
  have hwrap := akhcRec_hrec_of_dropBound hCtotal_pos (le_refl (0 : ℝ)) hsource0 hdrop
  have hBw : (SuperdiffusionCLT.AKHC61.Step2.akhcJB_linConst d / 2 +
      SuperdiffusionCLT.AKHC61.Step2.akhcJB_prodConst d) * bound =
      akhcRW_Bw d s' rho * S := by
    rw [hbound_def, akhcRW_Bw]; ring
  rw [hsource_def, hBw] at hwrap
  linarith only [hwrap]

end Weighted

/-! ## Satisfiability of the scale and window hypotheses -/

end

end SuperdiffusionCLT.AKHC61.Step3
