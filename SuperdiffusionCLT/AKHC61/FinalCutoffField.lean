/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.FinalStepTwoM0

/-!
# AK.HC Theorem 6.1 (`t.weaker.P3`), version 5, for the cutoff field

`akhc_weakerP3_port` proves the statement of the V5 anchor
`SuperdiffusionCLT/Frozen/Section4/AKHCWeakerP3.lean` (read, never imported here), with
the statement body copied verbatim from that file.

The constants, depending on `d` only:
* `C := akhcDim_C d`, the maximum of Step 3's `C_min(d)`, the `Υ₁` comparison constant
  `B c_Υ/ζ`, Step 2's `ω`-constant `akhcDim_Comega d` and its `m₀`-constants
  `2 c_L N₁`, `4 c_L + 1`;
* `c := 1/2` (logically inert in the statement);
* `α := κ(d) = akhcCL5_kappa d ∈ (0, 1/48]`.

The proof runs `akhcF1_core` at `σ := σ_d` with `hOmega` from `akhcDim_hOmega`, `hm0` from
`akhcDim_m0Req` and `hStep3` from `akhcStep3_decay` (`U = akhcCL5_U d K_Ψ`, `C_s = 1`,
`κ = κ(d)`), then converts the conclusion: `U ≤ C K_Ψ^{6(d+1)²}` (`akhcCL5_U_le`),
`min{d+1, p_Ψ} - d = 1`, and `3^{-κ t} ≤ C 3^{-min{α,(1-γ)/2} t}` for `t ≥ 0`.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61

noncomputable section

/-- **The constant `C(d)` of V5.** -/
def akhcDim_C (d : ℕ) [NeZero d] : ℝ :=
  max (max (SuperdiffusionCLT.AKHC61.Step3.akhcCL5_Cmin d)
      (SuperdiffusionCLT.AKHC61.Step3.akhcCL5_B d *
        SuperdiffusionCLT.AKHC61.Step3.akhcCL5_cUps d /
          SuperdiffusionCLT.AKHC61.Step3.akhcCL5_zeta d))
    (max (akhcDim_Comega d) (max (2 * akhcDim_cL d * (akhcDim_N1 d : ℝ)) (4 * akhcDim_cL d + 1)))

theorem akhcDim_C_props (d : ℕ) [NeZero d] :
    SuperdiffusionCLT.AKHC61.Step3.akhcCL5_Cmin d ≤ akhcDim_C d ∧
      SuperdiffusionCLT.AKHC61.Step3.akhcCL5_B d *
          SuperdiffusionCLT.AKHC61.Step3.akhcCL5_cUps d /
            SuperdiffusionCLT.AKHC61.Step3.akhcCL5_zeta d ≤ akhcDim_C d ∧
      akhcDim_Comega d ≤ akhcDim_C d ∧
      2 * akhcDim_cL d * (akhcDim_N1 d : ℝ) ≤ akhcDim_C d ∧
      4 * akhcDim_cL d + 1 ≤ akhcDim_C d ∧ 16 ≤ akhcDim_C d := by
  have h1 : SuperdiffusionCLT.AKHC61.Step3.akhcCL5_Cmin d ≤ akhcDim_C d :=
    (le_max_left _ _).trans (le_max_left _ _)
  have h16 : (16 : ℝ) ≤ SuperdiffusionCLT.AKHC61.Step3.akhcCL5_Cmin d :=
    (le_max_left _ _).trans (le_max_left _ _)
  refine ⟨h1, (le_max_right _ _).trans (le_max_left _ _),
    (le_max_left _ _).trans (le_max_right _ _), ?_, ?_, h16.trans h1⟩
  · exact ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  · exact ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)

/-- **AK.HC Theorem 6.1 (`t.weaker.P3`), version 5, for the infrared cutoff field.** The
statement is that of `SuperdiffusionCLT.Frozen.Section4.akhc_weakerP3`, verbatim. -/
theorem akhc_weakerP3_port (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∃ alpha : ℝ, 0 < alpha ∧ alpha < 1 ∧
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : MeasureTheory.ProbabilityMeasure
              (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          ∀ L : ℕ,
          -- (P2') `a.ellipticity.weaker`
          ∀ (gamma H D : ℝ) (m2 : ℕ) (PsiS : ℝ → ℝ) (KPsiS pPsiS : ℝ),
            0 ≤ gamma → gamma ≤ 1 / 2 → 1 ≤ H → 0 ≤ D →
            MonotoneOn PsiS (Set.Ici 0) → (∀ t : ℝ, 0 ≤ t → 1 ≤ PsiS t) →
            1 ≤ KPsiS → 3 ≤ pPsiS →
            (∀ p : ℝ, 2 ≤ p → p ≤ pPsiS → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
              s ^ p ≤ KPsiS ^ (3 * ⌈p⌉₊ ^ 2) * (PsiS (t * s) / PsiS t)) →
            (∀ j : ℕ, m2 ≤ j →
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
                            (Homogenization.originCube d (j : ℤ))))) →
          -- (P3') `a.CFS.weaker`
          ∀ (beta L1 L2 : ℝ) (m3 : ℕ) (omegaSeq : ℕ → ℝ) (Psi : ℝ → ℝ) (KPsi pPsi : ℝ),
            0 ≤ beta → beta ≤ 1 / 2 → 1 ≤ L1 → 1 ≤ L2 →
            (∀ k : ℕ, 0 < omegaSeq k) → Antitone omegaSeq →
            Filter.Tendsto omegaSeq Filter.atTop (nhds 0) →
            StrictMonoOn Psi (Set.Ici 0) → (∀ t : ℝ, 0 ≤ t → 1 ≤ Psi t) →
            1 ≤ KPsi → (d : ℝ) + 1 ≤ pPsi →
            (∀ p : ℝ, 1 < p → p ≤ pPsi → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
              s ^ p ≤ KPsi ^ (3 * ⌈p⌉₊ ^ 2) * (Psi (t * s) / Psi t)) →
            (∀ j n : ℕ, m3 ≤ n → beta * (j : ℝ) < (n : ℝ) →
              (n : ℝ) < (j : ℝ) - L1 * Real.log (L2 * (n : ℝ)) →
              ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                Measurable X ∧
                Homogenization.IndependentSums.IsBigO P.toMeasure Psi X (omegaSeq n) ∧
                ∀ (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
                  (p q : Homogenization.BlockVec d),
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
                            q))) →
          -- the conclusion
          ∀ m m0 : ℕ, max m2 m3 ≤ m →
            omegaSeq m ^ 2 ≤
              (C * KPsi ^ (6 * (d + 1) ^ 2) / (min ((d : ℝ) + 1) pPsi - (d : ℝ)))⁻¹ →
            C * (L1 + (1 + D) / (1 - gamma)) * (1 + D) / ((1 - beta) * (1 - gamma)) *
                Real.log
                  ((C * KPsi ^ (6 * (d + 1) ^ 2) / (min ((d : ℝ) + 1) pPsi - (d : ℝ)) +
                      C / (min 3 pPsiS - 2) *
                        Real.exp (C * ((L1 + D / (1 - gamma)) * Real.log (2 * L2) +
                          (D + Real.log (H + KPsiS)) / (1 - gamma)))) *
                    ((m : ℝ) + (m0 : ℝ) + 1) *
                    SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P 0) *
                Real.log (3 * SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P 0 *
                  (2 + L1 * Real.log
                  ((C * KPsi ^ (6 * (d + 1) ^ 2) / (min ((d : ℝ) + 1) pPsi - (d : ℝ)) +
                      C / (min 3 pPsiS - 2) *
                        Real.exp (C * ((L1 + D / (1 - gamma)) * Real.log (2 * L2) +
                          (D + Real.log (H + KPsiS)) / (1 - gamma)))) *
                    ((m : ℝ) + (m0 : ℝ) + 1) *
                    SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P 0))) ≤
              (m0 : ℝ) →
            ∀ n : ℕ, m + 4 * m0 ≤ n →
              SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P n - 1 ≤
                C * KPsi ^ (6 * (d + 1) ^ 2) / (min ((d : ℝ) + 1) pPsi - (d : ℝ)) *
                    omegaSeq m ^ 2 +
                  C * (3 : ℝ) ^
                    (-(min alpha ((1 - gamma) / 2) * ((n : ℝ) - (m : ℝ) - 4 * (m0 : ℝ))))
    := by
  obtain ⟨hCmin, hCU, hCom, hCa, hCb, hC16⟩ := akhcDim_C_props d
  have hκ0 := SuperdiffusionCLT.AKHC61.Step3.akhcCL5_kappa_pos d
  have hκ1 := SuperdiffusionCLT.AKHC61.Step3.akhcCL5_kappa_le_small d hd
  refine ⟨akhcDim_C d, by linarith only [hC16], 1 / 2, by norm_num, by norm_num,
    SuperdiffusionCLT.AKHC61.Step3.akhcCL5_kappa d, hκ0, by linarith only [hκ1], ?_⟩
  intro nu hnu _hnu1 P hPrefix hJ2 hJ4 L gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma hH hD
    hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 beta L1 L2 m3 omegaSeq Psi KPsi pPsi hbeta0
    hbeta hL1 hL2 homega homegaAnti _hTendsto _hStrict hPsiOne hKPsi hpPsi hGrowthPsi hP3 m m0
    hm hOm hthr n hn
  have hC1 : (1 : ℝ) ≤ akhcDim_C d := by linarith only [hC16]
  have hC2 : (2 : ℝ) ≤ akhcDim_C d := by linarith only [hC16]
  have hgamma1 : gamma < 1 := by linarith only [hgamma]
  have hpPsiS2 : 2 < pPsiS := by linarith only [hpPsiS]
  have hpPsi' : (d : ℝ) < pPsi := by linarith only [hpPsi]
  have hσ0 := SuperdiffusionCLT.AKHC61.Step3.akhcCL5_sigma_pos d
  have hσ1 : SuperdiffusionCLT.AKHC61.Step3.akhcCL5_sigma d < 1 := by
    obtain ⟨hσε, -, -⟩ := SuperdiffusionCLT.AKHC61.Step3.akhcCL5_sigma_props hσ0.le
      (le_refl (SuperdiffusionCLT.AKHC61.Step3.akhcCL5_sigma d))
    have hε := SuperdiffusionCLT.AKHC61.Step3.akhcCL5_eps_le d
    linarith only [hσε, hε]
  have hΘ0 := SuperdiffusionCLT.AKHC61.Carrier.akhc_one_le_thetaCutoff_of_P2 hnu hJ4
    gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS2
    hGrowth hP2 (L := L) 0
  have hOmega := akhcDim_hOmega hd hgamma hpPsi hpPsiS hKPsi hC1 hCom hOm
    (gamma := gamma) (pPsiS := pPsiS)
  have hm0 := akhcDim_m0Req hd hgamma0 hgamma hbeta0 hbeta hpPsi hpPsiS hL1 hL2 hH hD hKPsiS
    hKPsi hΘ0 hC2 hCa hCb hthr
  have hStep3 := SuperdiffusionCLT.AKHC61.Step3.akhcStep3_decay hnu P L hPrefix hJ2 hJ4
    gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth
    hP2 beta L1 L2 m3 omegaSeq Psi KPsi pPsi hbeta0 hbeta hL1 hL2 homega homegaAnti hPsiOne
    hKPsi hpPsi hGrowthPsi hP3 hd hm hσ0 le_rfl hCmin hOm hthr
  have hF1 := SuperdiffusionCLT.AKHC61.Core.akhcF1_core hnu L P hPrefix hJ2 hJ4 hd gamma H
    D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS2 hGrowth hP2
    beta L1 L2 m3 omegaSeq Psi KPsi pPsi hbeta0 hL1 hL2 homega homegaAnti hPsiOne hKPsi hpPsi'
    hGrowthPsi hP3 hm hσ0 hσ1 (SuperdiffusionCLT.AKHC61.Step3.akhcCL5_U d KPsi) 1
    (SuperdiffusionCLT.AKHC61.Step3.akhcCL5_kappa d) hOmega hm0 hStep3
  have h := hF1.2 n hn
  -- the `ω_m²` term
  have hmin : min ((d : ℝ) + 1) pPsi - (d : ℝ) = 1 := by rw [min_eq_left hpPsi]; ring
  rw [hmin, div_one]
  have hKp0 : 0 ≤ KPsi ^ (6 * (d + 1) ^ 2) := pow_nonneg (by linarith only [hKPsi]) _
  have hUle := SuperdiffusionCLT.AKHC61.Step3.akhcCL5_U_le d hd hKPsi
  have hUC : SuperdiffusionCLT.AKHC61.Step3.akhcCL5_U d KPsi ≤
      akhcDim_C d * KPsi ^ (6 * (d + 1) ^ 2) :=
    hUle.trans (mul_le_mul_of_nonneg_right hCU hKp0)
  have hω : SuperdiffusionCLT.AKHC61.Step3.akhcCL5_U d KPsi * omegaSeq m ^ 2 ≤
      akhcDim_C d * KPsi ^ (6 * (d + 1) ^ 2) * omegaSeq m ^ 2 :=
    mul_le_mul_of_nonneg_right hUC (sq_nonneg _)
  -- the decay term
  have hnR : ((m + 4 * m0 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  push_cast at hnR
  have ht : 0 ≤ (n : ℝ) - (m : ℝ) - 4 * (m0 : ℝ) := by linarith only [hnR]
  have hmu : min (SuperdiffusionCLT.AKHC61.Step3.akhcCL5_kappa d) ((1 - gamma) / 2) ≤
      SuperdiffusionCLT.AKHC61.Step3.akhcCL5_kappa d := min_le_left _ _
  have hexp : -(SuperdiffusionCLT.AKHC61.Step3.akhcCL5_kappa d *
        ((n : ℝ) - (m : ℝ) - 4 * (m0 : ℝ))) ≤
      -(min (SuperdiffusionCLT.AKHC61.Step3.akhcCL5_kappa d) ((1 - gamma) / 2) *
        ((n : ℝ) - (m : ℝ) - 4 * (m0 : ℝ))) :=
    neg_le_neg (mul_le_mul_of_nonneg_right hmu ht)
  have h3 := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexp
  set y := (3 : ℝ) ^ (-(min (SuperdiffusionCLT.AKHC61.Step3.akhcCL5_kappa d)
    ((1 - gamma) / 2) * ((n : ℝ) - (m : ℝ) - 4 * (m0 : ℝ)))) with hy
  have hy0 : 0 ≤ y := Real.rpow_nonneg (by norm_num) _
  have hyC : y ≤ akhcDim_C d * y := le_mul_of_one_le_left hy0 hC1
  linarith only [h, hω, h3, hyC]

end

end SuperdiffusionCLT.AKHC61
