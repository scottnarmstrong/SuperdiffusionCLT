/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.HomogBelow.ThetaLmMainB
public import SuperdiffusionCLT.Section4.HomogBelow.ThetaLmAssemblyAKHCApp
public import SuperdiffusionCLT.Section4.HomogBelow.ThetaLmFinalBigLog
public import SuperdiffusionCLT.Section4.HomogBelow.ThetaLmFinalMonoM
public import SuperdiffusionCLT.Section4.HomogBelow.ThetaLmFinalExpDecay
public import SuperdiffusionCLT.Section4.HomogBelow.ThetaLmFinalSmallness
public import SuperdiffusionCLT.Section4.HomogBelow.M0ThresholdC
public import SuperdiffusionCLT.Assumptions.ShellLaw.J5Consequences
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5

/-!
The display `e.Theta.Lm.final.bound` of the paper,
in exactly the form of the `hThetaLm` binder of `homogBelow_from_thetaLm`
(`FromThetaLm.lean`): from the body of [AK, Theorem 6.1] and the mixing body, both
taken as the leading arguments of the binder type.

The proof is Steps 1-3 of `p.homog.below`. The constants are fixed first
(the constants `C₆₁, α₆₁` of [AK, Theorem 6.1], the mixing `C_mix`, the `m₃`-headroom
witness `c`, the smallness threshold at `8 Υ₁`, the two `m₀`-thresholds and the two
exponential-remainder thresholds),
then the final `C` is their maximum. At each `(ν, P, L, m)` the startup scale is
`m₀ = ⌈C_b log² L⌉₊` when `m ≤ L²` and `m₀ = ⌈C_b log² m⌉₊` when `L² ≤ m`; the rest is
`homogBelow_thetaLm_of_m0` (`ThetaLmMainB.lean`). -/

@[expose] public section

namespace SuperdiffusionCLT.Section4.HomogBelow

/-- **`e.Theta.Lm.final.bound`**, with exactly the type of the `hThetaLm` binder of
`homogBelow_from_thetaLm`. -/
theorem homogBelow_thetaLm (d : ℕ) [NeZero d] :
  (hd' : 2 ≤ d) →
  (hAKHC' : ∃ C : ℝ, 1 ≤ C ∧ ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∃ alpha : ℝ, 0 < alpha ∧ alpha < 1 ∧
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : MeasureTheory.ProbabilityMeasure
              (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          ∀ L : ℕ,
          -- (P2') [AK] `a.ellipticity.weaker`
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
          -- (P3') [AK] `a.CFS.weaker`
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
          -- the conclusion of [AK]
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
                    (-(min alpha ((1 - gamma) / 2) * ((n : ℝ) - (m : ℝ) - 4 * (m0 : ℝ))))) →
  (hMix' : ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : MeasureTheory.ProbabilityMeasure
              (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          ∀ m n L : ℕ, 1 ≤ L →
            (L : ℝ) - (n : ℝ) ≤
              C⁻¹ *
                (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
                    (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)))) ^
                  (2 : ℝ) →
            m < 2 * n →
            (n : ℤ) ≤ (m : ℤ) - ⌈C * Real.log (nu⁻¹ * (L : ℝ))⌉ →
            ⌈C * Real.log (nu⁻¹ * (L : ℝ))⌉ ≤ (n : ℤ) →
            (n : ℤ) ≤ (m : ℤ) - ⌈C * Real.log (nu⁻¹ * (n : ℝ))⌉ →
            ((m : ℝ) ≤ (L : ℝ) + C * Real.log (nu⁻¹ * (L : ℝ)) →
              ∃ X1 X2 X3 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                Measurable X1 ∧
                Homogenization.IndependentSums.IsBigO P.toMeasure
                    (Homogenization.IndependentSums.gammaSigma 2) X1
                    (C * ((L - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
                      (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
                          (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)))) ^
                        (-(1 : ℝ))) ∧
                Measurable X2 ∧
                Homogenization.IndependentSums.IsBigO P.toMeasure
                    (Homogenization.IndependentSums.gammaSigma 1) X2
                    (C * ((L - n : ℕ) : ℝ) *
                      (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
                          (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)))) ^
                        (-(2 : ℝ))) ∧
                Measurable X3 ∧
                Homogenization.IndependentSums.IsBigO P.toMeasure
                    (Homogenization.IndependentSums.gammaSigma ((1 : ℝ) / 3)) X3
                    (C * (m : ℝ) ^ (-(3000 : ℝ))) ∧
                  ∀ (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
                    (p q : Homogenization.BlockVec d),
                    2 *
                        (((Homogenization.descendantsAtDepth
                                (Homogenization.originCube d (m : ℤ)) (m - n)).card : ℝ)⁻¹ *
                          ∑ R ∈ Homogenization.descendantsAtDepth
                              (Homogenization.originCube d (m : ℤ)) (m - n),
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
                      (X1 omega + X2 omega + X3 omega) *
                        (Homogenization.blockVecDot p
                            (Homogenization.blockMatVecMul
                              (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                                (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ))))
                              p) +
                          Homogenization.blockVecDot q
                            (Homogenization.blockMatVecMul
                              (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                                (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ))))
                              q))) ∧
            ((L : ℝ) + C * Real.log (nu⁻¹ * (L : ℝ)) < (m : ℝ) →
              ∃ X4 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                Measurable X4 ∧
                Homogenization.IndependentSums.IsBigO P.toMeasure
                    (Homogenization.IndependentSums.gammaSigma 1) X4
                    (C * (m : ℝ) ^ (-(3000 : ℝ))) ∧
                  ∀ (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
                    (p q : Homogenization.BlockVec d),
                    2 *
                        (((Homogenization.descendantsAtDepth
                                (Homogenization.originCube d (m : ℤ)) (m - n)).card : ℝ)⁻¹ *
                          ∑ R ∈ Homogenization.descendantsAtDepth
                              (Homogenization.originCube d (m : ℤ)) (m - n),
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
                      X4 omega *
                        (Homogenization.blockVecDot p
                            (Homogenization.blockMatVecMul
                              (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                                (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ))))
                              p) +
                          Homogenization.blockVecDot q
                            (Homogenization.blockMatVecMul
                              (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                                (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ))))
                              q)))) →
  ∃ C : ℝ, 1 ≤ C ∧
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
        ∀ alpha M : ℝ, 0 ≤ alpha → alpha < 1 → 1 ≤ M →
          ∀ L m : ℕ,
            SuperdiffusionCLT.Frozen.Section4.lNaught C (C * M) alpha cStar nu K ≤ (L : ℝ) →
            (L : ℝ) - M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (m : ℝ) →
            SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1 ≤
              (C * (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu L P) ^
                  (-(2 : ℝ)) *
                max 0 ((L : ℝ) - (m : ℝ) + C * Real.log (L : ℝ) ^ (2 : ℝ)) *
                (if (m : ℝ) ≤ (L : ℝ) + C * Real.log (L : ℝ) ^ (2 : ℝ)
                 then (1 : ℝ) else 0)) +
              C * (m : ℝ) ^ (-(3000 : ℝ))
    := by
  intro hd hAKHC hMix
  obtain ⟨C61, hC61, _c61, _hc61, _hc61', alpha61, ha61, ha61', hAKHCraw⟩ := hAKHC
  obtain ⟨Cmix, hCmix1, hMixraw⟩ := hMix
  -- `Υ₁` and `κ`.
  have hgc1 : (1 : ℝ) ≤ Homogenization.IndependentSums.gammaGrowthConst (1 / 3) :=
    le_trans one_le_two (Homogenization.IndependentSums.two_le_gammaGrowthConst _)
  have hU1 : (1 : ℝ) ≤ C61 * (Homogenization.IndependentSums.gammaGrowthConst (1/3)) ^
      (6 * (d + 1) ^ 2) / (min ((d : ℝ) + 1) ((d : ℝ) + 1) - (d : ℝ)) := by
    have hmin : min ((d : ℝ) + 1) ((d : ℝ) + 1) - (d : ℝ) = 1 := by rw [min_self]; ring
    rw [hmin, div_one]
    have hp : (1 : ℝ) ≤ (Homogenization.IndependentSums.gammaGrowthConst (1/3)) ^
        (6 * (d + 1) ^ 2) := one_le_pow₀ hgc1
    nlinarith only [hp, hC61]
  have hU : (0 : ℝ) < C61 * (Homogenization.IndependentSums.gammaGrowthConst (1/3)) ^
      (6 * (d + 1) ^ 2) / (min ((d : ℝ) + 1) ((d : ℝ) + 1) - (d : ℝ)) :=
    lt_of_lt_of_le one_pos hU1
  have hκ : (0 : ℝ) < min alpha61 ((1 - (1/2 : ℝ)) / 2) := lt_min ha61 (by norm_num)
  -- The thresholds, all fixed before the final constant.
  obtain ⟨C1h, c, hC1h, hc, hHead⟩ := homogBelow_m3_headroom d hd Cmix hCmix1
  have hKappa3 : (0 : ℝ) ≤ c * max 1 (3 / c) :=
    mul_nonneg hc.le (le_trans zero_le_one (le_max_left _ _))
  obtain ⟨C1s, _r, hC1s, _hr, hSm⟩ := homogBelow_smallness d hd Cmix hCmix1
    (8 * (C61 * (Homogenization.IndependentSums.gammaGrowthConst (1/3)) ^
      (6 * (d + 1) ^ 2) / (min ((d : ℝ) + 1) ((d : ℝ) + 1) - (d : ℝ))))
    (by linarith only [hU1]) (c * max 1 (3 / c)) hKappa3
  obtain ⟨CB, _hCB, hM0B⟩ := homogBelowM0_threshold_corrected C61 hC61 Cmix hCmix1
    (homogBelow_Cellip d hd) (homogBelow_Cellip_ge1 d hd) d hd
  obtain ⟨CC, _hCC, hM0C⟩ := homogBelowM0_threshold_large_m C61 hC61 Cmix hCmix1
    (homogBelow_Cellip d hd) (homogBelow_Cellip_ge1 d hd) d hd
  obtain ⟨CE6, hCE6, hE6⟩ := homogBelow_expDecay_le_polyDecay _ hκ C61 hC61 6000
  obtain ⟨CE3, _hCE3, hE3⟩ := homogBelow_expDecay_le_polyDecay _ hκ C61 hC61 3000
  set Cb : ℝ := max (max CB CC) (max CE6 CE3) with hCbdef
  have hCB_Cb : CB ≤ Cb := le_trans (le_max_left _ _) (le_max_left _ _)
  have hCC_Cb : CC ≤ Cb := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCE6_Cb : CE6 ≤ Cb := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCE3_Cb : CE3 ≤ Cb := le_trans (le_max_right _ _) (le_max_right _ _)
  have hCb1 : (1 : ℝ) ≤ Cb := le_trans hCE6 hCE6_Cb
  obtain ⟨C1t, hC1t, hMt⟩ := homogBelow_mtilde_ge_m3 Cb hCb1 Cmix hCmix1
  obtain ⟨C1B, hC1B, hLM⟩ := homogBelow_largeM_headroom Cb (by linarith only [hCb1]) Cmix hCmix1
  obtain ⟨C1L, hC1L, hL3⟩ := homogBelow_L_ge_of_lNaught 3
  -- The final constant.
  set Cfin : ℝ := max (max (max C1h C1s) (max C1t C1B))
    (max (max C1L Cb) (max (5 * Cb + 5) (max
      ((C61 * (Homogenization.IndependentSums.gammaGrowthConst (1/3)) ^
        (6 * (d + 1) ^ 2) / (min ((d : ℝ) + 1) ((d : ℝ) + 1) - (d : ℝ))) *
        (3 * (Homogenization.IndependentSums.gammaTriangleConst ((1 : ℝ) / 3)) ^ 2 *
          (4 * Cmix ^ 2 + 16 * Cmix)))
      ((C61 * (Homogenization.IndependentSums.gammaGrowthConst (1/3)) ^
        (6 * (d + 1) ^ 2) / (min ((d : ℝ) + 1) ((d : ℝ) + 1) - (d : ℝ))) *
        (3 * (Homogenization.IndependentSums.gammaTriangleConst ((1 : ℝ) / 3)) ^ 2 * 9 *
          Cmix ^ 2) * (2 : ℝ) ^ (6000 : ℝ) + 1)))) with hCfindef
  have hA := le_max_left (max (max C1h C1s) (max C1t C1B)) (max (max C1L Cb) (max (5 * Cb + 5) (max
      ((C61 * (Homogenization.IndependentSums.gammaGrowthConst (1/3)) ^
        (6 * (d + 1) ^ 2) / (min ((d : ℝ) + 1) ((d : ℝ) + 1) - (d : ℝ))) *
        (3 * (Homogenization.IndependentSums.gammaTriangleConst ((1 : ℝ) / 3)) ^ 2 *
          (4 * Cmix ^ 2 + 16 * Cmix)))
      ((C61 * (Homogenization.IndependentSums.gammaGrowthConst (1/3)) ^
        (6 * (d + 1) ^ 2) / (min ((d : ℝ) + 1) ((d : ℝ) + 1) - (d : ℝ))) *
        (3 * (Homogenization.IndependentSums.gammaTriangleConst ((1 : ℝ) / 3)) ^ 2 * 9 *
          Cmix ^ 2) * (2 : ℝ) ^ (6000 : ℝ) + 1))))
  have hB := le_max_right (max (max C1h C1s) (max C1t C1B)) (max (max C1L Cb) (max (5 * Cb + 5) (max
      ((C61 * (Homogenization.IndependentSums.gammaGrowthConst (1/3)) ^
        (6 * (d + 1) ^ 2) / (min ((d : ℝ) + 1) ((d : ℝ) + 1) - (d : ℝ))) *
        (3 * (Homogenization.IndependentSums.gammaTriangleConst ((1 : ℝ) / 3)) ^ 2 *
          (4 * Cmix ^ 2 + 16 * Cmix)))
      ((C61 * (Homogenization.IndependentSums.gammaGrowthConst (1/3)) ^
        (6 * (d + 1) ^ 2) / (min ((d : ℝ) + 1) ((d : ℝ) + 1) - (d : ℝ))) *
        (3 * (Homogenization.IndependentSums.gammaTriangleConst ((1 : ℝ) / 3)) ^ 2 * 9 *
          Cmix ^ 2) * (2 : ℝ) ^ (6000 : ℝ) + 1))))
  rw [← hCfindef] at hA hB
  have hC1h_C : C1h ≤ Cfin := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hA
  have hC1s_C : C1s ≤ Cfin := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hA
  have hC1t_C : C1t ≤ Cfin := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hA
  have hC1B_C : C1B ≤ Cfin := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hA
  have hC1L_C : C1L ≤ Cfin := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hB
  have hCb_C : Cb ≤ Cfin := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hB
  have hB' := le_trans (le_max_right _ _) hB
  have hC5_C : 5 * Cb + 5 ≤ Cfin := le_trans (le_max_left _ _) hB'
  have hB'' := le_trans (le_max_right _ _) hB'
  have hCA_C := le_trans (le_max_left _ _) hB''
  have hCB2_C := le_trans (le_max_right _ _) hB''
  have hCfin1 : (1 : ℝ) ≤ Cfin := le_trans hC1h hC1h_C
  refine ⟨Cfin, hCfin1, ?_⟩
  intro nu cStar K hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 alpha M halpha0 halpha1 hM L m hL hScale
  have hcS : 0 < cStar := hJ5.cStar_pos
  have hcS2 : cStar ≤ 2 := SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5.cStar_le_two hJ5
  have hK0 : 0 ≤ K := hJ5.K_pos.le
  have hL3R : (3 : ℝ) ≤ (L : ℝ) :=
    hL3 Cfin hC1L_C M alpha cStar nu K hM halpha0 halpha1 hcS hcS2 hnu hnu1 hK0 L hL
  have hL1 : 1 ≤ L := by exact_mod_cast (show (1 : ℝ) ≤ (L : ℝ) by linarith only [hL3R])
  have hLCb : SuperdiffusionCLT.Frozen.Section4.lNaught Cb M alpha cStar nu K ≤ (L : ℝ) :=
    le_trans (SuperdiffusionCLT.Section4.LNaught.lNaught_mono_both
      (by linarith only [hCb1]) hCb_C (by linarith only [hM])
      (by nlinarith only [hCfin1, hM]) hK0 hcS hnu halpha1) hL
  -- (P2') and the `m₃`-headroom at this `(ν, P, L)`.
  obtain ⟨H, D, m2, PsiS, KPsiS, pPsiS, hH1, hD0, hPsiSMono, hPsiSge1, hKPsiS1, hpPsiS,
    hgrowth, hexists, hm2, hHeq, hD1, hKeq, hpeq⟩ :=
    homogBelow_P2prime_verified d hd nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 L hL1 (1 / 2)
      (by norm_num) (by norm_num)
  obtain ⟨m3, hF1, hF2, hF3, hF4, hm3ge, hheadroom, hL2m3⟩ :=
    hHead Cfin hC1h_C M alpha cStar nu K hM halpha0 halpha1 hcS hcS2 hnu hnu1 hK0
      P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 L hL
  -- The conclusion of [AK, Theorem 6.1] at this `(ν, P, L)`.
  have hStep := homogBelow_akhcApplication d C61 hC61 alpha61 ha61 ha61' hAKHCraw nu hnu hnu1 P
    hPrefix hJ2 hJ3 hJ4 L hL1 H D m2 PsiS KPsiS pPsiS hH1 hD0 hPsiSMono hPsiSge1 hKPsiS1 hpPsiS
    hgrowth hexists Cmix hCmix1 (M * max 1 (3 / c)) alpha c hc m3 hF1 hF2 hF3 hF4 hm3ge
    (hMixraw nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4)
  -- The smallness `ω_h² ≤ (8 Υ₁)⁻¹` for every `h > m₃`.
  have hm3K : (L : ℝ) - (m3 : ℝ) ≤
      c * max 1 (3 / c) * M * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) := by
    have e : c * max 1 (3 / c) * M * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) =
        c * (M * max 1 (3 / c)) * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) := by ring
    rw [e]; linarith only [hm3ge]
  have hSmall := fun (h : ℕ) (hh : m3 + 1 ≤ h) =>
    hSm Cfin hC1s_C M alpha cStar nu K hM halpha0 halpha1 hcS hcS2 hnu hnu1 hK0
      P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 L hL m3 h hL2m3 hh hm3K
  -- The monotonicity data for the startup-scale expression.
  have hUps12 : (1 : ℝ) ≤
      C61 * (Homogenization.IndependentSums.gammaGrowthConst ((1 : ℝ) / 3)) ^
          (6 * ((d : ℝ) + 1) ^ 2) +
        C61 * Real.exp (C61 * ((4 * Cmix + 2) * Real.log (2 * nu⁻¹) +
          2 * (1 + Real.log (8 * homogBelow_Cellip d hd * nu⁻¹ ^ 2 + 2)))) := by
    have hgc1' : (1 : ℝ) ≤ Homogenization.IndependentSums.gammaGrowthConst ((1 : ℝ) / 3) := by
      simpa only [one_div] using hgc1
    have hp : (1 : ℝ) ≤ (Homogenization.IndependentSums.gammaGrowthConst ((1 : ℝ) / 3)) ^
        (6 * ((d : ℝ) + 1) ^ 2) := Real.one_le_rpow hgc1' (by positivity)
    have he : 0 ≤ C61 * Real.exp (C61 * ((4 * Cmix + 2) * Real.log (2 * nu⁻¹) +
          2 * (1 + Real.log (8 * homogBelow_Cellip d hd * nu⁻¹ ^ 2 + 2)))) := by positivity
    nlinarith only [hp, hC61, he]
  have hT1 : (1 : ℝ) ≤
      (2 * SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst d +
          4 * (SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst d) ^ 2) *
        nu⁻¹ ^ 2 * (L : ℝ) := by
    have hCd := SuperdiffusionCLT.Section2.Annealed.one_le_cutoffEnvelopeConst d
    have hnuinv : (1 : ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).mpr hnu1
    have hnu2 : (1 : ℝ) ≤ nu⁻¹ ^ 2 := one_le_pow₀ hnuinv
    have hc6 : (1 : ℝ) ≤ 2 * SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst d +
        4 * (SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst d) ^ 2 := by
      nlinarith only [hCd]
    have hLR : (1 : ℝ) ≤ (L : ℝ) := by linarith only [hL3R]
    have h1 := one_le_mul_of_one_le_of_one_le hc6 hnu2
    exact one_le_mul_of_one_le_of_one_le h1 hLR
  have hBigOf := fun (m0 x : ℕ) (hM0 : _) =>
    homogBelow_bigLog_le_m0 d hd nu hnu hnu1 P hPrefix hJ2 hJ3 hJ4 L hL1 H D m2 PsiS KPsiS pPsiS
      hH1 hD0 hPsiSMono hPsiSge1 hKPsiS1 hpPsiS hgrowth hexists hD1 hKeq hpeq hHeq C61 hC61
      Cmix hCmix1 m0 x hM0
  rcases le_total m (L ^ 2) with hmL | hmL
  · -- The branch `m ≤ L²`: `m₀ = ⌈C_b log² L⌉₊`.
    have hScale' : (L : ℝ) - M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ 3 ≤ (m : ℝ) := by
      have h3 : Real.log (L : ℝ) ^ (3 : ℝ) = Real.log (L : ℝ) ^ (3 : ℕ) := by
        rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [← h3]; exact hScale
    have hhead' : 2 * (M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ 3) ≤ (L : ℝ) - (m3 : ℝ) := by
      have h3 : Real.log (L : ℝ) ^ (3 : ℝ) = Real.log (L : ℝ) ^ (3 : ℕ) := by
        rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [← h3]; linarith only [hheadroom]
    have hmain := hMt Cfin hC1t_C M alpha cStar nu K hM halpha0 halpha1 hcS hcS2 hnu hnu1 hK0
      L m m3 hL hScale' hhead'
    have hM0 := hM0B Cb hCB_Cb M hM alpha halpha0 halpha1 cStar hcS hcS2 nu hnu hnu1 K hK0
      L hLCb m hmL
    have hE := hE6 Cb hCE6_Cb L (by exact_mod_cast (show (3 : ℝ) ≤ (L : ℝ) from hL3R))
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show 1 ≤ m by omega)
    have hLm : (m : ℝ) ≤ (L : ℝ) ^ 2 := by exact_mod_cast hmL
    exact homogBelow_thetaLm_of_m0 hnu L hPrefix hJ2 hJ3 hJ4 hCmix1 _ _ C61 _ hU m2 m3 hStep
      hm2 hL2m3 hF2 hm3ge hSmall m _ hmain
      (fun x hx => hBigOf _ x (le_trans (homogBelow_bigLog_monotone_in_m hC61 hCmix1 hUps12 hT1
        hx) hM0))
      (le_trans hE (homogBelow_rpow_neg_le_eighth hL3R (by norm_num)))
      (le_trans hE (homogBelow_rpow_sq_le (by positivity) (by linarith only [hm1]) hLm))
      Cfin
      (fun mt' he => homogBelow_natSub_le_max he
        (by have h5 := homogBelow_five_m0_le (by linarith only [hCb1]) hL3R hC5_C
            push_cast
            exact h5))
      hCA_C hCB2_C
  · -- The branch `L² ≤ m`: `m₀ = ⌈C_b log² m⌉₊`.
    have hLM' := hLM Cfin hC1B_C M alpha cStar nu K hM halpha0 halpha1 hcS hcS2 hnu hnu1 hK0
      L m hL hmL
    have hm3L : m3 ≤ L := by
      have hlog0 : 0 ≤ Real.log (L : ℝ) := Real.log_nonneg (by linarith only [hL3R])
      have hnn : 0 ≤ 2 * M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) := by
        have h1 : 0 ≤ (L : ℝ) ^ alpha := Real.rpow_nonneg (Nat.cast_nonneg L) _
        have h2 : 0 ≤ Real.log (L : ℝ) ^ (3 : ℝ) := Real.rpow_nonneg hlog0 _
        have h3 : 0 ≤ 2 * M := by linarith only [hM]
        positivity
      exact_mod_cast (show (m3 : ℝ) ≤ (L : ℝ) by linarith only [hheadroom, hnn])
    have hM0 := hM0C Cb hCC_Cb M hM alpha halpha0 halpha1 cStar hcS hcS2 nu hnu hnu1 K hK0
      L hLCb m hmL
    have hm3' : 3 ≤ m := by
      have hL3n : 3 ≤ L := by exact_mod_cast hL3R
      nlinarith only [hL3n, hmL]
    have hE := hE3 Cb hCE3_Cb m hm3'
    have hm3R : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm3'
    exact homogBelow_thetaLm_of_m0 hnu L hPrefix hJ2 hJ3 hJ4 hCmix1 _ _ C61 _ hU m2 m3 hStep
      hm2 hL2m3 hF2 hm3ge hSmall m _ (by omega)
      (fun x hx => hBigOf _ x (le_trans (homogBelow_bigLog_monotone_in_m hC61 hCmix1 hUps12 hT1
        hx) hM0))
      (le_trans hE (homogBelow_rpow_neg_le_eighth hm3R (by norm_num))) hE
      Cfin
      (fun mt' he => by
        have hLmt : L ≤ mt' := by omega
        rw [Nat.sub_eq_zero_of_le hLmt, Nat.cast_zero]
        exact le_max_left _ _)
      hCA_C hCB2_C

/-- Satisfiability of the scale hypotheses of `homogBelow_thetaLm`'s conclusion at `α = 0`,
`M = 1`, `K = 0`, `c⋆ = 2`, `ν = 1`: for every `C`, some `L` clears `L₀(C, C M, …)` and
`m = L` meets `L - M L^α log³ L ≤ m`. -/
example (C : ℝ) : ∃ L m : ℕ,
    SuperdiffusionCLT.Frozen.Section4.lNaught C (C * 1) 0 2 1 0 ≤ (L : ℝ) ∧
      (L : ℝ) - 1 * (L : ℝ) ^ (0 : ℝ) * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (m : ℝ) := by
  obtain ⟨L, hL⟩ := exists_nat_ge
    (max 1 (SuperdiffusionCLT.Frozen.Section4.lNaught C (C * 1) 0 2 1 0))
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := le_trans (le_max_left _ _) hL
  have hlog : 0 ≤ Real.log (L : ℝ) ^ (3 : ℝ) := Real.rpow_nonneg (Real.log_nonneg hL1) _
  refine ⟨L, L, le_trans (le_max_right _ _) hL, ?_⟩
  rw [Real.rpow_zero]
  linarith only [hlog]

end SuperdiffusionCLT.Section4.HomogBelow
