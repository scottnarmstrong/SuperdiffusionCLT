/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.Section2.Annealed.Symmetry
public import SuperdiffusionCLT.Section2.BfAmEllipticityRegimeSplit
public import SuperdiffusionCLT.Frozen.Section2.CoefficientCutoff
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5
public import SuperdiffusionCLT.Frozen.Section4.LNaught
public import SuperdiffusionCLT.Frozen.Section4.ThetaCutoff
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp

@[expose] public section

/-- Converts the intermediate-scale ratio bound into the scalar estimate of the
main statement. The sole remaining input is the display `e.Theta.Lm.final.bound` of the paper,
after the three Section 4 inputs. -/
theorem SuperdiffusionCLT.Section4.HomogBelow.homogBelow_from_thetaLm
    (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hAKHC : ∃ C : ℝ, 1 ≤ C ∧ ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∃ alpha : ℝ, 0 < alpha ∧ alpha < 1 ∧
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
                    (-(min alpha ((1 - gamma) / 2) * ((n : ℝ) - (m : ℝ) - 4 * (m0 : ℝ)))))
    (hMix : ∃ C : ℝ, 1 ≤ C ∧
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
                              q))))
    (hThetaLm :
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
              C * (m : ℝ) ^ (-(3000 : ℝ)))
    : ∃ C : ℝ, 1 ≤ C ∧
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
              |(SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu L P)⁻¹ *
                    SuperdiffusionCLT.Section2.Annealed.sigmaBarSeq nu L P m -
                  1| +
                |SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu L P *
                      SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu L P m -
                    1| ≤
                  C * (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu L P) ^
                      (-(2 : ℝ)) *
                    max 0 ((L : ℝ) - (m : ℝ) + C * Real.log (L : ℝ) ^ (2 : ℝ)) +
                  C * (m : ℝ) ^ (-(3000 : ℝ)) := by
  obtain ⟨C, hC, hTheta⟩ := hThetaLm hd hAKHC hMix
  refine ⟨C, hC, ?_⟩
  intro nu cStar K hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 alpha M hAlpha hAlpha1 hM
    L m hL hScale
  have hThetaBound := hTheta nu cStar K hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
    alpha M hAlpha hAlpha1 hM L m hL hScale
  let s := SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu L P
  let u := SuperdiffusionCLT.Section2.Annealed.sigmaBarSeq nu L P m
  let v := SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu L P m
  have hs : 0 < s := by
    dsimp [s]
    exact SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite_pos
      hnu L hPrefix hJ2 hJ3 hJ4
  have hUpper : s ≤ u := by
    calc
      s ≤ SuperdiffusionCLT.Section2.Annealed.sigmaBarUpperLimit nu L P := by
        dsimp [s]
        exact SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite_le_sigmaBarUpperLimit
          hnu L hPrefix hJ2 hJ3 hJ4
      _ ≤ u := by
        dsimp [u]
        exact SuperdiffusionCLT.Section2.Annealed.sigmaBarUpperLimit_le
          hnu L hPrefix hJ2 hJ3 hJ4 m
  have hA : 1 ≤ s⁻¹ * u := by
    have hmul := mul_le_mul_of_nonneg_left hUpper (inv_nonneg.mpr hs.le)
    simpa only [inv_mul_cancel₀ hs.ne'] using hmul
  have hLimitPos : 0 < SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvLimit nu L P := by
    exact SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvLimit_pos
      hnu L hPrefix hJ2 hJ3 hJ4
  have hLimitLe :
      SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvLimit nu L P ≤ v := by
    dsimp [v]
    exact SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvLimit_le
      hnu L hPrefix hJ2 hJ3 hJ4 m
  have hB : 1 ≤ s * v := by
    calc
      1 = SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvLimit nu L P * s := by
        dsimp [s, SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite]
        exact (mul_inv_cancel₀ hLimitPos.ne').symm
      _ ≤ v * s := mul_le_mul_of_nonneg_right hLimitLe hs.le
      _ = s * v := mul_comm _ _
  let a := s⁻¹ * u
  let b := s * v
  have hab : a * b = SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m := by
    change (s⁻¹ * u) * (s * v) =
      SuperdiffusionCLT.Section2.Annealed.sigmaBarSeq nu L P m *
        SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu L P m
    calc
      (s⁻¹ * u) * (s * v) = (s⁻¹ * s) * (u * v) := by ring
      _ = u * v := by rw [inv_mul_cancel₀ hs.ne', one_mul]
      _ = SuperdiffusionCLT.Section2.Annealed.sigmaBarSeq nu L P m *
          SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu L P m := rfl
  have hA' : 1 ≤ a := hA
  have hB' : 1 ≤ b := hB
  have hprod : 0 ≤ (a - 1) * (b - 1) :=
    mul_nonneg (sub_nonneg.mpr hA') (sub_nonneg.mpr hB')
  have hThetaNoIndicator :
      SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1 ≤
        C * s ^ (-(2 : ℝ)) *
            max 0 ((L : ℝ) - (m : ℝ) + C * Real.log (L : ℝ) ^ (2 : ℝ)) +
          C * (m : ℝ) ^ (-(3000 : ℝ)) := by
    let head := C * s ^ (-(2 : ℝ)) *
      max 0 ((L : ℝ) - (m : ℝ) + C * Real.log (L : ℝ) ^ (2 : ℝ))
    have hhead : 0 ≤ head := by
      dsimp [head]
      positivity
    have hIndicator :
        (if (m : ℝ) ≤ (L : ℝ) + C * Real.log (L : ℝ) ^ (2 : ℝ)
         then (1 : ℝ) else 0) ≤ 1 := by
      split_ifs
      · exact le_rfl
      · exact zero_le_one
    have hScaled := mul_le_mul_of_nonneg_left hIndicator hhead
    calc
      SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1 ≤
          head * (if (m : ℝ) ≤ (L : ℝ) + C * Real.log (L : ℝ) ^ (2 : ℝ)
                 then (1 : ℝ) else 0) + C * (m : ℝ) ^ (-(3000 : ℝ)) := by
        simpa only [head, s] using hThetaBound
      _ ≤ head + C * (m : ℝ) ^ (-(3000 : ℝ)) := by
        simpa only [mul_one] using
          add_le_add hScaled (le_rfl : C * (m : ℝ) ^ (-(3000 : ℝ)) ≤
            C * (m : ℝ) ^ (-(3000 : ℝ)))
      _ = C * s ^ (-(2 : ℝ)) *
            max 0 ((L : ℝ) - (m : ℝ) + C * Real.log (L : ℝ) ^ (2 : ℝ)) +
          C * (m : ℝ) ^ (-(3000 : ℝ)) := by rfl
  have hsum : |a - 1| + |b - 1| ≤
      C * s ^ (-(2 : ℝ)) *
          max 0 ((L : ℝ) - (m : ℝ) + C * Real.log (L : ℝ) ^ (2 : ℝ)) +
        C * (m : ℝ) ^ (-(3000 : ℝ)) := by
    calc
      |a - 1| + |b - 1| = (a - 1) + (b - 1) := by
        rw [abs_of_nonneg (sub_nonneg.mpr hA'), abs_of_nonneg (sub_nonneg.mpr hB')]
      _ ≤ a * b - 1 := by
        calc
          (a - 1) + (b - 1) ≤ (a - 1) + (b - 1) + (a - 1) * (b - 1) :=
            le_add_of_nonneg_right hprod
          _ = a * b - 1 := by ring
      _ = SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1 := by rw [hab]
      _ ≤ C * s ^ (-(2 : ℝ)) *
            max 0 ((L : ℝ) - (m : ℝ) + C * Real.log (L : ℝ) ^ (2 : ℝ)) +
          C * (m : ℝ) ^ (-(3000 : ℝ)) := hThetaNoIndicator
  simpa only [a, b, s, u, v] using hsum
