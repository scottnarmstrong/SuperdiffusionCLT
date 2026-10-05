/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.HomogBelow.FromThetaLm
public import SuperdiffusionCLT.Section4.HomogBelow.ThetaLmMain
public import SuperdiffusionCLT.Frozen.Section4.AKHCWeakerP3

/-!
`p.homog.below`: the statement of
`SuperdiffusionCLT.Frozen.Section4.homogenization_below_cutoff`, copied verbatim, proved
from [AK, Theorem 6.1] (`akhc_weakerP3`) and the bound
`e.Theta.Lm.final.bound` (`homogBelow_thetaLm`). The only hypothesis is `hMix`, the body of the
mixing statement `SuperdiffusionCLT.Frozen.Section4.mixing_below_cutoff`, copied
verbatim. -/

@[expose] public section

/-- **`p.homog.below`**, from the mixing estimate `p.mixing.below` (`hMix`). -/
theorem SuperdiffusionCLT.Section4.HomogBelow.homogBelow_main (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hMix :
    ∃ C : ℝ, 1 ≤ C ∧
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
                              q)))) :
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
              |(SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu L P)⁻¹ *
                    SuperdiffusionCLT.Section2.Annealed.sigmaBarSeq nu L P m -
                  1| +
                |SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu L P *
                      SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu L P m -
                    1| ≤
                  C * (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu L P) ^
                      (-(2 : ℝ)) *
                    max 0 ((L : ℝ) - (m : ℝ) + C * Real.log (L : ℝ) ^ (2 : ℝ)) +
                  C * (m : ℝ) ^ (-(3000 : ℝ))
    :=
  SuperdiffusionCLT.Section4.HomogBelow.homogBelow_from_thetaLm d hd
    (SuperdiffusionCLT.Frozen.Section4.akhc_weakerP3 d hd) hMix
    (SuperdiffusionCLT.Section4.HomogBelow.homogBelow_thetaLm d)
