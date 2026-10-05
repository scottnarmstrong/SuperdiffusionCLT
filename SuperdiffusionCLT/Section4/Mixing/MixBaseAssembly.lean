/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.Mixing.MixMainB
public import SuperdiffusionCLT.Section4.Mixing.MixWlogWrapperB
public import SuperdiffusionCLT.Section4.Mixing.MixBaseAssemblyF

/-!
# `mixing_below_cutoff` with no remaining hypothesis

* `mixBase_hBase`: the bounded-gap base case (`hBase` of `mixWlog_smallGapFromBaseB`, for
  `n ≤ L`) at the margin constant `K₀ = 1100`. For `L - n ≤ 6500 log(ν⁻¹L)` it is
  `mixBaseE_near` (large-gap estimate, `F1 = F2 = 0`); otherwise it is `mixBaseD_far`
  (`ell = n + ⌈5010 log(ν⁻¹L)⌉`, gauge pieces, localization piece).
* `mixMain_main_closed`: the statement of
  `SuperdiffusionCLT.Frozen.Section4.mixing_below_cutoff`, copied verbatim from
  `Frozen/Section4`, as `mixMain_mainB ∘ mixWlog_smallGapFromBaseB ∘ mixBase_hBase`. It carries no
  hypothesis beyond `d ≥ 2`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

open Homogenization
open Homogenization.IndependentSums
open MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff (ShellSeq)
open SuperdiffusionCLT.Frozen.Section2 (coefficientCutoff)

noncomputable section

/-- **The bounded-gap base case**, at `K₀ = 1100`. -/
theorem mixBase_hBase (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
      ∃ K0 C0base : ℝ, 1 ≤ K0 ∧ 1 ≤ C0base ∧
        ∀ C : ℝ, C0base ≤ C →
          ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
            ∀ (P : ProbabilityMeasure (ShellSeq d)),
              ShellLawPrefix d P → ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P →
              ShellLawJ4 d P →
                ∀ n L : ℕ, 1 ≤ L → 1 ≤ n → n ≤ L →
                  (L : ℝ) - (n : ℝ) ≤
                    C⁻¹ * (sigmaBarStarScalar nu L P (cubeSet (originCube d (n : ℤ)))) ^ (2 : ℝ) →
                  ∀ mb : ℕ, n ≤ mb →
                    (10 * K0 * Real.log (nu⁻¹ * (L : ℝ)) ≤ ((mb - n : ℕ) : ℝ)) →
                    (((mb - n : ℕ) : ℝ) ≤ 20 * K0 * (1 + Real.log (nu⁻¹ * (L : ℝ)))) →
                    ∃ F1 F2 F3 : TriadicCube d → ShellSeq d → BlockVec d → BlockVec d → ℝ,
                      (∀ R omega p q, F1 R omega p q + F2 R omega p q + F3 R omega p q =
                        blockVecDot p (blockMatVecMul (ofFullBlockMat
                          (toFullBlockMat (coarseBlockMatrix (cubeSet R)
                                (coefficientCutoff nu omega L).toCoeffField) -
                            toFullBlockMat
                              (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))))) q)) ∧
                      (∀ (zreal : Vec d) (w : Fin d → ℤ) (Q : TriadicCube d) (omega : ShellSeq d)
                          (p q : BlockVec d),
                          cubeSet (translateCube w Q) = translateSet zreal (cubeSet Q) →
                            F1 (translateCube w Q) omega p q =
                              F1 Q (ShellField.translateSequence zreal omega) p q) ∧
                      (∀ (zreal : Vec d) (w : Fin d → ℤ) (Q : TriadicCube d) (omega : ShellSeq d)
                          (p q : BlockVec d),
                          cubeSet (translateCube w Q) = translateSet zreal (cubeSet Q) →
                            F2 (translateCube w Q) omega p q =
                              F2 Q (ShellField.translateSequence zreal omega) p q) ∧
                      (∀ (zreal : Vec d) (w : Fin d → ℤ) (Q : TriadicCube d) (omega : ShellSeq d)
                          (p q : BlockVec d),
                          cubeSet (translateCube w Q) = translateSet zreal (cubeSet Q) →
                            F3 (translateCube w Q) omega p q =
                              F3 Q (ShellField.translateSequence zreal omega) p q) ∧
                      (L ≤ n → ∀ R omega p q, F1 R omega p q = 0) ∧
                      (L ≤ n → ∀ R omega p q, F2 R omega p q = 0) ∧
                      ∃ X1 X2 X3 : ShellSeq d → ℝ,
                        Measurable X1 ∧
                          IsBigO P.toMeasure (gammaSigma 2) X1
                            (C * ((L - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
                              (sigmaBarStarScalar nu L P (cubeSet (originCube d (n : ℤ)))) ^
                                (-(1 : ℝ))) ∧
                        Measurable X2 ∧
                          IsBigO P.toMeasure (gammaSigma 1) X2
                            (C * ((L - n : ℕ) : ℝ) *
                              (sigmaBarStarScalar nu L P (cubeSet (originCube d (n : ℤ)))) ^
                                (-(2 : ℝ))) ∧
                        Measurable X3 ∧
                          IsBigO P.toMeasure (gammaSigma ((1 : ℝ) / 3)) X3
                            (C * (mb : ℝ) ^ (-(3000 : ℝ))) ∧
                          ∀ (omega : ShellSeq d) (p q : BlockVec d),
                            2 * descendantsAverage (originCube d (mb : ℤ)) (mb - n)
                                (fun R' => F1 R' omega p q) ≤
                              X1 omega *
                                (blockVecDot p
                                    (blockMatVecMul
                                      (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ))))
                                      p) +
                                  blockVecDot q
                                    (blockMatVecMul
                                      (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ))))
                                      q)) ∧
                            2 * descendantsAverage (originCube d (mb : ℤ)) (mb - n)
                                (fun R' => F2 R' omega p q) ≤
                              X2 omega *
                                (blockVecDot p
                                    (blockMatVecMul
                                      (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ))))
                                      p) +
                                  blockVecDot q
                                    (blockMatVecMul
                                      (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ))))
                                      q)) ∧
                            2 * descendantsAverage (originCube d (mb : ℤ)) (mb - n)
                                (fun R' => F3 R' omega p q) ≤
                              X3 omega *
                                (blockVecDot p
                                    (blockMatVecMul
                                      (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ))))
                                      p) +
                                  blockVecDot q
                                    (blockMatVecMul
                                      (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ))))
                                      q)) := by
  obtain ⟨Cnear, hCn1, hNear⟩ := mixBaseE_near d hd
  obtain ⟨Cfar, hCf1, hFar⟩ := mixBaseD_far d hd
  refine ⟨1100, max Cnear Cfar, by norm_num, le_trans hCn1 (le_max_left _ _), ?_⟩
  intro C hC nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 n L hL1 hn1 hnL hgap mb hnmb hw1 hw2
  have hLg0 : (0 : ℝ) ≤ Real.log (nu⁻¹ * (L : ℝ)) := by
    have hnuinv1 : (1 : ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
    have hLcast : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
    refine Real.log_nonneg ?_
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ nu⁻¹ * (L : ℝ) := mul_le_mul hnuinv1 hLcast (by norm_num) (by linarith only [hnuinv1])
  by_cases hnear : (L : ℝ) - (n : ℝ) ≤ 6500 * Real.log (nu⁻¹ * (L : ℝ))
  · exact hNear C (le_trans (le_max_left _ _) hC) nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 n L hL1
      hn1 hnL mb hnmb hw1 hnear
  · have hfar := not_le.1 hnear
    have hnL' : n < L := by
      have : (n : ℝ) < (L : ℝ) := by linarith only [hfar, hLg0]
      exact_mod_cast this
    exact hFar C (le_trans (le_max_right _ _) hC) nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 n L hL1
      hn1 hnL' hgap mb hnmb hw1 hw2 hfar

/-- **`mixing_below_cutoff`, with no remaining hypothesis**: the verbatim body of the main
statement, proved from the bounded-gap base case. -/
theorem mixMain_main_closed (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
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
                              q))) :=
  mixMain_mainB d hd (mixWlog_smallGapFromBaseB d hd (mixBase_hBase d hd))

end

end SuperdiffusionCLT.Section4.Mixing
