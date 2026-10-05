/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.Mixing.MixBaseAssemblyD
public import SuperdiffusionCLT.Section4.HomogBelow.ThetaLmGammaSigmaWeaken
public import SuperdiffusionCLT.Section4.Mixing.LargeGapAboveMainUniform
public import SuperdiffusionCLT.Section4.Mixing.WlogTranslate

/-!
# `hBase` in the near regime `L - n ≤ 6500 log(ν⁻¹L)`

For `n ≤ L` with `L - n ≤ 6500 log(ν⁻¹L)` and the margin `m - n ≥ 11000 log(ν⁻¹L)`, the gap
`m - L` is at least `4500 log(ν⁻¹L)`, which exceeds the canonical threshold
`6100 / (d log 3) ≤ 3050`. The large-gap estimate `mixGap_main_full_uniform` therefore gives the
whole summand a `Γ₁` bound at amplitude `C m^{-3000}`; it is weakened to `Γ_{1/3}` and used as
the `F3` piece, with `F1 = F2 = 0`.
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

variable {d : ℕ}

theorem mixBaseE_near (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ Cnear : ℝ, 1 ≤ Cnear ∧ ∀ C : ℝ, Cnear ≤ C →
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : ProbabilityMeasure (ShellSeq d)),
          ShellLawPrefix d P → ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P →
            ShellLawJ4 d P →
              ∀ n L : ℕ, 1 ≤ L → 1 ≤ n → n ≤ L →
                ∀ mb : ℕ, n ≤ mb →
                  (10 * 1100 * Real.log (nu⁻¹ * (L : ℝ)) ≤ ((mb - n : ℕ) : ℝ)) →
                  (L : ℝ) - (n : ℝ) ≤ 6500 * Real.log (nu⁻¹ * (L : ℝ)) →
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
  obtain ⟨C4, hC4, hFull⟩ := mixGap_main_full_uniform (d := d) hd
  refine ⟨max 1 C4, le_max_left _ _, ?_⟩
  intro C hC nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 n L hL1 hn1 hnL mb hnmb hw1 hnear
  have hC4le : C4 ≤ C := le_trans (le_max_right _ _) hC
  have hC1 : 1 ≤ C := le_trans (le_max_left _ _) hC
  have hm1 : 1 ≤ mb := le_trans hn1 hnmb
  have hLg0 : (0 : ℝ) ≤ Real.log (nu⁻¹ * (L : ℝ)) := by
    have hnuinv1 : (1 : ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
    have hLcast : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
    refine Real.log_nonneg ?_
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ nu⁻¹ * (L : ℝ) := mul_le_mul hnuinv1 hLcast (by norm_num) (by linarith only [hnuinv1])
  have hK : 6100 / ((d : ℝ) * Real.log 3) ≤ 3050 := by
    have hdc : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hl := mixBaseB_one_lt_log_three
    have hdl : (2 : ℝ) ≤ (d : ℝ) * Real.log 3 := by nlinarith only [hdc, hl]
    rw [div_le_iff₀ (by linarith only [hdl])]
    linarith only [hdl]
  have hmbn : ((mb - n : ℕ) : ℝ) = (mb : ℝ) - (n : ℝ) := Nat.cast_sub hnmb
  have hgapL : (6100 / ((d : ℝ) * Real.log 3)) * Real.log (nu⁻¹ * (L : ℝ)) ≤
      (mb : ℝ) - (L : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_right hK hLg0
    linarith only [h1, hw1, hnear, hmbn, hLg0]
  obtain ⟨X4, hX4M, hX4O, hX4b⟩ := hFull hnu hnu1 hL1 hm1 hnL hgapL hPrefix hJ1V2 hJ2 hJ3 hJ4
  have hσpos := SuperdiffusionCLT.Section3.HighContrast.sigmaBarStarScalar_pos hnu L hPrefix
    hJ2 hJ3 hJ4 (n : ℤ)
  have hamp1 : 0 ≤ C * ((L - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
      (sigmaBarStarScalar nu L P (cubeSet (originCube d (n : ℤ)))) ^ (-(1 : ℝ)) :=
    mul_nonneg (mul_nonneg (by linarith only [hC1]) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (Real.rpow_nonneg hσpos.le _)
  have hamp2 : 0 ≤ C * ((L - n : ℕ) : ℝ) *
      (sigmaBarStarScalar nu L P (cubeSet (originCube d (n : ℤ)))) ^ (-(2 : ℝ)) :=
    mul_nonneg (mul_nonneg (by linarith only [hC1]) (Nat.cast_nonneg _))
      (Real.rpow_nonneg hσpos.le _)
  have hmp : (0 : ℝ) ≤ (mb : ℝ) ^ (-(3000 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hX3O : IsBigO P.toMeasure (gammaSigma ((1 : ℝ) / 3)) X4 (C * (mb : ℝ) ^ (-(3000 : ℝ))) :=
    (SuperdiffusionCLT.Section4.HomogBelow.homogBelow_isBigO_of_gammaSigma_le
      (sigma1 := 1) (sigma2 := (1 : ℝ) / 3) (by norm_num) hX4O).mono_scale
      (mul_le_mul_of_nonneg_right hC4le hmp)
  refine ⟨fun _ _ _ _ => 0, fun _ _ _ _ => 0,
    fun R omega p q => blockVecDot p (blockMatVecMul (ofFullBlockMat
      (toFullBlockMat (coarseBlockMatrix (cubeSet R) (coefficientCutoff nu omega L).toCoeffField) -
        toFullBlockMat (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))))) q),
    ?_, ?_, ?_, ?_, ?_, ?_, fun _ => 0, fun _ => 0, X4, measurable_const,
    mixBaseA_isBigO_zero 2 hamp1, measurable_const, mixBaseA_isBigO_zero 1 hamp2, hX4M, hX3O, ?_⟩
  · intro R omega p q
    simp
  · intro zreal w Q omega p q hset
    rfl
  · intro zreal w Q omega p q hset
    rfl
  · intro zreal w Q omega p q hset
    beta_reduce
    rw [mixTerms_blockVecDot_ofFullBlockMat_sub_bilinear, mixTerms_blockVecDot_ofFullBlockMat_sub_bilinear,
      mixFin_coarseBlockMatrix_hFcov nu L zreal w Q omega p q hset]
  · intro _ R omega p q
    rfl
  · intro _ R omega p q
    rfl
  · intro omega p q
    refine ⟨?_, ?_, hX4b omega p q⟩
    · have h0 : descendantsAverage (originCube d (mb : ℤ)) (mb - n)
          (fun _ : TriadicCube d => (0 : ℝ)) = 0 := mixBaseA_avg_const _ _ 0
      show 2 * descendantsAverage (originCube d (mb : ℤ)) (mb - n)
          (fun _ : TriadicCube d => (0 : ℝ)) ≤ _
      rw [h0]
      simp
    · have h0 : descendantsAverage (originCube d (mb : ℤ)) (mb - n)
          (fun _ : TriadicCube d => (0 : ℝ)) = 0 := mixBaseA_avg_const _ _ 0
      show 2 * descendantsAverage (originCube d (mb : ℤ)) (mb - n)
          (fun _ : TriadicCube d => (0 : ℝ)) ≤ _
      rw [h0]
      simp

end

end SuperdiffusionCLT.Section4.Mixing
