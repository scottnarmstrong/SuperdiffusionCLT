/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.Mixing.LargeGapAboveMainUniform

/-!
# `mixMain_mainB`: the mixing statement with a `d`-dependent small-gap threshold

A reduction of the statement `mixing_below_cutoff` with a `d`-independent small-gap threshold
(such as `max 1 (2 * (50100 / Real.log 3))`) is not enough, since the small-gap clause's own
construction needs the constant of the statement to dominate several genuinely `d`-dependent
constants (`Fintype.card (BlockCoord d × BlockCoord d) = 4d²`, `mixGaugeFinal_Cbase d`,
the scale-comparison witness `Ct(d)`, `MixMainTerm1Bare`'s own absorbed
constant). So this file states the reduction with a `d`-dependent threshold
`hSmallGapD : ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ C ≥ C₀, [small-gap clause at C]`. The proof
folds `C₀` into the same `max` chain that
already builds the final constant from the large-gap witnesses
`Cfull`, `Cabove` (so `C₀ ≤ C` exactly the way `Cfull ≤ C`, `Cabove ≤ C`
already were) -- this is the "checking both clauses are monotone in `C` for
`C` at least their thresholds" step: `hSmallGapD`'s own `∀ C ≥ C₀` already
supplies monotonicity for the small-gap clause, and the large-gap clause is
weakened up to the common `C` via `IsBigO.mono_scale`. -/

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

/-- **`mixMain_mainB`: the verbatim body of
`SuperdiffusionCLT.Frozen.Section4.mixing_below_cutoff`**, reduced to
ONE remaining hypothesis `hSmallGapD`, the small-gap clause stated with a
`d`-dependent threshold `C₀` instead of a `d`-independent
numeral. -/
theorem mixMain_mainB (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hSmallGapD : ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C →
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : ProbabilityMeasure (ShellSeq d)),
          ShellLawPrefix d P → ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P →
          ShellLawJ4 d P →
            ∀ m n L : ℕ, 1 ≤ L →
              (L : ℝ) - (n : ℝ) ≤
                C⁻¹ * (sigmaBarStarScalar nu L P (cubeSet (originCube d (n : ℤ)))) ^ (2 : ℝ) →
              m < 2 * n →
              (n : ℤ) ≤ (m : ℤ) - ⌈C * Real.log (nu⁻¹ * (L : ℝ))⌉ →
              ⌈C * Real.log (nu⁻¹ * (L : ℝ))⌉ ≤ (n : ℤ) →
              (n : ℤ) ≤ (m : ℤ) - ⌈C * Real.log (nu⁻¹ * (n : ℝ))⌉ →
              ((m : ℝ) ≤ (L : ℝ) + C * Real.log (nu⁻¹ * (L : ℝ)) →
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
                      (C * (m : ℝ) ^ (-(3000 : ℝ))) ∧
                    ∀ (omega : ShellSeq d) (p q : BlockVec d),
                      2 *
                          (((descendantsAtDepth (originCube d (m : ℤ)) (m - n)).card : ℝ)⁻¹ *
                            ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n),
                              blockVecDot p
                                (blockMatVecMul
                                  (ofFullBlockMat
                                    (toFullBlockMat
                                        (coarseBlockMatrix (cubeSet R)
                                          (coefficientCutoff nu omega L).toCoeffField) -
                                      toFullBlockMat
                                        (annealedBlockMatrix nu L P
                                          (cubeSet (originCube d (n : ℤ))))))
                                  q)) ≤
                        (X1 omega + X2 omega + X3 omega) *
                          (blockVecDot p
                              (blockMatVecMul
                                (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ))))
                                p) +
                            blockVecDot q
                              (blockMatVecMul
                                (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ))))
                                q)))) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : ProbabilityMeasure (ShellSeq d)),
          ShellLawPrefix d P → ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P →
          ShellLawJ4 d P →
            ∀ m n L : ℕ, 1 ≤ L →
              (L : ℝ) - (n : ℝ) ≤
                C⁻¹ * (sigmaBarStarScalar nu L P (cubeSet (originCube d (n : ℤ)))) ^ (2 : ℝ) →
              m < 2 * n →
              (n : ℤ) ≤ (m : ℤ) - ⌈C * Real.log (nu⁻¹ * (L : ℝ))⌉ →
              ⌈C * Real.log (nu⁻¹ * (L : ℝ))⌉ ≤ (n : ℤ) →
              (n : ℤ) ≤ (m : ℤ) - ⌈C * Real.log (nu⁻¹ * (n : ℝ))⌉ →
              ((m : ℝ) ≤ (L : ℝ) + C * Real.log (nu⁻¹ * (L : ℝ)) →
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
                      (C * (m : ℝ) ^ (-(3000 : ℝ))) ∧
                    ∀ (omega : ShellSeq d) (p q : BlockVec d),
                      2 *
                          (((descendantsAtDepth (originCube d (m : ℤ)) (m - n)).card : ℝ)⁻¹ *
                            ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n),
                              blockVecDot p
                                (blockMatVecMul
                                  (ofFullBlockMat
                                    (toFullBlockMat
                                        (coarseBlockMatrix (cubeSet R)
                                          (coefficientCutoff nu omega L).toCoeffField) -
                                      toFullBlockMat
                                        (annealedBlockMatrix nu L P
                                          (cubeSet (originCube d (n : ℤ))))))
                                  q)) ≤
                        (X1 omega + X2 omega + X3 omega) *
                          (blockVecDot p
                              (blockMatVecMul
                                (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ))))
                                p) +
                            blockVecDot q
                              (blockMatVecMul
                                (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ))))
                                q))) ∧
              ((L : ℝ) + C * Real.log (nu⁻¹ * (L : ℝ)) < (m : ℝ) →
                ∃ X4 : ShellSeq d → ℝ,
                  Measurable X4 ∧
                  IsBigO P.toMeasure (gammaSigma 1) X4
                      (C * (m : ℝ) ^ (-(3000 : ℝ))) ∧
                    ∀ (omega : ShellSeq d) (p q : BlockVec d),
                      2 *
                          (((descendantsAtDepth (originCube d (m : ℤ)) (m - n)).card : ℝ)⁻¹ *
                            ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n),
                              blockVecDot p
                                (blockMatVecMul
                                  (ofFullBlockMat
                                    (toFullBlockMat
                                        (coarseBlockMatrix (cubeSet R)
                                          (coefficientCutoff nu omega L).toCoeffField) -
                                      toFullBlockMat
                                        (annealedBlockMatrix nu L P
                                          (cubeSet (originCube d (n : ℤ))))))
                                  q)) ≤
                        X4 omega *
                          (blockVecDot p
                              (blockMatVecMul
                                (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ))))
                                p) +
                            blockVecDot q
                              (blockMatVecMul
                                (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ))))
                                q))) := by
  obtain ⟨C0, hC0_1, hSmallGapD⟩ := hSmallGapD
  obtain ⟨Cfull, hCfull_nn, hCfull⟩ := mixGap_main_full_uniform (d := d) hd
  obtain ⟨Cabove, hCabove_nn, hCabove⟩ := mixGapAbove_main_uniform (d := d) hd
  set C : ℝ := max (max 1 (2 * (50100 / Real.log 3))) (max C0 (max Cfull Cabove)) with hCdef
  have hC1 : (1:ℝ) ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
  have hCthresh : max 1 (2 * (50100 / Real.log 3)) ≤ C := le_max_left _ _
  have hC0le : C0 ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCfullle : Cfull ≤ C :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hCabovele : Cabove ≤ C :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  refine ⟨C, hC1, ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 m n L hL1 hLnR hmn2n hgapMn hgapLn hgapNn
  have hmn : n ≤ m := by
    have hceil_nn : (0:ℤ) ≤ ⌈C * Real.log (nu⁻¹ * (L:ℝ))⌉ := by
      have hlognn : (0:ℝ) ≤ Real.log (nu⁻¹ * (L:ℝ)) := by
        have hnuinv1 : (1:ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
        have hLcast : (1:ℝ) ≤ (L:ℝ) := by exact_mod_cast hL1
        refine Real.log_nonneg ?_
        calc (1:ℝ) = 1*1 := by ring
          _ ≤ nu⁻¹ * (L:ℝ) := mul_le_mul hnuinv1 hLcast (by norm_num) (by linarith only [hnuinv1])
      have : (0:ℝ) ≤ C * Real.log (nu⁻¹ * (L:ℝ)) := mul_nonneg (by linarith only [hC1]) hlognn
      exact_mod_cast Int.ceil_nonneg this
    omega
  have hn1 : 1 ≤ n := by omega
  have hm1 : 1 ≤ m := by omega
  have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) hd
  have hdcast : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hlog3pos : (0:ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hthresh_le : (6100 / ((d:ℝ) * Real.log 3)) ≤ C := by
    have hdlog3pos : (0:ℝ) < (d:ℝ) * Real.log 3 := mul_pos hd0 hlog3pos
    rw [div_le_iff₀ hdlog3pos]
    have hCge : (100200:ℝ) / Real.log 3 ≤ C := by
      have h2C : (2:ℝ) * (50100 / Real.log 3) ≤ C :=
        le_trans (le_max_right _ _) hCthresh
      have heq : (2:ℝ) * (50100 / Real.log 3) = 100200 / Real.log 3 := by ring
      linarith only [h2C, heq.le, heq.ge]
    have hClog3 : (100200:ℝ) ≤ C * Real.log 3 := by
      have hmul := mul_le_mul_of_nonneg_right hCge hlog3pos.le
      rwa [div_mul_cancel₀ _ hlog3pos.ne'] at hmul
    have hprod : (100200:ℝ) * 2 ≤ (C * Real.log 3) * (d:ℝ) :=
      mul_le_mul hClog3 hdcast (by norm_num) (by linarith only [hClog3])
    nlinarith only [hprod]
  refine ⟨fun hcase => hSmallGapD C hC0le nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 m n L hL1 hLnR
      hmn2n hgapMn hgapLn hgapNn hcase, fun hcase => ?_⟩
  rcases le_or_gt n L with hnl | hln
  · -- n ≤ L: large-gap via mixGap_main_full_uniform.
    have hgapL : (6100 / ((d:ℝ) * Real.log 3)) * Real.log (nu⁻¹ * (L:ℝ)) ≤ (m:ℝ) - (L:ℝ) := by
      have hlognn : (0:ℝ) ≤ Real.log (nu⁻¹ * (L:ℝ)) := by
        have hnuinv1 : (1:ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
        have hLcast : (1:ℝ) ≤ (L:ℝ) := by exact_mod_cast hL1
        refine Real.log_nonneg ?_
        calc (1:ℝ) = 1*1 := by ring
          _ ≤ nu⁻¹ * (L:ℝ) := mul_le_mul hnuinv1 hLcast (by norm_num) (by linarith only [hnuinv1])
      have := mul_le_mul_of_nonneg_right hthresh_le hlognn
      linarith only [this, hcase]
    obtain ⟨X4, hX4M, hX4O, hX4bd⟩ :=
      hCfull hnu hnu1 hL1 hm1 hnl hgapL hPrefix hJ1 hJ2 hJ3 hJ4
    refine ⟨X4, hX4M, ?_, hX4bd⟩
    have hmp : (0:ℝ) ≤ (m:ℝ) ^ (-(3000:ℝ)) := by positivity
    exact hX4O.mono_scale (mul_le_mul_of_nonneg_right hCfullle hmp)
  · -- L < n: large-gap via mixGapAbove_main_uniform, from the standing hyp alone.
    have hgapN : (6100 / ((d:ℝ) * Real.log 3)) * Real.log (nu⁻¹ * (n:ℝ)) ≤ (m:ℝ) - (n:ℝ) := by
      have hceil_le : (C * Real.log (nu⁻¹ * (n:ℝ)) : ℝ) ≤ (⌈C * Real.log (nu⁻¹ * (n:ℝ))⌉ : ℝ) :=
        Int.le_ceil _
      have hZ : (⌈C * Real.log (nu⁻¹ * (n:ℝ))⌉ : ℤ) ≤ (m:ℤ) - (n:ℤ) := by linarith only [hgapNn]
      have hcast : ((⌈C * Real.log (nu⁻¹ * (n:ℝ))⌉ : ℤ) : ℝ) ≤ (((m:ℤ) - (n:ℤ) : ℤ) : ℝ) := by
        exact_mod_cast hZ
      have hmnZ : (((m:ℤ) - (n:ℤ) : ℤ) : ℝ) = (m:ℝ) - (n:ℝ) := by
        have hmnI : (n:ℤ) ≤ (m:ℤ) := by exact_mod_cast hmn
        push_cast
        ring
      have hClog_le : C * Real.log (nu⁻¹ * (n:ℝ)) ≤ (m:ℝ) - (n:ℝ) := by
        rw [← hmnZ]; linarith only [hceil_le, hcast]
      have hlognn : (0:ℝ) ≤ Real.log (nu⁻¹ * (n:ℝ)) := by
        have hnuinv1 : (1:ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
        have hncast : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
        refine Real.log_nonneg ?_
        calc (1:ℝ) = 1*1 := by ring
          _ ≤ nu⁻¹ * (n:ℝ) := mul_le_mul hnuinv1 hncast (by norm_num) (by linarith only [hnuinv1])
      have := mul_le_mul_of_nonneg_right hthresh_le hlognn
      linarith only [this, hClog_le]
    obtain ⟨X4, hX4M, hX4O, hX4bd⟩ :=
      hCabove hnu hnu1 hL1 hm1 hln hgapN hPrefix hJ1 hJ2 hJ3 hJ4
    refine ⟨X4, hX4M, ?_, hX4bd⟩
    have hmp : (0:ℝ) ≤ (m:ℝ) ^ (-(3000:ℝ)) := by positivity
    exact hX4O.mono_scale (mul_le_mul_of_nonneg_right hCabovele hmp)

end

end SuperdiffusionCLT.Section4.Mixing
