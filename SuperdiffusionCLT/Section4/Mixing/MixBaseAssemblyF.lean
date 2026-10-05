/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.Mixing.MixBaseAssemblyE
public import Mathlib.Data.Int.Star

/-!
# The `L < n` clause of the small-gap statement

For `L < n` the amplitudes `C (L - n)_+^{1/2} σ⁻¹` and `C (L - n)_+ σ⁻²` vanish, so
`X1 = X2 = 0` and the whole summand is bounded by the large-gap estimate above scale `L`
(`mixGapAbove_main_uniform`), whose gap hypothesis `(6100 / (d log 3)) log(ν⁻¹n) ≤ m - n` follows
from the standing hypothesis `n ≤ m - ⌈C log(ν⁻¹n)⌉` once `C ≥ 6100 / (d log 3)`.
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

/-- **The `L < n` clause, directly from the large-gap estimate above scale `L`.** -/
theorem mixWlogB_above (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ Ca : ℝ, 1 ≤ Ca ∧ ∀ C : ℝ, Ca ≤ C →
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : ProbabilityMeasure (ShellSeq d)),
          ShellLawPrefix d P → ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P →
          ShellLawJ4 d P →
            ∀ m n L : ℕ, 1 ≤ L → L < n →
              (n : ℤ) ≤ (m : ℤ) - ⌈C * Real.log (nu⁻¹ * (n : ℝ))⌉ →
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
                                  q)) := by
  obtain ⟨Cabove, hCabove_nn, hCabove⟩ := mixGapAbove_main_uniform (d := d) hd
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) hd
  have hlog3pos : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hdlog3pos : (0 : ℝ) < (d : ℝ) * Real.log 3 := mul_pos hd0 hlog3pos
  refine ⟨max (max 1 Cabove) (6100 / ((d : ℝ) * Real.log 3)),
    le_trans (le_max_left _ _) (le_max_left _ _), ?_⟩
  intro C hC nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 m n L hL1 hLn hgapNn
  have hCabove_le : Cabove ≤ C :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hC
  have hC1 : (1 : ℝ) ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hC
  have hthresh_le : 6100 / ((d : ℝ) * Real.log 3) ≤ C := le_trans (le_max_right _ _) hC
  have hn1 : 1 ≤ n := by omega
  have hlognn : (0 : ℝ) ≤ Real.log (nu⁻¹ * (n : ℝ)) := by
    have hnuinv1 : (1 : ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
    have hncast : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    refine Real.log_nonneg ?_
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ nu⁻¹ * (n : ℝ) := mul_le_mul hnuinv1 hncast (by norm_num) (by linarith only [hnuinv1])
  have hceil_nn : (0 : ℤ) ≤ ⌈C * Real.log (nu⁻¹ * (n : ℝ))⌉ :=
    Int.ceil_nonneg (mul_nonneg (by linarith only [hC1]) hlognn)
  have hmn : n ≤ m := by omega
  have hm1 : 1 ≤ m := by omega
  have hceil_le : (C * Real.log (nu⁻¹ * (n : ℝ)) : ℝ) ≤ (⌈C * Real.log (nu⁻¹ * (n : ℝ))⌉ : ℝ) :=
    Int.le_ceil _
  have hZ : (⌈C * Real.log (nu⁻¹ * (n : ℝ))⌉ : ℤ) ≤ (m : ℤ) - (n : ℤ) := by
    linarith only [hgapNn]
  have hcast : ((⌈C * Real.log (nu⁻¹ * (n : ℝ))⌉ : ℤ) : ℝ) ≤ (((m : ℤ) - (n : ℤ) : ℤ) : ℝ) := by
    exact_mod_cast hZ
  have hmnZ : (((m : ℤ) - (n : ℤ) : ℤ) : ℝ) = (m : ℝ) - (n : ℝ) := by
    push_cast
    ring
  have hClog_le : C * Real.log (nu⁻¹ * (n : ℝ)) ≤ (m : ℝ) - (n : ℝ) := by
    rw [← hmnZ]
    linarith only [hceil_le, hcast]
  have hgapN : (6100 / ((d : ℝ) * Real.log 3)) * Real.log (nu⁻¹ * (n : ℝ)) ≤
      (m : ℝ) - (n : ℝ) := by
    have := mul_le_mul_of_nonneg_right hthresh_le hlognn
    linarith only [this, hClog_le]
  obtain ⟨X4, hX4M, hX4O, hX4bd⟩ :=
    hCabove hnu hnu1 hL1 hm1 hLn hgapN hPrefix hJ1V2 hJ2 hJ3 hJ4
  have hmp : (0 : ℝ) ≤ (m : ℝ) ^ (-(3000 : ℝ)) := by positivity
  have hX3O : IsBigO P.toMeasure (gammaSigma ((1 : ℝ) / 3)) X4 (C * (m : ℝ) ^ (-(3000 : ℝ))) :=
    (SuperdiffusionCLT.Section4.HomogBelow.homogBelow_isBigO_of_gammaSigma_le
      (sigma1 := 1) (sigma2 := (1 : ℝ) / 3) (by norm_num) hX4O).mono_scale
      (mul_le_mul_of_nonneg_right (le_trans hCabove_le le_rfl) hmp)
  have hLnzero : ((L - n : ℕ) : ℝ) = 0 := by
    have hz : L - n = 0 := Nat.sub_eq_zero_of_le hLn.le
    exact_mod_cast hz
  have hamp1zero : C * ((L - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
      (sigmaBarStarScalar nu L P (cubeSet (originCube d (n : ℤ)))) ^ (-(1 : ℝ)) = 0 := by
    rw [hLnzero, Real.zero_rpow (by norm_num)]
    ring
  have hamp2zero : C * ((L - n : ℕ) : ℝ) *
      (sigmaBarStarScalar nu L P (cubeSet (originCube d (n : ℤ)))) ^ (-(2 : ℝ)) = 0 := by
    rw [hLnzero]
    ring
  refine ⟨fun _ => 0, fun _ => 0, X4, measurable_const, ?_, measurable_const, ?_, hX4M, hX3O, ?_⟩
  · rw [hamp1zero]
    exact mixBaseA_isBigO_zero 2 le_rfl
  · rw [hamp2zero]
    exact mixBaseA_isBigO_zero 1 le_rfl
  · intro omega p q
    have h := hX4bd omega p q
    simpa using h

end

end SuperdiffusionCLT.Section4.Mixing
