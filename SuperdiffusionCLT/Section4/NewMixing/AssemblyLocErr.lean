/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.NewMixing.AssemblySplit
public import SuperdiffusionCLT.Section4.NewMixing.LocAvgUniformWitness
public import SuperdiffusionCLT.Section4.NewMixing.Splitting

/-!
# The localization error with the witness constant fixed first

The localization-error estimate of the uniform localization-error file binds its amplitude
constant after the scales. This file restates it with the constant bound first, built from
`newMixAsm_splitting_uniform`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.NewMixing

open Homogenization
open Homogenization.Book.Ch02

noncomputable section

theorem newMixAsm_localizationError_uniform (d : ℕ) [NeZero d] :
    ∃ C : ℝ, ∀
    {nu : ℝ} {P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)}
    (hnu : 0 < nu), nu ≤ 1 →
    SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P →
    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P →
    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P →
    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
    ∀ {L m ell n : ℕ}, n ≤ ell → ell ≤ m → ell ≤ L → 1 ≤ ell → 1 ≤ L → 1 ≤ m - n →
    ∃ X0 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
      Measurable X0 ∧
      Homogenization.IndependentSums.IsBigO P.toMeasure
        (Homogenization.IndependentSums.gammaSigma ((1 : ℝ) / 3)) X0
        (C * nu ^ (-(4 : ℝ)) *
          ((if ell < L then (L : ℝ) ^ 2 * (3 : ℝ) ^ (-((ell - n : ℕ) : ℝ)) else 0) +
            (ell : ℝ) * (L : ℝ) ^ 2 * ((m - n : ℕ) : ℝ) *
              (3 : ℝ) ^ (-((d : ℝ) / 2 * ((m - ell : ℕ) : ℝ))))) ∧
      ∀ (h0 : Mat d) (hh0 : matTranspose h0 = -h0) (Pvec : BlockVec d)
        (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d),
        blockVecDot Pvec
            (blockMatVecMul
              (Homogenization.Book.Ch02.coarseBlockMatrix
                (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d (m : ℤ)))
                (newMixParam_aLplusH0 nu hnu omega L m h0 hh0))
              Pvec) ≤
          Homogenization.blockVecDot (blockMatVecMul (blockG (-h0)) Pvec)
              (blockMatVecMul (blockG (-h0)) Pvec) * X0 omega +
          Homogenization.descendantsAverage (Homogenization.originCube d (m : ℤ)) (m - n)
            (fun R => blockVecDot
              (blockMatVecMul
                (Homogenization.Book.Ch02.blockG
                  (-(Homogenization.volumeAverageMat (Homogenization.cubeSet R)
                        (fun y => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                          omega ell L y) + h0)))
                Pvec)
              (blockMatVecMul
                (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu ell P
                  (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ))))
                (blockMatVecMul
                  (Homogenization.Book.Ch02.blockG
                    (-(Homogenization.volumeAverageMat (Homogenization.cubeSet R)
                          (fun y => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                            omega ell L y) + h0)))
                  Pvec))) := by
  obtain ⟨C, hC⟩ := newMixAsm_splitting_uniform d
  refine ⟨|C|, ?_⟩
  intro nu P hnu hnu1 hPrefix hJ1V2 hJ2 hJ3 hJ4 L m ell n hn_ell hell_m hell_L hell1 hL1 hmn1
  obtain ⟨X0, hX0meas, hX0BigO, hX0bound⟩ :=
    hC hnu hnu1 hPrefix hJ1V2 hJ2 hJ3 hJ4 hn_ell hell_m hell_L
  refine ⟨X0, hX0meas, ?_, hX0bound⟩
  refine hX0BigO.mono_scale ?_
  have hnupow : nu ^ (-(3 : ℝ)) ≤ nu ^ (-(4 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hnu hnu1 (by norm_num)
  have hnu3nn : (0 : ℝ) ≤ nu ^ (-(3 : ℝ)) := Real.rpow_nonneg hnu.le _
  have hLR : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
  have hellR : (1 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell1
  have hmnR : (1 : ℝ) ≤ ((m - n : ℕ) : ℝ) := by exact_mod_cast hmn1
  have hLsq : (L : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith only [hLR]
  rw [max_eq_right hLR, max_eq_right hellR, max_eq_right hmnR]
  have hb1le : (L : ℝ) * (3 : ℝ) ^ (-((ell - n : ℕ) : ℝ)) ≤
      (L : ℝ) ^ 2 * (3 : ℝ) ^ (-((ell - n : ℕ) : ℝ)) := by
    have hpow1nn : (0 : ℝ) ≤ (3 : ℝ) ^ (-((ell - n : ℕ) : ℝ)) := by positivity
    exact mul_le_mul_of_nonneg_right hLsq hpow1nn
  have hb2le : (ell : ℝ) * (L : ℝ) * ((m - n : ℕ) : ℝ) *
        (3 : ℝ) ^ (-((d : ℝ) / 2 * ((m - ell : ℕ) : ℝ))) ≤
      (ell : ℝ) * (L : ℝ) ^ 2 * ((m - n : ℕ) : ℝ) *
        (3 : ℝ) ^ (-((d : ℝ) / 2 * ((m - ell : ℕ) : ℝ))) := by
    have hpow2nn : (0 : ℝ) ≤ (3 : ℝ) ^ (-((d : ℝ) / 2 * ((m - ell : ℕ) : ℝ))) := by positivity
    have h1 : (ell : ℝ) * (L : ℝ) ≤ (ell : ℝ) * (L : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hLsq (by linarith only [hellR])
    have h2 : (ell : ℝ) * (L : ℝ) * ((m - n : ℕ) : ℝ) ≤
        (ell : ℝ) * (L : ℝ) ^ 2 * ((m - n : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right h1 (by linarith only [hmnR])
    exact mul_le_mul_of_nonneg_right h2 hpow2nn
  have hbracketle :
      ((if ell < L then (L : ℝ) * (3 : ℝ) ^ (-((ell - n : ℕ) : ℝ)) else 0) +
        (ell : ℝ) * (L : ℝ) * ((m - n : ℕ) : ℝ) *
          (3 : ℝ) ^ (-((d : ℝ) / 2 * ((m - ell : ℕ) : ℝ)))) ≤
      ((if ell < L then (L : ℝ) ^ 2 * (3 : ℝ) ^ (-((ell - n : ℕ) : ℝ)) else 0) +
        (ell : ℝ) * (L : ℝ) ^ 2 * ((m - n : ℕ) : ℝ) *
          (3 : ℝ) ^ (-((d : ℝ) / 2 * ((m - ell : ℕ) : ℝ)))) := by
    split_ifs with hcase
    · linarith only [hb1le, hb2le]
    · linarith only [hb2le]
  have hCleAbsC : C ≤ |C| := le_abs_self C
  have hAbsCnn : (0 : ℝ) ≤ |C| := abs_nonneg C
  have hbracketnn : (0 : ℝ) ≤
      (if ell < L then (L : ℝ) * (3 : ℝ) ^ (-((ell - n : ℕ) : ℝ)) else 0) +
        (ell : ℝ) * (L : ℝ) * ((m - n : ℕ) : ℝ) *
          (3 : ℝ) ^ (-((d : ℝ) / 2 * ((m - ell : ℕ) : ℝ))) := by
    have h1 : (0 : ℝ) ≤ if ell < L then (L : ℝ) * (3 : ℝ) ^ (-((ell - n : ℕ) : ℝ)) else 0 := by
      split_ifs with h <;> positivity
    have h2 : (0 : ℝ) ≤ (ell : ℝ) * (L : ℝ) * ((m - n : ℕ) : ℝ) *
        (3 : ℝ) ^ (-((d : ℝ) / 2 * ((m - ell : ℕ) : ℝ))) := by positivity
    linarith only [h1, h2]
  calc C * nu ^ (-(3 : ℝ)) *
      ((if ell < L then (L : ℝ) * (3 : ℝ) ^ (-((ell - n : ℕ) : ℝ)) else 0) +
        (ell : ℝ) * (L : ℝ) * ((m - n : ℕ) : ℝ) *
          (3 : ℝ) ^ (-((d : ℝ) / 2 * ((m - ell : ℕ) : ℝ))))
      ≤ |C| * nu ^ (-(3 : ℝ)) *
          ((if ell < L then (L : ℝ) * (3 : ℝ) ^ (-((ell - n : ℕ) : ℝ)) else 0) +
            (ell : ℝ) * (L : ℝ) * ((m - n : ℕ) : ℝ) *
              (3 : ℝ) ^ (-((d : ℝ) / 2 * ((m - ell : ℕ) : ℝ)))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCleAbsC hnu3nn) hbracketnn
    _ ≤ |C| * nu ^ (-(4 : ℝ)) *
          ((if ell < L then (L : ℝ) * (3 : ℝ) ^ (-((ell - n : ℕ) : ℝ)) else 0) +
            (ell : ℝ) * (L : ℝ) * ((m - n : ℕ) : ℝ) *
              (3 : ℝ) ^ (-((d : ℝ) / 2 * ((m - ell : ℕ) : ℝ)))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnupow hAbsCnn) hbracketnn
    _ ≤ |C| * nu ^ (-(4 : ℝ)) *
          ((if ell < L then (L : ℝ) ^ 2 * (3 : ℝ) ^ (-((ell - n : ℕ) : ℝ)) else 0) +
            (ell : ℝ) * (L : ℝ) ^ 2 * ((m - n : ℕ) : ℝ) *
              (3 : ℝ) ^ (-((d : ℝ) / 2 * ((m - ell : ℕ) : ℝ)))) :=
        mul_le_mul_of_nonneg_left hbracketle (by positivity)

end

end SuperdiffusionCLT.Section4.NewMixing
