/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Probability.GammaSigmaHelpers
public import SuperdiffusionCLT.Section2.Estimates.Stream.OriginConcentration

/-!
# Marginal finite-shell concentration at a fixed point

This module transports the scalar shell inputs individually by stationarity
before applying independent-sum concentration. It does not assert joint
stationarity of the shell sequence and uses no scaling law.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Estimates.Stream

open Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Section2.Cutoff
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}
variable {P : MeasureTheory.ProbabilityMeasure (ShellSeq d)}

/-- Entrywise marginal concentration for a finite shell increment at an
arbitrary deterministic spatial point. -/
theorem isBigO_gammaSigma_incrementAt_entry
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    {n m : ℕ} (hnm : n < m) (x : Vec d) (i k : Fin d) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d ↦
        ∑ l ∈ Finset.Ioc n m, (omega l) x i k)
      (Book.Ch04.gammaSigmaIndependentSumConst 2 *
        Real.sqrt ((m - n : ℕ) : ℝ)) := by
  have h :=
    Book.Ch04.isBigO_gammaSigma_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero
      (μ := P.toMeasure)
      (X := fun (l : ℕ) (omega : ShellSeq d) ↦ (omega l) x i k)
      (s := Finset.Ioc n m) (σ := 2) (K := 1)
      (hJ2.iIndepFun_entry_coordinate x i k)
      (fun l ↦ ShellLawConsequences.measurable_entry_coordinate l x i k)
      (Finset.nonempty_Ioc.mpr hnm) (by norm_num) (by norm_num) (by norm_num)
      (fun l _ ↦
        ShellLawConsequences.isBigO_gammaSigma_entry_coordinate
          hPrefix hJ3 l x i k)
      (fun l _ ↦
        ShellLawConsequences.integral_entry_coordinate_eq_zero hJ4 l x i k)
  simpa only [Nat.card_Ioc, mul_one] using h

/-- Marginal concentration for the matrix-valued finite shell increment at an
arbitrary deterministic spatial point, with the same amplitude as at the
origin. -/
theorem isBigOWith_gammaSigma_incrementAt
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    {n m : ℕ} (hnm : n < m) (x : Vec d) :
    IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d ↦
        matrixOperatorNorm (finiteShellIncrement omega n m x))
      (IndependentSums.gammaTriangleConst 2 *
        ((d : ℝ) ^ 2 *
          (Book.Ch04.gammaSigmaIndependentSumConst 2 *
            Real.sqrt ((m - n : ℕ) : ℝ)))) := by
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) hPrefix.dimension
  have hGap : (0 : ℝ) < (m - n : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt hnm
  have hAmp : 0 < Book.Ch04.gammaSigmaIndependentSumConst 2 *
      Real.sqrt ((m - n : ℕ) : ℝ) :=
    mul_pos gammaSigmaIndependentSumConst_two_pos
      (Real.sqrt_pos.2 hGap)
  have hne : (Finset.univ : Finset (Fin d × Fin d)).Nonempty :=
    ⟨(⟨0, hd⟩, ⟨0, hd⟩), Finset.mem_univ _⟩
  have hentry : ∀ p : Fin d × Fin d,
      IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
        (fun omega : ShellSeq d ↦
          |∑ l ∈ Finset.Ioc n m, (omega l) x p.1 p.2|)
        (Book.Ch04.gammaSigmaIndependentSumConst 2 *
          Real.sqrt ((m - n : ℕ) : ℝ)) := by
    intro p
    have h := isBigO_gammaSigma_incrementAt_entry
      hPrefix hJ2 hJ3 hJ4 hnm x p.1 p.2
    simpa only [IndependentSums.IsBigO, abs_abs] using h
  have hmeas : ∀ p : Fin d × Fin d, Measurable (fun omega : ShellSeq d ↦
      |∑ l ∈ Finset.Ioc n m, (omega l) x p.1 p.2|) := by
    intro p
    have hsum : Measurable (fun omega : ShellSeq d ↦
        ∑ l ∈ Finset.Ioc n m, (omega l) x p.1 p.2) :=
      Finset.measurable_sum (Finset.Ioc n m) fun l _ ↦
        ShellLawConsequences.measurable_entry_coordinate l x p.1 p.2
    simpa only [Real.norm_eq_abs] using hsum.norm
  have htriangle := IndependentSums.isBigO_finset_sum_of_isBigO_gammaSigma
    (μ := P.toMeasure) (Finset.univ : Finset (Fin d × Fin d))
    (X := fun p omega ↦ |∑ l ∈ Finset.Ioc n m, (omega l) x p.1 p.2|)
    (a := fun _ : Fin d × Fin d ↦
      Book.Ch04.gammaSigmaIndependentSumConst 2 *
        Real.sqrt ((m - n : ℕ) : ℝ))
    (σ := 2) (by norm_num) hne (fun _ _ ↦ hAmp)
    (fun p _ ↦ hentry p) (fun p _ ↦ hmeas p)
  have hcard : ∑ _p : Fin d × Fin d,
      (Book.Ch04.gammaSigmaIndependentSumConst 2 *
        Real.sqrt ((m - n : ℕ) : ℝ)) =
      (d : ℝ) ^ 2 *
        (Book.Ch04.gammaSigmaIndependentSumConst 2 *
          Real.sqrt ((m - n : ℕ) : ℝ)) := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin]
    push_cast
    ring
  rw [hcard] at htriangle
  refine htriangle.of_le fun omega ↦ ?_
  refine (matrixOperatorNorm_le_sum_univ_abs_entry _).trans ?_
  refine le_trans (le_of_eq ?_) (le_abs_self _)
  exact Finset.sum_congr rfl fun p _ ↦ by
    rw [finiteShellIncrement_apply_entry]

end

end SuperdiffusionCLT.Section2.Estimates.Stream
