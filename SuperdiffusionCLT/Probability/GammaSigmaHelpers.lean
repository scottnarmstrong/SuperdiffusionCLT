/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Book.Ch04.Theorems.Concentration

/-!
# Shared helpers for stretched-exponential tail estimates

The paper writes every concentration estimate of Section 2 as
`X ≤ O_{Gamma_sigma}(A)`, and the same four elementary facts about that
notation are needed in several modules. They are collected here once so
that a single proof serves all of them.

## Main results

* `gammaSigmaIndependentSumConst_two_pos`: the constant of the independent-sum
  concentration rule of `CoarseGraining` is positive at `sigma = 2`, the value
  used throughout Section 2. The upstream positivity proof is `private`, so it
  is reproved here from the definition; at `sigma = 2` the rule takes its
  exponential-regime branch.
* `isBigOWith_iff_isBigO_of_nonneg`: for a nonnegative random variable the
  one-sided tail predicate `IsBigOWith` and the absolute-value predicate
  `IsBigO` agree, because the absolute value may be dropped.
* `isBigO_gammaSigma_add_of_isBigO`: the two-term case of the triangle
  inequality for `Gamma_sigma` tails, with the constant
  `gammaTriangleConst sigma` of `CoarseGraining`.
* `sum_Ioc_inv_pow_three_le`: the geometric tail sum
  `sum_{k = n+1}^{m} 3^{-k} ≤ 3^{-n}`, used whenever a telescoping estimate
  over shells is summed.
-/

@[expose] public section

namespace SuperdiffusionCLT.Probability

open Homogenization
open MeasureTheory

noncomputable section

/-- The independent-sum concentration constant of `CoarseGraining` is positive
at `sigma = 2`. -/
theorem gammaSigmaIndependentSumConst_two_pos :
    0 < Book.Ch04.gammaSigmaIndependentSumConst 2 := by
  rw [Book.Ch04.gammaSigmaIndependentSumConst, ite_eq_right (by norm_num)]
  change 0 < IndependentSums.gammaSigmaExpRegimeEndpointConst 2
  rw [IndependentSums.gammaSigmaExpRegimeEndpointConst, ite_eq_right (by norm_num)]
  refine mul_pos (by norm_num) ?_
  dsimp [IndependentSums.gammaSigmaExpRegimeConst]
  exact lt_of_lt_of_le
    (mul_pos (by positivity)
      (IndependentSums.gammaMomentConst_pos (by norm_num)))
    (le_max_left _ _)

/-- For a nonnegative random variable the one-sided tail bound is the same
statement as the absolute-value tail bound. -/
theorem isBigOWith_iff_isBigO_of_nonneg
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {Psi : ℝ → ℝ} {X : Omega → ℝ} {A : ℝ}
    (hX : ∀ omega, 0 ≤ X omega) :
    IndependentSums.IsBigOWith mu Psi X A ↔
      IndependentSums.IsBigO mu Psi X A := by
  have habs : (fun omega ↦ |X omega|) = X :=
    funext fun omega ↦ abs_of_nonneg (hX omega)
  rw [IndependentSums.IsBigO, habs]

/-- The two-term triangle inequality for `Gamma_sigma` tails: a sum of two
random variables with amplitudes `A` and `B` has amplitude
`gammaTriangleConst sigma * (A + B)`. -/
theorem isBigO_gammaSigma_add_of_isBigO
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsFiniteMeasure mu] {X Y : Omega → ℝ} {A B sigma : ℝ}
    (hsigma : 0 < sigma) (hA : 0 < A) (hB : 0 < B)
    (hX : IndependentSums.IsBigO mu (IndependentSums.gammaSigma sigma) X A)
    (hY : IndependentSums.IsBigO mu (IndependentSums.gammaSigma sigma) Y B)
    (hXm : Measurable X) (hYm : Measurable Y) :
    IndependentSums.IsBigO mu (IndependentSums.gammaSigma sigma)
      (fun omega ↦ X omega + Y omega)
      (IndependentSums.gammaTriangleConst sigma * (A + B)) := by
  classical
  have hsum : ∑ i ∈ Finset.range 2,
      (if i = 0 then A else B) = A + B := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    norm_num
  have htriangle := IndependentSums.isBigO_finset_sum_of_isBigO_gammaSigma
    (μ := mu) (Finset.range 2)
    (X := fun i : ℕ ↦ if i = 0 then X else Y)
    (a := fun i : ℕ ↦ if i = 0 then A else B) (σ := sigma) hsigma
    (Finset.nonempty_range_iff.mpr (by norm_num))
    (fun i _ ↦ by split_ifs <;> assumption)
    (fun i _ ↦ by split_ifs <;> assumption)
    (fun i _ ↦ by split_ifs <;> assumption)
  rw [hsum] at htriangle
  have hfun :
      (fun omega ↦ ∑ i ∈ Finset.range 2,
        (if i = 0 then X else Y) omega) =
        fun omega ↦ X omega + Y omega := by
    funext omega
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    norm_num
  rw [hfun] at htriangle
  exact htriangle

/-- The geometric tail sum over a half-open range of shells:
`sum_{k = n+1}^{m} 3^{-k} ≤ 3^{-n}`. -/
theorem sum_Ioc_inv_pow_three_le {n m : ℕ} (hnm : n ≤ m) :
    ∑ k ∈ Finset.Ioc n m, ((3 : ℝ) ^ k)⁻¹ ≤
      ((3 : ℝ) ^ n)⁻¹ := by
  have hIoc : Finset.Ioc n m = Finset.Ico (n + 1) (m + 1) := by
    ext k
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  let r : ℝ := (3 : ℝ)⁻¹
  simp only [← inv_pow]
  change ∑ k ∈ Finset.Ioc n m, r ^ k ≤ r ^ n
  rw [hIoc]
  have hr : r = 1 / 3 := by norm_num [r]
  have hone_sub : 1 - r = (2 / 3 : ℝ) := by rw [hr]; norm_num
  have hnm_succ : n + 1 ≤ m + 1 := Nat.add_le_add_right hnm 1
  have hgeom := geom_sum_Ico_mul_neg r hnm_succ
  have hpow_nonneg : 0 ≤ r ^ n := pow_nonneg (by positivity) n
  have hpow_m_nonneg : 0 ≤ r ^ (m + 1) := pow_nonneg (by positivity) (m + 1)
  have hstep : r ^ (n + 1) = (1 / 3 : ℝ) * r ^ n := by
    rw [pow_succ, hr]
    ring
  rw [hone_sub, hstep] at hgeom
  have hgeom_le :
      (∑ k ∈ Finset.Ico (n + 1) (m + 1), r ^ k) * (2 / 3 : ℝ) ≤
        (1 / 3 : ℝ) * r ^ n := by
    rw [hgeom]
    exact sub_le_self _ hpow_m_nonneg
  have hhalf :
      ∑ k ∈ Finset.Ico (n + 1) (m + 1), r ^ k ≤
        (1 / 2 : ℝ) * r ^ n := by
    rw [show (1 / 2 : ℝ) * r ^ n =
      ((1 / 3 : ℝ) * r ^ n) / (2 / 3 : ℝ) by ring]
    exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 2 / 3)).2 hgeom_le
  exact hhalf.trans <| by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (by norm_num : (1 / 2 : ℝ) ≤ 1) hpow_nonneg

end

end SuperdiffusionCLT.Probability
