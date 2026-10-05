/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Probability.IndependentSums.WeakOrlicz
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

open MeasureTheory
open Homogenization.IndependentSums

/-- `e.powerofGammasigma` at the square root: if `Y = O_{Γ_σ}(B)` then
`√|Y| = O_{Γ_{2σ}}(√B)`. -/
theorem srootE_isBigO_sqrt_abs {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {Y : Ω → ℝ} {B σ : ℝ} (hB : 0 ≤ B)
    (hY : IsBigO μ (gammaSigma σ) Y B) :
    IsBigO μ (gammaSigma (2 * σ)) (fun ω => Real.sqrt |Y ω|) (Real.sqrt B) := by
  rw [isBigO_gammaSigma_iff] at hY ⊢
  intro t ht
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  have ht2 : 1 ≤ t ^ 2 := one_le_pow₀ ht
  have hsub : absTailEvent (fun ω => Real.sqrt |Y ω|) (Real.sqrt B * t) ⊆
      absTailEvent Y (B * t ^ 2) := by
    intro ω hω
    simp only [mem_absTailEvent, abs_of_nonneg (Real.sqrt_nonneg _)] at hω ⊢
    have h0 : 0 ≤ Real.sqrt B * t := mul_nonneg (Real.sqrt_nonneg _) ht0
    have hsq := mul_self_lt_mul_self h0 hω
    rw [Real.mul_self_sqrt (abs_nonneg _)] at hsq
    have : Real.sqrt B * t * (Real.sqrt B * t) = B * t ^ 2 := by
      rw [show Real.sqrt B * t * (Real.sqrt B * t) = (Real.sqrt B * Real.sqrt B) * t ^ 2 by ring,
        Real.mul_self_sqrt hB]
    rw [this] at hsq
    exact hsq
  refine le_trans (measureReal_mono hsub) (le_trans (hY ht2) ?_)
  refine Real.exp_le_exp.2 (neg_le_neg (le_of_eq ?_))
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht0]
  norm_num

/-- The two-variable version at `σ = 1/3`: if `Y, Z = O_{Γ_{1/3}}(B)` then
`√(|Y| + |Z|) = O_{Γ_{2/3}}(4 √B)`. -/
theorem srootE_isBigO_sqrt_abs_add {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {Y Z : Ω → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hY : IsBigO μ (gammaSigma (1 / 3)) Y B) (hZ : IsBigO μ (gammaSigma (1 / 3)) Z B) :
    IsBigO μ (gammaSigma (2 / 3)) (fun ω => Real.sqrt (|Y ω| + |Z ω|)) (4 * Real.sqrt B) := by
  rw [isBigO_gammaSigma_iff] at hY hZ ⊢
  intro t ht
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  have ht8 : 1 ≤ 8 * t ^ 2 := by nlinarith only [ht]
  have hsub : absTailEvent (fun ω => Real.sqrt (|Y ω| + |Z ω|)) (4 * Real.sqrt B * t) ⊆
      absTailEvent Y (B * (8 * t ^ 2)) ∪ absTailEvent Z (B * (8 * t ^ 2)) := by
    intro ω hω
    simp only [mem_absTailEvent, abs_of_nonneg (Real.sqrt_nonneg _)] at hω
    have h0 : 0 ≤ 4 * Real.sqrt B * t := by positivity
    have hsq := mul_self_lt_mul_self h0 hω
    rw [Real.mul_self_sqrt (by positivity)] at hsq
    have : 4 * Real.sqrt B * t * (4 * Real.sqrt B * t) = 16 * B * t ^ 2 := by
      rw [show 4 * Real.sqrt B * t * (4 * Real.sqrt B * t) =
          16 * (Real.sqrt B * Real.sqrt B) * t ^ 2 by ring, Real.mul_self_sqrt hB]
    rw [this] at hsq
    by_contra hcon
    simp only [Set.mem_union, mem_absTailEvent, not_or, not_lt] at hcon
    linarith only [hsq, hcon.1, hcon.2]
  have hpow : (8 * t ^ 2) ^ ((1 : ℝ) / 3) = 2 * t ^ ((2 : ℝ) / 3) := by
    rw [Real.mul_rpow (by norm_num) (by positivity)]
    have h8 : (8 : ℝ) ^ ((1 : ℝ) / 3) = 2 := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [h8, ← Real.rpow_natCast, ← Real.rpow_mul ht0]
    norm_num
  have hx : 1 ≤ t ^ ((2 : ℝ) / 3) := Real.one_le_rpow ht (by norm_num)
  have hhalf : Real.exp (-(t ^ ((2 : ℝ) / 3))) ≤ 1 / 2 := by
    have h1 : Real.exp (-(t ^ ((2 : ℝ) / 3))) ≤ Real.exp (-1) :=
      Real.exp_le_exp.2 (neg_le_neg hx)
    have h2 : Real.exp (-1) < 1 / 2 := by
      have := Real.add_one_lt_exp (one_ne_zero : (1 : ℝ) ≠ 0)
      rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
      linarith only [this]
    linarith only [h1, h2]
  have hsplit : Real.exp (-(2 * t ^ ((2 : ℝ) / 3))) =
      Real.exp (-(t ^ ((2 : ℝ) / 3))) * Real.exp (-(t ^ ((2 : ℝ) / 3))) := by
    rw [← Real.exp_add]; ring_nf
  calc μ.real (absTailEvent (fun ω => Real.sqrt (|Y ω| + |Z ω|)) (4 * Real.sqrt B * t))
      ≤ μ.real (absTailEvent Y (B * (8 * t ^ 2)) ∪ absTailEvent Z (B * (8 * t ^ 2))) :=
        measureReal_mono hsub
    _ ≤ μ.real (absTailEvent Y (B * (8 * t ^ 2))) + μ.real (absTailEvent Z (B * (8 * t ^ 2))) :=
        measureReal_union_le _ _
    _ ≤ Real.exp (-((8 * t ^ 2) ^ ((1 : ℝ) / 3))) + Real.exp (-((8 * t ^ 2) ^ ((1 : ℝ) / 3))) :=
        add_le_add (hY ht8) (hZ ht8)
    _ = 2 * Real.exp (-(2 * t ^ ((2 : ℝ) / 3))) := by rw [hpow]; ring
    _ ≤ Real.exp (-(t ^ ((2 : ℝ) / 3))) := by
        rw [hsplit]
        have he : 0 ≤ Real.exp (-(t ^ ((2 : ℝ) / 3))) := (Real.exp_pos _).le
        nlinarith only [he, hhalf]

/-- The near/deep split of a nonnegative series: `∑' f ≤ ∑_{l<N} f l + ∑' f (l+N)`,
with no summability hypothesis. -/
theorem srootE_tsum_le_split {f : ℕ → ℝ} (hf : ∀ l, 0 ≤ f l) (N : ℕ) :
    ∑' l, f l ≤ ∑ l ∈ Finset.range N, f l + ∑' l, f (l + N) := by
  by_cases hs : Summable f
  · exact le_of_eq ((Summable.sum_add_tsum_nat_add N hs).symm)
  · rw [tsum_eq_zero_of_not_summable hs]
    exact add_nonneg (Finset.sum_nonneg fun l _ => hf l) (tsum_nonneg fun l => hf (l + N))

end SuperdiffusionCLT.Section4.MinimalScales
