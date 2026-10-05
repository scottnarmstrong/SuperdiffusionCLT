/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.LinftyL2B

/-!
# `L^∞`-`L²` estimate: the scale bookkeeping

The bottom scale `nK N n = n - ⌈N log n⌉₊` of the interior estimate equals the exponent `ms_e N n`
of the minimal scale for `n ≥ ms_j0 N`, and a radius `r ≥ C₀ 3^{m⋆}` determines a triadic scale
`n` with `3^n ≤ r / C₀ < 3^{n+1}` at which the interior estimate is available.
-/

@[expose] public section

open MeasureTheory
open SuperdiffusionCLT.Section7

namespace SuperdiffusionCLT.Section8

theorem linfL2_nK_eq {N : ℝ} (hN : 0 ≤ N) {n : ℕ} (hn : ms_j0 N ≤ n) :
    ((nK N n : ℕ) : ℤ) = ms_e N n := by
  have hK : (4 * N + 2) ^ 2 ≤ (n : ℝ) := by
    have : ((ms_j0 N : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    exact le_trans (Nat.le_ceil _) this
  have h := ceil_le_half hN hK
  have hle : ⌈N * Real.log (n : ℝ)⌉₊ ≤ n := by
    have : (⌈N * Real.log (n : ℝ)⌉₊ : ℝ) ≤ n := by
      have : 0 ≤ (⌈N * Real.log (n : ℝ)⌉₊ : ℝ) := Nat.cast_nonneg _
      linarith only [h, this]
    exact_mod_cast this
  have hlog : 0 ≤ N * Real.log (n : ℝ) := by
    have hn1 : (1 : ℝ) ≤ n := by nlinarith only [sq_nonneg N, hK, hN]
    exact mul_nonneg hN (Real.log_nonneg hn1)
  unfold nK ms_e
  rw [Nat.cast_sub hle, Int.natCast_ceil_eq_ceil hlog]

/-- The interior-estimate conditions at the scale attached to a radius. -/
theorem linfL2_scale {N L X0 C0 r : ℝ} (hN : 0 ≤ N) (hX : 1 ≤ X0) (hC0 : 1 ≤ C0)
    (hr : C0 * (3 : ℝ) ^ ms_star N L X0 ≤ r) :
    ∃ n : ℕ, ms_j0 N ≤ n ∧ L ≤ (nK N n : ℝ) ∧ X0 ≤ (3 : ℝ) ^ nK N n ∧
      (3 : ℝ) ^ n ≤ r / C0 ∧ r / C0 < (3 : ℝ) ^ (n + 1) := by
  have hC : 0 < C0 := by linarith only [hC0]
  obtain ⟨_, hj, hL, hX0⟩ := ms_scale_consumer_real hN hX hC0 hr
  set n := ⌊Real.logb 3 (r / C0)⌋₊ with hn
  have hpos : 0 < r / C0 := by
    have : (1 : ℝ) ≤ (3 : ℝ) ^ ms_star N L X0 := one_le_pow₀ (by norm_num)
    rw [lt_div_iff₀ hC]; nlinarith only [hr, this, hC0]
  have heq := linfL2_nK_eq hN hj
  have hL' : L ≤ (nK N n : ℝ) := by
    have : (((nK N n : ℕ) : ℤ) : ℝ) = (nK N n : ℝ) := Int.cast_natCast _
    rw [← this, heq]; exact hL
  have hX' : X0 ≤ (3 : ℝ) ^ nK N n := by
    rw [← zpow_natCast, heq]; exact hX0
  have hl : 0 ≤ Real.logb 3 (r / C0) := Real.logb_nonneg (by norm_num) (by
    have : (1 : ℝ) ≤ (3 : ℝ) ^ ms_star N L X0 := one_le_pow₀ (by norm_num)
    rw [le_div_iff₀ hC]; nlinarith only [hr, this, hC0])
  refine ⟨n, hj, hL', hX', ?_, ?_⟩
  · have h1 : (n : ℝ) ≤ Real.logb 3 (r / C0) := Nat.floor_le hl
    have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 3 by norm_num) h1
    rwa [Real.rpow_natCast, Real.rpow_logb (by norm_num) (by norm_num) hpos] at this
  · have h1 : Real.logb 3 (r / C0) < (n : ℝ) + 1 := Nat.lt_floor_add_one _
    have := Real.rpow_lt_rpow_of_exponent_lt (show (1 : ℝ) < 3 by norm_num) h1
    rw [Real.rpow_logb (by norm_num) (by norm_num) hpos, Real.rpow_add (by norm_num),
      Real.rpow_natCast, Real.rpow_one] at this
    rw [pow_succ]; exact this

end SuperdiffusionCLT.Section8
