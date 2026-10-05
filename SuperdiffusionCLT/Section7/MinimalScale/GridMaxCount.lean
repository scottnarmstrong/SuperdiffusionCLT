/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.MinimalScale.GridMax

/-!
# The polynomial grid count at scale `K`

For `n_K = K - ⌈N log K⌉₊`, the grid `3^{n_K-3}ℤ^d ∩ {‖y‖_∞ ≤ 3^{K+2}}` has at most `B K^b`
points, with `B = 1500^d` and `b = d N log 3`, as soon as `K ≥ (4N+2)^2`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open MeasureTheory Homogenization

noncomputable section

/-- The bottom scale `n_K = K - ⌈N log K⌉₊`. -/
def nK (N : ℝ) (K : ℕ) : ℕ := K - ⌈N * Real.log (K : ℝ)⌉₊

/-- For `K ≥ (4N+2)^2` the cut is at most `K / 2`. -/
theorem ceil_le_half {N : ℝ} (hN : 0 ≤ N) {K : ℕ} (hK : (4 * N + 2) ^ 2 ≤ (K : ℝ)) :
    2 * (⌈N * Real.log (K : ℝ)⌉₊ : ℝ) ≤ K := by
  have hK1 : (1 : ℝ) ≤ K := by nlinarith only [sq_nonneg N, hK, hN]
  have hK0 : (0 : ℝ) ≤ K := by linarith only [hK1]
  have hlog : 0 ≤ N * Real.log (K : ℝ) := mul_nonneg hN (Real.log_nonneg hK1)
  have hceil : (⌈N * Real.log (K : ℝ)⌉₊ : ℝ) < N * Real.log (K : ℝ) + 1 := Nat.ceil_lt_add_one hlog
  have hl : Real.log (K : ℝ) ≤ (K : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) :=
    Real.log_le_rpow_div hK0 (by norm_num)
  set s := Real.sqrt (K : ℝ) with hs
  have hsq : s ^ 2 = (K : ℝ) := Real.sq_sqrt hK0
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hKrpow : (K : ℝ) ^ (1 / 2 : ℝ) = s := by rw [hs, Real.sqrt_eq_rpow]
  rw [hKrpow] at hl
  have hs4 : 4 * N + 2 ≤ s := by
    have := Real.sqrt_le_sqrt hK
    rwa [Real.sqrt_sq (by linarith only [hN])] at this
  have h1 : N * Real.log (K : ℝ) ≤ N * (2 * s) := by
    refine mul_le_mul_of_nonneg_left ?_ hN
    linarith only [hl]
  have h2 : 2 * (N * (2 * s) + 1) ≤ s ^ 2 := by nlinarith only [hs4, hN, hs0]
  linarith only [hceil, h1, h2, hsq]

theorem nK_cast {N : ℝ} (hN : 0 ≤ N) {K : ℕ} (hK : (4 * N + 2) ^ 2 ≤ (K : ℝ)) :
    (nK N K : ℝ) = K - ⌈N * Real.log (K : ℝ)⌉₊ := by
  have h := ceil_le_half hN hK
  have hle : ⌈N * Real.log (K : ℝ)⌉₊ ≤ K := by
    have : (⌈N * Real.log (K : ℝ)⌉₊ : ℝ) ≤ K := by
      have : 0 ≤ (⌈N * Real.log (K : ℝ)⌉₊ : ℝ) := Nat.cast_nonneg _
      linarith only [h, this]
    exact_mod_cast this
  unfold nK
  rw [Nat.cast_sub hle]

theorem nK_ge_half {N : ℝ} (hN : 0 ≤ N) {K : ℕ} (hK : (4 * N + 2) ^ 2 ≤ (K : ℝ)) :
    (K : ℝ) / 2 ≤ nK N K := by
  rw [nK_cast hN hK]
  linarith only [ceil_le_half hN hK]

theorem nK_le (N : ℝ) (K : ℕ) : nK N K ≤ K := Nat.sub_le _ _

/-- **Polynomial count.** -/
theorem card_grid_le_poly (d : ℕ) {N : ℝ} (hN : 0 ≤ N) {K : ℕ}
    (hK : (4 * N + 2) ^ 2 ≤ (K : ℝ)) :
    ((gridPts d ((nK N K : ℤ) - 3) ((3 : ℝ) ^ (K + 2))).card : ℝ) ≤
      (1500 : ℝ) ^ d * (K : ℝ) ^ ((d : ℝ) * (N * Real.log 3)) := by
  have hK1 : (1 : ℝ) ≤ K := by nlinarith only [sq_nonneg N, hK, hN]
  have hR : (0 : ℝ) ≤ (3 : ℝ) ^ (K + 2) := by positivity
  refine (card_gridPts_le d _ hR).trans ?_
  set h := ⌈N * Real.log (K : ℝ)⌉₊ with hh
  have hsum : nK N K + h = K := by
    have : h ≤ K := by
      have := ceil_le_half hN hK
      have h0 : (0 : ℝ) ≤ h := Nat.cast_nonneg _
      exact_mod_cast (by linarith only [this, h0] : (h : ℝ) ≤ K)
    unfold nK; omega
  have hdiv : 2 * (3 : ℝ) ^ (K + 2) / (3 : ℝ) ^ ((nK N K : ℤ) - 3) = 2 * 3 ^ (h + 5) := by
    have : K + 2 = nK N K + h + 2 := by omega
    rw [zpow_sub₀ (by norm_num), zpow_natCast, this]
    have : (3 : ℝ) ^ (nK N K + h + 2) = 3 ^ (nK N K) * 3 ^ (h + 5) / 3 ^ 3 := by
      rw [eq_div_iff (by norm_num)]; ring
    rw [this]; field_simp
  have hhle : (h : ℝ) ≤ N * Real.log (K : ℝ) + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg hN (Real.log_nonneg hK1))).le
  have h3 : (3 : ℝ) ^ h ≤ 3 * (K : ℝ) ^ (N * Real.log 3) := by
    have : (3 : ℝ) ^ h = (3 : ℝ) ^ (h : ℝ) := (Real.rpow_natCast 3 h).symm
    rw [this]
    calc (3 : ℝ) ^ (h : ℝ) ≤ (3 : ℝ) ^ (N * Real.log (K : ℝ) + 1) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hhle
      _ = 3 * (K : ℝ) ^ (N * Real.log 3) := by
          rw [Real.rpow_add (by norm_num), Real.rpow_one, mul_comm]
          congr 1
          rw [Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos (by linarith only [hK1])]
          congr 1; ring
  have hKe : (1 : ℝ) ≤ (K : ℝ) ^ (N * Real.log 3) :=
    Real.one_le_rpow hK1 (mul_nonneg hN (Real.log_nonneg (by norm_num)))
  have hbase : 2 * (3 : ℝ) ^ (h + 5) + 1 ≤ 1500 * (K : ℝ) ^ (N * Real.log 3) := by
    have : (3 : ℝ) ^ (h + 5) = 3 ^ h * 243 := by rw [pow_add]; norm_num
    rw [this]
    nlinarith only [h3, hKe]
  rw [hdiv]
  calc (2 * (3 : ℝ) ^ (h + 5) + 1) ^ d ≤ (1500 * (K : ℝ) ^ (N * Real.log 3)) ^ d :=
        pow_le_pow_left₀ (by positivity) hbase d
    _ = (1500 : ℝ) ^ d * (K : ℝ) ^ ((d : ℝ) * (N * Real.log 3)) := by
        rw [mul_pow, ← Real.rpow_natCast ((K : ℝ) ^ (N * Real.log 3)) d,
          ← Real.rpow_mul (by linarith only [hK1])]
        congr 2; ring

end

end SuperdiffusionCLT.Section7
