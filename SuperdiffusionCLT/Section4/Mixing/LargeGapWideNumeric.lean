/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The `ν^{-4}L^2` numeric tail, unrestricted `m` (the `n ≤ L` case, any gap size)

`p.mixing.P.three.prime#large-gap-case`'s numeric step, generalized beyond
the comparable-scale
restriction `m ≤ 2L`: covers *every* `m` satisfying the guard
`K log(ν^{-1}L) ≤ m - L` (no upper bound on `m` relative to `L`).

The key fact absent from the comparable-scale proof: `ν^{-4}L^2` itself
*decays* as the gap `x := m - L` grows, because the gap hypothesis bounds
`ν^{-1}L` (not `ν^{-1}` alone) by `exp(x/K)`, so `ν^{-4}L^2 = (ν^{-1}L)^4 /
L^2 ≤ exp(4x/K) / L^2 ≤ exp(4x/K)` (using `L ≥ 1`) — the `L^2` factor never
needs a separate polynomial bound. What remains is `exp(-cx) ≤ C m^{-3000}`
for `c := (d/2)log3 - 4/K > 0`, proved by a case split on `L ≤ x` versus
`L > x` (i.e. `x ≥ m/2` versus `L > m/2`):

* `L ≤ x`: `m = L + x ≤ 2x`, so `m^{3000} ≤ (2x)^{3000}`, bounded by
  `exp(cx)` via the elementary fact `y^k ≤ k^k exp(y)` (`mixGap_pow_le_pow_mul_exp`).
* `L > x`: `x ≥ K log(ν^{-1}L) ≥ K log L > K log(m/2)` (using `ν ≤ 1`), so
  `exp(cx) ≥ (m/2)^{cK} \gg m^{3000}` once `cK ≥ 3000` (using the base `m`,
  not `m/2`, for the exponent-monotonicity step, since `m ≥ 1` always but
  `m/2` need not be).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

/-- **The elementary bound `y^k ≤ k^k · exp y`, for `y ≥ 0`.** Proved from
`Real.add_one_le_exp` applied at `y/k` and raised to the `k`-th power — no
factorial-series machinery needed. -/
theorem mixGap_pow_le_pow_mul_exp {k : ℕ} {y : ℝ} (hy : 0 ≤ y) :
    y ^ k ≤ (k : ℝ) ^ k * Real.exp y := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · subst hk0
    simpa using Real.one_le_exp hy
  · have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
    set t : ℝ := y / (k : ℝ) with ht
    have ht_nonneg : (0 : ℝ) ≤ t := div_nonneg hy hk_pos.le
    have h0 : t + 1 ≤ Real.exp t := Real.add_one_le_exp t
    have h1 : (1 : ℝ) + t ≤ Real.exp t := by linarith only [h0]
    have h1nonneg : (0 : ℝ) ≤ 1 + t := by linarith only [ht_nonneg]
    have h2 : t ^ k ≤ (1 + t) ^ k := pow_le_pow_left₀ ht_nonneg (by linarith only [ht_nonneg]) k
    have h3 : (1 + t) ^ k ≤ (Real.exp t) ^ k := pow_le_pow_left₀ h1nonneg h1 k
    have h4 : (Real.exp t) ^ k = Real.exp y := by
      rw [← Real.exp_nat_mul]
      congr 1
      rw [ht]
      field_simp
    have hchain : t ^ k ≤ Real.exp y := h2.trans (h3.trans_eq h4)
    have h5 : t ^ k = y ^ k / (k : ℝ) ^ k := by rw [ht, div_pow]
    have hkpow_pos : (0 : ℝ) < (k : ℝ) ^ k := by positivity
    rw [h5] at hchain
    calc y ^ k = (y ^ k / (k : ℝ) ^ k) * (k : ℝ) ^ k := by field_simp
      _ ≤ Real.exp y * (k : ℝ) ^ k := mul_le_mul_of_nonneg_right hchain hkpow_pos.le
      _ = (k : ℝ) ^ k * Real.exp y := by ring

/-- **`x^k * exp(-(c·x)) ≤ (k/c)^k`, for `x ≥ 0`, `c > 0`.** -/
theorem mixGap_pow_mul_exp_neg_le (k : ℕ) {c x : ℝ} (hc : 0 < c) (hx : 0 ≤ x) :
    x ^ k * Real.exp (-(c * x)) ≤ ((k : ℝ) / c) ^ k := by
  have hy : (0 : ℝ) ≤ c * x := mul_nonneg hc.le hx
  have hb := mixGap_pow_le_pow_mul_exp (k := k) hy
  rw [mul_pow] at hb
  have hckpos : (0 : ℝ) < c ^ k := by positivity
  have hexppos : (0 : ℝ) < Real.exp (c * x) := Real.exp_pos _
  have hkdiv_eq : ((k : ℝ) / c) ^ k = (k : ℝ) ^ k / c ^ k := div_pow _ _ _
  rw [hkdiv_eq, Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ hexppos hckpos]
  nlinarith only [hb]

end SuperdiffusionCLT.Section4.Mixing
