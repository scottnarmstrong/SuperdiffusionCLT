/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.MinimalScale.GridMaxCount

/-!
# Interior pointwise oscillation: the scale arithmetic

The bottom scale `nK N j = j - ⌈N log j⌉₊` is nondecreasing in `j` once `j ≥ N`; hence the scale
`k = min m (n + k₀ + 3)` of the iteration satisfies `nK N n ≤ nK N k`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

/-- One step: `nK N j ≤ nK N (j + 1)` for `N ≤ j`. -/
theorem ip_nK_succ {N : ℝ} (hN : 0 ≤ N) {j : ℕ} (hj : N ≤ (j : ℝ)) (hj1 : 1 ≤ j) :
    nK N j ≤ nK N (j + 1) := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
  have hlog : Real.log ((j : ℝ) + 1) ≤ Real.log (j : ℝ) + 1 / (j : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (x := ((j : ℝ) + 1) / (j : ℝ)) (by positivity)
    rw [Real.log_div (by positivity) hj0.ne'] at h
    have : ((j : ℝ) + 1) / (j : ℝ) - 1 = 1 / (j : ℝ) := by field_simp; ring
    linarith only [h, this]
  have hNj : N * (1 / (j : ℝ)) ≤ 1 := by
    rw [mul_one_div, div_le_one hj0]; exact hj
  have hl0 : 0 ≤ N * Real.log (j : ℝ) :=
    mul_nonneg hN (Real.log_nonneg (by exact_mod_cast hj1))
  have hc : ⌈N * Real.log (((j + 1 : ℕ)) : ℝ)⌉₊ ≤ ⌈N * Real.log (j : ℝ)⌉₊ + 1 := by
    rw [← Nat.ceil_add_one hl0]
    refine Nat.ceil_mono ?_
    push_cast
    have := mul_le_mul_of_nonneg_left hlog hN
    nlinarith only [this, hNj]
  unfold nK
  omega

/-- Monotonicity of the bottom scale. -/
theorem ip_nK_mono {N : ℝ} (hN : 0 ≤ N) {j k : ℕ} (hj : N ≤ (j : ℝ)) (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    nK N j ≤ nK N k := by
  induction k, hjk using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih =>
    refine ih.trans (ip_nK_succ hN ?_ (hj1.trans hk))
    exact hj.trans (by exact_mod_cast hk)

/-- Witness: the scale arithmetic applies (`N = 1`, `j = 3`). -/
example : nK 1 3 ≤ nK 1 5 := ip_nK_mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end SuperdiffusionCLT.Section7
