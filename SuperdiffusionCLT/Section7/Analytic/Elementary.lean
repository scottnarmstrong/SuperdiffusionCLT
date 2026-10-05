/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Filter.Finite
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum

/-!
# Elementary real analysis used in Section 7

This file contains the finite-range excess iteration of the `C^{0,1}` proof: from
`E_{k-k₀} ≤ ½ E_{k+1} + a_k + b_k ∑_{j=k}^m E_j` for `k ∈ [n,m]` with `∑ b_k ≤ 1/4`, the sum of
the excesses over `[n-k₀, m+1]` is at most four times the sum of the errors `a_k` plus the sum of
the uncontrolled top excesses `E_j`, `j ∈ [m-k₀+1, m+1]`. Also the reusable pattern for the
enlargement of the deterministic threshold `L̂` (`∃ L̂₀, ∀ L̂ ≥ L̂₀`), which may always be
enlarged: thresholds combine by maximum, and a statement `∀ m ≥ L̂, R m` is monotone in `L̂`.

## Main results

* `SuperdiffusionCLT.Section7.excess_iteration_sum`
* `SuperdiffusionCLT.Section7.exists_forall_ge_and`
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Finset

private theorem a23_sum_shift (E : ℤ → ℝ) (c n m : ℤ) :
    ∑ k ∈ Icc n m, E (k - c) = ∑ j ∈ Icc (n - c) (m - c), E j := by
  refine Finset.sum_nbij' (fun k => k - c) (fun j => j + c) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj ⊢
    omega
  · intro k _
    simp
  · intro j _
    simp
  · intro k _
    rfl

private theorem a23_sum_mono (E : ℤ → ℝ) (hE : ∀ j, 0 ≤ E j) {s t : Finset ℤ} (h : s ⊆ t) :
    ∑ j ∈ s, E j ≤ ∑ j ∈ t, E j :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun j _ _ => hE j

/-- **Excess iteration (sum form).** Let `E, a, b ≥ 0` satisfy
`E_{k-k₀} ≤ ½ E_{k+1} + a_k + b_k ∑_{j=k}^m E_j` for `n ≤ k ≤ m` and `∑_{k=n}^m b_k ≤ 1/4`.
Then `∑_{j=n-k₀}^{m+1} E_j ≤ 4 (∑_{k=n}^m a_k + ∑_{j=m-k₀+1}^{m+1} E_j)`. -/
theorem excess_iteration_sum (k₀ : ℕ) (n m : ℤ) (hnm : n ≤ m) (E a b : ℤ → ℝ)
    (hE : ∀ j, 0 ≤ E j) (hb : ∀ k, 0 ≤ b k)
    (hit : ∀ k ∈ Icc n m,
      E (k - k₀) ≤ 1 / 2 * E (k + 1) + a k + b k * ∑ j ∈ Icc k m, E j)
    (hsmall : ∑ k ∈ Icc n m, b k ≤ 1 / 4) :
    ∑ j ∈ Icc (n - k₀) (m + 1), E j ≤
      4 * (∑ k ∈ Icc n m, a k + ∑ j ∈ Icc (m - k₀ + 1) (m + 1), E j) := by
  set S : ℝ := ∑ j ∈ Icc (n - k₀) (m + 1), E j with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => hE j
  have hsum := Finset.sum_le_sum hit
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, a23_sum_shift E k₀ n m]
    at hsum
  have h1 : ∑ k ∈ Icc n m, E (k + 1) ≤ S := by
    have e : ∑ k ∈ Icc n m, E (k + 1) = ∑ j ∈ Icc (n + 1) (m + 1), E j := by
      have := a23_sum_shift E (-1) n m
      simpa [sub_neg_eq_add] using this
    rw [e]
    refine a23_sum_mono E hE fun j hj => ?_
    simp only [Finset.mem_Icc] at hj ⊢
    omega
  have h2 : ∑ k ∈ Icc n m, b k * ∑ j ∈ Icc k m, E j ≤ (∑ k ∈ Icc n m, b k) * S := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun k hk => ?_
    refine mul_le_mul_of_nonneg_left (a23_sum_mono E hE fun j hj => ?_) (hb k)
    simp only [Finset.mem_Icc] at hj hk ⊢
    omega
  have h3 : (∑ k ∈ Icc n m, b k) * S ≤ 1 / 4 * S :=
    mul_le_mul_of_nonneg_right hsmall hS0
  have hsplit : S = ∑ j ∈ Icc (n - k₀) (m - k₀), E j + ∑ j ∈ Icc (m - k₀ + 1) (m + 1), E j := by
    rw [hS, ← Finset.sum_union]
    · congr 1
      ext j
      simp only [Finset.mem_Icc, Finset.mem_union]
      omega
    · rw [Finset.disjoint_left]
      intro j hj hj'
      simp only [Finset.mem_Icc] at hj hj'
      omega
  linarith only [hsum, h1, h2, h3, hsplit, hS0]

/-- Witness (all hypotheses met, non-trivially): `k₀ = 1`, `n = 0`, `m = 2`, `E ≡ 1`,
`a_k = 1/2`, `b_k = 1/12`. The inequality `1 ≤ 1/2 + 1/2 + (1/12) * (m-k+1)` holds, the
smallness `∑ b = 1/4` is tight, and the conclusion reads `5 ≤ 4 * (3/2 + 2)`. -/
example : ∑ j ∈ Icc ((0 : ℤ) - (1 : ℕ)) (2 + 1), (fun _ : ℤ => (1 : ℝ)) j ≤
    4 * (∑ k ∈ Icc (0 : ℤ) 2, (fun _ : ℤ => (1 / 2 : ℝ)) k +
      ∑ j ∈ Icc ((2 : ℤ) - (1 : ℕ) + 1) (2 + 1), (fun _ : ℤ => (1 : ℝ)) j) := by
  refine excess_iteration_sum 1 0 2 (by norm_num) (fun _ => 1) (fun _ => 1 / 2)
    (fun _ => 1 / 12) (fun _ => zero_le_one) (fun _ => by norm_num) ?_ ?_
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    have hk' : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk' with rfl | rfl | rfl <;> simp <;> norm_num
  · simp
    norm_num

/-! ### Enlargement of the deterministic threshold -/

/-- Two thresholds combine: if `A` holds above `L₁` and `B` above `L₂`, both hold above `L₀`. -/
theorem exists_forall_ge_and {A B : ℝ → Prop} (hA : ∃ L₁, ∀ L, L₁ ≤ L → A L)
    (hB : ∃ L₂, ∀ L, L₂ ≤ L → B L) : ∃ L₀, ∀ L, L₀ ≤ L → A L ∧ B L := by
  obtain ⟨L₁, h1⟩ := hA
  obtain ⟨L₂, h2⟩ := hB
  exact ⟨max L₁ L₂, fun L hL => ⟨h1 L (le_trans (le_max_left _ _) hL),
    h2 L (le_trans (le_max_right _ _) hL)⟩⟩

/-- Witness: thresholds `3` and `5` for `L ≤ ·` and `L ≥ ·` style statements combine at `5`. -/
example : ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → 3 ≤ L ∧ 5 ≤ L :=
  exists_forall_ge_and (A := fun L => 3 ≤ L) (B := fun L => 5 ≤ L) ⟨3, fun _ h => h⟩
    ⟨5, fun _ h => h⟩

end SuperdiffusionCLT.Section7
