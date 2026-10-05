/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Choice of triadic scales for the cube-to-ball passage

Real-number part of the passage from the cube estimate to Euclidean balls in the proof of the
large-scale Hölder theorem (the paragraph beginning
"We pass from cubes to balls"): the integers `n`, `m` with `2 r ≤ 3^n < 6 r`
(so that `B_r ⊆ □_n`) and `3^m ≤ 2R/√d < 3^{m+1}` (so that `□_m ⊆ B_R`), and the conversion of
the decay `3^{-γ(m-n)}` into `(r/R)^γ`.

## Main results

* `SuperdiffusionCLT.Section7.h1_exists_outer`
* `SuperdiffusionCLT.Section7.h1_exists_inner`
* `SuperdiffusionCLT.Section7.h1_rate`
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

/-- An integer `n` with `2 r ≤ 3^n < 6 r`, for `r ≥ 1/2`. -/
theorem h1_exists_outer {r : ℝ} (hr : 1 / 2 ≤ r) :
    ∃ n : ℕ, 2 * r ≤ (3 : ℝ) ^ n ∧ (3 : ℝ) ^ n < 6 * r := by
  have hex : ∃ n : ℕ, 2 * r ≤ (3 : ℝ) ^ n := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 * r) (by norm_num : (1 : ℝ) < 3)
    exact ⟨n, hn.le⟩
  classical
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0]; linarith only [hr]
  · have := Nat.find_min hex (Nat.sub_lt hpos one_pos)
    push Not at this
    have e : (3 : ℝ) ^ Nat.find hex = 3 * (3 : ℝ) ^ (Nat.find hex - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [e]; linarith only [this]

/-- An integer `m` with `3^m ≤ s < 3^{m+1}`, for `s ≥ 1`. -/
theorem h1_exists_inner {s : ℝ} (hs : 1 ≤ s) :
    ∃ m : ℕ, (3 : ℝ) ^ m ≤ s ∧ s < (3 : ℝ) ^ (m + 1) := by
  have hex : ∃ n : ℕ, s < (3 : ℝ) ^ n := pow_unbounded_of_one_lt s (by norm_num : (1 : ℝ) < 3)
  classical
  have hpos : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | h
    · have := Nat.find_spec hex
      rw [h0] at this; simp only [pow_zero] at this; linarith only [this, hs]
    · exact h
  refine ⟨Nat.find hex - 1, ?_, ?_⟩
  · have := Nat.find_min hex (Nat.sub_lt hpos one_pos)
    push Not at this; exact this
  · have e : Nat.find hex - 1 + 1 = Nat.find hex := by omega
    rw [e]; exact Nat.find_spec hex

/-- Conversion of the geometric decay: if `3^n / 3^m ≤ κ (r/R)` then
`3^{-γ(m-n)} ≤ κ^γ (r/R)^γ`. -/
theorem h1_rate {γ κ r R : ℝ} (hγ : 0 ≤ γ) (hκ : 0 ≤ κ) (hr : 0 ≤ r) (hR : 0 < R) (n m : ℤ)
    (h : (3 : ℝ) ^ n / (3 : ℝ) ^ m ≤ κ * (r / R)) :
    (3 : ℝ) ^ (-γ * ((m - n : ℤ) : ℝ)) ≤ κ ^ γ * (r / R) ^ γ := by
  have e : (3 : ℝ) ^ (-γ * ((m - n : ℤ) : ℝ)) = ((3 : ℝ) ^ n / (3 : ℝ) ^ m) ^ γ := by
    have : (3 : ℝ) ^ n / (3 : ℝ) ^ m = (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) := by
      rw [← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_sub (by norm_num)]
      congr 1; push_cast; ring
    rw [this, ← Real.rpow_mul (by norm_num)]
    congr 1; ring
  rw [e, ← Real.mul_rpow hκ (by positivity)]
  exact Real.rpow_le_rpow (by positivity) h hγ

/-- Satisfiability of `h1_rate`'s hypothesis: `n = 0`, `m = 1`, `κ = 1`, `r/R = 1/3`. -/
example : (3 : ℝ) ^ (0 : ℤ) / (3 : ℝ) ^ (1 : ℤ) ≤ 1 * (1 / 3 : ℝ) := by norm_num

end SuperdiffusionCLT.Section7
