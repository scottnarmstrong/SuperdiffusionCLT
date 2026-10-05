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
# Block iteration for the large-scale Hölder estimate

Deterministic iteration in the proof of the large-scale Hölder theorem (the cube estimate
`e.Dir.new.large.scale.Holder.cube`).  Real sequences `E` (the `L^∞`
oscillation at scale `n`), `D` (the normalized `L²` oscillation) and `F` (the source term) satisfy
the one-step estimate `E n ≤ C 3^{-(m-n)} (D m + F m)` over blocks of length at most `N`.  Then
`E n ≤ C' 3^{-γ(m-n)} (D m + K G)` for all `n < m` in the range.

## Main results

* `SuperdiffusionCLT.Section7.h1_iteration`
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

/-- Iteration over whole blocks: `E (m - j N) ≤ ρ^j (D m + K G)` for `j ≥ 1`. -/
theorem h1_blocks (E D F : ℤ → ℝ) (C γ K G : ℝ) (N : ℕ) (m₀ M m : ℤ) (hN : 1 ≤ N)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hG : 0 ≤ G) (hD0 : 0 ≤ D m) (hm : m ≤ M)
    (hq : C * (3 : ℝ) ^ (-(N : ℤ)) ≤ 1 / 2 * (3 : ℝ) ^ (-γ * (N : ℝ)))
    (hstep : ∀ n k : ℤ, m₀ ≤ n → n < k → k ≤ M → k - n ≤ N →
      E n ≤ C * (3 : ℝ) ^ (-(k - n)) * (D k + F k))
    (hDE : ∀ k, m₀ ≤ k → k ≤ M → D k ≤ E k)
    (hF : ∀ k, m₀ ≤ k → k ≤ m → F k ≤ K * (3 : ℝ) ^ (-γ * ((m - k : ℤ) : ℝ)) * G) :
    ∀ j : ℕ, 1 ≤ j → m₀ ≤ m - j * N →
      E (m - j * N) ≤ ((3 : ℝ) ^ (-γ * (N : ℝ))) ^ j * (D m + K * G) := by
  set ρ : ℝ := (3 : ℝ) ^ (-γ * (N : ℝ)) with hρ
  have hρpos : 0 < ρ := by positivity
  have hpow : ∀ j : ℕ, (3 : ℝ) ^ (-γ * (((m - (m - j * N) : ℤ)) : ℝ)) = ρ ^ j := by
    intro j
    rw [hρ, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    push_cast
    ring
  have hstepj : ∀ j : ℕ, 1 ≤ j → m₀ ≤ m - (j + 1) * N →
      E (m - (j + 1) * N) ≤ C * (3 : ℝ) ^ (-(N : ℤ)) * (E (m - j * N) + F (m - j * N)) := by
    intro j hj h0
    have hNpos : (1 : ℤ) ≤ N := by exact_mod_cast hN
    have hjN : (0 : ℤ) ≤ j * N := by positivity
    have := hstep (m - (j + 1 : ℕ) * N) (m - j * N) (by push_cast; exact h0) (by push_cast; linarith only [hNpos])
      (by linarith only [hjN, hm]) (by push_cast; linarith only)
    have e : (m - (j : ℤ) * N) - (m - ((j + 1 : ℕ) : ℤ) * N) = N := by push_cast; ring
    rw [e] at this
    refine this.trans ?_
    have hle : D (m - j * N) ≤ E (m - j * N) := hDE _ (by nlinarith only [h0, hNpos, hjN]) (by linarith only [hjN, hm])
    have : 0 ≤ C * (3 : ℝ) ^ (-(N : ℤ)) := by positivity
    nlinarith only [hle, this]
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    intro h0
    have hNpos : (1 : ℤ) ≤ N := by exact_mod_cast hN
    have := hstep (m - (1 : ℕ) * N) m (by simpa using h0) (by push_cast; linarith only [hNpos])
      hm (by push_cast; linarith only)
    have e : m - (m - ((1 : ℕ) : ℤ) * N) = N := by push_cast; ring
    rw [e] at this
    refine this.trans ?_
    have hF0 := hF m (by push_cast at h0; linarith only [h0, hNpos]) le_rfl
    simp only [sub_self, Int.cast_zero, mul_zero, Real.rpow_zero, mul_one] at hF0
    have hKG : 0 ≤ K * G := by positivity
    have h2 : C * (3 : ℝ) ^ (-(N : ℤ)) * (D m + F m) ≤ 1 / 2 * ρ * (D m + K * G) := by
      refine (mul_le_mul_of_nonneg_right hq (by linarith only [hD0, hKG, hF0, hKG])).trans' ?_
      refine mul_le_mul_of_nonneg_left (by linarith only [hF0]) (by positivity)
    have : ρ * (D m + K * G) ≥ 1 / 2 * ρ * (D m + K * G) := by
      nlinarith only [hρpos, hD0, hKG]
    simpa using h2.trans this
  | succ j hj ih =>
    intro h0
    have hNpos : (1 : ℤ) ≤ N := by exact_mod_cast hN
    have hjN : (0 : ℤ) ≤ j * N := by positivity
    have h0' : m₀ ≤ m - j * N := by push_cast at h0; linarith only [h0, hNpos]
    have ihj := ih h0'
    have hFj := hF (m - j * N) h0' (by linarith only [hjN])
    rw [hpow j] at hFj
    have hs := hstepj j hj h0
    have hKG : 0 ≤ K * G := by positivity
    have hρj : 0 < ρ ^ j := by positivity
    have hFj' : F (m - j * N) ≤ ρ ^ j * (K * G) := by linarith only [hFj, mul_comm K (ρ ^ j), mul_assoc (ρ ^ j) K G]
    have hsum : E (m - j * N) + F (m - j * N) ≤ ρ ^ j * (D m + K * G) + ρ ^ j * (K * G) := by
      linarith only [ihj, hFj']
    have hqq : 0 ≤ C * (3 : ℝ) ^ (-(N : ℤ)) := by positivity
    have h3 : C * (3 : ℝ) ^ (-(N : ℤ)) * (E (m - j * N) + F (m - j * N))
        ≤ 1 / 2 * ρ * (ρ ^ j * (D m + K * G) + ρ ^ j * (K * G)) := by
      calc _ ≤ C * (3 : ℝ) ^ (-(N : ℤ)) * (ρ ^ j * (D m + K * G) + ρ ^ j * (K * G)) :=
            mul_le_mul_of_nonneg_left hsum hqq
        _ ≤ _ := mul_le_mul_of_nonneg_right hq (by positivity)
    have h4 : 1 / 2 * ρ * (ρ ^ j * (D m + K * G) + ρ ^ j * (K * G)) ≤ ρ ^ (j + 1) * (D m + K * G) := by
      rw [pow_succ]
      have : 0 ≤ ρ ^ j * ρ := by positivity
      nlinarith only [this, hD0, hKG]
    exact hs.trans (h3.trans h4)

end SuperdiffusionCLT.Section7
