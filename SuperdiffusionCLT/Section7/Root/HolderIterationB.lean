/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Root.HolderIteration

/-!
# Block iteration, all scales

The conclusion of the cube estimate of the large-scale Hölder theorem
(`e.Dir.new.large.scale.Holder.cube`), deterministic part:
the one-step estimate over blocks of length at most `N`, with `C 3^{-N} ≤ ½ 3^{-γN}`, gives the
geometric decay `3^{-γ(m-n)}` over any number of blocks (`n < m`; the case `n = m` is not
controlled by the `L²` quantity).

## Main results

* `SuperdiffusionCLT.Section7.h1_iteration`
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

theorem h1_remainder (E D F : ℤ → ℝ) (C γ K G : ℝ) (N : ℕ) (m₀ M m n : ℤ) (hN : 1 ≤ N)
    (hC : 1 ≤ C) (hγ : 0 ≤ γ) (hK : 0 ≤ K) (hG : 0 ≤ G) (hD0' : ∀ k, 0 ≤ D k) (hF0 : ∀ k, 0 ≤ F k) (hm : m ≤ M)
    (hq : C * (3 : ℝ) ^ (-(N : ℤ)) ≤ 1 / 2 * (3 : ℝ) ^ (-γ * (N : ℝ)))
    (hstep : ∀ n k : ℤ, m₀ ≤ n → n < k → k ≤ M → k - n ≤ N →
      E n ≤ C * (3 : ℝ) ^ (-(k - n)) * (D k + F k))
    (hDE : ∀ k, m₀ ≤ k → k ≤ M → D k ≤ E k)
    (hF : ∀ k, m₀ ≤ k → k ≤ m → F k ≤ K * (3 : ℝ) ^ (-γ * ((m - k : ℤ) : ℝ)) * G)
    (hmn : n < m) (hn : m₀ ≤ n) (hbig : (N : ℤ) < m - n) :
    E n ≤ 2 * C * (3 : ℝ) ^ (γ * (N : ℝ)) * (3 : ℝ) ^ (-γ * ((m - n : ℤ) : ℝ)) *
      (D m + K * G) := by
  set ρ : ℝ := (3 : ℝ) ^ (-γ * (N : ℝ)) with hρ
  have hρpos : 0 < ρ := by positivity
  have hNpos : (1 : ℤ) ≤ N := by exact_mod_cast hN
  obtain ⟨t, ht⟩ : ∃ t : ℕ, (t : ℤ) = m - n := ⟨(m - n).toNat, by omega⟩
  set j : ℕ := t / N with hj
  set s : ℕ := t % N with hs
  have hdiv : (j : ℤ) * N + s = m - n := by
    rw [← ht]; exact_mod_cast Nat.div_add_mod' t N
  have hsN : (s : ℤ) < N := by exact_mod_cast Nat.mod_lt t (by omega)
  have hj1 : 1 ≤ j := by
    rw [hj]; exact (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  have hj1' : (1 : ℤ) ≤ j := by exact_mod_cast hj1
  have hjN : (0 : ℤ) ≤ j * N := by positivity
  have hs0 : (0 : ℤ) ≤ s := by positivity
  set n' : ℤ := m - j * N with hn'
  have hn'n : n = n' - s := by omega
  have hn'0 : m₀ ≤ n' := by omega
  have hD0 : 0 ≤ D m := hD0' m
  have hblocks := h1_blocks E D F C γ K G N m₀ M m hN (by linarith only [hC]) hK hG hD0 hm hq hstep hDE
    hF j hj1 hn'0
  have hFp : F n' ≤ ρ ^ j * (K * G) := by
    have := hF n' hn'0 (by omega)
    have e : (3 : ℝ) ^ (-γ * (((m - n' : ℤ)) : ℝ)) = ρ ^ j := by
      rw [hρ, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      congr 1
      rw [hn']; push_cast; ring
    rw [e] at this
    linarith only [this, mul_comm K (ρ ^ j), mul_assoc (ρ ^ j) K G]
  have hKG : 0 ≤ K * G := by positivity
  have hX : 0 ≤ D m + K * G := by linarith only [hD0, hKG]
  have hρj : 0 < ρ ^ j := by positivity
  have hmain : E n ≤ 2 * C * (ρ ^ j * (D m + K * G)) := by
    have hb : E n' ≤ ρ ^ j * (D m + K * G) := hblocks
    have hge : ρ ^ j * (D m + K * G) ≤ 2 * C * (ρ ^ j * (D m + K * G)) := by
      have : 0 ≤ ρ ^ j * (D m + K * G) := by positivity
      nlinarith only [this, hC]
    rcases Nat.eq_zero_or_pos s with h0 | hpos
    · have : n = n' := by rw [hn'n, h0]; simp
      rw [this]; exact hb.trans hge
    · have h1 := hstep n n' hn (by omega) (by omega) (by omega)
      have e3 : (3 : ℝ) ^ (-(n' - n)) ≤ 1 := by
        apply zpow_le_one_of_nonpos₀ (by norm_num); omega
      have hDn := hDE n' hn'0 (by omega)
      have hCn : 0 ≤ C := by linarith only [hC]
      have h2 : E n ≤ C * (E n' + F n') := by
        calc E n ≤ C * (3 : ℝ) ^ (-(n' - n)) * (D n' + F n') := h1
          _ ≤ C * 1 * (D n' + F n') := by
              refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e3 hCn) ?_
              exact add_nonneg (hD0' n') (hF0 n')
          _ ≤ _ := by nlinarith only [hDn, hCn]
      have : C * (E n' + F n') ≤ C * (ρ ^ j * (D m + K * G) + ρ ^ j * (K * G)) :=
        mul_le_mul_of_nonneg_left (by linarith only [hb, hFp]) hCn
      have : C * (ρ ^ j * (D m + K * G) + ρ ^ j * (K * G)) ≤ 2 * C * (ρ ^ j * (D m + K * G)) := by
        have : 0 ≤ C * (ρ ^ j * D m) := by positivity
        nlinarith only [this, hC, hρj, hD0, hKG]
      linarith only [h2, ‹C * (E n' + F n') ≤ _›, this]
  have hρ' : ρ ^ j ≤ (3 : ℝ) ^ (γ * (N : ℝ)) * (3 : ℝ) ^ (-γ * ((m - n : ℤ) : ℝ)) := by
    rw [hρ, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have : ((m - n : ℤ) : ℝ) ≤ ((j : ℝ) + 1) * N := by
      have e : ((j : ℤ) + 1) * N = j * N + N := by ring
      have : m - n ≤ ((j : ℤ) + 1) * N := by omega
      exact_mod_cast this
    nlinarith only [this, hγ]
  calc E n ≤ 2 * C * (ρ ^ j * (D m + K * G)) := hmain
    _ ≤ 2 * C * ((3 : ℝ) ^ (γ * (N : ℝ)) * (3 : ℝ) ^ (-γ * ((m - n : ℤ) : ℝ)) * (D m + K * G)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith only [hC])
        exact mul_le_mul_of_nonneg_right hρ' hX
    _ = _ := by ring

/-- **Block iteration.** If `E n ≤ C 3^{-(k-n)} (D k + F k)` whenever `m₀ ≤ n < k ≤ M`,
`k - n ≤ N`, if `D ≤ E`, `D, F ≥ 0`, `C 3^{-N} ≤ ½ 3^{-γN}`, and `F k ≤ K 3^{-γ(m-k)} G` for
`m₀ ≤ k ≤ m`, then `E n ≤ 2 C 3^{γN} 3^{-γ(m-n)} (D m + K G)` for `m₀ ≤ n < m ≤ M`. -/
theorem h1_iteration (E D F : ℤ → ℝ) (C γ K G : ℝ) (N : ℕ) (m₀ M m n : ℤ) (hN : 1 ≤ N)
    (hC : 1 ≤ C) (hγ : 0 ≤ γ) (hK : 0 ≤ K) (hG : 0 ≤ G) (hD0 : ∀ k, 0 ≤ D k)
    (hF0 : ∀ k, 0 ≤ F k) (hm : m ≤ M)
    (hq : C * (3 : ℝ) ^ (-(N : ℤ)) ≤ 1 / 2 * (3 : ℝ) ^ (-γ * (N : ℝ)))
    (hstep : ∀ n k : ℤ, m₀ ≤ n → n < k → k ≤ M → k - n ≤ N →
      E n ≤ C * (3 : ℝ) ^ (-(k - n)) * (D k + F k))
    (hDE : ∀ k, m₀ ≤ k → k ≤ M → D k ≤ E k)
    (hF : ∀ k, m₀ ≤ k → k ≤ m → F k ≤ K * (3 : ℝ) ^ (-γ * ((m - k : ℤ) : ℝ)) * G)
    (hmn : n < m) (hn : m₀ ≤ n) :
    E n ≤ 2 * C * (3 : ℝ) ^ (γ * (N : ℝ)) * (3 : ℝ) ^ (-γ * ((m - n : ℤ) : ℝ)) *
      (D m + K * G) := by
  by_cases hbig : (N : ℤ) < m - n
  · exact h1_remainder E D F C γ K G N m₀ M m n hN hC hγ hK hG hD0 hF0 hm hq hstep hDE hF hmn hn hbig
  · have h1 := hstep n m hn hmn hm (by omega)
    have e3 : (3 : ℝ) ^ (-(m - n)) ≤ 1 := by
      apply zpow_le_one_of_nonpos₀ (by norm_num); omega
    have hFm := hF m (by omega) le_rfl
    simp only [sub_self, Int.cast_zero, mul_zero, Real.rpow_zero, mul_one] at hFm
    have hX : 0 ≤ D m + F m := add_nonneg (hD0 m) (hF0 m)
    have hCn : 0 ≤ C := by linarith only [hC]
    have hKG : 0 ≤ K * G := by positivity
    have h2 : E n ≤ C * (D m + K * G) := by
      calc E n ≤ C * (3 : ℝ) ^ (-(m - n)) * (D m + F m) := h1
        _ ≤ C * 1 * (D m + F m) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e3 hCn) hX
        _ ≤ C * (D m + K * G) := by nlinarith only [hFm, hCn]
    have hge : 1 ≤ (3 : ℝ) ^ (γ * (N : ℝ)) * (3 : ℝ) ^ (-γ * ((m - n : ℤ) : ℝ)) := by
      rw [← Real.rpow_add (by norm_num)]
      apply Real.one_le_rpow (by norm_num)
      have : ((m - n : ℤ) : ℝ) ≤ N := by exact_mod_cast not_lt.1 hbig
      nlinarith only [this, hγ]
    have hY : 0 ≤ C * (D m + K * G) := by
      have := hD0 m
      positivity
    have : C * (D m + K * G) ≤ 2 * C * ((3 : ℝ) ^ (γ * (N : ℝ)) * (3 : ℝ) ^ (-γ * ((m - n : ℤ) : ℝ)))
        * (D m + K * G) := by
      have h0 : 0 ≤ D m + K * G := by have := hD0 m; positivity
      nlinarith only [hge, hCn, h0, mul_nonneg hCn h0]
    calc E n ≤ _ := h2
      _ ≤ _ := this
      _ = _ := by ring

/-- Satisfiability: the hypotheses of `h1_iteration` hold together (`C = 1`, `γ = 1/2`, `N = 2`). -/
example : (1 : ℝ) * (3 : ℝ) ^ (-((2 : ℕ) : ℤ)) ≤ 1 / 2 * (3 : ℝ) ^ (-(1 / 2 : ℝ) * ((2 : ℕ) : ℝ)) := by
  have : (3 : ℝ) ^ (-(1 / 2 : ℝ) * ((2 : ℕ) : ℝ)) = (3 : ℝ) ^ (-(1 : ℤ)) := by
    rw [← Real.rpow_intCast]; norm_num
  rw [this]
  norm_num

end SuperdiffusionCLT.Section7
