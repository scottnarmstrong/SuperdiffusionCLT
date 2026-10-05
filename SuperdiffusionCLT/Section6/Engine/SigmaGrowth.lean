/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Prereq.SigmaBarWindow
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Growth of `σ̄` across scales

Chaining the logarithmic-window comparison of `σ̄` down from `m` to `k` in steps of a fixed
length `s ≥ 1/κ` gives `σ̄_k ≤ 2 · 9^{κ(m-k)} σ̄_m` for `k` large.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6

/-- Chaining a one-step doubling bound over steps of length at most `s`. -/
private theorem ec3_chain (S : ℕ → ℝ) (s L0 : ℕ) (hs : 1 ≤ s) (hpos : ∀ k, L0 ≤ k → 0 < S k)
    (hstep : ∀ k n, L0 ≤ k → 1 ≤ n → n ≤ s → S k ≤ 2 * S (k + n)) :
    ∀ n k : ℕ, L0 ≤ k → S k ≤ (2 : ℝ) ^ ((n : ℝ) / s + 1) * S (k + n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k hk
    have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
    have hSk := hpos k hk
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.cast_zero, zero_div, zero_add, Real.rpow_one, add_zero]
      linarith only [hSk]
    rcases le_or_gt n s with hns | hns
    · have hSn := hpos (k + n) (le_trans hk (Nat.le_add_right _ _))
      have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / s + 1) := by
        calc (2 : ℝ) = 2 ^ (1 : ℝ) := (Real.rpow_one 2).symm
          _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
              have : (0 : ℝ) ≤ (n : ℝ) / s := by positivity
              linarith only [this])
      calc S k ≤ 2 * S (k + n) := hstep k n hk hn hns
        _ ≤ _ := mul_le_mul_of_nonneg_right h2 hSn.le
    · have hk' : L0 ≤ k + s := le_trans hk (Nat.le_add_right _ _)
      have := ih (n - s) (by omega) (k + s) hk'
      have hkn : k + s + (n - s) = k + n := by omega
      rw [hkn] at this
      have hcast : ((n - s : ℕ) : ℝ) = (n : ℝ) - s := by
        rw [Nat.cast_sub hns.le]
      rw [hcast] at this
      have hexp : (2 : ℝ) * (2 : ℝ) ^ (((n : ℝ) - s) / s + 1) = (2 : ℝ) ^ ((n : ℝ) / s + 1) := by
        have : ((n : ℝ) - s) / s + 1 = (n : ℝ) / s := by field_simp; ring
        rw [this, show (n : ℝ) / s + 1 = (n : ℝ) / s + 1 from rfl, Real.rpow_add (by norm_num),
          Real.rpow_one]
        ring
      calc S k ≤ 2 * S (k + s) := hstep k s hk hs le_rfl
        _ ≤ 2 * ((2 : ℝ) ^ (((n : ℝ) - s) / s + 1) * S (k + n)) := by
            exact mul_le_mul_of_nonneg_left this (by norm_num)
        _ = _ := by rw [← mul_assoc, hexp]

/-- **Growth of `σ̄` across scales**, from the logarithmic-window comparison. -/
theorem eng_sigma_growth (d : ℕ) [NeZero d] (hd : 2 ≤ d) (nu cStar K κ : ℝ) (hnu : 0 < nu)
    (hnu1 : nu ≤ 1) (hcStar : 0 < cStar) (hκ : 0 < κ) :
    ∃ L0 : ℕ,
      ∀ (P : MeasureTheory.ProbabilityMeasure
            (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
        (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
        (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
        (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
        ∀ k m : ℕ, L0 ≤ k → k ≤ m →
          0 < SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P ∧
            SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu (m + 1) P ≤
              2 * SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P ∧
            SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu k P ≤
              2 * (9 : ℝ) ^ (κ * ((m : ℝ) - (k : ℝ))) *
                SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P := by
  obtain ⟨Lw, hLw⟩ := sigmaBar_log_window_comparable d hd nu cStar K 1 hnu hnu1 hcStar
  set s : ℕ := ⌈1 / κ⌉₊ with hsdef
  have hs1 : 1 ≤ s := Nat.one_le_iff_ne_zero.2 (fun h => by
    have := Nat.ceil_pos.2 (show 0 < 1 / κ by positivity)
    omega)
  have hsκ : 1 / κ ≤ (s : ℝ) := Nat.le_ceil _
  refine ⟨max Lw (max 3 ⌈Real.exp s⌉₊), ?_⟩
  intro P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 k m hk hkm
  have hLw' : Lw ≤ k := le_trans (le_max_left _ _) hk
  have h3 : 3 ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hexp : Real.exp s ≤ (k : ℝ) :=
    le_trans (Nat.le_ceil _) (Nat.cast_le.2 (le_trans (le_trans (le_max_right _ _)
      (le_max_right _ _)) hk))
  have hsl : (s : ℝ) ≤ Real.log (k : ℝ) :=
    (Real.le_log_iff_exp_le (by exact_mod_cast (by omega : 0 < k))).2 hexp
  have hwin : ∀ a n : ℕ, k ≤ a → n ≤ s →
      0 < SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu a P ∧
      (1 / 2 : ℝ) * SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu a P ≤
        SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu (a + n) P ∧
      SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu (a + n) P ≤
        (3 / 2 : ℝ) * SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu a P := by
    intro a n ha hn
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hlog : Real.log (k : ℝ) ≤ Real.log ((a + n : ℕ) : ℝ) :=
      Real.log_le_log hk0 (by exact_mod_cast le_trans ha (Nat.le_add_right _ _))
    exact hLw P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 (a + n) a (Nat.le_add_right _ _)
      (le_trans hLw' ha) (by
        push_cast at hlog ⊢
        have : (n : ℝ) ≤ s := by exact_mod_cast hn
        linarith only [this, hsl, hlog])
  have hpos : ∀ a, k ≤ a → 0 <
      SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu a P :=
    fun a ha => (hwin a 0 ha (Nat.zero_le _)).1
  have hchain := ec3_chain
    (fun a => SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu a P) s k hs1 hpos
    (fun a n ha hn1 hns => by
      have := (hwin a n ha hns).2.1
      linarith only [this])
  have hm := hpos m hkm
  refine ⟨hm, ?_, ?_⟩
  · have := (hwin m 1 hkm hs1).2.2
    linarith only [this, hm]
  · have h := hchain (m - k) k le_rfl
    have hkm' : k + (m - k) = m := by omega
    rw [hkm'] at h
    have hs0 : (0 : ℝ) < s := by exact_mod_cast hs1
    have hn : ((m - k : ℕ) : ℝ) = (m : ℝ) - k := by rw [Nat.cast_sub hkm]
    rw [hn] at h
    have hκs : 1 / (s : ℝ) ≤ κ := by
      rw [div_le_iff₀ hs0]
      rw [div_le_iff₀ hκ] at hsκ
      linarith only [hsκ]
    have hnn : (0 : ℝ) ≤ (m : ℝ) - k := by
      have : (k : ℝ) ≤ m := by exact_mod_cast hkm
      linarith only [this]
    have hexp2 : (2 : ℝ) ^ (((m : ℝ) - k) / s + 1) ≤ 2 * (9 : ℝ) ^ (κ * ((m : ℝ) - k)) := by
      rw [Real.rpow_add (by norm_num), Real.rpow_one, mul_comm]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      calc (2 : ℝ) ^ (((m : ℝ) - k) / s) ≤ 9 ^ (((m : ℝ) - k) / s) :=
            Real.rpow_le_rpow (by norm_num) (by norm_num) (by positivity)
        _ ≤ 9 ^ (κ * ((m : ℝ) - k)) := by
            apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
            rw [div_eq_mul_inv, ← one_div, mul_comm]
            exact mul_le_mul_of_nonneg_right hκs hnn
    calc _ ≤ _ := h
      _ ≤ _ := mul_le_mul_of_nonneg_right hexp2 hm.le

/-- Parameter witness: `d = 2`, `ν = 1`, `c⋆ = 1`, `κ = 1`. -/
example : (2 : ℕ) ≤ 2 ∧ (0 : ℝ) < 1 ∧ (1 : ℝ) ≤ 1 ∧ (0 : ℝ) < 1 ∧ (0 : ℝ) < 1 := by
  norm_num

end SuperdiffusionCLT.Section6
