/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Thresholds.ThresholdChain
public import SuperdiffusionCLT.Section5.Thresholds.IterationTelescope
public import SuperdiffusionCLT.Section5.Thresholds.SequencePasses

/-!
# Reduction of `t.sstar.sharp.bounds` to `p.one.step.sharp`

For an abstract real sequence `s` (standing for `shom_·`) satisfying the bracket of
`e.theorem.shom.bracket` and the one-step recursion `e.approximate.recurrence`, the sharp asymptotics
hold from an index `M` that is chosen BEFORE `s`: it depends only on the constant `Cr` of the
recursion, on `c⋆, κ, A` and on the two thresholds `N₀` and M_prop.

Compared with the printed proof, no crude bound `shom_n ≤ E max(1,n)` is needed: the fixed
constants `B` and `C₀` of Steps 3 and 6 are absorbed through the upper bracket at the (explicit)
indices `N₂` and `N₅`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

theorem sharp_of_recurrence :
    ∀ Cr : ℝ, 1 ≤ Cr →
      ∃ Chat : ℝ, 1 ≤ Chat ∧
        ∀ (cStar K A : ℝ), 0 < cStar → cStar ≤ 2 → 0 ≤ K → 0 < A →
          ∀ N0 Mp : ℕ,
            ∃ M : ℕ,
              ∀ s : ℕ → ℝ,
                (∀ n : ℕ, N0 ≤ n →
                    A⁻¹ * (n : ℝ) ^ ((1 : ℝ) / 2) * Real.log (n : ℝ) ^ (-((9 : ℝ) / 2)) ≤ s n ∧
                    s n ≤ A * (n : ℝ) ^ ((1 : ℝ) / 2) * Real.log (n : ℝ) ^ ((9 : ℝ) / 2)) →
                (∀ n : ℕ, Mp ≤ n → ∀ h : ℕ, 1 ≤ h → (h : ℝ) ≤ s n →
                    |s (n + h) - s n - cStar * Real.log 3 * (s n)⁻¹ * (h : ℝ)| ≤
                      Cr * (Real.log (n : ℝ) ^ (2 : ℝ) + K) * (s n)⁻¹) →
                ∀ m : ℕ, M ≤ m →
                  |s m - (2 * cStar * Real.log 3 * (m : ℝ)) ^ ((1 : ℝ) / 2)| ≤
                    Chat * cStar⁻¹ * (Real.log (m : ℝ) ^ (2 : ℝ) + K) := by
  intro Cr hCr
  set C1 : ℝ := 9 + 8 * Cr + Cr ^ 2 with hC1def
  have hC1 : 0 ≤ C1 := by rw [hC1def]; nlinarith only [hCr]
  refine ⟨13 * C1 + 1, by linarith only [hC1], ?_⟩
  intro cStar K A hc hc2 hK hA N0 Mp
  have hl3 := Real.log_pos (show (1 : ℝ) < 3 by norm_num)
  have hc3 : 0 < cStar * Real.log 3 := by positivity
  obtain ⟨Nl, hNl3, hNl⟩ := threshold_bracket_lower A 2 K hA hK
  obtain ⟨Nu, hNu3, hNu⟩ := threshold_bracket_upper A
  set N1 : ℕ := max (max N0 Mp) (max Nl Nu) with hN1def
  have hN1_3 : 3 ≤ N1 := le_trans hNl3 (le_trans (le_max_left _ _) (le_max_right _ _))
  obtain ⟨N4, hN14, hcoarse⟩ :=
    coarse_lower_of_square_increment C1 cStar K A hC1 hc hK hA N1 hN1_3
  obtain ⟨hlam, hcondR⟩ := threshold_N5 hc hc2
  set N5 : ℕ := max N4 ⌈max 1 (max ((1 / 2 * (cStar * Real.log 3) ^ (1 / 2 : ℝ))⁻¹ ^ 2) cStar)⌉₊
    with hN5def
  have hN4_5 : N4 ≤ N5 := le_max_left _ _
  have hN5_3 : 3 ≤ N5 := le_trans hN1_3 (le_trans hN14 hN4_5)
  have hr0 : 0 < cStar ^ (-(1 / 2 : ℝ)) := by positivity
  obtain ⟨N6, -, hN6⟩ := threshold_const_absorbed
    ((A * (N5 : ℝ) ^ (1 / 2 : ℝ) * Real.log (N5 : ℝ) ^ (9 / 2 : ℝ)) ^ 2 +
      2 * (cStar * Real.log 3) * N5) (cStar ^ (-(1 / 2 : ℝ))) K hr0 hK
  refine ⟨max N5 N6, fun s hbr hrec m hm => ?_⟩
  have hN1_N0 : N0 ≤ N1 := le_trans (le_max_left _ _) (le_max_left _ _)
  have hN1_Mp : Mp ≤ N1 := le_trans (le_max_right _ _) (le_max_left _ _)
  have hN1_l : Nl ≤ N1 := le_trans (le_max_left _ _) (le_max_right _ _)
  have hN1_u : Nu ≤ N1 := le_trans (le_max_right _ _) (le_max_right _ _)
  -- bracket data on `[N1, ∞)`
  have hb1 : ∀ n : ℕ, N1 ≤ n → 2 ≤ s n ∧ s n ≤ n ∧
      s n ≤ A * (n : ℝ) ^ (1 / 2 : ℝ) * Real.log (n : ℝ) ^ (9 / 2 : ℝ) ∧
      A⁻¹ * (n : ℝ) ^ (1 / 2 : ℝ) * Real.log (n : ℝ) ^ (-(9 / 2 : ℝ)) ≤ s n ∧
      Real.log (n : ℝ) ^ 2 + K ≤ s n ^ 2 := by
    intro n hn
    have hbn := hbr n (le_trans hN1_N0 hn)
    have h1 := hNl n (le_trans hN1_l hn) (s n) hbn.1
    have h2 := hNu n (le_trans hN1_u hn) (s n) hbn.2
    exact ⟨by simpa using h1.1, h2, hbn.2, hbn.1, h1.2⟩
  have hsq : ∀ n : ℕ, N1 ≤ n → ∀ h : ℕ, (h : ℝ) ≤ s n →
      |s (n + h) ^ 2 - s n ^ 2 - 2 * (cStar * Real.log 3) * (h : ℝ)| ≤
        C1 * (Real.log (n : ℝ) ^ 2 + K) := by
    intro n hn h hh
    have hb := hb1 n hn
    refine sq_increment_step Cr cStar K (by linarith only [hCr]) hc hc2 hK s n h
      (le_trans hN1_3 hn) (by linarith only [hb.1]) hb.2.2.2.2 hh (fun h1 => ?_)
    have := hrec n (le_trans hN1_Mp hn) h h1 hh
    simpa only [Real.rpow_two] using this
  have hco : ∀ n : ℕ, N4 ≤ n → cStar * Real.log 3 * (n : ℝ) ≤ s n ^ 2 :=
    hcoarse s (fun n hn => ⟨(hb1 n hn).1, (hb1 n hn).2.1, (hb1 n hn).2.2.1, (hb1 n hn).2.2.2.1⟩)
      hsq
  have hsec := second_pass_telescope C1 cStar K hC1 hc hK s N5 hN5_3
    (fun n hn => by
      have hnr : max 1 (max ((1 / 2 * (cStar * Real.log 3) ^ (1 / 2 : ℝ))⁻¹ ^ 2) cStar) ≤ (n : ℝ) :=
        le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hn)
      exact hcondR (n : ℝ) hnr)
    (fun n hn => ⟨by linarith only [(hb1 n (le_trans hN14 (le_trans hN4_5 hn))).1],
      hco n (le_trans hN4_5 hn)⟩)
    (fun n hn => hsq n (le_trans hN14 (le_trans hN4_5 hn)))
  -- the fixed constant at `N5`
  have hmN5 : N5 ≤ m := le_trans (le_max_left _ _) hm
  have hmN6 : N6 ≤ m := le_trans (le_max_right _ _) hm
  have hf5 : |s N5 ^ 2 - 2 * (cStar * Real.log 3) * (N5 : ℝ)| ≤
      cStar ^ (-(1 / 2 : ℝ)) * (m : ℝ) ^ (1 / 2 : ℝ) * (Real.log (m : ℝ) ^ 2 + K) := by
    have hb5 := hb1 N5 (le_trans hN14 hN4_5)
    have hs2 : s N5 ^ 2 ≤ (A * (N5 : ℝ) ^ (1 / 2 : ℝ) * Real.log (N5 : ℝ) ^ (9 / 2 : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (by linarith only [hb5.1]) hb5.2.2.1 2
    have h0 : 0 ≤ 2 * (cStar * Real.log 3) * (N5 : ℝ) := by positivity
    have h6 := hN6 m hmN6
    have : |s N5 ^ 2 - 2 * (cStar * Real.log 3) * (N5 : ℝ)| ≤
        (A * (N5 : ℝ) ^ (1 / 2 : ℝ) * Real.log (N5 : ℝ) ^ (9 / 2 : ℝ)) ^ 2 +
          2 * (cStar * Real.log 3) * N5 := by
      rw [abs_le]; constructor <;> nlinarith only [hs2, h0, sq_nonneg (s N5)]
    calc _ ≤ _ := this
      _ ≤ _ := h6
      _ = _ := by ring
  have hfm := hsec m hmN5
  set Λ : ℝ := Real.log (m : ℝ) ^ 2 + K with hΛdef
  have hm3 : 3 ≤ m := le_trans hN5_3 hmN5
  have hu1 := one_le_log_nat hm3
  have hΛ : 1 ≤ Λ := by rw [hΛdef]; nlinarith only [hu1, hK]
  set r : ℝ := cStar ^ (-(1 / 2 : ℝ)) with hrdef
  set w : ℝ := (m : ℝ) ^ (1 / 2 : ℝ) with hwdef
  have hfmm : |s m ^ 2 - 2 * (cStar * Real.log 3) * (m : ℝ)| ≤ (13 * C1 + 1) * (r * w * Λ) := by
    have := abs_add_le ((s m ^ 2 - 2 * (cStar * Real.log 3) * (m : ℝ)) -
        (s N5 ^ 2 - 2 * (cStar * Real.log 3) * (N5 : ℝ)))
      (s N5 ^ 2 - 2 * (cStar * Real.log 3) * (N5 : ℝ))
    rw [sub_add_cancel] at this
    linarith only [this, hfm, hf5]
  -- Step 7
  have hsm := hb1 m (le_trans hN14 (le_trans hN4_5 hmN5))
  have hs0 : 0 < s m := by linarith only [hsm.1]
  have hcm := hco m (le_trans hN4_5 hmN5)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have ha : 0 < Real.sqrt cStar := Real.sqrt_pos.2 hc
  have hb : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hm0
  have hwb : w = Real.sqrt (m : ℝ) := (Real.sqrt_eq_rpow _).symm
  have hra : r = (Real.sqrt cStar)⁻¹ := by
    rw [hrdef, Real.rpow_neg hc.le, Real.sqrt_eq_rpow]
  have hroot : (2 * cStar * Real.log 3 * (m : ℝ)) ^ ((1 : ℝ) / 2) =
      Real.sqrt (2 * (cStar * Real.log 3) * (m : ℝ)) := by
    rw [Real.sqrt_eq_rpow]; ring_nf
  rw [hroot]
  set t := Real.sqrt (2 * (cStar * Real.log 3) * (m : ℝ)) with htdef
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t ^ 2 = 2 * (cStar * Real.log 3) * (m : ℝ) := Real.sq_sqrt (by positivity)
  -- `s m ≥ √c⋆ √m`
  have hlow : Real.sqrt cStar * Real.sqrt (m : ℝ) ≤ s m := by
    have h1 : Real.sqrt cStar * Real.sqrt (m : ℝ) = Real.sqrt (cStar * m) :=
      (Real.sqrt_mul hc.le _).symm
    rw [h1]
    refine Real.sqrt_le_iff.2 ⟨hs0.le, ?_⟩
    have : cStar * (m : ℝ) ≤ cStar * Real.log 3 * m := by
      nlinarith only [one_lt_log_three, mul_pos hc hm0]
    linarith only [this, hcm]
  have hid : |s m - t| * (s m + t) = |s m ^ 2 - 2 * (cStar * Real.log 3) * (m : ℝ)| := by
    rw [← ht2, show s m ^ 2 - t ^ 2 = (s m - t) * (s m + t) by ring, abs_mul,
      abs_of_nonneg (by linarith only [hs0, ht0] : (0 : ℝ) ≤ s m + t)]
  have h1 : |s m - t| * (Real.sqrt cStar * Real.sqrt (m : ℝ)) ≤
      (13 * C1 + 1) * ((Real.sqrt cStar)⁻¹ * Real.sqrt (m : ℝ) * Λ) := by
    have : |s m - t| * (Real.sqrt cStar * Real.sqrt (m : ℝ)) ≤ |s m - t| * (s m + t) :=
      mul_le_mul_of_nonneg_left (by linarith only [hlow, ht0]) (abs_nonneg _)
    rw [hid] at this
    rw [hra, hwb] at hfmm
    exact le_trans this hfmm
  have h2 : |s m - t| * Real.sqrt cStar ^ 2 * Real.sqrt (m : ℝ) ≤
      (13 * C1 + 1) * Λ * Real.sqrt (m : ℝ) := by
    have := mul_le_mul_of_nonneg_left h1 ha.le
    calc |s m - t| * Real.sqrt cStar ^ 2 * Real.sqrt (m : ℝ)
        = Real.sqrt cStar * (|s m - t| * (Real.sqrt cStar * Real.sqrt (m : ℝ))) := by ring
      _ ≤ Real.sqrt cStar * ((13 * C1 + 1) * ((Real.sqrt cStar)⁻¹ * Real.sqrt (m : ℝ) * Λ)) := this
      _ = _ := by field_simp
  have h3 : |s m - t| * Real.sqrt cStar ^ 2 ≤ (13 * C1 + 1) * Λ := le_of_mul_le_mul_right h2 hb
  rw [Real.sq_sqrt hc.le] at h3
  rw [show (13 * C1 + 1) * cStar⁻¹ * (Real.log (m : ℝ) ^ (2 : ℝ) + K) =
      ((13 * C1 + 1) * Λ) / cStar by rw [Real.rpow_two]; ring, le_div_iff₀ hc]
  exact h3

/-! ## Satisfiability: `c⋆ = 2`, `κ = 0`, `A = 3`, `C_r = 9`, `N₀ = M_prop = 3`

The sequence `s n = (2 c⋆ (log 3) n)^{1/2}` satisfies both hypotheses of `sharp_of_recurrence`. -/

end SuperdiffusionCLT.Section5
