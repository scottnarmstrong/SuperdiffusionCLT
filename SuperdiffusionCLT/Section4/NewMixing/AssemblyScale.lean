/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.NewMixing.ScaleConstruction

/-!
# The scale construction with its witnesses identified

`ScaleConstruction.lean` proves the numeric facts behind the scale choice; the construction itself
is assembled here. The `T_0` refinement needs to know which case produced the scales `ell, n`, so
the construction carries the extra conclusion that
`ell = m - h`, `n = ell - h` (case `m ≤ L + h`) or `ell = L`, `n = ell - h` (case `L + h < m`), where
`h = ⌈K₀ K log L⌉`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.NewMixing

open SuperdiffusionCLT.Section4.LNaught

noncomputable section

/-- **The scale construction** (`l.new.mixing.parameterized#scale-construction`).
See the module docstring for what is (and is not) proved. -/
theorem newMixAsm_scaleExplicit :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ alpha M K cStar nu nondeg : ℝ,
        0 ≤ alpha → alpha < 1 → 1 ≤ M → 1 ≤ K → 0 < cStar → cStar ≤ 2 → 0 < nu → nu ≤ 1 →
        0 ≤ nondeg →
        ∀ L m r : ℕ,
          SuperdiffusionCLT.Frozen.Section4.lNaught C (C * (M + K)) alpha cStar nu nondeg ≤
            (L : ℝ) →
          SuperdiffusionCLT.Frozen.Section4.lNaught C (C * (M + K)) alpha cStar nu nondeg ≤
            (m : ℝ) →
          (L : ℝ) - M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (m : ℝ) →
          |(L : ℝ) - (r : ℝ)| ≤ K * Real.log (L : ℝ) →
          ∃ ell n : ℕ,
            n < ell ∧ ell < m ∧ ell ≤ L ∧
            (L : ℝ) / 2 ≤ (ell : ℝ) ∧
            (L : ℝ) / 2 ≤ (r : ℝ) ∧ (r : ℝ) ≤ 2 * (L : ℝ) ∧
            (L : ℝ) - (ell : ℝ) ≤ max 0 ((L : ℝ) - (m : ℝ)) + C * K * Real.log (L : ℝ) ∧
            (ell : ℝ) - (n : ℝ) ≤ C * K * Real.log (L : ℝ) ∧
            n ≤ r ∧
            (r : ℝ) - (n : ℝ) ≤ max 0 ((L : ℝ) - (m : ℝ)) + C * K * Real.log (L : ℝ) ∧
            200 * Real.log (L : ℝ) ≤ min (ell : ℝ) (r : ℝ) - (n : ℝ) ∧
            ((m ≤ L + newMixParam_h K (Real.log (L : ℝ)) ∧
                ell = m - newMixParam_h K (Real.log (L : ℝ)) ∧
                n = ell - newMixParam_h K (Real.log (L : ℝ))) ∨
              (L + newMixParam_h K (Real.log (L : ℝ)) < m ∧ ell = L ∧
                n = ell - newMixParam_h K (Real.log (L : ℝ)))) ∧
            (8 : ℝ) < (L : ℝ) ∧ (L : ℝ) / 4 ≤ (n : ℝ) := by
  obtain ⟨C0, hC0, hslack⟩ := newMixParam_absorbSlack
  refine ⟨max C0 100000, le_trans hC0 (le_max_left _ _), ?_⟩
  intro alpha M K cStar nu nondeg hα0 hα1 hM hK hcStar hcStar2 hnu hnu1 hnondeg L m r hL hm hLm hLr
  have hC0' : C0 ≤ max C0 100000 := le_max_left _ _
  have hC100000 : (100000 : ℝ) ≤ max C0 100000 := le_max_right _ _
  set C := max C0 100000 with hCdef
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le (by norm_num) hC100000
  obtain ⟨hL8, hMLslack, hKLslack⟩ :=
    hslack C hC0' M K alpha cStar nu nondeg hM hK hα0 hα1 hcStar hcStar2 hnu hnu1 hnondeg L hL
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by linarith only [hL8]
  have hlogLnn : (0 : ℝ) ≤ Real.log (L : ℝ) := Real.log_nonneg hL1
  have hlogL_gt2 : (2 : ℝ) < Real.log (L : ℝ) := by
    have h8 : Real.log (8 : ℝ) < Real.log (L : ℝ) := Real.log_lt_log (by norm_num) hL8
    have hlog8eq : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℕ) by norm_num, Real.log_pow]
      push_cast; ring
    have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    linarith only [h8, hlog8eq, hlog2]
  have hlogL1 : (1 : ℝ) ≤ Real.log (L : ℝ) := by linarith only [hlogL_gt2]
  have hLalpha1 : (1 : ℝ) ≤ (L : ℝ) ^ alpha := newMixParam_one_le_rpow hL1 hα0
  have hlog3geLog : Real.log (L : ℝ) ≤ Real.log (L : ℝ) ^ (3 : ℝ) :=
    newMixParam_le_rpow_three hlogL1
  have hlog3nn : (0 : ℝ) ≤ Real.log (L : ℝ) ^ (3 : ℝ) := le_trans hlogLnn hlog3geLog
  have hKnn : (0 : ℝ) ≤ K := by linarith only [hK]
  have hstepLE : Real.log (L : ℝ) ≤ (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) := by
    calc Real.log (L : ℝ) ≤ Real.log (L : ℝ) ^ (3 : ℝ) := hlog3geLog
      _ = 1 * Real.log (L : ℝ) ^ (3 : ℝ) := (one_mul _).symm
      _ ≤ (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) :=
        mul_le_mul_of_nonneg_right hLalpha1 hlog3nn
  have hKlogL_le_slack : K * Real.log (L : ℝ) ≤ (L : ℝ) / (2 * C) := by
    have h1 : K * Real.log (L : ℝ) ≤ K * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) :=
      mul_le_mul_of_nonneg_left hstepLE hKnn
    have h2 : K * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) =
        K * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) := by ring
    rw [h2] at h1
    exact le_trans h1 hKLslack
  -- `K₀ K log L ≥ 1`, so the ceiling of `h` is controlled by `2 K₀ K log L`.
  have hKlogL1 : (1 : ℝ) ≤ K * Real.log (L : ℝ) := by nlinarith only [hK, hlogL1]
  have hx1 : (1 : ℝ) ≤ newMixParam_K0 * K * Real.log (L : ℝ) := by
    unfold newMixParam_K0
    nlinarith only [hKlogL1]
  have hx0 : (0 : ℝ) < newMixParam_K0 * K * Real.log (L : ℝ) :=
    lt_of_lt_of_le one_pos hx1
  have hhle := newMixParam_h_le hx1
  have hhge := @newMixParam_h_ge K (Real.log (L : ℝ))
  have hhpos := newMixParam_h_pos hx0
  set h := newMixParam_h K (Real.log (L : ℝ)) with hhdef
  -- `h ≤ 2 K₀ K log L`, so (with `K₀ = 12000` and `C ≥ 100000`) `h ≤ L/4`.
  have hK0eq : newMixParam_K0 = 12000 := rfl
  have hhleL4 : (h : ℝ) ≤ (L : ℝ) / 4 := by
    have h1 : (h : ℝ) ≤ 2 * (newMixParam_K0 * (K * Real.log (L : ℝ))) := by
      have heqassoc : newMixParam_K0 * K * Real.log (L : ℝ) =
          newMixParam_K0 * (K * Real.log (L : ℝ)) := by ring
      rw [heqassoc] at hhle
      exact hhle
    rw [hK0eq] at h1
    have h2 : (12000 : ℝ) * (K * Real.log (L : ℝ)) ≤ 12000 * ((L : ℝ) / (2 * C)) :=
      mul_le_mul_of_nonneg_left hKlogL_le_slack (by norm_num)
    have h3 : (L : ℝ) / (2 * C) ≤ (L : ℝ) / 200000 := by
      apply div_le_div_of_nonneg_left (Nat.cast_nonneg L) (by norm_num)
      linarith only [hC100000]
    have h4 : (24000 : ℝ) * ((L : ℝ) / 200000) ≤ (L : ℝ) / 4 := by
      have heq : (24000 : ℝ) * ((L:ℝ) / 200000) = (L:ℝ) * (24000/200000) := by ring
      rw [heq]
      have heq2 : (L:ℝ) / 4 = (L:ℝ) * (1/4) := by ring
      rw [heq2]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg L)
      norm_num
    linarith only [h1, h2, h3, h4]
  have hLnn : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have hKlogLnn : (0 : ℝ) ≤ K * Real.log (L : ℝ) := mul_nonneg hKnn hlogLnn
  -- The sharp bound `h ≤ 24000 K log L` (`K₀ = 12000`, ceiling doubling).
  have hh24000 : (h : ℝ) ≤ 24000 * (K * Real.log (L : ℝ)) := by
    have heqassoc : newMixParam_K0 * K * Real.log (L : ℝ) =
        newMixParam_K0 * (K * Real.log (L : ℝ)) := by ring
    rw [heqassoc, hK0eq] at hhle
    linarith only [hhle]
  -- `h ≤ C K log L` (fact 7): from `h ≤ 24000 K log L` and `C ≥ 100000`. Stated
  -- left-associated (`C * K * log L`), matching the final conclusion's shape.
  have hCKbound : (h : ℝ) ≤ C * K * Real.log (L : ℝ) := by
    have h2 : (24000 : ℝ) * (K * Real.log (L : ℝ)) ≤ C * (K * Real.log (L : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith only [hC100000]) hKlogLnn
    have heq : C * (K * Real.log (L : ℝ)) = C * K * Real.log (L : ℝ) := by ring
    rw [heq] at h2
    linarith only [hh24000, h2]
  -- The doubled sharp bound, `2h ≤ 48000 K log L ≤ (C-1) K log L`, needed for the
  -- `r - n` bound (both branches): the extra `+ K log L` term from `|L-r|≤KlogL`
  -- needs slack beyond `h ≤ C K log L` alone.
  have hCKbound' : (h : ℝ) + K * Real.log (L : ℝ) ≤ C * K * Real.log (L : ℝ) := by
    have h2 : (24001 : ℝ) * (K * Real.log (L : ℝ)) ≤ C * (K * Real.log (L : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith only [hC100000]) hKlogLnn
    have heq : C * (K * Real.log (L : ℝ)) = C * K * Real.log (L : ℝ) := by ring
    rw [heq] at h2
    linarith only [hh24000, h2]
  have hCKbound2 : (h : ℝ) + (h : ℝ) + K * Real.log (L : ℝ) ≤ C * K * Real.log (L : ℝ) := by
    have h2 : (48001 : ℝ) * (K * Real.log (L : ℝ)) ≤ C * (K * Real.log (L : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith only [hC100000]) hKlogLnn
    have heq : C * (K * Real.log (L : ℝ)) = C * K * Real.log (L : ℝ) := by ring
    rw [heq] at h2
    linarith only [hh24000, h2]
  -- `h ≥ (200+K) log L` (used for fact 9 in both branches).
  have hh200K : (200 + K) * Real.log (L : ℝ) ≤ (h : ℝ) := by
    have h1 : (200 + K) * Real.log (L:ℝ) ≤ newMixParam_K0 * K * Real.log (L:ℝ) := by
      have h1a : (200 + K) ≤ 11999 * K := by nlinarith only [hK]
      have h1b : (200 + K) * Real.log (L:ℝ) ≤ (11999 * K) * Real.log (L:ℝ) :=
        mul_le_mul_of_nonneg_right h1a hlogLnn
      have h1c : (11999 * K) * Real.log (L:ℝ) ≤ newMixParam_K0 * K * Real.log (L:ℝ) := by
        rw [hK0eq]; nlinarith only [hKlogL1, hlogLnn]
      linarith only [h1b, h1c]
    linarith only [h1, hhge]
  -- `m ≥ L - L/(2C) ≥ 3L/4` and `h ≤ L/4 ≤ m`, so `h ≤ m` as naturals.
  have hmLB : (L : ℝ) - (L : ℝ) / (2 * C) ≤ (m : ℝ) := by linarith only [hLm, hMLslack]
  have hslackleL4 : (L : ℝ) / (2 * C) ≤ (L : ℝ) / 4 := by
    apply div_le_div_of_nonneg_left hLnn (by norm_num)
    linarith only [hC100000]
  have hmge34 : (3 : ℝ) / 4 * (L : ℝ) ≤ (m : ℝ) := by linarith only [hmLB, hslackleL4]
  have hhlem : (h : ℝ) ≤ (m : ℝ) := by nlinarith only [hhleL4, hmge34, hLnn]
  have hhlem_nat : h ≤ m := by exact_mod_cast hhlem
  have hrL_le : (r : ℝ) ≤ (L : ℝ) + K * Real.log (L : ℝ) := by
    have := abs_le.mp hLr
    linarith only [this.1]
  have hrL_ge : (L : ℝ) - K * Real.log (L : ℝ) ≤ (r : ℝ) := by
    have := abs_le.mp hLr
    linarith only [this.2]
  rcases le_or_gt m (L + h) with hcaseA | hcaseB
  · -- Case A: `ℓ := m - h`, `n := ℓ - h = m - 2h`.
    have hellR : (L : ℝ) / 2 ≤ (m : ℝ) - (h : ℝ) := by linarith only [hmge34, hhleL4]
    have hhleell : (h : ℝ) ≤ (m : ℝ) - (h : ℝ) := by linarith only [hhleL4, hellR, hLnn]
    have hellcast : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub hhlem_nat
    have hhleell_nat : h ≤ m - h := by
      have h1 : (h : ℝ) ≤ ((m - h : ℕ) : ℝ) := by rw [hellcast]; exact hhleell
      exact_mod_cast h1
    have hncast : (((m - h) - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) - (h : ℝ) := by
      rw [Nat.cast_sub hhleell_nat, hellcast]
    have hcaseAR : (m : ℝ) ≤ (L : ℝ) + (h : ℝ) := by exact_mod_cast hcaseA
    refine ⟨m - h, (m - h) - h, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · have : (((m - h : ℕ) : ℝ)) ≤ (L:ℝ) := by rw [hellcast]; linarith only [hcaseAR]
      exact_mod_cast this
    · rw [hellcast]; exact hellR
    · linarith only [hrL_ge, hKlogL_le_slack, hslackleL4]
    · nlinarith only [hrL_le, hLnn, hKlogL_le_slack, hslackleL4]
    · rw [hellcast]
      rcases le_or_gt m L with hml | hml
      · have hmL0 : (0:ℝ) ≤ (L:ℝ) - (m:ℝ) := by
          have : (m:ℝ) ≤ (L:ℝ) := by exact_mod_cast hml
          linarith only [this]
        rw [max_eq_right hmL0]
        linarith only [hCKbound]
      · have hmL0 : (L:ℝ) - (m:ℝ) < 0 := by
          have : (L:ℝ) < (m:ℝ) := by exact_mod_cast hml
          linarith only [this]
        rw [max_eq_left hmL0.le]
        linarith only [hCKbound, hmL0]
    · rw [hncast, hellcast]
      linarith only [hCKbound]
    · have hnr : (((m - h) - h : ℕ) : ℝ) ≤ (r : ℝ) := by
        rw [hncast]
        linarith only [hrL_ge, hcaseAR, hCKbound, hh200K, hlogLnn]
      exact_mod_cast hnr
    · rw [hncast]
      rcases le_or_gt m L with hml | hml
      · have hmL0 : (0:ℝ) ≤ (L:ℝ) - (m:ℝ) := by
          have : (m:ℝ) ≤ (L:ℝ) := by exact_mod_cast hml
          linarith only [this]
        rw [max_eq_right hmL0]
        linarith only [hrL_le, hCKbound2]
      · have hmL0 : (L:ℝ) - (m:ℝ) < 0 := by
          have : (L:ℝ) < (m:ℝ) := by exact_mod_cast hml
          linarith only [this]
        rw [max_eq_left hmL0.le]
        linarith only [hrL_le, hCKbound2, hmL0]
    · rw [hellcast, hncast]
      rw [le_sub_iff_add_le, le_min_iff]
      have hKlogLnn : (0:ℝ) ≤ K * Real.log (L:ℝ) := mul_nonneg hKnn hlogLnn
      constructor
      · linarith only [hh200K, hKlogLnn]
      · linarith only [hrL_ge, hcaseAR, hh200K]
    · exact Or.inl ⟨hcaseA, rfl, rfl⟩
    · exact hL8
    · rw [hncast]; linarith only [hmge34, hhleL4]
  · -- Case B: `ℓ := L`, `n := L - h`.
    have hLh_nat : h ≤ L := by
      have h1 : (h:ℝ) ≤ (L:ℝ) := by linarith only [hhleL4, hLnn]
      exact_mod_cast h1
    have hncast : ((L - h : ℕ) : ℝ) = (L : ℝ) - (h : ℝ) := Nat.cast_sub hLh_nat
    have hcaseBR : (L : ℝ) + (h : ℝ) < (m : ℝ) := by exact_mod_cast hcaseB
    refine ⟨L, L - h, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · exact le_rfl
    · linarith only [hLnn]
    · linarith only [hrL_ge, hKlogL_le_slack, hslackleL4]
    · nlinarith only [hrL_le, hLnn, hKlogL_le_slack, hslackleL4]
    · have hmL0 : (L:ℝ) - (m:ℝ) < 0 := by linarith only [hcaseBR, hhpos]
      rw [max_eq_left hmL0.le, sub_self]
      have h2 : (0:ℝ) ≤ C * K * Real.log (L:ℝ) :=
        mul_nonneg (mul_nonneg hCpos.le hKnn) hlogLnn
      linarith only [h2]
    · rw [hncast]
      linarith only [hCKbound]
    · have hnr : ((L - h : ℕ) : ℝ) ≤ (r : ℝ) := by
        rw [hncast]
        linarith only [hrL_ge, hh200K, hlogLnn]
      exact_mod_cast hnr
    · have hmL0 : (L:ℝ) - (m:ℝ) < 0 := by linarith only [hcaseBR, hhpos]
      rw [max_eq_left hmL0.le, hncast]
      linarith only [hrL_le, hCKbound']
    · rw [hncast]
      rw [le_sub_iff_add_le, le_min_iff]
      have hKlogLnn : (0:ℝ) ≤ K * Real.log (L:ℝ) := mul_nonneg hKnn hlogLnn
      constructor
      · linarith only [hh200K, hKlogLnn]
      · linarith only [hrL_ge, hh200K]
    · exact Or.inr ⟨hcaseB, rfl, rfl⟩
    · exact hL8
    · rw [hncast]; linarith only [hhleL4, hLnn]

end

end SuperdiffusionCLT.Section4.NewMixing
