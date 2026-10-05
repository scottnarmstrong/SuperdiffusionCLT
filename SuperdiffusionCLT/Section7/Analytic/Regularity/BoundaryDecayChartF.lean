/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.BoundaryDecayChartE

@[expose] public section

open Homogenization MeasureTheory Filter Topology Matrix
open scoped ENNReal NNReal

/-!
# The dyadic chain of slopes

The flat boundary decay gives an affine function at every scale.  Along the dyadic scales
`3^m / (36 · 2^j)` the slopes of these affine functions form a Cauchy sequence with geometric
increments, so every slope stays within a multiple of the datum of the slope at the top scale.
-/

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem r3e_pow_half (α : ℝ) (hα : 0 < α) (j : ℕ) :
    ((1 : ℝ) / (36 * 2 ^ j)) ^ α ≤ (((1 : ℝ) / 2) ^ α) ^ j := by
  have h1 : (((1 : ℝ) / 2) ^ α) ^ j = (((1 : ℝ) / 2) ^ j) ^ α :=
    Real.rpow_pow_comm (by norm_num) α j
  rw [h1]
  refine Real.rpow_le_rpow (by positivity) ?_ hα.le
  rw [_root_.one_div_pow, one_div, one_div]
  exact inv_anti₀ (by positivity) (by nlinarith only [pow_pos (by norm_num : (0 : ℝ) < 2) j])

/-- **The chain of slopes.** -/
theorem r3e_chain (e : Fin d) (m : ℤ) {α C₀ B : ℝ} (hα : 0 < α) (hC₀ : 0 ≤ C₀) (hB : 0 ≤ B)
    {v : Vec d → ℝ}
    (H : ∀ s : ℝ, 0 < s → s ≤ (3 : ℝ) ^ m / 36 → ∃ (a : ℝ) (b : Vec d),
      ∀ᵐ x ∂(volume.restrict (r3e_F e m s)),
        |v x - (a + vecDot b (x - r3c_z0 e m))| ≤ C₀ * s * (s / (3 : ℝ) ^ m) ^ α * B) :
    ∃ (a₁ : ℝ) (b₁ : Vec d),
      (∀ᵐ x ∂(volume.restrict (r3e_F e m ((3 : ℝ) ^ m / 36))),
        |v x - (a₁ + vecDot b₁ (x - r3c_z0 e m))| ≤
          C₀ * ((3 : ℝ) ^ m / 36) * (((3 : ℝ) ^ m / 36) / (3 : ℝ) ^ m) ^ α * B) ∧
      ∀ s : ℝ, 0 < s → s ≤ (3 : ℝ) ^ m / 36 → ∃ (a : ℝ) (b : Vec d),
        (∀ᵐ x ∂(volume.restrict (r3e_F e m s)),
          |v x - (a + vecDot b (x - r3c_z0 e m))| ≤
            C₀ * (2 * s) * (2 * s / (3 : ℝ) ^ m) ^ α * B) ∧
        ‖b - b₁‖ ≤ 6 * C₀ * B / (1 - ((1 : ℝ) / 2) ^ α) := by
  have hR : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  set R : ℝ := (3 : ℝ) ^ m with hRd
  set q : ℝ := ((1 : ℝ) / 2) ^ α with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hα
  have hq1' : 0 < 1 - q := by linarith only [hq1]
  set sj : ℕ → ℝ := fun j => R / 36 / 2 ^ j with hsj
  have hsj0 : ∀ j, 0 < sj j := fun j => by simp only [hsj]; positivity
  have hsjle : ∀ j, sj (j + 1) ≤ sj j := fun j => by
    simp only [hsj, pow_succ]
    have : 0 < R / 36 / 2 ^ j := by positivity
    rw [div_mul_eq_div_div]
    linarith only [this]
  have hsjR : ∀ j, sj j ≤ R / 36 := fun j => by
    simp only [hsj]
    exact div_le_self (by positivity) (one_le_pow₀ (by norm_num))
  have hsjratio : ∀ j, sj j / R = 1 / (36 * 2 ^ j) := fun j => by
    simp only [hsj]; field_simp
  obtain ⟨a₁, b₁, h₁⟩ := H (R / 36) (by positivity) le_rfl
  have hP : ∀ j : ℕ, ∃ (a : ℝ) (b : Vec d),
      (∀ᵐ x ∂(volume.restrict (r3e_F e m (sj j))),
        |v x - (a + vecDot b (x - r3c_z0 e m))| ≤ C₀ * sj j * (sj j / R) ^ α * B) ∧
      ‖b - b₁‖ ≤ 6 * C₀ * B * (1 - q ^ j) / (1 - q) := by
    intro j
    induction j with
    | zero =>
      refine ⟨a₁, b₁, ?_, by simp⟩
      simpa [hsj] using h₁
    | succ j ih =>
      obtain ⟨a, b, hab, hb⟩ := ih
      obtain ⟨a', b', hab'⟩ := H (sj (j + 1)) (hsj0 _) ((hsjle j).trans (hsjR j))
      refine ⟨a', b', hab', ?_⟩
      have hE0 : 0 ≤ C₀ * sj j * (sj j / R) ^ α * B := by
        have := hsj0 j
        positivity
      have hE0' : 0 ≤ C₀ * sj (j + 1) * (sj (j + 1) / R) ^ α * B := by
        have := hsj0 (j + 1)
        positivity
      have hdiff := r3e_slope_diff e m (hsj0 (j + 1)) (hsjle j) hE0 hE0' hab hab'
      have hs2 : sj j = 2 * sj (j + 1) := by
        simp only [hsj, pow_succ]; field_simp
      have hpow1 : (sj (j + 1) / R) ^ α ≤ (sj j / R) ^ α :=
        Real.rpow_le_rpow (by have := hsj0 (j + 1); positivity)
          (div_le_div_of_nonneg_right (hsjle j) hR.le) hα.le
      have hpow2 : (sj j / R) ^ α ≤ q ^ j := by
        rw [hsjratio]; exact r3e_pow_half α hα j
      have hsp := hsj0 (j + 1)
      have hstep : 2 * (C₀ * sj j * (sj j / R) ^ α * B + C₀ * sj (j + 1) * (sj (j + 1) / R) ^ α * B) /
          sj (j + 1) ≤ 6 * C₀ * B * q ^ j := by
        rw [div_le_iff₀ hsp]
        have hCB : 0 ≤ C₀ * B := mul_nonneg hC₀ hB
        have e1 : 2 * (C₀ * sj j * (sj j / R) ^ α * B + C₀ * sj (j + 1) * (sj (j + 1) / R) ^ α * B) =
            2 * (C₀ * B) * (sj j * (sj j / R) ^ α + sj (j + 1) * (sj (j + 1) / R) ^ α) := by ring
        rw [e1]
        have hA : sj j * (sj j / R) ^ α ≤ 2 * sj (j + 1) * q ^ j :=
          calc sj j * (sj j / R) ^ α ≤ sj j * q ^ j := mul_le_mul_of_nonneg_left hpow2 (hsj0 j).le
            _ = 2 * sj (j + 1) * q ^ j := by rw [hs2]
        have hB' : sj (j + 1) * (sj (j + 1) / R) ^ α ≤ sj (j + 1) * q ^ j :=
          mul_le_mul_of_nonneg_left (hpow1.trans hpow2) hsp.le
        calc 2 * (C₀ * B) * (sj j * (sj j / R) ^ α + sj (j + 1) * (sj (j + 1) / R) ^ α)
            ≤ 2 * (C₀ * B) * (3 * sj (j + 1) * q ^ j) :=
              mul_le_mul_of_nonneg_left (by linarith only [hA, hB']) (by positivity)
          _ = 6 * C₀ * B * q ^ j * sj (j + 1) := by ring
      have hbb : ‖b' - b₁‖ ≤ ‖b - b'‖ + ‖b - b₁‖ := by
        calc ‖b' - b₁‖ = ‖(b - b₁) - (b - b')‖ := by congr 1; abel
          _ ≤ ‖b - b₁‖ + ‖b - b'‖ := norm_sub_le _ _
          _ = _ := add_comm _ _
      have hfin : 6 * C₀ * B * q ^ j + 6 * C₀ * B * (1 - q ^ j) / (1 - q) =
          6 * C₀ * B * (1 - q ^ (j + 1)) / (1 - q) := by
        field_simp
        ring
      calc ‖b' - b₁‖ ≤ ‖b - b'‖ + ‖b - b₁‖ := hbb
        _ ≤ 6 * C₀ * B * q ^ j + 6 * C₀ * B * (1 - q ^ j) / (1 - q) :=
          add_le_add (hdiff.trans hstep) hb
        _ = _ := hfin
  have hb_bound : ∀ j : ℕ, 6 * C₀ * B * (1 - q ^ j) / (1 - q) ≤ 6 * C₀ * B / (1 - q) := fun j => by
    refine div_le_div_of_nonneg_right ?_ hq1'.le
    have : 0 ≤ q ^ j := by positivity
    have h6 : 0 ≤ 6 * C₀ * B := by positivity
    nlinarith only [this, h6]
  refine ⟨a₁, b₁, ?_, ?_⟩
  · simpa using h₁
  · intro s hs hsR
    have hex : ∃ j : ℕ, sj (j + 1) < s := by
      obtain ⟨n, hn⟩ := exists_nat_gt (R / 36 / s)
      refine ⟨n, ?_⟩
      have h2n : (n : ℝ) < 2 ^ (n + 1) := by
        have := Nat.lt_two_pow_self (n := n + 1)
        have h' : (n : ℝ) < ((2 ^ (n + 1) : ℕ) : ℝ) := by exact_mod_cast (by omega)
        simpa using h'
      simp only [hsj]
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hs] at hn
      nlinarith only [hn, h2n, hs]
    classical
    set j := Nat.find hex with hj
    have hj1 : sj (j + 1) < s := Nat.find_spec hex
    have hj2 : s ≤ sj j := by
      by_cases h0 : j = 0
      · rw [h0]; simpa [hsj] using hsR
      · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h0
        have := Nat.find_min hex (show k < j by omega)
        rw [hk]
        exact not_lt.1 this
    have hj3 : sj j ≤ 2 * s := by
      have hs2 : sj j = 2 * sj (j + 1) := by
        simp only [hsj, pow_succ]; field_simp
      linarith only [hs2, hj1]
    obtain ⟨a, b, hab, hb⟩ := hP j
    refine ⟨a, b, ?_, hb.trans (hb_bound j)⟩
    have hmono := ae_restrict_of_ae_restrict_of_subset (r3e_F_mono e m hj2) hab
    refine hmono.mono fun x hx => hx.trans ?_
    have hsp := hsj0 j
    have hpw : (sj j / R) ^ α ≤ (2 * s / R) ^ α :=
      Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_right hj3 hR.le) hα.le
    have hCB : 0 ≤ C₀ * B := mul_nonneg hC₀ hB
    have h7 : C₀ * sj j * (sj j / R) ^ α ≤ C₀ * (2 * s) * (2 * s / R) ^ α :=
      mul_le_mul (mul_le_mul_of_nonneg_left hj3 hC₀) hpw (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right h7 hB

end SuperdiffusionCLT.Section7
