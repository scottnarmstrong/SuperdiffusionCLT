/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Complex.Exponential

/-!
# Real-variable estimates for the stretched-exponential union bound

* `rpow_mul_exp_neg_le`: `x^(b+2) * exp(-(x^σ)/2) ≤ C₂` for all `x > 0`.
* `poly_mul_exp_le`: the term `B K^b exp(-(aK)^σ)` is at most `B C₂ a^{-(b+2)} K^{-2} exp(-(aK)^σ/2)`.
* `sum_tail_le`: the tail sum of these terms over `K ≥ m` is at most `2 B C₂ a^{-(b+2)} exp(-(am)^σ/2)`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Finset

noncomputable section

/-- `x^(b+2) e^{-x^σ/2}` is bounded on `(0, ∞)` by a constant depending only on `σ, b`. -/
theorem rpow_mul_exp_neg_le {σ : ℝ} (hσ : 0 < σ) (b : ℝ) (hb : 0 ≤ b) :
    ∃ C₂ : ℝ, 1 ≤ C₂ ∧ ∀ x : ℝ, 0 < x → x ^ (b + 2) * Real.exp (-(x ^ σ / 2)) ≤ C₂ := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (b + 2) / σ ≤ m := ⟨⌈(b + 2) / σ⌉₊, Nat.le_ceil _⟩
  refine ⟨2 ^ m * (m.factorial : ℝ), ?_, fun x hx => ?_⟩
  · have h1 : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
    have h2 : (1 : ℝ) ≤ (m.factorial : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero m)
    nlinarith only [h1, h2]
  · by_cases hx1 : x ≤ 1
    · have h1 : x ^ (b + 2) ≤ 1 := Real.rpow_le_one hx.le hx1 (by linarith only [hb])
      have h2 : Real.exp (-(x ^ σ / 2)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ x ^ σ := Real.rpow_nonneg hx.le σ
        linarith only [this]
      have h3 : (1 : ℝ) ≤ 2 ^ m * (m.factorial : ℝ) := by
        have h1 : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
        have h2 : (1 : ℝ) ≤ (m.factorial : ℝ) := by
          exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero m)
        nlinarith only [h1, h2]
      calc x ^ (b + 2) * Real.exp (-(x ^ σ / 2)) ≤ 1 * 1 :=
            mul_le_mul h1 h2 (Real.exp_pos _).le zero_le_one
        _ ≤ _ := by linarith only [h3]
    · push Not at hx1
      have hxpow : x ^ (b + 2) ≤ (x ^ σ) ^ m := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
        exact Real.rpow_le_rpow_of_exponent_le hx1.le (by
          have := (div_le_iff₀ hσ).1 hm
          linarith only [this])
      set y := x ^ σ / 2 with hy
      have hy0 : 0 ≤ y := by positivity
      have hxy : x ^ σ = 2 * y := by rw [hy]; ring
      have hexp : y ^ m / (m.factorial : ℝ) ≤ Real.exp y := Real.pow_div_factorial_le_exp y hy0 m
      have hexp' : y ^ m ≤ (m.factorial : ℝ) * Real.exp y := by
        have hf : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
        rw [div_le_iff₀ hf] at hexp
        linarith only [hexp]
      have key : x ^ (b + 2) * Real.exp (-y) ≤ 2 ^ m * (m.factorial : ℝ) := by
        calc x ^ (b + 2) * Real.exp (-y) ≤ (2 * y) ^ m * Real.exp (-y) := by
              refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
              rw [← hxy]; exact hxpow
          _ = 2 ^ m * (y ^ m * Real.exp (-y)) := by rw [mul_pow]; ring
          _ ≤ 2 ^ m * ((m.factorial : ℝ) * Real.exp y * Real.exp (-y)) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              exact mul_le_mul_of_nonneg_right hexp' (Real.exp_pos _).le
          _ = 2 ^ m * (m.factorial : ℝ) := by
              rw [mul_assoc, ← Real.exp_add]; simp
      simpa [hy] using key

/-- The pointwise term bound. -/
theorem poly_mul_exp_le {σ : ℝ} (hσ : 0 < σ) (b : ℝ) (hb : 0 ≤ b) :
    ∃ C₂ : ℝ, 1 ≤ C₂ ∧ ∀ (a : ℝ), 0 < a → ∀ K : ℕ, 1 ≤ K →
      (K : ℝ) ^ b * Real.exp (-((a * K) ^ σ)) ≤
        C₂ * a ^ (-(b + 2)) * ((K : ℝ) ^ 2)⁻¹ * Real.exp (-((a * K) ^ σ / 2)) := by
  obtain ⟨C₂, hC₂, h⟩ := rpow_mul_exp_neg_le hσ b hb
  refine ⟨C₂, hC₂, fun a ha K hK => ?_⟩
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  set x := a * K with hx
  have hx0 : 0 < x := mul_pos ha hK0
  have hxK : (K : ℝ) = x / a := by rw [hx]; field_simp
  have h1 := h x hx0
  have hsplit : Real.exp (-(x ^ σ)) = Real.exp (-(x ^ σ / 2)) * Real.exp (-(x ^ σ / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hxb : x ^ (b + 2) = x ^ b * x ^ (2 : ℝ) := Real.rpow_add hx0 b 2
  have hx2 : x ^ (2 : ℝ) = (K : ℝ) ^ 2 * a ^ 2 := by
    rw [Real.rpow_two, hx]; ring
  have hKb : (K : ℝ) ^ b = x ^ b * a ^ (-b) := by
    rw [hxK, Real.div_rpow hx0.le ha.le, Real.rpow_neg ha.le, div_eq_mul_inv]
  have ha2 : a ^ (-(b + 2)) = a ^ (-b) * (a ^ (2 : ℝ))⁻¹ := by
    rw [Real.rpow_neg ha.le, Real.rpow_add ha, Real.rpow_neg ha.le]
    rw [mul_inv]
  have hpos : 0 < (K : ℝ) ^ 2 * a ^ 2 := by positivity
  have hE : 0 < Real.exp (-(x ^ σ / 2)) := Real.exp_pos _
  have hxb0 : 0 < x ^ b := Real.rpow_pos_of_pos hx0 b
  have hab : 0 < a ^ (-b) := Real.rpow_pos_of_pos ha _
  -- x^b e^{-x^σ/2} ≤ C₂ / x^2
  have h2 : x ^ b * Real.exp (-(x ^ σ / 2)) ≤ C₂ * ((K : ℝ) ^ 2 * a ^ 2)⁻¹ := by
    rw [← hx2]
    have hx2pos : 0 < x ^ (2 : ℝ) := Real.rpow_pos_of_pos hx0 2
    rw [← div_eq_mul_inv, le_div_iff₀ hx2pos]
    calc x ^ b * Real.exp (-(x ^ σ / 2)) * x ^ (2 : ℝ)
        = x ^ (b + 2) * Real.exp (-(x ^ σ / 2)) := by rw [hxb]; ring
      _ ≤ C₂ := h1
  rw [hKb, hsplit, ha2]
  have hrw : (a ^ (2 : ℝ))⁻¹ = (a ^ 2)⁻¹ := by rw [Real.rpow_two]
  rw [hrw]
  calc x ^ b * a ^ (-b) * (Real.exp (-(x ^ σ / 2)) * Real.exp (-(x ^ σ / 2)))
      = a ^ (-b) * (x ^ b * Real.exp (-(x ^ σ / 2))) * Real.exp (-(x ^ σ / 2)) := by ring
    _ ≤ a ^ (-b) * (C₂ * ((K : ℝ) ^ 2 * a ^ 2)⁻¹) * Real.exp (-(x ^ σ / 2)) := by
        gcongr
    _ = C₂ * (a ^ (-b) * (a ^ 2)⁻¹) * ((K : ℝ) ^ 2)⁻¹ * Real.exp (-(x ^ σ / 2)) := by
        rw [mul_inv]; ring

/-- Tail sums of the term bound over `K ≥ m`. -/
theorem sum_tail_le (σ D a : ℝ) (m n : ℕ) (hm : 1 ≤ m)
    (hD : 0 ≤ D) :
    ∑ K ∈ range n, (if m ≤ K then D * ((K : ℝ) ^ 2)⁻¹ * Real.exp (-((a * m) ^ σ / 2)) else 0) ≤
      2 * D * Real.exp (-((a * m) ^ σ / 2)) := by
  have hE : 0 ≤ Real.exp (-((a * m) ^ σ / 2)) := (Real.exp_pos _).le
  have hsub : ∑ K ∈ range n, (if m ≤ K then ((K : ℝ) ^ 2)⁻¹ else 0) ≤ 2 := by
    rw [← Finset.sum_filter]
    have hsub : (range n).filter (fun K => m ≤ K) ⊆ Ioo (m - 1) n := by
      intro K hK
      rw [Finset.mem_filter, Finset.mem_range] at hK
      rw [Finset.mem_Ioo]; omega
    calc ∑ K ∈ (range n).filter (fun K => m ≤ K), ((K : ℝ) ^ 2)⁻¹
        ≤ ∑ K ∈ Ioo (m - 1) n, ((K : ℝ) ^ 2)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ ≤ 2 / (((m - 1 : ℕ) : ℝ) + 1) := sum_Ioo_inv_sq_le (m - 1) n
      _ ≤ 2 := by
          have : (1 : ℝ) ≤ ((m - 1 : ℕ) : ℝ) + 1 := by
            have : (0 : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
            linarith only [this]
          rw [div_le_iff₀ (by linarith only [this])]; linarith only [this]
  calc ∑ K ∈ range n, (if m ≤ K then D * ((K : ℝ) ^ 2)⁻¹ * Real.exp (-((a * m) ^ σ / 2)) else 0)
      = D * Real.exp (-((a * m) ^ σ / 2)) *
          ∑ K ∈ range n, (if m ≤ K then ((K : ℝ) ^ 2)⁻¹ else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun K _ => ?_
        split_ifs <;> ring
    _ ≤ D * Real.exp (-((a * m) ^ σ / 2)) * 2 :=
        mul_le_mul_of_nonneg_left hsub (mul_nonneg hD hE)
    _ = 2 * D * Real.exp (-((a * m) ^ σ / 2)) := by ring

end

end SuperdiffusionCLT.Section7
