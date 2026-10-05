/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics


/-!
# Threshold chain `N₀ … N₆` of the proof of `p.one.step.sharp`

Pure real-variable lemmas, each of the form `∃ N, ∀ n ≥ N, …` with the constants fixed first.
`κ` is the paper's `nondegconst`, `c₃ = c⋆ log 3`, `s` stands for `σ̄_n`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

theorem threshold_log_le_rpow (a b G : ℝ) (hb : 0 < b) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → G * Real.log (n : ℝ) ^ a ≤ (n : ℝ) ^ b := by
  have ho := isLittleO_log_rpow_rpow_atTop a hb
  have hev := ho.def' (show (0 : ℝ) < 1 / (|G| + 1) by positivity)
  have hev' := tendsto_natCast_atTop_atTop (R := ℝ) |>.eventually
    hev.bound
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev'
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  have hnb : 0 ≤ (n : ℝ) ^ b := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnb] at h1
  have hG : G * Real.log n ^ a ≤ |G| * |Real.log n ^ a| :=
    (le_abs_self _).trans (by rw [abs_mul])
  have hG1 : 0 < |G| + 1 := by positivity
  have h3 : |Real.log n ^ a| * (|G| + 1) ≤ (n : ℝ) ^ b := by
    have := mul_le_mul_of_nonneg_right h1 hG1.le
    calc _ ≤ _ := this
      _ = (n : ℝ) ^ b := by field_simp
  nlinarith only [hG, h3, abs_nonneg (Real.log (n : ℝ) ^ a), abs_nonneg G]

/-- `log(ν⁻¹ n) ≤ 2 log n` once `n ≥ ν⁻¹`. -/
theorem log_inv_mul_le {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1) {n : ℝ} (hn : nu⁻¹ ≤ n) :
    Real.log (nu⁻¹ * n) ≤ 2 * Real.log n := by
  have h1 : 1 ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
  have hn0 : 0 < n := lt_of_lt_of_le (by linarith only [h1]) hn
  rw [Real.log_mul (by positivity) hn0.ne']
  have := Real.log_le_log (by positivity) hn
  linarith only [this]

/-- Absorption conditions of Steps 1-2: below the lower bracket, `s ≥ G` and `log²n+κ ≤ s²`. -/
theorem threshold_bracket_lower (A G κ : ℝ) (hA : 0 < A) (hκ : 0 ≤ κ) :
    ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ s : ℝ,
      A⁻¹ * (n : ℝ) ^ (1 / 2 : ℝ) * Real.log (n : ℝ) ^ (-(9 / 2 : ℝ)) ≤ s →
        G ≤ s ∧ Real.log (n : ℝ) ^ 2 + κ ≤ s ^ 2 := by
  obtain ⟨N1, h1⟩ := threshold_log_le_rpow (9 / 2) (1 / 2) (A * |G|) (by norm_num)
  obtain ⟨N2, h2⟩ := threshold_log_le_rpow 11 1 ((1 + κ) * A ^ 2) (by norm_num)
  refine ⟨max 3 (max N1 N2), le_max_left _ _, fun n hn s hs => ?_⟩
  have hn3 : 3 ≤ n := le_trans (le_max_left _ _) hn
  have hn1 := h1 n (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn)
  have hn2 := h2 n (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn)
  have hn3r : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hn0 : (0 : ℝ) < n := by linarith only [hn3r]
  set u := Real.log (n : ℝ) with hu
  have hu1 : 1 ≤ u := by
    have : Real.log 3 ≤ u := Real.log_le_log (by norm_num) hn3r
    have h3 : 1 < Real.log 3 := by
      have := Real.exp_one_lt_d9
      rw [Real.lt_log_iff_exp_lt (by norm_num)]; linarith only [this]
    linarith only [this, h3]
  have hu0 : 0 < u := by linarith only [hu1]
  set w := (n : ℝ) ^ (1 / 2 : ℝ) with hw
  have hw0 : 0 < w := by positivity
  have hw2 : w ^ 2 = n := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; norm_num
  set v := u ^ (9 / 2 : ℝ) with hv
  have hv0 : 0 < v := by positivity
  have hv2 : v ^ 2 = u ^ 9 := by
    rw [hv, ← Real.rpow_natCast, ← Real.rpow_mul hu0.le]; norm_num
  have hvn : u ^ (-(9 / 2 : ℝ)) = v⁻¹ := by rw [Real.rpow_neg hu0.le]
  rw [hvn] at hs
  have hAv : A * |G| * v ≤ w := by simpa [mul_comm] using hn1
  have ht : A⁻¹ * w * v⁻¹ = w / (A * v) := by field_simp
  rw [ht] at hs
  have hAv0 : 0 < A * v := by positivity
  have hs1 : G ≤ s := by
    have : |G| ≤ w / (A * v) := by
      rw [le_div_iff₀ hAv0]; nlinarith only [hAv, abs_nonneg G, hA, hv0]
    exact le_trans (le_abs_self G) (le_trans this hs)
  refine ⟨hs1, ?_⟩
  have hs0 : 0 ≤ w / (A * v) := by positivity
  have hsq : (w / (A * v)) ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hs0 hs 2
  have h11 : (1 + κ) * A ^ 2 * u ^ (11 : ℝ) ≤ (n : ℝ) ^ (1 : ℝ) := hn2
  rw [Real.rpow_one] at h11
  have h11' : (1 + κ) * A ^ 2 * u ^ 11 ≤ n := by
    have : u ^ (11 : ℝ) = u ^ 11 := by rw [← Real.rpow_natCast]; norm_num
    rwa [this] at h11
  have key : (u ^ 2 + κ) ≤ (w / (A * v)) ^ 2 := by
    rw [div_pow, le_div_iff₀ (by positivity), mul_pow, hv2, hw2]
    have hu9 : 0 ≤ u ^ 9 := by positivity
    have h5 : (u ^ 2 + κ) * u ^ 9 ≤ (1 + κ) * u ^ 11 := by
      have : κ * u ^ 9 ≤ κ * u ^ 11 := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hu1 (by norm_num)) hκ
      nlinarith only [this]
    calc (u ^ 2 + κ) * (A ^ 2 * u ^ 9) = A ^ 2 * ((u ^ 2 + κ) * u ^ 9) := by ring
      _ ≤ A ^ 2 * ((1 + κ) * u ^ 11) := mul_le_mul_of_nonneg_left h5 (by positivity)
      _ = (1 + κ) * A ^ 2 * u ^ 11 := by ring
      _ ≤ n := h11'
  linarith only [key, hsq]

/-- Step 2: below the upper bracket, `s ≤ n`. -/
theorem threshold_bracket_upper (A : ℝ) :
    ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ s : ℝ,
      s ≤ A * (n : ℝ) ^ (1 / 2 : ℝ) * Real.log (n : ℝ) ^ (9 / 2 : ℝ) → s ≤ n := by
  obtain ⟨N1, h1⟩ := threshold_log_le_rpow (9 / 2) (1 / 2) A (by norm_num)
  refine ⟨max 3 N1, le_max_left _ _, fun n hn s hs => ?_⟩
  have hn1 := h1 n (le_trans (le_max_right _ _) hn)
  have hn0 : (0 : ℝ) < n := by
    have : 3 ≤ n := le_trans (le_max_left _ _) hn
    exact_mod_cast (by omega : 0 < n)
  have hw2 : ((n : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; norm_num
  have hw0 : 0 ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by positivity
  calc s ≤ _ := hs
    _ = (n : ℝ) ^ (1 / 2 : ℝ) * (A * Real.log (n : ℝ) ^ (9 / 2 : ℝ)) := by ring
    _ ≤ (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) := mul_le_mul_of_nonneg_left hn1 hw0
    _ = n := by rw [← sq, hw2]

/-- Steps 4 and 6 (`N₃`, `N₆`): a fixed constant is eventually absorbed by `G (log²n+κ) n^{1/2}`
(`G > 0`). -/
theorem threshold_const_absorbed (B G κ : ℝ) (hG : 0 < G) (hκ : 0 ≤ κ) :
    ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      B ≤ G * (Real.log (n : ℝ) ^ 2 + κ) * (n : ℝ) ^ (1 / 2 : ℝ) := by
  obtain ⟨N1, h1⟩ := threshold_log_le_rpow 0 (1 / 2) (|B| / G) (by norm_num)
  refine ⟨max 3 N1, le_max_left _ _, fun n hn => ?_⟩
  have hn1 := h1 n (le_trans (le_max_right _ _) hn)
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_left _ _) hn
  have hu1 : 1 ≤ Real.log (n : ℝ) := by
    have : Real.log 3 ≤ Real.log n := Real.log_le_log (by norm_num) hn3
    have h3 : 1 < Real.log 3 := by
      have := Real.exp_one_lt_d9
      rw [Real.lt_log_iff_exp_lt (by norm_num)]; linarith only [this]
    linarith only [this, h3]
  rw [Real.rpow_zero, mul_one] at hn1
  have hw0 : 0 ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by positivity
  have hB : |B| ≤ G * (n : ℝ) ^ (1 / 2 : ℝ) := by
    rwa [div_le_iff₀ hG, mul_comm] at hn1
  have : 1 ≤ Real.log (n : ℝ) ^ 2 + κ := by nlinarith only [hu1, hκ]
  calc B ≤ |B| := le_abs_self B
    _ ≤ G * (n : ℝ) ^ (1 / 2 : ℝ) := hB
    _ = G * 1 * (n : ℝ) ^ (1 / 2 : ℝ) := by ring
    _ ≤ G * (Real.log (n : ℝ) ^ 2 + κ) * (n : ℝ) ^ (1 / 2 : ℝ) := by
      gcongr

/-- Step 5 (`N₄`): `G (log²n+κ) n^{1/2} log^{9/2} n ≤ c₃ n` eventually (`c₃ > 0`). -/
theorem threshold_coarse (G κ c₃ : ℝ) (hc : 0 < c₃) (hκ : 0 ≤ κ) :
    ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      G * (Real.log (n : ℝ) ^ 2 + κ) * (n : ℝ) ^ (1 / 2 : ℝ) * Real.log (n : ℝ) ^ (9 / 2 : ℝ) ≤
        c₃ * n := by
  obtain ⟨N1, h1⟩ := threshold_log_le_rpow (13 / 2) (1 / 2) (|G| * (1 + κ) / c₃) (by norm_num)
  refine ⟨max 3 N1, le_max_left _ _, fun n hn => ?_⟩
  have hn1 := h1 n (le_trans (le_max_right _ _) hn)
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_left _ _) hn
  have hn0 : (0 : ℝ) < n := by linarith only [hn3]
  have hu1 : 1 ≤ Real.log (n : ℝ) := by
    have : Real.log 3 ≤ Real.log n := Real.log_le_log (by norm_num) hn3
    have h3 : 1 < Real.log 3 := by
      have := Real.exp_one_lt_d9
      rw [Real.lt_log_iff_exp_lt (by norm_num)]; linarith only [this]
    linarith only [this, h3]
  set u := Real.log (n : ℝ)
  set w := (n : ℝ) ^ (1 / 2 : ℝ) with hw
  have hw0 : 0 < w := by positivity
  have hw2 : w ^ 2 = n := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; norm_num
  have hu0 : 0 < u := by linarith only [hu1]
  have hp : u ^ (13 / 2 : ℝ) = u ^ 2 * u ^ (9 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hu0]; norm_num
  have hp0 : 0 < u ^ (9 / 2 : ℝ) := by positivity
  have hk : u ^ 2 + κ ≤ (1 + κ) * u ^ 2 := by
    nlinarith only [mul_nonneg hκ (by nlinarith only [hu1] : (0 : ℝ) ≤ u ^ 2 - 1)]
  rw [div_mul_eq_mul_div, div_le_iff₀ hc] at hn1
  have hn1' : |G| * (1 + κ) * (u ^ 2 * u ^ (9 / 2 : ℝ)) ≤ w * c₃ := by
    rw [← hp]; linarith only [hn1]
  calc G * (u ^ 2 + κ) * w * u ^ (9 / 2 : ℝ)
      ≤ |G| * ((1 + κ) * u ^ 2) * w * u ^ (9 / 2 : ℝ) := by
        have : G ≤ |G| := le_abs_self G
        have h0 : 0 ≤ u ^ 2 + κ := by positivity
        have : G * (u ^ 2 + κ) ≤ |G| * ((1 + κ) * u ^ 2) :=
          mul_le_mul this hk h0 (abs_nonneg G)
        gcongr
    _ = w * (|G| * (1 + κ) * (u ^ 2 * u ^ (9 / 2 : ℝ))) := by ring
    _ ≤ w * (w * c₃) := mul_le_mul_of_nonneg_left hn1' hw0.le
    _ = c₃ * n := by rw [← hw2]; ring

/-- Step 1 algebra: with `s ≥ 1`, `0 ≤ h ≤ s`, `1 ≤ Λ ≤ s²`, `0 ≤ c₃ ≤ 3` and
`|δ| ≤ R Λ / s`, the square of `s + c₃ h / s + δ` is within `(9 + 8R + R²) Λ` of `s² + 2 c₃ h`. -/
theorem square_increment_alg {s h δ c₃ Λ R : ℝ} (hs : 1 ≤ s) (h0 : 0 ≤ h) (hhs : h ≤ s)
    (hΛ1 : 1 ≤ Λ) (hΛs : Λ ≤ s ^ 2) (hc0 : 0 ≤ c₃) (hc3 : c₃ ≤ 3) (hR : 0 ≤ R)
    (hδ : |δ| ≤ R * Λ / s) :
    |(s + c₃ * s⁻¹ * h + δ) ^ 2 - s ^ 2 - 2 * c₃ * h| ≤ (9 + 8 * R + R ^ 2) * Λ := by
  have hs0 : 0 < s := by linarith only [hs]
  have hsq : (s + c₃ * s⁻¹ * h + δ) ^ 2 - s ^ 2 - 2 * c₃ * h =
      c₃ ^ 2 * h ^ 2 * (s ^ 2)⁻¹ + 2 * s * δ + 2 * c₃ * s⁻¹ * h * δ + δ ^ 2 := by
    field_simp; ring
  have hδ' : |δ| * s ≤ R * Λ := by rwa [le_div_iff₀ hs0] at hδ
  have hδ1 : |δ| ≤ R * Λ := by nlinarith only [hδ', abs_nonneg δ, hs]
  have hhs' : h * s⁻¹ ≤ 1 := by rw [← div_eq_mul_inv, div_le_one hs0]; exact hhs
  have hhs0 : 0 ≤ h * s⁻¹ := by positivity
  have t1 : |c₃ ^ 2 * h ^ 2 * (s ^ 2)⁻¹| ≤ 9 * Λ := by
    have : c₃ ^ 2 * h ^ 2 * (s ^ 2)⁻¹ = c₃ ^ 2 * (h * s⁻¹) ^ 2 := by field_simp
    rw [this, abs_of_nonneg (by positivity)]
    have : (h * s⁻¹) ^ 2 ≤ 1 := by nlinarith only [hhs', hhs0]
    have : c₃ ^ 2 ≤ 9 := by nlinarith only [hc0, hc3]
    nlinarith only [this, ‹(h * s⁻¹) ^ 2 ≤ 1›, sq_nonneg (h * s⁻¹), sq_nonneg c₃, hΛ1]
  have t2 : |2 * s * δ| ≤ 2 * R * Λ := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * s)]
    nlinarith only [hδ', hs0]
  have t3 : |2 * c₃ * s⁻¹ * h * δ| ≤ 6 * R * Λ := by
    have : 2 * c₃ * s⁻¹ * h * δ = (2 * c₃ * (h * s⁻¹)) * δ := by ring
    rw [this, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * c₃ * (h * s⁻¹))]
    have : 2 * c₃ * (h * s⁻¹) ≤ 6 := by nlinarith only [hc3, hhs', hhs0, hc0]
    have hRΛ : 0 ≤ R * Λ := by positivity
    nlinarith only [this, hδ1, abs_nonneg δ]
  have t4 : δ ^ 2 ≤ R ^ 2 * Λ := by
    have : δ ^ 2 = |δ| ^ 2 := (sq_abs δ).symm
    have h2 : |δ| ^ 2 ≤ (R * Λ / s) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hδ 2
    have h3 : (R * Λ / s) ^ 2 ≤ R ^ 2 * Λ := by
      rw [div_pow, div_le_iff₀ (by positivity)]
      nlinarith only [hΛs, hR, hΛ1, mul_nonneg (sq_nonneg R) (by linarith only [hΛ1] : (0 : ℝ) ≤ Λ)]
    linarith only [this, h2, h3]
  rw [hsq]
  have := abs_add_le (c₃ ^ 2 * h ^ 2 * (s ^ 2)⁻¹ + 2 * s * δ + 2 * c₃ * s⁻¹ * h * δ) (δ ^ 2)
  have := abs_add_le (c₃ ^ 2 * h ^ 2 * (s ^ 2)⁻¹ + 2 * s * δ) (2 * c₃ * s⁻¹ * h * δ)
  have := abs_add_le (c₃ ^ 2 * h ^ 2 * (s ^ 2)⁻¹) (2 * s * δ)
  have h4 : |δ ^ 2| ≤ R ^ 2 * Λ := by rw [abs_of_nonneg (sq_nonneg δ)]; exact t4
  linarith only [this, ‹_ ≤ _ + |δ ^ 2|›, t1, t2, t3, h4, ‹|_ + 2 * c₃ * s⁻¹ * h * δ| ≤ _›]

/-- Step 6 (`N₅`): with `λ = ½ (c⋆ log 3)^{1/2}` and `0 < c⋆ ≤ 2`, we have `λ ≤ 1`, and
`n ≥ max 1 (λ⁻²) c⋆` gives the three conditions of `e.theorem.N5.cond`. -/
theorem threshold_N5 {cStar : ℝ} (hc : 0 < cStar) (hc2 : cStar ≤ 2) :
    (1 / 2 * (cStar * Real.log 3) ^ (1 / 2 : ℝ)) ≤ 1 ∧
    ∀ n : ℝ, max 1 (max ((1 / 2 * (cStar * Real.log 3) ^ (1 / 2 : ℝ)) ⁻¹ ^ 2) cStar) ≤ n →
      1 ≤ (1 / 2 * (cStar * Real.log 3) ^ (1 / 2 : ℝ)) * n ^ (1 / 2 : ℝ) ∧
      (1 / 2 * (cStar * Real.log 3) ^ (1 / 2 : ℝ)) * n ^ (1 / 2 : ℝ) ≤ n ∧
      1 ≤ cStar ^ (-(1 / 2 : ℝ)) * n ^ (1 / 2 : ℝ) := by
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hl32 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith only [this]
  set lam := 1 / 2 * (cStar * Real.log 3) ^ (1 / 2 : ℝ) with hlam
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  have hlam1 : lam ≤ 1 := by
    have h4 : (cStar * Real.log 3) ^ (1 / 2 : ℝ) ≤ 2 := by
      rw [← Real.sqrt_eq_rpow]
      apply Real.sqrt_le_iff.2
      constructor <;> nlinarith only [hc, hc2, hl3, hl32]
    rw [hlam]; linarith only [h4]
  refine ⟨hlam1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : lam⁻¹ ^ 2 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn3 : cStar ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hn0 : 0 < n := by linarith only [hn1]
  have hw2 : (n ^ (1 / 2 : ℝ)) ^ 2 = n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; norm_num
  have hw0 : 0 < n ^ (1 / 2 : ℝ) := by positivity
  have hw1 : 1 ≤ n ^ (1 / 2 : ℝ) := Real.one_le_rpow hn1 (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · have : lam⁻¹ ≤ n ^ (1 / 2 : ℝ) := by
      by_contra hcon
      push Not at hcon
      have := pow_lt_pow_left₀ hcon hw0.le (two_ne_zero)
      rw [hw2] at this; linarith only [this, hn2]
    rw [inv_le_iff_one_le_mul₀ hlam0] at this
    linarith only [this]
  · calc lam * n ^ (1 / 2 : ℝ) ≤ 1 * n ^ (1 / 2 : ℝ) := mul_le_mul_of_nonneg_right hlam1 hw0.le
      _ ≤ n ^ (1 / 2 : ℝ) * n ^ (1 / 2 : ℝ) := by nlinarith only [hw1, hw0]
      _ = n := by rw [← sq, hw2]
  · have hc12 : cStar ^ (-(1 / 2 : ℝ)) * n ^ (1 / 2 : ℝ) = (n / cStar) ^ (1 / 2 : ℝ) := by
      rw [Real.div_rpow hn0.le hc.le, Real.rpow_neg hc.le]; ring
    rw [hc12]
    exact Real.one_le_rpow ((one_le_div hc).2 hn3) (by norm_num)

/-! ## Satisfiability: the smallest admissible parameters `c⋆ = 2`, `ν = 1`, `κ = 0`, `A = 1`. -/

example : ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ s : ℝ,
    (1 : ℝ)⁻¹ * (n : ℝ) ^ (1 / 2 : ℝ) * Real.log (n : ℝ) ^ (-(9 / 2 : ℝ)) ≤ s →
      2 ≤ s ∧ Real.log (n : ℝ) ^ 2 + 0 ≤ s ^ 2 :=
  threshold_bracket_lower 1 2 0 one_pos le_rfl

example : ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    (1 : ℝ) * (Real.log (n : ℝ) ^ 2 + 0) * (n : ℝ) ^ (1 / 2 : ℝ) * Real.log (n : ℝ) ^ (9 / 2 : ℝ) ≤
      2 * Real.log 3 * n :=
  threshold_coarse 1 0 (2 * Real.log 3) (by positivity [Real.log_pos (show (1 : ℝ) < 3 by norm_num)]) le_rfl

example : (1 / 2 * ((2 : ℝ) * Real.log 3) ^ (1 / 2 : ℝ)) ≤ 1 :=
  (threshold_N5 (by norm_num : (0 : ℝ) < 2) le_rfl).1

example : ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    (5 : ℝ) ≤ 1 * (Real.log (n : ℝ) ^ 2 + 0) * (n : ℝ) ^ (1 / 2 : ℝ) :=
  threshold_const_absorbed 5 1 0 one_pos le_rfl

example : |((1 : ℝ) + 2 * Real.log 3 * 1⁻¹ * 1 + 0) ^ 2 - 1 ^ 2 - 2 * (2 * Real.log 3) * 1| ≤
    (9 + 8 * 0 + 0 ^ 2) * 1 := by
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h32 : Real.log 3 ≤ 3 / 2 := by
    have he := Real.exp_one_gt_d9
    have h1 : Real.log (3 / Real.exp 1) ≤ 3 / Real.exp 1 - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by norm_num) (Real.exp_pos 1).ne', Real.log_exp] at h1
    have h2 : 3 / Real.exp 1 ≤ 3 / 2 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num); linarith only [he]
    linarith only [h1, h2]
  refine square_increment_alg (δ := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by positivity) (by linarith only [h32]) le_rfl (by simp)

end SuperdiffusionCLT.Section5
