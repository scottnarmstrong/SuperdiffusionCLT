/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.BallRescaling
public import SuperdiffusionCLT.Section8.Prereq.ResolventMismatchB

/-!
# Prefactor mismatch and the iteration arithmetic of the exit-time estimate

After rescaling `B_ρ` to `B₁` the field is that of `ε/ρ`, while the prefactor of the operator is
still `opScale cStar ε`; the two differ by the relative factor `|log ρ|/|log ε|`.

* `ballResc_opScale_mismatch`: the ratio of the prefactors;
* `ballResc_abs_log_shift` (`ρ ∈ [1/2, 1]`: change of `|log ε|` by at most `log 2`);
* `ballResc_steps`, `ballResc_iteration`: the number of balls and the geometric decay;
* `ballResc_exit_arith`: with `lam = min (1/t₀) (c₂ |log ε|^α)` the bound
  `P ≤ exp(lam t₀) 2^{-N}`, `N ≥ a √lam - 1`, gives `P ≤ 2 exp(-c min(t₀^{-1/2}, |log ε|^{α/6}))`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization

/-- `|√x - 1| ≤ |x - 1|` for `x ≥ 0`. -/
theorem ballResc_abs_sqrt_sub_one_le {x : ℝ} (hx : 0 ≤ x) : |Real.sqrt x - 1| ≤ |x - 1| := by
  have h1 : x - 1 = (Real.sqrt x - 1) * (Real.sqrt x + 1) := by
    have := Real.sq_sqrt hx
    linear_combination -this
  rw [h1, abs_mul]
  have : 1 ≤ |Real.sqrt x + 1| := by
    rw [abs_of_nonneg (by positivity)]
    linarith only [Real.sqrt_nonneg x]
  nlinarith only [this, abs_nonneg (Real.sqrt x - 1)]

/-- `|log (ε/ρ)| = |log ε| - |log ρ|` for `0 < ε ≤ ρ ≤ 1`. -/
theorem ballResc_abs_log_div {ε ρ : ℝ} (hε : 0 < ε) (hερ : ε ≤ ρ) (hρ : ρ ≤ 1) :
    |Real.log (ε / ρ)| = |Real.log ε| - |Real.log ρ| := by
  have hρ0 : 0 < ρ := lt_of_lt_of_le hε hερ
  have h1 : Real.log ε ≤ 0 := Real.log_nonpos hε.le (hερ.trans hρ)
  have h2 : Real.log ρ ≤ 0 := Real.log_nonpos hρ0.le hρ
  have h3 : Real.log (ε / ρ) ≤ Real.log ε - Real.log ρ + 0 := by
    rw [Real.log_div hε.ne' hρ0.ne']; exact le_of_eq (by ring)
  have h4 : Real.log (ε / ρ) ≤ 0 := Real.log_nonpos (div_pos hε hρ0).le
    ((div_le_one hρ0).mpr hερ)
  rw [abs_of_nonpos h4, abs_of_nonpos h1, abs_of_nonpos h2, Real.log_div hε.ne' hρ0.ne']
  ring

/-- The prefactors `opScale cStar ε` and `opScale cStar (ε/ρ)` of `L^ε` and `L^{ε/ρ}`: after
rescaling `B_ρ` to `B₁` the operator carries the first while `ε/ρ` naturally carries the
second.  Their ratio is `√(|log (ε/ρ)| / |log ε|)`. -/
theorem ballResc_opScale_ratio {cStar ε ρ : ℝ} (hc : 0 < cStar) (hε : 0 < ε) (hερ : ε < ρ)
    (hρ : ρ ≤ 1) :
    opScale cStar ε / opScale cStar (ε / ρ) =
      Real.sqrt (|Real.log (ε / ρ)| / |Real.log ε|) := by
  have hρ0 : 0 < ρ := lt_trans hε hερ
  have hL : 0 < |Real.log ε| := abs_pos.mpr (Real.log_ne_zero_of_pos_of_ne_one hε
    (ne_of_lt (lt_of_lt_of_le hερ hρ)))
  have hL' : 0 < |Real.log (ε / ρ)| := abs_pos.mpr (Real.log_ne_zero_of_pos_of_ne_one
    (div_pos hε hρ0) (ne_of_lt ((div_lt_one hρ0).mpr hερ)))
  unfold opScale
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_div' _ hL.le]
  have h1 : 0 < Real.sqrt (2 * cStar * |Real.log ε|) := Real.sqrt_pos.mpr (by positivity)
  have h2 : 0 < Real.sqrt (2 * cStar * |Real.log (ε / ρ)|) := Real.sqrt_pos.mpr (by positivity)
  have h3 : Real.sqrt (2 * cStar * |Real.log ε|) = Real.sqrt (2 * cStar) * Real.sqrt |Real.log ε| :=
    Real.sqrt_mul (by positivity) _
  have h4 : Real.sqrt (2 * cStar * |Real.log (ε / ρ)|) =
      Real.sqrt (2 * cStar) * Real.sqrt |Real.log (ε / ρ)| := Real.sqrt_mul (by positivity) _
  have h5 : 0 < Real.sqrt (2 * cStar) := Real.sqrt_pos.mpr (by positivity)
  have h6 : 0 < Real.sqrt |Real.log ε| := Real.sqrt_pos.mpr hL
  have h7 : 0 < Real.sqrt |Real.log (ε / ρ)| := Real.sqrt_pos.mpr hL'
  rw [h3, h4]
  field_simp

/-- **The prefactor mismatch**, first form: for `0 < ε < ρ ≤ 1`,
`|√(|log (ε/ρ)| / |log ε|) - 1| ≤ |log ρ| / |log ε|`. -/
theorem ballResc_sqrt_ratio_sub_one {ε ρ : ℝ} (hε : 0 < ε) (hερ : ε < ρ) (hρ : ρ ≤ 1) :
    |Real.sqrt (|Real.log (ε / ρ)| / |Real.log ε|) - 1| ≤ |Real.log ρ| / |Real.log ε| := by
  have hL : 0 < |Real.log ε| := abs_pos.mpr (Real.log_ne_zero_of_pos_of_ne_one hε
    (ne_of_lt (lt_of_lt_of_le hερ hρ)))
  have hρ0 : 0 < ρ := lt_trans hε hερ
  have hl : 0 ≤ |Real.log ρ| := abs_nonneg _
  have h := ballResc_abs_log_div hε hερ.le hρ
  have hx : |Real.log (ε / ρ)| / |Real.log ε| - 1 = -(|Real.log ρ| / |Real.log ε|) := by
    rw [h]; field_simp; ring
  refine (ballResc_abs_sqrt_sub_one_le (by positivity)).trans ?_
  rw [hx, abs_neg, abs_of_nonneg (by positivity)]

/-- The mismatch of the two prefactors: `|opScale ε / opScale (ε/ρ) - 1| ≤ |log ρ|/|log ε|`. -/
theorem ballResc_opScale_mismatch {cStar ε ρ : ℝ} (hc : 0 < cStar) (hε : 0 < ε) (hερ : ε < ρ)
    (hρ : ρ ≤ 1) :
    |opScale cStar ε / opScale cStar (ε / ρ) - 1| ≤ |Real.log ρ| / |Real.log ε| := by
  rw [ballResc_opScale_ratio hc hε hερ hρ]
  exact ballResc_sqrt_ratio_sub_one hε hερ hρ

/-- The estimate used in the proof of `l.decay.estimate.Linfty`: for `ρ ∈ [1/2, 1]` and `ε ≤ 1/2`,
rescaling replaces `|log ε|` by `|log (ε/ρ)|`, a change by at most `log 2`. -/
theorem ballResc_abs_log_shift {ε ρ : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hρ1 : 1 / 2 ≤ ρ)
    (hρ : ρ ≤ 1) : |(|Real.log (ε / ρ)| - |Real.log ε|)| ≤ Real.log 2 := by
  rw [ballResc_abs_log_div hε (hε2.trans hρ1) hρ]
  have h : |Real.log ε| - |Real.log ρ| - |Real.log ε| = -|Real.log ρ| := by ring
  rw [h, abs_neg, abs_abs]
  have hρ0 : 0 < ρ := by linarith only [hρ1]
  rw [abs_of_nonpos (Real.log_nonpos hρ0.le hρ)]
  have : Real.log (1 / 2) ≤ Real.log ρ := Real.log_le_log (by norm_num) hρ1
  rw [one_div, Real.log_inv] at this
  linarith only [this]

/-- Radii of the iteration: `r k = 1/2 + k h`. -/
noncomputable def ballResc_radius (h : ℝ) (k : ℕ) : ℝ := 1 / 2 + k * h

theorem ballResc_radius_succ (h : ℝ) (k : ℕ) :
    ballResc_radius h (k + 1) = ballResc_radius h k + h := by
  unfold ballResc_radius; push_cast; ring

/-- The number of balls: for `0 < h ≤ 1/8` there is `N` with `r N + h ≤ 1`... more precisely
`N h + h ≤ 1/2` (so every ball `B_{r k + h}`, `k ≤ N`, lies in `B_1`) and `1/(4h) - 1 ≤ N`. -/
theorem ballResc_steps {h : ℝ} (hh : 0 < h) (hh8 : h ≤ 1 / 8) :
    ∃ N : ℕ, (N : ℝ) * h + h ≤ 1 / 2 ∧ 1 / (4 * h) - 1 ≤ N := by
  refine ⟨⌊1 / (4 * h)⌋₊, ?_, ?_⟩
  · have h1 : (⌊1 / (4 * h)⌋₊ : ℝ) ≤ 1 / (4 * h) := Nat.floor_le (by positivity)
    have h2 : (⌊1 / (4 * h)⌋₊ : ℝ) * h ≤ 1 / 4 := by
      calc (⌊1 / (4 * h)⌋₊ : ℝ) * h ≤ 1 / (4 * h) * h := mul_le_mul_of_nonneg_right h1 hh.le
        _ = 1 / 4 := by field_simp
    linarith only [h2, hh8]
  · have := Nat.lt_floor_add_one (1 / (4 * h))
    linarith only [this]

/-- From a bound `P ≤ 2 e exp(-B)` and `P ≤ 1`, `P ≤ 2 exp(-B/3)`. -/
theorem ballResc_two_exp {P B : ℝ} (hP1 : P ≤ 1) (hP : P ≤ 2 * Real.exp 1 * Real.exp (-B)) : P ≤ 2 * Real.exp (-(B / 3)) := by
  by_cases hcase : 3 / 2 ≤ B
  · refine hP.trans ?_
    have h1 : Real.exp 1 * Real.exp (-B) ≤ Real.exp (-(B / 3)) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith only [hcase])
    calc 2 * Real.exp 1 * Real.exp (-B) = 2 * (Real.exp 1 * Real.exp (-B)) := by ring
      _ ≤ 2 * Real.exp (-(B / 3)) := by linarith only [h1]
  · push Not at hcase
    refine hP1.trans ?_
    have h1 : -(B / 3) + 1 ≤ Real.exp (-(B / 3)) := Real.add_one_le_exp _
    linarith only [h1, hcase]

/-- The exponent comparison `κ m ≤ √lam` for `lam = min (1/t₀) (c₂ L^α)`, where
`m = min (t₀^{-1/2}) (L^{α/6})`, `L ≥ log 2` and `κ = min 1 (√c₂) (log 2)^{α/3}`. -/
theorem ballResc_sqrt_lambda_ge {t₀ L α c₂ : ℝ} (ht : 0 < t₀) (hL : Real.log 2 ≤ L) (hα : 0 < α)
    (hc₂ : 0 < c₂) :
    min 1 (Real.sqrt c₂) * Real.log 2 ^ (α / 3) *
        min (t₀ ^ (-(1 / 2 : ℝ))) (L ^ (α / 6)) ≤
      Real.sqrt (min (1 / t₀) (c₂ * L ^ α)) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2one : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9; linarith only [this]
  have hL0 : 0 < L := lt_of_lt_of_le hl2 hL
  set m := min (t₀ ^ (-(1 / 2 : ℝ))) (L ^ (α / 6)) with hm
  set κ₀ := min 1 (Real.sqrt c₂) with hκ₀
  have hm0 : 0 ≤ m := le_min (Real.rpow_nonneg ht.le _) (Real.rpow_nonneg hL0.le _)
  have hκ₀0 : 0 ≤ κ₀ := le_min zero_le_one (Real.sqrt_nonneg _)
  have hp : Real.log 2 ^ (α / 3) ≤ 1 := Real.rpow_le_one hl2.le hl2one (by positivity)
  have hp0 : 0 ≤ Real.log 2 ^ (α / 3) := Real.rpow_nonneg hl2.le _
  have hκ : κ₀ * Real.log 2 ^ (α / 3) ≤ 1 := by
    calc κ₀ * Real.log 2 ^ (α / 3) ≤ 1 * 1 :=
          mul_le_mul (min_le_left _ _) hp hp0 zero_le_one
      _ = 1 := by ring
  apply Real.le_sqrt_of_sq_le
  refine le_min ?_ ?_
  · have h1 : κ₀ * Real.log 2 ^ (α / 3) * m ≤ t₀ ^ (-(1 / 2 : ℝ)) := by
      calc κ₀ * Real.log 2 ^ (α / 3) * m ≤ 1 * m :=
            mul_le_mul_of_nonneg_right hκ hm0
        _ ≤ t₀ ^ (-(1 / 2 : ℝ)) := by rw [one_mul]; exact min_le_left _ _
    have h2 : (t₀ ^ (-(1 / 2 : ℝ))) ^ 2 = 1 / t₀ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
      norm_num
      rw [Real.rpow_neg_one]
    rw [← h2]
    exact pow_le_pow_left₀ (by positivity) h1 2
  · have hLa : Real.log 2 ^ (α / 3) ≤ L ^ (α / 3) :=
      Real.rpow_le_rpow hl2.le hL (by positivity)
    have hsplit : L ^ (α / 2) = L ^ (α / 3) * L ^ (α / 6) := by
      rw [← Real.rpow_add hL0]; congr 1; ring
    have h1 : κ₀ * Real.log 2 ^ (α / 3) * m ≤ Real.sqrt c₂ * L ^ (α / 2) := by
      rw [hsplit]
      have a1 : κ₀ ≤ Real.sqrt c₂ := min_le_right _ _
      have a2 : m ≤ L ^ (α / 6) := min_le_right _ _
      calc κ₀ * Real.log 2 ^ (α / 3) * m ≤ Real.sqrt c₂ * L ^ (α / 3) * L ^ (α / 6) := by
            refine mul_le_mul (mul_le_mul a1 hLa hp0 (Real.sqrt_nonneg _)) a2 hm0 (by positivity)
        _ = Real.sqrt c₂ * (L ^ (α / 3) * L ^ (α / 6)) := by ring
    have h2 : (Real.sqrt c₂ * L ^ (α / 2)) ^ 2 = c₂ * L ^ α := by
      rw [mul_pow, Real.sq_sqrt hc₂.le, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
      congr 2
      push_cast; ring
    rw [← h2]
    exact pow_le_pow_left₀ (by positivity) h1 2

/-- **The final arithmetic of the exit-time lemma.**  Let `lam = min (1/t₀) (c₂ L^α)`
(`L = |log ε| ≥ log 2`).  If a probability `P` satisfies the Chebyshev-and-iteration bound
`P ≤ exp(lam t₀) exp(-N log 2)` with `N ≥ a √lam - 1` balls, then
`P ≤ 2 exp(-c min (t₀^{-1/2}) (L^{α/6}))`, `c = (a log 2 / 3) min 1 (√c₂) (log 2)^{α/3}`. -/
theorem ballResc_exit_arith {t₀ L α c₂ a P : ℝ} {N : ℕ} (ht : 0 < t₀) (hL : Real.log 2 ≤ L)
    (hα : 0 < α) (hc₂ : 0 < c₂) (ha : 0 < a) (hP1 : P ≤ 1)
    (hN : a * Real.sqrt (min (1 / t₀) (c₂ * L ^ α)) - 1 ≤ N)
    (hP : P ≤ Real.exp (min (1 / t₀) (c₂ * L ^ α) * t₀) * Real.exp (-(N * Real.log 2))) :
    P ≤ 2 * Real.exp (-((a * Real.log 2 * (min 1 (Real.sqrt c₂) * Real.log 2 ^ (α / 3)) / 3) *
      min (t₀ ^ (-(1 / 2 : ℝ))) (L ^ (α / 6)))) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set lam := min (1 / t₀) (c₂ * L ^ α) with hlam
  set κ := min 1 (Real.sqrt c₂) * Real.log 2 ^ (α / 3) with hκ
  set m := min (t₀ ^ (-(1 / 2 : ℝ))) (L ^ (α / 6)) with hm
  have hge : κ * m ≤ Real.sqrt lam := ballResc_sqrt_lambda_ge ht hL hα hc₂
  have h1 : lam * t₀ ≤ 1 := by
    have : lam ≤ 1 / t₀ := min_le_left _ _
    calc lam * t₀ ≤ 1 / t₀ * t₀ := mul_le_mul_of_nonneg_right this ht.le
      _ = 1 := by field_simp
  have h2 : -(N * Real.log 2) ≤ Real.log 2 - a * Real.log 2 * (κ * m) := by
    have h3 : a * (κ * m) ≤ a * Real.sqrt lam := mul_le_mul_of_nonneg_left hge ha.le
    have h4 : (a * Real.sqrt lam - 1) * Real.log 2 ≤ N * Real.log 2 :=
      mul_le_mul_of_nonneg_right hN hl2.le
    have h5 : a * Real.log 2 * (κ * m) ≤ a * Real.sqrt lam * Real.log 2 := by
      calc a * Real.log 2 * (κ * m) = (a * (κ * m)) * Real.log 2 := by ring
        _ ≤ (a * Real.sqrt lam) * Real.log 2 := mul_le_mul_of_nonneg_right h3 hl2.le
    linarith only [h4, h5]
  have hmain : P ≤ 2 * Real.exp 1 * Real.exp (-(a * Real.log 2 * (κ * m))) := by
    refine hP.trans ?_
    have e1 : Real.exp (lam * t₀) ≤ Real.exp 1 := Real.exp_le_exp.mpr h1
    have e2 : Real.exp (-(N * Real.log 2)) ≤ 2 * Real.exp (-(a * Real.log 2 * (κ * m))) := by
      calc Real.exp (-(N * Real.log 2)) ≤ Real.exp (Real.log 2 - a * Real.log 2 * (κ * m)) :=
            Real.exp_le_exp.mpr h2
        _ = 2 * Real.exp (-(a * Real.log 2 * (κ * m))) := by
          rw [sub_eq_add_neg, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    calc Real.exp (lam * t₀) * Real.exp (-(N * Real.log 2))
        ≤ Real.exp 1 * (2 * Real.exp (-(a * Real.log 2 * (κ * m)))) :=
          mul_le_mul e1 e2 (Real.exp_pos _).le (Real.exp_pos _).le
      _ = 2 * Real.exp 1 * Real.exp (-(a * Real.log 2 * (κ * m))) := by ring
  have := ballResc_two_exp hP1 hmain
  convert this using 3
  ring

/-- With `h = C₁/√lam` the number of balls `1/(4h) - 1` is `a √lam - 1`, `a = 1/(4 C₁)`. -/
theorem ballResc_inv_four_h {C₁ lam : ℝ} (hC : 0 < C₁) (hlam : 0 < lam) :
    1 / (4 * (C₁ / Real.sqrt lam)) = (1 / (4 * C₁)) * Real.sqrt lam := by
  have : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  field_simp

/-- **The iteration over balls, deterministic part.**  `M r` is the supremum over `B_r` of the
profile `v ≤ 1`.  If one step reads `M r ≤ q M (r + h)` for `1/2 ≤ r ≤ 1 - h` with `q ≤ 1/2`, then
`M (1/2) ≤ exp(-N log 2)` with at least `1/(4h) - 1` steps. -/
theorem ballResc_iteration {h q : ℝ} (hh : 0 < h) (hh8 : h ≤ 1 / 8) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2)
    (M : ℝ → ℝ) (hM1 : ∀ r, M r ≤ 1)
    (hstep : ∀ r, 1 / 2 ≤ r → r + h ≤ 1 → M r ≤ q * M (r + h)) :
    ∃ N : ℕ, 1 / (4 * h) - 1 ≤ N ∧ M (1 / 2) ≤ Real.exp (-(N * Real.log 2)) := by
  obtain ⟨N, hN1, hN2⟩ := ballResc_steps hh hh8
  refine ⟨N, hN2, ?_⟩
  have hchain := resMis_chain hq0 N (fun k => M (ballResc_radius h k))
    (fun k hk => by
      have hr : 1 / 2 ≤ ballResc_radius h k := by
        unfold ballResc_radius
        have : 0 ≤ (k : ℝ) * h := by positivity
        linarith only [this]
      have hk' : (k : ℝ) + 1 ≤ N := by exact_mod_cast hk
      have hle : ballResc_radius h k + h ≤ 1 := by
        unfold ballResc_radius
        have : ((k : ℝ) + 1) * h ≤ N * h := mul_le_mul_of_nonneg_right hk' hh.le
        linarith only [this, hN1, hh]
      have := hstep _ hr hle
      rw [← ballResc_radius_succ] at this
      exact this) (hM1 _)
  have h0 : ballResc_radius h 0 = 1 / 2 := by simp [ballResc_radius]
  simp only [h0] at hchain
  exact hchain.trans (resMis_pow_half_le hq0 hq N)

/-- Witness for the final arithmetic: `t₀ = 1`, `L = 1`, `α = 1/2`, `c₂ = a = 1`, `N = 0`, `P = 0`. -/
example : (0 : ℝ) ≤ 2 * Real.exp (-((1 * Real.log 2 * (min 1 (Real.sqrt 1) * Real.log 2 ^ ((1 / 2 : ℝ) / 3)) / 3) *
      min ((1 : ℝ) ^ (-(1 / 2 : ℝ))) ((1 : ℝ) ^ ((1 / 2 : ℝ) / 6)))) :=
  ballResc_exit_arith (N := 0) (c₂ := 1) (a := 1) (P := 0) one_pos
    (by have := Real.log_two_lt_d9; linarith only [this]) (by norm_num) one_pos one_pos
    zero_le_one (by simp) (by simp [Real.exp_nonneg])

/-- Witness for the iteration: the constant profile `M = 0`... a nonzero one, `M r = 1/2`-valued
is excluded by the step; the profile `M r = 0` satisfies all hypotheses. -/
example : ∃ N : ℕ, 1 / (4 * (1 / 8 : ℝ)) - 1 ≤ N ∧ (fun _ : ℝ => (0 : ℝ)) (1 / 2) ≤
    Real.exp (-(N * Real.log 2)) :=
  ballResc_iteration (h := 1 / 8) (q := 1 / 2) (by norm_num) le_rfl (by norm_num) le_rfl
    (fun _ => 0) (fun _ => zero_le_one) (fun r _ _ => by simp)

/-- Witness for the prefactor mismatch: `c⋆ = 1`, `ε = 1/4`, `ρ = 1/2`. -/
example : |opScale 1 (1 / 4 : ℝ) / opScale 1 ((1 / 4 : ℝ) / (1 / 2)) - 1| ≤
    |Real.log (1 / 2 : ℝ)| / |Real.log (1 / 4 : ℝ)| :=
  ballResc_opScale_mismatch one_pos (by norm_num) (by norm_num) (by norm_num)

/-- Witness for the ball rescaling: the heat field `a = Id`, `u = 1`, `f = 1`, `lam = 1`, `s = 1`
on `B₂`, rescaled to `B₁`. -/
example : ∀ x ∈ SuperdiffusionCLT.Section6.euclidBall (d := 2) 1,
    ((1 : ℝ) * 2 ^ 2) * (fun _ : Vec 2 => (1 : ℝ)) ((2 : ℝ) • x) -
      divForm 1 (fun y => (fun (_ : Vec 2) (i j : Fin 2) => if i = j then (1 : ℝ) else 0)
        ((1 / (2 : ℝ))⁻¹ • y)) (fun y => (fun _ : Vec 2 => (1 : ℝ)) ((2 : ℝ) • y)) x =
      2 ^ 2 * (fun _ : Vec 2 => (1 : ℝ)) ((2 : ℝ) • x) := by
  have h := (ballResc_equation_iff (d := 2) (by norm_num : (0 : ℝ) < 2) 1 1 1
    (fun (_ : Vec 2) (i j : Fin 2) => if i = j then (1 : ℝ) else 0)
    (fun _ => 1) (fun _ => 1)).mp (fun x _ => by simp [divForm])
  simpa using h

end SuperdiffusionCLT.Section8
