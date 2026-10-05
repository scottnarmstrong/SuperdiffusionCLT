/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.RootArithOneScaleC

/-!
# `hOneScale`'s union-bound inequality: abstract real-variable lemmas

In the proof of `p.minimal.scales`
(`e.new.mixing.minscale.one.scale`), this file proves the
purely real-variable steps behind the finite union bound: the size of the
counting prefactor, the combination of the two Gaussian-type tails, the lower
bound of the squared `Γ₂` ratio, and a lower bound for `L₀`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

open SuperdiffusionCLT.Section4.LNaught
open SuperdiffusionCLT.Section4.NewMixing
open SuperdiffusionCLT.Frozen.Section4 (lNaught)

noncomputable section

/-! ## The counting prefactor -/

/-- `3 ^ n = exp (n log 3)`. -/
theorem srootD_three_pow_eq (n : ℕ) : (3 : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log 3) := by
  rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]

/-- `log 3 ≤ 2`. -/
theorem srootD_log_three_le_two : Real.log 3 ≤ 2 := by
  have h := srootA_four_log3_lt_eight
  linarith only [h]

/-- The prefactor of the finite union bound is at most `exp (7 (1 + 2d) K ℓ)`. -/
theorem srootD_prefactor_le (d : ℕ) {K l : ℝ} (hK : 1 ≤ K) (hl : 1 ≤ l) :
    (((⌈K * l⌉₊ : ℝ) + 1) * (2 * (3 : ℝ) ^ (⌈K * l⌉₊ + 3) + 1) ^ d) ≤
      Real.exp (7 * (1 + 2 * (d : ℝ)) * (K * l)) := by
  have hKl : 1 ≤ K * l := by nlinarith only [hK, hl]
  set h : ℕ := ⌈K * l⌉₊ with hh
  have hhle : (h : ℝ) ≤ K * l + 1 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ K * l by linarith only [hKl])
    exact this.le
  have hlog3 : Real.log 3 ≤ 2 := srootD_log_three_le_two
  have h1 : ((h : ℝ) + 1) ≤ Real.exp (h : ℝ) := Real.add_one_le_exp _
  have h3h : (1 : ℝ) ≤ (3 : ℝ) ^ h := one_le_pow₀ (by norm_num)
  have h2 : 2 * (3 : ℝ) ^ (h + 3) + 1 ≤ (3 : ℝ) ^ (h + 5) := by
    rw [pow_add, pow_add]
    nlinarith only [h3h]
  have h3 : (3 : ℝ) ^ (h + 5) ≤ Real.exp (2 * ((h : ℝ) + 5)) := by
    rw [srootD_three_pow_eq]
    apply Real.exp_le_exp.2
    push_cast
    have : (0 : ℝ) ≤ (h : ℝ) + 5 := by positivity
    nlinarith only [hlog3, this]
  have h4 : (2 * (3 : ℝ) ^ (h + 3) + 1) ^ d ≤ Real.exp (2 * ((h : ℝ) + 5)) ^ d :=
    pow_le_pow_left₀ (by positivity) (le_trans h2 h3) d
  have h5 : Real.exp (2 * ((h : ℝ) + 5)) ^ d = Real.exp ((d : ℝ) * (2 * ((h : ℝ) + 5))) := by
    rw [← Real.exp_nat_mul]
  have h6 : ((h : ℝ) + 1) * (2 * (3 : ℝ) ^ (h + 3) + 1) ^ d ≤
      Real.exp (h : ℝ) * Real.exp ((d : ℝ) * (2 * ((h : ℝ) + 5))) := by
    rw [← h5]
    exact mul_le_mul h1 h4 (by positivity) (Real.exp_pos _).le
  rw [← Real.exp_add] at h6
  refine le_trans h6 (Real.exp_le_exp.2 ?_)
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hh5 : (h : ℝ) + 5 ≤ 7 * (K * l) := by linarith only [hhle, hKl]
  have hh0 : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
  nlinarith only [hh5, hd0, hh0]

/-! ## Combining the two tails -/

/-- One tail against the target: `P e^{-X} ≤ ½ m^{-2} e^{-W}` once
`(14 d + 10) K ℓ + W ≤ X`. -/
theorem srootD_one_tail (d : ℕ) {K l W X m : ℝ} (hK : 1 ≤ K) (hl : 1 ≤ l) (hm : 0 < m)
    (hlm : l = Real.log m)
    (hX : (14 * (d : ℝ) + 10) * (K * l) + W ≤ X) :
    (((⌈K * l⌉₊ : ℝ) + 1) * (2 * (3 : ℝ) ^ (⌈K * l⌉₊ + 3) + 1) ^ d) * Real.exp (-X) ≤
      (1 / 2) * (((m ^ 2)⁻¹) * Real.exp (-W)) := by
  have hKl : 1 ≤ K * l := by nlinarith only [hK, hl]
  have hP := srootD_prefactor_le d hK hl
  have hlK : l ≤ K * l := by nlinarith only [hK, hl]
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9
    linarith only [this]
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hmsq : (m ^ 2)⁻¹ = Real.exp (-(2 * l)) := by
    have h2 : Real.exp (2 * Real.log m) = m ^ 2 := by
      have := Real.exp_nat_mul (Real.log m) 2
      rw [Real.exp_log hm] at this
      rw [← this]; norm_num
    rw [hlm, Real.exp_neg, h2]
  have hhalf : (1 / 2 : ℝ) = Real.exp (-Real.log 2) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have hrhs : (1 / 2 : ℝ) * (((m ^ 2)⁻¹) * Real.exp (-W)) =
      Real.exp (-Real.log 2 + (-(2 * l)) + (-W)) := by
    rw [hmsq, hhalf, Real.exp_add, Real.exp_add]
    ring
  rw [hrhs]
  calc (((⌈K * l⌉₊ : ℝ) + 1) * (2 * (3 : ℝ) ^ (⌈K * l⌉₊ + 3) + 1) ^ d) * Real.exp (-X)
      ≤ Real.exp (7 * (1 + 2 * (d : ℝ)) * (K * l)) * Real.exp (-X) :=
        mul_le_mul_of_nonneg_right hP (Real.exp_pos _).le
    _ = Real.exp (7 * (1 + 2 * (d : ℝ)) * (K * l) + -X) := by rw [Real.exp_add]
    _ ≤ Real.exp (-Real.log 2 + (-(2 * l)) + (-W)) := by
        apply Real.exp_le_exp.2
        nlinarith only [hX, hlK, hlog2, hd0, hKl]

/-- The finite union bound's arithmetic: both tails are below the target. -/
theorem srootD_union_bound (d : ℕ) {K l W X1 X2 m : ℝ} (hK : 1 ≤ K) (hl : 1 ≤ l) (hm : 0 < m)
    (hlm : l = Real.log m)
    (hX1 : (14 * (d : ℝ) + 10) * (K * l) + W ≤ X1)
    (hX2 : (14 * (d : ℝ) + 10) * (K * l) + W ≤ X2) :
    (((⌈K * l⌉₊ : ℝ) + 1) * (2 * (3 : ℝ) ^ (⌈K * l⌉₊ + 3) + 1) ^ d) *
        (Real.exp (-X1) + Real.exp (-X2)) ≤ ((m ^ 2)⁻¹) * Real.exp (-W) := by
  have h1 := srootD_one_tail d hK hl hm hlm hX1
  have h2 := srootD_one_tail d hK hl hm hlm hX2
  rw [mul_add]
  linarith only [h1, h2]

/-! ## The squared `Γ₂` ratio -/

/-- Two lower bounds for `T₁² = (r D / (2 CE a))²`, where `r² = ℓ` and `a² = K u²`. -/
theorem srootD_T1sq {r l CE a D K u C M Y Q delta : ℝ} (hr0 : 0 < r) (hrr : r * r = l)
    (hCE : 1 ≤ CE) (haa : a * a = K * u ^ 2) (hK : K = C * M * u)
    (hC : 1 ≤ C) (hM : 1 ≤ M) (hu : 1 ≤ u) (hY : 0 ≤ Y) (hdQ : 0 ≤ delta * Q)
    (hD1 : (C / 6) * (u ^ 4 * M ^ 2) * Y ≤ D) (hD2 : (2 / 3) * (delta * Q) ≤ D) :
    K * l * Y ^ 2 ≤ 144 * CE ^ 2 * ((r * D / (2 * CE * a)) ^ 2) ∧
    delta ^ 2 * Q ^ 2 * l ≤ 9 * CE ^ 2 * K * u ^ 2 * ((r * D / (2 * CE * a)) ^ 2) := by
  have hCEpos : 0 < CE := lt_of_lt_of_le one_pos hCE
  have hCpos : 0 < C := lt_of_lt_of_le one_pos hC
  have hMpos : 0 < M := lt_of_lt_of_le one_pos hM
  have hupos : 0 < u := lt_of_lt_of_le one_pos hu
  have hKpos : 0 < K := by rw [hK]; positivity
  have hl0 : 0 ≤ l := by rw [← hrr]; positivity
  have hP : 0 < 4 * CE ^ 2 * (K * u ^ 2) := by positivity
  have hX : (r * D / (2 * CE * a)) ^ 2 = l * D ^ 2 / (4 * CE ^ 2 * (K * u ^ 2)) := by
    have ha2 : a ^ 2 = K * u ^ 2 := by rw [sq]; exact haa
    have hr2 : r ^ 2 = l := by rw [sq]; exact hrr
    rw [div_pow, mul_pow, mul_pow, ha2, hr2]
    ring
  have hKuY : K * u * Y ≤ 6 * D := by
    have h1 : K * u = C * M * u ^ 2 := by rw [hK]; ring
    have hu2 : u ^ 2 ≤ u ^ 4 := pow_le_pow_right₀ hu (by norm_num)
    have hM1 : M ≤ M ^ 2 := by nlinarith only [hM]
    have h2 : C * M * u ^ 2 ≤ C * (u ^ 4 * M ^ 2) := by
      have h0 : M * u ^ 2 ≤ M ^ 2 * u ^ 4 :=
        mul_le_mul hM1 hu2 (by positivity) (by positivity)
      have : M * u ^ 2 ≤ u ^ 4 * M ^ 2 := by linarith only [h0]
      nlinarith only [this, hCpos]
    have h3 : C * M * u ^ 2 * Y ≤ C * (u ^ 4 * M ^ 2) * Y := mul_le_mul_of_nonneg_right h2 hY
    rw [h1]
    linarith only [h3, hD1]
  have hKuY0 : 0 ≤ K * u * Y := by positivity
  have hsq1 : (K * u * Y) ^ 2 ≤ (6 * D) ^ 2 := pow_le_pow_left₀ hKuY0 hKuY 2
  have hD0 : 0 ≤ (3 / 2) * D := by nlinarith only [hD2, hdQ]
  have hsq2 : (delta * Q) ^ 2 ≤ ((3 / 2) * D) ^ 2 := by
    have : delta * Q ≤ (3 / 2) * D := by linarith only [hD2]
    exact pow_le_pow_left₀ hdQ this 2
  rw [hX]
  constructor
  · rw [mul_div_assoc', le_div_iff₀ hP]
    have h5 : 0 ≤ 4 * CE ^ 2 * l := by positivity
    have := mul_le_mul_of_nonneg_left hsq1 h5
    nlinarith only [this]
  · rw [mul_div_assoc', le_div_iff₀ hP]
    have h5 : 0 ≤ 4 * CE ^ 2 * l * (K * u ^ 2) := by positivity
    have := mul_le_mul_of_nonneg_left hsq2 h5
    nlinarith only [this]

/-- The first tail exponent dominates `n K ℓ + W`. -/
theorem srootD_X1_ge {n K l W X Q Y CE Lh2 delta u : ℝ} (hCE : 1 ≤ CE) (hl : 1 ≤ l)
    (hK : 0 < K) (hW0 : 0 ≤ W) (hdelta : 0 < delta) (hu : 0 < u)
    (hA : K * l * Y ^ 2 ≤ 144 * CE ^ 2 * X)
    (hB : delta ^ 2 * Q ^ 2 * l ≤ 9 * CE ^ 2 * K * u ^ 2 * X)
    (hY : 288 * n * CE ^ 2 ≤ Y ^ 2)
    (hWL : W * Lh2 ≤ 4 * Q ^ 2) (hL : 72 * CE ^ 2 * K * u ^ 2 ≤ Lh2 * delta ^ 2) :
    n * (K * l) + W ≤ X := by
  have hCEpos : 0 < CE := lt_of_lt_of_le one_pos hCE
  have hKl : 0 ≤ K * l := by positivity
  have h1 : 2 * n * (K * l) ≤ X := by
    have h144 : (0 : ℝ) < 144 * CE ^ 2 := by positivity
    have : 144 * CE ^ 2 * (2 * n * (K * l)) ≤ 144 * CE ^ 2 * X := by
      have h2 := mul_le_mul_of_nonneg_left hY hKl
      nlinarith only [h2, hA]
    exact le_of_mul_le_mul_left this h144
  have h2 : W ≤ X / 2 := by
    have hP : (0 : ℝ) < 72 * CE ^ 2 * K * u ^ 2 := by positivity
    have hQ2 : delta ^ 2 * Q ^ 2 ≤ delta ^ 2 * Q ^ 2 * l := by
      have : 0 ≤ delta ^ 2 * Q ^ 2 := by positivity
      nlinarith only [this, hl]
    have hstep1 : W * (72 * CE ^ 2 * K * u ^ 2) ≤ W * (Lh2 * delta ^ 2) :=
      mul_le_mul_of_nonneg_left hL hW0
    have hstep2 : W * (Lh2 * delta ^ 2) ≤ 4 * Q ^ 2 * delta ^ 2 := by
      have := mul_le_mul_of_nonneg_right hWL (sq_nonneg delta)
      nlinarith only [this]
    have hstep3 : 4 * Q ^ 2 * delta ^ 2 ≤ 36 * CE ^ 2 * K * u ^ 2 * X := by
      nlinarith only [hQ2, hB]
    have : W * (72 * CE ^ 2 * K * u ^ 2) ≤ (X / 2) * (72 * CE ^ 2 * K * u ^ 2) := by
      nlinarith only [hstep1, hstep2, hstep3]
    exact le_of_mul_le_mul_right this hP
  linarith only [h1, h2]

/-! ## Elementary bounds -/

/-- `2 ≤ expon⁻¹ delta^{-1} nu^{-4}`. -/
theorem srootD_slack_two {expon delta nu : ℝ}
    (hexp0 : 0 < expon) (hexp1 : expon < 1 / 2) (hdel0 : 0 < delta) (hdel1 : delta ≤ 1)
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) :
    (2 : ℝ) ≤ expon⁻¹ * delta ^ (-(1 : ℝ)) * nu ^ (-(4 : ℝ)) := by
  have hexpinv : (2 : ℝ) ≤ expon⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hexp0]; linarith only [hexp1]
  have hd : (1 : ℝ) ≤ delta ^ (-(1 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hdel0 hdel1
      (show (-(1 : ℝ)) ≤ (0 : ℝ) by norm_num)
    rwa [Real.rpow_zero] at h
  have hn : (1 : ℝ) ≤ nu ^ (-(4 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hnu hnu1
      (show (-(4 : ℝ)) ≤ (0 : ℝ) by norm_num)
    rwa [Real.rpow_zero] at h
  calc (2 : ℝ) = 2 * 1 * 1 := by norm_num
    _ ≤ expon⁻¹ * delta ^ (-(1 : ℝ)) * nu ^ (-(4 : ℝ)) := by gcongr

/-- `delta m^expon ≥ (C/4) s^{-4} M² (log m)^{12}`, from the `R'` bound. -/
theorem srootD_bound_Y {C expon delta s M nu l Q : ℝ}
    (hC : 0 ≤ C) (hs0 : 0 < s) (hM0 : 0 ≤ M) (hl0 : 0 ≤ l)
    (hslack : (2 : ℝ) ≤ expon⁻¹ * delta ^ (-(1 : ℝ)) * nu ^ (-(4 : ℝ)))
    (hR : (C / 8) * expon⁻¹ * delta ^ (-(1 : ℝ)) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ) *
        nu ^ (-(4 : ℝ)) * l ^ (12 : ℝ) ≤ delta * Q) :
    (C / 4) * (s ^ (-(4 : ℝ)) * M ^ (2 : ℝ)) * l ^ (12 : ℝ) ≤ delta * Q := by
  have hX_nn : (0 : ℝ) ≤ (C / 8) * (s ^ (-(4 : ℝ)) * M ^ (2 : ℝ)) * l ^ (12 : ℝ) := by
    have h1 : 0 ≤ s ^ (-(4 : ℝ)) := Real.rpow_nonneg hs0.le _
    have h2 : 0 ≤ M ^ (2 : ℝ) := Real.rpow_nonneg hM0 _
    have h3 : 0 ≤ l ^ (12 : ℝ) := Real.rpow_nonneg hl0 _
    positivity
  have hchain : (C / 4) * (s ^ (-(4 : ℝ)) * M ^ (2 : ℝ)) * l ^ (12 : ℝ) ≤
      (C / 8) * expon⁻¹ * delta ^ (-(1 : ℝ)) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ) *
        nu ^ (-(4 : ℝ)) * l ^ (12 : ℝ) := by
    have heq1 : (C / 8) * expon⁻¹ * delta ^ (-(1 : ℝ)) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ) *
        nu ^ (-(4 : ℝ)) * l ^ (12 : ℝ) =
        ((C / 8) * (s ^ (-(4 : ℝ)) * M ^ (2 : ℝ)) * l ^ (12 : ℝ)) *
          (expon⁻¹ * delta ^ (-(1 : ℝ)) * nu ^ (-(4 : ℝ))) := by ring
    have heq2 : (C / 4) * (s ^ (-(4 : ℝ)) * M ^ (2 : ℝ)) * l ^ (12 : ℝ) =
        ((C / 8) * (s ^ (-(4 : ℝ)) * M ^ (2 : ℝ)) * l ^ (12 : ℝ)) * 2 := by ring
    rw [heq1, heq2]
    exact mul_le_mul_of_nonneg_left hslack hX_nn
  linarith only [hchain, hR]

/-! ## A lower bound for `L₀` and the size of the `L̂₂`-tail -/

/-- `lNaughtInner ≥ (C M / 8) (log 2)^12`. -/
theorem srootD_inner_ge {C M alpha cStar nu K : ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hK : 0 ≤ K) (hcStar : 0 < cStar) (hcStar2 : cStar ≤ 2)
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hα0 : 0 ≤ alpha) (halpha : alpha < 1) :
    (C * M / 8) * (Real.log 2) ^ (12 : ℝ) ≤ lNaughtInner C M alpha cStar nu K := by
  have h1ma_pos : (0 : ℝ) < 1 - alpha := one_minus_alpha_pos halpha
  unfold lNaughtInner
  have hcpow : (1 : ℝ) / 8 ≤ cStar ^ (-(3 : ℝ)) := newMixParam_cStar_neg3_ge hcStar hcStar2
  have hcpow_nn : (0 : ℝ) ≤ cStar ^ (-(3 : ℝ)) := le_trans (by norm_num) hcpow
  have hnum : C * M / 8 ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) := by
    have h1 : C * M ≤ C * (M + 1 + K) := mul_le_mul_of_nonneg_left (by linarith only [hK]) hC
    have h2 : C * (M + 1 + K) * ((1 : ℝ) / 8) ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) :=
      mul_le_mul_of_nonneg_left hcpow (mul_nonneg hC (by linarith only [hM, hK]))
    linarith only [h1, h2]
  have hdenle1 : (1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ) ≤ 1 := by
    have h1 : (1 - alpha) ^ (12 : ℝ) ≤ 1 := by
      calc (1 - alpha) ^ (12 : ℝ) ≤ (1 : ℝ) ^ (12 : ℝ) :=
            Real.rpow_le_rpow h1ma_pos.le (by linarith only [hα0]) (by norm_num)
        _ = 1 := Real.one_rpow _
    have h2 : nu ^ (4 : ℝ) ≤ 1 := by
      calc nu ^ (4 : ℝ) ≤ (1 : ℝ) ^ (4 : ℝ) := Real.rpow_le_rpow hnu.le hnu1 (by norm_num)
        _ = 1 := Real.one_rpow _
    have h1nn : (0 : ℝ) ≤ (1 - alpha) ^ (12 : ℝ) := Real.rpow_nonneg h1ma_pos.le _
    have h2nn : (0 : ℝ) ≤ nu ^ (4 : ℝ) := Real.rpow_nonneg hnu.le _
    calc (1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ) ≤ 1 * nu ^ (4 : ℝ) :=
          mul_le_mul_of_nonneg_right h1 h2nn
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = 1 := by ring
  have hdenpos : (0 : ℝ) < (1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ) := denom_pos hnu halpha
  have hnumnn : (0 : ℝ) ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) :=
    mul_nonneg (mul_nonneg hC (by linarith only [hM, hK])) hcpow_nn
  have hfrac : C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) ≤
      C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) := by
    calc C * (M + 1 + K) * cStar ^ (-(3 : ℝ))
        = C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / 1 := by ring
      _ ≤ _ := div_le_div_of_nonneg_left hnumnn hdenpos hdenle1
  have hlogarg : (2 : ℝ) ≤ 2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha)) :=
    log_arg_ge_two hM hK hcStar hnu halpha
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogmono : Real.log 2 ≤
      Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) :=
    Real.log_le_log (by norm_num) hlogarg
  have hlogpow : (Real.log 2) ^ (12 : ℝ) ≤
      Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) :=
    Real.rpow_le_rpow hlog2.le hlogmono (by norm_num)
  have hfracnn : (0 : ℝ) ≤
      C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) :=
    div_nonneg hnumnn hdenpos.le
  have hlog2pow12nn : (0 : ℝ) ≤ (Real.log 2) ^ (12 : ℝ) := Real.rpow_nonneg hlog2.le _
  calc (C * M / 8) * (Real.log 2) ^ (12 : ℝ)
      ≤ (C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ))) *
          (Real.log 2) ^ (12 : ℝ) :=
        mul_le_mul_of_nonneg_right (le_trans hnum hfrac) hlog2pow12nn
    _ ≤ _ := mul_le_mul_of_nonneg_left hlogpow hfracnn

/-- `(log 2)^12 ≥ 1/4096`. -/
theorem srootD_log2_pow_ge : (1 : ℝ) / 4096 ≤ (Real.log 2) ^ (12 : ℝ) := by
  have h : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith only [this]
  have h2 : ((1 : ℝ) / 2) ^ (12 : ℝ) ≤ (Real.log 2) ^ (12 : ℝ) :=
    Real.rpow_le_rpow (by norm_num) h (by norm_num)
  have h3 : ((1 : ℝ) / 2) ^ (12 : ℝ) = 1 / 4096 := by
    rw [show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  linarith only [h2, h3]

/-- The `expon`-th power of `L̂₂` is at least `(C M' / 8) (log 2)^12`, `M'` the
`M`-slot of its first `L₀` term. -/
theorem srootD_Lhat2_rpow_ge {C expon delta s M cStar nu nondeg : ℝ}
    (hC : 0 ≤ C) (hexp0 : 0 < expon) (hexp1 : expon < 1 / 2) (hdel0 : 0 < delta)
    (hs0 : 0 < s) (hM0 : 0 ≤ M) (hcStar : 0 < cStar) (hcStar2 : cStar ≤ 2)
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hnondeg : 0 < nondeg) :
    (C * (C * expon⁻¹ * delta ^ (-(2 : ℝ)) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ)) / 8) *
        (Real.log 2) ^ (12 : ℝ) ≤
      srootMS_Lhat2 C expon delta s M cStar nu nondeg ^ expon := by
  set M' := C * expon⁻¹ * delta ^ (-(2 : ℝ)) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ) with hM'
  have hM'0 : 0 ≤ M' := by rw [hM']; positivity
  have hα1 : (1 - expon) < 1 := by linarith only [hexp0]
  have hα0 : (0 : ℝ) ≤ 1 - expon := by linarith only [hexp1]
  have hL1nn : 0 ≤ lNaught C M' (1 - expon) cStar nu nondeg := by
    rw [newMixParam_lNaught_eq_inner_rpow]
    exact Real.rpow_nonneg (inner_nonneg hC hM'0 hnondeg.le hcStar hnu hα1) _
  have hle : lNaught C M' (1 - expon) cStar nu nondeg ≤
      srootMS_Lhat2 C expon delta s M cStar nu nondeg := by
    unfold srootMS_Lhat2; exact le_max_left _ _
  have h1 := Real.rpow_le_rpow hL1nn hle hexp0.le
  have h2 := lNaught_rpow_eq_inner (C := C) (M := M') (alpha := 1 - expon) (cStar := cStar)
    (nu := nu) (K := nondeg) hC hM'0 hnondeg.le hcStar hnu hα1
  rw [show (1 : ℝ) - (1 - expon) = expon by ring] at h2
  have h3 := srootD_inner_ge (C := C) (M := M') (alpha := 1 - expon) (cStar := cStar)
    (nu := nu) (K := nondeg) hC hM'0 hnondeg.le hcStar hcStar2 hnu hnu1 hα0 hα1
  linarith only [h1, h2, h3]

/-- Dividing out `L̂₂`: `W · L̂₂^{2ρ} ≤ 4 (m^ρ)²`. -/
theorem srootD_W_mul_le {expon Lh m : ℝ} (hexp1 : expon < 1 / 2)
    (hLh : 0 < Lh) (hm : 0 < m) :
    (2 * Real.log 3 * m / Lh) ^ (2 * expon) * Lh ^ (2 * expon) ≤ 4 * (m ^ expon) ^ 2 := by
  have hlog3 : (1 : ℝ) < Real.log 3 :=
    SuperdiffusionCLT.Section2.Estimates.Stream.one_lt_log_three
  have hlog3le : Real.log 3 ≤ 2 := srootD_log_three_le_two
  have hb1 : (1 : ℝ) ≤ 2 * Real.log 3 := by linarith only [hlog3]
  have hbm : (0 : ℝ) ≤ 2 * Real.log 3 := by linarith only [hlog3]
  have hdiv : (2 * Real.log 3 * m / Lh) ^ (2 * expon) =
      (2 * Real.log 3) ^ (2 * expon) * m ^ (2 * expon) / Lh ^ (2 * expon) := by
    rw [Real.div_rpow (by positivity) hLh.le, Real.mul_rpow hbm hm.le]
  have hLpos : 0 < Lh ^ (2 * expon) := Real.rpow_pos_of_pos hLh _
  have hbpow : (2 * Real.log 3) ^ (2 * expon) ≤ 4 := by
    have h := Real.rpow_le_rpow_of_exponent_le hb1 (show 2 * expon ≤ 1 by linarith only [hexp1])
    rw [Real.rpow_one] at h
    linarith only [h, hlog3le]
  have hmQ : m ^ (2 * expon) = (m ^ expon) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm.le]
    norm_num
    ring_nf
  rw [hdiv, div_mul_cancel₀ _ hLpos.ne', hmQ]
  exact mul_le_mul_of_nonneg_right hbpow (by positivity)

/-- `(2 log 3 m / L̂₂)^{2ρ} ≤ m` once `4 log 3 ≤ L̂₂ ≤ m`. -/
theorem srootD_W_le_m {expon Lh m : ℝ} (hexp0 : 0 < expon) (hexp1 : expon < 1 / 2)
    (hLh : 4 * Real.log 3 ≤ Lh) (hLm : Lh ≤ m) :
    (2 * Real.log 3 * m / Lh) ^ (2 * expon) ≤ m := by
  have hlog3 : (1 : ℝ) < Real.log 3 :=
    SuperdiffusionCLT.Section2.Estimates.Stream.one_lt_log_three
  have hLpos : 0 < Lh := by linarith only [hLh, hlog3]
  have hm1 : (1 : ℝ) ≤ m := by linarith only [hLh, hLm, hlog3]
  have hx : 2 * Real.log 3 * m / Lh ≤ m := by
    rw [div_le_iff₀ hLpos]
    nlinarith only [hLh, hm1, hlog3]
  have hx0 : 0 ≤ 2 * Real.log 3 * m / Lh := by positivity
  by_cases h1 : 2 * Real.log 3 * m / Lh ≤ 1
  · have := Real.rpow_le_one hx0 h1 (show 0 ≤ 2 * expon by linarith only [hexp0])
    linarith only [this, hm1]
  · have h1' : 1 < 2 * Real.log 3 * m / Lh := not_le.mp h1
    have h := Real.rpow_le_rpow_of_exponent_le h1'.le
      (show 2 * expon ≤ 1 by linarith only [hexp1])
    rw [Real.rpow_one] at h
    linarith only [h, hx]

/-! ## The second tail -/

/-- `T₂ ≥ m^{999}`. -/
theorem srootD_T2_ge {CE C Cg nu sig Dl l : ℝ} {m : ℕ}
    (hCE1 : 1 ≤ CE) (hCg1 : 1 ≤ Cg) (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hsig0 : 0 < sig)
    (hm1 : 1 ≤ (m : ℝ)) (hl : 1 ≤ l) (hsigle : sig ≤ Cg * nu⁻¹ * (1 + (m : ℝ)))
    (hC24 : 24 * Cg * CE ≤ C) (hD : (C / 6) * nu ^ (-(4 : ℝ)) ≤ Dl) :
    (m : ℝ) ^ 999 ≤ (sig⁻¹ * l * Dl) / (2 * (CE * (m : ℝ) ^ (-(1000 : ℝ)))) := by
  have hCEpos : 0 < CE := lt_of_lt_of_le one_pos hCE1
  have hCgpos : 0 < Cg := lt_of_lt_of_le one_pos hCg1
  have hmpos : 0 < (m : ℝ) := lt_of_lt_of_le one_pos hm1
  have hCpos : 0 < C := by nlinarith only [hC24, hCEpos, hCgpos, mul_pos hCgpos hCEpos]
  have hnegpow : (m : ℝ) ^ (-(1000 : ℝ)) = ((m : ℝ) ^ 1000)⁻¹ := by
    rw [Real.rpow_neg hmpos.le, show (1000 : ℝ) = ((1000 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hm1000 : 0 < (m : ℝ) ^ 1000 := by positivity
  have hsiginv_ge : nu / (2 * Cg * (m : ℝ)) ≤ sig⁻¹ :=
    srootA2_siginv_ge hCg1 hnu hsig0 hm1 hsigle
  have hDnn : 0 ≤ Dl := le_trans (by positivity) hD
  have hnup : nu * nu ^ (-(4 : ℝ)) = nu ^ (-(3 : ℝ)) := by
    nth_rewrite 1 [← Real.rpow_one nu]
    rw [← Real.rpow_add hnu]; norm_num
  have hnu3ge1 : (1 : ℝ) ≤ nu ^ (-(3 : ℝ)) := by
    have h1 : nu ^ (3 : ℝ) ≤ 1 := by
      calc nu ^ (3 : ℝ) ≤ (1 : ℝ) ^ (3 : ℝ) := Real.rpow_le_rpow hnu.le hnu1 (by norm_num)
        _ = 1 := Real.one_rpow _
    have h2 : (0 : ℝ) < nu ^ (3 : ℝ) := Real.rpow_pos_of_pos hnu _
    rw [Real.rpow_neg hnu.le]
    exact (one_le_inv₀ h2).2 h1
  -- `2 CE ≤ sig⁻¹ m Dl`
  have hkey : 2 * CE ≤ sig⁻¹ * (m : ℝ) * Dl := by
    have h1 : nu / (2 * Cg * (m : ℝ)) * (m : ℝ) * ((C / 6) * nu ^ (-(4 : ℝ))) ≤
        sig⁻¹ * (m : ℝ) * Dl := by
      have ha : nu / (2 * Cg * (m : ℝ)) * (m : ℝ) ≤ sig⁻¹ * (m : ℝ) :=
        mul_le_mul_of_nonneg_right hsiginv_ge hmpos.le
      have ha0 : 0 ≤ nu / (2 * Cg * (m : ℝ)) * (m : ℝ) := by positivity
      exact mul_le_mul ha hD (by positivity) (by positivity)
    have h2 : nu / (2 * Cg * (m : ℝ)) * (m : ℝ) * ((C / 6) * nu ^ (-(4 : ℝ))) =
        C / (12 * Cg) * nu ^ (-(3 : ℝ)) := by
      rw [← hnup]
      field_simp
      ring
    have h3 : 2 * CE ≤ C / (12 * Cg) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith only [hC24]
    have h4 : C / (12 * Cg) ≤ C / (12 * Cg) * nu ^ (-(3 : ℝ)) := by
      have : 0 ≤ C / (12 * Cg) := by positivity
      nlinarith only [this, hnu3ge1]
    linarith only [h1, h2, h3, h4]
  have hkey2 : 2 * CE ≤ l * (sig⁻¹ * (m : ℝ) * Dl) := by
    have : 0 ≤ sig⁻¹ * (m : ℝ) * Dl := by positivity
    nlinarith only [hkey, hl, this]
  rw [hnegpow, le_div_iff₀ (by positivity)]
  have h5 : (m : ℝ) ^ 999 * (2 * (CE * ((m : ℝ) ^ 1000)⁻¹)) = 2 * CE * ((m : ℝ) ^ 999 * ((m : ℝ) ^ 1000)⁻¹) := by ring
  have h6 : (m : ℝ) ^ 999 * ((m : ℝ) ^ 1000)⁻¹ = (m : ℝ)⁻¹ := by
    field_simp
  have h7 : sig⁻¹ * l * Dl = (sig⁻¹ * (m : ℝ) * Dl) * l * (m : ℝ)⁻¹ := by
    field_simp
  rw [h5, h6]
  have hm0 : 0 < (m : ℝ)⁻¹ := inv_pos.2 hmpos
  have : 2 * CE * (m : ℝ)⁻¹ ≤ l * (sig⁻¹ * (m : ℝ) * Dl) * (m : ℝ)⁻¹ :=
    mul_le_mul_of_nonneg_right hkey2 hm0.le
  calc 2 * CE * (m : ℝ)⁻¹ ≤ l * (sig⁻¹ * (m : ℝ) * Dl) * (m : ℝ)⁻¹ := this
    _ = sig⁻¹ * l * Dl := by rw [h7]; ring

/-- The second tail exponent dominates `n K ℓ + W`. -/
theorem srootD_X2_ge {n K l W T m : ℝ} (hn : 0 ≤ n) (hl1 : 1 ≤ l)
    (hKm : K ≤ m) (hlm : l ≤ m) (hWm : W ≤ m) (hnm : n + 1 ≤ m)
    (hT : m ^ 999 ≤ T) :
    n * (K * l) + W ≤ T ^ ((2 : ℝ) / 3) := by
  have hm1 : (1 : ℝ) ≤ m := by linarith only [hnm, hn]
  have hm0 : 0 ≤ m := by linarith only [hm1]
  have hpow : m ^ (666 : ℕ) ≤ T ^ ((2 : ℝ) / 3) := by
    have h1 : (m ^ 999) ^ ((2 : ℝ) / 3) ≤ T ^ ((2 : ℝ) / 3) :=
      Real.rpow_le_rpow (by positivity) hT (by norm_num)
    have h2 : (m ^ 999) ^ ((2 : ℝ) / 3) = m ^ (666 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hm0, ← Real.rpow_natCast]
      norm_num
    linarith only [h1, h2]
  have h3 : m ^ 3 ≤ m ^ (666 : ℕ) := pow_le_pow_right₀ hm1 (by norm_num)
  have hKl : K * l ≤ m * m := mul_le_mul hKm hlm (by linarith only [hl1]) hm0
  have hmm : m ≤ m * m := by nlinarith only [hm1]
  have h4 : n * (K * l) ≤ n * (m * m) := mul_le_mul_of_nonneg_left hKl hn
  have h5 : (n + 1) * (m * m) ≤ m * (m * m) :=
    mul_le_mul_of_nonneg_right hnm (by positivity)
  have h6 : m ^ 3 = m * (m * m) := by ring
  nlinarith only [h3, h4, h5, h6, hmm, hpow, hWm]

end
end SuperdiffusionCLT.Section4.MinimalScales
