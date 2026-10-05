/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.ElementaryB

/-!
# Elementary inequalities for the interior Caccioppoli wrapper

Real-analysis facts used to choose the scales and constants of the almost-sure wrapper: `log² m + K ≤ b √m`
and `log m ≤ m^κ` for large `m`; the window `1 ≤ σ ≤ m` for `σ` within the sharp-bound error of
`(2 c⋆ log 3 · m)^{1/2}`; and the scale-separation inequalities `τ (σ/ν)² ≤ 1`,
`τ (1 + d Λ²/ν²) ≤ 1`, `(σ α₂ + α₁)² ≤ 4 C² σ ν`, `σ β₂ + β₁ ≤ 3^m` that follow from
`τ (m/ν)^4 ≤ 1/m`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

/-- `log² m + K ≤ b √m` for large `m`. -/
theorem ca1w_log_sq_le (b : ℝ) (hb : 0 < b) (K : ℝ) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ m : ℝ, L ≤ m → Real.log m ^ 2 + K ≤ b * Real.sqrt m := by
  obtain ⟨L0, hL0⟩ := a23_log_le_mul (Real.sqrt (b / 32)) (by positivity)
  refine ⟨max (max 1 (max L0 1 ^ 4)) ((2 * |K| / b) ^ 2), le_trans (le_max_left _ _) (le_max_left _ _), ?_⟩
  intro m hm
  have hm1 : 1 ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
  have hm0 : 0 < m := by linarith only [hm1]
  set t : ℝ := Real.sqrt (Real.sqrt m) with ht
  have ht0 : 0 < t := Real.sqrt_pos.2 (Real.sqrt_pos.2 hm0)
  have hsq : t ^ 2 = Real.sqrt m := by
    rw [ht]; exact Real.sq_sqrt (Real.sqrt_nonneg _)
  have hm4 : m = t ^ 4 := by
    have h1 : (Real.sqrt m) ^ 2 = m := Real.sq_sqrt hm0.le
    calc m = (Real.sqrt m) ^ 2 := h1.symm
      _ = (t ^ 2) ^ 2 := by rw [hsq]
      _ = t ^ 4 := by ring
  have hmL : max L0 1 ^ 4 ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
  have htL : L0 ≤ t := by
    by_contra hlt
    push Not at hlt
    have h1 : t < max L0 1 := lt_of_lt_of_le hlt (le_max_left _ _)
    have h2 : t ^ 4 < max L0 1 ^ 4 := pow_lt_pow_left₀ h1 ht0.le (by norm_num)
    linarith only [h2, hm4, hmL]
  have hlog := hL0 t htL
  have hlogm : Real.log m = 4 * Real.log t := by
    rw [hm4, Real.log_pow]; norm_num
  have hlt0 : 0 ≤ Real.log t := by
    have : 1 ≤ t := by
      by_contra h
      push Not at h
      have : t ^ 4 < 1 := pow_lt_one₀ ht0.le h (by norm_num)
      linarith only [this, hm4, hm1]
    exact Real.log_nonneg this
  have h4 : Real.log m ^ 2 ≤ b / 2 * Real.sqrt m := by
    rw [hlogm]
    have h5 : Real.log t ≤ Real.sqrt (b / 32) * t := hlog
    have h6 : (Real.log t) ^ 2 ≤ (Real.sqrt (b / 32) * t) ^ 2 := pow_le_pow_left₀ hlt0 h5 2
    have h7 : (Real.sqrt (b / 32) * t) ^ 2 = b / 32 * t ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
    rw [← hsq]
    nlinarith only [h6, h7]
  have hK : K ≤ b / 2 * Real.sqrt m := by
    have h8 : 2 * |K| / b ≤ Real.sqrt m := by
      have h9 : (2 * |K| / b) ^ 2 ≤ m := le_trans (le_max_right _ _) hm
      calc 2 * |K| / b = Real.sqrt ((2 * |K| / b) ^ 2) := (Real.sqrt_sq (by positivity)).symm
        _ ≤ Real.sqrt m := Real.sqrt_le_sqrt h9
    have h10 : 2 * |K| ≤ b * Real.sqrt m := by
      have := (div_le_iff₀ hb).1 h8
      linarith only [this]
    have := le_abs_self K
    linarith only [h10, this]
  linarith only [h4, hK]

/-- `log m ≤ m^κ` for large `m`, for any `κ > 0`. -/
theorem ca1w_log_le_rpow (κ : ℝ) (hκ : 0 < κ) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ m : ℝ, L ≤ m → Real.log m ≤ m ^ κ := by
  obtain ⟨L0, hL0⟩ := a23_log_le_mul κ hκ
  refine ⟨max 1 (L0 ^ (1 / κ)), le_max_left _ _, fun m hm => ?_⟩
  have hm1 : 1 ≤ m := le_trans (le_max_left _ _) hm
  have hm0 : 0 < m := by linarith only [hm1]
  have ht0 : 0 < m ^ κ := Real.rpow_pos_of_pos hm0 κ
  have hL : L0 ≤ m ^ κ := by
    by_cases hL : L0 ≤ 0
    · exact le_trans hL ht0.le
    · push Not at hL
      have h1 : L0 ^ (1 / κ) ≤ m := le_trans (le_max_right _ _) hm
      have h2 := Real.rpow_le_rpow (Real.rpow_nonneg hL.le _) h1 hκ.le
      rwa [← Real.rpow_mul hL.le, one_div, inv_mul_cancel₀ hκ.ne', Real.rpow_one] at h2
  have h3 := hL0 _ hL
  rw [Real.log_rpow hm0] at h3
  have := (mul_le_mul_iff_of_pos_left hκ).1 (show κ * Real.log m ≤ κ * m ^ κ by linarith only [h3])
  exact this

/-- **The window `1 ≤ σ ≤ m`**: a number within the sharp-bound error of `(2 c⋆ log 3 · m)^{1/2}`
lies in `[1, m]` for large `m`. -/
theorem ca1w_sigma_window (cStar C K : ℝ) (hc : 0 < cStar) (hC : 1 ≤ C) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ m S : ℝ, L ≤ m →
      |S - (2 * cStar * Real.log 3 * m) ^ ((1 : ℝ) / 2)| ≤
        C * cStar⁻¹ * (Real.log m ^ (2 : ℝ) + K) → 1 ≤ S ∧ S ≤ m := by
  have hl3 := a23_log_three_pos
  set a : ℝ := 2 * cStar * Real.log 3 with ha
  have ha0 : 0 < a := by positivity
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha0
  obtain ⟨L1, hL1, H1⟩ := ca1w_log_sq_le (cStar * Real.sqrt a / (2 * C)) (by positivity) K
  refine ⟨max (max L1 (4 / a)) (9 * a / 4), le_trans hL1 (le_trans (le_max_left _ _) (le_max_left _ _)), ?_⟩
  intro m S hm hS
  have hmL1 : L1 ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
  have hm1 : 1 ≤ m := le_trans hL1 hmL1
  have hm0 : 0 < m := by linarith only [hm1]
  have hm4 : 4 / a ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
  have hm9 : 9 * a / 4 ≤ m := le_trans (le_max_right _ _) hm
  have hr : (2 * cStar * Real.log 3 * m) ^ ((1 : ℝ) / 2) = Real.sqrt a * Real.sqrt m := by
    rw [← ha, ← Real.sqrt_eq_rpow, Real.sqrt_mul ha0.le]
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.2 hm0
  have hlog2 : Real.log m ^ (2 : ℝ) = Real.log m ^ 2 := by
    exact_mod_cast Real.rpow_natCast (Real.log m) 2
  have hE : C * cStar⁻¹ * (Real.log m ^ (2 : ℝ) + K) ≤ Real.sqrt a * Real.sqrt m / 2 := by
    have h1 := H1 m hmL1
    rw [hlog2]
    have h2 : C * cStar⁻¹ * (Real.log m ^ 2 + K) ≤
        C * cStar⁻¹ * (cStar * Real.sqrt a / (2 * C) * Real.sqrt m) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : C * cStar⁻¹ * (cStar * Real.sqrt a / (2 * C) * Real.sqrt m) =
        Real.sqrt a * Real.sqrt m / 2 := by
      field_simp
    linarith only [h2, h3]
  rw [hr] at hS
  have hS1 := abs_le.1 hS
  have hE2 := hE
  have h2r : 2 ≤ Real.sqrt a * Real.sqrt m := by
    have h4 : 4 ≤ a * m := by
      have := (div_le_iff₀ ha0).1 hm4
      linarith only [this]
    have h5 : Real.sqrt 4 ≤ Real.sqrt (a * m) := Real.sqrt_le_sqrt h4
    rw [Real.sqrt_mul ha0.le] at h5
    have h6 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
    linarith only [h5, h6]
  have h3r : Real.sqrt a * Real.sqrt m * (3 / 2) ≤ m := by
    have h7 : Real.sqrt m ≥ 3 / 2 * Real.sqrt a := by
      have h8 : (3 / 2 * Real.sqrt a) ^ 2 ≤ m := by
        rw [mul_pow, Real.sq_sqrt ha0.le]
        linarith only [hm9]
      calc 3 / 2 * Real.sqrt a = Real.sqrt ((3 / 2 * Real.sqrt a) ^ 2) :=
            (Real.sqrt_sq (by positivity)).symm
        _ ≤ Real.sqrt m := Real.sqrt_le_sqrt h8
    have h9 : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm0.le
    nlinarith only [h7, h9, hsa, hsm]
  constructor
  · linarith only [hS1.1, hE2, h2r]
  · linarith only [hS1.2, hE2, h3r]


theorem ca1w_rpow_le_sq {m ρ : ℝ} (hm : 1 ≤ m) (hρ : ρ ≤ 1) : m ^ (1 + ρ) ≤ m ^ 2 := by
  have h1 : m ^ (1 + ρ) ≤ m ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hm (by linarith only [hρ])
  rw [Real.rpow_two] at h1
  exact h1

/-- The scale-separation inequality `x (m/ν)^4 ≤ 1/m` gives the first two `τ`-inequalities. -/
theorem ca1w_tau_ineq (d : ℕ) {ν S m x Λ ρ : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hSm : S ≤ m)
    (hS0 : 0 ≤ S) (hm : (1 : ℝ) + 4 * d ≤ m) (hx : 0 ≤ x) (hmaster : x * (m / ν) ^ 4 ≤ m⁻¹)
    (hΛ0 : 0 ≤ Λ) (hΛ : Λ ≤ ν + m ^ (1 + ρ)) (hρ : ρ ≤ 1) :
    x * (S / ν) ^ 2 ≤ 1 ∧ x * (1 + d * Λ ^ 2 / ν ^ 2) ≤ 1 := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hm1 : 1 ≤ m := by linarith only [hm, hd0]
  have hm0 : 0 < m := by linarith only [hm1]
  have hq1 : 1 ≤ m / ν := by
    rw [le_div_iff₀ hν]; linarith only [hm1, hν1]
  have hinv : m⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hm1
  have hq2 : (m / ν) ^ 2 ≤ (m / ν) ^ 4 := pow_le_pow_right₀ hq1 (by norm_num)
  have hq4 : 1 ≤ (m / ν) ^ 4 := one_le_pow₀ hq1
  refine ⟨?_, ?_⟩
  · have h1 : S / ν ≤ m / ν := div_le_div_of_nonneg_right hSm hν.le
    have h2 : (S / ν) ^ 2 ≤ (m / ν) ^ 2 := pow_le_pow_left₀ (div_nonneg hS0 hν.le) h1 2
    have h3 := mul_le_mul_of_nonneg_left (h2.trans hq2) hx
    linarith only [h3, hmaster, hinv]
  · have hmρ := ca1w_rpow_le_sq hm1 hρ
    have hm2 : 1 ≤ m ^ 2 := one_le_pow₀ hm1
    have hΛ2 : Λ ≤ 2 * m ^ 2 := by linarith only [hΛ, hmρ, hν1, hm2]
    have hΛsq : Λ ^ 2 ≤ 4 * m ^ 4 := by
      have := pow_le_pow_left₀ hΛ0 hΛ2 2
      nlinarith only [this]
    have hν2 : ν ^ 4 ≤ ν ^ 2 := pow_le_pow_of_le_one hν.le hν1 (by norm_num)
    have hν2p : 0 < ν ^ 4 := by positivity
    have hkey : d * Λ ^ 2 / ν ^ 2 ≤ 4 * d * (m / ν) ^ 4 := by
      rw [div_pow, mul_div_assoc', div_le_div_iff₀ (by positivity) hν2p]
      have h1 : d * Λ ^ 2 ≤ d * (4 * m ^ 4) := mul_le_mul_of_nonneg_left hΛsq hd0
      have h2 : 0 ≤ d * (4 * m ^ 4) := by positivity
      calc d * Λ ^ 2 * ν ^ 4 ≤ d * (4 * m ^ 4) * ν ^ 4 :=
            mul_le_mul_of_nonneg_right h1 hν2p.le
        _ ≤ d * (4 * m ^ 4) * ν ^ 2 := mul_le_mul_of_nonneg_left hν2 h2
        _ = 4 * d * m ^ 4 * ν ^ 2 := by ring
    have h1 := mul_le_mul_of_nonneg_left hkey hx
    have h2 := mul_le_mul_of_nonneg_left hq4 hx
    have h3 : x * (1 + d * Λ ^ 2 / ν ^ 2) ≤ x * (m / ν) ^ 4 + 4 * d * (x * (m / ν) ^ 4) := by
      calc x * (1 + d * Λ ^ 2 / ν ^ 2) = x + x * (d * Λ ^ 2 / ν ^ 2) := by ring
        _ ≤ x * (m / ν) ^ 4 + x * (4 * d * (m / ν) ^ 4) := by
            have := mul_one x
            linarith only [h1, h2, this]
        _ = x * (m / ν) ^ 4 + 4 * d * (x * (m / ν) ^ 4) := by ring
    have h4 : (1 + 4 * (d : ℝ)) * m⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hm0]; exact hm
    have h5 : (1 + 4 * (d : ℝ)) * (x * (m / ν) ^ 4) ≤ (1 + 4 * (d : ℝ)) * m⁻¹ :=
      mul_le_mul_of_nonneg_left hmaster (by positivity)
    linarith only [h3, h4, h5]

/-- The coefficient inequalities of the interior Caccioppoli core, from the scale separation. -/
theorem ca1w_coef_ineq {C1 ν S m x δ ρ T Tn : ℝ} (hC1 : 1 ≤ C1) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hνS : ν ≤ S) (hSm : S ≤ m) (hm : 5 * C1 ^ 2 ≤ m) (hm1 : 1 ≤ m) (hx : 0 ≤ x)
    (hmaster : x * (m / ν) ^ 4 ≤ m⁻¹) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hρ : ρ ≤ 1) (hT : 0 < T)
    (hTn : Tn = x * T) :
    (S * (C1 * (Real.sqrt S)⁻¹ * Real.sqrt ν) + C1 * Real.sqrt S * δ * Real.sqrt ν) ^ 2 ≤
        4 * C1 ^ 2 * S * ν ∧
      S * ((C1 * (Real.sqrt S)⁻¹ * Real.sqrt ν + C1) * (C1 * Tn / ν)) +
          (C1 * Real.sqrt S * δ * Real.sqrt ν + C1 * (|ν - S| + m ^ (1 + ρ))) *
            (C1 * Tn / ν) ≤ T := by
  have hC0 : 0 < C1 := by linarith only [hC1]
  have hS0 : 0 < S := lt_of_lt_of_le hν hνS
  have hm0 : 0 < m := by linarith only [hm1]
  obtain ⟨a, ha, haS⟩ : ∃ a, 0 < a ∧ S = a ^ 2 := ⟨Real.sqrt S, Real.sqrt_pos.2 hS0, (Real.sq_sqrt hS0.le).symm⟩
  obtain ⟨b, hb, hbν⟩ : ∃ b, 0 < b ∧ ν = b ^ 2 := ⟨Real.sqrt ν, Real.sqrt_pos.2 hν, (Real.sq_sqrt hν.le).symm⟩
  have hba : b ≤ a := by
    have : b ^ 2 ≤ a ^ 2 := by rw [← haS, ← hbν]; exact hνS
    exact le_of_sq_le_sq this ha.le
  have hsa : Real.sqrt S = a := by rw [haS]; exact Real.sqrt_sq ha.le
  have hsb : Real.sqrt ν = b := by rw [hbν]; exact Real.sqrt_sq hb.le
  rw [hsa, hsb]
  refine ⟨?_, ?_⟩
  · have e : S * (C1 * a⁻¹ * b) + C1 * a * δ * b = C1 * a * b * (1 + δ) := by
      rw [haS]; field_simp
    rw [e, haS, hbν]
    have h1 : (1 + δ) ^ 2 ≤ 4 := by nlinarith only [hδ0, hδ1]
    calc (C1 * a * b * (1 + δ)) ^ 2 = C1 ^ 2 * a ^ 2 * b ^ 2 * (1 + δ) ^ 2 := by ring
      _ ≤ C1 ^ 2 * a ^ 2 * b ^ 2 * 4 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 4 * C1 ^ 2 * a ^ 2 * b ^ 2 := by ring
  · have hmρ := ca1w_rpow_le_sq hm1 hρ
    have hm2 : m ≤ m ^ 2 := by nlinarith only [hm1]
    have habs : |ν - S| = S - ν := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith only [hνS])
    have hab : a * b ≤ S := by
      rw [haS]; nlinarith only [hba, ha, hb]
    have hq4 : m ^ 2 / ν ≤ (m / ν) ^ 4 := by
      rw [div_pow, div_le_div_iff₀ hν (by positivity)]
      have h3 : ν ^ 3 ≤ m ^ 2 := by
        have h1 : ν ^ 3 ≤ 1 := pow_le_one₀ hν.le hν1
        have h2 : 1 ≤ m ^ 2 := one_le_pow₀ hm1
        linarith only [h1, h2]
      have h4 : 0 ≤ m ^ 2 * ν := by positivity
      calc m ^ 2 * ν ^ 4 = (m ^ 2 * ν) * ν ^ 3 := by ring
        _ ≤ (m ^ 2 * ν) * m ^ 2 := mul_le_mul_of_nonneg_left h3 h4
        _ = m ^ 4 * ν := by ring
    have hxm : x * (m ^ 2 / ν) ≤ m⁻¹ := (mul_le_mul_of_nonneg_left hq4 hx).trans hmaster
    have hbig : 0 ≤ (C1 * Tn / ν) := by
      rw [hTn]; positivity
    have hb2 : S * (C1 * a⁻¹ * b + C1) ≤ 2 * C1 * S := by
      have e : S * (C1 * a⁻¹ * b) = C1 * (a * b) := by rw [haS]; field_simp
      have : S * (C1 * a⁻¹ * b + C1) = C1 * (a * b) + C1 * S := by rw [mul_add, e]; ring
      rw [this]
      nlinarith only [hab, hC0]
    have hb1 : C1 * a * δ * b + C1 * (|ν - S| + m ^ (1 + ρ)) ≤ C1 * (2 * S + m ^ 2) := by
      have h1 : C1 * a * δ * b ≤ C1 * S := by
        have : a * b * δ ≤ S := le_trans (mul_le_of_le_one_right (by positivity) hδ1) hab
        nlinarith only [this, hC0]
      rw [habs]
      have : C1 * (S - ν + m ^ (1 + ρ)) ≤ C1 * (S + m ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hC0.le
        linarith only [hmρ, hν]
      linarith only [h1, this]
    have hsum : S * ((C1 * a⁻¹ * b + C1) * (C1 * Tn / ν)) +
        (C1 * a * δ * b + C1 * (|ν - S| + m ^ (1 + ρ))) * (C1 * Tn / ν) ≤
        (2 * C1 * S + C1 * (2 * S + m ^ 2)) * (C1 * Tn / ν) := by
      rw [← mul_assoc, ← add_mul]
      exact mul_le_mul_of_nonneg_right (add_le_add hb2 hb1) hbig
    refine hsum.trans ?_
    have h5 : 2 * C1 * S + C1 * (2 * S + m ^ 2) ≤ C1 * (5 * m ^ 2) := by
      nlinarith only [hSm, hm2, hC0]
    have h6 : (2 * C1 * S + C1 * (2 * S + m ^ 2)) * (C1 * Tn / ν) ≤ C1 * (5 * m ^ 2) * (C1 * Tn / ν) :=
      mul_le_mul_of_nonneg_right h5 hbig
    refine h6.trans ?_
    have e : C1 * (5 * m ^ 2) * (C1 * Tn / ν) = 5 * C1 ^ 2 * (x * (m ^ 2 / ν)) * T := by
      rw [hTn]; ring
    rw [e]
    have h7 : 5 * C1 ^ 2 * (x * (m ^ 2 / ν)) ≤ 5 * C1 ^ 2 * m⁻¹ :=
      mul_le_mul_of_nonneg_left hxm (by positivity)
    have h8 : 5 * C1 ^ 2 * m⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hm0]; exact hm
    have h9 : 5 * C1 ^ 2 * (x * (m ^ 2 / ν)) ≤ 1 := h7.trans h8
    calc 5 * C1 ^ 2 * (x * (m ^ 2 / ν)) * T ≤ 1 * T := mul_le_mul_of_nonneg_right h9 hT.le
      _ = T := one_mul T

end SuperdiffusionCLT.Section7
