/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.L2AssemblyE
public import SuperdiffusionCLT.Section7.Analytic.ElementaryB
public import SuperdiffusionCLT.Section7.Lipschitz.InnerBall
public import SuperdiffusionCLT.Section7.Lipschitz.SigmaWindow
public import SuperdiffusionCLT.Section7.Lipschitz.Carriers

/-!
# The parameter bounds of the `L²` Dirichlet comparison

Display `e.Dir.new.h.choice` and the end of the proof: with the mesoscale `n = K - h_K` the
layer factor and the cell factor are at most `K^{-(A+3)}`, and the five
terms of the core are bounded by the two terms of the block (`l2e_block_ineq`).
-/

@[expose] public section

open MeasureTheory Set Filter Homogenization
open scoped ENNReal NNReal Pointwise

namespace SuperdiffusionCLT.Section7

theorem l2e_expand (X Y Fn : ℝ≥0∞) {c3 c0 p Λ sI κ a b t sk e g : ℝ} (hc3 : 0 ≤ c3) (hc0 : 0 ≤ c0)
    (hp : 0 ≤ p) (hΛ : 0 ≤ Λ) (hsI : 0 ≤ sI) (hκ : 0 ≤ κ) (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 ≤ t)
    (hsk : 0 ≤ sk) (he : 0 ≤ e) (hg : 0 ≤ g) :
    ENNReal.ofReal c3 * (ENNReal.ofReal c0 * (ENNReal.ofReal p * (X + Y) +
      ENNReal.ofReal Λ * (ENNReal.ofReal sI * (ENNReal.ofReal κ * ENNReal.ofReal a * X +
          ENNReal.ofReal κ * ENNReal.ofReal b * Fn) + ENNReal.ofReal t * Y +
        ENNReal.ofReal t * (X + Y) +
        ENNReal.ofReal sI * (ENNReal.ofReal p * Fn +
          (ENNReal.ofReal κ * ENNReal.ofReal a + ENNReal.ofReal sk * ENNReal.ofReal e) *
            ENNReal.ofReal t * X +
          (ENNReal.ofReal κ * ENNReal.ofReal b + ENNReal.ofReal sk * ENNReal.ofReal g) * Fn)))) =
      ENNReal.ofReal (c3 * c0 * (p + Λ * (sI * (κ * a) + t + sI * ((κ * a + sk * e) * t)))) * X +
        ENNReal.ofReal (c3 * c0 * (p + Λ * (t + t))) * Y +
        ENNReal.ofReal (c3 * c0 * (Λ * (sI * (κ * b) + sI * p + sI * (κ * b + sk * g)))) * Fn := by
  simp (disch := positivity) only [ENNReal.ofReal_mul, ENNReal.ofReal_add]
  ring


/-- Bounds for the scale `δ_k = ε k^{-(1-ρ)/2} log k`. -/
theorem l2e_delta_bounds {k ε ρ : ℝ} (hk : 3 ≤ k) (hε : 0 < ε) (hε1 : ε ≤ 1) (hρ : 0 < ρ)
    (hρ1 : ρ < 1) : ε * k ^ (-(1 / 2 : ℝ)) ≤ deltaScale ε ρ k ∧ deltaScale ε ρ k ≤ k := by
  have hk0 : 0 < k := by linarith only [hk]
  have hk1 : 1 ≤ k := by linarith only [hk]
  have hlog1 : 1 ≤ Real.log k := by
    have h3 : Real.log 3 ≥ 1 := by
      rw [ge_iff_le, Real.le_log_iff_exp_le (by norm_num)]
      have := Real.exp_one_lt_d9
      linarith only [this]
    exact h3.trans (Real.log_le_log (by norm_num) hk)
  have hlogk : Real.log k ≤ k := by
    have := Real.log_le_sub_one_of_pos hk0
    linarith only [this]
  unfold deltaScale
  constructor
  · have h1 : k ^ (-(1 / 2 : ℝ)) ≤ k ^ (-((1 - ρ) / 2)) :=
      Real.rpow_le_rpow_of_exponent_le hk1 (by linarith only [hρ])
    have h2 : 0 ≤ k ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hk0.le _
    calc ε * k ^ (-(1 / 2 : ℝ)) = ε * k ^ (-(1 / 2 : ℝ)) * 1 := (mul_one _).symm
      _ ≤ ε * k ^ (-((1 - ρ) / 2)) * Real.log k := by gcongr
  · have h1 : k ^ (-((1 - ρ) / 2)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hk1 (by linarith only [hρ1])
    have h2 : 0 ≤ k ^ (-((1 - ρ) / 2)) := Real.rpow_nonneg hk0.le _
    calc ε * k ^ (-((1 - ρ) / 2)) * Real.log k ≤ 1 * 1 * k := by
          gcongr
      _ = k := by ring


/-- `x * k^(A+3) ≤ c` gives `x * k^3 ≤ c * (k^A)⁻¹`. -/
theorem l2e_pow_aux {k x c : ℝ} {A : ℕ} (hk : 1 ≤ k) (h : x * k ^ (A + 3) ≤ c) :
    x * k ^ 3 ≤ c * (k ^ A)⁻¹ := by
  have hkA : 0 < k ^ A := pow_pos (by linarith only [hk]) A
  rw [← div_eq_mul_inv, le_div_iff₀ hkA]
  calc x * k ^ 3 * k ^ A = x * k ^ (A + 3) := by ring
    _ ≤ c := h

theorem l2e_cY {k c0 cv R t c3 L3 p Pn : ℝ} {A : ℕ} (hk : 1 ≤ k) (hc0 : 0 ≤ c0) (hcv : 0 ≤ cv)
    (hc3 : c3 * L3 = 1) (hPn : Pn = R * L3) (hp : p = 5 * Pn) (hR0 : 0 < R)
    (hRk : R * k ^ (A + 3) ≤ 1) (ht0 : 0 ≤ t) (htk : t * k ^ (A + 3) ≤ cv) :
    c3 * c0 * (p + L3 * (t + t)) ≤ c0 * (5 + 2 * cv) * (k ^ A)⁻¹ := by
  have hk3 : 1 ≤ k ^ 3 := one_le_pow₀ hk
  have hkA : 0 < k ^ A := pow_pos (by linarith only [hk]) A
  have hQ : 0 < (k ^ A)⁻¹ := inv_pos.2 hkA
  have hR := l2e_pow_aux hk hRk
  have hT := l2e_pow_aux hk htk
  rw [one_mul] at hR
  have hR' : R ≤ (k ^ A)⁻¹ := by nlinarith only [hR, hk3, hR0]
  have hT' : t ≤ cv * (k ^ A)⁻¹ := by
    have : 0 ≤ cv * (k ^ A)⁻¹ := by positivity
    nlinarith only [hT, hk3, ht0, this]
  have h1 : c3 * c0 * (p + L3 * (t + t)) = c0 * (5 * R * (c3 * L3) + 2 * t * (c3 * L3)) := by
    rw [hp, hPn]; ring
  rw [h1, hc3]
  nlinarith only [hR', hT', hc0, hQ]


theorem l2e_cF {k ν σ δ C K' c0 R Pn L3 c3 p aC e b g ρ : ℝ} {A : ℕ} (hk : 1 ≤ k) (hν0 : 0 < ν)
    (hν1 : ν ≤ 1) (hσν : ν ≤ σ) (hσk : σ ≤ k) (hδ0 : 0 ≤ δ) (hδk : δ ≤ k) (hρ1 : ρ < 1)
    (hC : 0 ≤ C) (hK' : 0 ≤ K') (hc0 : 0 ≤ c0) (hc3 : c3 * L3 = 1) (hL3 : 0 < L3)
    (hPn : Pn = R * L3) (hp : p = 5 * Pn) (hR0 : 0 < R) (hRk : R * k ^ (A + 3) ≤ 1)
    (hthr : 1 ≤ k * ν ^ 2) (haC : aC = C * Real.sqrt σ * δ * Real.sqrt ν)
    (he : e = C * (Real.sqrt σ)⁻¹ * Real.sqrt ν)
    (hb : b = (aC + C * (|ν - σ| + k ^ (1 + ρ))) * (C * (3 * Pn) / ν))
    (hg : g = (e + C) * (C * (3 * Pn) / ν)) :
    c3 * c0 * (L3 * (σ⁻¹ * (K' * b) + σ⁻¹ * p + σ⁻¹ * (K' * b + (σ * K') * g))) ≤
      c0 * (24 * K' * C ^ 2 + 5) * (k ^ A)⁻¹ * L3 := by
  have hk0 : 0 < k := by linarith only [hk]
  have hσ0 : 0 < σ := lt_of_lt_of_le hν0 hσν
  have hPn0 : 0 ≤ Pn := by rw [hPn]; positivity
  have hkA : 0 < k ^ A := pow_pos hk0 A
  have hQ : 0 < (k ^ A)⁻¹ := inv_pos.2 hkA
  have hk2 : k ≤ k ^ 2 := by nlinarith only [hk]
  -- elementary bounds
  have hsq : Real.sqrt σ ≤ k :=
    Real.sqrt_le_iff.2 ⟨hk0.le, by nlinarith only [hσk, hk2]⟩
  have hsqν : Real.sqrt ν ≤ 1 := Real.sqrt_le_one.2 hν1
  have hsqσν : Real.sqrt ν ≤ Real.sqrt σ := Real.sqrt_le_sqrt hσν
  have hsqσ0 : 0 < Real.sqrt σ := Real.sqrt_pos.2 hσ0
  have hsqν0 : 0 ≤ Real.sqrt ν := Real.sqrt_nonneg _
  have haC' : aC ≤ C * k ^ 2 := by
    rw [haC]
    have h1 : C * Real.sqrt σ * δ * Real.sqrt ν ≤ C * k * k * 1 := by
      gcongr
    nlinarith only [h1, hC, hk2, hk]
  have hkρ : k ^ (1 + ρ) ≤ k ^ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le hk (show 1 + ρ ≤ (2 : ℝ) by linarith only [hρ1])
    simpa using this
  have habs : |ν - σ| ≤ k := by
    rw [abs_of_nonpos (by linarith only [hσν])]
    linarith only [hσk, hν0]
  have hw0 : 0 ≤ C * (3 * Pn) / ν := by positivity
  have hb' : b ≤ 3 * C * k ^ 2 * (C * (3 * Pn) / ν) := by
    rw [hb]
    refine mul_le_mul_of_nonneg_right ?_ hw0
    nlinarith only [haC', habs, hkρ, hk2, hC]
  have he' : e ≤ C := by
    rw [he]
    have : (Real.sqrt σ)⁻¹ * Real.sqrt ν ≤ 1 := by
      rw [inv_mul_le_iff₀ hsqσ0]; linarith only [hsqσν]
    calc C * (Real.sqrt σ)⁻¹ * Real.sqrt ν = C * ((Real.sqrt σ)⁻¹ * Real.sqrt ν) := by ring
      _ ≤ C * 1 := by gcongr
      _ = C := mul_one C
  have he0 : 0 ≤ e := by
    rw [he]; exact mul_nonneg (mul_nonneg hC (inv_nonneg.2 hsqσ0.le)) hsqν0
  have hg' : g ≤ 2 * C * (C * (3 * Pn) / ν) := by
    rw [hg]
    refine mul_le_mul_of_nonneg_right ?_ hw0
    linarith only [he']
  have haC0 : 0 ≤ aC := by rw [haC]; positivity
  have hb0 : 0 ≤ b := by
    rw [hb]
    exact mul_nonneg (add_nonneg haC0 (mul_nonneg hC (add_nonneg (abs_nonneg _)
      (Real.rpow_nonneg hk0.le _)))) hw0
  have hg0 : 0 ≤ g := by rw [hg]; exact mul_nonneg (add_nonneg he0 hC) hw0
  -- the shape
  have hiσ : σ⁻¹ * σ = 1 := inv_mul_cancel₀ hσ0.ne'
  have hiσν : σ⁻¹ ≤ ν⁻¹ := inv_anti₀ hν0 hσν
  have hiν : ν⁻¹ * ν = 1 := inv_mul_cancel₀ hν0.ne'
  have hiν1 : 1 ≤ ν⁻¹ := (one_le_inv₀ hν0).2 hν1
  have hiν0 : 0 < ν⁻¹ := inv_pos.2 hν0
  have hiν2 : ν⁻¹ ^ 2 ≤ k := by
    have : ν⁻¹ ^ 2 = (ν ^ 2)⁻¹ := by rw [inv_pow]
    rw [this, inv_le_iff_one_le_mul₀' (by positivity)]
    linarith only [hthr]
  have hw : C * (3 * Pn) / ν = 3 * C * Pn * ν⁻¹ := by rw [div_eq_mul_inv]; ring
  rw [hw] at hb' hg'
  set iν := ν⁻¹ with hiν_def
  have hk1' : 1 ≤ k ^ 2 := one_le_pow₀ hk
  have hiνsq : iν ≤ iν ^ 2 := by nlinarith only [hiν1]
  have hiσ0 : 0 ≤ σ⁻¹ := inv_nonneg.2 hσ0.le
  have h1 : σ⁻¹ * (K' * b) ≤ 9 * K' * C ^ 2 * k ^ 2 * Pn * iν ^ 2 := by
    calc σ⁻¹ * (K' * b) ≤ iν * (K' * (3 * C * k ^ 2 * (3 * C * Pn * iν))) :=
          mul_le_mul hiσν (mul_le_mul_of_nonneg_left hb' hK') (mul_nonneg hK' hb0) hiν0.le
      _ = 9 * K' * C ^ 2 * k ^ 2 * Pn * iν ^ 2 := by ring
  have h2 : σ⁻¹ * p ≤ 5 * Pn * (iν ^ 2 * k ^ 2) := by
    rw [hp]
    have hiσ' : σ⁻¹ ≤ iν ^ 2 * k ^ 2 := by
      calc σ⁻¹ ≤ iν := hiσν
        _ ≤ iν ^ 2 := hiνsq
        _ = iν ^ 2 * 1 := (mul_one _).symm
        _ ≤ iν ^ 2 * k ^ 2 := by gcongr
    calc σ⁻¹ * (5 * Pn) ≤ (iν ^ 2 * k ^ 2) * (5 * Pn) := by gcongr
      _ = 5 * Pn * (iν ^ 2 * k ^ 2) := by ring
  have h3 : K' * g ≤ 6 * K' * C ^ 2 * Pn * (iν ^ 2 * k ^ 2) := by
    calc K' * g ≤ K' * (2 * C * (3 * C * Pn * iν)) := mul_le_mul_of_nonneg_left hg' hK'
      _ = 6 * K' * C ^ 2 * Pn * iν := by ring
      _ ≤ 6 * K' * C ^ 2 * Pn * (iν ^ 2 * k ^ 2) := by
          have : iν ≤ iν ^ 2 * k ^ 2 := by
            calc iν ≤ iν ^ 2 := hiνsq
              _ = iν ^ 2 * 1 := (mul_one _).symm
              _ ≤ iν ^ 2 * k ^ 2 := by gcongr
          have h6 : 0 ≤ 6 * K' * C ^ 2 * Pn := by positivity
          exact mul_le_mul_of_nonneg_left this h6
  have h1' : σ⁻¹ * (K' * b) ≤ 9 * K' * C ^ 2 * Pn * (iν ^ 2 * k ^ 2) := by
    calc _ ≤ _ := h1
      _ = _ := by ring
  have hS : 2 * (σ⁻¹ * (K' * b)) + σ⁻¹ * p + K' * g ≤ (24 * K' * C ^ 2 + 5) * (Pn * k ^ 3) := by
    have hsum : 2 * (σ⁻¹ * (K' * b)) + σ⁻¹ * p + K' * g ≤
        (24 * K' * C ^ 2 + 5) * (Pn * (iν ^ 2 * k ^ 2)) := by
      nlinarith only [h1', h2, h3]
    refine hsum.trans ?_
    have : Pn * (iν ^ 2 * k ^ 2) ≤ Pn * k ^ 3 := by
      refine mul_le_mul_of_nonneg_left ?_ hPn0
      calc iν ^ 2 * k ^ 2 ≤ k * k ^ 2 := by gcongr
        _ = k ^ 3 := by ring
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have e1 : c3 * c0 * (L3 * (σ⁻¹ * (K' * b) + σ⁻¹ * p + σ⁻¹ * (K' * b + (σ * K') * g))) =
      c0 * (2 * (σ⁻¹ * (K' * b)) + σ⁻¹ * p + K' * g) := by
    have h5 : σ⁻¹ * ((σ * K') * g) = K' * g := by
      rw [← mul_assoc, ← mul_assoc, hiσ, one_mul]
    have h2' : c3 * c0 * (L3 * (σ⁻¹ * (K' * b) + σ⁻¹ * p + σ⁻¹ * (K' * b + (σ * K') * g))) =
        (c3 * L3) * c0 * (2 * (σ⁻¹ * (K' * b)) + σ⁻¹ * p + σ⁻¹ * ((σ * K') * g)) := by ring
    rw [h2', hc3, h5]; ring
  rw [e1]
  have hRQ := l2e_pow_aux hk hRk
  rw [one_mul] at hRQ
  have hPQ : Pn * k ^ 3 ≤ (k ^ A)⁻¹ * L3 := by
    rw [hPn]
    calc R * L3 * k ^ 3 = (R * k ^ 3) * L3 := by ring
      _ ≤ (k ^ A)⁻¹ * L3 := mul_le_mul_of_nonneg_right hRQ hL3.le
  calc c0 * (2 * (σ⁻¹ * (K' * b)) + σ⁻¹ * p + K' * g)
      ≤ c0 * ((24 * K' * C ^ 2 + 5) * (Pn * k ^ 3)) := mul_le_mul_of_nonneg_left hS hc0
    _ ≤ c0 * ((24 * K' * C ^ 2 + 5) * ((k ^ A)⁻¹ * L3)) := by
        gcongr
    _ = c0 * (24 * K' * C ^ 2 + 5) * (k ^ A)⁻¹ * L3 := by ring


theorem l2e_cX {k ν ε σ δ C K' c0 cv R t c3 L3 p Pn aC e : ℝ} {A : ℕ} (hk : 1 ≤ k) (hε0 : 0 < ε)
    (hν0 : 0 < ν) (hν1 : ν ≤ 1) (hσν : ν ≤ σ) (hσk : σ ≤ k) (hδ0 : 0 ≤ δ)
    (hδlow : ε ≤ δ * Real.sqrt k) (hthr : 1 ≤ k * ε * ν ^ 2) (hC : 0 ≤ C) (hK' : 0 ≤ K')
    (hc0 : 0 ≤ c0) (hcv : 0 ≤ cv) (hc3 : c3 * L3 = 1) (hPn : Pn = R * L3) (hp : p = 5 * Pn)
    (hR0 : 0 < R) (hRk : R * k ^ (A + 3) ≤ 1) (ht0 : 0 ≤ t) (htk : t * k ^ (A + 3) ≤ cv)
    (haC : aC = C * Real.sqrt σ * δ * Real.sqrt ν) (he : e = C * (Real.sqrt σ)⁻¹ * Real.sqrt ν) :
    c3 * c0 * (p + L3 * (σ⁻¹ * (K' * aC) + t + σ⁻¹ * ((K' * aC + (σ * K') * e) * t))) ≤
      c0 * (5 + cv + K' * C * (1 + 2 * cv)) * (δ * (Real.sqrt σ)⁻¹ * Real.sqrt ν) := by
  have hk0 : 0 < k := by linarith only [hk]
  have hσ0 : 0 < σ := lt_of_lt_of_le hν0 hσν
  have hsσ : 0 < Real.sqrt σ := Real.sqrt_pos.2 hσ0
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.2 hk0
  have hsν : 0 ≤ Real.sqrt ν := Real.sqrt_nonneg _
  set z := (Real.sqrt σ)⁻¹ * Real.sqrt ν with hz
  have hz0 : 0 ≤ z := mul_nonneg (inv_nonneg.2 hsσ.le) hsν
  set T := δ * z with hT
  have hT0 : 0 ≤ T := mul_nonneg hδ0 hz0
  have hTg : δ * (Real.sqrt σ)⁻¹ * Real.sqrt ν = T := by rw [hT, hz]; ring
  rw [hTg]
  -- the identities
  have hiσ : σ⁻¹ * σ = 1 := inv_mul_cancel₀ hσ0.ne'
  have hσsq : σ⁻¹ * Real.sqrt σ = (Real.sqrt σ)⁻¹ := by
    have h := Real.mul_self_sqrt hσ0.le
    field_simp
    nlinarith only [h]
  have hiaC : σ⁻¹ * aC = C * T := by
    rw [haC, hT, hz, ← hσsq]; ring
  have he' : e = C * z := by rw [he, hz]; ring
  have hexp : c3 * c0 * (p + L3 * (σ⁻¹ * (K' * aC) + t + σ⁻¹ * ((K' * aC + (σ * K') * e) * t))) =
      c0 * (5 * R + K' * (C * T) + t + (K' * (C * T) + K' * e) * t) := by
    have h5 : σ⁻¹ * ((K' * aC + (σ * K') * e) * t) = (K' * (σ⁻¹ * aC) + K' * e) * t := by
      calc σ⁻¹ * ((K' * aC + (σ * K') * e) * t)
          = (K' * (σ⁻¹ * aC) + (σ⁻¹ * σ) * (K' * e)) * t := by ring
        _ = _ := by rw [hiσ, one_mul]
    have h6 : σ⁻¹ * (K' * aC) = K' * (σ⁻¹ * aC) := by ring
    rw [h5, h6, hiaC]
    have h7 : c3 * c0 * (p + L3 * (K' * (C * T) + t + (K' * (C * T) + K' * e) * t)) =
        c0 * (5 * R * (c3 * L3) + (K' * (C * T) + t + (K' * (C * T) + K' * e) * t) * (c3 * L3)) := by
      rw [hp, hPn]; ring
    rw [h7, hc3]; ring
  rw [hexp]
  -- elementary consequences of the hypotheses
  have hk3 : 1 ≤ k ^ 3 := one_le_pow₀ hk
  have hkA : 1 ≤ k ^ A := one_le_pow₀ hk
  have hRk3 : R * k ^ 3 ≤ 1 := by
    have : R * k ^ 3 ≤ R * k ^ (A + 3) := by
      rw [pow_add]
      have : 0 ≤ R * k ^ 3 := by positivity
      nlinarith only [hkA, this]
    linarith only [this, hRk]
  have htk3 : t * k ^ 3 ≤ cv := by
    have : t * k ^ 3 ≤ t * k ^ (A + 3) := by
      rw [pow_add]
      have : 0 ≤ t * k ^ 3 := by positivity
      nlinarith only [hkA, this]
    linarith only [this, htk]
  have ht1 : t ≤ cv := by nlinarith only [htk3, hk3, ht0]
  have hεk : 1 ≤ k * ε := by
    have h1 : ν ^ 2 ≤ 1 := pow_le_one₀ hν0.le hν1
    have h2 : 0 ≤ k * ε := by positivity
    nlinarith only [hthr, h1, h2]
  -- `T k ≥ ε √ν`
  have hsqk : Real.sqrt σ ≤ Real.sqrt k := Real.sqrt_le_sqrt hσk
  have hzk : Real.sqrt ν ≤ z * Real.sqrt k := by
    rw [hz]
    have : Real.sqrt ν ≤ Real.sqrt ν * (Real.sqrt k / Real.sqrt σ) := by
      have h1 : 1 ≤ Real.sqrt k / Real.sqrt σ := (one_le_div hsσ).2 hsqk
      nlinarith only [h1, hsν]
    calc Real.sqrt ν ≤ Real.sqrt ν * (Real.sqrt k / Real.sqrt σ) := this
      _ = (Real.sqrt σ)⁻¹ * Real.sqrt ν * Real.sqrt k := by field_simp
  have hTk : ε * Real.sqrt ν ≤ T * k := by
    calc ε * Real.sqrt ν ≤ (δ * Real.sqrt k) * (z * Real.sqrt k) :=
          mul_le_mul hδlow hzk hsν (mul_nonneg hδ0 hsk.le)
      _ = T * (Real.sqrt k * Real.sqrt k) := by rw [hT]; ring
      _ = T * k := by rw [Real.mul_self_sqrt hk0.le]
  have hsν2 : ν ^ 2 ≤ Real.sqrt ν := by
    have h1 : ν ^ 2 ≤ ν := by nlinarith only [hν0, hν1]
    have h2 : ν ≤ Real.sqrt ν := by
      calc ν = Real.sqrt (ν ^ 2) := (Real.sqrt_sq hν0.le).symm
        _ ≤ Real.sqrt ν := Real.sqrt_le_sqrt h1
    linarith only [h1, h2]
  -- `5 R + t ≤ (5 + cv) T`
  have hRT : (5 * R + t) ≤ (5 + cv) * T := by
    have h1 : R * k ≤ ε * Real.sqrt ν := by
      have : R * k ≤ R * k * (k * ε * ν ^ 2) := by
        have : 0 ≤ R * k := by positivity
        nlinarith only [hthr, this]
      have h2 : R * k * (k * ε * ν ^ 2) = (R * k ^ 2) * (ε * ν ^ 2) := by ring
      have h3 : R * k ^ 2 ≤ 1 := by
        have : R * k ^ 2 ≤ R * k ^ 3 := by
          have : k ^ 2 ≤ k ^ 3 := pow_le_pow_right₀ hk (by norm_num)
          exact mul_le_mul_of_nonneg_left this hR0.le
        linarith only [this, hRk3]
      have h4 : (R * k ^ 2) * (ε * ν ^ 2) ≤ 1 * (ε * ν ^ 2) :=
        mul_le_mul_of_nonneg_right h3 (by positivity)
      have h5 : ε * ν ^ 2 ≤ ε * Real.sqrt ν := mul_le_mul_of_nonneg_left hsν2 hε0.le
      linarith only [this, h2, h4, h5]
    have h1' : t * k ≤ cv * (ε * Real.sqrt ν) := by
      have : t * k ≤ t * k * (k * ε * ν ^ 2) := by
        have : 0 ≤ t * k := by positivity
        nlinarith only [hthr, this]
      have h2 : t * k * (k * ε * ν ^ 2) = (t * k ^ 2) * (ε * ν ^ 2) := by ring
      have h3 : t * k ^ 2 ≤ cv := by
        have : t * k ^ 2 ≤ t * k ^ 3 := by
          have : k ^ 2 ≤ k ^ 3 := pow_le_pow_right₀ hk (by norm_num)
          exact mul_le_mul_of_nonneg_left this ht0
        linarith only [this, htk3]
      have h4 : (t * k ^ 2) * (ε * ν ^ 2) ≤ cv * (ε * ν ^ 2) :=
        mul_le_mul_of_nonneg_right h3 (by positivity)
      have h5 : cv * (ε * ν ^ 2) ≤ cv * (ε * Real.sqrt ν) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsν2 hε0.le) hcv
      linarith only [this, h2, h4, h5]
    have : (5 * R + t) * k ≤ ((5 + cv) * T) * k := by
      have hTk' : (5 + cv) * (ε * Real.sqrt ν) ≤ (5 + cv) * (T * k) :=
        mul_le_mul_of_nonneg_left hTk (by positivity)
      nlinarith only [h1, h1', hTk']
    exact le_of_mul_le_mul_right this hk0
  -- `e t ≤ C cv T`
  have hezt : e * t ≤ C * cv * T := by
    rw [he']
    have h1 : z * ε ≤ T * Real.sqrt k := by
      rw [hT]; nlinarith only [hδlow, hz0]
    have h2 : t * Real.sqrt k ≤ cv * ε := by
      have a1 : Real.sqrt k ≤ k := by
        rw [Real.sqrt_le_left hk0.le]; nlinarith only [hk]
      have a2 : (t * Real.sqrt k) * k ≤ cv := by
        have b1 : (t * Real.sqrt k) * k ≤ t * k * k := by
          have : t * Real.sqrt k ≤ t * k := mul_le_mul_of_nonneg_left a1 ht0
          exact mul_le_mul_of_nonneg_right this hk0.le
        have b2 : t * k * k ≤ t * k ^ 3 := by
          have : k * k ≤ k ^ 3 := by nlinarith only [hk]
          calc t * k * k = t * (k * k) := by ring
            _ ≤ t * k ^ 3 := mul_le_mul_of_nonneg_left this ht0
        linarith only [b1, b2, htk3]
      have a3 : t * Real.sqrt k ≤ (t * Real.sqrt k) * (k * ε) := by
        have : 0 ≤ t * Real.sqrt k := by positivity
        nlinarith only [hεk, this]
      calc t * Real.sqrt k ≤ (t * Real.sqrt k) * (k * ε) := a3
        _ = ((t * Real.sqrt k) * k) * ε := by ring
        _ ≤ cv * ε := mul_le_mul_of_nonneg_right a2 hε0.le
    have h3 : (z * t) * ε ≤ (T * cv) * ε := by
      calc (z * t) * ε = (z * ε) * t := by ring
        _ ≤ (T * Real.sqrt k) * t := mul_le_mul_of_nonneg_right h1 ht0
        _ = T * (t * Real.sqrt k) := by ring
        _ ≤ T * (cv * ε) := mul_le_mul_of_nonneg_left h2 hT0
        _ = (T * cv) * ε := by ring
    have h4 : z * t ≤ T * cv := le_of_mul_le_mul_right h3 hε0
    calc C * z * t = C * (z * t) := by ring
      _ ≤ C * (T * cv) := mul_le_mul_of_nonneg_left h4 hC
      _ = C * cv * T := by ring
  -- the final bound
  have hKt : K' * (C * T) * t ≤ K' * C * cv * T := by
    have : K' * C * T * t ≤ K' * C * T * cv :=
      mul_le_mul_of_nonneg_left ht1 (by positivity)
    calc K' * (C * T) * t = K' * C * T * t := by ring
      _ ≤ K' * C * T * cv := this
      _ = K' * C * cv * T := by ring
  have hKe : K' * e * t ≤ K' * (C * cv * T) := by
    calc K' * e * t = K' * (e * t) := by ring
      _ ≤ K' * (C * cv * T) := mul_le_mul_of_nonneg_left hezt hK'
  have hin : 5 * R + K' * (C * T) + t + (K' * (C * T) + K' * e) * t ≤
      (5 + cv + K' * C * (1 + 2 * cv)) * T := by
    have e1 : (K' * (C * T) + K' * e) * t = K' * (C * T) * t + K' * e * t := by ring
    rw [e1]
    nlinarith only [hRT, hKt, hKe]
  exact mul_le_mul_of_nonneg_left hin hc0 |>.trans_eq (by ring)


/-- **The block inequality from the core**: the five-term bound of `l2d_core`, with the parameters of
the proof inserted, is at most the right side of `LipL2Block`. -/
theorem l2e_block_ineq (X Y Fn : ℝ≥0∞) {k ν ε ρ σ δ C K' c0 cv R t c3 L3 Pn p aC e b g : ℝ}
    {A : ℕ} (hk : 3 ≤ k) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1) (hν0 : 0 < ν)
    (hν1 : ν ≤ 1) (hσν : ν ≤ σ) (hσk : σ ≤ k) (hδ : δ = deltaScale ε ρ k)
    (hthr : 1 ≤ k * ε * ν ^ 2) (hC : 0 ≤ C) (hK' : 0 ≤ K') (hc0 : 0 ≤ c0) (hcv : 0 ≤ cv)
    (hc3 : c3 * L3 = 1) (hL3 : 0 < L3) (hPn : Pn = R * L3) (hp : p = 5 * Pn) (hR0 : 0 < R)
    (hRk : R * k ^ (A + 3) ≤ 1) (ht0 : 0 ≤ t) (htk : t * k ^ (A + 3) ≤ cv)
    (haC : aC = C * Real.sqrt σ * δ * Real.sqrt ν) (he : e = C * (Real.sqrt σ)⁻¹ * Real.sqrt ν)
    (hb : b = (aC + C * (|ν - σ| + k ^ (1 + ρ))) * (C * (3 * Pn) / ν))
    (hg : g = (e + C) * (C * (3 * Pn) / ν)) :
    ENNReal.ofReal c3 * (ENNReal.ofReal c0 * (ENNReal.ofReal p * (X + Y) +
      ENNReal.ofReal L3 * (ENNReal.ofReal σ⁻¹ * (ENNReal.ofReal K' * ENNReal.ofReal aC * X +
          ENNReal.ofReal K' * ENNReal.ofReal b * Fn) + ENNReal.ofReal t * Y +
        ENNReal.ofReal t * (X + Y) +
        ENNReal.ofReal σ⁻¹ * (ENNReal.ofReal p * Fn +
          (ENNReal.ofReal K' * ENNReal.ofReal aC + ENNReal.ofReal (σ * K') * ENNReal.ofReal e) *
            ENNReal.ofReal t * X +
          (ENNReal.ofReal K' * ENNReal.ofReal b + ENNReal.ofReal (σ * K') * ENNReal.ofReal g) *
            Fn)))) ≤
      ENNReal.ofReal ((c0 * (10 + 3 * cv + K' * C * (1 + 2 * cv) + 24 * K' * C ^ 2)) * δ *
          (Real.sqrt σ)⁻¹ * Real.sqrt ν) * X +
        ENNReal.ofReal ((c0 * (10 + 3 * cv + K' * C * (1 + 2 * cv) + 24 * K' * C ^ 2)) *
          (k ^ A)⁻¹) * (Y + ENNReal.ofReal L3 * Fn) := by
  have hk1 : 1 ≤ k := by linarith only [hk]
  have hk0 : 0 < k := by linarith only [hk]
  have hσ0 : 0 < σ := lt_of_lt_of_le hν0 hσν
  have hc3' : 0 ≤ c3 := by
    by_contra h
    have := mul_neg_of_neg_of_pos (not_le.1 h) hL3
    linarith only [this, hc3]
  have hPn0 : 0 ≤ Pn := by rw [hPn]; positivity
  have hδb := l2e_delta_bounds hk hε0 hε1 hρ hρ1
  rw [← hδ] at hδb
  have hδ0 : 0 ≤ δ := by
    have : 0 ≤ ε * k ^ (-(1 / 2 : ℝ)) := by positivity
    linarith only [hδb.1, this]
  have hδlow : ε ≤ δ * Real.sqrt k := by
    have h1 : k ^ (-(1 / 2 : ℝ)) = (Real.sqrt k)⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hk0.le]
    have h2 := hδb.1
    rw [h1, mul_inv_le_iff₀ (Real.sqrt_pos.2 hk0)] at h2
    linarith only [h2]
  have hsc : 0 ≤ C * Real.sqrt σ * δ * Real.sqrt ν := by positivity
  have he0 : 0 ≤ e := by
    rw [he]; exact mul_nonneg (mul_nonneg hC (inv_nonneg.2 (Real.sqrt_nonneg _))) (Real.sqrt_nonneg _)
  have haC0 : 0 ≤ aC := by rw [haC]; exact hsc
  have hw0 : 0 ≤ C * (3 * Pn) / ν := by positivity
  have hb0 : 0 ≤ b := by
    rw [hb]
    exact mul_nonneg (add_nonneg haC0 (mul_nonneg hC (add_nonneg (abs_nonneg _)
      (Real.rpow_nonneg hk0.le _)))) hw0
  have hg0 : 0 ≤ g := by rw [hg]; exact mul_nonneg (add_nonneg he0 hC) hw0
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  have hσi0 : 0 ≤ σ⁻¹ := inv_nonneg.2 hσ0.le
  have hexp := l2e_expand X Y Fn (c3 := c3) (c0 := c0) (p := p) (Λ := L3) (sI := σ⁻¹) (κ := K')
    (a := aC) (b := b) (t := t) (sk := σ * K') (e := e) (g := g) hc3' hc0 hp0 hL3.le hσi0 hK' haC0
    hb0 ht0 (mul_nonneg hσ0.le hK') he0 hg0
  rw [hexp]
  have hthr' : 1 ≤ k * ν ^ 2 := by
    have : k * ν ^ 2 ≥ k * ε * ν ^ 2 := by
      have : 0 ≤ k * ν ^ 2 := by positivity
      nlinarith only [hε1, this]
    linarith only [hthr, this]
  have hcX := l2e_cX (A := A) hk1 hε0 hν0 hν1 hσν hσk hδ0 hδlow hthr hC hK' hc0 hcv hc3 hPn hp hR0
    hRk ht0 htk haC he
  have hcY := l2e_cY (A := A) hk1 hc0 hcv hc3 hPn hp hR0 hRk ht0 htk
  have hcF := l2e_cF (A := A) hk1 hν0 hν1 hσν hσk hδ0 hδb.2 hρ1 hC hK' hc0 hc3 hL3 hPn hp hR0 hRk
    hthr' haC he hb hg
  set Cs : ℝ := c0 * (10 + 3 * cv + K' * C * (1 + 2 * cv) + 24 * K' * C ^ 2) with hCs
  have hQ0 : 0 ≤ (k ^ A) ⁻¹ := inv_nonneg.2 (pow_nonneg hk0.le A)
  have hT0 : 0 ≤ δ * (Real.sqrt σ)⁻¹ * Real.sqrt ν := by positivity
  have hKC : 0 ≤ K' * C := mul_nonneg hK' hC
  have hCsX : c0 * (5 + cv + K' * C * (1 + 2 * cv)) ≤ Cs := by
    rw [hCs]
    refine mul_le_mul_of_nonneg_left ?_ hc0
    nlinarith only [hcv, hKC, mul_nonneg hKC hcv, mul_nonneg hK' (sq_nonneg C)]
  have hCsY : c0 * (5 + 2 * cv) ≤ Cs := by
    rw [hCs]
    refine mul_le_mul_of_nonneg_left ?_ hc0
    nlinarith only [hcv, hKC, mul_nonneg hKC hcv, mul_nonneg hK' (sq_nonneg C)]
  have hCsF : c0 * (24 * K' * C ^ 2 + 5) ≤ Cs := by
    rw [hCs]
    refine mul_le_mul_of_nonneg_left ?_ hc0
    nlinarith only [hcv, hKC, mul_nonneg hKC hcv, mul_nonneg hK' (sq_nonneg C)]
  have tX : c3 * c0 * (p + L3 * (σ⁻¹ * (K' * aC) + t + σ⁻¹ * ((K' * aC + (σ * K') * e) * t))) ≤
      Cs * δ * (Real.sqrt σ)⁻¹ * Real.sqrt ν := by
    refine hcX.trans ?_
    calc c0 * (5 + cv + K' * C * (1 + 2 * cv)) * (δ * (Real.sqrt σ)⁻¹ * Real.sqrt ν)
        ≤ Cs * (δ * (Real.sqrt σ)⁻¹ * Real.sqrt ν) := mul_le_mul_of_nonneg_right hCsX hT0
      _ = Cs * δ * (Real.sqrt σ)⁻¹ * Real.sqrt ν := by ring
  have tY : c3 * c0 * (p + L3 * (t + t)) ≤ Cs * (k ^ A)⁻¹ :=
    hcY.trans (mul_le_mul_of_nonneg_right hCsY hQ0)
  have tF : c3 * c0 * (L3 * (σ⁻¹ * (K' * b) + σ⁻¹ * p + σ⁻¹ * (K' * b + (σ * K') * g))) ≤
      Cs * (k ^ A)⁻¹ * L3 := by
    refine hcF.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCsF hQ0) hL3.le
  have hCs0 : 0 ≤ Cs := by rw [hCs]; positivity
  calc _ ≤ ENNReal.ofReal (Cs * δ * (Real.sqrt σ)⁻¹ * Real.sqrt ν) * X +
        ENNReal.ofReal (Cs * (k ^ A)⁻¹) * Y + ENNReal.ofReal (Cs * (k ^ A)⁻¹ * L3) * Fn := by
        gcongr
    _ = _ := by
        rw [ENNReal.ofReal_mul (mul_nonneg hCs0 hQ0)]
        ring


/-- Satisfiability of the parameter bounds: `k = 10`, `ν = ε = σ = 1`, `ρ = 1/2`, `A = 0`,
`R = 10⁻³`, `t = 0`. -/
example : True := by
  have _ := l2e_block_ineq (A := 0) 0 0 0 (k := 10) (ν := 1) (ε := 1) (ρ := 1 / 2) (σ := 1)
    (δ := deltaScale 1 (1 / 2) 10) (C := 1) (K' := 1) (c0 := 1) (cv := 1) (R := 1 / 1000)
    (t := 0) (c3 := 1) (L3 := 1) (Pn := 1 / 1000) (p := 5 / 1000)
    (aC := 1 * Real.sqrt 1 * deltaScale 1 (1 / 2) 10 * Real.sqrt 1)
    (e := 1 * (Real.sqrt 1)⁻¹ * Real.sqrt 1)
    (b := (1 * Real.sqrt 1 * deltaScale 1 (1 / 2) 10 * Real.sqrt 1 +
      1 * (|(1 : ℝ) - 1| + (10 : ℝ) ^ (1 + (1 / 2 : ℝ)))) * (1 * (3 * (1 / 1000)) / 1))
    (g := (1 * (Real.sqrt 1)⁻¹ * Real.sqrt 1 + 1) * (1 * (3 * (1 / 1000)) / 1))
    (hk := by norm_num) (hε0 := one_pos) (hε1 := le_rfl) (hρ := by norm_num) (hρ1 := by norm_num)
    (hν0 := one_pos) (hν1 := le_rfl) (hσν := le_rfl) (hσk := by norm_num) (hδ := rfl)
    (hthr := by norm_num) (hC := zero_le_one) (hK' := zero_le_one) (hc0 := zero_le_one)
    (hcv := zero_le_one) (hc3 := by norm_num) (hL3 := one_pos) (hPn := by norm_num)
    (hp := by norm_num) (hR0 := by norm_num) (hRk := by norm_num) (ht0 := le_rfl)
    (htk := by norm_num) (haC := rfl) (he := rfl) (hb := rfl) (hg := rfl)
  trivial


variable {d : ℕ}

theorem l2e_smul_inv_smul {l : ℝ} (hl : 0 < l) (V : Set (Vec d)) : l • (l⁻¹ • V) = V := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hl.ne', Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hl.ne'),
    inv_inv, smul_smul, mul_inv_cancel₀ hl.ne', one_smul]

theorem l2e_volume_engCube_le (k : ℕ) (V : Set (Vec d)) (hV : V ⊆ Section6.engCube d k) :
    volume V ≤ ENNReal.ofReal (((3 : ℝ) ^ k) ^ d) := by
  have h1 : volume V ≤ volume (l2b_cell (0 : Vec d) k) := by
    refine measure_mono (hV.trans ?_)
    unfold l2b_cell
    rw [translateSet_zero]
    exact openCubeSet_subset_cubeSet _
  refine h1.trans (le_of_eq ?_)
  rw [l2b_volume_cell]
  simp [zpow_natCast]


/-- **Geometry of the dilated domain**: the uniform data of `V = 3^k U`, the volume bound
`|V|^{1/d} ≤ 3^k`, and the layer ratio `|layer| / |V| ≤ c 3^{n-k}`. -/
theorem l2e_geom [NeZero d] (r' M₁' D' : ℝ) :
    ∃ cvol : ℝ, 0 < cvol ∧ ∀ {M₂' : ℝ} {k n : ℕ} {V : Set (Vec d)}, V ⊆ Section6.engCube d k →
      IsUniformC11Domain (((3 : ℝ) ^ k)⁻¹ • V) r' M₁' M₂' D' → V.Nonempty →
      12 * (3 : ℝ) ^ n ≤ (3 : ℝ) ^ k * r' →
      IsUniformC11Domain V ((3 : ℝ) ^ k * r') M₁' (M₂' / (3 : ℝ) ^ k) ((3 : ℝ) ^ k * D') ∧
        volume V ≠ 0 ∧ volume V ^ (1 / (d : ℝ)) ≤ ENNReal.ofReal ((3 : ℝ) ^ k) ∧
        volume (boundaryLayer V (3 * (4 * (3 : ℝ) ^ n))) / volume V ≤
          ENNReal.ofReal (cvol * ((3 : ℝ) ^ n / (3 : ℝ) ^ k)) := by
  by_cases hr' : 0 < r'
  swap
  · refine ⟨1, one_pos, ?_⟩
    intro M₂' k n V _ hU
    exact absurd hU.2.1 hr'
  obtain ⟨C1, hC1, HL⟩ := exists_volume_boundaryLayer_smul_le (d := d) r' M₁' D' hr'
  obtain ⟨c, hc, Hc⟩ := lip_inner_ball_volume d M₁'
  refine ⟨12 * C1 / (c * r' ^ d) + 1, by positivity, ?_⟩
  intro M₂' k n V hV hU hne h12
  have hl : 0 < (3 : ℝ) ^ k := by positivity
  set l : ℝ := (3 : ℝ) ^ k with hldef
  have hVU : l • (l⁻¹ • V) = V := l2e_smul_inv_smul hl V
  have hUV : IsUniformC11Domain V (l * r') M₁' (M₂' / l) (l * D') := by
    have := hU.smul hl
    rwa [hVU] at this
  have hUne : (l⁻¹ • V).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨l⁻¹ • x, Set.smul_mem_smul_set hx⟩
  have hvolU := Hc (l⁻¹ • V) r' M₂' D' hU hUne
  have hvolV : volume V = ENNReal.ofReal (l ^ d) * volume (l⁻¹ • V) := by
    conv_lhs => rw [← hVU]
    rw [Measure.addHaar_smul, abs_of_pos (pow_pos hl _)]
    simp only [Module.finrank_pi, Fintype.card_fin]
  have hlow : ENNReal.ofReal (l ^ d * (c * r' ^ d)) ≤ volume V := by
    rw [hvolV, ENNReal.ofReal_mul (pow_nonneg hl.le _)]
    exact mul_le_mul' le_rfl hvolU
  have hpos : 0 < l ^ d * (c * r' ^ d) := by positivity
  have hVne : volume V ≠ 0 :=
    (lt_of_lt_of_le (ENNReal.ofReal_pos.2 hpos) hlow).ne'
  refine ⟨hUV, hVne, ?_, ?_⟩
  · have h1 := ENNReal.rpow_le_rpow (l2e_volume_engCube_le k V hV)
      (show 0 ≤ 1 / (d : ℝ) by positivity)
    refine h1.trans (le_of_eq ?_)
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity), one_div,
      Real.pow_rpow_inv_natCast hl.le (NeZero.ne d)]
  · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne d)
    have hlay := HL hU l hl (3 * (4 * (3 : ℝ) ^ n)) (by positivity) (by linarith only [h12])
    rw [hVU] at hlay
    refine (ENNReal.div_le_div hlay hlow).trans ?_
    rw [← ENNReal.ofReal_div_of_pos hpos]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hm]
    simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
    have hr'p : 0 < r' ^ (m + 1) := by positivity
    have e : C1 * (3 * (4 * (3 : ℝ) ^ n)) * l ^ m / (l ^ (m + 1) * (c * r' ^ (m + 1))) =
        12 * C1 / (c * r' ^ (m + 1)) * ((3 : ℝ) ^ n / l) := by
      field_simp
      ring
    rw [e]
    have : (12 * C1 / (c * r' ^ (m + 1)) + 1) * ((3 : ℝ) ^ n / l) ≥
        12 * C1 / (c * r' ^ (m + 1)) * ((3 : ℝ) ^ n / l) := by
      have : 0 ≤ (3 : ℝ) ^ n / l := by positivity
      nlinarith only [this]
    exact this


/-- The standard bump is bounded and Lipschitz. -/
theorem l2e_bump_lip (d : ℕ) :
    ∃ (B : ℝ) (L : ℝ≥0), (∀ w, |li1_bump d w| ≤ B) ∧ LipschitzWith L (li1_bump d) := by
  obtain ⟨B, hB⟩ := (li1_bump_contDiff d).continuous.bounded_above_of_compact_support
    (li1_bump_compact d)
  obtain ⟨L, hL⟩ := (li1_bump_contDiff d).lipschitzWith_of_hasCompactSupport (li1_bump_compact d)
    l2d_top_ne_zero
  exact ⟨B, L, fun w => by simpa [Real.norm_eq_abs] using hB w, hL⟩

/-- The bound of the standard bump. -/
noncomputable def l2e_bumpB (d : ℕ) : ℝ := (l2e_bump_lip d).choose

/-- The Lipschitz constant of the standard bump. -/
noncomputable def l2e_bumpL (d : ℕ) : ℝ≥0 := (l2e_bump_lip d).choose_spec.choose

theorem l2e_bump_bound (d : ℕ) (w : Vec d) : |li1_bump d w| ≤ l2e_bumpB d :=
  (l2e_bump_lip d).choose_spec.choose_spec.1 w

theorem l2e_bump_lipschitz (d : ℕ) : LipschitzWith (l2e_bumpL d) (li1_bump d) :=
  (l2e_bump_lip d).choose_spec.choose_spec.2

/-- The kernel constant `3^d (6 L + A)` of the mollified flux bounds, for the standard bump. -/
noncomputable def l2e_Kp (d : ℕ) : ℝ := 3 ^ d * (6 * (l2e_bumpL d : ℝ) + l2e_bumpB d)

/-- The mollifier ball of a point of the cell `z + □_n` lies in the cell `z + □_{n+1}`. -/
theorem l2e_ball_cell {n : ℕ} {z x y : Vec d} (hx : x ∈ l2b_cell z n) (hy : dist y x ≤ (3 : ℝ) ^ n) :
    y ∈ l2b_cell z (n + 1) := by
  rw [l2b_mem_cell] at hx ⊢
  intro i
  have h1 : |y i - x i| ≤ (3 : ℝ) ^ n := by
    have := (dist_pi_le_iff (by positivity)).1 hy i
    rwa [Real.dist_eq] at this
  have h2 := abs_le.1 h1
  obtain ⟨hx1, hx2⟩ := hx i
  have e : (3 : ℝ) ^ (n + 1) = 3 * 3 ^ n := by ring
  rw [e]
  constructor <;> linarith only [h2.1, h2.2, hx1, hx2]

/-- Mollification at a point of a good cell only sees the values on the domain. -/
theorem l2e_mollify_congr {V : Set (Vec d)} {n : ℕ} {z x : Vec d}
    (hcell : l2b_cell z (n + 1) ⊆ V) (hx : x ∈ l2b_cell z n) {η : Vec d → ℝ}
    (hηs : ∀ w, (∃ i, 1 < |w i|) → η w = 0) {G H : Vec d → Vec d} (h : ∀ y ∈ V, G y = H y) :
    a16_mollify d ((3 : ℝ) ^ n) η G x = a16_mollify d ((3 : ℝ) ^ n) η H x := by
  funext i
  exact l2a_moll_congr (by positivity) hηs fun y hy =>
    congrFun (h y (hcell (l2e_ball_cell hx hy))) i

end SuperdiffusionCLT.Section7
