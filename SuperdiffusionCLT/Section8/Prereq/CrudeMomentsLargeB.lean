/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# A stretched-exponential absorption inequality

The localized tail at shift `1 / t` is a polynomial in `t` and `s` times an exponential whose rate is
`r₁ s / (Λ₁ g ^ n)` with `g = ℓ + log (1 + s)`.  Beyond the cutting radius `(W₀ ℓ) ^ (2 n)` the
whole expression is at most `exp (-κ sqrt s)`, with `κ` and `W₀` independent of `ℓ` and `t`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

noncomputable section

/-- The expression to be absorbed. -/
def crudeMomL_phi (d n : ℕ) (Cc Λ₁ r₁ Aq ℓ t s : ℝ) : ℝ :=
  Cc * (Λ₁ * (ℓ + Real.log (1 + s)) ^ n + (1 + s) ^ 2) * (Aq * t * (1 + s) ^ 2) ^ d *
    Real.exp (-(r₁ * s / (Λ₁ * (ℓ + Real.log (1 + s)) ^ n)))

theorem crudeMomL_log_one_add_le {n : ℕ} (hn : 1 ≤ n) {w : ℝ} (hw : 1 ≤ w) :
    Real.log (1 + w ^ (2 * n)) ≤ 4 * n * w := by
  have hw0 : 0 < w := lt_of_lt_of_le zero_lt_one hw
  have h1 : (1 : ℝ) ≤ w ^ (2 * n) := one_le_pow₀ hw
  have h2 : (2 : ℝ) ≤ 2 ^ (2 * n) := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * n) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h3 : 1 + w ^ (2 * n) ≤ (2 * w) ^ (2 * n) := by
    rw [mul_pow]
    nlinarith only [h1, h2]
  have h4 : Real.log (1 + w ^ (2 * n)) ≤ Real.log ((2 * w) ^ (2 * n)) :=
    Real.log_le_log (by positivity) h3
  rw [Real.log_pow] at h4
  have h5 := Real.log_le_sub_one_of_pos (show 0 < 2 * w by positivity)
  have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  push_cast at h4
  calc _ ≤ 2 * (n : ℝ) * Real.log (2 * w) := h4
    _ ≤ 2 * (n : ℝ) * (2 * w - 1) := mul_le_mul_of_nonneg_left h5 (by positivity)
    _ ≤ 4 * n * w := by nlinarith only [hn']

/-- The expression to be absorbed, in the variable `w` with `s = w ^ (2 n)`. -/
theorem crudeMomL_phi_le_wform (d n : ℕ) (hn : 1 ≤ n) {Cc Λ₁ r₁ Aq : ℝ} (hCc : 0 ≤ Cc)
    (hΛ : 0 < Λ₁) (hr : 0 < r₁) (hAq : 0 < Aq) {ℓ t w : ℝ} (hℓ : 1 ≤ ℓ) (ht : 1 ≤ t)
    (htl : Real.log t ≤ ℓ) (hℓw : ℓ ≤ w) :
    crudeMomL_phi d n Cc Λ₁ r₁ Aq ℓ t (w ^ (2 * n)) ≤
      Cc * (Λ₁ * (1 + 4 * n) ^ n + 4) * (4 * Aq) ^ d *
        (w ^ (4 * n + 4 * n * d) * Real.exp (d * w)) *
        Real.exp (-(r₁ / (Λ₁ * (1 + 4 * n) ^ n) * w ^ n)) := by
  have hw1 : 1 ≤ w := hℓ.trans hℓw
  have hw0 : 0 < w := lt_of_lt_of_le zero_lt_one hw1
  set s : ℝ := w ^ (2 * n) with hs
  have hs1 : 1 ≤ s := one_le_pow₀ hw1
  have hlog0 : 0 ≤ Real.log (1 + s) := Real.log_nonneg (by linarith only [hs1])
  have hlog : Real.log (1 + s) ≤ 4 * n * w := crudeMomL_log_one_add_le hn hw1
  set g : ℝ := ℓ + Real.log (1 + s) with hg
  have hg1 : 1 ≤ g := by linarith only [hℓ, hlog0]
  have hg0 : 0 < g := lt_of_lt_of_le zero_lt_one hg1
  have hgw : g ≤ (1 + 4 * n) * w := by
    have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith only [hlog, hℓw, hn', hw0]
  set Γ : ℝ := (1 + 4 * (n : ℝ)) ^ n with hΓ
  have hΓ0 : 0 < Γ := by positivity
  have hgn : g ^ n ≤ Γ * w ^ n := by
    calc g ^ n ≤ ((1 + 4 * (n : ℝ)) * w) ^ n := pow_le_pow_left₀ hg0.le hgw n
      _ = Γ * w ^ n := mul_pow _ _ _
  have hgn0 : 0 < g ^ n := pow_pos hg0 n
  have hwn : 0 < w ^ n := pow_pos hw0 n
  -- the exponential factor
  have hexp : Real.exp (-(r₁ * s / (Λ₁ * g ^ n))) ≤
      Real.exp (-(r₁ / (Λ₁ * Γ) * w ^ n)) := by
    apply Real.exp_le_exp.2
    apply neg_le_neg
    have hss : s = w ^ n * w ^ n := by rw [hs, two_mul, pow_add]
    calc r₁ / (Λ₁ * Γ) * w ^ n = r₁ * s / (Λ₁ * (Γ * w ^ n)) := by
          rw [hss]; field_simp
      _ ≤ r₁ * s / (Λ₁ * g ^ n) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left hgn hΛ.le
  -- the polynomial factors
  have hwn4 : w ^ n ≤ w ^ (4 * n) := pow_le_pow_right₀ hw1 (by omega)
  have hs2 : (1 + s) ^ 2 ≤ 4 * w ^ (4 * n) := by
    have : (1 + s) ^ 2 ≤ (2 * s) ^ 2 :=
      pow_le_pow_left₀ (by linarith only [hs1]) (by linarith only [hs1]) 2
    calc (1 + s) ^ 2 ≤ (2 * s) ^ 2 := this
      _ = 4 * w ^ (4 * n) := by
        rw [mul_pow, hs, ← pow_mul]
        have : 2 * n * 2 = 4 * n := by ring
        rw [this]; norm_num
  have hP1 : Λ₁ * g ^ n + (1 + s) ^ 2 ≤ (Λ₁ * Γ + 4) * w ^ (4 * n) := by
    have h1 : Λ₁ * g ^ n ≤ Λ₁ * Γ * w ^ (4 * n) :=
      calc Λ₁ * g ^ n ≤ Λ₁ * (Γ * w ^ n) := mul_le_mul_of_nonneg_left hgn hΛ.le
        _ ≤ Λ₁ * (Γ * w ^ (4 * n)) := by gcongr
        _ = _ := by ring
    linarith only [h1, hs2]
  have htexp : t ≤ Real.exp w := by
    calc t = Real.exp (Real.log t) := (Real.exp_log (lt_of_lt_of_le zero_lt_one ht)).symm
      _ ≤ Real.exp w := Real.exp_le_exp.2 (htl.trans hℓw)
  have hP2 : (Aq * t * (1 + s) ^ 2) ^ d ≤
      (4 * Aq) ^ d * (w ^ (4 * n * d) * Real.exp (d * w)) := by
    have h1 : Aq * t * (1 + s) ^ 2 ≤ (4 * Aq) * (w ^ (4 * n) * Real.exp w) := by
      calc Aq * t * (1 + s) ^ 2 ≤ Aq * Real.exp w * (4 * w ^ (4 * n)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left htexp hAq.le) hs2 (by positivity) (by positivity)
        _ = _ := by ring
    calc (Aq * t * (1 + s) ^ 2) ^ d ≤ ((4 * Aq) * (w ^ (4 * n) * Real.exp w)) ^ d :=
          pow_le_pow_left₀ (by positivity) h1 d
      _ = _ := by
        rw [mul_pow (4 * Aq), mul_pow (w ^ (4 * n)), ← pow_mul, ← Real.exp_nat_mul]
  have hphi : crudeMomL_phi d n Cc Λ₁ r₁ Aq ℓ t s =
      Cc * (Λ₁ * g ^ n + (1 + s) ^ 2) * (Aq * t * (1 + s) ^ 2) ^ d *
        Real.exp (-(r₁ * s / (Λ₁ * g ^ n))) := rfl
  rw [hphi]
  have hA : 0 ≤ Λ₁ * g ^ n + (1 + s) ^ 2 := by positivity
  have hB : 0 ≤ (Aq * t * (1 + s) ^ 2) ^ d := by
    have : 0 ≤ t := by linarith only [ht]
    positivity
  calc Cc * (Λ₁ * g ^ n + (1 + s) ^ 2) * (Aq * t * (1 + s) ^ 2) ^ d *
        Real.exp (-(r₁ * s / (Λ₁ * g ^ n)))
      ≤ Cc * ((Λ₁ * Γ + 4) * w ^ (4 * n)) * ((4 * Aq) ^ d * (w ^ (4 * n * d) * Real.exp (d * w))) *
        Real.exp (-(r₁ / (Λ₁ * Γ) * w ^ n)) := by
        refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hP1 hCc) hP2 hB (by positivity))
          hexp (Real.exp_pos _).le (by positivity)
    _ = _ := by
      rw [show 4 * n + 4 * n * d = 4 * n + 4 * n * d from rfl, pow_add]
      ring

/-- The decay constant of the absorbed bound. -/
def crudeMomL_kappa (n : ℕ) (Λ₁ r₁ : ℝ) : ℝ := r₁ / (Λ₁ * (1 + 4 * (n : ℝ)) ^ n) / 2

/-- The cutting constant of the absorbed bound. -/
def crudeMomL_W0 (d n : ℕ) (Cc Λ₁ r₁ Aq : ℝ) : ℝ :=
  max 1 ((Cc * (Λ₁ * (1 + 4 * (n : ℝ)) ^ n + 4) * (4 * Aq) ^ d +
    ((4 * n + 4 * n * d : ℕ) : ℝ) + d) / crudeMomL_kappa n Λ₁ r₁)

theorem crudeMomL_kappa_pos (n : ℕ) {Λ₁ r₁ : ℝ} (hΛ : 0 < Λ₁) (hr : 0 < r₁) :
    0 < crudeMomL_kappa n Λ₁ r₁ := by
  unfold crudeMomL_kappa; positivity

theorem crudeMomL_one_le_W0 (d n : ℕ) (Cc Λ₁ r₁ Aq : ℝ) : 1 ≤ crudeMomL_W0 d n Cc Λ₁ r₁ Aq :=
  le_max_left _ _

/-- The `w`-form absorption: beyond `W₀ ℓ` the expression is at most `exp (-κ w ^ n)`. -/
theorem crudeMomL_exists_absorb (d n : ℕ) (hn : 2 ≤ n) {Cc Λ₁ r₁ Aq : ℝ} (hCc : 0 ≤ Cc)
    (hΛ : 0 < Λ₁) (hr : 0 < r₁) (hAq : 0 < Aq) :
    ∀ ℓ t w : ℝ, 1 ≤ ℓ → 1 ≤ t → Real.log t ≤ ℓ → crudeMomL_W0 d n Cc Λ₁ r₁ Aq * ℓ ≤ w →
      crudeMomL_phi d n Cc Λ₁ r₁ Aq ℓ t (w ^ (2 * n)) ≤
          Real.exp (-(crudeMomL_kappa n Λ₁ r₁ * w ^ n)) ∧
        Real.exp (-(crudeMomL_kappa n Λ₁ r₁ * w ^ n)) ≤ 1 / 2 := by
  set Γ : ℝ := (1 + 4 * (n : ℝ)) ^ n with hΓ
  have hΓ0 : 0 < Γ := by positivity
  set κ : ℝ := crudeMomL_kappa n Λ₁ r₁ with hκ
  have hκdef : κ = r₁ / (Λ₁ * Γ) / 2 := rfl
  have hκ0 : 0 < κ := crudeMomL_kappa_pos n hΛ hr
  set C' : ℝ := Cc * (Λ₁ * Γ + 4) * (4 * Aq) ^ d with hC'
  have hC'0 : 0 ≤ C' := by positivity
  set N : ℝ := ((4 * n + 4 * n * d : ℕ) : ℝ) with hN
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  intro ℓ t w hℓ ht htl hW
  set W₀ : ℝ := crudeMomL_W0 d n Cc Λ₁ r₁ Aq with hW₀
  have hW₀def : W₀ = max 1 ((C' + N + d) / κ) := rfl
  have hW1 : 1 ≤ W₀ := le_max_left _ _
  have hℓw : ℓ ≤ w := by nlinarith only [hW, hW1, hℓ]
  have hw1 : 1 ≤ w := hℓ.trans hℓw
  have hw0 : 0 < w := lt_of_lt_of_le zero_lt_one hw1
  have hwW : W₀ ≤ w := by nlinarith only [hW, hW1, hℓ]
  have hcoef : (C' + N + d) ≤ κ * w := by
    have h1 : (C' + N + d) / κ ≤ w := (hW₀def ▸ le_max_right _ _).trans hwW
    rw [div_le_iff₀ hκ0] at h1
    linarith only [h1]
  have hwn2 : w ^ 2 ≤ w ^ n := pow_le_pow_right₀ hw1 hn
  have hkey : (C' + N + d) * w ≤ κ * w ^ n := by
    calc (C' + N + d) * w ≤ (κ * w) * w := mul_le_mul_of_nonneg_right hcoef hw0.le
      _ = κ * w ^ 2 := by ring
      _ ≤ κ * w ^ n := mul_le_mul_of_nonneg_left hwn2 hκ0.le
  have hone : 1 ≤ κ * w ^ n := by
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hNd : 1 ≤ N := by
      rw [hN]
      have : 1 ≤ 4 * n + 4 * n * d := by omega
      exact_mod_cast this
    nlinarith only [hkey, hC'0, hNd, hd0, hw1]
  refine ⟨?_, ?_⟩
  · have hw := crudeMomL_phi_le_wform d n (by omega) hCc hΛ hr hAq hℓ ht htl hℓw
    refine hw.trans ?_
    have hwN : w ^ (4 * n + 4 * n * d) ≤ Real.exp (N * w) := by
      calc w ^ (4 * n + 4 * n * d) ≤ (Real.exp w) ^ (4 * n + 4 * n * d) :=
            pow_le_pow_left₀ hw0.le (by linarith only [Real.add_one_le_exp w]) _
        _ = Real.exp (N * w) := by rw [← Real.exp_nat_mul, hN]
    have hrw : Cc * (Λ₁ * (1 + 4 * (n : ℝ)) ^ n + 4) * (4 * Aq) ^ d *
        (w ^ (4 * n + 4 * n * d) * Real.exp (d * w)) *
        Real.exp (-(r₁ / (Λ₁ * (1 + 4 * (n : ℝ)) ^ n) * w ^ n)) =
        C' * (w ^ (4 * n + 4 * n * d) * Real.exp (d * w)) *
        Real.exp (-(2 * κ * w ^ n)) := by
      rw [hC', hκdef, ← hΓ]; congr 3; ring
    rw [hrw]
    have h1 : C' * (w ^ (4 * n + 4 * n * d) * Real.exp (d * w)) ≤
        Real.exp ((C' + N + d) * w) := by
      calc C' * (w ^ (4 * n + 4 * n * d) * Real.exp (d * w))
          ≤ Real.exp C' * (Real.exp (N * w) * Real.exp (d * w)) := by
            refine mul_le_mul (by linarith only [Real.add_one_le_exp C']) ?_ (by positivity)
              (Real.exp_pos _).le
            exact mul_le_mul_of_nonneg_right hwN (Real.exp_pos _).le
        _ = Real.exp (C' + N * w + d * w) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
        _ ≤ Real.exp ((C' + N + d) * w) := by
            apply Real.exp_le_exp.2
            nlinarith only [hC'0, hw1]
    calc C' * (w ^ (4 * n + 4 * n * d) * Real.exp (d * w)) * Real.exp (-(2 * κ * w ^ n))
        ≤ Real.exp ((C' + N + d) * w) * Real.exp (-(2 * κ * w ^ n)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ ≤ Real.exp (κ * w ^ n) * Real.exp (-(2 * κ * w ^ n)) :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hkey) (Real.exp_pos _).le
      _ = Real.exp (-(κ * w ^ n)) := by rw [← Real.exp_add]; congr 1; ring
  · have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
    have h3 : Real.exp (-(κ * w ^ n)) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by linarith only [hone])
    rw [Real.exp_neg 1] at h3
    calc Real.exp (-(κ * w ^ n)) ≤ (Real.exp 1)⁻¹ := h3
      _ ≤ 1 / 2 := by
        rw [one_div]; exact inv_anti₀ (by norm_num) h2

/-- **The absorption inequality.**  With the constants `κ` and `W₀ ≥ 1` of the displayed
definitions, independent of `ℓ` and `t`, `Φ ≤ exp (-κ sqrt s) ≤ 1 / 2` for `s ≥ (W₀ ℓ) ^ (2 n)`. -/
theorem crudeMomL_absorb (d n : ℕ) (hn : 2 ≤ n) {Cc Λ₁ r₁ Aq : ℝ} (hCc : 0 ≤ Cc)
    (hΛ : 0 < Λ₁) (hr : 0 < r₁) (hAq : 0 < Aq) :
    ∀ ℓ t s : ℝ, 1 ≤ ℓ → 1 ≤ t → Real.log t ≤ ℓ →
      (crudeMomL_W0 d n Cc Λ₁ r₁ Aq * ℓ) ^ (2 * n) ≤ s →
      crudeMomL_phi d n Cc Λ₁ r₁ Aq ℓ t s ≤
          Real.exp (-(crudeMomL_kappa n Λ₁ r₁ * Real.sqrt s)) ∧
        Real.exp (-(crudeMomL_kappa n Λ₁ r₁ * Real.sqrt s)) ≤ 1 / 2 := by
  have h := crudeMomL_exists_absorb d n hn hCc hΛ hr hAq
  have hW₀ := crudeMomL_one_le_W0 d n Cc Λ₁ r₁ Aq
  set W₀ := crudeMomL_W0 d n Cc Λ₁ r₁ Aq
  intro ℓ t s hℓ ht htl hs
  have hn0 : 2 * n ≠ 0 := by omega
  have hs0 : 0 ≤ s := le_trans (by positivity : 0 ≤ (W₀ * ℓ) ^ (2 * n)) hs
  set w : ℝ := s ^ (((2 * n : ℕ) : ℝ)⁻¹) with hw
  have hw0 : 0 ≤ w := Real.rpow_nonneg hs0 _
  have hws : w ^ (2 * n) = s := Real.rpow_inv_natCast_pow hs0 hn0
  have hW : W₀ * ℓ ≤ w := by
    have hW0 : 0 ≤ W₀ * ℓ := by positivity
    rw [← hws] at hs
    exact (pow_le_pow_iff_left₀ hW0 hw0 hn0).1 hs
  have hsq : Real.sqrt s = w ^ n := by
    rw [← hws, show 2 * n = n * 2 by ring, pow_mul, Real.sqrt_sq (pow_nonneg hw0 n)]
  obtain ⟨h1, h2⟩ := h ℓ t w hℓ ht htl hW
  rw [hws] at h1
  rw [hsq]
  exact ⟨h1, h2⟩

end

end SuperdiffusionCLT.Section8
