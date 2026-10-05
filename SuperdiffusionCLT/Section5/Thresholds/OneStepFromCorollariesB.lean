/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Real


/-!
# Pure algebra of the one-step proposition
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

/-- From the two one-sided ratio
bounds with `m = n + h`, absorb `C h² s⁻⁴ ≤ C s⁻²`, invert the lower ratio via
`1/(1-x) ≥ 1 + x`, and multiply by `s`. Here `s = shom_n`, `s' = shom_{n+h}`, `a = c⋆ log 3`,
`ℓ2 = log² n`, `Lm = log²(n+h)`. -/
theorem one_step_algebra {s s' a h C K ℓ2 Lm : ℝ} (hs : 0 < s) (hs' : 0 < s')
    (ha : 0 < a) (hh1 : 1 ≤ h) (hhs : h ≤ s) (has : 2 * a ≤ s) (hC : 1 ≤ C) (hK : 0 ≤ K)
    (hℓ : 1 ≤ ℓ2) (hLm0 : 0 ≤ Lm) (hLm : Lm ≤ 4 * ℓ2)
    (hup : s' * s⁻¹ ≤ 1 + (a * h + C * (Lm + K)) * s ^ (-(2 : ℝ)) +
      C * s ^ (-(4 : ℝ)) * h ^ (2 : ℝ))
    (hlow : s * s'⁻¹ ≤ 1 + (-(a * h) + C * (Lm + K)) * s ^ (-(2 : ℝ)) +
      C * s ^ (-(4 : ℝ)) * h ^ (2 : ℝ)) :
    |s' - s - a * s⁻¹ * h| ≤ 5 * C * (ℓ2 + K) * s⁻¹ := by
  have e2 : s ^ (-(2 : ℝ)) = (s ^ 2)⁻¹ := by
    rw [Real.rpow_neg hs.le]; norm_cast
  have e4 : s ^ (-(4 : ℝ)) = (s ^ 4)⁻¹ := by
    rw [Real.rpow_neg hs.le]; norm_cast
  have eh : h ^ (2 : ℝ) = h ^ 2 := by norm_cast
  rw [e2, e4, eh] at hup hlow
  have hh0 : 0 < h := by linarith only [hh1]
  have hC0 : 0 < C := by linarith only [hC]
  have hs2 : 0 < s ^ 2 := by positivity
  -- E ≤ B s⁻²
  have hE : C * (Lm + K) * (s ^ 2)⁻¹ + C * (s ^ 4)⁻¹ * h ^ 2 ≤
      5 * C * (ℓ2 + K) * (s ^ 2)⁻¹ := by
    have h1 : C * (s ^ 4)⁻¹ * h ^ 2 ≤ C * (s ^ 2)⁻¹ := by
      have : h ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hh0.le hhs 2
      have e : (s ^ 4)⁻¹ * h ^ 2 = (s ^ 2)⁻¹ * (h ^ 2 / s ^ 2) := by field_simp
      have hd : h ^ 2 / s ^ 2 ≤ 1 := (div_le_one hs2).2 this
      calc C * (s ^ 4)⁻¹ * h ^ 2 = C * ((s ^ 4)⁻¹ * h ^ 2) := by ring
        _ = C * ((s ^ 2)⁻¹ * (h ^ 2 / s ^ 2)) := by rw [e]
        _ ≤ C * ((s ^ 2)⁻¹ * 1) := by
          gcongr
        _ = C * (s ^ 2)⁻¹ := by ring
    have hi : 0 < (s ^ 2)⁻¹ := inv_pos.2 hs2
    have h2 : C * (Lm + K) * (s ^ 2)⁻¹ + C * (s ^ 2)⁻¹ ≤ 5 * C * (ℓ2 + K) * (s ^ 2)⁻¹ := by
      have : C * (Lm + K) + C ≤ 5 * C * (ℓ2 + K) := by
        nlinarith only [hC0, hLm, hℓ, hK, mul_nonneg hC0.le hK]
      nlinarith only [this, hi]
    linarith only [h1, h2]
  set X : ℝ := a * h * (s ^ 2)⁻¹ with hX
  set E : ℝ := C * (Lm + K) * (s ^ 2)⁻¹ + C * (s ^ 4)⁻¹ * h ^ 2 with hEd
  have hB : 0 ≤ E := by
    have : 0 ≤ C * (Lm + K) := by positivity
    positivity
  have hup' : s' * s⁻¹ ≤ 1 + X + E := by
    have : (a * h + C * (Lm + K)) * (s ^ 2)⁻¹ + C * (s ^ 4)⁻¹ * h ^ 2 = X + E := by
      rw [hX, hEd]; ring
    linarith only [hup, this]
  have hlow' : s * s'⁻¹ ≤ 1 - X + E := by
    have : (-(a * h) + C * (Lm + K)) * (s ^ 2)⁻¹ + C * (s ^ 4)⁻¹ * h ^ 2 = -X + E := by
      rw [hX, hEd]; ring
    linarith only [hlow, this]
  have hX2 : X ≤ 1 / 2 := by
    have : a * h * (s ^ 2)⁻¹ ≤ a * s * (s ^ 2)⁻¹ := by
      gcongr
    have e : a * s * (s ^ 2)⁻¹ = a / s := by field_simp
    have : a / s ≤ 1 / 2 := by
      rw [div_le_iff₀ hs]; linarith only [has]
    linarith only [this, e, ‹a * h * (s ^ 2)⁻¹ ≤ a * s * (s ^ 2)⁻¹›]
  have hX0 : 0 ≤ X := by positivity
  -- lower inversion
  have hlowinv : 1 + X - E ≤ s' * s⁻¹ := by
    have hx1 : 0 < 1 - (X - E) := by linarith only [hX2, hB]
    have hq : s * s'⁻¹ ≤ 1 - (X - E) := by linarith only [hlow']
    have hr : 0 < s * s'⁻¹ := by positivity
    have h3 : 1 ≤ (1 - (X - E)) * (s' * s⁻¹) := by
      have : s * s'⁻¹ * (s' * s⁻¹) = 1 := by field_simp
      calc (1 : ℝ) = s * s'⁻¹ * (s' * s⁻¹) := this.symm
        _ ≤ (1 - (X - E)) * (s' * s⁻¹) := by
          apply mul_le_mul_of_nonneg_right hq; positivity
    by_contra hcon
    have hcon := lt_of_not_ge hcon
    have hpos : 0 < s' * s⁻¹ := by positivity
    have h4 := mul_lt_mul_of_pos_left hcon hx1
    nlinarith only [h3, h4, sq_nonneg (X - E)]
  have key : s' - s - a * s⁻¹ * h = s * (s' * s⁻¹ - 1 - X) := by
    rw [hX]; field_simp
  have hEB : E ≤ 5 * C * (ℓ2 + K) * (s ^ 2)⁻¹ := hE
  have hsB : s * (5 * C * (ℓ2 + K) * (s ^ 2)⁻¹) = 5 * C * (ℓ2 + K) * s⁻¹ := by
    field_simp
  rw [key, abs_le]
  constructor
  · have : -(5 * C * (ℓ2 + K) * (s ^ 2)⁻¹) ≤ s' * s⁻¹ - 1 - X := by linarith only [hlowinv, hEB]
    calc -(5 * C * (ℓ2 + K) * s⁻¹) = s * (-(5 * C * (ℓ2 + K) * (s ^ 2)⁻¹)) := by rw [← hsB]; ring
      _ ≤ s * (s' * s⁻¹ - 1 - X) := mul_le_mul_of_nonneg_left this hs.le
  · have : s' * s⁻¹ - 1 - X ≤ 5 * C * (ℓ2 + K) * (s ^ 2)⁻¹ := by linarith only [hup', hEB]
    calc s * (s' * s⁻¹ - 1 - X) ≤ s * (5 * C * (ℓ2 + K) * (s ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left this hs.le
      _ = _ := hsB

end SuperdiffusionCLT.Section5
