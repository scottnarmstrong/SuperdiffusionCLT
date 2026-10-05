/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Ratio algebra for the reference comparison

Pure real algebra: from `|s⁻¹ A - 1|`, `|s B - 1|`, `|σ B' - 1|` and `|B - B'|` small, the two
quantities `|σ⁻¹ A - 1|` and `|σ B - 1|` are small, and `σ ≤ 3 s`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.NewMixing

noncomputable section

/-- Ratio algebra for the reference comparison: from the four scalar relations
`|s⁻¹ A - 1| ≤ e1`, `|s B - 1| ≤ e2`, `|σ B' - 1| ≤ e3`, `|B - B'| ≤ δ` conclude
`|σ⁻¹ A - 1| + |σ B - 1| ≤ e1 + 3 e2 + 4 (e3 + σ δ)` and `σ ≤ 3 s`. -/
theorem newMixAsm_ratio_algebra {σ s A B B' e1 e2 e3 δ : ℝ} (hσ : 0 < σ) (hs : 0 < s)
    (he2 : 0 ≤ e2) (he3 : 0 ≤ e3) (hδ : 0 ≤ δ)
    (he1h : e1 ≤ 1 / 2) (he2h : e2 ≤ 1 / 2) (hη : e3 + σ * δ ≤ 1 / 2)
    (h1 : |s⁻¹ * A - 1| ≤ e1) (h2 : |s * B - 1| ≤ e2) (h3 : |σ * B' - 1| ≤ e3)
    (h4 : |B - B'| ≤ δ) :
    |σ⁻¹ * A - 1| + |σ * B - 1| ≤ e1 + 3 * e2 + 4 * (e3 + σ * δ) ∧ σ ≤ 3 * s := by
  set η : ℝ := e3 + σ * δ with hηdef
  have hη0 : 0 ≤ η := by rw [hηdef]; positivity
  -- `v = σ B`
  have hv : |σ * B - 1| ≤ η := by
    have h5 : σ * B - 1 = (σ * B' - 1) + σ * (B - B') := by ring
    rw [h5]
    calc |(σ * B' - 1) + σ * (B - B')| ≤ |σ * B' - 1| + |σ * (B - B')| := abs_add_le _ _
      _ ≤ e3 + σ * δ := by
        rw [abs_mul, abs_of_pos hσ]
        exact add_le_add h3 (mul_le_mul_of_nonneg_left h4 hσ.le)
  have hv_lb : 1 / 2 ≤ σ * B := by
    have := (abs_le.mp hv).1
    linarith only [this, hη]
  have hu_lb : 1 / 2 ≤ s * B := by
    have := (abs_le.mp h2).1
    linarith only [this, he2h]
  have hBpos : 0 < B := by
    by_contra hneg
    rw [not_lt] at hneg
    have : σ * B ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hσ.le hneg
    linarith only [this, hv_lb]
  have hvpos : 0 < σ * B := by linarith only [hv_lb]
  have hu_ub : s * B ≤ 3 / 2 := by
    have := (abs_le.mp h2).2
    linarith only [this, he2h]
  -- `σ ≤ 3 s`
  have hσs : σ ≤ 3 * s := by
    have hvle : σ * B ≤ 3 / 2 := by
      have := (abs_le.mp hv).2
      linarith only [this, hη]
    have h6 : σ * B ≤ 3 * (s * B) := by linarith only [hvle, hu_lb]
    have h7 : σ * B ≤ (3 * s) * B := by linarith only [h6]
    exact le_of_mul_le_mul_right h7 hBpos
  refine ⟨?_, hσs⟩
  set w : ℝ := s⁻¹ * A with hwdef
  set u : ℝ := s * B with hudef
  set v : ℝ := σ * B with hvdef
  have hAw : A = s * w := by rw [hwdef]; field_simp
  have hkey : σ⁻¹ * A - 1 = ((u - v) * w + v * (w - 1)) / v := by
    rw [hAw, hudef, hvdef]
    field_simp
    ring
  have hw_le : |w| ≤ 3 / 2 := by
    have := abs_le.mp h1
    rw [abs_le]; constructor <;> linarith only [this.1, this.2, he1h]
  have huv : |u - v| ≤ e2 + η := by
    have h8 : u - v = (u - 1) - (v - 1) := by ring
    rw [h8]
    calc |(u - 1) - (v - 1)| ≤ |u - 1| + |v - 1| := abs_sub _ _
      _ ≤ e2 + η := add_le_add h2 hv
  have hX : |(u - v) * w + v * (w - 1)| ≤ (e2 + η) * (3 / 2) + v * e1 := by
    calc |(u - v) * w + v * (w - 1)| ≤ |(u - v) * w| + |v * (w - 1)| := abs_add_le _ _
      _ = |u - v| * |w| + v * |w - 1| := by rw [abs_mul (u - v) w, abs_mul v (w - 1), abs_of_pos hvpos]
      _ ≤ (e2 + η) * (3 / 2) + v * e1 := by
        refine add_le_add ?_ (mul_le_mul_of_nonneg_left h1 hvpos.le)
        exact mul_le_mul huv hw_le (abs_nonneg _) (by linarith only [he2, hη0])
  have hmain : |σ⁻¹ * A - 1| ≤ e1 + 3 * (e2 + η) := by
    rw [hkey, abs_div, abs_of_pos hvpos, div_le_iff₀ hvpos]
    have hc : (e2 + η) * (3 / 2) ≤ 3 * (e2 + η) * v := by
      have h0 : 0 ≤ e2 + η := by linarith only [he2, hη0]
      nlinarith only [hv_lb, h0]
    have hd : v * e1 ≤ e1 * v := by ring_nf; exact le_refl _
    nlinarith only [hX, hc, hd]
  linarith only [hmain, hv]

end
end SuperdiffusionCLT.Section4.NewMixing
