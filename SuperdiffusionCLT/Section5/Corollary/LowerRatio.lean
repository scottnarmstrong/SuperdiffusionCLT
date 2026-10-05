/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic


/-!
# `cor.lower.ratio`: elementary pieces

The limsup bookkeeping and the real arithmetic of the proof of `cor.lower.ratio`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Filter
open scoped ENNReal

/-- A bound valid for all large `Kc` passes to the `limsup` of the main term. -/
theorem lowerRatio_le_of_limsup {X c r B : ℝ≥0∞} {T : ℕ → ℝ≥0∞} {N0 : ℕ} (hc : c ≠ ⊤)
    (hX : ∀ Kc : ℕ, N0 ≤ Kc → X ≤ c * T Kc + r)
    (hT : Filter.limsup T Filter.atTop ≤ B) : X ≤ c * B + r := by
  have h1 : X ≤ Filter.limsup (fun Kc => c * T Kc + r) Filter.atTop :=
    Filter.le_limsup_of_frequently_le
      (Filter.Eventually.frequently (Filter.eventually_atTop.2 ⟨N0, hX⟩))
  have hmono : Monotone (fun x : ℝ≥0∞ => c * x + r) := fun a b hab => by
    dsimp only
    gcongr
  have hcont : ContinuousAt (fun x : ℝ≥0∞ => c * x + r) (Filter.limsup T Filter.atTop) :=
    ((ENNReal.continuous_const_mul hc).add continuous_const).continuousAt
  have h2 := hmono.map_limsup_of_continuousAt (F := Filter.atTop) T hcont
  have h3 : Filter.limsup (fun Kc => c * T Kc + r) Filter.atTop =
      c * Filter.limsup T Filter.atTop + r := h2.symm
  rw [h3] at h1
  refine h1.trans ?_
  gcongr

/-- `log 3 ≤ 2`. -/
theorem lowerRatio_log_three_le : Real.log 3 ≤ 2 := by
  have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
  linarith only [this]

/-- The main bracket is nonnegative once the quadratic constant is at least `4`. -/
theorem lowerRatio_bracket_nonneg {cStar y K C : ℝ} (hc2 : cStar ≤ 2)
    (hy : 0 ≤ y) (hK : 0 ≤ K) (hC : 4 ≤ C) :
    0 ≤ 1 - cStar * Real.log 3 * y + K + C * y ^ 2 := by
  have hl := lowerRatio_log_three_le
  have hl0 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have h1 : cStar * Real.log 3 ≤ 4 := by
    have := mul_le_mul hc2 hl hl0 (by norm_num : (0 : ℝ) ≤ 2)
    linarith only [this]
  have h2 : cStar * Real.log 3 * y ≤ 4 * y := mul_le_mul_of_nonneg_right h1 hy
  have h3 : 4 * y ^ 2 ≤ C * y ^ 2 := mul_le_mul_of_nonneg_right hC (sq_nonneg y)
  have h4 : 0 ≤ (1 - 2 * y) ^ 2 := sq_nonneg _
  have h5 : (1 - 2 * y) ^ 2 = 1 - 4 * y + 4 * y ^ 2 := by ring
  linarith only [h2, h3, h4, h5, hK]

/-- The product expansion of `e.lower.ratio.product`. -/
theorem lowerRatio_arith {R A B N H r x L Kk s4h Ca Ca2 Cr Ch C : ℝ}
    (hR : R ≤ (1 + A) * (1 - B + N + H) + r)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hN0 : 0 ≤ N) (hH0 : 0 ≤ H)
    (hAL : A ≤ Ca * x * L) (hA2 : A ≤ Ca2) (hr : r ≤ Cr * x * L)
    (hNK : N = Kk * x) (hHs : H ≤ Ch * s4h)
    (hx : 0 ≤ x) (hL : 0 ≤ L) (hK : 0 ≤ Kk) (hs : 0 ≤ s4h) (hCa2 : 0 ≤ Ca2)
    (hC1 : Ca + Cr ≤ C) (hC2 : 1 + Ca2 ≤ C) (hC3 : (1 + Ca2) * Ch ≤ C) :
    R ≤ 1 - B + C * (L + Kk) * x + C * s4h := by
  have e : (1 + A) * (1 - B + N + H) = (1 - B + N + H) + A + A * N + A * H - A * B := by ring
  have hAB : 0 ≤ A * B := mul_nonneg hA0 hB0
  have hAN : A * N ≤ Ca2 * N := mul_le_mul_of_nonneg_right hA2 hN0
  have hAH : A * H ≤ Ca2 * H := mul_le_mul_of_nonneg_right hA2 hH0
  have hH2 : (1 + Ca2) * H ≤ (1 + Ca2) * (Ch * s4h) :=
    mul_le_mul_of_nonneg_left hHs (by linarith only [hCa2])
  have hH3 : (1 + Ca2) * (Ch * s4h) ≤ C * s4h := by
    have := mul_le_mul_of_nonneg_right hC3 hs
    linarith only [this]
  have hN2 : (1 + Ca2) * N ≤ C * (Kk * x) := by
    rw [hNK]
    have hKx : 0 ≤ Kk * x := mul_nonneg hK hx
    exact mul_le_mul_of_nonneg_right hC2 hKx
  have hAr : A + r ≤ C * L * x := by
    have h1 : (Ca + Cr) * (x * L) ≤ C * (x * L) :=
      mul_le_mul_of_nonneg_right hC1 (mul_nonneg hx hL)
    have h2 : Ca * x * L + Cr * x * L = (Ca + Cr) * (x * L) := by ring
    have h3 : C * (x * L) = C * L * x := by ring
    linarith only [hAL, hr, h1, h2, h3]
  have h6 : C * (L + Kk) * x = C * L * x + C * (Kk * x) := by ring
  linarith only [hR, e, hAB, hAN, hAH, hH2, hH3, hN2, hAr, h6]

end SuperdiffusionCLT.Section5
