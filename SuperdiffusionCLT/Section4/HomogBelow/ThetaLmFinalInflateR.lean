/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.LNaught.Monotone

/-!
**The `M`-inflation lemma at an arbitrary ratio `r`.** Generalizes `ThetaLmM3Headroom.lean`'s
`homogBelow_inflateM3` (ratio `3`) to a free `r ≥ 1`, needed because the
smallness-condition step of the proof of `p.homog.below` requires an inflation ratio
depending on the constant `C₆₁` of [AK, Theorem 6.1], which is
not fixed in advance the way `3` was for the `m₃`-headroom. -/

@[expose] public section

namespace SuperdiffusionCLT.Section4.HomogBelow

private theorem homogBelow_inflateR_identity {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    min (1 : ℝ) (c / r) * max (1 : ℝ) (r / c) = 1 := by
  rcases le_or_gt c r with hle | hlt
  · have hmin : min (1 : ℝ) (c / r) = c / r := min_eq_right (by
      rw [div_le_one₀ hr]; linarith only [hle])
    have hmax : max (1 : ℝ) (r / c) = r / c := by
      apply max_eq_right
      rw [le_div_iff₀ hc]
      linarith only [hle]
    rw [hmin, hmax]
    field_simp
  · have hmin : min (1 : ℝ) (c / r) = 1 := by
      apply min_eq_left
      rw [le_div_iff₀ hr]
      linarith only [hlt]
    have hmax : max (1 : ℝ) (r / c) = 1 := by
      apply max_eq_left
      rw [div_le_one₀ hc]
      linarith only [hlt]
    rw [hmin, hmax]; norm_num

/-- **The `M`-inflation lemma, at a free ratio `r > 0`.** Same shape as
`homogBelow_inflateM3`, generalized. -/
theorem homogBelow_inflateMR
    {C M c r alpha cStar nu K : ℝ} (hC0 : 0 ≤ C) (hM1 : 1 ≤ M) (hc : 0 < c) (hr : 0 < r)
    (halpha1 : alpha < 1) (hcStar : 0 < cStar) (hnu : 0 < nu) (hK : 0 ≤ K)
    {L : ℕ}
    (hL : SuperdiffusionCLT.Frozen.Section4.lNaught C (C * M) alpha cStar nu K ≤ (L : ℝ)) :
    1 ≤ M * max (1 : ℝ) (r / c) ∧
    C * min (1 : ℝ) (c / r) ≤ C ∧
    r ≤ c * max (1 : ℝ) (r / c) ∧
    SuperdiffusionCLT.Frozen.Section4.lNaught (C * min (1 : ℝ) (c / r))
        ((C * min (1 : ℝ) (c / r)) * (M * max (1 : ℝ) (r / c))) alpha cStar nu K ≤ (L : ℝ) := by
  have hmaxge1 : (1 : ℝ) ≤ max (1 : ℝ) (r / c) := le_max_left _ _
  have hminle1 : min (1 : ℝ) (c / r) ≤ 1 := min_le_left _ _
  have hminpos : (0 : ℝ) < min (1 : ℝ) (c / r) := lt_min (by norm_num) (by
    exact div_pos hc hr)
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
      _ ≤ M * max (1 : ℝ) (r / c) := mul_le_mul hM1 hmaxge1 (by norm_num) (by linarith only [hM1])
  · calc C * min (1 : ℝ) (c / r) ≤ C * 1 := mul_le_mul_of_nonneg_left hminle1 hC0
      _ = C := mul_one C
  · rcases le_or_gt c r with hle | hlt
    · have hmax : max (1 : ℝ) (r / c) = r / c := by
        apply max_eq_right
        rw [le_div_iff₀ hc]
        linarith only [hle]
      rw [hmax]
      have heq : c * (r / c) = r := by field_simp
      linarith only [heq]
    · have hmax : max (1 : ℝ) (r / c) = 1 := by
        apply max_eq_left
        rw [div_le_one₀ hc]
        linarith only [hlt]
      rw [hmax, mul_one]
      linarith only [hlt]
  · have hCthr0 : (0 : ℝ) ≤ C * min (1 : ℝ) (c / r) := mul_nonneg hC0 hminpos.le
    have hCthrleC : C * min (1 : ℝ) (c / r) ≤ C := by
      calc C * min (1 : ℝ) (c / r) ≤ C * 1 := mul_le_mul_of_nonneg_left hminle1 hC0
        _ = C := mul_one C
    have hid : (C * min (1 : ℝ) (c / r)) * (M * max (1 : ℝ) (r / c)) = C * M := by
      have hidentity := homogBelow_inflateR_identity hc hr
      calc (C * min (1 : ℝ) (c / r)) * (M * max (1 : ℝ) (r / c))
          = (C * M) * (min (1 : ℝ) (c / r) * max (1 : ℝ) (r / c)) := by ring
        _ = (C * M) * 1 := by rw [hidentity]
        _ = C * M := mul_one _
    rw [hid]
    have hCM0 : (0 : ℝ) ≤ C * M := mul_nonneg hC0 (by linarith only [hM1])
    exact SuperdiffusionCLT.Section4.LNaught.lNaught_mono_const
      hCthr0 hCthrleC hCM0 hK hcStar hnu halpha1 |>.trans hL

end SuperdiffusionCLT.Section4.HomogBelow
