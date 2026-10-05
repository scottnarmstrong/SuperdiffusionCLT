/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# A quantitative variant of `sbComp_three_factor_bound`

`ComparisonBound.lean`'s `sbComp_three_factor_bound` needs `ea ≤ 1/8` for
BOTH `|a-1|` and `|c-1|` to get its tight `17/7, 8/7` coefficients. Reaching
the QUANTITATIVE target `e.sL.vs.sell` needs a version taking two DIFFERENT
(quantitative, not a priori `≤ 1/8`) bounds `ea1` (for `a`) and `ea2` (for
`c`), using only the qualitative fact `c ≥ 7/8` (established separately, via
`sbComp_three_factor_bound` itself at the constant bound `1/8`) in place of
deriving it internally from `ea2 ≤ 1/8`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.SigmaBarComparison

/-- Pure algebra, no context: a bound on `|a*b*c⁻¹-1|` from `|a-1|≤ea1`,
`|b-1|≤eb`, `|c-1|≤ea2`, `c ≥ 7/8` (established independently, not
necessarily from `ea2 ≤ 1/8`), and `eb ≤ 1/8`. No bound on `ea1`, `ea2`
beyond nonnegativity is needed. -/
theorem sbAsmF_three_factor_quant {a b c ea1 ea2 eb : ℝ}
    (ha : |a - 1| ≤ ea1) (hb : |b - 1| ≤ eb) (hc : |c - 1| ≤ ea2)
    (hc78 : (7 / 8 : ℝ) ≤ c) (heb : eb ≤ 1 / 8) :
    |a * b * c⁻¹ - 1| ≤ (9 / 7 : ℝ) * ea1 + (8 / 7 : ℝ) * eb + (8 / 7 : ℝ) * ea2 := by
  have hea1nn : (0 : ℝ) ≤ ea1 := le_trans (abs_nonneg _) ha
  have heb0 : (0 : ℝ) ≤ eb := le_trans (abs_nonneg _) hb
  have hea2nn : (0 : ℝ) ≤ ea2 := le_trans (abs_nonneg _) hc
  have hcpos : (0 : ℝ) < c := by linarith only [hc78]
  have hcne : c ≠ 0 := ne_of_gt hcpos
  have hid : a * b * c⁻¹ - 1 = (a * b - c) * c⁻¹ := by field_simp
  have hexpand : a * b - c = (a - 1) + (b - 1) - (c - 1) + (a - 1) * (b - 1) := by ring
  have htri2 : |(a - 1) + (b - 1) - (c - 1)| ≤ |a - 1| + |b - 1| + |c - 1| := by
    have e1 : (a - 1) + (b - 1) - (c - 1) = (a - 1) + (b - 1) + (-(c - 1)) := by ring
    rw [e1]
    have s1 : |(a - 1) + (b - 1) + (-(c - 1))| ≤ |(a - 1) + (b - 1)| + |-(c - 1)| :=
      abs_add_le _ _
    have s2 : |(a - 1) + (b - 1)| ≤ |a - 1| + |b - 1| := abs_add_le _ _
    have s3 : |-(c - 1)| = |c - 1| := abs_neg _
    linarith only [s1, s2, s3]
  have habs : |a * b - c| ≤ |a - 1| + |b - 1| + |c - 1| + |a - 1| * |b - 1| := by
    rw [hexpand]
    have htri : |(a - 1) + (b - 1) - (c - 1) + (a - 1) * (b - 1)| ≤
        |(a - 1) + (b - 1) - (c - 1)| + |(a - 1) * (b - 1)| := abs_add_le _ _
    have hm : |(a - 1) * (b - 1)| = |a - 1| * |b - 1| := abs_mul _ _
    linarith only [htri, htri2, hm]
  have hprod : |a - 1| * |b - 1| ≤ ea1 * eb := mul_le_mul ha hb (abs_nonneg _) hea1nn
  have heaeb : ea1 * eb ≤ ea1 * (1 / 8) := mul_le_mul_of_nonneg_left heb hea1nn
  have habs3 : |a * b - c| ≤ (9 / 8) * ea1 + eb + ea2 := by
    have h1 : |a - 1| ≤ ea1 := ha
    have h2 : |b - 1| ≤ eb := hb
    have h3 : |c - 1| ≤ ea2 := hc
    linarith only [habs, hprod, heaeb, h1, h2, h3]
  have hcinvpos : (0 : ℝ) < c⁻¹ := inv_pos.mpr hcpos
  have hcinvle : c⁻¹ ≤ 8 / 7 := by
    rw [inv_le_comm₀ hcpos (by norm_num : (0 : ℝ) < 8 / 7)]
    have hh : (8 / 7 : ℝ)⁻¹ = 7 / 8 := by norm_num
    rw [hh]
    exact hc78
  have hrhs0 : (0 : ℝ) ≤ (9 / 8) * ea1 + eb + ea2 := by linarith only [hea1nn, heb0, hea2nn]
  calc |a * b * c⁻¹ - 1| = |a * b - c| * c⁻¹ := by rw [hid, abs_mul, abs_of_pos hcinvpos]
  _ ≤ ((9 / 8) * ea1 + eb + ea2) * (8 / 7) :=
      mul_le_mul habs3 hcinvle (le_of_lt hcinvpos) hrhs0
  _ = (9 / 7 : ℝ) * ea1 + (8 / 7 : ℝ) * eb + (8 / 7 : ℝ) * ea2 := by ring

end SuperdiffusionCLT.Section4.SigmaBarComparison
