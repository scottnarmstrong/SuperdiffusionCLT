/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.SstarLowerBoundCloseB

/-!
# The depth shape of the lower bound: a threshold constant depending on `CM`

The assembly of the lower bound is the whole of `p.sstar.lower.bound` up to its
bridges.  One of its numerical hypotheses is the depth shape `CM · L^{-500} ≤ cStar/8`, where
`CM` is the master-inequality constant.  This file proves that shape from the threshold data
*plus one scalar*, `2 ^ 1502 * CM ≤ T ^ 500` at the threshold constant `T`, and shows what the
scalar costs.

## Main results

* `sstarWorkDepthThrConst CM = max 1 ((2 ^ 1502 * CM) ^ (1/500))` — the threshold constant the
  depth shape forces; it meets its requirement (`sstarWorkDepthThrConst_pow_ge`);
* `sstarWorkDepthShape_of_thr` — the depth shape from `T cStar⁻³ eLvs ≤ m ≤ L`, `eLvs ≥ 1` and the
  scalar `2 ^ 1502 * CM ≤ T ^ 500`.

## Why the constant depends on `CM`

The constant `CM` is produced by the master inequality, below data-dependent constants, so it is
not reachable by `Classical.choose` at `d` alone (see `Terms/SstarLowerBoundClose.lean`); the
issue is the placement of the existential, not a size estimate.  For the depth shape the exact
scalar needed is `2 ^ 1502 * CM ≤ T ^ 500` (`sstarWorkDepthShape_of_thr`), and the threshold
constant that achieves it, `max 1 ((2 ^ 1502 * CM) ^ (1/500))`, is `CM`-dependent
(`sstarWorkDepthThrConst`, `sstarWorkDepthThrConst_pow_ge`), which is what a `d`-only constant such
as `sstarCloseThrConst d` cannot be.  Neither anchor bounds its constant from above: the
homogenization anchor `exists_bell_bound` uses `CB` as a multiplicative coefficient on the right of
its estimate and carries the tail shape `CB log²(ν⁻¹L) ≤ n` as an input of its own statement, and
the localization anchor likewise uses `CL` as a multiplicative coefficient.  Placing the threshold
first is therefore a matter of quantifying the constant after the anchors.
-/

@[expose] public section

open MeasureTheory
open Homogenization
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section3.Setup

namespace SuperdiffusionCLT.Section3.Terms

noncomputable section

/-! ## The depth shape is a placement of the threshold after `CM`

The shape `CM · L^{-500} ≤ c★/8` of the assembly is proved below from
the threshold data *plus one scalar*: `2 ^ 1502 * CM ≤ T ^ 500` at the
threshold constant `T`.  The scalar cannot be dropped, and the constant that
meets it is the `CM`-dependent `sstarWorkDepthThrConst CM` — so no `d`-only
threshold constant can carry the shape for a free `CM`. -/

/-- **The threshold constant the depth shape forces.**  `T` must satisfy
`T ^ 500 ≥ 2 ^ 1502 * CM`, so the least such constant (at least `1`) is
`(2 ^ 1502 * CM) ^ (1/500)`.  Its free variable is `CM` alone: this is a
`CM`-dependent constant. -/
noncomputable def sstarWorkDepthThrConst (CM : ℝ) : ℝ :=
  max 1 (((2 : ℝ) ^ (1502 : ℝ) * CM) ^ ((1 : ℝ) / 500))

theorem sstarWorkDepthThrConst_pos (CM : ℝ) : (0 : ℝ) < sstarWorkDepthThrConst CM :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

/-- **The constant meets its own requirement**: `2 ^ 1502 * CM ≤ T ^ 500`. -/
theorem sstarWorkDepthThrConst_pow_ge (CM : ℝ) (hCM : 0 ≤ CM) :
    (2 : ℝ) ^ (1502 : ℝ) * CM ≤ (sstarWorkDepthThrConst CM) ^ (500 : ℝ) := by
  have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (1502 : ℝ) * CM :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) hCM
  have ha : (0 : ℝ) ≤ ((2 : ℝ) ^ (1502 : ℝ) * CM) ^ ((1 : ℝ) / 500) :=
    Real.rpow_nonneg h2 _
  have hle : ((2 : ℝ) ^ (1502 : ℝ) * CM) ^ ((1 : ℝ) / 500) ≤
      sstarWorkDepthThrConst CM := le_max_right _ _
  have hpow : (((2 : ℝ) ^ (1502 : ℝ) * CM) ^ ((1 : ℝ) / 500)) ^ (500 : ℝ) ≤
      (sstarWorkDepthThrConst CM) ^ (500 : ℝ) :=
    Real.rpow_le_rpow ha hle (by norm_num)
  have hsimp : (((2 : ℝ) ^ (1502 : ℝ) * CM) ^ ((1 : ℝ) / 500)) ^ (500 : ℝ) =
      (2 : ℝ) ^ (1502 : ℝ) * CM := by
    rw [← Real.rpow_mul h2]
    norm_num
  calc (2 : ℝ) ^ (1502 : ℝ) * CM
      = (((2 : ℝ) ^ (1502 : ℝ) * CM) ^ ((1 : ℝ) / 500)) ^ (500 : ℝ) := hsimp.symm
    _ ≤ (sstarWorkDepthThrConst CM) ^ (500 : ℝ) := hpow

/-- **The depth shape from the threshold data and the scalar.**  This is the
assembly's depth shape at a threshold constant `T`, from `T c★⁻³ eLvs ≤ m ≤ L`,
`eLvs ≥ 1` and the scalar `2 ^ 1502 * CM ≤ T ^ 500`.  The proof is the whole of
the shape's arithmetic: `L^{-500} ≤ (T c★⁻³)^{-500} = T^{-500} c★^{1500}`, the
scalar gives `CM T^{-500} ≤ 2^{-1502}`, and `c★ ≤ 2` gives
`2^{-1502} c★^{1500} ≤ c★ / 8`. -/
theorem sstarWorkDepthShape_of_thr
    {CM cStar eLvs T : ℝ} {m L : ℕ}
    (hCM : 0 ≤ CM) (hcStar : 0 < cStar) (hcStar2 : cStar ≤ 2)
    (hT : 0 < T) (heLvs : 1 ≤ eLvs)
    (hTpow : (2 : ℝ) ^ (1502 : ℝ) * CM ≤ T ^ (500 : ℝ))
    (hft : T * cStar ^ (-(3 : ℝ)) * eLvs ≤ (m : ℝ)) (hmL : m ≤ L) :
    CM * (L : ℝ) ^ (-(500 : ℝ)) ≤ cStar / 8 := by
  have hc3 : (0 : ℝ) < cStar ^ (-(3 : ℝ)) := Real.rpow_pos_of_pos hcStar _
  have hb : (0 : ℝ) < T * cStar ^ (-(3 : ℝ)) := mul_pos hT hc3
  have hbe : (0 : ℝ) < T * cStar ^ (-(3 : ℝ)) * eLvs :=
    mul_pos hb (lt_of_lt_of_le zero_lt_one heLvs)
  have hmpos : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le hbe hft
  have hm0 : (0 : ℕ) < m := by exact_mod_cast hmpos
  have hLpos : (0 : ℝ) < (L : ℝ) :=
    lt_of_lt_of_le hbe (le_trans hft (by exact_mod_cast hmL))
  have hTL : T * cStar ^ (-(3 : ℝ)) ≤ (L : ℝ) := by
    have h1 : T * cStar ^ (-(3 : ℝ)) ≤ T * cStar ^ (-(3 : ℝ)) * eLvs := by
      simpa using mul_le_mul_of_nonneg_left heLvs (le_of_lt hb)
    have h2 : (m : ℝ) ≤ (L : ℝ) := by exact_mod_cast hmL
    linarith only [h1, hft, h2]
  have hrpow : (L : ℝ) ^ (-(500 : ℝ)) ≤ (T * cStar ^ (-(3 : ℝ))) ^ (-(500 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hb hTL (by norm_num)
  have hsplit : (T * cStar ^ (-(3 : ℝ))) ^ (-(500 : ℝ)) =
      T ^ (-(500 : ℝ)) * cStar ^ (1500 : ℝ) := by
    rw [Real.mul_rpow (le_of_lt hT) (Real.rpow_nonneg (le_of_lt hcStar) _)]
    congr 1
    rw [← Real.rpow_mul (le_of_lt hcStar)]
    norm_num
  have hstep1 : CM * (L : ℝ) ^ (-(500 : ℝ)) ≤
      CM * (T ^ (-(500 : ℝ)) * cStar ^ (1500 : ℝ)) := by
    rw [hsplit] at hrpow
    exact mul_le_mul_of_nonneg_left hrpow hCM
  have hT500pos : (0 : ℝ) < T ^ (500 : ℝ) := Real.rpow_pos_of_pos hT _
  have hu : CM * T ^ (-(500 : ℝ)) ≤ ((2 : ℝ) ^ (1502 : ℝ))⁻¹ := by
    rw [Real.rpow_neg (le_of_lt hT)]
    have hA : CM ≤ T ^ (500 : ℝ) / (2 : ℝ) ^ (1502 : ℝ) := by
      rw [le_div_iff₀ (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)]
      linarith only [hTpow, mul_comm ((2 : ℝ) ^ (1502 : ℝ)) CM]
    have hB : T ^ (500 : ℝ) / (2 : ℝ) ^ (1502 : ℝ) * (T ^ (500 : ℝ))⁻¹ =
        ((2 : ℝ) ^ (1502 : ℝ))⁻¹ := by
      rw [div_eq_mul_inv, mul_assoc,
        mul_comm ((2 : ℝ) ^ (1502 : ℝ))⁻¹ (T ^ (500 : ℝ))⁻¹, ← mul_assoc,
        mul_inv_cancel₀ (ne_of_gt hT500pos), one_mul]
    calc CM * (T ^ (500 : ℝ))⁻¹
        ≤ T ^ (500 : ℝ) / (2 : ℝ) ^ (1502 : ℝ) * (T ^ (500 : ℝ))⁻¹ :=
          mul_le_mul_of_nonneg_right hA (inv_nonneg.mpr (le_of_lt hT500pos))
      _ = ((2 : ℝ) ^ (1502 : ℝ))⁻¹ := hB
  have hfinal : ((2 : ℝ) ^ (1502 : ℝ))⁻¹ * cStar ^ (1500 : ℝ) ≤ cStar / 8 := by
    have hc1499 : cStar ^ (1499 : ℝ) ≤ (2 : ℝ) ^ (1499 : ℝ) :=
      Real.rpow_le_rpow (le_of_lt hcStar) hcStar2 (by norm_num)
    have hmul : ((2 : ℝ) ^ (1502 : ℝ))⁻¹ * cStar ^ (1499 : ℝ) ≤
        ((2 : ℝ) ^ (1502 : ℝ))⁻¹ * (2 : ℝ) ^ (1499 : ℝ) :=
      mul_le_mul_of_nonneg_left hc1499
        (inv_nonneg.mpr (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _))
    have hkey : ((2 : ℝ) ^ (1502 : ℝ))⁻¹ * (2 : ℝ) ^ (1499 : ℝ) = 1 / 8 := by
      have hs : (2 : ℝ) ^ (1499 : ℝ) = (2 : ℝ) ^ (1502 : ℝ) * (2 : ℝ) ^ (-(3 : ℝ)) := by
        have h := Real.rpow_add (by norm_num : (0 : ℝ) < 2) (1502 : ℝ) (-(3 : ℝ))
        rw [show (1502 : ℝ) + (-(3 : ℝ)) = 1499 by norm_num] at h
        exact h
      rw [hs, ← mul_assoc,
        inv_mul_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)),
        one_mul, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have hc1500 : cStar ^ (1500 : ℝ) = cStar ^ (1499 : ℝ) * cStar := by
      have h := Real.rpow_add hcStar (1499 : ℝ) (1 : ℝ)
      rw [show (1499 : ℝ) + 1 = 1500 by norm_num, Real.rpow_one] at h
      exact h
    calc ((2 : ℝ) ^ (1502 : ℝ))⁻¹ * cStar ^ (1500 : ℝ)
        = (((2 : ℝ) ^ (1502 : ℝ))⁻¹ * cStar ^ (1499 : ℝ)) * cStar := by
          rw [hc1500]; ring
      _ ≤ (((2 : ℝ) ^ (1502 : ℝ))⁻¹ * (2 : ℝ) ^ (1499 : ℝ)) * cStar :=
          mul_le_mul_of_nonneg_right hmul (le_of_lt hcStar)
      _ = (1 / 8) * cStar := by rw [hkey]
      _ = cStar / 8 := by ring
  calc CM * (L : ℝ) ^ (-(500 : ℝ))
      ≤ CM * (T ^ (-(500 : ℝ)) * cStar ^ (1500 : ℝ)) := hstep1
    _ = (CM * T ^ (-(500 : ℝ))) * cStar ^ (1500 : ℝ) := by ring
    _ ≤ ((2 : ℝ) ^ (1502 : ℝ))⁻¹ * cStar ^ (1500 : ℝ) :=
        mul_le_mul_of_nonneg_right hu (Real.rpow_nonneg (le_of_lt hcStar) _)
    _ ≤ cStar / 8 := hfinal


end

end SuperdiffusionCLT.Section3.Terms
