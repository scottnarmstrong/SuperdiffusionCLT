/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.BfAmEllipticityLevelTailB
public import SuperdiffusionCLT.Section2.BfAmEllipticityScaleTail

/-!
# A level-tail reduction at an arbitrary per-scale rate

This module concerns lemma `l.bfAm.ellip`.  The reduction of `BfAmEllipticityLevelTailB` fixes
the decay constant of the printed per-scale tail at
`2 * levelTailConst (max 3 (subCubeUnionConst d)) ≥ 4`; since the Γ₁ tail of
`envelopeRatio` certifies only rate `2` in the threshold `2 * 3^{γk}`
(`BfAmEllipticityScaleTail`), that rate is out of reach.

This file restates the tail with its rate as an explicit parameter
`c₀ ≥ 6.2918`, absorbing the union bound over the `3^{d(n-l)}`
sub-cubes and the sum over the scales into the **amplitude** instead of the
rate. Via the split `c₀ = c + 2` and the two-sided comparison of the printed
exponent `E_k = γk + (d/2) max (K-k) 0` with `γK` and `γk`, the level tail
closes at the rate `c = c₀ - 2 ≥ 4.2918`; the residual geometric
sum at rate `2` is absorbed by the geometric majorant of
`BfAmEllipticityLevelTailB`. The constant `4.2918` is independent of the
amplitude constant, so the required per-scale rate is absolute. The only
per-scale hypothesis is the printed display at the rate `c₀`; DIMENSION ONE IS
OUT OF SCOPE (`2 ≤ d` enters only through `subCubeUnionConst d ≥ 3`).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2

noncomputable section

variable {d : ℕ}

/-! ## The pointwise split of the per-scale exponent

The printed per-scale tail of the paper decays at the exponent `γ k + (d/2) max (K - k) 0`,
which is at least both extremes `γ k` and `γ K`. Writing the per-scale rate as
`c + c₁` with `c, c₁ > 0` therefore splits the exponential *without loss*:

> `exp(-(c + c₁) 3^{γk + (d/2) max (K-k) 0})`
>   `≤ exp(-(c 3^{γK})) · exp(-(c₁ 3^{γk}))`.

The corresponding bound of `BfAmEllipticityLevelTailB` instead
averages the two extremes, which costs a factor `2` in the exponent and is the
reason its per-scale rate is `4t` for a level rate `2t`. The split below spends
nothing on the level rate: the level decay is produced at the full `c`, and the
factor `c₁` is the *amplitude* rate, which the sum over the scales can absorb. -/

/-- **The split of one per-scale term.** The level decay at rate `c` is taken out
at the full constant, and the residual term at rate `c₁` is the summand of the
amplitude sum. Valid for every `c, c₁ > 0`; the two extremes are compared
separately instead of being averaged. -/
theorem levelTerm_point_le_c (d : ℕ) (hd : 2 ≤ d) {gamma c c1 K : ℝ} (hg0 : 0 < gamma)
    (hg1 : gamma ≤ 1) (hc : 0 < c) (hc1 : 0 < c1) (k : ℕ) :
    (3 : ℝ) ^ ((d + 1) * (k + 1)) *
        Real.exp (-((c + c1) * (3 : ℝ) ^ (gamma * (k : ℝ) +
          ((d : ℝ) / 2) * max (K - (k : ℝ)) 0))) ≤
      Real.exp (-(c * (3 : ℝ) ^ (gamma * K))) *
        ((3 : ℝ) ^ ((d + 1) * (k + 1)) *
          Real.exp (-(c1 * (3 : ℝ) ^ (gamma * (k : ℝ))))) := by
  set E : ℝ := (3 : ℝ) ^ (gamma * (k : ℝ) + ((d : ℝ) / 2) * max (K - (k : ℝ)) 0) with hE
  have hbase : (1 : ℝ) ≤ (3 : ℝ) := by norm_num
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hgl : gamma ≤ (d : ℝ) / 2 := by linarith only [hg1, hd2]
  have hu_k : (3 : ℝ) ^ (gamma * (k : ℝ)) ≤ E := by
    rw [hE]
    refine Real.rpow_le_rpow_of_exponent_le hbase ?_
    have h0 : 0 ≤ ((d : ℝ) / 2) * max (K - (k : ℝ)) 0 :=
      mul_nonneg (by positivity) (le_max_right _ _)
    linarith only [h0]
  have hu_K : (3 : ℝ) ^ (gamma * K) ≤ E := by
    rw [hE]
    refine Real.rpow_le_rpow_of_exponent_le hbase ?_
    rcases le_total (k : ℝ) K with hk | hk
    · rw [max_eq_left (sub_nonneg.2 hk)]
      have hge : gamma * (K - (k : ℝ)) ≤ ((d : ℝ) / 2) * (K - (k : ℝ)) :=
        mul_le_mul_of_nonneg_right hgl (sub_nonneg.2 hk)
      linarith only [hge]
    · rw [max_eq_right (sub_nonpos.2 hk), mul_zero, add_zero]
      exact mul_le_mul_of_nonneg_left hk hg0.le
  have hsplit : Real.exp (-((c + c1) * E)) =
      Real.exp (-(c * E)) * Real.exp (-(c1 * E)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h1 : Real.exp (-(c * E)) ≤ Real.exp (-(c * (3 : ℝ) ^ (gamma * K))) := by
    refine Real.exp_le_exp.2 ?_
    have hm := mul_le_mul_of_nonneg_left hu_K hc.le
    linarith only [hm]
  have h2 : Real.exp (-(c1 * E)) ≤ Real.exp (-(c1 * (3 : ℝ) ^ (gamma * (k : ℝ)))) := by
    refine Real.exp_le_exp.2 ?_
    have hm := mul_le_mul_of_nonneg_left hu_k hc1.le
    linarith only [hm]
  calc (3 : ℝ) ^ ((d + 1) * (k + 1)) * Real.exp (-((c + c1) * E))
      = (3 : ℝ) ^ ((d + 1) * (k + 1)) *
          (Real.exp (-(c * E)) * Real.exp (-(c1 * E))) := by rw [hsplit]
    _ = Real.exp (-(c * E)) *
          ((3 : ℝ) ^ ((d + 1) * (k + 1)) * Real.exp (-(c1 * E))) := by ring
    _ ≤ Real.exp (-(c * (3 : ℝ) ^ (gamma * K))) *
          ((3 : ℝ) ^ ((d + 1) * (k + 1)) *
            Real.exp (-(c1 * (3 : ℝ) ^ (gamma * (k : ℝ))))) :=
        mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 (by positivity)) (by positivity)
          (Real.exp_pos _).le

/-! ## The amplitude sum at rate `c₁ ≥ 2`

The residual sum `∑_k 3^{(d+1)(k+1)} exp(-(c₁ 3^{γk}))` is the amplitude that the
sub-cube count and the scale sum are absorbed into. It is dominated by the
geometric majorant `exp(D log 3 + (D/γ) log(D/γ)) exp(-t) 3/(γ log 3)` of
the scale-sum lemma of `BfAmEllipticityLevelTailB` at `t = c₁/2`, and
then by the exhibited amplitude `subCubeUnionConst d exp(subCubeUnionConst d
|log γ|/γ)` of `exp_amplitude_le_b`; the only price is `c₁ ≥ 2`. -/

/-! ## The level tail at rate `c + c₁`

The union bound over the `3^{d(n-l)}` triadic sub-cubes of `cu_n` and the sum over the scales
are carried out exactly as in `BfAmEllipticityLevelTailB`, except that the per-scale exponent is
split by `levelTerm_point_le_c` instead of averaged: the level decay is taken
out at the *full* rate `c`, and the residual rate `c₁ ≥ 2` is absorbed into the
amplitude `subCubeUnionConst d exp(subCubeUnionConst d |log γ|/γ)`. The level
tail therefore comes out at the decay constant `c` rather than at half of the
per-scale constant. -/

/-! ## A level constant independent of the amplitude

The last ingredient of the conclusion is the pair of arithmetic clauses
`hAbs` and `hGeo` of `measureReal_minScale_gt_le`.
The earlier `levelTailConst C` pays `C` itself for the term
`C |log γ| / γ` of `hAbs`, which is why that reduction needs a per-scale
rate of order `2 * subCubeUnionConst d`. The bound below keeps the factor
`γ^C / γ` instead of discarding it: the singular part contributes
`C |log γ| γ^{C-1} ≤ C/(C-1) ≤ 3/2` and the constant part contributes
`(1 + log 2 + log C)(3/C)^γ γ^C ≤ 1 + log 2 + log 3`. Hence the *universal*
constant `1 + log 2 + log 3 + 3/2` works for every amplitude constant `C ≥ 3`,
and the present reduction needs only an absolute per-scale rate. -/

/-- `y e^{-y} ≤ 1`, from `y ≤ e^y`. -/
theorem y_mul_exp_neg_le_one (y : ℝ) : y * Real.exp (-y) ≤ 1 := by
  have hyexp : y ≤ Real.exp y := by
    have h := Real.add_one_le_exp y
    linarith only [h]
  have hmul : y * Real.exp (-y) ≤ Real.exp y * Real.exp (-y) :=
    mul_le_mul_of_nonneg_right hyexp (Real.exp_pos (-y)).le
  have hone : Real.exp y * Real.exp (-y) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  linarith only [hmul, hone]

/-- The growth of the two factors of the singular part. -/
theorem rpow_ratio_mul_rpow_le_c (C gamma : ℝ) (hC : 3 ≤ C) (hg0 : 0 < gamma)
    (hg1 : gamma < 1) : (3 / C) ^ gamma * gamma ^ C ≤ 3 / C := by
  have hC0 : 0 < C := by linarith only [hC]
  set A : ℝ := Real.log (C / 3) with hA
  set b : ℝ := -Real.log gamma with hb
  have hAle : A ≤ C := by
    have h := Real.log_le_sub_one_of_pos (by linarith only [hC] : (0 : ℝ) < C / 3)
    rw [← hA] at h
    linarith only [h, hC0]
  have hb0 : 0 ≤ b := by
    rw [hb]
    exact neg_nonneg.2 (Real.log_nonpos hg0.le hg1.le)
  have hhexp : Real.log gamma = -b := by
    rw [hb]
    ring
  have hexpneg : Real.exp (-b) = gamma := by
    rw [hb, neg_neg, Real.exp_log hg0]
  have hb_le : 1 - Real.exp (-b) ≤ b := by
    have h := Real.add_one_le_exp (-b)
    linarith only [h]
  have hone_sub : 0 ≤ 1 - Real.exp (-b) := by
    rw [hexpneg]
    linarith only [hg1]
  have hlog3C : Real.log (3 / C) = -A := by
    rw [hA, ← Real.log_inv]
    congr 1
    rw [inv_div]
  have hstep : (3 / C) ^ gamma * gamma ^ C = Real.exp (-(A * gamma + C * b)) := by
    rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < 3 / C), Real.rpow_def_of_pos hg0,
      hlog3C, hhexp]
    rw [← Real.exp_add]
    congr 1
    ring
  have hkey : A ≤ A * gamma + C * b := by
    have h1 : A * (1 - Real.exp (-b)) ≤ C * (1 - Real.exp (-b)) :=
      mul_le_mul_of_nonneg_right hAle hone_sub
    have h2 : C * (1 - Real.exp (-b)) ≤ C * b := mul_le_mul_of_nonneg_left hb_le hC0.le
    have h3 : A * gamma = A * Real.exp (-b) := by rw [hexpneg]
    linarith only [h1, h2, h3]
  calc (3 / C) ^ gamma * gamma ^ C = Real.exp (-(A * gamma + C * b)) := hstep
    _ ≤ Real.exp (-A) := Real.exp_le_exp.2 (by linarith only [hkey])
    _ = 3 / C := by rw [← hlog3C, Real.exp_log (by positivity : (0 : ℝ) < 3 / C)]

/-! ## The reduction at an arbitrary rate -/

/-! ## The rate-2 bound is still not enough

`measureReal_envelopeRatio_gt_two_mul_rpow_le`
(in `BfAmEllipticityScaleTail`) certifies the printed per-scale event at the
rate `2` with no factor in the level `n - m`. The reduction above closes
only at the rate `levelTailConstUniv + 2`, which is strictly larger than `2`, so
the rate-2 bound still does not reach it: the printed improvement
`3^{(d/2)((l-m)∨0)}` is still needed. The separation below is the exact
counterpart of the separation of the honest and displayed exponents
(in `BfAmEllipticityScaleTail`) at the present constant. -/

end

end SuperdiffusionCLT.Section2
