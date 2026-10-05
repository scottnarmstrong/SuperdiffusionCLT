/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.BfAmEllipticityWorkB

/-!
# Reducing the level tail `hLevel` to the printed per-scale tail

The proof of lemma `l.bfAm.ellip` rests on the pointwise square bound labelled
`e.km.square.bound`:

> `(C(1∨m))^{-1} ||k_m||²_{L²(z+cu_l)} ≤ 1 + O_{Γ₁}(C 3^{-((d/2)(l-m)∨0)})`.

Its first deduced consequence is the per-scale tail:

> `P[ (C(1∨m))^{-1} ||k_m||²_{L²(cu_l)} > 2t3^{γ(n-l)} ]`
> `≤ exp(-ct 3^{γ(n-l)+(d/2)((l-m)∨0)})`,

and the printed *level* tail `hLevel` is the union bound over the `3^{d(n-l)}` triadic
sub-cubes of each scale `l ≤ n` followed by the sum over the scales:

> `≤ exp(C|log γ|/γ) exp(-c 3^{γ(n-m)})`.

The theorem `measureReal_exists_subCube_gt_le_of_scaleTail` (in `EnvelopeMinimalScale`) already
formalises the union over the sub-cubes; read at the per-scale tail
`isBigOWith_gammaSigma_envelopeRatio`, which holds at amplitude `1` uniformly in the cube and in
`m`, it carries **no decay in the level**.  This file supplies the
remaining half, the sum over the scales at the *printed* per-scale tail, whose exponent carries
the improvement `3^{(d/2)((l-m)∨0)}`, and concludes the exact `hLevel` shape that
`bfAmEllipticity_of_levelTail` demands, with the two constants exhibited.

The input taken as a hypothesis is therefore exactly one printed display: the per-scale tail
(hence, through the mean-plus-`Γ₁`-tail computation of the printed proof, the improved square
bound `e.km.square.bound`).  No shell law is missing: the hypothesis `hScaleTail` is quantified
over the same five laws `ShellLawPrefix`, `ShellLawJ1Restriction`, `ShellLawJ2`, `ShellLawJ3`,
`ShellLawJ4` that the main statement and `hLevel` carry.

DIMENSION ONE IS OUT OF SCOPE: the sum over the scales uses `d/2 ≥ γ` for
`γ ∈ (0,1)`, so `2 ≤ d` is assumed (and only there).
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

/-! ## Elementary exponential inequalities (ported, renamed) -/

theorem log_three_pos_b : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)

/-- The Legendre bound `sup_{u} (a u - e^u) = a log a - a` for `a ≥ 1`. -/
theorem legendre_exp_sub_le (a u : ℝ) (ha : 1 ≤ a) :
    a * u - Real.exp u ≤ a * Real.log a - a := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have h1 : u - Real.log a + 1 ≤ Real.exp (u - Real.log a) := Real.add_one_le_exp _
  have h2 : Real.exp (u - Real.log a) = Real.exp u / a := by
    rw [Real.exp_sub, Real.exp_log ha0]
  rw [h2] at h1
  have h3 : (u - Real.log a + 1) * a ≤ Real.exp u / a * a :=
    mul_le_mul_of_nonneg_right h1 ha0.le
  rw [div_mul_cancel₀ _ (ne_of_gt ha0)] at h3
  have h4 : a * u - a * Real.log a + a ≤ Real.exp u := by
    calc a * u - a * Real.log a + a = (u - Real.log a + 1) * a := by ring
      _ ≤ Real.exp u := h3
  linarith only [h4]

/-- For `gamma ∈ (0,1]` the reciprocal is below `1 + |log gamma| / gamma`. -/
theorem inv_le_one_add_abs_log_div_b (gamma : ℝ) (h0 : 0 < gamma) (h1 : gamma ≤ 1) :
    1 / gamma ≤ 1 + |Real.log gamma| / gamma := by
  have hlog : Real.log gamma ≤ 0 := Real.log_nonpos h0.le h1
  have habs : |Real.log gamma| = -Real.log gamma := abs_of_nonpos hlog
  have hsub : Real.log gamma ≤ gamma - 1 := Real.log_le_sub_one_of_pos h0
  have hnum : 1 ≤ gamma + |Real.log gamma| := by
    rw [habs]; linarith only [hsub]
  have hkey : 1 / gamma ≤ (gamma + |Real.log gamma|) / gamma := by
    gcongr
  rw [add_div, div_self (ne_of_gt h0)] at hkey
  linarith only [hkey]

/-! ## The geometric sum over the scales at the printed tail -/

theorem exp_neg_gamma_log_three_lt_one_b {gamma : ℝ} (hg0 : 0 < gamma) :
    Real.exp (-(gamma * Real.log 3)) < 1 := by
  rw [Real.exp_lt_one_iff]
  exact neg_lt_zero.2 (mul_pos hg0 log_three_pos_b)

theorem inv_one_sub_exp_le_b {gamma : ℝ} (hg0 : 0 < gamma) (hg1 : gamma ≤ 1) :
    (1 - Real.exp (-(gamma * Real.log 3)))⁻¹ ≤ 3 / (gamma * Real.log 3) := by
  set x : ℝ := gamma * Real.log 3 with hx
  have hx0 : 0 < x := mul_pos hg0 log_three_pos_b
  have hxle : x ≤ Real.log 3 := by
    rw [hx]
    exact mul_le_of_le_one_left log_three_pos_b.le hg1
  have hthird : (1 : ℝ) / 3 ≤ Real.exp (-x) := by
    have hmono : Real.exp (-Real.log 3) ≤ Real.exp (-x) :=
      Real.exp_le_exp.2 (by linarith only [hxle])
    have h3 : Real.exp (-Real.log 3) = 1 / 3 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
      norm_num
    linarith only [hmono, h3]
  have hone : Real.exp (-x) + x * Real.exp (-x) ≤ 1 := by
    have h := Real.add_one_le_exp x
    have hmul := mul_le_mul_of_nonneg_right h (Real.exp_pos (-x)).le
    rw [← Real.exp_add] at hmul
    have hzero : Real.exp (x + -x) = 1 := by
      rw [add_neg_cancel, Real.exp_zero]
    rw [hzero] at hmul
    have hring : (x + 1) * Real.exp (-x) = Real.exp (-x) + x * Real.exp (-x) := by ring
    linarith only [hmul, hring]
  have hlow : x / 3 ≤ 1 - Real.exp (-x) := by
    have hmul : x * (1 / 3) ≤ x * Real.exp (-x) :=
      mul_le_mul_of_nonneg_left hthird hx0.le
    have hring : x * (1 / 3) = x / 3 := by ring
    linarith only [hone, hmul, hring]
  have hpos : (0 : ℝ) < x / 3 := by linarith only [hx0]
  have hinv := inv_anti₀ hpos hlow
  rw [inv_div] at hinv
  exact hinv

/-! ## The sum over the scales at the printed per-scale tail

The per-scale tail of the paper carries
the improvement `3^{(d/2)((l-m)∨0)}` in its **decay**:

> `≤ exp(-ct 3^{γ(n-l)+(d/2)((l-m)∨0)})`,

so with `l = n - k` and `K = n - m` the scale `l = n - k` contributes
`exp(-ct 3^{γk+(d/2)max(K-k,0)})` to the union bound. Its two extremes are what the
sum needs: the exponent is at least `γk` (so the geometric sum over the scales
converges) and at least `γK` (so the common level decay `3^{γK}` can be taken out).
The factor `1/2` paid in combining them is exactly why the per-scale tail is used
at the constant `4t` below and the level tail is produced at the constant `2t`. -/

/-- The number of triadic sub-cubes of a scale, as an exponential. -/
theorem pow_three_eq_exp_b (N : ℕ) :
    (3 : ℝ) ^ N = Real.exp ((N : ℝ) * Real.log 3) := by
  rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 3)]

/-- A real power of `3`, as an exponential. -/
theorem rpow_three_eq_exp_b (y : ℝ) : (3 : ℝ) ^ y = Real.exp (y * Real.log 3) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
  congr 1
  ring

/-! ## The level tail at the printed per-scale tail -/

/-! ## The level tail and the conclusion -/

end

end SuperdiffusionCLT.Section2
