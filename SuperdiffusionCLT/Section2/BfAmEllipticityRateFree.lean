/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.BfAmEllipticityRateFreeB
public import SuperdiffusionCLT.Section2.BfAmEllipticityLevelTailC
public import SuperdiffusionCLT.Section2.BfAmEllipticityScaleTail

/-!
# The ellipticity anchor at an arbitrary per-scale rate

This module concerns lemma `l.bfAm.ellip`.  The level-tail reduction of
`BfAmEllipticityLevelTailC` produces the conclusion from the printed per-scale tail only at a
rate `c₀ ≥ 6.2918` (uniform in `d`).  The Γ₁ tail of `envelopeRatio` certifies only the rate `2`,
leaving a constant gap of `≈ 4.29`.

The rate-free reduction
`bfAmEllipticity_of_scaleTailAnyRate` is proved by calling `bfAmEllipticity_of_levelTail`
**directly**, and the rate threshold of that reduction is not traversed.  The
chain is `bfAmEllipticity_of_regimeSplit` → `bfAmEllipticity_of_scaleTailAnyRate` →
`bfAmEllipticity_of_levelTail`.

This file removes the gap.  The conclusion's constant `C` is
**existential** and sits ahead of everything, so a larger `C` absorbs a smaller
per-scale rate: the two arithmetic clauses `hAbs`, `hGeo`
(in `BfAmEllipticityRateFreeB`) hold at *any* fixed rate `c > 0` once the
amplitude constant is large enough, and the scale sum that the level tail pays
for the absorbed residual rate `c₁` is bounded by an amplitude of exactly the
printed shape `C exp(C |log γ| / γ)`. The rate `2` of
`measureReal_envelopeRatio_gt_two_mul_rpow_le` is therefore admissible.

The residual sum `ampAny d c₁ γ = ∑_k 3^{(d+1)(k+1)} exp(-(c₁ 3^{γk}))` is the
amplitude into which the sub-cube count and the scale sum are absorbed. The
geometric majorant of `BfAmEllipticityLevelTailC` needs `c₁ ≥ 2` (it spends
`exp(-t)` with `t = c₁/2 ≥ 1`); at a general rate the Legendre bound
`a u - t e^u ≤ a log(a/t) - a` (valid for *every* `t > 0`) does the work, and
the geometric decay is retained at the rate `ampLam c₁ = min (c₁/2) 1 ≤ c₁`.

What is *not* removable is the printed improvement `3^{(d/2)((l-m)∨0)}`: the
level decay `exp(-c 3^{γ(n-m)})` is extracted from the per-scale exponent
`E_k ≥ γK`, so the per-scale tail must decay at
`E_k = γk + (d/2) max (K-k) 0`, not at `γk`.
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

/-! ## The amplitude at any positive rate

The residual sum `ampAny d c₁ γ = ∑_k 3^{(d+1)(k+1)} exp(-(c₁ 3^{γk}))` is the
amplitude into which the sub-cube count and the scale sum are absorbed. The
geometric majorant of `BfAmEllipticityLevelTailC` needs `c₁ ≥ 2` (it spends `exp(-t)` with
`t = c₁/2 ≥ 1`); at a general rate the Legendre bound `a u - t e^u ≤ a log(a/t) - a`
(valid for *every* `t > 0`, not only `t ≥ 1`) does the work, and the geometric
decay is retained at the rate `ampLam c₁ = min (c₁/2) 1 ≤ c₁`: writing
`u = γ k log 3` and `a = (d+1)/γ`,

    D(k+1) log 3 - c₁ e^u = D log 3 + (a u - (c₁ - λ) e^u) - λ e^u
                          ≤ D log 3 + a log(a/(c₁-λ)) - a - λ u,

because `λ e^u ≥ λ u` for all `u ≥ 0` and `λ > 0`. Summing the resulting geometric
series gives the amplitude `exp(ampEX d c₁ γ) · 3/(λ γ log 3)`, which is absorbed
into `ampConst d c₁ · exp(ampConst d c₁ |log γ|/γ)`. -/

/-- The raw amplitude of the scale sum at rate `c₁`. -/
def ampAny (d : ℕ) (c1 gamma : ℝ) : ℝ :=
  ∑' k : ℕ, (3 : ℝ) ^ ((d + 1) * (k + 1)) *
    Real.exp (-(c1 * (3 : ℝ) ^ (gamma * (k : ℝ))))

/-- The geometric rate retained by the general amplitude bound. -/
def ampLam (c1 : ℝ) : ℝ := min (c1 / 2) 1

theorem ampLam_pos {c1 : ℝ} (hc1 : 0 < c1) : 0 < ampLam c1 :=
  lt_min (by linarith only [hc1]) one_pos

theorem ampLam_le_one (c1 : ℝ) : ampLam c1 ≤ 1 := min_le_right _ _

theorem ampLam_lt {c1 : ℝ} (hc1 : 0 < c1) : ampLam c1 < c1 := by
  rw [ampLam]
  have h := min_le_left (c1 / 2) 1
  linarith only [h, hc1]

/-- The exponent constant of the general amplitude bound. -/
def ampEX (d : ℕ) (c1 gamma : ℝ) : ℝ :=
  ((d : ℝ) + 1) * Real.log 3 +
    (((d : ℝ) + 1) / gamma) * Real.log ((((d : ℝ) + 1) / gamma) / (c1 - ampLam c1)) -
    ((d : ℝ) + 1) / gamma

/-- The Legendre bound with an arbitrary coefficient: `a u - t e^u ≤ a log(a/t) - a`
for every `a ≥ 1` and `t > 0`. -/
theorem legendre_exp_mul_sub_le (a t u : ℝ) (ha : 1 ≤ a) (ht : 0 < t) :
    a * u - t * Real.exp u ≤ a * Real.log (a / t) - a := by
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le zero_lt_one ha
  have h := legendre_exp_sub_le a (u + Real.log t) ha
  rw [Real.exp_add, Real.exp_log ht] at h
  have hlog : Real.log (a / t) = Real.log a - Real.log t :=
    Real.log_div (ne_of_gt ha0) (ne_of_gt ht)
  rw [hlog]
  linarith only [h]

/-- **One scale at any positive rate.** The term `3^{D(k+1)} e^{-c₁ 3^{γk}}` is at
most `exp(ampEX d c₁ γ)` times the geometric factor `(e^{-λγ log 3})^k`. -/
theorem exp_ampTerm_le_anyRate (d : ℕ) (hd : 2 ≤ d) {gamma c1 : ℝ} (hg0 : 0 < gamma)
    (hg1 : gamma ≤ 1) (hc1 : 0 < c1) (k : ℕ) :
    (3 : ℝ) ^ ((d + 1) * (k + 1)) * Real.exp (-(c1 * (3 : ℝ) ^ (gamma * (k : ℝ)))) ≤
      Real.exp (ampEX d c1 gamma) * Real.exp (-(ampLam c1 * gamma * Real.log 3)) ^ k := by
  have hD1 : (1 : ℝ) ≤ (d : ℝ) + 1 := by
    have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith only [hd2]
  have hlam0 : (0 : ℝ) < ampLam c1 := ampLam_pos hc1
  have ht0 : (0 : ℝ) < c1 - ampLam c1 := by
    have h := ampLam_lt hc1
    linarith only [h]
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  set u : ℝ := gamma * (k : ℝ) * Real.log 3 with hu
  set a : ℝ := ((d : ℝ) + 1) / gamma with ha
  have ha1 : 1 ≤ a := (one_le_div hg0).2 (le_trans hg1 hD1)
  have hau : a * u = ((d : ℝ) + 1) * (k : ℝ) * Real.log 3 := by
    rw [ha, hu]
    field_simp
  have hu0 : (0 : ℝ) ≤ u := by
    rw [hu]
    exact mul_nonneg (mul_nonneg hg0.le (Nat.cast_nonneg k)) hlog3.le
  have hleg := legendre_exp_mul_sub_le a (c1 - ampLam c1) u ha1 ht0
  have hexpu : u ≤ Real.exp u := by
    have h := Real.add_one_le_exp u
    linarith only [h, hu0]
  have hlamu : ampLam c1 * u ≤ ampLam c1 * Real.exp u :=
    mul_le_mul_of_nonneg_left hexpu hlam0.le
  have hsplit : c1 * Real.exp u =
      (c1 - ampLam c1) * Real.exp u + ampLam c1 * Real.exp u := by ring
  have hkey : a * u - c1 * Real.exp u ≤
      a * Real.log (a / (c1 - ampLam c1)) - a - ampLam c1 * u := by
    linarith only [hleg, hlamu, hsplit]
  have hL : (3 : ℝ) ^ ((d + 1) * (k + 1)) *
        Real.exp (-(c1 * (3 : ℝ) ^ (gamma * (k : ℝ)))) =
      Real.exp (((d : ℝ) + 1) * Real.log 3 + (a * u - c1 * Real.exp u)) := by
    rw [pow_three_eq_exp_b ((d + 1) * (k + 1)), rpow_three_eq_exp_b (gamma * (k : ℝ)),
      show gamma * (k : ℝ) * Real.log 3 = u from hu.symm, ← Real.exp_add]
    congr 1
    rw [hau]
    push_cast
    ring
  have hR : Real.exp (((d : ℝ) + 1) * Real.log 3 +
        (a * Real.log (a / (c1 - ampLam c1)) - a - ampLam c1 * u)) =
      Real.exp (ampEX d c1 gamma) * Real.exp (-(ampLam c1 * gamma * Real.log 3)) ^ k := by
    simp only [ampEX]
    rw [ha, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    rw [hu]
    ring
  calc (3 : ℝ) ^ ((d + 1) * (k + 1)) * Real.exp (-(c1 * (3 : ℝ) ^ (gamma * (k : ℝ))))
      = Real.exp (((d : ℝ) + 1) * Real.log 3 + (a * u - c1 * Real.exp u)) := hL
    _ ≤ Real.exp (((d : ℝ) + 1) * Real.log 3 +
          (a * Real.log (a / (c1 - ampLam c1)) - a - ampLam c1 * u)) :=
        Real.exp_le_exp.2 (by linarith only [hkey])
    _ = Real.exp (ampEX d c1 gamma) *
          Real.exp (-(ampLam c1 * gamma * Real.log 3)) ^ k := hR

/-- The raw amplitude at any positive rate is summable, by the geometric factor
of `exp_ampTerm_le_anyRate`. -/
theorem summable_ampAny (d : ℕ) (hd : 2 ≤ d) {gamma c1 : ℝ} (hg0 : 0 < gamma)
    (hg1 : gamma ≤ 1) (hc1 : 0 < c1) :
    Summable fun k : ℕ => (3 : ℝ) ^ ((d + 1) * (k + 1)) *
      Real.exp (-(c1 * (3 : ℝ) ^ (gamma * (k : ℝ)))) := by
  have hlam0 : (0 : ℝ) < ampLam c1 := ampLam_pos hc1
  refine Summable.of_nonneg_of_le (fun k => by positivity)
    (fun k => exp_ampTerm_le_anyRate d hd hg0 hg1 hc1 k) ?_
  exact (summable_geometric_of_lt_one (Real.exp_pos _).le
    (exp_neg_gamma_log_three_lt_one_b (mul_pos hlam0 hg0))).mul_left _

/-- **The amplitude sum at any positive rate.** -/
theorem tsum_ampAny_le_anyRate (d : ℕ) (hd : 2 ≤ d) {gamma c1 : ℝ} (hg0 : 0 < gamma)
    (hg1 : gamma ≤ 1) (hc1 : 0 < c1) :
    ampAny d c1 gamma ≤ Real.exp (ampEX d c1 gamma) * (3 / (ampLam c1 * gamma * Real.log 3)) := by
  have hlam0 : (0 : ℝ) < ampLam c1 := ampLam_pos hc1
  have hlample : ampLam c1 * gamma ≤ 1 := by
    have h := mul_le_mul (ampLam_le_one c1) hg1 hg0.le (by norm_num : (0 : ℝ) ≤ 1)
    linarith only [h]
  have hlt := exp_neg_gamma_log_three_lt_one_b (mul_pos hlam0 hg0)
  have hmaj := Summable.tsum_le_tsum (fun k => exp_ampTerm_le_anyRate d hd hg0 hg1 hc1 k)
    (summable_ampAny d hd hg0 hg1 hc1)
    ((summable_geometric_of_lt_one (Real.exp_pos _).le hlt).mul_left (Real.exp (ampEX d c1 gamma)))
  change (∑' k : ℕ, (3 : ℝ) ^ ((d + 1) * (k + 1)) *
      Real.exp (-(c1 * (3 : ℝ) ^ (gamma * (k : ℝ))))) ≤
    Real.exp (ampEX d c1 gamma) * (3 / (ampLam c1 * gamma * Real.log 3))
  rw [tsum_mul_left, tsum_geometric_of_lt_one (Real.exp_pos _).le hlt] at hmaj
  exact hmaj.trans (mul_le_mul_of_nonneg_left (inv_one_sub_exp_le_b (mul_pos hlam0 hg0) hlample)
    (Real.exp_pos _).le)

/-- The truncated log-ratio `max 0 (log ((d+1)/(c₁ - λ)))` entering the raw
amplitude exponent, shared by `ampK1` and `ampK2`. -/
def ampM (d : ℕ) (c1 : ℝ) : ℝ :=
  max 0 (Real.log (((d : ℝ) + 1) / (c1 - ampLam c1)))

/-- The constant part of the absorption of the raw amplitude. -/
def ampK1 (d : ℕ) (c1 : ℝ) : ℝ :=
  ((d : ℝ) + 1) * Real.log 3 +
    ((d : ℝ) + 1) * ampM d c1 +
    Real.log (3 / (ampLam c1 * Real.log 3))

/-- The coefficient of `|log γ|/γ` in the absorption of the raw amplitude. -/
def ampK2 (d : ℕ) (c1 : ℝ) : ℝ :=
  ((d : ℝ) + 1) * ampM d c1 + ((d : ℝ) + 1) + 1

/-- The amplitude constant of the absorbed raw amplitude: `ampConst d c₁ ≥ 1`, and
it dominates both `exp (ampK1 d c₁)` and `ampK2 d c₁`. -/
def ampConst (d : ℕ) (c1 : ℝ) : ℝ :=
  max 1 (max (Real.exp (ampK1 d c1)) (max (ampK2 d c1) 0))

theorem ampConst_nonneg (d : ℕ) (c1 : ℝ) : 0 ≤ ampConst d c1 := by
  rw [ampConst]
  exact le_trans zero_le_one (le_max_left _ _)

theorem exp_ampK1_le_ampConst (d : ℕ) (c1 : ℝ) :
    Real.exp (ampK1 d c1) ≤ ampConst d c1 := by
  rw [ampConst]
  exact le_trans (le_max_left _ _) (le_max_right _ _)

theorem ampK2_le_ampConst (d : ℕ) (c1 : ℝ) : ampK2 d c1 ≤ ampConst d c1 := by
  rw [ampConst]
  exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))

/-- **The raw amplitude is absorbed into `C exp(C |log γ|/γ)`**, with the exhibited
constant `ampConst d c₁`. Writing `t := |log γ|`, `l := log (D/(c₁-λ))`,
`m := max 0 l`, `q := log (3/(λ log 3))` (with `D := d+1`, `λ := ampLam c₁`), the
exponent `ampEX + log (3/(λ γ log 3))` is
`D log 3 + D/γ · l + D/γ · t - D/γ + q + t`, which the two elementary inequalities
`1/γ ≤ 1 + t/γ` and `l ≤ m` bound by `ampK1 d c₁ + ampK2 d c₁ · t/γ`. -/
theorem ampAny_le_const (d : ℕ) (hd : 2 ≤ d) {gamma c1 : ℝ} (hg0 : 0 < gamma)
    (hg1 : gamma < 1) (hc1 : 0 < c1) :
    ampAny d c1 gamma ≤ ampConst d c1 * Real.exp (ampConst d c1 * |Real.log gamma| / gamma) := by
  have hg1' : gamma ≤ 1 := le_of_lt hg1
  have hD1 : (1 : ℝ) ≤ (d : ℝ) + 1 := by
    have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith only [hd2]
  have hD0 : (0 : ℝ) < (d : ℝ) + 1 := lt_of_lt_of_le zero_lt_one hD1
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hlam0 : (0 : ℝ) < ampLam c1 := ampLam_pos hc1
  have hR0 : (0 : ℝ) < c1 - ampLam c1 := by
    have h := ampLam_lt hc1
    linarith only [h]
  have hinv0 : (0 : ℝ) < gamma⁻¹ := inv_pos.mpr hg0
  set t : ℝ := |Real.log gamma| with ht
  set l : ℝ := Real.log (((d : ℝ) + 1) / (c1 - ampLam c1)) with hl
  set m : ℝ := ampM d c1 with hm
  set q : ℝ := Real.log (3 / (ampLam c1 * Real.log 3)) with hq
  have ht0 : (0 : ℝ) ≤ t := by rw [ht]; exact abs_nonneg _
  have hl_le : l ≤ m := by rw [hm, ampM, hl]; exact le_max_right _ _
  have hm0 : (0 : ℝ) ≤ m := by rw [hm, ampM]; exact le_max_left _ _
  have hg_one : (1 : ℝ) ≤ gamma⁻¹ := by
    have h := one_le_one_div hg0 hg1'
    rwa [one_div] at h
  have hg_le : gamma⁻¹ ≤ 1 + t * gamma⁻¹ := by
    have h := inv_le_one_add_abs_log_div_b gamma hg0 hg1'
    rw [one_div, div_eq_mul_inv, ← ht] at h
    exact h
  have hgl : gamma⁻¹ * l ≤ m * (1 + t * gamma⁻¹) :=
    (mul_le_mul_of_nonneg_left hl_le hinv0.le).trans (by
      have h := mul_le_mul_of_nonneg_right hg_le hm0
      rwa [mul_comm (1 + t * gamma⁻¹) m] at h)
  have hlog1 : Real.log ((((d : ℝ) + 1) / gamma) / (c1 - ampLam c1)) = l + t := by
    have h1 : (((d : ℝ) + 1) / gamma) / (c1 - ampLam c1) =
        (((d : ℝ) + 1) / (c1 - ampLam c1)) * gamma⁻¹ := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
    rw [h1, Real.log_mul (ne_of_gt (div_pos hD0 hR0)) (inv_ne_zero (ne_of_gt hg0)),
      Real.log_inv, ← abs_of_nonpos (Real.log_nonpos hg0.le hg1'), ← hl, ← ht]
  have hlog2 : Real.log (3 / (ampLam c1 * gamma * Real.log 3)) = q + t := by
    have h1 : 3 / (ampLam c1 * gamma * Real.log 3) =
        (3 / (ampLam c1 * Real.log 3)) * gamma⁻¹ := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
    rw [h1, Real.log_mul (ne_of_gt (div_pos (by norm_num) (mul_pos hlam0 hlog3)))
      (inv_ne_zero (ne_of_gt hg0)), Real.log_inv,
      ← abs_of_nonpos (Real.log_nonpos hg0.le hg1'), ← hq, ← ht]
  have hX : ampEX d c1 gamma + Real.log (3 / (ampLam c1 * gamma * Real.log 3)) =
      ((d : ℝ) + 1) * Real.log 3 +
        (((d : ℝ) + 1) * gamma⁻¹ * l +
          (((d : ℝ) + 1) * gamma⁻¹ * t - ((d : ℝ) + 1) * gamma⁻¹) + t) + q := by
    rw [ampEX, hlog1, hlog2]
    ring
  have hK : ampK1 d c1 + ampK2 d c1 * (t * gamma⁻¹) =
      ((d : ℝ) + 1) * Real.log 3 +
        (((d : ℝ) + 1) * gamma⁻¹ * l +
          (((d : ℝ) + 1) * gamma⁻¹ * t - ((d : ℝ) + 1) * gamma⁻¹) + t) + q +
        (((d : ℝ) + 1) * (m * (1 + t * gamma⁻¹) - gamma⁻¹ * l) +
          ((d : ℝ) + 1) * gamma⁻¹ + t * (gamma⁻¹ - 1)) := by
    rw [ampK1, ampK2, ← hq, ← hm]
    ring
  have hpos : 0 ≤ ((d : ℝ) + 1) * (m * (1 + t * gamma⁻¹) - gamma⁻¹ * l) +
      ((d : ℝ) + 1) * gamma⁻¹ + t * (gamma⁻¹ - 1) :=
    add_nonneg (add_nonneg (mul_nonneg hD0.le (sub_nonneg.mpr hgl))
      (mul_nonneg hD0.le hinv0.le)) (mul_nonneg ht0 (sub_nonneg.mpr hg_one))
  have hStepB : Real.exp (ampK1 d c1 + ampK2 d c1 * (t * gamma⁻¹)) ≤
      ampConst d c1 * Real.exp (ampConst d c1 * t / gamma) := by
    have h4 : ampConst d c1 * (t * gamma⁻¹) = ampConst d c1 * t / gamma := by
      rw [div_eq_mul_inv]
      ring
    have h2 : Real.exp (ampK2 d c1 * (t * gamma⁻¹)) ≤
        Real.exp (ampConst d c1 * t / gamma) := by
      refine Real.exp_le_exp.2 ?_
      have h3 : ampK2 d c1 * (t * gamma⁻¹) ≤ ampConst d c1 * (t * gamma⁻¹) :=
        mul_le_mul_of_nonneg_right (ampK2_le_ampConst d c1) (mul_nonneg ht0 hinv0.le)
      linarith only [h3, h4]
    calc Real.exp (ampK1 d c1 + ampK2 d c1 * (t * gamma⁻¹))
        = Real.exp (ampK1 d c1) * Real.exp (ampK2 d c1 * (t * gamma⁻¹)) := Real.exp_add _ _
      _ ≤ Real.exp (ampK1 d c1) * Real.exp (ampConst d c1 * t / gamma) :=
          mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ ≤ ampConst d c1 * Real.exp (ampConst d c1 * t / gamma) :=
          mul_le_mul_of_nonneg_right (exp_ampK1_le_ampConst d c1) (Real.exp_pos _).le
  have hA1 : Real.exp (ampEX d c1 gamma) * (3 / (ampLam c1 * gamma * Real.log 3)) =
      Real.exp (ampEX d c1 gamma + Real.log (3 / (ampLam c1 * gamma * Real.log 3))) := by
    rw [Real.exp_add,
      Real.exp_log (by positivity : (0 : ℝ) < 3 / (ampLam c1 * gamma * Real.log 3))]
  refine (tsum_ampAny_le_anyRate d hd hg0 hg1' hc1).trans (hA1.le.trans ?_)
  refine (Real.exp_le_exp.2 ?_).trans hStepB
  rw [hX, hK]
  exact le_add_of_nonneg_right hpos

/-- The weighted summand of the union bound is summable at any positive residual
rate `c₁`, by `levelTerm_point_le_c` and the amplitude sum `summable_ampAny`. -/
theorem summable_ampTerm (d : ℕ) (hd : 2 ≤ d) {gamma c c1 K : ℝ} (hg0 : 0 < gamma)
    (hg1 : gamma < 1) (hc : 0 < c) (hc1 : 0 < c1) :
    Summable fun k : ℕ => (3 : ℝ) ^ ((d + 1) * (k + 1)) *
        Real.exp (-((c + c1) * (3 : ℝ) ^ (gamma * (k : ℝ) +
          ((d : ℝ) / 2) * max (K - (k : ℝ)) 0))) :=
  Summable.of_nonneg_of_le (fun k => by positivity)
    (fun k => levelTerm_point_le_c d hd hg0 (le_of_lt hg1) hc hc1 k)
    ((summable_ampAny d hd hg0 (le_of_lt hg1) hc1).mul_left
      (Real.exp (-(c * (3 : ℝ) ^ (gamma * K)))))

/-- **The sum over the scales at any split of the rate.** -/
theorem tsum_ampTerm_le (d : ℕ) (hd : 2 ≤ d) {gamma c c1 K : ℝ} (hg0 : 0 < gamma)
    (hg1 : gamma < 1) (hc : 0 < c) (hc1 : 0 < c1) :
    ∑' k : ℕ, (3 : ℝ) ^ ((d + 1) * (k + 1)) *
        Real.exp (-((c + c1) * (3 : ℝ) ^ (gamma * (k : ℝ) +
          ((d : ℝ) / 2) * max (K - (k : ℝ)) 0))) ≤
      Real.exp (-(c * (3 : ℝ) ^ (gamma * K))) *
        (ampConst d c1 * Real.exp (ampConst d c1 * |Real.log gamma| / gamma)) := by
  have hstep := Summable.tsum_le_tsum
    (fun k => levelTerm_point_le_c d hd hg0 (le_of_lt hg1) hc hc1 k)
    (summable_ampTerm d hd hg0 hg1 hc hc1)
    ((summable_ampAny d hd hg0 (le_of_lt hg1) hc1).mul_left
      (Real.exp (-(c * (3 : ℝ) ^ (gamma * K)))))
  refine hstep.trans ?_
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left (ampAny_le_const d hd hg0 hg1 hc1) (Real.exp_pos _).le

/-- **The level tail at any split `c + c₁` of the per-scale rate**, for arbitrary
`c, c₁ > 0`: the union bound and the sum over the scales, with the residual amplitude `ampAny`
in place of the rate-`2` amplitude. -/
theorem measureReal_badLevel_le_of_scaleTailAnyRate (d : ℕ) (hd : 2 ≤ d)
    {P : ProbabilityMeasure (ShellSeq d)} {m n : ℕ} {gamma c c1 : ℝ} (hg0 : 0 < gamma)
    (hg1 : gamma < 1) (hc : 0 < c) (hc1 : 0 < c1)
    (hScaleTail : ∀ (k : ℕ) (Q : TriadicCube d), Q.scale = (n : ℤ) - (k : ℤ) →
      P.toMeasure.real {omega : ShellSeq d |
          2 * 1 * (3 : ℝ) ^ (gamma * (k : ℝ)) < envelopeRatio m Q omega} ≤
        Real.exp (-((c + c1) * (3 : ℝ) ^ (gamma * (k : ℝ) +
          ((d : ℝ) / 2) * max (((n : ℝ) - (m : ℝ)) - (k : ℝ)) 0)))) :
    P.toMeasure.real {omega : ShellSeq d | badLevel d m gamma n omega} ≤
      ampConst d c1 * Real.exp (ampConst d c1 * |Real.log gamma| / gamma) *
        Real.exp (-(c * (3 : ℝ) ^ (gamma * ((n : ℝ) - (m : ℝ))))) := by
  have hkr : ∀ Q : TriadicCube d, Q.scale ≤ (n : ℤ) →
      ((((n : ℤ) - Q.scale).toNat : ℕ) : ℝ) = (n : ℝ) - (Q.scale : ℝ) := by
    intro Q _
    have h1 : (((n : ℤ) - Q.scale).toNat : ℤ) = (n : ℤ) - Q.scale :=
      Int.toNat_of_nonneg (by omega)
    exact_mod_cast h1
  have hset : {omega : ShellSeq d | badLevel d m gamma n omega} =
      {omega : ShellSeq d | ∃ Q : TriadicCube d, Q.scale ≤ (n : ℤ) ∧
        cubeCenter Q ∈ cubeSet (originCube d (n : ℤ)) ∧
        (fun k : ℕ => 2 * 1 * (3 : ℝ) ^ (gamma * (k : ℝ))) (((n : ℤ) - Q.scale).toNat) <
          envelopeRatio m Q omega} := by
    ext omega
    constructor
    · rintro ⟨Q, h1, h2, h3⟩
      refine ⟨Q, h1, h2, ?_⟩
      change 2 * 1 * (3 : ℝ) ^ (gamma * ((((n : ℤ) - Q.scale).toNat : ℕ) : ℝ)) <
        envelopeRatio m Q omega
      rw [hkr Q h1]
      exact h3
    · rintro ⟨Q, h1, h2, h3⟩
      refine ⟨Q, h1, h2, ?_⟩
      change 2 * 1 * (3 : ℝ) ^ (gamma * ((((n : ℤ) - Q.scale).toNat : ℕ) : ℝ)) <
        envelopeRatio m Q omega at h3
      rw [hkr Q h1] at h3
      exact h3
  have htail : ∀ (k : ℕ) (Q : TriadicCube d), Q.scale = (n : ℤ) - (k : ℤ) →
      P.toMeasure.real {omega : ShellSeq d |
          (fun j : ℕ => 2 * 1 * (3 : ℝ) ^ (gamma * (j : ℝ))) k <
            envelopeRatio m Q omega} ≤
        (fun j : ℕ => Real.exp (-((c + c1) * (3 : ℝ) ^ (gamma * (j : ℝ) +
          ((d : ℝ) / 2) * max (((n : ℝ) - (m : ℝ)) - (j : ℝ)) 0)))) k :=
    fun k Q hQ => hScaleTail k Q hQ
  have hkey := measureReal_exists_subCube_gt_le_of_scaleTail (P := P) m n
    (fun k : ℕ => 2 * 1 * (3 : ℝ) ^ (gamma * (k : ℝ)))
    (fun k : ℕ => Real.exp (-((c + c1) * (3 : ℝ) ^ (gamma * (k : ℝ) +
      ((d : ℝ) / 2) * max (((n : ℝ) - (m : ℝ)) - (k : ℝ)) 0))))
    htail (fun k => (Real.exp_pos _).le) (summable_ampTerm d hd hg0 hg1 hc hc1)
  have htsum := tsum_ampTerm_le (d := d) (gamma := gamma) (c := c) (c1 := c1)
    (K := (n : ℝ) - (m : ℝ)) hd hg0 hg1 hc hc1
  have hAmp : Real.exp (-(c * (3 : ℝ) ^ (gamma * ((n : ℝ) - (m : ℝ))))) *
      (ampConst d c1 * Real.exp (ampConst d c1 * |Real.log gamma| / gamma)) =
      ampConst d c1 * Real.exp (ampConst d c1 * |Real.log gamma| / gamma) *
        Real.exp (-(c * (3 : ℝ) ^ (gamma * ((n : ℝ) - (m : ℝ))))) := by ring
  rw [hset]
  exact hkey.trans (htsum.trans (le_of_eq hAmp))

/-- **The absorbed amplitude is monotone in the constant**: for `0 ≤ K ≤ C` and
`0 ≤ t`, `K exp(K t) ≤ C exp(C t)`. -/
theorem mul_exp_mono {K C t : ℝ} (hK : 0 ≤ K) (hKC : K ≤ C) (ht : 0 ≤ t) :
    K * Real.exp (K * t) ≤ C * Real.exp (C * t) := by
  have hC0 : (0 : ℝ) ≤ C := le_trans hK hKC
  have h1 : K * Real.exp (K * t) ≤ C * Real.exp (K * t) :=
    mul_le_mul_of_nonneg_right hKC (Real.exp_pos _).le
  have h2 : Real.exp (K * t) ≤ Real.exp (C * t) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hKC ht)
  exact h1.trans (mul_le_mul_of_nonneg_left h2 hC0)

/-- **The conclusion at ANY positive per-scale rate `c₀`.** This is the
conclusion at a rate `c₀ ≥ 6.2918`, with that hypothesis replaced by `0 < c₀`: the level rate
is `c₀/2`, the residual rate `c₀/2` is absorbed into the enlarged existential constant
`Csc := max 3 (max (subCubeUnionConst d) (max (max Cabs Cgeo) (ampConst d (c₀/2))))`,
where `Cabs`, `Cgeo` are the rate-`c₀/2` thresholds of `exists_hAbs_large` and
`exists_hGeo_large`.  The proof goes to `bfAmEllipticity_of_levelTail`
directly. -/
theorem bfAmEllipticity_of_scaleTailAnyRate (d : ℕ) (hd : 2 ≤ d) (c0 : ℝ)
    (hc0 : 0 < c0)
    (hScaleTail : ∀ P : ProbabilityMeasure (ShellSeq d),
        ShellLawPrefix d P → ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P →
        ShellLawJ4 d P →
        ∀ (m n : ℕ), m ≤ n → ∀ gamma : ℝ, 0 < gamma → gamma < 1 →
          ∀ (k : ℕ) (Q : TriadicCube d), Q.scale = (n : ℤ) - (k : ℤ) →
            P.toMeasure.real {omega : ShellSeq d |
                2 * 1 * (3 : ℝ) ^ (gamma * (k : ℝ)) < envelopeRatio m Q omega} ≤
              Real.exp (-(c0 * (3 : ℝ) ^ (gamma * (k : ℝ) +
                ((d : ℝ) / 2) * max (((n : ℝ) - (m : ℝ)) - (k : ℝ)) 0)))) :
    ∃ C : ℝ,
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ P : ProbabilityMeasure (ShellSeq d),
          ShellLawPrefix d P → ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P →
          ShellLawJ4 d P →
          ∀ m : ℕ,
            (∀ U : Homogenization.Book.Ch02.Domain d,
                Measurable
                  (fun omega : ShellSeq d =>
                      Carriers.blockMatrixOperatorNorm
                        (envelopeRescale d nu m
                          (Homogenization.coarseBlockMatrix
                            (U : Set (Homogenization.Vec d))
                            (coefficientCutoff nu omega m).toCoeffField))) ∧
                IndependentSums.IsBigOWith P.toMeasure
                  (IndependentSums.gammaSigma 1)
                  (fun omega : ShellSeq d =>
                    Carriers.blockMatrixOperatorNorm
                      (envelopeRescale d nu m
                        (Homogenization.coarseBlockMatrix
                          (U : Set (Homogenization.Vec d))
                          (coefficientCutoff nu omega m).toCoeffField)))
                  1) ∧
              (∀ n : ℕ,
                  BlockMatLoewnerLE
                      (envelopeRescale d nu m (Carriers.annealedBlockMatInfinite nu m P))
                      (envelopeRescale d nu m
                        (annealedBlockMatrix nu m P (cubeSet (originCube d (n : ℤ))))) ∧
                    BlockMatLoewnerLE
                      (envelopeRescale d nu m
                        (annealedBlockMatrix nu m P (cubeSet (originCube d (n : ℤ)))))
                      (Homogenization.Book.Ch02.blockIdentity d)) ∧
              (∀ gamma : ℝ, 0 < gamma → gamma < 1 →
                  ∃ S : ShellSeq d → ℝ,
                    Measurable S ∧
                    IndependentSums.IsBigO P.toMeasure
                        (IndependentSums.gammaSigma gamma) S
                        (C * Real.exp (C * |Real.log gamma| / gamma) * (3 : ℝ) ^ m) ∧
                      ∀ᵐ omega : ShellSeq d ∂P.toMeasure,
                        ∀ n : ℕ, S omega ≤ (3 : ℝ) ^ n →
                        ∀ Q : Homogenization.TriadicCube d, Q.scale ≤ (n : ℤ) →
                          cubeCenter Q ∈ cubeSet (originCube d (n : ℤ)) →
                            BlockMatLoewnerLE
                              (((3 : ℝ) ^ (-(gamma * ((n : ℝ) - (Q.scale : ℝ))))) •
                                envelopeRescale d nu m
                                  (Homogenization.coarseBlockMatrix
                                    (cubeSet Q)
                                    (coefficientCutoff nu omega m).toCoeffField))
                              ((2 : ℝ) • Homogenization.Book.Ch02.blockIdentity d)) := by
  have hc : (0 : ℝ) < c0 / 2 := by linarith only [hc0]
  obtain ⟨Cabs, _hCabs3, hCabs⟩ := exists_hAbs_large (c0 / 2) hc
  obtain ⟨Cgeo, _hCgeo3, hCgeo⟩ := exists_hGeo_large (c0 / 2) hc
  set Csc : ℝ := max 3 (max (subCubeUnionConst d) (max (max Cabs Cgeo) (ampConst d (c0 / 2))))
    with hCsc
  have hCsc3 : (3 : ℝ) ≤ Csc := by rw [hCsc]; exact le_max_left (3 : ℝ) _
  have hpair : max (subCubeUnionConst d)
      (max (max Cabs Cgeo) (ampConst d (c0 / 2))) ≤ Csc := by
    rw [hCsc]
    exact le_max_right (3 : ℝ) _
  have hinner : max (max Cabs Cgeo) (ampConst d (c0 / 2)) ≤ Csc :=
    le_trans (le_max_right (subCubeUnionConst d) _) hpair
  have hU : subCubeUnionConst d ≤ Csc :=
    le_trans (le_max_left (subCubeUnionConst d) _) hpair
  have hCC : max Cabs Cgeo ≤ Csc :=
    le_trans (le_max_left (max Cabs Cgeo) _) hinner
  have hCabs_le : Cabs ≤ Csc := le_trans (le_max_left Cabs Cgeo) hCC
  have hCgeo_le : Cgeo ≤ Csc := le_trans (le_max_right Cabs Cgeo) hCC
  have hamp_le : ampConst d (c0 / 2) ≤ Csc :=
    le_trans (le_max_right (max Cabs Cgeo) _) hinner
  refine bfAmEllipticity_of_levelTail d Csc (c0 / 2) hCsc3 hc ?_ ?_ ?_
  · intro gamma hg0 hg1
    exact hCabs Csc hCabs_le gamma hg0 hg1
  · intro gamma hg0 hg1
    exact hCgeo Csc hCgeo_le gamma hg0 hg1
  · intro nu _hnu0 _hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 m gamma hg0 hg1 k
    have hsplit : c0 / 2 + c0 / 2 = c0 := by ring
    have hb := measureReal_badLevel_le_of_scaleTailAnyRate (d := d) (P := P) (m := m)
      (n := m + k) (gamma := gamma) (c := c0 / 2) (c1 := c0 / 2) hd hg0 hg1 hc hc
      (fun j Q hQ => by
        have hst := hScaleTail P hPrefix hJ1 hJ2 hJ3 hJ4 m (m + k) (Nat.le_add_right m k)
          gamma hg0 hg1 j Q hQ
        rwa [← hsplit] at hst)
    have hcast : (((m + k : ℕ) : ℝ) - (m : ℝ)) = (k : ℝ) := by
      push_cast
      ring
    rw [hcast] at hb
    have ht : (0 : ℝ) ≤ |Real.log gamma| / gamma := div_nonneg (abs_nonneg _) hg0.le
    have hmono : ampConst d (c0 / 2) *
        Real.exp (ampConst d (c0 / 2) * |Real.log gamma| / gamma) ≤
        Csc * Real.exp (Csc * |Real.log gamma| / gamma) := by
      have h1 := mul_exp_mono (K := ampConst d (c0 / 2)) (C := Csc)
        (t := |Real.log gamma| / gamma) (ampConst_nonneg d (c0 / 2)) hamp_le ht
      have h2 : ampConst d (c0 / 2) * |Real.log gamma| / gamma =
          ampConst d (c0 / 2) * (|Real.log gamma| / gamma) := mul_div_assoc _ _ _
      have h3 : Csc * |Real.log gamma| / gamma = Csc * (|Real.log gamma| / gamma) :=
        mul_div_assoc _ _ _
      rwa [h2, h3]
    exact hb.trans (mul_le_mul_of_nonneg_right hmono (Real.exp_pos _).le)

end

end SuperdiffusionCLT.Section2

