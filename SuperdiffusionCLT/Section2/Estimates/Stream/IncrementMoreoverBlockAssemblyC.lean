/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementMoreoverBlockAssemblyB
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementMoreoverBlockG

/-!
# The corrected amplitude of the `Γ_{2σ}` tail of `log K_σ`

`IncrementMoreoverBlockG` produces the tail of
`log K_σ` at the honest amplitude
`2 (log 3) (4 + (2 A δ⁻¹ √Θ)^{1/σ})`, `Θ = 3 + σ⁻¹ + (3/(2σ)) max(0, log(6A²δ⁻²σ⁻¹))`,
where `A` is the uniform `Γ₂` amplitude of the envelope family. This module
compares that amplitude with the closed shape

`C₀ · (C₁ δ⁻¹ √(σ⁻¹ log(e + C₂ δ⁻¹ σ⁻¹)))^{1/σ}`,

whose free constant `C₀` sits **outside** the `1/σ` power and whose logarithm is
regularized so that its argument is at least `e`.

Two elementary mechanisms carry the comparison, and both are needed:

* below the `1/σ` power, `2 A δ⁻¹ √Θ ≤ e^σ · C₁ δ⁻¹ √(σ⁻¹ L)` with
  `L = log(e + δ⁻¹σ⁻¹)`, because `σ Θ` is at most a constant multiple of
  `L · e^{2σ}` — the `3σ` of `σΘ` is absorbed by `e^{2σ}` and the logarithm
  `log(6A²δ⁻²σ⁻¹)` by `L`, since `2 log δ⁻¹ + log σ⁻¹ = 2(log δ⁻¹ + log σ⁻¹) + log σ`;
* above it, the whole `1/σ` power is bounded below by `1/2`, uniformly in `σ`,
  because `x^{1/σ} = exp((log x)/σ) ≥ 1 + (log x)/σ` and `log σ ≤ σ`. This is
  what lets the additive `4` of the honest amplitude be absorbed by the free
  outer constant, which is impossible when the constant sits inside the power.

## Main definitions and results

* `moreoverAmpGauge`, `moreoverAmpInner`: the constants `G(A) = max(0, log 6A²)`
  and `C₁(A) = 3A(3 + G(A))`.
* `sigma_mul_expTailTheta_le`: `σ Θ ≤ (7 + 3G/2) L e^{2σ}`.
* `half_le_moreoverAmpBase_rpow`: the uniform lower bound `1/2` of the power.
* `moreoverLogScaleAmplitude_le_moreoverAmpBound`: the comparison.
* `moreoverAmpOuterConst`, `moreoverAmpInnerConst`, `moreoverLogArgConst`: the
  three constants of the block, in `d` and `s` only.

## References

* `e.mathcal.K.int`.
-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Section2
namespace Estimates
namespace Stream

open Homogenization MeasureTheory
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open scoped ENNReal

noncomputable section

/-! ## The regularized logarithm -/

section Logarithm

variable {delta sigma : ℝ}

/-- **The regularization keeps the logarithm above `1`**, so that the square
root of the corrected amplitude is honest at every `(δ, σ)`. -/
theorem one_le_log_expOne_add (hdelta : 0 < delta) (hsigma : 0 < sigma) :
    (1 : ℝ) ≤ Real.log (Real.exp 1 + delta⁻¹ * sigma⁻¹) := by
  have hpos : (0 : ℝ) < delta⁻¹ * sigma⁻¹ := by positivity
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log (Real.exp 1 + delta⁻¹ * sigma⁻¹) :=
        Real.log_le_log (Real.exp_pos 1) (by linarith only [hpos])

/-- The regularized logarithm dominates `log δ⁻¹ + log σ⁻¹`. -/
theorem log_inv_add_log_inv_le (hdelta : 0 < delta) (hsigma : 0 < sigma) :
    Real.log delta⁻¹ + Real.log sigma⁻¹ ≤
      Real.log (Real.exp 1 + delta⁻¹ * sigma⁻¹) := by
  have hd : (0 : ℝ) < delta⁻¹ := by positivity
  have hs : (0 : ℝ) < sigma⁻¹ := by positivity
  have hmul : Real.log (delta⁻¹ * sigma⁻¹) =
      Real.log delta⁻¹ + Real.log sigma⁻¹ :=
    Real.log_mul (ne_of_gt hd) (ne_of_gt hs)
  rw [← hmul]
  refine Real.log_le_log (by positivity) ?_
  have hexp : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  linarith only [hexp]

/-- `2σ ≤ e^{2σ}`, the growth that absorbs the linear part of `σΘ`. -/
theorem two_mul_le_exp_two_mul (sigma : ℝ) :
    2 * sigma ≤ Real.exp (2 * sigma) := by
  have h := Real.add_one_le_exp (2 * sigma)
  linarith only [h]

/-- `1 ≤ e^{2σ}`. -/
theorem one_le_exp_two_mul (hsigma : 0 < sigma) :
    (1 : ℝ) ≤ Real.exp (2 * sigma) := by
  have h := Real.add_one_le_exp (2 * sigma)
  linarith only [h, hsigma]

/-- `log σ ≤ e^{2σ}` for every positive `σ`. -/
theorem log_le_exp_two_mul (hsigma : 0 < sigma) :
    Real.log sigma ≤ Real.exp (2 * sigma) := by
  have h1 : Real.log sigma ≤ sigma - 1 := Real.log_le_sub_one_of_pos hsigma
  have h2 := two_mul_le_exp_two_mul sigma
  linarith only [h1, h2, hsigma]

/-- **The logarithm of the print's `Θ`-argument is absorbed by the regularized
logarithm.** The identity `2 log δ⁻¹ + log σ⁻¹ = 2(log δ⁻¹ + log σ⁻¹) + log σ`
splits the left side into a part the regularized logarithm dominates and a part
the exponential factor dominates. -/
theorem max_zero_two_log_inv_add_le (hdelta : 0 < delta) (hsigma : 0 < sigma) :
    max 0 (2 * Real.log delta⁻¹ + Real.log sigma⁻¹) ≤
      3 * (Real.log (Real.exp 1 + delta⁻¹ * sigma⁻¹) * Real.exp (2 * sigma)) := by
  have hL1 : (1 : ℝ) ≤ Real.log (Real.exp 1 + delta⁻¹ * sigma⁻¹) :=
    one_le_log_expOne_add hdelta hsigma
  have hsum := log_inv_add_log_inv_le hdelta hsigma
  have hE1 : (1 : ℝ) ≤ Real.exp (2 * sigma) := one_le_exp_two_mul hsigma
  have hlog : Real.log sigma ≤ Real.exp (2 * sigma) := log_le_exp_two_mul hsigma
  have hinv : Real.log sigma⁻¹ = -Real.log sigma := Real.log_inv sigma
  have hstep : 2 * Real.log delta⁻¹ + Real.log sigma⁻¹ ≤
      2 * Real.log (Real.exp 1 + delta⁻¹ * sigma⁻¹) + Real.exp (2 * sigma) := by
    linarith only [hsum, hlog, hinv]
  have hprod : 2 * Real.log (Real.exp 1 + delta⁻¹ * sigma⁻¹) +
      Real.exp (2 * sigma) ≤
      3 * (Real.log (Real.exp 1 + delta⁻¹ * sigma⁻¹) * Real.exp (2 * sigma)) := by
    nlinarith only [hL1, hE1]
  refine max_le ?_ (le_trans hstep hprod)
  nlinarith only [hL1, hE1]

end Logarithm

/-! ## The constants of the corrected amplitude -/

/-- The logarithmic gauge `G(A) = max(0, log(6 A²))` of the uniform `Γ₂`
amplitude `A` of the envelope family. -/
def moreoverAmpGauge (A : ℝ) : ℝ := max 0 (Real.log (6 * A ^ 2))

theorem moreoverAmpGauge_nonneg (A : ℝ) : 0 ≤ moreoverAmpGauge A := le_max_left _ _

/-- The inner constant `C₁(A) = 3 A (3 + G(A))` of the corrected amplitude. -/
def moreoverAmpInner (A : ℝ) : ℝ := 3 * A * (3 + moreoverAmpGauge A)

theorem one_le_moreoverAmpInner {A : ℝ} (hA : 1 ≤ A) : (1 : ℝ) ≤ moreoverAmpInner A := by
  have hG := moreoverAmpGauge_nonneg A
  rw [moreoverAmpInner]
  nlinarith only [hA, hG]

theorem moreoverAmpInner_pos {A : ℝ} (hA : 1 ≤ A) : 0 < moreoverAmpInner A :=
  lt_of_lt_of_le one_pos (one_le_moreoverAmpInner hA)

/-! ## The constant `Θ` of the summation against the regularized logarithm -/

/-- **The `Θ` of the geometric summation, weighted by the scale, is bounded by
the regularized logarithm times `e^{2σ}`.** With `c = δ²/(4A²)` and `η = 2σ`,
`σ Θ = 3σ + 1 + (3/2) max(0, log(6 A² δ⁻² σ⁻¹))`; the linear part is absorbed by
`e^{2σ}` and the logarithm by `log(e + δ⁻¹σ⁻¹)`. -/
theorem sigma_mul_expTailTheta_le {A delta sigma : ℝ} (hA : 0 < A)
    (hdelta : 0 < delta) (hsigma : 0 < sigma) :
    sigma * expTailTheta (delta ^ 2 / (4 * A ^ 2)) (2 * sigma) ≤
      (7 + 3 / 2 * moreoverAmpGauge A) *
        (Real.log (Real.exp 1 + delta⁻¹ * sigma⁻¹) * Real.exp (2 * sigma)) := by
  have hsne : sigma ≠ 0 := ne_of_gt hsigma
  have hdne : delta ≠ 0 := ne_of_gt hdelta
  have hane : A ≠ 0 := ne_of_gt hA
  have hL1 : (1 : ℝ) ≤ Real.log (Real.exp 1 + delta⁻¹ * sigma⁻¹) :=
    one_le_log_expOne_add hdelta hsigma
  have hE1 : (1 : ℝ) ≤ Real.exp (2 * sigma) := one_le_exp_two_mul hsigma
  have hE2 : 2 * sigma ≤ Real.exp (2 * sigma) := two_mul_le_exp_two_mul sigma
  have hmax0 := max_zero_two_log_inv_add_le hdelta hsigma
  have hG := moreoverAmpGauge_nonneg A
  have harg : (3 : ℝ) / (delta ^ 2 / (4 * A ^ 2) * (2 * sigma)) =
      6 * A ^ 2 * delta⁻¹ ^ 2 * sigma⁻¹ := by
    field_simp
    ring
  have hlogarg : Real.log (6 * A ^ 2 * delta⁻¹ ^ 2 * sigma⁻¹) =
      Real.log (6 * A ^ 2) + (2 * Real.log delta⁻¹ + Real.log sigma⁻¹) := by
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast
    ring
  set L : ℝ := Real.log (Real.exp 1 + delta⁻¹ * sigma⁻¹) with hLdef
  set E : ℝ := Real.exp (2 * sigma) with hEdef
  set M : ℝ := max 0 (Real.log (3 / (delta ^ 2 / (4 * A ^ 2) * (2 * sigma)))) with hMdef
  have hMle : M ≤ moreoverAmpGauge A + 3 * (L * E) := by
    have hsplit : max 0 (Real.log (6 * A ^ 2) +
          (2 * Real.log delta⁻¹ + Real.log sigma⁻¹)) ≤
        max 0 (Real.log (6 * A ^ 2)) +
          max 0 (2 * Real.log delta⁻¹ + Real.log sigma⁻¹) :=
      max_le (add_nonneg (le_max_left _ _) (le_max_left _ _))
        (add_le_add (le_max_right _ _) (le_max_right _ _))
    rw [hMdef, harg, hlogarg, moreoverAmpGauge]
    linarith only [hsplit, hmax0]
  have hexpand : sigma * expTailTheta (delta ^ 2 / (4 * A ^ 2)) (2 * sigma) =
      3 * sigma + 1 + 3 / 2 * M := by
    rw [expTailTheta, ← hMdef]
    field_simp
  have hY1 : (1 : ℝ) ≤ L * E := by nlinarith only [hL1, hE1]
  have hY2 : 2 * sigma ≤ L * E := by nlinarith only [hL1, hE1, hE2]
  have hGY : 3 / 2 * moreoverAmpGauge A ≤ 3 / 2 * moreoverAmpGauge A * (L * E) := by
    nlinarith only [hG, hY1]
  rw [hexpand]
  linarith only [hMle, hY1, hY2, hGY]

/-! ## The corrected amplitude -/

/-- The base of the corrected amplitude,
`C₁(A) δ⁻¹ √(σ⁻¹ log(e + δ⁻¹σ⁻¹))`. -/
def moreoverAmpBase (A delta sigma : ℝ) : ℝ :=
  moreoverAmpInner A * delta⁻¹ *
    Real.sqrt (sigma⁻¹ * Real.log (Real.exp 1 + delta⁻¹ * sigma⁻¹))

theorem moreoverAmpBase_nonneg {A delta sigma : ℝ} (hA : 1 ≤ A) (hdelta : 0 < delta) :
    0 ≤ moreoverAmpBase A delta sigma := by
  rw [moreoverAmpBase]
  exact mul_nonneg (mul_nonneg (moreoverAmpInner_pos hA).le (inv_pos.2 hdelta).le)
    (Real.sqrt_nonneg _)

/-- The corrected amplitude `48 (C₁(A) δ⁻¹ √(σ⁻¹ log(e + δ⁻¹σ⁻¹)))^{1/σ}` of the
`Γ_{2σ}` tail of `log K_σ`. -/
def moreoverAmpBound (A delta sigma : ℝ) : ℝ :=
  48 * moreoverAmpBase A delta sigma ^ sigma⁻¹

/-- **Below the `1/σ` power, the honest scale is dominated by `e^σ` times the
base of the corrected amplitude.** -/
theorem two_mul_sqrt_expTailTheta_le {A delta sigma : ℝ} (hA : 1 ≤ A)
    (hdelta : 0 < delta) (hsigma : 0 < sigma) :
    2 * A * delta⁻¹ *
        Real.sqrt (expTailTheta (delta ^ 2 / (4 * A ^ 2)) (2 * sigma)) ≤
      Real.exp sigma * moreoverAmpBase A delta sigma := by
  have hApos : (0 : ℝ) < A := lt_of_lt_of_le one_pos hA
  have hG := moreoverAmpGauge_nonneg A
  have hsi : (0 : ℝ) < sigma⁻¹ := by positivity
  have hexpsq : Real.exp sigma ^ 2 = Real.exp (2 * sigma) := by
    rw [sq, ← Real.exp_add]
    ring_nf
  have hTheta := sigma_mul_expTailTheta_le (A := A) (delta := delta) (sigma := sigma)
    hApos hdelta hsigma
  set Theta : ℝ := expTailTheta (delta ^ 2 / (4 * A ^ 2)) (2 * sigma) with hThetaDef
  set L : ℝ := Real.log (Real.exp 1 + delta⁻¹ * sigma⁻¹) with hLdef
  have hconst : 4 * A ^ 2 * (7 + 3 / 2 * moreoverAmpGauge A) ≤ moreoverAmpInner A ^ 2 := by
    rw [moreoverAmpInner]
    nlinarith only [hG, sq_nonneg A, hApos]
  have hA2 : (0 : ℝ) ≤ 4 * A ^ 2 := by positivity
  have hkey : 4 * A ^ 2 * (sigma * Theta) ≤
      Real.exp (2 * sigma) * moreoverAmpInner A ^ 2 * L := by
    have hstep : 4 * A ^ 2 * (sigma * Theta) ≤
        4 * A ^ 2 * ((7 + 3 / 2 * moreoverAmpGauge A) * (L * Real.exp (2 * sigma))) :=
      mul_le_mul_of_nonneg_left hTheta hA2
    have hLE : (0 : ℝ) ≤ L * Real.exp (2 * sigma) := by
      have hL1 : (1 : ℝ) ≤ L := one_le_log_expOne_add hdelta hsigma
      have hE1 : (1 : ℝ) ≤ Real.exp (2 * sigma) := one_le_exp_two_mul hsigma
      nlinarith only [hL1, hE1]
    have hstep2 : 4 * A ^ 2 * (7 + 3 / 2 * moreoverAmpGauge A) *
        (L * Real.exp (2 * sigma)) ≤
        moreoverAmpInner A ^ 2 * (L * Real.exp (2 * sigma)) :=
      mul_le_mul_of_nonneg_right hconst hLE
    nlinarith only [hstep, hstep2]
  have hcore : 4 * A ^ 2 * Theta ≤
      (Real.exp sigma * moreoverAmpInner A) ^ 2 * (sigma⁻¹ * L) := by
    have hmul := mul_le_mul_of_nonneg_left hkey hsi.le
    have hleft : sigma⁻¹ * (4 * A ^ 2 * (sigma * Theta)) = 4 * A ^ 2 * Theta := by
      field_simp
    have hright : sigma⁻¹ * (Real.exp (2 * sigma) * moreoverAmpInner A ^ 2 * L) =
        (Real.exp sigma * moreoverAmpInner A) ^ 2 * (sigma⁻¹ * L) := by
      rw [mul_pow, hexpsq]
      ring
    rw [hleft, hright] at hmul
    exact hmul
  have hdi2 : (0 : ℝ) ≤ delta⁻¹ ^ 2 := sq_nonneg _
  have hfinal : (2 * A * delta⁻¹) ^ 2 * Theta ≤
      (Real.exp sigma * moreoverAmpInner A * delta⁻¹) ^ 2 * (sigma⁻¹ * L) := by
    calc (2 * A * delta⁻¹) ^ 2 * Theta = delta⁻¹ ^ 2 * (4 * A ^ 2 * Theta) := by ring
      _ ≤ delta⁻¹ ^ 2 * ((Real.exp sigma * moreoverAmpInner A) ^ 2 * (sigma⁻¹ * L)) :=
          mul_le_mul_of_nonneg_left hcore hdi2
      _ = (Real.exp sigma * moreoverAmpInner A * delta⁻¹) ^ 2 * (sigma⁻¹ * L) := by ring
  have hleft0 : (0 : ℝ) ≤ 2 * A * delta⁻¹ := by positivity
  have hright0 : (0 : ℝ) ≤ Real.exp sigma * moreoverAmpInner A * delta⁻¹ := by
    have := moreoverAmpInner_pos hA
    positivity
  have hlefteq : 2 * A * delta⁻¹ * Real.sqrt Theta =
      Real.sqrt ((2 * A * delta⁻¹) ^ 2 * Theta) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hleft0]
  have hrighteq : Real.exp sigma * moreoverAmpBase A delta sigma =
      Real.sqrt ((Real.exp sigma * moreoverAmpInner A * delta⁻¹) ^ 2 * (sigma⁻¹ * L)) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hright0, moreoverAmpBase, ← hLdef]
    ring
  rw [hlefteq, hrighteq]
  exact Real.sqrt_le_sqrt hfinal

/-- **The `1/σ` power of the base is bounded below by `1/2`, uniformly in
`σ`.** This is what the outer free constant needs in order to absorb the
additive `4` of the honest amplitude. -/
theorem half_le_moreoverAmpBase_rpow {A delta sigma : ℝ} (hA : 1 ≤ A)
    (hdelta : 0 < delta) (hdelta1 : delta < 1) (hsigma : 0 < sigma) :
    (1 : ℝ) / 2 ≤ moreoverAmpBase A delta sigma ^ sigma⁻¹ := by
  have hsi : (0 : ℝ) < sigma⁻¹ := by positivity
  have hL1 : (1 : ℝ) ≤ Real.log (Real.exp 1 + delta⁻¹ * sigma⁻¹) :=
    one_le_log_expOne_add hdelta hsigma
  have hCin : (1 : ℝ) ≤ moreoverAmpInner A := one_le_moreoverAmpInner hA
  have hdinv : (1 : ℝ) ≤ delta⁻¹ := by
    have h1 : delta * delta⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hdelta)
    have h2 : (0 : ℝ) < delta⁻¹ := by positivity
    nlinarith only [h1, h2, hdelta1]
  set L : ℝ := Real.log (Real.exp 1 + delta⁻¹ * sigma⁻¹) with hLdef
  have hsq : Real.sqrt sigma⁻¹ ≤ Real.sqrt (sigma⁻¹ * L) := by
    refine Real.sqrt_le_sqrt ?_
    nlinarith only [hsi, hL1]
  have hs0 : (0 : ℝ) ≤ Real.sqrt (sigma⁻¹ * L) := Real.sqrt_nonneg _
  have hstep1 : Real.sqrt (sigma⁻¹ * L) ≤ delta⁻¹ * Real.sqrt (sigma⁻¹ * L) := by
    nlinarith only [hdinv, hs0]
  have hstep2 : delta⁻¹ * Real.sqrt (sigma⁻¹ * L) ≤
      moreoverAmpInner A * delta⁻¹ * Real.sqrt (sigma⁻¹ * L) := by
    have h0 : (0 : ℝ) ≤ delta⁻¹ * Real.sqrt (sigma⁻¹ * L) := by
      have := (inv_pos.2 hdelta).le
      positivity
    nlinarith only [hCin, h0]
  have hbase : Real.sqrt sigma⁻¹ ≤ moreoverAmpBase A delta sigma := by
    rw [moreoverAmpBase, ← hLdef]
    linarith only [hsq, hstep1, hstep2]
  have hbasepos : 0 < Real.sqrt sigma⁻¹ := Real.sqrt_pos.2 hsi
  have hrpow : Real.sqrt sigma⁻¹ ^ sigma⁻¹ ≤ moreoverAmpBase A delta sigma ^ sigma⁻¹ :=
    Real.rpow_le_rpow (Real.sqrt_nonneg _) hbase hsi.le
  have hlog : Real.log (Real.sqrt sigma⁻¹) = Real.log sigma⁻¹ / 2 :=
    Real.log_sqrt hsi.le
  have hexp : Real.sqrt sigma⁻¹ ^ sigma⁻¹ =
      Real.exp (Real.log sigma⁻¹ / 2 * sigma⁻¹) := by
    rw [Real.rpow_def_of_pos hbasepos, hlog]
  have hge : (1 : ℝ) / 2 ≤ Real.exp (Real.log sigma⁻¹ / 2 * sigma⁻¹) := by
    have h1 := Real.add_one_le_exp (Real.log sigma⁻¹ / 2 * sigma⁻¹)
    have h2 : Real.log sigma ≤ sigma := by
      have h := Real.log_le_sub_one_of_pos hsigma
      linarith only [h]
    have h3 : Real.log sigma⁻¹ = -Real.log sigma := Real.log_inv sigma
    have h4 : sigma * sigma⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hsigma)
    have h6 : -sigma ≤ Real.log sigma⁻¹ := by linarith only [h2, h3]
    have h7 : (0 : ℝ) ≤ (Real.log sigma⁻¹ + sigma) * sigma⁻¹ :=
      mul_nonneg (by linarith only [h6]) hsi.le
    linarith only [h1, h7, h4]
  linarith only [hrpow, hge, hexp]

/-- **The corrected amplitude dominates the honest amplitude of the geometric
summation**, at every `0 < δ < 1` and every `0 < σ`. -/
theorem moreoverLogScaleAmplitude_le_moreoverAmpBound {A delta sigma : ℝ} (hA : 1 ≤ A)
    (hdelta : 0 < delta) (hdelta1 : delta < 1) (hsigma : 0 < sigma) :
    moreoverLogScaleAmplitude A delta sigma ≤ moreoverAmpBound A delta sigma := by
  have hApos : (0 : ℝ) < A := lt_of_lt_of_le one_pos hA
  have hsi : (0 : ℝ) < sigma⁻¹ := by positivity
  have hteq := moreoverTailScale_eq (A := A) (delta := delta) (sigma := sigma)
    hApos hdelta hsigma
  have hhalf := half_le_moreoverAmpBase_rpow hA hdelta hdelta1 hsigma
  have hVW := two_mul_sqrt_expTailTheta_le hA hdelta hsigma
  have hV0 : (0 : ℝ) ≤ 2 * A * delta⁻¹ *
      Real.sqrt (expTailTheta (delta ^ 2 / (4 * A ^ 2)) (2 * sigma)) := by positivity
  have hrp := Real.rpow_le_rpow hV0 hVW hsi.le
  have hsplit : (Real.exp sigma * moreoverAmpBase A delta sigma) ^ sigma⁻¹ =
      Real.exp 1 * moreoverAmpBase A delta sigma ^ sigma⁻¹ := by
    rw [Real.mul_rpow (Real.exp_pos sigma).le (moreoverAmpBase_nonneg hA hdelta),
      Real.rpow_def_of_pos (Real.exp_pos sigma), Real.log_exp,
      mul_inv_cancel₀ (ne_of_gt hsigma)]
  rw [hsplit] at hrp
  set Wp : ℝ := moreoverAmpBase A delta sigma ^ sigma⁻¹ with hWpdef
  have hWp0 : (0 : ℝ) ≤ Wp := by linarith only [hhalf]
  have hlog3nn : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hlog3le : Real.log 3 ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith only [h]
  have hprod : Real.log 3 * Real.exp 1 ≤ 2 * 2.7182818286 :=
    mul_le_mul hlog3le Real.exp_one_lt_d9.le (Real.exp_pos 1).le (by norm_num)
  have hprod2 : 2 * Real.log 3 * Real.exp 1 ≤ 16 := by linarith only [hprod]
  have hc : 2 * Real.log 3 * (Real.exp 1 * Wp) ≤ 16 * Wp := by
    nlinarith only [hprod2, hWp0]
  have hd2 : 2 * Real.log 3 *
      (2 * A * delta⁻¹ *
        Real.sqrt (expTailTheta (delta ^ 2 / (4 * A ^ 2)) (2 * sigma))) ^ sigma⁻¹ ≤
      2 * Real.log 3 * (Real.exp 1 * Wp) :=
    mul_le_mul_of_nonneg_left hrp (by linarith only [hlog3nn])
  rw [moreoverLogScaleAmplitude, hteq, moreoverAmpBound, ← hWpdef]
  linarith only [hc, hd2, hlog3le, hhalf]

/-! ## The three constants of the block, in `d` and `s` -/

/-- **The outer constant `C₀` of the corrected amplitude**: it stands outside
the `1/σ` power, which is what makes the amplitude usable at large `σ`. -/
def moreoverAmpOuterConst : ℝ := 48

/-- **The constant `C₂` inside the regularized logarithm.** -/
def moreoverLogArgConst : ℝ := 1

/-- **The inner constant `C₁` of the corrected amplitude**, in `d` and `s`
only, built from the uniform `Γ₂` amplitude of the envelope family. -/
def moreoverAmpInnerConst (d : ℕ) (s : ℝ) : ℝ :=
  moreoverAmpInner (moreoverEnvelopeConst d s)

/-- The uniform `Γ₂` amplitude of the envelope family is at least `1`. -/
theorem one_le_moreoverEnvelopeConst {d : ℕ} (hCl : 0 ≤ largeCubeLinftyConst d)
    {s : ℝ} (hs : 0 < s) : (1 : ℝ) ≤ moreoverEnvelopeConst d s := by
  have hstc : (0 : ℝ) ≤ streamDerivTailConst := by
    rw [streamDerivTailConst]; norm_num
  have hrpos : (0 : ℝ) < 1 - (3 : ℝ) ^ (-s) := by
    linarith only [rpow_neg_lt_one hs]
  have hU : (0 : ℝ) ≤ moreoverLinftyUniformBound d s := by
    have hg := moreoverLinftyGrowthConst_nonneg hCl
    have h1 : (0 : ℝ) ≤ (matHatNegBridgeConstant d).toReal := ENNReal.toReal_nonneg
    have h2 : (0 : ℝ) ≤ (1 - (3 : ℝ) ^ (-s))⁻¹ := inv_nonneg.2 hrpos.le
    have h3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
    have h4 : (0 : ℝ) ≤ (s * Real.log 3)⁻¹ := inv_nonneg.2 (by positivity)
    have hb : (0 : ℝ) ≤ (matHatNegBridgeConstant d).toReal *
        (1 - (3 : ℝ) ^ (-s))⁻¹ * (d : ℝ) * (s * Real.log 3)⁻¹ := by positivity
    rw [moreoverLinftyUniformBound]
    exact mul_nonneg hg (by linarith only [hb])
  have hcW : (0 : ℝ) ≤ moreoverWindowScale d s := by
    have h2 : (0 : ℝ) ≤ (matHatNegBridgeConstant d).toReal * moreoverDepthWeight s :=
      mul_nonneg ENNReal.toReal_nonneg (moreoverDepthWeight_nonneg hs)
    rw [moreoverWindowScale]; linarith only [h2]
  have hwc : (0 : ℝ) ≤ moreoverWindowConst d := by
    have hD : (0 : ℝ) ≤ (d : ℝ) * Real.sqrt d * streamDerivTailConst := by
      positivity
    have h1 : (0 : ℝ) ≤ centeredCubeAverageConst d := by
      rw [centeredCubeAverageConst]
      linarith only [coarseAverageDiffConst_nonneg d, hD]
    rw [moreoverWindowConst]
    exact mul_nonneg h1 (Real.sqrt_nonneg _)
  rw [moreoverEnvelopeConst]
  linarith only [hU, hstc, mul_nonneg hcW hwc]

/-- **The corrected amplitude of the block dominates the honest amplitude of the
geometric summation**, in the exact shape the printed text carries: the free
constant `C₀` outside the `1/σ` power and the logarithm regularized by `e`. -/
theorem moreoverLogScaleAmplitude_le_moreoverAmpConst {d : ℕ}
    (hCl : 0 ≤ largeCubeLinftyConst d) {s : ℝ} (hs : 0 < s) {delta sigma : ℝ}
    (hdelta : 0 < delta) (hdelta1 : delta < 1) (hsigma : 0 < sigma) :
    moreoverLogScaleAmplitude (moreoverEnvelopeConst d s) delta sigma ≤
      moreoverAmpOuterConst *
        (moreoverAmpInnerConst d s * delta⁻¹ *
            Real.sqrt (sigma⁻¹ *
              Real.log (Real.exp 1 + moreoverLogArgConst * delta⁻¹ * sigma⁻¹))) ^
          sigma⁻¹ := by
  have hA := one_le_moreoverEnvelopeConst hCl hs
  have h := moreoverLogScaleAmplitude_le_moreoverAmpBound hA hdelta hdelta1 hsigma
  rw [moreoverAmpBound, moreoverAmpBase] at h
  rw [moreoverAmpOuterConst, moreoverAmpInnerConst, moreoverLogArgConst, one_mul]
  exact h

end

end Stream
end Estimates
end Section2
end SuperdiffusionCLT
