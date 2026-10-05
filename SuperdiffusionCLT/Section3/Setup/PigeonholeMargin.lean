/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.PigeonholeCounting

/-!
# The exponential counting step of the pigeonhole selection

The paper discharges the counting step of the pigeonhole subargument underlying
[AK, Lemma 3.4] with the exponential estimate `log(1+δ) ≥ δ/2`: from the
second condition of `e.h.restrictions` (`(C log(Cν⁻¹L)/δ) h ≤ L`) the step count
`N = ⌊L/(8h)⌋` satisfies `C log(Cν⁻¹L) < 8Nδ + 8δ`, so `(1+δ)^N` grows at least
like `exp(C log(Cν⁻¹L)/16)`, which beats the polynomial envelope bound
`envelopeScalarProduct ≤ 6 (Cν⁻¹L)²` of `envelopeScalarProduct_le` as soon as
`C` is large.

This file carries out that route.  `log_one_add_ge_half` is the exponential
estimate itself; `one_add_delta_pow_ge_exp` is its power form `(1+δ)^N ≥ exp(Nδ/2)`;
`envelopeScalarProduct_lt_one_add_delta_pow_of_windowRestrictions` runs the
counting step from the window restrictions alone, with the explicit largeness
condition `64 ≤ C` on the constant of `e.h.restrictions` — an explicit
strengthening: the print leaves the largeness of `C` implicit in this passage
(the constant it selects here is `K`, "a large constant to be selected later",
and `C`'s largeness is fixed elsewhere in the paper), while the accounting
below is what forces `C ≥ 64`; and the selection theorem
`exists_pigeonhole_scale_of_windowRestrictions` discharges the printed
pigeonhole scale from the window restrictions under that same largeness
condition, combining the counting step with the two ingredients of
`PigeonholeCounting` (the step count `pigeonholeStepCount` and the
polynomial bound `envelopeScalarProduct_le`).

## The arithmetic, with no hidden factor

Write `S = Cν⁻¹L` (the scale of the printed bound `det bfE_L ≤ (Cν⁻¹L)^{2d}`)
and `X = log S`. The chain is

`envelopeScalarProduct ≤ 6 S² ≤ S³ = exp(3 log S) ≤ exp(CX/16 − 1/2)
≤ exp(CX/16 − δ/2) < exp(Nδ/2) ≤ (1+δ)^N`.

* `6 S² ≤ S³` holds because `S ≥ C ≥ 64 ≥ 6`.
* `3 log S ≤ CX/16 − 1/2`, i.e. `48X + 8 ≤ CX`: `X ≥ log 2 ≥ 1/2`
  (`Real.one_sub_inv_le_log_of_pos` at `2`, with `S ≥ 2`) and `C ≥ 64` give
  `48X + 8 ≤ 64X ≤ CX`. This is the only place the largeness of `C` enters:
  with only `X ≥ 1/2` available, `48X + 8 ≤ CX` forces `C ≥ 64` (equality at
  `X = 1/2` in that single inequality), so `64` is the exact threshold of this
  accounting. The stronger guard `X = log S ≥ log C` (from `S ≥ C`) is in fact
  available, and under it the threshold drops to about `51`; `64` therefore
  carries slack, but hides no dependence.
* `CX/16 − 1/2 ≤ CX/16 − δ/2` uses `δ ≤ 1`, the smallness of the printed
  `δ = c₀c*²`; `CX/16 − δ/2 < Nδ/2` is the step-count bound of
  `log_window_scale_lt`, i.e. `CX < 8Nδ + 8δ`, which is what the second
  condition of `e.h.restrictions` gives through the remainder estimate for
  `N = ⌊L/(8h)⌋` (`pigeonholeStepCount_lt_succ_mul`).
* `(1+δ)^N ≥ exp(Nδ/2)` is `one_add_delta_pow_ge_exp`, i.e.
  `log(1+δ) ≥ δ/2` of `log_one_add_ge_half`.

So the counting step holds under the two conditions of `e.h.restrictions`
(kept unchanged, in `WindowRestrictions`), the standing small-scale hypotheses
`0 < nu ≤ 1`, `1 ≤ L`, the identification `cutoffEnvelopeConst d ≤ C` of the
constant of the envelope with the printed constant of the restrictions, and the
largeness condition `64 ≤ C` — the print's largeness of `C` is implicit in this
passage, and the accounting above is what forces `C ≥ 64` — with no margin
hypothesis. No restriction of `Parameters.lean` is altered.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Setup

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

/-! ## The exponential estimate `log(1+δ) ≥ δ/2` -/

/-- **`log(1+δ) ≥ δ/2` for `δ ∈ [0,1]`**, the exponential estimate
("using `log(1+δ) ≥ δ/2`"). The route is the two-sided bound of
`Real.one_sub_inv_le_log_of_pos`, `1 − 1/x ≤ log x`, at `x = 1+δ`: it gives
`δ/(1+δ) ≤ log(1+δ)`, and `δ/(1+δ) ≥ δ/2` because `δ ≤ 1`. -/
theorem log_one_add_ge_half {delta : ℝ} (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 1) :
    delta / 2 ≤ Real.log (1 + delta) := by
  have hbase : 0 < 1 + delta := by linarith only [hdelta]
  have hform : 1 - (1 + delta)⁻¹ = delta / (1 + delta) := by
    field_simp
    ring
  have hstep : delta / (1 + delta) ≤ Real.log (1 + delta) := by
    have h1 := Real.one_sub_inv_le_log_of_pos hbase
    linarith only [h1, hform]
  have hhalf : delta / 2 ≤ delta / (1 + delta) :=
    div_le_div_of_nonneg_left hdelta hbase (by linarith only [hdelta1])
  exact le_trans hhalf hstep

/-- **The power form of the exponential estimate**: `(1+δ)^N ≥ exp(N·δ/2)` for
`δ ∈ [0,1]`, the form in which `log_one_add_ge_half` enters the counting step
of the pigeonhole selection. -/
theorem one_add_delta_pow_ge_exp {delta : ℝ} (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (N : ℕ) : Real.exp ((N : ℝ) * delta / 2) ≤ (1 + delta) ^ N := by
  have hbase : 0 < 1 + delta := by linarith only [hdelta]
  have hlog := log_one_add_ge_half hdelta hdelta1
  have hcast : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  have hmul : (N : ℝ) * delta / 2 ≤ (N : ℝ) * Real.log (1 + delta) := by
    calc (N : ℝ) * delta / 2 = (N : ℝ) * (delta / 2) := by ring
      _ ≤ (N : ℝ) * Real.log (1 + delta) := mul_le_mul_of_nonneg_left hlog hcast
  have hexp : Real.exp ((N : ℝ) * Real.log (1 + delta)) = (1 + delta) ^ N := by
    rw [Real.exp_nat_mul, Real.exp_log hbase]
  exact (Real.exp_le_exp_of_le hmul).trans hexp.le

/-! ## The step-count bound from the second window restriction -/

/-- **The step-count bound**: under the window restrictions
`e.h.restrictions` the second condition `(C log(Cν⁻¹L)/δ) h ≤ L`
gives `C log(Cν⁻¹L) < 8Nδ + 8δ` for the step count `N = pigeonholeStepCount L h
= ⌊L/(8h)⌋`: the restriction gives `C log(Cν⁻¹L) ≤ (L/h)·δ`, while the
remainder bound `pigeonholeStepCount_lt_succ_mul` gives `L/h < 8(N+1)`, so
`C log(Cν⁻¹L) < 8δ(N+1) = 8Nδ + 8δ`. This is the step-count input of the
exponential counting comparison
`envelopeScalarProduct_lt_one_add_delta_pow_of_windowRestrictions`; it is the
only window-restriction input of the exponential counting step. -/
private theorem log_window_scale_lt {C K nu delta : ℝ} {L h : ℕ}
    (hdelta : 0 < delta) (hK : 0 < K) (hlog1 : 1 ≤ Real.log (nu⁻¹ * L))
    (hres : WindowRestrictions C K nu delta L h) :
    C * Real.log (C * (nu⁻¹ * L)) < 8 * ((pigeonholeStepCount L h : ℝ) * delta) + 8 * delta := by
  -- `h ≥ 10` from the first restriction, since `K log²(ν⁻¹L) > 0`.
  have hKlog : 0 < K * Real.log (nu⁻¹ * L) ^ 2 := by
    have hlogpos : 0 < Real.log (nu⁻¹ * L) := lt_of_lt_of_le zero_lt_one hlog1
    exact mul_pos hK (pow_pos hlogpos 2)
  have h10 : 10 ≤ h := by
    have hceil : 0 < ⌈K * Real.log (nu⁻¹ * L) ^ 2⌉₊ := Nat.ceil_pos.2 hKlog
    have := hres.ceil_le
    omega
  have hpos : 0 < (h : ℝ) := by
    have h1 : (10 : ℝ) ≤ (h : ℝ) := by exact_mod_cast h10
    linarith only [h1]
  -- The window restriction in the form `C log(Cν⁻¹L) · h ≤ L · δ`.
  have hXh : C * Real.log (C * (nu⁻¹ * L)) * (h : ℝ) ≤ (L : ℝ) * delta := by
    have h2 : C * Real.log (C * (nu⁻¹ * L)) / delta * (h : ℝ) * delta ≤
        (L : ℝ) * delta := mul_le_mul_of_nonneg_right hres.window_le hdelta.le
    have h3 : C * Real.log (C * (nu⁻¹ * L)) / delta * (h : ℝ) * delta
        = C * Real.log (C * (nu⁻¹ * L)) * (h : ℝ) := by
      rw [div_mul_eq_mul_div, mul_assoc, div_mul_cancel₀ _ hdelta.ne']
    linarith only [h2, h3]
  -- `L/h < 8(N+1)`, so `C log(Cν⁻¹L) < 8(Nδ + δ)`.
  have hstep : (L : ℝ) < (8 * ((pigeonholeStepCount L h : ℝ) + 1)) * (h : ℝ) := by
    have hnat := pigeonholeStepCount_lt_succ_mul L h (by omega)
    have hcast : ((8 * h * (pigeonholeStepCount L h + 1) : ℕ) : ℝ)
        = (8 * ((pigeonholeStepCount L h : ℝ) + 1)) * (h : ℝ) := by
      push_cast; ring
    have hcast' : ((L : ℕ) : ℝ) <
        ((8 * h * (pigeonholeStepCount L h + 1) : ℕ) : ℝ) := by
      exact_mod_cast hnat
    linarith only [hcast', hcast]
  have hLdiv : (L : ℝ) / (h : ℝ) < 8 * ((pigeonholeStepCount L h : ℝ) + 1) :=
    (div_lt_iff₀ hpos).2 hstep
  calc C * Real.log (C * (nu⁻¹ * L)) ≤ (L : ℝ) * delta / (h : ℝ) :=
        (le_div_iff₀ hpos).2 hXh
    _ = (L : ℝ) / (h : ℝ) * delta := by ring
    _ < 8 * ((pigeonholeStepCount L h : ℝ) + 1) * delta :=
        mul_lt_mul_of_pos_right hLdiv hdelta
    _ = 8 * ((pigeonholeStepCount L h : ℝ) * delta) + 8 * delta := by ring

/-! ## The exponential counting comparison -/

/-- **The exponential form of the counting step**: under the
window restrictions `e.h.restrictions` the polynomial
envelope bound `envelopeScalarProduct ≤ 6 (Cν⁻¹L)²` of
`envelopeScalarProduct_le` is below the exponential scale `(1+δ)^N` for the
step count `N = pigeonholeStepCount L h = ⌊L/(8h)⌋`, using the exponential
estimate `log(1+δ) ≥ δ/2` in the power form
`one_add_delta_pow_ge_exp`. No margin hypothesis is used.

The largeness condition on `C` is `64 ≤ C` (with `C` the constant of
`e.h.restrictions`, identified with the envelope constant through
`cutoffEnvelopeConst d ≤ C`) — an explicit strengthening: the print leaves the
largeness of `C` implicit in this passage, and the accounting below is what
forces `C ≥ 64`; the accounting is `48 log(Cν⁻¹L) + 8 ≤ C
log(Cν⁻¹L)`, which holds because `log(Cν⁻¹L) ≥ log 2 ≥ 1/2` and `C ≥ 64`. The
smallness `δ ≤ 1` of the printed `δ = c₀c*²` is used once, in
`one_add_delta_pow_ge_exp`. -/
theorem envelopeScalarProduct_lt_one_add_delta_pow_of_windowRestrictions {d : ℕ}
    {C K nu delta : ℝ} {L h : ℕ}
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hL : 1 ≤ L) (hdelta : 0 < delta)
    (hdelta1 : delta ≤ 1)
    (hK : 0 < K) (hlog1 : 1 ≤ Real.log (nu⁻¹ * L))
    (hres : WindowRestrictions C K nu delta L h)
    (hC : cutoffEnvelopeConst d ≤ C) (hClarge : 64 ≤ C) :
    envelopeScalarProduct d nu L < (1 + delta) ^ pigeonholeStepCount L h := by
  have hkey := log_window_scale_lt hdelta hK hlog1 hres
  -- The scale `S = Cν⁻¹L` of the printed bound and its logarithm `X`.
  set S : ℝ := C * (nu⁻¹ * (L : ℝ)) with hSdef
  set X : ℝ := Real.log S with hXdef
  set N : ℝ := (pigeonholeStepCount L h : ℝ) with hNdef
  -- `S ≥ 64 ≥ 6` and `X = log S ≥ log 2 ≥ 1/2`.
  have hC1 : (1 : ℝ) ≤ C := le_trans (one_le_cutoffEnvelopeConst d) hC
  have hnuinv1 : (1 : ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
  have hS0 : 0 < S := by
    rw [hSdef]
    exact mul_pos (lt_of_lt_of_le zero_lt_one hC1)
      (mul_pos (inv_pos.2 hnu) (Nat.cast_pos.2 hL))
  have hS64 : 64 ≤ S := by
    have hterm : (1 : ℝ) ≤ nu⁻¹ * (L : ℝ) := by
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ nu⁻¹ * 1 := mul_le_mul_of_nonneg_right hnuinv1 zero_le_one
        _ ≤ nu⁻¹ * (L : ℝ) :=
            mul_le_mul_of_nonneg_left (Nat.one_le_cast.2 hL) (inv_nonneg.2 hnu.le)
    rw [hSdef]
    calc (64 : ℝ) ≤ C := hClarge
      _ = C * 1 := (mul_one C).symm
      _ ≤ C * (nu⁻¹ * (L : ℝ)) :=
          mul_le_mul_of_nonneg_left hterm (le_trans zero_le_one hC1)
  have h2S : (2 : ℝ) ≤ S := le_trans (by norm_num : (2 : ℝ) ≤ 64) hS64
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h0 : (0 : ℝ) < 2 := by norm_num
    have h := Real.one_sub_inv_le_log_of_pos h0
    have h1 : (1 : ℝ) - (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
    linarith only [h, h1]
  have hXge : Real.log 2 ≤ X := by
    rw [hXdef]
    exact (Real.log_le_log_iff (by norm_num : (0 : ℝ) < 2) hS0).2 h2S
  have hXhalf : (1 : ℝ) / 2 ≤ X := le_trans hlog2 hXge
  have hX0 : 0 ≤ X := le_trans (by norm_num : (0 : ℝ) ≤ 1 / 2) hXhalf
  -- The largeness accounting `48X + 8 ≤ CX`.
  have h48 : (48 : ℝ) * X + 8 ≤ 64 * X := by
    calc (48 : ℝ) * X + 8 = 48 * X + 16 * (1 / 2) := by ring
      _ ≤ 48 * X + 16 * X := by
          have hstep : 16 * (1 / 2) ≤ 16 * X :=
            mul_le_mul_of_nonneg_left hXhalf (by norm_num : (0 : ℝ) ≤ 16)
          linarith only [hstep]
      _ = 64 * X := by ring
  have hCX : (64 : ℝ) * X ≤ C * X := mul_le_mul_of_nonneg_right hClarge hX0
  have hgoal : 3 * X ≤ C * X / 16 - 1 / 2 := by
    have hnum : 3 * X + 1 / 2 = (48 * X + 8) / 16 := by ring
    have hden : (48 * X + 8) / 16 ≤ C * X / 16 :=
      div_le_div_of_nonneg_right (le_trans h48 hCX) (by norm_num : (0 : ℝ) ≤ 16)
    calc 3 * X = 3 * X + 1 / 2 - 1 / 2 := by ring
      _ = (48 * X + 8) / 16 - 1 / 2 := by rw [hnum]
      _ ≤ C * X / 16 - 1 / 2 := sub_le_sub_right hden (1 / 2)
  -- The polynomial envelope bound, in terms of `S`.
  have henv : envelopeScalarProduct d nu L ≤ 6 * S ^ 2 := by
    have h1 := envelopeScalarProduct_le (d := d) hnu hnu1 L hL
    have hA1 : 0 ≤ cutoffEnvelopeConst d * nu⁻¹ * (L : ℝ) :=
      mul_nonneg (mul_nonneg (le_of_lt (cutoffEnvelopeConst_pos d))
        (inv_nonneg.2 hnu.le)) (Nat.cast_nonneg _)
    have hcu : cutoffEnvelopeConst d * nu⁻¹ * (L : ℝ) ≤ C * (nu⁻¹ * (L : ℝ)) := by
      calc cutoffEnvelopeConst d * nu⁻¹ * (L : ℝ) ≤
            (C * nu⁻¹) * (L : ℝ) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hC (inv_nonneg.2 hnu.le))
              (Nat.cast_nonneg _)
        _ = C * (nu⁻¹ * (L : ℝ)) := by ring
    have hmono : (cutoffEnvelopeConst d * nu⁻¹ * (L : ℝ)) ^ 2 ≤ S ^ 2 :=
      pow_le_pow_left₀ hA1 hcu 2
    exact le_trans h1 (mul_le_mul_of_nonneg_left hmono (by norm_num : (0 : ℝ) ≤ 6))
  have hSq : 6 * S ^ 2 ≤ S ^ 3 := by
    calc 6 * S ^ 2 ≤ S * S ^ 2 :=
          mul_le_mul_of_nonneg_right (le_trans (by norm_num : (6 : ℝ) ≤ 64) hS64)
            (pow_nonneg hS0.le 2)
      _ = S ^ 3 := by ring
  have hS3exp : Real.exp (3 * X) = S ^ 3 := by
    have hcast : (3 : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
    calc Real.exp (3 * X) = Real.exp (((3 : ℕ) : ℝ) * X) := by rw [hcast]
      _ = Real.exp (((3 : ℕ) : ℝ) * Real.log S) := by rw [hXdef]
      _ = Real.exp (Real.log S) ^ 3 := Real.exp_nat_mul (Real.log S) 3
      _ = S ^ 3 := by rw [Real.exp_log hS0]
  -- The step count: `CX/16 − δ/2 < Nδ/2`, from `CX < 8Nδ + 8δ`.
  have hB : C * X / 16 - delta / 2 < N * delta / 2 := by
    have h1 : C * X / 16 < (8 * (N * delta) + 8 * delta) / 16 :=
      div_lt_div_of_pos_right hkey (by norm_num : (0 : ℝ) < 16)
    have h2 : (8 * (N * delta) + 8 * delta) / 16 = N * delta / 2 + delta / 2 := by
      ring
    calc C * X / 16 - delta / 2 < N * delta / 2 + delta / 2 - delta / 2 :=
          by linarith only [h1, h2]
      _ = N * delta / 2 := by ring
  calc envelopeScalarProduct d nu L ≤ 6 * S ^ 2 := henv
    _ ≤ S ^ 3 := hSq
    _ = Real.exp (3 * X) := hS3exp.symm
    _ ≤ Real.exp (C * X / 16 - 1 / 2) := Real.exp_le_exp_of_le hgoal
    _ ≤ Real.exp (C * X / 16 - delta / 2) :=
        Real.exp_le_exp_of_le (by
          have h := div_le_div_of_nonneg_right hdelta1 (by norm_num : (0 : ℝ) ≤ 2)
          linarith only [h])
    _ < Real.exp (N * delta / 2) := Real.exp_strictMono hB
    _ ≤ (1 + delta) ^ pigeonholeStepCount L h :=
        one_add_delta_pow_ge_exp hdelta.le hdelta1 (pigeonholeStepCount L h)

/-! ## The pigeonhole selection from the window restrictions -/

section Selection

variable {d : ℕ}

variable [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ)
  {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
  (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)

include hnu hPrefix hJ2 hJ3 hJ4

/-- **`p.sstar.lower.bound#pigeonhole-scale`, discharged from
the window restrictions of `e.h.restrictions` with the
printed exponential estimate** `log(1+δ) ≥ δ/2`: the counting comparison
`envelopeScalarProduct_lt_one_add_delta_pow_of_windowRestrictions` produces the
hypothesis of `exists_pigeonhole_scale` directly, so the scale
`m ∈ ℕ ∩ [L/4, L/2]` of the lattice `⌊L/4⌋ + 2hℕ` with `m ≥ ⌊L/4⌋+2h` exists
under the two conditions of `e.h.restrictions` alone, with the largeness
condition `64 ≤ C` — the print's largeness of `C` is implicit in this passage,
and the accounting of the counting step is what forces `C ≥ 64`. -/
theorem exists_pigeonhole_scale_of_windowRestrictions
    {C K delta : ℝ} {h : ℕ}
    (hnu1 : nu ≤ 1) (hL : 1 ≤ L) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hK : 0 < K) (hlog1 : 1 ≤ Real.log (nu⁻¹ * L))
    (hres : WindowRestrictions C K nu delta L h)
    (hC : cutoffEnvelopeConst d ≤ C) (hClarge : 64 ≤ C) :
    ∃ m : ℕ, L / 4 + 2 * h ≤ m ∧ m ≤ L / 2 ∧ 2 * h ≤ m ∧
      (∃ j : ℕ, m = L / 4 + 2 * h * (j + 1)) ∧
      sigmaBarSeq nu L P (m - 2 * h) ≤ (1 + delta) * sigmaBarSeq nu L P m ∧
        sigmaBarStarInvSeq nu L P (m - 2 * h) ≤
          (1 + delta) * sigmaBarStarInvSeq nu L P m := by
  have hpow := envelopeScalarProduct_lt_one_add_delta_pow_of_windowRestrictions
    (d := d) hnu hnu1 hL hdelta hdelta1 hK hlog1 hres hC hClarge
  have hN := pigeonholeStepCount_half_le L h
  exact exists_pigeonhole_scale hnu L hPrefix hJ2 hJ3 hJ4 h
    (pigeonholeStepCount L h) hN hdelta.le hpow

end Selection

end

end SuperdiffusionCLT.Section3.Setup