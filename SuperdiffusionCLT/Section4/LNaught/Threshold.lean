/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Frozen.Section4.LNaught
public import SuperdiffusionCLT.Section4.LNaught.Monotone
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The defining threshold property of `L₀`

display `e.Lnaught.def`,
defines `L₀(M,α,c⋆,ν)` (Lean `SuperdiffusionCLT.Frozen.Section4.lNaught`)
and asserts that "the universal constant `C` is chosen to be so large that"

```
L ≥ L₀ ⟹ L^{1-α} ≥ M c⋆^{-3} ν^{-4} log^{12} L
      and L^{1-α}/log(3+L) ≥ (M+1+K) c⋆^{-3}.
```

This file proves that defining property (`lNaught_threshold`), together with
the downstream absorption forms actually used in Section 4
(`lNaught_absorbs`) and a lower bound on `L₀`
itself (`lNaught_ge`).

The proof is elementary real analysis: `log` grows slower than any positive
power, so once `C` is chosen large enough the displayed implications hold.
The technical engine is `lNaught_crossing_core`: once a "base point" `t0`
clears both a size threshold (`hpeak`) and the target inequality itself
(`hbase`), the same inequality persists for every larger `t`, because
`log^p(t)/t^a` is eventually decreasing. The two thresholds `hpeak`/`hbase`
are verified once, at one explicit numeral `C = lNaughtThresholdC0`; the
general statement for every `C ≥ lNaughtThresholdC0` then follows from the
monotonicity `lNaught_mono_const` (`Monotone.lean`).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.LNaught

open Real

/-! ## The elementary crossing lemma -/

/-- If `Aconst * (log t0)^p ≤ t0 ^ a` at a base point `t0` past the "peak"
`log t0 ≥ p / a`, the same inequality holds at every `t ≥ t0`: past the peak,
`(log t)^p / t^a` is nonincreasing. -/
private lemma lNaught_crossing_core {a Aconst t0 t : ℝ} {p : ℕ}
    (ha : 0 < a) (hA : 0 < Aconst) (ht0 : 1 ≤ t0) (hp : 1 ≤ p)
    (hpeak : (p : ℝ) ≤ a * Real.log t0)
    (hbase : Aconst * Real.log t0 ^ p ≤ t0 ^ a)
    (ht0t : t0 ≤ t) :
    Aconst * Real.log t ^ p ≤ t ^ a := by
  have ht0pos : 0 < t0 := lt_of_lt_of_le one_pos ht0
  have htpos : 0 < t := lt_of_lt_of_le ht0pos ht0t
  set v0 := Real.log t0 with hv0def
  set v := Real.log t with hvdef
  have hv0nonneg : 0 ≤ v0 := Real.log_nonneg ht0
  have hvv0 : v0 ≤ v := Real.log_le_log ht0pos ht0t
  have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hav0 : (1 : ℝ) ≤ a * v0 := le_trans hpR hpeak
  have hv0pos : 0 < v0 := by
    by_contra hcon
    push Not at hcon
    have hle : a * v0 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha.le hcon
    linarith only [hav0, hle]
  have hvpos : 0 < v := lt_of_lt_of_le hv0pos hvv0
  have hpPos : (0 : ℝ) < (p : ℝ) := lt_of_lt_of_le one_pos hpR
  have hcoeff : (1 : ℝ) / v0 ≤ a / (p : ℝ) := by
    rw [div_le_div_iff₀ hv0pos hpPos, one_mul]
    linarith only [hpeak]
  have hvv0nonneg : 0 ≤ v - v0 := by linarith only [hvv0]
  have hstep : (v - v0) / v0 ≤ a * (v - v0) / (p : ℝ) := by
    have h1 : (v - v0) * (1 / v0) ≤ (v - v0) * (a / (p : ℝ)) :=
      mul_le_mul_of_nonneg_left hcoeff hvv0nonneg
    calc (v - v0) / v0 = (v - v0) * (1 / v0) := by ring
      _ ≤ (v - v0) * (a / (p : ℝ)) := h1
      _ = a * (v - v0) / (p : ℝ) := by ring
  have hlog : Real.log (v / v0) ≤ v / v0 - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hvpos hv0pos)
  have heq : v / v0 - 1 = (v - v0) / v0 := by
    rw [div_sub_one hv0pos.ne']
  have hchain : Real.log (v / v0) ≤ a * (v - v0) / (p : ℝ) := by
    rw [heq] at hlog
    exact le_trans hlog hstep
  have hratio : v / v0 ≤ Real.exp (a * (v - v0) / (p : ℝ)) := by
    calc v / v0 = Real.exp (Real.log (v / v0)) := (Real.exp_log (div_pos hvpos hv0pos)).symm
      _ ≤ Real.exp (a * (v - v0) / (p : ℝ)) := Real.exp_le_exp.mpr hchain
  have hratiop : (v / v0) ^ p ≤ Real.exp (a * (v - v0) / (p : ℝ)) ^ p :=
    pow_le_pow_left₀ (le_of_lt (div_pos hvpos hv0pos)) hratio p
  have hexpp : Real.exp (a * (v - v0) / (p : ℝ)) ^ p = Real.exp (a * (v - v0)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  rw [hexpp, div_pow] at hratiop
  have hexpsub : Real.exp (a * (v - v0)) = Real.exp (a * v) / Real.exp (a * v0) := by
    rw [mul_sub, Real.exp_sub]
  rw [hexpsub] at hratiop
  have hv0ppos : 0 < v0 ^ p := pow_pos hv0pos p
  have hexpv0pos : 0 < Real.exp (a * v0) := Real.exp_pos _
  have hcross : v ^ p * Real.exp (a * v0) ≤ v0 ^ p * Real.exp (a * v) := by
    rw [div_le_div_iff₀ hv0ppos hexpv0pos] at hratiop
    linarith only [hratiop]
  have ht0arpow : t0 ^ a = Real.exp (a * v0) := by
    rw [Real.rpow_def_of_pos ht0pos, mul_comm]
  have htarpow : t ^ a = Real.exp (a * v) := by
    rw [Real.rpow_def_of_pos htpos, mul_comm]
  rw [ht0arpow] at hbase
  rw [htarpow]
  have key : Aconst * v ^ p * Real.exp (a * v0) ≤ Real.exp (a * v) * Real.exp (a * v0) := by
    have h1 : Aconst * v ^ p * Real.exp (a * v0) ≤ Aconst * (v0 ^ p * Real.exp (a * v)) := by
      have h1' := mul_le_mul_of_nonneg_left hcross hA.le
      calc Aconst * v ^ p * Real.exp (a * v0)
          = Aconst * (v ^ p * Real.exp (a * v0)) := by ring
        _ ≤ Aconst * (v0 ^ p * Real.exp (a * v)) := h1'
    have h2 : Aconst * (v0 ^ p * Real.exp (a * v)) ≤ Real.exp (a * v) * Real.exp (a * v0) := by
      have h2' := mul_le_mul_of_nonneg_right hbase (Real.exp_pos (a * v)).le
      calc Aconst * (v0 ^ p * Real.exp (a * v))
          = (Aconst * v0 ^ p) * Real.exp (a * v) := by ring
        _ ≤ Real.exp (a * v0) * Real.exp (a * v) := h2'
        _ = Real.exp (a * v) * Real.exp (a * v0) := by ring
    exact le_trans h1 h2
  exact (mul_le_mul_iff_of_pos_right hexpv0pos).mp key

/-! ## The exact identity `L₀ ^ (1 - α) = ` the inner (pre-outer-power) content -/

/-- `lNaught`'s own outer `^(1/(1-α))` and this identity's `^(1-α)` cancel: the
`(1-α)`-power of `L₀(C,M,α,c⋆,ν,K)` is exactly the bracketed content of
`e.Lnaught.def` before the outer power is taken. -/
lemma lNaught_rpow_eq_inner {C M alpha cStar nu K : ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hK : 0 ≤ K) (hcStar : 0 < cStar) (hnu : 0 < nu)
    (halpha : alpha < 1) :
    (SuperdiffusionCLT.Frozen.Section4.lNaught C M alpha cStar nu K) ^ (1 - alpha) =
      lNaughtInner C M alpha cStar nu K := by
  have hinner_nonneg : 0 ≤ lNaughtInner C M alpha cStar nu K :=
    inner_nonneg hC hM hK hcStar hnu halpha
  have hane : (1 - alpha) ≠ 0 := (sub_pos.mpr halpha).ne'
  show ((lNaughtInner C M alpha cStar nu K) ^ ((1 : ℝ) / (1 - alpha))) ^ (1 - alpha) =
      lNaughtInner C M alpha cStar nu K
  rw [← Real.rpow_mul hinner_nonneg, div_mul_cancel₀ 1 hane, Real.rpow_one]

/-! ## The witness constant -/

/-- The witness for `C₀` in `lNaught_threshold`. `2 ^ 240` is far more than the
elementary estimates below need; it is chosen as a clean power of `2` so every
numeral check below reduces to comparisons against `Real.log 2`, for which
`Real.log_two_gt_d9` / `Real.log_two_lt_d9` give rational bounds. -/
private def lNaughtThresholdC0 : ℝ := (2 : ℝ) ^ (240 : ℕ)

private lemma lNaughtThresholdC0_ge1 : (1 : ℝ) ≤ lNaughtThresholdC0 := by
  unfold lNaughtThresholdC0
  calc (1 : ℝ) = 1 ^ (240 : ℕ) := by norm_num
    _ ≤ (2 : ℝ) ^ (240 : ℕ) := pow_le_pow_left₀ (by norm_num) (by norm_num) 240

/-! ## Elementary base-positivity helpers -/

private lemma lNaught_cStar_neg3_ge {cStar : ℝ} (hx : 0 < cStar) (hx2 : cStar ≤ 2) :
    (1 : ℝ) / 8 ≤ cStar ^ (-(3 : ℝ)) := by
  have h := Real.rpow_le_rpow_of_nonpos hx hx2 (by norm_num : (-(3 : ℝ)) ≤ 0)
  have h2 : (2 : ℝ) ^ (-(3 : ℝ)) = 1 / 8 := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    have h3 : (3 : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
    rw [h3, Real.rpow_natCast]
    norm_num
  rw [h2] at h
  exact h

/-! ## The `L₀(2^240, M, α, c⋆, ν, K)` numeral checks -/

/-- Both the "past the peak" threshold and the target inequality itself, at
`L = L₀(2^240, M, α, c⋆, ν, K)`: the base case `lNaught_crossing_core` needs
for the `p = 12`, `Aconst = M c⋆^{-3} ν^{-4}` instance of the displayed
threshold property. Everything downstream of `L₀`'s own numeral (`2^240`) is
elementary: `log X ≥ log 2 > 0` for the argument `X` of the print's inner
`log`, and every other factor is squeezed between its extreme values over the
standing ranges `M ≥ 1`, `K ≥ 0`, `c⋆ ∈ (0,2]`, `ν ∈ (0,1]`, `α ∈ [0,1)`. -/
private lemma lNaught_c0_peak_base12 {M alpha cStar nu K : ℝ}
    (hM : 1 ≤ M) (hK : 0 ≤ K) (hcStar : 0 < cStar) (hcStar2 : cStar ≤ 2)
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1) :
    (1 : ℝ) ≤ SuperdiffusionCLT.Frozen.Section4.lNaught
        lNaughtThresholdC0 M alpha cStar nu K ∧
      (12 : ℝ) ≤ (1 - alpha) *
        Real.log (SuperdiffusionCLT.Frozen.Section4.lNaught
          lNaughtThresholdC0 M alpha cStar nu K) ∧
      (M * cStar ^ (-(3 : ℝ)) * nu ^ (-(4 : ℝ))) *
          Real.log (SuperdiffusionCLT.Frozen.Section4.lNaught
            lNaughtThresholdC0 M alpha cStar nu K) ^ (12 : ℕ) ≤
        (SuperdiffusionCLT.Frozen.Section4.lNaught
          lNaughtThresholdC0 M alpha cStar nu K) ^ (1 - alpha) ∧
      (2 * ((M + 1 + K) * cStar ^ (-(3 : ℝ)))) *
          Real.log (SuperdiffusionCLT.Frozen.Section4.lNaught
            lNaughtThresholdC0 M alpha cStar nu K) ^ (1 : ℕ) ≤
        (SuperdiffusionCLT.Frozen.Section4.lNaught
          lNaughtThresholdC0 M alpha cStar nu K) ^ (1 - alpha) := by
  set a := 1 - alpha with hadef
  have hapos : 0 < a := by rw [hadef]; linarith only [halpha1]
  have hale1 : a ≤ 1 := by rw [hadef]; linarith only [halpha0]
  have hcStar3 : (1 : ℝ) / 8 ≤ cStar ^ (-(3 : ℝ)) := lNaught_cStar_neg3_ge hcStar hcStar2
  have hcStar3pos : 0 < cStar ^ (-(3 : ℝ)) := Real.rpow_pos_of_pos hcStar _
  have hMK2 : (2 : ℝ) ≤ M + 1 + K := by linarith only [hM, hK]
  have hnua_pos : 0 < nu * a := mul_pos hnu hapos
  have hnua_le1 : nu * a ≤ 1 := (mul_le_mul hnu1 hale1 hapos.le zero_le_one).trans_eq (one_mul 1)
  set F := (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * a) with hFdef
  set X := 2 + F with hXdef
  have hFnonneg : 0 ≤ F := by
    apply div_nonneg
    · exact mul_nonneg (by linarith only [hMK2]) hcStar3pos.le
    · exact hnua_pos.le
  have hFleX : F ≤ X := by rw [hXdef]; linarith only [hFnonneg]
  have hMK2nonneg : (0 : ℝ) ≤ M + 1 + K := by linarith only [hMK2]
  have hMK2strict : 0 < M + 1 + K := by linarith only [hMK2]
  have hprod_ge_quarter : (1 : ℝ) / 4 ≤ (M + 1 + K) * cStar ^ (-(3 : ℝ)) := by
    have h : (2 : ℝ) * (1 / 8) ≤ (M + 1 + K) * cStar ^ (-(3 : ℝ)) :=
      mul_le_mul hMK2 hcStar3 (by norm_num) hMK2nonneg
    have heq : (2 : ℝ) * (1 / 8) = 1 / 4 := by norm_num
    linarith only [h, heq]
  have hane' : a ≠ 0 := hapos.ne'
  have hXa : (1 : ℝ) / (4 * a) ≤ F := by
    rw [hFdef, le_div_iff₀ hnua_pos]
    have heq : (1 / (4 * a)) * (nu * a) = nu / 4 := by field_simp
    rw [heq]
    have h1 : nu / 4 ≤ (1 : ℝ) / 4 := by linarith only [hnu1]
    linarith only [h1, hprod_ge_quarter]
  have hXnu : (1 : ℝ) / (4 * nu) ≤ F := by
    rw [hFdef, le_div_iff₀ hnua_pos]
    have heq : (1 / (4 * nu)) * (nu * a) = a / 4 := by field_simp
    rw [heq]
    have h1 : a / 4 ≤ (1 : ℝ) / 4 := by linarith only [hale1]
    linarith only [h1, hprod_ge_quarter]
  have hXcStar : (2 : ℝ) * cStar ^ (-(3 : ℝ)) ≤ F := by
    rw [hFdef, le_div_iff₀ hnua_pos]
    have h1 : (2 : ℝ) * cStar ^ (-(3 : ℝ)) * (nu * a) ≤ (2 : ℝ) * cStar ^ (-(3 : ℝ)) * 1 :=
      mul_le_mul_of_nonneg_left hnua_le1 (by positivity)
    have h2 : (2 : ℝ) * cStar ^ (-(3 : ℝ)) * 1 = (2 : ℝ) * cStar ^ (-(3 : ℝ)) := by ring
    have h3 : (2 : ℝ) * cStar ^ (-(3 : ℝ)) ≤ (M + 1 + K) * cStar ^ (-(3 : ℝ)) :=
      mul_le_mul_of_nonneg_right hMK2 hcStar3pos.le
    linarith only [h1, h2, h3]
  have hXMK : (M + 1 + K) / 8 ≤ F := by
    rw [hFdef, le_div_iff₀ hnua_pos]
    have h1 : (M + 1 + K) / 8 * (nu * a) ≤ (M + 1 + K) / 8 * 1 :=
      mul_le_mul_of_nonneg_left hnua_le1 (by positivity)
    have h2 : (M + 1 + K) / 8 * 1 = (M + 1 + K) * (1 / 8) := by ring
    have h3 : (M + 1 + K) * (1 / 8) ≤ (M + 1 + K) * cStar ^ (-(3 : ℝ)) :=
      mul_le_mul_of_nonneg_left hcStar3 hMK2nonneg
    linarith only [h1, h2, h3]
  have hXge2 : (2 : ℝ) ≤ X := by rw [hXdef]; linarith only [hFnonneg]
  have hXa2 : (1 : ℝ) / (4 * a) ≤ X := le_trans hXa hFleX
  have hXnu2 : (1 : ℝ) / (4 * nu) ≤ X := le_trans hXnu hFleX
  have hXcStar2 : (2 : ℝ) * cStar ^ (-(3 : ℝ)) ≤ X := le_trans hXcStar hFleX
  have hXMK2' : (M + 1 + K) / 8 ≤ X := le_trans hXMK hFleX
  have hXpos : 0 < X := lt_of_lt_of_le (by norm_num) hXge2
  have hlogXge : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) hXge2
  have hlogXpos : 0 < Real.log X := Real.log_pos (by linarith only [hXge2])
  have hloga_bound : -Real.log a ≤ Real.log X + Real.log 4 := by
    have h1 : Real.log (1 / (4 * a)) ≤ Real.log X :=
      Real.log_le_log (by positivity) hXa2
    have h2 : Real.log (1 / (4 * a)) = -(Real.log 4 + Real.log a) := by
      rw [Real.log_div (by norm_num) (by positivity), Real.log_one, Real.log_mul (by norm_num) hane']
      ring
    linarith only [h1, h2]
  have hlognu_bound : -Real.log nu ≤ Real.log X + Real.log 4 := by
    have h1 : Real.log (1 / (4 * nu)) ≤ Real.log X :=
      Real.log_le_log (by positivity) hXnu2
    have h2 : Real.log (1 / (4 * nu)) = -(Real.log 4 + Real.log nu) := by
      rw [Real.log_div (by norm_num) (by positivity), Real.log_one, Real.log_mul (by norm_num) hnu.ne']
      ring
    linarith only [h1, h2]
  have hlogcStar_bound : -(3 : ℝ) * Real.log cStar ≤ Real.log X - Real.log 2 := by
    have h1 : Real.log (2 * cStar ^ (-(3 : ℝ))) ≤ Real.log X :=
      Real.log_le_log (by positivity) hXcStar2
    have h2 : Real.log (2 * cStar ^ (-(3 : ℝ))) = Real.log 2 + (-(3 : ℝ)) * Real.log cStar := by
      rw [Real.log_mul (by norm_num) hcStar3pos.ne', Real.log_rpow hcStar]
    linarith only [h1, h2]
  have hlogMK_bound : Real.log (M + 1 + K) ≤ Real.log X + Real.log 8 := by
    have h1 : Real.log ((M + 1 + K) / 8) ≤ Real.log X :=
      Real.log_le_log (by linarith only [hMK2]) hXMK2'
    have h2 : Real.log ((M + 1 + K) / 8) = Real.log (M + 1 + K) - Real.log 8 :=
      Real.log_div (by linarith only [hMK2]) (by norm_num)
    linarith only [h1, h2]
  have hC0pos : (0 : ℝ) < lNaughtThresholdC0 :=
    lt_of_lt_of_le (by norm_num) lNaughtThresholdC0_ge1
  set a12 := a ^ (12 : ℝ) with ha12def
  set nu4 := nu ^ (4 : ℝ) with hnu4def
  have ha12pos : 0 < a12 := Real.rpow_pos_of_pos hapos _
  have hnu4pos : 0 < nu4 := Real.rpow_pos_of_pos hnu _
  set coeff := lNaughtThresholdC0 * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (a12 * nu4) with hcoeffdef
  have hcoeffpos : 0 < coeff := by
    rw [hcoeffdef]
    exact div_pos (mul_pos (mul_pos hC0pos hMK2strict) hcStar3pos) (mul_pos ha12pos hnu4pos)
  set logXpow := (Real.log X) ^ (12 : ℝ) with hlogXpowdef
  have hlogXpowpos : 0 < logXpow := Real.rpow_pos_of_pos hlogXpos _
  set inner := coeff * logXpow with hinnerdef
  have hinnerpos : 0 < inner := mul_pos hcoeffpos hlogXpowpos
  have hinner_eq : inner = lNaughtInner lNaughtThresholdC0 M alpha cStar nu K := by
    rw [hinnerdef, hcoeffdef, hlogXpowdef, hXdef, hFdef, ha12def, hnu4def, hadef]
    rfl
  have hlog_inner : Real.log inner = Real.log coeff + 12 * Real.log (Real.log X) := by
    rw [hinnerdef, Real.log_mul hcoeffpos.ne' hlogXpowpos.ne', hlogXpowdef,
      Real.log_rpow hlogXpos]
  have hlog_coeff : Real.log coeff =
      Real.log lNaughtThresholdC0 + Real.log (M + 1 + K) + (-(3 : ℝ)) * Real.log cStar -
        (12 * Real.log a + 4 * Real.log nu) := by
    rw [hcoeffdef, Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) hcStar3pos.ne', Real.log_mul hC0pos.ne' hMK2strict.ne',
      Real.log_rpow hcStar, Real.log_mul ha12pos.ne' hnu4pos.ne', ha12def, hnu4def,
      Real.log_rpow hapos, Real.log_rpow hnu]
  have hexp_inv_lt_half : Real.exp (-1) < (1 : ℝ) / 2 := by
    rw [Real.exp_neg]
    rw [inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
    linarith only [Real.exp_one_gt_d9]
  have hlogXgt_inv_e : Real.exp (-1) < Real.log X := by
    have h2 : (1 : ℝ) / 2 < Real.log 2 := by linarith only [Real.log_two_gt_d9]
    linarith only [hexp_inv_lt_half, h2, hlogXge]
  have hloglogX_ge : (-1 : ℝ) ≤ Real.log (Real.log X) := by
    have h := Real.log_le_log (Real.exp_pos (-1)) hlogXgt_inv_e.le
    rwa [Real.log_exp] at h
  have hlog2lt1 : Real.log 2 < 1 := by linarith only [Real.log_two_lt_d9]
  have hlogC0eq : Real.log lNaughtThresholdC0 = 240 * Real.log 2 := by
    unfold lNaughtThresholdC0
    rw [Real.log_pow]
    push_cast
    ring
  have hlogcoeff_lower :
      Real.log lNaughtThresholdC0 - 2 * Real.log 2 ≤ Real.log coeff := by
    have h1 : Real.log 2 ≤ Real.log (M + 1 + K) :=
      Real.log_le_log (by norm_num) hMK2
    have h2 : -(3 : ℝ) * Real.log cStar ≥ -(3 : ℝ) * Real.log 2 := by
      have := Real.log_le_log hcStar hcStar2
      linarith only [this]
    have h3 : 12 * Real.log a ≤ 0 := by
      have : Real.log a ≤ 0 := Real.log_nonpos hapos.le hale1
      linarith only [this]
    have h4 : 4 * Real.log nu ≤ 0 := by
      have : Real.log nu ≤ 0 := Real.log_nonpos hnu.le hnu1
      linarith only [this]
    linarith only [hlog_coeff, h1, h2, h3, h4]
  have hloglogX_le : Real.log (Real.log X) ≤ Real.log X := by
    have h := Real.log_le_sub_one_of_pos hlogXpos
    linarith only [h]
  have hlog4eq : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow]
    push_cast; ring
  have hlog8eq : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℕ) by norm_num, Real.log_pow]
    push_cast; ring
  have hconst : Real.log 8 - Real.log 2 + 16 * Real.log 4 ≤ 34 := by
    rw [hlog4eq, hlog8eq]; linarith only [hlog2lt1]
  have hlog_inner_upper :
      Real.log inner ≤ Real.log lNaughtThresholdC0 + 30 * Real.log X + 34 := by
    linarith only [hlog_inner, hlog_coeff, hlogMK_bound, hlogcStar_bound, hloga_bound,
      hlognu_bound, hloglogX_le, hconst]
  -- Numeral closure: at `X = 2`'s minimum, `30 * log X` is beaten by `2^20 * log X`.
  have hnumeral : Real.log lNaughtThresholdC0 + 34 ≤ (2 ^ (20 : ℕ) - 30) * Real.log X := by
    have h1 : Real.log lNaughtThresholdC0 + 34 ≤ 240 * Real.log 2 + 34 := by
      linarith only [hlogC0eq]
    have h2 : (240 : ℝ) * Real.log 2 + 34 ≤ (2 ^ (20 : ℕ) - 30) * Real.log 2 := by
      have : (2 : ℝ) ^ (20 : ℕ) - 30 = 1048546 := by norm_num
      rw [this]
      linarith only [Real.log_two_gt_d9]
    have h3 : (2 ^ (20 : ℕ) - 30 : ℝ) * Real.log 2 ≤ (2 ^ (20 : ℕ) - 30) * Real.log X := by
      apply mul_le_mul_of_nonneg_left hlogXge
      norm_num
    linarith only [h1, h2, h3]
  have hbase_log : Real.log inner ≤ (2 : ℝ) ^ (20 : ℕ) * Real.log X := by
    linarith only [hlog_inner_upper, hnumeral]
  have hpeak_log : (12 : ℝ) ≤ Real.log inner := by
    have h1 : (12 : ℝ) ≤ Real.log lNaughtThresholdC0 - 2 * Real.log 2 - 12 := by
      rw [hlogC0eq]; linarith only [Real.log_two_gt_d9]
    have h2 : Real.log lNaughtThresholdC0 - 2 * Real.log 2 - 12 ≤ Real.log inner := by
      have h3 : Real.log lNaughtThresholdC0 - 2 * Real.log 2 + 12 * (-1) ≤ Real.log inner := by
        rw [hlog_inner]
        linarith only [hlogcoeff_lower, hloglogX_ge]
      linarith only [h3]
    linarith only [h1, h2]
  set t0 := SuperdiffusionCLT.Frozen.Section4.lNaught lNaughtThresholdC0 M alpha cStar nu K
    with ht0def
  have ht0_rpow : t0 ^ a = inner := by
    rw [ht0def, hadef, hinner_eq]
    exact lNaught_rpow_eq_inner hC0pos.le (by linarith only [hM]) hK hcStar hnu halpha1
  have ht0nonneg : 0 ≤ t0 := by
    rw [ht0def]
    exact SuperdiffusionCLT.Section4.LNaught.lNaught_nonneg hC0pos.le
      (by linarith only [hM] : (0:ℝ) ≤ M) hK hcStar hnu halpha1
  have ht0pos : 0 < t0 := by
    rcases ht0nonneg.lt_or_eq with h | h
    · exact h
    · exfalso
      have hz : t0 ^ a = 0 := by rw [← h]; exact Real.zero_rpow hane'
      rw [ht0_rpow] at hz
      exact hinnerpos.ne' hz
  have hpeak_final : (12 : ℝ) ≤ a * Real.log t0 := by
    have h1 : a * Real.log t0 = Real.log (t0 ^ a) := (Real.log_rpow ht0pos a).symm
    rw [h1, ht0_rpow]
    exact hpeak_log
  have ht0ge1 : (1 : ℝ) ≤ t0 := by
    by_contra hcon
    push Not at hcon
    have hlogt0nonpos : Real.log t0 ≤ 0 := Real.log_nonpos ht0pos.le hcon.le
    have : a * Real.log t0 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hapos.le hlogt0nonpos
    linarith only [hpeak_final, this]
  have hav0_le : a * Real.log t0 ≤ (2 : ℝ) ^ (20 : ℕ) * Real.log X := by
    have heq : a * Real.log t0 = Real.log inner := by
      rw [(Real.log_rpow ht0pos a).symm, ht0_rpow]
    rw [heq]; exact hbase_log
  have hav0_nonneg : 0 ≤ a * Real.log t0 := by linarith only [hpeak_final]
  have ha12_le_a : a12 ≤ a := by
    rw [ha12def]
    calc a ^ (12 : ℝ) ≤ a ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hapos hale1 (by norm_num)
      _ = a := Real.rpow_one a
  have hnu4_le1 : nu4 ≤ 1 := by
    rw [hnu4def]
    calc nu ^ (4 : ℝ) ≤ 1 ^ (4 : ℝ) := Real.rpow_le_rpow hnu.le hnu1 (by norm_num)
      _ = 1 := Real.one_rpow 4
  have ha12nu4_le_a : a12 * nu4 ≤ a := by
    calc a12 * nu4 ≤ a * 1 := mul_le_mul ha12_le_a hnu4_le1 hnu4pos.le hapos.le
      _ = a := mul_one a
  have ha12nu4_pos : 0 < a12 * nu4 := mul_pos ha12pos hnu4pos
  refine ⟨ht0ge1, hpeak_final, ?_, ?_⟩
  · rw [ht0_rpow]
    have hpow12 : (a * Real.log t0) ^ (12 : ℕ) ≤ ((2 : ℝ) ^ (20 : ℕ) * Real.log X) ^ (12 : ℕ) :=
      pow_le_pow_left₀ hav0_nonneg hav0_le 12
    have hrhs_eq : ((2 : ℝ) ^ (20 : ℕ) * Real.log X) ^ (12 : ℕ) =
        lNaughtThresholdC0 * (Real.log X) ^ (12 : ℕ) := by
      unfold lNaughtThresholdC0
      rw [mul_pow]
      congr 1
      rw [← pow_mul]
    have hlhs_eq : (a * Real.log t0) ^ (12 : ℕ) = a ^ (12 : ℕ) * (Real.log t0) ^ (12 : ℕ) :=
      mul_pow a (Real.log t0) 12
    rw [hlhs_eq, hrhs_eq] at hpow12
    have ha12nat_pos : 0 < a ^ (12 : ℕ) := pow_pos hapos 12
    have hv0_12 : (Real.log t0) ^ (12 : ℕ) ≤
        lNaughtThresholdC0 * (Real.log X) ^ (12 : ℕ) / a ^ (12 : ℕ) := by
      rw [le_div_iff₀ ha12nat_pos, mul_comm]
      exact hpow12
    have ha12_eq_nat : a12 = a ^ (12 : ℕ) := by
      rw [ha12def]
      have h3 : (12 : ℝ) = ((12 : ℕ) : ℝ) := by norm_num
      rw [h3, Real.rpow_natCast]
    have hAconst_nonneg : (0 : ℝ) ≤ M * cStar ^ (-(3 : ℝ)) * nu ^ (-(4 : ℝ)) := by positivity
    have hkey : (M * cStar ^ (-(3 : ℝ)) * nu ^ (-(4 : ℝ))) * (Real.log t0) ^ (12 : ℕ) ≤
        (M * cStar ^ (-(3 : ℝ)) * nu ^ (-(4 : ℝ))) *
          (lNaughtThresholdC0 * (Real.log X) ^ (12 : ℕ) / a ^ (12 : ℕ)) :=
      mul_le_mul_of_nonneg_left hv0_12 hAconst_nonneg
    have hratio_le : (M * cStar ^ (-(3 : ℝ)) * nu ^ (-(4 : ℝ))) *
        (lNaughtThresholdC0 * (Real.log X) ^ (12 : ℕ) / a ^ (12 : ℕ)) ≤ inner := by
      rw [hinnerdef, hcoeffdef, hlogXpowdef]
      have hlogXpow_nat_eq : (Real.log X) ^ (12 : ℝ) = (Real.log X) ^ (12 : ℕ) := by
        have h3 : (12 : ℝ) = ((12 : ℕ) : ℝ) := by norm_num
        rw [h3, Real.rpow_natCast]
      rw [hlogXpow_nat_eq, ← ha12_eq_nat]
      have hstep : (M * cStar ^ (-(3 : ℝ)) * nu ^ (-(4 : ℝ))) *
          (lNaughtThresholdC0 * (Real.log X) ^ (12 : ℕ) / a12) =
          lNaughtThresholdC0 * (M * cStar ^ (-(3 : ℝ)) / (a12 * nu4)) *
            (Real.log X) ^ (12 : ℕ) := by
        have hnu4inv : nu ^ (-(4 : ℝ)) = 1 / nu4 := by
          rw [hnu4def, Real.rpow_neg hnu.le]
          ring
        rw [hnu4inv]
        field_simp
      rw [hstep]
      have hcoef_le : lNaughtThresholdC0 * (M * cStar ^ (-(3 : ℝ)) / (a12 * nu4)) ≤
          lNaughtThresholdC0 * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (a12 * nu4) := by
        have h1 : M * cStar ^ (-(3 : ℝ)) ≤ (M + 1 + K) * cStar ^ (-(3 : ℝ)) :=
          mul_le_mul_of_nonneg_right (by linarith only [hK]) hcStar3pos.le
        have h2 : lNaughtThresholdC0 * (M * cStar ^ (-(3 : ℝ))) ≤
            lNaughtThresholdC0 * ((M + 1 + K) * cStar ^ (-(3 : ℝ))) :=
          mul_le_mul_of_nonneg_left h1 hC0pos.le
        have h3 : lNaughtThresholdC0 * (M * cStar ^ (-(3 : ℝ)) / (a12 * nu4)) =
            lNaughtThresholdC0 * (M * cStar ^ (-(3 : ℝ))) / (a12 * nu4) := by ring
        have h4 : lNaughtThresholdC0 * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (a12 * nu4) =
            lNaughtThresholdC0 * ((M + 1 + K) * cStar ^ (-(3 : ℝ))) / (a12 * nu4) := by ring
        rw [h3, h4]
        exact div_le_div_of_nonneg_right h2 (mul_pos ha12pos hnu4pos).le
      exact mul_le_mul_of_nonneg_right hcoef_le (pow_pos hlogXpos 12).le
    exact le_trans hkey hratio_le
  · rw [ht0_rpow, pow_one]
    have hlogt0_le : Real.log t0 ≤ (2 : ℝ) ^ (20 : ℕ) * Real.log X / a := by
      rw [le_div_iff₀ hapos]
      calc Real.log t0 * a = a * Real.log t0 := by ring
        _ ≤ (2 : ℝ) ^ (20 : ℕ) * Real.log X := hav0_le
    have hlog2_11 : (Real.log 2) ^ (11 : ℝ) ≤ (Real.log X) ^ (11 : ℝ) :=
      Real.rpow_le_rpow (by linarith only [Real.log_two_gt_d9]) hlogXge (by norm_num)
    have hnumeral2 : (2 : ℝ) ^ (21 : ℕ) ≤ lNaughtThresholdC0 * (Real.log 2) ^ (11 : ℕ) := by
      have hlog2gt : (0.6 : ℝ) < Real.log 2 := by linarith only [Real.log_two_gt_d9]
      have h06 : (0.6 : ℝ) ^ (11 : ℕ) ≤ (Real.log 2) ^ (11 : ℕ) :=
        pow_le_pow_left₀ (by norm_num) hlog2gt.le 11
      have hbig : (2 : ℝ) ^ (21 : ℕ) ≤ lNaughtThresholdC0 * (0.6 : ℝ) ^ (11 : ℕ) := by
        unfold lNaughtThresholdC0; norm_num
      calc (2 : ℝ) ^ (21 : ℕ) ≤ lNaughtThresholdC0 * (0.6 : ℝ) ^ (11 : ℕ) := hbig
        _ ≤ lNaughtThresholdC0 * (Real.log 2) ^ (11 : ℕ) :=
          mul_le_mul_of_nonneg_left h06 hC0pos.le
    have hnumeral2' : (2 : ℝ) ^ (21 : ℕ) ≤ lNaughtThresholdC0 * (Real.log X) ^ (11 : ℝ) := by
      have h11eq : (Real.log 2) ^ (11 : ℕ) = (Real.log 2) ^ (11 : ℝ) := by
        have h3 : (11 : ℝ) = ((11 : ℕ) : ℝ) := by norm_num
        rw [h3, Real.rpow_natCast]
      rw [h11eq] at hnumeral2
      calc (2 : ℝ) ^ (21 : ℕ) ≤ lNaughtThresholdC0 * (Real.log 2) ^ (11 : ℝ) := hnumeral2
        _ ≤ lNaughtThresholdC0 * (Real.log X) ^ (11 : ℝ) :=
          mul_le_mul_of_nonneg_left hlog2_11 hC0pos.le
    have hlogXpow_split : (Real.log X) ^ (12 : ℝ) = (Real.log X) ^ (11 : ℝ) * Real.log X := by
      have h1 : (Real.log X) ^ ((11 : ℝ) + 1) =
          (Real.log X) ^ (11 : ℝ) * (Real.log X) ^ (1 : ℝ) := Real.rpow_add hlogXpos 11 1
      rw [Real.rpow_one] at h1
      have h2 : (11 : ℝ) + 1 = 12 := by norm_num
      rwa [h2] at h1
    have h21le : (2 : ℝ) ^ (21 : ℕ) * Real.log X ≤
        lNaughtThresholdC0 * (Real.log X) ^ (12 : ℝ) := by
      rw [hlogXpow_split]
      calc (2 : ℝ) ^ (21 : ℕ) * Real.log X ≤
            (lNaughtThresholdC0 * (Real.log X) ^ (11 : ℝ)) * Real.log X :=
            mul_le_mul_of_nonneg_right hnumeral2' hlogXpos.le
        _ = lNaughtThresholdC0 * ((Real.log X) ^ (11 : ℝ) * Real.log X) := by ring
    -- extra headroom: `2^22` (not just `2^21`) so the target's own factor of
    -- `2` (`Aconst = 2*(M+1+K)*c⋆^{-3}`) is absorbed on top of the `a12*nu4
    -- ≤ a` loss.
    have hnumeral3 : (2 : ℝ) ^ (22 : ℕ) ≤ lNaughtThresholdC0 * (Real.log 2) ^ (11 : ℕ) := by
      have hlog2gt : (0.6 : ℝ) < Real.log 2 := by linarith only [Real.log_two_gt_d9]
      have h06 : (0.6 : ℝ) ^ (11 : ℕ) ≤ (Real.log 2) ^ (11 : ℕ) :=
        pow_le_pow_left₀ (by norm_num) hlog2gt.le 11
      have hbig : (2 : ℝ) ^ (22 : ℕ) ≤ lNaughtThresholdC0 * (0.6 : ℝ) ^ (11 : ℕ) := by
        unfold lNaughtThresholdC0; norm_num
      calc (2 : ℝ) ^ (22 : ℕ) ≤ lNaughtThresholdC0 * (0.6 : ℝ) ^ (11 : ℕ) := hbig
        _ ≤ lNaughtThresholdC0 * (Real.log 2) ^ (11 : ℕ) :=
          mul_le_mul_of_nonneg_left h06 hC0pos.le
    have hnumeral3' : (2 : ℝ) ^ (22 : ℕ) ≤ lNaughtThresholdC0 * (Real.log X) ^ (11 : ℝ) := by
      have h11eq : (Real.log 2) ^ (11 : ℕ) = (Real.log 2) ^ (11 : ℝ) := by
        have h3 : (11 : ℝ) = ((11 : ℕ) : ℝ) := by norm_num
        rw [h3, Real.rpow_natCast]
      rw [h11eq] at hnumeral3
      calc (2 : ℝ) ^ (22 : ℕ) ≤ lNaughtThresholdC0 * (Real.log 2) ^ (11 : ℝ) := hnumeral3
        _ ≤ lNaughtThresholdC0 * (Real.log X) ^ (11 : ℝ) :=
          mul_le_mul_of_nonneg_left hlog2_11 hC0pos.le
    have h22le : (2 : ℝ) ^ (22 : ℕ) * Real.log X ≤
        lNaughtThresholdC0 * (Real.log X) ^ (12 : ℝ) := by
      rw [hlogXpow_split]
      calc (2 : ℝ) ^ (22 : ℕ) * Real.log X ≤
            (lNaughtThresholdC0 * (Real.log X) ^ (11 : ℝ)) * Real.log X :=
            mul_le_mul_of_nonneg_right hnumeral3' hlogXpos.le
        _ = lNaughtThresholdC0 * ((Real.log X) ^ (11 : ℝ) * Real.log X) := by ring
    have hfinal_ratio2 : 2 * ((2 : ℝ) ^ (20 : ℕ) * Real.log X / a) ≤
        lNaughtThresholdC0 * (Real.log X) ^ (12 : ℝ) / (a12 * nu4) := by
      have hlhs_eq : 2 * ((2 : ℝ) ^ (20 : ℕ) * Real.log X / a) =
          (2 : ℝ) ^ (21 : ℕ) * Real.log X / a := by
        rw [show (2 : ℝ) ^ (21 : ℕ) = 2 * (2 : ℝ) ^ (20 : ℕ) by norm_num]
        ring
      rw [hlhs_eq, div_le_div_iff₀ hapos ha12nu4_pos]
      have hstep1 : (2 : ℝ) ^ (21 : ℕ) * Real.log X * (a12 * nu4) ≤
          (2 : ℝ) ^ (21 : ℕ) * Real.log X * a :=
        mul_le_mul_of_nonneg_left ha12nu4_le_a (by positivity)
      have hstep2 : (2 : ℝ) ^ (21 : ℕ) * Real.log X * a ≤
          (2 : ℝ) ^ (22 : ℕ) * Real.log X * a := by
        apply mul_le_mul_of_nonneg_right _ hapos.le
        apply mul_le_mul_of_nonneg_right _ hlogXpos.le
        norm_num
      have hstep3 : (2 : ℝ) ^ (22 : ℕ) * Real.log X * a ≤
          lNaughtThresholdC0 * (Real.log X) ^ (12 : ℝ) * a :=
        mul_le_mul_of_nonneg_right h22le hapos.le
      linarith only [hstep1, hstep2, hstep3]
    have hcoeff_eq : (M + 1 + K) * cStar ^ (-(3 : ℝ)) *
        (lNaughtThresholdC0 * (Real.log X) ^ (12 : ℝ) / (a12 * nu4)) = inner := by
      rw [hinnerdef, hcoeffdef, hlogXpowdef]; ring
    have h2MK_nonneg : (0 : ℝ) ≤ 2 * ((M + 1 + K) * cStar ^ (-(3 : ℝ))) := by positivity
    have hMK_nonneg : (0 : ℝ) ≤ (M + 1 + K) * cStar ^ (-(3 : ℝ)) := by positivity
    calc 2 * ((M + 1 + K) * cStar ^ (-(3 : ℝ))) * Real.log t0 ≤
          2 * ((M + 1 + K) * cStar ^ (-(3 : ℝ))) * ((2 : ℝ) ^ (20 : ℕ) * Real.log X / a) :=
          mul_le_mul_of_nonneg_left hlogt0_le h2MK_nonneg
      _ = (M + 1 + K) * cStar ^ (-(3 : ℝ)) *
            (2 * ((2 : ℝ) ^ (20 : ℕ) * Real.log X / a)) := by ring
      _ ≤ (M + 1 + K) * cStar ^ (-(3 : ℝ)) *
            (lNaughtThresholdC0 * (Real.log X) ^ (12 : ℝ) / (a12 * nu4)) :=
          mul_le_mul_of_nonneg_left hfinal_ratio2 hMK_nonneg
      _ = inner := hcoeff_eq

/-! ## The defining threshold property (`e.Lnaught.def`) -/

/-- **The defining threshold property of `L₀`** (`e.Lnaught.def`):
the universal constant `C` in `L₀`'s own formula is chosen large
enough that once `L ≥ L₀(M,α,c⋆,ν,K)`, both displayed consequences hold. -/
theorem lNaught_threshold :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C →
      ∀ M : ℝ, 1 ≤ M → ∀ alpha : ℝ, 0 ≤ alpha → alpha < 1 →
      ∀ cStar : ℝ, 0 < cStar → cStar ≤ 2 →
      ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
      ∀ K : ℝ, 0 ≤ K →
      ∀ L : ℕ,
        SuperdiffusionCLT.Frozen.Section4.lNaught C M alpha cStar nu K ≤ (L : ℝ) →
        M * cStar ^ (-(3 : ℝ)) * nu ^ (-(4 : ℝ)) * Real.log (L : ℝ) ^ (12 : ℝ) ≤
            (L : ℝ) ^ (1 - alpha) ∧
        (M + 1 + K) * cStar ^ (-(3 : ℝ)) * Real.log (3 + (L : ℝ)) ≤ (L : ℝ) ^ (1 - alpha) := by
  refine ⟨lNaughtThresholdC0, lNaughtThresholdC0_ge1, ?_⟩
  intro C hC M hM alpha halpha0 halpha1 cStar hcStar hcStar2 nu hnu hnu1 K hK L hL
  obtain ⟨ht0ge1, hpeak, hbase, hbase1⟩ :=
    lNaught_c0_peak_base12 hM hK hcStar hcStar2 hnu hnu1 halpha0 halpha1
  set t0 := SuperdiffusionCLT.Frozen.Section4.lNaught lNaughtThresholdC0 M alpha cStar nu K
    with ht0def
  have ht0leC : t0 ≤ SuperdiffusionCLT.Frozen.Section4.lNaught C M alpha cStar nu K := by
    rw [ht0def]
    exact SuperdiffusionCLT.Section4.LNaught.lNaught_mono_const
      (le_trans zero_le_one lNaughtThresholdC0_ge1) hC (by linarith only [hM]) hK hcStar hnu
      halpha1
  have ht0leL : t0 ≤ (L : ℝ) := le_trans ht0leC hL
  have ha : 0 < 1 - alpha := by linarith only [halpha1]
  have hA : 0 < M * cStar ^ (-(3 : ℝ)) * nu ^ (-(4 : ℝ)) := by positivity
  have hres := lNaught_crossing_core (a := 1 - alpha)
    (Aconst := M * cStar ^ (-(3 : ℝ)) * nu ^ (-(4 : ℝ))) (t0 := t0) (t := (L : ℝ)) (p := 12)
    ha hA ht0ge1 (by norm_num) hpeak hbase ht0leL
  have hcast : Real.log (L : ℝ) ^ (12 : ℕ) = Real.log (L : ℝ) ^ (12 : ℝ) := by
    have h3 : (12 : ℝ) = ((12 : ℕ) : ℝ) := by norm_num
    rw [h3, Real.rpow_natCast]
  refine ⟨by rwa [hcast] at hres, ?_⟩
  -- The second conjunct: apply the crossing lemma at `t = 3 + L`, then absorb
  -- `(3+L)^{1-α} ≤ 2 L^{1-α}` (using `L ≥ t0 > 4 > 3`).
  have ht0pos : 0 < t0 := lt_of_lt_of_le one_pos ht0ge1
  have hlogt0nonneg : 0 ≤ Real.log t0 := Real.log_nonneg ht0ge1
  have hlogt0_ge12 : (12 : ℝ) ≤ Real.log t0 := by
    have hale1 : (1 - alpha) ≤ 1 := by linarith only [halpha0]
    have h1 : (1 - alpha) * Real.log t0 ≤ Real.log t0 :=
      mul_le_of_le_one_left hlogt0nonneg hale1
    linarith only [hpeak, h1]
  have hlog4le3 : Real.log 4 ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith only [h]
  have ht0_gt4 : (4 : ℝ) < t0 := by
    by_contra hcon
    push Not at hcon
    have h1 : Real.log t0 ≤ Real.log 4 := Real.log_le_log ht0pos hcon
    linarith only [h1, hlog4le3, hlogt0_ge12]
  have hL_gt4 : (4 : ℝ) < (L : ℝ) := lt_of_lt_of_le ht0_gt4 ht0leL
  have ht0le3L : t0 ≤ 3 + (L : ℝ) := by linarith only [ht0leL, hL_gt4]
  have hA' : 0 < 2 * ((M + 1 + K) * cStar ^ (-(3 : ℝ))) := by positivity
  have hres' := lNaught_crossing_core (a := 1 - alpha)
    (Aconst := 2 * ((M + 1 + K) * cStar ^ (-(3 : ℝ)))) (t0 := t0) (t := 3 + (L : ℝ)) (p := 1)
    ha hA' ht0ge1 (le_refl 1) (le_trans (by norm_num) hpeak) hbase1 ht0le3L
  rw [pow_one] at hres'
  have h3Lpos : (0 : ℝ) < 3 + (L : ℝ) := by linarith only [hL_gt4]
  have h3Lle2L : 3 + (L : ℝ) ≤ 2 * (L : ℝ) := by linarith only [hL_gt4]
  have hLpos : (0 : ℝ) < (L : ℝ) := by linarith only [hL_gt4]
  have hrpow1 : (3 + (L : ℝ)) ^ (1 - alpha) ≤ (2 * (L : ℝ)) ^ (1 - alpha) :=
    Real.rpow_le_rpow h3Lpos.le h3Lle2L ha.le
  have hrpow2 : (2 * (L : ℝ)) ^ (1 - alpha) = (2 : ℝ) ^ (1 - alpha) * (L : ℝ) ^ (1 - alpha) :=
    Real.mul_rpow (by norm_num) hLpos.le
  have hrpow3 : (2 : ℝ) ^ (1 - alpha) ≤ (2 : ℝ) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [halpha0])
  have hrpow4 : (2 : ℝ) ^ (1 : ℝ) = 2 := Real.rpow_one 2
  have hLrpow_nonneg : (0 : ℝ) ≤ (L : ℝ) ^ (1 - alpha) := Real.rpow_nonneg hLpos.le _
  have hfinal : (3 + (L : ℝ)) ^ (1 - alpha) ≤ 2 * (L : ℝ) ^ (1 - alpha) := by
    calc (3 + (L : ℝ)) ^ (1 - alpha) ≤ (2 * (L : ℝ)) ^ (1 - alpha) := hrpow1
      _ = (2 : ℝ) ^ (1 - alpha) * (L : ℝ) ^ (1 - alpha) := hrpow2
      _ ≤ (2 : ℝ) ^ (1 : ℝ) * (L : ℝ) ^ (1 - alpha) :=
          mul_le_mul_of_nonneg_right hrpow3 hLrpow_nonneg
      _ = 2 * (L : ℝ) ^ (1 - alpha) := by rw [hrpow4]
  have hchain : 2 * ((M + 1 + K) * cStar ^ (-(3 : ℝ))) * Real.log (3 + (L : ℝ)) ≤
      2 * (L : ℝ) ^ (1 - alpha) := le_trans hres' hfinal
  have hchain' : 2 * ((M + 1 + K) * cStar ^ (-(3 : ℝ)) * Real.log (3 + (L : ℝ))) ≤
      2 * (L : ℝ) ^ (1 - alpha) := by
    have heq : 2 * ((M + 1 + K) * cStar ^ (-(3 : ℝ)) * Real.log (3 + (L : ℝ))) =
        2 * ((M + 1 + K) * cStar ^ (-(3 : ℝ))) * Real.log (3 + (L : ℝ)) := by ring
    rw [heq]; exact hchain
  linarith only [hchain']

/-! ## The absorption consequence used downstream (`e.L.vs.Lnaught`) -/

/-- The form of the absorption property `e.Lnaught.def` ⟹ `e.L.vs.Lnaught`
that the scale constructions actually consume: once
`L ≥ L₀`, the correction term `M L^α \log^3 L` is at most `L/2`. Derived
directly from `lNaught_threshold`'s first conjunct: `cStar ≤ 2` and `nu ≤ 1`
bound the extra constant by `16`, and `L > 8` (itself forced by `L ≥ L₀`, the
same way `lNaught_threshold`'s second conjunct forces `L > 4`) gives
`log^9 L ≥ 16`. -/
theorem lNaught_absorbs :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C →
      ∀ M : ℝ, 1 ≤ M → ∀ alpha : ℝ, 0 ≤ alpha → alpha < 1 →
      ∀ cStar : ℝ, 0 < cStar → cStar ≤ 2 →
      ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
      ∀ K : ℝ, 0 ≤ K →
      ∀ L : ℕ,
        SuperdiffusionCLT.Frozen.Section4.lNaught C M alpha cStar nu K ≤ (L : ℝ) →
        M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (L : ℝ) / 2 := by
  refine ⟨lNaughtThresholdC0, lNaughtThresholdC0_ge1, ?_⟩
  intro C hC M hM alpha halpha0 halpha1 cStar hcStar hcStar2 nu hnu hnu1 K hK L hL
  obtain ⟨ht0ge1, hpeak, hbase, _⟩ :=
    lNaught_c0_peak_base12 hM hK hcStar hcStar2 hnu hnu1 halpha0 halpha1
  set t0 := SuperdiffusionCLT.Frozen.Section4.lNaught lNaughtThresholdC0 M alpha cStar nu K
    with ht0def
  have ht0leC : t0 ≤ SuperdiffusionCLT.Frozen.Section4.lNaught C M alpha cStar nu K := by
    rw [ht0def]
    exact SuperdiffusionCLT.Section4.LNaught.lNaught_mono_const
      (le_trans zero_le_one lNaughtThresholdC0_ge1) hC (by linarith only [hM]) hK hcStar hnu
      halpha1
  have ht0leL : t0 ≤ (L : ℝ) := le_trans ht0leC hL
  have ha : 0 < 1 - alpha := by linarith only [halpha1]
  have hA : 0 < M * cStar ^ (-(3 : ℝ)) * nu ^ (-(4 : ℝ)) := by positivity
  have hres := lNaught_crossing_core (a := 1 - alpha)
    (Aconst := M * cStar ^ (-(3 : ℝ)) * nu ^ (-(4 : ℝ))) (t0 := t0) (t := (L : ℝ)) (p := 12)
    ha hA ht0ge1 (by norm_num) hpeak hbase ht0leL
  have hcast : Real.log (L : ℝ) ^ (12 : ℕ) = Real.log (L : ℝ) ^ (12 : ℝ) := by
    have h3 : (12 : ℝ) = ((12 : ℕ) : ℝ) := by norm_num
    rw [h3, Real.rpow_natCast]
  rw [hcast] at hres
  -- `L > 8`, so `log L ≥ log 8 > 3 log 2`.
  have ht0pos : 0 < t0 := lt_of_lt_of_le one_pos ht0ge1
  have hlogt0nonneg : 0 ≤ Real.log t0 := Real.log_nonneg ht0ge1
  have hlogt0_ge12 : (12 : ℝ) ≤ Real.log t0 := by
    have hale1 : (1 - alpha) ≤ 1 := by linarith only [halpha0]
    have h1 : (1 - alpha) * Real.log t0 ≤ Real.log t0 :=
      mul_le_of_le_one_left hlogt0nonneg hale1
    linarith only [hpeak, h1]
  have hlog8eq2 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℕ) by norm_num, Real.log_pow]
    push_cast; ring
  have hlog8le3 : Real.log 8 ≤ 3 := by
    rw [hlog8eq2]; linarith only [Real.log_two_lt_d9]
  have ht0_gt8 : (8 : ℝ) < t0 := by
    by_contra hcon
    push Not at hcon
    have h1 : Real.log t0 ≤ Real.log 8 := Real.log_le_log ht0pos hcon
    linarith only [h1, hlog8le3, hlogt0_ge12]
  have hL_gt8 : (8 : ℝ) < (L : ℝ) := lt_of_lt_of_le ht0_gt8 ht0leL
  have hLpos : (0 : ℝ) < (L : ℝ) := by linarith only [hL_gt8]
  have hlogLge : Real.log 8 ≤ Real.log (L : ℝ) :=
    Real.log_le_log (by norm_num) (by linarith only [hL_gt8])
  have hlogLpos : 0 < Real.log (L : ℝ) := by
    have h0lt8 : (0:ℝ) < Real.log 8 := by
      rw [hlog8eq2]; linarith only [Real.log_two_gt_d9]
    linarith only [h0lt8, hlogLge]
  -- `log^9 L ≥ (3 log 2)^9 ≥ 16`.
  have hlogL_ge3log2 : (3 : ℝ) * Real.log 2 ≤ Real.log (L : ℝ) := by
    rw [← hlog8eq2]; exact hlogLge
  have h3log2pos : (0 : ℝ) < 3 * Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hpow9 : ((3 : ℝ) * Real.log 2) ^ (9 : ℕ) ≤ Real.log (L : ℝ) ^ (9 : ℕ) :=
    pow_le_pow_left₀ h3log2pos.le hlogL_ge3log2 9
  have hnum9 : (16 : ℝ) ≤ ((3 : ℝ) * Real.log 2) ^ (9 : ℕ) := by
    have h3log2gt : (2.07 : ℝ) ≤ 3 * Real.log 2 := by linarith only [Real.log_two_gt_d9]
    have hpow : (2.07 : ℝ) ^ (9 : ℕ) ≤ ((3 : ℝ) * Real.log 2) ^ (9 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) h3log2gt 9
    have hval : (16 : ℝ) ≤ (2.07 : ℝ) ^ (9 : ℕ) := by norm_num
    linarith only [hpow, hval]
  have hlogL9ge16 : (16 : ℝ) ≤ Real.log (L : ℝ) ^ (9 : ℕ) := le_trans hnum9 hpow9
  have hlogL9eq : Real.log (L : ℝ) ^ (9 : ℝ) = Real.log (L : ℝ) ^ (9 : ℕ) := by
    have h3 : (9 : ℝ) = ((9 : ℕ) : ℝ) := by norm_num
    rw [h3, Real.rpow_natCast]
  have hlogL9ge16' : (16 : ℝ) ≤ Real.log (L : ℝ) ^ (9 : ℝ) := by rw [hlogL9eq]; exact hlogL9ge16
  -- assemble: `M * L^α * log^3 L ≤ L * c⋆^3 * ν^4 / log^9 L ≤ L / 2`.
  have hcStar3nonneg : (0 : ℝ) ≤ cStar ^ (-(3 : ℝ)) := (Real.rpow_pos_of_pos hcStar _).le
  have hnu4nonneg : (0 : ℝ) ≤ nu ^ (-(4 : ℝ)) := (Real.rpow_pos_of_pos hnu _).le
  have hlogL3pos : (0 : ℝ) < Real.log (L : ℝ) ^ (3 : ℝ) := Real.rpow_pos_of_pos hlogLpos _
  have hlogL12pos : (0 : ℝ) < Real.log (L : ℝ) ^ (12 : ℝ) := Real.rpow_pos_of_pos hlogLpos _
  have hcStarpos3' : (0 : ℝ) < cStar ^ (3 : ℝ) := Real.rpow_pos_of_pos hcStar _
  have hnupos4' : (0 : ℝ) < nu ^ (4 : ℝ) := Real.rpow_pos_of_pos hnu _
  have hMbound : M ≤ (L : ℝ) ^ (1 - alpha) * cStar ^ (3 : ℝ) * nu ^ (4 : ℝ) /
      Real.log (L : ℝ) ^ (12 : ℝ) := by
    rw [le_div_iff₀ hlogL12pos]
    have hcStarinv : cStar ^ (-(3 : ℝ)) = (cStar ^ (3 : ℝ))⁻¹ := Real.rpow_neg hcStar.le 3
    have hnuinv : nu ^ (-(4 : ℝ)) = (nu ^ (4 : ℝ))⁻¹ := Real.rpow_neg hnu.le 4
    rw [hcStarinv, hnuinv] at hres
    have hmul := mul_le_mul_of_nonneg_right hres (mul_pos hcStarpos3' hnupos4').le
    calc M * Real.log (L : ℝ) ^ (12 : ℝ) =
          M * (cStar ^ (3 : ℝ))⁻¹ * (nu ^ (4 : ℝ))⁻¹ * Real.log (L : ℝ) ^ (12 : ℝ) *
            (cStar ^ (3 : ℝ) * nu ^ (4 : ℝ)) := by
          field_simp
      _ ≤ (L : ℝ) ^ (1 - alpha) * (cStar ^ (3 : ℝ) * nu ^ (4 : ℝ)) := hmul
      _ = (L : ℝ) ^ (1 - alpha) * cStar ^ (3 : ℝ) * nu ^ (4 : ℝ) := by ring
  have hLalpha_nonneg : (0 : ℝ) ≤ (L : ℝ) ^ alpha := Real.rpow_nonneg hLpos.le _
  have hkey : M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤
      ((L : ℝ) ^ (1 - alpha) * cStar ^ (3 : ℝ) * nu ^ (4 : ℝ) / Real.log (L : ℝ) ^ (12 : ℝ)) *
        (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) := by
    apply mul_le_mul_of_nonneg_right _ hlogL3pos.le
    exact mul_le_mul_of_nonneg_right hMbound hLalpha_nonneg
  have hcStarpos3 : (0 : ℝ) < cStar ^ (3 : ℝ) := Real.rpow_pos_of_pos hcStar _
  have hnupos4 : (0 : ℝ) < nu ^ (4 : ℝ) := Real.rpow_pos_of_pos hnu _
  have hcStarle8 : cStar ^ (3 : ℝ) ≤ 8 := by
    have h3 : (3 : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
    rw [h3, Real.rpow_natCast]
    calc cStar ^ (3 : ℕ) ≤ (2 : ℝ) ^ (3 : ℕ) := pow_le_pow_left₀ hcStar.le hcStar2 3
      _ = 8 := by norm_num
  have hnule1 : nu ^ (4 : ℝ) ≤ 1 := by
    calc nu ^ (4 : ℝ) ≤ (1 : ℝ) ^ (4 : ℝ) := Real.rpow_le_rpow hnu.le hnu1 (by norm_num)
      _ = 1 := Real.one_rpow 4
  have hlogL9pos : (0 : ℝ) < Real.log (L : ℝ) ^ (9 : ℝ) := Real.rpow_pos_of_pos hlogLpos _
  have hrhs_eq : ((L : ℝ) ^ (1 - alpha) * cStar ^ (3 : ℝ) * nu ^ (4 : ℝ) /
      Real.log (L : ℝ) ^ (12 : ℝ)) * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) =
      (L : ℝ) * (cStar ^ (3 : ℝ) * nu ^ (4 : ℝ)) / Real.log (L : ℝ) ^ (9 : ℝ) := by
    have hLpow_split : (L : ℝ) ^ (1 - alpha) * (L : ℝ) ^ alpha = (L : ℝ) := by
      rw [← Real.rpow_add hLpos]
      norm_num
    have hlogpow_split : Real.log (L : ℝ) ^ (12 : ℝ) =
        Real.log (L : ℝ) ^ (9 : ℝ) * Real.log (L : ℝ) ^ (3 : ℝ) := by
      rw [← Real.rpow_add hlogLpos]
      norm_num
    rw [hlogpow_split, div_mul_eq_mul_div, div_mul_eq_mul_div]
    rw [show (L : ℝ) ^ (1 - alpha) * cStar ^ (3 : ℝ) * nu ^ (4 : ℝ) * (L : ℝ) ^ alpha *
          Real.log (L : ℝ) ^ (3 : ℝ) =
        (L : ℝ) ^ (1 - alpha) * (L : ℝ) ^ alpha *
          (cStar ^ (3 : ℝ) * nu ^ (4 : ℝ) * Real.log (L : ℝ) ^ (3 : ℝ)) from by ring,
      hLpow_split]
    rw [show (Real.log (L : ℝ) ^ (9 : ℝ) * Real.log (L : ℝ) ^ (3 : ℝ)) =
        Real.log (L : ℝ) ^ (3 : ℝ) * Real.log (L : ℝ) ^ (9 : ℝ) from by ring,
      ← div_div, mul_div_assoc, mul_div_cancel_right₀ _ hlogL3pos.ne']
  have hfinal_le : (L : ℝ) * (cStar ^ (3 : ℝ) * nu ^ (4 : ℝ)) / Real.log (L : ℝ) ^ (9 : ℝ) ≤
      (L : ℝ) / 2 := by
    rw [div_le_div_iff₀ hlogL9pos (by norm_num : (0 : ℝ) < 2)]
    have h1 : cStar ^ (3 : ℝ) * nu ^ (4 : ℝ) ≤ 8 :=
      le_trans (mul_le_mul_of_nonneg_right hcStarle8 hnupos4.le) (by linarith only [hnule1])
    have h2 : (L : ℝ) * (cStar ^ (3 : ℝ) * nu ^ (4 : ℝ)) * 2 ≤ (L : ℝ) * 8 * 2 := by
      have := mul_le_mul_of_nonneg_left h1 hLpos.le
      nlinarith only [this]
    have h3 : (L : ℝ) * 8 * 2 ≤ (L : ℝ) * Real.log (L : ℝ) ^ (9 : ℝ) := by
      have h4 : (16 : ℝ) ≤ Real.log (L : ℝ) ^ (9 : ℝ) := hlogL9ge16'
      nlinarith only [h4, hLpos]
    linarith only [h2, h3]
  rw [hrhs_eq] at hkey
  linarith only [hkey, hfinal_le]

/-! ## An explicit lower bound on `L₀` itself -/

/-- `L₀` is always past `8`: an explicit instance of the "`L` large" fact used
throughout Section 4 to secure `3 + L ≤ 2L` (`lNaught_threshold`'s second
conjunct) and `\log^9 L ≥ 16` (`lNaught_absorbs`), packaged as a standalone
lower bound on `L₀` itself so downstream proofs need not re-derive it. -/
theorem lNaught_ge :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C →
      ∀ M : ℝ, 1 ≤ M → ∀ alpha : ℝ, 0 ≤ alpha → alpha < 1 →
      ∀ cStar : ℝ, 0 < cStar → cStar ≤ 2 →
      ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
      ∀ K : ℝ, 0 ≤ K →
      (8 : ℝ) < SuperdiffusionCLT.Frozen.Section4.lNaught C M alpha cStar nu K := by
  refine ⟨lNaughtThresholdC0, lNaughtThresholdC0_ge1, ?_⟩
  intro C hC M hM alpha halpha0 halpha1 cStar hcStar hcStar2 nu hnu hnu1 K hK
  obtain ⟨ht0ge1, hpeak, _, _⟩ :=
    lNaught_c0_peak_base12 hM hK hcStar hcStar2 hnu hnu1 halpha0 halpha1
  set t0 := SuperdiffusionCLT.Frozen.Section4.lNaught lNaughtThresholdC0 M alpha cStar nu K
    with ht0def
  have ht0leC : t0 ≤ SuperdiffusionCLT.Frozen.Section4.lNaught C M alpha cStar nu K := by
    rw [ht0def]
    exact SuperdiffusionCLT.Section4.LNaught.lNaught_mono_const
      (le_trans zero_le_one lNaughtThresholdC0_ge1) hC (by linarith only [hM]) hK hcStar hnu
      halpha1
  have ht0pos : 0 < t0 := lt_of_lt_of_le one_pos ht0ge1
  have hlogt0nonneg : 0 ≤ Real.log t0 := Real.log_nonneg ht0ge1
  have hlogt0_ge12 : (12 : ℝ) ≤ Real.log t0 := by
    have hale1 : (1 - alpha) ≤ 1 := by linarith only [halpha0]
    have h1 : (1 - alpha) * Real.log t0 ≤ Real.log t0 :=
      mul_le_of_le_one_left hlogt0nonneg hale1
    linarith only [hpeak, h1]
  have hlog8eq2 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℕ) by norm_num, Real.log_pow]
    push_cast; ring
  have hlog8le3 : Real.log 8 ≤ 3 := by
    rw [hlog8eq2]; linarith only [Real.log_two_lt_d9]
  have ht0_gt8 : (8 : ℝ) < t0 := by
    by_contra hcon
    push Not at hcon
    have h1 : Real.log t0 ≤ Real.log 8 := Real.log_le_log ht0pos hcon
    linarith only [h1, hlog8le3, hlogt0_ge12]
  exact lt_of_lt_of_le ht0_gt8 ht0leC

end SuperdiffusionCLT.Section4.LNaught
