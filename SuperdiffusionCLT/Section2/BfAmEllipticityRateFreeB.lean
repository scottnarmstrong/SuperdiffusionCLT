/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.BfAmEllipticityLevelTailC
public import SuperdiffusionCLT.Section2.BfAmEllipticityScaleTail

/-!
# Absorption arithmetic for the rate-free ellipticity anchor

This module concerns lemma `l.bfAm.ellip`.  The conclusion of lemma `l.bfAm.ellip` carries an
**existential** amplitude constant `C`, so a per-scale decay rate below the printed one is
absorbed by enlarging `C`. This file supplies the two arithmetic clauses `hGeo` and `hAbs`
consumed by `measureReal_minScale_gt_le` at
*any* positive rate `c`, for a large enough amplitude constant `C`:

* `exists_hGeo_large`: `1 ≤ c ((C/3)^γ γ^{-C}) γ log 3`;
* `exists_hAbs_large`: `1 + log 2 + log C + C |log γ|/γ ≤ c ((C/3)^γ γ^{-C})`.

Both hold uniformly over `γ ∈ (0,1)` once `C` is large; the threshold grows like
`1/c²` as `c → 0`. The `γ → 0` regime is carried by the singular part
`C |log γ|/γ` together with `y e^{-y} ≤ 1`; the `γ → 1` regime by the constant
part `1 + log 2 + log C` against the base `C/3`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2

noncomputable section

/-- **The `hGeo` arithmetic clause at any positive rate, for a large enough
amplitude constant.** With `C ≥ 3` and `C ≥ 3 / (c log 3)` the amplitude
`(C/3)^γ γ^{-C}` beats the factor `(c γ log 3)⁻¹`, uniformly over
`γ ∈ (0,1)`. -/
theorem exists_hGeo_large (c : ℝ) (hc : 0 < c) :
    ∃ C0 : ℝ, 3 ≤ C0 ∧ ∀ C : ℝ, C0 ≤ C → ∀ gamma : ℝ, 0 < gamma → gamma < 1 →
      1 ≤ c * ((C / 3) ^ gamma * gamma ^ (-C)) * gamma * Real.log 3 := by
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  refine ⟨max 3 (3 / (c * Real.log 3)), le_max_left _ _, ?_⟩
  intro C hCC gamma hg0 hg1
  have hC3 : (3 : ℝ) ≤ C := le_trans (le_max_left _ _) hCC
  have hCdiv : (0 : ℝ) < C / 3 := by linarith only [hC3]
  have hCbound : 3 ≤ c * C * Real.log 3 := by
    have h2 : 3 / (c * Real.log 3) ≤ C := le_trans (le_max_right _ _) hCC
    have h3 : 0 < c * Real.log 3 := mul_pos hc hlog3
    have h4 : c * Real.log 3 * (3 / (c * Real.log 3)) ≤ c * Real.log 3 * C :=
      mul_le_mul_of_nonneg_left h2 h3.le
    have h5 : c * Real.log 3 * (3 / (c * Real.log 3)) = 3 := by
      field_simp
    rw [h5] at h4
    linarith only [h4]
  -- the key product bound `C / 3 ≤ (C/3)^γ γ^{1-C}`
  have hkey : C / 3 ≤ (C / 3) ^ gamma * gamma ^ (1 - C) := by
    have hlogCsub : Real.log (C / 3) ≤ C - 1 := by
      have h7 : Real.log (C / 3) ≤ C / 3 - 1 := Real.log_le_sub_one_of_pos hCdiv
      linarith only [hC3, h7]
    have h1g : (0 : ℝ) ≤ 1 - gamma := by linarith only [hg1]
    have hC1 : (0 : ℝ) ≤ C - 1 := by linarith only [hC3]
    have hLge : 1 - gamma ≤ -Real.log gamma := by
      have h := Real.log_le_sub_one_of_pos hg0
      linarith only [h]
    have hA : Real.log (C / 3) * (1 - gamma) ≤ (C - 1) * (1 - gamma) :=
      mul_le_mul_of_nonneg_right hlogCsub h1g
    have hB : (C - 1) * (1 - gamma) ≤ (C - 1) * (-Real.log gamma) :=
      mul_le_mul_of_nonneg_left hLge hC1
    have hmain : Real.log (C / 3) ≤
        Real.log (C / 3) * gamma + Real.log gamma * (1 - C) := by
      have hident : Real.log (C / 3) * gamma + Real.log gamma * (1 - C) - Real.log (C / 3) =
          (C - 1) * (-Real.log gamma) - Real.log (C / 3) * (1 - gamma) := by ring
      linarith only [le_trans hA hB, hident]
    calc C / 3 = Real.exp (Real.log (C / 3)) := (Real.exp_log hCdiv).symm
      _ ≤ Real.exp (Real.log (C / 3) * gamma + Real.log gamma * (1 - C)) :=
          Real.exp_le_exp.2 hmain
      _ = (C / 3) ^ gamma * gamma ^ (1 - C) := by
          rw [Real.rpow_def_of_pos hCdiv, Real.rpow_def_of_pos hg0, ← Real.exp_add]
  have h1C : (1 : ℝ) - C = -C + 1 := by ring
  have hgpow : gamma ^ (-C) * gamma = gamma ^ (1 - C) := by
    rw [h1C, Real.rpow_add hg0, Real.rpow_one]
  have hstep : C / 3 ≤ (C / 3) ^ gamma * gamma ^ (-C) * gamma := by
    rw [mul_assoc, hgpow]
    exact hkey
  have h1 : c * Real.log 3 * (C / 3) ≤
      c * Real.log 3 * ((C / 3) ^ gamma * gamma ^ (-C) * gamma) :=
    mul_le_mul_of_nonneg_left hstep (le_of_lt (mul_pos hc hlog3))
  have h2 : 1 ≤ c * Real.log 3 * (C / 3) := by
    have h3 : c * Real.log 3 * (C / 3) = c * C * Real.log 3 / 3 := by ring
    rw [h3]
    linarith only [hCbound]
  calc (1 : ℝ) ≤ c * Real.log 3 * (C / 3) := h2
    _ ≤ c * Real.log 3 * ((C / 3) ^ gamma * gamma ^ (-C) * gamma) := h1
    _ = c * ((C / 3) ^ gamma * gamma ^ (-C)) * gamma * Real.log 3 := by ring

/-! ## The absorption clause `hAbs` at any positive rate

`hAbs` at rate `c` and amplitude constant `C` reads
`1 + log 2 + log C + C |log γ|/γ ≤ c ((C/3)^γ γ^{-C})`. The earlier
level-tail file `BfAmEllipticityLevelTailC` needs
`c ≥ 4.2918` at every `C`. The bound below shows that the
*ratio* of the two sides is below the **slack** `hAbsSlack C`, which is
independent of `γ` and tends to `0` as `C → ∞`; hence `hAbs` at rate `c` holds
for every `c > 0` provided `C` is large enough. The `γ → 1` regime is the
constant part `1 + log 2 + log C` against the base `(C/3)^γ γ^{-C} ≥ C/3 · γ^{-C}`,
which pays `3(1 + log 2 + log C)/C`; the `γ → 0` regime is the singular part
`C|log γ|/γ`, where the *same* base supplies the factor `(3/C)^γ ≤ 3/C`
(`abs_log_div_mul_le_sharp`) and the remainder is `y e^{-y} ≤ 1` at
`y = |log γ| (C-1)/2`, paying `6/(C-1)`. -/

/-- The slack of the absorption clause: `hAbs` at rate `c` holds whenever
`hAbsSlack C ≤ c`. Both parts tend to `0` as `C → ∞`. -/
def hAbsSlack (C : ℝ) : ℝ := 3 * (1 + Real.log 2 + Real.log C) / C + 6 / (C - 1)

/-- The constant part of the slack, `3 (1 + log 2 + log C)/C`, is antitone on
`[1,∞)`: `log C' ≤ log C + (C'/C - 1)` from `log ≤ id - 1`. -/
theorem three_log_div_anti {C C' : ℝ} (hC : 1 ≤ C) (hCC : C ≤ C') :
    3 * (1 + Real.log 2 + Real.log C') / C' ≤ 3 * (1 + Real.log 2 + Real.log C) / C := by
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le zero_lt_one hC
  have hC'0 : (0 : ℝ) < C' := lt_of_lt_of_le hC0 hCC
  have hlogC : (0 : ℝ) ≤ Real.log C := Real.log_nonneg hC
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog : Real.log C' ≤ Real.log C + (C' / C - 1) := by
    have h := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < C' / C)
    rw [Real.log_div (ne_of_gt hC'0) (ne_of_gt hC0)] at h
    linarith only [h]
  have h1 : 1 + Real.log 2 + Real.log C' ≤ Real.log 2 + Real.log C + C' / C := by
    linarith only [hlog]
  have h2 : 3 * (Real.log 2 + Real.log C + C' / C) / C' =
      3 * (Real.log 2 + Real.log C) / C' + 3 / C := by
    field_simp
  have hA : (0 : ℝ) ≤ 3 * (Real.log 2 + Real.log C) := by linarith only [hlogC, hlog2]
  have hstep : 3 * (Real.log 2 + Real.log C) / C' ≤ 3 * (Real.log 2 + Real.log C) / C :=
    div_le_div_of_nonneg_left hA hC0 hCC
  calc 3 * (1 + Real.log 2 + Real.log C') / C'
      ≤ 3 * (Real.log 2 + Real.log C + C' / C) / C' :=
        div_le_div_of_nonneg_right (by linarith only [h1]) hC'0.le
    _ = 3 * (Real.log 2 + Real.log C) / C' + 3 / C := h2
    _ ≤ 3 * (Real.log 2 + Real.log C) / C + 3 / C := by linarith only [hstep]
    _ = 3 * (1 + Real.log 2 + Real.log C) / C := by ring

/-- `6/(C-1)` is antitone on `(1,∞)`. -/
theorem div_pred_anti {C C' : ℝ} (hC : 1 < C) (hCC : C ≤ C') :
    6 / (C' - 1) ≤ 6 / (C - 1) := by
  have hC0 : (0 : ℝ) < C - 1 := by linarith only [hC]
  exact div_le_div_of_nonneg_left (by norm_num) hC0 (by linarith only [hCC])

theorem hAbsSlack_anti {C C' : ℝ} (hC : 3 ≤ C) (hCC : C ≤ C') :
    hAbsSlack C' ≤ hAbsSlack C := by
  have h1 : (1 : ℝ) ≤ C := by linarith only [hC]
  have h2 : (1 : ℝ) < C := by linarith only [hC]
  simp only [hAbsSlack]
  have ha := three_log_div_anti (C := C) (C' := C') h1 hCC
  have hb := div_pred_anti (C := C) (C' := C') h2 hCC
  linarith only [ha, hb]

/-- **The singular part of `hAbs` vanishes.** For `C ≥ 3` and `γ ∈ (0,1)`,
`C|log γ|/γ · (3/C)^γ γ^C ≤ 6/(C-1)`. Writing `b = |log γ|` and `L = log(C/3)` the
left side is exactly `C b e^{-(C-1)b - γL}`; since `γ ≥ 1 - b` (from `log ≤ id - 1`)
and `L ≥ 0`, the exponent is at most `-L - b(C-1)/2` (using `L ≤ (C-1)/2`), and
`e^{-L} = 3/C`, so the bound is `3 b e^{-b(C-1)/2} ≤ 6/(C-1)` by `y e^{-y} ≤ 1`.
The factor `(3/C)^γ` is what makes the constant vanish: it is kept, not discarded. -/
theorem abs_log_div_mul_le_sharp (C gamma : ℝ) (hC : 3 ≤ C) (hg0 : 0 < gamma)
    (hg1 : gamma < 1) :
    C * |Real.log gamma| / gamma * ((3 / C) ^ gamma * gamma ^ C) ≤ 6 / (C - 1) := by
  have hC0 : 0 < C := by linarith only [hC]
  have hC1 : 0 < C - 1 := by linarith only [hC]
  set b : ℝ := -Real.log gamma with hb
  have hlogg : Real.log gamma = -b := by rw [hb]; ring
  have hb0 : (0 : ℝ) ≤ b := by
    rw [hb, neg_nonneg]
    exact Real.log_nonpos hg0.le hg1.le
  have habs : |Real.log gamma| = b := by
    rw [hlogg, abs_neg]
    exact abs_of_nonneg hb0
  have hL0 : (0 : ℝ) ≤ Real.log (C / 3) := Real.log_nonneg (by linarith only [hC])
  have hL : Real.log (C / 3) ≤ (C - 1) / 2 := by
    have h := Real.log_le_sub_one_of_pos (by linarith only [hC] : (0 : ℝ) < C / 3)
    linarith only [h, hC]
  have hL3 : Real.log (3 / C) = -Real.log (C / 3) := by
    rw [Real.log_div (by norm_num) (ne_of_gt hC0), Real.log_div (ne_of_gt hC0) (by norm_num)]
    ring
  have hinv : gamma⁻¹ = Real.exp b := by
    rw [hb, Real.exp_neg, Real.exp_log hg0]
  have hgammab : 1 - b ≤ gamma := by
    have h := Real.log_le_sub_one_of_pos hg0
    rw [hlogg] at h
    linarith only [h]
  have hform : C * b / gamma * ((3 / C) ^ gamma * gamma ^ C) =
      C * b * Real.exp (-(C - 1) * b - gamma * Real.log (C / 3)) := by
    have h1 : C * b / gamma * ((3 / C) ^ gamma * gamma ^ C) =
        C * b * (Real.exp b *
          (Real.exp (-Real.log (C / 3) * gamma) * Real.exp (Real.log gamma * C))) := by
      rw [div_eq_mul_inv, hinv,
        Real.rpow_def_of_pos (div_pos (by norm_num) (by linarith only [hC])) gamma,
        Real.rpow_def_of_pos hg0 C, hL3]
      ring
    have h2 : Real.exp b *
        (Real.exp (-Real.log (C / 3) * gamma) * Real.exp (Real.log gamma * C)) =
        Real.exp (-(C - 1) * b - gamma * Real.log (C / 3)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      rw [hlogg]
      ring
    rw [h1, h2]
  have hmain : Real.exp (-(C - 1) * b - gamma * Real.log (C / 3)) ≤
      Real.exp (-Real.log (C / 3)) * Real.exp (-(b * (C - 1) / 2)) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have h1 : (1 - b) * Real.log (C / 3) ≤ gamma * Real.log (C / 3) :=
      mul_le_mul_of_nonneg_right hgammab hL0
    have h2 : b * ((C - 1) / 2) ≤ b * (C - 1 - Real.log (C / 3)) :=
      mul_le_mul_of_nonneg_left (by linarith only [hL]) hb0
    linarith only [h1, h2]
  have hCb : (0 : ℝ) ≤ C * b := mul_nonneg (by linarith only [hC]) hb0
  calc C * |Real.log gamma| / gamma * ((3 / C) ^ gamma * gamma ^ C)
      = C * b / gamma * ((3 / C) ^ gamma * gamma ^ C) := by rw [habs]
    _ = C * b * Real.exp (-(C - 1) * b - gamma * Real.log (C / 3)) := hform
    _ ≤ C * b * (Real.exp (-Real.log (C / 3)) * Real.exp (-(b * (C - 1) / 2))) :=
        mul_le_mul_of_nonneg_left hmain hCb
    _ = (C * Real.exp (-Real.log (C / 3))) * (b * Real.exp (-(b * (C - 1) / 2))) := by ring
    _ = 3 * (b * Real.exp (-(b * (C - 1) / 2))) := by
        have he : C * Real.exp (-Real.log (C / 3)) = 3 := by
          rw [Real.exp_neg, Real.exp_log (by linarith only [hC] : (0 : ℝ) < C / 3)]
          field_simp
        rw [he]
    _ ≤ 6 / (C - 1) := by
        have hle : b * Real.exp (-(b * (C - 1) / 2)) ≤ 2 / (C - 1) := by
          have h := y_mul_exp_neg_le_one (b * (C - 1) / 2)
          rw [show b * (C - 1) / 2 * Real.exp (-(b * (C - 1) / 2)) =
              b * Real.exp (-(b * (C - 1) / 2)) * (C - 1) / 2 from by ring,
            div_le_iff₀ (by norm_num : (0 : ℝ) < 2)] at h
          rw [le_div_iff₀ hC1]
          linarith only [h]
        have h3 := mul_le_mul_of_nonneg_left hle (by norm_num : (0 : ℝ) ≤ 3)
        have he : 3 * (2 / (C - 1)) = 6 / (C - 1) := by ring
        linarith only [h3, he]

/-- **The absorption clause is bounded by the slack.** For every `C ≥ 3` and
`γ ∈ (0,1)`, the left side of `hAbs` is at most `hAbsSlack C` times the base
`(C/3)^γ γ^{-C}`. -/
theorem hAbs_aux_bound (C gamma : ℝ) (hC : 3 ≤ C) (hg0 : 0 < gamma) (hg1 : gamma < 1) :
    1 + Real.log 2 + Real.log C + C * |Real.log gamma| / gamma ≤
      hAbsSlack C * ((C / 3) ^ gamma * gamma ^ (-C)) := by
  have hC0 : 0 < C := by linarith only [hC]
  have hXpos : 0 < (C / 3) ^ gamma * gamma ^ (-C) :=
    mul_pos (Real.rpow_pos_of_pos (by linarith only [hC]) gamma)
      (Real.rpow_pos_of_pos hg0 (-C))
  have hcross : (3 / C) ^ gamma * (C / 3) ^ gamma = 1 := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    have h : (3 / C) * (C / 3) = 1 := by field_simp
    rw [h, Real.one_rpow]
  have hgg : gamma ^ C * gamma ^ (-C) = 1 := by
    rw [← Real.rpow_add hg0]
    rw [show C + -C = 0 from by ring, Real.rpow_zero]
  have hYX : ((3 / C) ^ gamma * gamma ^ C) * ((C / 3) ^ gamma * gamma ^ (-C)) = 1 := by
    rw [mul_mul_mul_comm, hcross, hgg, mul_one]
  have hlogC : (0 : ℝ) ≤ Real.log C := Real.log_nonneg (by linarith only [hC])
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hA : (0 : ℝ) ≤ 1 + Real.log 2 + Real.log C := by linarith only [hlogC, hlog2]
  have hterm1 : (1 + Real.log 2 + Real.log C) * ((3 / C) ^ gamma * gamma ^ C) ≤
      3 * (1 + Real.log 2 + Real.log C) / C := by
    have h := mul_le_mul_of_nonneg_left (rpow_ratio_mul_rpow_le_c C gamma hC hg0 hg1) hA
    have he : (1 + Real.log 2 + Real.log C) * (3 / C) =
        3 * (1 + Real.log 2 + Real.log C) / C := by ring
    linarith only [h, he]
  have hterm2 : C * |Real.log gamma| / gamma * ((3 / C) ^ gamma * gamma ^ C) ≤ 6 / (C - 1) :=
    abs_log_div_mul_le_sharp C gamma hC hg0 hg1
  have hsum : (1 + Real.log 2 + Real.log C + C * |Real.log gamma| / gamma) *
      ((3 / C) ^ gamma * gamma ^ C) ≤ hAbsSlack C := by
    have hsplit : (1 + Real.log 2 + Real.log C + C * |Real.log gamma| / gamma) *
        ((3 / C) ^ gamma * gamma ^ C) =
        (1 + Real.log 2 + Real.log C) * ((3 / C) ^ gamma * gamma ^ C) +
          (C * |Real.log gamma| / gamma) * ((3 / C) ^ gamma * gamma ^ C) := by ring
    rw [hsplit, hAbsSlack]
    linarith only [hterm1, hterm2]
  have hmul := mul_le_mul_of_nonneg_right hsum hXpos.le
  rw [mul_assoc, hYX, mul_one] at hmul
  exact hmul

/-- The slack is at most `c` once `N` is large: the three explicit constraints
`12(1 + log 2) ≤ cN`, `576 ≤ c² N`, `12 ≤ c(N-1)` suffice. The middle one controls
the logarithmic part through `log N ≤ 2√N`, i.e. it only needs `c√N ≥ 24`. -/
theorem hAbsSlack_le_of {c N : ℝ} (hc : 0 < c) (hN1 : 1 < N)
    (h1 : 12 * (1 + Real.log 2) ≤ c * N) (h2 : 576 ≤ c ^ 2 * N)
    (h3 : 12 ≤ c * (N - 1)) : hAbsSlack N ≤ c := by
  have hN0 : (0 : ℝ) < N := by linarith only [hN1]
  have hlogN : Real.log N ≤ 2 * Real.sqrt N := by
    have h := Real.log_le_rpow_div hN0.le (show (0 : ℝ) < 1 / 2 by norm_num)
    have he : N ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) = 2 * N ^ (1 / 2 : ℝ) := by ring
    rw [he] at h
    rwa [Real.sqrt_eq_rpow]
  have hspos : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hsqrt : 24 ≤ c * Real.sqrt N := by
    have hsq : (24 : ℝ) ^ 2 ≤ (c * Real.sqrt N) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hN0.le]
      linarith only [h2]
    have h := (sq_le_sq).1 hsq
    rwa [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 24),
      abs_of_nonneg (mul_nonneg hc.le hspos.le)] at h
  have hA : 3 * (1 + Real.log 2) / N ≤ c / 4 := by
    rw [div_le_iff₀ hN0]
    linarith only [h1]
  have hB : 3 * Real.log N / N ≤ c / 4 := by
    rw [div_le_iff₀ hN0]
    have hm : 24 * Real.sqrt N ≤ c * N := by
      have h := mul_le_mul_of_nonneg_right hsqrt hspos.le
      have h' : 24 * Real.sqrt N ≤ c * (Real.sqrt N * Real.sqrt N) := by
        calc 24 * Real.sqrt N ≤ (c * Real.sqrt N) * Real.sqrt N := h
          _ = c * (Real.sqrt N * Real.sqrt N) := by ring
      rwa [Real.mul_self_sqrt hN0.le] at h'
    have h3N : 3 * Real.log N ≤ 6 * Real.sqrt N := by linarith only [hlogN]
    linarith only [h3N, hm]
  have hC : 6 / (N - 1) ≤ c / 2 := by
    have hN1' : (0 : ℝ) < N - 1 := by linarith only [hN1]
    rw [div_le_iff₀ hN1']
    linarith only [h3]
  have hp : 3 * (1 + Real.log 2 + Real.log N) / N =
      3 * (1 + Real.log 2) / N + 3 * Real.log N / N := by ring
  rw [hAbsSlack, hp]
  linarith only [hA, hB, hC]

/-- **`hAbs` at any positive rate, for a large enough amplitude constant.** The
threshold `C₀ = 576/c² + 12(1 + log 2)/c + 3 ≥ 3` satisfies the clause, and by
`hAbsSlack_anti` so does every larger `C`. The constant grows as `c → 0` (like
`1/c²`), and is uniform in `γ` and in `d`. -/
theorem exists_hAbs_large (c : ℝ) (hc : 0 < c) :
    ∃ C0 : ℝ, 3 ≤ C0 ∧ ∀ C : ℝ, C0 ≤ C → ∀ gamma : ℝ, 0 < gamma → gamma < 1 →
      1 + Real.log 2 + Real.log C + C * |Real.log gamma| / gamma ≤
        c * ((C / 3) ^ gamma * gamma ^ (-C)) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2' : (0 : ℝ) < 1 + Real.log 2 := by linarith only [hlog2]
  set N : ℝ := 576 / c ^ 2 + 12 * (1 + Real.log 2) / c + 3 with hN
  have ha0 : (0 : ℝ) ≤ 576 / c ^ 2 := div_nonneg (by norm_num) (sq_nonneg c)
  have hb0 : (0 : ℝ) ≤ 12 * (1 + Real.log 2) / c := div_nonneg (by linarith only [hlog2]) hc.le
  have hN1 : (1 : ℝ) < N := by rw [hN]; linarith only [ha0, hb0]
  have hN3 : (3 : ℝ) ≤ N := by rw [hN]; linarith only [ha0, hb0]
  have hca : (0 : ℝ) ≤ 576 / c := div_nonneg (by norm_num) hc.le
  have hcl : c * N = 576 / c + 12 * (1 + Real.log 2) + 3 * c := by
    rw [hN]
    field_simp
  have hcm : c ^ 2 * N = 576 + 12 * (1 + Real.log 2) * c + 3 * c ^ 2 := by
    rw [hN]
    field_simp
  have hcp : c * (N - 1) = 576 / c + 12 * (1 + Real.log 2) + 2 * c := by
    rw [hN]
    field_simp
    ring
  have h1 : 12 * (1 + Real.log 2) ≤ c * N := by
    rw [hcl]
    have hc' : (0 : ℝ) ≤ 3 * c := mul_nonneg (by norm_num) hc.le
    linarith only [hca, hc']
  have h2 : 576 ≤ c ^ 2 * N := by
    rw [hcm]
    have ha : (0 : ℝ) ≤ 12 * (1 + Real.log 2) * c := mul_nonneg (by linarith only [hlog2]) hc.le
    have hc' : (0 : ℝ) ≤ 3 * c ^ 2 := mul_nonneg (by norm_num) (sq_nonneg c)
    linarith only [ha, hc']
  have h3 : 12 ≤ c * (N - 1) := by
    rw [hcp]
    have hc' : (0 : ℝ) ≤ 2 * c := mul_nonneg (by norm_num) hc.le
    linarith only [hca, hc', hlog2]
  refine ⟨N, hN3, ?_⟩
  intro C hNC gamma hg0 hg1
  have hC3 : (3 : ℝ) ≤ C := le_trans hN3 hNC
  have hslack : hAbsSlack C ≤ c :=
    le_trans (hAbsSlack_anti (C := N) (C' := C) hN3 hNC) (hAbsSlack_le_of hc hN1 h1 h2 h3)
  have hbound := hAbs_aux_bound C gamma hC3 hg0 hg1
  have hX : (0 : ℝ) ≤ (C / 3) ^ gamma * gamma ^ (-C) :=
    mul_nonneg (Real.rpow_nonneg (by linarith only [hC3]) gamma) (Real.rpow_nonneg hg0.le (-C))
  exact le_trans hbound (mul_le_mul_of_nonneg_right hslack hX)

end

end SuperdiffusionCLT.Section2
