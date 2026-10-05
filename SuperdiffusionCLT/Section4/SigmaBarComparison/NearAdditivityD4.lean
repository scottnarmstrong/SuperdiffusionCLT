/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Frozen.Section4.LNaught
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Near-additivity, the scale arithmetic

Elementary consequences of `lNaught Cth (Cth * M) alpha cStar nu K ≤ ell` for
every `Cth ≥ 1` (not only for a large threshold constant):

* `sbNear_lNaught_ge`: `lNaught ≥ (a M ν⁻⁴ (1-α)⁻¹²)^{1/(1-α)}` with
  `a = (log 2)^12 / 8`;
* `sbNear_nu_le`: `a ν⁻⁴ ≤ L`;
* `sbNear_caseB`: when the witness `n = ell - ⌈200 log L⌉` is truncated at `0`
  (`ell < 200 log L + 1`), the scale is bounded, `L ≤ L*`, by a universal
  constant (the scale constraint `L - M L^α log³ L ≤ ell` forces
  `(1-α) log L ≲ log M + log log L`, and `lNaught ≤ ell` bounds both `M` and
  `1/(1-α)` by `O(log L)`);
* `sbNear_absorb_arith`: `ν⁻³ L 3^{-(ell-n)} ≤ B L^{-99}` at the witness, with
  `B` universal (the untruncated branch uses `3^{200 log L} ≥ L^101`).

The source absorbs these losses with `e.L.vs.Lnaught` at a large threshold
constant; here every `Cth ≥ 1` is covered, as `hNearAdd` requires.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.SigmaBarComparison

noncomputable section

/-- The constant `a = (log 2)^12 / 8`. -/
def sbNear_a : ℝ := Real.log 2 ^ (12 : ℝ) / 8

theorem sbNear_a_pos : 0 < sbNear_a :=
  div_pos (Real.rpow_pos_of_pos (Real.log_pos (by norm_num)) _) (by norm_num)

theorem sbNear_a_le_one : sbNear_a ≤ 1 := by
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
    linarith only [this]
  have h0 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have h12 : Real.log 2 ^ (12 : ℝ) ≤ 1 := by
    calc Real.log 2 ^ (12 : ℝ) ≤ (1 : ℝ) ^ (12 : ℝ) :=
          Real.rpow_le_rpow h0 hlog2.le (by norm_num)
      _ = 1 := Real.one_rpow _
  unfold sbNear_a
  linarith only [h12]

private theorem sbNear_cStar_rpow_ge {cStar : ℝ} (hc : 0 < cStar) (hc2 : cStar ≤ 2) :
    (1 / 8 : ℝ) ≤ cStar ^ (-(3 : ℝ)) := by
  have h := Real.rpow_le_rpow_of_nonpos hc hc2 (by norm_num : (-(3 : ℝ)) ≤ 0)
  have h2 : (2 : ℝ) ^ (-(3 : ℝ)) = 1 / 8 := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
    norm_num
  rw [h2] at h
  exact h

/-- **The lower bound on `lNaught`**, valid for every `Cth ≥ 1`. -/
theorem sbNear_lNaught_ge {Cth M alpha cStar nu K : ℝ} (hC : 1 ≤ Cth) (hM : 1 ≤ M)
    (hα1 : alpha < 1) (hc : 0 < cStar) (hc2 : cStar ≤ 2) (hnu : 0 < nu) (hK : 0 ≤ K) :
    (sbNear_a * M / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ))) ^ ((1 : ℝ) / (1 - alpha)) ≤
      SuperdiffusionCLT.Frozen.Section4.lNaught Cth (Cth * M) alpha cStar nu K := by
  unfold SuperdiffusionCLT.Frozen.Section4.lNaught
  have hγ : 0 < 1 - alpha := by linarith only [hα1]
  have hD : 0 < (1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ) :=
    mul_pos (Real.rpow_pos_of_pos hγ _) (Real.rpow_pos_of_pos hnu _)
  have hc3 := sbNear_cStar_rpow_ge hc hc2
  have hc3pos : 0 < cStar ^ (-(3 : ℝ)) := Real.rpow_pos_of_pos hc _
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hCM : M ≤ Cth * M := le_mul_of_one_le_left hM0 hC
  have hsum : M ≤ Cth * (Cth * M + 1 + K) := by
    have h1 : Cth * M ≤ Cth * M + 1 + K := by linarith only [hK]
    have h2 : Cth * M + 1 + K ≤ Cth * (Cth * M + 1 + K) :=
      le_mul_of_one_le_left (by linarith only [h1, hCM, hM0]) hC
    linarith only [hCM, h1, h2]
  have hnum : M * (1 / 8 : ℝ) ≤ Cth * (Cth * M + 1 + K) * cStar ^ (-(3 : ℝ)) :=
    mul_le_mul hsum hc3 (by norm_num) (le_trans hM0 hsum)
  have hx : 0 ≤ (Cth * M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha)) := by
    have : 0 ≤ Cth * M + 1 + K := by nlinarith only [hC, hM, hK]
    positivity
  have hlog : Real.log 2 ^ (12 : ℝ) ≤
      Real.log (2 + (Cth * M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) :=
    Real.rpow_le_rpow (Real.log_pos (by norm_num)).le
      (Real.log_le_log (by norm_num) (by linarith only [hx])) (by norm_num)
  have hinner : sbNear_a * M / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) ≤
      Cth * (Cth * M + 1 + K) * cStar ^ (-(3 : ℝ)) /
          ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) *
        Real.log (2 + (Cth * M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) := by
    have heq : sbNear_a * M / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) =
        M * (1 / 8 : ℝ) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) * Real.log 2 ^ (12 : ℝ) := by
      unfold sbNear_a; ring
    rw [heq]
    exact mul_le_mul (div_le_div_of_nonneg_right hnum hD.le) hlog
      (Real.rpow_nonneg (Real.log_pos (by norm_num)).le _)
      (div_nonneg (le_trans (by positivity) hnum) hD.le)
  exact Real.rpow_le_rpow (div_nonneg (mul_nonneg sbNear_a_pos.le hM0) hD.le) hinner
    (div_nonneg zero_le_one hγ.le)

/-- `a ν⁻⁴ ≤ L` whenever `lNaught ≤ L` and `L ≥ 1`. -/
theorem sbNear_nu_le {Cth M alpha cStar nu K L : ℝ} (hC : 1 ≤ Cth) (hM : 1 ≤ M)
    (hα0 : 0 ≤ alpha) (hα1 : alpha < 1) (hc : 0 < cStar) (hc2 : cStar ≤ 2) (hnu : 0 < nu)
    (hK : 0 ≤ K) (hL1 : 1 ≤ L)
    (hL : SuperdiffusionCLT.Frozen.Section4.lNaught Cth (Cth * M) alpha cStar nu K ≤ L) :
    sbNear_a / nu ^ (4 : ℝ) ≤ L := by
  have hγ : 0 < 1 - alpha := by linarith only [hα1]
  have hγ1 : 1 - alpha ≤ 1 := by linarith only [hα0]
  have hγ12pos : 0 < (1 - alpha) ^ (12 : ℝ) := Real.rpow_pos_of_pos hγ _
  have hγ12 : (1 - alpha) ^ (12 : ℝ) ≤ 1 := Real.rpow_le_one hγ.le hγ1 (by norm_num)
  have hnu4 : 0 < nu ^ (4 : ℝ) := Real.rpow_pos_of_pos hnu _
  set Y := sbNear_a * M / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) with hYdef
  have hYge : sbNear_a / nu ^ (4 : ℝ) ≤ Y := by
    rw [hYdef, div_le_div_iff₀ hnu4 (mul_pos hγ12pos hnu4)]
    have ha := sbNear_a_pos
    have h1 : sbNear_a * ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) ≤ sbNear_a * nu ^ (4 : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ ha.le
      nlinarith only [hγ12, hnu4]
    have h2 : sbNear_a * nu ^ (4 : ℝ) ≤ sbNear_a * M * nu ^ (4 : ℝ) := by
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM ha.le) hnu4.le
      simpa only [mul_one] using this
    linarith only [h1, h2]
  have hYL : Y ^ ((1 : ℝ) / (1 - alpha)) ≤ L :=
    (sbNear_lNaught_ge hC hM hα1 hc hc2 hnu hK).trans hL
  rcases le_or_gt 1 Y with hY1 | hY1
  · have hexp : (1 : ℝ) ≤ 1 / (1 - alpha) := by
      rw [le_div_iff₀ hγ]; linarith only [hγ1]
    have h := Real.rpow_le_rpow_of_exponent_le hY1 hexp
    rw [Real.rpow_one] at h
    linarith only [hYge, h, hYL]
  · linarith only [hYge, hY1, hL1]

private theorem sbNear_log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h1 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 := Real.log_le_sub_one_of_pos hs
  have h2 : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hx.le
  rw [h2] at h1
  linarith only [h1]

private theorem sbNear_log_le_four_rpow {s : ℝ} (hs : 1 ≤ s) :
    Real.log s ≤ 4 * s ^ ((1 : ℝ) / 4) ∧ 1 ≤ s ^ ((1 : ℝ) / 4) ∧
      (s ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) = s := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hq1 : 1 ≤ s ^ ((1 : ℝ) / 4) := Real.one_le_rpow hs (by norm_num)
  have hqpos : 0 < s ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hs0 _
  have hlogq : Real.log (s ^ ((1 : ℝ) / 4)) = (1 / 4) * Real.log s := Real.log_rpow hs0 _
  have h1 : Real.log (s ^ ((1 : ℝ) / 4)) ≤ s ^ ((1 : ℝ) / 4) - 1 :=
    Real.log_le_sub_one_of_pos hqpos
  refine ⟨by linarith only [h1, hlogq], hq1, ?_⟩
  rw [← Real.rpow_natCast, ← Real.rpow_mul hs0.le]
  norm_num

/-- The constant `K0 = (log(402/a) + 16)(e/a + log 201 + 4)`. -/
def sbNear_K0 : ℝ :=
  (Real.log (402 / sbNear_a) + 16) * (Real.exp 1 / sbNear_a + Real.log 201 + 4)

/-- The threshold `L*` beyond which the truncated branch of the witness is impossible. -/
def sbNear_Lstar : ℝ := max (806 ^ 2) (Real.exp (sbNear_K0 ^ 2))

private theorem sbNear_caseB_M {M alpha ell s : ℝ} (hM : 1 ≤ M) (hα0 : 0 ≤ alpha)
    (hα1 : alpha < 1) (hs : 1 ≤ s)
    (hZ : (sbNear_a * M / (1 - alpha) ^ (12 : ℝ)) ^ ((1 : ℝ) / (1 - alpha)) ≤ ell)
    (hell : ell < 200 * s + 1) :
    sbNear_a * M ≤ 201 * s := by
  have hγ : 0 < 1 - alpha := by linarith only [hα1]
  have hγ1 : 1 - alpha ≤ 1 := by linarith only [hα0]
  have hγ12pos : 0 < (1 - alpha) ^ (12 : ℝ) := Real.rpow_pos_of_pos hγ _
  have hγ12 : (1 - alpha) ^ (12 : ℝ) ≤ 1 := Real.rpow_le_one hγ.le hγ1 (by norm_num)
  have haM : 0 ≤ sbNear_a * M := mul_nonneg sbNear_a_pos.le (le_trans zero_le_one hM)
  have hZge : sbNear_a * M ≤ sbNear_a * M / (1 - alpha) ^ (12 : ℝ) := by
    rw [le_div_iff₀ hγ12pos]
    exact mul_le_of_le_one_right haM hγ12
  rcases le_or_gt 1 (sbNear_a * M / (1 - alpha) ^ (12 : ℝ)) with hZ1 | hZ1
  · have hexp : (1 : ℝ) ≤ 1 / (1 - alpha) := by
      rw [le_div_iff₀ hγ]; linarith only [hγ1]
    have h := Real.rpow_le_rpow_of_exponent_le hZ1 hexp
    rw [Real.rpow_one] at h
    linarith only [hZge, h, hZ, hell, hs]
  · linarith only [hZge, hZ1, hs]

private theorem sbNear_caseB_gamma {M alpha L : ℝ} (hL : 0 < L) (hs : 1 ≤ Real.log L)
    (hMs : sbNear_a * M ≤ 201 * Real.log L)
    (hhalf : L / 2 ≤ M * L ^ alpha * Real.log L ^ (3 : ℝ)) :
    (1 - alpha) * Real.log L ≤
      Real.log (402 / sbNear_a) + 4 * Real.log (Real.log L) := by
  set s := Real.log L with hsdef
  have ha := sbNear_a_pos
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hLα : 0 < L ^ alpha := Real.rpow_pos_of_pos hL _
  have hsplit : L = L ^ alpha * L ^ (1 - alpha) := by
    rw [← Real.rpow_add hL, add_sub_cancel, Real.rpow_one]
  have hs3 : s ^ (3 : ℝ) = s ^ (3 : ℕ) := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hs3] at hhalf
  have hLγ : L ^ (1 - alpha) ≤ 2 * M * s ^ 3 := by
    have h1 : L ^ alpha * L ^ (1 - alpha) ≤ L ^ alpha * (2 * M * s ^ 3) := by
      rw [← hsplit]; nlinarith only [hhalf]
    exact le_of_mul_le_mul_left h1 hLα
  have hM : M ≤ 201 * s / sbNear_a := by rw [le_div_iff₀ ha]; linarith only [hMs]
  have hLγ2 : L ^ (1 - alpha) ≤ 402 / sbNear_a * s ^ 4 := by
    have hs3pos : 0 ≤ s ^ 3 := by positivity
    have h := mul_le_mul_of_nonneg_right hM (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hs3pos)
    have heq : 201 * s / sbNear_a * (2 * s ^ 3) = 402 / sbNear_a * s ^ 4 := by ring
    nlinarith only [hLγ, h, heq]
  have hpos : 0 < L ^ (1 - alpha) := Real.rpow_pos_of_pos hL _
  have hlog := Real.log_le_log hpos hLγ2
  rw [Real.log_rpow hL, Real.log_mul (by positivity) (by positivity), Real.log_pow] at hlog
  push_cast at hlog
  linarith only [hlog]

private theorem sbNear_caseB_inv {M alpha ell s : ℝ} (hM : 1 ≤ M) (hα0 : 0 ≤ alpha)
    (hα1 : alpha < 1) (hs : 1 ≤ s)
    (hZ : (sbNear_a * M / (1 - alpha) ^ (12 : ℝ)) ^ ((1 : ℝ) / (1 - alpha)) ≤ ell)
    (hell : ell < 201 * s) :
    1 / (1 - alpha) ≤ Real.exp 1 / sbNear_a + Real.log (201 * s) := by
  have ha := sbNear_a_pos
  have hγ : 0 < 1 - alpha := by linarith only [hα1]
  have hγ1 : 1 - alpha ≤ 1 := by linarith only [hα0]
  have hγ12pos : 0 < (1 - alpha) ^ (12 : ℝ) := Real.rpow_pos_of_pos hγ _
  have hlog0 : 0 ≤ Real.log (201 * s) := Real.log_nonneg (by linarith only [hs])
  have hea : 0 < Real.exp 1 / sbNear_a := div_pos (Real.exp_pos 1) ha
  rcases le_or_gt (Real.exp 1) (sbNear_a * M / (1 - alpha) ^ (12 : ℝ)) with hZe | hZe
  · have h := Real.rpow_le_rpow (Real.exp_pos 1).le hZe (div_nonneg zero_le_one hγ.le)
    rw [Real.exp_one_rpow] at h
    have h2 : Real.exp (1 / (1 - alpha)) < 201 * s := by linarith only [h, hZ, hell]
    have h3 := (Real.lt_log_iff_exp_lt (by linarith only [hs])).mpr h2
    linarith only [h3, hea]
  · have hγ12 : (1 - alpha) ^ (12 : ℝ) ≤ 1 - alpha := by
      have := Real.rpow_le_rpow_of_exponent_ge hγ hγ1 (by norm_num : (1 : ℝ) ≤ 12)
      rwa [Real.rpow_one] at this
    have haZ : sbNear_a / (1 - alpha) ^ (12 : ℝ) ≤ sbNear_a * M / (1 - alpha) ^ (12 : ℝ) :=
      div_le_div_of_nonneg_right (le_mul_of_one_le_right ha.le hM) hγ12pos.le
    have h1 : sbNear_a < Real.exp 1 * (1 - alpha) ^ (12 : ℝ) := by
      rw [← div_lt_iff₀ hγ12pos]; linarith only [haZ, hZe]
    have h2 : sbNear_a < Real.exp 1 * (1 - alpha) := by
      nlinarith only [h1, hγ12, Real.exp_pos 1]
    have h3 : 1 / (1 - alpha) < Real.exp 1 / sbNear_a := by
      rw [div_lt_div_iff₀ hγ ha]; linarith only [h2]
    linarith only [h3, hlog0]

private theorem sbNear_caseB_log {M alpha ell L : ℝ} (hM : 1 ≤ M) (hα0 : 0 ≤ alpha)
    (hα1 : alpha < 1) (hL : 0 < L) (hs : 1 ≤ Real.log L)
    (hZ : (sbNear_a * M / (1 - alpha) ^ (12 : ℝ)) ^ ((1 : ℝ) / (1 - alpha)) ≤ ell)
    (hell : ell < 200 * Real.log L + 1)
    (hhalf : L / 2 ≤ M * L ^ alpha * Real.log L ^ (3 : ℝ)) :
    Real.log L ≤ sbNear_K0 ^ 2 := by
  set s := Real.log L with hsdef
  have ha := sbNear_a_pos
  have hγ : 0 < 1 - alpha := by linarith only [hα1]
  have hMs := sbNear_caseB_M hM hα0 hα1 hs hZ hell
  have hgs := sbNear_caseB_gamma hL hs hMs hhalf
  have hinv := sbNear_caseB_inv hM hα0 hα1 hs hZ (by linarith only [hell, hs])
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  rw [Real.log_mul (by norm_num) hs0.ne'] at hinv
  obtain ⟨hp4, hq1, hq4⟩ := sbNear_log_le_four_rpow hs
  set q := s ^ ((1 : ℝ) / 4) with hqdef
  set p := Real.log s with hpdef
  have hp0 : 0 ≤ p := Real.log_nonneg hs
  have hA : 0 ≤ Real.log (402 / sbNear_a) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ ha]
    linarith only [sbNear_a_le_one]
  have hB : 0 ≤ Real.exp 1 / sbNear_a + Real.log 201 :=
    add_nonneg (div_pos (Real.exp_pos 1) ha).le (Real.log_nonneg (by norm_num))
  -- `s = (γ s) (1/γ) ≤ (A + 4p)(B + p)`
  have hsle : s ≤ (Real.log (402 / sbNear_a) + 4 * p) *
      (Real.exp 1 / sbNear_a + Real.log 201 + p) := by
    have heq : s = ((1 - alpha) * s) * (1 / (1 - alpha)) := by field_simp
    rw [heq]
    exact mul_le_mul hgs (by linarith only [hinv]) (by positivity)
      (by linarith only [hA, hp0])
  -- `(A + 4p)(B + p) ≤ K0 q²`
  have h1 : Real.log (402 / sbNear_a) + 4 * p ≤ (Real.log (402 / sbNear_a) + 16) * q := by
    nlinarith only [hA, hq1, hp4]
  have h2 : Real.exp 1 / sbNear_a + Real.log 201 + p ≤
      (Real.exp 1 / sbNear_a + Real.log 201 + 4) * q := by
    nlinarith only [hB, hq1, hp4]
  have hK : s ≤ sbNear_K0 * q ^ 2 := by
    have := mul_le_mul h1 h2 (by linarith only [hB, hp0]) (by positivity)
    unfold sbNear_K0
    nlinarith only [hsle, this]
  have hq2pos : 0 < q ^ 2 := by positivity
  have hq2 : q ^ 2 ≤ sbNear_K0 := by
    have hs4 : q ^ 2 * q ^ 2 ≤ sbNear_K0 * q ^ 2 := by
      have : q ^ 2 * q ^ 2 = s := by rw [← hq4]; ring
      linarith only [this, hK]
    exact le_of_mul_le_mul_right hs4 hq2pos
  have : s = q ^ 2 * q ^ 2 := by rw [← hq4]; ring
  rw [this]
  nlinarith only [hq2, hq2pos]

/-- **The truncated branch forces a bounded scale**: if `ell < 200 log L + 1`,
then `L ≤ L*`, a universal constant. -/
theorem sbNear_caseB {M alpha ell L : ℝ} (hM : 1 ≤ M) (hα0 : 0 ≤ alpha) (hα1 : alpha < 1)
    (hL1 : 1 ≤ L)
    (hZ : (sbNear_a * M / (1 - alpha) ^ (12 : ℝ)) ^ ((1 : ℝ) / (1 - alpha)) ≤ ell)
    (hell : ell < 200 * Real.log L + 1)
    (hscale : L - M * L ^ alpha * Real.log L ^ (3 : ℝ) ≤ ell) :
    L ≤ sbNear_Lstar := by
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  rcases le_or_gt L (806 ^ 2) with hsmall | hbig
  · exact hsmall.trans (le_max_left _ _)
  have hs : 1 ≤ Real.log L := by
    rw [Real.le_log_iff_exp_le hL]
    have := Real.exp_one_lt_d9
    nlinarith only [this, hbig]
  rcases lt_or_ge (L / 2) (200 * Real.log L + 1) with hhalf | hhalf
  · exfalso
    have hlog := sbNear_log_le_two_sqrt hL
    have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL.le
    have hsqpos : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
    have h806 : 806 < Real.sqrt L := by
      rw [show (806 : ℝ) = Real.sqrt (806 ^ 2) by
        rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_lt_sqrt (by norm_num) hbig
    nlinarith only [hhalf, hlog, hsq, h806, hs]
  · have hhalf' : L / 2 ≤ M * L ^ alpha * Real.log L ^ (3 : ℝ) := by
      linarith only [hhalf, hscale, hell]
    have := sbNear_caseB_log hM hα0 hα1 hL hs hZ hell hhalf'
    calc L = Real.exp (Real.log L) := (Real.exp_log hL).symm
      _ ≤ Real.exp (sbNear_K0 ^ 2) := Real.exp_le_exp.mpr this
      _ ≤ sbNear_Lstar := le_max_right _ _

theorem sbNear_Lstar_ge_one : 1 ≤ sbNear_Lstar :=
  le_trans (by norm_num) (le_max_left _ _)

/-- The absorption constant `B = L*^101 / a`. -/
def sbNear_B : ℝ := sbNear_Lstar ^ 101 / sbNear_a

private theorem sbNear_three_pow_ge {L gap : ℝ} (hL : 0 < L) (hL1 : 1 ≤ L)
    (hgap : 200 * Real.log L ≤ gap) : L ^ (101 : ℕ) ≤ (3 : ℝ) ^ gap := by
  have hlog3 : 1 ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith only [this]
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL1
  rw [Real.rpow_def_of_pos (by norm_num), ← Real.exp_log (pow_pos hL 101), Real.log_pow,
    Real.exp_le_exp]
  push_cast
  nlinarith only [hlog3, hlogL, hgap]

/-- **The scale arithmetic of the absorption**, for every `Cth ≥ 1`:
`ν⁻³ L 3^{-(ell - n)} ≤ B L^{-99}` at the witness `n = ell - ⌈200 log L⌉`. -/
theorem sbNear_absorb_arith {Cth M alpha cStar nu K : ℝ} {ell L : ℕ} (hC : 1 ≤ Cth)
    (hM : 1 ≤ M) (hα0 : 0 ≤ alpha) (hα1 : alpha < 1) (hc : 0 < cStar) (hc2 : cStar ≤ 2)
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hK : 0 ≤ K) (hlt : ell < L)
    (hLnaught : SuperdiffusionCLT.Frozen.Section4.lNaught Cth (Cth * M) alpha cStar nu K ≤
      (ell : ℝ))
    (hscale : (L : ℝ) - M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (ell : ℝ))
    (n : ℕ) (hn : n = ell - ⌈200 * Real.log (L : ℝ)⌉₊) :
    nu ^ (-(3 : ℝ)) * ((L : ℝ) * (3 : ℝ) ^ (-((ell - n : ℕ) : ℝ))) ≤
      sbNear_B * (L : ℝ) ^ (-(99 : ℝ)) := by
  have ha := sbNear_a_pos
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (Nat.zero_le ell).trans_lt hlt
  have hL : (0 : ℝ) < L := lt_of_lt_of_le zero_lt_one hL1
  have hellL : (ell : ℝ) ≤ L := by exact_mod_cast hlt.le
  have hnu4 : 0 < nu ^ (4 : ℝ) := Real.rpow_pos_of_pos hnu _
  -- `ν⁻³ ≤ L / a`
  have hnuL := sbNear_nu_le hC hM hα0 hα1 hc hc2 hnu hK hL1 (hLnaught.trans hellL)
  have hnu3 : nu ^ (-(3 : ℝ)) ≤ L / sbNear_a := by
    have h34 : nu ^ (-(3 : ℝ)) ≤ nu ^ (-(4 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge hnu hnu1 (by norm_num)
    rw [Real.rpow_neg hnu.le (4 : ℝ)] at h34
    rw [le_div_iff₀ ha]
    rw [div_le_iff₀ hnu4] at hnuL
    have : nu ^ (-(3 : ℝ)) * sbNear_a ≤ (nu ^ (4 : ℝ))⁻¹ * sbNear_a :=
      mul_le_mul_of_nonneg_right h34 ha.le
    have h2 : (nu ^ (4 : ℝ))⁻¹ * sbNear_a ≤ L := by
      rw [inv_mul_le_iff₀ hnu4]; linarith only [hnuL]
    linarith only [this, h2]
  have hnu3pos : 0 ≤ nu ^ (-(3 : ℝ)) := (Real.rpow_pos_of_pos hnu _).le
  have hL99 : (L : ℝ) ^ (-(99 : ℝ)) = ((L : ℝ) ^ (99 : ℕ))⁻¹ := by
    rw [Real.rpow_neg hL.le, show (99 : ℝ) = ((99 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hL99, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hL 99)]
  set g : ℝ := ((ell - n : ℕ) : ℝ) with hgdef
  have h3pos : 0 < (3 : ℝ) ^ g := Real.rpow_pos_of_pos (by norm_num) _
  have h3neg : (3 : ℝ) ^ (-g) = ((3 : ℝ) ^ g)⁻¹ := Real.rpow_neg (by norm_num) _
  rw [h3neg]
  rcases le_or_gt ⌈200 * Real.log (L : ℝ)⌉₊ ell with hA | hB
  · -- the untruncated branch: `3^{gap} ≥ L^101`
    have hg : g = (⌈200 * Real.log (L : ℝ)⌉₊ : ℝ) := by
      rw [hgdef, hn, Nat.sub_sub_self hA]
    have hgap : 200 * Real.log (L : ℝ) ≤ g := by rw [hg]; exact Nat.le_ceil _
    have h101 := sbNear_three_pow_ge hL hL1 hgap
    have hkey : nu ^ (-(3 : ℝ)) * ((L : ℝ) * ((3 : ℝ) ^ g)⁻¹) * (L : ℝ) ^ 99 ≤
        L / sbNear_a * ((L : ℝ) * ((L : ℝ) ^ 101)⁻¹) * (L : ℝ) ^ 99 := by
      apply mul_le_mul_of_nonneg_right _ (pow_pos hL 99).le
      apply mul_le_mul hnu3 _ (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left
        ((inv_le_inv₀ h3pos (pow_pos hL 101)).mpr h101) hL.le
    have heq : L / sbNear_a * ((L : ℝ) * ((L : ℝ) ^ 101)⁻¹) * (L : ℝ) ^ 99 = 1 / sbNear_a := by
      field_simp
    have hB1 : 1 / sbNear_a ≤ sbNear_B := by
      unfold sbNear_B
      exact div_le_div_of_nonneg_right (one_le_pow₀ sbNear_Lstar_ge_one) ha.le
    linarith only [hkey, heq, hB1]
  · -- the truncated branch: `L ≤ L*`
    have hell : (ell : ℝ) < 200 * Real.log (L : ℝ) + 1 := by
      have h := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 200 * Real.log (L : ℝ))
      have hB' : (ell : ℝ) < (⌈200 * Real.log (L : ℝ)⌉₊ : ℝ) := by exact_mod_cast hB
      linarith only [h, hB']
    have hγ : 0 < 1 - alpha := by linarith only [hα1]
    have hγ12pos : 0 < (1 - alpha) ^ (12 : ℝ) := Real.rpow_pos_of_pos hγ _
    have hnu41 : nu ^ (4 : ℝ) ≤ 1 := Real.rpow_le_one hnu.le hnu1 (by norm_num)
    have hZ : (sbNear_a * M / (1 - alpha) ^ (12 : ℝ)) ^ ((1 : ℝ) / (1 - alpha)) ≤ (ell : ℝ) := by
      refine le_trans ?_ ((sbNear_lNaught_ge hC hM hα1 hc hc2 hnu hK).trans hLnaught)
      apply Real.rpow_le_rpow (by positivity) _ (div_nonneg zero_le_one hγ.le)
      apply div_le_div_of_nonneg_left (by positivity) (mul_pos hγ12pos hnu4)
      exact mul_le_of_le_one_right hγ12pos.le hnu41
    have hLstar := sbNear_caseB hM hα0 hα1 hL1 hZ hell hscale
    have hg1 : 1 ≤ (3 : ℝ) ^ g := Real.one_le_rpow (by norm_num) (by positivity)
    have hinv1 : ((3 : ℝ) ^ g)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hg1
    have hkey : nu ^ (-(3 : ℝ)) * ((L : ℝ) * ((3 : ℝ) ^ g)⁻¹) * (L : ℝ) ^ 99 ≤
        L / sbNear_a * ((L : ℝ) * 1) * (L : ℝ) ^ 99 := by
      apply mul_le_mul_of_nonneg_right _ (pow_pos hL 99).le
      exact mul_le_mul hnu3 (mul_le_mul_of_nonneg_left hinv1 hL.le) (by positivity)
        (by positivity)
    have heq : L / sbNear_a * ((L : ℝ) * 1) * (L : ℝ) ^ 99 = (L : ℝ) ^ 101 / sbNear_a := by
      ring
    have hpow : (L : ℝ) ^ 101 ≤ sbNear_Lstar ^ 101 := pow_le_pow_left₀ hL.le hLstar 101
    have hB2 : (L : ℝ) ^ 101 / sbNear_a ≤ sbNear_B :=
      div_le_div_of_nonneg_right hpow ha.le
    linarith only [hkey, heq, hB2]

end

end SuperdiffusionCLT.Section4.SigmaBarComparison
