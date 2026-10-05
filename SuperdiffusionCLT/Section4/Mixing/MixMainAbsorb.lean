/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The absorption step: explicit `ell, L, m, n, ν`-polynomial-times-exponential
amplitudes into a bare `m`-power

The final assembly of `p.mixing.P.three.prime` needs to convert the *explicit* amplitudes
produced by `MixMainTerm1B.lean` and `TermGaugeFinalB.lean` -- built from
`ell, L, m, n, ν`-polynomial prefactors times `3^{-(ell-n)}`- or
`3^{-(d/2)(m-ell)}`-type decay -- into the bare `C · m^{-N}` amplitude the
statement of `p.mixing.P.three.prime` (and the `TermsCombined.lean` /
`AnnealedFinal.lean` pipeline) prints. This
absorption genuinely needs both the mixing-gap margin
`ell - n ≥ (K/10) log(ν⁻¹L)` (from the choice of the auxiliary scale `ell`)
*and* the case guard `m ≤ L + (K/2)
log(ν⁻¹L)` together, since neither alone bounds the amplitude uniformly down
to `ν⁻¹L = 1`.

This file supplies the generic real-analysis core of that absorption, in two
layers:

* `mixMain_rpow_le_of_le_mul`: base-monotonicity for a nonpositive `rpow`
  exponent, in ratio form (`Y ≥ m / B` and `a ≤ 0` give
  `Y ^ a ≤ B ^ (-a) * m ^ a`).
* `mixMain_m_le_mul_nuInvL`: the case guard `m ≤ L + (K/2) log(ν⁻¹L)`
  converts, via `Real.log_le_sub_one_of_pos`, into a genuine linear bound
  `m ≤ (1 + K/2) * (ν⁻¹L)`, uniformly in `ν, L` (no lower threshold on
  `ν⁻¹L` needed, unlike the `hSigmaStarTail`/gauge-term
  amplitudes taken alone).
* `mixMain_gammaLog_eq_rpow`: `3^{-(K/10) log(ν⁻¹L)} = (ν⁻¹L)^{-(K log 3)/10}`,
  the exact exponential-decay-to-`rpow`-decay conversion.

Combining these three lets a caller convert any amplitude of the shape
`poly(ell, L, m, n, ν⁻¹) · 3^{-x}` (`x ≥ (K/10) log(ν⁻¹L)`, `poly` bounded by
a fixed power of `ν⁻¹L`) into `C(K, d) · m^{-N}` for any fixed target power
`N`, by choosing `K` large enough that `(K log 3)/10` exceeds the polynomial
degree plus `N`. -/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

/-- **Base-monotonicity for a nonpositive `rpow` exponent, in ratio form.**
For `Y ≥ m / B` (`B, m > 0`) and `a ≤ 0`, `Y ^ a ≤ B ^ (-a) * m ^ a`. -/
theorem mixMain_rpow_le_of_le_mul {Y m B a : ℝ} (hB : 0 < B) (hm : 0 < m)
    (ha : a ≤ 0) (hmY : m ≤ B * Y) :
    Y ^ a ≤ B ^ (-a) * m ^ a := by
  have hY_pos : 0 < Y := by
    rcases lt_or_ge 0 Y with hYpos | hYnonpos
    · exact hYpos
    · exfalso
      have : B * Y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hB.le hYnonpos
      linarith only [hmY, hm, this]
  have hmB : m / B ≤ Y := (div_le_iff₀ hB).2 (by linarith only [hmY])
  have hmB_pos : 0 < m / B := div_pos hm hB
  have hYpow_pos : 0 < Y ^ (-a) := Real.rpow_pos_of_pos hY_pos _
  have hmBpow_pos : 0 < (m / B) ^ (-a) := Real.rpow_pos_of_pos hmB_pos _
  have hmono : (m / B) ^ (-a) ≤ Y ^ (-a) :=
    Real.rpow_le_rpow hmB_pos.le hmB (by linarith only [ha])
  have hinv : (Y ^ (-a))⁻¹ ≤ ((m / B) ^ (-a))⁻¹ :=
    (inv_le_inv₀ hYpow_pos hmBpow_pos).mpr hmono
  have hYa : Y ^ a = (Y ^ (-a))⁻¹ := by
    rw [← Real.rpow_neg hY_pos.le, neg_neg]
  have hmBa : (m / B) ^ (-a) = m ^ (-a) * B ^ a := by
    rw [Real.div_rpow hm.le hB.le, div_eq_mul_inv, Real.rpow_neg hB.le, inv_inv]
  rw [hYa]
  refine hinv.trans (le_of_eq ?_)
  rw [hmBa, mul_inv, Real.rpow_neg hm.le, inv_inv, Real.rpow_neg hB.le]
  ring

/-- **The case-guard linearization.** `m ≤ L + (K/2) log(ν⁻¹L)`, together
with `0 < ν ≤ 1`, `1 ≤ L`, `0 ≤ K`, gives the genuine linear bound
`m ≤ (1 + K/2) * (ν⁻¹L)`, using `log x ≤ x - 1 ≤ x` for `x ≥ 1`. -/
theorem mixMain_m_le_mul_nuInvL {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    {K : ℝ} (hK0 : 0 ≤ K) {L m : ℕ} (hL : 1 ≤ L)
    (hCase : (m : ℝ) ≤ (L : ℝ) + K / 2 * Real.log (nu⁻¹ * (L : ℝ))) :
    (m : ℝ) ≤ (1 + K / 2) * (nu⁻¹ * (L : ℝ)) := by
  have hnuinv1 : (1 : ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
  have hLcast : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have harg1 : (1 : ℝ) ≤ nu⁻¹ * (L : ℝ) := by
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ nu⁻¹ * (L : ℝ) := mul_le_mul hnuinv1 hLcast (by norm_num) (by linarith only [hnuinv1])
  have hlog_le : Real.log (nu⁻¹ * (L : ℝ)) ≤ nu⁻¹ * (L : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hLleY : (L : ℝ) ≤ nu⁻¹ * (L : ℝ) := by
    calc (L : ℝ) = 1 * (L : ℝ) := by ring
      _ ≤ nu⁻¹ * (L : ℝ) := mul_le_mul_of_nonneg_right hnuinv1 (by linarith only [hLcast])
  have hstep : (L : ℝ) + K / 2 * Real.log (nu⁻¹ * (L : ℝ)) ≤
      (L : ℝ) + K / 2 * (nu⁻¹ * (L : ℝ) - 1) := by
    have := mul_le_mul_of_nonneg_left hlog_le (by linarith only [hK0] : (0:ℝ) ≤ K / 2)
    linarith only [this]
  have hfin : (L : ℝ) + K / 2 * (nu⁻¹ * (L : ℝ) - 1) ≤ (1 + K / 2) * (nu⁻¹ * (L : ℝ)) := by
    nlinarith only [hLleY, harg1, hK0]
  linarith only [hCase, hstep, hfin]

/-- **The exponential-to-`rpow` decay conversion.** For `Y ≥ 1` and `c ≥ 0`,
`3 ^ (-(c / 10 * Real.log Y)) = Y ^ (-(c * Real.log 3 / 10))`. -/
theorem mixMain_gammaLog_eq_rpow {Y c : ℝ} (hY : 0 < Y) :
    (3 : ℝ) ^ (-(c / 10 * Real.log Y)) = Y ^ (-(c * Real.log 3 / 10)) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 3), Real.rpow_def_of_pos hY]
  congr 1
  ring

end SuperdiffusionCLT.Section4.Mixing
