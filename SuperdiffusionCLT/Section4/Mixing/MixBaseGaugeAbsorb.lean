/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.Mixing.MixBaseTLBound

/-!
# The exponential-vs-polynomial absorption for the `t_ell -> t_L` leftover

The bounded-gap base case needs the following: the leftover
`E := nu⁻¹ * gammaMomentConst 1 * (Cf * nu^{-2} * 3^{-(ell-n)})` produced by
the scale conversion `t_ell ≤ t_L + E` (see `TermGaugeFinalB.lean`) is
`≤ const(d) * t_L` once `ell - n ≥ K0(d) * log(nu⁻¹ L)`, for a FIXED
`K0(d), const(d)` depending only on `d` (and the fixed dimension constant
`Cf` of that conversion, which itself traces to
`cutoff_localization`'s constant, a function of `d` alone).

## The chain

`MixBaseTLBound.lean`'s `mixBase_tL_lowerBound` gives `t_L ≥
nu / ((1 + 2 cutoffEnvelopeConst d) * L)`. Setting `Y := nu⁻¹ * L ≥ 1`, the
polynomial prefactor `nu⁻¹ * nu^{-2} = nu^{-3}` and the extra `nu` from the
denominator of `t_L`'s lower bound combine into `(nu⁻¹)^4 * L`, which is
`≤ Y^5` (elementary, nat powers, no `rpow` needed); the exponential factor
`3^{-(ell-n)}` is `≤ Y^{-5}` once `ell - n ≥ K0(d) * log Y` for `K0(d) := 5 /
log 3` (so `K0(d) * log 3 = 5` exactly, no slack needed in the exponent).
The product `Y^5 * Y^{-5} = 1` finishes the absorption, and unwinding the
algebra gives `E ≤ (gammaMomentConst 1 * Cf * (1 + 2 cutoffEnvelopeConst d))
* t_L`.

## Main result

* `mixBase_gaugeE_absorb`: `∃ K0 CE, ...`, the absorption above.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

open Homogenization
open MeasureTheory
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff (ShellSeq)

noncomputable section

variable {d : ℕ}

/-- **The `t_ell → t_L` leftover absorption.** For a fixed `Cf ≥ 1` (the
constant the scale conversion supplies), there is a threshold `K0(d)`
and a constant `CE(d, Cf)` such that once `ell - n ≥ K0 * log(nu⁻¹ L)`, the
leftover amplitude `nu⁻¹ * gammaMomentConst 1 * (Cf * nu^{-2} *
3^{-(ell-n)})` is `≤ CE * t_L`. -/
theorem mixBase_gaugeE_absorb (d : ℕ) [NeZero d] (Cf : ℝ) (hCf1 : 1 ≤ Cf) :
    ∃ K0 CE : ℝ, 1 ≤ K0 ∧ K0 ≤ 5 ∧ 0 ≤ CE ∧
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (L : ℕ), 1 ≤ L →
          ∀ (ell n : ℕ),
            K0 * Real.log (nu⁻¹ * (L : ℝ)) ≤ (((ell - n : ℕ) : ℕ) : ℝ) →
            ∀ (P : ProbabilityMeasure (ShellSeq d)),
              ShellLawPrefix d P → ShellLawJ2 d P → ShellLawJ3 d P → ShellLawJ4 d P →
                ∀ (j : ℤ), 0 ≤ j →
                  nu⁻¹ * gammaMomentConst 1 *
                      (Cf * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((ell - n : ℕ) : ℕ) : ℝ))) ≤
                    CE * sigmaBarStarInvScalar nu L P (cubeSet (originCube d j)) := by
  have hlog3_pos : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hlog3_le2 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
    linarith only [this]
  set K0 : ℝ := 5 / Real.log 3 with hK0def
  have hK0_1 : (1 : ℝ) ≤ K0 := by
    rw [hK0def, le_div_iff₀ hlog3_pos]
    linarith only [hlog3_le2]
  have hK0log3 : K0 * Real.log 3 = 5 := by
    rw [hK0def]; field_simp
  have hgm : (0 : ℝ) < gammaMomentConst 1 := gammaMomentConst_pos one_pos
  have hCfpos : (0 : ℝ) < Cf := lt_of_lt_of_le zero_lt_one hCf1
  have hCenvpos : (0 : ℝ) < cutoffEnvelopeConst d := cutoffEnvelopeConst_pos d
  set CE : ℝ := gammaMomentConst 1 * Cf * (1 + 2 * cutoffEnvelopeConst d) with hCEdef
  have hCEnn : (0 : ℝ) ≤ CE := by
    have h1 : (0 : ℝ) ≤ gammaMomentConst 1 * Cf := (mul_pos hgm hCfpos).le
    have h2 : (0 : ℝ) ≤ 1 + 2 * cutoffEnvelopeConst d := by linarith only [hCenvpos]
    rw [hCEdef]; exact mul_nonneg h1 h2
  have hK0_5 : K0 ≤ 5 := by
    have hlog3_ge1 : (1 : ℝ) ≤ Real.log 3 := by
      have h : (1 : ℝ) < Real.log 3 :=
        (Real.lt_log_iff_exp_lt (by norm_num)).2 (by
          have := Real.exp_one_lt_d9
          linarith only [this])
      exact h.le
    rw [hK0def, div_le_iff₀ hlog3_pos]
    linarith only [hlog3_ge1]
  refine ⟨K0, CE, hK0_1, hK0_5, hCEnn, ?_⟩
  intro nu hnu hnu1 L hL1 ell n hgap P hPrefix hJ2 hJ3 hJ4 j hj
  set Y : ℝ := nu⁻¹ * (L : ℝ) with hYdef
  have hnuinv1 : (1 : ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
  have hLcast : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
  have hLpos : (0 : ℝ) < (L : ℝ) := lt_of_lt_of_le zero_lt_one hLcast
  have hLne : (L : ℝ) ≠ 0 := hLpos.ne'
  have hY1 : (1 : ℝ) ≤ Y := by
    rw [hYdef]
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ nu⁻¹ * (L : ℝ) := mul_le_mul hnuinv1 hLcast (by norm_num) (by linarith only [hnuinv1])
  have hY_pos : (0 : ℝ) < Y := lt_of_lt_of_le zero_lt_one hY1
  have hnuinv_le_Y : nu⁻¹ ≤ Y := by
    rw [hYdef]
    calc nu⁻¹ = nu⁻¹ * 1 := by ring
      _ ≤ nu⁻¹ * (L : ℝ) := mul_le_mul_of_nonneg_left hLcast (by positivity)
  have hL_le_Y : (L : ℝ) ≤ Y := by
    rw [hYdef]
    calc (L : ℝ) = 1 * (L : ℝ) := by ring
      _ ≤ nu⁻¹ * (L : ℝ) := mul_le_mul_of_nonneg_right hnuinv1 (by linarith only [hLcast])
  -- `(nu⁻¹)^4 * L ≤ Y^5`, pure nat-power monotonicity.
  have hpow4 : (nu⁻¹) ^ 4 ≤ Y ^ 4 := pow_le_pow_left₀ (inv_nonneg.mpr hnu.le) hnuinv_le_Y 4
  have hLnn : (0 : ℝ) ≤ (L : ℝ) := hLpos.le
  have hYpow4nn : (0 : ℝ) ≤ Y ^ 4 := by positivity
  have hprod4L : (nu⁻¹) ^ 4 * (L : ℝ) ≤ Y ^ 4 * Y := mul_le_mul hpow4 hL_le_Y hLnn hYpow4nn
  have hY5eq : Y ^ 4 * Y = Y ^ 5 := by ring
  have hprod5 : (nu⁻¹) ^ 4 * (L : ℝ) ≤ Y ^ 5 := by rw [hY5eq] at hprod4L; exact hprod4L
  -- `E3 := 3^{-(ell-n)} ≤ Y^{-5} = (Y^5)⁻¹`.
  set E3 : ℝ := (3 : ℝ) ^ (-(((ell - n : ℕ) : ℕ) : ℝ)) with hE3def
  have hE3nn : (0 : ℝ) ≤ E3 := by rw [hE3def]; positivity
  have hexpmono : E3 ≤ (3 : ℝ) ^ (-(K0 * Real.log Y)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hgap])
  have heq2 : (3 : ℝ) ^ (-(K0 * Real.log Y)) = Y ^ (-(5 : ℝ)) := by
    rw [Real.rpow_def_of_pos (show (0 : ℝ) < 3 by norm_num), Real.rpow_def_of_pos hY_pos]
    congr 1
    have hswap : Real.log 3 * (-(K0 * Real.log Y)) = -(K0 * Real.log 3) * Real.log Y := by ring
    rw [hswap, hK0log3]; ring
  have hYconv : Y ^ (-(5 : ℝ)) = (Y ^ 5)⁻¹ := by
    rw [Real.rpow_neg hY_pos.le, show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hE3le : E3 ≤ (Y ^ 5)⁻¹ := (hexpmono.trans_eq heq2).trans_eq hYconv
  have hY5pos : (0 : ℝ) < Y ^ 5 := by positivity
  have hkey : (nu⁻¹) ^ 4 * (L : ℝ) * E3 ≤ 1 := by
    have h1 : (nu⁻¹) ^ 4 * (L : ℝ) * E3 ≤ Y ^ 5 * (Y ^ 5)⁻¹ :=
      mul_le_mul hprod5 hE3le hE3nn hY5pos.le
    rwa [mul_inv_cancel₀ hY5pos.ne'] at h1
  -- Unwind `nu^{-2} = (nu⁻¹)^2` and assemble.
  have hnu2 : nu ^ (-(2 : ℝ)) = (nu⁻¹) ^ 2 := by
    rw [Real.rpow_neg hnu.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← inv_pow]
  have hnune : nu ≠ 0 := hnu.ne'
  have heqnu4 : nu * (nu⁻¹) ^ 4 = (nu⁻¹) ^ 3 := by
    have hh : nu * (nu⁻¹) ^ 4 = (nu * nu⁻¹) * (nu⁻¹) ^ 3 := by ring
    rw [hh, mul_inv_cancel₀ hnune, one_mul]
  have hstar : (nu⁻¹) ^ 3 * (L : ℝ) * E3 ≤ nu := by
    have hmul := mul_le_mul_of_nonneg_left hkey hnu.le
    calc (nu⁻¹) ^ 3 * (L : ℝ) * E3 = nu * ((nu⁻¹) ^ 4 * (L : ℝ) * E3) := by
          rw [← heqnu4]; ring
      _ ≤ nu * 1 := hmul
      _ = nu := by ring
  have hgmCfnn : (0 : ℝ) ≤ gammaMomentConst 1 * Cf := (mul_pos hgm hCfpos).le
  have hfinal1 : gammaMomentConst 1 * Cf * ((nu⁻¹) ^ 3 * (L : ℝ) * E3) ≤
      gammaMomentConst 1 * Cf * nu := mul_le_mul_of_nonneg_left hstar hgmCfnn
  have hLHS_eq2 : gammaMomentConst 1 * Cf * ((nu⁻¹) ^ 3 * E3) * (L : ℝ) =
      gammaMomentConst 1 * Cf * ((nu⁻¹) ^ 3 * (L : ℝ) * E3) := by ring
  have hfinal2 : gammaMomentConst 1 * Cf * ((nu⁻¹) ^ 3 * E3) * (L : ℝ) ≤
      gammaMomentConst 1 * Cf * nu := by rw [hLHS_eq2]; exact hfinal1
  have hfinal3 : gammaMomentConst 1 * Cf * ((nu⁻¹) ^ 3 * E3) ≤
      gammaMomentConst 1 * Cf * nu / (L : ℝ) := (le_div_iff₀ hLpos).2 hfinal2
  have hCEbound := mixBase_tL_lowerBound hnu hnu1 hL1 hPrefix hJ2 hJ3 hJ4 hj
  have hCenvsum_pos : (0 : ℝ) < 1 + 2 * cutoffEnvelopeConst d := by linarith only [hCenvpos]
  have hCenvne : (1 + 2 * cutoffEnvelopeConst d : ℝ) ≠ 0 := hCenvsum_pos.ne'
  have hsimpEq : gammaMomentConst 1 * Cf * (1 + 2 * cutoffEnvelopeConst d) *
      (nu / ((1 + 2 * cutoffEnvelopeConst d) * (L : ℝ))) =
        gammaMomentConst 1 * Cf * nu / (L : ℝ) := by
    field_simp
  have hRHSfinal : gammaMomentConst 1 * Cf * nu / (L : ℝ) ≤
      CE * sigmaBarStarInvScalar nu L P (cubeSet (originCube d j)) := by
    have hmul2 := mul_le_mul_of_nonneg_left hCEbound hCEnn
    rw [hCEdef]
    calc gammaMomentConst 1 * Cf * nu / (L : ℝ)
        = gammaMomentConst 1 * Cf * (1 + 2 * cutoffEnvelopeConst d) *
            (nu / ((1 + 2 * cutoffEnvelopeConst d) * (L : ℝ))) := hsimpEq.symm
      _ ≤ CE * sigmaBarStarInvScalar nu L P (cubeSet (originCube d j)) := by
          rw [← hCEdef]; exact hmul2
  rw [hnu2]
  calc nu⁻¹ * gammaMomentConst 1 * (Cf * (nu⁻¹) ^ 2 * E3)
      = gammaMomentConst 1 * Cf * ((nu⁻¹) ^ 3 * E3) := by ring
    _ ≤ gammaMomentConst 1 * Cf * nu / (L : ℝ) := hfinal3
    _ ≤ CE * sigmaBarStarInvScalar nu L P (cubeSet (originCube d j)) := hRHSfinal

end

end SuperdiffusionCLT.Section4.Mixing
