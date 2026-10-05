/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.LNaught.SstarLower

/-!
# `e.L.vs.Lnaught`, assembly (continues `SstarLower.lean`)

This file completes `SuperdiffusionCLT.Section4.LNaught.lNaught_sstar_lower`
(display `e.L.vs.Lnaught`): combines `SstarLower.lean`'s
`sstarLower_h_clears_threshold` (step (a): `h` clears the threshold of
`sigmaBarStar_lower_bound`) with `Threshold.lean`'s
`lNaught_threshold`, `lNaught_absorbs`, `lNaught_ge` (steps (b), (c): the
polynomial-loss absorption `M L^α log³L ≤ c⋆³ν⁴L log⁻⁹L` and `log(ν⁻¹h) ≤
2 log L`) to assemble the final display.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.LNaught

open Real

/-- `ν⁻¹ ≤ L` once `L ≥ L₀(C,...)` (`C` past `lNaught_threshold`'s and
`lNaught_ge`'s own thresholds): `lNaught_threshold`'s first conjunct forces
`ν⁻⁴ ≤ 8L`, and `L > 8` (`lNaught_ge`) forces `8L ≤ L^4`, so `(ν⁻¹)^4 ≤ L^4`
and `ν⁻¹ ≤ L` follows by a `pow` contrapositive. -/
private lemma sstarLower_nuinv_le_L {M alpha cStar nu : ℝ} {L : ℕ}
    (hM : 1 ≤ M) (halpha0 : 0 ≤ alpha)
    (hcStar : 0 < cStar) (hcStar2 : cStar ≤ 2) (hnu : 0 < nu)
    (hLgt8 : (8:ℝ) < (L:ℝ))
    (hThresh1 : M * cStar ^ (-(3 : ℝ)) * nu ^ (-(4 : ℝ)) * Real.log (L : ℝ) ^ (12 : ℝ) ≤
        (L : ℝ) ^ (1 - alpha)) :
    nu⁻¹ ≤ (L : ℝ) := by
  have hLpos : (0:ℝ) < (L:ℝ) := by linarith only [hLgt8]
  have hL1 : (1:ℝ) ≤ (L:ℝ) := by linarith only [hLgt8]
  have hcube_ge : (1:ℝ) / 8 ≤ cStar ^ (-(3 : ℝ)) := sstarLower_cStar_neg_three_ge_eighth hcStar hcStar2
  have hale1 : 1 - alpha ≤ 1 := by linarith only [halpha0]
  have hLpow_le : (L:ℝ) ^ (1 - alpha) ≤ (L:ℝ) ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 hale1
  have hLpow_eq : (L:ℝ) ^ (1:ℝ) = (L:ℝ) := Real.rpow_one _
  have hnu4_nonneg : (0:ℝ) ≤ nu ^ (-(4:ℝ)) := Real.rpow_nonneg hnu.le _
  have hMcube_ge : (1:ℝ) * ((1:ℝ)/8) ≤ M * cStar ^ (-(3:ℝ)) :=
    mul_le_mul hM hcube_ge (by norm_num) (by linarith only [hM])
  have h8 : Real.log 8 ≤ Real.log (L:ℝ) := Real.log_le_log (by norm_num) hLgt8.le
  have hlog8 : (2:ℝ) < Real.log 8 := by
    have heq : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8:ℝ) = (2:ℝ) ^ (3:ℕ) by norm_num, Real.log_pow]; push_cast; ring
    rw [heq]; linarith only [Real.log_two_gt_d9]
  have hlogL1 : (1:ℝ) ≤ Real.log (L:ℝ) := by linarith only [h8, hlog8]
  have hlogL12 : (1:ℝ) ≤ Real.log (L:ℝ) ^ (12:ℝ) := by
    calc (1:ℝ) = (1:ℝ) ^ (12:ℝ) := by rw [Real.one_rpow]
      _ ≤ Real.log (L:ℝ) ^ (12:ℝ) := Real.rpow_le_rpow (by norm_num) hlogL1 (by norm_num)
  have hlogL12pos : (0:ℝ) < Real.log (L:ℝ) ^ (12:ℝ) := lt_of_lt_of_le one_pos hlogL12
  have hstep1 : (1:ℝ)/8 * nu ^ (-(4:ℝ)) ≤ M * cStar ^ (-(3:ℝ)) * nu ^ (-(4:ℝ)) := by
    have h1 : (1:ℝ) * ((1:ℝ)/8) * nu ^ (-(4:ℝ)) ≤ M * cStar ^ (-(3:ℝ)) * nu ^ (-(4:ℝ)) :=
      mul_le_mul_of_nonneg_right hMcube_ge hnu4_nonneg
    linarith only [h1]
  have hstep2 : (1:ℝ)/8 * nu ^ (-(4:ℝ)) * Real.log (L:ℝ) ^ (12:ℝ) ≤
      M * cStar ^ (-(3:ℝ)) * nu ^ (-(4:ℝ)) * Real.log (L:ℝ) ^ (12:ℝ) :=
    mul_le_mul_of_nonneg_right hstep1 hlogL12pos.le
  have hstep3 : nu ^ (-(4:ℝ)) ≤ nu ^ (-(4:ℝ)) * Real.log (L:ℝ) ^ (12:ℝ) := by
    have h1 : nu ^ (-(4:ℝ)) * (1:ℝ) ≤ nu ^ (-(4:ℝ)) * Real.log (L:ℝ) ^ (12:ℝ) :=
      mul_le_mul_of_nonneg_left hlogL12 hnu4_nonneg
    linarith only [h1]
  have heighthle : (1:ℝ)/8 * nu ^ (-(4:ℝ)) * Real.log (L:ℝ) ^ (12:ℝ) ≤ (L:ℝ) := by
    calc (1:ℝ)/8 * nu ^ (-(4:ℝ)) * Real.log (L:ℝ) ^ (12:ℝ) ≤
        M * cStar ^ (-(3:ℝ)) * nu ^ (-(4:ℝ)) * Real.log (L:ℝ) ^ (12:ℝ) := hstep2
      _ ≤ (L:ℝ) ^ (1-alpha) := hThresh1
      _ ≤ (L:ℝ) ^ (1:ℝ) := hLpow_le
      _ = (L:ℝ) := hLpow_eq
  have hnu4logL12_le : nu ^ (-(4:ℝ)) * Real.log (L:ℝ) ^ (12:ℝ) ≤ 8 * (L:ℝ) := by
    have h1 : (8:ℝ) * ((1:ℝ)/8 * nu ^ (-(4:ℝ)) * Real.log (L:ℝ) ^ (12:ℝ)) ≤ 8 * (L:ℝ) :=
      mul_le_mul_of_nonneg_left heighthle (by norm_num)
    have h2 : (8:ℝ) * ((1:ℝ)/8 * nu ^ (-(4:ℝ)) * Real.log (L:ℝ) ^ (12:ℝ)) =
        nu ^ (-(4:ℝ)) * Real.log (L:ℝ) ^ (12:ℝ) := by ring
    linarith only [h1, h2.le, h2.ge]
  have hnu4_le8L : nu ^ (-(4:ℝ)) ≤ 8 * (L:ℝ) := le_trans hstep3 hnu4logL12_le
  have hnu4eq : nu ^ (-(4:ℝ)) = (nu⁻¹) ^ (4:ℕ) := by
    rw [Real.rpow_neg hnu.le, inv_pow]
    congr 1
    rw [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have hnuinvpow_le : (nu⁻¹) ^ (4:ℕ) ≤ 8 * (L:ℝ) := by rw [← hnu4eq]; exact hnu4_le8L
  have hL3ge8 : (8:ℝ) ≤ (L:ℝ) ^ (3:ℕ) := by
    calc (8:ℝ) = (8:ℝ) ^ (1:ℕ) := by norm_num
      _ ≤ (L:ℝ) ^ (3:ℕ) := by
          have h1 : (8:ℝ) ≤ (L:ℝ) := hLgt8.le
          calc (8:ℝ) ^ (1:ℕ) ≤ (L:ℝ) ^ (1:ℕ) := by
                simpa using h1
            _ ≤ (L:ℝ) ^ (3:ℕ) :=
                pow_le_pow_right₀ hL1 (by norm_num)
  have h8Lle : 8 * (L:ℝ) ≤ (L:ℝ) ^ (4:ℕ) := by
    have h1 : (8:ℝ) * (L:ℝ) ≤ (L:ℝ) ^ (3:ℕ) * (L:ℝ) :=
      mul_le_mul_of_nonneg_right hL3ge8 hLpos.le
    have h2 : (L:ℝ) ^ (3:ℕ) * (L:ℝ) = (L:ℝ) ^ (4:ℕ) := by ring
    linarith only [h1, h2.le, h2.ge]
  have hnuinvpow_leL4 : (nu⁻¹) ^ (4:ℕ) ≤ (L:ℝ) ^ (4:ℕ) := le_trans hnuinvpow_le h8Lle
  by_contra hcon
  push Not at hcon
  have h1 : (L:ℝ) ^ (4:ℕ) < (nu⁻¹) ^ (4:ℕ) := by
    apply pow_lt_pow_left₀ hcon hLpos.le
    norm_num
  linarith only [h1, hnuinvpow_leL4]

/-- `log(ν⁻¹h) ≤ 2 log L`, from `ν⁻¹ ≤ L` and `h ≤ L`. -/
private lemma sstarLower_log_nuinvh_le {L h : ℕ} {nu : ℝ}
    (hnu : 0 < nu) (hnuinvL : nu⁻¹ ≤ (L:ℝ)) (hhL : h ≤ L) (hLgt8 : (8:ℝ) < (L:ℝ)) (hhpos : 0 < h) :
    Real.log (nu⁻¹ * (h:ℝ)) ≤ 2 * Real.log (L:ℝ) := by
  have hhLr : (h:ℝ) ≤ (L:ℝ) := by exact_mod_cast hhL
  have hLpos : (0:ℝ) < (L:ℝ) := by linarith only [hLgt8]
  have hnuinvpos : (0:ℝ) < nu⁻¹ := inv_pos.mpr hnu
  have hhposR : (0:ℝ) < (h:ℝ) := by exact_mod_cast hhpos
  have hprod_le : nu⁻¹ * (h:ℝ) ≤ (L:ℝ) * (L:ℝ) :=
    mul_le_mul hnuinvL hhLr hhposR.le hLpos.le
  have hprodpos : (0:ℝ) < nu⁻¹ * (h:ℝ) := mul_pos hnuinvpos hhposR
  have hlog_le : Real.log (nu⁻¹ * (h:ℝ)) ≤ Real.log ((L:ℝ) * (L:ℝ)) :=
    Real.log_le_log hprodpos hprod_le
  have heq : Real.log ((L:ℝ) * (L:ℝ)) = 2 * Real.log (L:ℝ) := by
    rw [Real.log_mul hLpos.ne' hLpos.ne']; ring
  linarith only [hlog_le, heq.le, heq.ge]

/-- Step (c): the exact algebraic absorption `M L^α log³L ≤ c⋆³ν⁴L log⁻⁹L`,
obtained from `lNaught_threshold`'s first conjunct by multiplying through by
`c⋆³ν⁴L^α log⁻⁹L` (matching the derivation of `e.L.vs.Lnaught` in the paper). -/
private lemma sstarLower_absorption {M alpha cStar nu : ℝ} {L : ℕ}
    (hcStar : 0 < cStar) (hnu : 0 < nu)
    (hLgt8 : (8:ℝ) < (L:ℝ))
    (hThresh1 : M * cStar ^ (-(3 : ℝ)) * nu ^ (-(4 : ℝ)) * Real.log (L : ℝ) ^ (12 : ℝ) ≤
        (L : ℝ) ^ (1 - alpha)) :
    M * (L:ℝ) ^ alpha * Real.log (L:ℝ) ^ (3:ℝ) ≤
      cStar ^ (3:ℝ) * nu ^ (4:ℝ) * (L:ℝ) * Real.log (L:ℝ) ^ (-(9:ℝ)) := by
  have hLpos : (0:ℝ) < (L:ℝ) := by linarith only [hLgt8]
  have h8 : Real.log 8 ≤ Real.log (L:ℝ) := Real.log_le_log (by norm_num) hLgt8.le
  have hlog8 : (2:ℝ) < Real.log 8 := by
    have heq : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8:ℝ) = (2:ℝ) ^ (3:ℕ) by norm_num, Real.log_pow]; push_cast; ring
    rw [heq]; linarith only [Real.log_two_gt_d9]
  have hlogLpos : (0:ℝ) < Real.log (L:ℝ) := by linarith only [h8, hlog8]
  have hfactor_nonneg : (0:ℝ) ≤
      cStar ^ (3:ℝ) * nu ^ (4:ℝ) * (L:ℝ) ^ alpha * Real.log (L:ℝ) ^ (-(9:ℝ)) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hThresh1 hfactor_nonneg
  have heq1 : cStar ^ (-(3:ℝ)) * cStar ^ (3:ℝ) = 1 := by
    rw [← Real.rpow_add hcStar]; norm_num
  have heq2 : nu ^ (-(4:ℝ)) * nu ^ (4:ℝ) = 1 := by
    rw [← Real.rpow_add hnu]; norm_num
  have heq3 : Real.log (L:ℝ) ^ (12:ℝ) * Real.log (L:ℝ) ^ (-(9:ℝ)) = Real.log (L:ℝ) ^ (3:ℝ) := by
    rw [← Real.rpow_add hlogLpos]; norm_num
  have heq4 : (L:ℝ) ^ (1 - alpha) * (L:ℝ) ^ alpha = (L:ℝ) := by
    rw [← Real.rpow_add hLpos, show (1 - alpha) + alpha = (1:ℝ) by ring, Real.rpow_one]
  have hLHSeq : M * cStar ^ (-(3 : ℝ)) * nu ^ (-(4 : ℝ)) * Real.log (L : ℝ) ^ (12 : ℝ) *
      (cStar ^ (3:ℝ) * nu ^ (4:ℝ) * (L:ℝ) ^ alpha * Real.log (L:ℝ) ^ (-(9:ℝ))) =
      M * (L:ℝ) ^ alpha * Real.log (L:ℝ) ^ (3:ℝ) := by
    have hregroup : M * cStar ^ (-(3 : ℝ)) * nu ^ (-(4 : ℝ)) * Real.log (L : ℝ) ^ (12 : ℝ) *
        (cStar ^ (3:ℝ) * nu ^ (4:ℝ) * (L:ℝ) ^ alpha * Real.log (L:ℝ) ^ (-(9:ℝ))) =
        M * (cStar ^ (-(3:ℝ)) * cStar ^ (3:ℝ)) * (nu ^ (-(4:ℝ)) * nu ^ (4:ℝ)) *
          (Real.log (L:ℝ) ^ (12:ℝ) * Real.log (L:ℝ) ^ (-(9:ℝ))) * (L:ℝ) ^ alpha := by
      ring
    rw [hregroup, heq1, heq2, heq3]; ring
  have hRHSeq : (L:ℝ) ^ (1 - alpha) *
      (cStar ^ (3:ℝ) * nu ^ (4:ℝ) * (L:ℝ) ^ alpha * Real.log (L:ℝ) ^ (-(9:ℝ))) =
      cStar ^ (3:ℝ) * nu ^ (4:ℝ) * (L:ℝ) * Real.log (L:ℝ) ^ (-(9:ℝ)) := by
    have hregroup : (L:ℝ) ^ (1 - alpha) *
        (cStar ^ (3:ℝ) * nu ^ (4:ℝ) * (L:ℝ) ^ alpha * Real.log (L:ℝ) ^ (-(9:ℝ))) =
        cStar ^ (3:ℝ) * nu ^ (4:ℝ) * ((L:ℝ) ^ (1 - alpha) * (L:ℝ) ^ alpha) *
          Real.log (L:ℝ) ^ (-(9:ℝ)) := by ring
    rw [hregroup, heq4]
  rw [hLHSeq, hRHSeq] at hmul
  exact hmul

/-- Squaring the root's annealed lower bound: from `c_r c⋆^{3/2} ν² h^{1/2}
log(ν⁻¹h)^{-9/2} ≤ S`, with all the printed factors positive, get
`c_r² c⋆³ ν⁴ h log(ν⁻¹h)^{-9} ≤ S²`. -/
private lemma sstarLower_square_root_bound {c_r cStar nu : ℝ} {h : ℕ} {S : ℝ}
    (hcr : 0 < c_r) (hcStar : 0 < cStar) (hnu : 0 < nu) (hhpos : 0 < h)
    (hlog_pos : 0 < Real.log (nu⁻¹ * (h:ℝ)))
    (hS : c_r * cStar ^ ((3:ℝ)/2) * nu ^ (2:ℝ) * (h:ℝ) ^ ((1:ℝ)/2) *
        Real.log (nu⁻¹ * (h:ℝ)) ^ (-((9:ℝ)/2)) ≤ S) :
    c_r ^ (2:ℕ) * cStar ^ (3:ℝ) * nu ^ (4:ℝ) * (h:ℝ) * Real.log (nu⁻¹ * (h:ℝ)) ^ (-(9:ℝ)) ≤
      S ^ (2:ℕ) := by
  have hhposR : (0:ℝ) < (h:ℝ) := by exact_mod_cast hhpos
  have hLHSpos : (0:ℝ) < c_r * cStar ^ ((3:ℝ)/2) * nu ^ (2:ℝ) * (h:ℝ) ^ ((1:ℝ)/2) *
      Real.log (nu⁻¹ * (h:ℝ)) ^ (-((9:ℝ)/2)) := by
    have h1 : (0:ℝ) < cStar ^ ((3:ℝ)/2) := Real.rpow_pos_of_pos hcStar _
    have h2 : (0:ℝ) < nu ^ (2:ℝ) := Real.rpow_pos_of_pos hnu _
    have h3 : (0:ℝ) < (h:ℝ) ^ ((1:ℝ)/2) := Real.rpow_pos_of_pos hhposR _
    have h4 : (0:ℝ) < Real.log (nu⁻¹ * (h:ℝ)) ^ (-((9:ℝ)/2)) :=
      Real.rpow_pos_of_pos hlog_pos _
    positivity
  have hsq : (c_r * cStar ^ ((3:ℝ)/2) * nu ^ (2:ℝ) * (h:ℝ) ^ ((1:ℝ)/2) *
      Real.log (nu⁻¹ * (h:ℝ)) ^ (-((9:ℝ)/2))) ^ (2:ℕ) ≤ S ^ (2:ℕ) :=
    pow_le_pow_left₀ hLHSpos.le hS 2
  have hexpand : (c_r * cStar ^ ((3:ℝ)/2) * nu ^ (2:ℝ) * (h:ℝ) ^ ((1:ℝ)/2) *
      Real.log (nu⁻¹ * (h:ℝ)) ^ (-((9:ℝ)/2))) ^ (2:ℕ) =
      c_r ^ (2:ℕ) * cStar ^ (3:ℝ) * nu ^ (4:ℝ) * (h:ℝ) * Real.log (nu⁻¹ * (h:ℝ)) ^ (-(9:ℝ)) := by
    have heq1 : (cStar ^ ((3:ℝ)/2)) ^ (2:ℕ) = cStar ^ (3:ℝ) := by
      rw [sq, ← Real.rpow_add hcStar]; norm_num
    have heq2 : (nu ^ (2:ℝ)) ^ (2:ℕ) = nu ^ (4:ℝ) := by
      rw [sq, ← Real.rpow_add hnu]; norm_num
    have heq3 : ((h:ℝ) ^ ((1:ℝ)/2)) ^ (2:ℕ) = (h:ℝ) := by
      rw [sq, ← Real.rpow_add hhposR, show (1:ℝ)/2 + 1/2 = (1:ℝ) by norm_num, Real.rpow_one]
    have heq4 : (Real.log (nu⁻¹ * (h:ℝ)) ^ (-((9:ℝ)/2))) ^ (2:ℕ) =
        Real.log (nu⁻¹ * (h:ℝ)) ^ (-(9:ℝ)) := by
      rw [sq, ← Real.rpow_add hlog_pos]; norm_num
    have hring : (c_r * cStar ^ ((3:ℝ)/2) * nu ^ (2:ℝ) * (h:ℝ) ^ ((1:ℝ)/2) *
        Real.log (nu⁻¹ * (h:ℝ)) ^ (-((9:ℝ)/2))) ^ (2:ℕ) =
        c_r ^ (2:ℕ) * (cStar ^ ((3:ℝ)/2)) ^ (2:ℕ) * (nu ^ (2:ℝ)) ^ (2:ℕ) *
          ((h:ℝ) ^ ((1:ℝ)/2)) ^ (2:ℕ) *
          (Real.log (nu⁻¹ * (h:ℝ)) ^ (-((9:ℝ)/2))) ^ (2:ℕ) := by ring
    rw [hring, heq1, heq2, heq3, heq4]
  rw [hexpand] at hsq
  exact hsq

/-- The final combination: steps (b), (c) turn the squared root bound (at
`h`) into the target display (at `L`), with `c = c_r²/2¹⁰`. -/
private lemma sstarLower_final_combine {c_r M alpha cStar nu S : ℝ} {L h : ℕ}
    (hcr : 0 < c_r) (hcStar : 0 < cStar) (hnu : 0 < nu)
    (hLh : (L:ℝ) ≤ 2 * (h:ℝ)) (hlogL_pos : 0 < Real.log (L:ℝ))
    (hlog_nuinvh_pos : 0 < Real.log (nu⁻¹ * (h:ℝ)))
    (hlog_nuinvh_le : Real.log (nu⁻¹ * (h:ℝ)) ≤ 2 * Real.log (L:ℝ))
    (hSquared : c_r ^ (2:ℕ) * cStar ^ (3:ℝ) * nu ^ (4:ℝ) * (h:ℝ) *
        Real.log (nu⁻¹ * (h:ℝ)) ^ (-(9:ℝ)) ≤ S ^ (2:ℕ))
    (hAbsorb : M * (L:ℝ) ^ alpha * Real.log (L:ℝ) ^ (3:ℝ) ≤
        cStar ^ (3:ℝ) * nu ^ (4:ℝ) * (L:ℝ) * Real.log (L:ℝ) ^ (-(9:ℝ))) :
    (c_r ^ 2 / 2 ^ 10) * M * (L:ℝ) ^ alpha * Real.log (L:ℝ) ^ (3:ℝ) ≤ S ^ (2:ℕ) := by
  have hpow_ge : (2 * Real.log (L:ℝ)) ^ (-(9:ℝ)) ≤ Real.log (nu⁻¹ * (h:ℝ)) ^ (-(9:ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hlog_nuinvh_pos hlog_nuinvh_le (by norm_num)
  have hcr2_nonneg : (0:ℝ) ≤ c_r ^ (2:ℕ) := by positivity
  have hcube_nonneg : (0:ℝ) ≤ cStar ^ (3:ℝ) := Real.rpow_nonneg hcStar.le _
  have hnu4_nonneg : (0:ℝ) ≤ nu ^ (4:ℝ) := Real.rpow_nonneg hnu.le _
  have hhnn : (0:ℝ) ≤ (h:ℝ) := Nat.cast_nonneg h
  have hcoef_nonneg : (0:ℝ) ≤ c_r ^ (2:ℕ) * cStar ^ (3:ℝ) * nu ^ (4:ℝ) * (h:ℝ) := by positivity
  have hstepA : c_r ^ (2:ℕ) * cStar ^ (3:ℝ) * nu ^ (4:ℝ) * (h:ℝ) *
      (2 * Real.log (L:ℝ)) ^ (-(9:ℝ)) ≤
      c_r ^ (2:ℕ) * cStar ^ (3:ℝ) * nu ^ (4:ℝ) * (h:ℝ) * Real.log (nu⁻¹ * (h:ℝ)) ^ (-(9:ℝ)) :=
    mul_le_mul_of_nonneg_left hpow_ge hcoef_nonneg
  have hstepB : c_r ^ (2:ℕ) * cStar ^ (3:ℝ) * nu ^ (4:ℝ) * (h:ℝ) *
      (2 * Real.log (L:ℝ)) ^ (-(9:ℝ)) ≤ S ^ (2:ℕ) := le_trans hstepA hSquared
  have h2rpow_eq : (2 * Real.log (L:ℝ)) ^ (-(9:ℝ)) =
      (2:ℝ) ^ (-(9:ℝ)) * Real.log (L:ℝ) ^ (-(9:ℝ)) :=
    Real.mul_rpow (by norm_num) hlogL_pos.le
  rw [h2rpow_eq] at hstepB
  -- `h ≥ L/2`.
  have hhalf : (L:ℝ) / 2 ≤ (h:ℝ) := by linarith only [hLh]
  have hlogLpow_nonneg : (0:ℝ) ≤ Real.log (L:ℝ) ^ (-(9:ℝ)) := Real.rpow_nonneg hlogL_pos.le _
  have hcube4_nonneg : (0:ℝ) ≤ cStar ^ (3:ℝ) * nu ^ (4:ℝ) * Real.log (L:ℝ) ^ (-(9:ℝ)) := by
    have := mul_nonneg hcube_nonneg hnu4_nonneg
    exact mul_nonneg this hlogLpow_nonneg
  have hhbound : cStar ^ (3:ℝ) * nu ^ (4:ℝ) * ((L:ℝ) / 2) * Real.log (L:ℝ) ^ (-(9:ℝ)) ≤
      cStar ^ (3:ℝ) * nu ^ (4:ℝ) * (h:ℝ) * Real.log (L:ℝ) ^ (-(9:ℝ)) := by
    have h1 : cStar ^ (3:ℝ) * nu ^ (4:ℝ) * ((L:ℝ)/2) ≤ cStar ^ (3:ℝ) * nu ^ (4:ℝ) * (h:ℝ) := by
      have hmul_nonneg := mul_nonneg hcube_nonneg hnu4_nonneg
      exact mul_le_mul_of_nonneg_left hhalf hmul_nonneg
    exact mul_le_mul_of_nonneg_right h1 hlogLpow_nonneg
  have heqhalf : cStar ^ (3:ℝ) * nu ^ (4:ℝ) * ((L:ℝ)/2) * Real.log (L:ℝ) ^ (-(9:ℝ)) =
      (cStar ^ (3:ℝ) * nu ^ (4:ℝ) * (L:ℝ) * Real.log (L:ℝ) ^ (-(9:ℝ))) / 2 := by ring
  have hAbsorbHalf : M * (L:ℝ) ^ alpha * Real.log (L:ℝ) ^ (3:ℝ) / 2 ≤
      cStar ^ (3:ℝ) * nu ^ (4:ℝ) * ((L:ℝ)/2) * Real.log (L:ℝ) ^ (-(9:ℝ)) := by
    rw [heqhalf]; linarith only [hAbsorb]
  have hfinalChain : M * (L:ℝ) ^ alpha * Real.log (L:ℝ) ^ (3:ℝ) / 2 ≤
      cStar ^ (3:ℝ) * nu ^ (4:ℝ) * (h:ℝ) * Real.log (L:ℝ) ^ (-(9:ℝ)) :=
    le_trans hAbsorbHalf hhbound
  have hscaleFinal : c_r ^ (2:ℕ) * (2:ℝ) ^ (-(9:ℝ)) * (M * (L:ℝ) ^ alpha * Real.log (L:ℝ) ^ (3:ℝ) / 2) ≤
      c_r ^ (2:ℕ) * (2:ℝ) ^ (-(9:ℝ)) *
        (cStar ^ (3:ℝ) * nu ^ (4:ℝ) * (h:ℝ) * Real.log (L:ℝ) ^ (-(9:ℝ))) := by
    have hcoef2_nonneg : (0:ℝ) ≤ c_r ^ (2:ℕ) * (2:ℝ) ^ (-(9:ℝ)) := by positivity
    exact mul_le_mul_of_nonneg_left hfinalChain hcoef2_nonneg
  have hLHSeq : c_r ^ (2:ℕ) * (2:ℝ) ^ (-(9:ℝ)) *
      (M * (L:ℝ) ^ alpha * Real.log (L:ℝ) ^ (3:ℝ) / 2) =
      (c_r ^ 2 / 2 ^ 10) * M * (L:ℝ) ^ alpha * Real.log (L:ℝ) ^ (3:ℝ) := by
    have h29 : (2:ℝ) ^ (-(9:ℝ)) = ((2:ℝ) ^ (9:ℕ))⁻¹ := by
      rw [Real.rpow_neg (by norm_num), show (9:ℝ) = ((9:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    rw [h29]
    have hpow210 : (2:ℝ) ^ (10:ℕ) = (2:ℝ) ^ (9:ℕ) * 2 := by ring
    rw [show c_r ^ 2 = c_r ^ (2:ℕ) by norm_num]
    field_simp
  have hRHSeq : c_r ^ (2:ℕ) * (2:ℝ) ^ (-(9:ℝ)) *
      (cStar ^ (3:ℝ) * nu ^ (4:ℝ) * (h:ℝ) * Real.log (L:ℝ) ^ (-(9:ℝ))) =
      c_r ^ (2:ℕ) * cStar ^ (3:ℝ) * nu ^ (4:ℝ) * (h:ℝ) *
        ((2:ℝ) ^ (-(9:ℝ)) * Real.log (L:ℝ) ^ (-(9:ℝ))) := by ring
  rw [hLHSeq, hRHSeq] at hscaleFinal
  exact le_trans hscaleFinal hstepB

/-! ## The main theorem: `e.L.vs.Lnaught` -/

/-- **`e.L.vs.Lnaught`**:
`L ≥ L₀(M,α,c⋆,ν,K)` forces the lower bound `inf_{h∈[L/2,L]} σ̄²_{L,*}(cu_h) ≥
c(d) M L^α log³L`, with the explicit witness `c = c_r²/2¹⁰` (`c_r` the constant of
`sigmaBarStar_lower_bound`). Proved from
`sigmaBarStar_lower_bound` (`p.sstar.lower.bound`) via: (a) `sstarLower_h_clears_threshold`,
so `h` clears the threshold of that theorem; (b) `sstarLower_nuinv_le_L` /
`sstarLower_log_nuinvh_le`, so `log(ν⁻¹h) ≤ 2 log L`; (c)
`sstarLower_absorption`, the exact algebraic identity `M L^α log³L ≤ c⋆³ν⁴L
log⁻⁹L` from `lNaught_threshold`'s first conjunct. -/
theorem lNaught_sstar_lower (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∃ c : ℝ, 0 < c ∧
      ∀ C : ℝ, C₀ ≤ C →
      ∀ M : ℝ, 1 ≤ M → ∀ alpha : ℝ, 0 ≤ alpha → alpha < 1 →
      ∀ cStar : ℝ, 0 < cStar → cStar ≤ 2 →
      ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
      ∀ K : ℝ, 0 ≤ K →
      ∀ (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
        (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
        (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
        (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
      ∀ L : ℕ, SuperdiffusionCLT.Frozen.Section4.lNaught C M alpha cStar nu K ≤ (L : ℝ) →
      ∀ h : ℕ, (L : ℝ) ≤ 2 * (h : ℝ) → h ≤ L →
        c * M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤
          SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
            (Homogenization.cubeSet (Homogenization.originCube d (h : ℤ))) ^ 2 := by
  obtain ⟨C_r, hCr1, c_r, hcrpos, hcrle, Hroot⟩ :=
    SuperdiffusionCLT.Frozen.Section3.sigmaBarStar_lower_bound d hd
  obtain ⟨C1, hC1_1, hThresh⟩ := lNaught_threshold
  obtain ⟨C2, hC2_1, hAbs⟩ := lNaught_absorbs
  obtain ⟨C3, hC3_1, hGeFn⟩ := lNaught_ge
  refine ⟨max (2 * C_r * sstarLowerKappa0) (max C1 (max C2 C3)), ?_, c_r ^ 2 / 2 ^ 10, ?_, ?_⟩
  · calc (1:ℝ) ≤ C1 := hC1_1
      _ ≤ max C1 (max C2 C3) := le_max_left _ _
      _ ≤ max (2 * C_r * sstarLowerKappa0) (max C1 (max C2 C3)) := le_max_right _ _
  · positivity
  · intro C hC M hM alpha halpha0 halpha1 cStar hcStar hcStar2 nu hnu hnu1 K hK
      P hPrefix hJ2 hJ3 hJ1V2 hJ4 hJ5 L hL h hLh hhL
    have hC_a : 2 * C_r * sstarLowerKappa0 ≤ C := le_trans (le_max_left _ _) hC
    have hC_Y : max C1 (max C2 C3) ≤ C := le_trans (le_max_right _ _) hC
    have hC_C1 : C1 ≤ C := le_trans (le_max_left _ _) hC_Y
    have hC23 : max C2 C3 ≤ C := le_trans (le_max_right _ _) hC_Y
    have hC_C2 : C2 ≤ C := le_trans (le_max_left _ _) hC23
    have hC_C3 : C3 ≤ C := le_trans (le_max_right _ _) hC23
    -- Step (a): `h` clears the root's own threshold.
    have hRootThresh := sstarLower_h_clears_threshold hCr1 hC_a hM halpha0 halpha1 hcStar hcStar2
      hnu hnu1 hK hL hLh
    have hLh_nat : L ≤ 2 * h := by exact_mod_cast hLh
    have hRoot := Hroot nu cStar K hnu hnu1 P hPrefix hJ2 hJ3 hJ1V2 hJ4 hJ5 L h hhL hLh_nat
      hRootThresh
    obtain ⟨⟨_, hAnnealed⟩, _⟩ := hRoot
    -- `L > 8`.
    have hLgt8 : (8:ℝ) < (L:ℝ) :=
      lt_of_lt_of_le (hGeFn C hC_C3 M hM alpha halpha0 halpha1 cStar hcStar hcStar2 nu hnu hnu1 K hK)
        hL
    have hLgt8_nat : 8 < L := by exact_mod_cast hLgt8
    have hhge5 : 5 ≤ h := by omega
    have hhpos_nat : 0 < h := by omega
    -- `log(ν⁻¹h) > 0`.
    have hnuinv_ge1 : (1:ℝ) ≤ nu⁻¹ := by
      have h1 := mul_le_mul_of_nonneg_right hnu1 (inv_nonneg.mpr hnu.le)
      rw [mul_inv_cancel₀ hnu.ne'] at h1
      linarith only [h1]
    have hhge5R : (5:ℝ) ≤ (h:ℝ) := by exact_mod_cast hhge5
    have hnuinvh_ge5 : (5:ℝ) ≤ nu⁻¹ * (h:ℝ) := by
      calc (5:ℝ) = 1 * 5 := by ring
        _ ≤ nu⁻¹ * (h:ℝ) :=
          mul_le_mul hnuinv_ge1 hhge5R (by norm_num) (by linarith only [hnuinv_ge1])
    have hlognuinvh_pos : (0:ℝ) < Real.log (nu⁻¹ * (h:ℝ)) := Real.log_pos (by linarith only [hnuinvh_ge5])
    have hSquared := sstarLower_square_root_bound hcrpos hcStar hnu hhpos_nat hlognuinvh_pos hAnnealed
    -- Steps (b), (c): `lNaught_threshold`'s first conjunct.
    obtain ⟨hThresh1, _⟩ := hThresh C hC_C1 M hM alpha halpha0 halpha1 cStar hcStar hcStar2 nu hnu
      hnu1 K hK L hL
    have hnuinvL := sstarLower_nuinv_le_L hM halpha0 hcStar hcStar2 hnu hLgt8 hThresh1
    have hlognuinvh_le := sstarLower_log_nuinvh_le hnu hnuinvL hhL hLgt8 hhpos_nat
    have hAbsorb := sstarLower_absorption hcStar hnu hLgt8 hThresh1
    have hlogLpos : (0:ℝ) < Real.log (L:ℝ) := by
      have h8 : Real.log 8 ≤ Real.log (L:ℝ) := Real.log_le_log (by norm_num) hLgt8.le
      have hlog8 : (2:ℝ) < Real.log 8 := by
        have heq : Real.log 8 = 3 * Real.log 2 := by
          rw [show (8:ℝ) = (2:ℝ) ^ (3:ℕ) by norm_num, Real.log_pow]; push_cast; ring
        rw [heq]; linarith only [Real.log_two_gt_d9]
      linarith only [h8, hlog8]
    exact sstarLower_final_combine hcrpos hcStar hnu hLh hlogLpos hlognuinvh_pos hlognuinvh_le
      hSquared hAbsorb

end SuperdiffusionCLT.Section4.LNaught
