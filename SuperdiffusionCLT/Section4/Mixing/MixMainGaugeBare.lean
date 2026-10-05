/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.Mixing.TermGaugeFinalB
public import SuperdiffusionCLT.Section4.Mixing.MixMainAbsorb
public import SuperdiffusionCLT.Section3.Setup.CrudeBounds

/-!
# The `X3g` witness of `TermGaugeFinalB.lean`: absorption into the bare `C · m^{-5000}` amplitude

Remaining step (i) of task `smixc`: `TermGaugeFinalB.lean`'s
`mixGaugeFinal_X3g_isBigO` supplies `X3g` at an *explicit* amplitude in
`ell, L, n, nu` and the scale-comparison witness `Ct`, including a genuine
`P`-dependent factor `sigmaBarStarInvScalar nu L P (cu_n)` (`tL`). This file
repeats `MixMainTerm1Bare.lean`'s absorption argument for this amplitude,
using the crude uniform bound `tL ≤ nu⁻¹`
(`SuperdiffusionCLT.Section3.Setup.sigmaBarStarInvSeq_le_nuInv`) to fold
`tL` into the same `Y := nu⁻¹ · L` scale used throughout the absorption
machinery, so the result stays pure real analysis in `Y` (no dependence on
`P` beyond the single crude scalar bound).

At the canonical threshold `K₀ := 50100 / log 3` (the same one
`MixMainTerm1Bare.lean` uses), the three summands of `X3g`'s amplitude have
`Y`-exponents `7/2 - c'`, `5 - c'`, `7 - 2c'` (`c' := K₀ log 3 / 10 = 5010`),
all `≤ -5000`, so the same three-step recipe (bound the exponential decay
`3^{-(ell-n)}` and the polynomial factors by fixed powers of `Y`, then
convert `Y^a ≤ m^{-5000}` via `mixMain_rpow_le_of_le_mul` using the case-guard
bound `m ≤ Bm · Y`) applies verbatim. -/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

open Homogenization
open Homogenization.IndependentSums
open SuperdiffusionCLT.Section2.Cutoff (finiteShellIncrement)
open SuperdiffusionCLT.Section2.Estimates.Stream

noncomputable section

/-- **The `X3g`-amplitude absorption core**, generic in the scale-comparison
witness constant `Ct ≥ 1` (the output of the scale conversion) and in the
`P`-dependent scalar `tL := sigmaBarStarInvScalar nu L P (cu_n)`, taken here
as an abstract nonnegative real bounded by `nu⁻¹` (discharged at the call site
by `SuperdiffusionCLT.Section3.Setup.sigmaBarStarInvSeq_le_nuInv`). -/
theorem mixGaugeAbsorb_X3g_amplitude_bound (d : ℕ) (K : ℝ)
    (hK : 50100 / Real.log 3 ≤ K) (Ct : ℝ) (hCt1 : 1 ≤ Ct) :
    ∃ C' : ℝ, 0 ≤ C' ∧
      ∀ (nu : ℝ) (L m n ell : ℕ) (tL : ℝ), 0 < nu → nu ≤ 1 → 1 ≤ L → 1 ≤ m → ell ≤ L →
        0 ≤ tL → tL ≤ nu⁻¹ →
        (K / 10 * Real.log (nu⁻¹ * (L : ℝ)) ≤ ((ell - n : ℕ) : ℝ)) →
        ((m : ℝ) ≤ (L : ℝ) + K / 2 * Real.log (nu⁻¹ * (L : ℝ))) →
        gammaTriangleConst ((1 : ℝ) / 3) *
            (4 * (nu⁻¹ * gammaMomentConst 1 *
                  (Ct * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((ell - n : ℕ) : ℕ) : ℝ)))) *
                (gammaTriangleConst 2 *
                  ((d : ℝ) * finiteShellIncrementPthMomentConst d 1 *
                    Real.sqrt (((L - ell : ℕ) : ℕ) : ℝ))) +
              (4 * tL *
                    (nu⁻¹ * gammaMomentConst 1 *
                      (Ct * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((ell - n : ℕ) : ℕ) : ℝ)))) +
                  2 * (nu⁻¹ * gammaMomentConst 1 *
                      (Ct * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((ell - n : ℕ) : ℕ) : ℝ)))) ^ 2) *
                (gammaTriangleConst 1 *
                  ((d : ℝ) ^ 2 * finiteShellIncrementPthMomentConst d 2 ^ 2 *
                    (((L - ell : ℕ) : ℕ) : ℝ)))) ≤
          C' * (m : ℝ) ^ (-(5000 : ℝ)) := by
  have hlog3_pos : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hK0 : 0 ≤ K := le_trans (by positivity) hK
  set Bm : ℝ := 1 + K / 2 with hBmdef
  have hBm1 : (1 : ℝ) ≤ Bm := by rw [hBmdef]; linarith only [hK0]
  have hBm_pos : (0 : ℝ) < Bm := lt_of_lt_of_le (by norm_num) hBm1
  set c' : ℝ := K * Real.log 3 / 10 with hc'def
  have hc'_ge : (5010 : ℝ) ≤ c' := by
    rw [hc'def]
    have hK' : (50100 : ℝ) ≤ K * Real.log 3 := (div_le_iff₀ hlog3_pos).1 hK
    linarith only [hK']
  have hCt_nn : (0 : ℝ) ≤ Ct := le_trans zero_le_one hCt1
  have hGM_nn : (0 : ℝ) ≤ gammaMomentConst (1 : ℝ) := (gammaMomentConst_pos (by norm_num)).le
  have hTri2_nn : (0 : ℝ) ≤ gammaTriangleConst 2 := gammaTriangleConst_pos.le
  have hTri1_nn : (0 : ℝ) ≤ gammaTriangleConst 1 := gammaTriangleConst_pos.le
  have hTri13_nn : (0 : ℝ) ≤ gammaTriangleConst ((1 : ℝ) / 3) := gammaTriangleConst_pos.le
  have hK1_nn : (0 : ℝ) ≤ finiteShellIncrementPthMomentConst d 1 :=
    SuperdiffusionCLT.Section2.Estimates.Stream.finiteShellIncrementPthMomentConst_nonneg d
      (le_refl 1)
  have hK2_nn : (0 : ℝ) ≤ finiteShellIncrementPthMomentConst d 2 :=
    SuperdiffusionCLT.Section2.Estimates.Stream.finiteShellIncrementPthMomentConst_nonneg d
      (by norm_num)
  set A1c : ℝ := gammaTriangleConst 2 * ((d : ℝ) * finiteShellIncrementPthMomentConst d 1)
    with hA1cdef
  set A2c : ℝ := gammaTriangleConst 1 * ((d : ℝ) ^ 2 * finiteShellIncrementPthMomentConst d 2 ^ 2)
    with hA2cdef
  have hA1c_nn : (0 : ℝ) ≤ A1c := by
    rw [hA1cdef]; positivity
  have hA2c_nn : (0 : ℝ) ≤ A2c := by
    rw [hA2cdef]; positivity
  set E0 : ℝ := gammaMomentConst (1 : ℝ) * Ct with hE0def
  have hE0_nn : (0 : ℝ) ≤ E0 := mul_nonneg hGM_nn hCt_nn
  -- The three target exponents, all `≤ -5000` at `c' ≥ 5010`.
  have haA0 : (7 / 2 - c' : ℝ) ≤ 0 := by linarith only [hc'_ge]
  have haB10 : (5 - c' : ℝ) ≤ 0 := by linarith only [hc'_ge]
  have haB20 : (7 - 2 * c' : ℝ) ≤ 0 := by linarith only [hc'_ge]
  have haA' : (7 / 2 - c' : ℝ) ≤ -(5000 : ℝ) := by linarith only [hc'_ge]
  have haB1' : (5 - c' : ℝ) ≤ -(5000 : ℝ) := by linarith only [hc'_ge]
  have haB2' : (7 - 2 * c' : ℝ) ≤ -(5000 : ℝ) := by linarith only [hc'_ge]
  refine ⟨gammaTriangleConst ((1 : ℝ) / 3) *
      (4 * E0 * A1c * Bm ^ (-(7 / 2 - c')) + 4 * E0 * A2c * Bm ^ (-(5 - c')) +
        2 * E0 ^ 2 * A2c * Bm ^ (-(7 - 2 * c'))), ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ Bm ^ (-(7 / 2 - c')) := Real.rpow_nonneg hBm_pos.le _
    have h2 : (0 : ℝ) ≤ Bm ^ (-(5 - c')) := Real.rpow_nonneg hBm_pos.le _
    have h3 : (0 : ℝ) ≤ Bm ^ (-(7 - 2 * c')) := Real.rpow_nonneg hBm_pos.le _
    have hE0sq_nn : (0 : ℝ) ≤ E0 ^ 2 := sq_nonneg _
    positivity
  · intro nu L m n ell tL hnu hnu1 hL1 hm1 hellL htL_nn htL_le hgap1 hcase
    set Y : ℝ := nu⁻¹ * (L : ℝ) with hYdef
    have hnuinv1 : (1 : ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
    have hLcast : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
    have hY1 : (1 : ℝ) ≤ Y := by
      rw [hYdef]
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ nu⁻¹ * (L : ℝ) := mul_le_mul hnuinv1 hLcast (by norm_num) (by linarith only [hnuinv1])
    have hY_pos : (0 : ℝ) < Y := lt_of_lt_of_le (by norm_num) hY1
    have hnuinv_le_Y : nu⁻¹ ≤ Y := by
      rw [hYdef]; calc nu⁻¹ = nu⁻¹ * 1 := by ring
        _ ≤ nu⁻¹ * (L : ℝ) := mul_le_mul_of_nonneg_left hLcast (by positivity)
    have hL_le_Y : (L : ℝ) ≤ Y := by
      rw [hYdef]; calc (L : ℝ) = 1 * (L : ℝ) := by ring
        _ ≤ nu⁻¹ * (L : ℝ) := mul_le_mul_of_nonneg_right hnuinv1 (by linarith only [hLcast])
    have htL_le_Y : tL ≤ Y := htL_le.trans hnuinv_le_Y
    have hm_le_BmY : (m : ℝ) ≤ Bm * Y := by
      have := mixMain_m_le_mul_nuInvL hnu hnu1 hK0 hL1 hcase
      rw [hYdef]; exact this
    have hLellcast : (((L - ell : ℕ) : ℕ) : ℝ) ≤ Y := by
      have h1 : ((L - ell : ℕ) : ℝ) ≤ (L : ℝ) := by exact_mod_cast Nat.sub_le L ell
      exact h1.trans hL_le_Y
    have hLellnn : (0 : ℝ) ≤ (((L - ell : ℕ) : ℕ) : ℝ) := by positivity
    have hsqrtLellY : Real.sqrt (((L - ell : ℕ) : ℕ) : ℝ) ≤ Y ^ ((1 : ℝ) / 2) := by
      rw [show Y ^ ((1 : ℝ) / 2) = Real.sqrt Y from (Real.sqrt_eq_rpow Y).symm]
      exact Real.sqrt_le_sqrt hLellcast
    have hlogY_nonneg : 0 ≤ Real.log Y := Real.log_nonneg hY1
    have hexp1 : (3 : ℝ) ^ (-(((ell - n : ℕ) : ℕ) : ℝ)) ≤ Y ^ (-c') := by
      have hstep : (3 : ℝ) ^ (-(((ell - n : ℕ) : ℕ) : ℝ)) ≤ (3 : ℝ) ^ (-(K / 10 * Real.log Y)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hgap1])
      have heq : (3 : ℝ) ^ (-(K / 10 * Real.log Y)) = Y ^ (-c') := by
        rw [hc'def]; exact mixMain_gammaLog_eq_rpow (c := K) hY_pos
      linarith only [hstep, heq.le, heq.ge]
    have hnu2_le : nu ^ (-(2 : ℝ)) ≤ Y ^ (2 : ℝ) := by
      have hnu2eq : nu ^ (-(2 : ℝ)) = (nu⁻¹) ^ (2 : ℝ) := by
        rw [Real.rpow_neg hnu.le, ← Real.inv_rpow hnu.le]
      rw [hnu2eq]
      exact Real.rpow_le_rpow (by positivity) hnuinv_le_Y (by norm_num)
    have hnu2_nn : (0 : ℝ) ≤ nu ^ (-(2 : ℝ)) := Real.rpow_nonneg hnu.le _
    have hYaddc : ∀ a b : ℝ, Y ^ a * Y ^ b = Y ^ (a + b) := fun a b => (Real.rpow_add hY_pos a b).symm
    -- `E ≤ E0 · Y^{3-c'}`.
    have hEraw : nu⁻¹ * gammaMomentConst 1 * (Ct * nu ^ (-(2 : ℝ)) *
        (3 : ℝ) ^ (-(((ell - n : ℕ) : ℕ) : ℝ))) ≤
        Y * gammaMomentConst 1 * (Ct * Y ^ (2 : ℝ) * Y ^ (-c')) := by
      have hEn : (0 : ℝ) ≤ Ct * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((ell - n : ℕ) : ℕ) : ℝ)) :=
        mul_nonneg (mul_nonneg hCt_nn (Real.rpow_nonneg hnu.le _)) (Real.rpow_nonneg (by norm_num) _)
      exact mul_le_mul (mul_le_mul_of_nonneg_right hnuinv_le_Y hGM_nn)
        (mul_le_mul (mul_le_mul_of_nonneg_left hnu2_le hCt_nn) hexp1
          (Real.rpow_nonneg (by norm_num) _) (mul_nonneg hCt_nn (Real.rpow_nonneg hY_pos.le _)))
        hEn (mul_nonneg hY_pos.le hGM_nn)
    have hY3mc : Y * gammaMomentConst 1 * (Ct * Y ^ (2 : ℝ) * Y ^ (-c')) = E0 * Y ^ (3 - c') := by
      rw [hE0def]
      have hcomb : Y ^ (1 : ℝ) * Y ^ (2 : ℝ) * Y ^ (-c') = Y ^ (3 - c') := by
        rw [← Real.rpow_add hY_pos, ← Real.rpow_add hY_pos]
        congr 1; ring
      calc Y * gammaMomentConst 1 * (Ct * Y ^ (2 : ℝ) * Y ^ (-c'))
          = gammaMomentConst 1 * Ct * (Y ^ (1 : ℝ) * Y ^ (2 : ℝ) * Y ^ (-c')) := by
            rw [Real.rpow_one]; ring
        _ = gammaMomentConst 1 * Ct * Y ^ (3 - c') := by rw [hcomb]
    have hE_le : nu⁻¹ * gammaMomentConst 1 * (Ct * nu ^ (-(2 : ℝ)) *
        (3 : ℝ) ^ (-(((ell - n : ℕ) : ℕ) : ℝ))) ≤ E0 * Y ^ (3 - c') := hY3mc ▸ hEraw
    have hE_nn : (0 : ℝ) ≤ nu⁻¹ * gammaMomentConst 1 * (Ct * nu ^ (-(2 : ℝ)) *
        (3 : ℝ) ^ (-(((ell - n : ℕ) : ℕ) : ℝ))) :=
      mul_nonneg (mul_nonneg (inv_nonneg.2 hnu.le) hGM_nn)
        (mul_nonneg (mul_nonneg hCt_nn hnu2_nn) (Real.rpow_nonneg (by norm_num) _))
    have hE0Ypow_nn : (0 : ℝ) ≤ E0 * Y ^ (3 - c') := mul_nonneg hE0_nn (Real.rpow_nonneg hY_pos.le _)
    have hSnn : (0 : ℝ) ≤ Real.sqrt (((L - ell : ℕ) : ℕ) : ℝ) := Real.sqrt_nonneg _
    generalize hExdef : (nu⁻¹ * gammaMomentConst 1 * (Ct * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((ell - n : ℕ) : ℕ) : ℝ)))) = Ex at hE_le hE_nn ⊢
    generalize hSxdef : (Real.sqrt (((L - ell : ℕ) : ℕ) : ℝ)) = Sx at hsqrtLellY hSnn ⊢
    generalize hNxdef : (((L - ell : ℕ) : ℕ) : ℝ) = Nx at hLellcast hLellnn hsqrtLellY ⊢
    -- `TermA := 4 E A1poly ≤ 4 E0 A1c · Y^{7/2 - c'}`.
    have hTermA : 4 * Ex *
        (gammaTriangleConst 2 * ((d : ℝ) * finiteShellIncrementPthMomentConst d 1 *
          Sx)) ≤
        4 * E0 * A1c * Y ^ (7 / 2 - c') := by
      have hstep1 : 4 * Ex *
          (gammaTriangleConst 2 * ((d : ℝ) * finiteShellIncrementPthMomentConst d 1 *
            Sx)) ≤
          4 * (E0 * Y ^ (3 - c')) * (gammaTriangleConst 2 *
            ((d : ℝ) * finiteShellIncrementPthMomentConst d 1 * Y ^ ((1 : ℝ) / 2))) := by
        have hdK1 : (0 : ℝ) ≤ (d : ℝ) * finiteShellIncrementPthMomentConst d 1 :=
          mul_nonneg (Nat.cast_nonneg d) hK1_nn
        exact mul_le_mul (mul_le_mul_of_nonneg_left hE_le (by norm_num))
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsqrtLellY hdK1) hTri2_nn)
          (mul_nonneg hTri2_nn (mul_nonneg hdK1 hSnn))
          (mul_nonneg (by norm_num) hE0Ypow_nn)
      have hstep2 : 4 * (E0 * Y ^ (3 - c')) * (gammaTriangleConst 2 *
          ((d : ℝ) * finiteShellIncrementPthMomentConst d 1 * Y ^ ((1 : ℝ) / 2))) =
          4 * E0 * A1c * Y ^ (7 / 2 - c') := by
        rw [hA1cdef]
        have hcomb : Y ^ (3 - c') * Y ^ ((1 : ℝ) / 2) = Y ^ (7 / 2 - c') := by
          rw [← Real.rpow_add hY_pos]; congr 1; ring
        calc 4 * (E0 * Y ^ (3 - c')) * (gammaTriangleConst 2 *
              ((d : ℝ) * finiteShellIncrementPthMomentConst d 1 * Y ^ ((1 : ℝ) / 2)))
            = 4 * E0 * (gammaTriangleConst 2 * ((d : ℝ) * finiteShellIncrementPthMomentConst d 1)) *
                (Y ^ (3 - c') * Y ^ ((1 : ℝ) / 2)) := by ring
          _ = 4 * E0 * (gammaTriangleConst 2 * ((d : ℝ) * finiteShellIncrementPthMomentConst d 1)) *
                Y ^ (7 / 2 - c') := by rw [hcomb]
      linarith only [hstep1, hstep2.le, hstep2.ge]
    -- `TermB1 := 4 tL E A2poly ≤ 4 E0 A2c · Y^{5-c'}`.
    have hTermB1 : 4 * tL * Ex *
        (gammaTriangleConst 1 * ((d : ℝ) ^ 2 * finiteShellIncrementPthMomentConst d 2 ^ 2 *
          Nx)) ≤
        4 * E0 * A2c * Y ^ (5 - c') := by
      have hstep1 : 4 * tL * Ex *
          (gammaTriangleConst 1 * ((d : ℝ) ^ 2 * finiteShellIncrementPthMomentConst d 2 ^ 2 *
            Nx)) ≤
          4 * Y * (E0 * Y ^ (3 - c')) * (gammaTriangleConst 1 *
            ((d : ℝ) ^ 2 * finiteShellIncrementPthMomentConst d 2 ^ 2 * Y)) := by
        have hD2 : (0 : ℝ) ≤ (d : ℝ) ^ 2 * finiteShellIncrementPthMomentConst d 2 ^ 2 :=
          mul_nonneg (sq_nonneg _) (sq_nonneg _)
        exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left htL_le_Y (by norm_num)) hE_le hE_nn
            (mul_nonneg (by norm_num) hY_pos.le))
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hLellcast hD2) hTri1_nn)
          (mul_nonneg hTri1_nn (mul_nonneg hD2 hLellnn))
          (mul_nonneg (mul_nonneg (by norm_num) hY_pos.le) hE0Ypow_nn)
      have hstep2 : 4 * Y * (E0 * Y ^ (3 - c')) * (gammaTriangleConst 1 *
          ((d : ℝ) ^ 2 * finiteShellIncrementPthMomentConst d 2 ^ 2 * Y)) =
          4 * E0 * A2c * Y ^ (5 - c') := by
        rw [hA2cdef]
        have hcomb : Y ^ (1 : ℝ) * (Y ^ (3 - c') * Y ^ (1 : ℝ)) = Y ^ (5 - c') := by
          rw [← Real.rpow_add hY_pos, ← Real.rpow_add hY_pos]; congr 1; ring
        calc 4 * Y * (E0 * Y ^ (3 - c')) * (gammaTriangleConst 1 *
              ((d : ℝ) ^ 2 * finiteShellIncrementPthMomentConst d 2 ^ 2 * Y))
            = 4 * E0 * (gammaTriangleConst 1 *
                ((d : ℝ) ^ 2 * finiteShellIncrementPthMomentConst d 2 ^ 2)) *
                (Y ^ (1 : ℝ) * (Y ^ (3 - c') * Y ^ (1 : ℝ))) := by
              rw [Real.rpow_one]; ring
          _ = 4 * E0 * (gammaTriangleConst 1 *
                ((d : ℝ) ^ 2 * finiteShellIncrementPthMomentConst d 2 ^ 2)) *
                Y ^ (5 - c') := by rw [hcomb]
      linarith only [hstep1, hstep2.le, hstep2.ge]
    -- `TermB2 := 2 E^2 A2poly ≤ 2 E0^2 A2c · Y^{7-2c'}`.
    have hTermB2 : 2 * Ex ^ 2 *
        (gammaTriangleConst 1 * ((d : ℝ) ^ 2 * finiteShellIncrementPthMomentConst d 2 ^ 2 *
          Nx)) ≤
        2 * E0 ^ 2 * A2c * Y ^ (7 - 2 * c') := by
      have hsqle : Ex ^ 2 ≤ (E0 * Y ^ (3 - c')) ^ 2 :=
        pow_le_pow_left₀ hE_nn hE_le 2
      have hstep1 : 2 * Ex ^ 2 *
          (gammaTriangleConst 1 * ((d : ℝ) ^ 2 * finiteShellIncrementPthMomentConst d 2 ^ 2 *
            Nx)) ≤
          2 * (E0 * Y ^ (3 - c')) ^ 2 * (gammaTriangleConst 1 *
            ((d : ℝ) ^ 2 * finiteShellIncrementPthMomentConst d 2 ^ 2 * Y)) := by
        have hD2 : (0 : ℝ) ≤ (d : ℝ) ^ 2 * finiteShellIncrementPthMomentConst d 2 ^ 2 :=
          mul_nonneg (sq_nonneg _) (sq_nonneg _)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hsqle (by norm_num))
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hLellcast hD2) hTri1_nn)
          (mul_nonneg hTri1_nn (mul_nonneg hD2 hLellnn))
          (mul_nonneg (by norm_num) (sq_nonneg _))
      have hstep2 : 2 * (E0 * Y ^ (3 - c')) ^ 2 * (gammaTriangleConst 1 *
          ((d : ℝ) ^ 2 * finiteShellIncrementPthMomentConst d 2 ^ 2 * Y)) =
          2 * E0 ^ 2 * A2c * Y ^ (7 - 2 * c') := by
        rw [hA2cdef]
        have hcomb : Y ^ (3 - c') * Y ^ (3 - c') * Y ^ (1 : ℝ) = Y ^ (7 - 2 * c') := by
          rw [← Real.rpow_add hY_pos, ← Real.rpow_add hY_pos]; congr 1; ring
        calc 2 * (E0 * Y ^ (3 - c')) ^ 2 * (gammaTriangleConst 1 *
              ((d : ℝ) ^ 2 * finiteShellIncrementPthMomentConst d 2 ^ 2 * Y))
            = 2 * E0 ^ 2 * (gammaTriangleConst 1 *
                ((d : ℝ) ^ 2 * finiteShellIncrementPthMomentConst d 2 ^ 2)) *
                (Y ^ (3 - c') * Y ^ (3 - c') * Y ^ (1 : ℝ)) := by
              rw [Real.rpow_one]; ring
          _ = 2 * E0 ^ 2 * (gammaTriangleConst 1 *
                ((d : ℝ) ^ 2 * finiteShellIncrementPthMomentConst d 2 ^ 2)) *
                Y ^ (7 - 2 * c') := by rw [hcomb]
      linarith only [hstep1, hstep2.le, hstep2.ge]
    -- Absorb the three `Y`-powers into `m^{-5000}`.
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have hm1' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    have hYA1 : Y ^ (7 / 2 - c') ≤ Bm ^ (-(7 / 2 - c')) * (m : ℝ) ^ (7 / 2 - c') :=
      mixMain_rpow_le_of_le_mul hBm_pos hm_pos haA0 hm_le_BmY
    have hYB1 : Y ^ (5 - c') ≤ Bm ^ (-(5 - c')) * (m : ℝ) ^ (5 - c') :=
      mixMain_rpow_le_of_le_mul hBm_pos hm_pos haB10 hm_le_BmY
    have hYB2 : Y ^ (7 - 2 * c') ≤ Bm ^ (-(7 - 2 * c')) * (m : ℝ) ^ (7 - 2 * c') :=
      mixMain_rpow_le_of_le_mul hBm_pos hm_pos haB20 hm_le_BmY
    have hmA1 : (m : ℝ) ^ (7 / 2 - c') ≤ (m : ℝ) ^ (-(5000 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hm1' haA'
    have hmB1 : (m : ℝ) ^ (5 - c') ≤ (m : ℝ) ^ (-(5000 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hm1' haB1'
    have hmB2 : (m : ℝ) ^ (7 - 2 * c') ≤ (m : ℝ) ^ (-(5000 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hm1' haB2'
    have hBmA1_nn : (0 : ℝ) ≤ Bm ^ (-(7 / 2 - c')) := Real.rpow_nonneg hBm_pos.le _
    have hBmB1_nn : (0 : ℝ) ≤ Bm ^ (-(5 - c')) := Real.rpow_nonneg hBm_pos.le _
    have hBmB2_nn : (0 : ℝ) ≤ Bm ^ (-(7 - 2 * c')) := Real.rpow_nonneg hBm_pos.le _
    have hpartA : Y ^ (7 / 2 - c') ≤ Bm ^ (-(7 / 2 - c')) * (m : ℝ) ^ (-(5000 : ℝ)) :=
      hYA1.trans (mul_le_mul_of_nonneg_left hmA1 hBmA1_nn)
    have hpartB1 : Y ^ (5 - c') ≤ Bm ^ (-(5 - c')) * (m : ℝ) ^ (-(5000 : ℝ)) :=
      hYB1.trans (mul_le_mul_of_nonneg_left hmB1 hBmB1_nn)
    have hpartB2 : Y ^ (7 - 2 * c') ≤ Bm ^ (-(7 - 2 * c')) * (m : ℝ) ^ (-(5000 : ℝ)) :=
      hYB2.trans (mul_le_mul_of_nonneg_left hmB2 hBmB2_nn)
    have hE0A1c_nn : (0 : ℝ) ≤ 4 * E0 * A1c := mul_nonneg (mul_nonneg (by norm_num) hE0_nn) hA1c_nn
    have hE0A2c_nn : (0 : ℝ) ≤ 4 * E0 * A2c := mul_nonneg (mul_nonneg (by norm_num) hE0_nn) hA2c_nn
    have hE0sqA2c_nn : (0 : ℝ) ≤ 2 * E0 ^ 2 * A2c :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hA2c_nn
    have hfinA : 4 * E0 * A1c * Y ^ (7 / 2 - c') ≤
        4 * E0 * A1c * (Bm ^ (-(7 / 2 - c')) * (m : ℝ) ^ (-(5000 : ℝ))) :=
      mul_le_mul_of_nonneg_left hpartA hE0A1c_nn
    have hfinB1 : 4 * E0 * A2c * Y ^ (5 - c') ≤
        4 * E0 * A2c * (Bm ^ (-(5 - c')) * (m : ℝ) ^ (-(5000 : ℝ))) :=
      mul_le_mul_of_nonneg_left hpartB1 hE0A2c_nn
    have hfinB2 : 2 * E0 ^ 2 * A2c * Y ^ (7 - 2 * c') ≤
        2 * E0 ^ 2 * A2c * (Bm ^ (-(7 - 2 * c')) * (m : ℝ) ^ (-(5000 : ℝ))) :=
      mul_le_mul_of_nonneg_left hpartB2 hE0sqA2c_nn
    have hTri13_nn' := hTri13_nn
    have hsum : 4 * Ex *
          (gammaTriangleConst 2 * ((d : ℝ) * finiteShellIncrementPthMomentConst d 1 *
            Sx)) +
        (4 * tL * Ex +
            2 * Ex ^ 2) *
          (gammaTriangleConst 1 * ((d : ℝ) ^ 2 * finiteShellIncrementPthMomentConst d 2 ^ 2 *
            Nx)) ≤
        (4 * E0 * A1c * (Bm ^ (-(7 / 2 - c')) * (m : ℝ) ^ (-(5000 : ℝ))) +
          4 * E0 * A2c * (Bm ^ (-(5 - c')) * (m : ℝ) ^ (-(5000 : ℝ)))) +
          2 * E0 ^ 2 * A2c * (Bm ^ (-(7 - 2 * c')) * (m : ℝ) ^ (-(5000 : ℝ))) := by
      have hexpand : (4 * tL * Ex +
            2 * Ex ^ 2) *
          (gammaTriangleConst 1 * ((d : ℝ) ^ 2 * finiteShellIncrementPthMomentConst d 2 ^ 2 *
            Nx)) =
          4 * tL * Ex *
              (gammaTriangleConst 1 * ((d : ℝ) ^ 2 * finiteShellIncrementPthMomentConst d 2 ^ 2 *
                Nx)) +
            2 * Ex ^ 2 *
              (gammaTriangleConst 1 * ((d : ℝ) ^ 2 * finiteShellIncrementPthMomentConst d 2 ^ 2 *
                Nx)) := by ring
      rw [hexpand]
      linarith only [hTermA, hfinA, hTermB1, hfinB1, hTermB2, hfinB2]
    have hscaled := mul_le_mul_of_nonneg_left hsum hTri13_nn'
    have heqRHS : gammaTriangleConst ((1 : ℝ) / 3) *
        ((4 * E0 * A1c * (Bm ^ (-(7 / 2 - c')) * (m : ℝ) ^ (-(5000 : ℝ))) +
            4 * E0 * A2c * (Bm ^ (-(5 - c')) * (m : ℝ) ^ (-(5000 : ℝ)))) +
          2 * E0 ^ 2 * A2c * (Bm ^ (-(7 - 2 * c')) * (m : ℝ) ^ (-(5000 : ℝ)))) =
        gammaTriangleConst ((1 : ℝ) / 3) *
            (4 * E0 * A1c * Bm ^ (-(7 / 2 - c')) + 4 * E0 * A2c * Bm ^ (-(5 - c')) +
              2 * E0 ^ 2 * A2c * Bm ^ (-(7 - 2 * c'))) *
          (m : ℝ) ^ (-(5000 : ℝ)) := by ring
    linarith only [hscaled, heqRHS.le, heqRHS.ge]

end

end SuperdiffusionCLT.Section4.Mixing
