/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Scale arithmetic for the reference comparison

Elementary real inequalities relating a scale `a` with `L/2 ≤ a ≤ 2 L` to `L`, and the
bounds on the error of `p.homog.below` at the scale `a` used by the reference comparison.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.NewMixing

noncomputable section

/-- Comparisons between `L` and a scale `a` with `L/2 ≤ a ≤ 2L`, `L ≥ 8`. -/
theorem newMixAsm_scale_facts {L a alpha : ℝ} (hL : 8 ≤ L) (ha1 : L / 2 ≤ a)
    (ha2 : a ≤ 2 * L) (hα0 : 0 ≤ alpha) (hα1 : alpha < 1) :
    1 ≤ a ^ alpha ∧ L ^ alpha ≤ 2 * a ^ alpha ∧ 1 ≤ Real.log a ∧
      Real.log a ≤ 2 * Real.log L ∧ Real.log L ≤ 2 * Real.log a ∧ 1 ≤ Real.log L := by
  have ha4 : 4 ≤ a := by linarith only [ha1, hL]
  have hapos : 0 < a := by linarith only [ha4]
  have hLpos : 0 < L := by linarith only [hL]
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2' : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlogL8 : Real.log 8 ≤ Real.log L := Real.log_le_log (by norm_num) hL
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have hlogL1 : 1 ≤ Real.log L := by linarith only [hlogL8, hlog8, hlog2]
  have hloga4 : Real.log 4 ≤ Real.log a := Real.log_le_log (by norm_num) ha4
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hloga1 : 1 ≤ Real.log a := by linarith only [hloga4, hlog4, hlog2]
  have hlog2L : Real.log 2 ≤ Real.log L := by linarith only [hlogL1, hlog2']
  have hlog2a : Real.log 2 ≤ Real.log a := by linarith only [hloga1, hlog2']
  refine ⟨Real.one_le_rpow (by linarith only [ha4]) hα0, ?_, hloga1, ?_, ?_, hlogL1⟩
  · have h1 : L ≤ 2 * a := by linarith only [ha1]
    calc L ^ alpha ≤ (2 * a) ^ alpha := Real.rpow_le_rpow hLpos.le h1 hα0
      _ = 2 ^ alpha * a ^ alpha := Real.mul_rpow (by norm_num) hapos.le
      _ ≤ 2 ^ (1 : ℝ) * a ^ alpha := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hapos.le _)
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hα1.le
      _ = 2 * a ^ alpha := by rw [Real.rpow_one]
  · have : Real.log a ≤ Real.log (2 * L) := Real.log_le_log hapos ha2
    rw [Real.log_mul (by norm_num) hLpos.ne'] at this
    linarith only [this, hlog2L]
  · have h1 : L ≤ 2 * a := by linarith only [ha1]
    have : Real.log L ≤ Real.log (2 * a) := Real.log_le_log hLpos h1
    rw [Real.log_mul (by norm_num) hapos.ne'] at this
    linarith only [this, hlog2a]

/-- The `n^{-3000}` term against the absorbed `a^{-99}` term, when `a ≤ 8 n`. -/
theorem newMixAsm_n_neg3000_le {a n : ℝ} (ha1 : 1 ≤ a) (hn : a / 8 ≤ n) :
    n ^ (-(3000 : ℝ)) ≤ (8 : ℝ) ^ (3000 : ℕ) * a ^ (-(99 : ℝ)) := by
  have hapos : 0 < a := by linarith only [ha1]
  have h8 : 0 < a / 8 := by positivity
  have h1 : n ^ (-(3000 : ℝ)) ≤ (a / 8) ^ (-(3000 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos h8 hn (by norm_num)
  have h2 : (a / 8) ^ (-(3000 : ℝ)) = (8 : ℝ) ^ (3000 : ℕ) * a ^ (-(3000 : ℝ)) := by
    rw [Real.rpow_neg h8.le, Real.rpow_neg hapos.le,
      show (3000 : ℝ) = ((3000 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.rpow_natCast,
      div_pow]
    field_simp
  have h3 : a ^ (-(3000 : ℝ)) ≤ a ^ (-(99 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le ha1 (by norm_num)
  have h4 : (0 : ℝ) ≤ (8 : ℝ) ^ (3000 : ℕ) := by positivity
  calc n ^ (-(3000 : ℝ)) ≤ (a / 8) ^ (-(3000 : ℝ)) := h1
    _ = (8 : ℝ) ^ (3000 : ℕ) * a ^ (-(3000 : ℝ)) := h2
    _ ≤ (8 : ℝ) ^ (3000 : ℕ) * a ^ (-(99 : ℝ)) := mul_le_mul_of_nonneg_left h3 h4

private theorem newMixAsm_rpow_three (x : ℝ) : x ^ (3 : ℝ) = x ^ 3 := by
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

private theorem newMixAsm_rpow_two (x : ℝ) : x ^ (2 : ℝ) = x ^ 2 := Real.rpow_two x

/-- The error of `p.homog.below` at a scale `a`, against the printed amplitude and against the
absorbed threshold. -/
theorem newMixAsm_perCutoff {s Chom Cabs Cg K M M1 B8 alpha L a n G : ℝ} (hs : 0 < s)
    (hChom1 : 1 ≤ Chom) (hCg1 : 1 ≤ Cg) (hK1 : 1 ≤ K) (hM1 : 1 ≤ M) (hα0 : 0 ≤ alpha)
    (hα1 : alpha < 1) (hCabsChom : Chom ≤ Cabs) (hCabs8 : Chom * B8 ≤ Cabs)
    (hnpow : n ^ (-(3000 : ℝ)) ≤ B8 * a ^ (-(99 : ℝ)))
    (hL : 8 ≤ L) (ha1 : L / 2 ≤ a) (ha2 : a ≤ 2 * L)
    (hG0 : 0 ≤ G) (hGM : G ≤ M * L ^ alpha * Real.log L ^ (3 : ℝ))
    (hdiff : a - n ≤ G + Cg * K * Real.log L)
    (hM1def : (16 + 2 * Cg + Chom) * (M + K) ≤ M1)
    (hAbs : Cabs * M1 * a ^ alpha * s ^ (-(2 : ℝ)) * Real.log a ^ (3 : ℝ) +
      Cabs * a ^ (-(99 : ℝ)) ≤ 1 / 8) :
    Chom * s ^ (-(2 : ℝ)) * max 0 (a - n + Chom * Real.log a ^ (2 : ℝ)) +
        Chom * n ^ (-(3000 : ℝ)) ≤
      Chom * s ^ (-(2 : ℝ)) * ((1 + Cg + 4 * Chom) * (G + K * Real.log L ^ (2 : ℝ))) +
        Chom * n ^ (-(3000 : ℝ)) ∧
    Chom * s ^ (-(2 : ℝ)) * max 0 (a - n + Chom * Real.log a ^ (2 : ℝ)) +
        Chom * n ^ (-(3000 : ℝ)) ≤ 1 / 8 ∧
    a - M1 * a ^ alpha * Real.log a ^ (3 : ℝ) ≤ n := by
  obtain ⟨hαa, hLa, hloga1, hlogaL, hlogLa, hlogL1⟩ :=
    newMixAsm_scale_facts hL ha1 ha2 hα0 hα1
  have hs2 : 0 ≤ s ^ (-(2 : ℝ)) := Real.rpow_nonneg hs.le _
  have hChom0 : 0 ≤ Chom := by linarith only [hChom1]
  have hCg0 : 0 ≤ Cg := by linarith only [hCg1]
  have hK0 : 0 ≤ K := by linarith only [hK1]
  have hlogL0 : 0 ≤ Real.log L := by linarith only [hlogL1]
  have hloga0 : 0 ≤ Real.log a := by linarith only [hloga1]
  have hL2 : Real.log L ^ (2 : ℝ) = Real.log L ^ 2 := newMixAsm_rpow_two _
  have ha2' : Real.log a ^ (2 : ℝ) = Real.log a ^ 2 := newMixAsm_rpow_two _
  have hL3 : Real.log L ^ (3 : ℝ) = Real.log L ^ 3 := newMixAsm_rpow_three _
  have ha3 : Real.log a ^ (3 : ℝ) = Real.log a ^ 3 := newMixAsm_rpow_three _
  -- the size bound
  have hsize : a - n + Chom * Real.log a ^ (2 : ℝ) ≤
      (1 + Cg + 4 * Chom) * (G + K * Real.log L ^ (2 : ℝ)) := by
    rw [ha2', hL2]
    have h1 : Real.log L ≤ Real.log L ^ 2 := by nlinarith only [hlogL1]
    have h2 : Real.log a ^ 2 ≤ 4 * Real.log L ^ 2 := by nlinarith only [hlogaL, hloga0, hlogL0]
    have h3 : Cg * K * Real.log L ≤ Cg * K * Real.log L ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (mul_nonneg hCg0 hK0)
    have h4 : Chom * Real.log a ^ 2 ≤ Chom * (4 * Real.log L ^ 2) :=
      mul_le_mul_of_nonneg_left h2 hChom0
    have h5 : 4 * Chom * Real.log L ^ 2 ≤ 4 * Chom * (K * Real.log L ^ 2) := by
      have : Real.log L ^ 2 ≤ K * Real.log L ^ 2 :=
        le_mul_of_one_le_left (sq_nonneg _) hK1
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have h6 : G ≤ (1 + Cg + 4 * Chom) * G := by
      have : (1 : ℝ) ≤ 1 + Cg + 4 * Chom := by linarith only [hCg0, hChom0]
      exact le_mul_of_one_le_left hG0 this
    have h7 : Cg * K * Real.log L ^ 2 ≤ Cg * (K * Real.log L ^ 2) := by ring_nf; exact le_refl _
    have hKL : 0 ≤ K * Real.log L ^ 2 := by positivity
    nlinarith only [hdiff, h3, h4, h5, h6, h7, hKL, hCg0, hChom0]
  -- the threshold bound
  have hsmall : a - n + Chom * Real.log a ^ (2 : ℝ) ≤ M1 * a ^ alpha * Real.log a ^ (3 : ℝ) := by
    rw [ha2', ha3]
    have hlogL3 : Real.log L ^ 3 ≤ 8 * Real.log a ^ 3 := by
      have : Real.log L ^ 3 ≤ (2 * Real.log a) ^ 3 :=
        pow_le_pow_left₀ hlogL0 hlogLa 3
      nlinarith only [this]
    have hGM' : G ≤ 16 * M * a ^ alpha * Real.log a ^ 3 := by
      rw [hL3] at hGM
      have h1 : M * L ^ alpha * Real.log L ^ 3 ≤ M * (2 * a ^ alpha) * (8 * Real.log a ^ 3) := by
        have hMn : 0 ≤ M := by linarith only [hM1]
        have hLn : 0 ≤ L ^ alpha := Real.rpow_nonneg (by linarith only [hL]) _
        have h2 : L ^ alpha * Real.log L ^ 3 ≤ (2 * a ^ alpha) * (8 * Real.log a ^ 3) :=
          mul_le_mul hLa hlogL3 (pow_nonneg hlogL0 3) (by positivity)
        have := mul_le_mul_of_nonneg_left h2 hMn
        nlinarith only [this]
      nlinarith only [hGM, h1]
    have hlogLle : Cg * K * Real.log L ≤ 2 * Cg * K * (a ^ alpha * Real.log a ^ 3) := by
      have h1 : Real.log L ≤ 2 * Real.log a ^ 3 := by
        have : Real.log a ≤ Real.log a ^ 3 := by
          nlinarith only [mul_nonneg (mul_nonneg hloga0 (sub_nonneg.mpr hloga1)) (add_nonneg hloga0 zero_le_one)]
        linarith only [hlogLa, this]
      have h2 : Real.log a ^ 3 ≤ a ^ alpha * Real.log a ^ 3 :=
        le_mul_of_one_le_left (pow_nonneg hloga0 3) hαa
      have h3 : Real.log L ≤ 2 * (a ^ alpha * Real.log a ^ 3) := by linarith only [h1, h2]
      have := mul_le_mul_of_nonneg_left h3 (mul_nonneg hCg0 hK0)
      nlinarith only [this]
    have hchom : Chom * Real.log a ^ 2 ≤ Chom * (a ^ alpha * Real.log a ^ 3) := by
      have h1 : Real.log a ^ 2 ≤ Real.log a ^ 3 := by
        nlinarith only [mul_nonneg (sq_nonneg (Real.log a)) (sub_nonneg.mpr hloga1)]
      have h2 : Real.log a ^ 3 ≤ a ^ alpha * Real.log a ^ 3 :=
        le_mul_of_one_le_left (pow_nonneg hloga0 3) hαa
      exact mul_le_mul_of_nonneg_left (le_trans h1 h2) hChom0
    have hW : 0 ≤ a ^ alpha * Real.log a ^ 3 := by positivity
    have hMK : (0 : ℝ) ≤ M + K := by linarith only [hM1, hK1]
    have hcoef : 16 * M + 2 * Cg * K + Chom ≤ M1 := by
      have : 16 * M + 2 * Cg * K + Chom ≤ (16 + 2 * Cg + Chom) * (M + K) := by
        nlinarith only [hM1, hK1, hCg0, hChom0]
      linarith only [this, hM1def]
    have hfin : (16 * M + 2 * Cg * K + Chom) * (a ^ alpha * Real.log a ^ 3) ≤
        M1 * (a ^ alpha * Real.log a ^ 3) := mul_le_mul_of_nonneg_right hcoef hW
    nlinarith only [hdiff, hGM', hlogLle, hchom, hfin]
  have hs3 : 0 ≤ M1 * a ^ alpha * Real.log a ^ (3 : ℝ) := by
    rw [ha3]
    have : 0 ≤ M1 := by nlinarith only [hM1def, hM1, hK1, hCg0, hChom0]
    positivity
  have hX0 : 0 ≤ (1 + Cg + 4 * Chom) * (G + K * Real.log L ^ (2 : ℝ)) := by
    rw [hL2]; positivity
  have hmax1 : max 0 (a - n + Chom * Real.log a ^ (2 : ℝ)) ≤
      (1 + Cg + 4 * Chom) * (G + K * Real.log L ^ (2 : ℝ)) :=
    max_le hX0 hsize
  have hmax2 : max 0 (a - n + Chom * Real.log a ^ (2 : ℝ)) ≤
      M1 * a ^ alpha * Real.log a ^ (3 : ℝ) := max_le hs3 hsmall
  refine ⟨?_, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_left hmax1 (mul_nonneg hChom0 hs2)
    linarith only [this]
  · have h1 := mul_le_mul_of_nonneg_left hmax2 (mul_nonneg hChom0 hs2)
    have h2 : Chom * s ^ (-(2 : ℝ)) * (M1 * a ^ alpha * Real.log a ^ (3 : ℝ)) ≤
        Cabs * M1 * a ^ alpha * s ^ (-(2 : ℝ)) * Real.log a ^ (3 : ℝ) := by
      have hW : 0 ≤ s ^ (-(2 : ℝ)) * (M1 * a ^ alpha * Real.log a ^ (3 : ℝ)) :=
        mul_nonneg hs2 hs3
      have := mul_le_mul_of_nonneg_right hCabsChom hW
      nlinarith only [this]
    have h3 : Chom * n ^ (-(3000 : ℝ)) ≤ Cabs * a ^ (-(99 : ℝ)) := by
      have h4 := mul_le_mul_of_nonneg_left hnpow hChom0
      have h5 : Chom * (B8 * a ^ (-(99 : ℝ))) ≤ Cabs * a ^ (-(99 : ℝ)) := by
        have hp : 0 ≤ a ^ (-(99 : ℝ)) := Real.rpow_nonneg (by linarith only [ha1, hL]) _
        have := mul_le_mul_of_nonneg_right hCabs8 hp
        nlinarith only [this]
      linarith only [h4, h5]
    linarith only [h1, h2, h3, hAbs]
  · have hCl : 0 ≤ Chom * Real.log a ^ (2 : ℝ) := by
      rw [ha2']; positivity
    linarith only [hsmall, hCl]

/-- `3^{-t} ≤ L^{-200}` once `t ≥ 200 log L`. -/
theorem newMixAsm_three_pow_le {t L : ℝ} (hL : 1 ≤ L) (ht : 200 * Real.log L ≤ t) :
    (3 : ℝ) ^ (-t) ≤ L ^ (-(200 : ℝ)) := by
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL
  have hlog3 : 1 ≤ Real.log 3 := by
    have : Real.exp 1 ≤ 3 := by
      have := Real.exp_one_lt_d9
      linarith only [this]
    have h3 : (1 : ℝ) ≤ Real.log 3 := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) this
    exact h3
  have ht0 : 0 ≤ t := by linarith only [ht, hlogL]
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), Real.rpow_def_of_pos hLpos]
  apply Real.exp_le_exp.mpr
  have h1 : t ≤ t * Real.log 3 := le_mul_of_one_le_right ht0 hlog3
  nlinarith only [h1, ht]

/-- `L ≥ C` from the polynomial bound `ν^{-4} ≤ 4/(C² (log 2)^{12}) L`, for `C ≥ 400`. -/
theorem newMixAsm_L_ge_of_nu4 {C nu L : ℝ} (hC : 400 ≤ C) (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (h : nu ^ (-(4 : ℝ)) ≤ (4 / (C ^ 2 * (Real.log 2) ^ (12 : ℝ))) * L) : C ≤ L := by
  have hnu4 : 1 ≤ nu ^ (-(4 : ℝ)) := by
    rw [Real.rpow_neg hnu.le]
    have : nu ^ (4 : ℝ) ≤ 1 := Real.rpow_le_one hnu.le hnu1 (by norm_num)
    exact one_le_inv₀ (Real.rpow_pos_of_pos hnu _) |>.mpr this
  have hlog2 : (0.69 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith only [this]
  have hlog12 : (0.01 : ℝ) ≤ (Real.log 2) ^ (12 : ℝ) := by
    have h1 : (0.69 : ℝ) ^ (12 : ℝ) ≤ (Real.log 2) ^ (12 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) hlog2 (by norm_num)
    have h2 : (0.01 : ℝ) ≤ (0.69 : ℝ) ^ (12 : ℝ) := by
      rw [show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      norm_num
    linarith only [h1, h2]
  have hC0 : 0 < C := by linarith only [hC]
  have hpos : 0 < C ^ 2 * (Real.log 2) ^ (12 : ℝ) := by
    have : 0 < (Real.log 2) ^ (12 : ℝ) := by linarith only [hlog12]
    positivity
  have h1 : 1 ≤ (4 / (C ^ 2 * (Real.log 2) ^ (12 : ℝ))) * L := le_trans hnu4 h
  rw [div_mul_eq_mul_div, le_div_iff₀ hpos] at h1
  have h2 : C ^ 2 * 0.01 ≤ C ^ 2 * (Real.log 2) ^ (12 : ℝ) :=
    mul_le_mul_of_nonneg_left hlog12 (by positivity)
  have h3 : C ^ 2 * 0.01 ≤ 4 * L := by linarith only [h1, h2]
  nlinarith only [h3, hC]

end
end SuperdiffusionCLT.Section4.NewMixing
