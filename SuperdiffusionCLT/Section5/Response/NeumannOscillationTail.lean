/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The scale arithmetic of `e.crude.Fz.bound`

Real-number estimates (no measure theory) for the two kinds of terms of the Dirichlet-comparison
route, at scale `n = ⌊m - h - 100 log_3(ν⁻¹m)⌋₊`, `Kc ≥ 100 m`, `ν⁻² ≤ m`:

* `hessian_scale_le`: `3^{4n} (3^{-(m-h)})⁴ ≤ C₀ (ν⁻¹m)^{-400}`.
  If `n ≤ m - h - 100 log_3(ν⁻¹m)` the constant is `1`; otherwise `n = 0`, and `(ν⁻¹m)^{400}
  ≤ m^{600}` is dominated by `3^{4(m-h)}` up to an absolute constant.
* `gap_tail_le`: `h⁴ (1+x)^{2/5} 3^{-x/5} ≤ C₀ (ν⁻¹m)^{-400}` for `x = Kc - m ≥ 99 m`.
  This is the interpolation term between the energy gap and the `L⁸` bound, with the weights
  chosen so that only the rate `3^{-x/5}` is needed.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Filter Topology

section

/-- An absolute bound for `n^s e^{-b n}` along the naturals. -/
theorem exists_bound_rpow_mul_exp_neg (s b : ℝ) (hb : 0 < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, (n : ℝ) ^ s * Real.exp (-b * n) ≤ C := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s b hb).comp
    tendsto_natCast_atTop_atTop
  obtain ⟨C, hC⟩ := h.bddAbove_range
  refine ⟨max C 0, le_max_right _ _, fun n => ?_⟩
  exact (hC ⟨n, rfl⟩).trans (le_max_left _ _)

/-- `m^{600} ≤ C₁ 3^{3m}` for an absolute constant. -/
theorem exists_pow_six_hundred_le :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ m : ℕ, (m : ℝ) ^ 600 ≤ C * (3 : ℝ) ^ (3 * m) := by
  have h := (tendsto_pow_const_div_const_pow_of_one_lt 600
    (by norm_num : (1 : ℝ) < 27)).bddAbove_range
  obtain ⟨C, hC⟩ := h
  refine ⟨max C 1, le_max_right _ _, fun m => ?_⟩
  have h1 : (m : ℝ) ^ 600 / (27 : ℝ) ^ m ≤ C := hC ⟨m, rfl⟩
  have h27 : (27 : ℝ) ^ m = (3 : ℝ) ^ (3 * m) := by
    rw [pow_mul]
    norm_num
  rw [h27] at h1
  have hp : 0 < (3 : ℝ) ^ (3 * m) := by positivity
  rw [div_le_iff₀ hp] at h1
  exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp.le)

theorem three_pow_nat_eq_exp (k : ℕ) : (3 : ℝ) ^ k = Real.exp (Real.log 3 * k) := by
  rw [mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num)]

theorem three_rpow_eq_exp (a : ℝ) : (3 : ℝ) ^ a = Real.exp (Real.log 3 * a) :=
  Real.rpow_def_of_pos (by norm_num) a

/-- `3^{4n} (3^{-(m-h)})⁴ ≤ C₀ (ν⁻¹m)^{-400}` at the scale `n = ⌊m - h - 100 log_3(ν⁻¹m)⌋₊`. -/
theorem hessian_scale_le :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (nu : ℝ) (m h n : ℕ), 0 < nu → nu ≤ 1 → 1 ≤ h → 400 * h ≤ m →
      nu⁻¹ ^ 2 ≤ (m : ℝ) →
      n = ⌊(m : ℝ) - h - 100 * (Real.log (nu⁻¹ * m) / Real.log 3)⌋₊ →
      (3 : ℝ) ^ (4 * n) * ((3 : ℝ) ^ (-((m - h : ℕ) : ℝ))) ^ 4 ≤
        C * (nu⁻¹ * m) ^ (-(400 : ℝ)) := by
  obtain ⟨C1, hC1, hm⟩ := exists_pow_six_hundred_le
  refine ⟨C1, hC1, fun nu m h n hnu hnu1 hh h400 hnm hn => ?_⟩
  have hmpos : (1 : ℝ) ≤ m := by
    have : 1 ≤ m := by omega
    exact_mod_cast this
  have hnuinv : 1 ≤ nu⁻¹ := one_le_inv₀ hnu |>.2 hnu1
  have hL : 1 ≤ nu⁻¹ * (m : ℝ) := by nlinarith only [hmpos, hnuinv]
  have hLpos : 0 < nu⁻¹ * (m : ℝ) := by linarith only [hL]
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlL : 0 ≤ Real.log (nu⁻¹ * m) := Real.log_nonneg hL
  have ha : (((m - h : ℕ) : ℝ)) = (m : ℝ) - h := Nat.cast_sub (by omega)
  have hRHS : (nu⁻¹ * (m : ℝ)) ^ (-(400 : ℝ)) =
      Real.exp (Real.log (nu⁻¹ * m) * (-400)) := Real.rpow_def_of_pos hLpos _
  have hLHS : (3 : ℝ) ^ (4 * n) * ((3 : ℝ) ^ (-((m - h : ℕ) : ℝ))) ^ 4 =
      Real.exp (Real.log 3 * (4 * n - 4 * (((m - h : ℕ) : ℝ)))) := by
    rw [three_pow_nat_eq_exp, three_rpow_eq_exp, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  by_cases hy : 0 ≤ (m : ℝ) - h - 100 * (Real.log (nu⁻¹ * m) / Real.log 3)
  · have hnle : (n : ℝ) ≤ (m : ℝ) - h - 100 * (Real.log (nu⁻¹ * m) / Real.log 3) := by
      rw [hn]
      exact Nat.floor_le hy
    have hkey : Real.log 3 * (4 * n - 4 * (((m - h : ℕ) : ℝ))) ≤ Real.log (nu⁻¹ * m) * (-400) := by
      have h1 : Real.log 3 * (100 * (Real.log (nu⁻¹ * m) / Real.log 3)) = 100 * Real.log (nu⁻¹ * m) := by
        field_simp
      rw [ha]
      nlinarith only [mul_le_mul_of_nonneg_left hnle hl3.le, h1]
    rw [hLHS, hRHS]
    calc Real.exp (Real.log 3 * (4 * n - 4 * (((m - h : ℕ) : ℝ))))
        ≤ Real.exp (Real.log (nu⁻¹ * m) * (-400)) := Real.exp_le_exp.2 hkey
      _ = 1 * Real.exp (Real.log (nu⁻¹ * m) * (-400)) := (one_mul _).symm
      _ ≤ C1 * Real.exp (Real.log (nu⁻¹ * m) * (-400)) := by gcongr
  · have hy' : (m : ℝ) - h - 100 * (Real.log (nu⁻¹ * m) / Real.log 3) ≤ 0 := by linarith only [not_le.1 hy]
    have hn0 : n = 0 := by
      rw [hn]
      exact Nat.floor_of_nonpos hy'
    subst hn0
    -- `L^{400} ≤ m^{600} ≤ C₁ 3^{3m} ≤ C₁ 3^{4(m-h)}`.
    have hL2 : (nu⁻¹ * (m : ℝ)) ^ 2 ≤ (m : ℝ) ^ 3 := by
      calc (nu⁻¹ * (m : ℝ)) ^ 2 = nu⁻¹ ^ 2 * (m : ℝ) ^ 2 := by ring
        _ ≤ (m : ℝ) * (m : ℝ) ^ 2 := by gcongr
        _ = (m : ℝ) ^ 3 := by ring
    have hL400 : (nu⁻¹ * (m : ℝ)) ^ 400 ≤ (m : ℝ) ^ 600 := by
      calc (nu⁻¹ * (m : ℝ)) ^ 400 = ((nu⁻¹ * (m : ℝ)) ^ 2) ^ 200 := by ring
        _ ≤ ((m : ℝ) ^ 3) ^ 200 := by gcongr
        _ = (m : ℝ) ^ 600 := by ring
    have h3m : (3 : ℝ) ^ (3 * m) ≤ Real.exp (Real.log 3 * (4 * (((m - h : ℕ) : ℝ)))) := by
      rw [three_pow_nat_eq_exp]
      refine Real.exp_le_exp.2 ?_
      rw [ha]
      have : (3 : ℝ) * m ≤ 4 * ((m : ℝ) - h) := by
        have : (400 : ℝ) * h ≤ m := by exact_mod_cast h400
        linarith only [this]
      push_cast
      nlinarith only [mul_le_mul_of_nonneg_left this hl3.le]
    have hmain : (nu⁻¹ * (m : ℝ)) ^ 400 ≤ C1 * Real.exp (Real.log 3 * (4 * (((m - h : ℕ) : ℝ)))) :=
      hL400.trans ((hm m).trans (by gcongr))
    rw [hLHS, hRHS]
    have hexp : Real.exp (Real.log 3 * (4 * (0 : ℕ) - 4 * (((m - h : ℕ) : ℝ)))) =
        (Real.exp (Real.log 3 * (4 * (((m - h : ℕ) : ℝ)))))⁻¹ := by
      rw [← Real.exp_neg]
      congr 1
      push_cast
      ring
    have hLexp : Real.exp (Real.log (nu⁻¹ * m) * (-400)) = ((nu⁻¹ * (m : ℝ)) ^ 400)⁻¹ := by
      rw [← Real.rpow_def_of_pos hLpos, Real.rpow_neg hLpos.le]
      norm_cast
    rw [hexp, hLexp]
    have hE : 0 < Real.exp (Real.log 3 * (4 * (((m - h : ℕ) : ℝ)))) := Real.exp_pos _
    have hLp : 0 < (nu⁻¹ * (m : ℝ)) ^ 400 := by positivity
    calc (Real.exp (Real.log 3 * (4 * (((m - h : ℕ) : ℝ)))))⁻¹
        = ((Real.exp (Real.log 3 * (4 * (((m - h : ℕ) : ℝ)))))⁻¹ * (nu⁻¹ * (m : ℝ)) ^ 400) *
          ((nu⁻¹ * (m : ℝ)) ^ 400)⁻¹ := by field_simp
      _ ≤ ((Real.exp (Real.log 3 * (4 * (((m - h : ℕ) : ℝ)))))⁻¹ *
          (C1 * Real.exp (Real.log 3 * (4 * (((m - h : ℕ) : ℝ)))))) *
          ((nu⁻¹ * (m : ℝ)) ^ 400)⁻¹ := by gcongr
      _ = C1 * ((nu⁻¹ * (m : ℝ)) ^ 400)⁻¹ := by field_simp

/-- `h⁴ (1+x)^{2/5} 3^{-x/5} ≤ C₀ (ν⁻¹m)^{-400}` for `x = Kc - m ≥ 99 m`, `h ≤ m`, `ν⁻² ≤ m`. -/
theorem gap_tail_le :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (nu : ℝ) (m h Kc : ℕ), 0 < nu → nu ≤ 1 → 1 ≤ h → 400 * h ≤ m →
      100 * m ≤ Kc → nu⁻¹ ^ 2 ≤ (m : ℝ) →
      (h : ℝ) ^ 4 * ((1 : ℝ) + ((Kc - m : ℕ) : ℝ)) ^ ((2 : ℝ) / 5) *
          (3 : ℝ) ^ (-((1 : ℝ) / 5 * ((Kc - m : ℕ) : ℝ))) ≤
        C * (nu⁻¹ * m) ^ (-(400 : ℝ)) := by
  obtain ⟨Cb, hCb0, hCb⟩ := exists_bound_rpow_mul_exp_neg ((4 : ℝ) + 600 + 2 / 5)
    (Real.log 3 / 5) (by have := Real.log_pos (by norm_num : (1 : ℝ) < 3); positivity)
  refine ⟨max 1 (Real.exp (Real.log 3 / 5) * Cb), le_max_left _ _,
    fun nu m h Kc hnu hnu1 hh h400 h100 hnm => ?_⟩
  have hmpos : (1 : ℝ) ≤ m := by
    have : 1 ≤ m := by omega
    exact_mod_cast this
  have hnuinv : 1 ≤ nu⁻¹ := one_le_inv₀ hnu |>.2 hnu1
  have hLpos : 0 < nu⁻¹ * (m : ℝ) := by nlinarith only [hmpos, hnuinv]
  set x : ℕ := Kc - m with hx
  have hxm : m ≤ x := by omega
  have hmx : (m : ℝ) ≤ x := by exact_mod_cast hxm
  have hhm : (h : ℝ) ≤ m := by exact_mod_cast (by omega : h ≤ m)
  have hy1 : (1 : ℝ) ≤ 1 + x := by linarith only [Nat.cast_nonneg (α := ℝ) x]
  have hmy : (m : ℝ) ≤ 1 + x := by linarith only [hmx]
  have hL2 : (nu⁻¹ * (m : ℝ)) ^ 2 ≤ (m : ℝ) ^ 3 := by
    calc (nu⁻¹ * (m : ℝ)) ^ 2 = nu⁻¹ ^ 2 * (m : ℝ) ^ 2 := by ring
      _ ≤ (m : ℝ) * (m : ℝ) ^ 2 := by gcongr
      _ = (m : ℝ) ^ 3 := by ring
  have hL400 : (nu⁻¹ * (m : ℝ)) ^ 400 ≤ (m : ℝ) ^ 600 := by
    calc (nu⁻¹ * (m : ℝ)) ^ 400 = ((nu⁻¹ * (m : ℝ)) ^ 2) ^ 200 := by ring
      _ ≤ ((m : ℝ) ^ 3) ^ 200 := by gcongr
      _ = (m : ℝ) ^ 600 := by ring
  set y : ℝ := ((x + 1 : ℕ) : ℝ) with hy
  have hy' : y = 1 + (x : ℝ) := by
    rw [hy]
    push_cast
    ring
  have hy1 : (1 : ℝ) ≤ y := by rw [hy']; linarith only [Nat.cast_nonneg (α := ℝ) x]
  have hmy : (m : ℝ) ≤ y := by rw [hy']; linarith only [hmx]
  have hypos : 0 < y := by linarith only [hy1]
  have hb : (3 : ℝ) ^ (-((1 : ℝ) / 5 * (x : ℝ))) =
      Real.exp (Real.log 3 / 5) * Real.exp (-(Real.log 3 / 5) * y) := by
    rw [three_rpow_eq_exp, ← Real.exp_add, hy']
    congr 1
    ring
  have hxy : (1 : ℝ) + ((Kc - m : ℕ) : ℝ) = y := by rw [hy', hx]
  rw [hxy]
  have hkey : (h : ℝ) ^ 4 * y ^ ((2 : ℝ) / 5) * (3 : ℝ) ^ (-((1 : ℝ) / 5 * (x : ℝ))) *
      (nu⁻¹ * (m : ℝ)) ^ 400 ≤ Real.exp (Real.log 3 / 5) * Cb := by
    have h1 : (h : ℝ) ^ 4 ≤ y ^ 4 := by gcongr; exact hhm.trans hmy
    have h2 : (nu⁻¹ * (m : ℝ)) ^ 400 ≤ y ^ 600 := hL400.trans (by gcongr)
    have h3 : y ^ (4 : ℕ) * y ^ ((2 : ℝ) / 5) * y ^ (600 : ℕ) = y ^ ((4 : ℝ) + 600 + 2 / 5) := by
      rw [← Real.rpow_natCast y 4, ← Real.rpow_natCast y 600, ← Real.rpow_add hypos,
        ← Real.rpow_add hypos]
      congr 1
      push_cast
      ring
    have h4 := hCb (x + 1)
    calc (h : ℝ) ^ 4 * y ^ ((2 : ℝ) / 5) * (3 : ℝ) ^ (-((1 : ℝ) / 5 * (x : ℝ))) *
        (nu⁻¹ * (m : ℝ)) ^ 400
        ≤ (y ^ 4 * y ^ ((2 : ℝ) / 5) * (3 : ℝ) ^ (-((1 : ℝ) / 5 * (x : ℝ)))) * y ^ 600 := by
          gcongr
      _ = (y ^ ((4 : ℝ) + 600 + 2 / 5) * Real.exp (-(Real.log 3 / 5) * y)) *
          Real.exp (Real.log 3 / 5) := by
          rw [hb, ← h3]
          ring
      _ ≤ Cb * Real.exp (Real.log 3 / 5) := by gcongr
      _ = Real.exp (Real.log 3 / 5) * Cb := mul_comm _ _
  rw [Real.rpow_neg hLpos.le, show (400 : ℝ) = ((400 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hLp : 0 < (nu⁻¹ * (m : ℝ)) ^ 400 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hLp]
  exact hkey.trans (le_max_right _ _)

/-- The interpolation term with the weight `t = s² 3^{x/5}`:
`(2t/3) X₀ + 128 G⁸/(3t²) ≤ s⁴ K h⁴ (1+x)^{2/5} 3^{-x/5}`, where `X₀` is the energy-gap bound
`C_g h^{4/5}(1+x)^{2/5}3^{-2x/5} s²` and `G = C s h^{1/2}`. -/
theorem gap_term_le {si Cg Cgr h x : ℝ} (hsi : 0 < si) (hCg : 0 ≤ Cg)
    (hh : 1 ≤ h) (hx : 0 ≤ x) :
    2 * (si ^ 2 * (3 : ℝ) ^ (x / 5)) / 3 *
          (Cg * h ^ ((4 : ℝ) / 5) * (1 + x) ^ ((2 : ℝ) / 5) *
            (3 : ℝ) ^ (-((2 : ℝ) / 5 * x)) * si ^ 2) +
        1 / (3 * (si ^ 2 * (3 : ℝ) ^ (x / 5)) ^ 2) *
          (128 * (Cgr * si * h ^ ((1 : ℝ) / 2)) ^ 8) ≤
      si ^ 4 * ((2 / 3) * Cg + (128 / 3) * Cgr ^ 8) *
        (h ^ 4 * (1 + x) ^ ((2 : ℝ) / 5) * (3 : ℝ) ^ (-((1 : ℝ) / 5 * x))) := by
  have h0 : 0 < h := by linarith only [hh]
  have hw1 : 0 < (3 : ℝ) ^ (x / 5) := by positivity
  have hw2 : 0 < (3 : ℝ) ^ (-((2 : ℝ) / 5 * x)) := by positivity
  have hw : 0 < (3 : ℝ) ^ (-((1 : ℝ) / 5 * x)) := by positivity
  have hex : 1 ≤ (1 + x) ^ ((2 : ℝ) / 5) :=
    Real.one_le_rpow (by linarith only [hx]) (by norm_num)
  have hhr : h ^ ((4 : ℝ) / 5) ≤ h ^ 4 := by
    have := Real.rpow_le_rpow_of_exponent_le hh (show ((4 : ℝ) / 5) ≤ 4 by norm_num)
    simpa using this
  have hww : (3 : ℝ) ^ (x / 5) * (3 : ℝ) ^ (-((2 : ℝ) / 5 * x)) =
      (3 : ℝ) ^ (-((1 : ℝ) / 5 * x)) := by
    rw [← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hww2 : ((3 : ℝ) ^ (x / 5)) ^ 2 * (3 : ℝ) ^ (-((2 : ℝ) / 5 * x)) = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
    have : x / 5 * ((2 : ℕ) : ℝ) + -((2 : ℝ) / 5 * x) = 0 := by
      push_cast
      ring
    rw [this, Real.rpow_zero]
  have hh8 : ((h : ℝ) ^ ((1 : ℝ) / 2)) ^ 8 = h ^ 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h0.le]
    rw [show (1 : ℝ) / 2 * ((8 : ℕ) : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hw2w : (3 : ℝ) ^ (-((2 : ℝ) / 5 * x)) ≤ (3 : ℝ) ^ (-((1 : ℝ) / 5 * x)) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    nlinarith only [hx]
  have e1 : 2 * (si ^ 2 * (3 : ℝ) ^ (x / 5)) / 3 *
      (Cg * h ^ ((4 : ℝ) / 5) * (1 + x) ^ ((2 : ℝ) / 5) *
        (3 : ℝ) ^ (-((2 : ℝ) / 5 * x)) * si ^ 2) =
      (2 / 3) * Cg * si ^ 4 * h ^ ((4 : ℝ) / 5) * (1 + x) ^ ((2 : ℝ) / 5) *
        (3 : ℝ) ^ (-((1 : ℝ) / 5 * x)) := by
    rw [← hww]
    ring
  have e2 : 1 / (3 * (si ^ 2 * (3 : ℝ) ^ (x / 5)) ^ 2) *
      (128 * (Cgr * si * h ^ ((1 : ℝ) / 2)) ^ 8) =
      (128 / 3) * Cgr ^ 8 * si ^ 4 * h ^ 4 * (3 : ℝ) ^ (-((2 : ℝ) / 5 * x)) := by
    have hnz : (3 : ℝ) ^ (x / 5) ≠ 0 := hw1.ne'
    have : (3 : ℝ) ^ (-((2 : ℝ) / 5 * x)) = (((3 : ℝ) ^ (x / 5)) ^ 2)⁻¹ := by
      exact (inv_eq_of_mul_eq_one_right hww2).symm
    rw [mul_pow, mul_pow, hh8, this]
    field_simp
  rw [e1, e2]
  have hs4 : 0 < si ^ 4 := by positivity
  have hA : (2 / 3) * Cg * si ^ 4 * h ^ ((4 : ℝ) / 5) * (1 + x) ^ ((2 : ℝ) / 5) *
        (3 : ℝ) ^ (-((1 : ℝ) / 5 * x)) ≤
      (2 / 3) * Cg * si ^ 4 * h ^ 4 * (1 + x) ^ ((2 : ℝ) / 5) *
        (3 : ℝ) ^ (-((1 : ℝ) / 5 * x)) := by gcongr
  have hB : (128 / 3) * Cgr ^ 8 * si ^ 4 * h ^ 4 * (3 : ℝ) ^ (-((2 : ℝ) / 5 * x)) ≤
      (128 / 3) * Cgr ^ 8 * si ^ 4 * h ^ 4 * ((1 + x) ^ ((2 : ℝ) / 5) *
        (3 : ℝ) ^ (-((1 : ℝ) / 5 * x))) := by
    gcongr
    calc (3 : ℝ) ^ (-((2 : ℝ) / 5 * x)) ≤ (3 : ℝ) ^ (-((1 : ℝ) / 5 * x)) := hw2w
      _ = 1 * (3 : ℝ) ^ (-((1 : ℝ) / 5 * x)) := (one_mul _).symm
      _ ≤ _ := by gcongr
  calc _ ≤ (2 / 3) * Cg * si ^ 4 * h ^ 4 * (1 + x) ^ ((2 : ℝ) / 5) *
        (3 : ℝ) ^ (-((1 : ℝ) / 5 * x)) + (128 / 3) * Cgr ^ 8 * si ^ 4 * h ^ 4 *
        ((1 + x) ^ ((2 : ℝ) / 5) * (3 : ℝ) ^ (-((1 : ℝ) / 5 * x))) := add_le_add hA hB
    _ = _ := by ring

end

end SuperdiffusionCLT.Section5

