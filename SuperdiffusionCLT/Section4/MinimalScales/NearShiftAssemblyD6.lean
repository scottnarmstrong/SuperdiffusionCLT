/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.NearShiftAssemblyD5
public import SuperdiffusionCLT.Section4.MinimalScales.NearMaxScale

/-!
# Near-scale assembly: cardinalities of the index sets

The descendants of `cu_n` at depth `l` number `(3^d)^l` (`srootN_descendantsAtScale_card`). This
file bounds the index sets of the finite maxima in the packaging, and the logarithms of their
cardinalities, which are the centering terms.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

noncomputable section

/-- The cardinalities of the two index sets of the finite domination. -/
theorem srootNSD_card_T {d : ℕ} [NeZero d] (n a b Nl : ℕ) (c : ℝ) (hNl : Nl ≤ n + 1)
    (hc : ((b + 1 + 1 - a : ℕ) : ℝ) ≤ c) (hc1 : 1 ≤ c) :
    ((((Finset.Icc a (b + 1)) ×ˢ ((Finset.range Nl).sigma (fun l : ℕ =>
        Homogenization.descendantsAtScale (Homogenization.originCube d (n : ℤ))
          ((n : ℤ) - (l : ℤ))))).card : ℕ) : ℝ) ≤ c * ((Nl : ℝ) * ((3 : ℝ) ^ d) ^ Nl) ∧
    ((((Finset.range Nl).sigma (fun l : ℕ =>
        Homogenization.descendantsAtScale (Homogenization.originCube d (n : ℤ))
          ((n : ℤ) - (l : ℤ)))).card : ℕ) : ℝ) ≤ c * ((Nl : ℝ) * ((3 : ℝ) ^ d) ^ Nl) := by
  have hsig : ((((Finset.range Nl).sigma (fun l : ℕ =>
        Homogenization.descendantsAtScale (Homogenization.originCube d (n : ℤ))
          ((n : ℤ) - (l : ℤ)))).card : ℕ) : ℝ) ≤ (Nl : ℝ) * ((3 : ℝ) ^ d) ^ Nl := by
    rw [Finset.card_sigma]
    have h1 : ∀ l ∈ Finset.range Nl, (Homogenization.descendantsAtScale
        (Homogenization.originCube d (n : ℤ)) ((n : ℤ) - (l : ℤ))).card ≤ (3 ^ d) ^ Nl := by
      intro l hl
      have hl' := Finset.mem_range.1 hl
      rw [srootN_descendantsAtScale_card (by omega : l ≤ n)]
      exact Nat.pow_le_pow_right (by positivity) hl'.le
    have h2 := Finset.sum_le_sum h1
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at h2
    have h3 : (∑ l ∈ Finset.range Nl, (Homogenization.descendantsAtScale
        (Homogenization.originCube d (n : ℤ)) ((n : ℤ) - (l : ℤ))).card) ≤ Nl * (3 ^ d) ^ Nl :=
      h2
    exact_mod_cast h3
  have hnn : 0 ≤ (Nl : ℝ) * ((3 : ℝ) ^ d) ^ Nl := by positivity
  refine ⟨?_, hsig.trans ?_⟩
  · rw [Finset.card_product, Nat.card_Icc]
    push_cast
    have : ((b + 1 + 1 - a : ℕ) : ℝ) * ((((Finset.range Nl).sigma (fun l : ℕ =>
        Homogenization.descendantsAtScale (Homogenization.originCube d (n : ℤ))
          ((n : ℤ) - (l : ℤ)))).card : ℕ) : ℝ) ≤ c * ((Nl : ℝ) * ((3 : ℝ) ^ d) ^ Nl) :=
      mul_le_mul hc hsig (by positivity) (by linarith only [hc, hc1])
    exact this
  · nlinarith only [hc1, hnn]

/-- The logarithm of the cardinality bound: `3 log (2 m Nl 3^{d Nl}) ≤ c3 m`. -/
theorem srootNSD_log_Ncap {m C0 d : ℝ} {Nl : ℕ} (hm : 2 ≤ m) (hd : 0 ≤ d)
    (hNl1 : 1 ≤ Nl) (hNl : (Nl : ℝ) ≤ 3 * C0 * m) (dn : ℕ) (hdn : (dn : ℝ) = d) :
    3 * Real.log (max 2 ((2 * m) * ((Nl : ℝ) * ((3 : ℝ) ^ dn) ^ Nl))) ≤
      (3 * (2 + 3 * C0 * (1 + 2 * d))) * m := by
  have hN1 : (1 : ℝ) ≤ Nl := by exact_mod_cast hNl1
  have h3d : (1 : ℝ) ≤ ((3 : ℝ) ^ dn) ^ Nl := one_le_pow₀ (one_le_pow₀ (by norm_num))
  have hpow : 0 < ((3 : ℝ) ^ dn) ^ Nl := by positivity
  have hNc : 2 ≤ (2 * m) * ((Nl : ℝ) * ((3 : ℝ) ^ dn) ^ Nl) := by
    have : 1 ≤ (Nl : ℝ) * ((3 : ℝ) ^ dn) ^ Nl := by nlinarith only [hN1, h3d]
    nlinarith only [hm, this]
  rw [max_eq_right hNc]
  have hm0 : 0 < m := by linarith only [hm]
  have hNl0 : (Nl : ℝ) ≠ 0 := by positivity
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) hm0.ne',
    Real.log_mul hNl0 hpow.ne', Real.log_pow, Real.log_pow]
  have l1 : Real.log 2 + Real.log m ≤ 2 * m := by
    have h1 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    have h2 := Real.log_le_sub_one_of_pos hm0
    linarith only [h1, h2, hm]
  have l2 : Real.log (Nl : ℝ) ≤ Nl := by
    have := Real.log_le_sub_one_of_pos (by linarith only [hN1] : (0 : ℝ) < Nl)
    linarith only [this]
  have l3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith only [this]
  have hl30 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have l4 : (Nl : ℝ) * ((dn : ℝ) * Real.log 3) ≤ (Nl : ℝ) * (d * 2) := by
    rw [hdn]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left l3 hd) (by linarith only [hN1])
  nlinarith only [l1, l2, l4, hNl, hd, hm, hN1]

/-- The centering of one depth: `log (2 x (3^d)^l) ≤ 2 log m + 2 d l`. -/
theorem srootNSD_logN_l {m x d : ℝ} {l dn : ℕ} (hx1 : 1 ≤ x) (hxm : x ≤ m)
    (hlg : 1 ≤ Real.log m) (hd : 0 ≤ d) (hdn : (dn : ℝ) = d) :
    Real.log (2 * (x * (((3 : ℝ) ^ dn) ^ l))) ≤ 2 * Real.log m + 2 * d * (l : ℝ) := by
  have hpow : 0 < ((3 : ℝ) ^ dn) ^ l := by positivity
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul (by linarith only [hx1])
    (by positivity), Real.log_pow, Real.log_pow]
  have l0 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith only [this]
  have l1 : Real.log x ≤ Real.log m := Real.log_le_log (by linarith only [hx1]) hxm
  have l3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith only [this]
  have hl : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  have l4 : (l : ℝ) * ((dn : ℝ) * Real.log 3) ≤ (l : ℝ) * (d * 2) := by
    rw [hdn]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left l3 hd) hl
  nlinarith only [l0, l1, l4, hlg]

/-- The number of cutoffs in the window is at most `m`. -/
theorem srootNSD_count_le {C1 t K lg m h : ℝ} (hC1 : 20000 ≤ C1) (ht : 1 ≤ t) (hK : 1 ≤ K)
    (hlg : 4 ≤ lg) (hm : 2 ≤ m) (hcore : C1 * (C1 * t * K * lg) ≤ 1600 * m)
    (hh : h ≤ 2 * K * lg) : h + 1 + C1 * t * h ≤ m := by
  have hP1 : 1 ≤ t * K * lg := by
    have h1 : 1 ≤ t * K := by nlinarith only [ht, hK]
    nlinarith only [h1, hlg]
  have hP0 : 0 ≤ t * K * lg := by linarith only [hP1]
  have hKlg : K * lg ≤ t * K * lg := by
    have : K ≤ t * K := by nlinarith only [ht, hK]
    exact mul_le_mul_of_nonneg_right this (by linarith only [hlg])
  have hsq : 400000000 ≤ C1 * C1 := by nlinarith only [hC1]
  have hP : C1 * C1 * (t * K * lg) ≤ 1600 * m := by
    have e : C1 * (C1 * t * K * lg) = C1 * C1 * (t * K * lg) := by ring
    linarith only [hcore, e]
  have hPm : t * K * lg ≤ m / 250000 := by
    have : 400000000 * (t * K * lg) ≤ C1 * C1 * (t * K * lg) :=
      mul_le_mul_of_nonneg_right hsq hP0
    linarith only [this, hP]
  have hC1P : C1 * (t * K * lg) ≤ m / 12 := by
    have h1 : C1 * (C1 * (t * K * lg)) ≤ 1600 * m := by
      have e : C1 * (C1 * (t * K * lg)) = C1 * C1 * (t * K * lg) := by ring
      linarith only [hP, e]
    have h2 : 20000 * (C1 * (t * K * lg)) ≤ C1 * (C1 * (t * K * lg)) :=
      mul_le_mul_of_nonneg_right hC1 (by positivity)
    linarith only [h1, h2, hm]
  have h3 : C1 * t * h ≤ C1 * t * (2 * K * lg) :=
    mul_le_mul_of_nonneg_left hh (by positivity)
  have e3 : C1 * t * (2 * K * lg) = 2 * (C1 * (t * K * lg)) := by ring
  have h4 : h ≤ 2 * (t * K * lg) := by linarith only [hh, hKlg]
  linarith only [h3, e3, h4, hC1P, hPm, hm]

end

end SuperdiffusionCLT.Section4.MinimalScales
