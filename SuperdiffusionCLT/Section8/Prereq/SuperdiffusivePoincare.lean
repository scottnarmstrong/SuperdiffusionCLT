/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Probability.IndependentSums.WeakOrlicz
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import SuperdiffusionCLT.Section6.Prereq.EuclidBall
public import SuperdiffusionCLT.Section7.Analytic.Defs
public import SuperdiffusionCLT.Section7.Prereq.RootCarriersApiC

/-!
# Scalar and scale lemmas for the superdiffusive Poincaré inequality on balls

* `sdPoinc_euclidBall_eq`: the dilate `t • B_{1/2}` is the ball `B_{t/2}`.
* `sdPoinc_exists_pow`: for `t ≥ 1` there is `m` with `3^m < 3 t ≤ 3^{m+1}`.
* `sdPoinc_sharp_threshold`: the error in the sharp bound for the diffusivity is eventually at
  most half of `√(c⋆ m)`.
* `sdPoinc_coef_first`, `sdPoinc_coef_second`: the two coefficients of the Whitney lemma at
  `3^m ≈ 2R`, converted to powers of `log R`.
* `sdPoinc_isBigO_max_exp`: deterministic enlargement of a scale with `Γ_ρ` control of its
  logarithm.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization MeasureTheory
open scoped Pointwise

variable {d : ℕ}



/-- The dilate of the ball of radius `1/2` by `t` is the ball of radius `t/2`. -/
theorem sdPoinc_euclidBall_eq {t : ℝ} (ht : 0 < t) :
    t • SuperdiffusionCLT.Section6.euclidBall (d := d) (1 / 2) =
      SuperdiffusionCLT.Section6.euclidBall (t / 2) := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ ht.ne', SuperdiffusionCLT.Section6.mem_euclidBall,
    SuperdiffusionCLT.Section6.mem_euclidBall, vecNormSq_smul]
  constructor
  · intro h
    have h2 : vecNormSq x < t ^ 2 * (1 / 2) ^ 2 := by
      have := mul_lt_mul_of_pos_left h (by positivity : 0 < t ^ 2)
      have h1 : t ^ 2 * (t⁻¹) ^ 2 = 1 := by field_simp
      rwa [← mul_assoc, h1, one_mul] at this
    calc vecNormSq x < t ^ 2 * (1 / 2) ^ 2 := h2
      _ = (t / 2) ^ 2 := by ring
  · intro h
    have h2 : (t⁻¹) ^ 2 * vecNormSq x < (t⁻¹) ^ 2 * (t / 2) ^ 2 :=
      mul_lt_mul_of_pos_left h (by positivity)
    calc (t⁻¹) ^ 2 * vecNormSq x < (t⁻¹) ^ 2 * (t / 2) ^ 2 := h2
      _ = (1 / 2) ^ 2 := by field_simp

/-- A power of three comparable to a real `t ≥ 1`. -/
theorem sdPoinc_exists_pow {t : ℝ} (ht : 1 ≤ t) :
    ∃ m : ℕ, (3 : ℝ) ^ m < 3 * t ∧ t ≤ (3 : ℝ) ^ m := by
  have hex : ∃ m : ℕ, t ≤ (3 : ℝ) ^ m := by
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt t (by norm_num : (1 : ℝ) < 3)
    exact ⟨m, hm.le⟩
  classical
  let m := Nat.find hex
  have hm : t ≤ (3 : ℝ) ^ m := Nat.find_spec hex
  refine ⟨m, ?_, hm⟩
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · rw [h0]; norm_num; linarith only [ht]
  · have := Nat.find_min hex (Nat.sub_lt hpos one_pos)
    push Not at this
    have h3 : (3 : ℝ) ^ m = 3 * (3 : ℝ) ^ (m - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [h3]
    linarith only [this]



/-- The error in the sharp bound for the diffusivity is eventually at most half of `√(c⋆ m)`. -/
theorem sdPoinc_sharp_threshold {Cs cStar : ℝ} (K : ℝ) (hCs : 0 ≤ Cs) (hc : 0 < cStar) :
    ∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∀ m : ℕ, m₁ ≤ m →
      Cs * cStar⁻¹ * (Real.log (m : ℝ) ^ (2 : ℝ) + K) ≤ 1 / 2 * Real.sqrt (cStar * m) := by
  set q : ℝ := Cs * cStar⁻¹ with hq
  have hq0 : 0 ≤ q := by positivity
  have hsc : 0 < Real.sqrt cStar := Real.sqrt_pos.2 hc
  set s : ℝ := max 1 (max (256 * q / Real.sqrt cStar) (4 * q * |K| / Real.sqrt cStar)) with hs
  have hs1 : 1 ≤ s := le_max_left _ _
  have hs2 : 256 * q / Real.sqrt cStar ≤ s := (le_max_left _ _).trans (le_max_right _ _)
  have hs3 : 4 * q * |K| / Real.sqrt cStar ≤ s := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨⌈s ^ 8⌉₊, ?_, fun m hm => ?_⟩
  · have : (1 : ℝ) ≤ s ^ 8 := one_le_pow₀ hs1
    exact Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by linarith only [this])).ne'
  have hm8 : s ^ 8 ≤ (m : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hm)
  have hm1 : (1 : ℝ) ≤ m := (one_le_pow₀ hs1).trans hm8
  have hm0 : (0 : ℝ) ≤ m := by linarith only [hm1]
  set y : ℝ := (m : ℝ) ^ ((1 : ℝ) / 8) with hy
  have hy0 : 0 ≤ y := Real.rpow_nonneg hm0 _
  have hy8 : y ^ 8 = m := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hm0]; norm_num
  have hsy : s ≤ y := le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) hy0 (by rw [hy8]; exact hm8)
  have hy1 : 1 ≤ y := hs1.trans hsy
  have hlog : Real.log (m : ℝ) ≤ 8 * y := by
    have := Real.log_le_rpow_div hm0 (by norm_num : (0 : ℝ) < 1 / 8)
    rw [hy]; linarith only [this]
  have hlog0 : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hm1
  have hlog2 : Real.log (m : ℝ) ^ (2 : ℝ) ≤ 64 * y ^ 2 := by
    rw [Real.rpow_two]
    nlinarith only [hlog, hlog0]
  have hsqrt : Real.sqrt (cStar * m) = Real.sqrt cStar * y ^ 4 := by
    rw [Real.sqrt_mul hc.le, ← hy8]
    congr 1
    rw [show y ^ 8 = (y ^ 4) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  rw [hsqrt]
  have e1 : 256 * q ≤ s * Real.sqrt cStar := by
    rwa [div_le_iff₀ hsc] at hs2
  have e2 : 4 * q * |K| ≤ s * Real.sqrt cStar := by
    rwa [div_le_iff₀ hsc] at hs3
  have hy2 : s ≤ y ^ 2 := by nlinarith only [hsy, hy1]
  have hy4 : y ^ 2 ≤ y ^ 4 := by
    have h1 : 1 ≤ y ^ 2 := one_le_pow₀ hy1
    nlinarith only [h1, sq_nonneg (y ^ 2)]
  have h64 : 64 * q * y ^ 2 ≤ 1 / 4 * (Real.sqrt cStar * y ^ 4) := by
    have : 256 * q ≤ y ^ 2 * Real.sqrt cStar := by
      nlinarith only [e1, hy2, hsc]
    nlinarith only [this, sq_nonneg y, hsc, hy0, mul_le_mul_of_nonneg_right this (by positivity : (0:ℝ) ≤ y ^ 2)]
  have hK : q * K ≤ 1 / 4 * (Real.sqrt cStar * y ^ 4) := by
    have h1 : q * K ≤ q * |K| := mul_le_mul_of_nonneg_left (le_abs_self K) hq0
    have h2 : 4 * q * |K| ≤ y ^ 4 * Real.sqrt cStar := by
      nlinarith only [e2, hy2, hy4, hsc, hs1]
    nlinarith only [h1, h2]
  have : q * (Real.log (m : ℝ) ^ (2 : ℝ) + K) ≤ q * (64 * y ^ 2) + q * K := by
    rw [mul_add]; exact add_le_add (mul_le_mul_of_nonneg_left hlog2 hq0) le_rfl
  nlinarith only [this, h64, hK]



theorem sdPoinc_one_le_log_three : 1 ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith only [this]

theorem sdPoinc_log_three_le_two : Real.log 3 ≤ 2 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have := Real.add_one_le_exp (2 : ℝ)
  linarith only [this]

/-- `m ≥ log R / 2` when `2 R ≤ 3 ^ m`. -/
theorem sdPoinc_m_ge {R : ℝ} {m : ℕ} (hR : 1 ≤ R) (h : 2 * R ≤ (3 : ℝ) ^ m) :
    Real.log R / 2 ≤ (m : ℝ) := by
  have h1 : Real.log R ≤ Real.log ((3 : ℝ) ^ m) :=
    Real.log_le_log (by linarith only [hR]) (by linarith only [h, hR])
  rw [Real.log_pow] at h1
  have := sdPoinc_log_three_le_two
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  nlinarith only [h1, this, hm]

/-- The first coefficient. -/
theorem sdPoinc_coef_first {R cStar sh : ℝ} {m : ℕ} (hR : 3 ≤ R) (hc : 0 < cStar)
    (h2 : 2 * R ≤ (3 : ℝ) ^ m) (h6 : (3 : ℝ) ^ m < 6 * R)
    (hsh : 1 / 2 * Real.sqrt (cStar * m) ≤ sh) :
    (3 : ℝ) ^ m * (Real.sqrt sh)⁻¹ ≤
      12 * R * (cStar ^ (-(1 / 4 : ℝ)) * Real.log R ^ (-(1 / 4 : ℝ))) := by
  have hR1 : 1 ≤ R := by linarith only [hR]
  have hL1 : 1 ≤ Real.log R := by
    have := sdPoinc_one_le_log_three
    exact this.trans (Real.log_le_log (by norm_num) hR)
  have hL0 : 0 < Real.log R := by linarith only [hL1]
  have hmg := sdPoinc_m_ge hR1 h2
  set w : ℝ := (cStar * Real.log R) ^ ((1 : ℝ) / 4) with hw
  have hcL : 0 < cStar * Real.log R := mul_pos hc hL0
  have hw0 : 0 < w := Real.rpow_pos_of_pos hcL _
  have hw2 : w ^ 2 = Real.sqrt (cStar * Real.log R) := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul hcL.le, Real.sqrt_eq_rpow]; norm_num
  have hsq : 1 / 2 * Real.sqrt (cStar * Real.log R) ≤ Real.sqrt (cStar * m) := by
    have : cStar * (Real.log R / 4) ≤ cStar * m := by
      refine mul_le_mul_of_nonneg_left ?_ hc.le
      linarith only [hmg, hL0]
    have h' := Real.sqrt_le_sqrt this
    have e : Real.sqrt (cStar * (Real.log R / 4)) = 1 / 2 * Real.sqrt (cStar * Real.log R) := by
      rw [show cStar * (Real.log R / 4) = (1 / 2) ^ 2 * (cStar * Real.log R) by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
    rwa [e] at h'
  have hsh2 : w ^ 2 / 4 ≤ sh := by
    rw [hw2]; linarith only [hsh, hsq]
  have hsw : w / 2 ≤ Real.sqrt sh := by
    refine Real.le_sqrt_of_sq_le ?_
    nlinarith only [hsh2]
  have hshpos : 0 < Real.sqrt sh := lt_of_lt_of_le (by positivity) hsw
  have hinv : (Real.sqrt sh)⁻¹ ≤ 2 / w := by
    calc (Real.sqrt sh)⁻¹ ≤ (w / 2)⁻¹ := inv_anti₀ (by positivity) hsw
      _ = 2 / w := by rw [inv_div]
  have hw' : 2 / w = 2 * (cStar ^ (-(1 / 4 : ℝ)) * Real.log R ^ (-(1 / 4 : ℝ))) := by
    rw [hw, Real.mul_rpow hc.le hL0.le, Real.rpow_neg hc.le, Real.rpow_neg hL0.le,
      ← mul_inv, div_eq_mul_inv]
  have hcoef : 0 ≤ cStar ^ (-(1 / 4 : ℝ)) * Real.log R ^ (-(1 / 4 : ℝ)) := by positivity
  calc (3 : ℝ) ^ m * (Real.sqrt sh)⁻¹ ≤ (6 * R) * (2 * (cStar ^ (-(1 / 4 : ℝ)) * Real.log R ^ (-(1 / 4 : ℝ)))) := by
        rw [← hw'] at *
        exact mul_le_mul h6.le (hinv.trans_eq hw') (by positivity) (by positivity)
    _ = 12 * R * (cStar ^ (-(1 / 4 : ℝ)) * Real.log R ^ (-(1 / 4 : ℝ))) := by ring

/-- The second coefficient. -/
theorem sdPoinc_coef_second {R M : ℝ} {m : ℕ} (hR : 3 ≤ R) (h2 : 2 * R ≤ (3 : ℝ) ^ m)
    (h6 : (3 : ℝ) ^ m < 6 * R) (hM : 101 ≤ M * Real.log 3) :
    (3 : ℝ) ^ (2 * (m : ℝ) - (⌈M * Real.log (m : ℝ)⌉ : ℝ)) ≤
      36 * (2 : ℝ) ^ (101 : ℝ) * R ^ 2 * Real.log R ^ (-(100 : ℝ)) := by
  have hR1 : 1 ≤ R := by linarith only [hR]
  have hL1 : 1 ≤ Real.log R := by
    have := sdPoinc_one_le_log_three
    exact this.trans (Real.log_le_log (by norm_num) hR)
  have hL0 : 0 < Real.log R := by linarith only [hL1]
  have hmg := sdPoinc_m_ge hR1 h2
  have hm1 : (1 : ℝ) ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | hp
    · rw [h0] at h2; norm_num at h2; linarith only [h2, hR]
    · exact_mod_cast hp
  have hm0 : (0 : ℝ) < m := by linarith only [hm1]
  have hlogm : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hm1
  -- split the power
  have hsplit : (3 : ℝ) ^ (2 * (m : ℝ) - (⌈M * Real.log (m : ℝ)⌉ : ℝ)) =
      ((3 : ℝ) ^ m) ^ 2 * (3 : ℝ) ^ (-(⌈M * Real.log (m : ℝ)⌉ : ℝ)) := by
    rw [sub_eq_add_neg, Real.rpow_add (by norm_num), show 2 * (m : ℝ) = ((2 * m : ℕ) : ℝ) by
      push_cast; ring, Real.rpow_natCast, pow_mul']
  have hceil : (3 : ℝ) ^ (-(⌈M * Real.log (m : ℝ)⌉ : ℝ)) ≤ (3 : ℝ) ^ (-(M * Real.log (m : ℝ))) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
      have := Int.le_ceil (M * Real.log (m : ℝ)); linarith only [this])
  have hconv : (3 : ℝ) ^ (-(M * Real.log (m : ℝ))) = (m : ℝ) ^ (-(M * Real.log 3)) := by
    rw [Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos hm0]
    congr 1; ring
  have hm101 : (m : ℝ) ^ (-(M * Real.log 3)) ≤ (m : ℝ) ^ (-(101 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hm1 (by linarith only [hM])
  have hhalf : (m : ℝ) ^ (-(101 : ℝ)) ≤ (Real.log R / 2) ^ (-(101 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hmg (by norm_num)
  have hdiv : (Real.log R / 2) ^ (-(101 : ℝ)) = (2 : ℝ) ^ (101 : ℝ) * Real.log R ^ (-(101 : ℝ)) := by
    rw [Real.div_rpow hL0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      div_eq_mul_inv, inv_inv]
    ring
  have hL100 : Real.log R ^ (-(101 : ℝ)) ≤ Real.log R ^ (-(100 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have h3sq : ((3 : ℝ) ^ m) ^ 2 ≤ 36 * R ^ 2 := by
    have : (0 : ℝ) ≤ 3 ^ m := by positivity
    nlinarith only [h6, this, hR]
  have hp : 0 ≤ (2 : ℝ) ^ (101 : ℝ) * Real.log R ^ (-(100 : ℝ)) := by positivity
  calc (3 : ℝ) ^ (2 * (m : ℝ) - (⌈M * Real.log (m : ℝ)⌉ : ℝ))
      = ((3 : ℝ) ^ m) ^ 2 * (3 : ℝ) ^ (-(⌈M * Real.log (m : ℝ)⌉ : ℝ)) := hsplit
    _ ≤ (36 * R ^ 2) * ((2 : ℝ) ^ (101 : ℝ) * Real.log R ^ (-(100 : ℝ))) := by
        refine mul_le_mul h3sq ?_ (by positivity) (by positivity)
        calc (3 : ℝ) ^ (-(⌈M * Real.log (m : ℝ)⌉ : ℝ)) ≤ (3 : ℝ) ^ (-(M * Real.log (m : ℝ))) := hceil
          _ = (m : ℝ) ^ (-(M * Real.log 3)) := hconv
          _ ≤ (m : ℝ) ^ (-(101 : ℝ)) := hm101
          _ ≤ (Real.log R / 2) ^ (-(101 : ℝ)) := hhalf
          _ = (2 : ℝ) ^ (101 : ℝ) * Real.log R ^ (-(101 : ℝ)) := hdiv
          _ ≤ (2 : ℝ) ^ (101 : ℝ) * Real.log R ^ (-(100 : ℝ)) :=
            mul_le_mul_of_nonneg_left hL100 (by positivity)
    _ = 36 * (2 : ℝ) ^ (101 : ℝ) * R ^ 2 * Real.log R ^ (-(100 : ℝ)) := by ring




/-- Enlarging a scale deterministically keeps the stretched-exponential control of its logarithm. -/
theorem sdPoinc_isBigO_max_exp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {ρ L c : ℝ} {X : Ω → ℝ} (hX : ∀ ω, 1 ≤ X ω) (hc : 0 ≤ c)
    (h : Homogenization.IndependentSums.IsBigO μ (Homogenization.IndependentSums.gammaSigma ρ)
      (fun ω => Real.log (X ω)) L) :
    Homogenization.IndependentSums.IsBigO μ (Homogenization.IndependentSums.gammaSigma ρ)
      (fun ω => Real.log (max (X ω) (Real.exp c))) (max L c) := by
  rw [Homogenization.IndependentSums.isBigO_gammaSigma_iff] at h ⊢
  intro t ht
  refine le_trans (measureReal_mono ?_) (h ht)
  intro ω hω
  have hω' : max L c * t < |Real.log (max (X ω) (Real.exp c))| := hω
  have hlog : Real.log (max (X ω) (Real.exp c)) = max (Real.log (X ω)) c := by
    rcases le_total (X ω) (Real.exp c) with h1 | h1
    · rw [max_eq_right h1, Real.log_exp]
      exact (max_eq_right (by
        have := Real.log_le_log (by linarith only [hX ω]) h1
        rwa [Real.log_exp] at this)).symm
    · rw [max_eq_left h1]
      exact (max_eq_left (by
        have := Real.log_le_log (Real.exp_pos c) h1
        rwa [Real.log_exp] at this)).symm
  have hl0 : 0 ≤ Real.log (X ω) := Real.log_nonneg (hX ω)
  rw [hlog, abs_of_nonneg (le_trans hl0 (le_max_left _ _))] at hω'
  show L * t < |Real.log (X ω)|
  rw [abs_of_nonneg hl0]
  have ht0 : 1 ≤ t := ht
  have hLt : L * t ≤ max L c * t := mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith only [ht0])
  rcases le_total (Real.log (X ω)) c with h1 | h1
  · rw [max_eq_right h1] at hω'
    have : c ≤ max L c * t := by
      have h2 : c ≤ max L c := le_max_right _ _
      have h3 : max L c ≤ max L c * t := by
        have hm : 0 ≤ max L c := hc.trans (le_max_right _ _)
        nlinarith only [hm, ht0]
      linarith only [h2, h3]
    linarith only [hω', this]
  · rw [max_eq_left h1] at hω'
    linarith only [hω', hLt]


end SuperdiffusionCLT.Section8
