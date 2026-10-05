/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.FieldDiffusion

/-!
# The quenched second moment: bookkeeping of the scales

With `L = log t`, `Λ = L^{(1+α)/2}`, `r = √(tΛ)` and `ε = r⁻¹` (`e.rtnaught.def`), the real-variable
consequence of the moment bounds: the deviation of `m2 / t` from `2 d √c⋆ √L` and the squared mean
are at most a constant times `L^{(1-α)/2}`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization

/-- The bookkeeping of scales: `t ≥ 10`, `L = log t`, `Λ = L^{(1+α)/2}`, `r = √(tΛ)`, `ε = r⁻¹`. -/
theorem dtExp_scale_facts {t α : ℝ} (ht : 10 ≤ t) (hα0 : 0 < α) (hα1 : α < 1) :
    1 ≤ Real.log t ∧ 1 ≤ Real.log t ^ ((1 + α) / 2) ∧ Real.log t ^ ((1 + α) / 2) ≤ Real.log t := by
  have hL : 1 ≤ Real.log t := by
    rw [Real.le_log_iff_exp_le (by linarith only [ht])]
    have := Real.exp_one_lt_d9
    linarith only [this, ht]
  refine ⟨hL, Real.one_le_rpow hL (by linarith only [hα0]), ?_⟩
  calc Real.log t ^ ((1 + α) / 2) ≤ Real.log t ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL (by linarith only [hα1])
    _ = Real.log t := Real.rpow_one _

/-- The scale `ε = r⁻¹`. -/
theorem dtExp_eps_facts {t α : ℝ} (ht : 10 ≤ t) (hα0 : 0 < α) (hα1 : α < 1) {c : ℝ} (hc : 0 < c) :
    let L := Real.log t
    let Λ := L ^ ((1 + α) / 2)
    let ε := (Real.sqrt (t * Λ))⁻¹
    0 < ε ∧ ε ^ 2 * (t * Λ) = 1 ∧ ε ≤ 1 / 2 ∧
    L / 2 ≤ |Real.log ε| ∧ |Real.log ε| ≤ L ∧
    opScale c ε * (2 * Real.sqrt (2 * c * |Real.log ε|)) = 1 ∧
    |2 * Real.sqrt (2 * c * |Real.log ε|) - 2 * Real.sqrt c * Real.sqrt L| ≤ 4 * Real.sqrt c := by
  intro L Λ ε
  obtain ⟨hL, hΛ1, hΛL⟩ := dtExp_scale_facts ht hα0 hα1
  have hΛ0 : 0 < Λ := by linarith only [hΛ1]
  have ht0 : 0 < t := by linarith only [ht]
  have htΛ : 0 < t * Λ := mul_pos ht0 hΛ0
  have hsq : 0 < Real.sqrt (t * Λ) := Real.sqrt_pos.2 htΛ
  have hε0 : 0 < ε := inv_pos.2 hsq
  have hε2 : ε ^ 2 * (t * Λ) = 1 := by
    have : ε ^ 2 = (t * Λ)⁻¹ := by
      show ((Real.sqrt (t * Λ))⁻¹) ^ 2 = _
      rw [inv_pow, Real.sq_sqrt htΛ.le]
    rw [this]; field_simp
  have hr2 : 2 ≤ Real.sqrt (t * Λ) := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith only [ht, hΛ1])
  have hεhalf : ε ≤ 1 / 2 := by
    show (Real.sqrt (t * Λ))⁻¹ ≤ 1 / 2
    rw [inv_le_comm₀ hsq (by norm_num)]
    simpa using hr2
  -- the logarithm
  have hlogε : Real.log ε = -((L + ((1 + α) / 2) * Real.log L) / 2) := by
    show Real.log ((Real.sqrt (t * Λ))⁻¹) = _
    rw [Real.log_inv, Real.log_sqrt htΛ.le, Real.log_mul ht0.ne' hΛ0.ne']
    have : Real.log Λ = (1 + α) / 2 * Real.log L := Real.log_rpow (by linarith only [hL]) _
    rw [this]
  have hlogL0 : 0 ≤ Real.log L := Real.log_nonneg hL
  have hlogLle : Real.log L ≤ L := by
    have := Real.log_le_sub_one_of_pos (show 0 < L by linarith only [hL])
    linarith only [this]
  have hv : |Real.log ε| = (L + ((1 + α) / 2) * Real.log L) / 2 := by
    rw [hlogε, abs_neg, abs_of_nonneg (by positivity)]
  have hv1 : L / 2 ≤ |Real.log ε| := by
    rw [hv]; nlinarith only [hlogL0, hα0]
  have hv2 : |Real.log ε| ≤ L := by
    rw [hv]; nlinarith only [hlogLle, hα1, hlogL0]
  refine ⟨hε0, hε2, hεhalf, hv1, hv2, ?_, ?_⟩
  · have hpos : 0 < 2 * c * |Real.log ε| := by
      have : 0 < |Real.log ε| := by linarith only [hv1, hL]
      positivity
    have hs : 0 < Real.sqrt (2 * c * |Real.log ε|) := Real.sqrt_pos.2 hpos
    unfold opScale
    rw [← Real.sqrt_eq_rpow]
    field_simp
  · set v := |Real.log ε| with hvdef
    have hv0 : 0 ≤ 2 * v := by linarith only [hv1, hL]
    have hη : 2 * v = L + ((1 + α) / 2) * Real.log L := by rw [hv]; ring
    have hηle : 0 ≤ ((1 + α) / 2) * Real.log L := by positivity
    have hηle2 : ((1 + α) / 2) * Real.log L ≤ L := by nlinarith only [hlogLle, hα1, hlogL0]
    have hsL : 0 < Real.sqrt L := Real.sqrt_pos.2 (by linarith only [hL])
    -- |√(2v) - √L| ≤ 2
    have h2v : |Real.sqrt (2 * v) - Real.sqrt L| ≤ 2 := by
      have hge : Real.sqrt L ≤ Real.sqrt (2 * v) := Real.sqrt_le_sqrt (by linarith only [hη, hηle])
      rw [abs_of_nonneg (by linarith only [hge])]
      have hprod : (Real.sqrt (2 * v) - Real.sqrt L) * (Real.sqrt (2 * v) + Real.sqrt L) =
          ((1 + α) / 2) * Real.log L := by
        have e1 := Real.sq_sqrt hv0
        have e2 := Real.sq_sqrt (show 0 ≤ L by linarith only [hL])
        nlinarith only [e1, e2, hη]
      have hlog : Real.log L ≤ 2 * Real.sqrt L := by
        have h := Real.log_le_sub_one_of_pos hsL
        rw [Real.log_sqrt (by linarith only [hL])] at h
        linarith only [h]
      have hη2 : ((1 + α) / 2) * Real.log L ≤ 2 * Real.sqrt L := by
        nlinarith only [hlog, hα1, hlogL0]
      by_contra hcon
      have hgt : 2 < Real.sqrt (2 * v) - Real.sqrt L := not_le.1 hcon
      have : 2 * (2 * Real.sqrt L) ≤ (Real.sqrt (2 * v) - Real.sqrt L) *
          (Real.sqrt (2 * v) + Real.sqrt L) := by
        apply mul_le_mul hgt.le (by linarith only [hge, hsL]) (by positivity) (by linarith only [hgt])
      linarith only [this, hprod, hη2, hsL]
    have : 2 * Real.sqrt (2 * c * v) - 2 * Real.sqrt c * Real.sqrt L =
        2 * Real.sqrt c * (Real.sqrt (2 * v) - Real.sqrt L) := by
      rw [show 2 * c * v = c * (2 * v) by ring, Real.sqrt_mul hc.le]; ring
    rw [this, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt c)]
    have := mul_le_mul_of_nonneg_left h2v (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt c)
    linarith only [this]

theorem dtExp_numerics {d : ℕ} (hd : 1 ≤ d) {t α c C0 E0 a p m2 : ℝ} (m : Vec d)
    (ht : 10 ≤ t) (hα0 : 0 < α) (hα1 : α < 1) (hc : 0 < c) (hC0 : 1 ≤ C0)
    (hE0' : E0 ≤ 8 * C0 * Real.log t ^ (-α)) (ha : 0 ≤ a) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hap : a * Real.sqrt p ≤ 1) (hLp : Real.log t * p ≤ 1)
    (hI : |((Real.sqrt (t * Real.log t ^ ((1 + α) / 2)))⁻¹) ^ 2 / d * m2 -
        ((Real.sqrt (t * Real.log t ^ ((1 + α) / 2)))⁻¹) ^ 2 /
          opScale c ((Real.sqrt (t * Real.log t ^ ((1 + α) / 2)))⁻¹) * t| ≤
      2 * (E0 * (2 / d + 1)) +
        ((Real.sqrt (t * Real.log t ^ ((1 + α) / 2)))⁻¹) ^ 2 / d *
          (a * t * Real.sqrt p + (((Real.sqrt (t * Real.log t ^ ((1 + α) / 2)))⁻¹)⁻¹) ^ 2 * p) +
        ((Real.sqrt (t * Real.log t ^ ((1 + α) / 2)))⁻¹) ^ 2 /
          opScale c ((Real.sqrt (t * Real.log t ^ ((1 + α) / 2)))⁻¹) * (t * p))
    (hII : ∀ i : Fin d, |m i| ≤ 2 * E0 * ((Real.sqrt (t * Real.log t ^ ((1 + α) / 2)))⁻¹)⁻¹ +
      (Real.sqrt (a * t) * Real.sqrt p +
        ((Real.sqrt (t * Real.log t ^ ((1 + α) / 2)))⁻¹)⁻¹ * p)) :
    |m2 / t - 2 * d * Real.sqrt c * Real.sqrt (Real.log t)| + vecNormSq m / t ≤
      (16 * (2 + d) * C0 + 2 + 2 * d * Real.sqrt (2 * c) + 4 * d * Real.sqrt c +
        d * (16 * C0 + 2) ^ 2) * Real.log t ^ ((1 - α) / 2) := by
  obtain ⟨hL, hΛ1, hΛL⟩ := dtExp_scale_facts ht hα0 hα1
  obtain ⟨hε0, hε2, hεhalf, hv1, hv2, hop, hdiff⟩ := dtExp_eps_facts ht hα0 hα1 hc
  set L := Real.log t with hLdef
  set Λ := L ^ ((1 + α) / 2) with hΛdef
  set ε := (Real.sqrt (t * Λ))⁻¹ with hεdef
  have ht0 : 0 < t := by linarith only [ht]
  have hΛ0 : 0 < Λ := by linarith only [hΛ1]
  have hL0 : 0 < L := by linarith only [hL]
  have hd0 : (0 : ℝ) < d := Nat.cast_pos.2 (by omega)
  set v := |Real.log ε| with hvdef
  have hvpos : 0 < v := by linarith only [hv1, hL]
  set κ := 2 * Real.sqrt (2 * c * v) with hκ
  have hκpos : 0 < κ := by
    have : 0 < Real.sqrt (2 * c * v) := Real.sqrt_pos.2 (by positivity)
    linarith only [this]
  have hopeq : opScale c ε = κ⁻¹ := eq_inv_of_mul_eq_one_left hop
  have hρ : ε ^ 2 = 1 / (t * Λ) := by
    rw [eq_div_iff (mul_pos ht0 hΛ0).ne']; linarith only [hε2]
  have hrr : (ε⁻¹) ^ 2 = t * Λ := by
    rw [inv_pow, hρ]; field_simp
  have hεinv : ε⁻¹ = Real.sqrt t * Real.sqrt Λ := by
    rw [hεdef, inv_inv, Real.sqrt_mul ht0.le]
  rw [hopeq, div_inv_eq_mul] at hI
  rw [hrr] at hI
  rw [hεinv] at hII
  have hsp : Real.sqrt p ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hp1
  have hsp0 : 0 ≤ Real.sqrt p := Real.sqrt_nonneg p
  -- part 1
  have hX : m2 / t - d * κ = (d * Λ) * (ε ^ 2 / d * m2 - ε ^ 2 * κ * t) := by
    rw [hρ]; field_simp
  have hRe : (d * Λ) * (2 * (E0 * (2 / d + 1)) + ε ^ 2 / d * (a * t * Real.sqrt p + t * Λ * p) +
      ε ^ 2 * κ * (t * p)) =
      2 * Λ * E0 * (2 + d) + a * Real.sqrt p + Λ * p + d * κ * p := by
    rw [hρ]; field_simp; ring
  have hI2 : |m2 / t - d * κ| ≤ 2 * Λ * E0 * (2 + d) + a * Real.sqrt p + Λ * p + d * κ * p := by
    rw [hX, abs_mul, abs_of_pos (mul_pos hd0 hΛ0), ← hRe]
    exact mul_le_mul_of_nonneg_left hI (by positivity)
  -- part 2
  have hI3 : |d * κ - 2 * d * Real.sqrt c * Real.sqrt L| ≤ 4 * d * Real.sqrt c := by
    have : d * κ - 2 * d * Real.sqrt c * Real.sqrt L =
        d * (2 * Real.sqrt (2 * c * v) - 2 * Real.sqrt c * Real.sqrt L) := by rw [hκ]; ring
    rw [this, abs_mul, abs_of_pos hd0]
    have := mul_le_mul_of_nonneg_left hdiff hd0.le
    linarith only [this]
  -- the bounds on the pieces
  set W := L ^ ((1 - α) / 2) with hW
  have hW1 : 1 ≤ W := Real.one_le_rpow hL (by linarith only [hα1])
  have hΛLα : Λ * L ^ (-α) = W := by
    rw [hΛdef, ← Real.rpow_add hL0, hW]; congr 1; ring
  have b1 : 2 * Λ * E0 * (2 + d) ≤ 16 * (2 + d) * C0 * W := by
    have h1 : Λ * E0 ≤ Λ * (8 * C0 * L ^ (-α)) := mul_le_mul_of_nonneg_left hE0' hΛ0.le
    have h2 : Λ * (8 * C0 * L ^ (-α)) = 8 * C0 * W := by rw [← hΛLα]; ring
    have h3 : 0 ≤ 2 + (d : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left (h1.trans h2.le) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) h3)
    nlinarith only [this]
  have b3 : Λ * p ≤ 1 := (mul_le_mul_of_nonneg_right hΛL hp0).trans hLp
  have hsqL : Real.sqrt L ≤ L := by
    calc Real.sqrt L ≤ Real.sqrt L * Real.sqrt L := by
          have : 1 ≤ Real.sqrt L := by
            rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hL
          nlinarith only [this, Real.sqrt_nonneg L]
      _ = L := Real.mul_self_sqrt hL0.le
  have hκle : κ ≤ 2 * Real.sqrt (2 * c) * L := by
    have h1 : Real.sqrt (2 * c * v) ≤ Real.sqrt (2 * c * L) :=
      Real.sqrt_le_sqrt (by gcongr)
    have h1' : Real.sqrt (2 * c * L) = Real.sqrt (2 * c) * Real.sqrt L :=
      Real.sqrt_mul (by positivity) L
    have h2 := mul_le_mul_of_nonneg_left hsqL (Real.sqrt_nonneg (2 * c))
    rw [hκ]; linarith only [h1, h1', h2]
  have b4 : d * κ * p ≤ 2 * d * Real.sqrt (2 * c) := by
    have h1 : d * κ * p ≤ d * (2 * Real.sqrt (2 * c) * L) * p := by gcongr
    have h2 : d * (2 * Real.sqrt (2 * c) * L) * p = 2 * d * Real.sqrt (2 * c) * (L * p) := by ring
    have h3 : 0 ≤ 2 * (d : ℝ) * Real.sqrt (2 * c) := by positivity
    have := mul_le_mul_of_nonneg_left hLp h3
    linarith only [h1, h2, this]
  have hmain : |m2 / t - 2 * d * Real.sqrt c * Real.sqrt L| ≤
      (16 * (2 + d) * C0 + 2 + 2 * d * Real.sqrt (2 * c) + 4 * d * Real.sqrt c) * W := by
    have h1 := abs_sub_le (m2 / t) (d * κ) (2 * d * Real.sqrt c * Real.sqrt L)
    have h4 : 0 ≤ 2 * (d : ℝ) * Real.sqrt (2 * c) := by positivity
    have h5 : 0 ≤ 4 * (d : ℝ) * Real.sqrt c := by positivity
    have h6 : 0 ≤ 16 * (2 + (d : ℝ)) * C0 := by positivity
    have hWm : 0 ≤ W - 1 := by linarith only [hW1]
    have h7 := mul_nonneg h4 hWm
    have h8 := mul_nonneg h5 hWm
    linarith only [h1, hI2, hI3, b1, hap, b3, b4, hW1, h7, h8]
  -- part 4: the mean
  set w := L ^ ((1 - α) / 4) with hw
  have hw1 : 1 ≤ w := Real.one_le_rpow hL (by linarith only [hα1])
  have hww : w * w = W := by
    rw [hw, hW, ← Real.rpow_add hL0]; congr 1; ring
  have hsqΛ : Real.sqrt Λ = L ^ ((1 + α) / 4) := by
    rw [Real.sqrt_eq_rpow, hΛdef, ← Real.rpow_mul hL0.le]; congr 1; ring
  have hmi : ∀ i : Fin d, |m i| ≤ Real.sqrt t * ((16 * C0 + 2) * w) := by
    intro i
    refine (hII i).trans ?_
    have hst : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
    have e1 : 2 * E0 * (Real.sqrt t * Real.sqrt Λ) ≤ Real.sqrt t * (16 * C0 * w) := by
      have h1 : 2 * E0 ≤ 2 * (8 * C0 * L ^ (-α)) := by linarith only [hE0']
      have h2 : L ^ (-α) * Real.sqrt Λ ≤ w := by
        rw [hsqΛ, ← Real.rpow_add hL0, hw]
        exact Real.rpow_le_rpow_of_exponent_le hL (by linarith only [hα0])
      have h3 : 2 * E0 * (Real.sqrt t * Real.sqrt Λ) ≤
          2 * (8 * C0 * L ^ (-α)) * (Real.sqrt t * Real.sqrt Λ) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      have h4 : 2 * (8 * C0 * L ^ (-α)) * (Real.sqrt t * Real.sqrt Λ) =
          Real.sqrt t * (16 * C0 * (L ^ (-α) * Real.sqrt Λ)) := by ring
      have h5 : Real.sqrt t * (16 * C0 * (L ^ (-α) * Real.sqrt Λ)) ≤ Real.sqrt t * (16 * C0 * w) := by
        gcongr
      linarith only [h3, h4, h5]
    have e2 : Real.sqrt (a * t) * Real.sqrt p ≤ Real.sqrt t * 1 := by
      have hap' : a * p ≤ 1 := by
        have : a * p = (a * Real.sqrt p) * Real.sqrt p := by
          rw [mul_assoc, Real.mul_self_sqrt hp0]
        rw [this]
        calc a * Real.sqrt p * Real.sqrt p ≤ 1 * 1 :=
              mul_le_mul hap hsp hsp0 zero_le_one
          _ = 1 := by norm_num
      rw [← Real.sqrt_mul (mul_nonneg ha ht0.le) p, mul_one]
      exact Real.sqrt_le_sqrt (by nlinarith only [hap', ht0])
    have e3 : Real.sqrt t * Real.sqrt Λ * p ≤ Real.sqrt t * 1 := by
      have hsΛ : Real.sqrt Λ ≤ Λ := by
        calc Real.sqrt Λ ≤ Real.sqrt Λ * Real.sqrt Λ := by
              have : 1 ≤ Real.sqrt Λ := by
                rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hΛ1
              nlinarith only [this, Real.sqrt_nonneg Λ]
          _ = Λ := Real.mul_self_sqrt hΛ0.le
      have : Real.sqrt Λ * p ≤ 1 := (mul_le_mul_of_nonneg_right hsΛ hp0).trans b3
      calc Real.sqrt t * Real.sqrt Λ * p = Real.sqrt t * (Real.sqrt Λ * p) := by ring
        _ ≤ Real.sqrt t * 1 := by gcongr
    have : Real.sqrt t * (16 * C0 * w) + Real.sqrt t * 1 + Real.sqrt t * 1 ≤
        Real.sqrt t * ((16 * C0 + 2) * w) := by
      have : 0 ≤ Real.sqrt t * (w - 1) := mul_nonneg hst (by linarith only [hw1])
      nlinarith only [this, hst, hw1]
    linarith only [e1, e2, e3, this]
  have hdrift : vecNormSq m / t ≤ d * (16 * C0 + 2) ^ 2 * W := by
    have h1 : vecNormSq m ≤ d * (t * ((16 * C0 + 2) ^ 2 * W)) := by
      unfold vecNormSq vecDot
      calc ∑ i, m i * m i ≤ ∑ _i : Fin d, t * ((16 * C0 + 2) ^ 2 * W) := by
            refine Finset.sum_le_sum fun i _ => ?_
            have h2 := sq_le_sq' (by linarith only [abs_nonneg (m i), hmi i, abs_le.1 (hmi i)] :
              -(Real.sqrt t * ((16 * C0 + 2) * w)) ≤ m i) (abs_le.1 (hmi i)).2
            have h3 : (Real.sqrt t * ((16 * C0 + 2) * w)) ^ 2 = t * ((16 * C0 + 2) ^ 2 * W) := by
              rw [mul_pow, Real.sq_sqrt ht0.le, mul_pow, sq w, hww]
            nlinarith only [h2, h3]
        _ = d * (t * ((16 * C0 + 2) ^ 2 * W)) := by simp
    rw [div_le_iff₀ ht0]
    nlinarith only [h1]
  nlinarith only [hmain, hdrift]

end SuperdiffusionCLT.Section8
