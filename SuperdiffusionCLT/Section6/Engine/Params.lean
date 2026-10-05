/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The rate sequence `δ_j = j^{-β} log j`

`δ_j` is eventually small against any block length and eventually antitone; the rate at the
scale `k` with `2r ≤ 3^k ≤ 6r` is bounded by `4` times the rate at `log r`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6

/-- Antitonicity of `x ↦ x^{-β} log x` beyond `e^{1/β}`, in ratio form. -/
private theorem ec1_anti {β : ℝ} {i j : ℝ} (hi1 : 1 ≤ i) (hij : i ≤ j)
    (hiβ : 1 ≤ β * Real.log i) :
    j ^ (-β) * Real.log j ≤ i ^ (-β) * Real.log i := by
  have hi0 : 0 < i := lt_of_lt_of_le one_pos hi1
  have hj0 : 0 < j := lt_of_lt_of_le hi0 hij
  set t : ℝ := j / i with ht
  have ht1 : 1 ≤ t := by rw [ht, le_div_iff₀ hi0]; linarith only [hij]
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht1
  have hjt : j = i * t := by rw [ht]; field_simp
  have hlogj : Real.log j = Real.log i + Real.log t := by
    rw [hjt, Real.log_mul hi0.ne' ht0.ne']
  have hlt0 : 0 ≤ Real.log t := Real.log_nonneg ht1
  have hli0 : 0 ≤ Real.log i := Real.log_nonneg hi1
  have hexp : β * Real.log t + 1 ≤ t ^ β := by
    have := Real.add_one_le_exp (β * Real.log t)
    rwa [Real.rpow_def_of_pos ht0, mul_comm (Real.log t) β]
  have hkey : Real.log j ≤ t ^ β * Real.log i := by
    rw [hlogj]
    have h1 : Real.log t ≤ β * Real.log t * Real.log i := by
      have := mul_le_mul_of_nonneg_left hiβ hlt0
      nlinarith only [this]
    have h2 : (β * Real.log t + 1) * Real.log i ≤ t ^ β * Real.log i :=
      mul_le_mul_of_nonneg_right hexp hli0
    nlinarith only [h1, h2]
  have hjneg : j ^ (-β) = i ^ (-β) * (t ^ β)⁻¹ := by
    rw [hjt, Real.mul_rpow hi0.le ht0.le, Real.rpow_neg ht0.le]
  have htb : 0 < t ^ β := Real.rpow_pos_of_pos ht0 β
  rw [hjneg, mul_assoc, mul_comm ((t ^ β)⁻¹), ← mul_assoc, mul_assoc]
  have hip : 0 < i ^ (-β) := Real.rpow_pos_of_pos hi0 _
  have : Real.log j * (t ^ β)⁻¹ ≤ Real.log i := by
    rw [← div_eq_mul_inv, div_le_iff₀ htb]; linarith only [hkey, mul_comm (t ^ β) (Real.log i)]
  calc i ^ (-β) * (Real.log j * (t ^ β)⁻¹) ≤ i ^ (-β) * Real.log i :=
        mul_le_mul_of_nonneg_left this hip.le
    _ = _ := rfl

/-- **The rate sequence**: `δ_j = j^{-β} log j` is eventually small against any block length and
eventually antitone. -/
theorem eng_params (β c : ℝ) (hβ : 0 < β) (hc : 0 < c) (Hb : ℕ) :
    ∃ m0 : ℕ, 3 ≤ m0 ∧
      (∀ j : ℕ, m0 ≤ j →
        0 ≤ (j : ℝ) ^ (-β) * Real.log (j : ℝ) ∧
          (j : ℝ) ^ (-β) * Real.log (j : ℝ) * ((Hb : ℝ) + 1) ≤ c) ∧
      ∀ i j : ℕ, m0 ≤ i → i ≤ j →
        (j : ℝ) ^ (-β) * Real.log (j : ℝ) ≤ (i : ℝ) ^ (-β) * Real.log (i : ℝ) := by
  have hlim : Filter.Tendsto (fun x : ℝ => Real.log x / x ^ β) Filter.atTop (nhds 0) :=
    (isLittleO_log_rpow_atTop hβ).tendsto_div_nhds_zero
  have hHb : (0 : ℝ) < (Hb : ℝ) + 1 := by positivity
  have hev : ∀ᶠ x : ℝ in Filter.atTop, Real.log x / x ^ β < c / ((Hb : ℝ) + 1) :=
    hlim.eventually (gt_mem_nhds (by positivity))
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.1 hev
  refine ⟨max 3 (max (⌈X⌉₊) (⌈Real.exp (1 / β)⌉₊)), le_max_left _ _, ?_, ?_⟩
  · intro j hj
    have hj3 : (3 : ℝ) ≤ j := by exact_mod_cast le_trans (le_max_left _ _) hj
    have hjX : X ≤ (j : ℝ) :=
      le_trans (Nat.le_ceil _) (Nat.cast_le.2 (le_trans (le_trans (le_max_left _ _)
        (le_max_right _ _)) hj))
    have hj0 : (0 : ℝ) < j := by linarith only [hj3]
    have hlog : 0 ≤ Real.log (j : ℝ) := Real.log_nonneg (by linarith only [hj3])
    have hpos : 0 < (j : ℝ) ^ β := Real.rpow_pos_of_pos hj0 β
    have hrw : (j : ℝ) ^ (-β) * Real.log (j : ℝ) = Real.log (j : ℝ) / (j : ℝ) ^ β := by
      rw [Real.rpow_neg hj0.le, inv_mul_eq_div]
    refine ⟨by rw [hrw]; positivity, ?_⟩
    have := hX _ hjX
    rw [lt_div_iff₀ hHb] at this
    rw [hrw]
    exact this.le
  · intro i j hi hij
    have hi3 : (3 : ℝ) ≤ i := by exact_mod_cast le_trans (le_max_left _ _) hi
    have hie : Real.exp (1 / β) ≤ (i : ℝ) :=
      le_trans (Nat.le_ceil _) (Nat.cast_le.2 (le_trans (le_trans (le_max_right _ _)
        (le_max_right _ _)) hi))
    have hiβ : 1 ≤ β * Real.log (i : ℝ) := by
      have h1 : 1 / β ≤ Real.log (i : ℝ) :=
        (Real.le_log_iff_exp_le (by linarith only [hi3])).2 hie
      have := mul_le_mul_of_nonneg_left h1 hβ.le
      rwa [mul_one_div_cancel hβ.ne'] at this
    exact ec1_anti (by linarith only [hi3]) (by exact_mod_cast hij) hiβ

/-- Parameters witness for `eng_params`. -/
example : ∃ m0 : ℕ, 3 ≤ m0 := by
  obtain ⟨m0, h, -⟩ := eng_params (1 / 4) 1 (by norm_num) one_pos 0
  exact ⟨m0, h⟩

/-- **Conversion of the rate**: `k^{-β} log k ≤ 4 (log r)^{-β} log log r` when `2r ≤ 3^k ≤ 6r`. -/
theorem eng_rate_convert (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 2) (k : ℕ) (r : ℝ) (hk : 5 ≤ k)
    (h1 : 2 * r ≤ (3 : ℝ) ^ k) (h2 : (3 : ℝ) ^ k ≤ 6 * r) :
    (k : ℝ) ^ (-β) * Real.log (k : ℝ) ≤
      4 * (Real.log r ^ (-β) * Real.log (Real.log r)) := by
  have he1 := Real.exp_one_gt_d9
  have he2 := Real.exp_one_lt_d9
  have hl3a : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]; linarith only [he2]
  have hl3b : Real.log 3 ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by norm_num), show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith only [he1]
  have hk5 : (5 : ℝ) ≤ k := by exact_mod_cast hk
  have h35 : (3 : ℝ) ^ 5 ≤ (3 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hk
  have hr : 27 ≤ r := by norm_num at h35; linarith only [h35, h2]
  have hr0 : 0 < r := by linarith only [hr]
  set ℓ := Real.log r with hℓ
  have hℓ3 : 3 ≤ ℓ := by
    have : Real.log 27 ≤ ℓ := Real.log_le_log (by norm_num) hr
    have h27 : Real.log 27 = 3 * Real.log 3 := by
      rw [show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow]; norm_num
    linarith only [this, h27, hl3a]
  have hℓ0 : 0 < ℓ := by linarith only [hℓ3]
  have hk0 : (0 : ℝ) < k := by linarith only [hk5]
  have hlk : (k : ℝ) * Real.log 3 = Real.log ((3 : ℝ) ^ k) := by
    rw [Real.log_pow]
  have hlow : ℓ ≤ (k : ℝ) * Real.log 3 := by
    rw [hlk]
    have := Real.log_le_log (by positivity) h1
    rw [Real.log_mul (by norm_num) hr0.ne'] at this
    have h2l : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith only [this, h2l]
  have hup : (k : ℝ) * Real.log 3 ≤ Real.log 6 + ℓ := by
    rw [hlk]
    have := Real.log_le_log (by positivity) h2
    rwa [Real.log_mul (by norm_num) hr0.ne'] at this
  have hl6 : Real.log 6 ≤ ℓ := Real.log_le_log (by norm_num) (by linarith only [hr])
  have hkl : ℓ / 2 ≤ (k : ℝ) := by
    nlinarith only [hlow, hl3b, hk0]
  have hku : (k : ℝ) ≤ 2 * ℓ := by
    nlinarith only [hup, hl3a, hl6, hk0]
  have hneg : (k : ℝ) ^ (-β) ≤ 2 * ℓ ^ (-β) := by
    have h1' : (ℓ / 2) ^ (-β) ≥ (k : ℝ) ^ (-β) :=
      Real.rpow_le_rpow_of_nonpos (by linarith only [hℓ3]) hkl (by linarith only [hβ0])
    have h2' : (ℓ / 2) ^ (-β) = ℓ ^ (-β) * 2 ^ β := by
      rw [Real.div_rpow hℓ0.le (by norm_num), Real.rpow_neg hℓ0.le, Real.rpow_neg (by norm_num),
        div_eq_mul_inv, inv_inv]
    have h3' : (2 : ℝ) ^ β ≤ 2 := by
      calc (2 : ℝ) ^ β ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hβ1])
        _ = 2 := Real.rpow_one 2
    have hp : 0 < ℓ ^ (-β) := Real.rpow_pos_of_pos hℓ0 _
    rw [h2'] at h1'
    nlinarith only [h1', h3', hp]
  have hlogk : Real.log (k : ℝ) ≤ 2 * Real.log ℓ := by
    have := Real.log_le_log hk0 hku
    rw [Real.log_mul (by norm_num) hℓ0.ne'] at this
    have h2l : Real.log 2 ≤ Real.log ℓ := Real.log_le_log (by norm_num) (by linarith only [hℓ3])
    linarith only [this, h2l]
  have hlogk0 : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by linarith only [hk5])
  have hp : 0 < ℓ ^ (-β) := Real.rpow_pos_of_pos hℓ0 _
  have hkp : 0 ≤ (k : ℝ) ^ (-β) := Real.rpow_nonneg hk0.le _
  calc (k : ℝ) ^ (-β) * Real.log (k : ℝ) ≤ (2 * ℓ ^ (-β)) * (2 * Real.log ℓ) :=
        mul_le_mul hneg hlogk hlogk0 (by positivity)
    _ = 4 * (ℓ ^ (-β) * Real.log ℓ) := by ring

/-- Witness for the numerical hypotheses of `eng_rate_convert`: `r = 3^5/2`, `k = 5`. -/
example : (5 : ℕ) ≤ 5 ∧ 2 * ((3 : ℝ) ^ 5 / 2) ≤ (3 : ℝ) ^ 5 ∧ (3 : ℝ) ^ 5 ≤ 6 * ((3 : ℝ) ^ 5 / 2) := by
  norm_num

end SuperdiffusionCLT.Section6
