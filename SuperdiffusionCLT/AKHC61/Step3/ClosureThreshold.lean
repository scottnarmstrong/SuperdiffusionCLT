/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.Step3.ClosureScalesTails

/-!
# Closing Step 3 on the V5 range, part 3: V5's threshold gives the scale conditions

V5's `m₀` threshold is `m₀ ≥ C (L₁ + (1+D)/(1-γ)) (1+D)/((1-β)(1-γ)) · log X · log(3Θ₀(2 + L₁ log X))`
with `X = (Υ₁ + Υ₂)(m + m₀ + 1)Θ₀`. With `Y := log X` and `V := L₁ Y`, it gives
`m₀ ≥ C (1+D) V W`, `W := log(3Θ₀(2 + V))`, and `Y ≥ C (L₁ log(2L₂) + D + log(H + K_{Ψ_S})) +
log(m + m₀ + 1)`. From these:

* `ℓ̄ ≤ 4V`, `M ≤ (M_d + 20)V`, `log K₀ ≤ 7V`, `Lsum ≤ c₁(1+D)V`, `E ≤ 96(d+1)c₁(1+D)V + 1`;
* `Z + M ≤ c₂(1+D)V` and `K + 1 ≤ c₃ W` (the number of squaring blocks is `O(log V)`);
* so `ℓ̄ + K(Z+M) + Z ≤ (4 + c₂c₃)(1+D)VW ≤ m₀` once `C ≥ C_min(d)`, i.e. `N₀ ≤ m + 4m₀`.

The final theorem `akhcStep3_decay` has the conclusion of `akhcF1_core`'s `hStep3`, with
`U = akhcCL5_U d K_Ψ`, `C_s = 1` and `κ = akhcCL5_kappa d`. Its hypotheses are V5's binders, Step 2's
`0 < σ ≤ σ_d`, `C ≥ C_min(d)` with V5's `ω_m²` binder, and V5's `m₀` threshold.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.Step3

noncomputable section

/-! ## V5's threshold, by name -/

/-- V5's `X = (Υ₁ + Υ₂)(m + m₀ + 1)Θ₀`, written exactly as in the anchor. -/
def akhcCL5_thrX (d : ℕ) (C KPsi pPsi pPsiS L1 L2 D gamma H KPsiS : ℝ) (m m0 : ℕ) (Θ0 : ℝ) : ℝ :=
  (C * KPsi ^ (6 * (d + 1) ^ 2) / (min ((d : ℝ) + 1) pPsi - (d : ℝ)) +
      C / (min 3 pPsiS - 2) *
        Real.exp (C * ((L1 + D / (1 - gamma)) * Real.log (2 * L2) +
          (D + Real.log (H + KPsiS)) / (1 - gamma)))) *
    ((m : ℝ) + (m0 : ℝ) + 1) * Θ0

/-- V5's `m₀` threshold, written exactly as in the anchor. -/
def akhcCL5_thr (d : ℕ) (C KPsi pPsi pPsiS L1 L2 D gamma beta H KPsiS : ℝ) (m m0 : ℕ)
    (Θ0 : ℝ) : ℝ :=
  C * (L1 + (1 + D) / (1 - gamma)) * (1 + D) / ((1 - beta) * (1 - gamma)) *
    Real.log (akhcCL5_thrX d C KPsi pPsi pPsiS L1 L2 D gamma H KPsiS m m0 Θ0) *
    Real.log (3 * Θ0 * (2 + L1 *
      Real.log (akhcCL5_thrX d C KPsi pPsi pPsiS L1 L2 D gamma H KPsiS m m0 Θ0)))

/-! ## The dimension constants -/

/-- `c₁ := |log((6B+1)/(ζε))| + M_d + 58`. -/
def akhcCL5_c1 (d : ℕ) [NeZero d] : ℝ :=
  |Real.log ((6 * akhcCL5_B d + 1) / (akhcCL5_zeta d * akhcCL5_eps d))| +
    (akhcCL5_Md d : ℝ) + 58

/-- `c₂ := 13 + J + Z₂ + 96(d+1)c₁ + 2(M_d + 20)`. -/
def akhcCL5_c2 (d : ℕ) [NeZero d] : ℝ :=
  13 + (akhcDW_J (akhcCL5_theta d) (akhcCL5_B d) (akhcCL5_w d) (akhcCL5_Lstep d) : ℝ) +
    (akhcDW_Z2 (akhcCL5_theta d) (akhcCL5_B d) (akhcCL5_B d) (akhcCL5_w d) : ℝ) +
    96 * ((d : ℝ) + 1) * akhcCL5_c1 d + 2 * ((akhcCL5_Md d : ℝ) + 20)

/-- `c₃ := 2 log(M_d + 21) + 4`. -/
def akhcCL5_c3 (d : ℕ) [NeZero d] : ℝ := 2 * Real.log ((akhcCL5_Md d : ℝ) + 21) + 4

/-- **The constant of V5 that Step 3 needs**,
`C_min(d) := max{16, Lstep, 2 B c_Υ/(ζε), 4 + c₂c₃}`. -/
def akhcCL5_Cmin (d : ℕ) [NeZero d] : ℝ :=
  max (max 16 (akhcCL5_Lstep d : ℝ))
    (max (2 * akhcCL5_B d * akhcCL5_cUps d / (akhcCL5_zeta d * akhcCL5_eps d))
      (4 + akhcCL5_c2 d * akhcCL5_c3 d))

theorem akhcCL5_c1_nonneg (d : ℕ) [NeZero d] : 0 ≤ akhcCL5_c1 d := by
  unfold akhcCL5_c1
  positivity

theorem akhcCL5_c2_nonneg (d : ℕ) [NeZero d] : 0 ≤ akhcCL5_c2 d := by
  have := akhcCL5_c1_nonneg d
  unfold akhcCL5_c2
  positivity

theorem akhcCL5_c3_nonneg (d : ℕ) [NeZero d] : 0 ≤ akhcCL5_c3 d := by
  have : 0 ≤ Real.log ((akhcCL5_Md d : ℝ) + 21) := Real.log_nonneg (by
    have := Nat.cast_nonneg (α := ℝ) (akhcCL5_Md d)
    linarith only [this])
  unfold akhcCL5_c3
  positivity

/-! ## The threshold's two consequences -/

/-- **What V5's threshold gives.** With `Y := log X`: `Y ≥ C (L₁ log(2L₂) + D + log(H + K_{Ψ_S}))
+ log(m + m₀ + 1)`, `Y ≥ 1`, and `C (1+D)(L₁ Y) log(3Θ₀(2 + L₁ Y)) ≤ m₀`. -/
theorem akhcCL5_thr_props (d : ℕ) {C KPsi pPsi pPsiS L1 L2 D gamma beta H KPsiS Θ0 : ℝ}
    {m m0 : ℕ} (hC : 2 ≤ C) (hK : 1 ≤ KPsi) (hpPsi : (d : ℝ) + 1 ≤ pPsi) (hpS : 3 ≤ pPsiS)
    (hL1 : 1 ≤ L1) (hL2 : 1 ≤ L2) (hD : 0 ≤ D) (hg0 : 0 ≤ gamma) (hg : gamma ≤ 1 / 2)
    (hb0 : 0 ≤ beta) (hb : beta ≤ 1 / 2) (hH : 1 ≤ H) (hKS : 1 ≤ KPsiS) (hΘ0 : 1 ≤ Θ0)
    (hthr : akhcCL5_thr d C KPsi pPsi pPsiS L1 L2 D gamma beta H KPsiS m m0 Θ0 ≤ (m0 : ℝ)) :
    C * (L1 * Real.log (2 * L2) + D + Real.log (H + KPsiS)) + Real.log ((m : ℝ) + (m0 : ℝ) + 1) ≤
        Real.log (akhcCL5_thrX d C KPsi pPsi pPsiS L1 L2 D gamma H KPsiS m m0 Θ0) ∧
      1 ≤ Real.log (akhcCL5_thrX d C KPsi pPsi pPsiS L1 L2 D gamma H KPsiS m m0 Θ0) ∧
      C * (1 + D) * (L1 * Real.log (akhcCL5_thrX d C KPsi pPsi pPsiS L1 L2 D gamma H KPsiS m m0 Θ0)) *
          Real.log (3 * Θ0 * (2 + L1 *
            Real.log (akhcCL5_thrX d C KPsi pPsi pPsiS L1 L2 D gamma H KPsiS m m0 Θ0))) ≤
        (m0 : ℝ) := by
  have hC0 : 0 < C := by linarith only [hC]
  have hmin1 : min ((d : ℝ) + 1) pPsi - (d : ℝ) = 1 := by rw [min_eq_left hpPsi]; ring
  have hmin2 : min 3 pPsiS - 2 = 1 := by rw [min_eq_left hpS]; norm_num
  have h1g : 0 < 1 - gamma := by linarith only [hg]
  have h1g1 : 1 - gamma ≤ 1 := by linarith only [hg0]
  have hl2L2 : 0 ≤ Real.log (2 * L2) := Real.log_nonneg (by linarith only [hL2])
  have hlHK : 0 ≤ Real.log (H + KPsiS) := Real.log_nonneg (by linarith only [hH, hKS])
  set q := (L1 + D / (1 - gamma)) * Real.log (2 * L2) + (D + Real.log (H + KPsiS)) / (1 - gamma)
    with hq
  set q0 := L1 * Real.log (2 * L2) + D + Real.log (H + KPsiS) with hq0
  have hqq : q0 ≤ q := by
    have h1 : L1 * Real.log (2 * L2) ≤ (L1 + D / (1 - gamma)) * Real.log (2 * L2) :=
      mul_le_mul_of_nonneg_right (by have := div_nonneg hD h1g.le; linarith only [this]) hl2L2
    have h2 : D + Real.log (H + KPsiS) ≤ (D + Real.log (H + KPsiS)) / (1 - gamma) := by
      rw [le_div_iff₀ h1g]
      have := mul_le_mul_of_nonneg_left h1g1 (by positivity : 0 ≤ D + Real.log (H + KPsiS))
      linarith only [this]
    rw [hq, hq0]
    linarith only [h1, h2]
  set Υ1 := C * KPsi ^ (6 * (d + 1) ^ 2) / (min ((d : ℝ) + 1) pPsi - (d : ℝ)) with hΥ1
  set Υ2 := C / (min 3 pPsiS - 2) * Real.exp (C * q) with hΥ2
  have hΥ10 : 0 ≤ Υ1 := by
    rw [hΥ1, hmin1, div_one]
    have : 0 ≤ KPsi ^ (6 * (d + 1) ^ 2) := pow_nonneg (by linarith only [hK]) _
    positivity
  have hΥ2eq : Υ2 = C * Real.exp (C * q) := by rw [hΥ2, hmin2, div_one]
  have hΥ20 : 0 < Υ2 := by rw [hΥ2eq]; positivity
  have hmm : (1 : ℝ) ≤ (m : ℝ) + (m0 : ℝ) + 1 := by
    have h1 := Nat.cast_nonneg (α := ℝ) m
    have h2 := Nat.cast_nonneg (α := ℝ) m0
    linarith only [h1, h2]
  have hXeq : akhcCL5_thrX d C KPsi pPsi pPsiS L1 L2 D gamma H KPsiS m m0 Θ0 =
      (Υ1 + Υ2) * ((m : ℝ) + (m0 : ℝ) + 1) * Θ0 := rfl
  have hY : C * q0 + Real.log ((m : ℝ) + (m0 : ℝ) + 1) ≤
      Real.log (akhcCL5_thrX d C KPsi pPsi pPsiS L1 L2 D gamma H KPsiS m m0 Θ0) := by
    rw [hXeq, Real.log_mul (by positivity) (by linarith only [hΘ0]),
      Real.log_mul (by positivity) (by linarith only [hmm])]
    have h1 : Real.log Υ2 ≤ Real.log (Υ1 + Υ2) :=
      Real.log_le_log hΥ20 (by linarith only [hΥ10])
    have h2 : Real.log Υ2 = Real.log C + C * q := by
      rw [hΥ2eq, Real.log_mul hC0.ne' (Real.exp_pos _).ne', Real.log_exp]
    have h3 : 0 ≤ Real.log C := Real.log_nonneg (by linarith only [hC])
    have h4 : 0 ≤ Real.log Θ0 := Real.log_nonneg hΘ0
    have h5 := mul_le_mul_of_nonneg_left hqq hC0.le
    linarith only [h1, h2, h3, h4, h5]
  set Y := Real.log (akhcCL5_thrX d C KPsi pPsi pPsiS L1 L2 D gamma H KPsiS m m0 Θ0) with hYdef
  have hlogm : 0 ≤ Real.log ((m : ℝ) + (m0 : ℝ) + 1) := Real.log_nonneg hmm
  have hY1 : 1 ≤ Y := by
    have h2 := Real.log_two_gt_d9
    have hl2 : Real.log 2 ≤ Real.log (2 * L2) :=
      Real.log_le_log (by norm_num) (by linarith only [hL2])
    have h3 : 2 * Real.log 2 ≤ C * q0 := by
      have h4 : Real.log 2 ≤ q0 := by
        have := mul_le_mul_of_nonneg_right hL1 hl2L2
        rw [hq0]
        linarith only [this, hl2, hD, hlHK]
      have h5 := mul_le_mul hC h4 (by linarith only [h2]) hC0.le
      linarith only [h5]
    linarith only [hY, h3, h2, hlogm]
  refine ⟨hY, hY1, ?_⟩
  -- the threshold's lower bound
  have hW0 : 0 ≤ Real.log (3 * Θ0 * (2 + L1 * Y)) := by
    apply Real.log_nonneg
    have : 0 ≤ L1 * Y := by positivity
    nlinarith only [hΘ0, this]
  have hfac : L1 * (1 + D) ≤ (L1 + (1 + D) / (1 - gamma)) * ((1 + D) / ((1 - beta) * (1 - gamma))) := by
    have h1 : L1 ≤ L1 + (1 + D) / (1 - gamma) := by
      have := div_nonneg (by linarith only [hD] : (0 : ℝ) ≤ 1 + D) h1g.le
      linarith only [this]
    have h2 : 1 + D ≤ (1 + D) / ((1 - beta) * (1 - gamma)) := by
      have hb1 : 0 < 1 - beta := by linarith only [hb]
      have hb2 : (1 - beta) * (1 - gamma) ≤ 1 := by nlinarith only [hb0, hg0, hb1, h1g]
      rw [le_div_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left hb2 (by linarith only [hD] : (0 : ℝ) ≤ 1 + D)
      linarith only [this]
    exact mul_le_mul h1 h2 (by linarith only [hD]) (by linarith only [h1, hL1])
  have hthr' : akhcCL5_thr d C KPsi pPsi pPsiS L1 L2 D gamma beta H KPsiS m m0 Θ0 =
      (C * Y * Real.log (3 * Θ0 * (2 + L1 * Y))) *
        ((L1 + (1 + D) / (1 - gamma)) * ((1 + D) / ((1 - beta) * (1 - gamma)))) := by
    unfold akhcCL5_thr
    rw [← hYdef]
    ring
  have hCYW : 0 ≤ C * Y * Real.log (3 * Θ0 * (2 + L1 * Y)) := by positivity
  have := mul_le_mul_of_nonneg_left hfac hCYW
  have he : C * (1 + D) * (L1 * Y) * Real.log (3 * Θ0 * (2 + L1 * Y)) =
      C * Y * Real.log (3 * Θ0 * (2 + L1 * Y)) * (L1 * (1 + D)) := by ring
  rw [he]
  linarith only [this, hthr, hthr']

section FromYd

variable {d : ℕ} [NeZero d] {L1 L2 D H KPsiS C Y : ℝ} {m m0 : ℕ}

/-- `Lsum ≤ c₁ (1+D) L₁ Y`. -/
theorem akhcCL5_Lsum_le (hd : 2 ≤ d) (hL1 : 1 ≤ L1) (hL2 : 1 ≤ L2) (hD : 0 ≤ D) (hH : 1 ≤ H)
    (hKS : 1 ≤ KPsiS) (hC : 1 ≤ C) (hm0 : 1 ≤ m0)
    (hY : C * (L1 * Real.log (2 * L2) + D + Real.log (H + KPsiS)) +
      Real.log ((m : ℝ) + (m0 : ℝ) + 1) ≤ Y) (hY1 : 1 ≤ Y) :
    akhcCL5_Lsum d D H KPsiS (akhcCL5_M d L1 L2 m m0) (akhcCL5_K0 L1 L2 m m0) ≤
      akhcCL5_c1 d * ((1 + D) * (L1 * Y)) := by
  have hM := akhcCL5_M_le (d := d) hL1 hL2 hD hH hKS hC hm0 hY hY1
  have hK0 := akhcCL5_logK0_le hL1 hL2 hD hH hKS hC hm0 hY hY1
  have hV : 1 ≤ L1 * Y := by nlinarith only [hL1, hY1]
  have hYL : Y ≤ L1 * Y := by
    have := mul_le_mul_of_nonneg_right hL1 (by linarith only [hY1] : (0 : ℝ) ≤ Y)
    linarith only [this]
  set V := L1 * Y with hVdef
  set M := akhcCL5_M d L1 L2 m m0 with hMdef
  have hζ := akhcCL5_zeta_pos d
  have hε := akhcCL5_eps_pos d
  have hB := akhcCL5_B_nonneg d
  have hr := akhcCL5_r_pos d
  have hκ := akhcCL5_kappa_le_small d hd
  have hκ0 := (akhcCL5_kappa_pos d).le
  -- the logarithm of `(6B+1)/T`
  have hlogr : Real.log (akhcCL5_r d) = -akhcCL5_kappa d * Real.log 3 := by
    unfold akhcCL5_r akhcDW_r
    rw [Real.log_rpow (by norm_num)]
    rfl
  have hlogT : Real.log ((6 * akhcCL5_B d + 1) / akhcCL5_T d M) =
      Real.log ((6 * akhcCL5_B d + 1) / (akhcCL5_zeta d * akhcCL5_eps d)) +
        akhcCL5_kappa d * (M : ℝ) * Real.log 3 := by
    unfold akhcCL5_T
    rw [← div_div, Real.log_div (by positivity) (by positivity), Real.log_pow, hlogr]
    ring
  have hl3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith only [this]
  have hl30 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hM0 := Nat.cast_nonneg (α := ℝ) M
  have hκM : akhcCL5_kappa d * (M : ℝ) * Real.log 3 ≤ (M : ℝ) := by
    have h1 : akhcCL5_kappa d * Real.log 3 ≤ 1 := by nlinarith only [hκ, hκ0, hl3, hl30]
    have := mul_le_mul_of_nonneg_right h1 hM0
    linarith only [this]
  -- the logarithms of `K_{Ψ_S}` and `H`
  have hlHK : Real.log (H + KPsiS) ≤ Y := by
    have hl2L2 : 0 ≤ Real.log (2 * L2) := Real.log_nonneg (by linarith only [hL2])
    have hlHK0 : 0 ≤ Real.log (H + KPsiS) := Real.log_nonneg (by linarith only [hH, hKS])
    have hq0 : 0 ≤ L1 * Real.log (2 * L2) + D + Real.log (H + KPsiS) := by positivity
    have hCq := mul_le_mul_of_nonneg_right hC hq0
    have hlogm : 0 ≤ Real.log ((m : ℝ) + (m0 : ℝ) + 1) := Real.log_nonneg (by
      have h1 := Nat.cast_nonneg (α := ℝ) m
      have h2 := Nat.cast_nonneg (α := ℝ) m0
      linarith only [h1, h2])
    have := mul_nonneg (by linarith only [hL1] : (0 : ℝ) ≤ L1) hl2L2
    linarith only [hCq, hY, hlogm, hD, this]
  have hKS' : Real.log KPsiS ≤ Real.log (H + KPsiS) :=
    Real.log_le_log (by linarith only [hKS]) (by linarith only [hH])
  have hH' : Real.log H ≤ Real.log (H + KPsiS) :=
    Real.log_le_log (by linarith only [hH]) (by linarith only [hKS])
  have hDK : 2 * D * Real.log (akhcCL5_K0 L1 L2 m m0 : ℝ) ≤ 14 * (D * V) := by
    have := mul_le_mul_of_nonneg_left hK0 (by linarith only [hD] : (0 : ℝ) ≤ 2 * D)
    linarith only [this]
  -- assembling
  set c := |Real.log ((6 * akhcCL5_B d + 1) / (akhcCL5_zeta d * akhcCL5_eps d))| with hcdef
  have hc0 : 0 ≤ c := abs_nonneg _
  have hcle : Real.log ((6 * akhcCL5_B d + 1) / (akhcCL5_zeta d * akhcCL5_eps d)) ≤ c :=
    le_abs_self _
  have hMd := Nat.cast_nonneg (α := ℝ) (akhcCL5_Md d)
  have hDV : 0 ≤ D * V := by positivity
  have hcV : c ≤ c * V := by
    have := mul_le_mul_of_nonneg_left hV hc0
    linarith only [this]
  have hX : 0 ≤ (c + (akhcCL5_Md d : ℝ)) * (D * V) := by positivity
  have hc1 : akhcCL5_c1 d * ((1 + D) * V) =
      c * V + (akhcCL5_Md d : ℝ) * V + 58 * V + (c + (akhcCL5_Md d : ℝ)) * (D * V) +
        58 * (D * V) := by
    unfold akhcCL5_c1
    rw [← hcdef]
    ring
  have hMV : ((akhcCL5_Md d : ℝ) + 20) * V = (akhcCL5_Md d : ℝ) * V + 20 * V := by ring
  unfold akhcCL5_Lsum
  rw [hlogT, hc1]
  linarith only [hcle, hκM, hM, hMV, hlHK, hKS', hH', hDK, hYL, hcV, hX, hDV]

/-- `E ≤ 96(d+1) c₁ (1+D) L₁ Y + 1`. -/
theorem akhcCL5_E_le (hd : 2 ≤ d) (hL1 : 1 ≤ L1) (hL2 : 1 ≤ L2) (hD : 0 ≤ D) (hH : 1 ≤ H)
    (hKS : 1 ≤ KPsiS) (hC : 1 ≤ C) (hm0 : 1 ≤ m0)
    (hY : C * (L1 * Real.log (2 * L2) + D + Real.log (H + KPsiS)) +
      Real.log ((m : ℝ) + (m0 : ℝ) + 1) ≤ Y) (hY1 : 1 ≤ Y) :
    (akhcCL5_E d L1 L2 D H KPsiS m m0 : ℝ) ≤
      96 * ((d : ℝ) + 1) * akhcCL5_c1 d * ((1 + D) * (L1 * Y)) + 1 := by
  have hL := akhcCL5_Lsum_le hd hL1 hL2 hD hH hKS hC hm0 hY hY1
  have hV : 0 ≤ (1 + D) * (L1 * Y) := by
    have : 0 ≤ L1 * Y := by nlinarith only [hL1, hY1]
    positivity
  have hc1 := akhcCL5_c1_nonneg d
  have hl3 := akhcCL5_log3_ge
  have hl30 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set Q := akhcCL5_c1 d * ((1 + D) * (L1 * Y)) with hQ
  have hQ0 : 0 ≤ Q := mul_nonneg hc1 hV
  have hcoef : 48 * ((d : ℝ) + 1) / Real.log 3 ≤ 96 * ((d : ℝ) + 1) := by
    rw [div_le_iff₀ hl30]
    have hd0 : (0 : ℝ) ≤ (d : ℝ) + 1 := by positivity
    nlinarith only [hl3, hd0]
  have hcoef0 : 0 ≤ 48 * ((d : ℝ) + 1) / Real.log 3 := by positivity
  have h1 : 48 * ((d : ℝ) + 1) / Real.log 3 *
      akhcCL5_Lsum d D H KPsiS (akhcCL5_M d L1 L2 m m0) (akhcCL5_K0 L1 L2 m m0) ≤
      48 * ((d : ℝ) + 1) / Real.log 3 * Q := mul_le_mul_of_nonneg_left hL hcoef0
  have h2 : (akhcCL5_E d L1 L2 D H KPsiS m m0 : ℝ) < 48 * ((d : ℝ) + 1) / Real.log 3 * Q + 1 := by
    have h3 : akhcCL5_E d L1 L2 D H KPsiS m m0 ≤ ⌈48 * ((d : ℝ) + 1) / Real.log 3 * Q⌉₊ :=
      Nat.ceil_mono h1
    have h4 := Nat.ceil_lt_add_one (mul_nonneg hcoef0 hQ0)
    have h5 : (akhcCL5_E d L1 L2 D H KPsiS m m0 : ℝ) ≤
        (⌈48 * ((d : ℝ) + 1) / Real.log 3 * Q⌉₊ : ℝ) := by exact_mod_cast h3
    linarith only [h4, h5]
  have h6 := mul_le_mul_of_nonneg_right hcoef hQ0
  have h7 : 96 * ((d : ℝ) + 1) * Q = 96 * ((d : ℝ) + 1) * akhcCL5_c1 d * ((1 + D) * (L1 * Y)) := by
    rw [hQ]; ring
  linarith only [h2, h6, h7]

end FromYd

/-- `W := log(3Θ₀(2 + V)) ≥ 1` and `W ≥ log V`, for `Θ₀ ≥ 1`, `V ≥ 1`. -/
theorem akhcCL5_W_props {Θ0 V : ℝ} (hΘ0 : 1 ≤ Θ0) (hV : 1 ≤ V) :
    1 ≤ Real.log (3 * Θ0 * (2 + V)) ∧ Real.log V ≤ Real.log (3 * Θ0 * (2 + V)) := by
  have hl3 := akhcCL5_log3_ge
  have h9 : (9 : ℝ) ≤ 3 * Θ0 * (2 + V) := by nlinarith only [hΘ0, hV]
  refine ⟨?_, Real.log_le_log (by linarith only [hV]) (by nlinarith only [hΘ0, hV])⟩
  have h1 := Real.log_le_log (by norm_num) h9
  have h2 : Real.log (9 : ℝ) = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
    norm_num
  linarith only [h1, h2, hl3]

section FromYK

variable {d : ℕ} [NeZero d] {L1 L2 D H KPsiS C Y : ℝ} {m m0 : ℕ}

/-- **The number of squaring blocks is logarithmic**: `K + 1 ≤ c₃ log(3Θ₀(2 + L₁ Y))`. -/
theorem akhcCL5_K_le (hd : 2 ≤ d) (hL1 : 1 ≤ L1) (hL2 : 1 ≤ L2) (hD : 0 ≤ D) (hH : 1 ≤ H)
    (hKS : 1 ≤ KPsiS) (hC : 1 ≤ C) (hm0 : 1 ≤ m0)
    (hY : C * (L1 * Real.log (2 * L2) + D + Real.log (H + KPsiS)) +
      Real.log ((m : ℝ) + (m0 : ℝ) + 1) ≤ Y) (hY1 : 1 ≤ Y) {Θ0 : ℝ} (hΘ0 : 1 ≤ Θ0) :
    (akhcDW_K (akhcCL5_theta d) (akhcCL5_B d) (akhcCL5_w d) (akhcCL5_Lstep d)
        (akhcCL5_M d L1 L2 m m0) : ℝ) + 1 ≤
      akhcCL5_c3 d * Real.log (3 * Θ0 * (2 + L1 * Y)) := by
  have hM := akhcCL5_M_le (d := d) hL1 hL2 hD hH hKS hC hm0 hY hY1
  have hV : 1 ≤ L1 * Y := by nlinarith only [hL1, hY1]
  obtain ⟨hW1, hWV⟩ := akhcCL5_W_props hΘ0 hV
  set V := L1 * Y with hVdef
  set W := Real.log (3 * Θ0 * (2 + V)) with hWdef
  set M := akhcCL5_M d L1 L2 m m0 with hMdef
  have hκ := akhcCL5_kappa_le_small d hd
  have hκ0 := (akhcCL5_kappa_pos d).le
  have hM0 := Nat.cast_nonneg (α := ℝ) M
  have hMd := Nat.cast_nonneg (α := ℝ) (akhcCL5_Md d)
  set N := ⌈2 * akhcCL5_kappa d * (M : ℝ)⌉₊ with hNdef
  have hN : (N : ℝ) ≤ ((akhcCL5_Md d : ℝ) + 21) * V := by
    have h1 := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 2 * akhcCL5_kappa d * (M : ℝ))
    have h2 : 2 * akhcCL5_kappa d * (M : ℝ) ≤ (M : ℝ) := by nlinarith only [hκ, hκ0, hM0]
    have h3 : ((akhcCL5_Md d : ℝ) + 21) * V = ((akhcCL5_Md d : ℝ) + 20) * V + V := by ring
    linarith only [h1, h2, hM, h3, hV]
  have hl21 : 0 ≤ Real.log ((akhcCL5_Md d : ℝ) + 21) := Real.log_nonneg (by linarith only [hMd])
  have hlV : 0 ≤ Real.log V := Real.log_nonneg hV
  have hlog : (Nat.log 2 N : ℝ) ≤ 2 * (Real.log ((akhcCL5_Md d : ℝ) + 21) + Real.log V) := by
    by_cases hN0 : N = 0
    · rw [hN0, Nat.log_zero_right, Nat.cast_zero]
      linarith only [hl21, hlV]
    · have h1 := Nat.pow_log_le_self 2 hN0
      have h2 : (2 : ℝ) ^ (Nat.log 2 N) ≤ (N : ℝ) := by exact_mod_cast h1
      have h3 := Real.log_le_log (by positivity) (h2.trans hN)
      rw [Real.log_pow, Real.log_mul (by linarith only [hMd]) (by linarith only [hV])] at h3
      have h4 := Real.log_two_gt_d9
      have h5 : (Nat.log 2 N : ℝ) * (1 / 2) ≤ (Nat.log 2 N : ℝ) * Real.log 2 :=
        mul_le_mul_of_nonneg_left (by linarith only [h4]) (Nat.cast_nonneg _)
      linarith only [h3, h5]
  have hK : (akhcDW_K (akhcCL5_theta d) (akhcCL5_B d) (akhcCL5_w d) (akhcCL5_Lstep d) M : ℝ) =
      (Nat.log 2 N : ℝ) + 1 := by
    unfold akhcDW_K
    push_cast
    rfl
  have hc3 : akhcCL5_c3 d * W = 2 * Real.log ((akhcCL5_Md d : ℝ) + 21) * W + 4 * W := by
    unfold akhcCL5_c3
    ring
  have h6 : Real.log ((akhcCL5_Md d : ℝ) + 21) ≤ Real.log ((akhcCL5_Md d : ℝ) + 21) * W := by
    have := mul_le_mul_of_nonneg_left hW1 hl21
    linarith only [this]
  rw [hK, hc3]
  linarith only [hlog, h6, hWV, hW1]

/-- **`N₀ ≤ m + 4m₀`** from `C ≥ 4 + c₂c₃` and `C (1+D)(L₁ Y) log(3Θ₀(2 + L₁ Y)) ≤ m₀`. -/
theorem akhcCL5_N0_le (hd : 2 ≤ d) (hL1 : 1 ≤ L1) (hL2 : 1 ≤ L2) (hD : 0 ≤ D) (hH : 1 ≤ H)
    (hKS : 1 ≤ KPsiS) (hC : 1 ≤ C)
    (hY : C * (L1 * Real.log (2 * L2) + D + Real.log (H + KPsiS)) +
      Real.log ((m : ℝ) + (m0 : ℝ) + 1) ≤ Y) (hY1 : 1 ≤ Y) {Θ0 : ℝ} (hΘ0 : 1 ≤ Θ0)
    (hCbig : 4 + akhcCL5_c2 d * akhcCL5_c3 d ≤ C)
    (hm0 : C * (1 + D) * (L1 * Y) * Real.log (3 * Θ0 * (2 + L1 * Y)) ≤ (m0 : ℝ)) :
    akhcCL5_N0 d L1 L2 D H KPsiS m m0 ≤ m + 4 * m0 := by
  have hV : 1 ≤ L1 * Y := by nlinarith only [hL1, hY1]
  obtain ⟨hW1, -⟩ := akhcCL5_W_props hΘ0 hV
  set V := L1 * Y with hVdef
  set W := Real.log (3 * Θ0 * (2 + V)) with hWdef
  have hP : 1 ≤ (1 + D) * V := one_le_mul_of_one_le_of_one_le (by linarith only [hD]) hV
  set P := (1 + D) * V with hPdef
  have hCPW : C * (1 + D) * V * W = C * (P * W) := by rw [hPdef]; ring
  have hPW : 1 ≤ P * W := one_le_mul_of_one_le_of_one_le hP hW1
  have hm01 : 1 ≤ m0 := by
    have h1 : 1 ≤ C * (P * W) := one_le_mul_of_one_le_of_one_le hC hPW
    have h2 : (1 : ℝ) ≤ (m0 : ℝ) := by linarith only [h1, hm0, hCPW]
    exact_mod_cast h2
  have hlb := akhcCL5_lbar_le hL1 hL2 hD hH hKS hC hm01 hY hY1
  have hM := akhcCL5_M_le (d := d) hL1 hL2 hD hH hKS hC hm01 hY hY1
  have hE := akhcCL5_E_le hd hL1 hL2 hD hH hKS hC hm01 hY hY1
  have hK := akhcCL5_K_le hd hL1 hL2 hD hH hKS hC hm01 hY hY1 hΘ0
  rw [← hVdef, ← hWdef] at hK
  rw [← hVdef] at hlb hM hE
  rw [← hPdef] at hE
  set lb := akhcCL5_lbar L1 L2 m m0 with hlbdef
  set M := akhcCL5_M d L1 L2 m m0 with hMdef
  set E := akhcCL5_E d L1 L2 D H KPsiS m m0 with hEdef
  set J := akhcDW_J (akhcCL5_theta d) (akhcCL5_B d) (akhcCL5_w d) (akhcCL5_Lstep d) with hJdef
  set Z2 := akhcDW_Z2 (akhcCL5_theta d) (akhcCL5_B d) (akhcCL5_B d) (akhcCL5_w d) with hZ2def
  set K := akhcDW_K (akhcCL5_theta d) (akhcCL5_B d) (akhcCL5_w d) (akhcCL5_Lstep d) M with hKdef
  set Zb := akhcDW_Zb (akhcCL5_theta d) (akhcCL5_B d) (akhcCL5_B d) (akhcCL5_w d)
    (akhcCL5_Lstep d) (akhcCL5_ell d L1 L2 D H KPsiS m m0) M with hZbdef
  have hZbeq : Zb = 2 * lb + 4 + E + J + M + Z2 := by
    rw [hZbdef, akhcDW_Zb, akhcCL5_ell]
  have hN0eq : akhcCL5_N0 d L1 L2 D H KPsiS m m0 = m + 3 * m0 + lb + K * (Zb + M) + Zb := rfl
  -- `Z + M ≤ c₂ P`
  have hJ0 := Nat.cast_nonneg (α := ℝ) J
  have hZ20 := Nat.cast_nonneg (α := ℝ) Z2
  have hMd := Nat.cast_nonneg (α := ℝ) (akhcCL5_Md d)
  have hJP : (J : ℝ) ≤ (J : ℝ) * P := by
    have := mul_le_mul_of_nonneg_left hP hJ0
    linarith only [this]
  have hZ2P : (Z2 : ℝ) ≤ (Z2 : ℝ) * P := by
    have := mul_le_mul_of_nonneg_left hP hZ20
    linarith only [this]
  have hVP : V ≤ P := by
    have := mul_le_mul_of_nonneg_right (by linarith only [hD] : (1 : ℝ) ≤ 1 + D)
      (by linarith only [hV] : (0 : ℝ) ≤ V)
    rw [hPdef]
    linarith only [this]
  have hMdVP : ((akhcCL5_Md d : ℝ) + 20) * V ≤ ((akhcCL5_Md d : ℝ) + 20) * P :=
    mul_le_mul_of_nonneg_left hVP (by linarith only [hMd])
  have hc2 : akhcCL5_c2 d * P = 13 * P + (J : ℝ) * P + (Z2 : ℝ) * P +
      96 * ((d : ℝ) + 1) * akhcCL5_c1 d * P + 2 * (((akhcCL5_Md d : ℝ) + 20) * P) := by
    unfold akhcCL5_c2
    rw [← hJdef, ← hZ2def]
    ring
  have hZM : ((Zb + M : ℕ) : ℝ) ≤ akhcCL5_c2 d * P := by
    rw [hZbeq, hc2]
    push_cast
    linarith only [hlb, hE, hJP, hZ2P, hVP, hP, hM, hMdVP]
  -- the total
  have hc3 := akhcCL5_c3_nonneg d
  have hc20 := akhcCL5_c2_nonneg d
  have hKZ : ((K : ℝ) + 1) * ((Zb + M : ℕ) : ℝ) ≤ (akhcCL5_c3 d * W) * (akhcCL5_c2 d * P) :=
    mul_le_mul hK hZM (Nat.cast_nonneg _) (by positivity)
  have hP0 : 0 ≤ P := by linarith only [hP]
  have hlbPW : (lb : ℝ) ≤ 4 * (P * W) := by
    have := mul_le_mul_of_nonneg_left hW1 hP0
    linarith only [hlb, hVP, this]
  have hC4 := mul_le_mul_of_nonneg_right hCbig (by linarith only [hPW] : (0 : ℝ) ≤ P * W)
  have hreal : ((lb + K * (Zb + M) + Zb : ℕ) : ℝ) ≤ (m0 : ℝ) := by
    have he1 : ((lb + K * (Zb + M) + Zb : ℕ) : ℝ) + (M : ℝ) =
        (lb : ℝ) + ((K : ℝ) + 1) * ((Zb + M : ℕ) : ℝ) := by push_cast; ring
    have he2 : (akhcCL5_c3 d * W) * (akhcCL5_c2 d * P) =
        akhcCL5_c2 d * akhcCL5_c3 d * (P * W) := by ring
    have hM0 := Nat.cast_nonneg (α := ℝ) M
    linarith only [he1, he2, hKZ, hlbPW, hC4, hm0, hCPW, hM0]
  have hnat : lb + K * (Zb + M) + Zb ≤ m0 := by exact_mod_cast hreal
  rw [hN0eq]
  omega

end FromYK

/-! ## The closure on V5's range -/

section Final

variable {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
  (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
  (L : ℕ)
  (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
  (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
  (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
  (gamma H D : ℝ) (m2 : ℕ) (PsiS : ℝ → ℝ) (KPsiS pPsiS : ℝ)
  (hgamma0 : 0 ≤ gamma) (hgamma : gamma ≤ 1 / 2) (hH : 1 ≤ H) (hD : 0 ≤ D)
  (hPsiSMono : MonotoneOn PsiS (Set.Ici 0)) (hPsiSOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ PsiS t)
  (hKPsiS : 1 ≤ KPsiS) (hpPsiS : 3 ≤ pPsiS)
  (hGrowth : ∀ p : ℝ, 2 ≤ p → p ≤ pPsiS → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
    s ^ p ≤ KPsiS ^ (3 * ⌈p⌉₊ ^ 2) * (PsiS (t * s) / PsiS t))
  (hP2 : ∀ j : ℕ, m2 ≤ j →
    ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ, Measurable X ∧
      Homogenization.IndependentSums.IsBigO P.toMeasure PsiS X (H * (j : ℝ) ^ D) ∧
      ∀ (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
        (Q : Homogenization.TriadicCube d),
        Q.scale ≤ (j : ℤ) →
        Homogenization.cubeCenter Q ∈
            Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)) →
          Homogenization.BlockMatLoewnerLE
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q)
              (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField)
            ((1 + (3 : ℝ) ^ (-(gamma * ((Q.scale : ℝ) - (j : ℝ)))) * X omega) •
              SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                (Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)))))
  (beta L1 L2 : ℝ) (m3 : ℕ) (omegaSeq : ℕ → ℝ) (Psi : ℝ → ℝ) (KPsi pPsi : ℝ)
  (hbeta0 : 0 ≤ beta) (hbeta : beta ≤ 1 / 2) (hL1 : 1 ≤ L1) (hL2 : 1 ≤ L2)
  (homega : ∀ k : ℕ, 0 < omegaSeq k) (homegaAnti : Antitone omegaSeq)
  (hPsiOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ Psi t) (hKPsi : 1 ≤ KPsi) (hpPsi : (d : ℝ) + 1 ≤ pPsi)
  (hGrowthPsi : ∀ p : ℝ, 1 < p → p ≤ pPsi → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
    s ^ p ≤ KPsi ^ (3 * ⌈p⌉₊ ^ 2) * (Psi (t * s) / Psi t))
  (hP3 : ∀ j n : ℕ, m3 ≤ n → beta * (j : ℝ) < (n : ℝ) →
    (n : ℝ) < (j : ℝ) - L1 * Real.log (L2 * (n : ℝ)) →
    ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
      Measurable X ∧
      Homogenization.IndependentSums.IsBigO P.toMeasure Psi X (omegaSeq n) ∧
      ∀ (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
        (p q : Homogenization.BlockVec d),
        2 *
            (((Homogenization.descendantsAtDepth
                    (Homogenization.originCube d (j : ℤ)) (j - n)).card : ℝ)⁻¹ *
              ∑ R ∈ Homogenization.descendantsAtDepth
                  (Homogenization.originCube d (j : ℤ)) (j - n),
                Homogenization.blockVecDot p
                  (Homogenization.blockMatVecMul
                    (Homogenization.ofFullBlockMat
                      (Homogenization.toFullBlockMat
                          (Homogenization.coarseBlockMatrix
                            (Homogenization.cubeSet R)
                            (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                              nu omega L).toCoeffField) -
                        Homogenization.toFullBlockMat
                          (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix
                            nu L P
                            (Homogenization.cubeSet
                              (Homogenization.originCube d (n : ℤ))))))
                    q)) ≤
          X omega *
            (Homogenization.blockVecDot p
                (Homogenization.blockMatVecMul
                  (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                    (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ))))
                  p) +
              Homogenization.blockVecDot q
                (Homogenization.blockMatVecMul
                  (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                    (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ))))
                  q)))

include hnu hPrefix hJ2 hJ4 hgamma0 hgamma hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2
  hbeta0 hbeta hL1 hL2 homega homegaAnti hPsiOne hKPsi hpPsi hGrowthPsi hP3

/-- **Step 3 on V5's range (`akhcF1_core`'s `hStep3`).** Take V5's binders on its range
(`γ ≤ 1/2`, `β ≤ 1/2`, `d + 1 ≤ p_Ψ`, `3 ≤ p_{Ψ_S}`), Step 2's level `σ ≤ σ_d`, a constant
`C ≥ C_min(d)` with V5's `ω_m²` binder, and V5's `m₀` threshold. If `Θ_{m+3m₀} ≤ 1 + σ`, then
`Θ_n - 1 ≤ U ω_m² + 1 · 3^{-κ(d)(n-m-4m₀)}` for every `n ≥ m + 4m₀`, with `U = akhcCL5_U d K_Ψ`
and `κ(d) = akhcCL5_kappa d`. -/
theorem akhcStep3_decay (hd : 2 ≤ d) {m m0 : ℕ} (hm : max m2 m3 ≤ m) {sigma : ℝ}
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ akhcCL5_sigma d) {C : ℝ} (hC : akhcCL5_Cmin d ≤ C)
    (hOmega : omegaSeq m ^ 2 ≤
      (C * KPsi ^ (6 * (d + 1) ^ 2) / (min ((d : ℝ) + 1) pPsi - (d : ℝ)))⁻¹)
    (hm0 : C * (L1 + (1 + D) / (1 - gamma)) * (1 + D) / ((1 - beta) * (1 - gamma)) *
        Real.log
          ((C * KPsi ^ (6 * (d + 1) ^ 2) / (min ((d : ℝ) + 1) pPsi - (d : ℝ)) +
              C / (min 3 pPsiS - 2) *
                Real.exp (C * ((L1 + D / (1 - gamma)) * Real.log (2 * L2) +
                  (D + Real.log (H + KPsiS)) / (1 - gamma)))) *
            ((m : ℝ) + (m0 : ℝ) + 1) *
            SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P 0) *
        Real.log (3 * SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P 0 *
          (2 + L1 * Real.log
          ((C * KPsi ^ (6 * (d + 1) ^ 2) / (min ((d : ℝ) + 1) pPsi - (d : ℝ)) +
              C / (min 3 pPsiS - 2) *
                Real.exp (C * ((L1 + D / (1 - gamma)) * Real.log (2 * L2) +
                  (D + Real.log (H + KPsiS)) / (1 - gamma)))) *
            ((m : ℝ) + (m0 : ℝ) + 1) *
            SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P 0))) ≤
      (m0 : ℝ)) :
    SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P (m + 3 * m0) ≤ 1 + sigma →
      ∀ n : ℕ, m + 4 * m0 ≤ n →
        SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P n - 1 ≤
          akhcCL5_U d KPsi * omegaSeq m ^ 2 +
            1 * (3 : ℝ) ^ (-(akhcCL5_kappa d * ((n : ℝ) - (m : ℝ) - 4 * (m0 : ℝ)))) := by
  have hC16 : 16 ≤ C := ((le_max_left _ _).trans (le_max_left _ _)).trans hC
  have hCL : (akhcCL5_Lstep d : ℝ) ≤ C := ((le_max_right _ _).trans (le_max_left _ _)).trans hC
  have hCU : 2 * akhcCL5_B d * akhcCL5_cUps d / (akhcCL5_zeta d * akhcCL5_eps d) ≤ C :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hC
  have hCc : 4 + akhcCL5_c2 d * akhcCL5_c3 d ≤ C :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hC
  have hgamma1 : gamma < 1 := by linarith only [hgamma]
  have hpPsiS2 : 2 < pPsiS := by linarith only [hpPsiS]
  have hΘ0 := SuperdiffusionCLT.AKHC61.Carrier.akhc_one_le_thetaCutoff_of_P2 hnu hJ4
    gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS2
    hGrowth hP2 (L := L) 0
  obtain ⟨hY, hY1, hthr⟩ := akhcCL5_thr_props d (by linarith only [hC16]) hKPsi hpPsi hpPsiS hL1
    hL2 hD hgamma0 hgamma hbeta0 hbeta hH hKPsiS hΘ0 hm0
  set Θ0 := SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P 0 with hΘ0def
  set Y := Real.log (akhcCL5_thrX d C KPsi pPsi pPsiS L1 L2 D gamma H KPsiS m m0 Θ0) with hYdef
  have hV : 1 ≤ L1 * Y := one_le_mul_of_one_le_of_one_le hL1 hY1
  obtain ⟨hW1, -⟩ := akhcCL5_W_props hΘ0 hV
  set W := Real.log (3 * Θ0 * (2 + L1 * Y)) with hWdef
  -- `m₀ ≥ C·max{L₁, 1 + D}`
  have hVW : 1 ≤ L1 * Y * W := one_le_mul_of_one_le_of_one_le hV hW1
  have hYW : 1 ≤ Y * W := one_le_mul_of_one_le_of_one_le hY1 hW1
  have hbig1 : 1 + D ≤ (1 + D) * (L1 * Y) * W := by
    have := mul_le_mul_of_nonneg_left hVW (by linarith only [hD] : (0 : ℝ) ≤ 1 + D)
    linarith only [this]
  have hbig2 : L1 ≤ (1 + D) * (L1 * Y) * W := by
    have h1 := mul_le_mul_of_nonneg_left hYW (by linarith only [hL1] : (0 : ℝ) ≤ L1)
    have h2 : L1 * (Y * W) ≤ (1 + D) * (L1 * (Y * W)) :=
      le_mul_of_one_le_left (by positivity) (by linarith only [hD])
    have h3 : (1 + D) * (L1 * Y) * W = (1 + D) * (L1 * (Y * W)) := by ring
    linarith only [h1, h2, h3]
  have hCm : C * (1 + D) * (L1 * Y) * W = C * ((1 + D) * (L1 * Y) * W) := by ring
  have hC0 : 0 ≤ C := by linarith only [hC16]
  have hb1 := mul_le_mul_of_nonneg_left hbig1 hC0
  have hb2 := mul_le_mul_of_nonneg_left hbig2 hC0
  have hL1m0 : 2 * L1 ≤ (m0 : ℝ) := by
    have := mul_le_mul_of_nonneg_right hC16 (by linarith only [hL1] : (0 : ℝ) ≤ L1)
    linarith only [this, hb2, hCm, hthr, hL1]
  have hDm0 : 16 * D ≤ (m0 : ℝ) := by
    have := mul_le_mul_of_nonneg_right hC16 (by linarith only [hD] : (0 : ℝ) ≤ 1 + D)
    linarith only [this, hb1, hCm, hthr, hD]
  have hΛm0 : akhcCL5_Lstep d ≤ m0 := by
    have h1 : C ≤ C * (1 + D) := le_mul_of_one_le_right hC0 (by linarith only [hD])
    have h2 : (akhcCL5_Lstep d : ℝ) ≤ (m0 : ℝ) := by
      linarith only [hCL, h1, hb1, hCm, hthr]
    exact_mod_cast h2
  have hN0 := akhcCL5_N0_le hd hL1 hL2 hD hH hKPsiS (by linarith only [hC16]) hY hY1 hΘ0 hCc hthr
  have hS := akhcCL5_hS_of_omega d hd hKPsi hpPsi hCU (by linarith only [hC16]) hOmega
  exact akhcCL5_decay_of_scales hnu P L hPrefix hJ2 hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0
    hgamma hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 beta L1 L2 m3 omegaSeq Psi KPsi
    pPsi hbeta0 hbeta hL1 hL2 homega homegaAnti hPsiOne hKPsi hpPsi hGrowthPsi hP3 hd hm
    hsigma0.le hsigma hS hL1m0 hDm0 hΛm0 hN0

end Final

/-! ## Satisfiability of the closure's hypotheses -/

end

end SuperdiffusionCLT.AKHC61.Step3
