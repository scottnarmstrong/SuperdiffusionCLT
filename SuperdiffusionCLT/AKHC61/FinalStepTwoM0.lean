/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.FinalStepTwoInputs

/-!
# AK.HC Theorem 6.1 on the V5 range: Step 2's `m₀` requirement from V5's threshold

`akhcStep2_m0Req` (`Params/ConstantsProofNative.lean`) asks, with `L := L_req(m + 3m₀)` at `Y_d := δ_d σ_d²`,
for `⌈log(3Θ₀)⌉·N′(L) ≤ m₀` and `2L < (1-β)m₀`, where `N′(L) = 2L·N₁(d)`.

V5's threshold gives, with `Y := log X` (`akhcCL5_thr_props`),
`Y ≥ C(L₁ log(2L₂) + D + log(H + K_{Ψ_S})) + log(m + m₀ + 1)`, `Y ≥ 1`, and
`C(1+D)(L₁Y)·W ≤ m₀` with `W := log(3Θ₀(2 + L₁Y)) ≥ 1`. The affine bound of
`Params/M0ReqSat.lean` on `L_req` then gives `L ≤ c_L(d)·(1+D)L₁Y` (`akhcDim_Lreq_le`), with
`c_L(d) := 160 + (4d+7) log(1/Y_d)`. Since `⌈log(3Θ₀)⌉ ≤ W`, both requirements follow once
`C ≥ max{2 c_L N₁, 4 c_L + 1}` (`akhcDim_m0Req`).
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61

open SuperdiffusionCLT.AKHC61.Params
open SuperdiffusionCLT.AKHC61.ParamsProofNative
open SuperdiffusionCLT.AKHC61.Step3

noncomputable section

/-- `log(1/Y_d)`, `Y_d := δ_d σ_d²`. -/
def akhcDim_ell (d : ℕ) [NeZero d] : ℝ := Real.log (1 / (akhcDim_delta d * akhcCL5_sigma d ^ 2))

/-- `c_L(d) := 160 + (4d+7) log(1/Y_d)`: `L_req ≤ c_L(d)·(1+D)L₁Y`. -/
def akhcDim_cL (d : ℕ) [NeZero d] : ℝ := 160 + (4 * (d : ℝ) + 7) * akhcDim_ell d

/-- `N₁(d) := ⌈2/(σ_d² δ_d)·|log(σ_d/4)|⌉`, so that `N′(L) = 2L·N₁(d)`. -/
def akhcDim_N1 (d : ℕ) [NeZero d] : ℕ :=
  ⌈2 / (akhcCL5_sigma d ^ 2 * akhcDim_delta d) * |Real.log (akhcCL5_sigma d / 4)|⌉₊

theorem akhcDim_ell_nonneg (d : ℕ) [NeZero d] : 0 ≤ akhcDim_ell d := by
  obtain ⟨h0, h1⟩ := akhcDim_Yd_props d
  unfold akhcDim_ell
  apply Real.log_nonneg
  rw [le_div_iff₀ h0]
  linarith only [h1]

theorem akhcDim_cL_nonneg (d : ℕ) [NeZero d] : 0 ≤ akhcDim_cL d := by
  have := akhcDim_ell_nonneg d
  unfold akhcDim_cL
  positivity

/-- `1 ≤ log 3`. -/
theorem akhcDim_one_le_log3 : (1 : ℝ) ≤ Real.log 3 := by
  have hexp : Real.exp 1 ≤ 3 := Real.exp_one_lt_d9.le.trans (by norm_num)
  have := Real.log_le_log (Real.exp_pos 1) hexp
  rwa [Real.log_exp] at this

/-- **`L_req` is at most `c_L(d)·(1+D)L₁Y`** on V5's range, when
`Y ≥ C(L₁ log(2L₂) + D + log(H + K_{Ψ_S})) + log(m + m₀ + 1)`, `Y ≥ 1`, `C ≥ 1`, `m₀ ≥ 1`. -/
theorem akhcDim_Lreq_le {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    {gamma pPsi pPsiS L1 L2 H D KPsiS C Y : ℝ} {m m0 : ℕ}
    (hg0 : 0 ≤ gamma) (hg : gamma ≤ 1 / 2) (hpPsi : (d : ℝ) + 1 ≤ pPsi) (hpS : 3 ≤ pPsiS)
    (hL1 : 1 ≤ L1) (hL2 : 1 ≤ L2) (hH : 1 ≤ H) (hD : 0 ≤ D) (hKS : 1 ≤ KPsiS)
    (hC : 1 ≤ C) (hm0 : 1 ≤ m0)
    (hY : C * (L1 * Real.log (2 * L2) + D + Real.log (H + KPsiS)) +
      Real.log ((m : ℝ) + (m0 : ℝ) + 1) ≤ Y) (hY1 : 1 ≤ Y) :
    (akhcStep2_Lreq d gamma pPsi pPsiS L1 L2 H D KPsiS (akhcDim_delta d * akhcCL5_sigma d ^ 2)
        (m + 3 * m0) : ℝ) ≤ akhcDim_cL d * ((1 + D) * (L1 * Y)) := by
  obtain ⟨hYd0, hYd1⟩ := akhcDim_Yd_props d
  have hgamma1 : gamma < 1 := by linarith only [hg]
  have hpPsi' : (d : ℝ) < pPsi := by linarith only [hpPsi]
  have hpS' : 2 < pPsiS := by linarith only [hpS]
  have hK1 : 1 ≤ m + 3 * m0 := by omega
  have hL := akhcStep2Sat_Lreq_le hd hg0 hgamma1 hpPsi' hpS' hL1 hL2 hH hD hKS hYd0 hYd1
    (L1 := L1) (L2 := L2) (H := H) (D := D) (KPsiS := KPsiS) hK1
  set Yd := akhcDim_delta d * akhcCL5_sigma d ^ 2 with hYd
  have hℓ0 := akhcDim_ell_nonneg d
  have hℓ : akhcDim_ell d = Real.log (1 / Yd) := rfl
  have hlog3 := akhcDim_one_le_log3
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  -- `c₃ ≤ 3`
  have hc3_0 := (akhcStep2Sat_c3_pos hd hgamma1 hpPsi' hpS').le
  have hc3_le : akhcStep2Sat_c3 d gamma pPsi pPsiS ≤ 3 := by
    have hρ := akhcCL5_rho_ge d hd
    have hρg : (1 : ℝ) / 3 ≤ akhcCL5_rho d - gamma := by linarith only [hρ, hg]
    have hprod : (1 : ℝ) / 3 * 1 ≤ (akhcCL5_rho d - gamma) * Real.log 3 :=
      mul_le_mul hρg hlog3 (by norm_num) (by linarith only [hρg])
    unfold akhcStep2Sat_c3
    rw [akhcDim_rho_eq hd hg hpPsi hpS, div_le_iff₀ (by linarith only [hprod])]
    linarith only [hprod]
  -- the `hT1small` term
  have hT1 : akhcStep2Sat_T1val d gamma pPsi pPsiS Yd ≤ (4 * (d : ℝ) + 4) * akhcDim_ell d := by
    unfold akhcStep2Sat_T1val
    rw [akhcDim_one_sub_two_sPrime hd hg hpPsi hpS, ← hℓ]
    have hq : (0 : ℝ) < 1 / (4 * (d : ℝ) + 4) := by positivity
    have hden : 1 / (4 * (d : ℝ) + 4) ≤ 1 / (4 * (d : ℝ) + 4) * Real.log 3 :=
      le_mul_of_one_le_right hq.le hlog3
    calc akhcDim_ell d / (1 / (4 * (d : ℝ) + 4) * Real.log 3)
        ≤ akhcDim_ell d / (1 / (4 * (d : ℝ) + 4)) := div_le_div_of_nonneg_left hℓ0 hq hden
      _ = (4 * (d : ℝ) + 4) * akhcDim_ell d := by rw [one_div, div_inv_eq_mul]; ring
  -- the `(P2′)`-tail bracket
  set lHK := Real.log (H + KPsiS) with hlHK
  have hlHK0 : 0 ≤ lHK := Real.log_nonneg (by linarith only [hH, hKS])
  have hb0 := akhcStep2Sat_bracket0_nonneg hKS hH hpS' hYd0 hYd1
  have hb_le : akhcStep2Sat_bracket0 KPsiS H pPsiS Yd ≤ 5 + 38 * lHK + akhcDim_ell d := by
    have hmin : Real.log (min (3 : ℝ) pPsiS - 2) = 0 := by
      rw [min_eq_left hpS]; norm_num
    have hlogY : Real.log (1 / Yd) = -Real.log Yd := by rw [one_div, Real.log_inv]
    have h6 : Real.log (6 : ℝ) ≤ 6 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    have hKl : Real.log KPsiS ≤ lHK :=
      Real.log_le_log (by linarith only [hKS]) (by linarith only [hH])
    have hHl : Real.log H ≤ lHK :=
      Real.log_le_log (by linarith only [hH]) (by linarith only [hKS])
    have hlK0 : 0 ≤ Real.log KPsiS := Real.log_nonneg hKS
    have hlH0 : 0 ≤ Real.log H := Real.log_nonneg hH
    unfold akhcStep2Sat_bracket0
    rw [hmin, hℓ, hlogY]
    linarith only [h6, hKl, hHl, hlK0, hlH0, hlHK0]
  have hc3b : akhcStep2Sat_c3 d gamma pPsi pPsiS * akhcStep2Sat_bracket0 KPsiS H pPsiS Yd ≤
      3 * (5 + 38 * lHK + akhcDim_ell d) :=
    (mul_le_mul_of_nonneg_right hc3_le hb0).trans
      (mul_le_mul_of_nonneg_left hb_le (by norm_num))
  -- the `log K` coefficient
  have hcoef : akhcStep2Sat_Ccoef d gamma pPsi pPsiS L1 D ≤ 2 * L1 + 6 * D := by
    have := mul_le_mul_of_nonneg_left hc3_le (by linarith only [hD] : (0 : ℝ) ≤ 2 * D)
    unfold akhcStep2Sat_Ccoef
    linarith only [this]
  have hcoef0 := akhcStep2Sat_Ccoef_nonneg hd hgamma1 hpPsi' hpS' hL1 hD
  set lm := Real.log ((m : ℝ) + (m0 : ℝ) + 1) with hlm
  have hmm : (1 : ℝ) ≤ (m : ℝ) + (m0 : ℝ) + 1 := by
    have h1 := Nat.cast_nonneg (α := ℝ) m
    have h2 := Nat.cast_nonneg (α := ℝ) m0
    linarith only [h1, h2]
  have hlm0 : 0 ≤ lm := Real.log_nonneg hmm
  have hKR1 : (1 : ℝ) ≤ ((m + 3 * m0 : ℕ) : ℝ) := by exact_mod_cast hK1
  have hlogK0 : 0 ≤ Real.log ((m + 3 * m0 : ℕ) : ℝ) := Real.log_nonneg hKR1
  have hlogK : Real.log ((m + 3 * m0 : ℕ) : ℝ) ≤ 2 + lm := by
    have hKle : ((m + 3 * m0 : ℕ) : ℝ) ≤ 3 * ((m : ℝ) + (m0 : ℝ) + 1) := by
      have h1 := Nat.cast_nonneg (α := ℝ) m
      push_cast
      linarith only [h1]
    have h1 := Real.log_le_log (by linarith only [hKR1]) hKle
    rw [Real.log_mul (by norm_num) (by linarith only [hmm])] at h1
    have h3 : Real.log (3 : ℝ) ≤ 3 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith only [h1, h3]
  have hcK : akhcStep2Sat_Ccoef d gamma pPsi pPsiS L1 D * Real.log ((m + 3 * m0 : ℕ) : ℝ) ≤
      (2 * L1 + 6 * D) * (2 + lm) :=
    mul_le_mul hcoef hlogK hlogK0 (by linarith only [hcoef0, hcoef])
  -- `Y` dominates each piece
  have hl2L2 : 0 ≤ Real.log (2 * L2) := Real.log_nonneg (by linarith only [hL2])
  have hq0 : 0 ≤ L1 * Real.log (2 * L2) := mul_nonneg (by linarith only [hL1]) hl2L2
  have hCq : L1 * Real.log (2 * L2) + D + lHK ≤ C * (L1 * Real.log (2 * L2) + D + lHK) :=
    le_mul_of_one_le_left (by linarith only [hq0, hD, hlHK0]) hC
  have hLL : L1 * Real.log L2 ≤ L1 * Real.log (2 * L2) :=
    mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith only [hL2])
      (by linarith only [hL2])) (by linarith only [hL1])
  have hcY : (2 * L1 + 6 * D) * (2 + lm) ≤ (2 * L1 + 6 * D) * (2 + Y) :=
    mul_le_mul_of_nonneg_left (by linarith only [hY, hCq, hq0, hD, hlHK0])
      (by linarith only [hL1, hD])
  -- assemble in terms of `P := (1+D) L₁ Y`
  set P := (1 + D) * (L1 * Y) with hP
  have hV : 1 ≤ L1 * Y := one_le_mul_of_one_le_of_one_le hL1 hY1
  have hY0 : 0 ≤ Y := by linarith only [hY1]
  have hYP : Y ≤ P := by
    have h1 : Y ≤ L1 * Y := le_mul_of_one_le_left hY0 hL1
    have h2 : L1 * Y ≤ (1 + D) * (L1 * Y) := le_mul_of_one_le_left (by linarith only [hV])
      (by linarith only [hD])
    rw [hP]
    linarith only [h1, h2]
  have hP1 : 1 ≤ P := by linarith only [hYP, hY1]
  have hcoefP : (2 * L1 + 6 * D) * (2 + Y) ≤ 18 * P := by
    have hDL : D ≤ D * L1 := le_mul_of_one_le_right hD hL1
    have h1 : (2 * L1 + 6 * D) * (2 + Y) ≤ (2 * L1 + 6 * D) * (3 * Y) :=
      mul_le_mul_of_nonneg_left (by linarith only [hY1]) (by linarith only [hL1, hD])
    have h2 : (2 * L1 + 6 * D) * (3 * Y) ≤ (6 * (1 + D) * L1) * (3 * Y) :=
      mul_le_mul_of_nonneg_right (by linarith only [hDL, hL1]) (by linarith only [hY0])
    have h3 : (6 * (1 + D) * L1) * (3 * Y) = 18 * P := by rw [hP]; ring
    linarith only [h1, h2, h3]
  have hconst : 21 + (4 * (d : ℝ) + 7) * akhcDim_ell d ≤
      (21 + (4 * (d : ℝ) + 7) * akhcDim_ell d) * P :=
    le_mul_of_one_le_right (by positivity) hP1
  have hcL : akhcDim_cL d * P = (160 + (4 * (d : ℝ) + 7) * akhcDim_ell d) * P := rfl
  have hCc : akhcStep2Sat_Cconst d gamma pPsi pPsiS L1 L2 H KPsiS Yd =
      2 * (L1 * Real.log L2) + 4 + akhcStep2Sat_T1val d gamma pPsi pPsiS Yd +
        akhcStep2Sat_c3 d gamma pPsi pPsiS * akhcStep2Sat_bracket0 KPsiS H pPsiS Yd := by
    unfold akhcStep2Sat_Cconst; ring
  have hexp : (160 + (4 * (d : ℝ) + 7) * akhcDim_ell d) * P =
      (21 + (4 * (d : ℝ) + 7) * akhcDim_ell d) * P + 139 * P := by ring
  linarith only [hL, hCc, hT1, hc3b, hcK, hcY, hcoefP, hconst, hcL, hexp, hLL, hYP, hP1, hY,
    hCq, hq0, hD, hlHK0, hlm0, hℓ0]

/-- **`akhcF1_core`'s `hm0` at `σ = σ_d`** from V5's `m₀` threshold, for
`C ≥ max{2, 2 c_L(d) N₁(d), 4 c_L(d) + 1}`. -/
theorem akhcDim_m0Req {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    {gamma pPsi pPsiS L1 L2 H D KPsiS KPsi beta C Θ0 : ℝ} {m m0 : ℕ}
    (hg0 : 0 ≤ gamma) (hg : gamma ≤ 1 / 2) (hb0 : 0 ≤ beta) (hb : beta ≤ 1 / 2)
    (hpPsi : (d : ℝ) + 1 ≤ pPsi) (hpS : 3 ≤ pPsiS)
    (hL1 : 1 ≤ L1) (hL2 : 1 ≤ L2) (hH : 1 ≤ H) (hD : 0 ≤ D) (hKS : 1 ≤ KPsiS) (hK : 1 ≤ KPsi)
    (hΘ0 : 1 ≤ Θ0) (hC2 : 2 ≤ C) (hCa : 2 * akhcDim_cL d * (akhcDim_N1 d : ℝ) ≤ C)
    (hCb : 4 * akhcDim_cL d + 1 ≤ C)
    (hthr : akhcCL5_thr d C KPsi pPsi pPsiS L1 L2 D gamma beta H KPsiS m m0 Θ0 ≤ (m0 : ℝ)) :
    akhcStep2_m0Req d gamma pPsi pPsiS L1 L2 H D KPsiS beta (akhcCL5_sigma d) Θ0 m m0 := by
  obtain ⟨hY, hY1, hthrP⟩ := akhcCL5_thr_props d hC2 hK hpPsi hpS hL1 hL2 hD hg0 hg hb0 hb hH
    hKS hΘ0 hthr
  set Y := Real.log (akhcCL5_thrX d C KPsi pPsi pPsiS L1 L2 D gamma H KPsiS m m0 Θ0) with hYdef
  have hV : 1 ≤ L1 * Y := one_le_mul_of_one_le_of_one_le hL1 hY1
  obtain ⟨hW1, -⟩ := akhcCL5_W_props hΘ0 hV
  set W := Real.log (3 * Θ0 * (2 + L1 * Y)) with hWdef
  have hP1 : 1 ≤ (1 + D) * (L1 * Y) :=
    one_le_mul_of_one_le_of_one_le (by linarith only [hD]) hV
  set P := (1 + D) * (L1 * Y) with hP
  have hCPW : C * P * W ≤ (m0 : ℝ) := by
    have he : C * (1 + D) * (L1 * Y) * W = C * P * W := by rw [hP]; ring
    linarith only [he, hthrP]
  have hC1 : (1 : ℝ) ≤ C := by linarith only [hC2]
  have hPW : 1 ≤ P * W := one_le_mul_of_one_le_of_one_le hP1 hW1
  have hCPW1 : 1 ≤ C * P * W := by
    have := one_le_mul_of_one_le_of_one_le hC1 hPW
    rw [← mul_assoc] at this
    exact this
  have hm0N : 1 ≤ m0 := by
    have : (1 : ℝ) ≤ (m0 : ℝ) := by linarith only [hCPW1, hCPW]
    exact_mod_cast this
  have hLr := akhcDim_Lreq_le hd hg0 hg hpPsi hpS hL1 hL2 hH hD hKS hC1 hm0N hY hY1
    (gamma := gamma) (pPsi := pPsi) (pPsiS := pPsiS)
  rw [← hP] at hLr
  have hcL0 := akhcDim_cL_nonneg d
  have hP0 : 0 ≤ P := by linarith only [hP1]
  have hW0 : 0 ≤ W := by linarith only [hW1]
  unfold akhcStep2_m0Req
  rw [akhcDim_delta_eq hd hg hpPsi hpS]
  set Lr := akhcStep2_Lreq d gamma pPsi pPsiS L1 L2 H D KPsiS
    (akhcDim_delta d * akhcCL5_sigma d ^ 2) (m + 3 * m0) with hLrdef
  refine ⟨?_, ?_⟩
  · have hN : SuperdiffusionCLT.AKHC61.Step2.akhcLaunchNprimeNat Lr (akhcDim_delta d)
        (akhcCL5_sigma d) = 2 * Lr * akhcDim_N1 d := rfl
    rw [hN]
    have h3Θ : (1 : ℝ) ≤ 3 * Θ0 := by linarith only [hΘ0]
    have hl0 : 0 ≤ Real.log (3 * Θ0) := Real.log_nonneg h3Θ
    have hceil : (⌈Real.log (3 * Θ0)⌉₊ : ℝ) ≤ W := by
      have h1 := Nat.ceil_lt_add_one hl0
      have h2 : Real.log (3 * Θ0 * (2 + L1 * Y)) = Real.log (3 * Θ0) + Real.log (2 + L1 * Y) :=
        Real.log_mul (by linarith only [h3Θ]) (by linarith only [hV])
      have h3 : Real.log 3 ≤ Real.log (2 + L1 * Y) :=
        Real.log_le_log (by norm_num) (by linarith only [hV])
      have h4 := akhcDim_one_le_log3
      rw [hWdef, h2]
      linarith only [h1, h3, h4]
    have hN10 : (0 : ℝ) ≤ (akhcDim_N1 d : ℝ) := Nat.cast_nonneg _
    have hLr0 : (0 : ℝ) ≤ (Lr : ℝ) := Nat.cast_nonneg _
    have hinner : 2 * (Lr : ℝ) * (akhcDim_N1 d : ℝ) ≤ 2 * (akhcDim_cL d * P) * (akhcDim_N1 d : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith only [hLr]) hN10
    have hprod : (⌈Real.log (3 * Θ0)⌉₊ : ℝ) * (2 * (Lr : ℝ) * (akhcDim_N1 d : ℝ)) ≤
        W * (2 * (akhcDim_cL d * P) * (akhcDim_N1 d : ℝ)) :=
      mul_le_mul hceil hinner (by positivity) hW0
    have hre : W * (2 * (akhcDim_cL d * P) * (akhcDim_N1 d : ℝ)) =
        (2 * akhcDim_cL d * (akhcDim_N1 d : ℝ)) * (P * W) := by ring
    have hCa' : (2 * akhcDim_cL d * (akhcDim_N1 d : ℝ)) * (P * W) ≤ C * (P * W) :=
      mul_le_mul_of_nonneg_right hCa (mul_nonneg hP0 hW0)
    have hCre : C * (P * W) = C * P * W := by ring
    have hreal : ((⌈Real.log (3 * Θ0)⌉₊ * (2 * Lr * akhcDim_N1 d) : ℕ) : ℝ) ≤ (m0 : ℝ) := by
      push_cast
      linarith only [hprod, hre, hCa', hCre, hCPW]
    exact_mod_cast hreal
  · have hbm : beta * (m0 : ℝ) ≤ 1 / 2 * (m0 : ℝ) :=
      mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg _)
    have hCP : C * P ≤ C * P * W := le_mul_of_one_le_right (by positivity) hW1
    have hcP : (4 * akhcDim_cL d + 1) * P ≤ C * P := mul_le_mul_of_nonneg_right hCb hP0
    have he : (1 - beta) * (m0 : ℝ) = (m0 : ℝ) - beta * (m0 : ℝ) := by ring
    have he2 : (4 * akhcDim_cL d + 1) * P = 4 * (akhcDim_cL d * P) + P := by ring
    rw [he]
    linarith only [hLr, hbm, hCP, hcP, he2, hCPW, hP1]

end

end SuperdiffusionCLT.AKHC61
