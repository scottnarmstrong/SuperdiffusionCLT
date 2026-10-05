/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.Core
public import SuperdiffusionCLT.AKHC61.Params.M0ReqSat
public import SuperdiffusionCLT.AKHC61.Step3.ClosureThreshold

/-!
# AK.HC Theorem 6.1 on the V5 range: Step 2's inputs from V5's binders

`akhcF1_core` (`AKHC61/Core.lean`) closes Step 2 from two inputs at the level `σ`:
the smallness `ω_m² Υ₁^{port} ≤ δσ²` (`akhcStep2_Upsilon1`, `akhcStep2_delta`) and the requirement
`akhcStep2_m0Req` on `m₀`. This file derives both, at `σ := σ_d = akhcCL5_sigma d`, from V5's
`ω_m²` binder `ω_m² ≤ (C K_Ψ^{6(d+1)²}/(min{d+1,p_Ψ}-d))⁻¹` and V5's `m₀` threshold, for `C`
at least the dimension constant `akhcDim_C d`.

On V5's range (`γ ≤ 1/2`, `d + 1 ≤ p_Ψ`, `3 ≤ p_{Ψ_S}`) Step 2's exponents depend on `d` alone:
`ρ′ = d/(d+1)`, `η = d + 1`, `ρ = (2d+1)/(2d+2)`, `s′ = (4d+3)/(8d+8)`, so `δ` is a constant
`δ_d`. Step 2's `Υ₁` carries the powers `K_Ψ^{3(d+1)²}` and `K_Ψ^{3(d+1)²+6(d+1)}`, both at most
`K_Ψ^{6(d+1)²}`: `Υ₁ ≤ (d+2) c_Υ(d) K_Ψ^{6(d+1)²}` (`akhcDim_Upsilon1_le`).
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61

open SuperdiffusionCLT.AKHC61.Params
open SuperdiffusionCLT.AKHC61.ParamsProofNative
open SuperdiffusionCLT.AKHC61.Step3

noncomputable section

/-! ## Step 2's exponents on V5's range -/

section Exponents

variable {d : ℕ} {gamma pPsi pPsiS : ℝ}

/-- `ρ′ = d/(d+1)` on V5's range. -/
theorem akhcDim_rhoPrime_eq (hd : 2 ≤ d) (hg : gamma ≤ 1 / 2) (hpPsi : (d : ℝ) + 1 ≤ pPsi)
    (hpS : 3 ≤ pPsiS) : akhcRhoPrime d gamma pPsi pPsiS = (d : ℝ) / ((d : ℝ) + 1) := by
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have h1 : (2 : ℝ) / 3 ≤ (d : ℝ) / ((d : ℝ) + 1) := by
    rw [div_le_div_iff₀ (by norm_num) (by linarith only [hd2])]
    linarith only [hd2]
  have h2 : gamma ≤ (d : ℝ) / ((d : ℝ) + 1) := by linarith only [hg, h1]
  unfold akhcRhoPrime
  rw [min_eq_left hpPsi, min_eq_left hpS, max_eq_left h1, max_eq_right h2]

/-- `ρ′` agrees with its value at the reference point `(γ, p_Ψ, p_{Ψ_S}) = (0, d+1, 3)`. -/
theorem akhcDim_rhoPrime_ref (hd : 2 ≤ d) (hg : gamma ≤ 1 / 2) (hpPsi : (d : ℝ) + 1 ≤ pPsi)
    (hpS : 3 ≤ pPsiS) :
    akhcRhoPrime d gamma pPsi pPsiS = akhcRhoPrime d 0 ((d : ℝ) + 1) 3 := by
  rw [akhcDim_rhoPrime_eq hd hg hpPsi hpS,
    akhcDim_rhoPrime_eq hd (by norm_num) le_rfl le_rfl]

/-- `ρ = (2d+1)/(2d+2)` on V5's range. -/
theorem akhcDim_rho_eq (hd : 2 ≤ d) (hg : gamma ≤ 1 / 2) (hpPsi : (d : ℝ) + 1 ≤ pPsi)
    (hpS : 3 ≤ pPsiS) : akhcRho d gamma pPsi pPsiS = akhcCL5_rho d := by
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  unfold akhcRho akhcCL5_rho
  rw [akhcDim_rhoPrime_eq hd hg hpPsi hpS]
  field_simp
  ring

/-- `η = d + 1` on V5's range. -/
theorem akhcDim_eta_eq (hpPsi : (d : ℝ) + 1 ≤ pPsi) : akhcEta d pPsi = akhcCL5_eta d := by
  unfold akhcEta akhcCL5_eta
  exact min_eq_left hpPsi

/-- `1 - 2s′ = 1/(4d+4)` on V5's range. -/
theorem akhcDim_one_sub_two_sPrime (hd : 2 ≤ d) (hg : gamma ≤ 1 / 2)
    (hpPsi : (d : ℝ) + 1 ≤ pPsi) (hpS : 3 ≤ pPsiS) :
    1 - 2 * akhcStep2_sPrime d gamma pPsi pPsiS = 1 / (4 * (d : ℝ) + 4) := by
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  unfold akhcStep2_sPrime
  rw [akhcDim_rho_eq hd hg hpPsi hpS]
  unfold akhcCL5_rho
  field_simp
  ring

end Exponents

/-! ## The Step 2 level `δ_d` -/

/-- `δ_d := δ` at the reference point `(0, d+1, 3)`. -/
def akhcDim_delta (d : ℕ) [NeZero d] : ℝ := akhcStep2_delta d 0 ((d : ℝ) + 1) 3

theorem akhcDim_delta_eq {d : ℕ} [NeZero d] (hd : 2 ≤ d) {gamma pPsi pPsiS : ℝ}
    (hg : gamma ≤ 1 / 2) (hpPsi : (d : ℝ) + 1 ≤ pPsi) (hpS : 3 ≤ pPsiS) :
    akhcStep2_delta d gamma pPsi pPsiS = akhcDim_delta d := by
  unfold akhcDim_delta akhcStep2_delta akhcStep2_Kw akhcStep2_sPrime akhcRho
  rw [akhcDim_rhoPrime_ref hd hg hpPsi hpS]

theorem akhcDim_delta_pos (d : ℕ) [NeZero d] : 0 < akhcDim_delta d :=
  akhcStep2_delta_pos d 0 ((d : ℝ) + 1) 3

/-- `Y_d := δ_d σ_d²` lies in `(0, 1)`. -/
theorem akhcDim_Yd_props (d : ℕ) [NeZero d] :
    0 < akhcDim_delta d * akhcCL5_sigma d ^ 2 ∧ akhcDim_delta d * akhcCL5_sigma d ^ 2 < 1 := by
  have hδ := akhcDim_delta_pos d
  have hδle : akhcDim_delta d ≤ (6400 : ℝ)⁻¹ := akhcStep2_delta_le d 0 ((d : ℝ) + 1) 3
  have hσ := akhcCL5_sigma_pos d
  obtain ⟨-, -, hσ1⟩ := akhcCL5_sigma_props hσ.le (le_refl (akhcCL5_sigma d))
  have hσ2 : akhcCL5_sigma d ^ 2 ≤ 1 := by
    have := mul_le_mul hσ1 hσ1 hσ.le zero_le_one
    nlinarith only [this]
  refine ⟨by positivity, ?_⟩
  have := mul_le_mul hδle hσ2 (sq_nonneg _) (by norm_num)
  linarith only [this]

/-! ## Step 2's `Υ₁` fits V5's power -/

/-- `(d+2) c_Υ(d)`: the coefficient of `K_Ψ^{6(d+1)²}` bounding Step 2's `Υ₁`. -/
def akhcDim_cUps1 (d : ℕ) : ℝ := ((d : ℝ) + 2) * akhcCL5_cUps d

/-- **Step 2's `Υ₁` is at most `(d+2) c_Υ(d) K_Ψ^{6(d+1)²}`** on V5's range. Its powers are
`K_Ψ^{3(d+1)²}` and `K_Ψ^{3(d+1)²} K_Ψ^{6(d+1)}`, the same as `Υ^{port}`'s. -/
theorem akhcDim_Upsilon1_le {d : ℕ} (hd : 2 ≤ d) {gamma pPsi pPsiS KPsi : ℝ}
    (hg : gamma ≤ 1 / 2) (hpPsi : (d : ℝ) + 1 ≤ pPsi) (hpS : 3 ≤ pPsiS) (hK : 1 ≤ KPsi) :
    akhcStep2_Upsilon1 d gamma pPsi pPsiS KPsi ≤ akhcDim_cUps1 d * KPsi ^ (6 * (d + 1) ^ 2) := by
  have hUp := akhcCL5_UpsPort_le d hd hK
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hK0 : 0 ≤ KPsi := by linarith only [hK]
  have heta := akhcCL5_eta_gt d hd
  have hc := akhcCL5_c_pos d
  have hcmp : akhcStep2_Upsilon1 d gamma pPsi pPsiS KPsi ≤
      ((d : ℝ) + 2) * akhcRW_UpsPort d (akhcCL5_eta d) (akhcCL5_rho d) KPsi := by
    unfold akhcStep2_Upsilon1 akhcRW_UpsPort akhcRW_UpsVar akhcRW_UpsMM
    rw [akhcDim_eta_eq hpPsi, akhcDim_rho_eq hd hg hpPsi hpS]
    set η := akhcCL5_eta d with hη
    set A := η / (η - 2) * KPsi ^ (3 * ⌈η⌉₊ ^ 2) with hA
    have hA0 : 0 ≤ A := by
      rw [hA]
      exact mul_nonneg (div_nonneg (by linarith only [heta]) (by linarith only [heta]))
        (pow_nonneg hK0 _)
    have h3 : (3 : ℝ) ^ (-(2 * akhcCL5_rho d - 2 * (d : ℝ) / η)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hc])
    set Bm := A * KPsi ^ (2 * (3 * (⌈η⌉₊ : ℝ) ^ 2) / η) *
      (1 - (3 : ℝ) ^ (-(2 * akhcCL5_rho d - 2 * (d : ℝ) / η)))⁻¹ with hBm
    have hBm0 : 0 ≤ Bm := by
      rw [hBm]
      exact mul_nonneg (mul_nonneg hA0 (Real.rpow_nonneg hK0 _)) (inv_nonneg.2 (by
        linarith only [h3]))
    have key : ((d : ℝ) + 2) * (128 * ((2 * (d : ℝ)) ^ 2 * A) + Bm) =
        16 * (3 + 6 * (d : ℝ)) * (d : ℝ) ^ 2 * A + 2 * Bm +
          ((d : ℝ) ^ 2 * A * (416 * (d : ℝ) + 976) + (d : ℝ) * Bm) := by ring
    have hrest : 0 ≤ (d : ℝ) ^ 2 * A * (416 * (d : ℝ) + 976) + (d : ℝ) * Bm :=
      add_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hA0) (by positivity))
        (mul_nonneg hd0 hBm0)
    linarith only [key, hrest]
  have hmul := mul_le_mul_of_nonneg_left hUp (by linarith only [hd0] : (0 : ℝ) ≤ (d : ℝ) + 2)
  unfold akhcDim_cUps1
  linarith only [hcmp, hmul]

/-! ## `hOmega` from V5's `ω_m²` binder -/

/-- The constant `C` must reach for `hOmega`: `(d+2) c_Υ(d)/(δ_d σ_d²)`. -/
def akhcDim_Comega (d : ℕ) [NeZero d] : ℝ :=
  akhcDim_cUps1 d / (akhcDim_delta d * akhcCL5_sigma d ^ 2)

/-- **`akhcF1_core`'s `hOmega` at `σ = σ_d`** from V5's `ω_m²` binder, for
`C ≥ max{1, (d+2) c_Υ(d)/(δ_d σ_d²)}`. -/
theorem akhcDim_hOmega {d : ℕ} [NeZero d] (hd : 2 ≤ d) {gamma pPsi pPsiS KPsi C om : ℝ}
    (hg : gamma ≤ 1 / 2) (hpPsi : (d : ℝ) + 1 ≤ pPsi) (hpS : 3 ≤ pPsiS) (hK : 1 ≤ KPsi)
    (hC1 : 1 ≤ C) (hC : akhcDim_Comega d ≤ C)
    (hom : om ^ 2 ≤ (C * KPsi ^ (6 * (d + 1) ^ 2) / (min ((d : ℝ) + 1) pPsi - (d : ℝ)))⁻¹) :
    om ^ 2 * akhcStep2_Upsilon1 d gamma pPsi pPsiS KPsi ≤
      akhcStep2_delta d gamma pPsi pPsiS * akhcCL5_sigma d ^ 2 := by
  have hmin : min ((d : ℝ) + 1) pPsi - (d : ℝ) = 1 := by rw [min_eq_left hpPsi]; ring
  rw [hmin, div_one] at hom
  rw [akhcDim_delta_eq hd hg hpPsi hpS]
  obtain ⟨hY0, -⟩ := akhcDim_Yd_props d
  set Yd := akhcDim_delta d * akhcCL5_sigma d ^ 2 with hYd
  set Kp := KPsi ^ (6 * (d + 1) ^ 2) with hKp
  have hKp0 : 0 < Kp := pow_pos (by linarith only [hK]) _
  have hC0 : 0 < C := by linarith only [hC1]
  have hom0 : 0 ≤ om ^ 2 := sq_nonneg om
  have h1 : C * Kp * om ^ 2 ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hom (by positivity : (0 : ℝ) ≤ C * Kp)
    rwa [mul_inv_cancel₀ (by positivity)] at this
  have hcU : akhcDim_cUps1 d ≤ C * Yd := by
    unfold akhcDim_Comega at hC
    rw [← hYd, div_le_iff₀ hY0] at hC
    exact hC
  have h2 : om ^ 2 * akhcStep2_Upsilon1 d gamma pPsi pPsiS KPsi ≤ om ^ 2 * (akhcDim_cUps1 d * Kp) :=
    mul_le_mul_of_nonneg_left (akhcDim_Upsilon1_le hd hg hpPsi hpS hK) hom0
  have h3 : om ^ 2 * (akhcDim_cUps1 d * Kp) ≤ om ^ 2 * ((C * Yd) * Kp) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcU hKp0.le) hom0
  have h4 : om ^ 2 * ((C * Yd) * Kp) = Yd * (C * Kp * om ^ 2) := by ring
  have h5 : Yd * (C * Kp * om ^ 2) ≤ Yd * 1 := mul_le_mul_of_nonneg_left h1 hY0.le
  linarith only [h2, h3, h4, h5]

end

end SuperdiffusionCLT.AKHC61
