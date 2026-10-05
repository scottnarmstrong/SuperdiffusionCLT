/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.Step3.ClosurePrime
public import SuperdiffusionCLT.AKHC61.Step3.DecayWeightedB

/-!
# Closing Step 3 on the V5 range, part 1: the dimension-only parameters and the lag

The V5 anchor (`Frozen/Section4/AKHCWeakerP3.lean`, read and never imported) restricts AK.HC
Theorem 6.1 to `γ ≤ 1/2`, `β ≤ 1/2`, `d + 1 ≤ p_Ψ`, `3 ≤ p_{Ψ_S}`. On that range every exponent
of the weighted recursion `akhcRV2_weighted_recursion` can be fixed as a function of `d` alone:

* `s' := (4d+3)/(8d+8)`, so `1 - 2s' = 1/(4d+4)`;
* `ρ := (2d+1)/(2d+2)`, so `ρ ≥ 5/6` for `d ≥ 2` and `ρ - γ ≥ 1/3`;
* `η := d + 1`, so `2ρ - 2d/η = 1/(d+1)`;
* `w := 3^{-(1/2-s')}`, `θ := θmax(d)`, `c := linConst(d)/2`, `B := B_w(d, s', ρ)`;
* `Lstep := ⌈32·2^d·G_d⌉ + 1`, which meets the scale separation on every cube.

The decay lemma `akhcDW_decay` (`Step3/DecayWeightedB.lean`) at these values has the rate
`κ(d) := akhcDW_kappa θ B w Lstep`, with `κ(d) ≤ (1-2s')/4 = 1/(16(d+1))`.

This file also holds:
* the comparison of the port's `ω²` coefficient with V5's power,
  `Υ^{port}(d, d+1, ρ, K_Ψ) ≤ c_Υ(d) K_Ψ^{6(d+1)²}` (`akhcCL5_UpsPort_le`), and its use on V5's
  `ω_m²` binder (`akhcCL5_hS_of_omega`);
* the lag `ℓ(n) = ⌈L₁ log(L₂ n)⌉`, which grows by at most `(n - K)/4 + 1` above any `K ≥ 4L₁`
  (`akhcCL5_lag_growth`);
* the base of the recursion at scale `n`, `k(n) := max K₀ (⌊n/2⌋ + 1)`. It meets `βn < k(n)` for
  `β ≤ 1/2` and leaves `n - k(n) ≥ (n - K₀)/3` and `n - k(n) - ℓ(k(n)) ≥ (n - K₀)/4`
  (`akhcCL5_k_props`).
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.Step3

noncomputable section

/-! ## The parameters -/

/-- `s' := (4d+3)/(8d+8)`. -/
def akhcCL5_s (d : ℕ) : ℝ := (4 * (d : ℝ) + 3) / (8 * (d : ℝ) + 8)

/-- `ρ := (2d+1)/(2d+2)`. -/
def akhcCL5_rho (d : ℕ) : ℝ := (2 * (d : ℝ) + 1) / (2 * (d : ℝ) + 2)

/-- `η := d + 1`. -/
def akhcCL5_eta (d : ℕ) : ℝ := (d : ℝ) + 1

/-- The weight `w := 3^{-(1/2-s')}`. -/
def akhcCL5_w (d : ℕ) : ℝ := (3 : ℝ) ^ (-(1 / 2 - akhcCL5_s d))

/-- The contraction `θ := θmax(d)`. -/
def akhcCL5_theta (d : ℕ) : ℝ := akhcIter_thetaMax d

/-- The quadratic coefficient `c := linConst(d)/2`. -/
def akhcCL5_c (d : ℕ) : ℝ := SuperdiffusionCLT.AKHC61.Step2.akhcJB_linConst d / 2

/-- The weighted-sum coefficient `B := B_w(d, s', ρ)`. -/
def akhcCL5_B (d : ℕ) [NeZero d] : ℝ := akhcRW_Bw d (akhcCL5_s d) (akhcCL5_rho d)

/-- The contraction lag `Lstep := ⌈32·2^d·G_d⌉ + 1`. -/
def akhcCL5_Lstep (d : ℕ) : ℕ :=
  ⌈32 * (2 : ℝ) ^ d * Homogenization.quantitativeCubeCutoffGradientConst d⌉₊ + 1

/-- **The Step 3 rate** `κ(d) := akhcDW_kappa θ B w Lstep`. -/
def akhcCL5_kappa (d : ℕ) [NeZero d] : ℝ :=
  akhcDW_kappa (akhcCL5_theta d) (akhcCL5_B d) (akhcCL5_w d) (akhcCL5_Lstep d)

/-- `r := 3^{-κ(d)}`. -/
def akhcCL5_r (d : ℕ) [NeZero d] : ℝ :=
  akhcDW_r (akhcCL5_theta d) (akhcCL5_B d) (akhcCL5_w d) (akhcCL5_Lstep d)

/-- The lag-smallness level `ε(d)`. -/
def akhcCL5_eps (d : ℕ) [NeZero d] : ℝ :=
  akhcDW_eps (akhcCL5_theta d) (akhcCL5_B d) (akhcCL5_B d) (akhcCL5_w d)

/-- The source-smallness level `ζ(d)`. -/
def akhcCL5_zeta (d : ℕ) [NeZero d] : ℝ :=
  akhcDW_zeta (akhcCL5_theta d) (akhcCL5_B d) (akhcCL5_w d)

/-- **The Step 2 level** `σ_d := min{ε/2, (1-θ)/(4(c+1))}`. -/
def akhcCL5_sigma (d : ℕ) [NeZero d] : ℝ :=
  min (akhcCL5_eps d / 2) ((1 - akhcCL5_theta d) / (4 * (akhcCL5_c d + 1)))

/-- The base pre-phase length `M_d := ⌈log(1/2)/log r⌉`, so `r^{M_d} ≤ 1/2`. -/
def akhcCL5_Md (d : ℕ) [NeZero d] : ℕ :=
  ⌈Real.log (1 / 2) / Real.log (akhcCL5_r d)⌉₊

/-- The dimension constant of the `Υ^{port}` comparison,
`c_Υ := (η/(η-2)) (128 (2d)² + (1 - 3^{-(2ρ-2d/η)})⁻¹)`. -/
def akhcCL5_cUps (d : ℕ) : ℝ :=
  akhcCL5_eta d / (akhcCL5_eta d - 2) *
    (128 * (2 * (d : ℝ)) ^ 2 +
      (1 - (3 : ℝ) ^ (-(2 * akhcCL5_rho d - 2 * (d : ℝ) / akhcCL5_eta d)))⁻¹)

/-- **The `ω²` coefficient of Step 3**, `U := B Υ^{port}(d, η, ρ, K_Ψ) / ζ`. -/
def akhcCL5_U (d : ℕ) [NeZero d] (KPsi : ℝ) : ℝ :=
  akhcCL5_B d * akhcRW_UpsPort d (akhcCL5_eta d) (akhcCL5_rho d) KPsi / akhcCL5_zeta d

/-! ## The range conditions of the weighted recursion -/

theorem akhcCL5_s_lo (d : ℕ) : 1 / 4 ≤ akhcCL5_s d := by
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  unfold akhcCL5_s
  rw [le_div_iff₀ (by positivity)]
  linarith only [hd]

theorem akhcCL5_s_hi (d : ℕ) : akhcCL5_s d < 1 / 2 := by
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  unfold akhcCL5_s
  rw [div_lt_iff₀ (by positivity)]
  linarith only [hd]

theorem akhcCL5_one_sub_two_s (d : ℕ) : 1 - 2 * akhcCL5_s d = 1 / (4 * (d : ℝ) + 4) := by
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  unfold akhcCL5_s
  field_simp
  ring

theorem akhcCL5_gap (d : ℕ) : akhcCL5_rho d / 2 < akhcCL5_s d := by
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  unfold akhcCL5_rho akhcCL5_s
  rw [div_div, div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith only [hd]

theorem akhcCL5_rho_ge (d : ℕ) (hd : 2 ≤ d) : 5 / 6 ≤ akhcCL5_rho d := by
  have hd' : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  unfold akhcCL5_rho
  rw [le_div_iff₀ (by positivity)]
  linarith only [hd']

theorem akhcCL5_eta_gt (d : ℕ) (hd : 2 ≤ d) : 2 < akhcCL5_eta d := by
  have hd' : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  unfold akhcCL5_eta
  linarith only [hd']

theorem akhcCL5_c_eq (d : ℕ) :
    2 * akhcCL5_rho d - 2 * (d : ℝ) / akhcCL5_eta d = 1 / ((d : ℝ) + 1) := by
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  unfold akhcCL5_rho akhcCL5_eta
  field_simp
  ring

theorem akhcCL5_c_pos (d : ℕ) : 0 < 2 * akhcCL5_rho d - 2 * (d : ℝ) / akhcCL5_eta d := by
  rw [akhcCL5_c_eq]
  positivity

theorem akhcCL5_w_pos (d : ℕ) : 0 < akhcCL5_w d := by
  unfold akhcCL5_w
  positivity

theorem akhcCL5_w_lt_one (d : ℕ) : akhcCL5_w d < 1 := by
  have h := akhcCL5_s_hi d
  unfold akhcCL5_w
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [h])

theorem akhcCL5_theta_nonneg (d : ℕ) : 0 ≤ akhcCL5_theta d := akhcIter_thetaMax_nonneg d

theorem akhcCL5_theta_lt_one (d : ℕ) : akhcCL5_theta d < 1 := akhcIter_thetaMax_lt_one d

theorem akhcCL5_B_nonneg (d : ℕ) [NeZero d] : 0 ≤ akhcCL5_B d :=
  akhcCL_Bw_nonneg d (akhcCL5_rho d) (akhcCL5_s_hi d)

theorem akhcCL5_c_nonneg (d : ℕ) : 0 ≤ akhcCL5_c d := by
  have hG := Homogenization.quantitativeCubeCutoffGradientConst_nonneg d
  unfold akhcCL5_c SuperdiffusionCLT.AKHC61.Step2.akhcJB_linConst
  positivity

/-! ## The rate and the levels -/

section Levels

variable (d : ℕ) [NeZero d]

theorem akhcCL5_kappa_pos : 0 < akhcCL5_kappa d :=
  akhcDW_kappa_pos (akhcCL5_theta_nonneg d) (akhcCL5_theta_lt_one d) (akhcCL5_B_nonneg d)
    (akhcCL5_w_pos d) (akhcCL5_w_lt_one d) _

/-- `κ(d) ≤ (1-2s')/4 = 1/(16(d+1))`. -/
theorem akhcCL5_kappa_le : akhcCL5_kappa d ≤ 1 / (16 * ((d : ℝ) + 1)) := by
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h1 : akhcCL5_kappa d ≤ -Real.log (akhcCL5_w d) / (2 * Real.log 3) := min_le_right _ _
  have hlw : Real.log (akhcCL5_w d) = -(1 / 2 - akhcCL5_s d) * Real.log 3 := by
    unfold akhcCL5_w
    rw [Real.log_rpow (by norm_num)]
  have h2 : -Real.log (akhcCL5_w d) / (2 * Real.log 3) = (1 - 2 * akhcCL5_s d) / 4 := by
    rw [hlw]
    field_simp
    ring
  rw [h2, akhcCL5_one_sub_two_s] at h1
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  calc akhcCL5_kappa d ≤ 1 / (4 * (d : ℝ) + 4) / 4 := h1
    _ = 1 / (16 * ((d : ℝ) + 1)) := by field_simp; ring

theorem akhcCL5_kappa_le_small (hd2 : 2 ≤ d) : akhcCL5_kappa d ≤ 1 / 48 := by
  have h := akhcCL5_kappa_le d
  have hd : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
  have h2 : 1 / (16 * ((d : ℝ) + 1)) ≤ 1 / 48 := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith only [hd]
  linarith only [h, h2]

theorem akhcCL5_r_pos : 0 < akhcCL5_r d := akhcDW_r_pos _

theorem akhcCL5_r_lt_one : akhcCL5_r d < 1 :=
  akhcDW_r_lt_one (akhcCL5_theta_nonneg d) (akhcCL5_theta_lt_one d) (akhcCL5_B_nonneg d)
    (akhcCL5_w_pos d) (akhcCL5_w_lt_one d) _

theorem akhcCL5_r_pow (n : ℕ) :
    akhcCL5_r d ^ n = (3 : ℝ) ^ (-(akhcCL5_kappa d * (n : ℝ))) := akhcDW_r_pow _ n

theorem akhcCL5_eps_pos : 0 < akhcCL5_eps d :=
  akhcDW_eps_pos (akhcCL5_theta_nonneg d) (akhcCL5_theta_lt_one d) (akhcCL5_B_nonneg d)
    (akhcCL5_B_nonneg d) (akhcCL5_w_pos d) (akhcCL5_w_lt_one d)

theorem akhcCL5_eps_le : akhcCL5_eps d ≤ 1 / 4 :=
  akhcDW_eps_le (akhcCL5_theta_nonneg d) (akhcCL5_B_nonneg d) (akhcCL5_B_nonneg d)
    (akhcCL5_w_pos d) (akhcCL5_w_lt_one d)

theorem akhcCL5_zeta_pos : 0 < akhcCL5_zeta d :=
  akhcDW_zeta_pos (akhcCL5_theta_nonneg d) (akhcCL5_theta_lt_one d) (akhcCL5_B_nonneg d)
    (akhcCL5_w_lt_one d)

theorem akhcCL5_sigma_pos : 0 < akhcCL5_sigma d := by
  have he := akhcCL5_eps_pos d
  have hθ := akhcCL5_theta_lt_one d
  have hc := akhcCL5_c_nonneg d
  unfold akhcCL5_sigma
  refine lt_min (by positivity) (div_pos (by linarith only [hθ]) (by positivity))

variable {d}

/-- What `σ ≤ σ_d` gives: `σ ≤ ε/2`, `cσ ≤ (1-θ)/4`, and `σ ≤ 1`. -/
theorem akhcCL5_sigma_props {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ : σ ≤ akhcCL5_sigma d) :
    σ ≤ akhcCL5_eps d / 2 ∧ akhcCL5_c d * σ ≤ (1 - akhcCL5_theta d) / 4 ∧ σ ≤ 1 := by
  have hc := akhcCL5_c_nonneg d
  have hθ := akhcCL5_theta_lt_one d
  have he := akhcCL5_eps_le d
  have h1 : σ ≤ akhcCL5_eps d / 2 := hσ.trans (min_le_left _ _)
  have h2 : σ ≤ (1 - akhcCL5_theta d) / (4 * (akhcCL5_c d + 1)) := hσ.trans (min_le_right _ _)
  refine ⟨h1, ?_, by linarith only [h1, he]⟩
  rw [le_div_iff₀ (by positivity)] at h2
  nlinarith only [h2, hc, hσ0]

variable (d)

theorem akhcCL5_r_pow_Md : akhcCL5_r d ^ akhcCL5_Md d ≤ 1 / 2 :=
  akhcDW_pow_le_of_ceil_le (akhcCL5_r_pos d) (akhcCL5_r_lt_one d) (by norm_num) le_rfl

theorem akhcCL5_r_pow_le_half {M : ℕ} (hM : akhcCL5_Md d ≤ M) : akhcCL5_r d ^ M ≤ 1 / 2 :=
  (pow_le_pow_of_le_one (akhcCL5_r_pos d).le (akhcCL5_r_lt_one d).le hM).trans
    (akhcCL5_r_pow_Md d)

end Levels

/-! ## The scale separation at `Lstep` -/

/-- **The scale separation** `osc(Q)·sep(Q, Lstep) ≤ 1/4` on every cube. -/
theorem akhcCL5_scaleSep (d : ℕ) (Q : Homogenization.TriadicCube d) :
    Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffOscillationConstant Q *
      Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffScaleSep Q
        (akhcCL5_Lstep d) ≤ (1 / 4 : ℝ) := by
  rw [Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffOscillationConstant_mul_scaleSep_eq]
  set G := Homogenization.quantitativeCubeCutoffGradientConst d with hGdef
  have hG0 : 0 ≤ G := Homogenization.quantitativeCubeCutoffGradientConst_nonneg d
  have hcB := Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffBound_le_two_pow_card Q
  set Λ := akhcCL5_Lstep d with hΛ
  have hpow : (0 : ℝ) < (3 : ℝ) ^ Λ := by positivity
  have hLlt : ((Λ : ℕ) : ℝ) < (3 : ℝ) ^ Λ := by
    have := Nat.lt_pow_self (by norm_num : 1 < 3) (n := Λ)
    exact_mod_cast this
  have hceil : 32 * (2 : ℝ) ^ d * G ≤ ((Λ : ℕ) : ℝ) := by
    rw [hΛ, akhcCL5_Lstep, Nat.cast_add, Nat.cast_one]
    have := Nat.le_ceil (32 * (2 : ℝ) ^ d * G)
    linarith only [this]
  have h1 : 8 * G * Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffBound Q ≤
      8 * G * (2 : ℝ) ^ d := mul_le_mul_of_nonneg_left hcB (by positivity)
  rw [← div_eq_mul_inv, div_le_iff₀ hpow]
  linarith only [h1, hceil, hLlt]

/-! ## The `Υ^{port}` comparison -/

theorem akhcCL5_ceil_eta (d : ℕ) : ⌈akhcCL5_eta d⌉₊ = d + 1 := by
  unfold akhcCL5_eta
  rw [show (d : ℝ) + 1 = ((d + 1 : ℕ) : ℝ) by push_cast; ring]
  exact Nat.ceil_natCast _

/-- **`Υ^{port}` fits V5's power**: for `K_Ψ ≥ 1`,
`Υ^{port}(d, d+1, ρ, K_Ψ) ≤ c_Υ(d) K_Ψ^{6(d+1)²}`. The exponents are `3(d+1)²` (variance) and
`3(d+1)² + 6(d+1) ≤ 6(d+1)²` (`M⁺` moment). -/
theorem akhcCL5_UpsPort_le (d : ℕ) (hd : 2 ≤ d) {KPsi : ℝ} (hK : 1 ≤ KPsi) :
    akhcRW_UpsPort d (akhcCL5_eta d) (akhcCL5_rho d) KPsi ≤
      akhcCL5_cUps d * KPsi ^ (6 * (d + 1) ^ 2) := by
  have heta := akhcCL5_eta_gt d hd
  have hc := akhcCL5_c_pos d
  have hK0 : 0 ≤ KPsi := by linarith only [hK]
  have hd1 : (1 : ℝ) ≤ (d : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) d
    linarith only [this]
  set η := akhcCL5_eta d with hη
  set P6 := KPsi ^ (6 * (d + 1) ^ 2) with hP6
  have hq : 0 ≤ η / (η - 2) := div_nonneg (by linarith only [heta]) (by linarith only [heta])
  have h3 : (3 : ℝ) ^ (-(2 * akhcCL5_rho d - 2 * (d : ℝ) / η)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hc])
  have hinv : 0 ≤ (1 - (3 : ℝ) ^ (-(2 * akhcCL5_rho d - 2 * (d : ℝ) / η)))⁻¹ :=
    inv_nonneg.2 (by linarith only [h3])
  have hceil := akhcCL5_ceil_eta d
  -- the variance power
  have hpow3 : KPsi ^ (3 * ⌈η⌉₊ ^ 2) ≤ P6 := by
    rw [hceil, hP6]
    exact pow_le_pow_right₀ hK (by nlinarith only)
  -- the `M⁺` powers
  have hrp : KPsi ^ (2 * (3 * (⌈η⌉₊ : ℝ) ^ 2) / η) ≤ KPsi ^ (3 * (d + 1) ^ 2) := by
    rw [← Real.rpow_natCast KPsi (3 * (d + 1) ^ 2)]
    apply Real.rpow_le_rpow_of_exponent_le hK
    rw [hceil, hη, akhcCL5_eta]
    push_cast
    rw [div_le_iff₀ (by linarith only [hd1])]
    have hd3 : (2 : ℝ) ≤ (d : ℝ) + 1 := by
      have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      linarith only [this]
    have := mul_le_mul_of_nonneg_left hd3 (by positivity : (0 : ℝ) ≤ 3 * ((d : ℝ) + 1) ^ 2)
    linarith only [this]
  have hMM : KPsi ^ (3 * ⌈η⌉₊ ^ 2) * KPsi ^ (2 * (3 * (⌈η⌉₊ : ℝ) ^ 2) / η) ≤ P6 := by
    have h1 : KPsi ^ (3 * ⌈η⌉₊ ^ 2) * KPsi ^ (2 * (3 * (⌈η⌉₊ : ℝ) ^ 2) / η) ≤
        KPsi ^ (3 * (d + 1) ^ 2) * KPsi ^ (3 * (d + 1) ^ 2) := by
      rw [hceil] at hrp ⊢
      exact mul_le_mul_of_nonneg_left hrp (pow_nonneg hK0 _)
    rw [← pow_add] at h1
    rw [hP6]
    convert h1 using 2
    ring
  unfold akhcRW_UpsPort akhcRW_UpsVar akhcRW_UpsMM akhcCL5_cUps
  rw [← hη]
  have hv : 128 * ((2 * (d : ℝ)) ^ 2 * (η / (η - 2) * KPsi ^ (3 * ⌈η⌉₊ ^ 2))) ≤
      η / (η - 2) * (128 * (2 * (d : ℝ)) ^ 2) * P6 := by
    have := mul_le_mul_of_nonneg_left hpow3 (mul_nonneg hq (by positivity : (0 : ℝ) ≤
      128 * (2 * (d : ℝ)) ^ 2))
    linarith only [this]
  have hm : η / (η - 2) * KPsi ^ (3 * ⌈η⌉₊ ^ 2) * KPsi ^ (2 * (3 * (⌈η⌉₊ : ℝ) ^ 2) / η) *
      (1 - (3 : ℝ) ^ (-(2 * akhcCL5_rho d - 2 * (d : ℝ) / η)))⁻¹ ≤
      η / (η - 2) * (1 - (3 : ℝ) ^ (-(2 * akhcCL5_rho d - 2 * (d : ℝ) / η)))⁻¹ * P6 := by
    have := mul_le_mul_of_nonneg_left hMM (mul_nonneg hq hinv)
    linarith only [this]
  linarith only [hv, hm]

/-- **The Step 3 floor fits V5's `Υ₁`**: `U ≤ (B c_Υ/ζ) K_Ψ^{6(d+1)²}`, so V5's
`C K_Ψ^{6(d+1)²}/(min{d+1, p_Ψ} - d)` dominates `U` once `C ≥ B c_Υ/ζ` and `d + 1 ≤ p_Ψ`. -/
theorem akhcCL5_U_le (d : ℕ) [NeZero d] (hd : 2 ≤ d) {KPsi : ℝ} (hK : 1 ≤ KPsi) :
    akhcCL5_U d KPsi ≤
      akhcCL5_B d * akhcCL5_cUps d / akhcCL5_zeta d * KPsi ^ (6 * (d + 1) ^ 2) := by
  have h := mul_le_mul_of_nonneg_left (akhcCL5_UpsPort_le d hd hK) (akhcCL5_B_nonneg d)
  have hζ := akhcCL5_zeta_pos d
  unfold akhcCL5_U
  rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hζ]
  linarith only [h]

/-! ## The lag -/

section Lag

variable {L1 L2 : ℝ} (hL1 : 1 ≤ L1) (hL2 : 1 ≤ L2)

include hL1 hL2 in
theorem akhcCL5_lag_lt {n : ℕ} (hn : 1 ≤ n) :
    (SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 n : ℝ) <
      L1 * Real.log (L2 * (n : ℝ)) + 1 := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 : (1 : ℝ) ≤ L2 * (n : ℝ) := by nlinarith only [hL2, hn']
  have h2 : 0 ≤ L1 * Real.log (L2 * (n : ℝ)) :=
    mul_nonneg (by linarith only [hL1]) (Real.log_nonneg h1)
  exact Nat.ceil_lt_add_one h2

include hL1 hL2 in
theorem akhcCL5_lag_mono {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 a ≤
      SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 b := by
  have ha' : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  unfold SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag
  apply Nat.ceil_mono
  apply mul_le_mul_of_nonneg_left _ (by linarith only [hL1])
  apply Real.log_le_log (by nlinarith only [hL2, ha'])
  exact mul_le_mul_of_nonneg_left hab' (by linarith only [hL2])

include hL1 hL2 in
theorem akhcCL5_lag_pos {n : ℕ} (hn : 2 ≤ n) :
    1 ≤ SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 n := by
  have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  unfold SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag
  apply Nat.one_le_iff_ne_zero.2
  apply Nat.pos_iff_ne_zero.1
  apply Nat.ceil_pos.2
  apply mul_pos (by linarith only [hL1])
  exact Real.log_pos (by nlinarith only [hL2, hn'])

include hL1 hL2 in
/-- **The lag grows slowly**: for `1 ≤ K ≤ x` with `4L₁ ≤ K`, `ℓ(x) < ℓ(K) + (x - K)/4 + 1`. -/
theorem akhcCL5_lag_growth {K x : ℕ} (hK1 : 1 ≤ K) (hKL1 : 4 * L1 ≤ (K : ℝ)) (hKx : K ≤ x) :
    (SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 x : ℝ) <
      (SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 K : ℝ) +
        ((x : ℝ) - (K : ℝ)) / 4 + 1 := by
  have hK0 : (0 : ℝ) < (K : ℝ) := by
    have : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK1
    linarith only [this]
  have hKx' : (K : ℝ) ≤ (x : ℝ) := by exact_mod_cast hKx
  have hx0 : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le hK0 hKx'
  have hL20 : (0 : ℝ) < L2 := by linarith only [hL2]
  have hlt := akhcCL5_lag_lt hL1 hL2 (n := x) (by omega)
  have hlog : Real.log (L2 * (x : ℝ)) =
      Real.log (L2 * (K : ℝ)) + Real.log ((x : ℝ) / (K : ℝ)) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
  have hlogle : Real.log ((x : ℝ) / (K : ℝ)) ≤ (x : ℝ) / (K : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hstep : L1 * Real.log ((x : ℝ) / (K : ℝ)) ≤ ((x : ℝ) - (K : ℝ)) / 4 := by
    have h1 : L1 * Real.log ((x : ℝ) / (K : ℝ)) ≤ L1 * ((x : ℝ) / (K : ℝ) - 1) :=
      mul_le_mul_of_nonneg_left hlogle (by linarith only [hL1])
    have h2 : L1 * ((x : ℝ) / (K : ℝ) - 1) = L1 / (K : ℝ) * ((x : ℝ) - (K : ℝ)) := by
      field_simp
    have h3 : L1 / (K : ℝ) ≤ 1 / 4 := by
      rw [div_le_iff₀ hK0]
      linarith only [hKL1]
    have h4 : L1 / (K : ℝ) * ((x : ℝ) - (K : ℝ)) ≤ 1 / 4 * ((x : ℝ) - (K : ℝ)) :=
      mul_le_mul_of_nonneg_right h3 (by linarith only [hKx'])
    linarith only [h1, h2, h4]
  have hceil : L1 * Real.log (L2 * (K : ℝ)) ≤
      (SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 K : ℝ) := Nat.le_ceil _
  rw [hlog, mul_add] at hlt
  linarith only [hlt, hstep, hceil]

end Lag

/-! ## The base scale `k(n)` -/

/-- **The base of the recursion at scale `n`**, `k(n) := max K₀ (⌊n/2⌋ + 1)`. -/
def akhcCL5_k (K0 n : ℕ) : ℕ := max K0 (n / 2 + 1)

/-- **The base scale's properties.** With `4L₁ ≤ K₀`, `4ℓ̄ + 6 ≤ K₀`, `ℓ(K₀) ≤ ℓ̄`,
`n ≥ K₀ + 2ℓ̄ + 4` and `0 ≤ β ≤ 1/2`, the base `k := k(n)` satisfies `K₀ ≤ k < n`,
`k + ℓ(k) + 1 ≤ n`, `βn < k`, `n - K₀ ≤ 3(n - k)` and `n - K₀ ≤ 4(n - k - ℓ(k))`. -/
theorem akhcCL5_k_props {L1 L2 beta : ℝ} (hL1 : 1 ≤ L1) (hL2 : 1 ≤ L2)
    (hbeta : beta ≤ 1 / 2) {K0 lb n : ℕ} (hK0L1 : 4 * L1 ≤ (K0 : ℝ)) (hK0lb : 4 * lb + 6 ≤ K0)
    (hlagK0 : SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 K0 ≤ lb)
    (hn : K0 + 2 * lb + 4 ≤ n) :
    K0 ≤ akhcCL5_k K0 n ∧ akhcCL5_k K0 n < n ∧
      akhcCL5_k K0 n + SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2
        (akhcCL5_k K0 n) + 1 ≤ n ∧
      beta * (n : ℝ) < (akhcCL5_k K0 n : ℝ) ∧
      (n : ℝ) - (K0 : ℝ) ≤ 3 * ((n : ℝ) - (akhcCL5_k K0 n : ℝ)) ∧
      (n : ℝ) - (K0 : ℝ) ≤ 4 * ((n : ℝ) - (akhcCL5_k K0 n : ℝ) -
        (SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 (akhcCL5_k K0 n) : ℝ)) := by
  set k := akhcCL5_k K0 n with hkdef
  set ℓk := SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 k with hℓk
  have hKk : K0 ≤ k := le_max_left _ _
  have hk2 : n / 2 + 1 ≤ k := le_max_right _ _
  have hkn : k < n := max_lt (by omega) (by omega)
  have hgrow := akhcCL5_lag_growth hL1 hL2 (K := K0) (x := k) (by omega) hK0L1 hKk
  have hlagK0' : (SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 K0 : ℝ) ≤
      (lb : ℝ) := by exact_mod_cast hlagK0
  have hK0lb' : 4 * (lb : ℝ) + 6 ≤ (K0 : ℝ) := by exact_mod_cast hK0lb
  have hn' : (K0 : ℝ) + 2 * (lb : ℝ) + 4 ≤ (n : ℝ) := by exact_mod_cast hn
  have hh : ((n : ℝ) - 1) / 2 ≤ ((n / 2 : ℕ) : ℝ) := by
    have h1 : n ≤ 2 * (n / 2) + 1 := by omega
    have h2 : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast h1
    linarith only [h2]
  have hh2 : ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) / 2 := by
    have h1 : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
    have h2 : 2 * ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
    linarith only [h2]
  have hk2' : ((n / 2 : ℕ) : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hk2
  have hKk' : (K0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hKk
  -- the two cases of the maximum
  have hcase : (k : ℝ) = (K0 : ℝ) ∨ (k : ℝ) ≤ (n : ℝ) / 2 + 1 := by
    rcases le_total K0 (n / 2 + 1) with h | h
    · right
      have : k = n / 2 + 1 := max_eq_right h
      rw [this]
      push_cast
      linarith only [hh2]
    · left
      exact_mod_cast max_eq_left h
  have hδ : (n : ℝ) - (K0 : ℝ) ≤ 4 * ((n : ℝ) - (k : ℝ) - (ℓk : ℝ)) := by
    rcases hcase with h | h
    · rw [h] at hgrow ⊢
      linarith only [hgrow, hlagK0', hn']
    · linarith only [hgrow, hlagK0', hn', h, hK0lb', hKk']
  have hthird : (n : ℝ) - (K0 : ℝ) ≤ 3 * ((n : ℝ) - (k : ℝ)) := by
    rcases hcase with h | h
    · rw [h]
      linarith only [hn']
    · linarith only [h, hK0lb', hn']
  refine ⟨hKk, hkn, ?_, ?_, hthird, hδ⟩
  · have h1 : (k : ℝ) + (ℓk : ℝ) + 1 ≤ (n : ℝ) := by linarith only [hδ, hn']
    exact_mod_cast h1
  · have h1 : beta * (n : ℝ) ≤ (n : ℝ) / 2 := by
      have := mul_le_mul_of_nonneg_right hbeta (Nat.cast_nonneg (α := ℝ) n)
      linarith only [this]
    linarith only [h1, hh, hk2']

/-- **The per-scale windows** above the base: for `n' > k ≥ K₀` (`4L₁ ≤ K₀`,
`4ℓ̄ + 4 ≤ K₀`, `ℓ(K₀) ≤ ℓ̄`) and `β ≤ 1/2`, `βn' < n' - ℓ(n')`. -/
theorem akhcCL5_window {L1 L2 beta : ℝ} (hL1 : 1 ≤ L1) (hL2 : 1 ≤ L2)
    (hbeta : beta ≤ 1 / 2) {K0 lb n : ℕ} (hK0L1 : 4 * L1 ≤ (K0 : ℝ)) (hK0lb : 4 * lb + 6 ≤ K0)
    (hlagK0 : SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 K0 ≤ lb)
    (hn : K0 ≤ n) :
    beta * (n : ℝ) <
      (n : ℝ) - (SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 n : ℝ) := by
  have hgrow := akhcCL5_lag_growth hL1 hL2 (K := K0) (x := n) (by omega) hK0L1 hn
  have hlagK0' : (SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 K0 : ℝ) ≤
      (lb : ℝ) := by exact_mod_cast hlagK0
  have hK0lb' : 4 * (lb : ℝ) + 6 ≤ (K0 : ℝ) := by exact_mod_cast hK0lb
  have hn' : (K0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 : beta * (n : ℝ) ≤ (n : ℝ) / 2 := by
    have := mul_le_mul_of_nonneg_right hbeta (Nat.cast_nonneg (α := ℝ) n)
    linarith only [this]
  linarith only [h1, hgrow, hlagK0', hK0lb', hn']

/-! ## The source smallness from V5's `ω_m²` binder -/

theorem akhcCL5_cUps_nonneg (d : ℕ) (hd : 2 ≤ d) : 0 ≤ akhcCL5_cUps d := by
  have heta := akhcCL5_eta_gt d hd
  have hc := akhcCL5_c_pos d
  have h3 : (3 : ℝ) ^ (-(2 * akhcCL5_rho d - 2 * (d : ℝ) / akhcCL5_eta d)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hc])
  have h4 : 0 ≤ (1 - (3 : ℝ) ^ (-(2 * akhcCL5_rho d - 2 * (d : ℝ) / akhcCL5_eta d)))⁻¹ :=
    inv_nonneg.2 (by linarith only [h3])
  have h5 : 0 ≤ akhcCL5_eta d / (akhcCL5_eta d - 2) :=
    div_nonneg (by linarith only [heta]) (by linarith only [heta])
  unfold akhcCL5_cUps
  positivity

/-- **V5's `ω_m²` binder gives the source smallness** `B Υ^{port} ω_m² ≤ ζε/2`, once
`C ≥ 2 B c_Υ/(ζε)` (this is where `Υ^{port} ≤ c_Υ K_Ψ^{6(d+1)²}` is used). -/
theorem akhcCL5_hS_of_omega (d : ℕ) [NeZero d] (hd : 2 ≤ d) {C KPsi pPsi om : ℝ}
    (hK : 1 ≤ KPsi) (hpPsi : (d : ℝ) + 1 ≤ pPsi)
    (hC : 2 * akhcCL5_B d * akhcCL5_cUps d / (akhcCL5_zeta d * akhcCL5_eps d) ≤ C)
    (hC1 : 1 ≤ C)
    (hom : om ^ 2 ≤ (C * KPsi ^ (6 * (d + 1) ^ 2) / (min ((d : ℝ) + 1) pPsi - (d : ℝ)))⁻¹) :
    akhcCL5_B d * akhcRW_UpsPort d (akhcCL5_eta d) (akhcCL5_rho d) KPsi * om ^ 2 ≤
      akhcCL5_zeta d * akhcCL5_eps d / 2 := by
  have hmin : min ((d : ℝ) + 1) pPsi - (d : ℝ) = 1 := by rw [min_eq_left hpPsi]; ring
  rw [hmin, div_one] at hom
  have hUps := akhcCL5_UpsPort_le d hd hK
  have hB := akhcCL5_B_nonneg d
  have hcU := akhcCL5_cUps_nonneg d hd
  have hζε : 0 < akhcCL5_zeta d * akhcCL5_eps d :=
    mul_pos (akhcCL5_zeta_pos d) (akhcCL5_eps_pos d)
  have hC0 : 0 < C := by linarith only [hC1]
  set Kp := KPsi ^ (6 * (d + 1) ^ 2) with hKp
  have hKp0 : 0 < Kp := pow_pos (by linarith only [hK]) _
  have hom0 : 0 ≤ om ^ 2 := sq_nonneg om
  have h1 : C * Kp * om ^ 2 ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hom (by positivity : (0 : ℝ) ≤ C * Kp)
    rwa [mul_inv_cancel₀ (by positivity)] at this
  have h2 : akhcCL5_B d * akhcRW_UpsPort d (akhcCL5_eta d) (akhcCL5_rho d) KPsi * om ^ 2 ≤
      akhcCL5_B d * (akhcCL5_cUps d * Kp) * om ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hUps hB) hom0
  have h3 : akhcCL5_B d * (akhcCL5_cUps d * Kp) * om ^ 2 =
      akhcCL5_B d * akhcCL5_cUps d / C * (C * Kp * om ^ 2) := by
    field_simp
  have h4 : akhcCL5_B d * akhcCL5_cUps d / C * (C * Kp * om ^ 2) ≤
      akhcCL5_B d * akhcCL5_cUps d / C :=
    mul_le_of_le_one_right (by positivity) h1
  have h5 : akhcCL5_B d * akhcCL5_cUps d / C ≤ akhcCL5_zeta d * akhcCL5_eps d / 2 := by
    rw [div_le_iff₀ hC0]
    rw [div_le_iff₀ hζε] at hC
    nlinarith only [hC, hζε, hC0]
  linarith only [h2, h3, h4, h5]

end

end SuperdiffusionCLT.AKHC61.Step3
