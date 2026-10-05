/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.Step3.ClosureParameters

/-!
# Closing Step 3 on the V5 range, part 2: the scales, the tails, and the closure

* The scales: `ℓ̄ := ℓ(m + 4m₀)`, the sum base `K₀ := m + 3m₀ + ℓ̄`, the pre-phase
  `M := M_d + 4ℓ̄ + 4`, the tail level `T := ζ ε r^M`, the delay `E`, the lag parameter
  `ℓ_lem := 2ℓ̄ + 4 + E`, and the start `N₀` of `akhcDW_decay`.
* With `Y := log X` from V5's threshold: `ℓ̄ ≤ 4L₁Y`, `log K₀ ≤ 7L₁Y`, `M ≤ (M_d + 20)L₁Y`.
* The two low-scale tails of the recursion are at most `(T/2) r^{n-K₀}` once `n - K₀ ≥ E`
  (`akhcCL5_tail3_le`, `akhcCL5_tail2_le`).
* **The closure** `akhcCL5_decay_of_scales`. On V5's range it applies the bridge
  `akhcCL_recursion_range` at every scale `n ≥ K₀ + Z` with base `k(n)`, and then
  `akhcDW_decay`. Its inputs are Step 2's `Θ_{m+3m₀} ≤ 1 + σ`, `σ ≤ σ_d`, the source smallness
  `B Υ^{port} ω_m² ≤ ζε/2`, and the scale conditions `2L₁ ≤ m₀`, `16D ≤ m₀`, `Lstep ≤ m₀`,
  `N₀ ≤ m + 4m₀`. `Step3/ClosureThreshold.lean` derives all four from V5's binders.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.Step3

noncomputable section

/-! ## The scales -/

/-- `ℓ̄ := ℓ(m + 4m₀)`, the lag at the end of the window. -/
def akhcCL5_lbar (L1 L2 : ℝ) (m m0 : ℕ) : ℕ :=
  SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 (m + 4 * m0)

/-- The sum base `K₀ := m + 3m₀ + ℓ̄`. -/
def akhcCL5_K0 (L1 L2 : ℝ) (m m0 : ℕ) : ℕ := m + 3 * m0 + akhcCL5_lbar L1 L2 m m0

/-- The pre-phase `M := M_d + 4ℓ̄ + 4`. -/
def akhcCL5_M (d : ℕ) [NeZero d] (L1 L2 : ℝ) (m m0 : ℕ) : ℕ :=
  akhcCL5_Md d + 4 * akhcCL5_lbar L1 L2 m m0 + 4

/-- The tail level `T := ζ ε r^M`. -/
def akhcCL5_T (d : ℕ) [NeZero d] (M : ℕ) : ℝ :=
  akhcCL5_zeta d * akhcCL5_eps d * akhcCL5_r d ^ M

/-- The logarithmic size of the low-scale tails,
`log((6B+1)/T) + 36 log K_{Ψ_S} + 2 log H + 2D log K₀`. -/
def akhcCL5_Lsum (d : ℕ) [NeZero d] (D H KPsiS : ℝ) (M K0 : ℕ) : ℝ :=
  Real.log ((6 * akhcCL5_B d + 1) / akhcCL5_T d M) + 36 * Real.log KPsiS + 2 * Real.log H +
    2 * D * Real.log (K0 : ℝ)

/-- The delay `E := ⌈48(d+1) Lsum / log 3⌉` after which the tails are below `T r^{n-K₀}/2`. -/
def akhcCL5_E (d : ℕ) [NeZero d] (L1 L2 D H KPsiS : ℝ) (m m0 : ℕ) : ℕ :=
  ⌈48 * ((d : ℝ) + 1) / Real.log 3 *
    akhcCL5_Lsum d D H KPsiS (akhcCL5_M d L1 L2 m m0) (akhcCL5_K0 L1 L2 m m0)⌉₊

/-- The lag parameter of `akhcDW_decay`, `ℓ_lem := 2ℓ̄ + 4 + E`. -/
def akhcCL5_ell (d : ℕ) [NeZero d] (L1 L2 D H KPsiS : ℝ) (m m0 : ℕ) : ℕ :=
  2 * akhcCL5_lbar L1 L2 m m0 + 4 + akhcCL5_E d L1 L2 D H KPsiS m m0

/-- **The start of the decay**, `N₀ := akhcDW_N0 θ B B w Lstep K₀ ℓ_lem M`. -/
def akhcCL5_N0 (d : ℕ) [NeZero d] (L1 L2 D H KPsiS : ℝ) (m m0 : ℕ) : ℕ :=
  akhcDW_N0 (akhcCL5_theta d) (akhcCL5_B d) (akhcCL5_B d) (akhcCL5_w d) (akhcCL5_Lstep d)
    (akhcCL5_K0 L1 L2 m m0) (akhcCL5_ell d L1 L2 D H KPsiS m m0) (akhcCL5_M d L1 L2 m m0)

theorem akhcCL5_T_pos (d : ℕ) [NeZero d] (M : ℕ) : 0 < akhcCL5_T d M := by
  have h1 := akhcCL5_zeta_pos d
  have h2 := akhcCL5_eps_pos d
  have h3 := akhcCL5_r_pos d
  unfold akhcCL5_T
  positivity

/-! ## The scale conditions from `Y` -/

section FromY

variable {L1 L2 D H KPsiS C Y : ℝ} {m m0 : ℕ}

/-- `ℓ̄ ≤ 4 L₁ Y`. -/
theorem akhcCL5_lbar_le (hL1 : 1 ≤ L1) (hL2 : 1 ≤ L2) (hD : 0 ≤ D) (hH : 1 ≤ H)
    (hKS : 1 ≤ KPsiS) (hC : 1 ≤ C) (hm0 : 1 ≤ m0)
    (hY : C * (L1 * Real.log (2 * L2) + D + Real.log (H + KPsiS)) +
      Real.log ((m : ℝ) + (m0 : ℝ) + 1) ≤ Y) (hY1 : 1 ≤ Y) :
    (akhcCL5_lbar L1 L2 m m0 : ℝ) ≤ 4 * (L1 * Y) := by
  have hlt := akhcCL5_lag_lt hL1 hL2 (n := m + 4 * m0) (by omega)
  have hm' := Nat.cast_nonneg (α := ℝ) m
  have hm0' : (1 : ℝ) ≤ (m0 : ℝ) := by exact_mod_cast hm0
  have hmm : (0 : ℝ) < (m : ℝ) + (m0 : ℝ) + 1 := by linarith only [hm', hm0']
  have hlog : Real.log (L2 * ((m + 4 * m0 : ℕ) : ℝ)) ≤
      Real.log (2 * L2) + 1 + Real.log ((m : ℝ) + (m0 : ℝ) + 1) := by
    have h1 : L2 * ((m + 4 * m0 : ℕ) : ℝ) ≤ 2 * L2 * (2 * ((m : ℝ) + (m0 : ℝ) + 1)) := by
      push_cast
      nlinarith only [hL2, hm', hm0']
    have h2 := Real.log_le_log (by push_cast; nlinarith only [hL2, hm', hm0']) h1
    rw [Real.log_mul (x := 2 * L2) (y := 2 * ((m : ℝ) + (m0 : ℝ) + 1))
        (by linarith only [hL2]) (by positivity),
      Real.log_mul (x := 2) (y := (m : ℝ) + (m0 : ℝ) + 1) (by norm_num) hmm.ne'] at h2
    have h3 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith only [this]
    linarith only [h2, h3]
  have hl2L2 : 0 ≤ Real.log (2 * L2) := Real.log_nonneg (by linarith only [hL2])
  have hlHK : 0 ≤ Real.log (H + KPsiS) := Real.log_nonneg (by linarith only [hH, hKS])
  have hlogm : 0 ≤ Real.log ((m : ℝ) + (m0 : ℝ) + 1) := Real.log_nonneg (by linarith only [hm', hm0'])
  have hq0 : 0 ≤ L1 * Real.log (2 * L2) + D + Real.log (H + KPsiS) := by positivity
  have hCq := mul_le_mul_of_nonneg_right hC hq0
  have hA : L1 * Real.log (2 * L2) ≤ Y := by linarith only [hCq, hY, hD, hlHK, hlogm]
  have hB : L1 * Real.log ((m : ℝ) + (m0 : ℝ) + 1) ≤ L1 * Y :=
    mul_le_mul_of_nonneg_left (by linarith only [hCq, hY, hq0]) (by linarith only [hL1])
  have hYL : Y ≤ L1 * Y := by
    have := mul_le_mul_of_nonneg_right hL1 (by linarith only [hY1] : (0 : ℝ) ≤ Y)
    linarith only [this]
  have hLY : L1 ≤ L1 * Y := by
    have := mul_le_mul_of_nonneg_left hY1 (by linarith only [hL1] : (0 : ℝ) ≤ L1)
    linarith only [this]
  have hL : L1 * Real.log (L2 * ((m + 4 * m0 : ℕ) : ℝ)) ≤
      L1 * Real.log (2 * L2) + L1 + L1 * Real.log ((m : ℝ) + (m0 : ℝ) + 1) := by
    have := mul_le_mul_of_nonneg_left hlog (by linarith only [hL1] : (0 : ℝ) ≤ L1)
    linarith only [this]
  unfold akhcCL5_lbar
  linarith only [hlt, hL, hA, hB, hYL, hLY, hL1]

/-- `log K₀ ≤ 7 L₁ Y`. -/
theorem akhcCL5_logK0_le (hL1 : 1 ≤ L1) (hL2 : 1 ≤ L2) (hD : 0 ≤ D) (hH : 1 ≤ H)
    (hKS : 1 ≤ KPsiS) (hC : 1 ≤ C) (hm0 : 1 ≤ m0)
    (hY : C * (L1 * Real.log (2 * L2) + D + Real.log (H + KPsiS)) +
      Real.log ((m : ℝ) + (m0 : ℝ) + 1) ≤ Y) (hY1 : 1 ≤ Y) :
    Real.log (akhcCL5_K0 L1 L2 m m0 : ℝ) ≤ 7 * (L1 * Y) := by
  have hlb := akhcCL5_lbar_le hL1 hL2 hD hH hKS hC hm0 hY hY1
  have hm' := Nat.cast_nonneg (α := ℝ) m
  have hm0' : (1 : ℝ) ≤ (m0 : ℝ) := by exact_mod_cast hm0
  have hlb0 := Nat.cast_nonneg (α := ℝ) (akhcCL5_lbar L1 L2 m m0)
  set lb := (akhcCL5_lbar L1 L2 m m0 : ℝ) with hlbdef
  have hK0 : (akhcCL5_K0 L1 L2 m m0 : ℝ) = (m : ℝ) + 3 * (m0 : ℝ) + lb := by
    unfold akhcCL5_K0
    push_cast
    ring
  have hle : (m : ℝ) + 3 * (m0 : ℝ) + lb ≤ ((m : ℝ) + (m0 : ℝ) + 1) * (3 + lb) := by
    nlinarith only [hm', hm0', hlb0]
  rw [hK0]
  have h1 := Real.log_le_log (by linarith only [hm', hm0', hlb0]) hle
  rw [Real.log_mul (by linarith only [hm', hm0']) (by linarith only [hlb0])] at h1
  have h2 : Real.log (3 + lb) ≤ 3 + lb - 1 := Real.log_le_sub_one_of_pos (by linarith only [hlb0])
  have hl2L2 : 0 ≤ Real.log (2 * L2) := Real.log_nonneg (by linarith only [hL2])
  have hlHK : 0 ≤ Real.log (H + KPsiS) := Real.log_nonneg (by linarith only [hH, hKS])
  have hq0 : 0 ≤ L1 * Real.log (2 * L2) + D + Real.log (H + KPsiS) := by positivity
  have hCq : 0 ≤ C * (L1 * Real.log (2 * L2) + D + Real.log (H + KPsiS)) := by positivity
  have hYL : Y ≤ L1 * Y := by
    have := mul_le_mul_of_nonneg_right hL1 (by linarith only [hY1] : (0 : ℝ) ≤ Y)
    linarith only [this]
  linarith only [h1, h2, hY, hCq, hlb, hYL, hY1]

end FromY

section FromYd0

variable {d : ℕ} [NeZero d] {L1 L2 D H KPsiS C Y : ℝ} {m m0 : ℕ}

/-- `M ≤ (M_d + 20) L₁ Y`. -/
theorem akhcCL5_M_le (hL1 : 1 ≤ L1) (hL2 : 1 ≤ L2) (hD : 0 ≤ D) (hH : 1 ≤ H)
    (hKS : 1 ≤ KPsiS) (hC : 1 ≤ C) (hm0 : 1 ≤ m0)
    (hY : C * (L1 * Real.log (2 * L2) + D + Real.log (H + KPsiS)) +
      Real.log ((m : ℝ) + (m0 : ℝ) + 1) ≤ Y) (hY1 : 1 ≤ Y) :
    (akhcCL5_M d L1 L2 m m0 : ℝ) ≤ ((akhcCL5_Md d : ℝ) + 20) * (L1 * Y) := by
  have hlb := akhcCL5_lbar_le hL1 hL2 hD hH hKS hC hm0 hY hY1
  have hV : 1 ≤ L1 * Y := by nlinarith only [hL1, hY1]
  have hMd := Nat.cast_nonneg (α := ℝ) (akhcCL5_Md d)
  have h1 := mul_le_mul_of_nonneg_left hV hMd
  unfold akhcCL5_M
  push_cast
  linarith only [hlb, hV, h1]

end FromYd0

/-! ## The low-scale tails -/

/-- `P 3^{-x} ≤ T 3^{-y}` once `P ≤ e^L` and `L - log T ≤ (x - y) log 3`. -/
theorem akhcCL5_exp_le {P T x y L : ℝ} (hT : 0 < T) (hPL : P ≤ Real.exp L)
    (h : L - Real.log T ≤ (x - y) * Real.log 3) :
    P * (3 : ℝ) ^ (-x) ≤ T * (3 : ℝ) ^ (-y) := by
  rw [Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos (by norm_num)]
  calc P * Real.exp (Real.log 3 * -x) ≤ Real.exp L * Real.exp (Real.log 3 * -x) :=
        mul_le_mul_of_nonneg_right hPL (Real.exp_pos _).le
    _ = Real.exp (L + Real.log 3 * -x) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (Real.log T + Real.log 3 * -y) := by
        apply Real.exp_le_exp.2
        linarith only [h]
    _ = T * Real.exp (Real.log 3 * -y) := by rw [Real.exp_add, Real.exp_log hT]

theorem akhcCL5_log3_ge : (1 / 2 : ℝ) ≤ Real.log 3 := by
  have h2 := Real.log_two_gt_d9
  have h23 : Real.log 2 ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
  linarith only [h2, h23]

theorem akhcCL5_r_pow_sub (d : ℕ) [NeZero d] {K0 n : ℕ} (hKn : K0 ≤ n) :
    akhcCL5_r d ^ (n - K0) = (3 : ℝ) ^ (-(akhcCL5_kappa d * ((n : ℝ) - (K0 : ℝ)))) := by
  rw [akhcCL5_r_pow, Nat.cast_sub hKn]

/-- **The `3^{-(1-2s')(n-k)}` tail**: `B 3^{-(1-2s')(n-k)} ≤ (T/2) r^{n-K₀}` when
`n - K₀ ≤ 3(n-k)` and `n - K₀ ≥ 48(d+1) Lsum / log 3`. -/
theorem akhcCL5_tail3_le (d : ℕ) [NeZero d] {D H KPsiS : ℝ} (hH : 1 ≤ H) (hD : 0 ≤ D)
    (hKS : 1 ≤ KPsiS) {M K0 n k : ℕ} (hK0 : 1 ≤ K0) (hKn : K0 ≤ n)
    (hthird : (n : ℝ) - (K0 : ℝ) ≤ 3 * ((n : ℝ) - (k : ℝ)))
    (hE : 48 * ((d : ℝ) + 1) / Real.log 3 * akhcCL5_Lsum d D H KPsiS M K0 ≤ (n : ℝ) - (K0 : ℝ)) :
    akhcCL5_B d * (3 : ℝ) ^ (-(1 - 2 * akhcCL5_s d) * ((n : ℝ) - (k : ℝ))) ≤
      akhcCL5_T d M / 2 * akhcCL5_r d ^ (n - K0) := by
  have hB := akhcCL5_B_nonneg d
  have hT := akhcCL5_T_pos d M
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hd0 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hKn' : (K0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hKn
  have hκ := akhcCL5_kappa_le d
  rw [akhcCL5_r_pow_sub d hKn, akhcCL5_one_sub_two_s]
  set a := (n : ℝ) - (K0 : ℝ) with ha
  have ha0 : 0 ≤ a := by linarith only [hKn']
  -- the logarithmic size
  have hLs : Real.log ((6 * akhcCL5_B d + 1) / akhcCL5_T d M) ≤
      akhcCL5_Lsum d D H KPsiS M K0 := by
    have h1 : 0 ≤ Real.log KPsiS := Real.log_nonneg hKS
    have h2 : 0 ≤ Real.log H := Real.log_nonneg hH
    have h3 : 0 ≤ Real.log (K0 : ℝ) := Real.log_nonneg (by exact_mod_cast hK0)
    unfold akhcCL5_Lsum
    have h4 : 0 ≤ 2 * D * Real.log (K0 : ℝ) := by positivity
    linarith only [h1, h2, h4]
  have hE' : akhcCL5_Lsum d D H KPsiS M K0 * (48 * ((d : ℝ) + 1)) ≤ a * Real.log 3 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hl3] at hE
    linarith only [hE]
  have hx : a / (12 * ((d : ℝ) + 1)) ≤ 1 / (4 * (d : ℝ) + 4) * ((n : ℝ) - (k : ℝ)) := by
    rw [div_le_iff₀ (by positivity)]
    have : 1 / (4 * (d : ℝ) + 4) * ((n : ℝ) - (k : ℝ)) * (12 * ((d : ℝ) + 1)) =
        3 * ((n : ℝ) - (k : ℝ)) := by field_simp; ring
    rw [this]
    exact hthird
  have hy : akhcCL5_kappa d * a ≤ a / (16 * ((d : ℝ) + 1)) := by
    have := mul_le_mul_of_nonneg_right hκ ha0
    rw [div_eq_mul_one_div a]
    linarith only [this]
  have hxy : a / (48 * ((d : ℝ) + 1)) ≤
      1 / (4 * (d : ℝ) + 4) * ((n : ℝ) - (k : ℝ)) - akhcCL5_kappa d * a := by
    have : a / (48 * ((d : ℝ) + 1)) = a / (12 * ((d : ℝ) + 1)) - a / (16 * ((d : ℝ) + 1)) := by
      field_simp; ring
    linarith only [this, hx, hy]
  have hmain := akhcCL5_exp_le (P := 2 * akhcCL5_B d) (T := akhcCL5_T d M)
    (x := 1 / (4 * (d : ℝ) + 4) * ((n : ℝ) - (k : ℝ))) (y := akhcCL5_kappa d * a)
    (L := Real.log (6 * akhcCL5_B d + 1)) hT (by
      rw [Real.exp_log (by positivity)]
      linarith only [hB]) (by
      rw [← Real.log_div (by positivity) hT.ne']
      have h1 : a / (48 * ((d : ℝ) + 1)) * Real.log 3 ≤
          (1 / (4 * (d : ℝ) + 4) * ((n : ℝ) - (k : ℝ)) - akhcCL5_kappa d * a) * Real.log 3 :=
        mul_le_mul_of_nonneg_right hxy hl3.le
      have h2 : akhcCL5_Lsum d D H KPsiS M K0 ≤ a / (48 * ((d : ℝ) + 1)) * Real.log 3 := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        linarith only [hE']
      linarith only [h1, h2, hLs])
  have he : -(1 / (4 * (d : ℝ) + 4)) * ((n : ℝ) - (k : ℝ)) =
      -(1 / (4 * (d : ℝ) + 4) * ((n : ℝ) - (k : ℝ))) := by ring
  rw [he]
  linarith only [hmain]

/-- **The (P2′) tail**: `B · 3K_{Ψ_S}^{36}(H n^D)² 3^{-2(ρ-γ)(n-(k₀-1))}/(min{3,p_{Ψ_S}}-2) ≤
(T/2) r^{n-K₀}` when `γ ≤ 1/2`, `3 ≤ p_{Ψ_S}`, `48D ≤ K₀`, `n - K₀ ≤ 4(n - (k₀-1))` and
`n - K₀ ≥ 48(d+1) Lsum / log 3`. -/
theorem akhcCL5_tail2_le (d : ℕ) [NeZero d] (hd : 2 ≤ d) {gamma D H KPsiS pPsiS : ℝ}
    (hgamma : gamma ≤ 1 / 2) (hH : 1 ≤ H) (hD : 0 ≤ D) (hKS : 1 ≤ KPsiS) (hpS : 3 ≤ pPsiS)
    {M K0 n k0 : ℕ} (hK0 : 1 ≤ K0) (hKn : K0 ≤ n) (h48 : 48 * D ≤ (K0 : ℝ))
    (hδ : (n : ℝ) - (K0 : ℝ) ≤ 4 * ((n : ℝ) - ((k0 : ℝ) - 1)))
    (hE : 48 * ((d : ℝ) + 1) / Real.log 3 * akhcCL5_Lsum d D H KPsiS M K0 ≤ (n : ℝ) - (K0 : ℝ)) :
    akhcCL5_B d * (3 * KPsiS ^ 36 * (H * (n : ℝ) ^ D) ^ (2 : ℝ) *
        (3 : ℝ) ^ (-2 * (akhcCL5_rho d - gamma) * ((n : ℝ) - ((k0 : ℝ) - 1))) /
          (min 3 pPsiS - 2)) ≤
      akhcCL5_T d M / 2 * akhcCL5_r d ^ (n - K0) := by
  have hB := akhcCL5_B_nonneg d
  have hT := akhcCL5_T_pos d M
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hl3' := akhcCL5_log3_ge
  have hK0' : (1 : ℝ) ≤ (K0 : ℝ) := by exact_mod_cast hK0
  have hKn' : (K0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hKn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith only [hK0', hKn']
  have hκ := akhcCL5_kappa_le_small d hd
  have hρ := akhcCL5_rho_ge d hd
  have hmin : min 3 pPsiS - 2 = 1 := by rw [min_eq_left hpS]; norm_num
  rw [hmin, div_one, akhcCL5_r_pow_sub d hKn]
  set a := (n : ℝ) - (K0 : ℝ) with ha
  have ha0 : 0 ≤ a := by linarith only [hKn']
  set x := 2 * (akhcCL5_rho d - gamma) * ((n : ℝ) - ((k0 : ℝ) - 1)) with hx
  have hx' : a / 6 ≤ x := by
    have h1 : 0 ≤ (n : ℝ) - ((k0 : ℝ) - 1) := by linarith only [hδ, ha0]
    have h2 : 2 / 3 ≤ 2 * (akhcCL5_rho d - gamma) := by linarith only [hρ, hgamma]
    have h3 := mul_le_mul_of_nonneg_right h2 h1
    rw [hx]
    linarith only [h3, hδ]
  have hy : akhcCL5_kappa d * a ≤ a / 48 := by
    have := mul_le_mul_of_nonneg_right hκ ha0
    linarith only [this]
  -- the logarithm of `n`
  have hlogn : Real.log (n : ℝ) ≤ Real.log (K0 : ℝ) + a / (K0 : ℝ) := by
    have h1 : Real.log ((n : ℝ) / (K0 : ℝ)) ≤ (n : ℝ) / (K0 : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div hn0.ne' (by positivity)] at h1
    have h2 : (n : ℝ) / (K0 : ℝ) - 1 = a / (K0 : ℝ) := by
      rw [ha]; field_simp
    linarith only [h1, h2]
  have hDa : 2 * D * (a / (K0 : ℝ)) ≤ a / 24 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    have := mul_le_mul_of_nonneg_right h48 ha0
    linarith only [this]
  -- the prefactor as an exponential
  set L := Real.log (6 * akhcCL5_B d + 1) + 36 * Real.log KPsiS + 2 * Real.log H +
    2 * D * Real.log (n : ℝ) with hL
  have hHn : 0 < H * (n : ℝ) ^ D := mul_pos (by linarith only [hH]) (Real.rpow_pos_of_pos hn0 _)
  have hKS0 : 0 < KPsiS := by linarith only [hKS]
  have hK36 : Real.exp (36 * Real.log KPsiS) = KPsiS ^ 36 := by
    have h1 : Real.log (KPsiS ^ 36) = 36 * Real.log KPsiS := by
      rw [Real.log_pow]; norm_num
    rw [← h1, Real.exp_log (by positivity)]
  have hHnD : (H * (n : ℝ) ^ D) ^ (2 : ℝ) =
      Real.exp (2 * Real.log H) * Real.exp (2 * D * Real.log (n : ℝ)) := by
    rw [Real.rpow_def_of_pos hHn,
      Real.log_mul (by linarith only [hH]) (Real.rpow_pos_of_pos hn0 _).ne',
      Real.log_rpow hn0, ← Real.exp_add]
    congr 1
    ring
  have hQ : (6 * akhcCL5_B d + 1) * KPsiS ^ 36 * (H * (n : ℝ) ^ D) ^ (2 : ℝ) = Real.exp L := by
    rw [hL, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log (by positivity), hK36, hHnD]
    ring
  have hPL : 2 * (akhcCL5_B d * (3 * KPsiS ^ 36 * (H * (n : ℝ) ^ D) ^ (2 : ℝ))) ≤ Real.exp L := by
    rw [← hQ]
    have h1 : 0 ≤ KPsiS ^ 36 * (H * (n : ℝ) ^ D) ^ (2 : ℝ) :=
      mul_nonneg (pow_nonneg (by linarith only [hKS]) _) (Real.rpow_nonneg hHn.le _)
    have h2 : 6 * akhcCL5_B d ≤ 6 * akhcCL5_B d + 1 := by linarith only
    have h3 := mul_le_mul_of_nonneg_right h2 h1
    linarith only [h3]
  have hLs : L - Real.log (akhcCL5_T d M) ≤ akhcCL5_Lsum d D H KPsiS M K0 + a / 24 := by
    have h1 : 2 * D * Real.log (n : ℝ) ≤ 2 * D * Real.log (K0 : ℝ) + 2 * D * (a / (K0 : ℝ)) := by
      have := mul_le_mul_of_nonneg_left hlogn (by positivity : (0 : ℝ) ≤ 2 * D)
      linarith only [this]
    unfold akhcCL5_Lsum
    rw [Real.log_div (by positivity) hT.ne', hL]
    linarith only [h1, hDa]
  have hE' : akhcCL5_Lsum d D H KPsiS M K0 ≤ a * Real.log 3 / 48 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hl3] at hE
    have h1 : 0 ≤ a * Real.log 3 := mul_nonneg ha0 hl3.le
    have h2 : (1 : ℝ) ≤ (d : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) d
      linarith only [this]
    by_cases hLs0 : akhcCL5_Lsum d D H KPsiS M K0 ≤ 0
    · linarith only [hLs0, h1]
    · push Not at hLs0
      have h3 : akhcCL5_Lsum d D H KPsiS M K0 * 48 ≤
          akhcCL5_Lsum d D H KPsiS M K0 * (48 * ((d : ℝ) + 1)) := by
        have := mul_le_mul_of_nonneg_left h2 (by linarith only [hLs0] :
          (0 : ℝ) ≤ akhcCL5_Lsum d D H KPsiS M K0 * 48)
        linarith only [this]
      linarith only [h3, hE]
  have hmain := akhcCL5_exp_le (P := 2 * (akhcCL5_B d * (3 * KPsiS ^ 36 *
      (H * (n : ℝ) ^ D) ^ (2 : ℝ)))) (x := x) (y := akhcCL5_kappa d * a) hT hPL (by
    have h1 : a * Real.log 3 / 48 + a / 24 ≤ (a / 6 - a / 48) * Real.log 3 := by
      have := mul_le_mul_of_nonneg_left hl3' ha0
      have he : (a / 6 - a / 48) * Real.log 3 = 7 / 48 * (a * Real.log 3) := by ring
      rw [he]
      linarith only [this, ha0]
    have h2 : (a / 6 - a / 48) * Real.log 3 ≤ (x - akhcCL5_kappa d * a) * Real.log 3 :=
      mul_le_mul_of_nonneg_right (by linarith only [hx', hy]) hl3.le
    linarith only [hLs, hE', h1, h2])
  have he : -2 * (akhcCL5_rho d - gamma) * ((n : ℝ) - ((k0 : ℝ) - 1)) = -x := by rw [hx]; ring
  rw [he]
  linarith only [hmain]

/-! ## The closure from explicit scale conditions -/

theorem akhcCL5_unit (d : ℕ) [NeZero d] :
    Homogenization.vecNormSq
      (Pi.single (⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩ : Fin d) (1 : ℝ) :
        Homogenization.Vec d) = 1 := by
  rw [Homogenization.vecNormSq, Homogenization.vecDot,
    Finset.sum_eq_single (⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩ : Fin d)]
  · simp
  · intro j _ hij
    rw [Pi.single_eq_of_ne hij, zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ _) hi

section Closure

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

/-- **Step 3 from explicit scale conditions.** On V5's range, given Step 2's
`Θ_{m+3m₀} ≤ 1 + σ` with `σ ≤ σ_d`, the source smallness `B Υ^{port} ω_m² ≤ ζε/2`, and the
scale conditions `2L₁ ≤ m₀`, `16D ≤ m₀`, `Lstep ≤ m₀`, `N₀ ≤ m + 4m₀`:
`Θ_n - 1 ≤ U ω_m² + 1 · 3^{-κ(d)(n-m-4m₀)}` for every `n ≥ m + 4m₀`. -/
theorem akhcCL5_decay_of_scales (hd : 2 ≤ d) {m m0 : ℕ} (hm : max m2 m3 ≤ m) {sigma : ℝ}
    (hsigma0 : 0 ≤ sigma) (hsigma : sigma ≤ akhcCL5_sigma d)
    (hS : akhcCL5_B d * akhcRW_UpsPort d (akhcCL5_eta d) (akhcCL5_rho d) KPsi *
        omegaSeq m ^ 2 ≤ akhcCL5_zeta d * akhcCL5_eps d / 2)
    (hL1m0 : 2 * L1 ≤ (m0 : ℝ)) (hDm0 : 16 * D ≤ (m0 : ℝ)) (hΛm0 : akhcCL5_Lstep d ≤ m0)
    (hN0 : akhcCL5_N0 d L1 L2 D H KPsiS m m0 ≤ m + 4 * m0) :
    SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P (m + 3 * m0) ≤ 1 + sigma →
      ∀ n : ℕ, m + 4 * m0 ≤ n →
        SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P n - 1 ≤
          akhcCL5_U d KPsi * omegaSeq m ^ 2 +
            1 * (3 : ℝ) ^ (-(akhcCL5_kappa d * ((n : ℝ) - (m : ℝ) - 4 * (m0 : ℝ)))) := by
  intro hΘ
  have hgamma1 : gamma < 1 := by linarith only [hgamma]
  have hpPsiS2 : 2 < pPsiS := by linarith only [hpPsiS]
  have hanti := SuperdiffusionCLT.AKHC61.Carrier.akhc_antitone_thetaCutoff_of_P2 hnu
    hPrefix hJ2 hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne
    hKPsiS hpPsiS2 hGrowth hP2 (L := L)
  have hone := SuperdiffusionCLT.AKHC61.Carrier.akhc_one_le_thetaCutoff_of_P2 hnu hJ4
    gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS2
    hGrowth hP2 (L := L)
  have hm2 : m2 ≤ m := (le_max_left _ _).trans hm
  have hm3 : m3 ≤ m := (le_max_right _ _).trans hm
  set Θ := SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P with hΘdef
  set ℓ := SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 with hℓdef
  set lb := akhcCL5_lbar L1 L2 m m0 with hlbdef
  set K0 := akhcCL5_K0 L1 L2 m m0 with hK0def
  set M := akhcCL5_M d L1 L2 m m0 with hMdef
  set E := akhcCL5_E d L1 L2 D H KPsiS m m0 with hEdef
  set ell := akhcCL5_ell d L1 L2 D H KPsiS m m0 with hielldef
  set θ := akhcCL5_theta d with hθdef
  set B := akhcCL5_B d with hBdef
  set w := akhcCL5_w d with hwdef
  set Λ := akhcCL5_Lstep d with hΛdef
  set Zb := akhcDW_Zb θ B B w Λ ell M with hZbdef
  set N0 := akhcCL5_N0 d L1 L2 D H KPsiS m m0 with hN0def
  set Ups := akhcRW_UpsPort d (akhcCL5_eta d) (akhcCL5_rho d) KPsi with hUpsdef
  have hN0eq : N0 = K0 + akhcDW_K θ B w Λ M * (Zb + M) + Zb := rfl
  have hZbeq : Zb = ell + akhcDW_J θ B w Λ + M + akhcDW_Z2 θ B B w := rfl
  have helleq : ell = 2 * lb + 4 + E := rfl
  have hK0eq : K0 = m + 3 * m0 + lb := rfl
  have hMeq : M = akhcCL5_Md d + 4 * lb + 4 := rfl
  have hlbeq : lb = ℓ (m + 4 * m0) := rfl
  -- the scales
  have hK0Z : K0 + Zb ≤ N0 := by rw [hN0eq]; omega
  have hlbm0 : 3 * lb + 4 ≤ m0 := by omega
  have hK0le : K0 ≤ m + 4 * m0 := by omega
  have hN0K0 : K0 ≤ N0 := by omega
  have hm0K0 : 3 * (m0 : ℝ) ≤ (K0 : ℝ) := by
    have : 3 * m0 ≤ K0 := by omega
    exact_mod_cast this
  have hK0L1 : 4 * L1 ≤ (K0 : ℝ) := by linarith only [hm0K0, hL1m0]
  have hK0L1' : L1 ≤ (K0 : ℝ) := by linarith only [hK0L1, hL1]
  have hK0lb : 4 * lb + 6 ≤ K0 := by omega
  have hK01 : 1 ≤ K0 := by omega
  have hlagK0 : ℓ K0 ≤ lb := akhcCL5_lag_mono hL1 hL2 hK01 hK0le
  have h48 : 48 * D ≤ (K0 : ℝ) := by linarith only [hm0K0, hDm0]
  have hΛK0 : Λ ≤ K0 := by omega
  obtain ⟨hσε, hcσ, hσ1⟩ := akhcCL5_sigma_props hsigma0 hsigma
  have hΘσ : ∀ i, m + 3 * m0 ≤ i → Θ i ≤ 1 + sigma := fun i hi => (hanti hi).trans hΘ
  have hsub : ∀ i, K0 ≤ i → m + 3 * m0 ≤ i - ℓ i := fun i hi => by
    have : K0 - ℓ K0 ≤ i - ℓ i := akhcRW_sub_lag_mono hL1 hL2 hK0L1' hi
    omega
  -- the per-scale data above `K₀ + Z`
  have hscale : ∀ n, K0 + Zb ≤ n → K0 + 2 * lb + 4 ≤ n ∧
      48 * ((d : ℝ) + 1) / Real.log 3 * akhcCL5_Lsum d D H KPsiS M K0 ≤ (n : ℝ) - (K0 : ℝ) := by
    intro n hn
    refine ⟨by omega, ?_⟩
    have h1 : 48 * ((d : ℝ) + 1) / Real.log 3 * akhcCL5_Lsum d D H KPsiS M K0 ≤ (E : ℝ) :=
      Nat.le_ceil _
    have h2 : K0 + E ≤ n := by omega
    have h3 : (K0 : ℝ) + (E : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2
    linarith only [h1, h3]
  set sfun : ℕ → ℝ := fun n => B * (Ups * omegaSeq (akhcCL5_k K0 n - ℓ (akhcCL5_k K0 n)) ^ 2 +
      3 * KPsiS ^ 36 * (H * (n : ℝ) ^ D) ^ (2 : ℝ) *
        (3 : ℝ) ^ (-2 * (akhcCL5_rho d - gamma) *
          ((n : ℝ) - (((akhcCL5_k K0 n + ℓ (akhcCL5_k K0 n) + 1 : ℕ) : ℝ) - 1))) /
        (min 3 pPsiS - 2) +
      (3 : ℝ) ^ (-(1 - 2 * akhcCL5_s d) * ((n : ℝ) - (akhcCL5_k K0 n : ℝ)))) with hsfun
  have hθ0 := akhcCL5_theta_nonneg d
  have hθ1 := akhcCL5_theta_lt_one d
  have hB0 := akhcCL5_B_nonneg d
  have hw0 := akhcCL5_w_pos d
  have hw1 := akhcCL5_w_lt_one d
  have hUps0 : 0 ≤ Ups := add_nonneg (akhcRW_UpsVar_nonneg d (akhcCL5_eta_gt d hd) hKPsi)
    (akhcRW_UpsMM_nonneg d (akhcCL5_eta_gt d hd) hKPsi (akhcCL5_c_pos d))
  have hS0 : 0 ≤ B * Ups * omegaSeq m ^ 2 := by positivity
  -- the lag hypotheses of the decay lemma
  have hq : ∀ i, K0 < i → m + 3 * m0 ≤ i - ℓ i ∧ i - ℓ i < i := by
    intro i hi
    have h1 := hsub i hi.le
    have h2 : 1 ≤ ℓ i := akhcCL5_lag_pos hL1 hL2 (by omega)
    exact ⟨h1, by omega⟩
  have hqlag : ∀ i, K0 < i → i ≤ m + 4 * m0 → i ≤ i - ℓ i + ell := by
    intro i hi hiN
    have : ℓ i ≤ lb := akhcCL5_lag_mono hL1 hL2 (by omega) hiN
    omega
  have hqmono : ∀ i i', K0 < i → i ≤ i' → i - ℓ i ≤ i' - ℓ i' := by
    intro i i' hi hii'
    have hiR : L1 ≤ (i : ℝ) := hK0L1'.trans (by exact_mod_cast hi.le)
    exact akhcRW_sub_lag_mono hL1 hL2 hiR hii'
  have hqM : ∀ i, N0 + M ≤ i → i - N0 ≤ 2 * ((i - ℓ i) - N0) := by
    intro i hi
    have hN01 : 1 ≤ N0 := by omega
    have hN0L1 : 4 * L1 ≤ (N0 : ℝ) := hK0L1.trans (by exact_mod_cast hN0K0)
    have hg := akhcCL5_lag_growth hL1 hL2 hN01 hN0L1 (by omega : N0 ≤ i)
    have hlN0 : ℓ N0 ≤ lb := akhcCL5_lag_mono hL1 hL2 hN01 hN0
    have hlN0' : (ℓ N0 : ℝ) ≤ (lb : ℝ) := by exact_mod_cast hlN0
    have hiM : (N0 : ℝ) + (M : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
    have hMR : (M : ℝ) = (akhcCL5_Md d : ℝ) + 4 * (lb : ℝ) + 4 := by rw [hMeq]; push_cast; ring
    have hMd : (0 : ℝ) ≤ (akhcCL5_Md d : ℝ) := Nat.cast_nonneg _
    have h3 : ((2 * ℓ i + N0 : ℕ) : ℝ) < (i : ℝ) := by
      push_cast
      linarith only [hg, hlN0', hiM, hMR, hMd]
    have h4 := Nat.cast_lt.1 h3
    omega
  -- the recursion above `K₀ + Z`
  have hrec : ∀ n, K0 + Zb ≤ n → Θ n - 1 ≤ θ * (Θ (n - Λ) - 1) + akhcCL5_c d * (Θ n - 1) ^ 2 +
      B * ∑ j ∈ Finset.range (n - K0), w ^ j * ((Θ (n - j) - 1) - (Θ n - 1)) +
      B * ∑ j ∈ Finset.range (n - K0), w ^ j * (Θ ((n - j) - ℓ (n - j)) - 1) ^ 2 +
      sfun n := by
    intro n hn
    obtain ⟨hn1, -⟩ := hscale n hn
    obtain ⟨hKk, hkn, hk0n, hbk, -, -⟩ :=
      akhcCL5_k_props hL1 hL2 hbeta hK0L1 hK0lb hlagK0 hn1
    set k := akhcCL5_k K0 n with hkdef
    have hkL1 : L1 ≤ (k : ℝ) := hK0L1'.trans (by exact_mod_cast hKk)
    have hwin : (k : ℝ) < ((k + ℓ k + 1 : ℕ) : ℝ) - L1 * Real.log (L2 * (k : ℝ)) := by
      have : L1 * Real.log (L2 * (k : ℝ)) ≤ (ℓ k : ℝ) := Nat.le_ceil _
      push_cast
      linarith only [this]
    have hwinE2 : ∀ n' ∈ Finset.Icc (k + 1) n, 1 < L2 * (n' : ℝ) ∧
        beta * (n' : ℝ) < (n' : ℝ) - (ℓ n' : ℝ) ∧ m3 ≤ n' - ℓ n' := by
      intro n' hn'
      have hn'1 := (Finset.mem_Icc.1 hn').1
      have hn'2 : (2 : ℝ) ≤ (n' : ℝ) := by exact_mod_cast (by omega : 2 ≤ n')
      refine ⟨by nlinarith only [hL2, hn'2],
        akhcCL5_window hL1 hL2 hbeta hK0L1 hK0lb hlagK0 (by omega), ?_⟩
      have := hsub n' (by omega)
      omega
    have hΘ2 : Θ (k - ℓ k) ≤ 2 := by
      have := hΘσ _ (hsub k hKk)
      linarith only [this, hσ1]
    have hρ := akhcCL5_rho_ge d hd
    exact akhcCL_recursion_range hnu P L hPrefix hJ2 hJ4 gamma H D m2 PsiS KPsiS pPsiS
      hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS2 hGrowth hP2 beta L1 L2 m3 omegaSeq
      Psi KPsi pPsi hbeta0 hL1 hL2 homega hPsiOne hKPsi hGrowthPsi hP3 hd homegaAnti hKk
      (by omega) hkn (by omega) _ (akhcCL5_unit d) (akhcCL5_scaleSep d _) (akhcCL5_s_lo d)
      (akhcCL5_s_hi d) (akhcCL5_gap d) (by linarith only [hρ, hgamma]) (akhcCL5_eta_gt d hd)
      (by unfold akhcCL5_eta; exact hpPsi) (akhcCL5_c_pos d) hk0n (by omega) hbk hwin hkL1
      hwinE2 hΘ2
  -- the source above `K₀ + Z`
  have hs : ∀ n, K0 + Zb ≤ n →
      sfun n ≤ B * Ups * omegaSeq m ^ 2 + akhcCL5_T d M * akhcCL5_r d ^ (n - K0) := by
    intro n hn
    obtain ⟨hn1, hE⟩ := hscale n hn
    obtain ⟨hKk, -, -, -, hthird, hδ⟩ :=
      akhcCL5_k_props hL1 hL2 hbeta hK0L1 hK0lb hlagK0 hn1
    have hKn : K0 ≤ n := by omega
    have h1 : omegaSeq (akhcCL5_k K0 n - ℓ (akhcCL5_k K0 n)) ^ 2 ≤ omegaSeq m ^ 2 := by
      have hmk : m ≤ akhcCL5_k K0 n - ℓ (akhcCL5_k K0 n) := by
        have := hsub _ hKk
        omega
      exact pow_le_pow_left₀ (homega _).le (homegaAnti hmk) 2
    have h2 := akhcCL5_tail2_le d hd hgamma hH hD hKPsiS hpPsiS (M := M)
      (k0 := akhcCL5_k K0 n + ℓ (akhcCL5_k K0 n) + 1) hK01 hKn h48
      (by push_cast; linarith only [hδ]) hE
    have h3 := akhcCL5_tail3_le d hH hD hKPsiS (M := M) (k := akhcCL5_k K0 n) hK01 hKn
      hthird hE
    have h4 : B * (Ups * omegaSeq (akhcCL5_k K0 n - ℓ (akhcCL5_k K0 n)) ^ 2) ≤
        B * Ups * omegaSeq m ^ 2 := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left h1 (mul_nonneg hB0 hUps0)
    rw [hsfun]
    dsimp only
    rw [mul_add, mul_add]
    linarith only [h2, h3, h4]
  have hdecay := akhcDW_decay (F := fun i => Θ i - 1) (q := fun i => i - ℓ i) (s := sfun)
    (c := akhcCL5_c d) (σ := sigma) (S := B * Ups * omegaSeq m ^ 2) (T := akhcCL5_T d M)
    (Kσ := m + 3 * m0) (Nrec := K0 + Zb) (Ntot := m + 4 * m0)
    (fun i => by have := hone i; linarith only [this])
    (fun a b hab => by have := hanti hab; dsimp only; linarith only [this])
    hθ0 hθ1 (akhcCL5_c_nonneg d) hB0 hB0 hw0 hw1 hsigma0 hσε hcσ (by omega)
    (fun i hi => by have := hΘσ i hi; linarith only [this])
    hq hqlag hqmono hN0 hqM (akhcCL5_r_pow_le_half d (by omega)) hS0 hS le_rfl le_rfl hs hrec
  -- the conclusion
  intro n hn
  have hN0n : N0 ≤ n := hN0.trans hn
  have hmain := hdecay n hN0n
  have hζ := akhcCL5_zeta_pos d
  have hε4 := akhcCL5_eps_le d
  have hε0 := akhcCL5_eps_pos d
  have hr0 := akhcCL5_r_pos d
  have hr1 := akhcCL5_r_lt_one d
  have hrM : akhcCL5_r d ^ M ≤ 1 := pow_le_one₀ hr0.le hr1.le
  have hU : B * Ups * omegaSeq m ^ 2 / akhcCL5_zeta d = akhcCL5_U d KPsi * omegaSeq m ^ 2 := by
    unfold akhcCL5_U
    ring
  have hpow : akhcCL5_r d ^ (n - N0) ≤
      (3 : ℝ) ^ (-(akhcCL5_kappa d * ((n : ℝ) - (m : ℝ) - 4 * (m0 : ℝ)))) := by
    rw [akhcCL5_r_pow_sub d hN0n]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have h1 : (N0 : ℝ) ≤ (m : ℝ) + 4 * (m0 : ℝ) := by exact_mod_cast hN0
    have h2 := mul_le_mul_of_nonneg_left (show (n : ℝ) - (m : ℝ) - 4 * (m0 : ℝ) ≤
      (n : ℝ) - (N0 : ℝ) by linarith only [h1]) (akhcCL5_kappa_pos d).le
    linarith only [h2]
  have hrn0 : 0 ≤ akhcCL5_r d ^ (n - N0) := pow_nonneg hr0.le _
  have hεrM : akhcCL5_eps d * akhcCL5_r d ^ M ≤ 1 := by
    have := mul_le_mul hε4 hrM (pow_nonneg hr0.le _) (by norm_num)
    linarith only [this]
  have hlast : akhcCL5_eps d * akhcCL5_r d ^ M * akhcCL5_r d ^ (n - N0) ≤
      1 * (3 : ℝ) ^ (-(akhcCL5_kappa d * ((n : ℝ) - (m : ℝ) - 4 * (m0 : ℝ)))) :=
    mul_le_mul hεrM hpow hrn0 (by norm_num)
  have hmain' : Θ n - 1 ≤ B * Ups * omegaSeq m ^ 2 / akhcCL5_zeta d +
      akhcCL5_eps d * akhcCL5_r d ^ M * akhcCL5_r d ^ (n - N0) := hmain
  rw [hU] at hmain'
  linarith only [hmain', hlast]

end Closure

end

end SuperdiffusionCLT.AKHC61.Step3
