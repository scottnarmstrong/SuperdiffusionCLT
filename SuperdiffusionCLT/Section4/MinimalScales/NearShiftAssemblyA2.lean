/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.NearShiftAssembly
public import SuperdiffusionCLT.Section4.MinimalScales.RootArithOneScaleD
public import SuperdiffusionCLT.Section4.LNaught.Threshold

/-!
# Near-scale assembly: `lNaught` monotonicity and the window arithmetic

* `srootNS_inner_mono_scaled`, `srootNS_lNaught_quarter`: `lNaught Cp M ≤ ¼ lNaught C1 M'` when
  `M ≤ λ M'` and `C1 ≥ 2 Cp λ (1 + 2 λ)^12` (the constant `C` and the slot `M` enter through the
  product `C (M + 1 + K)`, which absorbs a larger `M` at the price of a larger `C`).
* `srootNS_window_arith`: from the threshold `lNaught C1 (C1 s⁻¹ K) (1/2) ≤ m` every size
  condition of the shifted local base at `K' = 4 C1 s⁻¹ K` over the hNear window.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

noncomputable section

private theorem srootNS_h12 (x : ℝ) : x ^ (12 : ℝ) = x ^ 12 := by
  exact_mod_cast Real.rpow_natCast x 12

/-- Monotonicity of `lNaughtInner` in the pair `(C, M)` when `M ≤ λ M'` and `C λ (1+2λ)^12 ≤ C'`. -/
theorem srootNS_inner_mono_scaled {C C' M M' alpha cStar nu K lam : ℝ} (hC : 0 ≤ C)
    (hlam : 1 ≤ lam) (hM : 0 ≤ M) (hM' : 0 ≤ M') (hMM' : M ≤ lam * M') (hK : 0 ≤ K)
    (hc : 0 < cStar) (hnu : 0 < nu) (halpha : alpha < 1)
    (hCC' : C * lam * (1 + 2 * lam) ^ 12 ≤ C') :
    SuperdiffusionCLT.Section4.LNaught.lNaughtInner C M alpha cStar nu K ≤
      SuperdiffusionCLT.Section4.LNaught.lNaughtInner C' M' alpha cStar nu K := by
  unfold SuperdiffusionCLT.Section4.LNaught.lNaughtInner
  have hD : 0 < (1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ) :=
    SuperdiffusionCLT.Section4.LNaught.denom_pos hnu halpha
  have he : 0 < nu * (1 - alpha) := mul_pos hnu (by linarith only [halpha])
  have hg : 0 ≤ cStar ^ (-(3 : ℝ)) := Real.rpow_nonneg hc.le _
  set g : ℝ := cStar ^ (-(3 : ℝ)) with hgdef
  set D : ℝ := (1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ) with hDdef
  set e : ℝ := nu * (1 - alpha) with hedef
  set u : ℝ := (M' + 1 + K) * g / e with hu
  set v : ℝ := (M + 1 + K) * g / e with hv
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hv0 : 0 ≤ v := by rw [hv]; positivity
  have hvu : v ≤ lam * u := by
    rw [hv, hu]
    have : (M + 1 + K) * g ≤ lam * ((M' + 1 + K) * g) := by
      have h1 : M + 1 + K ≤ lam * (M' + 1 + K) := by nlinarith only [hMM', hlam, hK]
      nlinarith only [mul_le_mul_of_nonneg_right h1 hg]
    calc (M + 1 + K) * g / e ≤ lam * ((M' + 1 + K) * g) / e :=
          div_le_div_of_nonneg_right this he.le
      _ = lam * ((M' + 1 + K) * g / e) := by ring
  have hl2 : (1 : ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith only [this]
  have hlogu : Real.log 2 ≤ Real.log (2 + u) := Real.log_le_log (by norm_num) (by linarith only [hu0])
  have hlogu0 : 0 ≤ Real.log (2 + u) := by linarith only [hlogu, hl2]
  have hlv : Real.log (2 + v) ≤ (1 + 2 * lam) * Real.log (2 + u) := by
    have h1 : 2 + v ≤ lam * (2 + u) := by nlinarith only [hvu, hlam]
    have h2 : Real.log (2 + v) ≤ Real.log (lam * (2 + u)) :=
      Real.log_le_log (by linarith only [hv0]) h1
    rw [Real.log_mul (by linarith only [hlam]) (by linarith only [hu0])] at h2
    have h3 : Real.log lam ≤ lam - 1 := Real.log_le_sub_one_of_pos (by linarith only [hlam])
    nlinarith only [h2, h3, hlogu, hl2, hlam]
  have hlv0 : 0 ≤ Real.log (2 + v) := by
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (show (2 : ℝ) ≤ 2 + v by linarith only [hv0])
    linarith only [this, hl2]
  have hp : Real.log (2 + v) ^ 12 ≤ (1 + 2 * lam) ^ 12 * Real.log (2 + u) ^ 12 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hlv0 hlv 12
  simp only [srootNS_h12]
  have hY : 0 ≤ (M' + 1 + K) * g / D * Real.log (2 + u) ^ 12 := by
    have : 0 ≤ M' + 1 + K := by linarith only [hM', hK]
    positivity
  have h1 : (M + 1 + K) ≤ lam * (M' + 1 + K) := by nlinarith only [hMM', hlam, hK]
  have hnum : C * (M + 1 + K) * g / D ≤ C * lam * (M' + 1 + K) * g / D := by
    apply div_le_div_of_nonneg_right _ hD.le
    have := mul_le_mul_of_nonneg_left h1 hC
    have := mul_le_mul_of_nonneg_right this hg
    nlinarith only [this]
  have hnn : 0 ≤ C * lam * (M' + 1 + K) * g / D := by
    have : 0 ≤ M' + 1 + K := by linarith only [hM', hK]
    have : 0 ≤ lam := by linarith only [hlam]
    positivity
  calc C * (M + 1 + K) * g / D * Real.log (2 + v) ^ 12
      ≤ (C * lam * (M' + 1 + K) * g / D) * ((1 + 2 * lam) ^ 12 * Real.log (2 + u) ^ 12) :=
        mul_le_mul hnum hp (by positivity) hnn
    _ = (C * lam * (1 + 2 * lam) ^ 12) * ((M' + 1 + K) * g / D * Real.log (2 + u) ^ 12) := by
        ring
    _ ≤ C' * ((M' + 1 + K) * g / D * Real.log (2 + u) ^ 12) :=
        mul_le_mul_of_nonneg_right hCC' hY
    _ = C' * (M' + 1 + K) * g / D * Real.log (2 + u) ^ 12 := by ring

private theorem srootNS_lNaught_half_eq (C M cStar nu K : ℝ) :
    SuperdiffusionCLT.Frozen.Section4.lNaught C M (1 / 2) cStar nu K =
      (SuperdiffusionCLT.Section4.LNaught.lNaughtInner C M (1 / 2) cStar nu K) ^ 2 := by
  unfold SuperdiffusionCLT.Frozen.Section4.lNaught
    SuperdiffusionCLT.Section4.LNaught.lNaughtInner
  rw [show (1 : ℝ) / (1 - 1 / 2) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- `lNaught Cp M ≤ ¼ lNaught C1 M'` at `alpha = 1/2` (the monotonicity trap of the shifted
local base: the product `C (M + 1 + K)` absorbs the larger slot). -/
theorem srootNS_lNaught_quarter {Cp C1 M M' cStar nu K lam : ℝ} (hCp : 0 ≤ Cp)
    (hlam : 1 ≤ lam) (hM : 0 ≤ M) (hM' : 0 ≤ M') (hMM' : M ≤ lam * M') (hK : 0 ≤ K)
    (hc : 0 < cStar) (hnu : 0 < nu) (hC : 2 * Cp * lam * (1 + 2 * lam) ^ 12 ≤ C1) :
    SuperdiffusionCLT.Frozen.Section4.lNaught Cp M (1 / 2) cStar nu K ≤
      SuperdiffusionCLT.Frozen.Section4.lNaught C1 M' (1 / 2) cStar nu K / 4 := by
  have h := srootNS_inner_mono_scaled (C := 2 * Cp) (C' := C1) (alpha := 1 / 2) (by linarith only [hCp])
    hlam hM hM' hMM' hK hc hnu (by norm_num) hC
  have h2 : SuperdiffusionCLT.Section4.LNaught.lNaughtInner (2 * Cp) M (1 / 2) cStar nu K =
      2 * SuperdiffusionCLT.Section4.LNaught.lNaughtInner Cp M (1 / 2) cStar nu K := by
    unfold SuperdiffusionCLT.Section4.LNaught.lNaughtInner; ring
  rw [h2] at h
  have h0 : 0 ≤ SuperdiffusionCLT.Section4.LNaught.lNaughtInner Cp M (1 / 2) cStar nu K :=
    SuperdiffusionCLT.Section4.LNaught.inner_nonneg hCp hM hK hc hnu (by norm_num)
  rw [srootNS_lNaught_half_eq, srootNS_lNaught_half_eq]
  nlinarith only [h, h0]

/-- From the threshold: `m ≥ 64` and `C1 · (C1 s⁻¹ K log m) ≤ 1600 m`. -/
theorem srootNS_threshold_core {C1 s K nondeg cStar nu : ℝ} {m : ℕ} (hC1 : 6400 ≤ C1)
    (hs0 : 0 < s) (hs1 : s ≤ 1) (hK : C1 ≤ K) (hnd : 0 ≤ nondeg) (hc : 0 < cStar)
    (hc2 : cStar ≤ 2) (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (hm : SuperdiffusionCLT.Frozen.Section4.lNaught C1 (C1 * s⁻¹ * K) (1 / 2) cStar nu
      nondeg ≤ (m : ℝ)) :
    (64 : ℝ) ≤ m ∧ C1 * (C1 * s⁻¹ * K * Real.log (m : ℝ)) ≤ 1600 * (m : ℝ) := by
  have hC10 : 0 ≤ C1 := by linarith only [hC1]
  have hs1inv : 1 ≤ s⁻¹ := (one_le_inv₀ hs0).2 hs1
  have hKpos : 0 ≤ K := by linarith only [hK, hC1]
  set M' : ℝ := C1 * s⁻¹ * K with hM'
  have hM'ge : C1 ≤ M' := by
    have h1 : C1 * 1 ≤ C1 * s⁻¹ := mul_le_mul_of_nonneg_left hs1inv hC10
    have h2 : C1 * s⁻¹ * 1 ≤ C1 * s⁻¹ * K := mul_le_mul_of_nonneg_left (by linarith only [hK, hC1]) (by positivity)
    rw [hM']; linarith only [h1, h2, hK]
  have hM'0 : 0 ≤ M' := by linarith only [hM'ge, hC10]
  have hin := srootD_inner_ge (C := C1) (M := M') (alpha := 1 / 2) (cStar := cStar) (nu := nu)
    (K := nondeg) hC10 hM'0 hnd hc hc2 hnu hnu1 (by norm_num) (by norm_num)
  rw [srootNS_h12] at hin
  have hl2 : (0.69 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith only [this]
  have hp : (0.69 : ℝ) ^ 12 ≤ Real.log 2 ^ 12 := pow_le_pow_left₀ (by norm_num) hl2.le 12
  have hp2 : (0.01 : ℝ) ≤ Real.log 2 ^ 12 := by
    have : (0.01 : ℝ) ≤ (0.69 : ℝ) ^ 12 := by norm_num
    linarith only [hp, this]
  have hge : C1 * M' / 800 ≤
      SuperdiffusionCLT.Section4.LNaught.lNaughtInner C1 M' (1 / 2) cStar nu nondeg := by
    have h1 : C1 * M' / 8 * 0.01 ≤ C1 * M' / 8 * Real.log 2 ^ 12 :=
      mul_le_mul_of_nonneg_left hp2 (by positivity)
    linarith only [hin, h1]
  have hnu' : (SuperdiffusionCLT.Frozen.Section4.lNaught C1 M' (1 / 2) cStar nu nondeg) ^
      ((1 : ℝ) - 1 / 2) =
      SuperdiffusionCLT.Section4.LNaught.lNaughtInner C1 M' (1 / 2) cStar nu nondeg :=
    SuperdiffusionCLT.Section4.LNaught.lNaught_rpow_eq_inner hC10 hM'0 hnd hc hnu
      (by norm_num)
  have hL0 : 0 ≤ SuperdiffusionCLT.Frozen.Section4.lNaught C1 M' (1 / 2) cStar nu nondeg :=
    SuperdiffusionCLT.Section4.LNaught.lNaught_nonneg hC10 hM'0 hnd hc hnu (by norm_num)
  have hmy : (SuperdiffusionCLT.Frozen.Section4.lNaught C1 M' (1 / 2) cStar nu nondeg) ^
      ((1 : ℝ) - 1 / 2) ≤ (m : ℝ) ^ ((1 : ℝ) - 1 / 2) :=
    Real.rpow_le_rpow hL0 hm (by norm_num)
  rw [hnu'] at hmy
  have hexp : (1 : ℝ) - 1 / 2 = (2 : ℝ)⁻¹ := by norm_num
  rw [hexp] at hmy
  set y : ℝ := (m : ℝ) ^ ((2 : ℝ)⁻¹) with hy
  have hy2 : y ^ 2 = (m : ℝ) := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg m)]
    norm_num
  have hy0 : 0 ≤ y := Real.rpow_nonneg (Nat.cast_nonneg m) _
  have hlog : Real.log (m : ℝ) ≤ 2 * y := by
    have := Real.log_le_rpow_div (Nat.cast_nonneg m) (show (0 : ℝ) < 2⁻¹ by norm_num)
    rw [← hy] at this
    have h2 : y / 2⁻¹ = 2 * y := by field_simp
    linarith only [this, h2]
  have hlog0 : 0 ≤ Real.log (m : ℝ) := Real.log_natCast_nonneg m
  have hCM : C1 * M' ≤ 800 * y := by linarith only [hge, hmy]
  have hy8 : 8 ≤ y := by
    have h1 : C1 * C1 ≤ C1 * M' := mul_le_mul_of_nonneg_left hM'ge hC10
    nlinarith only [h1, hCM, hC1]
  refine ⟨?_, ?_⟩
  · nlinarith only [hy2, hy8]
  · have := mul_le_mul hCM hlog hlog0 (by positivity)
    nlinarith only [this, hy2]

private theorem srootNS_four_le_log_of_64 {m : ℕ} (hm : (64 : ℝ) ≤ m) : (4 : ℝ) ≤ Real.log (m : ℝ) := by
  rw [Real.le_log_iff_exp_le (by linarith only [hm])]
  have h1 : Real.exp 4 = Real.exp 1 ^ 4 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h2 := Real.exp_one_lt_d9
  have h3 : Real.exp 1 ^ 4 ≤ (2.7182818286 : ℝ) ^ 4 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le h2.le 4
  have h4 : (2.7182818286 : ℝ) ^ 4 ≤ 64 := by norm_num
  linarith only [h1, h3, h4, hm]

private theorem srootNS_quarter_const {Cp C0 C1 : ℝ} (hC0 : 1 ≤ C0)
    (hA : 6400 * (1 + C0) + 16 * Cp ^ 2 * (1 + 16 * Cp) ^ 12 ≤ C1) :
    2 * Cp * (8 * Cp) * (1 + 2 * (8 * Cp)) ^ 12 ≤ C1 := by
  have e : 1 + 2 * (8 * Cp) = 1 + 16 * Cp := by ring
  rw [e]
  generalize (1 + 16 * Cp) ^ 12 = X at hA ⊢
  linarith only [hA, hC0]

private theorem srootNS_cube_aux {Kp x L : ℝ} (hKp : 0 ≤ Kp) (hL : 1 ≤ L) (hx : 1 ≤ x) :
    Kp * x ≤ Kp * L ^ ((1 : ℝ) / 2) * x ^ (3 : ℝ) := by
  have hsq : (1 : ℝ) ≤ L ^ ((1 : ℝ) / 2) := Real.one_le_rpow hL (by norm_num)
  have e : x ^ (3 : ℝ) = x ^ 3 := by exact_mod_cast Real.rpow_natCast x 3
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hcube : x ≤ x ^ 3 := by
    have h2 : 1 ≤ x ^ 2 := one_le_pow₀ hx
    have := mul_le_mul_of_nonneg_left h2 hx0
    linarith only [this]
  rw [e]
  have h2 : x * 1 ≤ x ^ 3 * L ^ ((1 : ℝ) / 2) :=
    mul_le_mul hcube hsq (by norm_num) (pow_nonneg hx0 3)
  linarith only [mul_le_mul_of_nonneg_left h2 hKp]

/-- The window arithmetic of the near-scale assembly. For the constant `Cp ≥ 1` of the shifted
local base and `C0 ≥ 1`, there is `A ≥ 1` such that, for every `C1 ≥ A`, the threshold
`lNaught C1 (C1 s⁻¹ K) (1/2) ≤ m` gives all size conditions of the shifted local base at
`K' = 4 C1 s⁻¹ K`, for every cutoff `L` of the hNear window `m - C1 s⁻¹ h ≤ L ≤ m + h`
(`h = ⌈K log m⌉`) and every depth `l ≤ ⌈C0 s⁻¹ log m⌉`. -/
theorem srootNS_window_arith (Cp C0 : ℝ) (hCp : 1 ≤ Cp) (hC0 : 1 ≤ C0) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ C1 : ℝ, A ≤ C1 → ∀ nu cStar nondeg : ℝ, 0 < nu → nu ≤ 1 → 0 < cStar →
      cStar ≤ 2 → 0 ≤ nondeg → ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ K : ℝ, C1 ≤ K → ∀ m n : ℕ,
      SuperdiffusionCLT.Frozen.Section4.lNaught C1 (C1 * s⁻¹ * K) (1 / 2) cStar nu nondeg ≤
        (m : ℝ) →
      m - ⌈K * Real.log (m : ℝ)⌉₊ ≤ n → n ≤ m →
      (64 : ℝ) ≤ m ∧ (4 : ℝ) ≤ Real.log (m : ℝ) ∧ K ≤ (m : ℝ) ∧
      (⌈K * Real.log (m : ℝ)⌉₊ : ℝ) ≤ 2 * K * Real.log (m : ℝ) ∧
      (⌈C0 * s⁻¹ * Real.log (m : ℝ)⌉₊ : ℝ) ≤ 2 * C0 * s⁻¹ * Real.log (m : ℝ) ∧
      1 ≤ (⌈K * Real.log (m : ℝ)⌉₊ : ℝ) ∧
      2 * (⌈K * Real.log (m : ℝ)⌉₊ : ℝ) ≤ (m : ℝ) ∧
      Real.log (2 * (⌈K * Real.log (m : ℝ)⌉₊ : ℝ)) ≤ Real.log (m : ℝ) ∧
      Real.log (2 * (⌈K * Real.log (m : ℝ)⌉₊ : ℝ)) ≤ 2 * Real.log (m : ℝ) ∧
      1 ≤ 4 * C1 * s⁻¹ * K ∧
      ∀ L : ℕ, (m : ℝ) - C1 * s⁻¹ * (⌈K * Real.log (m : ℝ)⌉₊ : ℝ) ≤ (L : ℝ) →
        (L : ℝ) ≤ (m : ℝ) + (⌈K * Real.log (m : ℝ)⌉₊ : ℝ) →
        (m : ℝ) / 2 ≤ (L : ℝ) ∧ (L : ℝ) ≤ 2 * (m : ℝ) ∧ 0 ≤ Real.log (L : ℝ) ∧
        Real.log (L : ℝ) ≤ 2 * Real.log (m : ℝ) ∧
        |(L : ℝ) - (m : ℝ)| ≤ (4 * C1 * s⁻¹ * K) * Real.log (L : ℝ) ∧
        ∀ l : ℕ, l ≤ ⌈C0 * s⁻¹ * Real.log (m : ℝ)⌉₊ →
          l ≤ n ∧ (m : ℝ) / 2 ≤ ((n - l : ℕ) : ℝ) ∧
          (L : ℝ) - ((n - l : ℕ) : ℝ) ≤ 2 * (⌈K * Real.log (m : ℝ)⌉₊ : ℝ) + (l : ℝ) ∧
          SuperdiffusionCLT.Frozen.Section4.lNaught Cp
              (Cp * ((4 * C1 * s⁻¹ * K) + (4 * C1 * s⁻¹ * K))) (1 / 2) cStar nu nondeg ≤ (L : ℝ) ∧
          SuperdiffusionCLT.Frozen.Section4.lNaught Cp
              (Cp * ((4 * C1 * s⁻¹ * K) + (4 * C1 * s⁻¹ * K))) (1 / 2) cStar nu nondeg ≤
            ((n - l : ℕ) : ℝ) ∧
          (L : ℝ) - (4 * C1 * s⁻¹ * K) * (L : ℝ) ^ ((1 : ℝ) / 2) * Real.log (L : ℝ) ^ (3 : ℝ) ≤
            ((n - l : ℕ) : ℝ) := by
  have hApos : 0 ≤ 16 * Cp ^ 2 * (1 + 16 * Cp) ^ 12 := by
    clear * - Cp hCp
    exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg Cp)) (pow_nonneg (by linarith only [hCp]) 12)
  refine ⟨6400 * (1 + C0) + 16 * Cp ^ 2 * (1 + 16 * Cp) ^ 12, ?_, ?_⟩
  · linarith only [hApos, hC0]
  intro C1 hA nu cStar nondeg hnu hnu1 hc hc2 hnd s hs0 hs1 K hK m n hm hn1 hn2
  clear hn2
  have hC1a : 6400 * (1 + C0) ≤ C1 := by clear * - C0 hApos C1 hA; linarith only [hA, hApos]
  clear hApos
  have hC1 : 6400 ≤ C1 := by clear * - hC0 C1 hC1a; linarith only [hC1a, hC0]
  have hC1pos : 0 < C1 := by clear * - C1 hC1; linarith only [hC1]
  have hK1 : 1 ≤ K := by clear * - K hK hC1; linarith only [hK, hC1]
  obtain ⟨hm64, hcore⟩ := srootNS_threshold_core hC1 hs0 hs1 hK hnd hc hc2 hnu hnu1 hm
  clear hK hc2 hnu1
  have hlg4 := srootNS_four_le_log_of_64 hm64
  set lg : ℝ := Real.log (m : ℝ) with hlg
  have hs1inv : 1 ≤ s⁻¹ := by
    clear * - s hs0 hs1
    exact (one_le_inv₀ hs0).2 hs1
  clear hs1
  set W0 : ℝ := s⁻¹ * K * lg with hW0
  clear_value W0 lg
  have hKlg : K * lg ≤ W0 := by
    clear * - s K hK1 hlg4 lg hs1inv W0 hW0
    have : K * lg * 1 ≤ K * lg * s⁻¹ :=
      mul_le_mul_of_nonneg_left hs1inv (mul_nonneg (by linarith only [hK1]) (by linarith only [hlg4]))
    rw [hW0]; linarith only [this]
  have hK1lg : 1 ≤ K * lg := by
    clear * - K hK1 hlg4 lg
    exact one_le_mul_of_one_le_of_one_le hK1 (by linarith only [hlg4])
  have hW01 : 1 ≤ W0 := by clear * - W0 hKlg hK1lg; linarith only [hKlg, hK1lg]
  have hslg : s⁻¹ * lg ≤ W0 := by
    clear * - s hs0 K hK1 hlg4 lg W0 hW0
    have : s⁻¹ * lg * 1 ≤ s⁻¹ * lg * K :=
      mul_le_mul_of_nonneg_left hK1 (mul_nonneg (inv_nonneg.2 hs0.le) (by linarith only [hlg4]))
    rw [hW0]; linarith only [this]
  have hZ : C1 * (C1 * W0) ≤ 1600 * (m : ℝ) := by
    clear * - C1 s K m hcore lg W0 hW0
    have : C1 * s⁻¹ * K * lg = C1 * W0 := by rw [hW0]; ring
    rw [this] at hcore; exact hcore
  clear hcore
  have hZm : 4 * (1 + C0) * (C1 * W0) ≤ (m : ℝ) := by
    clear * - C0 hC0 C1 m hC1a hC1pos hm64 W0 hZ
    have h1 : C1 * (4 * (1 + C0) * (C1 * W0)) ≤ C1 * (m : ℝ) := by
      have h2 : 4 * (1 + C0) * (C1 * (C1 * W0)) ≤ 4 * (1 + C0) * (1600 * (m : ℝ)) :=
        mul_le_mul_of_nonneg_left hZ (by linarith only [hC0])
      have h3 : 6400 * (1 + C0) * (m : ℝ) ≤ C1 * (m : ℝ) :=
        mul_le_mul_of_nonneg_right hC1a (by linarith only [hm64])
      linarith only [h2, h3]
    exact le_of_mul_le_mul_left h1 hC1pos
  clear hZ
  have hZ0 : 0 ≤ C1 * W0 := by
    clear * - C1 hC1pos W0 hW01
    exact mul_nonneg hC1pos.le (by linarith only [hW01])
  have hW0Z : W0 ≤ C1 * W0 := by
    clear * - C1 hC1 W0 hW01
    have := mul_le_mul_of_nonneg_right (by linarith only [hC1] : (1 : ℝ) ≤ C1)
      (by linarith only [hW01] : (0 : ℝ) ≤ W0)
    linarith only [this]
  have hZm2 : 8 * (C1 * W0) ≤ (m : ℝ) := by
    clear * - hC0 C1 m W0 hZm hZ0
    have := mul_nonneg (sub_nonneg.2 hC0) hZ0
    linarith only [hZm, this]
  clear hZ0
  have hZmC : 2 * (1 + C0) * (C1 * W0) ≤ (m : ℝ) / 2 := by clear * - C0 C1 m W0 hZm; linarith only [hZm]
  -- ceilings
  clear hZm
  set h : ℕ := ⌈K * lg⌉₊ with hhdef
  set hb : ℕ := ⌈C0 * s⁻¹ * lg⌉₊ with hhbdef
  clear_value h hb
  have hh : (h : ℝ) ≤ 2 * K * lg := by
    clear * - K lg hK1lg h hhdef
    have := Nat.ceil_lt_add_one (show 0 ≤ K * lg by linarith only [hK1lg])
    rw [← hhdef] at this
    linarith only [this, hK1lg]
  have hh1 : 1 ≤ (h : ℝ) := by clear * - hK1lg h hhdef; rw [hhdef]; exact le_trans hK1lg (Nat.le_ceil _)
  clear hhdef hK1lg
  have hC0lg : 1 ≤ C0 * s⁻¹ * lg := by
    clear * - C0 hC0 s hlg4 lg hs1inv
    have h1 : 1 ≤ s⁻¹ * lg := one_le_mul_of_one_le_of_one_le hs1inv (by linarith only [hlg4])
    have := one_le_mul_of_one_le_of_one_le hC0 h1
    linarith only [this]
  have hhb : (hb : ℝ) ≤ 2 * C0 * s⁻¹ * lg := by
    clear * - C0 s lg hb hhbdef hC0lg
    have := Nat.ceil_lt_add_one (show 0 ≤ C0 * s⁻¹ * lg by linarith only [hC0lg])
    rw [← hhbdef] at this
    linarith only [this, hC0lg]
  clear hC0lg hhbdef
  have hhW : (h : ℝ) ≤ 2 * W0 := by clear * - W0 hKlg h hh; linarith only [hh, hKlg]
  have hhbW : (hb : ℝ) ≤ 2 * C0 * W0 := by
    clear * - C0 hC0 W0 hslg hb hhb
    have := mul_le_mul_of_nonneg_left hslg (show 0 ≤ 2 * C0 by linarith only [hC0])
    linarith only [hhb, this]
  clear hslg
  have hC1h : C1 * s⁻¹ * (h : ℝ) ≤ 2 * (C1 * W0) := by
    clear * - C1 s hs0 K hC1pos lg W0 hW0 h hh
    have := mul_le_mul_of_nonneg_left hh (show 0 ≤ C1 * s⁻¹ from mul_nonneg hC1pos.le (inv_nonneg.2 hs0.le))
    have e : C1 * s⁻¹ * (2 * K * lg) = 2 * (C1 * W0) := by rw [hW0]; ring
    linarith only [this, e]
  have hKm : K ≤ (m : ℝ) := by
    clear * - K m hK1 hlg4 lg W0 hKlg hW0Z hZm2
    have h0 : K * 1 ≤ K * lg := mul_le_mul_of_nonneg_left (by linarith only [hlg4]) (by linarith only [hK1])
    have h1 : K ≤ W0 := by linarith only [hKlg, h0]
    linarith only [h1, hW0Z, hZm2]
  clear hKlg
  have h2hm : 2 * (h : ℝ) ≤ (m : ℝ) := by clear * - m hW0Z hZm2 h hhW; linarith only [hhW, hZm2, hW0Z]
  have hlog2h : Real.log (2 * (h : ℝ)) ≤ lg := by
    clear * - lg hlg h hh1 h2hm
    rw [hlg]
    exact Real.log_le_log (by linarith only [hh1]) h2hm
  have hlg0 : 0 ≤ lg := by clear * - hlg4 lg; linarith only [hlg4]
  have hKp1 : 1 ≤ 4 * C1 * s⁻¹ * K := by
    clear * - C1 s K hC1 hK1 hs1inv
    have h1 : 1 ≤ C1 * s⁻¹ := one_le_mul_of_one_le_of_one_le (by linarith only [hC1]) hs1inv
    have := one_le_mul_of_one_le_of_one_le h1 hK1
    linarith only [this]
  clear hs1inv
  refine ⟨hm64, hlg4, hKm, hh, hhb, hh1, h2hm, hlog2h, by linarith only [hlog2h, hlg0], hKp1, ?_⟩
  clear hlg0 hlog2h h2hm hKm hhb hh1 hh
  intro L hL1 hL2
  have hmL : (m : ℝ) / 2 ≤ L := by clear * - m hZm2 hC1h hL1; linarith only [hL1, hC1h, hZm2]
  have hLm : (L : ℝ) ≤ 2 * m := by clear * - m hm64 hW0Z hZm2 hhW hL2; linarith only [hL2, hhW, hZm2, hW0Z, hm64]
  clear hZm2
  have hL1r : (1 : ℝ) ≤ L := by clear * - hm64 hmL; linarith only [hmL, hm64]
  have hLpos : (0 : ℝ) < L := by clear * - hL1r; linarith only [hL1r]
  have hlogL0 : 0 ≤ Real.log (L : ℝ) := by
    clear * - hL1r
    exact Real.log_nonneg hL1r
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith only [this]
  have hlogLup : Real.log (L : ℝ) ≤ 2 * lg := by
    clear * - m hm64 hlg4 lg hlg hLm hLpos hlog2
    have h1 : Real.log (L : ℝ) ≤ Real.log (2 * (m : ℝ)) :=
      Real.log_le_log hLpos hLm
    rw [Real.log_mul (by norm_num) (by linarith only [hm64]), ← hlg] at h1
    linarith only [h1, hlog2, hlg4]
  clear hLpos
  have hlogLlo : lg / 2 ≤ Real.log (L : ℝ) := by
    clear * - m hm64 hlg4 lg hlg hmL hlog2
    have h1 : Real.log ((m : ℝ) / 2) ≤ Real.log (L : ℝ) :=
      Real.log_le_log (by linarith only [hm64]) hmL
    rw [Real.log_div (by linarith only [hm64]) (by norm_num), ← hlg] at h1
    linarith only [h1, hlog2, hlg4]
  clear hlog2 hlg
  have hKpL : 2 * (C1 * W0) ≤ (4 * C1 * s⁻¹ * K) * Real.log (L : ℝ) := by
    clear * - C1 s K lg W0 hW0 hKp1 hlogLlo
    have h1 := mul_le_mul_of_nonneg_left hlogLlo (show 0 ≤ 4 * C1 * s⁻¹ * K by linarith only [hKp1])
    have e : 4 * C1 * s⁻¹ * K * (lg / 2) = 2 * (C1 * W0) := by rw [hW0]; ring
    linarith only [h1, e]
  clear hW0
  refine ⟨hmL, hLm, hlogL0, hlogLup, ?_, ?_⟩
  clear hlogLup hlogL0 hLm
  · rw [abs_le]
    constructor
    · linarith only [hKpL, hL1, hC1h]
    · linarith only [hKpL, hL2, hhW, hW0Z]
  clear hL1 hC1h
  intro l hl
  have hlr : (l : ℝ) ≤ hb := by clear * - hb hl; exact_mod_cast hl
  clear hl
  have hnr : (m : ℝ) - h ≤ n := by
    clear * - m n hn1 h
    have : m ≤ n + h := Nat.sub_le_iff_le_add.1 hn1
    have : (m : ℝ) ≤ n + h := by exact_mod_cast this
    linarith only [this]
  clear hn1
  have hlW : (l : ℝ) ≤ 2 * C0 * W0 := by
    clear * - C0 W0 hhbW hlr
    exact le_trans hlr hhbW
  clear hlr hhbW
  have hC0W : 2 * C0 * W0 ≤ 2 * C0 * (C1 * W0) := by
    clear * - C0 hC0 C1 hC1 W0 hW01
    have : W0 * 1 ≤ W0 * C1 := mul_le_mul_of_nonneg_left (by linarith only [hC1]) (by linarith only [hW01])
    have h2 := mul_le_mul_of_nonneg_left this (by linarith only [hC0] : (0 : ℝ) ≤ 2 * C0)
    linarith only [h2]
  clear hC1
  have hnl : (m : ℝ) / 2 ≤ (n : ℝ) - l := by
    clear * - C1 m n W0 hW0Z hZmC h hhW hnr hlW hC0W
    have h1 : (h : ℝ) ≤ 2 * (C1 * W0) := by
      linarith only [hhW, hW0Z]
    linarith only [hnr, hlW, hC0W, h1, hZmC]
  clear hC0W hZmC hW0Z
  have hln : l ≤ n := by
    clear * - n hm64 hnl
    have : (l : ℝ) ≤ n := by linarith only [hnl, hm64]
    exact_mod_cast this
  have hcast : ((n - l : ℕ) : ℝ) = (n : ℝ) - l := by
    clear * - n hln
    exact Nat.cast_sub hln
  rw [hcast]
  clear hcast
  have hKs : 0 ≤ C1 * s⁻¹ * K := by
    clear * - C1 s hs0 K hC1pos hK1
    exact mul_nonneg (mul_nonneg hC1pos.le (inv_nonneg.2 hs0.le)) (by linarith only [hK1])
  clear hK1 hC1pos hs0
  have hMM : Cp * ((4 * C1 * s⁻¹ * K) + (4 * C1 * s⁻¹ * K)) ≤ (8 * Cp) * (C1 * s⁻¹ * K) := by
    clear * - Cp C1 s K
    exact le_of_eq (by ring)
  have hCpn : 0 ≤ Cp := by clear * - Cp hCp; linarith only [hCp]
  have h8Cp : 1 ≤ 8 * Cp := by clear * - Cp hCp; linarith only [hCp]
  clear hCp
  have hMn : 0 ≤ Cp * ((4 * C1 * s⁻¹ * K) + (4 * C1 * s⁻¹ * K)) := by
    clear * - Cp C1 s K hKs hCpn
    exact mul_nonneg hCpn (by linarith only [hKs])
  have hq := srootNS_lNaught_quarter (Cp := Cp) (C1 := C1)
    (M := Cp * ((4 * C1 * s⁻¹ * K) + (4 * C1 * s⁻¹ * K)))
    (M' := C1 * s⁻¹ * K) (cStar := cStar) (nu := nu) (K := nondeg) (lam := 8 * Cp)
    hCpn h8Cp hMn hKs hMM hnd hc hnu
    (srootNS_quarter_const hC0 hA)
  clear hMn h8Cp hCpn hMM hKs hnd hc hnu hA
  have hmn : 0 ≤ (m : ℝ) := by clear * - m hm64; linarith only [hm64]
  clear hm64
  refine ⟨hln, hnl, ?_, ?_, ?_, ?_⟩
  clear hln
  · linarith only [hL2, hnr]
  · linarith only [hq, hm, hmL, hmn]
  clear hmL
  · linarith only [hq, hm, hnl, hmn]
  clear hmn hq hnl hm
  · have hl1 : 1 ≤ Real.log (L : ℝ) := by linarith only [hlogLlo, hlg4]
    have hKp0 : 0 ≤ 4 * C1 * s⁻¹ * K := by linarith only [hKp1]
    have h1 := srootNS_cube_aux hKp0 hL1r hl1
    have h3 : 2 * (h : ℝ) + l ≤ 2 * (C1 * W0) := by
      have hh2 : (h : ℝ) ≤ 2 * W0 := hhW
      have : (2 + C0) * W0 ≤ C1 * W0 := mul_le_mul_of_nonneg_right (by linarith only [hC1a, hC0]) (by linarith only [hW01])
      linarith only [hh2, hlW, this]
    linarith only [hL2, hnr, h1, hKpL, h3]

/-- Satisfiability of the quarter lemma: `Cp = 1`, `λ = 1`, `M = M' = 1`, `c⋆ = 2`, `ν = 1`. -/
example : SuperdiffusionCLT.Frozen.Section4.lNaught 1 1 (1 / 2) 2 1 1 ≤
    SuperdiffusionCLT.Frozen.Section4.lNaught (2 * 3 ^ 12) 1 (1 / 2) 2 1 1 / 4 :=
  srootNS_lNaught_quarter (Cp := 1) (C1 := 2 * 3 ^ 12) (M := 1) (M' := 1) (lam := 1)
    (by norm_num) le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

end

end SuperdiffusionCLT.Section4.MinimalScales
