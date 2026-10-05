/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Root.InteriorPointwiseB
public import SuperdiffusionCLT.Section7.MinimalScale.GridMaxCount
public import SuperdiffusionCLT.Section7.Analytic.ElementaryB
public import SuperdiffusionCLT.Section7.MinimalScale.GridMaxEnlarge
public import SuperdiffusionCLT.Section7.MinimalScale.GridMaxEnlargeB
public import SuperdiffusionCLT.Section7.MinimalScale.TranslatedInputsB

/-!
# Interior approximation: scale separation and the bound of the field

* `ip_sep`, `ip_win`, `ip_numeric`: for scales `k` large, the numerical hypotheses of
  `ia_approx_det` hold (`3^{-⌈N log k⌉} ≤ k^{-N}`, the window `(N log k + 1) δ_{k-1} ≤ c`, and the
  three scale-separation inequalities), with a dimensional exponent `N`.
* `ia_ae_kb`: almost surely the centred field is bounded by `m^{1+ρ}` on the cube of the standing
  setup (the `L^∞` part of `e.Dir.new.k.bounds`, from the sharp inputs).
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal
open scoped Matrix.Norms.L2Operator

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem ip_rpow_neg_nat' (l : ℕ) : (3 : ℝ) ^ (-(l : ℝ)) = ((3 : ℝ) ^ l)⁻¹ := by
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]

/-- `3^{-⌈N log k⌉} ≤ k^{-N}`. -/
theorem ip_three_pow_ceil_le {N k : ℝ} (hN : 0 ≤ N) (hk : 1 ≤ k) :
    (3 : ℝ) ^ (-(⌈N * Real.log k⌉₊ : ℝ)) ≤ k ^ (-N) := by
  have hk0 : 0 < k := by linarith only [hk]
  have hlog3 : 1 < Real.log 3 := b2c_one_lt_log3
  have h1 : N * Real.log k ≤ (⌈N * Real.log k⌉₊ : ℝ) := Nat.le_ceil _
  have hlk : 0 ≤ N * Real.log k := mul_nonneg hN (Real.log_nonneg hk)
  rw [Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos hk0, Real.exp_le_exp]
  nlinarith only [h1, hlk, hlog3, Real.log_nonneg hk]

/-- **Scale separation.** For `N ≥ A + 1` and `k ≥ c²`, `c k^A 3^{-⌈N log k⌉} ≤ k^{-1/2}`. -/
theorem ip_sep {A c N k : ℝ} (hN : A + 1 ≤ N) (hA : 0 ≤ A) (hc : 0 ≤ c) (hk : 1 ≤ k) (hck : c ^ 2 ≤ k) :
    c * k ^ A * (3 : ℝ) ^ (-(⌈N * Real.log k⌉₊ : ℝ)) ≤ k ^ (-(1 / 2 : ℝ)) := by
  have hk0 : 0 < k := by linarith only [hk]
  have hN0 : 0 ≤ N := by linarith only [hN, hA]
  have h1 := ip_three_pow_ceil_le hN0 hk
  have h2 : c * k ^ A * (3 : ℝ) ^ (-(⌈N * Real.log k⌉₊ : ℝ)) ≤ c * k ^ A * k ^ (-N) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  refine h2.trans ?_
  have h3 : k ^ A * k ^ (-N) = k ^ (A - N) := by rw [← Real.rpow_add hk0]; ring_nf
  have h4 : k ^ (A - N) ≤ k ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hk (by linarith only [hN])
  have hck' : c ≤ k ^ (1 / 2 : ℝ) := by
    have : c = Real.sqrt (c ^ 2) := (Real.sqrt_sq hc).symm
    rw [this, Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow (by positivity) hck (by norm_num)
  calc c * k ^ A * k ^ (-N) = c * (k ^ A * k ^ (-N)) := by ring
    _ ≤ k ^ (1 / 2 : ℝ) * k ^ (-1 : ℝ) := by
        rw [h3]; exact mul_le_mul hck' h4 (by positivity) (by positivity)
    _ = k ^ (-(1 / 2 : ℝ)) := by rw [← Real.rpow_add hk0]; norm_num

/-- **The window is short**: `(N log k + 1) δ_{k-1} ≤ c` for large `k`. -/
theorem ip_win {ε ρ N c : ℝ} (hε : 0 < ε) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) (hN : 0 ≤ N) (hc : 0 < c) :
    ∃ L : ℝ, 3 ≤ L ∧ ∀ k : ℝ, L ≤ k → (N * Real.log k + 1) * deltaScale ε ρ (k - 1) ≤ c := by
  set κ : ℝ := (1 - ρ) / 2 with hκ
  have hκ0 : 0 < κ := by rw [hκ]; linarith only [hρ]
  have hc' : 0 < c / (2 * ε * (N + 1)) := by positivity
  have h := (isLittleO_log_rpow_rpow_atTop 2 hκ0).def hc'
  obtain ⟨L0, hL0⟩ := Filter.eventually_atTop.1 h
  refine ⟨max L0 4, (by norm_num : (3 : ℝ) ≤ 4).trans (le_max_right _ _), fun k hk => ?_⟩
  have hk4 : 4 ≤ k := (le_max_right _ _).trans hk
  have hk3 : 3 ≤ k := by linarith only [hk4]
  have hk0 : 0 < k := by linarith only [hk3]
  have hkL : L0 ≤ k := (le_max_left _ _).trans hk
  have hlog1 : 1 ≤ Real.log k := a23_one_le_log hk4
  have hlogk : Real.log (k - 1) ≤ Real.log k :=
    Real.log_le_log (by linarith only [hk3]) (by linarith only)
  have hlog0 : 0 ≤ Real.log (k - 1) := Real.log_nonneg (by linarith only [hk3])
  have hrp : (k - 1) ^ (-κ) ≤ 2 * k ^ (-κ) := by
    have h1 : k / 2 ≤ k - 1 := by linarith only [hk3]
    have h2 : (k / 2) ^ κ ≤ (k - 1) ^ κ := Real.rpow_le_rpow (by positivity) h1 hκ0.le
    have h22 : (2 : ℝ) ^ κ ≤ 2 := by
      calc (2 : ℝ) ^ κ ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by rw [hκ]; linarith only [hρ0])
        _ = 2 := by norm_num
    have h3 : k ^ κ / 2 ≤ (k - 1) ^ κ := by
      refine le_trans ?_ h2
      rw [Real.div_rpow hk0.le (by norm_num)]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) h22
    rw [Real.rpow_neg (by linarith only [hk3]), Real.rpow_neg hk0.le]
    calc ((k - 1) ^ κ)⁻¹ ≤ (k ^ κ / 2)⁻¹ := inv_anti₀ (by positivity) h3
      _ = 2 * (k ^ κ)⁻¹ := by rw [inv_div, div_eq_mul_inv]
  have hsq := hL0 k hkL
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)] at hsq
  rw [Real.rpow_two] at hsq
  have hNl : N * Real.log k + 1 ≤ (N + 1) * Real.log k := by nlinarith only [hlog1]
  unfold deltaScale
  have hd : ε * (k - 1) ^ (-((1 - ρ) / 2)) * Real.log (k - 1) ≤ ε * (2 * k ^ (-κ)) * Real.log k := by
    rw [← hκ]
    have := mul_le_mul_of_nonneg_left hrp hε.le
    exact mul_le_mul this hlogk hlog0 (by positivity)
  have hD1 : 0 ≤ ε * (k - 1) ^ (-((1 - ρ) / 2)) * Real.log (k - 1) := by
    have : 0 < k - 1 := by linarith only [hk3]
    positivity
  have hk1 : k ^ κ * k ^ (-κ) = 1 := by rw [← Real.rpow_add hk0]; simp
  have hkm : 0 ≤ k ^ (-κ) := by positivity
  calc (N * Real.log k + 1) * (ε * (k - 1) ^ (-((1 - ρ) / 2)) * Real.log (k - 1))
      ≤ ((N + 1) * Real.log k) * (ε * (2 * k ^ (-κ)) * Real.log k) :=
        mul_le_mul hNl hd hD1 (by positivity)
    _ = (2 * ε * (N + 1)) * (Real.log k ^ 2 * k ^ (-κ)) := by ring
    _ ≤ (2 * ε * (N + 1)) * (c / (2 * ε * (N + 1)) * k ^ κ * k ^ (-κ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_right hsq hkm
    _ = (2 * ε * (N + 1) * (c / (2 * ε * (N + 1)))) * (k ^ κ * k ^ (-κ)) := by ring
    _ = c := by rw [hk1]; field_simp

/-- The scale separation, in terms of `τ = 3^l / 3^k` with `l = k - ⌈N log k⌉`. -/
theorem ip_tau {k cn : ℕ} (h : cn ≤ k) :
    (3 : ℝ) ^ (k - cn) / 3 ^ k = (3 : ℝ) ^ (-(cn : ℝ)) := by
  rw [ip_rpow_neg_nat', pow_sub₀ _ (by norm_num) h]
  field_simp

/-- **The first numerical hypothesis of the deterministic core.** -/
theorem ip_num_N1 {CF Cthr nu ε ρ σ δ t T k τ : ℝ} (hCF : 1 ≤ CF) (hCthr : 1 ≤ Cthr)
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hε : 0 < ε) (hρ1 : ρ < 1) (hk : 1 ≤ k)
    (hσ1 : 1 ≤ σ) (hσk : σ ≤ k) (hδk : δ ≤ k) (hδ : ε * k ^ (-(1 / 2 : ℝ)) ≤ δ) (hT : 0 < T)
    (ht : t = τ * T) (hτ0 : 0 ≤ τ)
    (hsep : 12 * Cthr * CF ^ 2 / (nu * ε) * k ^ (2 : ℝ) * τ ≤ k ^ (-(1 / 2 : ℝ))) :
    Cthr * ((CF * Real.sqrt σ * δ * Real.sqrt nu + CF * (|nu - σ| + k ^ (1 + ρ))) *
      (CF * (3 * t) / nu)) ≤ δ * T := by
  have hk0 : 0 < k := by linarith only [hk]
  have ht0 : 0 ≤ t := by rw [ht]; exact mul_nonneg hτ0 hT.le
  have hk2 : k ^ (2 : ℝ) = k * k := by rw [Real.rpow_two]; ring
  have hsq1 : Real.sqrt σ ≤ k := by
    rw [Real.sqrt_le_iff]
    exact ⟨hk0.le, by nlinarith only [hσk, hk]⟩
  have hsn : Real.sqrt nu ≤ 1 := Real.sqrt_le_one.2 hnu1
  have hρk : k ^ (1 + ρ) ≤ k * k := by
    rw [← hk2]
    exact Real.rpow_le_rpow_of_exponent_le hk (by linarith only [hρ1])
  have hδ0 : 0 < δ := lt_of_lt_of_le (by positivity) hδ
  have hin : CF * Real.sqrt σ * δ * Real.sqrt nu + CF * (|nu - σ| + k ^ (1 + ρ)) ≤ 4 * CF * (k * k) := by
    have h1 : CF * Real.sqrt σ * δ * Real.sqrt nu ≤ CF * (k * k) := by
      have : Real.sqrt σ * δ * Real.sqrt nu ≤ k * k * 1 :=
        mul_le_mul (mul_le_mul hsq1 hδk hδ0.le hk0.le) hsn (Real.sqrt_nonneg _) (by positivity)
      calc CF * Real.sqrt σ * δ * Real.sqrt nu = CF * (Real.sqrt σ * δ * Real.sqrt nu) := by ring
        _ ≤ CF * (k * k * 1) := mul_le_mul_of_nonneg_left this (by linarith only [hCF])
        _ = CF * (k * k) := by ring
    have h2 : |nu - σ| + k ^ (1 + ρ) ≤ 3 * (k * k) := by
      have : |nu - σ| ≤ nu + σ := by
        rw [abs_le]; constructor <;> linarith only [hnu, hσ1]
      nlinarith only [this, hρk, hnu1, hσk, hk]
    have h3 := mul_le_mul_of_nonneg_left h2 (by linarith only [hCF] : (0 : ℝ) ≤ CF)
    nlinarith only [h1, h3]
  have hfin : Cthr * ((CF * Real.sqrt σ * δ * Real.sqrt nu + CF * (|nu - σ| + k ^ (1 + ρ))) *
      (CF * (3 * t) / nu)) ≤ Cthr * (4 * CF * (k * k) * (CF * (3 * t) / nu)) := by
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hin (by positivity)) (by linarith only [hCthr])
  refine hfin.trans ?_
  have hε' : 12 * Cthr * CF ^ 2 * k ^ (2 : ℝ) * τ / nu ≤ ε * k ^ (-(1 / 2 : ℝ)) := by
    have := mul_le_mul_of_nonneg_left hsep hε.le
    have e : ε * (12 * Cthr * CF ^ 2 / (nu * ε) * k ^ (2 : ℝ) * τ) =
        12 * Cthr * CF ^ 2 * k ^ (2 : ℝ) * τ / nu := by field_simp
    linarith only [this, e]
  have e2 : Cthr * (4 * CF * (k * k) * (CF * (3 * t) / nu)) =
      (12 * Cthr * CF ^ 2 * k ^ (2 : ℝ) * τ / nu) * T := by
    rw [hk2, ht]; ring
  rw [e2]
  calc (12 * Cthr * CF ^ 2 * k ^ (2 : ℝ) * τ / nu) * T ≤ (ε * k ^ (-(1 / 2 : ℝ))) * T :=
        mul_le_mul_of_nonneg_right hε' hT.le
    _ ≤ δ * T := mul_le_mul_of_nonneg_right hδ hT.le

/-- **The second numerical hypothesis.** -/
theorem ip_num_N2 {Cthr ε δ t T k τ : ℝ} (hCthr : 1 ≤ Cthr) (hε : 0 < ε)
    (hδ : ε * k ^ (-(1 / 2 : ℝ)) ≤ δ) (hT : 0 < T) (ht : t = τ * T)
    (hsep : Cthr / ε * k ^ (0 : ℝ) * τ ≤ k ^ (-(1 / 2 : ℝ))) : Cthr * t ≤ δ * T := by
  rw [Real.rpow_zero, mul_one] at hsep
  have h1 : Cthr * τ ≤ ε * k ^ (-(1 / 2 : ℝ)) := by
    have := mul_le_mul_of_nonneg_left hsep hε.le
    have e : ε * (Cthr / ε * τ) = Cthr * τ := by field_simp
    linarith only [this, e]
  calc Cthr * t = (Cthr * τ) * T := by rw [ht]; ring
    _ ≤ (ε * k ^ (-(1 / 2 : ℝ))) * T := mul_le_mul_of_nonneg_right h1 hT.le
    _ ≤ δ * T := mul_le_mul_of_nonneg_right hδ hT.le

/-- **The third numerical hypothesis.** -/
theorem ip_num_N3 {Cthr cL p nu ε δ σ k τ Lt : ℝ} (hCthr : 1 ≤ Cthr) (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (hε : 0 < ε) (hk : 1 ≤ k) (hσ : σ ≤ k) (hσ0 : 0 < σ) (hcL : 0 ≤ cL)
    (hδ : ε * k ^ (-(1 / 2 : ℝ)) ≤ δ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hLt : Lt ≤ cL * k ^ (4 * p))
    (hsep : 2 * Cthr * cL / (nu * ε) * k ^ (4 * p + 1) * τ ≤ k ^ (-(1 / 2 : ℝ))) :
    Cthr * Lt * (τ + σ / nu * τ ^ 2) ≤ δ := by
  have hk0 : 0 < k := by linarith only [hk]
  have h1 : τ + σ / nu * τ ^ 2 ≤ 2 * k / nu * τ := by
    have : σ / nu * τ ^ 2 ≤ k / nu * τ := by
      have : τ ^ 2 ≤ τ := by nlinarith only [hτ0, hτ1]
      calc σ / nu * τ ^ 2 ≤ σ / nu * τ := mul_le_mul_of_nonneg_left this (by positivity)
        _ ≤ k / nu * τ := by gcongr
    have h2 : τ ≤ k / nu * τ := by
      have : 1 ≤ k / nu := by rw [le_div_iff₀ hnu]; linarith only [hk, hnu1]
      nlinarith only [this, hτ0]
    calc τ + σ / nu * τ ^ 2 ≤ k / nu * τ + k / nu * τ := add_le_add h2 this
      _ = 2 * k / nu * τ := by ring
  have hkp : k ^ (4 * p) * k = k ^ (4 * p + 1) := by
    rw [Real.rpow_add hk0, Real.rpow_one]
  calc Cthr * Lt * (τ + σ / nu * τ ^ 2) ≤ Cthr * (cL * k ^ (4 * p)) * (2 * k / nu * τ) := by
        gcongr
    _ = (2 * Cthr * cL / nu * k ^ (4 * p + 1) * τ) := by rw [← hkp]; ring
    _ ≤ ε * k ^ (-(1 / 2 : ℝ)) := by
        have := mul_le_mul_of_nonneg_left hsep hε.le
        have e : ε * (2 * Cthr * cL / (nu * ε) * k ^ (4 * p + 1) * τ) =
            2 * Cthr * cL / nu * k ^ (4 * p + 1) * τ := by field_simp
        linarith only [this, e]
    _ ≤ δ := hδ

theorem ip_delta_bounds {ε ρ k : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hk : 4 ≤ k) :
    ε * k ^ (-(1 / 2 : ℝ)) ≤ deltaScale ε ρ k ∧ deltaScale ε ρ k ≤ k := by
  have hk1 : 1 ≤ k := by linarith only [hk]
  have hk0 : 0 < k := by linarith only [hk]
  have hlog1 : 1 ≤ Real.log k := a23_one_le_log hk
  have hlogk : Real.log k ≤ k := by
    have := Real.log_le_sub_one_of_pos hk0
    linarith only [this]
  unfold deltaScale
  constructor
  · have h1 : k ^ (-(1 / 2 : ℝ)) ≤ k ^ (-((1 - ρ) / 2)) :=
      Real.rpow_le_rpow_of_exponent_le hk1 (by linarith only [hρ0])
    calc ε * k ^ (-(1 / 2 : ℝ)) ≤ ε * k ^ (-((1 - ρ) / 2)) :=
          mul_le_mul_of_nonneg_left h1 hε.le
      _ = ε * k ^ (-((1 - ρ) / 2)) * 1 := by ring
      _ ≤ ε * k ^ (-((1 - ρ) / 2)) * Real.log k :=
          mul_le_mul_of_nonneg_left hlog1 (by positivity)
  · have h1 : k ^ (-((1 - ρ) / 2)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hk1 (by linarith only [hρ1])
    have h2 : ε * k ^ (-((1 - ρ) / 2)) ≤ 1 := by
      calc ε * k ^ (-((1 - ρ) / 2)) ≤ 1 * 1 := mul_le_mul hε1 h1 (by positivity) zero_le_one
        _ = 1 := by norm_num
    calc ε * k ^ (-((1 - ρ) / 2)) * Real.log k ≤ 1 * Real.log k :=
          mul_le_mul_of_nonneg_right h2 (by linarith only [hlog1])
      _ ≤ k := by linarith only [hlogk]

/-- **The numerical hypotheses of the deterministic core, for large scales.** -/
theorem ip_numeric (d : ℕ) [NeZero d] {Cthr CF c nu ε ρ N : ℝ} (hCthr : 1 ≤ Cthr) (hCF : 1 ≤ CF)
    (hc : 0 < c) (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) (hN : 4 * deGiorgiPower d + 3 ≤ N) (hp : 1 ≤ deGiorgiPower d) :
    ∃ L : ℝ, 4 ≤ L ∧ ∀ k : ℕ, L ≤ (k : ℝ) → ∀ σ : ℝ, 1 ≤ σ → σ ≤ (k : ℝ) →
      ⌈N * Real.log (k : ℝ)⌉₊ ≤ k ∧ nK N k + 5 ≤ k ∧
      (N * Real.log (k : ℝ) + 1) * deltaScale ε ρ ((k : ℝ) - 1) ≤ c ∧
      Cthr * ((CF * Real.sqrt σ * deltaScale ε ρ (k : ℝ) * Real.sqrt nu +
          CF * (|nu - σ| + (k : ℝ) ^ (1 + ρ))) * (CF * (3 : ℝ) ^ (nK N k + 1) / nu)) ≤
        deltaScale ε ρ (k : ℝ) * 3 ^ k ∧
      Cthr * (3 : ℝ) ^ (nK N k) ≤ deltaScale ε ρ (k : ℝ) * 3 ^ k ∧
      Cthr * (((d : ℝ) * d * (nu + (k : ℝ) ^ (1 + ρ)) ^ 2 + nu ^ 2) / nu / nu) ^ deGiorgiPower d *
        ((3 : ℝ) ^ (nK N k) / 3 ^ k + σ / nu * ((3 : ℝ) ^ (nK N k) / 3 ^ k) ^ 2) ≤
        deltaScale ε ρ (k : ℝ) := by
  set p := deGiorgiPower d with hpdef
  have hN1 : 1 ≤ N := by linarith only [hN, hp]
  have hN0 : 0 < N := by linarith only [hN1]
  set cL : ℝ := (((4 * (d : ℝ) ^ 2 + 1)) / nu ^ 2) ^ p with hcL
  set c1 : ℝ := 12 * Cthr * CF ^ 2 / (nu * ε) with hc1
  set c2 : ℝ := Cthr / ε with hc2
  set c3 : ℝ := 2 * Cthr * cL / (nu * ε) with hc3
  obtain ⟨Lw, hLw3, hLw⟩ := ip_win (N := N) (c := c) hε hρ0 hρ1 (by linarith only [hN0]) hc
  obtain ⟨Ll, hLl⟩ := a23_log_le_mul (1 / (4 * N)) (by positivity)
  refine ⟨max (max (max Lw Ll) (max (Real.exp 5) (c1 ^ 2))) (max (c2 ^ 2) (max (c3 ^ 2) 4)), ?_, ?_⟩
  · exact le_max_of_le_right (le_max_of_le_right (le_max_right _ _))
  intro k hk σ hσ1 hσk
  have hkL : ∀ x : ℝ, x ≤ max (max (max Lw Ll) (max (Real.exp 5) (c1 ^ 2))) (max (c2 ^ 2) (max (c3 ^ 2) 4)) → x ≤ k :=
    fun x hx => hx.trans hk
  have hk4 : 4 ≤ (k : ℝ) := hkL 4 (by simp)
  have hkw : Lw ≤ (k : ℝ) := hkL _ (by simp)
  have hkl : Ll ≤ (k : ℝ) := hkL _ (by simp)
  have hke : Real.exp 5 ≤ (k : ℝ) := hkL _ (by simp)
  have hk1c : c1 ^ 2 ≤ (k : ℝ) := hkL _ (by simp)
  have hk2c : c2 ^ 2 ≤ (k : ℝ) := hkL _ (by simp)
  have hk3c : c3 ^ 2 ≤ (k : ℝ) := hkL _ (by simp)
  have hk1 : (1 : ℝ) ≤ k := by linarith only [hk4]
  have hk0 : (0 : ℝ) < k := by linarith only [hk4]
  set cn : ℕ := ⌈N * Real.log (k : ℝ)⌉₊ with hcn
  have hlogk0 : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg hk1
  have hNlog0 : 0 ≤ N * Real.log (k : ℝ) := mul_nonneg hN0.le hlogk0
  have hcn1 : (cn : ℝ) ≤ N * Real.log (k : ℝ) + 1 := (Nat.ceil_lt_add_one hNlog0).le
  have hcn2 : N * Real.log (k : ℝ) ≤ (cn : ℝ) := Nat.le_ceil _
  have hNlog : N * Real.log (k : ℝ) ≤ (k : ℝ) / 4 := by
    have := hLl k hkl
    have h2 := mul_le_mul_of_nonneg_left this hN0.le
    have e : N * (1 / (4 * N) * (k : ℝ)) = (k : ℝ) / 4 := by field_simp
    linarith only [h2, e]
  have hcnk : cn ≤ k := by
    have : (cn : ℝ) ≤ k := by linarith only [hcn1, hNlog, hk4]
    exact_mod_cast this
  have h5 : 5 ≤ cn := by
    have h1 : (5 : ℝ) ≤ Real.log k := (Real.le_log_iff_exp_le hk0).2 hke
    have : (5 : ℝ) ≤ cn := by nlinarith only [hcn2, h1, hN1, hlogk0]
    exact_mod_cast this
  have hnK : nK N k = k - cn := rfl
  have hτ : (3 : ℝ) ^ (nK N k) / 3 ^ k = (3 : ℝ) ^ (-(cn : ℝ)) := by rw [hnK]; exact ip_tau hcnk
  have hτ0 : 0 ≤ (3 : ℝ) ^ (-(cn : ℝ)) := by positivity
  have hτ1 : (3 : ℝ) ^ (-(cn : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith only [(Nat.cast_nonneg cn : (0 : ℝ) ≤ cn)])
  have hT : (0 : ℝ) < 3 ^ k := by positivity
  have ht : (3 : ℝ) ^ (nK N k) = (3 : ℝ) ^ (-(cn : ℝ)) * 3 ^ k := by
    rw [← hτ]; field_simp
  obtain ⟨hδ1, hδ2⟩ := ip_delta_bounds hε hε1 hρ0 hρ1 hk4
  have hsep1 := ip_sep (A := 2) (c := c1) (N := N) (k := (k : ℝ)) (by linarith only [hN, hp]) (by norm_num)
    (by positivity) hk1 hk1c
  have hsep2 := ip_sep (A := 0) (c := c2) (N := N) (k := (k : ℝ)) (by linarith only [hN, hp]) le_rfl
    (by positivity) hk1 hk2c
  have hcL0 : 0 ≤ cL := by positivity
  have hsep3 := ip_sep (A := 4 * p + 1) (c := c3) (N := N) (k := (k : ℝ)) (by linarith only [hN]) (by linarith only [hp])
    (by positivity) hk1 hk3c
  refine ⟨hcnk, by omega, hLw _ hkw, ?_, ?_, ?_⟩
  · have h3 : (3 : ℝ) ^ (nK N k + 1) = 3 * 3 ^ (nK N k) := by ring
    rw [h3]
    exact ip_num_N1 hCF hCthr hnu hnu1 hε hρ1 hk1 hσ1 hσk hδ2 hδ1 hT ht hτ0 hsep1
  · exact ip_num_N2 hCthr hε hδ1 hT ht hsep2
  · rw [hτ]
    refine ip_num_N3 (cL := cL) (p := p) hCthr hnu hnu1 hε hk1 hσk (by linarith only [hσ1]) hcL0 hδ1 hτ0 hτ1 ?_ hsep3
    -- the bound of the ellipticity ratio
    have hB : (k : ℝ) ^ (1 + ρ) ≤ (k : ℝ) ^ 2 := by
      have : (k : ℝ) ^ (1 + ρ) ≤ (k : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hk1 (by linarith only [hρ1])
      rwa [Real.rpow_two] at this
    have hB0 : 0 ≤ (k : ℝ) ^ (1 + ρ) := by positivity
    have hbase : ((d : ℝ) * d * (nu + (k : ℝ) ^ (1 + ρ)) ^ 2 + nu ^ 2) / nu / nu ≤
        (4 * (d : ℝ) ^ 2 + 1) / nu ^ 2 * (k : ℝ) ^ 4 := by
      have h1 : (nu + (k : ℝ) ^ (1 + ρ)) ^ 2 ≤ 4 * (k : ℝ) ^ 4 := by
        have : nu + (k : ℝ) ^ (1 + ρ) ≤ 2 * (k : ℝ) ^ 2 := by nlinarith only [hB, hnu1, hk1]
        nlinarith only [this, hnu, hB0]
      have h2 : (d : ℝ) * d * (nu + (k : ℝ) ^ (1 + ρ)) ^ 2 + nu ^ 2 ≤
          (4 * (d : ℝ) ^ 2 + 1) * (k : ℝ) ^ 4 := by
        have hdd : (0 : ℝ) ≤ (d : ℝ) * d := by positivity
        have : (1 : ℝ) ≤ (k : ℝ) ^ 4 := one_le_pow₀ hk1
        nlinarith only [mul_le_mul_of_nonneg_left h1 hdd, this, hnu1, hnu]
      rw [div_div, show (nu * nu) = nu ^ 2 by ring, div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
      exact h2
    calc (((d : ℝ) * d * (nu + (k : ℝ) ^ (1 + ρ)) ^ 2 + nu ^ 2) / nu / nu) ^ p
        ≤ ((4 * (d : ℝ) ^ 2 + 1) / nu ^ 2 * (k : ℝ) ^ 4) ^ p :=
          Real.rpow_le_rpow (by positivity) hbase (by linarith only [hp])
      _ = cL * (k : ℝ) ^ (4 * p) := by
          have e4 : ((k : ℝ) ^ 4) ^ p = (k : ℝ) ^ (4 * p) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hk0.le]; norm_num
          rw [Real.mul_rpow (by positivity) (by positivity), hcL, e4]

/-- An almost-everywhere statement on the origin cube, read on its translate. -/
theorem ip_ae_translate {P : Vec d → Prop} (y : Vec d) (m : ℕ)
    (h : ∀ᵐ x ∂(normalizedCubeMeasure (originCube d (m : ℤ))), P (y + x)) :
    ∀ᵐ x ∂(volume.restrict (shiftCube y (m : ℤ))), P x := by
  have h1 : ∀ᵐ x ∂(volume.restrict (cubeSet (originCube d (m : ℤ)))), P (y + x) := by
    have : normalizedCubeMeasure (originCube d (m : ℤ)) =
        ENNReal.ofReal (cubeVolume (originCube d (m : ℤ)))⁻¹ • volume.restrict (cubeSet (originCube d (m : ℤ))) := by
      rw [normalizedCubeMeasure, cubeMeasure]
    rw [this] at h
    have hne : ENNReal.ofReal (cubeVolume (originCube d (m : ℤ)))⁻¹ ≠ 0 := by
      have : 0 < cubeVolume (originCube d (m : ℤ)) := cubeVolume_pos _
      exact (ENNReal.ofReal_pos.2 (inv_pos.2 this)).ne'
    exact (Measure.absolutelyContinuous_smul hne).ae_le h
  have h2 : ∀ᵐ x ∂(volume.restrict (l2b_cell y m)), P x := by
    have hmp := measurePreserving_addRight_restrict_translateSet y (cubeSet (originCube d (m : ℤ)))
    have hemb : MeasurableEmbedding (fun x : Vec d => x + y) := (Homeomorph.addRight y).measurableEmbedding
    have := (hemb.ae_map_iff (μ := volume.restrict (cubeSet (originCube d (m : ℤ)))) (p := P)).2
      (h1.mono fun x hx => by simpa only [add_comm] using hx)
    rw [hmp.map_eq] at this
    exact this
  rw [← ip_restrict_cell]
  exact h2

/-- **The bound of the field.** -/
theorem ia_ae_kb (d : ℕ) [NeZero d]
    (hInputs :
        ∃ C : ℝ, 1 ≤ C ∧
        ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
        ∀ cStar : ℝ, 0 < cStar →
        ∀ K : ℝ,
        ∀ ε ρ M : ℝ, 0 < ε → ε ≤ 1 → 0 < ρ → ρ < 1 → C ≤ M →
        ∃ Lhat : ℝ, 1 ≤ Lhat ∧
        ∀ (P : MeasureTheory.ProbabilityMeasure
        (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
        (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
        (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
        (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K
        hPrefix hJ2 hJ3 →
        ∃ X0 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
        Measurable X0 ∧ (∀ omega, 1 ≤ X0 omega) ∧
        Homogenization.IndependentSums.IsBigO P.toMeasure
        (Homogenization.IndependentSums.gammaSigma ρ)
        (fun omega => Real.log (X0 omega)) Lhat ∧
        ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
        ∀ m n : ℕ,
        X0 omega ≤ (3 : ℝ) ^ m →
        Lhat ≤ (m : ℝ) →
        (m : ℤ) - ⌈M * Real.log (m : ℝ)⌉ ≤ (n : ℤ) →
        n ≤ m →
        (∀ k : Fin d → ℤ,
        (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
        Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)) ⊆
        Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)) →
        -- e.Dir.new.full.good
        Homogenization.HomogenizationErrorOnCube
        (Homogenization.originCube d (n : ℤ)) (1 / 9)
        Homogenization.MultiscaleExponent.infinity
        (Homogenization.MultiscaleExponent.finite 2)
        (fun x => nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
        (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))
        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))
        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P •
        (1 : Homogenization.Mat d)) ≤
        ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ) ∧
        -- e.Dir.new.reg.ellipticity
        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ *
        Homogenization.LambdaSq (Homogenization.originCube d (n : ℤ))
        (1 / 4) (Homogenization.MultiscaleExponent.finite 1)
        (fun x => nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField
        omega
        (Homogenization.cubeSet
        (Homogenization.originCube d (m : ℤ)))
        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)) +
        SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P *
        (Homogenization.lambdaSq (Homogenization.originCube d (n : ℤ))
        (1 / 4) (Homogenization.MultiscaleExponent.finite 1)
        (fun x => nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField
        omega
        (Homogenization.cubeSet
        (Homogenization.originCube d (m : ℤ)))
        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)))⁻¹ ≤
        C ∧
        -- e.Dir.new.weak.flux, e.Dir.new.weak.grad, e.Dir.new.harmonic.approx
        (∀ u : Homogenization.AHarmonicFunction
        (fun x => nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
        (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))
        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))
        (Homogenization.openCubeSet (Homogenization.originCube d (n : ℤ))),
        ENNReal.ofReal
        (Homogenization.Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
        (Homogenization.originCube d (n : ℤ)) (1 / 4)
        (fun x => Homogenization.matVecMul
        (nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField
        omega
        (Homogenization.cubeSet
        (Homogenization.originCube d (m : ℤ)))
        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) -
        SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
        nu m P • (1 : Homogenization.Mat d))
        (u.toH1.grad x))) ≤
        ENNReal.ofReal
        (C *
        Real.sqrt
        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
        nu m P) *
        (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)) *
        Real.sqrt nu) *
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm
        (Homogenization.originCube d (n : ℤ)) 2
        (fun x => Real.sqrt (Homogenization.vecNormSq (u.toH1.grad x))) ∧
        ENNReal.ofReal
        (Homogenization.Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
        (Homogenization.originCube d (n : ℤ)) (1 / 4) u.toH1.grad) ≤
        ENNReal.ofReal
        (C *
        (Real.sqrt
        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
        nu m P))⁻¹ *
        Real.sqrt nu) *
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm
        (Homogenization.originCube d (n : ℤ)) 2
        (fun x => Real.sqrt (Homogenization.vecNormSq (u.toH1.grad x))) ∧
        ∃ w : Homogenization.AHarmonicFunction
        (fun _ => (1 : Homogenization.Mat d))
        (Homogenization.openCubeSet
        (Homogenization.originCube d ((n : ℤ) - 1))),
        ENNReal.ofReal ((3 : ℝ) ^ (-(n : ℝ))) *
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm
        (Homogenization.originCube d ((n : ℤ) - 1)) 2
        (fun x => u.toH1.toFun x - w.toH1.toFun x) ≤
        ENNReal.ofReal
        (C * (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)) *
        (Real.sqrt
        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
        nu m P))⁻¹ *
        Real.sqrt nu) *
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm
        (Homogenization.originCube d (n : ℤ)) 2
        (fun x =>
        Real.sqrt (Homogenization.vecNormSq (u.toH1.grad x)))) ∧
        -- e.Dir.new.sstar.close
        Homogenization.matNorm
        ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
        nu m P)⁻¹ •
        Homogenization.sigmaCoarse
        (Homogenization.cubeSet
        (Homogenization.originCube d (n : ℤ)))
        (fun x => nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField
        omega
        (Homogenization.cubeSet
        (Homogenization.originCube d (m : ℤ)))
        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)) -
        1) +
        Homogenization.matNorm
        ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
        nu m P)⁻¹ •
        Homogenization.sigmaStarCoarse
        (Homogenization.cubeSet
        (Homogenization.originCube d (n : ℤ)))
        (fun x => nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField
        omega
        (Homogenization.cubeSet
        (Homogenization.originCube d (m : ℤ)))
        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)) -
        1) ≤
        C * (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ))) ∧
        -- e.Dir.new.k.bounds
        ENNReal.ofReal ((m : ℝ)⁻¹) *
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm
        (Homogenization.originCube d (m : ℤ)) ∞
        (SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
        (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))) +
        ENNReal.ofReal ((3 : ℝ) ^ (-((1 / 4 : ℝ) * (m : ℝ)))) *
        SuperdiffusionCLT.Section2.Norms.matHatNegENorm
        (Homogenization.originCube d (m : ℤ)) (1 / 4) 2
        (SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
        (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))) ≤
        ENNReal.ofReal ((m : ℝ) ^ ρ))
    :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ nu : ℝ, 0 < nu → nu ≤ 1 → ∀ cStar : ℝ, 0 < cStar → ∀ K : ℝ,
      ∀ ε ρ : ℝ, 0 < ε → ε ≤ 1 → 0 < ρ → ρ < 1 →
      ∃ Lhat : ℝ, 1 ≤ Lhat ∧ ∀ (P : MeasureTheory.ProbabilityMeasure
        (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
        (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
        (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
        (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
        ∃ X0 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ, Measurable X0 ∧
          (∀ omega, 1 ≤ X0 omega) ∧
          Homogenization.IndependentSums.IsBigO P.toMeasure
            (Homogenization.IndependentSums.gammaSigma ρ) (fun omega => Real.log (X0 omega)) Lhat ∧
        ∀ y : Vec d, ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
          ∀ m : ℕ,
          X0 (SuperdiffusionCLT.Frozen.Assumptions.ShellField.translateSequence y omega) ≤
            (3 : ℝ) ^ m → Lhat ≤ (m : ℝ) →
          ∀ᵐ x ∂(volume.restrict (shiftCube y (m : ℤ))),
            Book.Ch02.matrixOperatorNorm
              (SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
                (translateSet y (cubeSet (originCube d (m : ℤ)))) x) ≤ (m : ℝ) ^ (1 + ρ) := by
  obtain ⟨Cb, hCb, H⟩ := b2_translated_inputs d hInputs
  refine ⟨Cb, hCb, fun nu hnu hnu1 cStar hcStar K ε ρ hε hε1 hρ hρ1 => ?_⟩
  obtain ⟨Lhat, hL, H2⟩ := H nu hnu hnu1 cStar hcStar K ε ρ Cb hε hε1 hρ hρ1 le_rfl
  refine ⟨Lhat, hL, fun P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 => ?_⟩
  obtain ⟨X0, hm, h1, hO, hae⟩ := H2 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  refine ⟨X0, hm, h1, hO, fun y => ?_⟩
  filter_upwards [hae y] with omega hω
  intro m hX hLm
  have hm1 : (1 : ℝ) ≤ m := hL.trans hLm
  have hn1 : (m : ℤ) - ⌈Cb * Real.log (m : ℝ)⌉ ≤ (m : ℤ) := by
    have : (0 : ℤ) ≤ ⌈Cb * Real.log (m : ℝ)⌉ :=
      Int.ceil_nonneg (mul_nonneg (by linarith only [hCb]) (Real.log_nonneg hm1))
    omega
  obtain ⟨-, hkb⟩ := hω m m hX hLm hn1 le_rfl
  have hae2 := r1_ae_opnorm_k (originCube d (m : ℤ)) (g := fun x =>
    SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
      (translateSet y (cubeSet (originCube d (m : ℤ)))) (y + x)) (m := (m : ℝ)) (ρ := ρ) hm1 _ hkb
  exact ip_ae_translate (P := fun x => Book.Ch02.matrixOperatorNorm
    (SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
      (translateSet y (cubeSet (originCube d (m : ℤ)))) x) ≤ (m : ℝ) ^ (1 + ρ)) y m hae2

end SuperdiffusionCLT.Section7
