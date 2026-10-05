/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Linfty.SmoothB
public import SuperdiffusionCLT.Section7.Linfty.Field

/-!
# The `L^∞` proposition for a smooth datum

`linf_smooth`: the `L^∞` proposition for the Dirichlet problem with a smooth datum
`g̃`, almost surely and uniformly in the dilation `R ∈ (3^n / 3, 3^n]`, from the inputs of
the sharp scale, the window of `σ̄` and the boundary Lipschitz estimate at the centres of a fine
grid. The comparison scale is `nK N n`, with `N` from the scale separation for the exponent
`A₀ = 6 p + 20`, `p` the De Giorgi power; the constant `C` of the statement is chosen after `N`
and after the constant of the boundary Lipschitz estimate, and its exponent `E = 2 C` after `C`.
-/

@[expose] public section

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff (ShellSeq)
open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)
open scoped ENNReal Pointwise
open scoped Matrix.Norms.L2Operator

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The De Giorgi power is at least one. -/
theorem linf_smooth_one_le_power (hd : 2 ≤ d) : 1 ≤ deGiorgiPower d := by
  rcases Nat.lt_or_ge d 3 with h | h
  · have : d = 2 := by omega
    subst this
    rw [deGiorgiPower_two]; norm_num
  · rw [deGiorgiPower_of_three_le h]
    have : (3 : ℝ) ≤ d := by exact_mod_cast h
    linarith only [this]

/-- `log 3 ≥ 1`. -/
theorem linf_smooth_one_le_log_three : (1 : ℝ) ≤ Real.log 3 :=
  SuperdiffusionCLT.Section2.Estimates.Stream.one_lt_log_three.le

/-- The window of the comparison scale: `k - nK N k ≤ (N + 1) log k`. -/
theorem linf_smooth_window {N : ℝ} (hN : 0 ≤ N) {k : ℕ} (hk : 3 ≤ k) :
    (k : ℝ) - (nK N k : ℝ) ≤ (N + 1) * Real.log (k : ℝ) := by
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hlog : 1 ≤ Real.log (k : ℝ) :=
    linf_smooth_one_le_log_three.trans (Real.log_le_log (by norm_num) hk3)
  have h1 : k ≤ nK N k + ⌈N * Real.log (k : ℝ)⌉₊ := by unfold nK; omega
  have h2 : (k : ℝ) ≤ (nK N k : ℝ) + (⌈N * Real.log (k : ℝ)⌉₊ : ℝ) := by exact_mod_cast h1
  have h3 : (⌈N * Real.log (k : ℝ)⌉₊ : ℝ) < N * Real.log (k : ℝ) + 1 :=
    Nat.ceil_lt_add_one (mul_nonneg hN (by linarith only [hlog]))
  nlinarith only [h2, h3, hlog]

/-- The smoothing factor: `k^{-2C} 3^k ≤ 3 · 3^{nK C k}`. -/
theorem linf_smooth_Epow {C : ℝ} (hC : 0 ≤ C) {k : ℕ} (hk : 1 ≤ k) :
    (k : ℝ) ^ (-(2 * C)) * (3 : ℝ) ^ k ≤ 3 * (3 : ℝ) ^ nK C k := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith only [hk1]
  have hlog0 : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg hk1
  set c : ℕ := ⌈C * Real.log (k : ℝ)⌉₊ with hc
  have h1 : k ≤ nK C k + c := by unfold nK; omega
  have h2 : (3 : ℝ) ^ k ≤ (3 : ℝ) ^ nK C k * (3 : ℝ) ^ c := by
    rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) h1
  have h3 : (3 : ℝ) ^ c ≤ 3 * (3 : ℝ) ^ (C * Real.log (k : ℝ)) := by
    have hcl : (c : ℝ) ≤ C * Real.log (k : ℝ) + 1 :=
      (Nat.ceil_lt_add_one (mul_nonneg hC hlog0)).le
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hcl
    rw [Real.rpow_natCast, Real.rpow_add (by norm_num), Real.rpow_one] at this
    linarith only [this]
  have h4 : (3 : ℝ) ^ (C * Real.log (k : ℝ)) ≤ (k : ℝ) ^ (2 * C) := by
    rw [Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos hk0]
    refine Real.exp_le_exp.2 ?_
    have hl3 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
      linarith only [this]
    have : 0 ≤ C * Real.log (k : ℝ) := mul_nonneg hC hlog0
    nlinarith only [this, hl3]
  have hkp : 0 < (k : ℝ) ^ (-(2 * C)) := Real.rpow_pos_of_pos hk0 _
  have hkk : (k : ℝ) ^ (-(2 * C)) * (k : ℝ) ^ (2 * C) = 1 := by
    rw [← Real.rpow_add hk0]; simp
  calc (k : ℝ) ^ (-(2 * C)) * (3 : ℝ) ^ k
      ≤ (k : ℝ) ^ (-(2 * C)) * ((3 : ℝ) ^ nK C k * (3 * (k : ℝ) ^ (2 * C))) := by
        gcongr
        exact h2.trans (mul_le_mul_of_nonneg_left (h3.trans (by linarith only [h4]))
          (by positivity))
    _ = 3 * (3 : ℝ) ^ nK C k * ((k : ℝ) ^ (-(2 * C)) * (k : ℝ) ^ (2 * C)) := by ring
    _ = 3 * (3 : ℝ) ^ nK C k := by rw [hkk, mul_one]

/-- The geometric threshold: `B₀ 3^{nK N k} ≤ 3^k` once `B₀ ≤ k`. -/
theorem linf_smooth_B0 {N B₀ : ℝ} (hN : 1 ≤ N) {k : ℕ} (hk : 3 ≤ (k : ℝ))
    (hk4 : 4 * N ^ 2 ≤ (k : ℝ)) (hB : B₀ ≤ (k : ℝ)) :
    B₀ * (3 : ℝ) ^ nK N k ≤ (3 : ℝ) ^ k := by
  have hN3 : 1 ≤ N * Real.log 3 := by
    have := linf_smooth_one_le_log_three
    nlinarith only [this, hN]
  obtain ⟨-, hck, hk3c⟩ := l2e_ceil_facts (lt_of_lt_of_le one_pos hN) hN3 hk hk4
  have e : (3 : ℝ) ^ k = (3 : ℝ) ^ nK N k * (3 : ℝ) ^ ⌈N * Real.log (k : ℝ)⌉₊ := by
    rw [← pow_add]; unfold nK; congr 1; omega
  rw [e, mul_comm B₀]
  exact mul_le_mul_of_nonneg_left (hB.trans hk3c) (by positivity)

/-- The scale ratio: `3^{nK N k} / 3^k = 3^{-⌈N log k⌉₊}` when `⌈N log k⌉₊ ≤ k`. -/
theorem linf_smooth_ratio {N : ℝ} {k : ℕ} (hc : ⌈N * Real.log (k : ℝ)⌉₊ ≤ k) :
    (3 : ℝ) ^ nK N k / (3 : ℝ) ^ k = (3 : ℝ) ^ (-(⌈N * Real.log (k : ℝ)⌉₊ : ℝ)) := by
  have e : (3 : ℝ) ^ k = (3 : ℝ) ^ nK N k * (3 : ℝ) ^ ⌈N * Real.log (k : ℝ)⌉₊ := by
    rw [← pow_add]; unfold nK; congr 1; omega
  rw [e, Real.rpow_neg (by norm_num), Real.rpow_natCast]
  field_simp

/-- The ellipticity constants of the centred field: with `Λ = (ν + C_f k^{1+ρ})² / ν`,
`ν ≤ Λ ≤ (1 + C_f)² k⁵` and `(Λ/ν)^{p+1} ≤ ((1 + C_f)²)^{p+1} k^{6(p+1)}`. -/
theorem linf_smooth_Lambda {k ν ρ Cf p : ℝ} (hk : 1 ≤ k) (hν : 0 < ν) (hkν : 1 ≤ k * ν)
    (hν1 : ν ≤ 1) (hρ1 : ρ ≤ 1) (hCf : 0 ≤ Cf) (hp : 0 ≤ p) :
    ν ≤ (ν + Cf * k ^ (1 + ρ)) ^ 2 / ν ∧
      (ν + Cf * k ^ (1 + ρ)) ^ 2 / ν ≤ (1 + Cf) ^ 2 * k ^ 5 ∧
      ((ν + Cf * k ^ (1 + ρ)) ^ 2 / ν / ν) ^ (p + 1) ≤
        ((1 + Cf) ^ 2) ^ (p + 1) * k ^ (6 * (p + 1)) := by
  have hk0 : 0 < k := lt_of_lt_of_le one_pos hk
  have hνi : ν⁻¹ ≤ k := by
    calc ν⁻¹ = ν⁻¹ * 1 := (mul_one _).symm
      _ ≤ ν⁻¹ * (k * ν) := mul_le_mul_of_nonneg_left hkν (inv_nonneg.2 hν.le)
      _ = k := by field_simp
  have hx0 : 0 ≤ Cf * k ^ (1 + ρ) := by positivity
  have hk2 : k ^ (1 + ρ) ≤ k ^ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le hk (show 1 + ρ ≤ (2 : ℝ) by linarith only [hρ1])
    rwa [Real.rpow_two] at this
  have hk21 : 1 ≤ k ^ 2 := one_le_pow₀ hk
  have hsum : ν + Cf * k ^ (1 + ρ) ≤ (1 + Cf) * k ^ 2 := by
    have : Cf * k ^ (1 + ρ) ≤ Cf * k ^ 2 := mul_le_mul_of_nonneg_left hk2 hCf
    nlinarith only [this, hν1, hk21]
  have hs0 : 0 ≤ ν + Cf * k ^ (1 + ρ) := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [le_div_iff₀ hν]
    nlinarith only [hx0, hν]
  · calc (ν + Cf * k ^ (1 + ρ)) ^ 2 / ν = (ν + Cf * k ^ (1 + ρ)) ^ 2 * ν⁻¹ := div_eq_mul_inv _ _
      _ ≤ ((1 + Cf) * k ^ 2) ^ 2 * k := by gcongr
      _ = (1 + Cf) ^ 2 * k ^ 5 := by ring
  · have hr : (ν + Cf * k ^ (1 + ρ)) ^ 2 / ν / ν ≤ (1 + Cf) ^ 2 * k ^ 6 := by
      calc (ν + Cf * k ^ (1 + ρ)) ^ 2 / ν / ν = ((ν + Cf * k ^ (1 + ρ)) * ν⁻¹) ^ 2 := by
            field_simp
        _ ≤ ((1 + Cf) * k ^ 2 * k) ^ 2 := by gcongr
        _ = (1 + Cf) ^ 2 * k ^ 6 := by ring
    have hr0 : 0 ≤ (ν + Cf * k ^ (1 + ρ)) ^ 2 / ν / ν := by positivity
    calc ((ν + Cf * k ^ (1 + ρ)) ^ 2 / ν / ν) ^ (p + 1)
        ≤ ((1 + Cf) ^ 2 * k ^ 6) ^ (p + 1) := Real.rpow_le_rpow hr0 hr (by linarith only [hp])
      _ = ((1 + Cf) ^ 2) ^ (p + 1) * (k ^ 6) ^ (p + 1) := Real.mul_rpow (by positivity) (by positivity)
      _ = ((1 + Cf) ^ 2) ^ (p + 1) * k ^ (6 * (p + 1)) := by
          rw [← Real.rpow_natCast_mul hk0.le]
          norm_num

/-- The smallness of the non-leading terms: `C_p ((c_q k^{a_q} + 1) k^{11}) τ ≤ δ_k` from the scale
separation `k^{A₀} τ ≤ k^{-2}`, `a_q + 11 ≤ A₀`, once `k ≥ C_p (c_q + 1) / ε`. -/
theorem linf_smooth_varpi {k ε ρ Cp cq aq A₀ τ : ℝ} (hk : 3 ≤ k) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hCp : 0 ≤ Cp) (hcq : 0 ≤ cq) (haq : 0 ≤ aq) (hA : aq + 11 ≤ A₀)
    (hτ0 : 0 ≤ τ) (hsc : k ^ A₀ * τ ≤ k ^ (-2 : ℝ)) (hkε : Cp * (cq + 1) / ε ≤ k) :
    Cp * ((cq * k ^ aq + 1) * k ^ 11) * τ ≤ deltaScale ε ρ k := by
  have hk1 : 1 ≤ k := by linarith only [hk]
  have hk0 : 0 < k := by linarith only [hk]
  have h11 : k ^ 11 = k ^ (11 : ℝ) := (Real.rpow_natCast k 11).symm
  have hQ : (cq * k ^ aq + 1) * k ^ 11 ≤ (cq + 1) * k ^ A₀ := by
    rw [h11]
    have e : (cq * k ^ aq + 1) * k ^ (11 : ℝ) = cq * k ^ (aq + 11) + k ^ (11 : ℝ) := by
      rw [Real.rpow_add hk0]; ring
    rw [e]
    have h1 : k ^ (aq + 11) ≤ k ^ A₀ := Real.rpow_le_rpow_of_exponent_le hk1 hA
    have h2 : k ^ (11 : ℝ) ≤ k ^ A₀ := Real.rpow_le_rpow_of_exponent_le hk1 (by linarith only [hA, haq])
    have h3 := mul_le_mul_of_nonneg_left h1 hcq
    linarith only [h2, h3]
  have hδ := (l2e_delta_bounds hk hε hε1 hρ hρ1).1
  have hm : Cp * (cq + 1) * k ^ (-2 : ℝ) ≤ ε * k ^ (-(1 / 2 : ℝ)) := by
    have e : k ^ (-(1 / 2 : ℝ)) = k ^ (3 / 2 : ℝ) * k ^ (-2 : ℝ) := by
      rw [← Real.rpow_add hk0]; norm_num
    rw [e, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hk0.le _)
    have h1 : Cp * (cq + 1) ≤ ε * k := by rw [div_le_iff₀ hε] at hkε; linarith only [hkε]
    have h2 : k ≤ k ^ (3 / 2 : ℝ) := by
      have := Real.rpow_le_rpow_of_exponent_le hk1 (show (1 : ℝ) ≤ 3 / 2 by norm_num)
      rwa [Real.rpow_one] at this
    nlinarith only [h1, h2, hε]
  calc Cp * ((cq * k ^ aq + 1) * k ^ 11) * τ ≤ Cp * ((cq + 1) * k ^ A₀) * τ := by gcongr
    _ = Cp * (cq + 1) * (k ^ A₀ * τ) := by ring
    _ ≤ Cp * (cq + 1) * k ^ (-2 : ℝ) := mul_le_mul_of_nonneg_left hsc (by positivity)
    _ ≤ ε * k ^ (-(1 / 2 : ℝ)) := hm
    _ ≤ deltaScale ε ρ k := hδ

/-- `δ_k → 0`: for every `c > 0` there is a threshold beyond which `δ_k ≤ c` for every `ε ≤ 1`. -/
theorem linf_smooth_delta_small {ρ c : ℝ} (hρ1 : ρ < 1) (hc : 0 < c) :
    ∃ k₀ : ℝ, 1 ≤ k₀ ∧ ∀ k ε : ℝ, k₀ ≤ k → 0 < ε → ε ≤ 1 → deltaScale ε ρ k ≤ c := by
  set a : ℝ := (1 - ρ) / 4 with ha
  have ha0 : 0 < a := by rw [ha]; linarith only [hρ1]
  refine ⟨max 1 (((a * c)⁻¹) ^ (1 / a)), le_max_left _ _, ?_⟩
  intro k ε hk hε hε1
  have hk1 : 1 ≤ k := (le_max_left _ _).trans hk
  have hk0 : 0 < k := lt_of_lt_of_le one_pos hk1
  have hlog : Real.log k ≤ k ^ a / a := Real.log_le_rpow_div hk0.le ha0
  have hlog0 : 0 ≤ Real.log k := Real.log_nonneg hk1
  have e1 : -((1 - ρ) / 2) = -(2 * a) := by rw [ha]; ring
  have hka : (a * c)⁻¹ ≤ k ^ a := by
    have h1 : ((a * c)⁻¹ ^ (1 / a)) ^ a ≤ k ^ a :=
      Real.rpow_le_rpow (by positivity) ((le_max_right _ _).trans hk) ha0.le
    rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel ha0.ne', Real.rpow_one] at h1
  have hkpos : 0 < k ^ a := Real.rpow_pos_of_pos hk0 a
  unfold deltaScale
  rw [e1]
  have e2 : k ^ (-(2 * a)) * (k ^ a / a) = (k ^ a)⁻¹ / a := by
    rw [show -(2 * a) = -a + -a by ring, Real.rpow_add hk0, Real.rpow_neg hk0.le]
    field_simp
  calc ε * k ^ (-(2 * a)) * Real.log k ≤ 1 * k ^ (-(2 * a)) * (k ^ a / a) := by gcongr
    _ = (k ^ a)⁻¹ / a := by rw [one_mul, e2]
    _ ≤ c := by
        rw [div_le_iff₀ ha0, inv_le_comm₀ hkpos (by positivity)]
        rw [mul_comm] at hka
        exact hka

/-- The window of the boundary Lipschitz estimate at `m' = k - 1`, `B = 2N`. -/
theorem linf_smooth_lipwin {N : ℝ} (hN : 0 ≤ N) {k j : ℕ} (hk : 3 ≤ k) (hj : nK N k ≤ j) :
    ((k - 1 : ℕ) : ℝ) - 2 * N * Real.log ((k - 1 : ℕ) : ℝ) ≤ (j : ℝ) := by
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have ec : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [ec]
  have hlogk : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by linarith only [hk3])
  have h1 : k ≤ nK N k + ⌈N * Real.log (k : ℝ)⌉₊ := by unfold nK; omega
  have h2 : (k : ℝ) ≤ (nK N k : ℝ) + (⌈N * Real.log (k : ℝ)⌉₊ : ℝ) := by exact_mod_cast h1
  have h3 : (⌈N * Real.log (k : ℝ)⌉₊ : ℝ) < N * Real.log (k : ℝ) + 1 :=
    Nat.ceil_lt_add_one (mul_nonneg hN hlogk)
  have hjr : (nK N k : ℝ) ≤ j := by exact_mod_cast hj
  have hlog2 : Real.log (k : ℝ) ≤ 2 * Real.log ((k : ℝ) - 1) := by
    rw [← Real.log_rpow (by linarith only [hk3])]
    refine Real.log_le_log (by linarith only [hk3]) ?_
    rw [Real.rpow_two]
    nlinarith only [hk3]
  have h4 : N * Real.log (k : ℝ) ≤ 2 * N * Real.log ((k : ℝ) - 1) := by
    have := mul_le_mul_of_nonneg_left hlog2 hN
    linarith only [this]
  linarith only [h2, h3, hjr, h4]

/-- The window of the sharp inputs: `k - ⌈M log k⌉ ≤ nK N k` for `N ≤ M`. -/
theorem linf_smooth_inwin {N M : ℝ} (hN : 0 ≤ N) (hNM : N ≤ M) {k : ℕ} (hk : 1 ≤ k)
    (hc : ⌈N * Real.log (k : ℝ)⌉₊ ≤ k) :
    (k : ℤ) - ⌈M * Real.log (k : ℝ)⌉ ≤ (nK N k : ℤ) := by
  have hlog : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast hk)
  have h1 : ⌈N * Real.log (k : ℝ)⌉ ≤ ⌈M * Real.log (k : ℝ)⌉ :=
    Int.ceil_mono (mul_le_mul_of_nonneg_right hNM hlog)
  have h2 : ((⌈N * Real.log (k : ℝ)⌉₊ : ℕ) : ℤ) = ⌈N * Real.log (k : ℝ)⌉ :=
    Int.natCast_ceil_eq_ceil (mul_nonneg hN hlog)
  have h3 : ((nK N k : ℕ) : ℤ) = (k : ℤ) - ((⌈N * Real.log (k : ℝ)⌉₊ : ℕ) : ℤ) := by
    unfold nK; omega
  rw [h3, h2]
  linarith only [h1]

private theorem linf_sc_nat_a (k : ℕ) : k ≤ 2 * k := by omega

private theorem linf_sc_nat_b {m k : ℕ} (h : m + 5 ≤ k) : m + 1 ≤ k := by omega

private theorem linf_sc_nat_c {m j k : ℕ} (h : j ≤ m + 3) (hm : m + 5 ≤ k) : j < k - 1 := by
  omega

private theorem linf_sc_Cp_nonneg {Kp Cin cθ cΛ : ℝ} (hKp : 0 ≤ Kp) (hCin : 0 ≤ Cin)
    (hcθ : 0 ≤ cθ) : 0 ≤ linfCp Kp Cin cθ cΛ := by
  unfold linfCp; positivity

/-- **The `L^∞` proposition for a smooth datum**, from the inputs
and the boundary Lipschitz estimate on a fine grid of centres. -/
theorem linf_smooth (d : ℕ) [NeZero d] (hd : 2 ≤ d)
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
    (hS5 :
        ∃ C : ℝ, 1 ≤ C ∧
        ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
        ∀ cStar : ℝ, 0 < cStar →
        ∀ K : ℝ,
        ∃ M : ℕ,
        ∀ (P : MeasureTheory.ProbabilityMeasure
        (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
        (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
        (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
        (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K
        hPrefix hJ2 hJ3 →
        ∀ m : ℕ, M ≤ m →
        |SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P -
        (2 * cStar * Real.log 3 * (m : ℝ)) ^ ((1 : ℝ) / 2)| ≤
        C * cStar⁻¹ * (Real.log (m : ℝ) ^ (2 : ℝ) + K))
    (hLipB :
    ∀ U : Set (Vec d), IsSmoothBoundedDomain U → U ⊆ openCubeSet (originCube d 0) →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ nu : ℝ, 0 < nu → nu ≤ 1 → ∀ cStar : ℝ, 0 < cStar → ∀ K : ℝ,
      ∀ ε ρ : ℝ, 0 < ε → ε ≤ 1 → 0 < ρ → ρ < 1 →
      ∀ (A s : ℕ) (B E : ℝ), 0 ≤ B → 0 ≤ E →
      ∃ Lhat : ℝ, 1 ≤ Lhat ∧ ∀ (P : ProbabilityMeasure (ShellSeq d)) (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
        (hJ3 : ShellLawJ3 d P), ShellLawJ1Restriction d P → ShellLawJ4 d P →
        ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
        ∃ X : ShellSeq d → ℝ, Measurable X ∧ (∀ omega, 1 ≤ X omega) ∧
        Homogenization.IndependentSums.IsBigO P.toMeasure
          (Homogenization.IndependentSums.gammaSigma ρ) (fun omega => Real.log (X omega)) Lhat ∧
        ∀ᵐ omega ∂P.toMeasure, ∀ m n m' : ℕ, n < m' → m' ≤ m → m ≤ m' + A →
          (m' : ℝ) - B * Real.log (m' : ℝ) ≤ (n : ℝ) → Lhat ≤ (n : ℝ) → X omega ≤ (3 : ℝ) ^ n →
          ∀ t : ℝ, (3 : ℝ) ^ m' ≤ t → t ≤ (3 : ℝ) ^ m →
          ∀ z ∈ gridPts d ((n : ℤ) - s) ((3 : ℝ) ^ (m + 2)), z ∈ t • U →
          ∀ (f g : Vec d → ℝ), ContDiff ℝ 2 g →
          ∀ u : H1Function (shiftCube z (m' : ℤ) ∩ t • U),
            IsWeakSolutionOn (Section6.fullCoefficientRecentered nu omega)
              (shiftCube z (m' : ℤ) ∩ t • U) u f (fun _ => 0) →
            LocalizedZeroTraceFunctionOn (shiftCube z (m' : ℤ) ∩ t • U)
              (shiftCube z (m' : ℤ)) (fun x => u.toFun x - g x) →
            ∀ R : ℝ≥0∞,
              R = ENNReal.ofReal (C * (3 : ℝ) ^ (-(m' : ℝ))) *
                  (lpBar (shiftCube z (m' : ℤ) ∩ t • U) 2
                      (fun x => u.toFun x - ⨍ w in shiftCube z (m' : ℤ) ∩ t • U, u.toFun w) +
                    lpBar (shiftCube z (m' : ℤ) ∩ t • U) 2 (fun x => u.toFun x - g x)) +
                ENNReal.ofReal (C * (sigmaBarInfinite nu m P)⁻¹ * (3 : ℝ) ^ m') *
                  eLpNorm f ⊤ (volume.restrict (shiftCube z (m' : ℤ) ∩ t • U)) +
                ENNReal.ofReal (C * ((m' : ℝ) - (n : ℝ))) *
                  eLpNorm (fun x => ‖fderiv ℝ g x‖) ⊤ (volume.restrict (shiftCube z (m' : ℤ))) +
                ENNReal.ofReal (C * (m : ℝ) ^ (-E) * (3 : ℝ) ^ m') *
                  eLpNorm (fun x => ‖fderiv ℝ (fderiv ℝ g) x‖) ⊤
                    (volume.restrict (shiftCube z (m' : ℤ))) →
            -- e.Dir.new.C01.boundary, with the oscillation kept on the left
            ENNReal.ofReal ((Real.sqrt (sigmaBarInfinite nu m P))⁻¹ * Real.sqrt nu) *
                  lpBar (shiftCube z (n : ℤ) ∩ t • U) 2 (fun x => eucNorm (u.grad x)) +
                ENNReal.ofReal ((3 : ℝ) ^ (-(n : ℝ))) *
                  lpBar (shiftCube z (n : ℤ) ∩ t • U) 2
                    (fun x => u.toFun x - ⨍ w in shiftCube z (n : ℤ) ∩ t • U, u.toFun w) ≤ R ∧
              -- on a cube that meets the boundary, the solution itself is flat relative to `g`
              (¬ shiftCube z (n : ℤ) ⊆ t • U →
                ENNReal.ofReal ((3 : ℝ) ^ (-(n : ℝ))) *
                  lpBar (shiftCube z (n : ℤ) ∩ t • U) 2 (fun x => u.toFun x - g x) ≤ R)) :
    ∀ U : Set (Vec d), IsSmoothBoundedDomain U → U ⊆ kc2_Q0 d →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ nu : ℝ, 0 < nu → nu ≤ 1 → ∀ cStar : ℝ, 0 < cStar → ∀ K : ℝ,
      ∀ ε ρ : ℝ, 0 < ε → ε ≤ 1 → 0 < ρ → ρ < 1 →
      ∃ Lhat : ℝ, 1 ≤ Lhat ∧ ∀ (P : ProbabilityMeasure (ShellSeq d)) (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
        (hJ3 : ShellLawJ3 d P), ShellLawJ1Restriction d P → ShellLawJ4 d P →
        ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
        ∃ X0 : ShellSeq d → ℝ, Measurable X0 ∧ (∀ omega, 1 ≤ X0 omega) ∧
        Homogenization.IndependentSums.IsBigO P.toMeasure
          (Homogenization.IndependentSums.gammaSigma ρ) (fun omega => Real.log (X0 omega)) Lhat ∧
        ∀ᵐ omega ∂P.toMeasure, ∀ (n : ℕ) (R : ℝ), C ≤ (n : ℝ) → Lhat ≤ (nK C n : ℝ) →
          X0 omega ≤ (3 : ℝ) ^ nK C n → (3 : ℝ) ^ n < 3 * R → R ≤ (3 : ℝ) ^ n →
          ∀ (f gt : Vec d → ℝ) (F G : ℝ), ContDiff ℝ (⊤ : ℕ∞) gt → 0 ≤ F → 0 ≤ G →
            AEStronglyMeasurable f (volume.restrict (R • U)) →
            (∀ᵐ x ∂volume.restrict (R • U), |f x| ≤ F) → (∀ x, ‖fderiv ℝ gt x‖ ≤ G) →
            (∀ x, ‖fderiv ℝ (fderiv ℝ gt) x‖ ≤ G / (3 : ℝ) ^ nK C n) →
          ∀ v vh : H1Function (R • U),
            IsWeakSolutionOn (Section6.fullCoefficientRecentered nu omega) (R • U) v f
              (fun _ => 0) →
            MemH10 (R • U) (fun x => v.toFun x - gt x) →
            IsWeakSolutionOn (fun _ => sigmaBarInfinite nu n P • (1 : Mat d)) (R • U) vh f
              (fun _ => 0) →
            MemH10 (R • U) (fun x => vh.toFun x - gt x) →
            eLpNorm (fun x => v.toFun x - vh.toFun x) ⊤ (volume.restrict (R • U)) +
                hMinusOneVec (R • U) (fun x => v.grad x - vh.grad x) +
                hMinusOneVec (R • U) (fun x =>
                  matVecMul ((sigmaBarInfinite nu n P)⁻¹ •
                    (Section6.fullCoefficientRecentered nu omega x -
                      volumeAverageMat (cubeSet (originCube d (n : ℤ)))
                        (Section6.fullStreamRecentered omega))) (v.grad x) - vh.grad x) ≤
              ENNReal.ofReal (C * deltaScale ε ρ (n : ℝ) *
                ((sigmaBarInfinite nu n P)⁻¹ * (3 : ℝ) ^ (2 * n) * F +
                  Real.log (n : ℝ) * (3 : ℝ) ^ n * G)) := by

  intro U hU hUQ
  have hU0 : U ⊆ openCubeSet (originCube d 0) := linf_smooth_hU0 hU.1 hUQ
  obtain ⟨s0, B₀, Cd, Cloc, CH, cθ, hB₀, hCd, hCloc, hCH, hcθ, Hs⟩ :=
    linf_smooth_sample hd hU hU0
  obtain ⟨Cin, hCin, Hin⟩ := l2b_ae_cell d hd hInputs
  obtain ⟨Cf, hCf, Hf⟩ := linf_field d hd hInputs
  obtain ⟨Cl, hCl, Hlip⟩ := hLipB U hU hU0
  have hp1 := linf_smooth_one_le_power hd
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  set p : ℝ := deGiorgiPower d with hp
  set A₀ : ℝ := 6 * p + 20 with hA₀
  obtain ⟨N, hN1, HN⟩ := linf_scale_choice A₀ 2 (1 / (2 * (d : ℝ)))
    (by rw [hA₀]; linarith only [hp1]) (by norm_num) (by positivity)
  have hN0 : 0 ≤ N := by linarith only [hN1]
  have hKp0 : 0 ≤ l2e_Kp d := by
    have hB : 0 ≤ l2e_bumpB d := (abs_nonneg _).trans (l2e_bump_bound d 0)
    unfold l2e_Kp
    positivity
  set Y₀ : ℝ := Cd * (l2e_Kp d * Cin + 1) * (Cloc * Cl * (CH + N + 7)) with hY₀
  have hY₀0 : 0 ≤ Y₀ := by
    have h1 : 0 ≤ Cin := by linarith only [hCin]
    have h2 : 0 ≤ Cl := by linarith only [hCl]
    exact mul_nonneg (mul_nonneg hCd (add_nonneg (mul_nonneg hKp0 h1) zero_le_one))
      (mul_nonneg (mul_nonneg hCloc h2) (add_nonneg (add_nonneg hCH hN0) (by norm_num)))
  set C₁ : ℝ := 2 * Cd * (l2e_Kp d * Cin + 1) * (Cloc * Cl * (CH + N + 7) + 1) with hC₁
  set C : ℝ := max C₁ (N + 1) with hCdef
  have hC1 : C₁ ≤ C := le_max_left _ _
  have hCN : N + 1 ≤ C := le_max_right _ _
  have hC0 : 0 ≤ C := by linarith only [hCN, hN0]
  refine ⟨C, by linarith only [hCN, hN1], ?_⟩
  intro nu hnu hnu1 cStar hcStar Kc ε ρ hε hε1 hρ hρ1
  set M : ℝ := max (max Cin Cf) N with hM
  have hCinM : Cin ≤ M := (le_max_left _ _).trans (le_max_left _ _)
  have hCfM : Cf ≤ M := (le_max_right _ _).trans (le_max_left _ _)
  have hNM : N ≤ M := le_max_right _ _
  obtain ⟨L1, hL1, H1⟩ := Hin nu hnu hnu1 cStar hcStar Kc ε ρ M hε hε1 hρ hρ1 hCinM
  obtain ⟨L2, hL2, H2⟩ := Hf nu hnu hnu1 cStar hcStar Kc ε ρ M hε hε1 hρ hρ1 hCfM
  obtain ⟨L3, hL3, H3⟩ := Hlip nu hnu hnu1 cStar hcStar Kc ε ρ hε hε1 hρ hρ1 1 s0 (2 * N)
    (2 * C) (mul_nonneg zero_le_two hN0) (mul_nonneg zero_le_two hC0)
  obtain ⟨Lσ, Hσ⟩ := lip_sigma_window d hd hS5 nu hnu hnu1 cStar hcStar Kc
  set cΛ : ℝ := (1 + Cf) ^ 2 with hcΛ
  set cq : ℝ := ((1 + Cf) ^ 2) ^ (p + 1) with hcq
  have hcq0 : 0 ≤ cq := Real.rpow_nonneg (by positivity) _
  set Cp : ℝ := linfCp (l2e_Kp d) Cin cθ cΛ with hCp
  have hCp0 : 0 ≤ Cp := by
    have : 0 ≤ Cin := by linarith only [hCin]
    exact linf_sc_Cp_nonneg hKp0 this hcθ
  obtain ⟨kδ, hkδ1, Hδ⟩ := linf_smooth_delta_small hρ1 (c := 1 / (2 * (Y₀ + 1)))
    (one_div_pos.2 (mul_pos two_pos (add_pos_of_nonneg_of_pos hY₀0 one_pos)))
  set cρ : ℝ := (3 * Real.log (2 : ℝ)) ^ ρ⁻¹ with hcρ
  have hcρ0 : 0 ≤ cρ := Real.rpow_nonneg
    (by have := Real.log_pos (one_lt_two : (1 : ℝ) < 2); positivity) _
  set L12 : ℝ := cρ * (L1 + L2) with hL12
  set Lsc : ℝ := cρ * (L12 + L3) with hLsc
  set Lhat : ℝ := max (max Lsc (max L1 (max L2 L3))) (max (max (Lσ : ℝ) (1 / nu))
    (max (max kδ (Cp * (cq + 1) / ε)) (max B₀ (max (4 * N ^ 2) 3)))) with hLhat
  have hall : Lsc ≤ Lhat ∧ L1 ≤ Lhat ∧ L2 ≤ Lhat ∧ L3 ≤ Lhat ∧ (Lσ : ℝ) ≤ Lhat ∧
      1 / nu ≤ Lhat ∧ kδ ≤ Lhat ∧ Cp * (cq + 1) / ε ≤ Lhat ∧ B₀ ≤ Lhat ∧ 4 * N ^ 2 ≤ Lhat ∧
      (3 : ℝ) ≤ Lhat := by
    simp only [hLhat, le_max_iff, le_refl, true_or, or_true, and_self]
  obtain ⟨hLsc, hLL1, hLL2, hLL3, hLσ, hLν, hLδ, hLε, hLB, hLN, hL3'⟩ := hall
  refine ⟨Lhat, by linarith only [hL3'], ?_⟩
  intro P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨X1, hX1m, hX11, hX1O, hae1⟩ := H1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨X2, hX2m, hX21, hX2O, hae2⟩ := H2 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨X3, hX3m, hX31, hX3O, hae3⟩ := H3 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  have hO12 := Section6.l9_log_max_bigO hρ (by linarith only [hL1]) (by linarith only [hL2])
    le_rfl hX21 hX1O hX2O
  have hO := Section6.l9_log_max_bigO hρ (by positivity) (by linarith only [hL3]) hLsc hX31
    hO12 hX3O
  refine ⟨fun ω => max (max (X1 ω) (X2 ω)) (X3 ω), (hX1m.max hX2m).max hX3m,
    fun ω => le_max_of_le_left (le_max_of_le_left (hX11 ω)), hO, ?_⟩
  filter_upwards [hae1, hae2, hae3, Section6.ae_centered_eq_recentered_add_skew hJ3 nu] with
    ω h1 h2 h3 hsk
  intro k R hCk hLk hXk hR1 hR2 f gt F G hgt hF hG hfm hfF hgtG hgt2G v vh hv hvmem hvh hvhmem
  -- the scale
  have hnCk : nK C k ≤ k := nK_le C k
  have hkL : Lhat ≤ (k : ℝ) := hLk.trans (by exact_mod_cast hnCk)
  have hk3 : (3 : ℝ) ≤ k := hL3'.trans hkL
  have hk3n : 3 ≤ k := by exact_mod_cast hk3
  have hk1 : (1 : ℝ) ≤ k := by linarith only [hk3]
  have hk0 : (0 : ℝ) < k := by linarith only [hk3]
  have hk1n : 1 ≤ k := Nat.le_trans (by norm_num) hk3n
  have hN3 : 1 ≤ N * Real.log 3 := by
    have := linf_smooth_one_le_log_three
    nlinarith only [this, hN1]
  obtain ⟨-, hck, -⟩ := l2e_ceil_facts (lt_of_lt_of_le one_pos hN1) hN3 hk3 (hLN.trans hkL)
  set m : ℕ := nK N k with hm
  have hnCm : nK C k ≤ m := by
    have := linf_scale_nK_le_sub hN0 0 (by simp only [Nat.cast_zero, add_zero]; exact hCN) hk3n
    simpa using this
  have hmB : B₀ * (3 : ℝ) ^ m ≤ (3 : ℝ) ^ k :=
    linf_smooth_B0 hN1 hk3 (hLN.trans hkL) (hLB.trans hkL)
  have hm5 : m + 5 ≤ k := by
    have h1 : (3 : ℝ) ^ (m + 5) ≤ (3 : ℝ) ^ k := by
      have e : (3 : ℝ) ^ (m + 5) = 243 * (3 : ℝ) ^ m := by ring
      rw [e]
      have : 243 * (3 : ℝ) ^ m ≤ B₀ * (3 : ℝ) ^ m :=
        mul_le_mul_of_nonneg_right hB₀ (by positivity)
      linarith only [this, hmB]
    exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1 h1
  have hX0m : max (max (X1 ω) (X2 ω)) (X3 ω) ≤ (3 : ℝ) ^ m :=
    hXk.trans (pow_le_pow_right₀ (by norm_num) hnCm)
  have hX1k : X1 ω ≤ (3 : ℝ) ^ k :=
    ((le_max_left _ _).trans (le_max_left _ _)).trans
      (hX0m.trans (pow_le_pow_right₀ (by norm_num) ((Nat.le_add_right m 5).trans hm5)))
  have hX2k : X2 ω ≤ (3 : ℝ) ^ k :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans
      (hX0m.trans (pow_le_pow_right₀ (by norm_num) ((Nat.le_add_right m 5).trans hm5)))
  have hX3m : X3 ω ≤ (3 : ℝ) ^ m := (le_max_right _ _).trans hX0m
  have hLm : Lhat ≤ (m : ℝ) := hLk.trans (by exact_mod_cast hnCm)
  -- the window of `σ̄`
  set σ : ℝ := sigmaBarInfinite nu k P with hσdef
  obtain ⟨hσ1, hσk, -, -⟩ := Hσ P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 k k
    (by exact_mod_cast (hLσ.trans hkL)) le_rfl (linf_sc_nat_a k)
  -- the inputs at the sample
  have hR0 : 0 < R := by
    have : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
    linarith only [hR1, this]
  have hWK := (linf_smooth_dom hU0 hR0 hR2).1
  obtain ⟨hid, hell⟩ := h2 k hX2k (hLL2.trans hkL)
  obtain ⟨K₀, hK₀s, hK₀⟩ := hsk k
  have hcellw := h1 k m hX1k (hLL1.trans hkL) (linf_smooth_inwin hN0 hNM hk1n hck)
    (linf_sc_nat_b hm5) (R • U) hWK
  have hηs : ∀ w : Vec d, (∃ i, 1 < |w i|) → li1_bump d w = 0 := (l2c_mollifier_witness d).2.2.2
  -- the numerical thresholds
  have hkν : 1 ≤ (k : ℝ) * nu := by
    have h := hLν.trans hkL
    rw [div_le_iff₀ hnu] at h
    exact h
  have hδb := l2e_delta_bounds hk3 hε hε1 hρ hρ1
  have hδ0 : 0 ≤ deltaScale ε ρ k := le_trans (by positivity) hδb.1
  obtain ⟨hΛ1, hΛ2, hΛ3⟩ := linf_smooth_Lambda (k := (k : ℝ)) (ρ := ρ) (Cf := Cf) (p := p) hk1
    hnu hkν hnu1 hρ1.le (by linarith only [hCf]) (by linarith only [hp1])
  have hsc : (k : ℝ) ^ A₀ * ((3 : ℝ) ^ m / (3 : ℝ) ^ k) ^ (1 / (2 * (d : ℝ))) ≤
      (k : ℝ) ^ (-2 : ℝ) := by
    rw [linf_smooth_ratio hck]
    have h := HN k hk3n 1 1 one_pos (by rw [inv_le_one₀ hk0]; exact hk1) one_pos hk1
    simp only [Real.one_rpow, mul_one] at h
    exact h
  have hϖ := linf_smooth_varpi (k := (k : ℝ)) (ε := ε) (ρ := ρ) (Cp := Cp) (cq := cq)
    (aq := 6 * (p + 1)) (A₀ := A₀) hk3 hε hε1 hρ hρ1 hCp0 hcq0 (by linarith only [hp1])
    (by rw [hA₀]; linarith only [hp1]) (Real.rpow_nonneg (by positivity) _) hsc
    (hLε.trans hkL)
  have hsmall : Y₀ * deltaScale ε ρ k ≤ 1 / 2 := by
    have hδs := Hδ k ε (hLδ.trans hkL) hε hε1
    calc Y₀ * deltaScale ε ρ k ≤ Y₀ * (1 / (2 * (Y₀ + 1))) :=
          mul_le_mul_of_nonneg_left hδs hY₀0
      _ ≤ 1 / 2 := by
          rw [mul_one_div, div_le_div_iff₀ (mul_pos two_pos (add_pos_of_nonneg_of_pos hY₀0 one_pos))
            (by norm_num)]
          linarith only [hY₀0]
  have h3k1R : (3 : ℝ) ^ (k - 1) ≤ R := by
    have e : (3 : ℝ) ^ k = 3 * (3 : ℝ) ^ (k - 1) := by
      rw [← pow_succ']; congr 1; exact (Nat.sub_add_cancel hk1n).symm
    linarith only [hR1, e]
  have hD0 : 0 ≤ σ⁻¹ * (3 : ℝ) ^ (2 * k) * F + Real.log (k : ℝ) * (3 : ℝ) ^ k * G := by
    have hlg : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg hk1
    have hσ0 : 0 ≤ σ := by linarith only [hσ1]
    exact add_nonneg (mul_nonneg (mul_nonneg (inv_nonneg.2 hσ0) (pow_nonneg (by norm_num) _)) hF)
      (mul_nonneg (mul_nonneg hlg (pow_nonneg (by norm_num) _)) hG)
  refine (Hs (Section6.fullCoefficientRecentered nu ω)
    (fun x => nu • (1 : Mat d) +
      SuperdiffusionCLT.Section2.Carriers.centeredStreamField ω
        (cubeSet (originCube d (k : ℤ))) x) K₀
    (volumeAverageMat (cubeSet (originCube d (k : ℤ))) (Section6.fullStreamRecentered ω))
    nu σ ((nu + Cf * (k : ℝ) ^ (1 + ρ)) ^ 2 / nu) cΛ (cq * (k : ℝ) ^ (6 * (p + 1))) Cin Cl N
    (2 * C) (deltaScale ε ρ k) ρ k m (nK C k) R hnu hnu1 hkν hσ1 hσk hk3 hδ0 hδb.2 hρ1.le hCin
    hCl hN0 (by positivity) hΛ1 hΛ2 hΛ3 hmB (linf_smooth_window hN0 hk3n)
    (linf_smooth_Epow hC0 hk1n) hϖ hsmall hR1 hR2 hK₀s (fun x => hK₀ x) (fun x => hid x)
    hell ?_ f gt F G hgt hF hG hfm hfF hgtG hgt2G ?_ v vh hv hvmem hvh hvhmem).trans ?_
  · intro u f' hfm' hsol kk hcs x hx
    obtain ⟨b1, b3⟩ := hcellw u f' hfm' hsol (li1_bump d) (l2e_bumpB d) (l2e_bumpL d)
      (l2e_bump_bound d) (l2e_bump_lipschitz d) hηs kk hcs x hx
    simp only [zpow_natCast] at b1 b3
    rw [← hσdef] at b1 b3
    constructor
    · refine b1.trans (le_of_eq ?_)
      simp only [l2e_b, l2e_aC, deltaScale, l2e_Kp, pow_succ]
      ring_nf
    · refine b3.trans (le_of_eq ?_)
      simp only [l2e_b, l2e_aC, l2e_e, l2e_g, deltaScale, l2e_Kp, pow_succ]
      ring_nf
  · intro j hj1 hj2 z hz hzU u hu hloc Rr hRr
    exact h3 k j (k - 1) (linf_sc_nat_c hj2 hm5) (Nat.sub_le k 1)
      (Nat.sub_add_cancel hk1n).symm.le (linf_smooth_lipwin hN0 hk3n hj1)
      (hLL3.trans (hLm.trans (by exact_mod_cast hj1)))
      (hX3m.trans (pow_le_pow_right₀ (by norm_num) hj1)) R h3k1R hR2 z hz hzU f gt
      (hgt.of_le (by simp)) u hu hloc Rr hRr
  · refine ENNReal.ofReal_le_ofReal ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC1 hδ0) hD0

/-- Witness: the two inputs are exactly the hypotheses `hInputs` and `hS5`, so the
statement holds as soon as the boundary Lipschitz estimate does. -/
example [NeZero d] (hd : 2 ≤ d) :=
  linf_smooth d hd (SuperdiffusionCLT.Frozen.Section6.sharp_scale_inputs d hd)
    (SuperdiffusionCLT.Frozen.Section5.sigmaBar_sharp_bounds d hd)

end SuperdiffusionCLT.Section7
