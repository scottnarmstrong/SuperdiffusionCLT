/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Root.FirstRootC
public import SuperdiffusionCLT.Section7.Analytic.ElementaryB
public import SuperdiffusionCLT.Section7.MinimalScale.RootScalesC

/-!
# The numerics of the first root

* The scalar replacement `S_ε ↔ shom_K` with constants independent of the sequence `shom`, and
  the lower bound `shom_K ≥ ½ (2 c⋆ log 3 K)^{1/2}`.
* The comparison of `S_ε` with the scale at the dilated parameter `ε / T`.
* The powers of the scale in the coefficients of the chain.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization MeasureTheory
open scoped ENNReal Pointwise

/-- **The scalar replacement, uniformly in the sequence `shom`.** -/
theorem s5_scalar_numerics {cStar C0 Kc : ℝ} (hc : 0 < cStar) (hC0 : 0 ≤ C0) {M : ℕ}
    {α : ℝ} (hα : α < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ K₀ : ℕ, ∀ shom : ℕ → ℝ,
      (∀ m : ℕ, M ≤ m → |shom m - (2 * cStar * Real.log 3 * (m : ℝ)) ^ ((1 : ℝ) / 2)| ≤
        C0 * cStar⁻¹ * (Real.log (m : ℝ) ^ (2 : ℝ) + Kc)) →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → (3 : ℝ) ^ K₀ ≤ ε⁻¹ →
      0 < shom (s12_scaleK ε) ∧ s12_scaleS cStar ε / shom (s12_scaleK ε) ≤ 2 ∧
      |s12_scaleS cStar ε / shom (s12_scaleK ε) - 1| ≤ C * (s12_scaleK ε : ℝ) ^ (-α) ∧
      Real.sqrt (2 * cStar * Real.log 3 * (s12_scaleK ε : ℝ)) / 2 ≤ shom (s12_scaleK ε) := by
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set A : ℝ := 2 * cStar * Real.log 3 with hA
  have hA0 : 0 < A := by positivity
  set κ : ℝ := Real.sqrt A with hκ
  have hκ0 : 0 < κ := Real.sqrt_pos.2 hA0
  set Θ : ℝ := 2 * C0 * cStar⁻¹ * (64 + |Kc|) / κ with hΘ
  have hΘ0 : 0 ≤ Θ := by positivity
  set C : ℝ := (2 * C0 * cStar⁻¹ / κ) * (1 / ((1 / 2 - α) / 4) ^ 2 + |Kc|) + 2 with hCdef
  have hC0' : 0 < C := by positivity
  refine ⟨C, hC0', max M ⌈Θ ^ 4⌉₊ + 1, ?_⟩
  intro shom hsh ε hε hε2 hK0
  obtain ⟨hR1, hR2, hK1⟩ := s12_scaleK_bounds hε hε2
  obtain ⟨hx1, hx2⟩ := s12_scaleK_x hε hε2
  have hx0 := s12_logb_pos hε hε2
  set K := s12_scaleK ε with hK
  set k : ℝ := (K : ℝ) with hk
  have hk1 : 1 ≤ k := by rw [hk]; exact_mod_cast hK1
  have hk0 : 0 < k := by linarith only [hk1]
  have hK0K : max M ⌈Θ ^ 4⌉₊ + 1 ≤ K := by
    have := hK0.trans hR1
    exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1 this
  have hMK : M ≤ K := by
    have := le_max_left M ⌈Θ ^ 4⌉₊
    omega
  have hΘK : Θ ^ 4 ≤ k := by
    have h1 := le_max_right M ⌈Θ ^ 4⌉₊
    have h2 : ⌈Θ ^ 4⌉₊ ≤ K := by omega
    calc Θ ^ 4 ≤ (⌈Θ ^ 4⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ k := by rw [hk]; exact_mod_cast h2
  -- the fourth root
  set q : ℝ := k ^ (1 / 4 : ℝ) with hq
  have hq1 : 1 ≤ q := Real.one_le_rpow hk1 (by norm_num)
  have hΘq : Θ ≤ q := by
    have h1 := Real.rpow_le_rpow (by positivity) hΘK (by norm_num : (0 : ℝ) ≤ 1 / 4)
    have h2 : (Θ ^ 4) ^ (1 / 4 : ℝ) = Θ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hΘ0]
      norm_num
    rwa [h2] at h1
  have hq2 : q ^ 2 = Real.sqrt k := by
    rw [hq, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hk0.le]
    norm_num
  -- T = κ q²
  set T : ℝ := Real.sqrt (A * k) with hT
  have hTe : T = κ * q ^ 2 := by
    rw [hT, hκ, hq2, Real.sqrt_mul hA0.le]
  have hTanchor : (2 * cStar * Real.log 3 * k) ^ ((1 : ℝ) / 2) = T := by
    rw [hT, Real.sqrt_eq_rpow, hA]
  obtain ⟨hST, hTpos, hTS⟩ := s12_sqrt_compare hA0 hk1 hx0 (by linarith only [hx2]) hx1
  have hSeq : s12_scaleS cStar ε = Real.sqrt (A * Real.logb 3 ε⁻¹) := by
    rw [s12_scaleS_eq hε hε2, hA]
  rw [← hSeq] at hST hTS
  -- the anchor
  have hanchor := hsh K hMK
  rw [← hk, hTanchor, Real.rpow_two] at hanchor
  set E : ℝ := C0 * cStar⁻¹ * (Real.log k ^ 2 + Kc) with hE
  -- E is at most T / 2
  have hlog := s12_log_sq_le hk1 (by norm_num : (0 : ℝ) < 1 / 8)
  have hlog' : Real.log k ^ 2 ≤ 64 * q := by
    have : k ^ (2 * (1 / 8 : ℝ)) = q := by rw [hq]; norm_num
    rw [this] at hlog
    have e : q / (1 / 8 : ℝ) ^ 2 = 64 * q := by norm_num; ring
    linarith only [hlog, e]
  have hKc : Kc ≤ |Kc| * q := by
    calc Kc ≤ |Kc| := le_abs_self _
      _ = |Kc| * 1 := (mul_one _).symm
      _ ≤ |Kc| * q := mul_le_mul_of_nonneg_left hq1 (abs_nonneg _)
  have hEq : E ≤ C0 * cStar⁻¹ * ((64 + |Kc|) * q) := by
    rw [hE]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith only [hlog', hKc]
  have hET : E ≤ T / 2 := by
    refine hEq.trans ?_
    have h1 : C0 * cStar⁻¹ * ((64 + |Kc|) * q) = (Θ * κ / 2) * q := by
      rw [hΘ]
      field_simp
    rw [h1, hTe]
    have h2 : Θ * κ / 2 * q ≤ q * κ / 2 * q := by
      refine mul_le_mul_of_nonneg_right ?_ (by linarith only [hq1])
      have := mul_le_mul_of_nonneg_right hΘq hκ0.le
      linarith only [this]
    linarith only [h2]
  obtain ⟨hshp, hrat, hbound⟩ := s12_ratio_core hTpos hST hTS hanchor hET
  refine ⟨hshp, hrat, ?_, ?_⟩
  · refine hbound.trans ?_
    -- 2E/T + 2(A/T)/T ≤ C k^{-α}
    have hTsq : T = κ * Real.sqrt k := by rw [hTe, hq2]
    have h1 : 2 * (A / T) / T = 2 / k := by
      have : T * T = A * k := Real.mul_self_sqrt (mul_pos hA0 hk0).le
      calc 2 * (A / T) / T = 2 * A / (T * T) := by field_simp
        _ = 2 * A / (A * k) := by rw [this]
        _ = 2 / k := by field_simp
    have h2 : 2 / k ≤ 2 * k ^ (-α) := by
      have : k ^ (-α) ≥ 1 / k := by
        rw [one_div, ← Real.rpow_neg_one]
        exact Real.rpow_le_rpow_of_exponent_le hk1 (by linarith only [hα])
      calc 2 / k = 2 * (1 / k) := by ring
        _ ≤ 2 * k ^ (-α) := mul_le_mul_of_nonneg_left this (by norm_num)
    have h3 : 2 * E / T ≤ (2 * C0 * cStar⁻¹ / κ) * ((1 / ((1 / 2 - α) / 4) ^ 2 + |Kc|) * k ^ (-α)) := by
      have hEq' : E ≤ C0 * cStar⁻¹ * (Real.log k ^ 2 + |Kc|) := by
        rw [hE]
        exact mul_le_mul_of_nonneg_left (by linarith only [le_abs_self Kc]) (by positivity)
      have hrb := s12_rate_bound hk1 hα (abs_nonneg Kc)
      have e : 2 * E / T = (2 / κ) * (E / Real.sqrt k) := by
        rw [hTsq]
        field_simp
      calc 2 * E / T = (2 / κ) * (E / Real.sqrt k) := e
        _ ≤ (2 / κ) * ((C0 * cStar⁻¹ * (Real.log k ^ 2 + |Kc|)) / Real.sqrt k) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact div_le_div_of_nonneg_right hEq' (Real.sqrt_nonneg _)
        _ = (2 * C0 * cStar⁻¹ / κ) * ((Real.log k ^ 2 + |Kc|) / Real.sqrt k) := by ring
        _ ≤ (2 * C0 * cStar⁻¹ / κ) * ((1 / ((1 / 2 - α) / 4) ^ 2 + |Kc|) * k ^ (-α)) :=
          mul_le_mul_of_nonneg_left hrb (by positivity)
    rw [h1]
    have : C * k ^ (-α) = (2 * C0 * cStar⁻¹ / κ) *
        ((1 / ((1 / 2 - α) / 4) ^ 2 + |Kc|) * k ^ (-α)) + 2 * k ^ (-α) := by
      rw [hCdef]; ring
    linarith only [h2, h3, this]
  · have h1 := abs_le.1 hanchor
    have : T / 2 ≤ shom K := by linarith only [h1.1, hET]
    exact this

/-! ### Powers of the scale -/

theorem s5_rate_log {α α0 : ℝ} (h : α < α0) :
    ∃ CA : ℝ, 0 < CA ∧ ∀ k : ℝ, 1 ≤ k →
      k ^ (-α0) * Real.log k ≤ CA * k ^ (-α) ∧ k ^ (-α0) * Real.log k ^ 2 ≤ CA * k ^ (-α) := by
  set t : ℝ := (α0 - α) / 2 with ht
  have ht0 : 0 < t := by rw [ht]; linarith only [h]
  refine ⟨1 / t ^ 2 + 1 / t, by positivity, fun k hk => ?_⟩
  have hk0 : 0 < k := by linarith only [hk]
  have hnk : 0 ≤ k ^ (-α) := Real.rpow_nonneg hk0.le _
  have e1 : k ^ (-α0) * k ^ (2 * t) = k ^ (-α) := by
    rw [← Real.rpow_add hk0]
    congr 1
    rw [ht]
    ring
  have e2 : k ^ (-α0) * k ^ t ≤ k ^ (-α) := by
    rw [← Real.rpow_add hk0]
    exact Real.rpow_le_rpow_of_exponent_le hk (by rw [ht]; linarith only [h])
  have hn0 : 0 ≤ k ^ (-α0) := Real.rpow_nonneg hk0.le _
  have hlog0 : 0 ≤ Real.log k := Real.log_nonneg hk
  have h1 : Real.log k ≤ k ^ t / t := Real.log_le_rpow_div hk0.le ht0
  have h2 := s12_log_sq_le hk ht0
  have hA : k ^ (-α0) * Real.log k ≤ (1 / t) * k ^ (-α) := by
    calc k ^ (-α0) * Real.log k ≤ k ^ (-α0) * (k ^ t / t) := mul_le_mul_of_nonneg_left h1 hn0
      _ = (k ^ (-α0) * k ^ t) / t := by ring
      _ ≤ k ^ (-α) / t := div_le_div_of_nonneg_right e2 ht0.le
      _ = (1 / t) * k ^ (-α) := by ring
  have hB : k ^ (-α0) * Real.log k ^ 2 ≤ (1 / t ^ 2) * k ^ (-α) := by
    calc k ^ (-α0) * Real.log k ^ 2 ≤ k ^ (-α0) * (k ^ (2 * t) / t ^ 2) :=
          mul_le_mul_of_nonneg_left h2 hn0
      _ = (k ^ (-α0) * k ^ (2 * t)) / t ^ 2 := by ring
      _ = (1 / t ^ 2) * k ^ (-α) := by rw [e1]; ring
  have hp1 : 0 ≤ (1 / t ^ 2) * k ^ (-α) := by positivity
  have hp2 : 0 ≤ (1 / t) * k ^ (-α) := by positivity
  constructor
  · calc k ^ (-α0) * Real.log k ≤ (1 / t) * k ^ (-α) := hA
      _ ≤ (1 / t ^ 2 + 1 / t) * k ^ (-α) := by linarith only [hp1, add_mul (1 / t ^ 2) (1 / t) (k ^ (-α))]
  · calc k ^ (-α0) * Real.log k ^ 2 ≤ (1 / t ^ 2) * k ^ (-α) := hB
      _ ≤ (1 / t ^ 2 + 1 / t) * k ^ (-α) := by linarith only [hp2, add_mul (1 / t ^ 2) (1 / t) (k ^ (-α))]

/-! ### The change of the dilation parameter `ε ↦ ε / T` -/

theorem s5_abs_log_div {ε T : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hT : 1 ≤ T) :
    |Real.log (ε / T)| = |Real.log ε| + Real.log T := by
  have hT0 : 0 < T := by linarith only [hT]
  have hl : Real.log ε < 0 := Real.log_neg hε (by linarith only [hε2])
  have hlT : 0 ≤ Real.log T := Real.log_nonneg hT
  have e : Real.log (ε / T) = Real.log ε - Real.log T := Real.log_div hε.ne' hT0.ne'
  rw [e, abs_of_neg (by linarith only [hl, hlT]), abs_of_neg hl]
  ring

theorem s5_scaleS_shift {cStar ε T : ℝ} (hc : 0 < cStar) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hT : 1 ≤ T) :
    s12_scaleS cStar ε ≤ s12_scaleS cStar (ε / T) ∧
      s12_scaleS cStar (ε / T) - s12_scaleS cStar ε ≤
        s12_scaleS cStar (ε / T) * (Real.log T / |Real.log (ε / T)|) := by
  have hl : Real.log ε < 0 := Real.log_neg hε (by linarith only [hε2])
  have hlT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hB : 0 < |Real.log ε| := abs_pos.2 hl.ne
  have hBB : |Real.log (ε / T)| = |Real.log ε| + Real.log T := s5_abs_log_div hε hε2 hT
  unfold s12_scaleS
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, hBB]
  set B := |Real.log ε| with hBdef
  set a := 2 * cStar with ha
  have ha0 : 0 < a := by positivity
  set u := Real.sqrt (a * B) with hu
  set u' := Real.sqrt (a * (B + Real.log T)) with hu'
  have hu2 : u * u = a * B := Real.mul_self_sqrt (by positivity)
  have hu'2 : u' * u' = a * (B + Real.log T) := Real.mul_self_sqrt (by positivity)
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu'0 : 0 ≤ u' := Real.sqrt_nonneg _
  have hle : u ≤ u' := Real.sqrt_le_sqrt (by
    have := mul_le_mul_of_nonneg_left (show B ≤ B + Real.log T by linarith only [hlT]) ha0.le
    linarith only [this])
  refine ⟨hle, ?_⟩
  have hBp : 0 < B + Real.log T := by linarith only [hB, hlT]
  rw [mul_div_assoc', le_div_iff₀ hBp]
  -- u' B ≤ u (B + log T)
  have key : u' * B ≤ u * (B + Real.log T) := by
    have hsq : (u' * B) ^ 2 ≤ (u * (B + Real.log T)) ^ 2 := by
      have e1 : (u' * B) ^ 2 = (u' * u') * B ^ 2 := by ring
      have e2 : (u * (B + Real.log T)) ^ 2 = (u * u) * (B + Real.log T) ^ 2 := by ring
      rw [e1, e2, hu'2, hu2]
      have : 0 ≤ a * B * (B + Real.log T) * Real.log T := by positivity
      have e3 : a * (B + Real.log T) * B ^ 2 + a * B * (B + Real.log T) * Real.log T =
          a * B * (B + Real.log T) ^ 2 := by ring
      linarith only [this, e3]
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hsq
  linarith only [key]

theorem s5_ratio_shift {S S' sh η : ℝ} (hsh : 0 < sh) (h1 : S ≤ S') (h2 : S' - S ≤ S' * η)
    (hη : 0 ≤ η) (hr : S' / sh ≤ 2) :
    S / sh ≤ 2 ∧ |S / sh - 1| ≤ |S' / sh - 1| + 2 * η := by
  refine ⟨(div_le_div_of_nonneg_right h1 hsh.le).trans hr, ?_⟩
  have e : S / sh - 1 = (S' / sh - 1) - (S' - S) / sh := by
    field_simp
    ring
  have h3 : (S' - S) / sh ≤ 2 * η := by
    rw [div_le_iff₀ hsh]
    have h4 : S' * η ≤ 2 * sh * η := by
      have : S' ≤ 2 * sh := by rwa [div_le_iff₀ hsh] at hr
      exact mul_le_mul_of_nonneg_right this hη
    linarith only [h2, h4]
  have h5 : 0 ≤ (S' - S) / sh := div_nonneg (by linarith only [h1]) hsh.le
  rw [e]
  refine (abs_sub _ _).trans ?_
  rw [abs_of_nonneg h5]
  linarith only [h3]

/-! ### The size of the coefficients -/

theorem s5_tau_bound {S sh E : ℝ} (hS : 0 < S) (hsh : 0 < sh) (h : |S / sh - 1| ≤ E)
    (hE : E ≤ 1 / 2) :
    |S⁻¹ - sh⁻¹| * sh ≤ 2 * E ∧ S * |sh⁻¹ - S⁻¹| ≤ E := by
  have h1 := abs_le.1 h
  have hr : 1 / 2 ≤ S / sh := by linarith only [h1.1, hE]
  have hr' : sh / S ≤ 2 := by
    rw [div_le_iff₀ hS]
    rw [le_div_iff₀ hsh] at hr
    linarith only [hr]
  have e1 : (S⁻¹ - sh⁻¹) * sh = -(S / sh - 1) * (sh / S) := by
    field_simp
    ring
  have e2 : S * (sh⁻¹ - S⁻¹) = S / sh - 1 := by
    field_simp
  refine ⟨?_, ?_⟩
  · rw [← abs_of_pos hsh, ← abs_mul, abs_of_pos hsh, e1, abs_mul, abs_neg,
      abs_of_nonneg (by positivity : 0 ≤ sh / S)]
    calc |S / sh - 1| * (sh / S) ≤ E * 2 :=
          mul_le_mul h hr' (by positivity) ((abs_nonneg _).trans h)
      _ = 2 * E := by ring
  · rw [← abs_of_pos hS, ← abs_mul, abs_of_pos hS, e2]
    exact h

/-- **The coefficients of the chain are `O(n^{-α})`.** -/
theorem s5_xi_bound {α α0 : ℝ} (hα : 0 < α) (hαα0 : α < α0)
    (CL CH LU C1 Ct cs Cf T dd : ℝ) (hCL : 0 ≤ CL) (hCH : 0 ≤ CH) (hLU : 0 ≤ LU) (hC1 : 0 ≤ C1)
    (hCt : 0 ≤ Ct) (hcs : 0 < cs) (hCf : 0 ≤ Cf) (hT : 1 ≤ T) (hdd : 0 ≤ dd) {σ' : ℝ}
    (hσ' : σ' ≤ 1 / 2 - α) :
    ∃ Cx N1 : ℝ, 0 < Cx ∧ ∀ (n : ℕ) (ε S sh Bc Cb : ℝ), N1 ≤ (n : ℝ) → 0 < ε →
      (3 : ℝ) ^ n * ε ≤ 3 * T → 0 < S → 0 < sh → S / sh ≤ 2 →
      |S / sh - 1| ≤ Ct * (n : ℝ) ^ (-α) → cs * (n : ℝ) ^ ((1 : ℝ) / 2) ≤ sh → 0 ≤ Bc →
      Bc ≤ Cf * (n : ℝ) ^ σ' → 0 ≤ Cb → Cb ≤ C1 * (n : ℝ) ^ (-α0) * Real.log n →
      s5_xiF CL CH LU dd Bc S sh ε Cb n ≤ Cx * (n : ℝ) ^ (-α) ∧
        s5_xiG CH LU dd Bc S sh ε Cb n ≤ Cx * (n : ℝ) ^ (-α) := by
  obtain ⟨CA, hCA, hrate⟩ := s5_rate_log hαα0
  set Af : ℝ := 18 * T ^ 2 * (C1 * CA) with hAf
  set Ag : ℝ := 3 * T * (C1 * CA) with hAg
  set Ck : ℝ := 2 * dd * (Cf / cs) + 2 * Ct with hCk
  set Pf : ℝ := CL * LU ^ 2 * Ct with hPf
  have hT0 : 0 < T := by linarith only [hT]
  have hAf0 : 0 ≤ Af := by positivity
  have hAg0 : 0 ≤ Ag := by positivity
  have hCk0 : 0 ≤ Ck := by positivity
  have hPf0 : 0 ≤ Pf := by positivity
  refine ⟨(Af + 2 * Pf + Ck * (Af + Pf + CH * LU ^ 2)) + (Ag + Ck * (Ag + CH * LU)) + 1,
    max 3 ((2 * Ct + 1) ^ (1 / α)), by positivity, ?_⟩
  intro n ε S sh Bc Cb hn hε h3 hS hsh hr2 hr1 hshlow hBc0 hBc hCb0 hCb
  set k : ℝ := (n : ℝ) with hk
  have hk3 : 3 ≤ k := (le_max_left _ _).trans hn
  have hk1 : 1 ≤ k := by linarith only [hk3]
  have hk0 : 0 < k := by linarith only [hk1]
  set x : ℝ := k ^ (-α) with hx
  have hx0 : 0 < x := Real.rpow_pos_of_pos hk0 _
  have hx1 : x ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hk1 (by linarith only [hα])
  have hkα : 2 * Ct + 1 ≤ k ^ α := by
    have h1 : (2 * Ct + 1) ^ (1 / α) ≤ k := (le_max_right _ _).trans hn
    have h2 := Real.rpow_le_rpow (by positivity) h1 hα.le
    rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel hα.ne', Real.rpow_one] at h2
  have hxsmall : Ct * x ≤ 1 / 2 := by
    have hkα0 : 0 < k ^ α := Real.rpow_pos_of_pos hk0 _
    have e : x = (k ^ α)⁻¹ := by rw [hx, Real.rpow_neg hk0.le]
    rw [e, ← div_eq_mul_inv, div_le_iff₀ hkα0]
    linarith only [hkα]
  obtain ⟨hτ, hτ0'⟩ := s5_tau_bound hS hsh hr1 hxsmall
  -- the size of Cb
  have hCb' : Cb ≤ C1 * CA * x := by
    have := (hrate k hk1).1
    calc Cb ≤ C1 * k ^ (-α0) * Real.log k := hCb
      _ = C1 * (k ^ (-α0) * Real.log k) := by ring
      _ ≤ C1 * (CA * x) := mul_le_mul_of_nonneg_left this hC1
      _ = C1 * CA * x := by ring
  have hCbl : Cb * Real.log k ≤ C1 * CA * x := by
    have := (hrate k hk1).2
    have hl0 : 0 ≤ Real.log k := Real.log_nonneg hk1
    calc Cb * Real.log k ≤ C1 * k ^ (-α0) * Real.log k * Real.log k :=
          mul_le_mul_of_nonneg_right hCb hl0
      _ = C1 * (k ^ (-α0) * Real.log k ^ 2) := by ring
      _ ≤ C1 * (CA * x) := mul_le_mul_of_nonneg_left this hC1
      _ = C1 * CA * x := by ring
  -- beta_f and beta_g
  have h3n : 0 ≤ (3 : ℝ) ^ n * ε := by positivity
  have hsq : ((3 : ℝ) ^ n * ε) ^ 2 ≤ 9 * T ^ 2 := by
    have := mul_le_mul h3 h3 h3n (by positivity)
    linarith only [this, sq ((3 : ℝ) ^ n * ε), sq (3 * T)]
  have hβf : Cb * (sh⁻¹ * (3 : ℝ) ^ (2 * n)) * (S * ε ^ 2) ≤ Af * x := by
    have e : Cb * (sh⁻¹ * (3 : ℝ) ^ (2 * n)) * (S * ε ^ 2) = Cb * ((S / sh) * ((3 : ℝ) ^ n * ε) ^ 2) := by
      rw [pow_mul', mul_pow]
      field_simp
    rw [e]
    have h4 : (S / sh) * ((3 : ℝ) ^ n * ε) ^ 2 ≤ 2 * (9 * T ^ 2) :=
      mul_le_mul hr2 hsq (by positivity) (by norm_num)
    calc Cb * ((S / sh) * ((3 : ℝ) ^ n * ε) ^ 2) ≤ Cb * (2 * (9 * T ^ 2)) :=
          mul_le_mul_of_nonneg_left h4 hCb0
      _ = 18 * T ^ 2 * Cb := by ring
      _ ≤ 18 * T ^ 2 * (C1 * CA * x) := mul_le_mul_of_nonneg_left hCb' (by positivity)
      _ = Af * x := by rw [hAf]; ring
  have hβg : Cb * Real.log k * (3 : ℝ) ^ n * ε ≤ Ag * x := by
    have e : Cb * Real.log k * (3 : ℝ) ^ n * ε = (Cb * Real.log k) * ((3 : ℝ) ^ n * ε) := by ring
    rw [e]
    calc (Cb * Real.log k) * ((3 : ℝ) ^ n * ε) ≤ (Cb * Real.log k) * (3 * T) :=
          mul_le_mul_of_nonneg_left h3 (mul_nonneg hCb0 (Real.log_nonneg hk1))
      _ ≤ (C1 * CA * x) * (3 * T) := mul_le_mul_of_nonneg_right hCbl (by positivity)
      _ = Ag * x := by rw [hAg]; ring
  -- kappa
  have hshB : sh⁻¹ * Bc ≤ (Cf / cs) * x := by
    have hcsk : 0 < cs * k ^ ((1 : ℝ) / 2) := by positivity
    have h1 : sh⁻¹ ≤ (cs * k ^ ((1 : ℝ) / 2))⁻¹ := inv_anti₀ hcsk hshlow
    have h2 : (cs * k ^ ((1 : ℝ) / 2))⁻¹ * (Cf * k ^ σ') = (Cf / cs) * k ^ (σ' - 1 / 2) := by
      rw [Real.rpow_sub hk0]
      field_simp
    have h5 : k ^ (σ' - 1 / 2) ≤ x := Real.rpow_le_rpow_of_exponent_le hk1 (by linarith only [hσ'])
    calc sh⁻¹ * Bc ≤ (cs * k ^ ((1 : ℝ) / 2))⁻¹ * (Cf * k ^ σ') :=
          mul_le_mul h1 hBc hBc0 (by positivity)
      _ = (Cf / cs) * k ^ (σ' - 1 / 2) := h2
      _ ≤ (Cf / cs) * x := mul_le_mul_of_nonneg_left h5 (by positivity)
  have hτ1 : |S⁻¹ - sh⁻¹| * sh ≤ 1 := by linarith only [hτ, hxsmall, hCt, hx0]
  set τ : ℝ := |S⁻¹ - sh⁻¹| * sh with hτdef
  have hτnn : 0 ≤ τ := by positivity
  have hκ : (1 + τ) * (sh⁻¹ * (dd * Bc)) + τ ≤ Ck * x := by
    have h1 : sh⁻¹ * (dd * Bc) ≤ dd * ((Cf / cs) * x) := by
      calc sh⁻¹ * (dd * Bc) = dd * (sh⁻¹ * Bc) := by ring
        _ ≤ dd * ((Cf / cs) * x) := mul_le_mul_of_nonneg_left hshB hdd
    have h2 : (1 + τ) * (sh⁻¹ * (dd * Bc)) ≤ 2 * (dd * ((Cf / cs) * x)) :=
      mul_le_mul (by linarith only [hτ1]) h1 (by positivity) (by norm_num)
    have h3' : τ ≤ 2 * (Ct * x) := by
      have : 2 * (Ct * x) = 2 * (Ct * x) := rfl
      have hE : |S / sh - 1| ≤ Ct * x := by rw [hx]; exact hr1
      have := (s5_tau_bound hS hsh hE hxsmall).1
      exact this
    calc (1 + τ) * (sh⁻¹ * (dd * Bc)) + τ ≤ 2 * (dd * ((Cf / cs) * x)) + 2 * (Ct * x) :=
          add_le_add h2 h3'
      _ = Ck * x := by rw [hCk]; ring
  have hκ0 : 0 ≤ (1 + τ) * (sh⁻¹ * (dd * Bc)) + τ := by positivity
  have hτ₀ : S * |sh⁻¹ - S⁻¹| ≤ Ct * x := hτ0'
  have hP : CL * LU ^ 2 * (S * |sh⁻¹ - S⁻¹|) ≤ Pf * x := by
    calc CL * LU ^ 2 * (S * |sh⁻¹ - S⁻¹|) ≤ CL * LU ^ 2 * (Ct * x) :=
          mul_le_mul_of_nonneg_left hτ₀ (by positivity)
      _ = Pf * x := by rw [hPf]; ring
  have hβf0 : 0 ≤ Cb * (sh⁻¹ * (3 : ℝ) ^ (2 * n)) * (S * ε ^ 2) := by positivity
  have hβg0 : 0 ≤ Cb * Real.log k * (3 : ℝ) ^ n * ε :=
    mul_nonneg (mul_nonneg (mul_nonneg hCb0 (Real.log_nonneg hk1)) (by positivity)) hε.le
  have hP0 : 0 ≤ CL * LU ^ 2 * (S * |sh⁻¹ - S⁻¹|) := by positivity
  have hxx : x * x ≤ x := by nlinarith only [hx0, hx1]
  unfold s5_xiF s5_xiG
  dsimp only
  constructor
  · set βf := Cb * (sh⁻¹ * (3 : ℝ) ^ (2 * n)) * (S * ε ^ 2) with hβfdef
    set κ := (1 + τ) * (sh⁻¹ * (dd * Bc)) + τ with hκdef
    set Q := CL * LU ^ 2 * (S * |sh⁻¹ - S⁻¹|) with hQ
    have h1 : κ * (βf + Q + CH * LU ^ 2) ≤ (Ck * x) * (Af + Pf + CH * LU ^ 2) := by
      refine mul_le_mul hκ ?_ (by positivity) (by positivity)
      have h5 : βf ≤ Af := hβf.trans (by nlinarith only [hx1, hAf0])
      have h6 : Q ≤ Pf := hP.trans (by nlinarith only [hx1, hPf0])
      linarith only [h5, h6]
    have h2 : (Ck * x) * (Af + Pf + CH * LU ^ 2) ≤ Ck * (Af + Pf + CH * LU ^ 2) * x := by
      linarith only [le_refl ((Ck * x) * (Af + Pf + CH * LU ^ 2))]
    have h7 : 0 ≤ Ag + Ck * (Ag + CH * LU) := by positivity
    have h8 : 0 ≤ (Ag + Ck * (Ag + CH * LU)) * x := by positivity
    calc βf + 2 * Q + κ * (βf + Q + CH * LU ^ 2)
        ≤ Af * x + 2 * (Pf * x) + Ck * (Af + Pf + CH * LU ^ 2) * x := by
          linarith only [hβf, hP, h1, h2]
      _ ≤ _ := by nlinarith only [hx0, h8]
  · set βg := Cb * Real.log k * (3 : ℝ) ^ n * ε with hβgdef
    set κ := (1 + τ) * (sh⁻¹ * (dd * Bc)) + τ with hκdef
    have h1 : κ * (βg + CH * LU) ≤ (Ck * x) * (Ag + CH * LU) := by
      refine mul_le_mul hκ ?_ (by positivity) (by positivity)
      have h5 : βg ≤ Ag := hβg.trans (by nlinarith only [hx1, hAg0])
      linarith only [h5]
    have h8 : 0 ≤ ((Af + 2 * Pf + Ck * (Af + Pf + CH * LU ^ 2))) * x := by positivity
    calc βg + κ * (βg + CH * LU) ≤ Ag * x + (Ck * x) * (Ag + CH * LU) := by
          linarith only [hβg, h1]
      _ ≤ _ := by nlinarith only [hx0, h8]

/-! ### Tails, uniformly in the law -/

/-- **Transfer of a tail, with the constant independent of the law** (a copy of the transfer
lemma of the minimal scales with the constant bound first). -/
theorem s5_transfer_unif {Ω : Type*} [MeasurableSpace Ω] {a A b0 B σ : ℝ} (ha : 0 < a)
    (hA : 0 < A) (hb0 : 0 ≤ b0) (hσ : 0 < σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (μ : Measure Ω) [IsProbabilityMeasure μ] {W f : Ω → ℝ},
      (∀ ω, Real.log (W ω) ≤ a * f ω + b0) →
      (∀ t : ℝ, 1 ≤ t → μ.real {ω | A * t < f ω} ≤ B * Real.exp (-(t ^ σ))) →
      ∀ t : ℝ, 1 ≤ t →
        μ.real {ω | t ≤ W ω} ≤ C * Real.exp (-(C⁻¹ * (Real.log t) ^ σ)) := by
  have haA : 0 < 4 * a * A := by positivity
  set T1 : ℝ := 4 * (b0 + a * A) with hT1
  have hT1pos : 0 < T1 := by positivity
  refine ⟨max (max 1 B) (max (Real.exp (T1 ^ σ)) ((4 * a * A) ^ σ)), le_trans (le_max_left _ _)
    (le_max_left _ _), ?_⟩
  intro μ _ W f hlog hT t ht
  set C := max (max 1 B) (max (Real.exp (T1 ^ σ)) ((4 * a * A) ^ σ)) with hC
  have hC1 : 1 ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
  have hCB : B ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCe : Real.exp (T1 ^ σ) ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCa : (4 * a * A) ^ σ ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
  have hC0 : 0 < C := lt_of_lt_of_le one_pos hC1
  have hu0 : 0 ≤ Real.log t := Real.log_nonneg ht
  by_cases hcase : Real.log t ≤ T1
  · have h1 : μ.real {ω | t ≤ W ω} ≤ 1 := measureReal_le_one
    have h2 : (Real.log t) ^ σ ≤ T1 ^ σ := Real.rpow_le_rpow hu0 hcase hσ.le
    have h3 : C⁻¹ * (Real.log t) ^ σ ≤ T1 ^ σ := by
      have hp : 0 ≤ (Real.log t) ^ σ := Real.rpow_nonneg hu0 σ
      have : C⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hC1
      calc C⁻¹ * (Real.log t) ^ σ ≤ 1 * (Real.log t) ^ σ :=
            mul_le_mul_of_nonneg_right this hp
        _ ≤ T1 ^ σ := by linarith only [h2]
    have h4 : Real.exp (-(T1 ^ σ)) ≤ Real.exp (-(C⁻¹ * (Real.log t) ^ σ)) :=
      Real.exp_le_exp.2 (by linarith only [h3])
    have h5 : 1 ≤ C * Real.exp (-(T1 ^ σ)) := by
      have : Real.exp (T1 ^ σ) * Real.exp (-(T1 ^ σ)) = 1 := by
        rw [← Real.exp_add]; simp
      calc (1 : ℝ) = Real.exp (T1 ^ σ) * Real.exp (-(T1 ^ σ)) := this.symm
        _ ≤ C * Real.exp (-(T1 ^ σ)) :=
          mul_le_mul_of_nonneg_right hCe (Real.exp_pos _).le
    calc μ.real {ω | t ≤ W ω} ≤ 1 := h1
      _ ≤ C * Real.exp (-(T1 ^ σ)) := h5
      _ ≤ C * Real.exp (-(C⁻¹ * (Real.log t) ^ σ)) := mul_le_mul_of_nonneg_left h4 hC0.le
  · push Not at hcase
    set u := Real.log t with hu
    have hupos : 0 < u := lt_of_lt_of_le hT1pos hcase.le
    set s := u / (4 * a * A) with hs
    have hs1 : 1 ≤ s := by
      rw [hs, le_div_iff₀ haA]
      have : 4 * a * A ≤ T1 := by rw [hT1]; linarith only [hb0]
      linarith only [this, hcase]
    have hsub : {ω | t ≤ W ω} ⊆ {ω | A * s < f ω} := by
      intro ω hω
      have h1 : u ≤ Real.log (W ω) := Real.log_le_log (by linarith only [ht]) hω
      have h2 := hlog ω
      have h3 : 4 * b0 ≤ T1 := by rw [hT1]; nlinarith only [ha, hA]
      have hAs : A * s = u / (4 * a) := by
        rw [hs]; field_simp
      show A * s < f ω
      rw [hAs, div_lt_iff₀ (by positivity)]
      nlinarith only [h1, h2, h3, hcase, ha, hupos]
    have h6 := (measureReal_mono hsub).trans (hT s hs1)
    have h7 : s ^ σ = u ^ σ / (4 * a * A) ^ σ := by
      rw [hs]; exact Real.div_rpow hupos.le haA.le σ
    have hpw : 0 < (4 * a * A) ^ σ := Real.rpow_pos_of_pos haA σ
    have h8 : C⁻¹ * u ^ σ ≤ s ^ σ := by
      rw [h7, inv_mul_eq_div]
      exact div_le_div_of_nonneg_left (Real.rpow_nonneg hupos.le σ) hpw hCa
    calc μ.real {ω | t ≤ W ω} ≤ B * Real.exp (-(s ^ σ)) := h6
      _ ≤ C * Real.exp (-(C⁻¹ * u ^ σ)) :=
        mul_le_mul hCB (Real.exp_le_exp.2 (by linarith only [h8])) (Real.exp_pos _).le hC0.le


/-- **The tail of `3^{m⋆}`, with the constant independent of the law.** -/
theorem s5_scale_tail_unif {Ω : Type*} [MeasurableSpace Ω] {Λ σ N₀ L : ℝ} (hΛ : 0 < Λ)
    (hσ : 0 < σ) (hN : 0 ≤ N₀) (hL : 0 ≤ L) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (μ : Measure Ω) [IsProbabilityMeasure μ] (X₀ : Ω → ℝ),
      (∀ ω, 1 ≤ X₀ ω) →
      (∀ t : ℝ, 1 ≤ t → μ.real {ω | Λ * t < |Real.log (X₀ ω)|} ≤ 1 * Real.exp (-(t ^ σ))) →
      ∀ t : ℝ, 1 ≤ t →
        μ.real {ω | t ≤ (3 : ℝ) ^ ms_star N₀ L (X₀ ω)} ≤
          C * Real.exp (-(C⁻¹ * (Real.log t) ^ σ)) := by
  have hj : (0 : ℝ) ≤ ms_j0 N₀ := by positivity
  obtain ⟨C, hC1, hC⟩ := s5_transfer_unif (Ω := Ω) (a := 2) (A := Λ)
    (b0 := 2 * (ms_j0 N₀ + 2 * L + 2)) (B := 1) (σ := σ) (by norm_num) hΛ (by positivity) hσ
  refine ⟨C, hC1, fun μ _ X₀ hX hT => ?_⟩
  refine hC μ (W := fun ω => (3 : ℝ) ^ ms_star N₀ L (X₀ ω)) (f := fun ω => |Real.log (X₀ ω)|)
    (fun ω => ?_) hT
  have hb := ms_star_le_bound (L := L) hN hL (hX ω)
  have h1 : Real.log ((3 : ℝ) ^ ms_star N₀ L (X₀ ω)) =
      (ms_star N₀ L (X₀ ω) : ℝ) * Real.log 3 := Real.log_pow _ _
  have h2 : Real.log (X₀ ω) ≤ |Real.log (X₀ ω)| := le_abs_self _
  show Real.log ((3 : ℝ) ^ ms_star N₀ L (X₀ ω)) ≤ 2 * |Real.log (X₀ ω)| + _
  linarith only [h1, hb, h2]

/-- **The tail of the maximum of two scales.** -/
theorem s5_tail_max_log {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} {ρ₁ ρ₂ β Λ₁ Λ₂ : ℝ} (hβ : 0 < β) (h₁ : β ≤ ρ₁) (h₂ : β ≤ ρ₂) (hΛ₁ : 0 < Λ₁)
    (hΛ₂ : 0 < Λ₂)
    (hO₁ : Homogenization.IndependentSums.IsBigO μ (Homogenization.IndependentSums.gammaSigma ρ₁)
      (fun ω => Real.log (X ω)) Λ₁)
    (hO₂ : Homogenization.IndependentSums.IsBigO μ (Homogenization.IndependentSums.gammaSigma ρ₂)
      (fun ω => Real.log (Y ω)) Λ₂) :
    ∀ t : ℝ, 1 ≤ t →
      μ.real {ω | ((2 : ℝ) ^ (1 / β) * max Λ₁ Λ₂) * t < |Real.log (max (X ω) (Y ω))|} ≤
        1 * Real.exp (-(t ^ β)) := by
  intro t ht
  set c : ℝ := (2 : ℝ) ^ (1 / β) with hc
  have hc1 : 1 ≤ c := Real.one_le_rpow (by norm_num) (by positivity)
  have hcβ : c ^ β = 2 := by
    rw [hc, ← Real.rpow_mul (by norm_num), one_div_mul_cancel hβ.ne', Real.rpow_one]
  set M := max Λ₁ Λ₂ with hM
  have hM1 : Λ₁ ≤ M := le_max_left _ _
  have hM2 : Λ₂ ≤ M := le_max_right _ _
  have ht0 : 0 < t := by linarith only [ht]
  have hs : 1 ≤ t ^ β := Real.one_le_rpow ht hβ.le
  have tail : ∀ {Λ ρ : ℝ} (f : Ω → ℝ), 0 < Λ → β ≤ ρ → Λ ≤ M →
      Homogenization.IndependentSums.IsBigO μ (Homogenization.IndependentSums.gammaSigma ρ) f Λ →
        μ.real {ω | (c * M) * t < |f ω|} ≤ Real.exp (-(2 * t ^ β)) := by
    intro Λ ρ f hΛ hρ hΛM hO
    set t₁ : ℝ := (c * M / Λ) * t with ht₁
    have hcM : c ≤ c * M / Λ := by
      rw [le_div_iff₀ hΛ]
      exact mul_le_mul_of_nonneg_left hΛM (by linarith only [hc1])
    have ht₁c : c * t ≤ t₁ := mul_le_mul_of_nonneg_right hcM ht0.le
    have ht₁1 : 1 ≤ t₁ := by
      have : 1 ≤ c * t := by nlinarith only [hc1, ht]
      linarith only [this, ht₁c]
    have e : (c * M) * t = Λ * t₁ := by
      rw [ht₁]
      field_simp
    have h1 := ms_tail_of_isBigO hO t₁ ht₁1
    rw [e]
    refine h1.trans ?_
    rw [one_mul]
    refine Real.exp_le_exp.2 ?_
    have h2 : t₁ ^ β ≤ t₁ ^ ρ := Real.rpow_le_rpow_of_exponent_le ht₁1 hρ
    have h3 : (c * t) ^ β ≤ t₁ ^ β := Real.rpow_le_rpow (by positivity) ht₁c hβ.le
    have h4 : (c * t) ^ β = 2 * t ^ β := by rw [Real.mul_rpow (by positivity) ht0.le, hcβ]
    linarith only [h2, h3, h4]
  have hsub : {ω | (c * M) * t < |Real.log (max (X ω) (Y ω))|} ⊆
      {ω | (c * M) * t < |Real.log (X ω)|} ∪ {ω | (c * M) * t < |Real.log (Y ω)|} := by
    intro ω hω
    have hω' : (c * M) * t < |Real.log (max (X ω) (Y ω))| := hω
    rcases le_total (X ω) (Y ω) with hxy | hxy
    · right
      rw [max_eq_right hxy] at hω'
      exact hω'
    · left
      rw [max_eq_left hxy] at hω'
      exact hω'
  have hu : μ.real ({ω | (c * M) * t < |Real.log (X ω)|} ∪ {ω | (c * M) * t < |Real.log (Y ω)|}) ≤
      μ.real {ω | (c * M) * t < |Real.log (X ω)|} + μ.real {ω | (c * M) * t < |Real.log (Y ω)|} :=
    measureReal_union_le _ _
  have hX := tail (fun ω => Real.log (X ω)) hΛ₁ h₁ hM1 hO₁
  have hY := tail (fun ω => Real.log (Y ω)) hΛ₂ h₂ hM2 hO₂
  have hexp : 2 * Real.exp (-(2 * t ^ β)) ≤ Real.exp (-(t ^ β)) := by
    have e1 : Real.exp (-(2 * t ^ β)) = Real.exp (-(t ^ β)) * Real.exp (-(t ^ β)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have e2 : Real.exp (-(t ^ β)) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by linarith only [hs])
    have e3 : Real.exp (-1) ≤ 1 / 2 := by
      have := Real.add_one_le_exp (1 : ℝ)
      rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos 1) (by norm_num)]
      linarith only [this]
    have e4 : 0 < Real.exp (-(t ^ β)) := Real.exp_pos _
    rw [e1]
    have : 2 * Real.exp (-(t ^ β)) ≤ 1 := by linarith only [e2, e3]
    calc 2 * (Real.exp (-(t ^ β)) * Real.exp (-(t ^ β))) =
          (2 * Real.exp (-(t ^ β))) * Real.exp (-(t ^ β)) := by ring
      _ ≤ 1 * Real.exp (-(t ^ β)) := mul_le_mul_of_nonneg_right this e4.le
      _ = Real.exp (-(t ^ β)) := one_mul _
  calc μ.real {ω | (c * M) * t < |Real.log (max (X ω) (Y ω))|} ≤ _ := measureReal_mono hsub
    _ ≤ _ := hu
    _ ≤ Real.exp (-(2 * t ^ β)) + Real.exp (-(2 * t ^ β)) := add_le_add hX hY
    _ = 2 * Real.exp (-(2 * t ^ β)) := by ring
    _ ≤ Real.exp (-(t ^ β)) := hexp
    _ = 1 * Real.exp (-(t ^ β)) := (one_mul _).symm

end SuperdiffusionCLT.Section7
