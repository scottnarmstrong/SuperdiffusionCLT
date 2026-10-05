/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Linfty.Det
public import SuperdiffusionCLT.Section7.Linfty.ScaleChoice
public import SuperdiffusionCLT.Section7.Prereq.L2AssemblyG

/-!
# The `L^∞` proposition for a smooth datum: the numerics

The real-number part of the assembly of the `L^∞` proposition (the computation of
`e.Dir.new.Linfty.scale.choice` and the absorption at the end of the proof). With the cell
constants of the flux bounds, the local gradient bound `Gb = σ^{1/2} ν^{-1/2} Rb` and the boundary
`L²` bound `Bb = 3^n Rb`, the error `linfErr` is the leading term `K_p C δ · L Rb` plus a term
carrying the factor `τ ≥ 3^n / L`, against a power `k^{11}` and the power `Q` of the ellipticity
ratio (`linf_smooth_err`). The leading term is absorbed when `δ` is small
(`linf_smooth_absorb`).
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

/-- Elementary bounds for the parameters `1/k ≤ ν ≤ 1 ≤ σ ≤ k`. -/
theorem linf_smooth_facts {k ν σ : ℝ} (hk : 1 ≤ k) (hν : 0 < ν) (hkν : 1 ≤ k * ν) (hν1 : ν ≤ 1)
    (hσ1 : 1 ≤ σ) (hσk : σ ≤ k) :
    Real.sqrt σ * (Real.sqrt ν)⁻¹ ≤ k ∧ ν⁻¹ ≤ k ∧ Real.sqrt ν ≤ 1 ∧ (Real.sqrt σ)⁻¹ ≤ 1 ∧
      Real.sqrt σ ≤ k ∧ σ * ν⁻¹ ≤ k ^ 2 ∧ σ⁻¹ ≤ 1 := by
  have hk0 : 0 < k := lt_of_lt_of_le one_pos hk
  have hνi : ν⁻¹ ≤ k := by
    calc ν⁻¹ = ν⁻¹ * 1 := (mul_one _).symm
      _ ≤ ν⁻¹ * (k * ν) := mul_le_mul_of_nonneg_left hkν (inv_nonneg.2 hν.le)
      _ = k := by field_simp
  have hsk : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt hk0.le
  have hs1 : Real.sqrt σ ≤ Real.sqrt k := Real.sqrt_le_sqrt hσk
  have hs2 : (Real.sqrt ν)⁻¹ ≤ Real.sqrt k := by
    rw [← Real.sqrt_inv]
    exact Real.sqrt_le_sqrt hνi
  have hsk1 : 1 ≤ Real.sqrt k := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hk
  have hσs1 : 1 ≤ Real.sqrt σ := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hσ1
  have hskk : Real.sqrt k ≤ k := by
    calc Real.sqrt k = Real.sqrt k * 1 := (mul_one _).symm
      _ ≤ Real.sqrt k * Real.sqrt k := mul_le_mul_of_nonneg_left hsk1 (Real.sqrt_nonneg _)
      _ = k := hsk
  refine ⟨?_, hνi, ?_, ?_, hs1.trans hskk, ?_, ?_⟩
  · calc Real.sqrt σ * (Real.sqrt ν)⁻¹ ≤ Real.sqrt k * Real.sqrt k :=
          mul_le_mul hs1 hs2 (inv_nonneg.2 (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
      _ = k := hsk
  · rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hν1
  · exact inv_le_one_of_one_le₀ hσs1
  · calc σ * ν⁻¹ ≤ k * k := mul_le_mul hσk hνi (inv_nonneg.2 hν.le) hk0.le
      _ = k ^ 2 := by ring
  · exact inv_le_one_of_one_le₀ hσ1

/-- `k^j ≤ (Q + 1) k^{11}` for `j ≤ 11`. -/
theorem linf_smooth_kpow {k Q : ℝ} (hk : 1 ≤ k) (hQ : 0 ≤ Q) {j : ℕ} (hj : j ≤ 11) :
    k ^ j ≤ (Q + 1) * k ^ 11 := by
  have h1 : k ^ j ≤ k ^ 11 := pow_le_pow_right₀ hk hj
  have h2 : 0 ≤ k ^ 11 := by positivity
  nlinarith only [h1, h2, hQ]

/-- The bracket of the flux constant: `C σ^{1/2} δ ν^{1/2} + C (|ν - σ| + k^{1+ρ}) ≤ 3 C k²`. -/
theorem linf_smooth_bracket {k ν σ δ ρ Cin : ℝ} (hk : 1 ≤ k) (hν : 0 < ν) (hkν : 1 ≤ k * ν)
    (hν1 : ν ≤ 1) (hσ1 : 1 ≤ σ) (hσk : σ ≤ k) (hδ0 : 0 ≤ δ) (hδk : δ ≤ k)
    (hρ1 : ρ ≤ 1) (hCin : 0 ≤ Cin) :
    l2e_aC Cin σ ν δ + Cin * (|ν - σ| + k ^ (1 + ρ)) ≤ 3 * Cin * k ^ 2 := by
  obtain ⟨-, -, hsν, -, hsσ, -, -⟩ := linf_smooth_facts hk hν hkν hν1 hσ1 hσk
  have hk0 : 0 ≤ k := le_trans zero_le_one hk
  have h1 : Real.sqrt σ * δ * Real.sqrt ν ≤ k * k * 1 :=
    mul_le_mul (mul_le_mul hsσ hδk hδ0 hk0) hsν (Real.sqrt_nonneg _) (mul_nonneg hk0 hk0)
  have h2 : |ν - σ| ≤ k ^ 2 := by
    have : |ν - σ| ≤ k := by
      rw [abs_le]; constructor <;> linarith only [hν, hν1, hσ1, hσk]
    have hkk : k ≤ k ^ 2 := by nlinarith only [hk]
    exact this.trans hkk
  have h3 : k ^ (1 + ρ) ≤ k ^ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le hk (show 1 + ρ ≤ (2 : ℝ) by linarith only [hρ1])
    rwa [Real.rpow_two] at this
  unfold l2e_aC
  have e : Cin * Real.sqrt σ * δ * Real.sqrt ν = Cin * (Real.sqrt σ * δ * Real.sqrt ν) := by ring
  rw [e]
  have h4 : Cin * (Real.sqrt σ * δ * Real.sqrt ν) ≤ Cin * (k * k * 1) :=
    mul_le_mul_of_nonneg_left h1 hCin
  have h5 : Cin * (|ν - σ| + k ^ (1 + ρ)) ≤ Cin * (k ^ 2 + k ^ 2) :=
    mul_le_mul_of_nonneg_left (add_le_add h2 h3) hCin
  have e2 : Cin * (k * k * 1) + Cin * (k ^ 2 + k ^ 2) = 3 * Cin * k ^ 2 := by ring
  linarith only [h4, h5, e2]

/-- Upgrade of a monomial bound to the common form `c (Q + 1) k^{11} τ S`. -/
theorem linf_smooth_up {c X Y τ P S : ℝ} (hc : 0 ≤ c) (hX : 0 ≤ X) (hXY : X ≤ Y) (hτ : 0 ≤ τ)
    (hP : 0 ≤ P) (hPS : P ≤ S) : c * X * τ * P ≤ c * Y * τ * S := by
  have hY : 0 ≤ Y := hX.trans hXY
  gcongr

/-- The flux term of the right-hand side: `L σ⁻¹ β F ≤ 9 K_p C² k³ τ σ⁻¹ L² F`. -/
theorem linf_smooth_t2 {k ν σ δ ρ Cin Kp L τ F : ℝ} {n : ℕ} (hk : 1 ≤ k) (hν : 0 < ν)
    (hkν : 1 ≤ k * ν) (hν1 : ν ≤ 1) (hσ1 : 1 ≤ σ) (hσk : σ ≤ k) (hδ0 : 0 ≤ δ) (hδk : δ ≤ k)
    (hρ1 : ρ ≤ 1) (hCin : 0 ≤ Cin) (hKp : 0 ≤ Kp) (hL : 0 < L) (hτ : (3 : ℝ) ^ n ≤ τ * L)
    (hF : 0 ≤ F) :
    L * σ⁻¹ * (Kp * l2e_b Cin σ ν ρ δ k n * F) ≤
      9 * Kp * Cin ^ 2 * k ^ 3 * τ * (σ⁻¹ * L ^ 2 * F) := by
  obtain ⟨-, hνi, -, -, -, -, -⟩ := linf_smooth_facts hk hν hkν hν1 hσ1 hσk
  have hB := linf_smooth_bracket hk hν hkν hν1 hσ1 hσk hδ0 hδk hρ1 hCin
  have hk0 : 0 < k := lt_of_lt_of_le one_pos hk
  have hσ0 : 0 < σ := lt_of_lt_of_le one_pos hσ1
  have hB0 : 0 ≤ l2e_aC Cin σ ν δ + Cin * (|ν - σ| + k ^ (1 + ρ)) := by
    unfold l2e_aC; positivity
  unfold l2e_b
  calc L * σ⁻¹ * (Kp * ((l2e_aC Cin σ ν δ + Cin * (|ν - σ| + k ^ (1 + ρ))) *
          (Cin * (3 * (3 : ℝ) ^ n) / ν)) * F)
      = 3 * Kp * Cin * (l2e_aC Cin σ ν δ + Cin * (|ν - σ| + k ^ (1 + ρ))) * ν⁻¹ *
          (3 : ℝ) ^ n * (σ⁻¹ * L * F) := by ring
    _ ≤ 3 * Kp * Cin * (3 * Cin * k ^ 2) * k * (τ * L) * (σ⁻¹ * L * F) := by gcongr
    _ = 9 * Kp * Cin ^ 2 * k ^ 3 * τ * (σ⁻¹ * L ^ 2 * F) := by ring

/-- The bracket of `linfDG`: `3^n Gb + 3^{2n} F/ν + Bb + 3^n G ≤ 2 k² τ S`. -/
theorem linf_smooth_dgin {k ν σ L τ Rb F G : ℝ} {n : ℕ} (hk : 1 ≤ k) (hν : 0 < ν)
    (hkν : 1 ≤ k * ν) (hν1 : ν ≤ 1) (hσ1 : 1 ≤ σ) (hσk : σ ≤ k) (hL : 0 < L)
    (hhL : (3 : ℝ) ^ n ≤ L) (hτ : (3 : ℝ) ^ n ≤ τ * L) (hRb : 0 ≤ Rb) (hF : 0 ≤ F)
    (hG : 0 ≤ G) :
    (3 : ℝ) ^ n * (Real.sqrt σ * (Real.sqrt ν)⁻¹ * Rb) + ((3 : ℝ) ^ n) ^ 2 / ν * F +
        (3 : ℝ) ^ n * Rb + (3 : ℝ) ^ n * G ≤
      2 * k ^ 2 * τ * (L * Rb + σ⁻¹ * L ^ 2 * F + L * G) := by
  obtain ⟨hsg, hνi, -, -, -, hσν, -⟩ := linf_smooth_facts hk hν hkν hν1 hσ1 hσk
  have hk0 : 0 < k := lt_of_lt_of_le one_pos hk
  have hσ0 : 0 < σ := lt_of_lt_of_le one_pos hσ1
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hτ0 : 0 ≤ τ := by
    by_contra hneg
    have : τ * L < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hneg) hL
    linarith only [this, hτ, h3]
  have e1 : (3 : ℝ) ^ n * (Real.sqrt σ * (Real.sqrt ν)⁻¹ * Rb) =
      (Real.sqrt σ * (Real.sqrt ν)⁻¹) * (3 : ℝ) ^ n * Rb := by ring
  have b1 : (Real.sqrt σ * (Real.sqrt ν)⁻¹) * (3 : ℝ) ^ n * Rb ≤ k * (τ * L) * Rb := by
    gcongr
  have b2 : ((3 : ℝ) ^ n) ^ 2 / ν * F ≤ τ * (σ * ν⁻¹) * (σ⁻¹ * L ^ 2 * F) := by
    have e : τ * (σ * ν⁻¹) * (σ⁻¹ * L ^ 2 * F) = (σ * σ⁻¹) * ν⁻¹ * (τ * L) * L * F := by ring
    rw [e, mul_inv_cancel₀ hσ0.ne', one_mul]
    have e2 : ((3 : ℝ) ^ n) ^ 2 / ν * F = ν⁻¹ * (3 : ℝ) ^ n * (3 : ℝ) ^ n * F := by ring
    rw [e2]
    gcongr
  have b2' : τ * (σ * ν⁻¹) * (σ⁻¹ * L ^ 2 * F) ≤ τ * k ^ 2 * (σ⁻¹ * L ^ 2 * F) := by gcongr
  have b3 : (3 : ℝ) ^ n * Rb ≤ τ * L * Rb := by gcongr
  have b4 : (3 : ℝ) ^ n * G ≤ τ * L * G := by gcongr
  have hY : 0 ≤ L * Rb := by positivity
  have hΦ : 0 ≤ σ⁻¹ * L ^ 2 * F := by positivity
  have hΓ : 0 ≤ L * G := by positivity
  have hkk : k ≤ k ^ 2 := by nlinarith only [hk]
  have hk1 : 1 ≤ k ^ 2 := by nlinarith only [hk]
  have c1 : k * (τ * L) * Rb ≤ k ^ 2 * τ * (L * Rb) := by
    have : k * (τ * L) * Rb = k * τ * (L * Rb) := by ring
    rw [this]; gcongr
  have c3 : τ * L * Rb ≤ k ^ 2 * τ * (L * Rb) := by
    have : τ * L * Rb = 1 * τ * (L * Rb) := by ring
    rw [this]; gcongr
  have c4 : τ * L * G ≤ 2 * k ^ 2 * τ * (L * G) := by
    have : τ * L * G = 1 * τ * (L * G) := by ring
    rw [this]; gcongr; linarith only [hk1]
  have c2 : τ * k ^ 2 * (σ⁻¹ * L ^ 2 * F) ≤ 2 * k ^ 2 * τ * (σ⁻¹ * L ^ 2 * F) := by
    have : 0 ≤ τ * k ^ 2 * (σ⁻¹ * L ^ 2 * F) := by positivity
    nlinarith only [this]
  have e3 : 2 * k ^ 2 * τ * (L * Rb + σ⁻¹ * L ^ 2 * F + L * G) =
      k ^ 2 * τ * (L * Rb) + k ^ 2 * τ * (L * Rb) + 2 * k ^ 2 * τ * (σ⁻¹ * L ^ 2 * F) +
        2 * k ^ 2 * τ * (L * G) := by ring
  rw [e1, e3]
  linarith only [b1, b2, b2', b3, b4, c1, c2, c3, c4]

/-- The De Giorgi error: `linfDG ≤ 2 Q k² τ S`. -/
theorem linf_smooth_t3 {k ν σ L τ q Q Rb F G : ℝ} {n : ℕ} (hk : 1 ≤ k) (hν : 0 < ν)
    (hkν : 1 ≤ k * ν) (hν1 : ν ≤ 1) (hσ1 : 1 ≤ σ) (hσk : σ ≤ k) (hL : 0 < L)
    (hhL : (3 : ℝ) ^ n ≤ L) (hτ : (3 : ℝ) ^ n ≤ τ * L) (hq : 0 ≤ q) (hqQ : q ≤ Q)
    (hRb : 0 ≤ Rb) (hF : 0 ≤ F) (hG : 0 ≤ G) :
    linfDG q ((3 : ℝ) ^ n) ν (Real.sqrt σ * (Real.sqrt ν)⁻¹ * Rb) ((3 : ℝ) ^ n * Rb) F G ≤
      2 * (Q * k ^ 2) * τ * (L * Rb + σ⁻¹ * L ^ 2 * F + L * G) := by
  have hin := linf_smooth_dgin hk hν hkν hν1 hσ1 hσk hL hhL hτ hRb hF hG
  have h0 : 0 ≤ (3 : ℝ) ^ n * (Real.sqrt σ * (Real.sqrt ν)⁻¹ * Rb) +
      ((3 : ℝ) ^ n) ^ 2 / ν * F + (3 : ℝ) ^ n * Rb + (3 : ℝ) ^ n * G := by positivity
  unfold linfDG
  calc q * ((3 : ℝ) ^ n * (Real.sqrt σ * (Real.sqrt ν)⁻¹ * Rb) + ((3 : ℝ) ^ n) ^ 2 / ν * F +
          (3 : ℝ) ^ n * Rb + (3 : ℝ) ^ n * G)
      ≤ Q * (2 * k ^ 2 * τ * (L * Rb + σ⁻¹ * L ^ 2 * F + L * G)) :=
        mul_le_mul hqQ hin h0 (hq.trans hqQ)
    _ = 2 * (Q * k ^ 2) * τ * (L * Rb + σ⁻¹ * L ^ 2 * F + L * G) := by ring

/-- The De Giorgi error divided by the scale: `L linfDG / 3^n ≤ 2 Q k² S`. -/
theorem linf_smooth_t4a {k ν σ L q Q Rb F G : ℝ} {n : ℕ} (hk : 1 ≤ k) (hν : 0 < ν)
    (hkν : 1 ≤ k * ν) (hν1 : ν ≤ 1) (hσ1 : 1 ≤ σ) (hσk : σ ≤ k) (hL : 0 < L)
    (hhL : (3 : ℝ) ^ n ≤ L) (hq : 0 ≤ q) (hqQ : q ≤ Q) (hRb : 0 ≤ Rb) (hF : 0 ≤ F)
    (hG : 0 ≤ G) :
    L * (linfDG q ((3 : ℝ) ^ n) ν (Real.sqrt σ * (Real.sqrt ν)⁻¹ * Rb) ((3 : ℝ) ^ n * Rb) F G /
        (3 : ℝ) ^ n) ≤
      2 * (Q * k ^ 2) * (L * Rb + σ⁻¹ * L ^ 2 * F + L * G) := by
  obtain ⟨hsg, hνi, -, -, -, hσν, -⟩ := linf_smooth_facts hk hν hkν hν1 hσ1 hσk
  have hσ0 : 0 < σ := lt_of_lt_of_le one_pos hσ1
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have e : L * (linfDG q ((3 : ℝ) ^ n) ν (Real.sqrt σ * (Real.sqrt ν)⁻¹ * Rb)
        ((3 : ℝ) ^ n * Rb) F G / (3 : ℝ) ^ n) =
      q * ((Real.sqrt σ * (Real.sqrt ν)⁻¹) * (L * Rb) + (σ * ν⁻¹) * ((3 : ℝ) ^ n * σ⁻¹ * L * F) +
        L * Rb + L * G) := by
    unfold linfDG
    field_simp
  rw [e]
  have hY : 0 ≤ L * Rb := by positivity
  have hΦ : 0 ≤ σ⁻¹ * L ^ 2 * F := by positivity
  have hΓ : 0 ≤ L * G := by positivity
  have hkk : k ≤ k ^ 2 := by nlinarith only [hk]
  have hk1 : 1 ≤ k ^ 2 := by nlinarith only [hk]
  have b2 : (3 : ℝ) ^ n * σ⁻¹ * L * F ≤ σ⁻¹ * L ^ 2 * F := by
    have : σ⁻¹ * L ^ 2 * F = L * σ⁻¹ * L * F := by ring
    rw [this]; gcongr
  have hin : (Real.sqrt σ * (Real.sqrt ν)⁻¹) * (L * Rb) + (σ * ν⁻¹) * ((3 : ℝ) ^ n * σ⁻¹ * L * F) +
      L * Rb + L * G ≤ 2 * k ^ 2 * (L * Rb + σ⁻¹ * L ^ 2 * F + L * G) := by
    have c1 : (Real.sqrt σ * (Real.sqrt ν)⁻¹) * (L * Rb) ≤ k ^ 2 * (L * Rb) :=
      mul_le_mul_of_nonneg_right (hsg.trans hkk) hY
    have c2 : (σ * ν⁻¹) * ((3 : ℝ) ^ n * σ⁻¹ * L * F) ≤ k ^ 2 * (σ⁻¹ * L ^ 2 * F) :=
      mul_le_mul hσν b2 (by positivity) (by positivity)
    have c3 : L * Rb ≤ k ^ 2 * (L * Rb) := le_mul_of_one_le_left hY hk1
    have c4 : L * G ≤ 2 * k ^ 2 * (L * G) := le_mul_of_one_le_left hΓ (by linarith only [hk1])
    have c5 : 0 ≤ k ^ 2 * (σ⁻¹ * L ^ 2 * F) := by positivity
    have e3 : 2 * k ^ 2 * (L * Rb + σ⁻¹ * L ^ 2 * F + L * G) =
        k ^ 2 * (L * Rb) + k ^ 2 * (L * Rb) + 2 * (k ^ 2 * (σ⁻¹ * L ^ 2 * F)) +
          2 * k ^ 2 * (L * G) := by ring
    rw [e3]
    linarith only [c1, c2, c3, c4, c5]
  have h0 : 0 ≤ (Real.sqrt σ * (Real.sqrt ν)⁻¹) * (L * Rb) +
      (σ * ν⁻¹) * ((3 : ℝ) ^ n * σ⁻¹ * L * F) + L * Rb + L * G := by positivity
  calc q * ((Real.sqrt σ * (Real.sqrt ν)⁻¹) * (L * Rb) + (σ * ν⁻¹) * ((3 : ℝ) ^ n * σ⁻¹ * L * F) +
          L * Rb + L * G)
      ≤ Q * (2 * k ^ 2 * (L * Rb + σ⁻¹ * L ^ 2 * F + L * G)) :=
        mul_le_mul hqQ hin h0 (hq.trans hqQ)
    _ = 2 * (Q * k ^ 2) * (L * Rb + σ⁻¹ * L ^ 2 * F + L * G) := by ring

/-- The second flux term: `L σ⁻¹ (α' Gb + β' F) ≤ (2 K_p C + 15 K_p C²) k³ S`. -/
theorem linf_smooth_t4c {k ν σ δ ρ Cin Kp L Rb F : ℝ} {n : ℕ} (hk : 1 ≤ k) (hν : 0 < ν)
    (hkν : 1 ≤ k * ν) (hν1 : ν ≤ 1) (hσ1 : 1 ≤ σ) (hσk : σ ≤ k) (hδ0 : 0 ≤ δ) (hδk : δ ≤ k)
    (hρ1 : ρ ≤ 1) (hCin : 0 ≤ Cin) (hKp : 0 ≤ Kp) (hL : 0 < L) (hhL : (3 : ℝ) ^ n ≤ L)
    (hRb : 0 ≤ Rb) (hF : 0 ≤ F) :
    L * (σ⁻¹ * ((Kp * l2e_aC Cin σ ν δ + σ * Kp * l2e_e Cin σ ν) *
          (Real.sqrt σ * (Real.sqrt ν)⁻¹ * Rb) +
        (Kp * l2e_b Cin σ ν ρ δ k n + σ * Kp * l2e_g Cin σ ν n) * F)) ≤
      (2 * Kp * Cin + 15 * Kp * Cin ^ 2) * k ^ 3 * (L * Rb + σ⁻¹ * L ^ 2 * F) := by
  obtain ⟨hsg, hνi, hsν, hsσi, hsσ, -, hσi⟩ := linf_smooth_facts hk hν hkν hν1 hσ1 hσk
  have hB := linf_smooth_bracket hk hν hkν hν1 hσ1 hσk hδ0 hδk hρ1 hCin
  have hk0 : 0 < k := lt_of_lt_of_le one_pos hk
  have hσ0 : 0 < σ := lt_of_lt_of_le one_pos hσ1
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hkk : k ≤ k ^ 2 := by nlinarith only [hk]
  have hk23 : k ^ 2 ≤ k ^ 3 := pow_le_pow_right₀ hk (by norm_num)
  -- the gradient part
  have ha : l2e_aC Cin σ ν δ + σ * l2e_e Cin σ ν ≤ 2 * Cin * k ^ 2 := by
    unfold l2e_aC l2e_e
    have h1 : Real.sqrt σ * δ * Real.sqrt ν ≤ k * k * 1 :=
      mul_le_mul (mul_le_mul hsσ hδk hδ0 hk0.le) hsν (Real.sqrt_nonneg _) (by positivity)
    have h2 : σ * ((Real.sqrt σ)⁻¹ * Real.sqrt ν) ≤ k * (1 * 1) :=
      mul_le_mul hσk (mul_le_mul hsσi hsν (Real.sqrt_nonneg _) zero_le_one) (by positivity)
        hk0.le
    have e : Cin * Real.sqrt σ * δ * Real.sqrt ν + σ * (Cin * (Real.sqrt σ)⁻¹ * Real.sqrt ν) =
        Cin * (Real.sqrt σ * δ * Real.sqrt ν) + Cin * (σ * ((Real.sqrt σ)⁻¹ * Real.sqrt ν)) := by
      ring
    rw [e]
    have h4 := mul_le_mul_of_nonneg_left h1 hCin
    have h5 := mul_le_mul_of_nonneg_left h2 hCin
    have h6 : Cin * k ≤ Cin * k ^ 2 := mul_le_mul_of_nonneg_left hkk hCin
    nlinarith only [h4, h5, h6]
  have ha0 : 0 ≤ l2e_aC Cin σ ν δ + σ * l2e_e Cin σ ν := by
    unfold l2e_aC l2e_e; positivity
  have tA : L * (σ⁻¹ * ((Kp * l2e_aC Cin σ ν δ + σ * Kp * l2e_e Cin σ ν) *
      (Real.sqrt σ * (Real.sqrt ν)⁻¹ * Rb))) ≤ 2 * Kp * Cin * k ^ 3 * (L * Rb) := by
    calc L * (σ⁻¹ * ((Kp * l2e_aC Cin σ ν δ + σ * Kp * l2e_e Cin σ ν) *
          (Real.sqrt σ * (Real.sqrt ν)⁻¹ * Rb)))
        = Kp * σ⁻¹ * (l2e_aC Cin σ ν δ + σ * l2e_e Cin σ ν) *
            (Real.sqrt σ * (Real.sqrt ν)⁻¹) * (L * Rb) := by ring
      _ ≤ Kp * 1 * (2 * Cin * k ^ 2) * k * (L * Rb) := by gcongr
      _ = 2 * Kp * Cin * k ^ 3 * (L * Rb) := by ring
  -- the right-hand side part
  have hb : l2e_b Cin σ ν ρ δ k n ≤ 9 * Cin ^ 2 * k ^ 3 * (3 : ℝ) ^ n := by
    unfold l2e_b
    have hB0 : 0 ≤ l2e_aC Cin σ ν δ + Cin * (|ν - σ| + k ^ (1 + ρ)) := by
      unfold l2e_aC; positivity
    calc (l2e_aC Cin σ ν δ + Cin * (|ν - σ| + k ^ (1 + ρ))) * (Cin * (3 * (3 : ℝ) ^ n) / ν)
        = 3 * Cin * (l2e_aC Cin σ ν δ + Cin * (|ν - σ| + k ^ (1 + ρ))) * ν⁻¹ * (3 : ℝ) ^ n := by
          ring
      _ ≤ 3 * Cin * (3 * Cin * k ^ 2) * k * (3 : ℝ) ^ n := by gcongr
      _ = 9 * Cin ^ 2 * k ^ 3 * (3 : ℝ) ^ n := by ring
  have hg : σ * l2e_g Cin σ ν n ≤ 6 * Cin ^ 2 * k ^ 3 * (3 : ℝ) ^ n := by
    unfold l2e_g l2e_e
    have he : Cin * (Real.sqrt σ)⁻¹ * Real.sqrt ν + Cin ≤ 2 * Cin := by
      have : Cin * (Real.sqrt σ)⁻¹ * Real.sqrt ν ≤ Cin * 1 * 1 := by gcongr
      linarith only [this]
    calc σ * ((Cin * (Real.sqrt σ)⁻¹ * Real.sqrt ν + Cin) * (Cin * (3 * (3 : ℝ) ^ n) / ν))
        = 3 * Cin * σ * (Cin * (Real.sqrt σ)⁻¹ * Real.sqrt ν + Cin) * ν⁻¹ * (3 : ℝ) ^ n := by ring
      _ ≤ 3 * Cin * k * (2 * Cin) * k * (3 : ℝ) ^ n := by gcongr
      _ = 6 * Cin ^ 2 * k ^ 2 * (3 : ℝ) ^ n := by ring
      _ ≤ 6 * Cin ^ 2 * k ^ 3 * (3 : ℝ) ^ n := by gcongr
  have hb0 : 0 ≤ l2e_b Cin σ ν ρ δ k n := by
    unfold l2e_b l2e_aC; positivity
  have hg0 : 0 ≤ σ * l2e_g Cin σ ν n := by
    unfold l2e_g l2e_e; positivity
  have tB : L * (σ⁻¹ * ((Kp * l2e_b Cin σ ν ρ δ k n + σ * Kp * l2e_g Cin σ ν n) * F)) ≤
      15 * Kp * Cin ^ 2 * k ^ 3 * (σ⁻¹ * L ^ 2 * F) := by
    calc L * (σ⁻¹ * ((Kp * l2e_b Cin σ ν ρ δ k n + σ * Kp * l2e_g Cin σ ν n) * F))
        = Kp * (l2e_b Cin σ ν ρ δ k n + σ * l2e_g Cin σ ν n) * (σ⁻¹ * L * F) := by ring
      _ ≤ Kp * (9 * Cin ^ 2 * k ^ 3 * (3 : ℝ) ^ n + 6 * Cin ^ 2 * k ^ 3 * (3 : ℝ) ^ n) *
          (σ⁻¹ * L * F) := by gcongr
      _ = 15 * Kp * Cin ^ 2 * k ^ 3 * ((3 : ℝ) ^ n * σ⁻¹ * L * F) := by ring
      _ ≤ 15 * Kp * Cin ^ 2 * k ^ 3 * (L * σ⁻¹ * L * F) := by gcongr
      _ = 15 * Kp * Cin ^ 2 * k ^ 3 * (σ⁻¹ * L ^ 2 * F) := by ring
  have e : L * (σ⁻¹ * ((Kp * l2e_aC Cin σ ν δ + σ * Kp * l2e_e Cin σ ν) *
          (Real.sqrt σ * (Real.sqrt ν)⁻¹ * Rb) +
        (Kp * l2e_b Cin σ ν ρ δ k n + σ * Kp * l2e_g Cin σ ν n) * F)) =
      L * (σ⁻¹ * ((Kp * l2e_aC Cin σ ν δ + σ * Kp * l2e_e Cin σ ν) *
          (Real.sqrt σ * (Real.sqrt ν)⁻¹ * Rb))) +
        L * (σ⁻¹ * ((Kp * l2e_b Cin σ ν ρ δ k n + σ * Kp * l2e_g Cin σ ν n) * F)) := by ring
  have e2 : (2 * Kp * Cin + 15 * Kp * Cin ^ 2) * k ^ 3 * (L * Rb + σ⁻¹ * L ^ 2 * F) =
      2 * Kp * Cin * k ^ 3 * (L * Rb) + 15 * Kp * Cin ^ 2 * k ^ 3 * (σ⁻¹ * L ^ 2 * F) +
        (2 * Kp * Cin * k ^ 3 * (σ⁻¹ * L ^ 2 * F) + 15 * Kp * Cin ^ 2 * k ^ 3 * (L * Rb)) := by
    ring
  have hx : 0 ≤ 2 * Kp * Cin * k ^ 3 * (σ⁻¹ * L ^ 2 * F) + 15 * Kp * Cin ^ 2 * k ^ 3 * (L * Rb) := by
    positivity
  rw [e, e2]
  linarith only [tA, tB, hx]

/-- The comparison of the homogenized problem with the smooth datum:
`3^n (1 + σ⁻¹ Λ)(Λ G / ν + L F / ν) ≤ (1 + c_Λ)² k^{11} τ S`. -/
theorem linf_smooth_t6 {k ν σ Λ cΛ L τ F G : ℝ} {n : ℕ} (hk : 1 ≤ k) (hν : 0 < ν)
    (hkν : 1 ≤ k * ν) (hν1 : ν ≤ 1) (hσ1 : 1 ≤ σ) (hσk : σ ≤ k) (hΛ0 : 0 ≤ Λ)
    (hΛ : Λ ≤ cΛ * k ^ 5) (hL : 0 < L) (hτ : (3 : ℝ) ^ n ≤ τ * L) (hF : 0 ≤ F) (hG : 0 ≤ G) :
    (3 : ℝ) ^ n * (1 + σ⁻¹ * Λ) * (Λ / ν * G + L / ν * F) ≤
      (1 + cΛ) ^ 2 * k ^ 11 * τ * (σ⁻¹ * L ^ 2 * F + L * G) := by
  obtain ⟨-, hνi, -, -, -, hσν, hσi⟩ := linf_smooth_facts hk hν hkν hν1 hσ1 hσk
  have hk0 : 0 < k := lt_of_lt_of_le one_pos hk
  have hσ0 : 0 < σ := lt_of_lt_of_le one_pos hσ1
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hτ0 : 0 ≤ τ := by
    by_contra hneg
    have : τ * L < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hneg) hL
    linarith only [this, hτ, h3]
  have hk5 : 1 ≤ k ^ 5 := one_le_pow₀ hk
  have hcΛ : 0 ≤ cΛ := by
    by_contra hneg
    have : cΛ * k ^ 5 < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hneg) (by positivity)
    linarith only [this, hΛ, hΛ0]
  have h1 : 1 + σ⁻¹ * Λ ≤ (1 + cΛ) * k ^ 5 := by
    have : σ⁻¹ * Λ ≤ 1 * (cΛ * k ^ 5) := mul_le_mul hσi hΛ hΛ0 zero_le_one
    nlinarith only [this, hk5]
  have h2 : Λ / ν * G + L / ν * F ≤ (1 + cΛ) * k ^ 6 * (σ⁻¹ * L ^ 2 * F + L * G) * L⁻¹ := by
    have e : (1 + cΛ) * k ^ 6 * (σ⁻¹ * L ^ 2 * F + L * G) * L⁻¹ =
        (1 + cΛ) * k ^ 6 * (σ⁻¹ * L * F) + (1 + cΛ) * k ^ 6 * G := by
      field_simp
    rw [e]
    have a1 : Λ / ν * G ≤ (cΛ * k ^ 5) * k * G := by
      rw [div_eq_mul_inv]; gcongr
    have a2 : L / ν * F ≤ k ^ 2 * (σ⁻¹ * L * F) := by
      have : L / ν * F = (σ * ν⁻¹) * (σ⁻¹ * L * F) := by field_simp
      rw [this]; gcongr
    have a3 : (cΛ * k ^ 5) * k * G ≤ (1 + cΛ) * k ^ 6 * G := by
      have : (cΛ * k ^ 5) * k = cΛ * k ^ 6 := by ring
      rw [this]; gcongr; linarith only
    have a4 : k ^ 2 * (σ⁻¹ * L * F) ≤ (1 + cΛ) * k ^ 6 * (σ⁻¹ * L * F) := by
      gcongr
      calc k ^ 2 = 1 * k ^ 2 := (one_mul _).symm
        _ ≤ (1 + cΛ) * k ^ 6 :=
          mul_le_mul (by linarith only [hcΛ]) (pow_le_pow_right₀ hk (by norm_num))
            (by positivity) (by positivity)
    linarith only [a1, a2, a3, a4]
  have h20 : 0 ≤ Λ / ν * G + L / ν * F := by positivity
  calc (3 : ℝ) ^ n * (1 + σ⁻¹ * Λ) * (Λ / ν * G + L / ν * F)
      ≤ (τ * L) * ((1 + cΛ) * k ^ 5) *
          ((1 + cΛ) * k ^ 6 * (σ⁻¹ * L ^ 2 * F + L * G) * L⁻¹) := by gcongr
    _ = (1 + cΛ) ^ 2 * k ^ 11 * τ * (σ⁻¹ * L ^ 2 * F + L * G) := by
        field_simp

/-- The constant of the non-leading part of `linfErr`. -/
noncomputable def linfCp (Kp Cin cθ cΛ : ℝ) : ℝ :=
  9 * Kp * Cin ^ 2 + 3 + 3 * cθ + cθ * (2 * Kp * Cin + 15 * Kp * Cin ^ 2) + (1 + cΛ) ^ 2

/-- **The error of the deterministic assembly, in the parameters of the probabilistic inputs.**
With the flux constants of the cell bounds, `Gb = σ^{1/2} ν^{-1/2} Rb`, `Bb = 3^n Rb`, `θ = c_θ τ`,
`3^n ≤ τ L`, `q ≤ Q` and `Λ ≤ c_Λ k⁵`, the error `linfErr` is the leading term `K_p C δ L Rb` plus
`C_p (Q + 1) k^{11} τ (L Rb + σ⁻¹ L² F + L G)`. -/
theorem linf_smooth_err {k ν σ δ ρ Cin Kp L τ cθ cΛ Λ q Q Rb F G : ℝ} {n : ℕ} (hk : 1 ≤ k)
    (hν : 0 < ν) (hkν : 1 ≤ k * ν) (hν1 : ν ≤ 1) (hσ1 : 1 ≤ σ) (hσk : σ ≤ k) (hδ0 : 0 ≤ δ)
    (hδk : δ ≤ k) (hρ1 : ρ ≤ 1) (hCin : 0 ≤ Cin) (hKp : 0 ≤ Kp) (hL : 0 < L)
    (hhL : (3 : ℝ) ^ n ≤ L) (hτ : (3 : ℝ) ^ n ≤ τ * L) (hcθ : 0 ≤ cθ) (hΛ0 : 0 ≤ Λ)
    (hΛ : Λ ≤ cΛ * k ^ 5) (hq : 0 ≤ q) (hqQ : q ≤ Q) (hRb : 0 ≤ Rb) (hF : 0 ≤ F)
    (hG : 0 ≤ G) :
    linfErr L ((3 : ℝ) ^ n) σ ν Λ q (cθ * τ) (Kp * l2e_aC Cin σ ν δ)
        (Kp * l2e_b Cin σ ν ρ δ k n) (Kp * l2e_aC Cin σ ν δ + σ * Kp * l2e_e Cin σ ν)
        (Kp * l2e_b Cin σ ν ρ δ k n + σ * Kp * l2e_g Cin σ ν n)
        (Real.sqrt σ * (Real.sqrt ν)⁻¹ * Rb) ((3 : ℝ) ^ n * Rb) F G ≤
      Kp * Cin * δ * (L * Rb) +
        linfCp Kp Cin cθ cΛ * ((Q + 1) * k ^ 11) * τ * (L * Rb + σ⁻¹ * L ^ 2 * F + L * G) := by
  have hk0 : 0 < k := lt_of_lt_of_le one_pos hk
  have hσ0 : 0 < σ := lt_of_lt_of_le one_pos hσ1
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hτ0 : 0 ≤ τ := by
    by_contra hneg
    have : τ * L < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hneg) hL
    linarith only [this, hτ, h3]
  have hQ : 0 ≤ Q := hq.trans hqQ
  set S : ℝ := L * Rb + σ⁻¹ * L ^ 2 * F + L * G with hS
  set P : ℝ := (Q + 1) * k ^ 11 with hP
  have hY : 0 ≤ L * Rb := by positivity
  have hΦ : 0 ≤ σ⁻¹ * L ^ 2 * F := by positivity
  have hΓ : 0 ≤ L * G := by positivity
  have hS0 : 0 ≤ S := by positivity
  have hΦS : σ⁻¹ * L ^ 2 * F ≤ S := by rw [hS]; linarith only [hY, hΓ]
  have hΓS : L * G ≤ S := by rw [hS]; linarith only [hY, hΦ]
  have hYΦS : L * Rb + σ⁻¹ * L ^ 2 * F ≤ S := by rw [hS]; linarith only [hΓ]
  have hΦΓS : σ⁻¹ * L ^ 2 * F + L * G ≤ S := by rw [hS]; linarith only [hY]
  have hP1 : 1 ≤ P := by
    have := linf_smooth_kpow hk hQ (j := 0) (by norm_num)
    simpa using this
  have hP3 : k ^ 3 ≤ P := linf_smooth_kpow hk hQ (by norm_num)
  have hP11 : k ^ 11 ≤ P := linf_smooth_kpow hk hQ (by norm_num)
  have hPQ : Q * k ^ 2 ≤ P := by
    have h1 : k ^ 2 ≤ k ^ 11 := pow_le_pow_right₀ hk (by norm_num)
    have h2 : 0 ≤ k ^ 11 := by positivity
    have h3 : Q * k ^ 2 ≤ Q * k ^ 11 := mul_le_mul_of_nonneg_left h1 hQ
    rw [hP]; nlinarith only [h3, h2]
  -- the leading term
  have t1 : L * σ⁻¹ * (Kp * l2e_aC Cin σ ν δ * (Real.sqrt σ * (Real.sqrt ν)⁻¹ * Rb)) =
      Kp * Cin * δ * (L * Rb) := by
    have hs : Real.sqrt σ * Real.sqrt σ = σ := Real.mul_self_sqrt hσ0.le
    have hn : Real.sqrt ν * (Real.sqrt ν)⁻¹ = 1 :=
      mul_inv_cancel₀ (Real.sqrt_ne_zero'.2 hν)
    unfold l2e_aC
    calc L * σ⁻¹ * (Kp * (Cin * Real.sqrt σ * δ * Real.sqrt ν) *
          (Real.sqrt σ * (Real.sqrt ν)⁻¹ * Rb))
        = Kp * Cin * δ * (L * Rb) * (σ⁻¹ * (Real.sqrt σ * Real.sqrt σ)) *
            (Real.sqrt ν * (Real.sqrt ν)⁻¹) := by ring
      _ = Kp * Cin * δ * (L * Rb) := by
          rw [hs, hn, inv_mul_cancel₀ hσ0.ne', mul_one, mul_one]
  -- the other terms
  have b2 := (linf_smooth_t2 (n := n) (L := L) (τ := τ) (F := F) (Kp := Kp) hk hν hkν hν1 hσ1
    hσk hδ0 hδk hρ1 hCin hKp hL hτ hF).trans
    (linf_smooth_up (by positivity) (by positivity) hP3 hτ0 hΦ hΦS)
  have b3 := (linf_smooth_t3 (q := q) (Q := Q) hk hν hkν hν1 hσ1 hσk hL hhL hτ hq hqQ hRb hF
    hG).trans (linf_smooth_up (c := 2) (by norm_num) (by positivity) hPQ hτ0 hS0 le_rfl)
  have b4a : L * (cθ * τ) * (linfDG q ((3 : ℝ) ^ n) ν (Real.sqrt σ * (Real.sqrt ν)⁻¹ * Rb)
      ((3 : ℝ) ^ n * Rb) F G / (3 : ℝ) ^ n) ≤ (2 * cθ) * P * τ * S := by
    have h := linf_smooth_t4a (q := q) (Q := Q) hk hν hkν hν1 hσ1 hσk hL hhL hq hqQ hRb hF hG
    calc L * (cθ * τ) * (linfDG q ((3 : ℝ) ^ n) ν (Real.sqrt σ * (Real.sqrt ν)⁻¹ * Rb)
          ((3 : ℝ) ^ n * Rb) F G / (3 : ℝ) ^ n)
        = cθ * τ * (L * (linfDG q ((3 : ℝ) ^ n) ν (Real.sqrt σ * (Real.sqrt ν)⁻¹ * Rb)
          ((3 : ℝ) ^ n * Rb) F G / (3 : ℝ) ^ n)) := by ring
      _ ≤ cθ * τ * (2 * (Q * k ^ 2) * S) := by gcongr
      _ = (2 * cθ) * (Q * k ^ 2) * τ * S := by ring
      _ ≤ (2 * cθ) * P * τ * S := by gcongr
  have b4b : L * (cθ * τ) * G ≤ cθ * P * τ * S := by
    calc L * (cθ * τ) * G = cθ * 1 * τ * (L * G) := by ring
      _ ≤ cθ * P * τ * S := linf_smooth_up hcθ zero_le_one hP1 hτ0 hΓ hΓS
  have b4c : L * (cθ * τ) * (σ⁻¹ * ((Kp * l2e_aC Cin σ ν δ + σ * Kp * l2e_e Cin σ ν) *
          (Real.sqrt σ * (Real.sqrt ν)⁻¹ * Rb) +
        (Kp * l2e_b Cin σ ν ρ δ k n + σ * Kp * l2e_g Cin σ ν n) * F)) ≤
      (cθ * (2 * Kp * Cin + 15 * Kp * Cin ^ 2)) * P * τ * S := by
    have h := linf_smooth_t4c (n := n) (L := L) (Rb := Rb) (F := F) hk hν hkν hν1 hσ1 hσk hδ0 hδk
      hρ1 hCin hKp hL hhL hRb hF
    calc L * (cθ * τ) * (σ⁻¹ * ((Kp * l2e_aC Cin σ ν δ + σ * Kp * l2e_e Cin σ ν) *
          (Real.sqrt σ * (Real.sqrt ν)⁻¹ * Rb) +
        (Kp * l2e_b Cin σ ν ρ δ k n + σ * Kp * l2e_g Cin σ ν n) * F))
        = cθ * τ * (L * (σ⁻¹ * ((Kp * l2e_aC Cin σ ν δ + σ * Kp * l2e_e Cin σ ν) *
          (Real.sqrt σ * (Real.sqrt ν)⁻¹ * Rb) +
        (Kp * l2e_b Cin σ ν ρ δ k n + σ * Kp * l2e_g Cin σ ν n) * F))) := by ring
      _ ≤ cθ * τ * ((2 * Kp * Cin + 15 * Kp * Cin ^ 2) * k ^ 3 *
          (L * Rb + σ⁻¹ * L ^ 2 * F)) := by gcongr
      _ = (cθ * (2 * Kp * Cin + 15 * Kp * Cin ^ 2)) * k ^ 3 * τ *
          (L * Rb + σ⁻¹ * L ^ 2 * F) := by ring
      _ ≤ (cθ * (2 * Kp * Cin + 15 * Kp * Cin ^ 2)) * P * τ * S :=
          linf_smooth_up (by positivity) (by positivity) hP3 hτ0 (by positivity) hYΦS
  have b5 : L * σ⁻¹ * (3 : ℝ) ^ n * F ≤ 1 * P * τ * S := by
    calc L * σ⁻¹ * (3 : ℝ) ^ n * F ≤ L * σ⁻¹ * (τ * L) * F := by gcongr
      _ = 1 * 1 * τ * (σ⁻¹ * L ^ 2 * F) := by ring
      _ ≤ 1 * P * τ * S := linf_smooth_up zero_le_one zero_le_one hP1 hτ0 hΦ hΦS
  have b6 := (linf_smooth_t6 (n := n) hk hν hkν hν1 hσ1 hσk hΛ0 hΛ hL hτ hF hG).trans
    (linf_smooth_up (by positivity) (by positivity) hP11 hτ0 (by positivity) hΦΓS)
  have e : linfErr L ((3 : ℝ) ^ n) σ ν Λ q (cθ * τ) (Kp * l2e_aC Cin σ ν δ)
        (Kp * l2e_b Cin σ ν ρ δ k n) (Kp * l2e_aC Cin σ ν δ + σ * Kp * l2e_e Cin σ ν)
        (Kp * l2e_b Cin σ ν ρ δ k n + σ * Kp * l2e_g Cin σ ν n)
        (Real.sqrt σ * (Real.sqrt ν)⁻¹ * Rb) ((3 : ℝ) ^ n * Rb) F G =
      L * σ⁻¹ * (Kp * l2e_aC Cin σ ν δ * (Real.sqrt σ * (Real.sqrt ν)⁻¹ * Rb)) +
        L * σ⁻¹ * (Kp * l2e_b Cin σ ν ρ δ k n * F) +
        linfDG q ((3 : ℝ) ^ n) ν (Real.sqrt σ * (Real.sqrt ν)⁻¹ * Rb) ((3 : ℝ) ^ n * Rb) F G +
        L * (cθ * τ) * (linfDG q ((3 : ℝ) ^ n) ν (Real.sqrt σ * (Real.sqrt ν)⁻¹ * Rb)
          ((3 : ℝ) ^ n * Rb) F G / (3 : ℝ) ^ n) +
        L * (cθ * τ) * G +
        L * (cθ * τ) * (σ⁻¹ * ((Kp * l2e_aC Cin σ ν δ + σ * Kp * l2e_e Cin σ ν) *
            (Real.sqrt σ * (Real.sqrt ν)⁻¹ * Rb) +
          (Kp * l2e_b Cin σ ν ρ δ k n + σ * Kp * l2e_g Cin σ ν n) * F)) +
        L * σ⁻¹ * (3 : ℝ) ^ n * F +
        (3 : ℝ) ^ n * (1 + σ⁻¹ * Λ) * (Λ / ν * G + L / ν * F) := by
    unfold linfErr; ring
  have eC : linfCp Kp Cin cθ cΛ * P * τ * S =
      9 * Kp * Cin ^ 2 * P * τ * S + 2 * P * τ * S + (2 * cθ) * P * τ * S + cθ * P * τ * S +
        (cθ * (2 * Kp * Cin + 15 * Kp * Cin ^ 2)) * P * τ * S + 1 * P * τ * S +
        (1 + cΛ) ^ 2 * P * τ * S := by
    unfold linfCp; ring
  rw [e, t1, eC]
  linarith only [b2, b3, b4a, b4b, b4c, b5, b6]

/-- The bound of the local quantity `L Rb`: with `ℋ ≤ 2 Z + C_H (Γ + Φ)`, the window
`κ ≤ (N + 1) log k` and the smoothing factor `ι ≤ 3`. -/
theorem linf_smooth_Yb {CL H Φ Γ Z lk CH N κ ι : ℝ} (hCL : 0 ≤ CL)
    (hH : H ≤ 2 * Z + CH * (Γ + Φ)) (hκ : κ ≤ (N + 1) * lk) (hι : ι ≤ 3) (hΦ : 0 ≤ Φ)
    (hΓ : 0 ≤ Γ) (hZ : 0 ≤ Z) (hlk : 1 ≤ lk) (hCH : 0 ≤ CH) (hN : 0 ≤ N) :
    CL * (H + Φ + κ * Γ + ι * Γ) ≤ CL * (CH + N + 7) * (Z + Φ + lk * Γ) := by
  have h1 : κ * Γ ≤ (N + 1) * lk * Γ := mul_le_mul_of_nonneg_right hκ hΓ
  have h2 : ι * Γ ≤ 3 * Γ := mul_le_mul_of_nonneg_right hι hΓ
  have h3 : CH * Γ ≤ CH * (lk * Γ) := by
    have : Γ ≤ lk * Γ := le_mul_of_one_le_left hΓ hlk
    exact mul_le_mul_of_nonneg_left this hCH
  have h4 : 3 * Γ ≤ 3 * (lk * Γ) := by
    have : Γ ≤ lk * Γ := le_mul_of_one_le_left hΓ hlk
    linarith only [this]
  have hin : H + Φ + κ * Γ + ι * Γ ≤ (CH + N + 7) * (Z + Φ + lk * Γ) := by
    have h5 : 0 ≤ (CH + N + 5) * Z := by positivity
    have h6 : 0 ≤ (N + 6) * Φ := by positivity
    have h7 : 0 ≤ 3 * (lk * Γ) := by positivity
    nlinarith only [hH, h1, h2, h3, h4, h5, h6, h7]
  have := mul_le_mul_of_nonneg_left hin hCL
  linarith only [this]

/-- **Absorption.** If `Z ≤ C_d (K_C δ Y + ϖ (Y + Φ + Γ))`, `Y ≤ C_Y (Z + Φ + l Γ)`, `ϖ ≤ δ` and
`C_d (K_C + 1) C_Y δ ≤ 1/2`, then `Z ≤ 2 C_d (K_C + 1) (C_Y + 1) δ (Φ + l Γ)`. -/
theorem linf_smooth_absorb {Z Y Φ Γ lk Cd KC δ ϖ CY : ℝ} (hZ0 : 0 ≤ Z) (hΦ : 0 ≤ Φ)
    (hΓ : 0 ≤ Γ) (hlk : 1 ≤ lk) (hCd : 0 ≤ Cd) (hKC : 0 ≤ KC) (hδ : 0 ≤ δ)
    (hZ : Z ≤ Cd * (KC * δ * Y + ϖ * (Y + Φ + Γ)))
    (hY : Y ≤ CY * (Z + Φ + lk * Γ)) (hY0 : 0 ≤ Y) (hϖ : ϖ ≤ δ)
    (hsmall : Cd * (KC + 1) * CY * δ ≤ 1 / 2) :
    Z ≤ 2 * Cd * (KC + 1) * (CY + 1) * δ * (Φ + lk * Γ) := by
  set D : ℝ := Φ + lk * Γ with hD
  have hD0 : 0 ≤ D := by positivity
  have hYΦΓ : Y + Φ + Γ ≤ Y + D := by
    have : Γ ≤ lk * Γ := le_mul_of_one_le_left hΓ hlk
    rw [hD]; linarith only [this]
  have hϖ0 : 0 ≤ Y + Φ + Γ := by positivity
  have h1 : ϖ * (Y + Φ + Γ) ≤ δ * (Y + D) :=
    mul_le_mul hϖ hYΦΓ hϖ0 hδ
  have hY' : Y ≤ CY * (Z + D) := by
    have e : Z + D = Z + Φ + lk * Γ := by rw [hD]; ring
    rw [e]; exact hY
  have h2 : (KC + 1) * δ * Y ≤ (KC + 1) * δ * (CY * (Z + D)) :=
    mul_le_mul_of_nonneg_left hY' (by positivity)
  have h3 : KC * δ * Y + ϖ * (Y + Φ + Γ) ≤ (KC + 1) * δ * (CY * (Z + D)) + δ * D := by
    have e : (KC + 1) * δ * Y = KC * δ * Y + δ * Y := by ring
    linarith only [h1, h2, e]
  have h4 : Z ≤ Cd * ((KC + 1) * δ * (CY * (Z + D)) + δ * D) :=
    hZ.trans (mul_le_mul_of_nonneg_left h3 hCd)
  have h5 : Cd * (KC + 1) * CY * δ * Z ≤ 1 / 2 * Z := mul_le_mul_of_nonneg_right hsmall hZ0
  have h6 : Cd * ((KC + 1) * CY * δ * D + δ * D) ≤ Cd * (KC + 1) * (CY + 1) * δ * D := by
    have : (KC + 1) * CY * δ * D + δ * D ≤ (KC + 1) * (CY + 1) * δ * D := by
      have : 0 ≤ KC * δ * D := by positivity
      nlinarith only [this]
    have := mul_le_mul_of_nonneg_left this hCd
    linarith only [this]
  have e : Cd * ((KC + 1) * δ * (CY * (Z + D)) + δ * D) =
      Cd * (KC + 1) * CY * δ * Z + Cd * ((KC + 1) * CY * δ * D + δ * D) := by ring
  rw [e] at h4
  linarith only [h4, h5, h6]

end SuperdiffusionCLT.Section7
