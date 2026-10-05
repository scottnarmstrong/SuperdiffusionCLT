/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Engine.Deterministic
public import SuperdiffusionCLT.Section6.Engine.InputsB
public import SuperdiffusionCLT.Section6.Engine.Params
public import SuperdiffusionCLT.Section6.Engine.SigmaGrowth
public import SuperdiffusionCLT.Section6.Engine.ScaleTail
public import SuperdiffusionCLT.Section6.Prereq.GrowthSpace
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Helpers for the assembly of the sharp-scale statement

Equality of growth spaces from equal finite dimension, the dyadic scale `3^k ∈ [2r, 6r]`,
and the division by the ellipticity constant in the growth of `σ̄`.
-/

@[expose] public section

open scoped ENNReal

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory

/-- Nested growth spaces of equal finite dimension coincide. -/
theorem ec6_growth_eq_of_le {d : ℕ} (a : CoeffField d) (hell : GrowthElliptic a) {γ γ' : ℝ}
    (hle : γ ≤ γ')
    (h : Module.finrank ℝ (Submodule.span ℝ (growthSpace a γ)) = 1 + d)
    (h' : Module.finrank ℝ (Submodule.span ℝ (growthSpace a γ')) = 1 + d) :
    growthSpace a γ' = growthSpace a γ := by
  have e1 : Submodule.span ℝ (growthSpace a γ) = growthSubmodule a γ hell :=
    Submodule.span_eq (growthSubmodule a γ hell)
  have e2 : Submodule.span ℝ (growthSpace a γ') = growthSubmodule a γ' hell :=
    Submodule.span_eq (growthSubmodule a γ' hell)
  rw [e1] at h
  rw [e2] at h'
  have hfin : FiniteDimensional ℝ (growthSubmodule a γ' hell) := by
    have : 0 < Module.finrank ℝ (growthSubmodule a γ' hell) := by omega
    exact Module.finite_of_finrank_pos this
  have hle' : growthSubmodule a γ hell ≤ growthSubmodule a γ' hell :=
    fun u hu => growthSpace_mono a hle hu
  have := Submodule.eq_of_le_of_finrank_eq hle' (by rw [h, h'])
  ext u
  have hu := SetLike.ext_iff.mp this u
  exact hu.symm

/-- Equality of the growth spaces at two exponents, from the dimension at each. -/
theorem ec6_growth_eq {d : ℕ} (a : CoeffField d) (hell : GrowthElliptic a) (γ γ' : ℝ)
    (h : Module.finrank ℝ (Submodule.span ℝ (growthSpace a γ)) = 1 + d)
    (h' : Module.finrank ℝ (Submodule.span ℝ (growthSpace a γ')) = 1 + d) :
    growthSpace a γ' = growthSpace a γ := by
  rcases le_total γ γ' with hle | hle
  · exact ec6_growth_eq_of_le a hell hle h h'
  · exact (ec6_growth_eq_of_le a hell hle h' h).symm

/-- A dyadic scale `3^k` between `2r` and `6r`, above any given scale. -/
theorem ec6_scale (n : ℕ) (r : ℝ) (hr : (3 : ℝ) ^ n ≤ r) :
    ∃ k : ℕ, n ≤ k ∧ 2 * r ≤ (3 : ℝ) ^ k ∧ (3 : ℝ) ^ k ≤ 6 * r := by
  have h3 : (1 : ℝ) < 3 := by norm_num
  have hn0 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hr0 : 0 < 2 * r := by linarith only [hr, hn0]
  refine ⟨⌈Real.logb 3 (2 * r)⌉₊, ?_, ?_, ?_⟩
  · have hl : (n : ℝ) ≤ Real.logb 3 (2 * r) := by
      rw [Real.le_logb_iff_rpow_le h3 hr0, Real.rpow_natCast]
      linarith only [hr, hn0]
    exact_mod_cast hl.trans (Nat.le_ceil _)
  · have hl : Real.logb 3 (2 * r) ≤ (⌈Real.logb 3 (2 * r)⌉₊ : ℝ) := Nat.le_ceil _
    have := (Real.logb_le_iff_le_rpow h3 hr0).1 hl
    rwa [Real.rpow_natCast] at this
  · have hlt : (⌈Real.logb 3 (2 * r)⌉₊ : ℝ) < Real.logb 3 (2 * r) + 1 := Nat.ceil_lt_add_one
      (Real.logb_nonneg h3 (by linarith only [hr, hn0, show (1 : ℝ) ≤ 3 ^ n from one_le_pow₀ (by norm_num)]))
    have h2 : (⌈Real.logb 3 (2 * r)⌉₊ : ℝ) - 1 ≤ Real.logb 3 (2 * r) := by linarith only [hlt]
    have h4 : (3 : ℝ) ^ ((⌈Real.logb 3 (2 * r)⌉₊ : ℝ) - 1) ≤ 2 * r := by
      have := (Real.le_logb_iff_rpow_le h3 hr0).1 h2
      exact this
    rw [Real.rpow_sub (by norm_num), Real.rpow_one, Real.rpow_natCast] at h4
    rw [div_le_iff₀ (by norm_num)] at h4
    linarith only [h4]

/-- Division of the growth of `σ̄` by the ellipticity constant. -/
theorem ec6_div_growth (nu Cs κ : ℝ) (hnu : 0 < nu) (σ : ℕ → ℝ) (L0 : ℕ)
    (h : ∀ k m : ℕ, L0 ≤ k → k ≤ m →
      0 < σ m ∧ σ (m + 1) ≤ 2 * σ m ∧ σ k ≤ Cs * (9 : ℝ) ^ (κ * ((m : ℝ) - (k : ℝ))) * σ m) :
    ∀ k m : ℕ, L0 ≤ k → k ≤ m →
      0 < σ m / nu ∧ σ (m + 1) / nu ≤ 2 * (σ m / nu) ∧
        σ k / nu ≤ Cs * (9 : ℝ) ^ (κ * ((m : ℝ) - (k : ℝ))) * (σ m / nu) := by
  intro k m hk hkm
  obtain ⟨h1, h2, h3⟩ := h k m hk hkm
  refine ⟨div_pos h1 hnu, ?_, ?_⟩
  · rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right h2 hnu.le
  · rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right h3 hnu.le

end SuperdiffusionCLT.Section6
