/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Localization.LocalizationB

/-!
# Elementary steps of `lem.localization`

The weighted arithmetic-geometric mean inequality for the right-hand side of
`error_step1`, the existence of the local minimizers `S_z`, the `L²` membership of the fluctuation
`F_z`, and the real arithmetic that turns `L1` and `L2` into `m^{-50}`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)
open SuperdiffusionCLT.Section2.Cutoff SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section3.ResponseFields
open scoped ENNReal

variable {d : ℕ}

theorem loc_abs_le {s f lam : ℝ} (hs : 0 ≤ s) (hf : 0 ≤ f) (hlam : 0 < lam) :
    Real.sqrt f * (2 * Real.sqrt s + Real.sqrt f) ≤ lam * s + (lam⁻¹ + 1) * f := by
  set a := Real.sqrt s with ha
  set b := Real.sqrt f with hb
  have ha2 : a ^ 2 = s := Real.sq_sqrt hs
  have hb2 : b ^ 2 = f := Real.sq_sqrt hf
  have hl : lam⁻¹ * lam = 1 := inv_mul_cancel₀ hlam.ne'
  have h := mul_nonneg (inv_nonneg.2 hlam.le) (sq_nonneg (lam * a - b))
  have e : lam⁻¹ * (lam * a - b) ^ 2 = lam * a ^ 2 - 2 * a * b + lam⁻¹ * b ^ 2 := by
    have : lam⁻¹ * (lam * a - b) ^ 2 = (lam⁻¹ * lam) * lam * a ^ 2 - 2 * (lam⁻¹ * lam) * a * b + lam⁻¹ * b ^ 2 := by
      ring
    rw [this, hl]; ring
  rw [← ha2, ← hb2]
  nlinarith only [h, e]

theorem loc_final_arith {nu : ℝ} {m : ℕ} {C1 C2 : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hm : 1 ≤ m)
    (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) :
    ((nu⁻¹ * (m : ℝ)) ^ 90)⁻¹ * (C1 * nu⁻¹ ^ 4 * (m : ℝ) ^ 4) +
        ((((nu⁻¹ * (m : ℝ)) ^ 90)⁻¹)⁻¹ + 1) * (C2 * ((nu⁻¹ * (m : ℝ)) ^ 190)⁻¹) ≤
      (C1 + 2 * C2) * (m : ℝ) ^ (-(50 : ℝ)) := by
  set L : ℝ := nu⁻¹ * (m : ℝ) with hLdef
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hnuinv : 1 ≤ nu⁻¹ := one_le_inv₀ hnu |>.2 hnu1
  have hL1 : 1 ≤ L := by rw [hLdef]; nlinarith only [hmR, hnuinv]
  have hLpos : 0 < L := by linarith only [hL1]
  have hmL : (m : ℝ) ≤ L := by rw [hLdef]; nlinarith only [hmR, hnuinv]
  have key : ∀ j e : ℕ, j + 50 ≤ e → L ^ j * (L ^ e)⁻¹ ≤ (L ^ 50)⁻¹ := by
    intro j e hje
    rw [← div_eq_mul_inv, ← one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul,
      ← pow_add]
    exact pow_le_pow_right₀ hL1 hje
  have e4 : nu⁻¹ ^ 4 * (m : ℝ) ^ 4 = L ^ 4 := by rw [hLdef, mul_pow]
  have h90 : (((L ^ 90)⁻¹)⁻¹ + 1) ≤ 2 * L ^ 90 := by
    rw [inv_inv]
    have : 1 ≤ L ^ 90 := one_le_pow₀ hL1
    linarith only [this]
  have T1 : (L ^ 90)⁻¹ * (C1 * nu⁻¹ ^ 4 * (m : ℝ) ^ 4) ≤ C1 * (L ^ 50)⁻¹ := by
    calc _ = C1 * (L ^ 4 * (L ^ 90)⁻¹) := by rw [mul_assoc, e4]; ring
      _ ≤ C1 * (L ^ 50)⁻¹ := mul_le_mul_of_nonneg_left (key 4 90 (by norm_num)) hC1
  have T2 : (((L ^ 90)⁻¹)⁻¹ + 1) * (C2 * (L ^ 190)⁻¹) ≤ 2 * C2 * (L ^ 50)⁻¹ := by
    calc _ ≤ (2 * L ^ 90) * (C2 * (L ^ 190)⁻¹) :=
          mul_le_mul_of_nonneg_right h90 (by positivity)
      _ = 2 * C2 * (L ^ 90 * (L ^ 190)⁻¹) := by ring
      _ ≤ 2 * C2 * (L ^ 50)⁻¹ :=
          mul_le_mul_of_nonneg_left (key 90 190 (by norm_num)) (by positivity)
  have hmL50 : ((L ^ 50)⁻¹) ≤ (m : ℝ) ^ (-(50 : ℝ)) := by
    rw [Real.rpow_neg (by positivity), show (50 : ℝ) = ((50 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hmL 50)
  calc _ ≤ C1 * (L ^ 50)⁻¹ + 2 * C2 * (L ^ 50)⁻¹ := add_le_add T1 T2
    _ = (C1 + 2 * C2) * (L ^ 50)⁻¹ := by ring
    _ ≤ (C1 + 2 * C2) * (m : ℝ) ^ (-(50 : ℝ)) :=
        mul_le_mul_of_nonneg_left hmL50 (by positivity)

theorem loc_isBlockL2_blockFluct [NeZero d] (nu : ℝ) (L : ℕ)
    (P : ProbabilityMeasure (ShellSeq d)) (Q : TriadicCube d) {g1 g2 : Vec d → Vec d}
    (h1 : MemVectorL2 (openCubeSet Q) g1) (h2 : MemVectorL2 (openCubeSet Q) g2) :
    IsBlockL2 (cubeSet Q) (blockFluct nu L P Q g1 g2) := by
  refine ⟨?_, ?_⟩
  · rw [memVectorL2_cubeSet_iff_openCubeSet]
    exact (loc_fluct_memL2 Q h1 (Set.Subset.refl _)).const_smul
      ((sigmaBarInfinite nu L P) ^ (-(1 : ℝ) / 2))
  · rw [memVectorL2_cubeSet_iff_openCubeSet]
    exact (loc_fluct_memL2 Q h2 (Set.Subset.refl _)).const_smul
      ((sigmaBarInfinite nu L P) ^ ((1 : ℝ) / 2))

/-- Minimizers `S_z` of the constant-offset problems exist, for every sample and every cube. -/
theorem loc_exists_minimizers [NeZero d] {nu : ℝ} (hnu : 0 < nu) (m : ℕ)
    (slope : ShellSeq d → TriadicCube d → BlockVec d) :
    ∃ S : ShellSeq d → TriadicCube d → BlockState d, ∀ omega (Q : TriadicCube d),
      IsBlockOffsetMinimizer (coefficientCutoff nu omega m).toCoeffField (cubeSet Q)
        (constBlockState (slope omega Q)) (S omega Q) := by
  have hex : ∀ (omega : ShellSeq d) (Q : TriadicCube d),
      ∃ X : BlockState d, IsBlockOffsetMinimizer (coefficientCutoff nu omega m).toCoeffField
        (cubeSet Q) (constBlockState (slope omega Q)) X := by
    intro omega Q
    obtain ⟨lam, Lam, hEll⟩ := exists_isEllipticFieldOn_coefficientCutoff_cubeSet hnu omega m Q
    obtain ⟨X, hX, -⟩ := exists_isBlockOffsetMinimizer_cubeSet Q hEll
      (F := constBlockState (slope omega Q)) (memVectorL2_const _) (memVectorL2_const _)
    exact ⟨X, hX⟩
  choose S hS using hex
  exact ⟨S, hS⟩

end SuperdiffusionCLT.Section5
