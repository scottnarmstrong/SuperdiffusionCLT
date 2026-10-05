/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.CaccioppoliG
public import SuperdiffusionCLT.Section7.Prereq.RhsLemmaC

/-!
# Pointwise operator bound of a continuous field from an almost-everywhere bound
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal
open scoped Matrix.Norms.L2Operator

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- An almost-everywhere bound with respect to the normalized cube measure holds almost everywhere
on the open cube. -/
theorem ca1w_ae_openCube (Q : TriadicCube d) {P : Vec d → Prop}
    (h : ∀ᵐ x ∂normalizedCubeMeasure Q, P x) :
    ∀ᵐ x ∂(volume.restrict (openCubeSet Q)), P x := by
  have h1 : ∀ᵐ x' ∂(volume.restrict (cubeSet Q)), P x' := by
    have : normalizedCubeMeasure Q = ENNReal.ofReal (cubeVolume Q)⁻¹ • volume.restrict (cubeSet Q) := by
      rw [normalizedCubeMeasure, cubeMeasure]
    rw [this] at h
    have hne : ENNReal.ofReal (cubeVolume Q)⁻¹ ≠ 0 := by
      have : 0 < cubeVolume Q := by
        unfold cubeVolume
        exact pow_pos (r1_scaleFactor_pos Q) d
      exact (ENNReal.ofReal_pos.2 (inv_pos.2 this)).ne'
    exact (Measure.absolutelyContinuous_smul hne).ae_le h
  rwa [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] at h1

/-- A continuous matrix field whose operator norm is bounded almost everywhere on the open cube is
bounded at every point of the open cube. -/
theorem ca1w_opnorm_pointwise (Q : TriadicCube d) {M : Vec d → Mat d} (hM : Continuous M) {B : ℝ}
    (h : ∀ᵐ x ∂normalizedCubeMeasure Q, Book.Ch02.matrixOperatorNorm (M x) ≤ B) :
    ∀ x ∈ openCubeSet Q, Book.Ch02.matrixOperatorNorm (M x) ≤ B := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x0, hx0, hlt⟩ := hcon
  have hcont : Continuous fun x => Book.Ch02.matrixOperatorNorm (M x) := by
    simp only [Book.Ch02.matrixOperatorNorm_eq_l2_opNorm]
    exact hM.norm
  have hopen : IsOpen ({x | B < Book.Ch02.matrixOperatorNorm (M x)} ∩ openCubeSet Q) :=
    (isOpen_lt continuous_const hcont).inter (isOpen_openCubeSet Q)
  have hpos : 0 < (volume.restrict (openCubeSet Q))
      ({x | B < Book.Ch02.matrixOperatorNorm (M x)} ∩ openCubeSet Q) := by
    rw [Measure.restrict_apply hopen.measurableSet, Set.inter_assoc, Set.inter_self]
    exact hopen.measure_pos volume ⟨x0, hlt, hx0⟩
  have hae := ca1w_ae_openCube Q h
  have hz : (volume.restrict (openCubeSet Q))
      {x | ¬ Book.Ch02.matrixOperatorNorm (M x) ≤ B} = 0 := hae
  have hsub : {x | B < Book.Ch02.matrixOperatorNorm (M x)} ∩ openCubeSet Q ⊆
      {x | ¬ Book.Ch02.matrixOperatorNorm (M x) ≤ B} :=
    fun x hx => not_le.2 hx.1
  exact absurd (measure_mono_null hsub hz) hpos.ne'

/-- The pointwise operator bound of `ν Id + K` from the operator bound of `K`. -/
theorem ca1w_hop [NeZero d] {ν B : ℝ} (hν : 0 ≤ ν) (K : Mat d)
    (hK : Book.Ch02.matrixOperatorNorm K ≤ B) (v : Vec d) :
    eucNorm (matVecMul (ν • (1 : Mat d) + K) v) ≤ (ν + B) * eucNorm v := by
  refine (r1_eucNorm_matVecMul_le _ v).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (by unfold eucNorm; positivity)
  rw [Book.Ch02.matrixOperatorNorm_eq_l2_opNorm]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, ← Book.Ch02.matrixOperatorNorm_eq_l2_opNorm, Book.Ch02.matrixOperatorNorm_one,
      Real.norm_eq_abs, mul_one, abs_of_nonneg hν]
  · rw [← Book.Ch02.matrixOperatorNorm_eq_l2_opNorm]
    exact hK

/-- The square-root step: from the squared interior Caccioppoli bound to the form of `LipCaccInt`. -/
theorem ca1w_sqrt_step {ν S Cf C X W Fg F t : ℝ} (hν : 0 < ν) (hS : 0 < S)
    (hW : 0 ≤ W) (hFg : 0 ≤ Fg) (hFgF : Fg ≤ F) (ht : 0 < t) (hC : 1 ≤ C) (hCf : Cf ≤ C ^ 2)
    (h : ν * X ^ 2 ≤ Cf * (S * (t⁻¹) ^ 2 * W ^ 2 + S⁻¹ * t ^ 2 * Fg ^ 2)) :
    Real.sqrt ν * X ≤ C * (Real.sqrt S * (t⁻¹ * W) + (Real.sqrt S)⁻¹ * t * F) := by
  have hF : 0 ≤ F := le_trans hFg hFgF
  have hsS : 0 < Real.sqrt S := Real.sqrt_pos.2 hS
  have hC0 : 0 ≤ C := by linarith only [hC]
  set p : ℝ := Real.sqrt S * (t⁻¹ * W) with hp
  set q : ℝ := (Real.sqrt S)⁻¹ * t * F with hq
  have hp0 : 0 ≤ p := by positivity
  have hq0 : 0 ≤ q := by positivity
  have hq' : (Real.sqrt S)⁻¹ * t * Fg ≤ q :=
    mul_le_mul_of_nonneg_left hFgF (by positivity)
  have e1 : S * (t⁻¹) ^ 2 * W ^ 2 = p ^ 2 := by
    rw [hp, mul_pow, mul_pow, Real.sq_sqrt hS.le]; ring
  have e2 : S⁻¹ * t ^ 2 * Fg ^ 2 = ((Real.sqrt S)⁻¹ * t * Fg) ^ 2 := by
    rw [mul_pow, mul_pow, inv_pow, Real.sq_sqrt hS.le]
  have hq2 : ((Real.sqrt S)⁻¹ * t * Fg) ^ 2 ≤ q ^ 2 :=
    pow_le_pow_left₀ (by positivity) hq' 2
  have hsq : (Real.sqrt ν * X) ^ 2 ≤ (C * (p + q)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hν.le]
    calc ν * X ^ 2 ≤ Cf * (p ^ 2 + ((Real.sqrt S)⁻¹ * t * Fg) ^ 2) := by
          rw [← e1, ← e2]; exact h
      _ ≤ C ^ 2 * (p ^ 2 + q ^ 2) := by
          have h1 : p ^ 2 + ((Real.sqrt S)⁻¹ * t * Fg) ^ 2 ≤ p ^ 2 + q ^ 2 := by
            linarith only [hq2]
          have h2 : 0 ≤ p ^ 2 + ((Real.sqrt S)⁻¹ * t * Fg) ^ 2 := by positivity
          calc Cf * (p ^ 2 + ((Real.sqrt S)⁻¹ * t * Fg) ^ 2)
              ≤ C ^ 2 * (p ^ 2 + ((Real.sqrt S)⁻¹ * t * Fg) ^ 2) := mul_le_mul_of_nonneg_right hCf h2
            _ ≤ C ^ 2 * (p ^ 2 + q ^ 2) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ (C * (p + q)) ^ 2 := by
          rw [mul_pow C (p + q) 2]
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg C)
          nlinarith only [hp0, hq0]
  exact le_of_sq_le_sq hsq (mul_nonneg hC0 (add_nonneg hp0 hq0))

theorem ca1w_zpow_neg_two (m : ℕ) :
    (3 : ℝ) ^ (-2 * (m : ℤ)) = (((3 : ℝ) ^ m)⁻¹) ^ 2 := by
  rw [show -2 * (m : ℤ) = -((m : ℤ) * 2) by ring, zpow_neg, zpow_mul, zpow_natCast, inv_pow]
  norm_cast

theorem ca1w_zpow_two (m : ℕ) : (3 : ℝ) ^ (2 * (m : ℤ)) = ((3 : ℝ) ^ m) ^ 2 := by
  rw [show 2 * (m : ℤ) = (m : ℤ) * 2 by ring, zpow_mul, zpow_natCast]
  norm_cast

end SuperdiffusionCLT.Section7
