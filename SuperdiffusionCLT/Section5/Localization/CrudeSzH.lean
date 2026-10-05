/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Localization.CrudeSzG

/-!
# The abstract assembly

`crude_assembly`: see `CrudeSzG`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- The expectation of the doubling bound `u` of the assembly. -/
theorem lintegral_u_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {B : ℝ} (hB : 0 < B) (u Z Wm : Ω → ℝ≥0∞) (hWm : Measurable Wm)
    (hW : ∫⁻ ω, Wm ω ∂μ ≤ ENNReal.ofReal B ^ (8 : ℕ))
    (hZ : ∫⁻ ω, Z ω ∂μ ≤ ENNReal.ofReal B ^ (8 : ℕ))
    (hu : ∀ ω, u ω ^ 2 ≤ 256 * (Wm ω + Z ω)) :
    ∫⁻ ω, u ω ∂μ ≤ ENNReal.ofReal (24 * B ^ 4) := by
  set t : ℝ≥0∞ := ENNReal.ofReal (1 / (32 * B ^ 4)) with ht
  set K0 : ℝ≥0∞ := ENNReal.ofReal (256 * B ^ 8) with hK0
  have h1 : ∫⁻ ω, u ω ∂μ ≤ ∫⁻ ω, t * ((K0 + 256 * Wm ω) + 256 * Z ω) ∂μ := by
    refine lintegral_mono fun ω => ?_
    refine (amgm_square hB (hu ω)).trans (le_of_eq ?_)
    rw [ht, hK0]
    ring
  refine h1.trans ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hg : Measurable (fun ω => K0 + 256 * Wm ω) := measurable_const.add (hWm.const_mul _)
  rw [lintegral_add_left hg, lintegral_add_left measurable_const, lintegral_const, lintegral_const_mul _ hWm,
    lintegral_const_mul' _ _ (by norm_num)]
  simp only [measure_univ, mul_one]
  have hB8 : ENNReal.ofReal B ^ (8 : ℕ) = ENNReal.ofReal (B ^ 8) := (ENNReal.ofReal_pow hB.le 8).symm
  calc t * (K0 + 256 * ∫⁻ ω, Wm ω ∂μ + 256 * ∫⁻ ω, Z ω ∂μ) ≤
      t * (K0 + 256 * ENNReal.ofReal (B ^ 8) + 256 * ENNReal.ofReal (B ^ 8)) := by
        rw [hB8] at hW hZ
        exact mul_le_mul' le_rfl (add_le_add (add_le_add le_rfl (mul_le_mul' le_rfl hW))
          (mul_le_mul' le_rfl hZ))
    _ = ENNReal.ofReal (24 * B ^ 4) := by
        have e256 : (256 : ℝ≥0∞) = ENNReal.ofReal 256 := by simp
        rw [ht, hK0, e256, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity)
          (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have : (B ^ 4) ≠ 0 := by positivity
        field_simp
        ring

/-- **The abstract assembly of the crude bound.** -/
theorem crude_assembly {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Kc n : ℕ} (hn : n ≤ Kc) {Lam B C2 : ℝ} (hB : 0 < B) (hLam : 0 ≤ Lam) (hC2 : 0 ≤ C2)
    (r a b f : TriadicCube d → Ω → ℝ≥0∞) (Z Wm : Ω → ℝ≥0∞)
    (hr : ∀ Q, Measurable (r Q))
    (hr2 : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
      ∫⁻ ω, r Q ω ^ 2 ∂μ ≤ ENNReal.ofReal C2)
    (hWm : Measurable Wm) (hW : ∫⁻ ω, Wm ω ∂μ ≤ ENNReal.ofReal B ^ (8 : ℕ))
    (hZ : ∫⁻ ω, Z ω ∂μ ≤ ENNReal.ofReal B ^ (8 : ℕ))
    (hu : ∀ ω, (subcubeAvg Kc n (fun Q => a Q ω ^ 2) + subcubeAvg Kc n (fun Q => b Q ω ^ 2)) ^ 2 ≤
      256 * (Wm ω + Z ω))
    (hf : ∀ ω, ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
      f Q ω ≤ ENNReal.ofReal (2 * Lam) * (r Q ω * (2 + a Q ω + b Q ω))) :
    subcubeAvg Kc n (fun Q => ∫⁻ ω, f Q ω ∂μ) ≤
      ENNReal.ofReal (Lam * (2 + (2 + 2 * B ^ 2) * C2 + 24 * B ^ 2)) := by
  set c : ℝ≥0∞ := ENNReal.ofReal (B ^ 2) with hcdef
  set ci : ℝ≥0∞ := ENNReal.ofReal (B ^ 2)⁻¹ with hcidef
  have hB2 : 0 < B ^ 2 := by positivity
  have hc : c * ci = 1 := by
    rw [hcdef, hcidef, ← ENNReal.ofReal_mul hB2.le, mul_inv_cancel₀ hB2.ne', ENNReal.ofReal_one]
  set R : Ω → ℝ≥0∞ := fun ω => subcubeAvg Kc n (fun Q => r Q ω ^ 2) with hRdef
  set u : Ω → ℝ≥0∞ := fun ω =>
    subcubeAvg Kc n (fun Q => a Q ω ^ 2) + subcubeAvg Kc n (fun Q => b Q ω ^ 2) with hudef
  have hRm : Measurable R := by
    refine (Finset.measurable_sum _ (fun Q _ => (hr Q).pow_const 2)).const_mul _
  have h1 := crudeSz_subcubeAvg_lintegral_le μ hn f
  have h2 : ∀ ω, subcubeAvg Kc n (fun Q => f Q ω) ≤
      ENNReal.ofReal Lam * (2 + (2 + 2 * c) * R ω + ci * u ω) := by
    intro ω
    have e2 : ENNReal.ofReal (2 * Lam) = ENNReal.ofReal Lam * 2 := by
      rw [ENNReal.ofReal_mul (by norm_num)]
      simp [mul_comm]
    calc subcubeAvg Kc n (fun Q => f Q ω) ≤
          subcubeAvg Kc n (fun Q => ENNReal.ofReal (2 * Lam) * (r Q ω * (2 + a Q ω + b Q ω))) :=
          subcubeAvg_mono_on (hf ω)
      _ = ENNReal.ofReal Lam * (2 * subcubeAvg Kc n (fun Q => r Q ω * (2 + a Q ω + b Q ω))) := by
          rw [subcubeAvg_const_mul, e2, mul_assoc]
      _ ≤ _ := mul_le_mul' le_rfl (subcubeAvg_young hn hc (fun Q => r Q ω) (fun Q => a Q ω)
          (fun Q => b Q ω))
  have h3 : ∫⁻ ω, subcubeAvg Kc n (fun Q => f Q ω) ∂μ ≤
      ENNReal.ofReal Lam * ∫⁻ ω, (2 + (2 + 2 * c) * R ω + ci * u ω) ∂μ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_mono h2
  have hM : Measurable (fun ω => 2 + (2 + 2 * c) * R ω) := measurable_const.add (hRm.const_mul _)
  have hRint : ∫⁻ ω, R ω ∂μ ≤ ENNReal.ofReal C2 :=
    lintegral_subcubeAvg_le μ hn (fun Q ω => r Q ω ^ 2) (fun Q => (hr Q).pow_const 2) hr2
  have hui := lintegral_u_le μ hB u Z Wm hWm hW hZ hu
  have h4 : ∫⁻ ω, (2 + (2 + 2 * c) * R ω + ci * u ω) ∂μ ≤
      2 + (2 + 2 * c) * ENNReal.ofReal C2 + ci * ENNReal.ofReal (24 * B ^ 4) := by
    rw [lintegral_add_left hM, lintegral_add_left measurable_const, lintegral_const,
      lintegral_const_mul _ hRm, lintegral_const_mul' _ _ (by simp [hcidef])]
    simp only [measure_univ, mul_one]
    exact add_le_add (add_le_add le_rfl (mul_le_mul' le_rfl hRint)) (mul_le_mul' le_rfl hui)
  have h5 : ci * ENNReal.ofReal (24 * B ^ 4) = ENNReal.ofReal (24 * B ^ 2) := by
    rw [hcidef, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  refine h1.trans (h3.trans ?_)
  refine (mul_le_mul' le_rfl h4).trans (le_of_eq ?_)
  rw [h5, hcdef]
  rw [ENNReal.ofReal_mul hLam]
  congr 1
  symm
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity)]
  simp

end SuperdiffusionCLT.Section5
