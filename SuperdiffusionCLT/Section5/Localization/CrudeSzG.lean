/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Localization.CrudeSzF

/-!
# The probabilistic assembly of the crude bound

An abstract assembly lemma: if the per-cube integrands are bounded by `2Λ r (2 + a + b)` with the
second moment of `r` bounded and `subcubeAvg (a² + b²)` bounded, through a quantity `u` with
`u² ≤ 256 (Wm + Z)` and `E[Wm], E[Z] ≤ B⁸`, then the average over the subcubes of the expectations
is at most `Λ (2 + (2 + 2B²) C₂ + 24 B²)`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization MeasureTheory
open scoped ENNReal

variable {d : ℕ}

theorem subcubeAvg_mono_on {Kc n : ℕ} {f g : TriadicCube d → ℝ≥0∞}
    (h : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ), f Q ≤ g Q) :
    subcubeAvg Kc n f ≤ subcubeAvg Kc n g := by
  unfold subcubeAvg
  exact mul_le_mul' le_rfl (Finset.sum_le_sum h)

theorem crudeSz_sum_lintegral_le_lintegral_sum {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (s : Finset (TriadicCube d)) (f : TriadicCube d → Ω → ℝ≥0∞) :
    ∑ Q ∈ s, ∫⁻ ω, f Q ω ∂μ ≤ ∫⁻ ω, ∑ Q ∈ s, f Q ω ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    simp_rw [Finset.sum_insert ha]
    exact (add_le_add le_rfl ih).trans (le_lintegral_add _ _)

theorem card_ne_zero_descendants {Kc n : ℕ} (hn : n ≤ Kc) :
    ((descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ)).card : ℝ≥0∞) ≠ 0 := by
  have hk : (n : ℤ) ≤ (originCube d (Kc : ℤ)).scale := by
    show (n : ℤ) ≤ (Kc : ℤ)
    exact_mod_cast hn
  exact_mod_cast (Finset.card_pos.2 (descendantsAtScale_nonempty _ hk)).ne'

theorem crudeSz_subcubeAvg_lintegral_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {Kc n : ℕ}
    (hn : n ≤ Kc)
    (f : TriadicCube d → Ω → ℝ≥0∞) :
    subcubeAvg Kc n (fun Q => ∫⁻ ω, f Q ω ∂μ) ≤
      ∫⁻ ω, subcubeAvg Kc n (fun Q => f Q ω) ∂μ := by
  unfold subcubeAvg
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 ?_)]
  · exact mul_le_mul' le_rfl (crudeSz_sum_lintegral_le_lintegral_sum μ _ f)
  · exact card_ne_zero_descendants hn

theorem lintegral_subcubeAvg_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {Kc n : ℕ}
    (hn : n ≤ Kc) (f : TriadicCube d → Ω → ℝ≥0∞) (hf : ∀ Q, Measurable (f Q)) {c : ℝ≥0∞}
    (hc : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ), ∫⁻ ω, f Q ω ∂μ ≤ c) :
    ∫⁻ ω, subcubeAvg Kc n (fun Q => f Q ω) ∂μ ≤ c := by
  unfold subcubeAvg
  have hne := card_ne_zero_descendants (d := d) hn
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hne),
    lintegral_finsetSum _ (fun Q _ => hf Q)]
  calc _ ≤ ((descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ)).card : ℝ≥0∞)⁻¹ *
        ∑ _Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ), c :=
        mul_le_mul' le_rfl (Finset.sum_le_sum hc)
    _ = c := by
      rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc,
        ENNReal.inv_mul_cancel hne (ENNReal.natCast_ne_top _), one_mul]

theorem amgm_square {u W : ℝ≥0∞} {B : ℝ} (hB : 0 < B) (h : u ^ 2 ≤ 256 * W) :
    u ≤ ENNReal.ofReal (1 / (32 * B ^ 4)) * (ENNReal.ofReal (256 * B ^ 8) + 256 * W) := by
  have hk := ennreal_two_mul_le (ENNReal.ofReal (16 * B ^ 4)) u
  have hB4 : 0 < B ^ 4 := by positivity
  have e1 : ENNReal.ofReal (1 / (32 * B ^ 4)) * (2 * ENNReal.ofReal (16 * B ^ 4)) = 1 := by
    have : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
    rw [this, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
    have : 1 / (32 * B ^ 4) * (2 * (16 * B ^ 4)) = 1 := by field_simp; ring
    rw [this, ENNReal.ofReal_one]
  have e2 : ENNReal.ofReal (16 * B ^ 4) ^ 2 = ENNReal.ofReal (256 * B ^ 8) := by
    rw [← ENNReal.ofReal_pow (by positivity)]
    congr 1; ring
  calc u = (ENNReal.ofReal (1 / (32 * B ^ 4)) * (2 * ENNReal.ofReal (16 * B ^ 4))) * u := by
        rw [e1, one_mul]
    _ = ENNReal.ofReal (1 / (32 * B ^ 4)) * (2 * ENNReal.ofReal (16 * B ^ 4) * u) := by ring
    _ ≤ ENNReal.ofReal (1 / (32 * B ^ 4)) *
          (ENNReal.ofReal (16 * B ^ 4) ^ 2 + u ^ 2) := mul_le_mul' le_rfl hk
    _ ≤ _ := by
        rw [e2]
        exact mul_le_mul' le_rfl (add_le_add le_rfl h)

end SuperdiffusionCLT.Section5
