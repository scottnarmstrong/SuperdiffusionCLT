/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Response.NeumannOscillationNorms
public import SuperdiffusionCLT.Section5.Response.NeumannOscillationYoung

/-!
# Moment bounds for the subcube oscillations

Generic estimates for the proof of `e.crude.Fz.bound`:

* `subcubeAvg_lintegral_le_osc`, `subcubeAvg_combo`: the subcube average of expectations and its
  linearity.
* `lintegral_pow_four_le_interpolation`: `E ‖F‖⁴_{L̲⁴} ≤ (2t/3) E ‖F‖²_{L̲²} + E ‖F‖⁸_{L̲⁸} / (3t²)`
  for every `t > 0`, the interpolation between the energy gap and the `L⁸` bound.

The interpolation needs measurability in the sample only of the `L̲²` norm.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open scoped ENNReal

noncomputable section

variable {d : ℕ}

theorem card_descendantsAtScale_ne_zero_osc {Kc n : ℕ} (hn : n ≤ Kc) :
    (descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ)).card ≠ 0 := by
  have hk : (n : ℤ) ≤ (originCube d (Kc : ℤ)).scale := by
    show (n : ℤ) ≤ (Kc : ℤ)
    exact_mod_cast hn
  rw [descendantsAtScale_eq_descendantsAtDepth _ hk, descendantsAtDepth_card]
  positivity

theorem subcubeAvg_mono_on_osc {Kc n : ℕ} {f g : TriadicCube d → ℝ≥0∞}
    (h : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ), f Q ≤ g Q) :
    subcubeAvg Kc n f ≤ subcubeAvg Kc n g := by
  unfold subcubeAvg
  exact mul_le_mul' le_rfl (Finset.sum_le_sum h)

/-- The subcube average of expectations is at most the expectation of the subcube average. -/
theorem subcubeAvg_lintegral_le_osc {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {Kc n : ℕ}
    (hn : n ≤ Kc) (F : TriadicCube d → Ω → ℝ≥0∞) :
    subcubeAvg Kc n (fun Q => ∫⁻ ω, F Q ω ∂μ) ≤
      ∫⁻ ω, subcubeAvg Kc n (fun Q => F Q ω) ∂μ := by
  unfold subcubeAvg
  have hc : ((descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ)).card : ℝ≥0∞)⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.2 (by exact_mod_cast card_descendantsAtScale_ne_zero_osc hn)
  rw [lintegral_const_mul' _ _ hc]
  exact mul_le_mul' le_rfl (osc_sum_lintegral_le_lintegral_sum _ _)

/-- Linearity of the subcube average for the shape of the oscillation bound. -/
theorem subcubeAvg_combo {Kc n : ℕ} (c₀ c₁ c₃ : ℝ≥0∞) (a₀ a₁ a₂ a₃ : TriadicCube d → ℝ≥0∞) :
    subcubeAvg Kc n (fun Q => c₀ * a₀ Q + 1024 * (c₁ * a₁ Q + a₂ Q + c₃ * a₃ Q)) =
      c₀ * subcubeAvg Kc n a₀ + 1024 * (c₁ * subcubeAvg Kc n a₁ + subcubeAvg Kc n a₂ +
        c₃ * subcubeAvg Kc n a₃) := by
  unfold subcubeAvg
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- **Interpolation**: for every `t > 0`,
`E ‖F‖⁴_{L̲⁴} ≤ (2t/3) E ‖F‖²_{L̲²} + E ‖F‖⁸_{L̲⁸} / (3t²)`; only the `L̲²` norm needs to be
measurable in the sample. -/
theorem lintegral_pow_four_le_interpolation {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] (μ : Measure Ω) {Kc : ℕ} (F : Ω → Vec d → E)
    (hmeas : ∀ ω, AEStronglyMeasurable (F ω)
      (normalizedCubeMeasure (originCube d (Kc : ℤ))))
    (hX : Measurable fun ω => SuperdiffusionCLT.Section2.Norms.cubeLpENorm
      (originCube d (Kc : ℤ)) 2 (F ω)) {t : ℝ} (ht : 0 < t) :
    ∫⁻ ω, (SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (Kc : ℤ)) 4
        (F ω)) ^ 4 ∂μ ≤
      ENNReal.ofReal (2 * t / 3) * ∫⁻ ω, (SuperdiffusionCLT.Section2.Norms.cubeLpENorm
        (originCube d (Kc : ℤ)) 2 (F ω)) ^ 2 ∂μ +
      ENNReal.ofReal (1 / (3 * t ^ 2)) * ∫⁻ ω, (SuperdiffusionCLT.Section2.Norms.cubeLpENorm
        (originCube d (Kc : ℤ)) 8 (F ω)) ^ 8 ∂μ := by
  set ν := normalizedCubeMeasure (originCube d (Kc : ℤ)) with hν
  have hpt : ∀ ω, (SuperdiffusionCLT.Section2.Norms.cubeLpENorm
      (originCube d (Kc : ℤ)) 4 (F ω)) ^ 4 ≤
      ENNReal.ofReal (2 * t / 3) * (SuperdiffusionCLT.Section2.Norms.cubeLpENorm
        (originCube d (Kc : ℤ)) 2 (F ω)) ^ 2 +
      ENNReal.ofReal (1 / (3 * t ^ 2)) * (SuperdiffusionCLT.Section2.Norms.cubeLpENorm
        (originCube d (Kc : ℤ)) 8 (F ω)) ^ 8 := by
    intro ω
    have hm : AEMeasurable (fun x => ‖F ω x‖ₑ) ν := (hmeas ω).enorm
    unfold SuperdiffusionCLT.Section2.Norms.cubeLpENorm
    have e4 : eLpNorm (F ω) 4 ν ^ 4 = ∫⁻ x, ‖F ω x‖ₑ ^ 4 ∂ν :=
      eLpNorm_nat_pow 4 (by norm_num) _ (hmeas ω)
    have e2 : eLpNorm (F ω) 2 ν ^ 2 = ∫⁻ x, ‖F ω x‖ₑ ^ 2 ∂ν :=
      eLpNorm_nat_pow 2 (by norm_num) _ (hmeas ω)
    have e8 : eLpNorm (F ω) 8 ν ^ 8 = ∫⁻ x, ‖F ω x‖ₑ ^ 8 ∂ν :=
      eLpNorm_nat_pow 8 (by norm_num) _ (hmeas ω)
    rw [e4, e2, e8]
    rw [← lintegral_const_mul'' _ (hm.pow_const 2), ← lintegral_const_mul'' _ (hm.pow_const 8),
      ← lintegral_add_left' ((hm.pow_const 2).const_mul _)]
    exact lintegral_mono fun x => pow_four_le_amgm _ ht
  calc ∫⁻ ω, (SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (Kc : ℤ)) 4
        (F ω)) ^ 4 ∂μ
      ≤ ∫⁻ ω, (ENNReal.ofReal (2 * t / 3) * (SuperdiffusionCLT.Section2.Norms.cubeLpENorm
        (originCube d (Kc : ℤ)) 2 (F ω)) ^ 2 +
      ENNReal.ofReal (1 / (3 * t ^ 2)) * (SuperdiffusionCLT.Section2.Norms.cubeLpENorm
        (originCube d (Kc : ℤ)) 8 (F ω)) ^ 8) ∂μ := lintegral_mono hpt
    _ = _ := by
        rw [lintegral_add_left ((hX.pow_const 2).const_mul _),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end

end SuperdiffusionCLT.Section5
