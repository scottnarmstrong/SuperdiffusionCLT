/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.BoundaryDecayChartH

@[expose] public section

open Homogenization MeasureTheory Filter Topology Matrix
open scoped ENNReal NNReal

/-!
# Normalized measures on subsets of balls

The `ℓ^d`-normalized restriction of the volume to a subset of a ball is a finite measure of total
mass at most `(2ρ/ℓ)^d`, so bounded measurable functions are square integrable for it.
-/

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem r3e_volume_le_ball_enn {S : Set (Vec d)} {x₀ : Vec d} {ρ : ℝ} (hρ : 0 < ρ)
    (hS : S ⊆ Metric.ball x₀ ρ) :
    volume S ≤ ENNReal.ofReal ((2 * ρ) ^ d) := by
  have := measure_mono (μ := (volume : Measure (Vec d))) hS
  rwa [Real.volume_pi_ball x₀ hρ, Fintype.card_fin] at this

theorem r3e_volume_le_ball {S : Set (Vec d)} {x₀ : Vec d} {ρ : ℝ} (hρ : 0 < ρ)
    (hS : S ⊆ Metric.ball x₀ ρ) :
    (volume S).toReal ≤ (2 * ρ) ^ d := by
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (r3e_volume_le_ball_enn hρ hS)
  rwa [ENNReal.toReal_ofReal (by positivity)] at this

theorem r3e_nmeas_finite {S : Set (Vec d)} {x₀ : Vec d} {ρ : ℝ} (hρ : 0 < ρ)
    (hS : S ⊆ Metric.ball x₀ ρ) (ℓ : ℝ) : IsFiniteMeasure (p12_nmeas ℓ S) := by
  refine ⟨?_⟩
  unfold p12_nmeas
  rw [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (lt_of_le_of_lt (r3e_volume_le_ball_enn hρ hS) ENNReal.ofReal_lt_top)

theorem r3e_nmeas_univ {S : Set (Vec d)} {x₀ : Vec d} {ρ : ℝ} (hρ : 0 < ρ)
    (hS : S ⊆ Metric.ball x₀ ρ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (p12_nmeas ℓ S Set.univ).toReal ≤ (ℓ ^ d)⁻¹ * (2 * ρ) ^ d := by
  unfold p12_nmeas
  rw [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  exact mul_le_mul_of_nonneg_left (r3e_volume_le_ball hρ hS) (by positivity)

theorem r3e_memLp_bound {S : Set (Vec d)} {x₀ : Vec d} {ρ : ℝ} (hρ : 0 < ρ)
    (hS : S ⊆ Metric.ball x₀ ρ) (ℓ : ℝ) {F : Vec d → ℝ}
    (hF : AEStronglyMeasurable F (p12_nmeas ℓ S)) {C : ℝ} (hC : ∀ y ∈ S, ‖F y‖ ≤ C)
    (hSm : MeasurableSet S) (q : ℝ≥0∞) : MemLp F q (p12_nmeas ℓ S) := by
  have := r3e_nmeas_finite hρ hS ℓ
  refine MemLp.of_bound hF C ?_
  unfold p12_nmeas
  refine Measure.ae_smul_measure ?_ _
  exact (ae_restrict_iff' hSm).2 (Filter.Eventually.of_forall hC)

end SuperdiffusionCLT.Section7
