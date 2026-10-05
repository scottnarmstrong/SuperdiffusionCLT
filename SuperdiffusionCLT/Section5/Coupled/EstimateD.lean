/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Coupled.EstimateC
public import SuperdiffusionCLT.Section5.Coupled.GradW
public import SuperdiffusionCLT.Section5.Neumann.NeumannInputD
public import SuperdiffusionCLT.Section5.Thresholds.HomogBelowAtScales
public import Mathlib.Algebra.Order.Star.Real

/-!
# `lem.coupled.input`

The lemma in the shape consumed by `cor.lower.ratio`: the `limsup` over the large cubes of the
box average of `E |Ahom^{1/2} G_{-hbar_z} Ahom^{-1/2} (e_{D,z}, e)|²` is at most
`1 - c⋆ log 3 h σ⁻² + K σ⁻² + C σ⁻⁴ h²`, `σ = shom_{m-h}`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open MeasureTheory Homogenization Filter Topology
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)
open SuperdiffusionCLT.Section3.ResponseFields (vecCubeLpENorm)
open scoped ENNReal

variable {d : ℕ}

/-- The absorption of the remainder terms into `C σ⁻⁴ h²`. -/
theorem coupled4_algebra (c μ h Cg Cr Ce : ℝ) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1)
    (hh : 1 ≤ h) (hCg : 1 ≤ Cg) (hCr : 1 ≤ Cr) (hμc : μ ≤ Ce ^ 2 * c ^ 2) :
    c ^ 2 * (Cg * c * h) ^ 2 + (c ^ 2 * (Cr * c * μ) ^ 2 + 2 * c ^ 2 * (Cg * c * h) * (Cr * c * μ) +
        2 * c * (Cr * c * μ)) ≤ ((Cg + Cr) ^ 2 + 2 * Cr * Ce ^ 2) * c ^ 4 * h ^ 2 := by
  have hh2 : 1 ≤ h ^ 2 := one_le_pow₀ hh
  have hμh : μ ≤ h := by linarith only [hμ1, hh]
  have hμ2 : μ ^ 2 ≤ h ^ 2 := pow_le_pow_left₀ hμ0.le hμh 2
  have hhμ : h * μ ≤ h ^ 2 := by nlinarith only [hμh, hh]
  have hc4 : 0 ≤ c ^ 4 := by positivity
  have hCr0 : 0 ≤ Cr := by linarith only [hCr]
  have hCg0 : 0 ≤ Cg := by linarith only [hCg]
  have h2 : Cr ^ 2 * c ^ 4 * μ ^ 2 ≤ Cr ^ 2 * c ^ 4 * h ^ 2 :=
    mul_le_mul_of_nonneg_left hμ2 (by positivity)
  have h3 : 2 * Cg * Cr * c ^ 4 * (h * μ) ≤ 2 * Cg * Cr * c ^ 4 * h ^ 2 :=
    mul_le_mul_of_nonneg_left hhμ (by positivity)
  have h4 : 2 * Cr * c ^ 2 * μ ≤ 2 * Cr * Ce ^ 2 * c ^ 4 * h ^ 2 := by
    have h5 : 2 * Cr * c ^ 2 * μ ≤ 2 * Cr * c ^ 2 * (Ce ^ 2 * c ^ 2) :=
      mul_le_mul_of_nonneg_left hμc (by positivity)
    have h6 : 2 * Cr * Ce ^ 2 * c ^ 4 * 1 ≤ 2 * Cr * Ce ^ 2 * c ^ 4 * h ^ 2 :=
      mul_le_mul_of_nonneg_left hh2 (by positivity)
    linarith only [h5, h6, show 2 * Cr * c ^ 2 * (Ce ^ 2 * c ^ 2) = 2 * Cr * Ce ^ 2 * c ^ 4 * 1 by ring]
  have e1 : c ^ 2 * (Cg * c * h) ^ 2 + (c ^ 2 * (Cr * c * μ) ^ 2 +
      2 * c ^ 2 * (Cg * c * h) * (Cr * c * μ) + 2 * c * (Cr * c * μ)) =
      Cg ^ 2 * c ^ 4 * h ^ 2 + Cr ^ 2 * c ^ 4 * μ ^ 2 + 2 * Cg * Cr * c ^ 4 * (h * μ) +
        2 * Cr * c ^ 2 * μ := by ring
  rw [e1]
  have e2 : ((Cg + Cr) ^ 2 + 2 * Cr * Ce ^ 2) * c ^ 4 * h ^ 2 =
      Cg ^ 2 * c ^ 4 * h ^ 2 + Cr ^ 2 * c ^ 4 * h ^ 2 + 2 * Cg * Cr * c ^ 4 * h ^ 2 +
        2 * Cr * Ce ^ 2 * c ^ 4 * h ^ 2 := by ring
  rw [e2]
  linarith only [h2, h3, h4]

end SuperdiffusionCLT.Section5
