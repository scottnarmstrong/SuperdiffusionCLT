/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Root.GeneratorsL
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Reduction to a source supported in the unit ball
-/

@[expose] public section

open Homogenization MeasureTheory Filter Topology SuperdiffusionCLT.Section6
open scoped ENNReal Pointwise Matrix.Norms.Elementwise

namespace SuperdiffusionCLT.Section8

variable {d : ℕ}

/-- A smooth compactly supported function is the dilate of one supported in the unit ball. -/
theorem gen_prep_u [NeZero d] {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hcs : HasCompactSupport u) :
    ∃ ρ : ℝ, 1 ≤ ρ ∧ ∃ u0 : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) u0 ∧
      tsupport u0 ⊆ euclidBall (d := d) 1 ∧ (fun x => u0 (ρ⁻¹ • x)) = u := by
  obtain ⟨R, hR⟩ := (hcs.isCompact.isBounded).subset_ball (0 : Vec d)
  set R' : ℝ := max R 1 with hR'
  have hR'1 : 1 ≤ R' := le_max_right _ _
  have hd1 : (1 : ℝ) ≤ Real.sqrt d := by
    rw [Real.one_le_sqrt]
    exact_mod_cast NeZero.one_le
  set ρ : ℝ := Real.sqrt d * R' with hρdef
  have hρ : 1 ≤ ρ := one_le_mul_of_one_le_of_one_le hd1 hR'1
  have hρ0 : 0 < ρ := by linarith only [hρ]
  have hsub : tsupport u ⊆ euclidBall (d := d) ρ := by
    intro x hx
    have h1 : x ∈ Metric.ball (0 : Vec d) R' := Metric.ball_subset_ball (le_max_left _ _) (hR hx)
    exact ball_subset_euclidBall h1
  refine ⟨ρ, hρ, fun y => u (ρ • y), hu.comp (contDiff_const_smul _), ?_, ?_⟩
  · intro x hx
    have hcl : IsClosed ((fun y : Vec d => ρ • y) ⁻¹' tsupport u) :=
      (isClosed_tsupport u).preimage (continuous_const_smul ρ)
    have hs : Function.support (fun y => u (ρ • y)) ⊆
        (fun y : Vec d => ρ • y) ⁻¹' tsupport u := fun y hy => subset_tsupport u hy
    have hx' : ρ • x ∈ tsupport u := closure_minimal hs hcl hx
    have h2 : vecNormSq (ρ • x) < ρ ^ 2 := hsub hx'
    rw [vecNormSq_smul] at h2
    show vecNormSq x < 1 ^ 2
    have : ρ ^ 2 * vecNormSq x < ρ ^ 2 * 1 := by linarith only [h2]
    have := lt_of_mul_lt_mul_left this (sq_nonneg ρ)
    linarith only [this]
  · funext x
    simp only [smul_smul, mul_inv_cancel₀ hρ0.ne', one_smul]

end SuperdiffusionCLT.Section8
