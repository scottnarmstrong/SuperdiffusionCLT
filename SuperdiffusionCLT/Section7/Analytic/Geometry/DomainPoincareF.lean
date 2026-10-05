/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Geometry.DomainPoincareE
public import SuperdiffusionCLT.Section7.Analytic.Geometry.RoundedCubeD

/-!
# Poincare inequalities: the rounded cubes

The rounded cube `V_{z,k}` is convex (a sublevel set of a sum of even powers, dilated and
translated) and contains the cube of half-width `3^k / 6` about `z`, so it is a star-ball domain with
`D / s = 6`, with a constant independent of `k` and `z`. This file proves the convexity input,
`a10_convex_superE`, and the star-ball criterion `a10_isStarBallDomain_of_convex`.
-/

@[expose] public section

open MeasureTheory Homogenization Set

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem a10_isStarBallDomain_of_convex {W : Set (Vec d)} (hWo : IsOpen W) (hconv : Convex ℝ W)
    {x0 : Vec d} {s D : ℝ} (hs : 0 < s) (hB : Metric.ball x0 s ⊆ W)
    (hdiam : ∀ x ∈ W, ∀ y ∈ W, ‖x - y‖ ≤ D) : IsStarBallDomain W x0 s D := by
  refine ⟨hWo, hs, hB, fun x hx b hb t ht => ?_, hdiam⟩
  exact hconv hx (hB hb) (by linarith only [ht.2]) ht.1 (by ring)

theorem a10_convex_superE (N : ℕ) : Convex ℝ (g1_superE d N) := by
  intro y hy z hz a b ha hb hab
  have hy' : g1_P N y < 1 := hy
  have hz' : g1_P N z < 1 := hz
  show g1_P N (a • y + b • z) < 1
  have hcoord : ∀ i, (a • y + b • z) i ^ (2 * N) ≤ a * y i ^ (2 * N) + b * z i ^ (2 * N) := by
    intro i
    have := (Even.convexOn_pow (𝕜 := ℝ) (even_two_mul N)).2 (Set.mem_univ (y i))
      (Set.mem_univ (z i)) ha hb hab
    simpa using this
  have hsum : g1_P N (a • y + b • z) ≤ a * g1_P N y + b * g1_P N z := by
    unfold g1_P
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => hcoord i
  have hpos : 0 < a * (1 - g1_P N y) + b * (1 - g1_P N z) := by
    rcases ha.lt_or_eq with ha' | ha'
    · have : 0 < a * (1 - g1_P N y) := mul_pos ha' (by linarith only [hy'])
      have : 0 ≤ b * (1 - g1_P N z) := mul_nonneg hb (by linarith only [hz'])
      linarith only [‹0 < a * (1 - g1_P N y)›, this]
    · have hb' : 0 < b := by linarith only [hab, ha']
      have : 0 < b * (1 - g1_P N z) := mul_pos hb' (by linarith only [hz'])
      have : 0 ≤ a * (1 - g1_P N y) := mul_nonneg ha (by linarith only [hy'])
      linarith only [‹0 < b * (1 - g1_P N z)›, this]
  nlinarith only [hsum, hpos, hab]

end SuperdiffusionCLT.Section7
