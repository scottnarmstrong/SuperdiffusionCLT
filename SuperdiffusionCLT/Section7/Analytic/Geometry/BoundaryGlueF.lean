/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Geometry.BoundaryGlueE

/-!
# The numerics of the glued domain

`g1c_numerics`: the numerical inequalities for the gluing constants `ζ = 1 / (4 (d + 1))` and
`c₁ = 1 / (16 (1 + d)² (1 + M))`, namely `d ζ² ≤ 1/16`, `(1 + d) c₁ ≤ ζ / 4`,
`(1 + d) (1 + M) c₁ ≤ 1/16` and `c₁ ≤ 1`. They are used in the construction of the glued domain
`W` of `a10_glue_normalized` (`DomainPoincareJ.lean`).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization

variable {d : ℕ}

theorem g1c_numerics {M : ℝ} (hM : 0 ≤ M) :
    let ζ : ℝ := 1 / (4 * ((d : ℝ) + 1))
    let c₁ : ℝ := 1 / (16 * (1 + (d : ℝ)) ^ 2 * (1 + M))
    (d : ℝ) * ζ ^ 2 ≤ 1 ^ 2 / 16 ∧ (1 + (d : ℝ)) * c₁ ≤ ζ / 4 ∧
      (1 + (d : ℝ)) * (1 + M) * c₁ ≤ 1 / 16 ∧ c₁ ≤ 1 := by
  intro ζ c₁
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hd1 : (0 : ℝ) < 1 + d := by positivity
  have hM1 : (0 : ℝ) < 1 + M := by linarith only [hM]
  have hc : (1 + (d : ℝ)) * (1 + M) * c₁ = 1 / (16 * (1 + d)) := by
    simp only [c₁]
    field_simp
  have hc' : (1 + (d : ℝ)) * c₁ = ζ / 4 / (1 + M) := by
    simp only [c₁, ζ]
    field_simp
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [ζ]
    rw [div_pow, one_pow, mul_pow, ← mul_div_assoc, mul_one,
      div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith only [hd0]
  · rw [hc']
    refine div_le_self (by positivity) (by linarith only [hM])
  · rw [hc, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith only [hd0]
  · simp only [c₁]
    rw [div_le_one (by positivity)]
    have h1 : (1 : ℝ) ≤ (1 + d) ^ 2 := by nlinarith only [hd0]
    have h2 : (1 : ℝ) ≤ 1 + M := by linarith only [hM]
    nlinarith only [h1, h2]

end SuperdiffusionCLT.Section7
