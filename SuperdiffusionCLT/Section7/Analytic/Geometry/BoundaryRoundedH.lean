/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Geometry.BoundaryRoundedG

/-!
# Charts of the model domain in directions orthogonal to the axis

At a frontier point `p` with `(⟨e,p⟩ + h)² / h² ≤ 1/8` the projection `P p` is nonzero and the model
domain is, near `p`, the region below the graph, in the direction `e' = P p / |P p|`, of
`z ↦ √(a² (1 - φ(v z)) - |P z|²)`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization

variable {d : ℕ}

theorem g1b_normSq_sub_smul (y f : Vec d) (c : ℝ) :
    vecNormSq (y - c • f) = vecNormSq y - 2 * c * vecDot f y + c ^ 2 * vecNormSq f := by
  simp only [vecNormSq, vecDot, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem g1b_vecDot_sub_smul_left (y f z : Vec d) (c : ℝ) :
    vecDot (y - c • f) z = vecDot y z - c * vecDot f z := by
  simp only [vecDot, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem g1b_vecDot_sub_smul_right (e y f : Vec d) (c : ℝ) :
    vecDot e (y - c • f) = vecDot e y - c * vecDot e f := by
  simp only [vecDot, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem g1b_vecDot_comm (x y : Vec d) : vecDot x y = vecDot y x := by
  simp only [vecDot]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `|P y|²` for a unit `e`. -/
theorem g1b_normSq_proj {e : Vec d} (he : vecNormSq e = 1) (y : Vec d) :
    vecNormSq (y - vecDot e y • e) = vecNormSq y - vecDot e y ^ 2 := by
  rw [g1b_normSq_sub_smul, he]
  ring

/-- Splitting of `|P y|²` along a unit vector `e'` orthogonal to `e`. -/
theorem g1b_normSq_proj_split {e e' : Vec d} (he : vecNormSq e = 1) (he' : vecNormSq e' = 1)
    (hee : vecDot e e' = 0) (y : Vec d) :
    vecNormSq (y - vecDot e y • e) =
      vecDot e' y ^ 2 + vecNormSq ((y - vecDot e' y • e') - vecDot e (y - vecDot e' y • e') • e) := by
  have h1 : vecDot e (y - vecDot e' y • e') = vecDot e y := by
    rw [g1b_vecDot_sub_smul_right, hee, mul_zero, sub_zero]
  have h2 := g1b_normSq_proj he (y - vecDot e' y • e')
  rw [h1] at h2
  have h4 := g1b_normSq_sub_smul y e' (vecDot e' y)
  rw [h1, g1b_normSq_proj he, h2, h4, he']
  ring

end SuperdiffusionCLT.Section7
