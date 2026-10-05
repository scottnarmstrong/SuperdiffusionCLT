/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Geometry.RoundedCube
public import SuperdiffusionCLT.Section7.Analytic.Geometry.AtlasTransform

/-!
# Rounded cubes are smooth domains

Explicit graph charts of the superellipsoid `{∑ xᵢ^(2N) < 1}`: near a boundary point `x`, with
`j` the coordinate of largest modulus and `s` its sign, the set is
`{s yⱼ < (1 - ∑_{i≠j} yᵢ^(2N))^(1/(2N))}`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization

variable {d : ℕ}

/-- The unit vector `s eⱼ`. -/
def g1_e (j : Fin d) (s : ℝ) : Vec d := s • Pi.single j (1 : ℝ)

theorem g1_vecDot_e (j : Fin d) (s : ℝ) (y : Vec d) : vecDot (g1_e j s) y = s * y j := by
  unfold vecDot g1_e
  simp [Pi.single_apply]

theorem g1_vecNormSq_e (j : Fin d) {s : ℝ} (hs : s * s = 1) : vecNormSq (g1_e j s) = 1 := by
  unfold vecNormSq
  rw [g1_vecDot_e]
  simp [g1_e, hs]

theorem g1_proj_e (j : Fin d) {s : ℝ} (hs : s * s = 1) (y : Vec d) (i : Fin d) :
    (y - vecDot (g1_e j s) y • g1_e j s) i = if i = j then 0 else y i := by
  rw [g1_vecDot_e]
  by_cases h : i = j
  · subst h
    have : (y - (s * y i) • g1_e i s) i = y i - s * y i * s := by simp [g1_e]
    rw [this]
    simp only [↓reduceIte]
    linear_combination (-(y i)) * hs
  · simp [g1_e, h]

theorem g1_P_split {N : ℕ} (hN : 1 ≤ N) (j : Fin d) {s : ℝ} (hs : s * s = 1) (y : Vec d) :
    g1_P N y = y j ^ (2 * N) + g1_P N (y - vecDot (g1_e j s) y • g1_e j s) := by
  have h0 : (0 : ℝ) ^ (2 * N) = 0 := zero_pow (by omega)
  have hp : g1_P N (y - vecDot (g1_e j s) y • g1_e j s) =
      ∑ i, (if i = j then 0 else y i ^ (2 * N)) := by
    unfold g1_P
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [g1_proj_e j hs]
    split_ifs
    · exact h0
    · rfl
  rw [hp]
  unfold g1_P
  have : ∀ i : Fin d, y i ^ (2 * N) =
      (if i = j then y i ^ (2 * N) else 0) + (if i = j then 0 else y i ^ (2 * N)) := fun i => by
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_add_distrib, Finset.sum_ite_eq' ]
  simp

end SuperdiffusionCLT.Section7
