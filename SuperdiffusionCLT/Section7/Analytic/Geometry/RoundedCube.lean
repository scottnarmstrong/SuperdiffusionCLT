/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Geometry.Atlas

/-!
# Rounded cubes: the model superellipsoid `{x : ∑ xᵢ^(2N) < 1}`

* `Section7.g1_superE d N`: the open superellipsoid of exponent `2N`.
* basic properties: open, star-shaped about `0`, between two concentric cubes, frontier inside
  the level set `{∑ xᵢ^(2N) = 1}`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization

variable {d : ℕ}

/-- The defining function `∑ xᵢ^(2N)`. -/
noncomputable def g1_P (N : ℕ) (y : Vec d) : ℝ := ∑ i, y i ^ (2 * N)

/-- The open superellipsoid of exponent `2N`. -/
def g1_superE (d N : ℕ) : Set (Vec d) := {y | g1_P N y < 1}

theorem g1_continuous_P (N : ℕ) : Continuous (g1_P (d := d) N) := by
  unfold g1_P
  fun_prop

theorem g1_contDiff_P (N : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (g1_P (d := d) N) := by
  unfold g1_P
  fun_prop

theorem g1_P_nonneg (N : ℕ) (y : Vec d) : 0 ≤ g1_P N y :=
  Finset.sum_nonneg fun _ _ => (even_two_mul N).pow_nonneg _

theorem g1_term_le_P (N : ℕ) (y : Vec d) (i : Fin d) : y i ^ (2 * N) ≤ g1_P N y :=
  Finset.single_le_sum (f := fun i => y i ^ (2 * N)) (fun _ _ => (even_two_mul N).pow_nonneg _)
    (Finset.mem_univ i)

theorem g1_isOpen_superE (N : ℕ) : IsOpen (g1_superE d N) :=
  isOpen_lt (g1_continuous_P N) continuous_const

theorem g1_P_smul (N : ℕ) (t : ℝ) (y : Vec d) : g1_P N (t • y) = t ^ (2 * N) * g1_P N y := by
  unfold g1_P
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_pow]

theorem g1_zero_mem {N : ℕ} (hN : 1 ≤ N) : (0 : Vec d) ∈ g1_superE d N := by
  show g1_P N (0 : Vec d) < 1
  have : g1_P N (0 : Vec d) = 0 := by
    simp [g1_P, zero_pow (show 2 * N ≠ 0 from by omega)]
  rw [this]
  exact one_pos

theorem g1_starConvex (N : ℕ) : StarConvex ℝ 0 (g1_superE d N) := by
  intro y hy a b ha hb hab
  have hy' : g1_P N y < 1 := hy
  have hb1 : b ≤ 1 := by linarith only [ha, hab]
  have hp : b ^ (2 * N) ≤ 1 := pow_le_one₀ hb hb1
  show g1_P N (a • (0 : Vec d) + b • y) < 1
  rw [smul_zero, zero_add, g1_P_smul]
  calc b ^ (2 * N) * g1_P N y ≤ 1 * g1_P N y :=
        mul_le_mul_of_nonneg_right hp (g1_P_nonneg N y)
    _ < 1 := by linarith only [hy']

theorem g1_isConnected_superE {N : ℕ} (hN : 1 ≤ N) : IsConnected (g1_superE d N) :=
  ((g1_starConvex N).isPathConnected (g1_zero_mem hN)).isConnected

theorem g1_abs_lt_one {N : ℕ} (hN : 1 ≤ N) {y : Vec d} (hy : y ∈ g1_superE d N) (i : Fin d) :
    |y i| < 1 := by
  have h1 : y i ^ (2 * N) < 1 := lt_of_le_of_lt (g1_term_le_P N y i) hy
  rw [← Even.pow_abs (even_two_mul N)] at h1
  exact (pow_lt_one_iff_of_nonneg (abs_nonneg _) (by omega)).1 h1

/-- The superellipsoid lies in the open unit cube. -/
theorem g1_superE_subset_ball {N : ℕ} (hN : 1 ≤ N) :
    g1_superE d N ⊆ Metric.ball (0 : Vec d) 1 := by
  intro y hy
  rw [mem_ball_zero_iff, pi_norm_lt_iff one_pos]
  intro i
  rw [Real.norm_eq_abs]
  exact g1_abs_lt_one hN hy i

/-- The superellipsoid is bounded in the form used by `IsBoundedDomain`. -/
theorem g1_isBoundedDomain {N : ℕ} (hN : 1 ≤ N) : IsBoundedDomain (g1_superE d N) :=
  ⟨1, one_pos, fun _ hy i => (g1_abs_lt_one hN hy i).le⟩

/-- The cube of half-width `1/3` lies in the superellipsoid, when `d ≤ 9^N`. -/
theorem g1_ball_subset_superE [NeZero d] {N : ℕ} (hN : 1 ≤ N) (hd : d ≤ 9 ^ N) :
    Metric.ball (0 : Vec d) (1 / 3) ⊆ g1_superE d N := by
  intro y hy
  rw [mem_ball_zero_iff, pi_norm_lt_iff (by norm_num)] at hy
  have hlt : ∀ i, y i ^ (2 * N) < (1 / 3 : ℝ) ^ (2 * N) := fun i => by
    rw [← Even.pow_abs (even_two_mul N)]
    have := hy i
    rw [Real.norm_eq_abs] at this
    exact pow_lt_pow_left₀ this (abs_nonneg _) (by omega)
  have hsum : g1_P N y < ∑ _i : Fin d, (1 / 3 : ℝ) ^ (2 * N) :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => hlt i
  have h9 : ((1 / 3 : ℝ)) ^ (2 * N) = 1 / 9 ^ N := by
    rw [pow_mul, one_div, inv_pow, one_div]
    norm_num
    rw [one_div, inv_pow]
  have hd' : (d : ℝ) ≤ 9 ^ N := by exact_mod_cast hd
  have h9pos : (0 : ℝ) < 9 ^ N := by positivity
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, h9, mul_one_div] at hsum
  have : (d : ℝ) / 9 ^ N ≤ 1 := (div_le_one h9pos).2 hd'
  exact lt_of_lt_of_le hsum this

/-- The frontier of the superellipsoid lies in the level set `{P = 1}`. -/
theorem g1_frontier_P (N : ℕ) {x : Vec d} (hx : x ∈ frontier (g1_superE d N)) :
    g1_P N x = 1 := by
  have hcl : closure (g1_superE d N) ⊆ {y | g1_P N y ≤ 1} :=
    closure_minimal (fun y hy => (le_of_lt (show g1_P N y < 1 from hy)))
      (isClosed_le (g1_continuous_P N) continuous_const)
  rw [(g1_isOpen_superE N).frontier_eq] at hx
  have h1 : g1_P N x ≤ 1 := hcl hx.1
  have h2 : ¬ g1_P N x < 1 := hx.2
  exact le_antisymm h1 (not_lt.1 h2)

end SuperdiffusionCLT.Section7
