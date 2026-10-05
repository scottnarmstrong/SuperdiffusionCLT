/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Geometry.RoundedCubeC

/-!
# The family of rounded cubes `V_{z,k}`

`g1_V d N k z` is the superellipsoid `{∑ xᵢ^(2N) < 1}` dilated by `3^k / 2` and translated to
`z`.  It lies between the concentric cubes of half-widths `3^(k-1)/2` and `3^k/2`, its rescaling
`3^(-k) (V - z)` is the fixed model `(1/2) • {∑ xᵢ^(2N) < 1}`, and the uniform `C^{1,1}` data
of the model are independent of `k` and `z`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization Pointwise

variable {d : ℕ}

/-- The rounded cube of scale `3^k` centred at `z`. -/
def g1_V (d N k : ℕ) (z : Vec d) : Set (Vec d) :=
  (fun y => ((3 : ℝ) ^ k / 2) • y + z) '' g1_superE d N

theorem g1_V_isOpen {N : ℕ} (k : ℕ) (z : Vec d) : IsOpen (g1_V d N k z) := by
  have hl : ((3 : ℝ) ^ k / 2) ≠ 0 := by positivity
  have : g1_V d N k z = affineHomeo hl z '' g1_superE d N := rfl
  rw [this]
  exact (affineHomeo hl z).isOpenMap _ (g1_isOpen_superE N)

theorem g1_V_subset_ball {N : ℕ} (hN : 1 ≤ N) (k : ℕ) (z : Vec d) :
    g1_V d N k z ⊆ Metric.ball z ((3 : ℝ) ^ k / 2) := by
  rintro _ ⟨u, hu, rfl⟩
  have hl : (0 : ℝ) < (3 : ℝ) ^ k / 2 := by positivity
  have h1 := g1_superE_subset_ball hN hu
  rw [mem_ball_zero_iff] at h1
  rw [mem_ball_iff_norm, add_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_pos hl]
  exact mul_lt_of_lt_one_right hl h1

theorem g1_ball_subset_V [NeZero d] {N : ℕ} (hN : 1 ≤ N) (hd : d ≤ 9 ^ N) (k : ℕ) (z : Vec d) :
    Metric.ball z ((3 : ℝ) ^ k / 2 / 3) ⊆ g1_V d N k z := by
  intro w hw
  have hl : (0 : ℝ) < (3 : ℝ) ^ k / 2 := by positivity
  refine ⟨((3 : ℝ) ^ k / 2)⁻¹ • (w - z), g1_ball_subset_superE hN hd ?_, ?_⟩
  · rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hl)]
    rw [mem_ball_iff_norm] at hw
    rw [inv_mul_lt_iff₀ hl]
    linarith only [hw]
  · show ((3 : ℝ) ^ k / 2) • (((3 : ℝ) ^ k / 2)⁻¹ • (w - z)) + z = w
    rw [smul_smul, mul_inv_cancel₀ hl.ne', one_smul]
    abel

/-- The rescaling `3^(-k) (V - z)` is the fixed model `(1/2) • E_N`. -/
theorem g1_V_rescale (N k : ℕ) (z : Vec d) :
    (fun y => ((3 : ℝ) ^ k)⁻¹ • (y - z)) '' g1_V d N k z = (1 / 2 : ℝ) • g1_superE d N := by
  have h3 : ((3 : ℝ) ^ k) ≠ 0 := by positivity
  unfold g1_V
  rw [Set.image_image, ← Set.image_smul]
  refine Set.image_congr fun u _ => ?_
  simp only [add_sub_cancel_right, smul_smul]
  congr 1
  field_simp

/-- The uniform family: constants independent of `k` and `z`, and the inclusions of the cubes
of half-widths `3^(k-1)/2` and `3^k/2`. -/
theorem g1_uniform_family [NeZero d] :
    ∃ (N : ℕ) (r M₁ M₂ D : ℝ), 1 ≤ N ∧ 0 < r ∧
      ∀ (k : ℕ) (z : Vec d),
        IsUniformC11Domain ((fun y => ((3 : ℝ) ^ k)⁻¹ • (y - z)) '' g1_V d N k z)
          (1 / 2 * r) M₁ (M₂ / (1 / 2)) (1 / 2 * D) ∧
        IsUniformC11Domain (g1_V d N k z) ((3 : ℝ) ^ k / 2 * r) M₁ (M₂ / ((3 : ℝ) ^ k / 2))
          ((3 : ℝ) ^ k / 2 * D) ∧
        Metric.ball z ((3 : ℝ) ^ k / 2 / 3) ⊆ g1_V d N k z ∧
        g1_V d N k z ⊆ Metric.ball z ((3 : ℝ) ^ k / 2) := by
  have hdpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hN : 1 ≤ d := hdpos
  have hd : d ≤ 9 ^ d := (Nat.lt_pow_self (n := d) (by norm_num : 1 < 9)).le
  obtain ⟨r, M₁, M₂, D, hU⟩ := exists_isUniformC11Domain_of_isSmoothBoundedDomain
    (g1_isSmoothBoundedDomain_superE (d := d) (N := d) hN)
  refine ⟨d, r, M₁, M₂, D, hN, hU.2.1, fun k z => ⟨?_, ?_, g1_ball_subset_V hN hd k z,
    g1_V_subset_ball hN k z⟩⟩
  · rw [g1_V_rescale]
    exact hU.smul (by norm_num)
  · exact hU.affineImage (by positivity) z

end SuperdiffusionCLT.Section7
