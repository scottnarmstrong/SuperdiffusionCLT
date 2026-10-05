/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.CaccioppoliBdryD
public import SuperdiffusionCLT.Section7.Lipschitz.InnerBall
public import SuperdiffusionCLT.Section7.Lipschitz.CarriersS
public import SuperdiffusionCLT.Section7.Analytic.Geometry.AtlasTransform

/-!
# Geometry of the translated dilate of a smooth domain at the scale of a cube

For a smooth bounded domain `U` and a real dilation `t ≥ 3^j`, the set `W = (t U) - y` is uniformly
`C^{1,1}` with chart radius `t r₀ ≥ 3^j r₀`.  The boundary layer of `W` of thickness `τ` has measure
`C τ (3^j)^{d-1}` inside any cube of side `3^j` (`ca2_layer_cube2`), and, if the centre of the cube
lies in `W`, the intersection of `W` with the cube of side `3^{j-1}` has measure at least a fixed
multiple of `(3^j)^d` (`ca2_density`).
-/

@[expose] public section

open scoped ENNReal NNReal Pointwise
open MeasureTheory Filter Topology Homogenization

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem ca2_translateSet_eq (z : Vec d) (S : Set (Vec d)) :
    translateSet z S = (fun y => y + z) '' S := by
  ext x
  simp only [translateSet, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩

theorem ca2_W_uniform {U : Set (Vec d)} {r M₁ M₂ D : ℝ} (h : IsUniformC11Domain U r M₁ M₂ D)
    {t : ℝ} (ht : 0 < t) (y : Vec d) :
    IsUniformC11Domain (translateSet (-y) (t • U)) (t * r) M₁ (M₂ / t) (t * D) := by
  rw [ca2_translateSet_eq]
  exact (h.smul ht).translate (-y)

/-- A uniformly `C^{1,1}` domain with a point has nonempty frontier. -/
theorem ca2_frontier_nonempty [NeZero d] {U : Set (Vec d)} {r M₁ M₂ D : ℝ}
    (h : IsUniformC11Domain U r M₁ M₂ D) (hne : U.Nonempty) : (frontier U).Nonempty := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne d)
  exact frontier_nonempty_of_uniform h.2.2.1 (Set.nonempty_iff_ne_empty.1 hne)

/-- **The local layer measure at the scale of a cube** (chart radius at least `ρ 3^m`). -/
theorem ca2_layer_cube2 {n : ℕ} {U : Set (Vec (n + 1))} {r M₁ M₂ D : ℝ}
    (h : IsUniformC11Domain U r M₁ M₂ D) (hF : (frontier U).Nonempty) (z : Vec (n + 1)) (m : ℤ)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hρr : ρ * (3 : ℝ) ^ m ≤ r) {τ : ℝ} (hτ : 0 < τ)
    (hτm : τ ≤ ρ * (3 : ℝ) ^ m / 2) :
    volume (boundaryLayer U τ ∩ shiftCube z m) ≤
      ENNReal.ofReal ((8 / ρ + 2) ^ (n + 1) * ca2_pieceConst n 1 M₁ * ρ ^ n * τ * ((3 : ℝ) ^ m) ^ n) := by
  have hL : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  have hr' : 0 < ρ * (3 : ℝ) ^ m := by positivity
  have h' := ca2_uniform_mono h hr' hρr
  have key := ca2_volume_layer_local_le h' hF z (R := (3 : ℝ) ^ m / 2) (by positivity) hτ hτm
  rw [lip_witness_bdry_cube_ball]
  refine key.trans (ENNReal.ofReal_le_ofReal ?_)
  have hpc : ca2_pieceConst n (ρ * (3 : ℝ) ^ m) M₁ = (ρ * (3 : ℝ) ^ m) ^ n * ca2_pieceConst n 1 M₁ :=
    ca2_pieceConst_mul n _ _
  rw [hpc]
  have hP : 0 ≤ ca2_pieceConst n 1 M₁ := by
    have := layerSlope_pos n M₁
    unfold ca2_pieceConst
    positivity
  have h1 : 8 * ((3 : ℝ) ^ m / 2 + τ) / (ρ * (3 : ℝ) ^ m) + 2 ≤ 8 / ρ + 2 := by
    have : 8 * ((3 : ℝ) ^ m / 2 + τ) / (ρ * (3 : ℝ) ^ m) ≤ 8 / ρ := by
      rw [div_le_div_iff₀ hr' hρ]
      have h3 : ρ * (3 : ℝ) ^ m ≤ (3 : ℝ) ^ m := mul_le_of_le_one_left hL.le hρ1
      have h4 : τ ≤ (3 : ℝ) ^ m / 2 := by linarith only [hτm, h3]
      have h5 := mul_le_mul_of_nonneg_left h4 hρ.le
      nlinarith only [h5]
    linarith only [this]
  have h2 : (8 * ((3 : ℝ) ^ m / 2 + τ) / (ρ * (3 : ℝ) ^ m) + 2) ^ (n + 1) ≤ (8 / ρ + 2) ^ (n + 1) :=
    pow_le_pow_left₀ (by positivity) h1 _
  calc (8 * ((3 : ℝ) ^ m / 2 + τ) / (ρ * (3 : ℝ) ^ m) + 2) ^ (n + 1) *
        ((ρ * (3 : ℝ) ^ m) ^ n * ca2_pieceConst n 1 M₁ * τ)
      ≤ (8 / ρ + 2) ^ (n + 1) * ((ρ * (3 : ℝ) ^ m) ^ n * ca2_pieceConst n 1 M₁ * τ) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = _ := by rw [mul_pow]; ring

/-- **Density**: if the centre `0` of the cube lies in `W = t U - y` and `3^j ≤ t`, then `W` fills a
fixed proportion of the cube of side `3^{j-1}`. -/
theorem ca2_density (d : ℕ) [NeZero d] (M₁ : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ {U : Set (Vec d)} {r M₂ D : ℝ}, IsUniformC11Domain U r M₁ M₂ D →
      ∀ {t : ℝ}, 0 < t → ∀ (y : Vec d), y ∈ t • U → ∀ j : ℕ, (3 : ℝ) ^ j ≤ t →
        ENNReal.ofReal (c * (min (1 / 6) r) ^ d * ((3 : ℝ) ^ j) ^ d) ≤
          volume (shiftCube (0 : Vec d) ((j : ℤ) - 1) ∩ translateSet (-y) (t • U)) := by
  obtain ⟨c0, hc0, hc01, hin⟩ := lip_inner_ball d M₁
  refine ⟨(2 * c0) ^ d, by positivity, ?_⟩
  intro U r M₂ D hU t ht y hy j hjt
  have hW := ca2_W_uniform hU ht y
  have hr : 0 < r := hU.2.1
  have h0 : (0 : Vec d) ∈ translateSet (-y) (t • U) := ⟨y, hy, by simp⟩
  have hj3 : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
  set ρ' : ℝ := min ((3 : ℝ) ^ ((j : ℤ) - 1) / 2) (t * r) with hρ'
  have hpred : (3 : ℝ) ^ ((j : ℤ) - 1) = (3 : ℝ) ^ j / 3 := lip_witness_bdry_zpow_pred j
  have hρ'0 : 0 < ρ' := by
    rw [hρ']; refine lt_min ?_ (by positivity)
    rw [hpred]; positivity
  obtain ⟨q, hq⟩ := hin _ _ _ _ hW 0 h0 ρ' hρ'0 (min_le_right _ _)
  have hsub : Metric.ball q (c0 * ρ') ⊆ shiftCube (0 : Vec d) ((j : ℤ) - 1) ∩ translateSet (-y) (t • U) := by
    intro x hx
    obtain ⟨h1, h2⟩ := hq hx
    refine ⟨?_, h2⟩
    rw [lip_witness_bdry_cube_ball]
    exact Metric.ball_subset_ball (min_le_left _ _) h1
  have hvol : volume (Metric.ball q (c0 * ρ')) = ENNReal.ofReal ((2 * c0) ^ d * ρ' ^ d) := by
    rw [Real.volume_pi_ball q (by positivity), Fintype.card_fin, ← mul_pow, mul_assoc]
  refine le_trans ?_ ((measure_mono hsub).trans' (le_of_eq hvol.symm))
  refine ENNReal.ofReal_le_ofReal ?_
  have hρ3 : (3 : ℝ) ^ j * min (1 / 6) r ≤ ρ' := by
    rw [hρ']
    refine le_min ?_ ?_
    · rw [hpred]
      have := min_le_left (1 / 6 : ℝ) r
      nlinarith only [this, hj3]
    · have := min_le_right (1 / 6 : ℝ) r
      nlinarith only [this, hj3, hjt, hr]
  have := pow_le_pow_left₀ (by positivity) hρ3 d
  calc (2 * c0) ^ d * min (1 / 6) r ^ d * ((3 : ℝ) ^ j) ^ d = (2 * c0) ^ d * ((3 : ℝ) ^ j * min (1 / 6) r) ^ d := by
        rw [mul_pow]; ring
    _ ≤ (2 * c0) ^ d * ρ' ^ d := mul_le_mul_of_nonneg_left this (by positivity)

end SuperdiffusionCLT.Section7
