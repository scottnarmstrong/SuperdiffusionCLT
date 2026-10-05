/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import SuperdiffusionCLT.Section7.Analytic.Geometry.RoundedCubeB

/-!
# The superellipsoid is a smooth bounded domain
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization

variable {d : ℕ}

/-- The graph chart of the superellipsoid at a frontier point. -/
theorem g1_chart [NeZero d] {N : ℕ} (hN : 1 ≤ N) {x : Vec d} (hx : x ∈ frontier (g1_superE d N)) :
    ∃ (e : Vec d) (ψ : Vec d → ℝ) (W : Set (Vec d)) (r : ℝ),
      vecNormSq e = 1 ∧ 0 < r ∧ IsOpen W ∧ ContDiffOn ℝ (⊤ : ℕ∞) ψ W ∧
      ∀ y ∈ Metric.ball x r, (y - vecDot e y • e) ∈ W ∧
        (y ∈ g1_superE d N ↔ vecDot e y < ψ (y - vecDot e y • e)) := by
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => |x i|) Finset.univ_nonempty
  have hP := g1_frontier_P N hx
  have hxj : x j ≠ 0 := by
    intro h0
    have hle : g1_P N x ≤ 0 := by
      unfold g1_P
      refine Finset.sum_nonpos fun i _ => ?_
      have h1 : |x i| ≤ |x j| := hj i (Finset.mem_univ i)
      rw [h0, abs_zero] at h1
      have h2 : x i = 0 := abs_nonpos_iff.1 h1
      rw [h2, zero_pow (show 2 * N ≠ 0 by omega)]
    linarith only [hP, hle]
  have hs : sgn (x j) * sgn (x j) = 1 := sgn_sq _
  have hsx : sgn (x j) * x j = |x j| := sgn_mul_self _
  have hO : IsOpen {y : Vec d | 0 < sgn (x j) * y j ∧
      g1_P N (y - vecDot (g1_e j (sgn (x j))) y • g1_e j (sgn (x j))) < 1} := by
    refine IsOpen.inter (isOpen_lt continuous_const (continuous_const.mul (continuous_apply j))) ?_
    exact isOpen_lt ((g1_continuous_P N).comp (continuous_proj _)) continuous_const
  have hxO : x ∈ {y : Vec d | 0 < sgn (x j) * y j ∧
      g1_P N (y - vecDot (g1_e j (sgn (x j))) y • g1_e j (sgn (x j))) < 1} := by
    refine ⟨?_, ?_⟩
    · rw [hsx]
      exact abs_pos.2 hxj
    · have := g1_P_split hN j hs x
      have hpos : 0 < x j ^ (2 * N) := (even_two_mul N).pow_pos hxj
      linarith only [this, hP, hpos]
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hO x hxO
  have hnpos : (0 : ℝ) < ((2 * N : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2 * N by omega)
  refine ⟨g1_e j (sgn (x j)), fun z => (1 - g1_P N z) ^ (((2 * N : ℕ) : ℝ)⁻¹),
    {z | g1_P N z < 1}, r, g1_vecNormSq_e j hs, hr,
    isOpen_lt (g1_continuous_P N) continuous_const, ?_, fun y hy => ?_⟩
  · have hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec d => 1 - g1_P N z) {z | g1_P N z < 1} :=
      (contDiff_const.sub (g1_contDiff_P N)).contDiffOn
    refine ContDiffOn.rpow_const_of_ne hf fun z hz => ?_
    have : g1_P N z < 1 := hz
    exact (sub_pos.2 this).ne'
  · obtain ⟨h1, h2⟩ := hball hy
    refine ⟨h2, ?_⟩
    have hsplit := g1_P_split hN j hs y
    have hq : 0 ≤ 1 - g1_P N (y - vecDot (g1_e j (sgn (x j))) y • g1_e j (sgn (x j))) := by
      linarith only [h2]
    show g1_P N y < 1 ↔ _ < (1 - g1_P N _) ^ (((2 * N : ℕ) : ℝ)⁻¹)
    generalize g1_P N (y - vecDot (g1_e j (sgn (x j))) y • g1_e j (sgn (x j))) = q at h2 hsplit hq ⊢
    rw [g1_vecDot_e]
    rw [Real.lt_rpow_inv_iff_of_pos h1.le hq hnpos, Real.rpow_natCast,
      mul_pow, pow_mul, sq, hs, one_pow, one_mul]
    constructor <;> intro h <;> linarith only [h, hsplit]

/-- The superellipsoid is a smooth bounded domain. -/
theorem g1_isSmoothBoundedDomain_superE [NeZero d] {N : ℕ} (hN : 1 ≤ N) :
    IsSmoothBoundedDomain (g1_superE d N) :=
  ⟨g1_isOpen_superE N, g1_isConnected_superE hN, g1_isBoundedDomain hN, fun _ hx => by
    obtain ⟨e, ψ, W, r, he, hr, hW, hψ, hc⟩ := g1_chart hN hx
    exact ⟨e, ψ, W, r, he, hr, hW, hψ, hc⟩⟩

end SuperdiffusionCLT.Section7
