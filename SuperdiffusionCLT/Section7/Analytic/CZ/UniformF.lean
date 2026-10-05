/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.CZ.UniformE

/-!
# Global `W^{1,p}` estimate: the two kinds of grid cell

For a grid cell meeting `U`, either a frontier point is near (the boundary estimate applies) or the
whole neighbourhood lies in `U` (the interior estimate applies).  Each case gives a set `B` of
bounded diameter around the cell with
`‖g‖_{L^p(U ∩ cell)} ≤ a ‖g‖_{L²(B)} + a' ‖φ‖_{L²(B)} + b ‖F‖_{L^p(B)}`.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal NNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem p13_combine {X Eg Ep EF Λ Li a a' b : ℝ≥0∞} {Cb : ℝ}
    (ha : ENNReal.ofReal Cb * Λ ≤ a) (ha' : ENNReal.ofReal Cb * (Λ * Li) ≤ a')
    (hb : ENNReal.ofReal Cb ≤ b) (hX : X ≤ ENNReal.ofReal Cb * (Λ * Eg + Λ * Li * Ep + EF)) :
    X ≤ a * Eg + a' * Ep + b * EF := by
  refine hX.trans ?_
  rw [mul_add, mul_add, ← mul_assoc, ← mul_assoc, ← mul_assoc, mul_assoc _ Λ Li]
  exact add_le_add (add_le_add (mul_le_mul_left ha _) (mul_le_mul_left ha' _)) (mul_le_mul_left hb _)

/-- A cell meeting a ball around a frontier point is controlled by the boundary estimate. -/
theorem p13_cell_bdy {U : Set (Vec d)} (hU : IsOpen U) {g : Vec d → Vec d} {φ : Vec d → ℝ}
    {F : Vec d → Vec d} {Pe : ℝ≥0∞} {x x₀ : Vec d} {s ρ₁ R₀ Rb R Cb : ℝ} {Λ Li a a' b : ℝ≥0∞}
    {k : Fin d → ℤ} (hs : 0 < s) (hxk : ∀ i, |x i - (k i : ℝ) * s| ≤ s / 2) (hx₀ : dist x x₀ < ρ₁)
    (hsR : ρ₁ + s ≤ R₀) (hR : Rb + ρ₁ + s / 2 ≤ R)
    (hbd : eLpNorm g Pe (volume.restrict (U ∩ Metric.ball x₀ R₀)) ≤
      ENNReal.ofReal Cb *
        (Λ * eLpNorm g 2 (volume.restrict (U ∩ Metric.ball x₀ Rb)) +
          Λ * Li * eLpNorm φ 2 (volume.restrict (U ∩ Metric.ball x₀ Rb)) +
          eLpNorm F Pe (volume.restrict (U ∩ Metric.ball x₀ Rb))))
    (ha : ENNReal.ofReal Cb * Λ ≤ a) (ha' : ENNReal.ofReal Cb * (Λ * Li) ≤ a')
    (hb : ENNReal.ofReal Cb ≤ b) :
    ∃ B : Set (Vec d), MeasurableSet B ∧ B ⊆ U ∧ (∀ y ∈ B, ∀ i, |y i - (k i : ℝ) * s| < R) ∧
      eLpNorm g Pe (volume.restrict (U ∩ {y | ∀ i, |y i - (k i : ℝ) * s| ≤ s / 2})) ≤
        a * eLpNorm g 2 (volume.restrict B) + a' * eLpNorm φ 2 (volume.restrict B) +
          b * eLpNorm F Pe (volume.restrict B) := by
  refine ⟨U ∩ Metric.ball x₀ Rb, hU.measurableSet.inter Metric.isOpen_ball.measurableSet,
    Set.inter_subset_left, ?_, ?_⟩
  · rintro y ⟨-, hy⟩ i
    have h1 := Metric.mem_ball.1 hy
    have h2 : |y i - x₀ i| ≤ dist y x₀ := by
      rw [dist_eq_norm]; simpa [Real.norm_eq_abs] using norm_le_pi_norm (y - x₀) i
    have h3 : |x₀ i - x i| ≤ dist x₀ x := by
      rw [dist_eq_norm]; simpa [Real.norm_eq_abs] using norm_le_pi_norm (x₀ - x) i
    rw [dist_comm] at hx₀
    have h4 := hxk i
    have h5 : |y i - (k i : ℝ) * s| ≤ |y i - x₀ i| + |x₀ i - x i| + |x i - (k i : ℝ) * s| := by
      calc |y i - (k i : ℝ) * s| = |(y i - x₀ i) + (x₀ i - x i) + (x i - (k i : ℝ) * s)| := by ring_nf
        _ ≤ _ := abs_add_three _ _ _
    linarith only [h1, h2, h3, h4, h5, hx₀, hR]
  · refine p13_combine ha ha' hb (le_trans ?_ hbd)
    refine eLpNorm_mono_measure _ (Measure.restrict_mono ?_ le_rfl)
    rintro y ⟨hyU, hyc⟩
    refine ⟨hyU, Metric.mem_ball.2 ?_⟩
    have h1 : dist y x ≤ s := by
      rw [dist_pi_le_iff hs.le]
      intro i
      have h6 := hyc i
      have h7 := hxk i
      rw [Real.dist_eq]
      calc |y i - x i| = |(y i - (k i : ℝ) * s) - (x i - (k i : ℝ) * s)| := by ring_nf
        _ ≤ |y i - (k i : ℝ) * s| + |x i - (k i : ℝ) * s| := abs_sub _ _
        _ ≤ s := by linarith only [h6, h7]
    have h2 : dist y x₀ ≤ dist y x + dist x x₀ := dist_triangle _ _ _
    linarith only [h1, h2, hx₀, hsR]

/-- A cell whose neighbourhood avoids the frontier is controlled by the interior estimate. -/
theorem p13_cell_int {U : Set (Vec d)} (hU : IsOpen U) {g : Vec d → Vec d} {φ : Vec d → ℝ}
    {F : Vec d → Vec d} {Pe : ℝ≥0∞} {x : Vec d} {s ρ₁ ℓi R Ci : ℝ} {Λ Li a a' b : ℝ≥0∞}
    {k : Fin d → ℤ} (hℓ : 0 < ℓi) (hsl : s ≤ ℓi / 2)
    (hxU : x ∈ U) (hxk : ∀ i, |x i - (k i : ℝ) * s| ≤ s / 2)
    (hρ : 0 < ρ₁) (hfar : ∀ x₀ ∈ frontier U, ρ₁ ≤ dist x x₀) (hρℓ : 3 * ℓi / 4 ≤ ρ₁)
    (hR : ℓi / 2 ≤ R)
    (hint : {y : Vec d | ∀ i, |y i - (k i : ℝ) * s| < ℓi / 2} ⊆ U →
      eLpNorm g Pe (volume.restrict (p12_box (fun i => (k i : ℝ) * s) (ℓi / 4))) ≤
        ENNReal.ofReal Ci *
          (Λ * eLpNorm g 2 (volume.restrict {y : Vec d | ∀ i, |y i - (k i : ℝ) * s| < ℓi / 2}) +
            Λ * Li * eLpNorm φ 2 (volume.restrict {y : Vec d | ∀ i, |y i - (k i : ℝ) * s| < ℓi / 2}) +
            eLpNorm F Pe (volume.restrict {y : Vec d | ∀ i, |y i - (k i : ℝ) * s| < ℓi / 2})))
    (ha : ENNReal.ofReal Ci * Λ ≤ a) (ha' : ENNReal.ofReal Ci * (Λ * Li) ≤ a')
    (hb : ENNReal.ofReal Ci ≤ b) :
    ∃ B : Set (Vec d), MeasurableSet B ∧ B ⊆ U ∧ (∀ y ∈ B, ∀ i, |y i - (k i : ℝ) * s| < R) ∧
      eLpNorm g Pe (volume.restrict (U ∩ {y | ∀ i, |y i - (k i : ℝ) * s| ≤ s / 2})) ≤
        a * eLpNorm g 2 (volume.restrict B) + a' * eLpNorm φ 2 (volume.restrict B) +
          b * eLpNorm F Pe (volume.restrict B) := by
  have hBeq := p13_box_eq_ball (fun i => (k i : ℝ) * s) (half_pos hℓ)
  have hBball : {y : Vec d | ∀ i, |y i - (k i : ℝ) * s| < ℓi / 2} ⊆ Metric.ball x ρ₁ := by
    intro y hy
    rw [Metric.mem_ball, dist_pi_lt_iff hρ]
    intro i
    have h1 := hy i
    have h2 := hxk i
    rw [Real.dist_eq]
    calc |y i - x i| = |(y i - (k i : ℝ) * s) - (x i - (k i : ℝ) * s)| := by ring_nf
      _ ≤ |y i - (k i : ℝ) * s| + |x i - (k i : ℝ) * s| := abs_sub _ _
      _ < ρ₁ := by linarith only [h1, h2, hsl, hρℓ]
  have hBU : {y : Vec d | ∀ i, |y i - (k i : ℝ) * s| < ℓi / 2} ⊆ U :=
    hBball.trans (p13_ball_subset hU hxU hρ hfar)
  refine ⟨{y : Vec d | ∀ i, |y i - (k i : ℝ) * s| < ℓi / 2}, ?_, hBU, ?_, ?_⟩
  · rw [hBeq]; exact Metric.isOpen_ball.measurableSet
  · intro y hy i
    exact (hy i).trans_le hR
  · refine p13_combine ha ha' hb (le_trans ?_ (hint hBU))
    refine eLpNorm_mono_measure _ (Measure.restrict_mono ?_ le_rfl)
    rintro y ⟨-, hyc⟩ i
    have := hyc i
    show |y i - (k i : ℝ) * s| ≤ ℓi / 4
    linarith only [this, hsl]

end SuperdiffusionCLT.Section7
