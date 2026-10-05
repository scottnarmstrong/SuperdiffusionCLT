/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.CZ.UniformF

/-!
# Global `W^{1,p}` estimate: summation over the grid cells

`p13_cells_sum` selects, for each cell of the grid of side `s`, the set `B` of bounded diameter from the
cell estimate, and sums with the bounded-overlap estimate of `p13_sum_estimate`.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal NNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- Summation over the grid cells. -/
theorem p13_cells_sum {U : Set (Vec d)} (hU : MeasurableSet U) {g : Vec d → Vec d}
    {φ : Vec d → ℝ} {F : Vec d → Vec d}
    (hg : AEStronglyMeasurable g (volume.restrict U)) (hφ : AEStronglyMeasurable φ (volume.restrict U))
    (hF : AEStronglyMeasurable F (volume.restrict U)) {p : ℝ} (hp : 2 ≤ p) {s R : ℝ} (hs : 0 < s)
    {a a' b : ℝ≥0∞}
    (hcell : ∀ k : Fin d → ℤ, (U ∩ {y : Vec d | ∀ i, |y i - (k i : ℝ) * s| ≤ s / 2}).Nonempty →
      ∃ B : Set (Vec d), MeasurableSet B ∧ B ⊆ U ∧ (∀ y ∈ B, ∀ i, |y i - (k i : ℝ) * s| < R) ∧
        eLpNorm g (ENNReal.ofReal p)
            (volume.restrict (U ∩ {y : Vec d | ∀ i, |y i - (k i : ℝ) * s| ≤ s / 2})) ≤
          a * eLpNorm g 2 (volume.restrict B) + a' * eLpNorm φ 2 (volume.restrict B) +
            b * eLpNorm F (ENNReal.ofReal p) (volume.restrict B)) :
    eLpNorm g (ENNReal.ofReal p) (volume.restrict U) ≤
      4 * (a * (((⌈2 * R / s⌉₊ + 1) ^ d : ℕ) : ℝ≥0∞) ^ (1 / 2 : ℝ) *
            eLpNorm g 2 (volume.restrict U) +
          a' * (((⌈2 * R / s⌉₊ + 1) ^ d : ℕ) : ℝ≥0∞) ^ (1 / 2 : ℝ) *
            eLpNorm φ 2 (volume.restrict U) +
          b * (((⌈2 * R / s⌉₊ + 1) ^ d : ℕ) : ℝ≥0∞) ^ (1 / p) *
            eLpNorm F (ENNReal.ofReal p) (volume.restrict U)) := by
  classical
  set cell : (Fin d → ℤ) → Set (Vec d) := fun k => {y : Vec d | ∀ i, |y i - (k i : ℝ) * s| ≤ s / 2}
    with hcelldef
  set Bk : (Fin d → ℤ) → Set (Vec d) := fun k =>
    if h : (U ∩ cell k).Nonempty then (hcell k h).choose else ∅ with hBk
  have hBprop : ∀ k, MeasurableSet (Bk k) ∧ Bk k ⊆ U ∧ (∀ y ∈ Bk k, ∀ i, |y i - (k i : ℝ) * s| < R) ∧
      eLpNorm g (ENNReal.ofReal p) (volume.restrict (U ∩ cell k)) ≤
        a * eLpNorm g 2 (volume.restrict (Bk k)) + a' * eLpNorm φ 2 (volume.restrict (Bk k)) +
          b * eLpNorm F (ENNReal.ofReal p) (volume.restrict (Bk k)) := by
    intro k
    by_cases h : (U ∩ cell k).Nonempty
    · have := (hcell k h).choose_spec
      simpa only [hBk, h, ↓reduceDIte] using this
    · have h0 : U ∩ cell k = ∅ := Set.not_nonempty_iff_eq_empty.1 h
      have hB0 : Bk k = ∅ := by
        show (if h : (U ∩ cell k).Nonempty then (hcell k h).choose else ∅) = ∅
        simp only [h, ↓reduceDIte]
      rw [hB0, h0]
      refine ⟨MeasurableSet.empty, Set.empty_subset _, fun y hy => absurd hy (Set.notMem_empty y), ?_⟩
      simp
  have hrestrU : ∀ t : Set (Vec d), t ⊆ U →
      (volume.restrict U).restrict t = volume.restrict t := fun t ht =>
    Measure.restrict_restrict_of_subset ht
  obtain ⟨N0, hN0⟩ : ∃ N0 : ℕ, N0 = (⌈2 * R / s⌉₊ + 1) ^ d := ⟨_, rfl⟩
  have hmain := p13_sum_estimate (μ := volume.restrict U) (P := fun k => U ∩ cell k) (B := Bk)
    (N := (⌈2 * R / s⌉₊ + 1) ^ d) (a := a) (a' := a') (b := b) hg hφ hF hp
    (fun k => (hBprop k).1) ?_ ?_ ?_
  · simpa only [hrestrU _ (hBprop _).2.1] using hmain
  · filter_upwards [ae_restrict_mem hU] with x hx
    obtain ⟨k, hk⟩ := p13_grid_cover s hs x
    exact ⟨k, hx, hk⟩
  · intro y
    obtain ⟨S, hS, hcard⟩ := p13_grid_count s R hs y
    refine ⟨S, fun k hk => hS k ?_, hcard⟩
    exact (hBprop k).2.2.1 y hk
  · intro k
    have h1 := (hBprop k).2.2.2
    have h2 : U ∩ cell k ⊆ U := Set.inter_subset_left
    rw [hrestrU _ h2, hrestrU _ (hBprop k).2.1]
    exact h1

end SuperdiffusionCLT.Section7
