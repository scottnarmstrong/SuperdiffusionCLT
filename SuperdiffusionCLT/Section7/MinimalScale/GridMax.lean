/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Ambient.Basic
public import Homogenization.Probability.IndependentSums.WeakOrlicz
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Data.Fintype.Pi

/-!
# The grid maximum of translated minimal scales

For `j : ℤ` and `R : ℝ`, `gridPts d j R` is the finite set of points of the lattice `3^j ℤ^d`
with sup-norm at most `R`; it has at most `(2 R / 3^j + 1)^d` elements.  `X0max X0 j R` is the
maximum of a function `X0 : Vec d → ℝ` over this set, and the union bound controls its upper tail
by the cardinality times the pointwise tail.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open MeasureTheory Homogenization

noncomputable section

open scoped Classical in
/-- The points of `3^j ℤ^d` with sup-norm at most `R`. -/
def gridPts (d : ℕ) (j : ℤ) (R : ℝ) : Finset (Vec d) :=
  (Fintype.piFinset fun _ : Fin d =>
      Finset.Icc (-(⌊R / (3 : ℝ) ^ j⌋₊ : ℤ)) (⌊R / (3 : ℝ) ^ j⌋₊ : ℤ)).image
    fun k i => (3 : ℝ) ^ j * (k i : ℝ)

/-- The maximum of `X0` over the grid `gridPts d j R`. -/
def X0max {d : ℕ} (X0 : Vec d → ℝ) (j : ℤ) (R : ℝ) : ℝ :=
  sSup (X0 '' ((gridPts d j R : Finset (Vec d)) : Set (Vec d)))

/-- Membership in the grid. -/
theorem mem_gridPts {d : ℕ} {j : ℤ} {R : ℝ} (hR : 0 ≤ R) (y : Vec d) :
    y ∈ gridPts d j R ↔ ∃ k : Fin d → ℤ, (∀ i, y i = (3 : ℝ) ^ j * (k i : ℝ)) ∧
      ∀ i, |y i| ≤ R := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) j
  unfold gridPts
  rw [Finset.mem_image]
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k, fun i => rfl, fun i => ?_⟩
    have hki : |(k i : ℝ)| ≤ (⌊R / (3 : ℝ) ^ j⌋₊ : ℝ) := by
      have := (Finset.mem_Icc.1 ((Fintype.mem_piFinset.1 hk) i))
      rw [← Int.cast_abs]
      exact_mod_cast abs_le.2 this
    have hfl : (⌊R / (3 : ℝ) ^ j⌋₊ : ℝ) ≤ R / (3 : ℝ) ^ j := Nat.floor_le (by positivity)
    rw [abs_mul, abs_of_pos h3]
    calc (3 : ℝ) ^ j * |(k i : ℝ)| ≤ (3 : ℝ) ^ j * (R / (3 : ℝ) ^ j) :=
          mul_le_mul_of_nonneg_left (hki.trans hfl) h3.le
      _ = R := by field_simp
  · rintro ⟨k, hk, hb⟩
    refine ⟨k, Fintype.mem_piFinset.2 fun i => Finset.mem_Icc.2 ?_, funext fun i => (hk i).symm⟩
    have hle : |(k i : ℝ)| ≤ R / (3 : ℝ) ^ j := by
      rw [le_div_iff₀ h3]
      have := hb i
      rw [hk i, abs_mul, abs_of_pos h3] at this
      linarith only [this, mul_comm (|(k i : ℝ)|) ((3 : ℝ) ^ j)]
    have hnat : |k i| ≤ (⌊R / (3 : ℝ) ^ j⌋₊ : ℤ) := by
      have h1 : ((|k i| : ℤ) : ℝ) ≤ R / (3 : ℝ) ^ j := by
        rw [Int.cast_abs]; exact hle
      have h2 : ((|k i|).toNat : ℝ) ≤ R / (3 : ℝ) ^ j := by
        have : ((|k i|).toNat : ℤ) = |k i| := Int.toNat_of_nonneg (abs_nonneg _)
        have h4 : (((|k i|).toNat : ℤ) : ℝ) = ((|k i| : ℤ) : ℝ) := by rw [this]
        rw [Int.cast_natCast] at h4
        rw [h4]; exact h1
      have h5 : (|k i|).toNat ≤ ⌊R / (3 : ℝ) ^ j⌋₊ := Nat.le_floor h2
      have : ((|k i|).toNat : ℤ) = |k i| := Int.toNat_of_nonneg (abs_nonneg _)
      rw [← this]; exact_mod_cast h5
    exact abs_le.1 hnat

/-- The origin is a grid point. -/
theorem zero_mem_gridPts {d : ℕ} {j : ℤ} {R : ℝ} (hR : 0 ≤ R) : (0 : Vec d) ∈ gridPts d j R :=
  (mem_gridPts hR 0).2 ⟨0, fun i => by simp, fun i => by simpa using hR⟩

/-- The grid is nonempty for `R ≥ 0`. -/
theorem gridPts_nonempty (d : ℕ) (j : ℤ) {R : ℝ} (hR : 0 ≤ R) : (gridPts d j R).Nonempty :=
  ⟨0, zero_mem_gridPts hR⟩

/-- **Cardinality of the grid.** -/
theorem card_gridPts_le (d : ℕ) (j : ℤ) {R : ℝ} (hR : 0 ≤ R) :
    ((gridPts d j R).card : ℝ) ≤ (2 * R / (3 : ℝ) ^ j + 1) ^ d := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) j
  unfold gridPts
  refine le_trans (Nat.cast_le.2 Finset.card_image_le) ?_
  rw [Fintype.card_piFinset]
  simp only [Finset.prod_const, Int.card_Icc, Finset.card_univ, Fintype.card_fin]
  have hfl : (⌊R / (3 : ℝ) ^ j⌋₊ : ℝ) ≤ R / (3 : ℝ) ^ j := Nat.floor_le (by positivity)
  have hint : (((⌊R / (3 : ℝ) ^ j⌋₊ : ℤ) + 1 - (-(⌊R / (3 : ℝ) ^ j⌋₊ : ℤ))).toNat : ℝ) ≤
      2 * R / (3 : ℝ) ^ j + 1 := by
    have : (((⌊R / (3 : ℝ) ^ j⌋₊ : ℤ) + 1 - (-(⌊R / (3 : ℝ) ^ j⌋₊ : ℤ))).toNat : ℤ) =
        2 * (⌊R / (3 : ℝ) ^ j⌋₊ : ℤ) + 1 := by
      rw [Int.toNat_of_nonneg (by omega)]; ring
    have h2 : ((((⌊R / (3 : ℝ) ^ j⌋₊ : ℤ) + 1 - (-(⌊R / (3 : ℝ) ^ j⌋₊ : ℤ))).toNat : ℤ) : ℝ) =
        2 * (⌊R / (3 : ℝ) ^ j⌋₊ : ℝ) + 1 := by
      rw [this]; push_cast; ring
    rw [Int.cast_natCast] at h2
    rw [h2]
    have : 2 * R / (3 : ℝ) ^ j = 2 * (R / (3 : ℝ) ^ j) := by ring
    rw [this]; linarith only [hfl]
  push_cast
  exact pow_le_pow_left₀ (by positivity) hint d

/-- On the grid, the maximum dominates the value. -/
theorem le_X0max {d : ℕ} (X0 : Vec d → ℝ) (j : ℤ) {R : ℝ} {y : Vec d} (hy : y ∈ gridPts d j R) :
    X0 y ≤ X0max X0 j R :=
  le_csSup ((Set.Finite.image _ (Finset.finite_toSet _)).bddAbove) ⟨y, hy, rfl⟩

/-- `X0max ≤ T` iff every grid value is at most `T`. -/
theorem X0max_le_iff {d : ℕ} (X0 : Vec d → ℝ) (j : ℤ) {R : ℝ} (hR : 0 ≤ R) (T : ℝ) :
    X0max X0 j R ≤ T ↔ ∀ y ∈ gridPts d j R, X0 y ≤ T := by
  constructor
  · intro h y hy
    exact (le_X0max X0 j hy).trans h
  · intro h
    refine csSup_le (Set.Nonempty.image X0 (Finset.coe_nonempty.2 (gridPts_nonempty d j hR))) ?_
    rintro _ ⟨y, hy, rfl⟩
    exact h y hy

/-- The maximum is attained on the grid. -/
theorem exists_X0max_eq {d : ℕ} (X0 : Vec d → ℝ) (j : ℤ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ y ∈ gridPts d j R, X0max X0 j R = X0 y := by
  have hne : (X0 '' ((gridPts d j R : Finset (Vec d)) : Set (Vec d))).Nonempty :=
    Set.Nonempty.image X0 (Finset.coe_nonempty.2 (gridPts_nonempty d j hR))
  obtain ⟨y, hy, hyeq⟩ := hne.csSup_mem (Set.Finite.image _ (Finset.finite_toSet _))
  exact ⟨y, hy, hyeq.symm⟩

end

end SuperdiffusionCLT.Section7
