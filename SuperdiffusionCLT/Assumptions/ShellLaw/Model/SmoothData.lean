/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Topology.Algebra.Support
public import Homogenization.Book.Ch02.Theorems.MatrixOperatorNorm

/-!
# Smooth data for the cell model of a nondegenerate shell law

Explicit smooth ingredients of the white-noise-by-cells construction.

* `partitionProfile`: an even smooth function `χ` with support in `(-1, 1)`,
  `0 ≤ χ ≤ 1`, `χ 0 = 1`, and `∑_{k ∈ ℤ} χ (t - k) ^ 2 = 1`.
* `cellWeight d`: the tensor product `w y = ∏ i, χ (2 * y i)`, supported in
  the open cube `(-1/2, 1/2)^d`, with `∑_{k ∈ ℤ^d} w (y - k/2) ^ 2 = 1`.
* `radialBump d`: `ψ x = s (1 - 4 * ∑ i, x i ^ 2)` with `s` the smooth
  transition, a radial smooth bump equal to `1` at the origin and vanishing
  outside the open Euclidean ball of radius `1/2`.

Both `w` and `ψ` are smooth, compactly supported, have values in `[0, 1]`,
have bounded iterated derivatives of every order, and are invariant under
coordinate permutations and coordinate sign changes.
-/

@[expose] public section

namespace SuperdiffusionCLT.Assumptions.ShellLaw.Model

open Homogenization Set Real

noncomputable section

/-! ## The one-dimensional partition profile -/

/-- The smooth transition applied to `3 |t| - 1`, written without the absolute
value as a sum of two one-sided pieces. -/
def partitionAngle (t : ℝ) : ℝ :=
  Real.smoothTransition (3 * t - 1) + Real.smoothTransition (-3 * t - 1)

/-- The even smooth partition profile `χ`: `cos (π/2 * h)` with `h` the smooth
transition of `3 |t| - 1`. -/
def partitionProfile (t : ℝ) : ℝ := Real.cos (π / 2 * partitionAngle t)

theorem partitionAngle_contDiff : ContDiff ℝ (⊤ : ℕ∞) partitionAngle := by
  unfold partitionAngle
  refine ContDiff.add ?_ ?_
  · exact Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul contDiff_id).sub contDiff_const)
  · exact Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul contDiff_id).sub contDiff_const)

theorem partitionProfile_contDiff : ContDiff ℝ (⊤ : ℕ∞) partitionProfile :=
  Real.contDiff_cos.comp (contDiff_const.mul partitionAngle_contDiff)

theorem partitionAngle_neg (t : ℝ) : partitionAngle (-t) = partitionAngle t := by
  unfold partitionAngle
  have h1 : 3 * -t - 1 = -3 * t - 1 := by ring
  have h2 : -3 * -t - 1 = 3 * t - 1 := by ring
  rw [h1, h2, add_comm]

theorem partitionProfile_neg (t : ℝ) : partitionProfile (-t) = partitionProfile t := by
  unfold partitionProfile
  rw [partitionAngle_neg]

theorem partitionAngle_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    partitionAngle t = Real.smoothTransition (3 * t - 1) := by
  unfold partitionAngle
  rw [Real.smoothTransition.zero_of_nonpos (x := -3 * t - 1) (by linarith only [ht]),
    add_zero]

theorem partitionProfile_zero : partitionProfile 0 = 1 := by
  unfold partitionProfile partitionAngle
  rw [Real.smoothTransition.zero_of_nonpos (by norm_num),
    Real.smoothTransition.zero_of_nonpos (by norm_num)]
  simp

/-- The profile vanishes outside `(-1, 1)`. -/
theorem partitionProfile_eq_zero_of_one_le_abs {t : ℝ} (ht : 1 ≤ |t|) :
    partitionProfile t = 0 := by
  have key : ∀ s : ℝ, 1 ≤ s → partitionProfile s = 0 := by
    intro s hs
    unfold partitionProfile
    rw [partitionAngle_of_nonneg (by linarith only [hs]),
      Real.smoothTransition.one_of_one_le (by linarith only [hs]), mul_one]
    exact Real.cos_pi_div_two
  rcases le_abs'.1 ht with h | h
  · rw [← partitionProfile_neg]; exact key _ (by linarith only [h])
  · exact key _ h

theorem smoothTransition_add_one_sub (x : ℝ) :
    Real.smoothTransition x + Real.smoothTransition (1 - x) = 1 := by
  unfold Real.smoothTransition
  have h1 := Real.smoothTransition.pos_denom x
  have h2 : 1 - (1 - x) = x := by ring
  rw [h2, add_comm (expNegInvGlue (1 - x)) (expNegInvGlue x), ← add_div,
    div_self h1.ne']

/-- On `[0, 1]` the profile and its shift by one are complementary. -/
theorem partitionProfile_sq_add {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    partitionProfile u ^ 2 + partitionProfile (u - 1) ^ 2 = 1 := by
  have h1 : partitionProfile (u - 1) = partitionProfile (1 - u) := by
    rw [← partitionProfile_neg (u - 1)]; congr 1; ring
  rw [h1]
  unfold partitionProfile
  rw [partitionAngle_of_nonneg hu0, partitionAngle_of_nonneg (by linarith only [hu1])]
  have hs := smoothTransition_add_one_sub (3 * u - 1)
  have h3 : 3 * (1 - u) - 1 = 1 - (3 * u - 1) := by ring
  have h4 : Real.smoothTransition (3 * (1 - u) - 1)
      = 1 - Real.smoothTransition (3 * u - 1) := by
    rw [h3]; linarith only [hs]
  rw [h4]
  have : π / 2 * (1 - Real.smoothTransition (3 * u - 1))
      = π / 2 - π / 2 * Real.smoothTransition (3 * u - 1) := by ring
  rw [this, Real.cos_pi_div_two_sub]
  exact Real.cos_sq_add_sin_sq _

/-- Away from the two cells meeting `t`, the shifted profile vanishes. -/
theorem partitionProfile_sub_int_sq_add (t : ℝ) :
    partitionProfile (t - ⌊t⌋) ^ 2 + partitionProfile (t - (⌊t⌋ + 1 : ℤ)) ^ 2 = 1 := by
  have h0 := Int.fract_nonneg t
  have h1 := Int.fract_lt_one t
  have := partitionProfile_sq_add (u := Int.fract t) h0 h1.le
  rw [Int.fract] at this
  have e : t - (⌊t⌋ + 1 : ℤ) = t - ⌊t⌋ - 1 := by push_cast; ring
  rw [e]; exact this

theorem partitionProfile_sub_int_eq_zero {t : ℝ} {k : ℤ} (hk0 : k ≠ ⌊t⌋)
    (hk1 : k ≠ ⌊t⌋ + 1) : partitionProfile (t - k) = 0 := by
  apply partitionProfile_eq_zero_of_one_le_abs
  have h0 := Int.floor_le t
  have h1 := Int.lt_floor_add_one t
  rcases lt_or_gt_of_ne hk0 with h | h
  · have : (k : ℝ) ≤ ⌊t⌋ - 1 := by exact_mod_cast (by omega : k ≤ ⌊t⌋ - 1)
    rw [abs_of_nonneg (by linarith only [h0, this])]
    linarith only [h0, this]
  · have h2 : ⌊t⌋ + 2 ≤ k := by omega
    have : (⌊t⌋ : ℝ) + 2 ≤ k := by exact_mod_cast h2
    rw [abs_of_nonpos (by linarith only [h1, this])]
    linarith only [h1, this]

/-! ## The tensor-product cell weight -/

variable {d : ℕ}

/-- The cell weight `w y = ∏ i, χ (2 * y i)`, supported in the open cube
`(-1/2, 1/2)^d`. -/
def cellWeight (d : ℕ) (y : Vec d) : ℝ := ∏ i, partitionProfile (2 * y i)

theorem cellWeight_contDiff : ContDiff ℝ (⊤ : ℕ∞) (cellWeight d) := by
  unfold cellWeight
  refine contDiff_prod fun i _ ↦ ?_
  exact partitionProfile_contDiff.comp (contDiff_const.mul (contDiff_apply ℝ ℝ i))

@[simp]
theorem cellWeight_zero : cellWeight d (0 : Vec d) = 1 := by
  simp [cellWeight, partitionProfile_zero]

/-- The cell weight vanishes as soon as one coordinate has `|y i| ≥ 1/2`. -/
theorem cellWeight_eq_zero_of_half_le {y : Vec d} {i : Fin d} (h : 1 / 2 ≤ |y i|) :
    cellWeight d y = 0 := by
  unfold cellWeight
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  refine partitionProfile_eq_zero_of_one_le_abs ?_
  rw [abs_mul, abs_two]
  linarith only [h]

theorem abs_lt_half_of_cellWeight_ne_zero {y : Vec d} (h : cellWeight d y ≠ 0) (i : Fin d) :
    |y i| < 1 / 2 :=
  lt_of_not_ge fun h1 ↦ h (cellWeight_eq_zero_of_half_le h1)

/-- The support of the cell weight lies in a compact cube, so `w` has compact
support. -/
theorem cellWeight_hasCompactSupport : HasCompactSupport (cellWeight d) := by
  refine HasCompactSupport.intro (K := Set.pi Set.univ fun _ : Fin d ↦ Icc (-(1 / 2 : ℝ)) (1 / 2))
    (isCompact_univ_pi fun _ ↦ isCompact_Icc) fun y hy ↦ ?_
  by_contra hne
  refine hy fun i _ ↦ ?_
  have := abs_lt_half_of_cellWeight_ne_zero hne i
  exact ⟨by linarith only [(abs_lt.1 this).1], by linarith only [(abs_lt.1 this).2]⟩

/-- The squares of the lattice translates of the cell weight over the lattice
`(1/2) ℤ^d` form a partition of unity. -/
theorem hasSum_cellWeight_sq (y : Vec d) :
    HasSum (fun k : Fin d → ℤ ↦ cellWeight d (fun i ↦ y i - (k i : ℝ) / 2) ^ 2) 1 := by
  have hterm : ∀ k : Fin d → ℤ,
      cellWeight d (fun i ↦ y i - (k i : ℝ) / 2) ^ 2
        = ∏ i, partitionProfile (2 * y i - k i) ^ 2 := by
    intro k
    unfold cellWeight
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    congr 2; ring
  let S : Finset (Fin d → ℤ) :=
    Fintype.piFinset fun i ↦ ({⌊2 * y i⌋, ⌊2 * y i⌋ + 1} : Finset ℤ)
  have hS : HasSum (fun k : Fin d → ℤ ↦ ∏ i, partitionProfile (2 * y i - k i) ^ 2)
      (∑ k ∈ S, ∏ i, partitionProfile (2 * y i - k i) ^ 2) :=
    hasSum_sum_of_ne_finset_zero (fun k hk ↦ by
      have : ∃ i, k i ∉ ({⌊2 * y i⌋, ⌊2 * y i⌋ + 1} : Finset ℤ) := by
        by_contra hall
        push Not at hall
        exact hk (Fintype.mem_piFinset.2 hall)
      obtain ⟨i, hi⟩ := this
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by
        rw [partitionProfile_sub_int_eq_zero hi.1 hi.2]; norm_num))
  have hval : ∑ k ∈ S, ∏ i, partitionProfile (2 * y i - k i) ^ 2 = 1 := by
    have := (Finset.prod_univ_sum (fun i ↦ ({⌊2 * y i⌋, ⌊2 * y i⌋ + 1} : Finset ℤ))
      (fun i (k : ℤ) ↦ partitionProfile (2 * y i - k) ^ 2)).symm
    rw [show (∑ k ∈ S, ∏ i, partitionProfile (2 * y i - k i) ^ 2) = _ from this]
    refine Finset.prod_eq_one fun i _ ↦ ?_
    have hne : ⌊2 * y i⌋ ≠ ⌊2 * y i⌋ + 1 := by omega
    rw [Finset.sum_pair hne, partitionProfile_sub_int_sq_add]
  rw [hval] at hS
  simpa only [hterm] using hS

/-! ## The radial bump -/

/-- The radial smooth bump `ψ x = s (1 - 4 * ∑ i, x i ^ 2)`, equal to `1` at the
origin, positive exactly on the open Euclidean ball of radius `1/2`. -/
def radialBump (d : ℕ) (x : Vec d) : ℝ :=
  Real.smoothTransition (1 - 4 * ∑ i, x i ^ 2)

theorem radialBump_contDiff : ContDiff ℝ (⊤ : ℕ∞) (radialBump d) := by
  unfold radialBump
  refine Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_const.mul ?_))
  exact ContDiff.sum fun i _ ↦ (contDiff_apply ℝ ℝ i).pow 2

theorem radialBump_nonneg (x : Vec d) : 0 ≤ radialBump d x :=
  Real.smoothTransition.nonneg _

@[simp]
theorem radialBump_zero : radialBump d (0 : Vec d) = 1 := by
  simp [radialBump]

/-- The bump vanishes when `∑ x i ^ 2 ≥ 1/4`. -/
theorem radialBump_eq_zero_of_le {x : Vec d} (h : 1 / 4 ≤ ∑ i, x i ^ 2) :
    radialBump d x = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith only [h])

/-- The support of the bump lies in the open cube `(-1/2, 1/2)^d`. -/
theorem abs_lt_half_of_radialBump_ne_zero {x : Vec d} (h : radialBump d x ≠ 0) (i : Fin d) :
    |x i| < 1 / 2 := by
  by_contra hge
  refine h (radialBump_eq_zero_of_le ?_)
  have h1 : x i ^ 2 ≤ ∑ j, x j ^ 2 :=
    Finset.single_le_sum (f := fun j ↦ x j ^ 2) (fun j _ ↦ sq_nonneg _) (Finset.mem_univ i)
  have h2 : 1 / 4 ≤ x i ^ 2 := by
    have : (1 / 2 : ℝ) ≤ |x i| := not_lt.1 hge
    nlinarith only [this, sq_abs (x i)]
  linarith only [h1, h2]

theorem radialBump_hasCompactSupport : HasCompactSupport (radialBump d) := by
  refine HasCompactSupport.intro (K := Set.pi Set.univ fun _ : Fin d ↦ Icc (-(1 / 2 : ℝ)) (1 / 2))
    (isCompact_univ_pi fun _ ↦ isCompact_Icc) fun y hy ↦ ?_
  by_contra hne
  refine hy fun i _ ↦ ?_
  have := abs_lt_half_of_radialBump_ne_zero hne i
  exact ⟨by linarith only [(abs_lt.1 this).1], by linarith only [(abs_lt.1 this).2]⟩

theorem radialBump_comp_perm (σ : Equiv.Perm (Fin d)) (x : Vec d) :
    radialBump d (fun i ↦ x (σ i)) = radialBump d x := by
  unfold radialBump
  rw [Equiv.sum_comp σ fun i ↦ x i ^ 2]

theorem radialBump_mul_sign (s : Fin d → ℝ) (hs : ∀ i, s i = 1 ∨ s i = -1) (x : Vec d) :
    radialBump d (fun i ↦ s i * x i) = radialBump d x := by
  unfold radialBump
  congr 3
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  show (s i * x i) ^ 2 = x i ^ 2
  rcases hs i with h | h <;> rw [h] <;> ring

/-! ## Derivative bounds -/

/-- The iterated derivatives of the cell weight up to any order are uniformly
bounded. -/
theorem cellWeight_exists_bound_iteratedFDeriv (m : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ i ≤ m, ∀ y : Vec d, ‖iteratedFDeriv ℝ i (cellWeight d) y‖ ≤ C :=
  cellWeight_hasCompactSupport.exists_bound_iteratedFDeriv cellWeight_contDiff m

/-- The iterated derivatives of the radial bump up to any order are uniformly
bounded. -/
theorem radialBump_exists_bound_iteratedFDeriv (m : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ i ≤ m, ∀ y : Vec d, ‖iteratedFDeriv ℝ i (radialBump d) y‖ ≤ C :=
  radialBump_hasCompactSupport.exists_bound_iteratedFDeriv radialBump_contDiff m

/-! ## Satisfiability witnesses -/

/-- The two-dimensional cell weight is nonzero at the origin, and a point of the
open half-ball has positive bump value, so the data are not identically zero. -/
example : cellWeight 2 (0 : Vec 2) = 1 ∧ radialBump 2 (0 : Vec 2) = 1 ∧
    ∃ y : Vec 2, 0 < cellWeight 2 y ∧ 0 < radialBump 2 y :=
  ⟨cellWeight_zero, radialBump_zero, 0, by simp, by simp⟩

end

end SuperdiffusionCLT.Assumptions.ShellLaw.Model
