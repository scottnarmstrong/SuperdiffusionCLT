/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellField.J3Observable

/-!
# First-derivative API for the marginal J3 cube norm

This module supplies the ordinary pointwise and monotonicity interface for the
exact first-derivative supremum appearing in `j3Observable`.  It is
source-neutral: it introduces no probabilistic assumption or scaling law.
-/

@[expose] public section

namespace SuperdiffusionCLT.Frozen.Assumptions.ShellField

open Set
open Homogenization
open Homogenization.Book.Ch02

noncomputable section

variable {d : ℕ}

private theorem shellCubeDerivRange_bddAbove (n : ℕ) (j : ShellField d) :
    BddAbove
      (Set.range fun o : Option (ShellOpenCubePoint d n) =>
        match o with
        | none => 0
        | some x => matrixDerivativeNorm (ShellField.deriv j x.1)) := by
  let K : Set (Vec d) :=
    Metric.closedBall
      (cubeCenter (originCube d (n : ℤ)))
      (cubeRadius (originCube d (n : ℤ)))
  have hK : IsCompact K := by
    simpa only [K] using
      isCompact_closedBall
        (cubeCenter (originCube d (n : ℤ)))
        (cubeRadius (originCube d (n : ℤ)))
  have hcont : Continuous
      (fun x : Vec d => matrixDerivativeNorm (ShellField.deriv j x)) :=
    matrixDerivativeNorm_continuous.comp (ShellField.deriv j).continuous
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max 0 C, ?_⟩
  rintro r ⟨o, rfl⟩
  cases o with
  | none =>
      exact le_max_left 0 C
  | some x =>
      have hxK : x.1 ∈ K := by
        apply Metric.ball_subset_closedBall
        rw [ball_cubeCenter_eq_openCubeSet]
        exact x.2
      have hderiv : matrixDerivativeNorm (ShellField.deriv j x.1) ≤ C := by
        calc
          matrixDerivativeNorm (ShellField.deriv j x.1) =
              |matrixDerivativeNorm (ShellField.deriv j x.1)| :=
            (abs_of_nonneg (matrixDerivativeNorm_nonneg _)).symm
          _ = ‖matrixDerivativeNorm (ShellField.deriv j x.1)‖ :=
            (Real.norm_eq_abs _).symm
          _ ≤ C := hC x.1 hxK
      exact hderiv.trans (le_max_right 0 C)

/-- Sharp characterization: the scale-`n` open-cube first-derivative norm is
the least nonnegative constant controlling the exact induced norm at every
point of the natural open cube. -/
theorem shellCubeDerivNorm_le_iff (n : ℕ) (j : ShellField d) (C : ℝ) :
    shellCubeDerivNorm n j ≤ C ↔
      0 ≤ C ∧
        ∀ x : ShellOpenCubePoint d n,
          matrixDerivativeNorm (ShellField.deriv j x.1) ≤ C := by
  constructor
  · intro h
    refine ⟨(shellCubeDerivNorm_nonneg n j).trans h, ?_⟩
    intro x
    have hx : matrixDerivativeNorm (ShellField.deriv j x.1) ≤
        shellCubeDerivNorm n j := by
      change matrixDerivativeNorm (ShellField.deriv j x.1) ≤
        sSup
          (Set.range fun o : Option (ShellOpenCubePoint d n) =>
            match o with
            | none => 0
            | some y => matrixDerivativeNorm (ShellField.deriv j y.1))
      exact le_csSup (shellCubeDerivRange_bddAbove n j) ⟨some x, rfl⟩
    exact hx.trans h
  · rintro ⟨hC, h⟩
    change
      sSup
          (Set.range fun o : Option (ShellOpenCubePoint d n) =>
            match o with
            | none => 0
            | some x => matrixDerivativeNorm (ShellField.deriv j x.1)) ≤ C
    apply csSup_le (Set.range_nonempty _)
    rintro r ⟨o, rfl⟩
    cases o with
    | none => exact hC
    | some x => exact h x

/-- The scale-`n` cube first-derivative norm dominates the exact induced
derivative norm at every point of the natural open cube. -/
theorem matrixDerivativeNorm_deriv_le_shellCubeDerivNorm (n : ℕ)
    (j : ShellField d) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d (n : ℤ))) :
    matrixDerivativeNorm (ShellField.deriv j x) ≤ shellCubeDerivNorm n j := by
  exact
    ((shellCubeDerivNorm_le_iff n j (shellCubeDerivNorm n j)).mp le_rfl).2
      ⟨x, hx⟩

private theorem openCubeSet_originCube_mono_nat {n k : ℕ} (h : n ≤ k) :
    openCubeSet (originCube d (n : ℤ)) ⊆
      openCubeSet (originCube d (k : ℤ)) := by
  intro x hx
  rw [mem_openCubeSet_originCube_iff] at hx ⊢
  have hnk : (n : ℤ) ≤ (k : ℤ) := by
    exact_mod_cast h
  have hpow : (3 : ℝ) ^ (n : ℤ) ≤ (3 : ℝ) ^ (k : ℤ) :=
    zpow_le_zpow_right₀ (by norm_num) hnk
  intro i
  obtain ⟨hlo, hhi⟩ := hx i
  constructor
  · exact
      lt_of_le_of_lt
        (mul_le_mul_of_nonpos_left hpow (by norm_num : -(1 / 2 : ℝ) ≤ 0))
        hlo
  · exact
      lt_of_lt_of_le hhi
        (mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 1 / 2))

/-- The natural-cube first-derivative norm is monotone in the Nat scale index,
because the centered open cubes are nested. -/
theorem shellCubeDerivNorm_mono {n k : ℕ} (h : n ≤ k)
    (j : ShellField d) :
    shellCubeDerivNorm n j ≤ shellCubeDerivNorm k j := by
  refine (shellCubeDerivNorm_le_iff n j (shellCubeDerivNorm k j)).2 ⟨?_, ?_⟩
  · exact shellCubeDerivNorm_nonneg k j
  · intro x
    exact matrixDerivativeNorm_deriv_le_shellCubeDerivNorm k j
      (openCubeSet_originCube_mono_nat h x.2)

end

end SuperdiffusionCLT.Frozen.Assumptions.ShellField
