/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellField.J3DerivativeAPI
public import SuperdiffusionCLT.Assumptions.ShellLaw.J3Consequences
public import SuperdiffusionCLT.Probability.GammaSigmaHelpers
public import SuperdiffusionCLT.Section2.Cutoff.Finite

/-!
# Finite-shell derivative concentration

This module gives the ordinary derivative-envelope estimate used at the start
of the finite-increment `L∞` argument.  Assumption J3 (`ShellLawJ3`) alone controls
the shellwise first-derivative norm at scale `3⁻ᵏ`; the generalized `Gamma₂` triangle
inequality of the CoarseGraining library and a finite geometric sum give scale `3⁻ⁿ`
for the sum over `k ∈ (n,m]`.

The deterministic statements identify the derivative of the finite increment
with the sum of the stored shell derivatives and bound its exact induced norm
pointwise on `cu_n`.  No `L∞` carrier equality is asserted here.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Estimates.Stream

open MeasureTheory
open Homogenization
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Section2.Cutoff
open scoped BigOperators Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}
variable {P : ProbabilityMeasure (ShellSeq d)}

/-- Sum of the exact first-derivative shell norms on the common smaller cube
`cu_n`, over the literal natural interval `(n,m]`. -/
def finiteShellDerivGauge (n m : ℕ) (omega : ShellSeq d) : ℝ :=
  ∑ k ∈ Finset.Ioc n m,
    ShellField.shellCubeDerivNorm n (omega k)

/-- The finite shell derivative gauge is pointwise nonnegative. -/
theorem finiteShellDerivGauge_nonneg (n m : ℕ) (omega : ShellSeq d) :
    0 ≤ finiteShellDerivGauge n m omega := by
  exact Finset.sum_nonneg fun k _ ↦
    ShellField.shellCubeDerivNorm_nonneg n (omega k)

/-- A fixed cube norm of a fixed shell coordinate is measurable on the
natural shell-sequence carrier. -/
theorem measurable_shellCubeDerivNorm_coordinate (n k : ℕ) :
    Measurable
      (fun omega : ShellSeq d ↦
        ShellField.shellCubeDerivNorm n (omega k)) :=
  (ShellField.shellCubeDerivNorm_measurable n).comp
    (ShellField.measurable_shellCoordinate k)

/-- The summed cube-`n` first-derivative gauge is measurable. -/
theorem measurable_finiteShellDerivGauge (n m : ℕ) :
    Measurable (finiteShellDerivGauge n m : ShellSeq d → ℝ) := by
  unfold finiteShellDerivGauge
  exact Finset.measurable_sum (Finset.Ioc n m) fun k _ ↦
    measurable_shellCubeDerivNorm_coordinate n k

private theorem matrixDerivativeNorm_zero :
    ShellField.matrixDerivativeNorm (0 : ShellField.MatrixDerivative d) = 0 := by
  apply le_antisymm
  · calc
      ShellField.matrixDerivativeNorm (0 : ShellField.MatrixDerivative d) ≤
          (d : ℝ) ^ 2 * ‖(0 : ShellField.MatrixDerivative d)‖ :=
        ShellField.matrixDerivativeNorm_le_sq_mul_norm 0
      _ = 0 := by rw [norm_zero, mul_zero]
  · exact ShellField.matrixDerivativeNorm_nonneg 0

private theorem shellCubeDerivNorm_eq_zero_of_dimension_zero
    (n : ℕ) (j : ShellField 0) :
    ShellField.shellCubeDerivNorm n j = 0 := by
  apply le_antisymm
  · apply (ShellField.shellCubeDerivNorm_le_iff n j 0).2
    refine ⟨le_rfl, ?_⟩
    intro x
    have hbound :=
      ShellField.matrixDerivativeNorm_le_sq_mul_norm (d := 0)
        (ShellField.deriv j x.1)
    simpa only [Nat.cast_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      zero_mul] using hbound
  · exact ShellField.shellCubeDerivNorm_nonneg n j

/-- The first-derivative term with the dimension-free weight `3^k` is
dominated by the complete J3 observable.  For positive dimension this uses
`1 ≤ √d`; in dimension zero the induced derivative norm vanishes. -/
theorem pow_mul_shellCubeDerivNorm_le_j3Observable
    (k : ℕ) (j : ShellField d) :
    (3 : ℝ) ^ k * ShellField.shellCubeDerivNorm k j ≤
      ShellField.j3Observable d k j := by
  by_cases hd : d = 0
  · subst d
    rw [shellCubeDerivNorm_eq_zero_of_dimension_zero, mul_zero]
    exact ShellField.j3Observable_nonneg 0 k j
  · have hd_one : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd
    have hsqrt : (1 : ℝ) ≤ Real.sqrt d := by
      rw [Real.one_le_sqrt]
      exact_mod_cast hd_one
    have hpow : 0 ≤ (3 : ℝ) ^ k := pow_nonneg (by norm_num) k
    have hweight : (3 : ℝ) ^ k ≤ Real.sqrt d * (3 : ℝ) ^ k := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hsqrt hpow
    have hderiv :
        (3 : ℝ) ^ k * ShellField.shellCubeDerivNorm k j ≤
          (Real.sqrt d * (3 : ℝ) ^ k) *
            ShellField.shellCubeDerivNorm k j :=
      mul_le_mul_of_nonneg_right hweight
        (ShellField.shellCubeDerivNorm_nonneg k j)
    exact hderiv.trans <| by
      calc
        (Real.sqrt d * (3 : ℝ) ^ k) *
              ShellField.shellCubeDerivNorm k j ≤
            ShellField.shellCubeValueNorm k j +
              (Real.sqrt d * (3 : ℝ) ^ k) *
                ShellField.shellCubeDerivNorm k j :=
          le_add_of_nonneg_left (ShellField.shellCubeValueNorm_nonneg k j)
        _ ≤ ShellField.shellCubeValueNorm k j +
              (Real.sqrt d * (3 : ℝ) ^ k) *
                ShellField.shellCubeDerivNorm k j +
              ((d : ℝ) * (3 : ℝ) ^ (2 * k)) *
                ShellField.shellCubeSecondDerivNorm k j :=
          le_add_of_nonneg_right
            (mul_nonneg
              (mul_nonneg (Nat.cast_nonneg d)
                (pow_nonneg (by norm_num) (2 * k)))
              (ShellField.shellCubeSecondDerivNorm_nonneg k j))
        _ = ShellField.j3Observable d k j := rfl

/-- Assumption J3 gives the exact first-derivative norm of shell `k` on its
natural cube a one-sided `Gamma₂` bound at scale `3⁻ᵏ`. -/
theorem isBigOWith_gammaSigma_shellCubeDerivNorm_coordinate
    (hJ3 : ShellLawJ3 d P) (k : ℕ) :
    IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d ↦
        ShellField.shellCubeDerivNorm k (omega k))
      (((3 : ℝ) ^ k)⁻¹) := by
  have hweighted :
      IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 2)
        (fun omega : ShellSeq d ↦
          (3 : ℝ) ^ k * ShellField.shellCubeDerivNorm k (omega k)) 1 :=
    (ShellLawJ3.isBigOWith_gammaSigma_j3Observable_coordinate hJ3 k).of_le
      (fun omega ↦ pow_mul_shellCubeDerivNorm_le_j3Observable k (omega k))
  have hinv_nonneg : 0 ≤ ((3 : ℝ) ^ k)⁻¹ := by positivity
  have hscaled := hweighted.const_mul hinv_nonneg
  have hpow_ne : (3 : ℝ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
  have hfun :
      (fun omega : ShellSeq d ↦
        ((3 : ℝ) ^ k)⁻¹ *
          ((3 : ℝ) ^ k * ShellField.shellCubeDerivNorm k (omega k))) =
        fun omega ↦ ShellField.shellCubeDerivNorm k (omega k) := by
    funext omega
    rw [← mul_assoc, inv_mul_cancel₀ hpow_ne, one_mul]
  rw [hfun, mul_one] at hscaled
  exact hscaled

/-! ## Deterministic derivative reconstruction -/

/-- The finite shell increment has derivative equal to the finite sum of the
stored shell derivatives. -/
theorem finiteShellIncrement_hasFDerivAt_sum_shellDeriv
    (omega : ShellSeq d) (n m : ℕ) (x : Vec d) :
    HasFDerivAt (finiteShellIncrement omega n m)
      (∑ k ∈ Finset.Ioc n m, ShellField.deriv (omega k) x) x := by
  have hfun :
      (finiteShellIncrement omega n m : Vec d → Mat d) =
        fun y ↦ ∑ k ∈ Finset.Ioc n m, omega k y := by
    funext y
    rw [finiteShellIncrement_apply]
    rfl
  rw [hfun]
  exact HasFDerivAt.fun_sum
    (u := Finset.Ioc n m)
    (A := fun k y ↦ omega k y)
    (A' := fun k ↦ ShellField.deriv (omega k) x)
    (x := x) fun k _ ↦ ShellField.hasFDerivAt (omega k) x

/-- The exact induced first-derivative norm is subadditive over finite
sums. -/
theorem matrixDerivativeNorm_finset_sum_le (s : Finset ℕ)
    (D : ℕ → ShellField.MatrixDerivative d) :
    ShellField.matrixDerivativeNorm (∑ k ∈ s, D k) ≤
      ∑ k ∈ s, ShellField.matrixDerivativeNorm (D k) := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty, matrixDerivativeNorm_zero]
  | cons a t ha ih =>
      rw [Finset.sum_cons, Finset.sum_cons]
      exact (ShellField.matrixDerivativeNorm_add_le _ _).trans
        (add_le_add (le_refl _) ih)

/-- At every point of `cu_n`, the exact induced norm of the reconstructed
finite-increment derivative is bounded by the measurable shell gauge. -/
theorem matrixDerivativeNorm_sum_shellDeriv_le_finiteShellDerivGauge
    (omega : ShellSeq d) (n m : ℕ) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d (n : ℤ))) :
    ShellField.matrixDerivativeNorm
        (∑ k ∈ Finset.Ioc n m, ShellField.deriv (omega k) x) ≤
      finiteShellDerivGauge n m omega := by
  refine (matrixDerivativeNorm_finset_sum_le (Finset.Ioc n m)
    (fun k ↦ ShellField.deriv (omega k) x)).trans ?_
  exact Finset.sum_le_sum fun k _ ↦
    ShellField.matrixDerivativeNorm_deriv_le_shellCubeDerivNorm n (omega k) hx

end

end SuperdiffusionCLT.Section2.Estimates.Stream
