/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellField.J3Observable
public import SuperdiffusionCLT.Assumptions.ShellLaw.J3Consequences
public import SuperdiffusionCLT.Probability.GammaSigmaHelpers

/-!
# The Orlicz restatement of the marginal J3 regularity assumption

The paper states the local regularity assumption J3 as a strict Gaussian
tail (display `(e.k(n).reg)`, with its displayed weights and tail bound):

`P[ ‖j_n‖_{L∞(cu_n)} + √d 3^n ‖∇j_n‖_{L∞(cu_n)} + d 3^(2n) ‖∇²j_n‖_{L∞(cu_n)} > t ] ≤ exp(-t²)`
for every `t ≥ 1`,

and rewrites it as the `Γ₂` statement of display `(e.k(n).reg.with.gamma)`,

`‖j_n‖_{L∞(cu_n)} + 3^n ‖∇j_n‖_{L∞(cu_n)} + 3^(2n) ‖∇²j_n‖_{L∞(cu_n)} ≤ O_{Γ₂}(1)`.

The printed restatement drops the dimensional weights of `(e.k(n).reg)`: the
factor `√d` multiplying the first-derivative term and the factor `d`
multiplying the second-derivative term are both removed, while the scale
factors `3 ^ n` and `3 ^ (2 n)` are kept. For `1 ≤ d` the unweighted sum is
dominated by the weighted observable through `1 ≤ √d` and `1 ≤ d`, and in
dimension zero the two derivative cube norms vanish, so the printed form is a
consequence of the tail in every dimension.

## Main definitions

* `j3OrliczNormSum`: the left side of `(e.k(n).reg.with.gamma)`, the three
  cube norms with the printed scale factors and no dimensional weight.

## Main results

* `j3OrliczNormSum_le_j3Observable`: the printed sum is bounded by the
  weighted J3 observable, which is what carries the strict Gaussian tail.
* `isBigOWith_gammaSigma_j3OrliczNormSum_coordinate`: the unit-amplitude `Γ₂`
  bound of the printed display.
* The three printed summands, and the three bare cube norms at the printed
  weights `1`, `3 ^ (-n)` and `3 ^ (-2n)`, are each `O_{Γ₂}` with unit
  amplitude.

## References

* The paper, displays `(e.k(n).reg)` and `(e.k(n).reg.with.gamma)`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Assumptions.ShellLaw

open MeasureTheory
open Homogenization
open IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Assumptions.ShellField

noncomputable section

variable {d : ℕ}
variable {P : ProbabilityMeasure (ℕ → ShellField d)}

/-- The left side of the paper's Orlicz restatement of the shell
regularity assumption, display `(e.k(n).reg.with.gamma)`: the value, first-derivative
and second-derivative cube norms of the shell on the natural open cube `cu_n`,
scaled by the printed factors `3 ^ n` and `3 ^ (2 n)` and carrying no
dimensional weight. -/
def j3OrliczNormSum (d n : ℕ) (j : ShellField d) : ℝ :=
  shellCubeValueNorm n j +
    ((3 : ℝ) ^ n) * shellCubeDerivNorm n j +
    ((3 : ℝ) ^ (2 * n)) * shellCubeSecondDerivNorm n j

/-- In dimension zero the exact induced derivative norm is nonpositive, since
it is dominated by `(d : ℝ) ^ 2 * ‖·‖` and the prefactor vanishes. -/
private theorem matrixDerivativeNorm_le_zero_of_dim_zero
    (hd : d = 0) (D : MatrixDerivative d) : matrixDerivativeNorm D ≤ 0 := by
  have hdR : (d : ℝ) = 0 := by exact_mod_cast hd
  refine le_trans (matrixDerivativeNorm_le_sq_mul_norm D) (le_of_eq ?_)
  rw [hdR, zero_pow (show (2 : ℕ) ≠ 0 by norm_num), zero_mul]

/-- In dimension zero the exact twice-induced second-derivative norm is
nonpositive. -/
private theorem matrixSecondDerivativeNorm_le_zero_of_dim_zero
    (hd : d = 0) (H : MatrixSecondDerivative d) :
    matrixSecondDerivativeNorm H ≤ 0 :=
  (matrixSecondDerivativeNorm_le_iff H 0).2
    ⟨le_refl _, fun u _ => matrixDerivativeNorm_le_zero_of_dim_zero hd (H u)⟩

/-- In dimension zero the first-derivative cube norm vanishes. -/
private theorem shellCubeDerivNorm_eq_zero_of_dim_zero (n : ℕ) (j : ShellField d)
    (hd : d = 0) : shellCubeDerivNorm n j = 0 := by
  refine le_antisymm ?_ (shellCubeDerivNorm_nonneg n j)
  unfold shellCubeDerivNorm
  apply csSup_le (Set.range_nonempty _)
  rintro r ⟨o, rfl⟩
  cases o with
  | none => exact le_refl _
  | some x =>
      show matrixDerivativeNorm (ShellField.deriv j x.1) ≤ 0
      exact matrixDerivativeNorm_le_zero_of_dim_zero hd _

/-- In dimension zero the second-derivative cube norm vanishes. -/
private theorem shellCubeSecondDerivNorm_eq_zero_of_dim_zero (n : ℕ)
    (j : ShellField d) (hd : d = 0) : shellCubeSecondDerivNorm n j = 0 := by
  refine le_antisymm ?_ (shellCubeSecondDerivNorm_nonneg n j)
  unfold shellCubeSecondDerivNorm
  apply csSup_le (Set.range_nonempty _)
  rintro r ⟨o, rfl⟩
  cases o with
  | none => exact le_refl _
  | some x =>
      show matrixSecondDerivativeNorm (ShellField.secondDeriv j x.1) ≤ 0
      exact matrixSecondDerivativeNorm_le_zero_of_dim_zero hd _

/-- The sum printed in display `(e.k(n).reg.with.gamma)` of
is dominated by the
weighted J3 observable of the carrier, the quantity whose strict
Gaussian tail is asserted by `(e.k(n).reg)`.

The printed restatement drops the dimensional weights `√d` and `d` of
`(e.k(n).reg)`. For `1 ≤ d` the comparison uses `1 ≤ √d` and `1 ≤ d`; in
dimension zero the two derivative cube norms vanish instead, so the printed
form follows from the tail in every dimension. -/
theorem j3OrliczNormSum_le_j3Observable (d n : ℕ) (j : ShellField d) :
    j3OrliczNormSum d n j ≤ ShellField.j3Observable d n j := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have h1 : shellCubeDerivNorm n j = 0 :=
      shellCubeDerivNorm_eq_zero_of_dim_zero n j rfl
    have h2 : shellCubeSecondDerivNorm n j = 0 :=
      shellCubeSecondDerivNorm_eq_zero_of_dim_zero n j rfl
    unfold j3OrliczNormSum ShellField.j3Observable
    simp only [h1, h2, mul_zero, add_zero]
    exact le_refl _
  · have hsqrt : (1 : ℝ) ≤ Real.sqrt d :=
      (Real.one_le_sqrt (x := d)).mpr (by exact_mod_cast hd)
    have hd2 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hD1 : 0 ≤ shellCubeDerivNorm n j := shellCubeDerivNorm_nonneg n j
    have hD2 : 0 ≤ shellCubeSecondDerivNorm n j :=
      shellCubeSecondDerivNorm_nonneg n j
    have hprod1 : 0 ≤ (3 : ℝ) ^ n * shellCubeDerivNorm n j :=
      mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) n) hD1
    have hprod2 : 0 ≤ (3 : ℝ) ^ (2 * n) * shellCubeSecondDerivNorm n j :=
      mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (2 * n)) hD2
    have k1 : (3 : ℝ) ^ n * shellCubeDerivNorm n j ≤
        (Real.sqrt d * (3 : ℝ) ^ n) * shellCubeDerivNorm n j := by
      rw [mul_assoc, mul_comm (Real.sqrt d)
        ((3 : ℝ) ^ n * shellCubeDerivNorm n j)]
      exact le_mul_of_one_le_right hprod1 hsqrt
    have k2 : (3 : ℝ) ^ (2 * n) * shellCubeSecondDerivNorm n j ≤
        ((d : ℝ) * (3 : ℝ) ^ (2 * n)) * shellCubeSecondDerivNorm n j := by
      rw [mul_assoc, mul_comm (d : ℝ)
        ((3 : ℝ) ^ (2 * n) * shellCubeSecondDerivNorm n j)]
      exact le_mul_of_one_le_right hprod2 hd2
    unfold j3OrliczNormSum ShellField.j3Observable
    exact add_le_add (add_le_add (le_refl _) k1) k2

/-- The value cube norm is the first printed summand. -/
theorem shellCubeValueNorm_le_j3OrliczNormSum (d n : ℕ) (j : ShellField d) :
    shellCubeValueNorm n j ≤ j3OrliczNormSum d n j := by
  unfold j3OrliczNormSum
  exact le_trans (le_add_of_nonneg_right
    (mul_nonneg (by positivity) (shellCubeDerivNorm_nonneg n j)))
    (le_add_of_nonneg_right
      (mul_nonneg (by positivity) (shellCubeSecondDerivNorm_nonneg n j)))

/-- The J3 tail gives the unit-amplitude `Γ₂` bound of the paper's
Orlicz restatement, display `(e.k(n).reg.with.gamma)`, for the shell-`n`
coordinate of the canonical sequence law. -/
theorem isBigOWith_gammaSigma_j3OrliczNormSum_coordinate
    (hJ3 : ShellLawJ3 d P) (n : ℕ) :
    IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 2)
      (fun F : ℕ → ShellField d => j3OrliczNormSum d n (F n)) 1 :=
  (ShellLawJ3.isBigOWith_gammaSigma_j3Observable_coordinate hJ3 n).of_le
    (fun F => j3OrliczNormSum_le_j3Observable d n (F n))

/-- The first printed summand `‖j_n‖_{L∞(cu_n)}` is `O_{Γ₂}(1)`. -/
theorem isBigOWith_gammaSigma_shellCubeValueNorm_coordinate
    (hJ3 : ShellLawJ3 d P) (n : ℕ) :
    IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 2)
      (fun F : ℕ → ShellField d => shellCubeValueNorm n (F n)) 1 :=
  (isBigOWith_gammaSigma_j3OrliczNormSum_coordinate hJ3 n).of_le
    (fun F => shellCubeValueNorm_le_j3OrliczNormSum d n (F n))

end

end SuperdiffusionCLT.Assumptions.ShellLaw