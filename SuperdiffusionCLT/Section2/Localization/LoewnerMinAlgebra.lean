/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Ambient.BlockMatrix
public import Homogenization.Book.Ch02.Theorems.MatrixOperatorNorm
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Loewner algebra for the min{1, .} truncation and the operator-norm sandwich

Deterministic matrix algebra behind the proof of
`sigmaStarInv_mixing_minscale`, the printed lemma `l.mixing.minscale`.
Everything here is deterministic: a random
variable enters only through its value at a fixed `omega`, so no probability
theory is used.

## The quadratic form of a Loewner statement

`Homogenization.MatLoewnerLE A B` is the inequality of the quadratic forms
`x |-> (1/2) x . A x`.  The public twins `quad_le_of_matLoewnerLE` and
`matLoewnerLE_of_quad_le` turn every Loewner statement below into an inequality
between real numbers (they are the public forms of private helpers of the
coarse-grained field development).

## The operator-norm sandwich

For a symmetric real matrix `M`, the multiplication step of
`e.refined.localization.twoo` reads `|M|` in the operator norm
`Book.Ch02.matrixOperatorNorm`.  The sandwich

`M <= ||M||op . Id`  and its mirror  `-||M||op . Id <= M`,

both in Loewner order, follow from the quadratic-form bound
`|y . M y| <= ||M||op |y|^2`, which holds for an arbitrary matrix: no
symmetry, and in particular no diagonalization, is needed.  The symmetric
hypothesis `M.IsSymm` of the printed step is therefore automatic, and the
sandwich is stated without it; the consumers (`sigmaStarInvCoarse` blocks) are
symmetric.

## The min{1, .} Loewner algebra

The sibling anchor `cutoff_localization` (`Frozen/Section2/CutoffLocalization.lean`,
third and fourth Loewner conjuncts, `e.localization.s.star`) supplies,
for a balanced scalar `X'`, the pair

`(1 - X') . A <= B <= (1 + X') . A`,

with `A = s^-1_{n'}(Q)` and `B = s^-1_L(Q)`.  With the crude ellipticity bound
`A, B <= nu^-1 Id` (the sentence before `e.v.ky.energy`, proved as
`matLoewnerLE_sigmaStarInvCoarse_cutoffCube`)
and the positivity of the blocks, the pair gives the unbalanced deterministic
sandwich of steps B-C of the printed proof:

`s^-1_L(Q) <= s^-1_{n'}(Q) + nu^-1 min{1, X'} . Id`,

together with the mirrored lower bound `s^-1_{n'}(Q) <= s^-1_L(Q) + nu^-1 min{1, X'} . Id`.
The `min{1, .}` truncation is where the printed proof discharges the `nu^-2`
(not `nu^-3`) bookkeeping: for `1 <= X'` the crude bound alone absorbs the
pair, so only `min{1, X'}` survives, which is the quantity that the
interpolation step squares down.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open Homogenization
open Homogenization.Book.Ch02

noncomputable section

/-! ## The quadratic form of a Loewner statement -/

/-- Quadratic forms are additive. -/
theorem quad_add {d : ℕ} (A B : Mat d) (y : Vec d) :
    vecDot y (matVecMul (A + B) y) =
      vecDot y (matVecMul A y) + vecDot y (matVecMul B y) := by
  rw [add_matVecMul, vecDot_add_right]

/-- Quadratic forms are homogeneous. -/
theorem quad_smul {d : ℕ} (c : ℝ) (A : Mat d) (y : Vec d) :
    vecDot y (matVecMul (c • A) y) = c * vecDot y (matVecMul A y) := by
  rw [smul_matVecMul, vecDot_smul_right]

/-- The quadratic form of the zero matrix vanishes. -/
theorem quad_zero {d : ℕ} (y : Vec d) :
    vecDot y (matVecMul (0 : Mat d) y) = 0 := by
  simp [matVecMul, vecDot]

/-- The quadratic form of the identity is the squared norm. -/
theorem quad_one {d : ℕ} (y : Vec d) :
    vecDot y (matVecMul (1 : Mat d) y) = vecNormSq y := by
  have h : matVecMul (1 : Mat d) y = y := by
    funext i
    simp [matVecMul, Matrix.one_apply]
  rw [h]
  rfl

/-- **Public quadratic-form reading of Loewner order**: the public twin of the
private `quad_le_of_matLoewnerLE` of the coarse-grained field development. -/
theorem quad_le_of_matLoewnerLE {d : ℕ} {A B : Mat d} (h : MatLoewnerLE A B)
    (y : Vec d) : vecDot y (matVecMul A y) ≤ vecDot y (matVecMul B y) := by
  linarith only [h y]

/-- **Public builder of Loewner order from quadratic forms**: the public twin
of the private `matLoewnerLE_of_quad_le` of
the coarse-grained field development. -/
theorem matLoewnerLE_of_quad_le {d : ℕ} {A B : Mat d}
    (h : ∀ y : Vec d, vecDot y (matVecMul A y) ≤ vecDot y (matVecMul B y)) :
    MatLoewnerLE A B := fun y => by linarith only [h y]

/-! ## The operator-norm sandwich -/

/-- The quadratic form of an arbitrary real matrix is bounded in absolute value
by the operator norm times the squared norm of the vector. -/
theorem abs_quad_le_matrixOperatorNorm_mul_vecNormSq {d : ℕ} (M : Mat d) (y : Vec d) :
    |vecDot y (matVecMul M y)| ≤ matrixOperatorNorm M * vecNormSq y := by
  have hcs := sq_vecDot_le_vecNormSq_mul_vecNormSq y (matVecMul M y)
  have hop := vecNormSq_matVecMul_le_matrixOperatorNorm_sq_mul_vecNormSq M y
  have hpos : 0 ≤ matrixOperatorNorm M * vecNormSq y :=
    mul_nonneg (matrixOperatorNorm_nonneg M) (vecNormSq_nonneg y)
  have hsq : vecDot y (matVecMul M y) ^ 2 ≤
      (matrixOperatorNorm M * vecNormSq y) ^ 2 := by
    have h1 : vecDot y (matVecMul M y) ^ 2 ≤
        matrixOperatorNorm M ^ 2 * vecNormSq y ^ 2 := by
      calc vecDot y (matVecMul M y) ^ 2
          ≤ vecNormSq y * vecNormSq (matVecMul M y) := hcs
        _ ≤ vecNormSq y * (matrixOperatorNorm M ^ 2 * vecNormSq y) :=
          mul_le_mul_of_nonneg_left hop (vecNormSq_nonneg y)
        _ = matrixOperatorNorm M ^ 2 * vecNormSq y ^ 2 := by ring
    calc vecDot y (matVecMul M y) ^ 2
        ≤ matrixOperatorNorm M ^ 2 * vecNormSq y ^ 2 := h1
      _ = (matrixOperatorNorm M * vecNormSq y) ^ 2 := by rw [mul_pow]
  exact abs_le_of_sq_le_sq hsq hpos

/-- **The operator-norm sandwich**: a real matrix is dominated in Loewner order
by its operator norm times the identity.  This is the deterministic sandwich
behind the multiplication step of `e.refined.localization.twoo`;
the printed hypothesis `M.IsSymm` is not needed, since the quadratic form of a
real matrix is controlled by the operator norm of the matrix itself. -/
theorem matLoewnerLE_matrixOperatorNorm_smul_one {d : ℕ} {M : Mat d} :
    MatLoewnerLE M (matrixOperatorNorm M • (1 : Mat d)) := by
  refine matLoewnerLE_of_quad_le fun y => ?_
  have habs := abs_quad_le_matrixOperatorNorm_mul_vecNormSq M y
  have hle : vecDot y (matVecMul M y) ≤ matrixOperatorNorm M * vecNormSq y :=
    (abs_le.1 habs).2
  have hone : vecDot y (matVecMul (matrixOperatorNorm M • (1 : Mat d)) y)
      = matrixOperatorNorm M * vecNormSq y := by
    rw [quad_smul, quad_one]
  linarith only [hle, hone]

/-! ## The min{1, .} Loewner algebra from the anchored pair -/

/-- **The min{1, .} Loewner algebra, upper half.** From the anchored pair
`(1 - t) . A <= B <= (1 + t) . A` together with the crude ellipticity bounds
`A <= c . Id` and `B <= c . Id` and the positivity of `A`, the upper member of
the pair satisfies the truncated deterministic sandwich

`B <= A + (c * min 1 t) . Id`,

with `c = nu^-1` in the application to `s^-1_L(Q)` and `s^-1_{n'}(Q)` (steps B-C of
the printed proof): the case `1 <= t` is absorbed by the crude bound
on `B` alone, so only `min{1, t}` survives. -/
theorem matLoewnerLE_add_min_smul_one_of_pair {d : ℕ} {A B : Mat d} {c t : ℝ}
    (ht : 0 ≤ t)
    (hUp : MatLoewnerLE B ((1 + t) • A))
    (hA : MatLoewnerLE A (c • (1 : Mat d)))
    (hB : MatLoewnerLE B (c • (1 : Mat d)))
    (hApos : MatLoewnerLE 0 A) :
    MatLoewnerLE B (A + (c * min 1 t) • (1 : Mat d)) := by
  refine matLoewnerLE_of_quad_le fun y => ?_
  rcases le_total 1 t with h1le | htle
  · -- `1 <= t`: `min 1 t = 1`, and the crude bound on `B` alone absorbs the pair
    have hmin : min 1 t = 1 := min_eq_left h1le
    rw [hmin, mul_one]
    have hone : vecDot y (matVecMul (c • (1 : Mat d)) y) = c * vecNormSq y := by
      rw [quad_smul, quad_one]
    have hBq : vecDot y (matVecMul B y) ≤ c * vecNormSq y :=
      (quad_le_of_matLoewnerLE hB y).trans (by rw [hone])
    have hAposq : 0 ≤ vecDot y (matVecMul A y) := by
      have h0 := hApos y
      linarith only [h0, quad_zero y]
    have hgoal : vecDot y (matVecMul (A + c • (1 : Mat d)) y)
        = vecDot y (matVecMul A y) + c * vecNormSq y := by
      rw [add_matVecMul, vecDot_add_right, quad_smul, quad_one]
    linarith only [hBq, hAposq, hgoal]
  · -- `t <= 1`: `min 1 t = t`, and the pair gives the term `t . A <= t . c . Id`
    have hmin : min 1 t = t := min_eq_right htle
    have hone : vecDot y (matVecMul (c • (1 : Mat d)) y) = c * vecNormSq y := by
      rw [quad_smul, quad_one]
    have hAq : vecDot y (matVecMul A y) ≤ c * vecNormSq y :=
      (quad_le_of_matLoewnerLE hA y).trans (by rw [hone])
    have hUpq : vecDot y (matVecMul B y) ≤ (1 + t) * vecDot y (matVecMul A y) := by
      refine (quad_le_of_matLoewnerLE hUp y).trans ?_
      rw [quad_smul]
    have hstep : vecDot y (matVecMul B y) ≤
        vecDot y (matVecMul A y) + t * (c * vecNormSq y) := by
      have h1 : (1 + t) * vecDot y (matVecMul A y)
          = vecDot y (matVecMul A y) + t * vecDot y (matVecMul A y) := by
        rw [add_mul, one_mul]
      have h2 : t * vecDot y (matVecMul A y) ≤ t * (c * vecNormSq y) :=
        mul_le_mul_of_nonneg_left hAq ht
      linarith only [hUpq, h1, h2]
    have hgoal : vecDot y (matVecMul (A + (c * min 1 t) • (1 : Mat d)) y)
        = vecDot y (matVecMul A y) + (c * min 1 t) * vecNormSq y := by
      rw [add_matVecMul, vecDot_add_right, quad_smul, quad_one]
    have h3 : (c * min 1 t) * vecNormSq y = t * (c * vecNormSq y) := by
      rw [hmin]
      ring
    linarith only [hstep, hgoal, h3]

/-! ## Measurability of the truncated scalar -/

/-- The truncated balanced scalar `omega |-> min 1 (X omega)` is measurable. -/
theorem measurable_min_one {Ω : Type} [MeasurableSpace Ω] {X : Ω → ℝ}
    (hX : Measurable X) : Measurable (fun omega => min 1 (X omega)) :=
  measurable_const.min hX

end