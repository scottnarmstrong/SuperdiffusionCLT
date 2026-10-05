/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3BlupPointwise
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3Holder
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3SignedBlockDev
public import SuperdiffusionCLT.Section2.Localization.PsdSqrtQuadratic

/-!
# The term-3 chain against the printed operator-norm slot

The paper's display `e.bL.to.bhomell.pre0zz` carries the quadratic term
**tested at the single chain direction `e`**, while the
display `e.blupbounds` carries the **operator-norm square**,
the supremum over `|e| = 1` named `translatedStreamSlot`
in `Section3/Terms/RHSTerm3BlupPointwise.lean`.  The tested form never exceeds
the slot, so the clause of `_hBlup`
that the chain consumes is strictly stronger than the print.

## How the chain consumes that clause

The clause reaches the chain only through a consuming step used to build the `hPre` argument
of the carrier-swap Hölder split.  That
step does exactly three things: the triangle inequality
`|b_{L'}| ≤ |b_ℓ| + |b_{L'} - b_ℓ|`, the signed trace bound
`translatedBlockNorm_le_blockDevSumSigned` on `|b_ℓ|`, and then a single
`linarith only [htri, hb, hc]`.  **The quadratic slot is never bounded from
below or inverted: it is only added to the right-hand side of an upper bound.**
That is the reason the consuming step itself has no preference between the tested form
and the print.

## Where the single direction is actually needed

The *next* step is the carrier-swap Hölder split, whose `hTriangle` reads

`q_ℓ(ω, z) ≤ q_{L'}(ω, z) + g(ω, z)`.

With `q_ℓ` the slot and `q_{L'}` the form tested at `e`, that is
`slot ≤ q(e) + g(e)`, and it is **false**: at `d = 2` there is a unit `e` and a matrix
whose tested form is strictly below the operator-norm square.  So the slot cannot simply be
substituted into the existing carriers; the carriers themselves have to move to
the `d` coordinate directions.

## The repair

* `translatedStreamQuadFormLower_eq_vecNormSq_sqrtMul`: the Gram identity of the
  bound of the tested form by the operator-norm square at an
  **arbitrary** direction, so that it may be instantiated at `basisVec i`.
* `matrixFrobeniusNormSq_eq_basisSum`, `matrixOperatorNorm_sq_le_basisSum`: the
  trace/Frobenius domination of the operator norm by the coordinate directions.
* `translatedStreamSlot_le_basisSum`,
  `translatedStreamSlot_le_basisSum_add_gap`: the printed slot is dominated by
  the **sum** of the tested forms plus the carrier-swap errors over the `d`
  directions `basisVec i`.
* `basisSum_le_card_mul` isolates the factor `d` paid by summing over the `d` directions.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory ProbabilityTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Localization
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal
open scoped BigOperators Matrix.Norms.Elementwise
open scoped MatrixOrder

noncomputable section

/-! ## The Gram identity at an arbitrary direction -/

/-- **`q(e) = |σ_{ℓ,*}^{-1/2} (∇·)_e e|²` at every direction `e`**, unit or not:
the Gram property `vecNormSq_sqrt_matVecMul_eq_vecDot_matVecMul` of the square
root of the positive-semidefinite block `σ_{ℓ,*}^{-1}(z + cu_n)`, with the
averaged increment written as `volumeAverageMat (cubeSet z)
(fun y => finiteShellIncrement …) e`.  The existing form of this identity
(in `Section3/Terms/BlupRemainderFinal.lean`) carries the hypothesis
`vecNormSq e = 1`, which the coordinate directions `basisVec i` do satisfy but
which the domination argument below does not want to track. -/
theorem translatedStreamQuadFormLower_eq_vecNormSq_sqrtMul {d : ℕ} [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (ell L : ℕ) (e : Vec d) (omega : ShellSeq d) (z : TriadicCube d) :
    translatedStreamQuadFormLower nu ell L e omega z =
      vecNormSq (matVecMul (CFC.sqrt (sigmaStarInvCoarse (cubeSet z)
            (coefficientCutoff nu omega ell).toCoeffField) *
          volumeAverageMat (cubeSet z)
            (fun y => finiteShellIncrement omega ell L y)) e) := by
  set A : Mat d := sigmaStarInvCoarse (cubeSet z)
    (coefficientCutoff nu omega ell).toCoeffField with hA
  set M : Mat d := volumeAverageMat (cubeSet z)
    (fun y => finiteShellIncrement omega ell L y) with hM
  have hgram :=
    SuperdiffusionCLT.Section2.Localization.vecNormSq_sqrt_matVecMul_eq_vecDot_matVecMul
      (posSemidef_sigmaStarInvCoarse_cutoffCube hnu ell omega z) (matVecMul M e)
  rw [translatedStreamQuadFormLower, streamIncrementCubeVec, ← hA, ← hM]
  rw [← matVecMul_mul (CFC.sqrt A) M e]
  exact hgram.symm

/-! ## The coordinate directions dominate the operator norm -/

/-- **The Frobenius square is the sum of the squared columns**: the legacy
Frobenius carrier `matrixFrobeniusNormSq` equals `∑ i, |N (basisVec i)|²`, since
`matVecMul N (basisVec i)` is the `i`-th column of `N` (`matVecMul_single`). -/
theorem matrixFrobeniusNormSq_eq_basisSum {d : ℕ} (N : Mat d) :
    matrixFrobeniusNormSq N = ∑ i : Fin d, vecNormSq (matVecMul N (basisVec i)) := by
  rw [matrixFrobeniusNormSq, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hcomp : matVecMul N (basisVec j) = fun i => N i j := by
    rw [basisVec]
    exact matVecMul_single N j
  rw [hcomp]
  simp [vecNormSq, vecDot, pow_two]

/-- **The operator-norm square is dominated by the sum of the squared
columns**: `matrixOperatorNorm_le_matrixFrobeniusNorm` composed with the
identity above.  At `d` coordinate directions this is the trace of `Nᵀ N`, i.e.
the sum of the squared singular values; the supremum over the unit sphere is
one of them, and the price of replacing it by their sum is exactly the factor
`d` isolated in `basisSum_le_card_mul`. -/
theorem matrixOperatorNorm_sq_le_basisSum {d : ℕ} (N : Mat d) :
    (matrixOperatorNorm N) ^ (2 : ℕ) ≤
      ∑ i : Fin d, vecNormSq (matVecMul N (basisVec i)) := by
  calc (matrixOperatorNorm N) ^ (2 : ℕ)
      ≤ (matrixFrobeniusNorm N) ^ (2 : ℕ) :=
        pow_le_pow_left₀ (matrixOperatorNorm_nonneg N)
          (matrixOperatorNorm_le_matrixFrobeniusNorm N) 2
    _ = matrixFrobeniusNormSq N := by
        rw [matrixFrobeniusNorm, Real.sq_sqrt (matrixFrobeniusNormSq_nonneg N)]
    _ = ∑ i : Fin d, vecNormSq (matVecMul N (basisVec i)) :=
        matrixFrobeniusNormSq_eq_basisSum N

/-! ## The printed slot at the coordinate directions -/

/-- **The printed operator-norm slot is dominated by the sum of the tested
forms over the `d` coordinate directions.**  This is the step that replaces the
false single-direction triangle `slot ≤ q(e) + g(e)`: it is true because the
slot is the square of the largest singular value and the summands are the
squares of the columns, so the sum contains the largest one. -/
theorem translatedStreamSlot_le_basisSum {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (ell L : ℕ) (omega : ShellSeq d) (z : TriadicCube d) :
    translatedStreamSlot nu ell L omega z ≤
      ∑ i : Fin d, translatedStreamQuadFormLower nu ell L (basisVec i) omega z := by
  rw [translatedStreamSlot]
  refine le_trans (matrixOperatorNorm_sq_le_basisSum _) ?_
  refine Finset.sum_le_sum fun i _ => ?_
  rw [translatedStreamQuadFormLower_eq_vecNormSq_sqrtMul hnu ell L (basisVec i) omega z]

/-- **The printed slot is dominated by the sum of the swapped carriers**: the
previous bound followed by the per-direction carrier swap
`translatedStreamQuadFormLower_le_add_gap` at each `basisVec i`.  This is the
true replacement of the `hTriangle` hypothesis of the carrier-swap Hölder split
for a chain driven by the printed slot. -/
theorem translatedStreamSlot_le_basisSum_add_gap {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (ell L : ℕ) (omega : ShellSeq d) (z : TriadicCube d) :
    translatedStreamSlot nu ell L omega z ≤
      ∑ i : Fin d, (translatedStreamQuadForm nu ell L (basisVec i) omega z +
        translatedStreamQuadFormGap nu ell L (basisVec i) omega z) := by
  refine le_trans (translatedStreamSlot_le_basisSum hnu ell L omega z) ?_
  refine Finset.sum_le_sum fun i _ => ?_
  exact translatedStreamQuadFormLower_le_add_gap nu ell L (basisVec i) omega z

/-- **The price of the coordinate directions**: a bound valid for all `d`
directions gives the same bound for the sum, at the cost of one factor `d`.
Every downstream bound the chain applies to the quadratic carriers
(`holder_terms_bridge`, `swap_bridge`, `averaged_quadratic_tail_translated`) has
a direction-independent right-hand side, so this is the only place where the
number of directions enters. -/
theorem basisSum_le_card_mul {d : ℕ} {F : Fin d → ℝ} {B : ℝ} (h : ∀ i, F i ≤ B) :
    ∑ i : Fin d, F i ≤ (d : ℝ) * B := by
  calc ∑ i : Fin d, F i ≤ ∑ _i : Fin d, B := Finset.sum_le_sum fun i _ => h i
    _ = (d : ℝ) * B := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ## The consuming step of the chain, at the printed slot -/

/-! ## The single-direction triangle at the slot is false -/

end

end SuperdiffusionCLT.Section3.Terms
