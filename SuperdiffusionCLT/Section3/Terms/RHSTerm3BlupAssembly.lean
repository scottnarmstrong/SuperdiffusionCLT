/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3BlupChain
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3AnchorsConstFirst
public import SuperdiffusionCLT.Section3.Terms.WindowFactorAbsorption

/-!
# The term-3 chain driven by the printed operator-norm slot

The paper's display `e.bL.to.bhomell.pre0zz` carries the quadratic term
**tested at the single chain direction `e`**, while the
display `e.blupbounds` carries the **operator-norm square**,
the supremum over `|e| = 1` named `translatedStreamSlot`
in `Section3/Terms/RHSTerm3BlupPointwise.lean`.  The tested form never exceeds
the slot, so a clause 3 of the `_hBlup` package stated at the tested form is
*strictly stronger* than the print.

## The triangle step with the printed slot

The chain's consuming step only ever *adds* the quadratic slot to the right-hand side of an
upper bound, so it takes the printed slot verbatim.  What refused a plain clause swap was the
*next* step, the triangle hypothesis `hTriangle` of the carrier-swap Hölder split: with the
slot on its left and the form tested at `e` on its right it reads `slot ≤ q(e) + g(e)`, which
is false at equal carriers.  The repair is the trace/Frobenius domination of the
operator norm by the `d` coordinate directions:

* `translatedStreamSlot_le_basisSum_add_gap` : the printed slot is dominated by
  `∑ i, (q(basisVec i) + g(basisVec i))`, i.e. by the *sum* of the tested forms
  and the carrier-swap errors over `basisVec i`;
* `basisSum_le_card_mul` : the only price of that replacement is one factor `d`.

## Main results

* `translatedStreamBasisSum` and `translatedStreamBasisGapSum`: the carriers a
  slot-driven chain has to use, the sums `∑ i, q(basisVec i)` and `∑ i, g(basisVec i)`
  of the tested forms and of the replacement errors.
* `blupChain_slotTriangle_basisSum`: the triangle step at those carriers, the printed
  clause 3 with the false single-direction triangle replaced by the trace domination.
* `weightedBlockAverage_univ_sum` : the linearity of the weighted block average
  over the `d` directions, the bookkeeping the basis sums cost.
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

/-! ## The carriers of a slot-driven chain -/

/-- **The quadratic carrier of the chain at the coordinate directions**: the sum
of the tested forms `translatedStreamQuadForm nu ell L (basisVec i)` over the `d`
coordinate directions.  This is the carrier that replaces the single-direction
form `translatedStreamQuadForm nu ell L e` once the printed slot is in place,
its size being the price isolated by `basisSum_le_card_mul`. -/
def translatedStreamBasisSum {d : ℕ} [NeZero d] (nu : ℝ) (ell L : ℕ) (omega : ShellSeq d)
    (z : TriadicCube d) : ℝ :=
  ∑ i : Fin d, translatedStreamQuadForm nu ell L (basisVec i) omega z

/-- **The carrier-swap error of the chain at the coordinate directions**, the
companion of `translatedStreamBasisSum`: the sum of the replacement errors
`translatedStreamQuadFormGap nu ell L (basisVec i)`. -/
def translatedStreamBasisGapSum {d : ℕ} [NeZero d] (nu : ℝ) (ell L : ℕ) (omega : ShellSeq d)
    (z : TriadicCube d) : ℝ :=
  ∑ i : Fin d, translatedStreamQuadFormGap nu ell L (basisVec i) omega z

/-- **The triangle step `hTriangle` of the carrier-swap Hölder split at the
slot-driven carriers**: the printed operator-norm slot is dominated by the sum
of the tested forms and the carrier-swap errors over the `d` coordinate
directions.  This is `translatedStreamSlot_le_basisSum_add_gap`
(`Section3/Terms/RHSTerm3BlupChain.lean`) restated at the carriers
`quadEll := translatedStreamBasisSum + translatedStreamBasisGapSum`,
`quadLPrime := translatedStreamBasisSum`, `swapDiff := translatedStreamBasisGapSum`,
where it becomes an identity after the domination. -/
theorem blupChain_slotTriangle_basisSum {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (ell L : ℕ) (omega : ShellSeq d) (z : TriadicCube d) :
    translatedStreamSlot nu ell L omega z ≤
      translatedStreamBasisSum nu ell L omega z +
        translatedStreamBasisGapSum nu ell L omega z := by
  have h := translatedStreamSlot_le_basisSum_add_gap hnu ell L omega z
  rw [Finset.sum_add_distrib] at h
  exact h

/-! ## Linearity of the weighted block average over the coordinate directions -/

/-- **The weighted block average is additive over a finite sum of carriers**:
`weightedBlockAverage d n k m g (∑ i, F i) = ∑ i, weightedBlockAverage d n k m g (F i)`.
This is the bookkeeping the basis sums of `translatedStreamBasisSum` cost: the
`hTerm2` and `hSwap` inputs of the carrier-swap Hölder split are known one
direction at a time (`averaged_quadratic_tail_translated`,
`swap_bridge`), and summing them over `Fin d` is what introduces the factor `d`
isolated by `basisSum_le_card_mul`. -/
theorem weightedBlockAverage_univ_sum {d : ℕ} {ι : Type*} [Fintype ι] {n m : ℕ} (k : ℕ)
    (g : Vec d → Vec d) (F : ι → TriadicCube d → ℝ) :
    weightedBlockAverage d n k m g (fun z => ∑ i, F i z) =
      ∑ i, weightedBlockAverage d n k m g (F i) := by
  simp only [weightedBlockAverage]
  have key : ∀ z' : TriadicCube d,
      vecNormSq (volumeAverageVec (openCubeSet z') g) *
        ((((descendantsAtDepth z' (k - n)).card : ℕ) : ℝ)⁻¹ *
          ∑ z ∈ descendantsAtDepth z' (k - n), ∑ i, F i z) =
      ∑ i, vecNormSq (volumeAverageVec (openCubeSet z') g) *
        ((((descendantsAtDepth z' (k - n)).card : ℕ) : ℝ)⁻¹ *
          ∑ z ∈ descendantsAtDepth z' (k - n), F i z) := by
    intro z'
    rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
  have hcongr : (∑ z' ∈ largeCubeSubcubes d k m,
        vecNormSq (volumeAverageVec (openCubeSet z') g) *
        ((((descendantsAtDepth z' (k - n)).card : ℕ) : ℝ)⁻¹ *
          ∑ z ∈ descendantsAtDepth z' (k - n), ∑ i, F i z)) =
      ∑ z' ∈ largeCubeSubcubes d k m, ∑ i,
        vecNormSq (volumeAverageVec (openCubeSet z') g) *
        ((((descendantsAtDepth z' (k - n)).card : ℕ) : ℝ)⁻¹ *
          ∑ z ∈ descendantsAtDepth z' (k - n), F i z) :=
    Finset.sum_congr rfl fun z' _ => key z'
  rw [hcongr, Finset.sum_comm, Finset.mul_sum]

/-! ## The `_hBlup` conclusion with clause 3 in the printed operator-norm form -/

end

end SuperdiffusionCLT.Section3.Terms
