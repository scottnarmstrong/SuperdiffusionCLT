/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.CutoffMinimizerClause
public import SuperdiffusionCLT.Section2.CoarseGraining.Correspondence
public import SuperdiffusionCLT.Section2.CoarseGraining.CutoffCorrespondence
public import SuperdiffusionCLT.Section2.CoarseGraining.SkewShiftCutoff

/-!
# The provable inputs of the minimizers clause

The third conjunct of the statement `Frozen.Section2.cutoff_localization`
takes several named hypotheses.  This module proves those inputs
that are genuine consequences of the standing data:

* `gradientDifference_integrableOn`: the integrability premise `hVint` for
  arbitrary bounded `U` and arbitrary pair of `AHarmonicFunction`s: each
  component of the gradient of an `H¹` function is square-integrable on `U`
  (`H1Function.gradMemL2`), the difference of two such components is again
  square-integrable (`MemLp.sub`), and the squared norm is the sum of the
  component squares.
* `responseJ_centeredPair_add_nonneg`: the nonnegativity premise `hS`.  The
  averaged carrier `e.Jaas.matform` (`responseJ_eq_blockQuadratic`) writes each
  response functional as half of the coarse block form at the offset `(-p, q)`
  minus the cross term, so the sum of the two responses plus `2 p·q` is half
  the sum of two positive semidefinite quadratic forms
  (`zero_le_blockVecDot_coarseBlockMatrix`), one for the level-`m` cutoff field
  and one for the volume-average-centered field, reached on the Chapter 2
  carrier through `coefficientCutoffCoeffOn` and the constant anti-symmetric
  shift `addConstSkewCoeffOn` by `-(k_L - k_m)_U`.

## Main results

* `gradientDifference_integrableOn`: the squared gradient difference of any
  pair of `AHarmonicFunction`s on a bounded set is integrable.
* `responseJ_centeredPair_add_nonneg`: the printed energy scale is
  nonnegative.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.CoarseGraining
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Terms
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## The integrability of the squared gradient difference -/

/-- **The integrability premise `hVint`** of the third clause: the squared norm
of the gradient difference of any two `AHarmonicFunction`s (any two coefficient
fields) is integrable on any set `U`.  Each component of the gradient of an
`H¹` function is square-integrable (`H1Function.gradMemL2`), the difference of
two square-integrable functions is square-integrable (`MemLp.sub`), and the
squared Euclidean norm is the sum of the component squares. -/
theorem gradientDifference_integrableOn (U : Set (Vec d)) {a b : CoeffField d}
    (u : AHarmonicFunction a U) (v : AHarmonicFunction b U) :
    IntegrableOn (fun x => vecNormSq (u.toH1.grad x - v.toH1.grad x)) U volume := by
  have hcomp : ∀ i : Fin d,
      Integrable (fun x => (u.toH1.grad x i - v.toH1.grad x i) ^ 2)
        (volume.restrict U) :=
    fun i => ((u.toH1.gradMemL2 i).sub (v.toH1.gradMemL2 i)).integrable_sq
  have hfun : (fun x => vecNormSq (u.toH1.grad x - v.toH1.grad x)) =
      fun x => ∑ i, (u.toH1.grad x i - v.toH1.grad x i) ^ 2 := by
    funext x
    simp only [vecNormSq, vecDot, pow_two, Pi.sub_apply]
  rw [hfun]
  exact MeasureTheory.integrable_finsetSum Finset.univ (fun i _ => hcomp i)

/-! ## The nonnegativity of the printed energy scale -/

/-- The volume average of the finite shell increment is anti-symmetric. -/
private theorem matTranspose_volumeAverageMat_finiteShellIncrement
    (omega : ShellSeq d) (m L : ℕ) (U : Set (Vec d)) :
    matTranspose (volumeAverageMat U
        (fun y => finiteShellIncrement omega m L y)) =
      -(volumeAverageMat (U : Set (Vec d))
        (fun y => finiteShellIncrement omega m L y)) := by
  refine matTranspose_volumeAverageMat U _ fun y i k => ?_
  have hsk := congrFun (congrFun (finiteShellIncrement_skew omega m L y) k) i
  simpa only [Matrix.transpose_apply, Matrix.neg_apply, Pi.neg_apply] using hsk

/-- The entry bound of the cutoff stream matrix on a Chapter 2 domain: the sum
over the entries of the per-entry bound of `CenteredCoeffOn`. -/
private theorem abs_streamCutoff_entry_le_sum (U : Book.Ch02.Domain d)
    (omega : ShellSeq d) (k : ℕ) (x : Vec d) (hx : x ∈ (U : Set (Vec d)))
    (i j : Fin d) :
    |streamCutoff omega k x i j| ≤
      ∑ r : Fin d × Fin d,
        |streamCutoffEntryBound U.isDomain.isBoundedDomain.isBounded omega k r| := by
  calc |streamCutoff omega k x i j| ≤
      streamCutoffEntryBound U.isDomain.isBoundedDomain.isBounded omega k (i, j) :=
        abs_streamCutoffEntryBound U.isDomain.isBoundedDomain.isBounded omega k
          (i, j) x hx
    _ ≤ |streamCutoffEntryBound U.isDomain.isBoundedDomain.isBounded omega k (i, j)| :=
        le_abs_self _
    _ ≤ ∑ r : Fin d × Fin d,
        |streamCutoffEntryBound U.isDomain.isBoundedDomain.isBounded omega k r| :=
        Finset.single_le_sum
          (f := fun r => |streamCutoffEntryBound U.isDomain.isBoundedDomain.isBounded
            omega k r|) (fun r _ => abs_nonneg _) (Finset.mem_univ _)

/-- **The nonnegativity premise `hS`** of the third clause: the printed energy
scale `J(U, p, q; â) + J(U, p, q; a_m) + 2 p·q` is nonnegative, where
`â = a_L - (k_L - k_m)_U` is the volume-average-centered pair field and
`a_m` the level-`m` cutoff field.  Each response functional is half of the
coarse block form at the offset `(-p, q)` minus the cross term
(`responseJ_eq_blockQuadratic` on the Chapter 2 carrier), so the sum plus the
cross term is half of the sum of two positive semidefinite quadratic forms
(`zero_le_blockVecDot_coarseBlockMatrix`).  The centered field is reached as
the constant anti-symmetric shift of `a_L` by `-(k_L - k_m)_U`
(`addConstSkewCoeffOn`), whose Chapter 2 carrier is the centered pair field
itself. -/
theorem responseJ_centeredPair_add_nonneg (nu : ℝ) (hnu : 0 < nu) (m L : ℕ)
    (U : Book.Ch02.Domain d) (omega : ShellSeq d) (p q : Vec d) :
    0 ≤ ResponseJ (U : Set (Vec d)) p q
        (centeredPairField nu omega m L (U : Set (Vec d))) +
      ResponseJ (U : Set (Vec d)) p q
        (coefficientCutoff nu omega m).toCoeffField +
      2 * vecDot p q := by
  -- the entry bounds of the two cutoff fields on `U`
  have hentryL : ∀ x ∈ (U : Set (Vec d)), ∀ i j : Fin d,
      |(coefficientCutoff nu omega L).toCoeffField x i j| ≤
        nu + ∑ r : Fin d × Fin d,
          |streamCutoffEntryBound U.isDomain.isBoundedDomain.isBounded omega L r| :=
    fun x hx i j =>
      abs_coefficientCutoff_entry_le hnu.le omega L x
        (fun i j => abs_streamCutoff_entry_le_sum U omega L x hx i j) i j
  have hentryM : ∀ x ∈ (U : Set (Vec d)), ∀ i j : Fin d,
      |(coefficientCutoff nu omega m).toCoeffField x i j| ≤
        nu + ∑ r : Fin d × Fin d,
          |streamCutoffEntryBound U.isDomain.isBoundedDomain.isBounded omega m r| :=
    fun x hx i j =>
      abs_coefficientCutoff_entry_le hnu.le omega m x
        (fun i j => abs_streamCutoff_entry_le_sum U omega m x hx i j) i j
  -- the constant anti-symmetric shift `-(k_L - k_m)_U`
  have hk0 : matTranspose
      (-(volumeAverageMat (U : Set (Vec d))
        (fun y => finiteShellIncrement omega m L y))) =
    -(-(volumeAverageMat (U : Set (Vec d))
      (fun y => finiteShellIncrement omega m L y))) := by
    have h1 : matTranspose
        (-(volumeAverageMat (U : Set (Vec d))
          (fun y => finiteShellIncrement omega m L y))) =
      -matTranspose (volumeAverageMat (U : Set (Vec d))
        (fun y => finiteShellIncrement omega m L y)) := by
      show Matrix.transpose
        (-(volumeAverageMat (U : Set (Vec d))
          (fun y => finiteShellIncrement omega m L y))) =
        -(Matrix.transpose (volumeAverageMat (U : Set (Vec d))
          (fun y => finiteShellIncrement omega m L y)))
      exact Matrix.transpose_neg _
    rw [h1, matTranspose_volumeAverageMat_finiteShellIncrement]
  -- the Chapter 2 coefficient objects of the two fields
  have hfieldâ :
      (addConstSkewCoeffOn (coefficientCutoffCoeffOn U hnu omega L hentryL) hk0).toCoeffField =
        centeredPairField nu omega m L (U : Set (Vec d)) := by
    funext x
    simp only [SuperdiffusionCLT.Section2.CoarseGraining.addConstSkewCoeffOn_toCoeffField,
      SuperdiffusionCLT.Section2.CoarseGraining.coefficientCutoffCoeffOn_toCoeffField,
      centeredPairField, sub_eq_add_neg]
  -- the averaged carrier `e.Jaas.matform` at the two fields
  have hformâ : ResponseJ (U : Set (Vec d)) p q
        (addConstSkewCoeffOn (coefficientCutoffCoeffOn U hnu omega L hentryL) hk0).toCoeffField =
      (1 / 2 : ℝ) * blockVecDot (-p, q)
          (blockMatVecMul (Book.Ch02.coarseBlockMatrix U
            (addConstSkewCoeffOn (coefficientCutoffCoeffOn U hnu omega L hentryL) hk0))
            (-p, q)) -
        vecDot p q :=
    SuperdiffusionCLT.Section2.CoarseGraining.responseJ_eq_blockQuadratic U
      (addConstSkewCoeffOn (coefficientCutoffCoeffOn U hnu omega L hentryL) hk0) p q
  have hformm : ResponseJ (U : Set (Vec d)) p q
        (coefficientCutoff nu omega m).toCoeffField =
      (1 / 2 : ℝ) * blockVecDot (-p, q)
          (blockMatVecMul (Book.Ch02.coarseBlockMatrix U
            (coefficientCutoffCoeffOn U hnu omega m hentryM)) (-p, q)) -
        vecDot p q :=
    SuperdiffusionCLT.Section2.CoarseGraining.responseJ_eq_blockQuadratic U
      (coefficientCutoffCoeffOn U hnu omega m hentryM) p q
  -- the two coarse block forms are positive semidefinite
  have hpsdâ : 0 ≤ blockVecDot (-p, q)
      (blockMatVecMul (Book.Ch02.coarseBlockMatrix U
        (addConstSkewCoeffOn (coefficientCutoffCoeffOn U hnu omega L hentryL) hk0)) (-p, q)) :=
    zero_le_blockVecDot_coarseBlockMatrix U
      (addConstSkewCoeffOn (coefficientCutoffCoeffOn U hnu omega L hentryL) hk0) (-p, q)
  have hpsdm : 0 ≤ blockVecDot (-p, q)
      (blockMatVecMul (Book.Ch02.coarseBlockMatrix U
        (coefficientCutoffCoeffOn U hnu omega m hentryM)) (-p, q)) :=
    zero_le_blockVecDot_coarseBlockMatrix U
      (coefficientCutoffCoeffOn U hnu omega m hentryM) (-p, q)
  -- the carrier identification of the centered field
  have hcar : ResponseJ (U : Set (Vec d)) p q
        (centeredPairField nu omega m L (U : Set (Vec d))) =
      ResponseJ (U : Set (Vec d)) p q
        (addConstSkewCoeffOn (coefficientCutoffCoeffOn U hnu omega L hentryL) hk0).toCoeffField := by
    rw [hfieldâ]
  rw [hcar, hformâ, hformm]
  linarith only [hpsdâ, hpsdm]

end

end SuperdiffusionCLT.Section2.Localization