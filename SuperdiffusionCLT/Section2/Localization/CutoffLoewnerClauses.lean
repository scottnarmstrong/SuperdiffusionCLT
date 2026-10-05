/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.CutoffComparison
public import SuperdiffusionCLT.Section2.Cutoff.CenteredCoeffOn
public import SuperdiffusionCLT.Section2.Localization.BlockSandwichExtraction
public import SuperdiffusionCLT.Section2.Localization.BlockGaugeGroup
public import SuperdiffusionCLT.Section2.Localization.BlockPerturbation
public import SuperdiffusionCLT.Section2.Localization.CenteredIncrementQuadratic
public import SuperdiffusionCLT.Section2.Localization.LocalizationWitnessPackaging

/-!
# The four `MatLoewnerLE` clauses of the localization anchor at the cutoff pair

The assembly step for conjunct 1 of the localization statement
(`e.localization.s.star` of the paper, the instantiation of
`e.localization.A`): the four `MatLoewnerLE`
clauses that `localizationConjunct1` of `LocalizationWitnessPackaging` takes as
its hypothesis `hLoewner`, produced from the block-sandwich engine
`coarseBlockMatrix_localization` (`BlockPerturbation`) at the cutoff pair.

The printed proof: the volume-average-centered field
`b = a_L - (k_L - k_m)_U = a_m + (h - h_U)` with `h = k_L - k_m` satisfies the
hypotheses of `e.localize.matrix.bounds.in.lemma` at `θ = nu⁻¹ M`
(`relSkewBound_centeredCutoffPair`), giving the two-sided ratio bound

`bfA(U; b) ≤ (1 + D) bfA(U; a_m)`  and  `bfA(U; a_m) ≤ (1 + D) bfA(U; b)`,

with `D = θ (1 + θ)`.  Each `bfA` is the gauge conjugate of a block-diagonal
matrix by `blockG (-k)`, `k` the corresponding `kappaCoarse` (the pointwise
gauge-conjugation identity), so the two sandwiches are
transported by the congruence invariance of the block Loewner order
(`blockMatLoewnerLE_congr_blockMatMul`) to sandwiches whose right side is
un-conjugated: the gauges `ħ - k_L + k_m` (forward) and `k_L - k_m - ħ`
(backward) arise as `a - b` of the two sides' gauges.  The extraction package
`matLoewnerLE_of_blockMatLoewnerLE_conj_blockG` /
`matLoewnerLE_lowerRight_of_blockMatLoewnerLE_conj_blockG`
(`BlockSandwichExtraction`) then reads off, in each direction,

`σ_L ≤ (1+D) σ_m`, `σ_m ≤ (1+D) σ_L`, `σ_*^{-1}_m ≤ (1+D) σ_*^{-1}_L`,
`σ_*^{-1}_L ≤ (1+D) σ_*^{-1}_m`,

and the two-sided ratio bound at the witness `X = 2 D` (a two-line real
argument: `σ_m ≤ (1+D) σ_L ≤ 2 σ_L` from `D ≤ 1/2`, then
`σ_L ≤ σ_m + D σ_m ≤ σ_m + 2 D σ_L = σ_m + X σ_L`) gives the four clauses.

## Main results

* `cutoffLoewnerClauses`: the four `MatLoewnerLE` clauses of the
  `hLoewner` hypothesis of `localizationConjunct1`, verbatim.
* `cutoffLocalizationConjunct1`: conjunct 1 itself, by composing
  with `localizationConjunct1`.
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
open SuperdiffusionCLT.Section3.ResponseFields
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## Block algebra used to transport the gauge -/

private theorem blockMatMul_smul_left (c : ℝ) (A B : BlockMat d) :
    blockMatMul (c • A) B = c • blockMatMul A B := by
  refine blockMat_ext ?_ ?_ ?_ ?_ <;>
    simp only [blockMatMul, blockSMul_upperLeft, blockSMul_upperRight,
      blockSMul_lowerLeft, blockSMul_lowerRight, Matrix.smul_mul, smul_add]

private theorem blockMatMul_smul_right (c : ℝ) (A B : BlockMat d) :
    blockMatMul A (c • B) = c • blockMatMul A B := by
  refine blockMat_ext ?_ ?_ ?_ ?_ <;>
    simp only [blockMatMul, blockSMul_upperLeft, blockSMul_upperRight,
      blockSMul_lowerLeft, blockSMul_lowerRight, Matrix.mul_smul, smul_add]

private theorem blockMatMul_id_left (A : BlockMat d) :
    blockMatMul (blockIdentity d) A = A := by
  refine blockMat_ext ?_ ?_ ?_ ?_ <;>
    simp only [blockMatMul, blockIdentity, blockDiag, Matrix.one_mul,
      Matrix.zero_mul, add_zero, zero_add]

private theorem blockMatMul_id_right (A : BlockMat d) :
    blockMatMul A (blockIdentity d) = A := by
  refine blockMat_ext ?_ ?_ ?_ ?_ <;>
    simp only [blockMatMul, blockIdentity, blockDiag, Matrix.mul_one,
      Matrix.mul_zero, add_zero, zero_add]

private theorem blockMatTranspose_blockIdentity :
    blockMatTranspose (blockIdentity d) = blockIdentity d := by
  refine blockMat_ext ?_ ?_ ?_ ?_ <;>
    simp only [blockMatTranspose, blockIdentity, blockDiag, matTranspose,
      Matrix.transpose_one, Matrix.transpose_zero]

/-- Two gauge conjugations in sequence combine: with `Q = blockG q`, the
sandwich `Qᵗ (G_aᵗ D G_a) Q` is `G_{a+q}ᵗ D G_{a+q}`. -/
private theorem blockG_conj_mul (D : BlockMat d) (a q : Mat d) :
    blockMatMul (blockMatTranspose (blockG q))
      (blockMatMul (blockMatMul (blockMatTranspose (blockG a)) (blockMatMul D (blockG a)))
        (blockG q))
    = blockMatMul (blockMatTranspose (blockG (a + q)))
        (blockMatMul D (blockG (a + q))) := by
  refine blockMat_ext ?_ ?_ ?_ ?_ <;>
    simp only [blockMatMul, blockMatTranspose, blockG, matTranspose,
      Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_zero] <;>
    noncomm_ring

/-- **Gauge transport for the block Loewner order.**  A sandwich between the
gauge conjugates `G_aᵗ D G_a ≤ c • (G_bᵗ D' G_b)` transports to a sandwich
whose left side carries the difference gauge and whose right side is
un-conjugated: `G_{a-b}ᵗ D G_{a-b} ≤ c • D'`. -/
private theorem blockMatLoewnerLE_shift_gauge {D D' : BlockMat d} {a b : Mat d} {c : ℝ}
    (hsand : BlockMatLoewnerLE
      (blockMatMul (blockMatTranspose (blockG a)) (blockMatMul D (blockG a)))
      (c • blockMatMul (blockMatTranspose (blockG b)) (blockMatMul D' (blockG b)))) :
    BlockMatLoewnerLE
      (blockMatMul (blockMatTranspose (blockG (a - b)))
        (blockMatMul D (blockG (a - b))))
      (c • D') := by
  have h1 := blockMatLoewnerLE_congr_blockMatMul (G := blockG (-b)) hsand
  simp only [blockG_conj_mul, blockMatMul_smul_left, blockMatMul_smul_right] at h1
  have h0 : b + -b = 0 := by abel
  rw [h0, blockG_zero, blockMatTranspose_blockIdentity, blockMatMul_id_left,
    blockMatMul_id_right] at h1
  rw [show a + -b = a - b from by abel] at h1
  exact h1

/-! ## `bfA` as a gauge conjugate of a block-diagonal matrix -/

/-- The pointwise identity behind `e.localization.A.def`: `bfA(U; a)` is the
gauge conjugate of `blockDiag σ σ_*⁻¹` by `blockG (-k)`. -/
private theorem coarseBlockMatrix_eq_blockG_conj (U : Book.Ch02.Domain d)
    (a : Book.Ch02.CoeffOn U) :
    Book.Ch02.coarseBlockMatrix U a =
      blockMatMul (blockMatTranspose (blockG (-(Book.Ch02.kappaCoarse U a))))
        (blockMatMul (blockDiag (Book.Ch02.sigmaCoarse U a)
            (Book.Ch02.sigmaStarInvCoarse U a))
          (blockG (-(Book.Ch02.kappaCoarse U a)))) := by
  refine blockMat_ext ?_ ?_ ?_ ?_ <;>
    simp only [Book.Ch02.coarseBlockMatrix, Book.Ch02.blockMatrixOfCoarseMatrices,
      Book.Ch02.coarseMatrices_sigma, Book.Ch02.coarseMatrices_sigmaStarInv,
      Book.Ch02.coarseMatrices_kappa, Book.Ch02.CoarseMatrices.b, blockMatMul,
      blockMatTranspose, blockG, blockDiag, matTranspose, Matrix.transpose_neg,
      Matrix.transpose_one, Matrix.transpose_zero, Matrix.mul_assoc] <;>
    noncomm_ring

/-! ## The two-sided ratio bound at the witness `X = 2 D` -/

/-- From the two one-sided ratio bounds `A ≤ (1+D) B` and `B ≤ (1+D) A` with
`D ≥ 0`, the two clauses of the statement at the witness `X = 2 D`. -/
private theorem matLoewnerLE_witness_clauses {A B : Mat d} {D X : ℝ}
    (hD : 0 ≤ D) (hX : X = 2 * D)
    (hA : ∀ x : Vec d, 0 ≤ vecDot x (matVecMul A x))
    (hB : ∀ x : Vec d, 0 ≤ vecDot x (matVecMul B x))
    (hAB : MatLoewnerLE A ((1 + D) • B)) (hBA : MatLoewnerLE B ((1 + D) • A)) :
    MatLoewnerLE ((1 - X) • A) B ∧ MatLoewnerLE B ((1 + X) • A) := by
  constructor
  · intro p
    have h1 := hAB p
    have h2 := hBA p
    have hA' : 0 ≤ vecDot p (matVecMul A p) := hA p
    have h0 : 0 ≤ vecDot p (matVecMul B p) := hB p
    simp only [smul_matVecMul, vecDot_smul_right] at h1 h2
    have h1' : vecDot p (matVecMul A p) ≤
        (1 + D) * vecDot p (matVecMul B p) := by linarith only [h1]
    have h2' : vecDot p (matVecMul B p) ≤
        (1 + D) * vecDot p (matVecMul A p) := by linarith only [h2]
    rw [hX, smul_matVecMul, vecDot_smul_right]
    by_cases hcase : 2 * D ≤ 1
    · -- the coefficient `1 - X` is nonnegative
      have hcoef : (1 + D) ≤ 2 := by linarith only [hcase]
      have hB2 : vecDot p (matVecMul B p) ≤ 2 * vecDot p (matVecMul A p) :=
        le_trans h2' (mul_le_mul_of_nonneg_right hcoef hA')
      have hDB : D * vecDot p (matVecMul B p) ≤ 2 * D * vecDot p (matVecMul A p) := by
        calc D * vecDot p (matVecMul B p)
            ≤ D * (2 * vecDot p (matVecMul A p)) :=
              mul_le_mul_of_nonneg_left hB2 hD
          _ = 2 * D * vecDot p (matVecMul A p) := by ring
      have hsplit : (1 + D) * vecDot p (matVecMul B p) =
          vecDot p (matVecMul B p) + D * vecDot p (matVecMul B p) := by ring
      have hA1 : vecDot p (matVecMul A p) ≤
          vecDot p (matVecMul B p) + D * vecDot p (matVecMul B p) := by
        rw [hsplit] at h1'
        linarith only [h1']
      have hchain : vecDot p (matVecMul A p) ≤
          vecDot p (matVecMul B p) + 2 * D * vecDot p (matVecMul A p) := by
        linarith only [hA1, hDB]
      have hrw : (1 - 2 * D) * vecDot p (matVecMul A p) =
          vecDot p (matVecMul A p) - 2 * D * vecDot p (matVecMul A p) := by ring
      rw [hrw]
      linarith only [hchain]
    · -- the coefficient `1 - X` is negative, and the quadratic form is nonnegative
      have hrw : (1 - 2 * D) * vecDot p (matVecMul A p) =
          -((2 * D - 1) * vecDot p (matVecMul A p)) := by ring
      rw [hrw]
      have hpos : 0 ≤ (2 * D - 1) * vecDot p (matVecMul A p) :=
        mul_nonneg (by linarith only [hcase]) hA'
      linarith only [hpos, h0]
  · intro p
    have h2 := hBA p
    simp only [smul_matVecMul, vecDot_smul_right] at h2
    have h2' : vecDot p (matVecMul B p) ≤
        (1 + D) * vecDot p (matVecMul A p) := by linarith only [h2]
    rw [hX, smul_matVecMul, vecDot_smul_right]
    have hfin : vecDot p (matVecMul B p) ≤
        (1 + 2 * D) * vecDot p (matVecMul A p) :=
      le_trans h2' (mul_le_mul_of_nonneg_right (by linarith only [hD]) (hA p))
    linarith only [hfin]

/-! ## The positivity vocabulary -/

private theorem vecDot_matVecMul_sigmaStarInvCoarse_nonneg
    (U : Book.Ch02.Domain d) (a : Book.Ch02.CoeffOn U) (x : Vec d) :
    0 ≤ vecDot x (matVecMul (Book.Ch02.sigmaStarInvCoarse U a) x) := by
  have hpsd := (Book.Ch02.sigmaStarInvCoarse_posDef U a).posSemidef
  simpa only [dotProduct, Matrix.mulVec, vecDot, matVecMul, RCLike.star_def,
    conj_trivial, star_trivial] using hpsd.dotProduct_mulVec_nonneg x

private theorem vecDot_matVecMul_sigmaCoarse_nonneg
    (U : Book.Ch02.Domain d) (a : Book.Ch02.CoeffOn U) (x : Vec d) :
    0 ≤ vecDot x (matVecMul (Book.Ch02.sigmaCoarse U a) x) := by
  have hpsd := (Book.Ch02.sigmaStarCoarse_posDef U a).posSemidef
  have h0 : 0 ≤ vecDot x (matVecMul (Book.Ch02.sigmaStarCoarse U a) x) := by
    simpa only [dotProduct, Matrix.mulVec, vecDot, matVecMul, RCLike.star_def,
      conj_trivial, star_trivial] using hpsd.dotProduct_mulVec_nonneg x
  have h1 : 1 / 2 * vecDot x (matVecMul (Book.Ch02.sigmaStarCoarse U a) x) ≤
      1 / 2 * vecDot x (matVecMul (Book.Ch02.sigmaCoarse U a) x) :=
    Book.Ch02.sigmaStarCoarse_le_sigmaCoarse U a x
  linarith only [h1, h0]

/-! ## The entry bounds of the cutoff pair -/

/-- An explicit entry bound for the level-`L` cutoff field `a_L` on `U`, in the
shape consumed by `coefficientCutoffCoeffOn`: the molecular diffusivity plus
the sum of the per-entry stream bounds. -/
noncomputable def cutoffEntryBound (U : Book.Ch02.Domain d) (nu : ℝ)
    (omega : ShellSeq d) (L : ℕ) : ℝ :=
  nu + ∑ p : Fin d × Fin d,
    |streamCutoffEntryBound U.isDomain.isBoundedDomain.isBounded omega L p|

/-- The entry bound of the cutoff stream matrix on `U`: the sum over the
entries of the per-entry bound of `CenteredCoeffOn`. -/
private theorem abs_streamCutoff_entry_le_bound (U : Book.Ch02.Domain d)
    (omega : ShellSeq d) (L : ℕ) (x : Vec d) (hx : x ∈ (U : Set (Vec d)))
    (i j : Fin d) :
    |streamCutoff omega L x i j| ≤ ∑ p : Fin d × Fin d,
      |streamCutoffEntryBound U.isDomain.isBoundedDomain.isBounded omega L p| := by
  calc |streamCutoff omega L x i j| ≤
      |streamCutoffEntryBound U.isDomain.isBoundedDomain.isBounded omega L (i, j)| :=
        (abs_streamCutoffEntryBound U.isDomain.isBoundedDomain.isBounded omega L
          (i, j) x hx).trans (le_abs_self _)
    _ ≤ ∑ p : Fin d × Fin d,
        |streamCutoffEntryBound U.isDomain.isBoundedDomain.isBounded omega L p| :=
        Finset.single_le_sum
          (f := fun p => |streamCutoffEntryBound U.isDomain.isBoundedDomain.isBounded
            omega L p|) (fun p _ => abs_nonneg _) (Finset.mem_univ _)

/-- The explicit entry bound works. -/
private theorem abs_coefficientCutoff_entry_le_bound (U : Book.Ch02.Domain d)
    (nu : ℝ) (hnu : 0 < nu) (omega : ShellSeq d) (L : ℕ) (x : Vec d)
    (hx : x ∈ (U : Set (Vec d))) (i j : Fin d) :
    |(coefficientCutoff nu omega L).toCoeffField x i j| ≤
      cutoffEntryBound U nu omega L := by
  unfold cutoffEntryBound
  exact abs_coefficientCutoff_entry_le hnu.le omega L x
    (abs_streamCutoff_entry_le_bound U omega L x hx) i j

/-! ## The four `MatLoewnerLE` clauses at the cutoff pair -/

/-- **The four `MatLoewnerLE` clauses of the localization statement**
(the `hLoewner` hypothesis of `localizationConjunct1`, verbatim): the
sandwich about the witness `X = 2 theta (1 + theta)` at the cutoff pair, with
`theta = nu⁻¹ (matrixOperatorNorm_diamConst d * 3^n *
upperShellDerivGauge n m L omega)` the printed gauge of the centered
perturbation. -/
theorem cutoffLoewnerClauses (nu : ℝ) (hnu : 0 < nu) (n m L : ℕ) (hmL : m ≤ L)
    (U : Book.Ch02.Domain d)
    (hU : (U : Set (Vec d)) ⊆ openCubeSet (originCube d (n : ℤ))) (omega : ShellSeq d) :
    Homogenization.MatLoewnerLE
      ((1 - localizationWitness nu n m L omega) •
        sigmaCoarse (U : Set (Vec d))
          (coefficientCutoff nu omega L).toCoeffField)
      (sigmaCoarse (U : Set (Vec d))
        (coefficientCutoff nu omega m).toCoeffField) ∧
    Homogenization.MatLoewnerLE
      (sigmaCoarse (U : Set (Vec d))
        (coefficientCutoff nu omega m).toCoeffField)
      ((1 + localizationWitness nu n m L omega) •
        sigmaCoarse (U : Set (Vec d))
          (coefficientCutoff nu omega L).toCoeffField) ∧
    Homogenization.MatLoewnerLE
      ((1 - localizationWitness nu n m L omega) •
        sigmaStarInvCoarse (U : Set (Vec d))
          (coefficientCutoff nu omega m).toCoeffField)
      (sigmaStarInvCoarse (U : Set (Vec d))
        (coefficientCutoff nu omega L).toCoeffField) ∧
    Homogenization.MatLoewnerLE
      (sigmaStarInvCoarse (U : Set (Vec d))
        (coefficientCutoff nu omega L).toCoeffField)
      ((1 + localizationWitness nu n m L omega) •
        sigmaStarInvCoarse (U : Set (Vec d))
          (coefficientCutoff nu omega m).toCoeffField) := by
  -- The objects of the printed proof: the volume average `ħ` of the finite
  -- shell increment `k_L - k_m`, the two coefficient objects, the
  -- volume-average-centered field `b = a_L - ħ`, and the perturbation
  -- `h = k_L - k_m - ħ`.
  have hincr_sub : ∀ x : Vec d,
      (coefficientCutoff nu omega L).toCoeffField x -
        (coefficientCutoff nu omega m).toCoeffField x =
      finiteShellIncrement omega m L x :=
    coefficientCutoff_toCoeffField_sub nu omega hmL
  have hħskew : matTranspose (volumeAverageMat (U : Set (Vec d))
      (fun y => finiteShellIncrement omega m L y)) =
    -(volumeAverageMat (U : Set (Vec d))
      (fun y => finiteShellIncrement omega m L y)) := by
    have h := matTranspose_volumeAverageMat (U : Set (Vec d))
      (fun y => finiteShellIncrement omega m L y)
      (fun y i k => by
        have hsk := congrFun (congrFun (finiteShellIncrement_skew omega m L y) k) i
        simpa only [Matrix.transpose_apply, Matrix.neg_apply, Pi.neg_apply] using hsk)
    exact h
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
    rw [h1, hħskew]
  -- The Chapter 2 coefficient objects and the centered shifted field.
  have hentryL : ∀ x ∈ (U : Set (Vec d)), ∀ i j : Fin d,
      |(coefficientCutoff nu omega L).toCoeffField x i j| ≤
        cutoffEntryBound U nu omega L :=
    fun x hx i j => abs_coefficientCutoff_entry_le_bound U nu hnu omega L x hx i j
  have hentryM : ∀ x ∈ (U : Set (Vec d)), ∀ i j : Fin d,
      |(coefficientCutoff nu omega m).toCoeffField x i j| ≤
        cutoffEntryBound U nu omega m :=
    fun x hx i j => abs_coefficientCutoff_entry_le_bound U nu hnu omega m x hx i j
  -- The hypotheses of the block-sandwich engine, at θ = localizationTheta.
  have hb : ∀ᵐ x ∂(volumeMeasureOn (U : Set (Vec d))),
      (addConstSkewCoeffOn (coefficientCutoffCoeffOn U hnu omega L hentryL) hk0).toCoeffField
          x =
        (coefficientCutoffCoeffOn U hnu omega m hentryM).toCoeffField x +
          (finiteShellIncrement omega m L x -
            volumeAverageMat (U : Set (Vec d))
              (fun y => finiteShellIncrement omega m L y)) := by
    refine Filter.Eventually.of_forall fun x => ?_
    simp only [addConstSkewCoeffOn_toCoeffField, coefficientCutoffCoeffOn_toCoeffField]
    have h1 : (coefficientCutoff nu omega L).toCoeffField x =
        (coefficientCutoff nu omega m).toCoeffField x +
          finiteShellIncrement omega m L x := by
      rw [← hincr_sub x]
      abel
    rw [h1]
    abel
  have hskew : ∀ᵐ x ∂(volumeMeasureOn (U : Set (Vec d))),
      matTranspose (finiteShellIncrement omega m L x -
        volumeAverageMat (U : Set (Vec d))
          (fun y => finiteShellIncrement omega m L y)) =
      -(finiteShellIncrement omega m L x -
        volumeAverageMat (U : Set (Vec d))
          (fun y => finiteShellIncrement omega m L y)) := by
    refine Filter.Eventually.of_forall fun x => ?_
    show Matrix.transpose (finiteShellIncrement omega m L x -
        volumeAverageMat (U : Set (Vec d))
          (fun y => finiteShellIncrement omega m L y)) =
      -(finiteShellIncrement omega m L x -
        volumeAverageMat (U : Set (Vec d))
          (fun y => finiteShellIncrement omega m L y))
    have h1 : Matrix.transpose (finiteShellIncrement omega m L x) =
        -finiteShellIncrement omega m L x := finiteShellIncrement_skew omega m L x
    have h2 : Matrix.transpose (volumeAverageMat (U : Set (Vec d))
        (fun y => finiteShellIncrement omega m L y)) =
      -(volumeAverageMat (U : Set (Vec d))
        (fun y => finiteShellIncrement omega m L y)) := hħskew
    rw [Matrix.transpose_sub, h1, h2]
    abel
  have hbound : ∀ᵐ x ∂(volumeMeasureOn (U : Set (Vec d))), ∀ p r : Vec d,
      2 * vecDot r (matVecMul (finiteShellIncrement omega m L x -
          volumeAverageMat (U : Set (Vec d))
            (fun y => finiteShellIncrement omega m L y)) p) ≤
        localizationTheta nu n m L omega *
          (vecDot p (matVecMul
              (symmPart ((coefficientCutoff nu omega m).toCoeffField x)) p) +
            vecDot r (matVecMul
              (symmPart ((coefficientCutoff nu omega m).toCoeffField x)) r)) := by
    filter_upwards [ae_restrict_mem U.measurableSet] with x hx p r
    have hkey := relSkewBound_centeredCutoffPair nu omega m L n hmL hnu U hU x hx p r
    rw [show ((coefficientCutoff nu omega L).toCoeffField x -
          volumeAverageMat (U : Set (Vec d))
            (fun y => finiteShellIncrement omega m L y)) -
        (coefficientCutoff nu omega m).toCoeffField x =
      finiteShellIncrement omega m L x -
        volumeAverageMat (U : Set (Vec d))
          (fun y => finiteShellIncrement omega m L y) from by
      rw [← hincr_sub x]
      abel] at hkey
    exact hkey
  -- The engine (`e.localize.matrix.bounds.in.lemma` and its flip).
  have hfwd : BlockMatLoewnerLE
      (Book.Ch02.coarseBlockMatrix U
        (addConstSkewCoeffOn (coefficientCutoffCoeffOn U hnu omega L hentryL) hk0))
      ((1 + localizationTheta nu n m L omega *
          (1 + localizationTheta nu n m L omega)) •
        Book.Ch02.coarseBlockMatrix U
          (coefficientCutoffCoeffOn U hnu omega m hentryM)) :=
    coarseBlockMatrix_blockMatLoewnerLE_smul hb hskew hbound
  have hrev : BlockMatLoewnerLE
      (Book.Ch02.coarseBlockMatrix U
        (coefficientCutoffCoeffOn U hnu omega m hentryM))
      ((1 + localizationTheta nu n m L omega *
          (1 + localizationTheta nu n m L omega)) •
        Book.Ch02.coarseBlockMatrix U
          (addConstSkewCoeffOn (coefficientCutoffCoeffOn U hnu omega L hentryL) hk0)) := by
    intro X
    rw [blockMatVecMul_blockSMul, blockVecDot_smul_right]
    exact mul_le_mul_of_nonneg_left
      (coarseBlockMatrix_le_add_skew hb hskew hbound X) (by linarith only : (0:ℝ) ≤ 1/2)
  -- The two `bfA`'s as gauge conjugates of block-diagonal matrices.
  have hdecL := coarseBlockMatrix_eq_blockG_conj U
    (coefficientCutoffCoeffOn U hnu omega L hentryL)
  have hdecM := coarseBlockMatrix_eq_blockG_conj U
    (coefficientCutoffCoeffOn U hnu omega m hentryM)
  have hbfAb : Book.Ch02.coarseBlockMatrix U
      (addConstSkewCoeffOn (coefficientCutoffCoeffOn U hnu omega L hentryL) hk0) =
      blockMatMul
        (blockMatTranspose (blockG (volumeAverageMat (U : Set (Vec d))
            (fun y => finiteShellIncrement omega m L y) -
          Book.Ch02.kappaCoarse U (coefficientCutoffCoeffOn U hnu omega L hentryL))))
        (blockMatMul
          (blockDiag (Book.Ch02.sigmaCoarse U
              (coefficientCutoffCoeffOn U hnu omega L hentryL))
            (Book.Ch02.sigmaStarInvCoarse U
              (coefficientCutoffCoeffOn U hnu omega L hentryL)))
          (blockG (volumeAverageMat (U : Set (Vec d))
            (fun y => finiteShellIncrement omega m L y) -
          Book.Ch02.kappaCoarse U (coefficientCutoffCoeffOn U hnu omega L hentryL)))) := by
    rw [coarseBlockMatrix_addConstSkewCoeffOn
      (coefficientCutoffCoeffOn U hnu omega L hentryL) hk0, neg_neg, hdecL,
      blockG_conj_mul]
    rw [show -(Book.Ch02.kappaCoarse U (coefficientCutoffCoeffOn U hnu omega L hentryL)) +
        volumeAverageMat (U : Set (Vec d))
          (fun y => finiteShellIncrement omega m L y) =
      volumeAverageMat (U : Set (Vec d))
        (fun y => finiteShellIncrement omega m L y) -
      Book.Ch02.kappaCoarse U (coefficientCutoffCoeffOn U hnu omega L hentryL) from
      by abel]
  -- Transport each sandwich to an un-conjugated right side.
  rw [hbfAb, hdecM] at hfwd
  rw [hbfAb, hdecM] at hrev
  have hsandF := blockMatLoewnerLE_shift_gauge
    (a := volumeAverageMat (U : Set (Vec d))
      (fun y => finiteShellIncrement omega m L y) -
      Book.Ch02.kappaCoarse U (coefficientCutoffCoeffOn U hnu omega L hentryL))
    (b := -(Book.Ch02.kappaCoarse U
      (coefficientCutoffCoeffOn U hnu omega m hentryM))) hfwd
  have hsandR := blockMatLoewnerLE_shift_gauge
    (a := -(Book.Ch02.kappaCoarse U
      (coefficientCutoffCoeffOn U hnu omega m hentryM)))
    (b := volumeAverageMat (U : Set (Vec d))
      (fun y => finiteShellIncrement omega m L y) -
      Book.Ch02.kappaCoarse U (coefficientCutoffCoeffOn U hnu omega L hentryL)) hrev
  -- The four extractions.
  have hupF := matLoewnerLE_of_blockMatLoewnerLE_conj_blockG _ hsandF
    (vecDot_matVecMul_sigmaStarInvCoarse_nonneg U
      (coefficientCutoffCoeffOn U hnu omega L hentryL))
  have hlowF := matLoewnerLE_lowerRight_of_blockMatLoewnerLE_conj_blockG _ hsandF
  have hupR := matLoewnerLE_of_blockMatLoewnerLE_conj_blockG _ hsandR
    (vecDot_matVecMul_sigmaStarInvCoarse_nonneg U
      (coefficientCutoffCoeffOn U hnu omega m hentryM))
  have hlowR := matLoewnerLE_lowerRight_of_blockMatLoewnerLE_conj_blockG _ hsandR
  -- The witness and the two-sided ratio bound.
  have hθ : 0 ≤ localizationTheta nu n m L omega :=
    localizationTheta_nonneg nu hnu.le n m L omega
  have hD : 0 ≤ localizationD nu n m L omega := by
    show 0 ≤ localizationTheta nu n m L omega *
      (1 + localizationTheta nu n m L omega)
    exact mul_nonneg hθ (by linarith only [hθ])
  have hX : localizationWitness nu n m L omega = 2 * localizationD nu n m L omega :=
    rfl
  have hclauses1 := matLoewnerLE_witness_clauses hD hX
    (vecDot_matVecMul_sigmaCoarse_nonneg U
      (coefficientCutoffCoeffOn U hnu omega L hentryL))
    (vecDot_matVecMul_sigmaCoarse_nonneg U
      (coefficientCutoffCoeffOn U hnu omega m hentryM)) hupF hupR
  have hclauses2 := matLoewnerLE_witness_clauses hD hX
    (vecDot_matVecMul_sigmaStarInvCoarse_nonneg U
      (coefficientCutoffCoeffOn U hnu omega m hentryM))
    (vecDot_matVecMul_sigmaStarInvCoarse_nonneg U
      (coefficientCutoffCoeffOn U hnu omega L hentryL)) hlowR hlowF
  exact ⟨hclauses1.1, hclauses1.2, hclauses2.1, hclauses2.2⟩

/-! ## Conjunct 1 -/

/-- **Conjunct 1** (`Frozen.Section2.cutoff_localization`, conjunct 1,
verbatim shape): the composition of `cutoffLoewnerClauses` with
`localizationConjunct1`. -/
theorem cutoffLocalizationConjunct1
    (P : MeasureTheory.ProbabilityMeasure (ShellSeq d)) (hJ3 : ShellLawJ3 d P)
    (nu : ℝ) (hnu : 0 < nu) (hnu1 : nu ≤ 1) (n m L : ℕ) (hnm : n ≤ m)
    (hmL : m ≤ L) (U : Book.Ch02.Domain d)
    (hU : (U : Set (Vec d)) ⊆ openCubeSet (originCube d (n : ℤ))) :
    ∃ X : ShellSeq d → ℝ,
      Measurable X ∧
      Homogenization.IndependentSums.IsBigO P.toMeasure
          (Homogenization.IndependentSums.gammaSigma 1) X
          (localizationConst d * nu ^ (-(2 : ℝ)) *
            (3 : ℝ) ^ (-((m - n : ℕ) : ℝ))) ∧
      ∀ omega : ShellSeq d,
        Homogenization.MatLoewnerLE
          ((1 - X omega) •
            sigmaCoarse (U : Set (Vec d))
              (coefficientCutoff nu omega L).toCoeffField)
          (sigmaCoarse (U : Set (Vec d))
            (coefficientCutoff nu omega m).toCoeffField) ∧
      Homogenization.MatLoewnerLE
        (sigmaCoarse (U : Set (Vec d))
          (coefficientCutoff nu omega m).toCoeffField)
        ((1 + X omega) •
          sigmaCoarse (U : Set (Vec d))
            (coefficientCutoff nu omega L).toCoeffField) ∧
      Homogenization.MatLoewnerLE
        ((1 - X omega) •
          sigmaStarInvCoarse (U : Set (Vec d))
            (coefficientCutoff nu omega m).toCoeffField)
        (sigmaStarInvCoarse (U : Set (Vec d))
          (coefficientCutoff nu omega L).toCoeffField) ∧
      Homogenization.MatLoewnerLE
        (sigmaStarInvCoarse (U : Set (Vec d))
          (coefficientCutoff nu omega L).toCoeffField)
        ((1 + X omega) •
          sigmaStarInvCoarse (U : Set (Vec d))
            (coefficientCutoff nu omega m).toCoeffField) :=
  localizationConjunct1 P hJ3 nu hnu hnu1 n m L hnm hmL U
    (fun omega => cutoffLoewnerClauses nu hnu n m L hmL U hU omega)

end

end SuperdiffusionCLT.Section2.Localization