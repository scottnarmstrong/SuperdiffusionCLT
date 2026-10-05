/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.CutoffLoewnerClauses
public import SuperdiffusionCLT.Section2.Localization.UnsymmetricConversion
public import SuperdiffusionCLT.Section2.CoarseGraining.CutoffCorrespondence

/-!
# The premises of the bilinear clause of the localization statement

The five premises of conjunct 2 of `Frozen.Section2.cutoff_localization` that
enter its bilinear clause are proved here:

* the carrier positivity `hA` (`s_*(U; a_L)` positive semidefinite), `hAunit`
  (its determinant a unit) and `hEnonneg` (`s(U; a_L)` of nonnegative
  quadratic form) — proved in `CoarseGraining.CutoffCorrespondence` at the
  cutoff carrier, read here on the raw carrier of the statement;
* the conjugated comparison `hsand`, `Hᵗ σ_*L⁻¹ H ≤ D (2 + D) • σ_L` at the
  amplitude `D (2 + D)`, `D = theta (1 + theta)`, built from the block
  sandwiches of `coarseBlockMatrix_blockMatLoewnerLE_smul`
  (`BlockPerturbation`) by the route of `cutoffLoewnerClauses`.

## The route of the conjugated comparison

The forward and backward shifted block sandwiches of
`coarseBlockMatrix_blockMatLoewnerLE_smul` give, with `D = theta (1 + theta)`,
at every `p` and with the abbreviations `x = p·σ_L p`, `y = p·σ_m p`,
`u = (H p)·σ_*L⁻¹(H p)`, `v = (H p)·σ_*m⁻¹(H p)` (where `H = k_L - k_m - ħ` is
the gauge matrix of the statement and `ħ` the volume average of the finite shell
increment):

* `x + u ≤ (1 + D) y` — the forward sandwich at gauge `ħ - k_L + k_m = -H`,
  upper-left block extracted with the conjugate kept;
* `y + v ≤ (1 + D) x` — the backward sandwich at gauge `k_L - k_m - ħ = H`,
  upper-left block extracted with the conjugate kept;
* `v ≤ (1 + D) u` — the backward sandwich's lower-right block, which carries
  no gauge at all.

The scalar chain then reads: `y ≤ (1 + D) x` from the second line and `v ≥ 0`,
so `u ≤ (1 + D) y - x ≤ (1 + D)² x - x = (2 D + D²) x` — the amplitude
`D (2 + D)` of the printed `ħ`-absorption step in the proof of `l.localization`.
Because `D (2 + D) = 2 D + D²` exceeds the sandwich witness `X = 2 D`, conjunct 2
is packaged at the witness `sqrt (2 D + D²)` (its own `IsBigO` transported from
the `Γ₁` bound of `D` through the square-root route; see `CutoffSkewPremisesB`),
not at the smaller packaging witness `localizationSkewWitness`.

## Main results

* `cutoffCarrierPositivity`: `hA`, `hAunit` and `hEnonneg` at the cutoff
  carrier, on the raw `sigmaStarCoarse` / `sigmaCoarse` carriers.
* `cutoffConjugatedComparison`: the conjugated comparison at the amplitude
  `D (2 + D)`, the `hsand` premise of the bilinear clause with
  `c = fun omega => localizationD nu n m L omega *
  (2 + localizationD nu n m L omega)`.
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

/-! ## The entry bound of the cutoff pair at the explicit witness -/
private theorem cutoffEntryBound_le (U : Book.Ch02.Domain d) (nu : ℝ) (hnu : 0 < nu)
    (omega : ShellSeq d) (L : ℕ) (x : Vec d) (hx : x ∈ (U : Set (Vec d)))
    (i j : Fin d) :
    |(coefficientCutoff nu omega L).toCoeffField x i j| ≤
      cutoffEntryBound U nu omega L := by
  refine abs_coefficientCutoff_entry_le hnu.le omega L x (fun i j => ?_) i j
  calc |streamCutoff omega L x i j| ≤
        |streamCutoffEntryBound U.isDomain.isBoundedDomain.isBounded omega L (i, j)| :=
      (abs_streamCutoffEntryBound U.isDomain.isBoundedDomain.isBounded omega L
        (i, j) x hx).trans (le_abs_self _)
    _ ≤ ∑ q : Fin d × Fin d,
          |streamCutoffEntryBound U.isDomain.isBoundedDomain.isBounded omega L q| :=
      Finset.single_le_sum
        (f := fun q => |streamCutoffEntryBound U.isDomain.isBoundedDomain.isBounded
          omega L q|) (fun q _ => abs_nonneg _) (Finset.mem_univ _)

/-- The level-`L` cutoff field of Chapter 2 at the explicit entry bound
`cutoffEntryBound`. -/
private def cutoffCoeffOnL (U : Book.Ch02.Domain d) (nu : ℝ) (hnu : 0 < nu)
    (omega : ShellSeq d) (L : ℕ) : Book.Ch02.CoeffOn U :=
  coefficientCutoffCoeffOn U hnu omega L (fun x hx i j =>
    cutoffEntryBound_le U nu hnu omega L x hx i j)

/-- The level-`m` cutoff coefficient object, same normalization. -/
private def cutoffCoeffOnM (U : Book.Ch02.Domain d) (nu : ℝ) (hnu : 0 < nu)
    (omega : ShellSeq d) (m : ℕ) : Book.Ch02.CoeffOn U :=
  coefficientCutoffCoeffOn U hnu omega m (fun x hx i j =>
    cutoffEntryBound_le U nu hnu omega m x hx i j)

/-- The raw coefficient field of `cutoffCoeffOnL` is the cutoff field. -/
private theorem cutoffCoeffOnL_toCoeffField (U : Book.Ch02.Domain d) (nu : ℝ)
    (hnu : 0 < nu) (omega : ShellSeq d) (L : ℕ) :
    (cutoffCoeffOnL U nu hnu omega L).toCoeffField =
      (coefficientCutoff nu omega L).toCoeffField := rfl

/-- The raw coefficient field of `cutoffCoeffOnM` is the cutoff field. -/
private theorem cutoffCoeffOnM_toCoeffField (U : Book.Ch02.Domain d) (nu : ℝ)
    (hnu : 0 < nu) (omega : ShellSeq d) (m : ℕ) :
    (cutoffCoeffOnM U nu hnu omega m).toCoeffField =
      (coefficientCutoff nu omega m).toCoeffField := rfl

/-! ## The carrier-positivity premises -/

/-- **The three carrier-positivity premises of conjunct 2** at the
cutoff carrier, on the raw `sigmaStarCoarse` / `sigmaCoarse` carriers:
`s_*(U; a_L)` positive semidefinite, its determinant a unit, and `s(U; a_L)`
of nonnegative quadratic form. -/
theorem cutoffCarrierPositivity (nu : ℝ) (hnu : 0 < nu) (omega : ShellSeq d)
    (L : ℕ) (U : Book.Ch02.Domain d) :
    (Homogenization.sigmaStarCoarse (U : Set (Vec d))
        (coefficientCutoff nu omega L).toCoeffField).PosSemidef ∧
      IsUnit (Homogenization.sigmaStarCoarse (U : Set (Vec d))
          (coefficientCutoff nu omega L).toCoeffField).det ∧
      ∀ v : Vec d, 0 ≤ vecDot v (matVecMul
          (Homogenization.sigmaCoarse (U : Set (Vec d))
            (coefficientCutoff nu omega L).toCoeffField) v) := by
  have hentryL : ∀ x ∈ (U : Set (Vec d)), ∀ i j : Fin d,
      |(coefficientCutoff nu omega L).toCoeffField x i j| ≤
        cutoffEntryBound U nu omega L :=
    fun x hx i j => cutoffEntryBound_le U nu hnu omega L x hx i j
  refine ⟨?_, ?_, ?_⟩
  · exact (sigmaStarCoarse_coefficientCutoff_posDef U hnu omega L hentryL).posSemidef
  · exact SuperdiffusionCLT.Section2.CoarseGraining.isUnit_det_sigmaStarCoarse U
      (cutoffCoeffOnL U nu hnu omega L)
  · intro v
    have h0 : 0 ≤ vecDot v (matVecMul
        (Homogenization.sigmaStarCoarse (U : Set (Vec d))
          (coefficientCutoff nu omega L).toCoeffField) v) :=
      posSemidef_quadratic_nonneg
        (sigmaStarCoarse_coefficientCutoff_posDef U hnu omega L hentryL).posSemidef v
    have h1 : 1 / 2 * vecDot v (matVecMul
        (Homogenization.sigmaStarCoarse (U : Set (Vec d))
          (coefficientCutoff nu omega L).toCoeffField) v) ≤
        1 / 2 * vecDot v (matVecMul
          (Homogenization.sigmaCoarse (U : Set (Vec d))
            (coefficientCutoff nu omega L).toCoeffField) v) :=
      sigmaStarCoarse_le_sigmaCoarse_coefficientCutoff U hnu omega L hentryL v
    linarith only [h0, h1]

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

/-! ## The quadratic forms and their gauge conversions -/

/-- The quadratic form of the primitive carrier `sigmaStarInvCoarse` is
nonnegative. -/
private theorem vecDot_matVecMul_sigmaStarInvCoarse_nonneg
    (U : Book.Ch02.Domain d) (a : Book.Ch02.CoeffOn U) (x : Vec d) :
    0 ≤ vecDot x (matVecMul (Book.Ch02.sigmaStarInvCoarse U a) x) := by
  have hpsd := (Book.Ch02.sigmaStarInvCoarse_posDef U a).posSemidef
  simpa only [dotProduct, Matrix.mulVec, vecDot, matVecMul, RCLike.star_def, star_trivial,
    conj_trivial] using hpsd.dotProduct_mulVec_nonneg x

/-- The quadratic form of a conjugate square only sees the gauge up to
equality of the gauge matrices. -/
private theorem quad_congr (M : Mat d) {g h : Mat d} (hgh : g = h) (w : Vec d) :
    vecDot (matVecMul g w) (matVecMul M (matVecMul g w))
      = vecDot (matVecMul h w) (matVecMul M (matVecMul h w)) := by
  rw [hgh]

/-- The quadratic form of a conjugate square only sees the gauge up to a
common sign: `g = -h` gives `w·(gᵗ M g) w = w'·M w'` with `w' = h w`. -/
private theorem quad_congr_neg (M : Mat d) {g h : Mat d} (hgh : g = -h) (w : Vec d) :
    vecDot (matVecMul g w) (matVecMul M (matVecMul g w))
      = vecDot (matVecMul h w) (matVecMul M (matVecMul h w)) := by
  rw [hgh, neg_matVecMul, matVecMul_neg, vecDot_neg_left, vecDot_neg_right, neg_neg]

/-! ## The scalar chain behind the amplitude `D (2 + D)` -/

/-- The scalar chain behind the amplitude: from the forward kept-upper-left
extraction `x + u ≤ (1 + D) y` and the backward kept-upper-left extraction
`y + v ≤ (1 + D) x` with `v ≥ 0`, the conjugate term obeys
`u ≤ (2 D + D ^ 2) x` — the printed `D (2 + D)` absorption amplitude. -/
private theorem scalarChain {x y u v D : ℝ} (hD : 0 ≤ D) (hv : 0 ≤ v)
    (h1 : x + u ≤ (1 + D) * y) (h2 : y + v ≤ (1 + D) * x) :
    u ≤ (2 * D + D * D) * x := by
  have hDp : (0:ℝ) ≤ 1 + D := by linarith only [hD]
  have hy : y ≤ (1 + D) * x := by linarith only [h2, hv]
  have hys : (1 + D) * y ≤ (1 + D) * ((1 + D) * x) :=
    mul_le_mul_of_nonneg_left hy hDp
  have hu : u ≤ (1 + D) * y - x := by linarith only [h1]
  have hkey : (1 + D) * ((1 + D) * x) - x = (2 * D + D * D) * x := by ring
  linarith only [hu, hys, hkey]

/-! ## The conjugated comparison at the cutoff pair -/

/-- **The conjugated comparison at the cutoff pair** (the `ħ`-absorption
output of the block sandwich, `e.lh.fs.matrix.cra.bound` at the printed
amplitude): with `H = k_L - k_m - (k_L - k_m)_U` the gauge matrix of
conjunct 2,

`Hᵗ σ_*L⁻¹ H ≤ D (2 + D) • σ_L` at `D = theta (1 + theta)` = `localizationD`,

from the two-sided shifted block sandwich of
`coarseBlockMatrix_blockMatLoewnerLE_smul` (`BlockPerturbation`) at the cutoff
pair, by the route of `cutoffLoewnerClauses`. -/
theorem cutoffConjugatedComparison (nu : ℝ) (hnu : 0 < nu) (n m L : ℕ) (hmL : m ≤ L)
    (U : Book.Ch02.Domain d)
    (hU : (U : Set (Vec d)) ⊆ openCubeSet (originCube d (n : ℤ)))
    (omega : ShellSeq d) :
    Homogenization.MatLoewnerLE
      (Homogenization.matTranspose
          (Homogenization.kappaCoarse (U : Set (Vec d))
              (coefficientCutoff nu omega L).toCoeffField -
            Homogenization.kappaCoarse (U : Set (Vec d))
              (coefficientCutoff nu omega m).toCoeffField -
            Homogenization.volumeAverageMat (U : Set (Vec d))
              (fun y => finiteShellIncrement omega m L y)) *
        (Homogenization.sigmaStarCoarse (U : Set (Vec d))
            (coefficientCutoff nu omega L).toCoeffField)⁻¹ *
        (Homogenization.kappaCoarse (U : Set (Vec d))
            (coefficientCutoff nu omega L).toCoeffField -
          Homogenization.kappaCoarse (U : Set (Vec d))
            (coefficientCutoff nu omega m).toCoeffField -
          Homogenization.volumeAverageMat (U : Set (Vec d))
            (fun y => finiteShellIncrement omega m L y)))
      ((localizationD nu n m L omega *
          (2 + localizationD nu n m L omega)) •
        Homogenization.sigmaCoarse (U : Set (Vec d))
          (coefficientCutoff nu omega L).toCoeffField) := by
  -- The objects of the printed proof: the volume average `ħ` of the finite
  -- shell increment, the two Chapter 2 coefficient objects, and the gauge
  -- matrix `H = k_L - k_m - ħ`.
  have hentryL : ∀ x ∈ (U : Set (Vec d)), ∀ i j : Fin d,
      |(coefficientCutoff nu omega L).toCoeffField x i j| ≤
        cutoffEntryBound U nu omega L :=
    fun x hx i j => cutoffEntryBound_le U nu hnu omega L x hx i j
  have hentryM : ∀ x ∈ (U : Set (Vec d)), ∀ i j : Fin d,
      |(coefficientCutoff nu omega m).toCoeffField x i j| ≤
        cutoffEntryBound U nu omega m :=
    fun x hx i j => cutoffEntryBound_le U nu hnu omega m x hx i j
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
  -- The hypotheses of the block-sandwich engine, at θ = localizationTheta.
  have hb : ∀ᵐ x ∂(volumeMeasureOn (U : Set (Vec d))),
      (addConstSkewCoeffOn (cutoffCoeffOnL U nu hnu omega L) hk0).toCoeffField
          x =
        (cutoffCoeffOnM U nu hnu omega m).toCoeffField x +
          (finiteShellIncrement omega m L x -
            volumeAverageMat (U : Set (Vec d))
              (fun y => finiteShellIncrement omega m L y)) := by
    refine Filter.Eventually.of_forall fun x => ?_
    rw [addConstSkewCoeffOn_toCoeffField, cutoffCoeffOnL_toCoeffField,
      cutoffCoeffOnM_toCoeffField]
    have h1 : (coefficientCutoff nu omega L).toCoeffField x =
        (coefficientCutoff nu omega m).toCoeffField x +
          finiteShellIncrement omega m L x := by
      rw [← hincr_sub x]
      abel
    show (coefficientCutoff nu omega L).toCoeffField x +
        -volumeAverageMat (U : Set (Vec d))
          (fun y => finiteShellIncrement omega m L y) =
      (coefficientCutoff nu omega m).toCoeffField x +
        (finiteShellIncrement omega m L x -
          volumeAverageMat (U : Set (Vec d))
            (fun y => finiteShellIncrement omega m L y))
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
        (addConstSkewCoeffOn (cutoffCoeffOnL U nu hnu omega L) hk0))
      ((1 + localizationTheta nu n m L omega *
          (1 + localizationTheta nu n m L omega)) •
        Book.Ch02.coarseBlockMatrix U (cutoffCoeffOnM U nu hnu omega m)) :=
    coarseBlockMatrix_blockMatLoewnerLE_smul hb hskew hbound
  have hrev : BlockMatLoewnerLE
      (Book.Ch02.coarseBlockMatrix U (cutoffCoeffOnM U nu hnu omega m))
      ((1 + localizationTheta nu n m L omega *
          (1 + localizationTheta nu n m L omega)) •
        Book.Ch02.coarseBlockMatrix U
          (addConstSkewCoeffOn (cutoffCoeffOnL U nu hnu omega L) hk0)) := by
    intro X
    rw [blockMatVecMul_blockSMul, blockVecDot_smul_right]
    exact mul_le_mul_of_nonneg_left
      (coarseBlockMatrix_le_add_skew hb hskew hbound X) (by linarith only : (0:ℝ) ≤ 1/2)
  -- The two `bfA`'s as gauge conjugates of block-diagonal matrices.
  have hdecL := coarseBlockMatrix_eq_blockG_conj U (cutoffCoeffOnL U nu hnu omega L)
  have hdecM := coarseBlockMatrix_eq_blockG_conj U (cutoffCoeffOnM U nu hnu omega m)
  have hbfAb : Book.Ch02.coarseBlockMatrix U
      (addConstSkewCoeffOn (cutoffCoeffOnL U nu hnu omega L) hk0) =
      blockMatMul
        (blockMatTranspose (blockG (volumeAverageMat (U : Set (Vec d))
            (fun y => finiteShellIncrement omega m L y) -
          Book.Ch02.kappaCoarse U (cutoffCoeffOnL U nu hnu omega L))))
        (blockMatMul
          (blockDiag (Book.Ch02.sigmaCoarse U (cutoffCoeffOnL U nu hnu omega L))
            (Book.Ch02.sigmaStarInvCoarse U (cutoffCoeffOnL U nu hnu omega L)))
          (blockG (volumeAverageMat (U : Set (Vec d))
            (fun y => finiteShellIncrement omega m L y) -
          Book.Ch02.kappaCoarse U (cutoffCoeffOnL U nu hnu omega L)))) := by
    rw [coarseBlockMatrix_addConstSkewCoeffOn
      (cutoffCoeffOnL U nu hnu omega L) hk0, neg_neg, hdecL, blockG_conj_mul]
    rw [show -(Book.Ch02.kappaCoarse U (cutoffCoeffOnL U nu hnu omega L)) +
        volumeAverageMat (U : Set (Vec d))
          (fun y => finiteShellIncrement omega m L y) =
      volumeAverageMat (U : Set (Vec d))
        (fun y => finiteShellIncrement omega m L y) -
      Book.Ch02.kappaCoarse U (cutoffCoeffOnL U nu hnu omega L) from
      by abel]
  -- Transport each sandwich to an un-conjugated right side.
  rw [hbfAb, hdecM] at hfwd
  rw [hbfAb, hdecM] at hrev
  have hsandF := blockMatLoewnerLE_shift_gauge
    (a := volumeAverageMat (U : Set (Vec d))
      (fun y => finiteShellIncrement omega m L y) -
      Book.Ch02.kappaCoarse U (cutoffCoeffOnL U nu hnu omega L))
    (b := -(Book.Ch02.kappaCoarse U (cutoffCoeffOnM U nu hnu omega m))) hfwd
  have hsandR := blockMatLoewnerLE_shift_gauge
    (a := -(Book.Ch02.kappaCoarse U (cutoffCoeffOnM U nu hnu omega m)))
    (b := volumeAverageMat (U : Set (Vec d))
      (fun y => finiteShellIncrement omega m L y) -
      Book.Ch02.kappaCoarse U (cutoffCoeffOnL U nu hnu omega L)) hrev
  -- The two extractions that feed the printed amplitude: the upper-left
  -- blocks with the conjugate kept.
  have hupF := matLoewnerLE_upperLeft_add_of_blockMatLoewnerLE_conj_blockG _ hsandF
  have hupR := matLoewnerLE_upperLeft_add_of_blockMatLoewnerLE_conj_blockG _ hsandR
  -- The witness and the gauge conversions.
  have hθ : 0 ≤ localizationTheta nu n m L omega :=
    localizationTheta_nonneg nu hnu.le n m L omega
  have hD : 0 ≤ localizationD nu n m L omega := by
    show 0 ≤ localizationTheta nu n m L omega *
      (1 + localizationTheta nu n m L omega)
    exact mul_nonneg hθ (by linarith only [hθ])
  have hDfwd :
      (1 + localizationTheta nu n m L omega *
          (1 + localizationTheta nu n m L omega)) =
      1 + localizationD nu n m L omega := rfl
  have hghF : ((volumeAverageMat (U : Set (Vec d))
        (fun y => finiteShellIncrement omega m L y) -
        Book.Ch02.kappaCoarse U (cutoffCoeffOnL U nu hnu omega L)) -
        -(Book.Ch02.kappaCoarse U (cutoffCoeffOnM U nu hnu omega m))) =
      -(Book.Ch02.kappaCoarse U (cutoffCoeffOnL U nu hnu omega L) -
        Book.Ch02.kappaCoarse U (cutoffCoeffOnM U nu hnu omega m) -
        volumeAverageMat (U : Set (Vec d))
          (fun y => finiteShellIncrement omega m L y)) := by
    abel
  have hghR : ((-(Book.Ch02.kappaCoarse U (cutoffCoeffOnM U nu hnu omega m))) -
        (volumeAverageMat (U : Set (Vec d))
          (fun y => finiteShellIncrement omega m L y) -
        Book.Ch02.kappaCoarse U (cutoffCoeffOnL U nu hnu omega L))) =
      (Book.Ch02.kappaCoarse U (cutoffCoeffOnL U nu hnu omega L) -
        Book.Ch02.kappaCoarse U (cutoffCoeffOnM U nu hnu omega m) -
        volumeAverageMat (U : Set (Vec d))
          (fun y => finiteShellIncrement omega m L y)) := by
    abel
  -- The carrier bridges to the raw statement of conjunct 2.
  have hσL : Homogenization.sigmaCoarse (U : Set (Vec d))
        (coefficientCutoff nu omega L).toCoeffField =
      Book.Ch02.sigmaCoarse U (cutoffCoeffOnL U nu hnu omega L) :=
    sigmaCoarse_toCoeffField U (cutoffCoeffOnL U nu hnu omega L)
  have hκL : Homogenization.kappaCoarse (U : Set (Vec d))
        (coefficientCutoff nu omega L).toCoeffField =
      Book.Ch02.kappaCoarse U (cutoffCoeffOnL U nu hnu omega L) :=
    kappaCoarse_toCoeffField U (cutoffCoeffOnL U nu hnu omega L)
  have hκM : Homogenization.kappaCoarse (U : Set (Vec d))
        (coefficientCutoff nu omega m).toCoeffField =
      Book.Ch02.kappaCoarse U (cutoffCoeffOnM U nu hnu omega m) :=
    kappaCoarse_toCoeffField U (cutoffCoeffOnM U nu hnu omega m)
  have hinvL : (Homogenization.sigmaStarCoarse (U : Set (Vec d))
          (coefficientCutoff nu omega L).toCoeffField)⁻¹ =
      Book.Ch02.sigmaStarInvCoarse U (cutoffCoeffOnL U nu hnu omega L) :=
    Eq.trans (inv_sigmaStarCoarse U (cutoffCoeffOnL U nu hnu omega L))
      (sigmaStarInvCoarse_toCoeffField U (cutoffCoeffOnL U nu hnu omega L))
  -- The three quadratic-form relations, at `p`.
  intro p
  have h1 : vecDot p (matVecMul (Book.Ch02.sigmaCoarse U
            (cutoffCoeffOnL U nu hnu omega L)) p)
        + vecDot (matVecMul (Book.Ch02.kappaCoarse U (cutoffCoeffOnL U nu hnu omega L) -
              Book.Ch02.kappaCoarse U (cutoffCoeffOnM U nu hnu omega m) -
            volumeAverageMat (U : Set (Vec d))
              (fun y => finiteShellIncrement omega m L y)) p)
          (matVecMul (Book.Ch02.sigmaStarInvCoarse U (cutoffCoeffOnL U nu hnu omega L))
            (matVecMul (Book.Ch02.kappaCoarse U (cutoffCoeffOnL U nu hnu omega L) -
                Book.Ch02.kappaCoarse U (cutoffCoeffOnM U nu hnu omega m) -
              volumeAverageMat (U : Set (Vec d))
                (fun y => finiteShellIncrement omega m L y)) p))
      ≤ (1 + localizationD nu n m L omega) * vecDot p (matVecMul
          (Book.Ch02.sigmaCoarse U (cutoffCoeffOnM U nu hnu omega m)) p) := by
    have hx := hupF p
    rw [vecDot_matVecMul_add_conj_mul
        (A := Book.Ch02.sigmaCoarse U (cutoffCoeffOnL U nu hnu omega L))
        (B := Book.Ch02.sigmaStarInvCoarse U (cutoffCoeffOnL U nu hnu omega L))
        ((volumeAverageMat (U : Set (Vec d))
            (fun y => finiteShellIncrement omega m L y) -
          Book.Ch02.kappaCoarse U (cutoffCoeffOnL U nu hnu omega L)) -
          -(Book.Ch02.kappaCoarse U (cutoffCoeffOnM U nu hnu omega m))) p,
      quad_congr_neg (Book.Ch02.sigmaStarInvCoarse U (cutoffCoeffOnL U nu hnu omega L))
        hghF p, smul_matVecMul, vecDot_smul_right, hDfwd] at hx
    linarith only [hx]
  have h2 : vecDot p (matVecMul (Book.Ch02.sigmaCoarse U
            (cutoffCoeffOnM U nu hnu omega m)) p)
        + vecDot (matVecMul (Book.Ch02.kappaCoarse U (cutoffCoeffOnL U nu hnu omega L) -
              Book.Ch02.kappaCoarse U (cutoffCoeffOnM U nu hnu omega m) -
            volumeAverageMat (U : Set (Vec d))
              (fun y => finiteShellIncrement omega m L y)) p)
          (matVecMul (Book.Ch02.sigmaStarInvCoarse U (cutoffCoeffOnM U nu hnu omega m))
            (matVecMul (Book.Ch02.kappaCoarse U (cutoffCoeffOnL U nu hnu omega L) -
                Book.Ch02.kappaCoarse U (cutoffCoeffOnM U nu hnu omega m) -
              volumeAverageMat (U : Set (Vec d))
                (fun y => finiteShellIncrement omega m L y)) p))
      ≤ (1 + localizationD nu n m L omega) * vecDot p (matVecMul
          (Book.Ch02.sigmaCoarse U (cutoffCoeffOnL U nu hnu omega L)) p) := by
    have hx := hupR p
    rw [vecDot_matVecMul_add_conj_mul
        (A := Book.Ch02.sigmaCoarse U (cutoffCoeffOnM U nu hnu omega m))
        (B := Book.Ch02.sigmaStarInvCoarse U (cutoffCoeffOnM U nu hnu omega m))
        (-(Book.Ch02.kappaCoarse U (cutoffCoeffOnM U nu hnu omega m)) -
          (volumeAverageMat (U : Set (Vec d))
            (fun y => finiteShellIncrement omega m L y) -
          Book.Ch02.kappaCoarse U (cutoffCoeffOnL U nu hnu omega L))) p,
      quad_congr (Book.Ch02.sigmaStarInvCoarse U (cutoffCoeffOnM U nu hnu omega m))
        hghR p, smul_matVecMul, vecDot_smul_right, hDfwd] at hx
    linarith only [hx]
  -- The nonnegativity of the discarded conjugate term on the backward side.
  have hv0 : 0 ≤ vecDot
      (matVecMul (Book.Ch02.kappaCoarse U (cutoffCoeffOnL U nu hnu omega L) -
          Book.Ch02.kappaCoarse U (cutoffCoeffOnM U nu hnu omega m) -
        volumeAverageMat (U : Set (Vec d))
          (fun y => finiteShellIncrement omega m L y)) p)
      (matVecMul (Book.Ch02.sigmaStarInvCoarse U (cutoffCoeffOnM U nu hnu omega m))
        (matVecMul (Book.Ch02.kappaCoarse U (cutoffCoeffOnL U nu hnu omega L) -
            Book.Ch02.kappaCoarse U (cutoffCoeffOnM U nu hnu omega m) -
          volumeAverageMat (U : Set (Vec d))
            (fun y => finiteShellIncrement omega m L y)) p)) :=
    vecDot_matVecMul_sigmaStarInvCoarse_nonneg U
      (cutoffCoeffOnM U nu hnu omega m)
      (matVecMul (Book.Ch02.kappaCoarse U (cutoffCoeffOnL U nu hnu omega L) -
          Book.Ch02.kappaCoarse U (cutoffCoeffOnM U nu hnu omega m) -
        volumeAverageMat (U : Set (Vec d))
          (fun y => finiteShellIncrement omega m L y)) p)
  -- The scalar chain.
  have hu2 : vecDot (matVecMul (Book.Ch02.kappaCoarse U (cutoffCoeffOnL U nu hnu omega L) -
        Book.Ch02.kappaCoarse U (cutoffCoeffOnM U nu hnu omega m) -
      volumeAverageMat (U : Set (Vec d))
        (fun y => finiteShellIncrement omega m L y)) p)
      (matVecMul (Book.Ch02.sigmaStarInvCoarse U (cutoffCoeffOnL U nu hnu omega L))
        (matVecMul (Book.Ch02.kappaCoarse U (cutoffCoeffOnL U nu hnu omega L) -
            Book.Ch02.kappaCoarse U (cutoffCoeffOnM U nu hnu omega m) -
          volumeAverageMat (U : Set (Vec d))
            (fun y => finiteShellIncrement omega m L y)) p))
    ≤ (2 * localizationD nu n m L omega +
        localizationD nu n m L omega * localizationD nu n m L omega) *
      vecDot p (matVecMul
        (Book.Ch02.sigmaCoarse U (cutoffCoeffOnL U nu hnu omega L)) p) :=
    scalarChain hD hv0 h1 h2
  -- The conclusion at `p`.
  have hamp : localizationD nu n m L omega * (2 + localizationD nu n m L omega)
      = 2 * localizationD nu n m L omega +
        localizationD nu n m L omega * localizationD nu n m L omega := by
    ring
  rw [hamp, smul_matVecMul, vecDot_smul_right, hinvL, hκL, hκM, hσL]
  have hkey : vecDot p (matVecMul
        (matTranspose (Book.Ch02.kappaCoarse U (cutoffCoeffOnL U nu hnu omega L) -
              Book.Ch02.kappaCoarse U (cutoffCoeffOnM U nu hnu omega m) -
            volumeAverageMat (U : Set (Vec d))
              (fun y => finiteShellIncrement omega m L y)) *
          Book.Ch02.sigmaStarInvCoarse U (cutoffCoeffOnL U nu hnu omega L) *
          (Book.Ch02.kappaCoarse U (cutoffCoeffOnL U nu hnu omega L) -
            Book.Ch02.kappaCoarse U (cutoffCoeffOnM U nu hnu omega m) -
            volumeAverageMat (U : Set (Vec d))
              (fun y => finiteShellIncrement omega m L y))) p)
      = vecDot (matVecMul (Book.Ch02.kappaCoarse U (cutoffCoeffOnL U nu hnu omega L) -
            Book.Ch02.kappaCoarse U (cutoffCoeffOnM U nu hnu omega m) -
          volumeAverageMat (U : Set (Vec d))
            (fun y => finiteShellIncrement omega m L y)) p)
        (matVecMul (Book.Ch02.sigmaStarInvCoarse U (cutoffCoeffOnL U nu hnu omega L))
          (matVecMul (Book.Ch02.kappaCoarse U (cutoffCoeffOnL U nu hnu omega L) -
              Book.Ch02.kappaCoarse U (cutoffCoeffOnM U nu hnu omega m) -
            volumeAverageMat (U : Set (Vec d))
              (fun y => finiteShellIncrement omega m L y)) p)) := by
    rw [← matVecMul_mul (matTranspose (Book.Ch02.kappaCoarse U
          (cutoffCoeffOnL U nu hnu omega L) -
        Book.Ch02.kappaCoarse U (cutoffCoeffOnM U nu hnu omega m) -
      volumeAverageMat (U : Set (Vec d))
        (fun y => finiteShellIncrement omega m L y)) *
      Book.Ch02.sigmaStarInvCoarse U (cutoffCoeffOnL U nu hnu omega L))
      (Book.Ch02.kappaCoarse U (cutoffCoeffOnL U nu hnu omega L) -
        Book.Ch02.kappaCoarse U (cutoffCoeffOnM U nu hnu omega m) -
      volumeAverageMat (U : Set (Vec d))
        (fun y => finiteShellIncrement omega m L y)) p]
    rw [← matVecMul_mul (matTranspose (Book.Ch02.kappaCoarse U
          (cutoffCoeffOnL U nu hnu omega L) -
        Book.Ch02.kappaCoarse U (cutoffCoeffOnM U nu hnu omega m) -
      volumeAverageMat (U : Set (Vec d))
        (fun y => finiteShellIncrement omega m L y)))
      (Book.Ch02.sigmaStarInvCoarse U (cutoffCoeffOnL U nu hnu omega L))
      (matVecMul (Book.Ch02.kappaCoarse U (cutoffCoeffOnL U nu hnu omega L) -
        Book.Ch02.kappaCoarse U (cutoffCoeffOnM U nu hnu omega m) -
      volumeAverageMat (U : Set (Vec d))
        (fun y => finiteShellIncrement omega m L y)) p)]
    exact vecDot_matVecMul_transpose p
      (matVecMul (Book.Ch02.sigmaStarInvCoarse U (cutoffCoeffOnL U nu hnu omega L))
        (matVecMul (Book.Ch02.kappaCoarse U (cutoffCoeffOnL U nu hnu omega L) -
            Book.Ch02.kappaCoarse U (cutoffCoeffOnM U nu hnu omega m) -
          volumeAverageMat (U : Set (Vec d))
            (fun y => finiteShellIncrement omega m L y)) p))
      (Book.Ch02.kappaCoarse U (cutoffCoeffOnL U nu hnu omega L) -
        Book.Ch02.kappaCoarse U (cutoffCoeffOnM U nu hnu omega m) -
        volumeAverageMat (U : Set (Vec d))
          (fun y => finiteShellIncrement omega m L y))
  rw [hkey]
  linarith only [hu2]

end

end SuperdiffusionCLT.Section2.Localization