/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3BlupChain
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3BlupAssembly
public import SuperdiffusionCLT.Section3.Terms.BlupRemainderInputs

/-!
# The `hBlup` conjunct at the printed operator-norm slot

The term-level residue of the root theorem carries, inside an `∃ Zrem`-binder, the
pointwise remainder display

`∀ omega z, matrixOperatorNorm (b_{L'} − b_ℓ) ≤ 1 |b_ℓ| + (1 + 1⁻¹) q(e) + Zrem`

with `b_L = translatedCoarseBlock nu L omega z`, `|b_ℓ| = translatedBlockNorm
nu ℓ` and `q(e) = translatedStreamQuadFormLower nu ℓ L' e`.  That binder is called `hBlup`.

The display of `e.blupbounds` (with the supremum over `|e| = 1` taken later in
the proof) instead carries the **operator-norm square**
`|σ_{ℓ,*}^{-1/2}(U) (κ_{L'} − κ_ℓ)_U|²`, which is `translatedStreamSlot nu ℓ L'`.
Since `q(e) ≤ translatedStreamSlot` for every unit `e`, the clause with the tested form `q(e)`
is *stronger* than the print.

## Main results

* `translatedSigmaStarInvHalf`, `translatedStreamIncrementAvg` — the two printed
  carriers of the slot, `σ_{ℓ,*}^{-1/2}(z + cu_n)` and the averaged increment
  `h_{z + cu_n}`; `translatedStreamSlot_eq_halfMul_avg` writes the slot through
  them.
* `cutoffCoeffOnCh02`, `translatedBlockMat_eq_ch02_coarseBlockMatrix`,
  `translatedCoarseBlock_eq_ch02_bCoarse`, `translatedBlockMat_eq_blockRecord`,
  `translatedSigmaStarInvHalf_eq_ch02_sqrt` — **the printed input relations of
  `e.blupbounds` at the translated carriers**, each discharged without hypothesis
  beyond `0 < nu`: the doubled block in the Chapter 2 spelling, its block form
  `e.bigA.def` through the canonical coupling matrix and the
  canonical starred inverse, the identification of its upper-left block with
  `b_L(z + cu_n)`, and the transport of the square root carriers.
* `rootSlotDisplay_of_operatorNormCore` — **the `hBlup` conjunct restated at the printed
  operator-norm slot**, with `translatedStreamSlot nu S.ell S.LPrime` in the quadratic
  position in place of the tested form.  It is discharged from the deterministic core of
  the print (`blupbounds_operatorNorm_le`)
  instantiated at the concrete translated carriers; of the core's six printed
  input relations, five are discharged here — the carrier relation
  `b_L = bfA_L.upperLeft` by definition, the block form `e.bigA.def` by the
  lemmas above, the Gram property of the printed square root by
  `gramSqrt_sigmaStarInvCoarse_cutoffCube_forall`, the Cauchy-Schwarz input
  `κᵗ σ^{-1} κ ≤ b` by `kappaUpperLeft_quadratic_le_bCoarse` (transported along
  the identifications above), and the symmetry of `(b_{L'} − b_ℓ)(z + cu_n)` by
  `isSymm_sub_translatedCoarseBlock`.  **The single premise that remains is the
  paper's own remainder display `e.blupbounds.remainder` at those carriers** —
  the `Zrem` of the clause itself.  The tested form is never used, and the
  direction `e` does not occur outside that remainder display.

## The boundary, stated plainly

What is not proved here is the printed remainder display named above.  The
tested form itself is not attempted.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Setup

open MeasureTheory ProbabilityTheory
open Homogenization Homogenization.Book.Ch02 Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Section2.Annealed SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Localization
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Terms
open scoped ENNReal
open scoped BigOperators Matrix.Norms.Elementwise
open scoped MatrixOrder

noncomputable section

variable {d : ℕ}

/-! ## The printed carriers of the slot -/

/-- **The printed square root `σ_{ℓ,*}^{-1/2}(z + cu_n)`** at the translated
carriers: the positive-semidefinite square root of the coarse matrix
`σ_{ℓ,*}^{-1}(z + cu_n)` of the cutoff coefficient at the finer scale `ell`,
the object whose Gram property the printed proof uses. -/
noncomputable def translatedSigmaStarInvHalf (nu : ℝ) (ell : ℕ) (omega : ShellSeq d)
    (z : TriadicCube d) : Mat d :=
  CFC.sqrt (sigmaStarInvCoarse (cubeSet z) (coefficientCutoff nu omega ell).toCoeffField)

/-- **The averaged increment `h_{z + cu_n}` of the print**: the volume average
over the cube `z` of the finite shell increment between the fine scale `ell` and
the coarse scale `L` (`(κ_{L'} − κ_ℓ)_{z + cu_n}` read at the coarse cube `z`). -/
noncomputable def translatedStreamIncrementAvg (omega : ShellSeq d) (ell L : ℕ)
    (z : TriadicCube d) : Mat d :=
  volumeAverageMat (cubeSet z) (fun y => finiteShellIncrement omega ell L y)

/-- **The operator-norm slot through the two printed carriers**: the slot is the
square of the operator norm of `σ_{ℓ,*}^{-1/2}(z + cu_n) h_{z + cu_n}`, which is
the object the printed supremum bounds. -/
theorem translatedStreamSlot_eq_halfMul_avg (nu : ℝ) (ell L : ℕ)
    (omega : ShellSeq d) (z : TriadicCube d) :
    translatedStreamSlot nu ell L omega z =
      (matrixOperatorNorm
        (translatedSigmaStarInvHalf nu ell omega z *
          translatedStreamIncrementAvg omega ell L z)) ^ (2 : ℕ) := rfl

/-! ## The printed input relations of `e.blupbounds` at the translated carriers -/

/-- **The Chapter 2 coefficient object of the cutoff field on the cube
domain**: the canonical a.e.-elliptic representative of `a_L = coefficientCutoff
nu omega L` on `cubeDomain z`, the Chapter 2 vocabulary in which the doubled
block has its printed block form `e.bigA.def`. -/
noncomputable def cutoffCoeffOnCh02 (nu : ℝ) (hnu : 0 < nu) (omega : ShellSeq d)
    (L : ℕ) (z : TriadicCube d) : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain z) :=
  (Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField (coefficientCutoff nu omega L)
    (aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega L)).coeffOn z

/-- **`bfA_L(z + cu_n)` in the Chapter 2 spelling.**  The doubled coarse block
of the cutoff coefficient on the translated cube is the Chapter 2
`coarseBlockMatrix` of the canonical a.e.-elliptic representative on the cube
domain: the two restriction bridges of the translated-block development. -/
theorem translatedBlockMat_eq_ch02_coarseBlockMatrix [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (L : ℕ) (omega : ShellSeq d) (z : TriadicCube d) :
    translatedBlockMat nu L omega z =
      Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain z)
        (cutoffCoeffOnCh02 nu hnu omega L z) := by
  rw [translatedBlockMat, ← coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube z
      (coefficientCutoff nu omega L).toCoeffField,
    show coarseBlockMatrix (cubeSet z) (coefficientCutoff nu omega L).toCoeffField =
      Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain z)
        (cutoffCoeffOnCh02 nu hnu omega L z) from
      Book.Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
        (aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega L) z]

/-- **The identification of the upper-left block.**  The carrier
`b_L(z + cu_n) = translatedCoarseBlock` is the Chapter 2 `bCoarse` of the
canonical a.e.-elliptic representative on the cube domain: the previous theorem
read through the definition of `translatedCoarseBlock` and the projection
`Book.Ch02.coarseBlockMatrix_upperLeft`. -/
theorem translatedCoarseBlock_eq_ch02_bCoarse [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (L : ℕ) (omega : ShellSeq d) (z : TriadicCube d) :
    translatedCoarseBlock nu L omega z =
      Book.Ch02.bCoarse (Book.Ch02.cubeDomain z) (cutoffCoeffOnCh02 nu hnu omega L z) := by
  rw [translatedCoarseBlock, translatedBlockMat_eq_ch02_coarseBlockMatrix hnu L omega z,
    Book.Ch02.coarseBlockMatrix_upperLeft]

/-- **The printed block form `e.bigA.def` of `bfA_ℓ(z + cu_n)`,
discharged at the translated carriers.**  The doubled coarse block of the cutoff
coefficient at the scale `ell` is the block record whose upper-left entry is
`b_ℓ(z + cu_n)`, whose off-diagonal entries are the canonical coupling matrix
`κ_ℓ(z + cu_n)` against the canonical starred inverse `σ_{ℓ,*}^{-1}(z + cu_n)`,
and whose lower-right entry is that inverse.  This is the Chapter 2 record form
of `coarseBlockMatrix` carried along the previous two identifications. -/
theorem translatedBlockMat_eq_blockRecord [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (L : ℕ) (omega : ShellSeq d) (z : TriadicCube d) :
    translatedBlockMat nu L omega z =
      { upperLeft := translatedCoarseBlock nu L omega z
        upperRight := -(matTranspose (Book.Ch02.kappaCoarse (Book.Ch02.cubeDomain z)
            (cutoffCoeffOnCh02 nu hnu omega L z)) *
          Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain z)
            (cutoffCoeffOnCh02 nu hnu omega L z))
        lowerLeft := -(Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain z)
            (cutoffCoeffOnCh02 nu hnu omega L z) *
          Book.Ch02.kappaCoarse (Book.Ch02.cubeDomain z) (cutoffCoeffOnCh02 nu hnu omega L z))
        lowerRight := Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain z)
          (cutoffCoeffOnCh02 nu hnu omega L z) } := by
  rw [translatedBlockMat_eq_ch02_coarseBlockMatrix hnu L omega z,
    translatedCoarseBlock_eq_ch02_bCoarse hnu L omega z]
  rfl

/-- **The printed square root in the Chapter 2 spelling.**  The square root
carrier of the slot, read at the half-open cube `cubeSet z`, is the square root
of the Chapter 2 starred inverse of the same coefficient object: the bridge
between the two realizations of the cube, after which the comparison is closed
by the definitional identification of the Chapter 2 vocabulary with the raw one
(the `Section2.CoarseGraining` correspondence). -/
theorem translatedSigmaStarInvHalf_eq_ch02_sqrt [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (L : ℕ) (omega : ShellSeq d) (z : TriadicCube d) :
    translatedSigmaStarInvHalf nu L omega z =
      CFC.sqrt (Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain z)
        (cutoffCoeffOnCh02 nu hnu omega L z)) := by
  rw [translatedSigmaStarInvHalf, sigmaStarInvCoarse_cubeSet_eq_openCubeSet z
      (coefficientCutoff nu omega L).toCoeffField,
    ← Book.Ch02.cubeDomain_coe]
  congr 1

/-! ## The root's clause at the printed slot, from the printed core -/

/-- **The root's `hBlup` conjunct at the printed operator-norm slot, from the
deterministic core of `e.blupbounds` at one point.**  The core
`blupbounds_operatorNorm_le` is instantiated at the concrete translated carriers
of `(omega, z)`: `b_{L'} = translatedCoarseBlock nu S.LPrime omega z`,
`b_ℓ = translatedCoarseBlock nu S.ell omega z`, the printed square root
`translatedSigmaStarInvHalf nu S.ell omega z`, the averaged increment
`translatedStreamIncrementAvg omega S.ell S.LPrime z`, at `ep = 1` and remainder
`Zrem omega z`.  Its conclusion is the root's display with
`translatedStreamSlot` in the quadratic position.

Five of the core's six printed input relations are discharged here: `b_L =
bfA_L.upperLeft` by definition (`rfl`), the block form `e.bigA.def` by
`translatedBlockMat_eq_blockRecord`, the Gram property of the printed square
root by `gramSqrt_sigmaStarInvCoarse_cutoffCube_forall` transported along
`translatedSigmaStarInvHalf_eq_ch02_sqrt`, the symmetry of the difference by
`isSymm_sub_translatedCoarseBlock`, and the Cauchy-Schwarz input
`κᵗ σ^{-1} κ ≤ b` by `kappaUpperLeft_quadratic_le_bCoarse` transported along
`translatedCoarseBlock_eq_ch02_bCoarse` and
`translatedSigmaStarInvHalf_eq_ch02_sqrt`.  **The one remaining premise is
`hRem`, the manuscript's remainder display `e.blupbounds.remainder` at those carriers.** -/
theorem rootSlotDisplay_of_operatorNormCore [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (S : ScaleSelection) (omega : ShellSeq d) (z : TriadicCube d)
    (Zrem : ShellSeq d → TriadicCube d → ℝ)
    (hRem : ∀ e : Vec d, vecNormSq e = 1 →
      |blockVecDot
          (blockMatVecMul
            (blockG (-(translatedStreamIncrementAvg omega S.ell S.LPrime z)))
            ((e, 0) : BlockVec d))
          (blockMatVecMul
            (blockMatMul
              (blockGT (translatedStreamIncrementAvg omega S.ell S.LPrime z))
              (blockMatMul (translatedBlockMat nu S.LPrime omega z)
                (blockG (translatedStreamIncrementAvg omega S.ell S.LPrime z))))
            (blockMatVecMul
              (blockG (-(translatedStreamIncrementAvg omega S.ell S.LPrime z)))
              ((e, 0) : BlockVec d))) -
        blockVecDot
          (blockMatVecMul
            (blockG (-(translatedStreamIncrementAvg omega S.ell S.LPrime z)))
            ((e, 0) : BlockVec d))
          (blockMatVecMul (translatedBlockMat nu S.ell omega z)
            (blockMatVecMul
              (blockG (-(translatedStreamIncrementAvg omega S.ell S.LPrime z)))
              ((e, 0) : BlockVec d)))| ≤ Zrem omega z) :
    matrixOperatorNorm
        (translatedCoarseBlock nu S.LPrime omega z -
          translatedCoarseBlock nu S.ell omega z) ≤
      1 * translatedBlockNorm nu S.ell omega z +
        (1 + (1 : ℝ)⁻¹) * translatedStreamSlot nu S.ell S.LPrime omega z +
        Zrem omega z := by
  have hAM := translatedBlockMat_eq_blockRecord hnu S.ell omega z
  have hSqrt : matTranspose (translatedSigmaStarInvHalf nu S.ell omega z) *
      translatedSigmaStarInvHalf nu S.ell omega z =
      Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain z)
        (cutoffCoeffOnCh02 nu hnu omega S.ell z) :=
    (gramSqrt_sigmaStarInvCoarse_cutoffCube_forall hnu S.ell omega z).trans
      (by rw [sigmaStarInvCoarse_cubeSet_eq_openCubeSet z
            (coefficientCutoff nu omega S.ell).toCoeffField,
          ← Book.Ch02.cubeDomain_coe]
          exact SuperdiffusionCLT.Section2.CoarseGraining.sigmaStarInvCoarse_toCoeffField
            (Book.Ch02.cubeDomain z) (cutoffCoeffOnCh02 nu hnu omega S.ell z))
  have hSym := isSymm_sub_translatedCoarseBlock hnu S.LPrime S.ell omega z
  have hKB : ∀ e : Vec d,
      vecNormSq (matVecMul (translatedSigmaStarInvHalf nu S.ell omega z)
        (matVecMul (Book.Ch02.kappaCoarse (Book.Ch02.cubeDomain z)
          (cutoffCoeffOnCh02 nu hnu omega S.ell z)) e)) ≤
      vecDot e (matVecMul (translatedCoarseBlock nu S.ell omega z) e) := by
    intro e
    have h := kappaUpperLeft_quadratic_le_bCoarse (Book.Ch02.cubeDomain z)
      (cutoffCoeffOnCh02 nu hnu omega S.ell z) e
    rw [← translatedCoarseBlock_eq_ch02_bCoarse hnu S.ell omega z,
      ← translatedSigmaStarInvHalf_eq_ch02_sqrt hnu S.ell omega z] at h
    exact h
  have hcore := blupbounds_operatorNorm_le 1 (by norm_num)
    (translatedBlockMat nu S.LPrime omega z) (translatedBlockMat nu S.ell omega z)
    (translatedCoarseBlock nu S.LPrime omega z) (translatedCoarseBlock nu S.ell omega z)
    (Book.Ch02.kappaCoarse (Book.Ch02.cubeDomain z)
      (cutoffCoeffOnCh02 nu hnu omega S.ell z))
    (Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain z)
      (cutoffCoeffOnCh02 nu hnu omega S.ell z))
    (translatedSigmaStarInvHalf nu S.ell omega z)
    (translatedStreamIncrementAvg omega S.ell S.LPrime z) (Zrem omega z)
    rfl hAM hSqrt hKB hSym hRem
  simpa only [translatedStreamSlot, translatedBlockNorm, translatedSigmaStarInvHalf,
    translatedStreamIncrementAvg] using hcore

/-! ## The bridge: the printed form drives the consuming step of the chain -/

end

end SuperdiffusionCLT.Section3.Setup
