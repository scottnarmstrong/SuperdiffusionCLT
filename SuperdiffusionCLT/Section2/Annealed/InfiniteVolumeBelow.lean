/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Carriers.AnnealedBlockInfinite

/-!
# The ellipticity sandwich `bfAhom_m ≤ bfAhom_m(cu_n) ≤ bfE_m`

The pigeonhole subargument underlying [AK, Lemma 3.4] sets
`A_k := bfAhom_L(cu_k)` and uses the chain of matrix inequalities

> `bfAhom_L ≤ A_k ≤ bfE_L`,

citing the monotone nonincreasing character of `n ↦ bfAhom_m(cu_n)` (the
sentence before `e.homs.defs`) and the ellipticity lemma `l.bfAm.ellip`. This module proves
that chain for the origin cubes.

## The two halves

* **The left half** `bfAhom_m ≤ bfAhom_m(cu_n)`: the infinite-volume annealed
  block matrix `annealedBlockMatInfinite` of
  `Section2/Carriers/AnnealedBlockInfinite.lean` is the entrywise infimum of the
  sequence `n ↦ bfAhom_m(cu_n)`, and the sequence is nonincreasing
  (`Section2/Annealed/InfiniteVolume.lean`), so the infimum lies below every
  term.
* **The right half** `bfAhom_m(cu_n) ≤ bfE_m`: lemma `l.bfAm.ellip` is stated in
  `Envelope.lean` in the *normalized* form
  `bfE_m^{-1/2} bfAhom_m(cu_n) bfE_m^{-1/2} ≤ I_{2d}`
  (`blockMatLoewnerLE_envelopeRescale_annealedBlockMatrix`, for an arbitrary
  bounded Lipschitz domain). The quadratic-form inequality behind it,
  `blockVecDot_annealedBlockMatrix_le`, bounds the doubled quadratic form of
  `bfAhom_m(cu_Q)` by the doubled quadratic form of `bfE_m` itself, so the un-normalized inequality
  `bfAhom_m(cu_n) ≤ bfE_m`, the printed form, is available directly and is the form in which the
  chain is stated here. The rescaled form of the full chain is recorded as well.

## Reduction to scalars

Under J4 both sides of the left comparison and both sides of the right
comparison are block diagonal with scalar blocks (`e.homs.defs.U`), so each Loewner
comparison reduces to two scalar inequalities:

* left: `sigmaBarUpperLimit ≤ sigmaBarSeq n` and
  `sigmaBarStarInvLimit ≤ sigmaBarStarInvSeq n`, the `ciInf_le` facts
  `sigmaBarUpperLimit_le` and `sigmaBarStarInvLimit_le` of
  `InfiniteVolume.lean`;
* right: `sigmaBarSeq n ≤ envelopeUpperScalar d nu m`, proved below from the
  quadratic-form bound at a coordinate vector, and
  `sigmaBarStarInvSeq n ≤ envelopeLowerScalar d nu`, which is
  `sigmaBarStarInvSeq_le_envelopeLowerScalar` of `InfiniteVolume.lean`.

## Main results

* `blockVecDot_annealedBlockMatInfinite`,
  `blockVecDot_annealedBlockMatrix_originCube`: the doubled quadratic forms of
  bfAhom_m and of `bfAhom_m(cu_n)` as scalar quadratic forms in the two scalars.
* `blockMatLoewnerLE_annealedBlockMatInfinite_originCube`: the left half.
* `sigmaBarSeq_le_envelopeUpperScalar`: the right half, as an inequality of the upper-left scalar
  `sigmaBarSeq n` with the upper-left scalar of the envelope.
* `blockMatLoewnerLE_envelopeRescale_annealedBlockMatInfinite_originCube`: the left half in the
  `envelopeRescale` normalization of `Envelope.lean`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Annealed

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## Scalar helpers

Under J4 the two diagonal blocks of `bfAhom_m(cu_n)` and of bfAhom_m are scalar
matrices, and the quadratic form of a scalar block-diagonal matrix factors
through the two scalars. The two private lemmas below identify that quadratic
form; `blockVecDot_blockDiag_smul_one` of `Envelope.lean` is its counterpart
for a literal `blockDiag`. -/

private theorem matVecMulOneS (x : Vec d) : matVecMul (1 : Mat d) x = x := by
  funext i
  simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]

private theorem vecDotSmulOneS {c : ℝ} (x : Vec d) :
    vecDot x (matVecMul (c • (1 : Mat d)) x) = c * vecNormSq x := by
  rw [smul_matVecMul, matVecMulOneS, vecDot_smul_right]
  rfl

private theorem matVecMulZeroS (x : Vec d) : matVecMul (0 : Mat d) x = 0 := by
  funext i
  simp [matVecMul]

private theorem vecNormSqZeroS : vecNormSq (0 : Vec d) = 0 := by
  show vecDot (0 : Vec d) (0 : Vec d) = 0
  rw [vecDot_zero_left]

private theorem vecNormSqSingleS (i : Fin d) :
    vecNormSq (Pi.single i (1 : ℝ)) = 1 := by
  rw [vecNormSq, vecDot_single_left]
  simp

/-! ## The quadratic forms of the two block-diagonal matrices -/

section QuadraticForms

variable [NeZero d] {nu : ℝ} (hnu : 0 < nu) (m : ℕ)
  {P : ProbabilityMeasure (ShellSeq d)} (hJ4 : ShellLawJ4 d P)

include hnu hJ4

/-- **The doubled quadratic form of bfAhom_m** as a scalar quadratic form in
the two limits of `InfiniteVolume.lean`: both diagonal blocks of the
infinite-volume matrix are scalar matrices (`Carriers.annealedBlockMatInfinite`
under J4), so the form is `shom_m |p|² + shom_{m,*}^{-1} |q|²`. -/
theorem blockVecDot_annealedBlockMatInfinite (p q : Vec d) :
    blockVecDot (p, q)
        (blockMatVecMul (Carriers.annealedBlockMatInfinite nu m P) (p, q)) =
      sigmaBarUpperLimit nu m P * vecNormSq p +
        sigmaBarStarInvLimit nu m P * vecNormSq q := by
  rw [Carriers.annealedBlockMatInfinite_eq_blockDiag hnu m hJ4,
    blockVecDot_blockDiag_smul_one]

/-- **The doubled quadratic form of `bfAhom_m(cu_n)` on an origin cube** as a
scalar quadratic form in the two scalars `shom_m(cu_n)` and
`shom_{m,*}^{-1}(cu_n)`: the off-diagonal blocks vanish and the diagonal blocks
are scalar matrices (`e.homs.defs.U`). -/
theorem blockVecDot_annealedBlockMatrix_originCube (n : ℕ) (p q : Vec d) :
    blockVecDot (p, q)
        (blockMatVecMul
          (annealedBlockMatrix nu m P (cubeSet (originCube d (n : ℤ)))) (p, q)) =
      sigmaBarSeq nu m P n * vecNormSq p +
        sigmaBarStarInvSeq nu m P n * vecNormSq q := by
  have hUL : (annealedBlockMatrix nu m P (cubeSet (originCube d (n : ℤ)))).upperLeft =
      sigmaBarSeq nu m P n • (1 : Mat d) := by
    rw [annealedBlockMatrix_originCube_upperLeft_eq_sigmaBar hnu m hJ4 (n : ℤ),
      sigmaBar_originCube_eq_smul_one hnu m hJ4 (n : ℤ)]
    rfl
  have hUR : (annealedBlockMatrix nu m P (cubeSet (originCube d (n : ℤ)))).upperRight =
      (0 : Mat d) := annealedBlockMatrix_originCube_upperRight_eq_zero hnu m hJ4 (n : ℤ)
  have hLL : (annealedBlockMatrix nu m P (cubeSet (originCube d (n : ℤ)))).lowerLeft =
      (0 : Mat d) := annealedBlockMatrix_originCube_lowerLeft_eq_zero hnu m hJ4 (n : ℤ)
  have hLR : (annealedBlockMatrix nu m P (cubeSet (originCube d (n : ℤ)))).lowerRight =
      sigmaBarStarInvSeq nu m P n • (1 : Mat d) := by
    rw [show (annealedBlockMatrix nu m P (cubeSet (originCube d (n : ℤ)))).lowerRight =
      sigmaBarStarInv nu m P (cubeSet (originCube d (n : ℤ))) from rfl,
      sigmaBarStarInv_originCube_eq_smul_one hnu m hJ4 (n : ℤ)]
    rfl
  rw [blockQuadratic_eq, hUL, hUR, hLL, hLR, vecDotSmulOneS, vecDotSmulOneS,
    matVecMulZeroS, matVecMulZeroS, vecDot_zero_right, vecDot_zero_right]
  ring

end QuadraticForms

/-! ## The sandwich `bfAhom_m ≤ bfAhom_m(cu_n) ≤ bfE_m` -/

section Sandwich

variable [NeZero d] {nu : ℝ} (hnu : 0 < nu) (m : ℕ)
  {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
  (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)

include hnu hPrefix hJ2 hJ3 hJ4

/-- **The upper scalar of the envelope bounds the scalar of the cube**: the
scalar of `shom_m(cu_n)` is below the upper-left scalar of the envelope `bfE_m`.
It is the quadratic-form bound of `Envelope.lean` tested at the first coordinate
vector in the upper block and at zero in the lower block. -/
theorem sigmaBarSeq_le_envelopeUpperScalar (n : ℕ) :
    sigmaBarSeq nu m P n ≤ envelopeUpperScalar d nu m := by
  have h := blockVecDot_annealedBlockMatrix_le hnu m (originCube d (n : ℤ)) hPrefix
    hJ2 hJ3 hJ4 (Pi.single (0 : Fin d) (1 : ℝ)) (0 : Vec d)
  rw [blockVecDot_annealedBlockMatrix_originCube hnu m hJ4 n, vecNormSqSingleS,
    vecNormSqZeroS] at h
  simpa only [mul_one, mul_zero, add_zero] using h

/-- **The left half of the sandwich**: the infinite-volume
annealed block matrix bfAhom_m lies below the annealed block matrix of every
origin cube, `bfAhom_m ≤ bfAhom_m(cu_n)`. Both matrices are block diagonal with
scalar blocks under J4, so the comparison is the pair of scalar inequalities
`sigmaBarUpperLimit_le` and `sigmaBarStarInvLimit_le`. -/
theorem blockMatLoewnerLE_annealedBlockMatInfinite_originCube (n : ℕ) :
    BlockMatLoewnerLE (Carriers.annealedBlockMatInfinite nu m P)
      (annealedBlockMatrix nu m P (cubeSet (originCube d (n : ℤ)))) := by
  rintro ⟨p, q⟩
  rw [blockVecDot_annealedBlockMatInfinite hnu m hJ4 p q,
    blockVecDot_annealedBlockMatrix_originCube hnu m hJ4 n p q]
  have h1 := mul_le_mul_of_nonneg_left
    (sigmaBarUpperLimit_le hnu m hPrefix hJ2 hJ3 hJ4 n) (vecNormSq_nonneg p)
  have h2 := mul_le_mul_of_nonneg_left
    (sigmaBarStarInvLimit_le hnu m hPrefix hJ2 hJ3 hJ4 n) (vecNormSq_nonneg q)
  linarith only [h1, h2]

/-! ### The chain in the `envelopeRescale` normalization

`Envelope.lean` proves the annealed half of `l.bfAm.ellip` in the normalized
form `bfE_m^{-1/2} bfAhom_m(cu_Q) bfE_m^{-1/2} ≤ I_{2d}` for an arbitrary bounded
Lipschitz domain. Since conjugation by the fixed matrix `envelopeInvSqrt`
preserves the block Loewner order, the left half of the sandwich transports to
the normalized form, and the two halves compose there as well. -/

/-- The left half of the sandwich in the `envelopeRescale` normalization:
`bfE_m^{-1/2} bfAhom_m bfE_m^{-1/2} ≤ bfE_m^{-1/2} bfAhom_m(cu_n) bfE_m^{-1/2}`. -/
theorem blockMatLoewnerLE_envelopeRescale_annealedBlockMatInfinite_originCube
    (n : ℕ) :
    BlockMatLoewnerLE
      (envelopeRescale d nu m (Carriers.annealedBlockMatInfinite nu m P))
      (envelopeRescale d nu m
        (annealedBlockMatrix nu m P (cubeSet (originCube d (n : ℤ))))) :=
  blockMatLoewnerLE_envelopeRescale d nu m
    (blockMatLoewnerLE_annealedBlockMatInfinite_originCube hnu m hPrefix hJ2 hJ3 hJ4
      n)

end Sandwich

end

end SuperdiffusionCLT.Section2.Annealed