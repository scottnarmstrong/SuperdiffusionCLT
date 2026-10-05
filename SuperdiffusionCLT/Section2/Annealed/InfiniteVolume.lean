/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellLaw.BlockStationarity
public import SuperdiffusionCLT.Section2.Annealed.Envelope
public import Homogenization.Book.Ch04.Theorems.AnnealedSubadditivity.LawCarrierAnnealedMatrix
public import Homogenization.Book.Ch04.Theorems.AnnealedSubadditivity.LawCarrierFullBlock

/-!
# The infinite-volume running diffusivity of the infrared cutoff

The paper's display `e.homs.defs` introduces the infinite-volume annealed objects of the cutoff
field `a_m`. The sentence preceding the display reads

> By subadditivity, the matrices `bfAhom_m(cu_n)` are monotone nonincreasing in
> `n`. We also define the deterministic matrices bfAhom_m and shom_m as the
> infinite-volume limits of these:
> `bfAhom_m = [[shom_m, 0], [0, shom_m^{-1}]] = lim_{n → ∞} E[bfA_m(cu_n)]`.

The sentence after the display adds that the convergence of
`shom_{m,*}^{-1}(cu_n)` to `shom_m^{-1}` is a consequence of qualitative
homogenization for the field `nu Id + k_m` ([AK, Proposition D.2 and
Theorem 3.1]).

## The two normalizations

The display names one scalar shom_m and uses it in both diagonal slots. Two
different sequences are therefore being asserted to have reciprocal limits:

* the **upper-left** sequence `n ↦ shom_m(cu_n)`, whose limit the display calls
  shom_m; and
* the **lower-right** sequence `n ↦ shom_{m,*}^{-1}(cu_n)`, whose limit the
  display calls `shom_m^{-1}`.

Proposition `p.sstar.lower.bound` fixes the second reading:
there `shom_L = lim_{r → ∞} shom_{L,*}(cu_r)` and the displayed conclusion is
`shom_L ≥ shom_{L,*}(cu_m)`.

This module proves everything that the two displays *define*:

* both scalar sequences are nonincreasing and bounded, hence convergent;
* `sigmaBarStarInvLimit` is the limit of `shom_{m,*}^{-1}(cu_n)`, and its
  inverse `sigmaBarInfinite` is the limit of `shom_{m,*}(cu_n)`, the scalar of
  `p.sstar.lower.bound`, with `shom_{m,*}(cu_n) ≤ sigmaBarInfinite` for every
  `n`;
* `sigmaBarUpperLimit` is the limit of the upper-left sequence `shom_m(cu_n)`;
* `sigmaBarInfinite ≤ sigmaBarUpperLimit`.

The reverse inequality `sigmaBarUpperLimit ≤ sigmaBarInfinite`, which is what
makes the two slots of `e.homs.defs` reciprocal, is exactly the qualitative
homogenization input of [AK]; it is **not** proved in this module, and nothing below assumes
it.

## The proof of monotonicity

`CoarseGraining` proves the annealed subadditivity of the block matrix on
origin cubes for a law on its coefficient carrier
(`Book.Ch04.RestrictionLawCarrier.blockMatLoewnerLE_annealedBlockMatrixAtScale`,
the deterministic descendant comparison averaged against stationarity). Two
inputs are supplied here:

* stationarity of the cutoff law under integer translations, which comes from
  the per-shell stationarity of the prefix and the shell independence of
  J2 through `ShellField.map_translateSequence_eq`; and
* integrability of every entry of `bfA_m(cu)` on every triadic cube, which is
  the content of `SuperdiffusionCLT.Section2.Annealed.Integrability`,
  transported along the pushforward `cutoffLaw`.

The bounds are: the envelope of `e.Enaught.mixing` for the upper bound
`shom_{m,*}^{-1}(cu_n) ≤ 2 C nu⁻¹`, and the annealed contrast inequality
`1 ≤ shom_m(cu_n) shom_{m,*}^{-1}(cu_n)` of `CoarseGraining` together with the
monotonicity of the upper-left scalar for the uniform lower bound
`shom_m(cu_0)⁻¹ ≤ shom_{m,*}^{-1}(cu_n)`. The lower bound is what makes the
limit strictly positive and hence invertible.

## Main results

* `restrictionStationaryLaw_cutoffLaw`: the cutoff law is stationary.
* `integrable_blockMatEntry_cutoffLaw`,
  `integrable_coarseFullBlockMatrixAtCube_cutoffLaw`: the integrability inputs
  on the coefficient carrier.
* `annealedBlockMatrix_eq_ch04`: the annealed block matrix is
  `CoarseGraining`'s at the pushforward law.
* `blockMatLoewnerLE_annealedBlockMatrix_originCube`: **the monotonicity
  sentence of `e.homs.defs`**, `bfAhom_m(cu_k) ≤ bfAhom_m(cu_j)` for `j ≤ k`.
* `matLoewnerLE_sigmaBarStarInv_originCube`,
  `sigmaBarStarInvScalar_le_of_le`, `antitone_sigmaBarStarInvSeq`: the lower
  block and its scalar.
* `sigmaBarStarInvScalar_le_envelopeLowerScalar`,
  `one_le_sigmaBarScalar_mul_sigmaBarStarInvScalar`,
  `inv_sigmaBarScalar_zero_le_sigmaBarStarInvScalar`: the bounds.
* `sigmaBarStarInvLimit`, `tendsto_sigmaBarStarInvSeq`,
  `sigmaBarStarInvLimit_pos`: the limit of the lower block.
* `sigmaBarInfinite`, `sigmaBarStarScalar_originCube_le_sigmaBarInfinite`: the
  infinite-volume running diffusivity.
* `sigmaBarUpperLimit`, `antitone_sigmaBarSeq`,
  `sigmaBarInfinite_le_sigmaBarUpperLimit`: the upper-left limit and the one
  comparison between the two normalizations that is available here.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Annealed

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-! ## Stationarity of the cutoff law

Translating the coefficient field of a shell sequence is translating every
shell, so the stationarity of the joint shell law transports to the law of the
cutoff field on `CoarseGraining`'s coefficient carrier. -/

/-- Translating the cutoff coefficient field translates every shell of the
underlying sequence. The constant symmetric part `nu Id` is unaffected. -/
theorem translateReg_coefficientCutoff (nu : ℝ) (z : Vec d) (omega : ShellSeq d)
    (m : ℕ) :
    translateReg z (coefficientCutoff nu omega m) =
      coefficientCutoff nu (ShellField.translateSequence z omega) m := by
  refine RegCoeffField.ext fun x ↦ ?_
  rw [translateReg_apply, coefficientCutoff_apply, coefficientCutoff_apply,
    streamCutoff_apply, streamCutoff_apply]
  exact congrArg (fun M : Mat d ↦ nu • (1 : Mat d) + M)
    (Finset.sum_congr rfl fun k _ ↦ rfl)

variable {P : ProbabilityMeasure (ShellSeq d)}

/-- The law of the cutoff field is invariant under every real translation of
the coefficient carrier. -/
theorem map_translateReg_cutoffLaw (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (nu : ℝ) (m : ℕ) (z : Vec d) :
    Measure.map (translateReg z) (cutoffLaw (d := d) nu m P) =
      cutoffLaw (d := d) nu m P := by
  rw [cutoffLaw]
  calc
    Measure.map (translateReg z)
          (Measure.map (fun omega : ShellSeq d ↦ coefficientCutoff nu omega m)
            P.toMeasure) =
        Measure.map (fun omega : ShellSeq d ↦
          translateReg z (coefficientCutoff nu omega m)) P.toMeasure :=
      Measure.map_map (measurable_translateReg z)
        (measurable_coefficientCutoff nu m)
    _ = Measure.map ((fun omega : ShellSeq d ↦ coefficientCutoff nu omega m) ∘
          ShellField.translateSequence z) P.toMeasure := by
      refine congrArg
        (fun g : ShellSeq d → RegCoeffField d ↦ Measure.map g P.toMeasure) ?_
      funext omega
      exact translateReg_coefficientCutoff nu z omega m
    _ = Measure.map (fun omega : ShellSeq d ↦ coefficientCutoff nu omega m)
          (Measure.map (ShellField.translateSequence z) P.toMeasure) :=
      (Measure.map_map (measurable_coefficientCutoff nu m)
        (ShellField.measurable_translateSequence z)).symm
    _ = Measure.map (fun omega : ShellSeq d ↦ coefficientCutoff nu omega m)
          P.toMeasure := by
      rw [ShellField.map_translateSequence_eq hPrefix hJ2 z]

/-- **The cutoff law is a stationary law in `CoarseGraining`'s sense.** This is
the stationarity input of the annealed subadditivity of `e.homs.defs`. -/
theorem restrictionStationaryLaw_cutoffLaw (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (nu : ℝ) (m : ℕ) :
    Book.Ch04.RestrictionStationaryLaw (cutoffLaw (d := d) nu m P) :=
  fun z ↦ map_translateReg_cutoffLaw hPrefix hJ2 nu m (intVecToRealVec z)

/-! ## The block matrix of the cutoff on the coefficient carrier

`Blocks.lean` identifies each block of `bfAhom_m(U)` with `CoarseGraining`'s
Chapter 4 annealed block at the pushforward law. The four identifications
assemble into one equality of block matrices, which is the form the annealed
subadditivity of `CoarseGraining` is stated in. -/

variable {nu : ℝ}

/-- The remaining block bridge of `Blocks.lean`: the upper-right block. -/
theorem annealedBlockMatrix_upperRight_eq_ch04 (hnu : 0 < nu) (m : ℕ)
    (P : ProbabilityMeasure (ShellSeq d)) (Q : TriadicCube d) :
    (annealedBlockMatrix nu m P (cubeSet Q)).upperRight =
      (Book.Ch04.annealedBlockMatrix (cutoffLaw (d := d) nu m P)
        (cubeSet Q)).upperRight := by
  ext i j
  rw [annealedBlockMatrix_upperRight_apply,
    Book.Ch04.annealedBlockMatrix_upperRight_apply]
  exact (integral_cutoffLaw (nu := nu) m P
    (fun a ↦ (coarseBlockMatrix (cubeSet Q) a.toFun).upperRight i j)
    (((restrictionLawCarrier_cutoffLaw hnu m
        P).aemeasurable_coarseBlockMatrix_upperRight_apply_cubeSet Q i
        j).aestronglyMeasurable)).symm

/-- **`bfAhom_m(cu_Q)` is `CoarseGraining`'s annealed block matrix at the
pushforward law.** -/
theorem annealedBlockMatrix_eq_ch04 (hnu : 0 < nu) (m : ℕ)
    (P : ProbabilityMeasure (ShellSeq d)) (Q : TriadicCube d) :
    annealedBlockMatrix nu m P (cubeSet Q) =
      Book.Ch04.annealedBlockMatrix (cutoffLaw (d := d) nu m P) (cubeSet Q) := by
  have hUL : (annealedBlockMatrix nu m P (cubeSet Q)).upperLeft =
      (Book.Ch04.annealedBlockMatrix (cutoffLaw (d := d) nu m P)
        (cubeSet Q)).upperLeft := bBar_eq_ch04 hnu m P Q
  have hLR : (annealedBlockMatrix nu m P (cubeSet Q)).lowerRight =
      (Book.Ch04.annealedBlockMatrix (cutoffLaw (d := d) nu m P)
        (cubeSet Q)).lowerRight := sigmaBarStarInv_eq_ch04 hnu m P Q
  have hLL : (annealedBlockMatrix nu m P (cubeSet Q)).lowerLeft =
      (Book.Ch04.annealedBlockMatrix (cutoffLaw (d := d) nu m P)
        (cubeSet Q)).lowerLeft := by
    have h := sigmaBarStarInvKappaMean_eq_ch04 hnu m P Q
    rw [sigmaBarStarInvKappaMean, Book.Ch04.annealedSigmaStarInvKappaMean,
      neg_inj] at h
    exact h
  have hUR := annealedBlockMatrix_upperRight_eq_ch04 hnu m P Q
  cases hA : annealedBlockMatrix nu m P (cubeSet Q) with
  | mk a b c e =>
      cases hB : Book.Ch04.annealedBlockMatrix (cutoffLaw (d := d) nu m P)
          (cubeSet Q) with
      | mk a' b' c' e' =>
          rw [hA, hB] at hUL hUR hLL hLR
          simp_all

/-! ## Integrability on the coefficient carrier

The annealed subadditivity of `CoarseGraining` consumes the integrability of
the entries of `bfA_m(cu)` on the parent cube and on all of its descendants at
the child scale. `Integrability.lean` supplies these on the shell-sequence
carrier for an arbitrary triadic cube; the pushforward moves them to the
coefficient carrier. -/

/-- Every entry of `bfA(cu_Q)` is almost everywhere measurable for the cutoff
law. -/
theorem aemeasurable_blockMatEntry_cutoffLaw (hnu : 0 < nu) (m : ℕ)
    (P : ProbabilityMeasure (ShellSeq d)) (Q : TriadicCube d)
    (alpha beta : BlockCoord d) :
    AEMeasurable (fun a : RegCoeffField d ↦
      blockMatEntry (coarseBlockMatrix (cubeSet Q) a.toFun) alpha beta)
      (cutoffLaw (d := d) nu m P) := by
  have hP := restrictionLawCarrier_cutoffLaw hnu m P
  cases alpha with
  | inl i =>
      cases beta with
      | inl j => exact hP.aemeasurable_coarseBlockMatrix_upperLeft_apply_cubeSet Q i j
      | inr j => exact hP.aemeasurable_coarseBlockMatrix_upperRight_apply_cubeSet Q i j
  | inr i =>
      cases beta with
      | inl j => exact hP.aemeasurable_coarseBlockMatrix_lowerLeft_apply_cubeSet Q i j
      | inr j => exact hP.aemeasurable_coarseBlockMatrix_lowerRight_apply_cubeSet Q i j

section Carrier

variable [NeZero d] (hnu : 0 < nu) (m : ℕ) (Q : TriadicCube d)
  (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
  (hJ4 : ShellLawJ4 d P)

include hnu hPrefix hJ2 hJ3 hJ4

/-- **The entries of `bfA_m(cu_Q)` are integrable for the cutoff law.** -/
theorem integrable_blockMatEntry_cutoffLaw (alpha beta : BlockCoord d) :
    Integrable (fun a : RegCoeffField d ↦
      blockMatEntry (coarseBlockMatrix (cubeSet Q) a.toFun) alpha beta)
      (cutoffLaw (d := d) nu m P) := by
  rw [cutoffLaw]
  refine (integrable_map_measure
    ((aemeasurable_blockMatEntry_cutoffLaw hnu m P Q alpha
      beta).aestronglyMeasurable)
    (measurable_coefficientCutoff nu m).aemeasurable).2 ?_
  exact integrable_blockMatEntry_coarseBlockMatrix hnu m Q hPrefix hJ2 hJ3 hJ4
    alpha beta

/-- The unfolded doubled coarse block matrix is Bochner integrable for the
cutoff law. This is the form of integrability that `CoarseGraining`'s annealed
contrast inequality consumes. -/
theorem integrable_coarseFullBlockMatrixAtCube_cutoffLaw :
    Integrable (Book.Ch04.coarseFullBlockMatrixAtCube Q)
      (cutoffLaw (d := d) nu m P) := by
  refine MeasureTheory.Integrable.of_eval ?_
  intro alpha
  refine MeasureTheory.Integrable.of_eval ?_
  intro beta
  have h := integrable_blockMatEntry_cutoffLaw hnu m Q hPrefix hJ2 hJ3 hJ4
    alpha beta
  have hfun :
      (fun a : RegCoeffField d ↦
        Book.Ch04.coarseFullBlockMatrixAtCube Q a alpha beta) =
        fun a : RegCoeffField d ↦
          blockMatEntry (coarseBlockMatrix (cubeSet Q) a.toFun) alpha beta := by
    funext a
    cases alpha <;> cases beta <;> rfl
  rw [hfun]
  exact h

end Carrier

/-! ## Monotonicity in the cube scale

This is the manuscript's sentence "by subadditivity, the matrices
`bfAhom_m(cu_n)` are monotone nonincreasing in `n`". The deterministic
subadditivity, the descendant average and the stationarity step are
`CoarseGraining`'s; the two inputs supplied here are the stationarity of the
cutoff law and the entrywise integrability. -/

section Monotone

variable [NeZero d] (hnu : 0 < nu) (m : ℕ)
  (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
  (hJ4 : ShellLawJ4 d P) {j k : ℤ}

include hnu hPrefix hJ2 hJ3 hJ4

/-- **The monotonicity sentence of `e.homs.defs`**: the annealed block matrices
of the cutoff on origin cubes are nonincreasing in the scale, in the Loewner
order on doubled vectors. -/
theorem blockMatLoewnerLE_annealedBlockMatrix_originCube (hj : 0 ≤ j)
    (hjk : j ≤ k) :
    BlockMatLoewnerLE (annealedBlockMatrix nu m P (cubeSet (originCube d k)))
      (annealedBlockMatrix nu m P (cubeSet (originCube d j))) := by
  have hmono :=
    (restrictionLawCarrier_cutoffLaw hnu m
        P).blockMatLoewnerLE_annealedBlockMatrixAtScale
      (restrictionStationaryLaw_cutoffLaw hPrefix hJ2 nu m) hj hjk
      (fun alpha beta ↦ integrable_blockMatEntry_cutoffLaw hnu m
        (originCube d k) hPrefix hJ2 hJ3 hJ4 alpha beta)
      (fun R _ alpha beta ↦ integrable_blockMatEntry_cutoffLaw hnu m R hPrefix
        hJ2 hJ3 hJ4 alpha beta)
  rw [annealedBlockMatrix_eq_ch04 hnu m P (originCube d k),
    annealedBlockMatrix_eq_ch04 hnu m P (originCube d j)]
  simpa only [Book.Ch04.annealedBlockMatrixAtScale] using hmono

/-- **`shom_{m,*}^{-1}(cu_k) ≤ shom_{m,*}^{-1}(cu_j)` for `j ≤ k`**, the lower
block of the previous theorem. -/
theorem matLoewnerLE_sigmaBarStarInv_originCube (hj : 0 ≤ j) (hjk : j ≤ k) :
    MatLoewnerLE (sigmaBarStarInv nu m P (cubeSet (originCube d k)))
      (sigmaBarStarInv nu m P (cubeSet (originCube d j))) :=
  Book.Ch04.matLoewnerLE_lowerRight_of_blockMatLoewnerLE
    (blockMatLoewnerLE_annealedBlockMatrix_originCube hnu m hPrefix hJ2 hJ3 hJ4
      hj hjk)

/-- **`shom_m(cu_k) ≤ shom_m(cu_j)` for `j ≤ k`**, the upper-left block. The
annealed coupling matrix vanishes on origin cubes, so the upper-left block of
`bfAhom_m(cu_n)` is `shom_m(cu_n)`. -/
theorem matLoewnerLE_sigmaBar_originCube (hj : 0 ≤ j) (hjk : j ≤ k) :
    MatLoewnerLE (sigmaBar nu m P (cubeSet (originCube d k)))
      (sigmaBar nu m P (cubeSet (originCube d j))) := by
  have h := Book.Ch04.matLoewnerLE_upperLeft_of_blockMatLoewnerLE
    (blockMatLoewnerLE_annealedBlockMatrix_originCube hnu m hPrefix hJ2 hJ3 hJ4
      hj hjk)
  rwa [annealedBlockMatrix_originCube_upperLeft_eq_sigmaBar hnu m hJ4 k,
    annealedBlockMatrix_originCube_upperLeft_eq_sigmaBar hnu m hJ4 j] at h

/-- The scalar form of the lower-block monotonicity. -/
theorem sigmaBarStarInvScalar_le_of_le (hj : 0 ≤ j) (hjk : j ≤ k) :
    sigmaBarStarInvScalar nu m P (cubeSet (originCube d k)) ≤
      sigmaBarStarInvScalar nu m P (cubeSet (originCube d j)) :=
  diag_le_of_matLoewnerLE
    (matLoewnerLE_sigmaBarStarInv_originCube hnu m hPrefix hJ2 hJ3 hJ4 hj hjk) 0

/-- The scalar form of the upper-left monotonicity. -/
theorem sigmaBarScalar_le_of_le (hj : 0 ≤ j) (hjk : j ≤ k) :
    sigmaBarScalar nu m P (cubeSet (originCube d k)) ≤
      sigmaBarScalar nu m P (cubeSet (originCube d j)) :=
  diag_le_of_matLoewnerLE
    (matLoewnerLE_sigmaBar_originCube hnu m hPrefix hJ2 hJ3 hJ4 hj hjk) 0

end Monotone

/-! ## Bounds on the annealed lower scalar

The upper bound is the lower-right slot of the envelope `bfE_m` of
`e.Enaught.mixing`, tested on a coordinate vector. The lower bound is the
annealed contrast inequality `1 ≤ shom_m(cu_n) shom_{m,*}^{-1}(cu_n)` of
`CoarseGraining` combined with the monotonicity of the upper-left scalar; it is
uniform in the scale, which is what makes the limit invertible. -/

private theorem vecDotZeroLeft (y : Vec d) : vecDot (0 : Vec d) y = 0 := by
  simp only [vecDot, Pi.zero_apply, zero_mul, Finset.sum_const_zero]

private theorem vecDotZeroRight (x : Vec d) : vecDot x (0 : Vec d) = 0 := by
  simp only [vecDot, Pi.zero_apply, mul_zero, Finset.sum_const_zero]

private theorem matVecMulZero (M : Mat d) : matVecMul M (0 : Vec d) = 0 := by
  funext i
  simp only [matVecMul, Pi.zero_apply, mul_zero, Finset.sum_const_zero]

private theorem vecNormSqZero : vecNormSq (0 : Vec d) = 0 :=
  vecDotZeroLeft (0 : Vec d)

private theorem vecNormSqSingle (i : Fin d) :
    vecNormSq (Pi.single i (1 : ℝ)) = 1 := by
  rw [vecNormSq, vecDot_single_left]
  simp

section Bounds

variable [NeZero d] (hnu : 0 < nu) (m : ℕ)
  (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
  (hJ4 : ShellLawJ4 d P)

include hnu hPrefix hJ2 hJ3 hJ4

/-- **The uniform upper bound `shom_{m,*}^{-1}(cu_Q) ≤ 2 C nu⁻¹`**, the
lower-right scalar of the envelope `bfE_m` of `e.Enaught.mixing`. It does not
depend on the cube. -/
theorem sigmaBarStarInvScalar_le_envelopeLowerScalar (Q : TriadicCube d) :
    sigmaBarStarInvScalar nu m P (cubeSet Q) ≤ envelopeLowerScalar d nu := by
  have h := blockVecDot_annealedBlockMatrix_le hnu m Q hPrefix hJ2 hJ3 hJ4
    (0 : Vec d) (Pi.single (0 : Fin d) (1 : ℝ))
  rw [blockQuadratic_eq, matVecMulZero, matVecMulZero, vecDotZeroLeft,
    vecDotZeroLeft, vecDotZeroRight, vecDot_single_matVecMul_single,
    vecNormSqZero, vecNormSqSingle] at h
  have hEq : (annealedBlockMatrix nu m P (cubeSet Q)).lowerRight 0 0 =
      sigmaBarStarInvScalar nu m P (cubeSet Q) := rfl
  rw [hEq] at h
  linarith only [h]

omit hPrefix hJ2 hJ3 in
/-- The scalar of the annealed lower block on an origin cube is the internal
`CoarseGraining` scalar of the same block. -/
theorem barSigmaStarInv_primitiveScalarizationData (j : ℤ) :
    Book.Ch04.Internal.AnnealedPrimitiveScalarizationData.barSigmaStarInv
        (primitiveScalarizationData hnu m hJ4 j) =
      sigmaBarStarInvScalar nu m P (cubeSet (originCube d j)) := by
  refine Book.Ch04.scalar_eq_of_smul_one_eq_smul_one (d := d) ?_
  rw [← Book.Ch04.Internal.AnnealedPrimitiveScalarizationData.sigmaStarInv_eq
      (primitiveScalarizationData hnu m hJ4 j),
    ← sigmaBarStarInv_originCube_eq_smul_one hnu m hJ4 j,
    sigmaBarStarInv_eq_ch04 hnu m P (originCube d j)]
  rfl

omit hPrefix hJ2 hJ3 in
/-- The scalar of the annealed upper-left block on an origin cube is the
internal `CoarseGraining` scalar of the same block. On an origin cube the
annealed coupling matrix vanishes, so that block is `shom_m(cu_j)`. -/
theorem barB_primitiveScalarizationData (j : ℤ) :
    Book.Ch04.Internal.AnnealedPrimitiveScalarizationData.barB
        (primitiveScalarizationData hnu m hJ4 j) =
      sigmaBarScalar nu m P (cubeSet (originCube d j)) := by
  refine Book.Ch04.scalar_eq_of_smul_one_eq_smul_one (d := d) ?_
  rw [← Book.Ch04.Internal.AnnealedPrimitiveScalarizationData.b_eq
      (primitiveScalarizationData hnu m hJ4 j),
    ← sigmaBar_originCube_eq_smul_one hnu m hJ4 j,
    ← annealedBlockMatrix_originCube_upperLeft_eq_sigmaBar hnu m hJ4 j,
    show (annealedBlockMatrix nu m P (cubeSet (originCube d j))).upperLeft =
      bBar nu m P (cubeSet (originCube d j)) from rfl,
    bBar_eq_ch04 hnu m P (originCube d j)]
  rfl

/-- **The annealed contrast inequality**
`1 ≤ shom_m(cu_j) shom_{m,*}^{-1}(cu_j)`. It is the nonnegativity of the
annealed response functional at the pair `(shom_{m,*}^{-1} e, e)`. -/
theorem one_le_sigmaBarScalar_mul_sigmaBarStarInvScalar (j : ℤ) :
    1 ≤ sigmaBarScalar nu m P (cubeSet (originCube d j)) *
      sigmaBarStarInvScalar nu m P (cubeSet (originCube d j)) := by
  have hcontrast :=
    Book.Ch04.RestrictionLawCarrier.Internal.one_le_primitive_contrast_of_integrable_coarseFullBlockMatrixAtCube
      (restrictionLawCarrier_cutoffLaw hnu m P)
      (primitiveScalarizationData hnu m hJ4 j)
      (integrable_coarseFullBlockMatrixAtCube_cutoffLaw hnu m (originCube d j)
        hPrefix hJ2 hJ3 hJ4)
  rw [show Book.Ch04.Internal.AnnealedPrimitiveScalarizationData.contrast
        (primitiveScalarizationData hnu m hJ4 j) =
      Book.Ch04.Internal.AnnealedPrimitiveScalarizationData.barB
          (primitiveScalarizationData hnu m hJ4 j) *
        Book.Ch04.Internal.AnnealedPrimitiveScalarizationData.barSigmaStarInv
          (primitiveScalarizationData hnu m hJ4 j) from rfl,
    barB_primitiveScalarizationData hnu m hJ4 j,
    barSigmaStarInv_primitiveScalarizationData hnu m hJ4 j]
    at hcontrast
  exact hcontrast

/-- The annealed upper-left scalar on an origin cube is strictly positive. -/
theorem sigmaBarScalar_originCube_pos (j : ℤ) :
    0 < sigmaBarScalar nu m P (cubeSet (originCube d j)) := by
  have hstar := sigmaBarStarInvScalar_pos_cutoff hnu m hPrefix hJ2 hJ3 hJ4 j
  have hcontrast :=
    one_le_sigmaBarScalar_mul_sigmaBarStarInvScalar hnu m hPrefix hJ2 hJ3 hJ4 j
  by_contra hle
  push Not at hle
  have hmul := mul_le_mul_of_nonneg_right hle hstar.le
  rw [zero_mul] at hmul
  linarith only [hcontrast, hmul]

/-- **The uniform lower bound `shom_m(cu_0)⁻¹ ≤ shom_{m,*}^{-1}(cu_j)`**, valid
for every scale `j ≥ 0`. It is the contrast inequality at scale `j` together
with the monotonicity of the upper-left scalar. -/
theorem inv_sigmaBarScalar_zero_le_sigmaBarStarInvScalar {j : ℤ} (hj : 0 ≤ j) :
    (sigmaBarScalar nu m P (cubeSet (originCube d 0)))⁻¹ ≤
      sigmaBarStarInvScalar nu m P (cubeSet (originCube d j)) := by
  have hB0 := sigmaBarScalar_originCube_pos hnu m hPrefix hJ2 hJ3 hJ4 0
  have hstar := sigmaBarStarInvScalar_pos_cutoff hnu m hPrefix hJ2 hJ3 hJ4 j
  have hcontrast :=
    one_le_sigmaBarScalar_mul_sigmaBarStarInvScalar hnu m hPrefix hJ2 hJ3 hJ4 j
  have hBmono := sigmaBarScalar_le_of_le hnu m hPrefix hJ2 hJ3 hJ4 le_rfl hj
  have hstep := mul_le_mul_of_nonneg_right hBmono hstar.le
  have hkey : 1 ≤ sigmaBarScalar nu m P (cubeSet (originCube d 0)) *
      sigmaBarStarInvScalar nu m P (cubeSet (originCube d j)) := by
    linarith only [hcontrast, hstep]
  have hinvpos : 0 < (sigmaBarScalar nu m P (cubeSet (originCube d 0)))⁻¹ :=
    inv_pos.2 hB0
  have hmul := mul_le_mul_of_nonneg_left hkey hinvpos.le
  rwa [mul_one, ← mul_assoc, inv_mul_cancel₀ hB0.ne', one_mul] at hmul

end Bounds

/-! ## The two scalar sequences and their limits

`e.homs.defs` takes `n → ∞` along the origin cubes `cu_n`, so the objects of
the display are limits of sequences indexed by `n : ℕ`. -/

section Sequences

variable [NeZero d]

/-- The sequence `n ↦ shom_{m,*}^{-1}(cu_n)` of `e.homs.defs`. -/
def sigmaBarStarInvSeq (nu : ℝ) (m : ℕ) (P : ProbabilityMeasure (ShellSeq d))
    (n : ℕ) : ℝ :=
  sigmaBarStarInvScalar nu m P (cubeSet (originCube d (n : ℤ)))

/-- The sequence `n ↦ shom_m(cu_n)` of `e.homs.defs`, the upper-left block. -/
def sigmaBarSeq (nu : ℝ) (m : ℕ) (P : ProbabilityMeasure (ShellSeq d))
    (n : ℕ) : ℝ :=
  sigmaBarScalar nu m P (cubeSet (originCube d (n : ℤ)))

/-- **The limit of `shom_{m,*}^{-1}(cu_n)`**, defined as the infimum of a
sequence which the theorems below show is nonincreasing and bounded below by a
positive constant. -/
def sigmaBarStarInvLimit (nu : ℝ) (m : ℕ)
    (P : ProbabilityMeasure (ShellSeq d)) : ℝ :=
  ⨅ n : ℕ, sigmaBarStarInvSeq nu m P n

/-- **The infinite-volume running diffusivity shom_m** in the normalization
of Proposition `p.sstar.lower.bound`: the inverse of the limit of
the annealed lower blocks, equivalently the limit of `shom_{m,*}(cu_n)`. -/
def sigmaBarInfinite (nu : ℝ) (m : ℕ)
    (P : ProbabilityMeasure (ShellSeq d)) : ℝ :=
  (sigmaBarStarInvLimit nu m P)⁻¹

/-- **The limit of the upper-left blocks `shom_m(cu_n)`**, the other scalar
that the display `e.homs.defs` calls shom_m. -/
def sigmaBarUpperLimit (nu : ℝ) (m : ℕ)
    (P : ProbabilityMeasure (ShellSeq d)) : ℝ :=
  ⨅ n : ℕ, sigmaBarSeq nu m P n

end Sequences

section Limit

variable [NeZero d] (hnu : 0 < nu) (m : ℕ)
  (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
  (hJ4 : ShellLawJ4 d P)

include hnu hPrefix hJ2 hJ3 hJ4

/-- **The sequence of annealed lower blocks is nonincreasing.** -/
theorem antitone_sigmaBarStarInvSeq : Antitone (sigmaBarStarInvSeq nu m P) := by
  intro a b hab
  exact sigmaBarStarInvScalar_le_of_le hnu m hPrefix hJ2 hJ3 hJ4
    (Int.natCast_nonneg a) (Int.ofNat_le.2 hab)

/-- **The sequence of annealed upper-left blocks is nonincreasing.** -/
theorem antitone_sigmaBarSeq : Antitone (sigmaBarSeq nu m P) := by
  intro a b hab
  exact sigmaBarScalar_le_of_le hnu m hPrefix hJ2 hJ3 hJ4
    (Int.natCast_nonneg a) (Int.ofNat_le.2 hab)

/-- Positivity of the annealed lower scalar at every scale. -/
theorem sigmaBarStarInvSeq_pos (n : ℕ) : 0 < sigmaBarStarInvSeq nu m P n :=
  sigmaBarStarInvScalar_pos_cutoff hnu m hPrefix hJ2 hJ3 hJ4 (n : ℤ)

/-- Positivity of the annealed upper-left scalar at every scale. -/
theorem sigmaBarSeq_pos (n : ℕ) : 0 < sigmaBarSeq nu m P n :=
  sigmaBarScalar_originCube_pos hnu m hPrefix hJ2 hJ3 hJ4 (n : ℤ)

/-- The envelope upper bound along the sequence. -/
theorem sigmaBarStarInvSeq_le_envelopeLowerScalar (n : ℕ) :
    sigmaBarStarInvSeq nu m P n ≤ envelopeLowerScalar d nu :=
  sigmaBarStarInvScalar_le_envelopeLowerScalar hnu m hPrefix hJ2 hJ3 hJ4
    (originCube d (n : ℤ))

/-- **The uniform positive lower bound along the sequence.** -/
theorem inv_sigmaBarSeq_zero_le_sigmaBarStarInvSeq (n : ℕ) :
    (sigmaBarSeq nu m P 0)⁻¹ ≤ sigmaBarStarInvSeq nu m P n := by
  have h := inv_sigmaBarScalar_zero_le_sigmaBarStarInvScalar hnu m hPrefix hJ2
    hJ3 hJ4 (j := (n : ℤ)) (Int.natCast_nonneg n)
  simpa only [sigmaBarSeq, sigmaBarStarInvSeq, Nat.cast_zero] using h

/-- The uniform positive lower bound for the upper-left sequence, from the
contrast inequality and the envelope. -/
theorem inv_envelopeLowerScalar_le_sigmaBarSeq (n : ℕ) :
    (envelopeLowerScalar d nu)⁻¹ ≤ sigmaBarSeq nu m P n := by
  have hE := envelopeLowerScalar_pos hnu d
  have hB := sigmaBarSeq_pos hnu m hPrefix hJ2 hJ3 hJ4 n
  have hS := sigmaBarStarInvSeq_le_envelopeLowerScalar hnu m hPrefix hJ2 hJ3
    hJ4 n
  have hcontrast :=
    one_le_sigmaBarScalar_mul_sigmaBarStarInvScalar hnu m hPrefix hJ2 hJ3 hJ4
      (n : ℤ)
  have hstep : sigmaBarSeq nu m P n * sigmaBarStarInvSeq nu m P n ≤
      sigmaBarSeq nu m P n * envelopeLowerScalar d nu :=
    mul_le_mul_of_nonneg_left hS hB.le
  have hkey : 1 ≤ sigmaBarSeq nu m P n * envelopeLowerScalar d nu := by
    have hc : 1 ≤ sigmaBarSeq nu m P n * sigmaBarStarInvSeq nu m P n :=
      hcontrast
    linarith only [hc, hstep]
  have hmul := mul_le_mul_of_nonneg_right hkey (inv_pos.2 hE).le
  rwa [one_mul, mul_assoc, mul_inv_cancel₀ hE.ne', mul_one] at hmul

/-- The range of the sequence of annealed lower blocks is bounded below. -/
theorem bddBelow_range_sigmaBarStarInvSeq :
    BddBelow (Set.range (sigmaBarStarInvSeq nu m P)) := by
  refine ⟨(sigmaBarSeq nu m P 0)⁻¹, ?_⟩
  rintro x ⟨n, rfl⟩
  exact inv_sigmaBarSeq_zero_le_sigmaBarStarInvSeq hnu m hPrefix hJ2 hJ3 hJ4 n

/-- The range of the sequence of annealed upper-left blocks is bounded below.
-/
theorem bddBelow_range_sigmaBarSeq :
    BddBelow (Set.range (sigmaBarSeq nu m P)) := by
  refine ⟨(envelopeLowerScalar d nu)⁻¹, ?_⟩
  rintro x ⟨n, rfl⟩
  exact inv_envelopeLowerScalar_le_sigmaBarSeq hnu m hPrefix hJ2 hJ3 hJ4 n

/-- **The convergence asserted by `e.homs.defs` for the lower block**: the
nonincreasing bounded sequence `shom_{m,*}^{-1}(cu_n)` converges to its
infimum. -/
theorem tendsto_sigmaBarStarInvSeq :
    Filter.Tendsto (sigmaBarStarInvSeq nu m P) Filter.atTop
      (nhds (sigmaBarStarInvLimit nu m P)) :=
  tendsto_atTop_ciInf (antitone_sigmaBarStarInvSeq hnu m hPrefix hJ2 hJ3 hJ4)
    (bddBelow_range_sigmaBarStarInvSeq hnu m hPrefix hJ2 hJ3 hJ4)

/-- The limit is below every term. -/
theorem sigmaBarStarInvLimit_le (n : ℕ) :
    sigmaBarStarInvLimit nu m P ≤ sigmaBarStarInvSeq nu m P n :=
  ciInf_le (bddBelow_range_sigmaBarStarInvSeq hnu m hPrefix hJ2 hJ3 hJ4) n

/-- The upper-left limit is below every term. -/
theorem sigmaBarUpperLimit_le (n : ℕ) :
    sigmaBarUpperLimit nu m P ≤ sigmaBarSeq nu m P n :=
  ciInf_le (bddBelow_range_sigmaBarSeq hnu m hPrefix hJ2 hJ3 hJ4) n

/-- **The limit of the annealed lower blocks is strictly positive**, so it may
be inverted. -/
theorem sigmaBarStarInvLimit_pos : 0 < sigmaBarStarInvLimit nu m P := by
  have hpos : 0 < (sigmaBarSeq nu m P 0)⁻¹ :=
    inv_pos.2 (sigmaBarSeq_pos hnu m hPrefix hJ2 hJ3 hJ4 0)
  refine lt_of_lt_of_le hpos ?_
  exact le_ciInf fun n ↦
    inv_sigmaBarSeq_zero_le_sigmaBarStarInvSeq hnu m hPrefix hJ2 hJ3 hJ4 n

/-- **The infinite-volume running diffusivity is strictly positive.** -/
theorem sigmaBarInfinite_pos : 0 < sigmaBarInfinite nu m P :=
  inv_pos.2 (sigmaBarStarInvLimit_pos hnu m hPrefix hJ2 hJ3 hJ4)

/-- **`shom_{m,*}(cu_n) ≤ shom_m` for every `n`**, the first inequality of
`e.sstar.lower.bound`. -/
theorem sigmaBarStarScalar_originCube_le_sigmaBarInfinite (n : ℕ) :
    sigmaBarStarScalar nu m P (cubeSet (originCube d (n : ℤ))) ≤
      sigmaBarInfinite nu m P := by
  have hSn := sigmaBarStarInvSeq_pos hnu m hPrefix hJ2 hJ3 hJ4 n
  have hL := sigmaBarStarInvLimit_pos hnu m hPrefix hJ2 hJ3 hJ4
  have hle := sigmaBarStarInvLimit_le hnu m hPrefix hJ2 hJ3 hJ4 n
  rw [sigmaBarStarScalar_eq_inv hnu m hJ4 (n : ℤ) hSn, sigmaBarInfinite]
  exact (inv_le_inv₀ hSn hL).2 hle

/-- **The one comparison between the two normalizations of `e.homs.defs` that
is available without qualitative homogenization**: the limit of
`shom_{m,*}(cu_n)` is at most the limit of `shom_m(cu_n)`. The reverse
inequality, which is what makes the two diagonal slots of the display
reciprocal, is the qualitative homogenization input and is not used here. -/
theorem sigmaBarInfinite_le_sigmaBarUpperLimit :
    sigmaBarInfinite nu m P ≤ sigmaBarUpperLimit nu m P := by
  have hL := sigmaBarStarInvLimit_pos hnu m hPrefix hJ2 hJ3 hJ4
  refine le_ciInf fun k ↦ ?_
  have hlim : Filter.Tendsto
      (fun n : ℕ ↦ sigmaBarSeq nu m P k * sigmaBarStarInvSeq nu m P n)
      Filter.atTop
      (nhds (sigmaBarSeq nu m P k * sigmaBarStarInvLimit nu m P)) :=
    (tendsto_sigmaBarStarInvSeq hnu m hPrefix hJ2 hJ3 hJ4).const_mul _
  have hev : ∀ᶠ n : ℕ in Filter.atTop,
      1 ≤ sigmaBarSeq nu m P k * sigmaBarStarInvSeq nu m P n := by
    refine Filter.eventually_atTop.2 ⟨k, fun n hn ↦ ?_⟩
    have hc : 1 ≤ sigmaBarSeq nu m P n * sigmaBarStarInvSeq nu m P n :=
      one_le_sigmaBarScalar_mul_sigmaBarStarInvScalar hnu m hPrefix hJ2 hJ3 hJ4
        (n : ℤ)
    have hB := antitone_sigmaBarSeq hnu m hPrefix hJ2 hJ3 hJ4 hn
    have hS := (sigmaBarStarInvSeq_pos hnu m hPrefix hJ2 hJ3 hJ4 n).le
    have hstep := mul_le_mul_of_nonneg_right hB hS
    linarith only [hc, hstep]
  have hkey : 1 ≤ sigmaBarSeq nu m P k * sigmaBarStarInvLimit nu m P :=
    ge_of_tendsto hlim hev
  have hmul := mul_le_mul_of_nonneg_right hkey (inv_pos.2 hL).le
  rw [one_mul, mul_assoc, mul_inv_cancel₀ hL.ne', mul_one] at hmul
  exact hmul

end Limit

end

end SuperdiffusionCLT.Section2.Annealed
