/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Carriers.CenteredStreamField
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementMoreoverBlockB
public import SuperdiffusionCLT.Section2.Localization.BlockGauge
public import SuperdiffusionCLT.Section2.Localization.ShellWindowDomination
public import SuperdiffusionCLT.Section3.ResponseFields.RegboundsInputs
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1Localization
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3InputsE

/-!
# The pointwise quadratic bound of the centered finite shell increment

The printed proof of `l.localization` reads the pointwise relative bound `theta` of the coefficient
perturbation `a_L - a_m` off two facts: the perturbation's symmetric part is
zero and its centered operator norm is controlled by the window.  This module
lands the quadratic form behind that reading, in the exact shape the scalar
engine `coarseBlockMatrix_localization_scalar_two_sided` of
`BlockPerturbation.lean` consumes through
`relSkewBound_of_symmPart_eq_smul_one` (its `hnorm` hypothesis is a pointwise
quadratic form in `w`, not an essential-supremum statement).

* `vecNormSq_matVecMul_le_operatorNormSq_mul_vecNormSq`: the general matrix
  lemma.  It is a re-export of CoarseGraining's
  `vecNormSq_matVecMul_le_matrixOperatorNorm_sq_mul_vecNormSq`, stated in the
  `Mat d` / `matVecMul` vocabulary of this development, so that the
  specialization below and its consumers read off one file.
* `vecNormSq_centeredFiniteShellIncrement_le`: at every point of a Chapter 2
  domain inside the centred cube, the quadratic form of the volume-average
  centered finite shell increment is bounded by the square of the
  operator-norm bound
  `matrixOperatorNorm_finiteShellIncrement_sub_volumeAverage_le`
  (`ShellWindowDomination.lean`), i.e. by `C(d)^2 3^(2n)` times the squared
  upper-shell gauge.
* `ae_vecNormSq_centeredFiniteShellIncrement_le`: the same bound almost
  everywhere on `U`, in the exact `hnorm` shape of
  `coarseBlockMatrix_localization_scalar_two_sided` with the single constant
  `M := matrixOperatorNorm_diamConst d * 3^n * upperShellDerivGauge n m L`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open Homogenization
open Homogenization.Book.Ch02
open MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Terms
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## The general quadratic form of the operator norm -/

/-- **The operator norm bounds the quadratic form it generates**: for every
matrix `A` and vector `w`, `|A w|^2 ≤ ‖A‖^2 |w|^2` in the exact Euclidean
vocabulary of this development.  CoarseGraining proves this verbatim as
`vecNormSq_matVecMul_le_matrixOperatorNorm_sq_mul_vecNormSq`; it is restated
here under the `Mat d` / `matVecMul` names so that the consumers of the
centered-increment bound below need no `Book.Ch02` qualification. -/
theorem vecNormSq_matVecMul_le_operatorNormSq_mul_vecNormSq (A : Mat d)
    (w : Vec d) :
    vecNormSq (matVecMul A w) ≤ matrixOperatorNorm A ^ 2 * vecNormSq w :=
  vecNormSq_matVecMul_le_matrixOperatorNorm_sq_mul_vecNormSq A w

/-! ## The centered finite shell increment -/

/-- **The pointwise quadratic bound of the centered finite shell increment**
(the printed proof of `l.localization`): at every point of a
Chapter 2 domain contained in the centred cube, the quadratic form of the
volume-average centered increment `h(x) = k_L(x) - k_m(x) - ((k_L - k_m)_U)(x)`
is at most the square of the operator-norm bound
`matrixOperatorNorm_finiteShellIncrement_sub_volumeAverage_le`, i.e.
`(matrixOperatorNorm_diamConst d * 3^n * gauge)^2`, times `|w|^2`.  This is
the exact pointwise shape that `relSkewBound_of_symmPart_eq_smul_one`
consumes. -/
theorem vecNormSq_centeredFiniteShellIncrement_le
    (omega : ShellSeq d) (m L n : ℕ)
    (U : Book.Ch02.Domain d)
    (hU : (U : Set (Vec d)) ⊆ openCubeSet (originCube d (n : ℤ)))
    (x : Vec d) (hx : x ∈ (U : Set (Vec d))) (w : Vec d) :
    vecNormSq (matVecMul (finiteShellIncrement omega m L x -
        volumeAverageMat (U : Set (Vec d))
          (fun y => finiteShellIncrement omega m L y)) w) ≤
      (matrixOperatorNorm_diamConst d * (3 : ℝ) ^ n *
        upperShellDerivGauge n m L omega) ^ 2 * vecNormSq w := by
  have hM : 0 ≤ matrixOperatorNorm_diamConst d * (3 : ℝ) ^ n *
      upperShellDerivGauge n m L omega :=
    mul_nonneg (mul_nonneg (matrixOperatorNorm_diamConst_nonneg d)
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) n))
      (upperShellDerivGauge_nonneg n m L omega)
  have hop :=
    matrixOperatorNorm_finiteShellIncrement_sub_volumeAverage_le omega m L n U
      hU x hx
  refine (vecNormSq_matVecMul_le_operatorNormSq_mul_vecNormSq
    (finiteShellIncrement omega m L x -
      volumeAverageMat (U : Set (Vec d))
        (fun y => finiteShellIncrement omega m L y)) w).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (vecNormSq_nonneg w)
  exact pow_le_pow_left₀ (matrixOperatorNorm_nonneg _) hop 2

/-- **The same bound almost everywhere on `U`**, in the exact `hnorm` shape of
the scalar engine `coarseBlockMatrix_localization_scalar_two_sided`: a single
constant `M := matrixOperatorNorm_diamConst d * 3^n * upperShellDerivGauge n m L`
works for the perturbation field `x ↦ finiteShellIncrement omega m L x -
(finiteShellIncrement omega m L)_U` almost everywhere on `U`. -/
theorem ae_vecNormSq_centeredFiniteShellIncrement_le
    (omega : ShellSeq d) (m L n : ℕ)
    (U : Book.Ch02.Domain d)
    (hU : (U : Set (Vec d)) ⊆ openCubeSet (originCube d (n : ℤ))) :
    ∀ᵐ x ∂(volumeMeasureOn (U : Set (Vec d))), ∀ w : Vec d,
      vecNormSq (matVecMul (finiteShellIncrement omega m L x -
          volumeAverageMat (U : Set (Vec d))
            (fun y => finiteShellIncrement omega m L y)) w) ≤
        (matrixOperatorNorm_diamConst d * (3 : ℝ) ^ n *
          upperShellDerivGauge n m L omega) ^ 2 * vecNormSq w := by
  filter_upwards [ae_restrict_mem U.measurableSet] with x hx
  exact vecNormSq_centeredFiniteShellIncrement_le omega m L n U hU x hx

/-! ## The pointwise relative skew bound at the volume-average-centered cutoff pair -/

/-- **The pointwise relative skew bound at the volume-average-centered cutoff
pair** (the printed proof of `l.localization`): the
perturbation between the volume-average centered field
`â_L(x) = a_L(x) - ((k_L - k_m)_U)(x)` and the level-`m` cutoff field `a_m`
(`coefficientCutoff_toCoeffField_sub` turns their difference into the finite
shell increment) has symmetric part `ν Id` (`symmPart_coefficientCutoff`) and
satisfies, with `θ = ν⁻¹ M` and `M` the operator-norm bound of the
centered increment, the bilinear estimate
`2 r · (h p) ≤ θ (p · s p + r · s r)`.  This is the per-point instance the
scalar engine `coarseBlockMatrix_localization_scalar_two_sided` builds its
`hbound` hypothesis from via `relSkewBound_of_symmPart_eq_smul_one`. -/
theorem relSkewBound_centeredCutoffPair
    (nu : ℝ) (omega : ShellSeq d) (m L n : ℕ) (hL : m ≤ L) (hnu : 0 < nu)
    (U : Book.Ch02.Domain d)
    (hU : (U : Set (Vec d)) ⊆ openCubeSet (originCube d (n : ℤ)))
    (x : Vec d) (hx : x ∈ (U : Set (Vec d))) (p r : Vec d) :
    2 * vecDot r (matVecMul
        (((coefficientCutoff nu omega L).toCoeffField x -
            volumeAverageMat (U : Set (Vec d))
              (fun y => finiteShellIncrement omega m L y)) -
          (coefficientCutoff nu omega m).toCoeffField x) p) ≤
      (nu⁻¹ * (matrixOperatorNorm_diamConst d * (3 : ℝ) ^ n *
          upperShellDerivGauge n m L omega)) *
        (vecDot p (matVecMul
            (symmPart ((coefficientCutoff nu omega m).toCoeffField x)) p) +
          vecDot r (matVecMul
            (symmPart ((coefficientCutoff nu omega m).toCoeffField x)) r)) := by
  have hM0 : 0 ≤ matrixOperatorNorm_diamConst d * (3 : ℝ) ^ n *
      upperShellDerivGauge n m L omega :=
    mul_nonneg (mul_nonneg (matrixOperatorNorm_diamConst_nonneg d)
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) n))
      (upperShellDerivGauge_nonneg n m L omega)
  have hsplit : (coefficientCutoff nu omega L).toCoeffField x -
      volumeAverageMat (U : Set (Vec d))
        (fun y => finiteShellIncrement omega m L y) -
      (coefficientCutoff nu omega m).toCoeffField x =
    finiteShellIncrement omega m L x -
      volumeAverageMat (U : Set (Vec d))
        (fun y => finiteShellIncrement omega m L y) := by
    rw [← coefficientCutoff_toCoeffField_sub nu omega hL x]
    abel
  rw [hsplit]
  have hnorm : ∀ w : Vec d,
      vecNormSq (matVecMul (finiteShellIncrement omega m L x -
        volumeAverageMat (U : Set (Vec d))
          (fun y => finiteShellIncrement omega m L y)) w) ≤
      (matrixOperatorNorm_diamConst d * (3 : ℝ) ^ n *
        upperShellDerivGauge n m L omega) ^ 2 * vecNormSq w :=
    vecNormSq_centeredFiniteShellIncrement_le omega m L n U hU x hx
  have hsymm : symmPart ((coefficientCutoff nu omega m).toCoeffField x) =
      nu • (1 : Mat d) :=
    symmPart_coefficientCutoff nu omega m x
  rw [hsymm]
  exact relSkewBound_of_symmPart_eq_smul_one hnu hM0 rfl hnorm p r

end

end SuperdiffusionCLT.Section2.Localization