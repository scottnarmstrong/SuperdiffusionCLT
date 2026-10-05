/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.Blocks

/-!
# Dihedral reduction of the annealed block matrices

The paper reduces the annealed matrices of the infrared cutoff by the symmetry assumption J4:

* negation symmetry (`a_m` has the same law as `a_m^t`, and
  `kcg(U; a^t) = -kcg(U; a)`) forces `khom_m(U) = 0`, which turns
  `e.homs.defs.U.0` into the block-diagonal `e.homs.defs.U`;
* the hyperoctahedral half of J4 forces each diagonal block of
  `bfAhom_m(cu_n)` to be a scalar matrix.

Both steps are transported here from `CoarseGraining`, which proves them for a
law on its coefficient carrier. The bridge is the law `cutoffLaw` of the cutoff
field, together with the two action identities

`a_m(R^t j(R .) R) = R^t a_m(R .) R` and `a_m(-j) = a_m^t`,

which turn J4 into `CoarseGraining`'s `IsIsotropicInLawR` and
`IsAdjointInvariantInLawR`.

The reduced matrices stay matrices: the conclusions are equations `M = c • (1 : Mat d)` with a
separately named real scalar, and the scalars are defined without choice as the `(0,0)`
entry of the matrix they scale.

## Main results

* `coefficientCutoff_rotateSequence`, `coefficientCutoff_negateSequence`: the
  action identities.
* `isIsotropicInLawR_cutoffLaw`, `isAdjointInvariantInLawR_cutoffLaw`: J4 in
  `CoarseGraining`'s vocabulary.
* `sigmaBarStarInvKappaMean_originCube_eq_zero`: the mean of the cross term vanishes.
* `annealedBlockMatrix_originCube_lowerLeft_eq_zero`,
  `..._upperRight_eq_zero`, `..._upperLeft_eq_sigmaBar`: `e.homs.defs.U`.
* `sigmaBarStarInv_originCube_eq_smul_one`,
  `sigmaBarStar_originCube_eq_inv_smul_one`,
  `sigmaBar_originCube_eq_smul_one`: each diagonal block of
  `bfAhom_m(cu_n)` is a scalar matrix.
* `sigmaBarStarInvScalar_pos`: positivity of the annealed scalar, from the
  a.s. positive definiteness of `s_{m,*}^{-1}(cu_n)`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Annealed

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.CoarseGraining
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-! ## The J4 actions on the cutoff field -/

/-- Conjugating every shell by a signed permutation conjugates the cutoff
field: `a_m(R^t j(R .) R) = R^t a_m(R .) R`. The constant symmetric part
`nu Id` is fixed because `R^t R = Id`. -/
theorem coefficientCutoff_rotateSequence (nu : ℝ) {R : Mat d}
    (hR : IsSignedPermutationMatrix R) (omega : ShellSeq d) (m : ℕ) :
    coefficientCutoff nu (ShellField.rotateSequence R hR omega) m =
      rotateReg R hR (coefficientCutoff nu omega m) := by
  refine RegCoeffField.ext ?_
  intro x
  have hstream : streamCutoff (ShellField.rotateSequence R hR omega) m x =
      matTranspose R * streamCutoff omega m (matVecMul R x) * R := by
    rw [streamCutoff_apply, streamCutoff_apply, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [ShellField.rotateSequence_apply, ShellField.rotate_apply]
  rw [rotateReg_apply, coefficientCutoff_apply, coefficientCutoff_apply, hstream,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    hR.transpose_mul_self]

/-- Negating every shell transposes the cutoff field: `a_m(-j) = a_m^t`. -/
theorem coefficientCutoff_negateSequence (nu : ℝ) (omega : ShellSeq d) (m : ℕ) :
    coefficientCutoff nu (ShellField.negateSequence omega) m =
      adjointReg (coefficientCutoff nu omega m) := by
  refine RegCoeffField.ext ?_
  intro x
  have hstream : streamCutoff (ShellField.negateSequence omega) m x =
      -streamCutoff omega m x := by
    rw [streamCutoff_apply, streamCutoff_apply, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [ShellField.negateSequence_apply, ShellField.negate_apply]
  rw [adjointReg_apply, coefficientCutoff_apply, coefficientCutoff_apply, hstream]
  ext i j
  have hskew : streamCutoff omega m x j i = -streamCutoff omega m x i j :=
    streamCutoff_skew_entry omega m x j i
  simp only [Matrix.transpose_apply, Matrix.add_apply, Matrix.neg_apply,
    Matrix.smul_apply, smul_eq_mul, hskew, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij; simp
  · have hji : j ≠ i := Ne.symm hij
    simp [hij, hji]

/-! ## J4 in `CoarseGraining`'s vocabulary -/

variable (nu : ℝ) (m : ℕ) {P : ProbabilityMeasure (ShellSeq d)}

/-- The hyperoctahedral half of J4 makes the cutoff law isotropic. -/
theorem isIsotropicInLawR_cutoffLaw (hJ4 : ShellLawJ4 d P) :
    IsIsotropicInLawR (cutoffLaw (d := d) nu m P) := by
  intro R hR
  have hlaw : Measure.map (ShellField.rotateSequence R hR) P.toMeasure = P.toMeasure := by
    have h := congrArg ProbabilityMeasure.toMeasure (hJ4.hyperoctahedral R hR)
    exact h
  have hcomp : (rotateReg R hR ∘ fun omega : ShellSeq d ↦ coefficientCutoff nu omega m) =
      (fun omega : ShellSeq d ↦ coefficientCutoff nu omega m) ∘
        ShellField.rotateSequence R hR := by
    funext omega
    exact (coefficientCutoff_rotateSequence nu hR omega m).symm
  rw [cutoffLaw, Measure.map_map (measurable_rotateReg R hR)
      (measurable_coefficientCutoff nu m), hcomp,
    ← Measure.map_map (measurable_coefficientCutoff nu m)
      (ShellField.measurable_rotateSequence R hR), hlaw]

/-- The negation half of J4 makes the cutoff law adjoint invariant: `a_m` has
the same law as `a_m^t`. -/
theorem isAdjointInvariantInLawR_cutoffLaw (hJ4 : ShellLawJ4 d P) :
    IsAdjointInvariantInLawR (cutoffLaw (d := d) nu m P) := by
  have hlaw : Measure.map (ShellField.negateSequence (d := d)) P.toMeasure = P.toMeasure := by
    have h := congrArg ProbabilityMeasure.toMeasure hJ4.negation
    exact h
  have hcomp : (adjointReg ∘ fun omega : ShellSeq d ↦ coefficientCutoff nu omega m) =
      (fun omega : ShellSeq d ↦ coefficientCutoff nu omega m) ∘
        ShellField.negateSequence := by
    funext omega
    exact (coefficientCutoff_negateSequence nu omega m).symm
  rw [IsAdjointInvariantInLawR, cutoffLaw, Measure.map_map measurable_adjointReg
      (measurable_coefficientCutoff nu m), hcomp,
    ← Measure.map_map (measurable_coefficientCutoff nu m)
      ShellField.measurable_negateSequence, hlaw]

/-! ## The scalar reduction on origin cubes

`CoarseGraining` proves the reduction for a law on its coefficient carrier; the
bridge of `Blocks.lean` transports the conclusions back to the marginal
annealed matrices. The scalars
are named separately and the conclusions stay matrix equations. -/

section Scalarization

variable [NeZero d]

/-- The scalar of `shom_{m,*}^{-1}(U)`. -/
def sigmaBarStarInvScalar (nu : ℝ) (m : ℕ) (P : ProbabilityMeasure (ShellSeq d))
    (U : Set (Vec d)) : ℝ :=
  sigmaBarStarInv nu m P U 0 0

/-- The scalar running diffusivity `shom_{m,*}(U)`. -/
def sigmaBarStarScalar (nu : ℝ) (m : ℕ) (P : ProbabilityMeasure (ShellSeq d))
    (U : Set (Vec d)) : ℝ :=
  sigmaBarStar nu m P U 0 0

/-- The scalar running diffusivity `shom_m(U)`. -/
def sigmaBarScalar (nu : ℝ) (m : ℕ) (P : ProbabilityMeasure (ShellSeq d))
    (U : Set (Vec d)) : ℝ :=
  sigmaBar nu m P U 0 0

private theorem eq_smul_one_of_isScalarMatrix {M : Mat d} (h : IsScalarMatrix M) :
    M = M 0 0 • (1 : Mat d) := by
  obtain ⟨c, rfl⟩ := h
  simp

variable {nu : ℝ} (hnu : 0 < nu) (m : ℕ) {P : ProbabilityMeasure (ShellSeq d)}
  (hJ4 : ShellLawJ4 d P) (n : ℤ)

include hnu hJ4

/-- The primitive scalarization data of `CoarseGraining` at the cutoff law:
the two diagonal annealed blocks are invariant under coordinate sign flips and
transpositions, and the annealed mixed block vanishes. -/
theorem primitiveScalarizationData :
    Book.Ch04.Internal.AnnealedScalarizationPrimitiveData
      (cutoffLaw (d := d) nu m P) n :=
  Book.Ch04.Internal.annealedPrimitiveScalarizationData_of_isotropic_adjoint
    (restrictionLawCarrier_cutoffLaw hnu m P)
    (isIsotropicInLawR_cutoffLaw nu m hJ4)
    (isAdjointInvariantInLawR_cutoffLaw nu m hJ4) n

/-- The annealed mixed block vanishes: `E[(s_{m,*}^{-1} kcg_m)(cu_n)] = 0`.
This is the negation half of J4. -/
theorem sigmaBarStarInvKappaMean_originCube_eq_zero :
    sigmaBarStarInvKappaMean nu m P (cubeSet (originCube d n)) = 0 := by
  rw [sigmaBarStarInvKappaMean_eq_ch04 hnu m P (originCube d n)]
  exact (primitiveScalarizationData hnu m hJ4 n).sigmaStarInvKappaMean_eq_zero

/-- The lower-left block of `bfAhom_m(cu_n)` vanishes, the first half of
`e.homs.defs.U`. -/
theorem annealedBlockMatrix_originCube_lowerLeft_eq_zero :
    (annealedBlockMatrix nu m P (cubeSet (originCube d n))).lowerLeft = 0 := by
  have h := sigmaBarStarInvKappaMean_originCube_eq_zero hnu m hJ4 n
  rw [sigmaBarStarInvKappaMean, neg_eq_zero] at h
  exact h

/-- The upper-right block of `bfAhom_m(cu_n)` vanishes, the second half of
`e.homs.defs.U`. -/
theorem annealedBlockMatrix_originCube_upperRight_eq_zero :
    (annealedBlockMatrix nu m P (cubeSet (originCube d n))).upperRight = 0 := by
  rw [annealedBlockMatrix_upperRight_eq_transpose_lowerLeft,
    annealedBlockMatrix_originCube_lowerLeft_eq_zero hnu m hJ4 n]
  simp [matTranspose]

/-- With `khom_m(cu_n) = 0` the upper-left block of `bfAhom_m(cu_n)` is
`shom_m(cu_n)`: this is the passage from `e.homs.defs.U.0` to
`e.homs.defs.U`. -/
theorem annealedBlockMatrix_originCube_upperLeft_eq_sigmaBar :
    (annealedBlockMatrix nu m P (cubeSet (originCube d n))).upperLeft =
      sigmaBar nu m P (cubeSet (originCube d n)) := by
  rw [show (annealedBlockMatrix nu m P (cubeSet (originCube d n))).upperLeft =
      bBar nu m P (cubeSet (originCube d n)) from rfl,
    bBar_eq_ch04 hnu m P (originCube d n), sigmaBar_eq_ch04 hnu m P (originCube d n)]
  exact (Book.Ch04.Internal.annealedSigmaAtScale_eq_annealedBAtScale_of_sigmaStarInvKappaMean_eq_zero
    (cutoffLaw (d := d) nu m P) n
    ((primitiveScalarizationData hnu m hJ4 n).sigmaStarInvKappaMean_eq_zero)).symm

/-- **The annealed lower block of `bfAhom_m(cu_n)` is a scalar matrix**: dihedral
symmetry forces `shom_{m,*}^{-1}(cu_n)` to commute with every coordinate sign flip and
transposition. -/
theorem sigmaBarStarInv_originCube_eq_smul_one :
    sigmaBarStarInv nu m P (cubeSet (originCube d n)) =
      sigmaBarStarInvScalar nu m P (cubeSet (originCube d n)) • (1 : Mat d) := by
  refine eq_smul_one_of_isScalarMatrix ?_
  rw [sigmaBarStarInv_eq_ch04 hnu m P (originCube d n)]
  exact Book.Ch04.Internal.annealedSigmaStarInvAtScale_isScalarMatrix_of_invariant
    (cutoffLaw (d := d) nu m P) n
    (primitiveScalarizationData hnu m hJ4 n).sigmaStarInvFlip
    (primitiveScalarizationData hnu m hJ4 n).sigmaStarInvSwap

/-- **The annealed upper block of `bfAhom_m(cu_n)` is a scalar matrix**. -/
theorem sigmaBar_originCube_eq_smul_one :
    sigmaBar nu m P (cubeSet (originCube d n)) =
      sigmaBarScalar nu m P (cubeSet (originCube d n)) • (1 : Mat d) := by
  refine eq_smul_one_of_isScalarMatrix ?_
  rw [sigmaBar_eq_ch04 hnu m P (originCube d n)]
  exact Book.Ch04.Internal.annealedSigmaAtScale_isScalarMatrix_of_bInvariant_of_sigmaStarInvKappaMean_eq_zero
    (cutoffLaw (d := d) nu m P) n
    (primitiveScalarizationData hnu m hJ4 n).bFlip
    (primitiveScalarizationData hnu m hJ4 n).bSwap
    (primitiveScalarizationData hnu m hJ4 n).sigmaStarInvKappaMean_eq_zero

/-! ## Positivity of the annealed scalar

The manuscript uses `shom_{m,*}^{-1}(cu_n) > 0` to invert it. Positivity of the
scalar follows from the a.s. positive definiteness of `s_{m,*}^{-1}(cu_n)`
together with integrability of that matrix observable. Integrability is the one
analytic input this module does not derive; it is the expectation half of
`l.bfAm.ellip` and is therefore carried as an explicit hypothesis, exactly as
`CoarseGraining`'s own Chapter 4 annealed statements do. -/

omit hJ4 in
/-- The a.s. positive definiteness of `s_{m,*}^{-1}(cu_n)`. -/
theorem posDef_coarseBlockMatrix_lowerRight_coefficientCutoff (omega : ShellSeq d) :
    ((coarseBlockMatrix (cubeSet (originCube d n))
      (coefficientCutoff nu omega m).toFun).lowerRight).PosDef := by
  have ha := aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega m
  rw [coarseBlockMatrix_cubeSet_lowerRight_eq ha (originCube d n)]
  have h := Book.Ch02.sigmaStarInvCoarse_posDef (Book.Ch02.cubeDomain (originCube d n))
    ((Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
      (coefficientCutoff nu omega m) ha).coeffOn (originCube d n))
  rwa [← sigmaStarInvCoarse_toCoeffField, Book.Ch02.cubeDomain_coe] at h

/-- **`shom_{m,*}^{-1}(cu_n) > 0`.** -/
theorem sigmaBarStarInvScalar_pos
    (hInt : Integrable (fun omega : ShellSeq d ↦
      (coarseBlockMatrix (cubeSet (originCube d n))
        (coefficientCutoff nu omega m).toFun).lowerRight) P.toMeasure) :
    0 < sigmaBarStarInvScalar nu m P (cubeSet (originCube d n)) := by
  refine Book.Ch04.scalar_coefficient_pos_of_smul_one_eq_integral_posDef hInt
    (Filter.Eventually.of_forall fun omega ↦
      posDef_coarseBlockMatrix_lowerRight_coefficientCutoff hnu m n omega) ?_
  rw [← sigmaBarStarInv_originCube_eq_smul_one hnu m hJ4 n]
  ext i j
  rw [Homogenization.integral_matrix_apply hInt i j, sigmaBarStarInv_apply]

/-- With `shom_{m,*}^{-1}(cu_n) = c Id` and `c > 0`, the annealed running
diffusivity `shom_{m,*}(cu_n)` is the scalar matrix `c^{-1} Id`. -/
theorem sigmaBarStar_originCube_eq_inv_smul_one
    (hpos : 0 < sigmaBarStarInvScalar nu m P (cubeSet (originCube d n))) :
    sigmaBarStar nu m P (cubeSet (originCube d n)) =
      (sigmaBarStarInvScalar nu m P (cubeSet (originCube d n)))⁻¹ • (1 : Mat d) := by
  have hone : ((1 : Mat d))⁻¹ = (1 : Mat d) := by simp
  rw [sigmaBarStar, sigmaBarStarInv_originCube_eq_smul_one hnu m hJ4 n,
    nonsing_inv_smul _ hpos.ne' (by simp), hone]

/-- The scalar of `shom_{m,*}(cu_n)` is the inverse of the scalar of
`shom_{m,*}^{-1}(cu_n)`. -/
theorem sigmaBarStarScalar_eq_inv
    (hpos : 0 < sigmaBarStarInvScalar nu m P (cubeSet (originCube d n))) :
    sigmaBarStarScalar nu m P (cubeSet (originCube d n)) =
      (sigmaBarStarInvScalar nu m P (cubeSet (originCube d n)))⁻¹ := by
  have h := sigmaBarStar_originCube_eq_inv_smul_one hnu m hJ4 n hpos
  have := congrFun (congrFun h 0) 0
  simpa only [sigmaBarStarScalar, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] using this

end Scalarization

end

end SuperdiffusionCLT.Section2.Annealed
