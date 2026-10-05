/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Probability.OrliczMoments
public import SuperdiffusionCLT.Section3.HighContrast.StructuralLaw

/-!
# The multiscale ellipticity moments of the rebased cutoff law

The proof of `l.b.ell.homogenization` records that the infrared
cutoff field `a_m = nu Id + k_m` "satisfies the high-contrast ellipticity
envelope required in [AK, Theorem 3.1] with contrast bounded by a dimensional
polynomial in `nu^{-1} k`". `CoarseGraining` asks for that envelope in the
quantitative form of `Book.Ch05.QuantitativeCoarseGrainedEllipticity`: two
moment conditions on the unit-cube multiscale ellipticity observables
`Lambda_{s_1,1}` and `lambda_{s_2,1}` of Subsection 2.3. Those
two conditions are the predicate `CutoffEllipticityMoments` of
`StructuralLaw`, and this module proves the lower one
and reduces the upper one to a single `L^infinity` size statement.

## The lower moment is deterministic

The symmetric part of `a_m` is the constant `nu Id` at every point and every
sample (`symmPart_coefficientCutoff`), so Young's inequality `e.how.to.upbound.A`
puts the pointwise block
field of `a_m` below the block-diagonal majorant with
lower-right block `2 nu^{-1} Id`, uniformly in the sample and in the cube
(`blockVecDot_coarseBlockMatrix_coefficientCutoff_le`). Hence the lower-right
coarse block `sigma_*^{-1}(R)` has operator norm at most `2 nu^{-1}` on **every**
triadic cube, and since the geometric weights of the `q = 1` multiscale
constants sum to one, `lambda_{s,1}(Q; a_m)^{-1} <= 2 nu^{-1}` for every triadic
cube `Q`. The observable of the rebased law at the unit cube is the observable
of the cutoff law at the cube `cu_{m + t_d}` (`CoarseGraining`'s
`lambdaSqCoeffField_originCube_rescaleCoeffField_of_aelocallyUniformlyElliptic`),
so the bound transports verbatim, and a bounded measurable observable is
integrable under a probability law.

## The upper moment needs one size estimate

The same block majorant bounds the upper-left coarse block on a cube `R` by
`nu + 2 nu^{-1} ||k_m||^2_{L^2(R)}`, hence by
`nu + 2 nu^{-1} ||k_m||^2_{L^infinity(cu_{m+t_d})}` for every descendant `R` of
the rebasing cube, and therefore
`Lambda_{s,1}(cu_{m+t_d}; a_m) <= nu + 2 nu^{-1} ||k_m||^2_{L^infinity(cu_{m+t_d})}`.
The remaining input is a `Gamma_2` tail for that `L^infinity` size, which is the
display `e.kmn.Linfty` of the paper read at `n = 0`. The
large-cube estimate of `IncrementLinftyLargeCube` covers the increment
`k_m - k_n` for `n < m`, that is the shells `j_1, ..., j_m`; the shell `j_0` is
not covered by it. The remaining statement is isolated here as the predicate
`CutoffLargeCubeLinfty` (established in `CutoffLinftyEnvelope`), and the upper
moment is proved from it.

## Main definitions

* `CutoffLargeCubeLinfty`: the `Gamma_2` envelope of `|k_m|` on the rebasing
  cube `cu_{m + t_d}`.

## Main results

* `matrixNorm_lowerRight_coarseBlockMatrix_coefficientCutoff_le`,
  `matrixNorm_upperLeft_coarseBlockMatrix_coefficientCutoff_le`: the per-cube
  operator-norm bounds on the two diagonal coarse blocks of `a_m`.
* `lambdaSqCoeffField_inv_le_of_forall_matrixNorm_lowerRight_le`,
  `LambdaSqCoeffField_le_of_forall_matrixNorm_upperLeft_le`: the passage from
  a cube-uniform block bound to the multiscale constants.
* `lambdaSqCoeffField_inv_coefficientCutoff_le`: `lambda_{s,1}(Q; a_m)^{-1} <= 2 nu^{-1}`.
* `lambdaSqCoeffField_inv_rebasedCutoff_le`: the same at the unit cube for the
  rebased field.
* `integrable_lambdaSqCoeffField_inv_pow_rebasedCutoffLaw`: the second conjunct
  of `CutoffEllipticityMoments`.
* `LambdaSqCoeffField_rebasedCutoff_le`: the deterministic upper bound of the
  upper multiscale observable by `nu + 2 nu^{-1} S^2`.
* `integrable_LambdaSqCoeffField_pow_rebasedCutoffLaw`: the first conjunct, from
  `CutoffLargeCubeLinfty`.
* `cutoffEllipticityMoments_of_largeCubeLinfty`: both conjuncts together.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.HighContrast

open Homogenization MeasureTheory ProbabilityTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## The block Loewner majorant of the cutoff on one cube

Young's inequality `e.how.to.upbound.A` is proved in
`Section2/Annealed/Integrability.lean` as the
scalar bound
`blockVecDot_coarseBlockMatrix_coefficientCutoff_le`. Here it is read back as a
comparison of block matrices, so that the two diagonal blocks can be extracted
separately. -/

/-- **The block Loewner form of `e.how.to.upbound.A` on a triadic cube.** The
coarse block matrix of `a_m` on a triadic cube is below the block-diagonal
matrix with scalar blocks `nu + 2 nu^{-1} ||k_m||^2_{L^2}` and `2 nu^{-1}`. -/
theorem blockMatLoewnerLE_blockDiag_coarseBlockMatrix_coefficientCutoff [NeZero d]
    {nu : ℝ} (hnu : 0 < nu) (omega : ShellSeq d) (m : ℕ) (Q : TriadicCube d) :
    BlockMatLoewnerLE
      (coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega m).toFun)
      (Book.Ch02.blockDiag
        ((nu + 2 * nu⁻¹ * volumeAverage (openCubeSet Q)
            (fun x ↦ Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ^ 2)) •
          (1 : Mat d))
        ((2 * nu⁻¹) • (1 : Mat d))) := by
  rintro ⟨p, q⟩
  rw [blockVecDot_blockDiag_smul_one]
  have h := blockVecDot_coarseBlockMatrix_coefficientCutoff_le hnu omega m Q p q
  linarith only [h]

/-- The lower-right coarse block of `a_m` is positive semidefinite: it is the
Chapter 2 matrix `sigma_*^{-1}(R)`, which is positive definite. -/
theorem posSemidef_lowerRight_coarseBlockMatrix_coefficientCutoff [NeZero d]
    {nu : ℝ} (hnu : 0 < nu) (omega : ShellSeq d) (m : ℕ) (Q : TriadicCube d) :
    ((coarseBlockMatrix (cubeSet Q)
      (coefficientCutoff nu omega m).toFun).lowerRight).PosSemidef := by
  rw [Book.Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
    (aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega m) Q]
  exact (Book.Ch02.sigmaStarInvCoarse_posDef (Book.Ch02.cubeDomain Q) _).posSemidef

/-- The upper-left coarse block of `a_m` is positive semidefinite: it is the
Chapter 2 matrix `b(R)`. -/
theorem posSemidef_upperLeft_coarseBlockMatrix_coefficientCutoff [NeZero d]
    {nu : ℝ} (hnu : 0 < nu) (omega : ShellSeq d) (m : ℕ) (Q : TriadicCube d) :
    ((coarseBlockMatrix (cubeSet Q)
      (coefficientCutoff nu omega m).toFun).upperLeft).PosSemidef := by
  rw [Book.Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
    (aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega m) Q]
  simpa using Book.Ch02.bCoarse_posSemidef (Book.Ch02.cubeDomain Q) _

/-- **The lower coarse-grained ellipticity constant of the cutoff on one cube.**
`|sigma_*^{-1}(R; a_m)| <= 2 nu^{-1}` on every triadic cube, with no size
estimate on `k_m`: the symmetric part of `a_m` is the constant `nu Id`. -/
theorem matrixNorm_lowerRight_coarseBlockMatrix_coefficientCutoff_le [NeZero d]
    {nu : ℝ} (hnu : 0 < nu) (omega : ShellSeq d) (m : ℕ) (Q : TriadicCube d) :
    Book.Ch02.matrixNorm
        (coarseBlockMatrix (cubeSet Q)
          (coefficientCutoff nu omega m).toFun).lowerRight ≤ 2 * nu⁻¹ := by
  have hnn : (0 : ℝ) ≤ 2 * nu⁻¹ := by positivity
  have hLR := Book.Ch04.matLoewnerLE_lowerRight_of_blockMatLoewnerLE
    (blockMatLoewnerLE_blockDiag_coarseBlockMatrix_coefficientCutoff hnu omega m Q)
  have hblk : (Book.Ch02.blockDiag
      ((nu + 2 * nu⁻¹ * volumeAverage (openCubeSet Q)
        (fun x ↦ Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ^ 2)) •
          (1 : Mat d))
      ((2 * nu⁻¹) • (1 : Mat d))).lowerRight = (2 * nu⁻¹) • (1 : Mat d) := rfl
  rw [hblk] at hLR
  have hscal : (((2 * nu⁻¹) : ℝ) • (1 : Mat d)).PosSemidef :=
    (Matrix.PosSemidef.one).smul hnn
  rw [Book.Ch02.matrixNorm_eq_matrixOperatorNorm]
  calc
    Book.Ch02.matrixOperatorNorm
        (coarseBlockMatrix (cubeSet Q)
          (coefficientCutoff nu omega m).toFun).lowerRight
        ≤ Book.Ch02.matrixOperatorNorm (((2 * nu⁻¹) : ℝ) • (1 : Mat d)) :=
          Book.Ch02.matrixOperatorNorm_le_of_matLoewnerLE_of_posSemidef
            (posSemidef_lowerRight_coarseBlockMatrix_coefficientCutoff hnu omega m Q)
            hscal hLR
    _ = 2 * nu⁻¹ := Book.Ch02.matrixOperatorNorm_smul_one_eq_of_nonneg hnn

/-- **The upper coarse-grained ellipticity constant of the cutoff on one cube.**
`|b(R; a_m)| <= nu + 2 nu^{-1} ||k_m||^2_{L^2(R)}`. -/
theorem matrixNorm_upperLeft_coarseBlockMatrix_coefficientCutoff_le [NeZero d]
    {nu : ℝ} (hnu : 0 < nu) (omega : ShellSeq d) (m : ℕ) (Q : TriadicCube d) :
    Book.Ch02.matrixNorm
        (coarseBlockMatrix (cubeSet Q)
          (coefficientCutoff nu omega m).toFun).upperLeft ≤
      nu + 2 * nu⁻¹ * volumeAverage (openCubeSet Q)
        (fun x ↦ Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ^ 2) := by
  have hZ : 0 ≤ volumeAverage (openCubeSet Q)
      (fun x ↦ Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ^ 2) := by
    unfold volumeAverage
    exact mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
      (integral_nonneg fun x ↦ by positivity)
  have hnn : (0 : ℝ) ≤ nu + 2 * nu⁻¹ * volumeAverage (openCubeSet Q)
      (fun x ↦ Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ^ 2) := by
    have hinv : (0 : ℝ) ≤ 2 * nu⁻¹ := by positivity
    have := mul_nonneg hinv hZ
    linarith only [hnu, this]
  have hUL := Book.Ch04.matLoewnerLE_upperLeft_of_blockMatLoewnerLE
    (blockMatLoewnerLE_blockDiag_coarseBlockMatrix_coefficientCutoff hnu omega m Q)
  have hblk : (Book.Ch02.blockDiag
      ((nu + 2 * nu⁻¹ * volumeAverage (openCubeSet Q)
        (fun x ↦ Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ^ 2)) •
          (1 : Mat d))
      ((2 * nu⁻¹) • (1 : Mat d))).upperLeft =
      (nu + 2 * nu⁻¹ * volumeAverage (openCubeSet Q)
        (fun x ↦ Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ^ 2)) •
          (1 : Mat d) := rfl
  rw [hblk] at hUL
  have hscal : ((nu + 2 * nu⁻¹ * volumeAverage (openCubeSet Q)
      (fun x ↦ Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ^ 2)) •
        (1 : Mat d)).PosSemidef :=
    (Matrix.PosSemidef.one).smul hnn
  rw [Book.Ch02.matrixNorm_eq_matrixOperatorNorm]
  calc
    Book.Ch02.matrixOperatorNorm
        (coarseBlockMatrix (cubeSet Q)
          (coefficientCutoff nu omega m).toFun).upperLeft
        ≤ Book.Ch02.matrixOperatorNorm
            ((nu + 2 * nu⁻¹ * volumeAverage (openCubeSet Q)
              (fun x ↦ Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ^ 2)) •
                (1 : Mat d)) :=
          Book.Ch02.matrixOperatorNorm_le_of_matLoewnerLE_of_posSemidef
            (posSemidef_upperLeft_coarseBlockMatrix_coefficientCutoff hnu omega m Q)
            hscal hUL
    _ = _ := Book.Ch02.matrixOperatorNorm_smul_one_eq_of_nonneg hnn

/-! ## From cube-uniform block bounds to the multiscale constants

The `q = 1` multiscale constants of Subsection 2.3 are geometric averages of
the descendant suprema of the two diagonal coarse blocks, and the geometric
weights `c_{s,1} 3^{-sn}` sum to one. A bound on every descendant therefore
passes to the constant with no loss. -/

private theorem geometricWeight_one_nonneg {s : ℝ} (hs : 0 < s) (n : ℕ) :
    0 ≤ Book.Ch02.geometricWeight s 1 n := by
  simpa [Book.Ch02.geometricWeight_eq_old] using
    geometricWeight_nonneg (s := s) (q := 1) n (by positivity)

private theorem tsum_geometricWeight_one {s : ℝ} (hs : 0 < s) :
    ∑' n : ℕ, Book.Ch02.geometricWeight s 1 n = 1 := by
  simpa [Book.Ch02.geometricWeight_eq_old] using
    tsum_geometricWeight_one_eq_one (s := s) hs

private theorem rpow_half_sq {c : ℝ} (hc : 0 ≤ c) :
    (Real.rpow c (1 / 2)) ^ 2 = c := by
  show (c ^ (1 / 2 : ℝ)) ^ 2 = c
  rw [pow_two, ← Real.rpow_add' hc (by norm_num : (1 / 2 + 1 / 2 : ℝ) ≠ 0),
    show (1 / 2 + 1 / 2 : ℝ) = 1 by norm_num, Real.rpow_one]

private theorem sub_natCast_le_scale (Q : TriadicCube d) (n : ℕ) :
    Q.scale - (n : ℤ) ≤ Q.scale := by
  have hn : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
  linarith only [hn]

/-- **The lower multiscale constant from a cube-uniform block bound.** If the
lower-right coarse block of `a` has operator norm at most `C` on every triadic
cube, then `lambda_{s,1}(Q; a)^{-1} <= C` for every triadic cube `Q`. -/
theorem lambdaSqCoeffField_inv_le_of_forall_matrixNorm_lowerRight_le [NeZero d]
    {a : RegCoeffField d} (ha : Book.Ch04.AELocallyUniformlyEllipticField a)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ R : TriadicCube d,
      Book.Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) a.toFun).lowerRight ≤ C)
    (Q : TriadicCube d) {s : ℝ} (hs : 0 < s) :
    (Book.Ch04.lambdaSqCoeffField Q s (.finite 1) a)⁻¹ ≤ C := by
  have hMax : ∀ n : ℕ,
      Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale Q
        (Q.scale - (n : ℤ)) a ≤ C := by
    intro n
    rw [Book.Ch04.RestrictionLawCarrier.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale_eq_finsetSupReal_ae
      ha Q (Q.scale - (n : ℤ))]
    exact Book.Ch02.finsetSupReal_le _
      (descendantsAtScale_nonempty Q (sub_natCast_le_scale Q n)) fun R _ ↦ hC R
  have hMaxNonneg : ∀ n : ℕ,
      0 ≤ Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale Q
        (Q.scale - (n : ℤ)) a := by
    intro n
    rw [Book.Ch04.RestrictionLawCarrier.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale_eq_finsetSupReal_ae
      ha Q (Q.scale - (n : ℤ))]
    exact Book.Ch02.finsetSupReal_nonneg _ _ fun R _ ↦ Book.Ch02.matrixNorm_nonneg _
  set K : ℝ := Real.rpow C (1 / 2) with hK
  have hterm : ∀ n : ℕ,
      Book.Ch02.geometricWeight s 1 n *
          Real.rpow (Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale Q
            (Q.scale - (n : ℤ)) a) (1 / 2) ≤
        Book.Ch02.geometricWeight s 1 n * K :=
    fun n ↦ mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (hMaxNonneg n) (hMax n) (by norm_num))
      (geometricWeight_one_nonneg hs n)
  have hsummL :
      Summable (fun n : ℕ ↦
        Book.Ch02.geometricWeight s 1 n *
          Real.rpow (Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale Q
            (Q.scale - (n : ℤ)) a) (1 / 2)) :=
    Book.Ch04.RestrictionLawCarrier.summable_weighted_maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
      Q a hs
  have hsummR : Summable (fun n : ℕ ↦ Book.Ch02.geometricWeight s 1 n * K) := by
    simpa [Book.Ch02.geometricWeight_eq_old] using
      (summable_geometricWeight_one (s := s) hs).mul_right K
  have hTle :
      (∑' n : ℕ, Book.Ch02.geometricWeight s 1 n *
        Real.rpow (Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale Q
          (Q.scale - (n : ℤ)) a) (1 / 2)) ≤ K := by
    calc
      _ ≤ ∑' n : ℕ, Book.Ch02.geometricWeight s 1 n * K :=
            Summable.tsum_le_tsum hterm hsummL hsummR
      _ = (∑' n : ℕ, Book.Ch02.geometricWeight s 1 n) * K := tsum_mul_right
      _ = K := by rw [tsum_geometricWeight_one hs, one_mul]
  have hTnn :
      0 ≤ ∑' n : ℕ, Book.Ch02.geometricWeight s 1 n *
        Real.rpow (Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale Q
          (Q.scale - (n : ℤ)) a) (1 / 2) :=
    tsum_nonneg fun n ↦ mul_nonneg (geometricWeight_one_nonneg hs n)
      (Real.rpow_nonneg (hMaxNonneg n) _)
  rw [Book.Ch04.RestrictionLawCarrier.lambdaSqCoeffField_finite_one_eq_tsum_sq_inv Q a hs,
    inv_inv]
  calc
    _ ≤ K ^ 2 := pow_le_pow_left₀ hTnn hTle 2
    _ = C := by rw [hK]; exact rpow_half_sq hC0

/-- **The upper multiscale constant from a cube-uniform block bound.** If the
upper-left coarse block of `a` has operator norm at most `C` on every descendant
of `Q`, then `Lambda_{s,1}(Q; a) <= C`. -/
theorem LambdaSqCoeffField_le_of_forall_matrixNorm_upperLeft_le [NeZero d]
    {a : RegCoeffField d} (ha : Book.Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ n : ℕ, ∀ R ∈ descendantsAtScale Q (Q.scale - (n : ℤ)),
      Book.Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) a.toFun).upperLeft ≤ C)
    {s : ℝ} (hs : 0 < s) :
    Book.Ch04.LambdaSqCoeffField Q s (.finite 1) a ≤ C := by
  have hMax : ∀ n : ℕ,
      Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale Q
        (Q.scale - (n : ℤ)) a ≤ C := by
    intro n
    rw [Book.Ch04.RestrictionLawCarrier.maxDescendantBMatrixNormCoeffFieldAtScale_eq_finsetSupReal_ae
      ha Q (Q.scale - (n : ℤ))]
    exact Book.Ch02.finsetSupReal_le _
      (descendantsAtScale_nonempty Q (sub_natCast_le_scale Q n)) fun R hR ↦ hC n R hR
  have hMaxNonneg : ∀ n : ℕ,
      0 ≤ Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale Q
        (Q.scale - (n : ℤ)) a := by
    intro n
    rw [Book.Ch04.RestrictionLawCarrier.maxDescendantBMatrixNormCoeffFieldAtScale_eq_finsetSupReal_ae
      ha Q (Q.scale - (n : ℤ))]
    exact Book.Ch02.finsetSupReal_nonneg _ _ fun R _ ↦ Book.Ch02.matrixNorm_nonneg _
  set K : ℝ := Real.rpow C (1 / 2) with hK
  have hterm : ∀ n : ℕ,
      Book.Ch02.geometricWeight s 1 n *
          Real.rpow (Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale Q
            (Q.scale - (n : ℤ)) a) (1 / 2) ≤
        Book.Ch02.geometricWeight s 1 n * K :=
    fun n ↦ mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (hMaxNonneg n) (hMax n) (by norm_num))
      (geometricWeight_one_nonneg hs n)
  have hsummL :
      Summable (fun n : ℕ ↦
        Book.Ch02.geometricWeight s 1 n *
          Real.rpow (Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale Q
            (Q.scale - (n : ℤ)) a) (1 / 2)) :=
    Book.Ch04.RestrictionLawCarrier.summable_weighted_maxDescendantBMatrixNormCoeffFieldAtScale
      Q a hs
  have hsummR : Summable (fun n : ℕ ↦ Book.Ch02.geometricWeight s 1 n * K) := by
    simpa [Book.Ch02.geometricWeight_eq_old] using
      (summable_geometricWeight_one (s := s) hs).mul_right K
  have hTle :
      (∑' n : ℕ, Book.Ch02.geometricWeight s 1 n *
        Real.rpow (Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale Q
          (Q.scale - (n : ℤ)) a) (1 / 2)) ≤ K := by
    calc
      _ ≤ ∑' n : ℕ, Book.Ch02.geometricWeight s 1 n * K :=
            Summable.tsum_le_tsum hterm hsummL hsummR
      _ = (∑' n : ℕ, Book.Ch02.geometricWeight s 1 n) * K := tsum_mul_right
      _ = K := by rw [tsum_geometricWeight_one hs, one_mul]
  have hTnn :
      0 ≤ ∑' n : ℕ, Book.Ch02.geometricWeight s 1 n *
        Real.rpow (Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale Q
          (Q.scale - (n : ℤ)) a) (1 / 2) :=
    tsum_nonneg fun n ↦ mul_nonneg (geometricWeight_one_nonneg hs n)
      (Real.rpow_nonneg (hMaxNonneg n) _)
  rw [Book.Ch04.RestrictionLawCarrier.LambdaSqCoeffField_finite_one_eq_tsum_sq Q a s]
  calc
    _ ≤ K ^ 2 := pow_le_pow_left₀ hTnn hTle 2
    _ = C := by rw [hK]; exact rpow_half_sq hC0

/-! ## The lower moment -/

/-- **The lower multiscale ellipticity constant of the cutoff.** On every
triadic cube, `lambda_{s,1}(Q; a_m)^{-1} <= 2 nu^{-1}`, uniformly in the sample:
the symmetric part of `a_m` is the constant `nu Id`, so no size estimate on
`k_m` enters. -/
theorem lambdaSqCoeffField_inv_coefficientCutoff_le [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (omega : ShellSeq d) (m : ℕ) (Q : TriadicCube d) {s : ℝ} (hs : 0 < s) :
    (Book.Ch04.lambdaSqCoeffField Q s (.finite 1) (coefficientCutoff nu omega m))⁻¹ ≤
      2 * nu⁻¹ :=
  lambdaSqCoeffField_inv_le_of_forall_matrixNorm_lowerRight_le
    (aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega m)
    (by positivity)
    (fun R ↦ matrixNorm_lowerRight_coarseBlockMatrix_coefficientCutoff_le hnu omega m R)
    Q hs

/-- The unit-cube multiscale observables of the rebased cutoff field are the
observables of the cutoff field at the rebasing cube `cu_{m + t_d}`. -/
theorem lambdaSqCoeffField_originCube_zero_rescaleReg_coefficientCutoff [NeZero d]
    {nu : ℝ} (hnu : 0 < nu) (omega : ShellSeq d) (m K : ℕ) (s : ℝ)
    (q : Book.Ch02.MultiscaleExponent) :
    Book.Ch04.lambdaSqCoeffField (originCube d (0 : ℤ)) s q
        (rescaleReg (d := d) K (coefficientCutoff nu omega m)) =
      Book.Ch04.lambdaSqCoeffField (originCube d (K : ℤ)) s q
        (coefficientCutoff nu omega m) := by
  simpa using
    Book.Ch04.lambdaSqCoeffField_originCube_rescaleCoeffField_of_aelocallyUniformlyElliptic
      (aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega m) K 0 s q

/-- The same identification for the upper observable. -/
theorem LambdaSqCoeffField_originCube_zero_rescaleReg_coefficientCutoff [NeZero d]
    {nu : ℝ} (hnu : 0 < nu) (omega : ShellSeq d) (m K : ℕ) (s : ℝ)
    (q : Book.Ch02.MultiscaleExponent) :
    Book.Ch04.LambdaSqCoeffField (originCube d (0 : ℤ)) s q
        (rescaleReg (d := d) K (coefficientCutoff nu omega m)) =
      Book.Ch04.LambdaSqCoeffField (originCube d (K : ℤ)) s q
        (coefficientCutoff nu omega m) := by
  simpa using
    Book.Ch04.LambdaSqCoeffField_originCube_rescaleCoeffField_of_aelocallyUniformlyElliptic
      (aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega m) K 0 s q

/-- **The unit-cube lower ellipticity constant of the rebased cutoff field.** -/
theorem lambdaSqCoeffField_inv_rebasedCutoff_le [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (omega : ShellSeq d) (m : ℕ) {s : ℝ} (hs : 0 < s) :
    (Book.Ch04.lambdaSqCoeffField (originCube d (0 : ℤ)) s (.finite 1)
        (rescaleReg (d := d) (m + triadicOffset d) (coefficientCutoff nu omega m)))⁻¹ ≤
      2 * nu⁻¹ := by
  rw [lambdaSqCoeffField_originCube_zero_rescaleReg_coefficientCutoff hnu omega m
    (m + triadicOffset d) s (.finite 1)]
  exact lambdaSqCoeffField_inv_coefficientCutoff_le hnu omega m _ hs

/-! ## Integrability under the rebased law

The rebased cutoff law is the law of the rescaled cutoff field on the shell
sequence, so an observable that is bounded on the range of that field is
integrable. -/

/-- The rebased cutoff law is the pushforward of the shell law along the
rescaled cutoff field. -/
theorem rebasedCutoffLaw_eq_map_shellSeq (nu : ℝ) (m : ℕ)
    (P : ProbabilityMeasure (ShellSeq d)) :
    rebasedCutoffLaw nu m P =
      Measure.map (fun omega : ShellSeq d ↦
          rescaleReg (d := d) (m + triadicOffset d) (coefficientCutoff nu omega m))
        P.toMeasure := by
  rw [rebasedCutoffLaw_eq_map, cutoffLaw,
    Measure.map_map (measurable_rescaleReg (d := d) (m + triadicOffset d))
      (measurable_coefficientCutoff nu m)]
  rfl

/-- An observable dominated on the range of the rescaled cutoff field by an
integrable observable of the sample is integrable under the rebased law. -/
theorem integrable_rebasedCutoffLaw_of_le {nu : ℝ} {m : ℕ}
    {P : ProbabilityMeasure (ShellSeq d)} {X : RegCoeffField d → ℝ}
    {g : ShellSeq d → ℝ}
    (hX : AEStronglyMeasurable X (rebasedCutoffLaw nu m P))
    (hg : Integrable g P.toMeasure)
    (hbound : ∀ omega : ShellSeq d,
      ‖X (rescaleReg (d := d) (m + triadicOffset d)
        (coefficientCutoff nu omega m))‖ ≤ g omega) :
    Integrable X (rebasedCutoffLaw nu m P) := by
  have hmeas : Measurable (fun omega : ShellSeq d ↦
      rescaleReg (d := d) (m + triadicOffset d) (coefficientCutoff nu omega m)) :=
    (measurable_rescaleReg (d := d) (m + triadicOffset d)).comp
      (measurable_coefficientCutoff nu m)
  rw [rebasedCutoffLaw_eq_map_shellSeq] at hX ⊢
  rw [integrable_map_measure hX hmeas.aemeasurable]
  exact Integrable.mono' hg (hX.comp_aemeasurable hmeas.aemeasurable)
    (Filter.Eventually.of_forall hbound)

/-- **The lower moment condition of the quantitative coarse-grained ellipticity
input.** The unit-cube reciprocal lower multiscale ellipticity observable of the
rebased cutoff law is bounded by `2 nu^{-1}`, hence has every moment. This is the
second conjunct of `CutoffEllipticityMoments`. -/
theorem integrable_lambdaSqCoeffField_inv_pow_rebasedCutoffLaw [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (m : ℕ) (P : ProbabilityMeasure (ShellSeq d)) {sLower : ℝ}
    (hsLower : 0 < sLower) (xi : ℕ) :
    Integrable (fun a : RegCoeffField d ↦
        (Book.Ch04.lambdaSqCoeffField (originCube d (0 : ℤ)) sLower (.finite 1) a)⁻¹ ^ xi)
      (rebasedCutoffLaw nu m P) := by
  have hcarrier := restrictionLawCarrier_rebasedCutoffLaw hnu m P
  have hmeas : AEStronglyMeasurable (fun a : RegCoeffField d ↦
      (Book.Ch04.lambdaSqCoeffField (originCube d (0 : ℤ)) sLower (.finite 1) a)⁻¹ ^ xi)
      (rebasedCutoffLaw nu m P) :=
    ((hcarrier.aemeasurable_lambdaSqCoeffField_finite_one_inv
      (originCube d (0 : ℤ)) hsLower).pow_const xi).aestronglyMeasurable
  refine integrable_rebasedCutoffLaw_of_le (g := fun _ ↦ (2 * nu⁻¹) ^ xi) hmeas
    (integrable_const _) fun omega ↦ ?_
  have hnn : (0 : ℝ) ≤ (Book.Ch04.lambdaSqCoeffField (originCube d (0 : ℤ)) sLower
      (.finite 1) (rescaleReg (d := d) (m + triadicOffset d)
        (coefficientCutoff nu omega m)))⁻¹ :=
    inv_nonneg.2 (Book.Ch04.lambdaSqCoeffField_finite_nonneg _ _ hsLower le_rfl)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hnn xi)]
  exact pow_le_pow_left₀ hnn
    (lambdaSqCoeffField_inv_rebasedCutoff_le hnu omega m hsLower) xi

/-! ## The upper moment

The upper-left block bound carries the normalized `L^2(R)` size of `k_m` on the
descendant cube `R`. Every descendant of the rebasing cube sits inside it, so a
single `L^infinity` bound on the rebasing cube controls all of them at once. -/

private theorem volumeAverage_le_of_forall_le {U : Set (Vec d)} (hU : MeasurableSet U)
    (hne : volume U ≠ 0) (hlt : volume U ≠ ⊤) {f : Vec d → ℝ}
    (hf : IntegrableOn f U) {M : ℝ} (hbound : ∀ x ∈ U, f x ≤ M) :
    volumeAverage U f ≤ M := by
  have : IsFiniteMeasure (volume.restrict U) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hlt⟩
  have hpos : 0 < (volume U).toReal := ENNReal.toReal_pos hne hlt
  have hle : ∫ x in U, f x ≤ (volume U).toReal * M := by
    have h1 : ∫ x in U, f x ≤ ∫ _x in U, M :=
      integral_mono_ae hf (integrable_const M)
        ((ae_restrict_iff' hU).2 (Filter.Eventually.of_forall hbound))
    simpa [setIntegral_const, smul_eq_mul, Measure.real] using h1
  calc volumeAverage U f
      ≤ (volume U).toReal⁻¹ * ((volume U).toReal * M) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = M := by field_simp

/-- **The upper multiscale ellipticity constant of the cutoff on a large cube.**
A uniform bound `S` on `|k_m|` over the open cube `cu_K` bounds
`Lambda_{s,1}(cu_K; a_m)` by `nu + 2 nu^{-1} S^2`: this is the dimensional
polynomial in `nu^{-1} k` of the printed proof. -/
theorem LambdaSqCoeffField_coefficientCutoff_le [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (omega : ShellSeq d) (m K : ℕ) {S : ℝ}
    (hbound : ∀ x ∈ openCubeSet (originCube d (K : ℤ)),
      Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ≤ S)
    {s : ℝ} (hs : 0 < s) :
    Book.Ch04.LambdaSqCoeffField (originCube d (K : ℤ)) s (.finite 1)
        (coefficientCutoff nu omega m) ≤ nu + 2 * nu⁻¹ * S ^ 2 := by
  obtain ⟨x₀, hx₀⟩ := Book.Ch02.openCubeSet_nonempty (originCube d (K : ℤ))
  have hS0 : 0 ≤ S :=
    le_trans (Book.Ch02.matrixOperatorNorm_nonneg _) (hbound x₀ hx₀)
  have hC0 : (0 : ℝ) ≤ nu + 2 * nu⁻¹ * S ^ 2 := by positivity
  refine LambdaSqCoeffField_le_of_forall_matrixNorm_upperLeft_le
    (aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega m) _ hC0
    (fun n R hR ↦ ?_) hs
  have hsub : openCubeSet R ⊆ openCubeSet (originCube d (K : ℤ)) := by
    rw [descendantsAtScale_eq_descendantsAtDepth _
      (sub_natCast_le_scale (originCube d (K : ℤ)) n)] at hR
    exact openCubeSet_subset_of_mem_descendantsAtDepth hR
  have havg : volumeAverage (openCubeSet R)
      (fun x ↦ Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ^ 2) ≤ S ^ 2 := by
    refine volumeAverage_le_of_forall_le (isOpen_openCubeSet R).measurableSet
      (volume_openCubeSet_ne_zero R) (volume_openCubeSet_lt_top R).ne
      (integrableOn_matrixOperatorNorm_sq_streamCutoff omega m R) fun x hx ↦ ?_
    exact pow_le_pow_left₀ (Book.Ch02.matrixOperatorNorm_nonneg _)
      (hbound x (hsub hx)) 2
  have hstep := matrixNorm_upperLeft_coarseBlockMatrix_coefficientCutoff_le hnu omega m R
  have hmul : 2 * nu⁻¹ * volumeAverage (openCubeSet R)
      (fun x ↦ Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ^ 2) ≤
      2 * nu⁻¹ * S ^ 2 :=
    mul_le_mul_of_nonneg_left havg (by positivity)
  linarith only [hstep, hmul]

/-- **The `L^infinity` size of the cutoff on the rebasing cube.** The manuscript's
display `e.kmn.Linfty`, read for the full cutoff `k_m` rather
than for an increment `k_m - k_n`, on the cube `cu_{m + t_d}` that the rebasing
of `Section3/HighContrast/StructuralLaw.lean` normalizes to the unit cube: there
is a random amplitude with a `Gamma_2` tail dominating `|k_m|` everywhere on that
cube.

`IncrementLinftyLargeCube` proves exactly this for
the increment `k_m - k_n` with `n < m`, that is for the shells
`j_{n+1}, ..., j_m`; the envelope is
`largeCubeIncrementSupBound n m l` and its tail is
`isBigOWith_gammaSigma_largeCubeIncrementSupBound`. What is missing is the shell
`j_0`: since `k_m = j_0 + (k_m - k_0)` and `k_0 = j_0`, this predicate follows
from the large-cube estimate at `n = 0`, `l = m + t_d` together with any
`Gamma_2` large-cube bound for the single shell `j_0`. -/
def CutoffLargeCubeLinfty (m : ℕ) (P : ProbabilityMeasure (ShellSeq d)) : Prop :=
  ∃ (S : ShellSeq d → ℝ) (A : ℝ), 0 < A ∧ AEMeasurable S P.toMeasure ∧
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2) S A ∧
    ∀ (omega : ShellSeq d) (x : Vec d),
      x ∈ openCubeSet (originCube d ((m + triadicOffset d : ℕ) : ℤ)) →
        Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ≤ S omega

/-- **The unit-cube upper ellipticity constant of the rebased cutoff field.** -/
theorem LambdaSqCoeffField_rebasedCutoff_le [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (omega : ShellSeq d) (m : ℕ) {S : ℝ}
    (hbound : ∀ x ∈ openCubeSet (originCube d ((m + triadicOffset d : ℕ) : ℤ)),
      Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ≤ S)
    {s : ℝ} (hs : 0 < s) :
    Book.Ch04.LambdaSqCoeffField (originCube d (0 : ℤ)) s (.finite 1)
        (rescaleReg (d := d) (m + triadicOffset d) (coefficientCutoff nu omega m)) ≤
      nu + 2 * nu⁻¹ * S ^ 2 := by
  rw [LambdaSqCoeffField_originCube_zero_rescaleReg_coefficientCutoff hnu omega m
    (m + triadicOffset d) s (.finite 1)]
  exact LambdaSqCoeffField_coefficientCutoff_le hnu omega m (m + triadicOffset d)
    hbound hs

/-- A polynomial in the envelope is dominated by a multiple of `1 + S^{2 xi}`. -/
private theorem pow_add_mul_sq_le {nu : ℝ} (hnu : 0 < nu) (S : ℝ) (xi : ℕ) :
    (nu + 2 * nu⁻¹ * S ^ 2) ^ xi ≤
      (nu + 2 * nu⁻¹) ^ xi * (1 + |S| ^ (2 * xi)) := by
  have hmax : (1 : ℝ) ≤ max 1 (|S| ^ 2) := le_max_left _ _
  have hsq : S ^ 2 ≤ max 1 (|S| ^ 2) := by
    have : S ^ 2 = |S| ^ 2 := (sq_abs S).symm
    rw [this]
    exact le_max_right _ _
  have hnuinv : (0 : ℝ) ≤ 2 * nu⁻¹ := by positivity
  have hbase : nu + 2 * nu⁻¹ * S ^ 2 ≤ (nu + 2 * nu⁻¹) * max 1 (|S| ^ 2) := by
    have h1 : nu ≤ nu * max 1 (|S| ^ 2) := le_mul_of_one_le_right hnu.le hmax
    have h2 : 2 * nu⁻¹ * S ^ 2 ≤ 2 * nu⁻¹ * max 1 (|S| ^ 2) :=
      mul_le_mul_of_nonneg_left hsq hnuinv
    linarith only [h1, h2]
  have hb0 : (0 : ℝ) ≤ nu + 2 * nu⁻¹ * S ^ 2 := by positivity
  have hpow : (nu + 2 * nu⁻¹ * S ^ 2) ^ xi ≤
      ((nu + 2 * nu⁻¹) * max 1 (|S| ^ 2)) ^ xi := pow_le_pow_left₀ hb0 hbase xi
  have hmaxpow : (max 1 (|S| ^ 2)) ^ xi ≤ 1 + |S| ^ (2 * xi) := by
    rcases le_total (|S| ^ 2) 1 with h | h
    · rw [max_eq_left h, one_pow]
      have : (0 : ℝ) ≤ |S| ^ (2 * xi) := by positivity
      linarith only [this]
    · rw [max_eq_right h, ← pow_mul, mul_comm 2 xi]
      have : (0 : ℝ) ≤ (1 : ℝ) := zero_le_one
      have heq : |S| ^ (xi * 2) = |S| ^ (2 * xi) := by rw [mul_comm]
      rw [heq]
      linarith only [this]
  have hc0 : (0 : ℝ) ≤ (nu + 2 * nu⁻¹) ^ xi := by positivity
  calc (nu + 2 * nu⁻¹ * S ^ 2) ^ xi
      ≤ ((nu + 2 * nu⁻¹) * max 1 (|S| ^ 2)) ^ xi := hpow
    _ = (nu + 2 * nu⁻¹) ^ xi * (max 1 (|S| ^ 2)) ^ xi := mul_pow _ _ _
    _ ≤ (nu + 2 * nu⁻¹) ^ xi * (1 + |S| ^ (2 * xi)) :=
        mul_le_mul_of_nonneg_left hmaxpow hc0

/-- **The upper moment condition of the quantitative coarse-grained ellipticity
input**, from the `L^infinity` size of the cutoff on the rebasing cube. A
`Gamma_2` tail has all polynomial moments, so the `xi`-th moment of a polynomial
of degree `2` in the envelope is finite. This is the first conjunct of
`CutoffEllipticityMoments`. -/
theorem integrable_LambdaSqCoeffField_pow_rebasedCutoffLaw [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) {m : ℕ} {P : ProbabilityMeasure (ShellSeq d)}
    (hlinfty : CutoffLargeCubeLinfty m P) {sUpper : ℝ} (hsUpper : 0 < sUpper)
    (xi : ℕ) :
    Integrable (fun a : RegCoeffField d ↦
        Book.Ch04.LambdaSqCoeffField (originCube d (0 : ℤ)) sUpper (.finite 1) a ^ xi)
      (rebasedCutoffLaw nu m P) := by
  obtain ⟨S, A, hA, hSm, hStail, hSbound⟩ := hlinfty
  have hcarrier := restrictionLawCarrier_rebasedCutoffLaw hnu m P
  have hmeas : AEStronglyMeasurable (fun a : RegCoeffField d ↦
      Book.Ch04.LambdaSqCoeffField (originCube d (0 : ℤ)) sUpper (.finite 1) a ^ xi)
      (rebasedCutoffLaw nu m P) :=
    ((hcarrier.aemeasurable_LambdaSqCoeffField_finite_one
      (originCube d (0 : ℤ)) hsUpper).pow_const xi).aestronglyMeasurable
  have hmom : Integrable (fun omega : ShellSeq d ↦ |S omega| ^ ((2 * xi : ℕ) : ℝ))
      P.toMeasure :=
    SuperdiffusionCLT.Probability.integrable_abs_rpow_of_isBigO_gammaSigma_two
      hA hSm hStail (2 * xi)
  have hmom' : Integrable (fun omega : ShellSeq d ↦ |S omega| ^ (2 * xi))
      P.toMeasure := by
    refine hmom.congr (Filter.Eventually.of_forall fun omega ↦ ?_)
    exact Real.rpow_natCast (|S omega|) (2 * xi)
  refine integrable_rebasedCutoffLaw_of_le
    (g := fun omega ↦ (nu + 2 * nu⁻¹) ^ xi * (1 + |S omega| ^ (2 * xi))) hmeas
    (((integrable_const (1 : ℝ)).add hmom').const_mul _) fun omega ↦ ?_
  have hnn : (0 : ℝ) ≤ Book.Ch04.LambdaSqCoeffField (originCube d (0 : ℤ)) sUpper
      (.finite 1) (rescaleReg (d := d) (m + triadicOffset d)
        (coefficientCutoff nu omega m)) :=
    Book.Ch04.LambdaSqCoeffField_finite_nonneg _ _ hsUpper le_rfl
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hnn xi)]
  refine le_trans (pow_le_pow_left₀ hnn
    (LambdaSqCoeffField_rebasedCutoff_le hnu omega m
      (fun x hx ↦ hSbound omega x hx) hsUpper) xi) ?_
  exact pow_add_mul_sq_le hnu (S omega) xi

/-- **Both moment conditions of `CoarseGraining`'s quantitative coarse-grained
ellipticity for the rebased cutoff law**, from the `L^infinity` size of `k_m` on
the rebasing cube alone. The lower half is unconditional; the upper half is the
size estimate `e.kmn.Linfty` read at `n = 0`. -/
theorem cutoffEllipticityMoments_of_largeCubeLinfty [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {m : ℕ} {P : ProbabilityMeasure (ShellSeq d)} (hlinfty : CutoffLargeCubeLinfty m P)
    {sUpper sLower : ℝ} (hsUpper : 0 < sUpper) (hsLower : 0 < sLower) (xi : ℕ) :
    CutoffEllipticityMoments nu m P sUpper sLower xi :=
  ⟨integrable_LambdaSqCoeffField_pow_rebasedCutoffLaw hnu hlinfty hsUpper xi,
    integrable_lambdaSqCoeffField_inv_pow_rebasedCutoffLaw hnu m P hsLower xi⟩

/-! ## The entry theorem with the ellipticity moments discharged -/

/-- The quantitative coarse-grained ellipticity package of the rebased cutoff
law, built from a parameter record and the `L^infinity` size of `k_m` on the
rebasing cube: the two moment conditions of
`Book.Ch05.QuantitativeCoarseGrainedEllipticity` are no longer hypotheses. -/
def quantitativeCoarseGrainedEllipticity_rebasedCutoffLaw_of_largeCubeLinfty [NeZero d]
    (params : Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d)
    {nu : ℝ} (hnu : 0 < nu) {m : ℕ} {P : ProbabilityMeasure (ShellSeq d)}
    (hlinfty : CutoffLargeCubeLinfty m P) :
    Book.Ch05.QuantitativeCoarseGrainedEllipticity (rebasedCutoffLaw nu m P) :=
  quantitativeCoarseGrainedEllipticity_rebasedCutoffLaw nu m P params
    (cutoffEllipticityMoments_of_largeCubeLinfty hnu hlinfty params.sUpper_pos
      params.sLower_pos params.xi)

end

end SuperdiffusionCLT.Section3.HighContrast
