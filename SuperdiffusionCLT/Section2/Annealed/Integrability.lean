/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.BlockAverageBound
public import SuperdiffusionCLT.Section2.Annealed.Symmetry

/-!
# Integrability of the coarse block matrix of the infrared cutoff

The annealed matrices of display `e.homs.defs.U.0` are expectations of the coarse-grained
block matrix `bfA_m(U)` of the cutoff field `a_m = nu Id + k_m`. That those
expectations are genuine Bochner integrals is the content of this module.

The chain is the one the manuscript uses in the proof of `l.bfAm.ellip`. Pointwise,
with `s = nu Id` and `k = k_m(x)`, the block field of `e.bfA.def` is

`bfA_m(x) = [[nu Id + nu⁻¹ k^t k, -nu⁻¹ k^t], [-nu⁻¹ k, nu⁻¹ Id]]`,

so Young's inequality `e.how.to.upbound.A` gives the block-diagonal majorant
`[[nu Id + 2 nu⁻¹ k^t k, 0], [0, 2 nu⁻¹ Id]]` and hence the scalar bound

`(p,q) · bfA_m(x) (p,q) ≤ (nu + 2 nu⁻¹ |k_m(x)|²) |p|² + 2 nu⁻¹ |q|².`

Averaging over a cube and using `e.CG.bounds.2` transports this to `bfA_m(U)`
with `|k_m(x)|²` replaced by its normalized `L²(U)` size, which by
`e.km.Ltwo.size` has a Γ₁ tail and is therefore integrable. Since
`bfA_m(U)` is symmetric and positive semidefinite, all of its entries are
controlled by its diagonal entries, so all of them are integrable.

## Main results

* `blockQuadratic_coefficientCutoff_le`: the pointwise scalar bound.
* `blockVecDot_coarseBlockMatrix_coefficientCutoff_le`: its coarse-grained
  form on a triadic cube.
* `integrable_volumeAverage_sq_streamCutoff`: `⨍_U |k_m|²` is integrable.
* `integrable_blockMatEntry_coarseBlockMatrix`,
  `integrable_coarseBlockMatrix_upperLeft_apply` and companions: the entries of
  `bfA_m(cu_n)` are integrable, so `annealedBlockMatrix` is a genuine
  expectation.
* `sigmaBarStarInvScalar_pos_cutoff`: the version of the corresponding
  theorem of the neighbouring modules with its `Integrable` premises discharged.
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

/-! ## The pointwise block field of the cutoff -/

private theorem matVecMulOne (x : Vec d) : matVecMul (1 : Mat d) x = x := by
  funext i
  simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]

/-- The inverse of a nonzero scalar matrix. -/
theorem inv_smul_one_mat {nu : ℝ} (hnu : nu ≠ 0) :
    (nu • (1 : Mat d))⁻¹ = nu⁻¹ • (1 : Mat d) := by
  rw [nonsing_inv_smul nu hnu (by simp)]
  simp

private theorem isSymm_smul_one {nu : ℝ} : ((nu • (1 : Mat d))).IsSymm := by
  show Matrix.transpose (nu • (1 : Mat d)) = nu • (1 : Mat d)
  rw [Matrix.transpose_smul, Matrix.transpose_one]

private theorem vecDot_smul_one {nu : ℝ} (x : Vec d) :
    vecDot x (matVecMul (nu • (1 : Mat d)) x) = nu * vecNormSq x := by
  rw [smul_matVecMul, matVecMulOne, vecDot_smul_right]
  rfl

/-- **`e.how.to.upbound.A` for the infrared cutoff**: the pointwise block field
of `a_m` is dominated by `[[nu Id + 2 nu⁻¹ k_m^t k_m, 0], [0, 2 nu⁻¹ Id]]`. -/
theorem blockMatLoewnerLE_blockDiag_coefficientCutoff {nu : ℝ} (hnu : 0 < nu)
    (omega : ShellSeq d) (m : ℕ) (x : Vec d) :
    BlockMatLoewnerLE (blockMatrixOfCoeff ((coefficientCutoff nu omega m).toCoeffField x))
      (Book.Ch02.blockDiag
        (nu • (1 : Mat d) +
          (2 : ℝ) • (matTranspose (streamCutoff omega m x) * (nu⁻¹ • (1 : Mat d)) *
            streamCutoff omega m x))
        ((2 : ℝ) • (nu⁻¹ • (1 : Mat d)))) := by
  have hpsd : ∀ y : Vec d, 0 ≤ vecDot y (matVecMul (nu⁻¹ • (1 : Mat d)) y) := by
    intro y
    rw [vecDot_smul_one]
    exact mul_nonneg (inv_nonneg.2 hnu.le) (vecNormSq_nonneg y)
  have hyoung := blockMatLoewnerLE_blockDiag_young
    (s₁ := nu • (1 : Mat d)) (s₂ := nu⁻¹ • (1 : Mat d))
    (k := streamCutoff omega m x) isSymm_smul_one hpsd
  have hs : symmPart ((coefficientCutoff nu omega m).toCoeffField x) = nu • (1 : Mat d) :=
    symmPart_coefficientCutoff nu omega m x
  have hk : skewPart ((coefficientCutoff nu omega m).toCoeffField x) =
      streamCutoff omega m x := skewPart_coefficientCutoff nu omega m x
  have hrw : blockMatrixOfCoeff ((coefficientCutoff nu omega m).toCoeffField x) =
      BlockMat.mk
        (nu • (1 : Mat d) + matTranspose (streamCutoff omega m x) *
          (nu⁻¹ • (1 : Mat d)) * streamCutoff omega m x)
        (-(matTranspose (streamCutoff omega m x) * (nu⁻¹ • (1 : Mat d))))
        (-((nu⁻¹ • (1 : Mat d)) * streamCutoff omega m x))
        (nu⁻¹ • (1 : Mat d)) := by
    show BlockMat.mk _ _ _ _ = _
    rw [hs, hk, inv_smul_one_mat hnu.ne']
  rw [hrw]
  exact hyoung

/-- The pointwise scalar bound behind the first display in the proof of
`l.bfAm.ellip`:
`(p,q) · bfA_m(x) (p,q) ≤ (nu + 2 nu⁻¹ |k_m(x)|²) |p|² + 2 nu⁻¹ |q|²`. -/
theorem blockQuadratic_coefficientCutoff_le {nu : ℝ} (hnu : 0 < nu)
    (omega : ShellSeq d) (m : ℕ) (x p q : Vec d) :
    blockVecDot (p, q)
        (blockMatVecMul
          (blockMatrixOfCoeff ((coefficientCutoff nu omega m).toCoeffField x)) (p, q)) ≤
      (nu + 2 * nu⁻¹ *
          Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ^ 2) * vecNormSq p +
        2 * nu⁻¹ * vecNormSq q := by
  have hbig := blockMatLoewnerLE_blockDiag_coefficientCutoff hnu omega m x (p, q)
  have hRval : blockVecDot (p, q)
      (blockMatVecMul (Book.Ch02.blockDiag
        (nu • (1 : Mat d) +
          (2 : ℝ) • (matTranspose (streamCutoff omega m x) * (nu⁻¹ • (1 : Mat d)) *
            streamCutoff omega m x))
        ((2 : ℝ) • (nu⁻¹ • (1 : Mat d)))) (p, q)) =
      nu * vecNormSq p +
        2 * nu⁻¹ * vecNormSq (matVecMul (streamCutoff omega m x) p) +
        2 * nu⁻¹ * vecNormSq q := by
    rw [blockQuadratic_eq]
    show vecDot p (matVecMul (nu • (1 : Mat d) +
          (2 : ℝ) • (matTranspose (streamCutoff omega m x) * (nu⁻¹ • (1 : Mat d)) *
            streamCutoff omega m x)) p) +
        vecDot p (matVecMul (0 : Mat d) q) + vecDot q (matVecMul (0 : Mat d) p) +
        vecDot q (matVecMul ((2 : ℝ) • (nu⁻¹ • (1 : Mat d))) q) = _
    have hzero : ∀ y : Vec d, matVecMul (0 : Mat d) y = 0 := by
      intro y
      funext i
      simp [matVecMul]
    have hmid : vecDot p (matVecMul ((2 : ℝ) •
        (matTranspose (streamCutoff omega m x) * (nu⁻¹ • (1 : Mat d)) *
          streamCutoff omega m x)) p) =
        2 * nu⁻¹ * vecNormSq (matVecMul (streamCutoff omega m x) p) := by
      have hmat : matTranspose (streamCutoff omega m x) * (nu⁻¹ • (1 : Mat d)) *
          streamCutoff omega m x =
          nu⁻¹ • (matTranspose (streamCutoff omega m x) * streamCutoff omega m x) := by
        rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
      rw [hmat, smul_smul, smul_matVecMul, vecDot_smul_right, ← matVecMul_mul,
        vecDot_matVecMul_transpose]
      rfl
    rw [add_matVecMul, vecDot_add_right, vecDot_smul_one, hmid, hzero, hzero,
      vecDot_zero_right, vecDot_zero_right, smul_smul, vecDot_smul_one]
    ring
  rw [hRval] at hbig
  have hop := Book.Ch02.vecNormSq_matVecMul_le_matrixOperatorNorm_sq_mul_vecNormSq
    (streamCutoff omega m x) p
  have hcoef : (0 : ℝ) ≤ 2 * nu⁻¹ := by positivity
  have hmul := mul_le_mul_of_nonneg_left hop hcoef
  linarith only [hbig, hmul]

/-! ## Averages over a cube -/

private theorem volumeAverage_mono {U : Set (Vec d)} {f g : Vec d → ℝ}
    (hf0 : 0 ≤ᵐ[volumeMeasureOn U] f) (hg : IntegrableOn g U)
    (hfg : f ≤ᵐ[volumeMeasureOn U] g) :
    volumeAverage U f ≤ volumeAverage U g := by
  have hint : ∫ x in U, f x ≤ ∫ x in U, g x := integral_mono_of_nonneg hf0 hg hfg
  have hvol : (0 : ℝ) ≤ (MeasureTheory.volume U).toReal⁻¹ := by positivity
  have hmul := mul_le_mul_of_nonneg_left hint hvol
  unfold volumeAverage
  linarith only [hmul]

private theorem volumeAverage_affine {U : Set (Vec d)}
    (hU0 : MeasureTheory.volume U ≠ 0) (hUtop : MeasureTheory.volume U ≠ ⊤)
    {Y : Vec d → ℝ} (hY : IntegrableOn Y U) (alpha beta : ℝ) :
    volumeAverage U (fun x ↦ alpha * Y x + beta) =
      alpha * volumeAverage U Y + beta := by
  have hfin : IsFiniteMeasure (volumeMeasureOn U) := by
    refine ⟨?_⟩
    rw [MeasureTheory.Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hUtop
  have hc : 0 < (MeasureTheory.volume U).toReal := ENNReal.toReal_pos hU0 hUtop
  have hconst : ∫ _x in U, beta ∂MeasureTheory.volume =
      (MeasureTheory.volume U).toReal * beta := by
    rw [MeasureTheory.setIntegral_const, smul_eq_mul, measureReal_def]
  have hsplit : ∫ x in U, (alpha * Y x + beta) ∂MeasureTheory.volume =
      alpha * (∫ x in U, Y x ∂MeasureTheory.volume) +
        (MeasureTheory.volume U).toReal * beta := by
    rw [integral_add (hY.const_mul alpha) (integrable_const beta), integral_const_mul, hconst]
  unfold volumeAverage
  rw [hsplit]
  field_simp

/-- The pointwise squared size of the cutoff field is integrable on every
triadic cube: it is continuous, and the cube is contained in a closed ball. -/
theorem integrableOn_matrixOperatorNorm_sq_streamCutoff (omega : ShellSeq d) (m : ℕ)
    (Q : TriadicCube d) :
    IntegrableOn
      (fun x ↦ Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ^ 2)
      (openCubeSet Q) := by
  have hcont : Continuous
      (fun x : Vec d ↦ Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ^ 2) :=
    (ShellField.continuous_matrixOperatorNorm.comp
      (continuous_streamCutoff_apply omega m)).pow 2
  have hball := hcont.continuousOn.integrableOn_compact
    (isCompact_closedBall (cubeCenter Q) (cubeRadius Q))
    (μ := MeasureTheory.volume)
  exact hball.mono_set
    ((openCubeSet_subset_cubeSet Q).trans (cubeSet_subset_closedBall Q))

/-- A triadic cube has positive volume. -/
theorem volume_openCubeSet_ne_zero (Q : TriadicCube d) :
    MeasureTheory.volume (openCubeSet Q) ≠ 0 := by
  intro h
  have := volume_openCubeSet_toReal Q
  rw [h] at this
  exact (cubeVolume_pos Q).ne (by simpa using this)

/-! ## The coarse-grained bound on a cube -/

section Cube

variable [NeZero d] {nu : ℝ} (hnu : 0 < nu) (omega : ShellSeq d) (m : ℕ)
  (Q : TriadicCube d)

include hnu

/-- The Chapter 2 coefficient object of `a_m` on a triadic cube supplied by the
unconditional admissibility of the cutoff field. -/
private def cutoffCoeffOn : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q) :=
  (Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
    (coefficientCutoff nu omega m)
    (aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega m)).coeffOn Q

/-- **The coarse block matrix of the cutoff field on a triadic cube is the Chapter 2 coarse block
matrix of its coefficient on that cube**: the coarse-grained form `bfA_m(cu)` entering the quadratic
comparison of `l.bfAm.ellip` is the Chapter 2 object attached to the coefficient supplied by the
unconditional admissibility `l.ell.adm` of the cutoff field. -/
theorem coarseBlockMatrix_cubeSet_coefficientCutoff_eq_ch02 :
    coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega m).toFun =
      Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q)
        ((Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
            (coefficientCutoff nu omega m)
            (aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega m)).coeffOn Q) :=
  Book.Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
    (aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega m) Q

/-- **The coarse-grained form of the first display in the proof of
`l.bfAm.ellip`**: on a triadic cube,
`(p,q) · bfA_m(cu) (p,q) ≤ (nu + 2 nu⁻¹ ‖k_m‖²_{L²(cu)}) |p|² + 2 nu⁻¹ |q|²`. -/
theorem blockVecDot_coarseBlockMatrix_coefficientCutoff_le (p q : Vec d) :
    blockVecDot (p, q)
        (blockMatVecMul
          (coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega m).toFun) (p, q)) ≤
      (nu + 2 * nu⁻¹ * volumeAverage (openCubeSet Q)
          (fun x ↦ Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ^ 2)) *
          vecNormSq p + 2 * nu⁻¹ * vecNormSq q := by
  have hcoe : ((Book.Ch02.cubeDomain Q : Book.Ch02.Domain d) : Set (Vec d)) =
      openCubeSet Q := Book.Ch02.cubeDomain_coe Q
  have hvar := blockVecDot_coarseBlockMatrix_le_volumeAverage
    (Book.Ch02.cubeDomain Q) (cutoffCoeffOn hnu omega m Q) (p, q)
  rw [coarseBlockMatrix_cubeSet_coefficientCutoff_eq_ch02 hnu omega m Q]
  refine hvar.trans ?_
  have hfield : ∀ x : Vec d,
      Book.Ch02.blockMatrixField (cutoffCoeffOn hnu omega m Q) x =
        blockMatrixOfCoeff ((coefficientCutoff nu omega m).toCoeffField x) := fun _ ↦ rfl
  simp only [hfield, hcoe]
  have hY := integrableOn_matrixOperatorNorm_sq_streamCutoff omega m Q
  have hmaj : volumeAverage (openCubeSet Q)
      (fun x ↦ blockVecDot (p, q) (blockMatVecMul
        (blockMatrixOfCoeff ((coefficientCutoff nu omega m).toCoeffField x)) (p, q))) ≤
      volumeAverage (openCubeSet Q)
        (fun x ↦ (2 * nu⁻¹ * vecNormSq p) *
            Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ^ 2 +
          (nu * vecNormSq p + 2 * nu⁻¹ * vecNormSq q)) := by
    refine volumeAverage_mono ?_ ?_ ?_
    · filter_upwards [(cutoffCoeffOn hnu omega m Q).aeElliptic] with x hx
      exact blockMatrixOfCoeff_quadratic_nonneg hx (p, q)
    · have hfin : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) := by
        refine ⟨?_⟩
        rw [MeasureTheory.Measure.restrict_apply_univ]
        exact volume_openCubeSet_lt_top Q
      exact ((hY.const_mul (2 * nu⁻¹ * vecNormSq p)).add
        (integrable_const (nu * vecNormSq p + 2 * nu⁻¹ * vecNormSq q)))
    · refine Filter.Eventually.of_forall fun x ↦ ?_
      have h := blockQuadratic_coefficientCutoff_le hnu omega m x p q
      linarith only [h]
  refine hmaj.trans ?_
  rw [volumeAverage_affine (volume_openCubeSet_ne_zero Q)
    (volume_openCubeSet_lt_top Q).ne hY]
  exact le_of_eq (by ring)

end Cube

/-! ## Entry bounds from symmetry and positivity -/

private theorem vecNormSq_single (i : Fin d) : vecNormSq (Pi.single i (1 : ℝ)) = 1 := by
  show vecDot (Pi.single i (1 : ℝ)) (Pi.single i (1 : ℝ)) = 1
  rw [vecDot_single_left]
  simp

private theorem vecNormSq_zero_vec : vecNormSq (0 : Vec d) = 0 := by
  show vecDot (0 : Vec d) (0 : Vec d) = 0
  rw [vecDot_zero_left]

private theorem zero_le_volumeAverage_sq (omega : ShellSeq d) (m : ℕ) (Q : TriadicCube d) :
    0 ≤ volumeAverage (openCubeSet Q)
      (fun x ↦ Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ^ 2) := by
  unfold volumeAverage
  exact mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
    (integral_nonneg fun x ↦ by positivity)

/-- The envelope of the entries of `bfA_m(cu)` provided by the coarse-grained
form of the pointwise bound. -/
def cutoffBlockEntryBound (nu : ℝ) (omega : ShellSeq d) (m : ℕ) (Q : TriadicCube d) : ℝ :=
  nu + 2 * nu⁻¹ * volumeAverage (openCubeSet Q)
      (fun x ↦ Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ^ 2) + 2 * nu⁻¹

section CubeEntries

variable [NeZero d] {nu : ℝ} (hnu : 0 < nu) (omega : ShellSeq d) (m : ℕ)
  (Q : TriadicCube d)

include hnu

/-- The coarse block matrix of the cutoff is a symmetric block matrix. -/
theorem isSymmetricBlockMat_coarseBlockMatrix_coefficientCutoff :
    IsSymmetricBlockMat
      (coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega m).toFun) := by
  rw [coarseBlockMatrix_cubeSet_coefficientCutoff_eq_ch02 hnu omega m Q]
  exact Book.Ch02.isSymmetricBlockMat_coarseBlockMatrix _ _

/-- The coarse block matrix of the cutoff is positive semidefinite. -/
theorem zero_le_blockVecDot_coarseBlockMatrix_coefficientCutoff (X : BlockVec d) :
    0 ≤ blockVecDot X
      (blockMatVecMul
        (coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega m).toFun) X) := by
  rw [coarseBlockMatrix_cubeSet_coefficientCutoff_eq_ch02 hnu omega m Q]
  exact SuperdiffusionCLT.Section2.Localization.zero_le_blockVecDot_coarseBlockMatrix
    _ _ X

/-- Each diagonal entry of `bfA_m(cu)` is bounded by
`nu + 2 nu⁻¹ ‖k_m‖²_{L²(cu)} + 2 nu⁻¹`. -/
theorem blockMatEntry_diag_le (alpha : BlockCoord d) :
    blockMatEntry
        (coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega m).toFun)
        alpha alpha ≤ cutoffBlockEntryBound nu omega m Q := by
  have hZ := zero_le_volumeAverage_sq omega m Q
  have hnuinv : (0 : ℝ) ≤ 2 * nu⁻¹ := by positivity
  cases alpha with
  | inl i =>
      have h := blockVecDot_coarseBlockMatrix_coefficientCutoff_le hnu omega m Q
        (Pi.single i 1) 0
      rw [vecNormSq_single, vecNormSq_zero_vec] at h
      have hbasis := blockBasis_pairing
        (coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega m).toFun)
        (Sum.inl i) (Sum.inl i)
      rw [← hbasis]
      unfold cutoffBlockEntryBound
      have hb : blockBasis (Sum.inl i) = ((Pi.single i (1 : ℝ)), (0 : Vec d)) := rfl
      rw [hb]
      linarith only [h, hnuinv]
  | inr i =>
      have h := blockVecDot_coarseBlockMatrix_coefficientCutoff_le hnu omega m Q
        0 (Pi.single i 1)
      rw [vecNormSq_single, vecNormSq_zero_vec] at h
      have hbasis := blockBasis_pairing
        (coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega m).toFun)
        (Sum.inr i) (Sum.inr i)
      rw [← hbasis]
      unfold cutoffBlockEntryBound
      have hb : blockBasis (Sum.inr i) = ((0 : Vec d), (Pi.single i (1 : ℝ))) := rfl
      rw [hb]
      have hnn : (0 : ℝ) ≤ 2 * nu⁻¹ * volumeAverage (openCubeSet Q)
          (fun x ↦ Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ^ 2) :=
        mul_nonneg hnuinv hZ
      linarith only [h, hnn, hnu]

/-- **Every entry of `bfA_m(cu)` is bounded by `cutoffBlockEntryBound`.** -/
theorem abs_blockMatEntry_coarseBlockMatrix_le (alpha beta : BlockCoord d) :
    |blockMatEntry
        (coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega m).toFun)
        alpha beta| ≤ cutoffBlockEntryBound nu omega m Q := by
  have hentry := abs_blockMatEntry_le_of_isSymmetricBlockMat
    (isSymmetricBlockMat_coarseBlockMatrix_coefficientCutoff hnu omega m Q)
    (zero_le_blockVecDot_coarseBlockMatrix_coefficientCutoff hnu omega m Q) alpha beta
  have h1 := blockMatEntry_diag_le hnu omega m Q alpha
  have h2 := blockMatEntry_diag_le hnu omega m Q beta
  linarith only [hentry, h1, h2]

end CubeEntries

/-! ## Integrability of the size observable -/

variable {P : ProbabilityMeasure (ShellSeq d)}

/-- A jointly measurable family has a measurable normalized volume average. -/
theorem measurable_volumeAverage_of_measurable_uncurry {Omega : Type*}
    [MeasurableSpace Omega] (Y : Vec d → Omega → ℝ)
    (hY : Measurable (Function.uncurry Y)) (U : Set (Vec d)) :
    Measurable (fun omega ↦ volumeAverage U (fun x ↦ Y x omega)) := by
  have hswap : Measurable (fun q : Omega × Vec d ↦ Y q.2 q.1) := hY.comp measurable_swap
  have hint : StronglyMeasurable (fun omega : Omega ↦
      ∫ x, Y x omega ∂(volumeMeasureOn U)) :=
    hswap.stronglyMeasurable.integral_prod_right'
  unfold volumeAverage
  exact hint.measurable.const_mul _

/-- The normalized `L²` size of the cutoff is a measurable observable. -/
theorem measurable_volumeAverage_sq_streamCutoff (m : ℕ) (U : Set (Vec d)) :
    Measurable (fun omega : ShellSeq d ↦ volumeAverage U
      (fun x ↦ Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ^ 2)) :=
  measurable_volumeAverage_of_measurable_uncurry
    (fun (x : Vec d) (omega : ShellSeq d) ↦
      Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ^ 2)
    ((continuous_pow 2).measurable.comp
      (measurable_uncurry_matrixOperatorNorm_streamCutoff m)) U

/-- **`e.km.Ltwo.size` makes the normalized `L²` size integrable.** The
Γ₁ tail of `⨍_U |k_m|²` gives it a finite first moment. -/
theorem integrable_volumeAverage_sq_streamCutoff
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (m : ℕ) {U : Set (Vec d)}
    (hU0 : MeasureTheory.volume U ≠ 0) (hUtop : MeasureTheory.volume U ≠ ⊤) :
    Integrable (fun omega ↦ volumeAverage U
      (fun x ↦ Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ^ 2))
      P.toMeasure := by
  have hbig := isBigOWith_gammaSigma_volumeAverage_sq_streamCutoff
    hPrefix hJ2 hJ3 hJ4 m hU0 hUtop
  have hK : 0 < cutoffL2Const d * ((m : ℝ) + 1) :=
    mul_pos (cutoffL2Const_pos hPrefix) (by positivity)
  have hnonneg : ∀ omega : ShellSeq d, 0 ≤ volumeAverage U
      (fun x ↦ Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ^ 2) := by
    intro omega
    unfold volumeAverage
    exact mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
      (integral_nonneg fun x ↦ by positivity)
  have h := IndependentSums.integrable_rpow_of_isBigOWith_gammaSigma
    (μ := P.toMeasure) one_pos hK le_rfl hnonneg
    (measurable_volumeAverage_sq_streamCutoff m U).aemeasurable hbig
  simpa only [Real.rpow_one] using h

/-! ## Integrability of the entries of the coarse block matrix -/

section CubeIntegrability

variable [NeZero d] {nu : ℝ} (hnu : 0 < nu) (m : ℕ) (Q : TriadicCube d)
  (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
  (hJ4 : ShellLawJ4 d P)

include hnu hPrefix hJ2 hJ3 hJ4

omit [NeZero d] hnu in
/-- The entry envelope of `bfA_m(cu_Q)` is integrable. -/
theorem integrable_cutoffBlockEntryBound :
    Integrable (fun omega ↦ cutoffBlockEntryBound nu omega m Q) P.toMeasure := by
  have hZ := integrable_volumeAverage_sq_streamCutoff hPrefix hJ2 hJ3 hJ4 m
    (U := openCubeSet Q) (volume_openCubeSet_ne_zero Q)
    (volume_openCubeSet_lt_top Q).ne
  unfold cutoffBlockEntryBound
  exact ((integrable_const nu).add (hZ.const_mul (2 * nu⁻¹))).add
    (integrable_const (2 * nu⁻¹))

omit [NeZero d] hPrefix hJ2 hJ3 hJ4 in
/-- The entries of `bfA_m(cu_Q)` are measurable observables. -/
theorem measurable_blockMatEntry_coarseBlockMatrix (alpha beta : BlockCoord d) :
    Measurable (fun omega : ShellSeq d ↦
      blockMatEntry
        (coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega m).toFun)
        alpha beta) := by
  have hA := measurable_coefficientCutoff (d := d) nu m
  have hEll := fun omega : ShellSeq d ↦
    aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega m
  cases alpha with
  | inl i =>
      cases beta with
      | inl j => exact measurable_coarseBlockMatrix_upperLeft_apply hA hEll Q i j
      | inr j => exact measurable_coarseBlockMatrix_upperRight_apply hA hEll Q i j
  | inr i =>
      cases beta with
      | inl j => exact measurable_coarseBlockMatrix_lowerLeft_apply hA hEll Q i j
      | inr j => exact measurable_coarseBlockMatrix_lowerRight_apply hA hEll Q i j

/-- **The entries of `bfA_m(cu_Q)` are integrable**, so the annealed block
matrix `bfAhom_m(cu_Q)` of `e.homs.defs.U.0` is a genuine expectation. -/
theorem integrable_blockMatEntry_coarseBlockMatrix (alpha beta : BlockCoord d) :
    Integrable (fun omega : ShellSeq d ↦
      blockMatEntry
        (coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega m).toFun)
        alpha beta) P.toMeasure := by
  refine Integrable.mono'
    (integrable_cutoffBlockEntryBound (nu := nu) m Q hPrefix hJ2 hJ3 hJ4)
    (measurable_blockMatEntry_coarseBlockMatrix hnu m Q alpha beta).aestronglyMeasurable
    (Filter.Eventually.of_forall fun omega ↦ ?_)
  rw [Real.norm_eq_abs]
  exact abs_blockMatEntry_coarseBlockMatrix_le hnu omega m Q alpha beta

/-- The upper-left block entries of `bfA_m(cu_Q)` are integrable. -/
theorem integrable_coarseBlockMatrix_upperLeft_apply (i j : Fin d) :
    Integrable (fun omega : ShellSeq d ↦
      (coarseBlockMatrix (cubeSet Q)
        (coefficientCutoff nu omega m).toFun).upperLeft i j) P.toMeasure :=
  integrable_blockMatEntry_coarseBlockMatrix hnu m Q hPrefix hJ2 hJ3 hJ4
    (Sum.inl i) (Sum.inl j)

/-- The upper-right block entries of `bfA_m(cu_Q)` are integrable. -/
theorem integrable_coarseBlockMatrix_upperRight_apply (i j : Fin d) :
    Integrable (fun omega : ShellSeq d ↦
      (coarseBlockMatrix (cubeSet Q)
        (coefficientCutoff nu omega m).toFun).upperRight i j) P.toMeasure :=
  integrable_blockMatEntry_coarseBlockMatrix hnu m Q hPrefix hJ2 hJ3 hJ4
    (Sum.inl i) (Sum.inr j)

/-- The lower-left block entries of `bfA_m(cu_Q)` are integrable. -/
theorem integrable_coarseBlockMatrix_lowerLeft_apply (i j : Fin d) :
    Integrable (fun omega : ShellSeq d ↦
      (coarseBlockMatrix (cubeSet Q)
        (coefficientCutoff nu omega m).toFun).lowerLeft i j) P.toMeasure :=
  integrable_blockMatEntry_coarseBlockMatrix hnu m Q hPrefix hJ2 hJ3 hJ4
    (Sum.inr i) (Sum.inl j)

/-- The lower-right block entries of `bfA_m(cu_Q)` are integrable. -/
theorem integrable_coarseBlockMatrix_lowerRight_apply (i j : Fin d) :
    Integrable (fun omega : ShellSeq d ↦
      (coarseBlockMatrix (cubeSet Q)
        (coefficientCutoff nu omega m).toFun).lowerRight i j) P.toMeasure :=
  integrable_blockMatEntry_coarseBlockMatrix hnu m Q hPrefix hJ2 hJ3 hJ4
    (Sum.inr i) (Sum.inr j)

/-- The lower-right block of `bfA_m(cu_Q)` is a Bochner integrable
matrix-valued observable. -/
theorem integrable_coarseBlockMatrix_lowerRight :
    Integrable (fun omega : ShellSeq d ↦
      (coarseBlockMatrix (cubeSet Q)
        (coefficientCutoff nu omega m).toFun).lowerRight) P.toMeasure := by
  refine MeasureTheory.Integrable.of_eval ?_
  intro i
  refine MeasureTheory.Integrable.of_eval ?_
  intro j
  exact integrable_coarseBlockMatrix_lowerRight_apply hnu m Q hPrefix hJ2 hJ3 hJ4 i j

end CubeIntegrability

/-! ## Entries of a symmetric positive semidefinite matrix -/

/-- Polarization of a matrix quadratic form along a one-parameter family. -/
theorem matQuadratic_add_smul (M : Mat d) (x y : Vec d) (c : ℝ) :
    vecDot (x + c • y) (matVecMul M (x + c • y)) =
      vecDot x (matVecMul M x) +
        c * (vecDot x (matVecMul M y) + vecDot y (matVecMul M x)) +
        c ^ 2 * vecDot y (matVecMul M y) := by
  rw [matVecMul_add, matVecMul_smul, vecDot_add_left, vecDot_add_right,
    vecDot_add_right, vecDot_smul_left, vecDot_smul_left, vecDot_smul_right,
    vecDot_smul_right]
  ring

/-- The pairing of two coordinate vectors through a matrix is the entry. -/
theorem vecDot_single_matVecMul_single (M : Mat d) (i j : Fin d) :
    vecDot (Pi.single i (1 : ℝ)) (matVecMul M (Pi.single j (1 : ℝ))) = M i j := by
  rw [matVecMul_single, vecDot_single_left]

/-- Every entry of a symmetric positive semidefinite matrix is bounded by the
mean of the two diagonal entries it sits between. -/
theorem abs_entry_le_of_isSymm_of_nonneg {M : Mat d} (hsymm : M.IsSymm)
    (hpos : ∀ x : Vec d, 0 ≤ vecDot x (matVecMul M x)) (i j : Fin d) :
    |M i j| ≤ (M i i + M j j) / 2 := by
  have hsym := hsymm.apply i j
  have hplus := hpos ((Pi.single i (1 : ℝ) : Vec d) +
    (1 : ℝ) • (Pi.single j (1 : ℝ) : Vec d))
  have hminus := hpos ((Pi.single i (1 : ℝ) : Vec d) +
    (-1 : ℝ) • (Pi.single j (1 : ℝ) : Vec d))
  rw [matQuadratic_add_smul, vecDot_single_matVecMul_single,
    vecDot_single_matVecMul_single, vecDot_single_matVecMul_single,
    vecDot_single_matVecMul_single] at hplus hminus
  rw [abs_le]
  constructor
  · linarith only [hplus, hsym]
  · linarith only [hminus, hsym]

/-- The Loewner order compares diagonal entries. -/
theorem diag_le_of_matLoewnerLE {M N : Mat d} (h : MatLoewnerLE M N) (i : Fin d) :
    M i i ≤ N i i := by
  have hi := h (Pi.single i 1)
  rw [vecDot_single_matVecMul_single, vecDot_single_matVecMul_single] at hi
  linarith only [hi]

/-! ## The coarse matrices `s_*(U)` and `s(U)` of the cutoff -/

section CubeCoarseMatrices

variable [NeZero d] {nu : ℝ} (hnu : 0 < nu) (omega : ShellSeq d) (m : ℕ)
  (Q : TriadicCube d)

include hnu

end CubeCoarseMatrices

/-! ## The discharged forms of the premised theorems -/

section Discharged

variable [NeZero d] {nu : ℝ} (hnu : 0 < nu) (m : ℕ) (Q : TriadicCube d)
  (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
  (hJ4 : ShellLawJ4 d P)

include hnu hPrefix hJ2 hJ3 hJ4

end Discharged

section DischargedScalar

variable [NeZero d] {nu : ℝ} (hnu : 0 < nu) (m : ℕ)
  (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
  (hJ4 : ShellLawJ4 d P) (n : ℤ)

include hnu hPrefix hJ2 hJ3 hJ4

/-- **`shom_{m,*}^{-1}(cu_n) > 0` with no analytic premise.** This is
`sigmaBarStarInvScalar_pos` of the symmetry module with its `Integrable`
hypothesis discharged. -/
theorem sigmaBarStarInvScalar_pos_cutoff :
    0 < sigmaBarStarInvScalar nu m P (cubeSet (originCube d n)) :=
  sigmaBarStarInvScalar_pos hnu m hJ4 n
    (integrable_coarseBlockMatrix_lowerRight hnu m (originCube d n)
      hPrefix hJ2 hJ3 hJ4)

end DischargedScalar

end

end SuperdiffusionCLT.Section2.Annealed
