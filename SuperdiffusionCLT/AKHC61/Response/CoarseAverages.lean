/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.Carrier.ScalarBlocks
public import SuperdiffusionCLT.AKHC61.Carrier.ScalarBlocksB
public import Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.CoarseAverages

/-!
# Package B4, part 1: the `Ahom(cu_m)`-normalized full-block fluctuation

The application `e.weaknorms.proto.applied` requires that the *average*
terms of the deterministic weak-norm maximizer right-hand side
(`WeakNormsMaximizer.gradientAverageTermAtScale`/`fluxAverageTermAtScale`,
`WeakNormsMaximizer/Basic.lean`) be controlled by weighted sums of
`E|Ahom^{-1/2}(bfA(cu_k) - Ahom)Ahom^{-1/2}|^2`.

`CoarseGraining`'s own conversion
(`Book/Ch05/Theorems/Section53/JUpperBoundCoarseFluctuations/CoarseAverages.lean`)
proves exactly this deterministic (samplewise) inequality, but
it is typed on `hStruct : Ch04.RestrictionStructuralLaw P`, which needs
`unit_range` — unavailable for `cutoffLaw`. Its scalar
content, `hP.barSigmaAtScale hStruct m` and `hP.barSigmaStarAtScale hStruct m`,
is exactly `sigmaBarScalar`/`(sigmaBarStarInvScalar)⁻¹` of package A2
(`AKHC61/Carrier/ScalarBlocks.lean`, `ScalarBlocksB.lean`), and the "annealed
center" `Abar` used throughout is, by A2's
`akhc_annealedBlockMatrix_originCube_eq_blockDiag`, exactly the local
`annealedBlockMatrix nu L P (cubeSet (originCube d m))`. This file RETYPES
CG's algebra chain onto these local objects, with no `RestrictionStructuralLaw`
anywhere. `CoarseAveragesB.lean` finishes with the finite-sum Cauchy-Schwarz
step (CG's `HighScaleAverages.lean`) and the expectation/stationarity
assembly.

## Main results

* `akhcFullBlockNormalizedFluctuation`, `akhcFullBlockNormalizedFluctuationAtScale`:
  the local `‖Ahom(cu_m)^{-1/2}(bfA(U) - Ahom(cu_m))Ahom(cu_m)^{-1/2}‖^2`.
* `akhc_weighted_special_average_mismatch_le_fullBlockNormalized_fluctuation`:
  the pointwise (fixed field) special-vector bound, node 16's deterministic
  core.
* `akhc_descendantsAverage_weighted_special_average_mismatch_le_fullBlockNormalized_fluctuation`:
  its descendant-averaged form, feeding `CoarseAveragesB.lean`.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.Response

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.AKHC61.Carrier
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-! ## The `Ahom(cu_m)`-normalized full-block fluctuation, law-free in the field -/

section Definitions

variable [NeZero d] (nu : ℝ) (L : ℕ) (P : ProbabilityMeasure (ShellSeq d)) (m : ℤ)

/-- Diagonal full-block normalization for the two scalars `b = sigmaBarScalar`,
`c = (sigmaBarStarInvScalar)⁻¹` at scale `m`: this is `Ahom(cu_m)^{-1/2}` on the
doubled block coordinates, `Book.Ch04.scalarFullBlockInvSqrtDiag` specialized to
the local scalars. -/
noncomputable def akhcFullBlockInvSqrtDiag : BlockCoord d → ℝ :=
  Book.Ch04.scalarFullBlockInvSqrtDiag (sigmaBarScalar nu L P (cubeSet (originCube d m)))
    (sigmaBarStarInvScalar nu L P (cubeSet (originCube d m)))⁻¹

/-- The `Ahom(cu_m)`-normalized full-block fluctuation of a deterministic
sample `a` on a deterministic set `U`,
`‖Ahom(cu_m)^{-1/2}(bfA(U) - Ahom(cu_m))Ahom(cu_m)^{-1/2}‖^2`, using the
Euclidean operator norm on the doubled block coordinates. -/
noncomputable def akhcFullBlockNormalizedFluctuation (U : Set (Vec d))
    (a : CoeffField d) : ℝ :=
  let D : FullBlockMat d := Matrix.diagonal (akhcFullBlockInvSqrtDiag nu L P m)
  let A := coarseBlockMatrix U a
  let Abar := annealedBlockMatrix nu L P (cubeSet (originCube d m))
  ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
      (D * (toFullBlockMat A - toFullBlockMat Abar) * D)‖ ^ 2

/-- The cube-set specialization of `akhcFullBlockNormalizedFluctuation`, for a
carrier sample `a : RegCoeffField d`. -/
noncomputable def akhcFullBlockNormalizedFluctuationAtScale (R : TriadicCube d)
    (a : RegCoeffField d) : ℝ :=
  akhcFullBlockNormalizedFluctuation nu L P m (cubeSet R) a.toFun

/-- The scalar geometric mean `\widehat\sigma_m = (\bar\sigma_m \bar\sigma_{*,m})^{1/2}`,
local analog of CG's `sigmaHatAtScale`. -/
noncomputable def akhcSigmaHatAtScale : ℝ :=
  Real.sqrt (sigmaBarScalar nu L P (cubeSet (originCube d m)) *
    (sigmaBarStarInvScalar nu L P (cubeSet (originCube d m)))⁻¹)

/-- The special vector `p_e = \widehat\sigma_m^{-1/2} e`. -/
noncomputable def akhcSpecialPAtScale (e : Vec d) : Vec d :=
  Real.rpow (akhcSigmaHatAtScale nu L P m) (-(1 / 2 : ℝ)) • e

/-- The special vector `q_e = \widehat\sigma_m^{1/2} e`. -/
noncomputable def akhcSpecialQAtScale (e : Vec d) : Vec d :=
  Real.rpow (akhcSigmaHatAtScale nu L P m) (1 / 2 : ℝ) • e

end Definitions

/-! ## Law-free deterministic identities (retyped, verbatim, from CG) -/

theorem akhc_canonicalScalarResponseGradientAverageCubeSet_self_eq_blockMatrix
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Book.Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (p q : Vec d) :
    Book.Ch04.canonicalScalarResponseGradientAverageCubeSet Q Q p q a.toFun =
      -p + matVecMul (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight q -
        matVecMul (coarseBlockMatrix (cubeSet Q) a.toFun).lowerLeft p := by
  let F := Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let aQ : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q) := F.coeffOn Q
  let v :=
    (Book.Ch02.canonicalMaximizer
      (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain Q) aQ) p q).toSolution
  have hself : Q ∈ descendantsAtDepth Q 0 := by
    simp [descendantsAtDepth_zero]
  have hAverage :=
    Book.Ch04.canonicalScalarResponseGradientAverageCubeSet_eq_cubeAverageVec_canonicalMaximizer
      a ha (Q := Q) (R := Q) (j := 0) hself p q
  have hCubeAverage :
      cubeAverageVec Q (fun x => v.toH1.grad x) =
        Book.Ch02.averageGradient (Book.Ch02.cubeDomain Q) aQ v := by
    ext i
    rw [Book.Ch02.averageGradient, Book.Ch02.averageVec,
      Book.Ch05.Section53.JUpperBoundWeakNorms.ch02_average_cubeDomain_eq_cubeAverage]
    rfl
  have hCh02 :=
    Book.Ch02.averageGradient_canonicalMaximizer_eq_blockMatrix
      (Book.Ch02.cubeDomain Q) aQ p q
  have hCoarse :
      coarseBlockMatrix (cubeSet Q) a.toFun =
        Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q) aQ := by
    simpa [F, aQ] using
      Book.Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
        ha Q
  calc
    Book.Ch04.canonicalScalarResponseGradientAverageCubeSet Q Q p q a.toFun =
        cubeAverageVec Q (fun x => v.toH1.grad x) := by
          simpa [F, aQ, v] using hAverage
    _ = Book.Ch02.averageGradient (Book.Ch02.cubeDomain Q) aQ v := hCubeAverage
    _ =
        -p + matVecMul (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q) aQ).lowerRight q -
          matVecMul (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q) aQ).lowerLeft p := by
          simpa [aQ, v] using hCh02
    _ =
        -p + matVecMul (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight q -
          matVecMul (coarseBlockMatrix (cubeSet Q) a.toFun).lowerLeft p := by
          rw [hCoarse]

theorem akhc_canonicalScalarResponseFluxAverageCubeSet_self_eq_blockMatrix
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Book.Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (p q : Vec d) :
    Book.Ch04.canonicalScalarResponseFluxAverageCubeSet Q Q p q a.toFun =
      q + matVecMul (coarseBlockMatrix (cubeSet Q) a.toFun).upperRight q -
        matVecMul (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft p := by
  let F := Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let aQ : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q) := F.coeffOn Q
  let v :=
    (Book.Ch02.canonicalMaximizer
      (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain Q) aQ) p q).toSolution
  have hself : Q ∈ descendantsAtDepth Q 0 := by
    simp [descendantsAtDepth_zero]
  have hAverage :=
    Book.Ch04.canonicalScalarResponseFluxAverageCubeSet_eq_cubeAverageVec_canonicalMaximizerFlux
      a ha (Q := Q) (R := Q) (j := 0) hself p q
  have hCubeAverage :
      cubeAverageVec Q (fun x => matVecMul (aQ.toCoeffField x) (v.toH1.grad x)) =
        Book.Ch02.averageFlux (Book.Ch02.cubeDomain Q) aQ v := by
    ext i
    rw [Book.Ch02.averageFlux, Book.Ch02.averageVec,
      Book.Ch05.Section53.JUpperBoundWeakNorms.ch02_average_cubeDomain_eq_cubeAverage]
    rfl
  have hCh02 :=
    Book.Ch02.averageFlux_canonicalMaximizer_eq_blockMatrix
      (Book.Ch02.cubeDomain Q) aQ p q
  have hCoarse :
      coarseBlockMatrix (cubeSet Q) a.toFun =
        Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q) aQ := by
    simpa [F, aQ] using
      Book.Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
        ha Q
  calc
    Book.Ch04.canonicalScalarResponseFluxAverageCubeSet Q Q p q a.toFun =
        cubeAverageVec Q (fun x => matVecMul (aQ.toCoeffField x) (v.toH1.grad x)) := by
          simpa [F, aQ, v] using hAverage
    _ = Book.Ch02.averageFlux (Book.Ch02.cubeDomain Q) aQ v := hCubeAverage
    _ =
        q + matVecMul (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q) aQ).upperRight q -
          matVecMul (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q) aQ).upperLeft p := by
          simpa [aQ, v] using hCh02
    _ =
        q + matVecMul (coarseBlockMatrix (cubeSet Q) a.toFun).upperRight q -
          matVecMul (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft p := by
          rw [hCoarse]

/-! ## Pure block-matrix algebra (law-free, retyped verbatim from CG) -/

theorem akhc_matVecMul_smul_one {d : ℕ} (c : ℝ) (x : Vec d) :
    matVecMul (c • (1 : Mat d)) x = c • x := by
  rw [smul_matVecMul]
  change c • (Matrix.mulVec (1 : Matrix (Fin d) (Fin d) ℝ) x) = c • x
  rw [Matrix.one_mulVec]

theorem akhc_matVecMul_zero_block {d : ℕ} (x : Vec d) :
    matVecMul (0 : Mat d) x = 0 := by
  funext i
  simp [matVecMul]

/-- **Node 16's pointwise linear-algebra core.** The special-vector average
mismatch, reflected, is the reflected block-fluctuation matrix applied to the
reflected special block vector. RETYPE of CG's
`special_average_mismatch_eq_reflected_block_fluctuation`, with `Abar` the
*local* `annealedBlockMatrix nu L P (cubeSet (originCube d m))` (identified
with `blockDiag(sigmaBarScalar, sigmaBarStarInvScalar)` by A2's
`akhc_annealedBlockMatrix_originCube_eq_blockDiag`, in place of CG's
`scalarAnnealedBlockMatrixAtScale hP hStruct m`). -/
theorem akhc_special_average_mismatch_eq_reflected_block_fluctuation
    {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ) {P : ProbabilityMeasure (ShellSeq d)}
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    (a : RegCoeffField d) (ha : Book.Ch04.AELocallyUniformlyEllipticField a)
    (m : ℕ) (R : TriadicCube d) (e : Vec d) :
    let p_e := akhcSpecialPAtScale nu L P (m : ℤ) e
    let q_e := akhcSpecialQAtScale nu L P (m : ℤ) e
    let p0_e := sigmaBarStarInvScalar nu L P (cubeSet (originCube d (m : ℤ))) • q_e - p_e
    let q0_e := q_e - sigmaBarScalar nu L P (cubeSet (originCube d (m : ℤ))) • p_e
    let A := coarseBlockMatrix (cubeSet R) a.toFun
    let Abar := annealedBlockMatrix nu L P (cubeSet (originCube d (m : ℤ)))
    let P_e : BlockVec d := (-q_e, p_e)
    (-(Book.Ch04.canonicalScalarResponseGradientAverageCubeSet R R p_e q_e a.toFun - p0_e),
      -(Book.Ch04.canonicalScalarResponseFluxAverageCubeSet R R p_e q_e a.toFun - q0_e)) =
        blockMatVecMul
          (ofFullBlockMat (toFullBlockMat (blockReflect A) - toFullBlockMat (blockReflect Abar)))
          P_e := by
  dsimp only
  rw [show annealedBlockMatrix nu L P (cubeSet (originCube d (m : ℤ))) =
      Book.Ch02.blockDiag (sigmaBarScalar nu L P (cubeSet (originCube d (m : ℤ))) • (1 : Mat d))
        (sigmaBarStarInvScalar nu L P (cubeSet (originCube d (m : ℤ))) • (1 : Mat d)) from
    akhc_annealedBlockMatrix_originCube_eq_blockDiag hnu L hJ4 (m : ℤ)]
  let p_e := akhcSpecialPAtScale nu L P (m : ℤ) e
  let q_e := akhcSpecialQAtScale nu L P (m : ℤ) e
  let p0_e := sigmaBarStarInvScalar nu L P (cubeSet (originCube d (m : ℤ))) • q_e - p_e
  let q0_e := q_e - sigmaBarScalar nu L P (cubeSet (originCube d (m : ℤ))) • p_e
  let A := coarseBlockMatrix (cubeSet R) a.toFun
  let Abar : BlockMat d :=
    Book.Ch02.blockDiag (sigmaBarScalar nu L P (cubeSet (originCube d (m : ℤ))) • (1 : Mat d))
      (sigmaBarStarInvScalar nu L P (cubeSet (originCube d (m : ℤ))) • (1 : Mat d))
  let P_e : BlockVec d := (-q_e, p_e)
  have hgrad :=
    akhc_canonicalScalarResponseGradientAverageCubeSet_self_eq_blockMatrix a ha R p_e q_e
  have hflux :=
    akhc_canonicalScalarResponseFluxAverageCubeSet_self_eq_blockMatrix a ha R p_e q_e
  have hblock :
      blockMatVecMul
          (ofFullBlockMat (toFullBlockMat (blockReflect A) - toFullBlockMat (blockReflect Abar)))
          P_e =
        blockMatVecMul (blockReflect A) P_e - blockMatVecMul (blockReflect Abar) P_e :=
    blockMatVecMul_ofFullBlockMat_sub (blockReflect A) (blockReflect Abar) P_e
  rw [hblock]
  rw [hgrad, hflux]
  ext i <;>
    simp [p_e, q_e, P_e, A, Abar, Book.Ch02.blockDiag, blockReflect, blockMatVecMul,
      akhc_matVecMul_smul_one, matVecMul_neg, akhc_matVecMul_zero_block,
      sub_eq_add_neg] <;>
    ring

theorem akhc_vecNormSq_neg {d : ℕ} (x : Vec d) :
    vecNormSq (-x) = vecNormSq x := by
  simp [vecNormSq, vecDot]

theorem akhc_vecNormSq_sub_comm {d : ℕ} (x y : Vec d) :
    vecNormSq (x - y) = vecNormSq (y - x) := by
  have h : x - y = -(y - x) := by
    ext i
    simp [sub_eq_add_neg]
  rw [h, akhc_vecNormSq_neg]

/-! ## The reflected/unreflected normalization diagonals (pure algebra) -/

/-- Diagonal weights for the *reflected* normalization: `b` on the flux
(`Sum.inr`) block, `c` on the gradient (`Sum.inl`) block. -/
noncomputable def akhcStarInvSqrtDiag {d : ℕ} (b c : ℝ) : BlockCoord d → ℝ
  | Sum.inl _ => Real.sqrt c
  | Sum.inr _ => (Real.sqrt b)⁻¹

/-- Diagonal weights for the inverse of `akhcStarInvSqrtDiag`. -/
noncomputable def akhcStarSqrtDiag {d : ℕ} (b c : ℝ) : BlockCoord d → ℝ
  | Sum.inl _ => (Real.sqrt c)⁻¹
  | Sum.inr _ => Real.sqrt b

/-- The block-coordinate swap `Sum.inl ↔ Sum.inr`, realizing `blockReflect` as
a reindexing. -/
def akhcBlockCoordSwapEquiv (d : ℕ) : BlockCoord d ≃ BlockCoord d where
  toFun
    | Sum.inl i => Sum.inr i
    | Sum.inr i => Sum.inl i
  invFun
    | Sum.inl i => Sum.inr i
    | Sum.inr i => Sum.inl i
  left_inv := by
    intro α
    cases α <;> rfl
  right_inv := by
    intro α
    cases α <;> rfl

theorem akhc_toFullBlockMat_blockReflect_eq_reindex_swap {d : ℕ} (A : BlockMat d) :
    toFullBlockMat (blockReflect A) =
      Matrix.reindex (akhcBlockCoordSwapEquiv d) (akhcBlockCoordSwapEquiv d) (toFullBlockMat A) := by
  ext α β
  cases α <;> cases β <;> rfl

theorem akhc_diagonal_starInvSqrtDiag_eq_reindex_fullBlockInvSqrtDiag
    {d : ℕ} (b c : ℝ) :
    Matrix.diagonal (akhcStarInvSqrtDiag (d := d) b c) =
      Matrix.reindex (akhcBlockCoordSwapEquiv d) (akhcBlockCoordSwapEquiv d)
        (Matrix.diagonal (Book.Ch04.scalarFullBlockInvSqrtDiag b c)) := by
  ext α β
  cases α <;> cases β <;>
    simp [Matrix.diagonal, akhcBlockCoordSwapEquiv, akhcStarInvSqrtDiag,
      Book.Ch04.scalarFullBlockInvSqrtDiag]

theorem akhc_reindex_swap_mul {d : ℕ} (M N : FullBlockMat d) :
      Matrix.reindex (akhcBlockCoordSwapEquiv d) (akhcBlockCoordSwapEquiv d) (M * N) =
        Matrix.reindex (akhcBlockCoordSwapEquiv d) (akhcBlockCoordSwapEquiv d) M *
          Matrix.reindex (akhcBlockCoordSwapEquiv d) (akhcBlockCoordSwapEquiv d) N := by
  exact map_mul (Matrix.reindexAlgEquiv ℝ ℝ (akhcBlockCoordSwapEquiv d)) M N

theorem akhc_reflectedNormalizedBlockFluctuationMatrix_eq_reindex_full
    {d : ℕ} (b c : ℝ) (A Abar : BlockMat d) :
    let Dstar : FullBlockMat d := Matrix.diagonal (akhcStarInvSqrtDiag b c)
    let D : FullBlockMat d := Matrix.diagonal (Book.Ch04.scalarFullBlockInvSqrtDiag b c)
    Dstar * (toFullBlockMat (blockReflect A) - toFullBlockMat (blockReflect Abar)) * Dstar =
      Matrix.reindex (akhcBlockCoordSwapEquiv d) (akhcBlockCoordSwapEquiv d)
        (D * (toFullBlockMat A - toFullBlockMat Abar) * D) := by
  dsimp only
  let e := akhcBlockCoordSwapEquiv d
  let Dstar : FullBlockMat d := Matrix.diagonal (akhcStarInvSqrtDiag b c)
  let D : FullBlockMat d := Matrix.diagonal (Book.Ch04.scalarFullBlockInvSqrtDiag b c)
  let M : FullBlockMat d := toFullBlockMat A - toFullBlockMat Abar
  have hD : Dstar = Matrix.reindex e e D := by
    simpa [Dstar, D, e] using
      akhc_diagonal_starInvSqrtDiag_eq_reindex_fullBlockInvSqrtDiag (d := d) b c
  have hM :
      toFullBlockMat (blockReflect A) - toFullBlockMat (blockReflect Abar) =
        Matrix.reindex e e M := by
    rw [akhc_toFullBlockMat_blockReflect_eq_reindex_swap A,
      akhc_toFullBlockMat_blockReflect_eq_reindex_swap Abar]
    ext α β
    rfl
  calc
    Dstar * (toFullBlockMat (blockReflect A) - toFullBlockMat (blockReflect Abar)) * Dstar =
        Matrix.reindex e e D * Matrix.reindex e e M * Matrix.reindex e e D := by
          rw [hD, hM]
    _ = Matrix.reindex e e (D * M) * Matrix.reindex e e D := by
          rw [← akhc_reindex_swap_mul]
    _ = Matrix.reindex e e ((D * M) * D) := by
          rw [← akhc_reindex_swap_mul]
    _ = Matrix.reindex e e (D * (toFullBlockMat A - toFullBlockMat Abar) * D) := by
          rfl

/-- The reflected form of the `Ahom(cu_m)`-normalized fluctuation, with the
local `Abar := annealedBlockMatrix nu L P (cubeSet (originCube d m))`. -/
noncomputable def akhcReflectedFullBlockNormalizedFluctuationAtScale
    {d : ℕ} [NeZero d] (nu : ℝ) (L : ℕ) (P : ProbabilityMeasure (ShellSeq d)) (m : ℤ)
    (R : TriadicCube d) (a : RegCoeffField d) : ℝ :=
  let b := sigmaBarScalar nu L P (cubeSet (originCube d m))
  let c := (sigmaBarStarInvScalar nu L P (cubeSet (originCube d m)))⁻¹
  let D : FullBlockMat d := Matrix.diagonal (akhcStarInvSqrtDiag b c)
  let A := coarseBlockMatrix (cubeSet R) a.toFun
  let Abar := annealedBlockMatrix nu L P (cubeSet (originCube d m))
  ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
      (D * (toFullBlockMat (blockReflect A) - toFullBlockMat (blockReflect Abar)) * D)‖ ^ 2

/-- **The reflected and unreflected `Ahom(cu_m)`-normalized fluctuations
agree.** RETYPE of CG's `reflectedNormalizedBlockFluctuationOperatorNormSqAtScale_eq_fullBlock`,
using the public norm-invariance-under-reindexing lemma
`Book.Ch02.norm_toEuclideanCLM_reindex_self`. -/
theorem akhc_reflectedFullBlockNormalizedFluctuationAtScale_eq_fullBlock
    {d : ℕ} [NeZero d] (nu : ℝ) (L : ℕ) (P : ProbabilityMeasure (ShellSeq d)) (m : ℤ)
    (R : TriadicCube d) (a : RegCoeffField d) :
    akhcReflectedFullBlockNormalizedFluctuationAtScale nu L P m R a =
      akhcFullBlockNormalizedFluctuationAtScale nu L P m R a := by
  let b := sigmaBarScalar nu L P (cubeSet (originCube d m))
  let c := (sigmaBarStarInvScalar nu L P (cubeSet (originCube d m)))⁻¹
  let D : FullBlockMat d := Matrix.diagonal (Book.Ch04.scalarFullBlockInvSqrtDiag b c)
  let A := coarseBlockMatrix (cubeSet R) a.toFun
  let Abar := annealedBlockMatrix nu L P (cubeSet (originCube d m))
  let e := akhcBlockCoordSwapEquiv d
  have hmat :
      Matrix.diagonal (akhcStarInvSqrtDiag (d := d) b c) *
          (toFullBlockMat (blockReflect A) - toFullBlockMat (blockReflect Abar)) *
          Matrix.diagonal (akhcStarInvSqrtDiag b c) =
        Matrix.reindex e e (D * (toFullBlockMat A - toFullBlockMat Abar) * D) := by
    simpa [D, e] using
      akhc_reflectedNormalizedBlockFluctuationMatrix_eq_reindex_full (d := d) b c A Abar
  have hnorm :
      ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
          (Matrix.reindex e e (D * (toFullBlockMat A - toFullBlockMat Abar) * D))‖ =
        ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
          (D * (toFullBlockMat A - toFullBlockMat Abar) * D)‖ :=
    Book.Ch02.norm_toEuclideanCLM_reindex_self e _
  unfold akhcReflectedFullBlockNormalizedFluctuationAtScale
  unfold akhcFullBlockNormalizedFluctuationAtScale akhcFullBlockNormalizedFluctuation
    akhcFullBlockInvSqrtDiag
  dsimp only
  calc
    ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
        (Matrix.diagonal (akhcStarInvSqrtDiag (d := d) b c) *
          (toFullBlockMat (blockReflect A) - toFullBlockMat (blockReflect Abar)) *
          Matrix.diagonal (akhcStarInvSqrtDiag b c))‖ ^ 2 =
        ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
          (Matrix.reindex e e (D * (toFullBlockMat A - toFullBlockMat Abar) * D))‖ ^ 2 := by
          rw [hmat]
    _ =
        ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
          (D * (toFullBlockMat A - toFullBlockMat Abar) * D)‖ ^ 2 := by
          rw [hnorm]

/-! ## The weighted quadratic-form identities (pure algebra, retyped from CG) -/

theorem akhc_starInvSqrtDiag_mul_starSqrtDiag {d : ℕ} {b c : ℝ}
    (hb : 0 < b) (hc : 0 < c) :
    Matrix.diagonal (akhcStarInvSqrtDiag (d := d) b c) *
      Matrix.diagonal (akhcStarSqrtDiag b c) = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  ext α β
  by_cases h : α = β
  · subst β
    cases α
    · simp [akhcStarInvSqrtDiag, akhcStarSqrtDiag, ne_of_gt (Real.sqrt_pos_of_pos hc)]
    · simp [akhcStarInvSqrtDiag, akhcStarSqrtDiag, ne_of_gt (Real.sqrt_pos_of_pos hb)]
  · simp [Matrix.diagonal, h]

theorem akhc_norm_sq_starInvSqrtDiag_mulVec_toFullBlockVec
    {d : ℕ} {b c : ℝ} (hb : 0 < b) (hc : 0 < c) (X : BlockVec d) :
    ‖(WithLp.toLp 2
        (Matrix.mulVec (Matrix.diagonal (akhcStarInvSqrtDiag (d := d) b c)) (toFullBlockVec X)) :
        PiLp 2 (fun _ : BlockCoord d => ℝ))‖ ^ 2 =
      c * vecNormSq X.1 + b⁻¹ * vecNormSq X.2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_sum_type]
  rcases X with ⟨x, y⟩
  simp [akhcStarInvSqrtDiag, toFullBlockVec, Matrix.mulVec, vecNormSq, vecDot,
    abs_of_nonneg (Real.sqrt_nonneg c), abs_of_nonneg (Real.sqrt_nonneg b)]
  simp_rw [mul_pow, sq_abs, inv_pow]
  rw [Real.sq_sqrt hc.le]
  have hs : (√b) ^ 2 = b := Real.sq_sqrt hb.le
  rw [hs]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  field_simp [ne_of_gt hb]

theorem akhc_norm_sq_starSqrtDiag_mulVec_toFullBlockVec
    {d : ℕ} {b c : ℝ} (hb : 0 < b) (hc : 0 < c) (X : BlockVec d) :
    ‖(WithLp.toLp 2
        (Matrix.mulVec (Matrix.diagonal (akhcStarSqrtDiag (d := d) b c)) (toFullBlockVec X)) :
        PiLp 2 (fun _ : BlockCoord d => ℝ))‖ ^ 2 =
      c⁻¹ * vecNormSq X.1 + b * vecNormSq X.2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_sum_type]
  rcases X with ⟨x, y⟩
  simp [akhcStarSqrtDiag, toFullBlockVec, Matrix.mulVec, vecNormSq, vecDot,
    abs_of_nonneg (Real.sqrt_nonneg c), abs_of_nonneg (Real.sqrt_nonneg b)]
  simp_rw [mul_pow, sq_abs, inv_pow]
  have hc_sq : (√c) ^ 2 = c := Real.sq_sqrt hc.le
  rw [hc_sq, Real.sq_sqrt hb.le]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  field_simp [ne_of_gt hc]

theorem akhc_normalized_mulVec_norm_sq_le
    {d : ℕ} [NeZero d] {b c : ℝ} (hb : 0 < b) (hc : 0 < c)
    (M : FullBlockMat d) (P : FullBlockVec d) :
    ‖(WithLp.toLp 2
        (Matrix.mulVec (Matrix.diagonal (akhcStarInvSqrtDiag (d := d) b c)) (Matrix.mulVec M P)) :
        PiLp 2 (fun _ : BlockCoord d => ℝ))‖ ^ 2 ≤
      ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
          (Matrix.diagonal (akhcStarInvSqrtDiag (d := d) b c) * M *
            Matrix.diagonal (akhcStarInvSqrtDiag b c))‖ ^ 2 *
        ‖(WithLp.toLp 2
          (Matrix.mulVec (Matrix.diagonal (akhcStarSqrtDiag (d := d) b c)) P) :
          PiLp 2 (fun _ : BlockCoord d => ℝ))‖ ^ 2 := by
  let D : FullBlockMat d := Matrix.diagonal (akhcStarInvSqrtDiag (d := d) b c)
  let E : FullBlockMat d := Matrix.diagonal (akhcStarSqrtDiag (d := d) b c)
  let x : PiLp 2 (fun _ : BlockCoord d => ℝ) := WithLp.toLp 2 (Matrix.mulVec E P)
  let y : PiLp 2 (fun _ : BlockCoord d => ℝ) := WithLp.toLp 2 (Matrix.mulVec D (Matrix.mulVec M P))
  have hDE : D * E = 1 := akhc_starInvSqrtDiag_mul_starSqrtDiag (d := d) hb hc
  have hmulVec : Matrix.mulVec D (Matrix.mulVec M P) =
      Matrix.mulVec (D * M * D) (Matrix.mulVec E P) := by
    symm
    calc
      Matrix.mulVec (D * M * D) (Matrix.mulVec E P) =
          Matrix.mulVec ((D * M * D) * E) P := by
            rw [Matrix.mulVec_mulVec]
      _ = Matrix.mulVec (D * M * (D * E)) P := by
            rw [Matrix.mul_assoc]
      _ = Matrix.mulVec (D * M * 1) P := by
            rw [hDE]
      _ = Matrix.mulVec (D * M) P := by
            rw [mul_one]
      _ = Matrix.mulVec D (Matrix.mulVec M P) := by
            rw [Matrix.mulVec_mulVec]
  have hy : (Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) (D * M * D)) x = y := by
    change WithLp.toLp 2 (Matrix.mulVec (D * M * D) (Matrix.mulVec E P)) =
      WithLp.toLp 2 (Matrix.mulVec D (Matrix.mulVec M P))
    rw [← hmulVec]
  have hnorm0 := (Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) (D * M * D)).le_opNorm x
  rw [hy] at hnorm0
  have hsq := pow_le_pow_left₀ (norm_nonneg y) hnorm0 2
  simpa [D, E, x, y, mul_pow] using hsq

theorem akhc_sigma_mul_inv_star_sq_eq_theta {b c σ θ : ℝ}
    (hb : 0 < b) (hc : 0 < c)
    (hσ : σ = Real.sqrt (b * c)) (hθ : θ = b * c⁻¹) :
    (σ * c⁻¹) ^ 2 = θ := by
  have hprod_pos : 0 < b * c := mul_pos hb hc
  rw [hσ, hθ]
  rw [mul_pow, Real.sq_sqrt hprod_pos.le]
  field_simp [ne_of_gt hc]

theorem akhc_barSigma_mul_sigma_inv_eq_sigma_mul_inv_star {b c σ : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hσ : σ = Real.sqrt (b * c)) :
    b * σ⁻¹ = σ * c⁻¹ := by
  have hprod_pos : 0 < b * c := mul_pos hb hc
  have hσpos : 0 < σ := by
    rw [hσ]
    exact Real.sqrt_pos_of_pos hprod_pos
  rw [hσ]
  have hsqrt_ne : Real.sqrt (b * c) ≠ 0 := ne_of_gt (Real.sqrt_pos_of_pos hprod_pos)
  field_simp [hsqrt_ne, ne_of_gt hc]
  rw [Real.sq_sqrt hprod_pos.le]

theorem akhc_norm_sq_starSqrtDiag_mulVec_specialBlockVec
    {d : ℕ} {b c σ : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hσ : σ = Real.sqrt (b * c)) (e : Vec d) :
    ‖(WithLp.toLp 2
        (Matrix.mulVec (Matrix.diagonal (akhcStarSqrtDiag (d := d) b c))
          (toFullBlockVec (-(σ ^ (1 / 2 : ℝ) • e), σ ^ (-(1 / 2 : ℝ)) • e))) :
        PiLp 2 (fun _ : BlockCoord d => ℝ))‖ ^ 2 =
      2 * (σ * c⁻¹) * vecNormSq e := by
  have hprod_pos : 0 < b * c := mul_pos hb hc
  have hσpos : 0 < σ := by
    rw [hσ]
    exact Real.sqrt_pos_of_pos hprod_pos
  have hpos_sq : (σ ^ (1 / 2 : ℝ)) ^ 2 = σ := by
    calc
      (σ ^ (1 / 2 : ℝ)) ^ 2 =
          (σ ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
        exact (Real.rpow_natCast (σ ^ (1 / 2 : ℝ)) 2).symm
      _ = σ ^ ((1 / 2 : ℝ) * (2 : ℝ)) :=
        (Real.rpow_mul hσpos.le (1 / 2 : ℝ) (2 : ℝ)).symm
      _ = σ ^ (1 : ℝ) := by
        norm_num
      _ = σ := by
        rw [Real.rpow_one]
  have hneg_sq : (σ ^ (-(1 / 2 : ℝ))) ^ 2 = σ⁻¹ := by
    calc
      (σ ^ (-(1 / 2 : ℝ))) ^ 2 =
          (σ ^ (-(1 / 2 : ℝ))) ^ (2 : ℝ) := by
        exact (Real.rpow_natCast (σ ^ (-(1 / 2 : ℝ))) 2).symm
      _ = σ ^ ((-(1 / 2 : ℝ)) * (2 : ℝ)) :=
        (Real.rpow_mul hσpos.le (-(1 / 2 : ℝ)) (2 : ℝ)).symm
      _ = σ ^ (-1 : ℝ) := by
        norm_num
      _ = (σ ^ (1 : ℝ))⁻¹ :=
        Real.rpow_neg hσpos.le 1
      _ = σ⁻¹ := by
        rw [Real.rpow_one]
  have hnorm :=
    akhc_norm_sq_starSqrtDiag_mulVec_toFullBlockVec (d := d) hb hc
      (-(σ ^ (1 / 2 : ℝ) • e), σ ^ (-(1 / 2 : ℝ)) • e)
  have hq_norm : vecNormSq (-(σ ^ (1 / 2 : ℝ) • e)) = σ * vecNormSq e := by
    have hneg :
        -(σ ^ (1 / 2 : ℝ) • e) = (-(σ ^ (1 / 2 : ℝ))) • e := by
      ext i
      simp
    rw [hneg, vecNormSq_smul]
    rw [show (-(σ ^ (1 / 2 : ℝ))) ^ 2 = (σ ^ (1 / 2 : ℝ)) ^ 2 by ring]
    rw [hpos_sq]
  have hp_norm : vecNormSq (σ ^ (-(1 / 2 : ℝ)) • e) = σ⁻¹ * vecNormSq e := by
    rw [vecNormSq_smul, hneg_sq]
  calc
    ‖(WithLp.toLp 2
        (Matrix.mulVec (Matrix.diagonal (akhcStarSqrtDiag (d := d) b c))
          (toFullBlockVec (-(σ ^ (1 / 2 : ℝ) • e), σ ^ (-(1 / 2 : ℝ)) • e))) :
        PiLp 2 (fun _ : BlockCoord d => ℝ))‖ ^ 2 =
        c⁻¹ * vecNormSq (-(σ ^ (1 / 2 : ℝ) • e)) +
          b * vecNormSq (σ ^ (-(1 / 2 : ℝ)) • e) := hnorm
    _ = c⁻¹ * (σ * vecNormSq e) + b * (σ⁻¹ * vecNormSq e) := by
          rw [hq_norm, hp_norm]
    _ = 2 * (σ * c⁻¹) * vecNormSq e := by
          have hbar := akhc_barSigma_mul_sigma_inv_eq_sigma_mul_inv_star hb hc hσ
          calc
            c⁻¹ * (σ * vecNormSq e) + b * (σ⁻¹ * vecNormSq e) =
                (c⁻¹ * σ + b * σ⁻¹) * vecNormSq e := by ring
            _ = (σ * c⁻¹ + σ * c⁻¹) * vecNormSq e := by
                  rw [hbar]
                  ring
            _ = 2 * (σ * c⁻¹) * vecNormSq e := by ring

theorem akhc_weighted_blockVec_norm_sq_eq_sigma_inv_star_mul_normalized_norm_sq
    {d : ℕ} {b c σ : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hσ : σ = Real.sqrt (b * c)) (X : BlockVec d) :
    σ * vecNormSq X.1 + σ⁻¹ * vecNormSq X.2 =
      (σ * c⁻¹) *
        ‖(WithLp.toLp 2
          (Matrix.mulVec (Matrix.diagonal (akhcStarInvSqrtDiag (d := d) b c)) (toFullBlockVec X)) :
          PiLp 2 (fun _ : BlockCoord d => ℝ))‖ ^ 2 := by
  have hprod_pos : 0 < b * c := mul_pos hb hc
  have hσpos : 0 < σ := by
    rw [hσ]
    exact Real.sqrt_pos_of_pos hprod_pos
  have hsigma_sq : σ ^ 2 = b * c := by
    rw [hσ]
    exact Real.sq_sqrt hprod_pos.le
  rw [akhc_norm_sq_starInvSqrtDiag_mulVec_toFullBlockVec (d := d) hb hc X]
  have hcoeff : σ * c⁻¹ * b⁻¹ = σ⁻¹ := by
    have hbne : b ≠ 0 := ne_of_gt hb
    have hcne : c ≠ 0 := ne_of_gt hc
    have hσne : σ ≠ 0 := ne_of_gt hσpos
    field_simp [hbne, hcne, hσne]
    nlinarith only [hsigma_sq]
  calc
    σ * vecNormSq X.1 + σ⁻¹ * vecNormSq X.2 =
        σ * vecNormSq X.1 + (σ * c⁻¹ * b⁻¹) * vecNormSq X.2 := by
          rw [hcoeff]
    _ = (σ * c⁻¹) * (c * vecNormSq X.1 + b⁻¹ * vecNormSq X.2) := by
          field_simp [ne_of_gt hc]

end

end SuperdiffusionCLT.AKHC61.Response
