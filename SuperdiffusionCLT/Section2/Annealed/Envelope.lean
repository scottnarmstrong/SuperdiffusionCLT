/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.Integrability

/-!
# The deterministic ellipticity envelope of the infrared cutoff

The paper's display `e.Enaught.mixing` introduces the deterministic block matrix

`bfE_m = [[ (nu + 2 C (1 ∨ m) nu⁻¹) Id, 0 ], [ 0, 2 C nu⁻¹ Id ]]`,

where `C` is the constant of the normalized `L²` size display
`e.km.Ltwo.size`. Lemma `l.bfAm.ellip` then states that the
normalized block matrix `bfE_m^{-1/2} bfA_m(U) bfE_m^{-1/2}` is `O_{Gamma_1}(1)`
and that its annealed counterpart is bounded by the identity.

## The constant

The formalized `e.km.Ltwo.size` is
`SuperdiffusionCLT.Section2.Cutoff.isBigOWith_gammaSigma_volumeAverage_sq_streamCutoff_max`,
whose scale is `2 * cutoffL2Const d * (1 ∨ m)`. Two adjustments are made, and
both only enlarge the envelope, so the displayed statement is unchanged:

* the first moment of a Γ₁ variable costs one factor
  `gammaMomentConst 1`, which the annealed half of the lemma needs; and
* the constant is truncated below at `1`, which is what makes `bfE_m` dominate
  the lower-right block `2 nu⁻¹ Id` of the pointwise majorant.

So `cutoffEnvelopeConst d = 1 ⊔ (gammaMomentConst 1 * (2 * cutoffL2Const d))`,
and the factor `2` printed in `2 C nu⁻¹` is the one produced by Young's
inequality `e.how.to.upbound.A`; it is genuinely needed.

## No matrix square roots

`bfE_m` is block diagonal with scalar blocks, so its inverse square root is the
explicit block-diagonal matrix `envelopeInvSqrt` with entries the reciprocal
square roots of the two scalars. The normalization
`bfE_m^{-1/2} M bfE_m^{-1/2}` is defined as the literal conjugation of `M` by
that matrix.

## Main results

* `envelopeBlockMat`: `bfE_m`.
* `envelopeInvSqrt`, `envelopeRescale`: the normalization.
* `blockVecDot_envelopeRescale`: the normalized quadratic form.
* `blockMatLoewnerLE_envelopeRescale_coarseBlockMatrix`: the first assertion of
  `l.bfAm.ellip` in its deterministic form, with the explicit random factor
  `envelopeRatio`.
* `isBigOWith_gammaSigma_envelopeRatio`: `envelopeRatio ≤ O_{Gamma_1}(1)`, which
  together with the previous item is `e.Enaught.vs.A.and.Ahom`.
* `blockMatLoewnerLE_envelopeRescale_annealedBlockMatrix`: the right half of the
  second assertion, `bfE_m^{-1/2} bfAhom_m(cu_n) bfE_m^{-1/2} ≤ I_{2d}`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Annealed

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## The envelope constant -/

/-- The constant `C` of `e.Enaught.mixing`: the constant of the normalized
`L²` size display `e.km.Ltwo.size`, enlarged by the first-moment factor of the
Γ₁ characterization and truncated below at `1`. -/
def cutoffEnvelopeConst (d : ℕ) : ℝ :=
  max 1 (IndependentSums.gammaMomentConst 1 * (2 * cutoffL2Const d))

theorem one_le_cutoffEnvelopeConst (d : ℕ) : 1 ≤ cutoffEnvelopeConst d :=
  le_max_left _ _

theorem cutoffEnvelopeConst_pos (d : ℕ) : 0 < cutoffEnvelopeConst d :=
  lt_of_lt_of_le zero_lt_one (one_le_cutoffEnvelopeConst d)

private theorem zero_le_cutoffL2Const (d : ℕ) : 0 ≤ cutoffL2Const d := by
  have hsq : 0 ≤ cutoffSquareConst d := by
    unfold cutoffSquareConst
    positivity
  have hmom : 0 < IndependentSums.gammaMomentConst 1 :=
    IndependentSums.gammaMomentConst_pos one_pos
  unfold cutoffL2Const
  positivity

private theorem one_le_gammaMomentConst_one :
    (1 : ℝ) ≤ IndependentSums.gammaMomentConst 1 := by
  have hexp : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  have hmax : (1 : ℝ) ≤ max 1 ((2 / (1 * Real.exp 1)) ^ (1 : ℝ)⁻¹) := le_max_left _ _
  have hfac : (1 : ℝ) ≤ 2 * Real.exp 1 := by linarith only [hexp]
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ (2 * Real.exp 1) * max 1 ((2 / (1 * Real.exp 1)) ^ (1 : ℝ)⁻¹) :=
        mul_le_mul hfac hmax zero_le_one (by linarith only [hfac])
    _ = IndependentSums.gammaMomentConst 1 := rfl

/-- The `L²`-size scale of `e.km.Ltwo.size` is below the envelope constant. -/
theorem two_mul_cutoffL2Const_le_cutoffEnvelopeConst (d : ℕ) :
    2 * cutoffL2Const d ≤ cutoffEnvelopeConst d := by
  have h0 : 0 ≤ 2 * cutoffL2Const d := by
    have := zero_le_cutoffL2Const d
    linarith only [this]
  have h1 : 2 * cutoffL2Const d ≤
      IndependentSums.gammaMomentConst 1 * (2 * cutoffL2Const d) :=
    le_mul_of_one_le_left h0 one_le_gammaMomentConst_one
  exact h1.trans (le_max_right _ _)

/-! ## The envelope block matrix `bfE_m` -/

/-- The upper-left scalar of `bfE_m`: `nu + 2 C nu⁻¹ (1 ∨ m)`. -/
def envelopeUpperScalar (d : ℕ) (nu : ℝ) (m : ℕ) : ℝ :=
  nu + 2 * cutoffEnvelopeConst d * nu⁻¹ * max 1 (m : ℝ)

/-- The lower-right scalar of `bfE_m`: `2 C nu⁻¹`. -/
def envelopeLowerScalar (d : ℕ) (nu : ℝ) : ℝ :=
  2 * cutoffEnvelopeConst d * nu⁻¹

theorem envelopeUpperScalar_pos {nu : ℝ} (hnu : 0 < nu) (d m : ℕ) :
    0 < envelopeUpperScalar d nu m := by
  have hC := cutoffEnvelopeConst_pos d
  have hmax : (1 : ℝ) ≤ max 1 (m : ℝ) := le_max_left _ _
  have hterm : 0 ≤ 2 * cutoffEnvelopeConst d * nu⁻¹ * max 1 (m : ℝ) := by positivity
  unfold envelopeUpperScalar
  linarith only [hnu, hterm]

theorem envelopeLowerScalar_pos {nu : ℝ} (hnu : 0 < nu) (d : ℕ) :
    0 < envelopeLowerScalar d nu := by
  have hC := cutoffEnvelopeConst_pos d
  unfold envelopeLowerScalar
  positivity

/-- **`e.Enaught.mixing`**: the deterministic envelope
`bfE_m = diag((nu + 2 C nu⁻¹ (1 ∨ m)) Id, 2 C nu⁻¹ Id)`. -/
def envelopeBlockMat (d : ℕ) (nu : ℝ) (m : ℕ) : BlockMat d :=
  Book.Ch02.blockDiag (envelopeUpperScalar d nu m • (1 : Mat d))
    (envelopeLowerScalar d nu • (1 : Mat d))

private theorem matVecMulOneE (x : Vec d) : matVecMul (1 : Mat d) x = x := by
  funext i
  simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]

private theorem vecDot_smul_oneE {c : ℝ} (x : Vec d) :
    vecDot x (matVecMul (c • (1 : Mat d)) x) = c * vecNormSq x := by
  rw [smul_matVecMul, matVecMulOneE, vecDot_smul_right]
  rfl

private theorem vecNormSq_smulE (c : ℝ) (x : Vec d) :
    vecNormSq (c • x) = c ^ 2 * vecNormSq x := by
  show vecDot (c • x) (c • x) = c ^ 2 * vecDot x x
  rw [vecDot_smul_left, vecDot_smul_right]
  ring

private theorem zero_matVecMulE (x : Vec d) : matVecMul (0 : Mat d) x = 0 := by
  funext i
  simp [matVecMul]

/-- The doubled quadratic form of a scalar block-diagonal matrix. -/
theorem blockVecDot_blockDiag_smul_one (a b : ℝ) (p q : Vec d) :
    blockVecDot (p, q)
        (blockMatVecMul (Book.Ch02.blockDiag (a • (1 : Mat d)) (b • (1 : Mat d)))
          (p, q)) = a * vecNormSq p + b * vecNormSq q := by
  rw [blockQuadratic_eq]
  show vecDot p (matVecMul (a • (1 : Mat d)) p) + vecDot p (matVecMul (0 : Mat d) q) +
      vecDot q (matVecMul (0 : Mat d) p) + vecDot q (matVecMul (b • (1 : Mat d)) q) = _
  rw [vecDot_smul_oneE, vecDot_smul_oneE, zero_matVecMulE, zero_matVecMulE,
    vecDot_zero_right, vecDot_zero_right]
  ring

/-! ## The inverse square root and the normalization -/

/-- The inverse square root of `bfE_m`: since `bfE_m` is block diagonal with
scalar blocks, it is the block-diagonal matrix of the reciprocal square roots
of the two scalars. -/
def envelopeInvSqrt (d : ℕ) (nu : ℝ) (m : ℕ) : BlockMat d :=
  Book.Ch02.blockDiag ((Real.sqrt (envelopeUpperScalar d nu m))⁻¹ • (1 : Mat d))
    ((Real.sqrt (envelopeLowerScalar d nu))⁻¹ • (1 : Mat d))

/-- **`bfE_m^{-1/2} M bfE_m^{-1/2}`**, the normalization of `l.bfAm.ellip`,
defined as the literal conjugation by `envelopeInvSqrt`. -/
def envelopeRescale (d : ℕ) (nu : ℝ) (m : ℕ) (M : BlockMat d) : BlockMat d :=
  Book.Ch02.blockMatMul (envelopeInvSqrt d nu m)
    (Book.Ch02.blockMatMul M (envelopeInvSqrt d nu m))

private theorem blockDiag_smul_one_conj (a b : ℝ) (M : BlockMat d) :
    Book.Ch02.blockMatMul (Book.Ch02.blockDiag (a • (1 : Mat d)) (b • (1 : Mat d)))
        (Book.Ch02.blockMatMul M
          (Book.Ch02.blockDiag (a • (1 : Mat d)) (b • (1 : Mat d)))) =
      BlockMat.mk ((a * a) • M.upperLeft) ((a * b) • M.upperRight)
        ((a * b) • M.lowerLeft) ((b * b) • M.lowerRight) := by
  refine blockMat_ext ?_ ?_ ?_ ?_ <;> show _ = _ <;>
    simp only [Book.Ch02.blockMatMul, Book.Ch02.blockDiag, Matrix.mul_zero,
      Matrix.zero_mul, smul_zero, add_zero, zero_add, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, smul_smul, mul_comm]

/-- The four blocks of the normalization are the blocks of `M` rescaled by the
reciprocal square roots of the two scalars of `bfE_m`. -/
theorem envelopeRescale_eq (d : ℕ) (nu : ℝ) (m : ℕ) (M : BlockMat d) :
    envelopeRescale d nu m M =
      BlockMat.mk
        (((Real.sqrt (envelopeUpperScalar d nu m))⁻¹ *
          (Real.sqrt (envelopeUpperScalar d nu m))⁻¹) • M.upperLeft)
        (((Real.sqrt (envelopeUpperScalar d nu m))⁻¹ *
          (Real.sqrt (envelopeLowerScalar d nu))⁻¹) • M.upperRight)
        (((Real.sqrt (envelopeUpperScalar d nu m))⁻¹ *
          (Real.sqrt (envelopeLowerScalar d nu))⁻¹) • M.lowerLeft)
        (((Real.sqrt (envelopeLowerScalar d nu))⁻¹ *
          (Real.sqrt (envelopeLowerScalar d nu))⁻¹) • M.lowerRight) :=
  blockDiag_smul_one_conj _ _ M

/-- The normalized doubled quadratic form is the quadratic form of `M` at the
rescaled block vector. -/
theorem blockVecDot_envelopeRescale (d : ℕ) (nu : ℝ) (m : ℕ) (M : BlockMat d)
    (p q : Vec d) :
    blockVecDot (p, q) (blockMatVecMul (envelopeRescale d nu m M) (p, q)) =
      blockVecDot ((Real.sqrt (envelopeUpperScalar d nu m))⁻¹ • p,
          (Real.sqrt (envelopeLowerScalar d nu))⁻¹ • q)
        (blockMatVecMul M ((Real.sqrt (envelopeUpperScalar d nu m))⁻¹ • p,
          (Real.sqrt (envelopeLowerScalar d nu))⁻¹ • q)) := by
  rw [envelopeRescale_eq, blockQuadratic_eq, blockQuadratic_eq]
  simp only [smul_matVecMul, matVecMul_smul, vecDot_smul_left, vecDot_smul_right]
  ring

/-- The normalization is monotone for the block Loewner order. -/
theorem blockMatLoewnerLE_envelopeRescale (d : ℕ) (nu : ℝ) (m : ℕ)
    {M N : BlockMat d} (h : BlockMatLoewnerLE M N) :
    BlockMatLoewnerLE (envelopeRescale d nu m M) (envelopeRescale d nu m N) := by
  rintro ⟨p, q⟩
  rw [blockVecDot_envelopeRescale, blockVecDot_envelopeRescale]
  exact h _

private theorem inv_sqrt_sq {e : ℝ} (he : 0 < e) :
    ((Real.sqrt e)⁻¹) ^ 2 = e⁻¹ := by
  rw [inv_pow, Real.sq_sqrt he.le]

private theorem blockVecDot_blockIdentity (p q : Vec d) :
    blockVecDot (p, q) (blockMatVecMul (Book.Ch02.blockIdentity d) (p, q)) =
      vecNormSq p + vecNormSq q := by
  rw [blockQuadratic_eq]
  show vecDot p (matVecMul (1 : Mat d) p) + vecDot p (matVecMul (0 : Mat d) q) +
      vecDot q (matVecMul (0 : Mat d) p) + vecDot q (matVecMul (1 : Mat d) q) = _
  rw [matVecMulOneE, matVecMulOneE, zero_matVecMulE, zero_matVecMulE,
    vecDot_zero_right, vecDot_zero_right]
  show vecDot p p + 0 + 0 + vecDot q q = vecDot p p + vecDot q q
  ring

/-! ## The first assertion of `l.bfAm.ellip` -/

/-- The random factor of `e.Enaught.vs.A.and.Ahom`: the normalized `L²` size of
`k_m` on the cube, measured against the deterministic scale of the envelope,
truncated below at `1`. -/
def envelopeRatio {d : ℕ} (m : ℕ) (Q : TriadicCube d)
    (omega : ShellSeq d) : ℝ :=
  max 1 (volumeAverage (openCubeSet Q)
      (fun x ↦ Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ^ 2) /
    (cutoffEnvelopeConst d * max 1 (m : ℝ)))

theorem one_le_envelopeRatio {d : ℕ} (m : ℕ) (Q : TriadicCube d)
    (omega : ShellSeq d) : 1 ≤ envelopeRatio m Q omega :=
  le_max_left _ _

private theorem envelopeScale_pos (d : ℕ) (m : ℕ) :
    0 < cutoffEnvelopeConst d * max 1 (m : ℝ) := by
  have hC := cutoffEnvelopeConst_pos d
  have hmax : (0 : ℝ) < max 1 (m : ℝ) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  exact mul_pos hC hmax

/-- **The first assertion of `l.bfAm.ellip`**, `e.Enaught.vs.A.and.Ahom`, in its deterministic
form: the normalized coarse block matrix of the cutoff is bounded by `envelopeRatio` times
the identity. -/
theorem blockMatLoewnerLE_envelopeRescale_coarseBlockMatrix [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (omega : ShellSeq d) (m : ℕ) (Q : TriadicCube d) :
    BlockMatLoewnerLE
      (envelopeRescale d nu m
        (coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega m).toFun))
      (envelopeRatio m Q omega • Book.Ch02.blockIdentity d) := by
  set Z : ℝ := volumeAverage (openCubeSet Q)
    (fun x ↦ Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ^ 2) with hZdef
  set S : ℝ := cutoffEnvelopeConst d * max 1 (m : ℝ) with hSdef
  have hSpos : 0 < S := envelopeScale_pos d m
  have hrho : 1 ≤ envelopeRatio m Q omega := one_le_envelopeRatio m Q omega
  have hZS : Z ≤ envelopeRatio m Q omega * S := by
    have hdiv : Z / S ≤ envelopeRatio m Q omega := le_max_right _ _
    exact (div_le_iff₀ hSpos).1 hdiv
  have hupPos := envelopeUpperScalar_pos hnu d m
  have hlowPos := envelopeLowerScalar_pos hnu d
  have hkey1 : (nu + 2 * nu⁻¹ * Z) * (envelopeUpperScalar d nu m)⁻¹ ≤
      envelopeRatio m Q omega := by
    have hupEq : envelopeUpperScalar d nu m = nu + 2 * nu⁻¹ * S := by
      rw [hSdef]
      unfold envelopeUpperScalar
      ring
    have hnuinv : (0 : ℝ) < 2 * nu⁻¹ := by positivity
    have hstep : nu + 2 * nu⁻¹ * Z ≤
        envelopeRatio m Q omega * envelopeUpperScalar d nu m := by
      rw [hupEq, mul_add]
      have h1 : 2 * nu⁻¹ * Z ≤ 2 * nu⁻¹ * (envelopeRatio m Q omega * S) :=
        mul_le_mul_of_nonneg_left hZS hnuinv.le
      have h2 : nu ≤ envelopeRatio m Q omega * nu :=
        le_mul_of_one_le_left hnu.le hrho
      have h3 : 2 * nu⁻¹ * (envelopeRatio m Q omega * S) =
          envelopeRatio m Q omega * (2 * nu⁻¹ * S) := by ring
      linarith only [h1, h2, h3]
    rw [← div_eq_mul_inv]
    exact (div_le_iff₀ hupPos).2 hstep
  have hkey2 : 2 * nu⁻¹ * (envelopeLowerScalar d nu)⁻¹ ≤
      envelopeRatio m Q omega := by
    have hCne : cutoffEnvelopeConst d ≠ 0 := (cutoffEnvelopeConst_pos d).ne'
    have hEq : 2 * nu⁻¹ * (envelopeLowerScalar d nu)⁻¹ =
        (cutoffEnvelopeConst d)⁻¹ := by
      unfold envelopeLowerScalar
      field_simp
    have hle : (cutoffEnvelopeConst d)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (one_le_cutoffEnvelopeConst d)
    rw [hEq]
    linarith only [hle, hrho]
  rintro ⟨p, q⟩
  rw [blockVecDot_envelopeRescale, blockMatVecMul_blockSMul, blockVecDot_smul_right,
    blockVecDot_blockIdentity]
  have hbound := blockVecDot_coarseBlockMatrix_coefficientCutoff_le hnu omega m Q
    ((Real.sqrt (envelopeUpperScalar d nu m))⁻¹ • p)
    ((Real.sqrt (envelopeLowerScalar d nu))⁻¹ • q)
  rw [vecNormSq_smulE, vecNormSq_smulE, inv_sqrt_sq hupPos, inv_sqrt_sq hlowPos,
    ← hZdef] at hbound
  have hp := vecNormSq_nonneg p
  have hq := vecNormSq_nonneg q
  have hA : (nu + 2 * nu⁻¹ * Z) * ((envelopeUpperScalar d nu m)⁻¹ * vecNormSq p) ≤
      envelopeRatio m Q omega * vecNormSq p := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hkey1 hp
  have hB : 2 * nu⁻¹ * ((envelopeLowerScalar d nu)⁻¹ * vecNormSq q) ≤
      envelopeRatio m Q omega * vecNormSq q := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hkey2 hq
  have hfinal : envelopeRatio m Q omega * (vecNormSq p + vecNormSq q) =
      envelopeRatio m Q omega * vecNormSq p +
        envelopeRatio m Q omega * vecNormSq q := by ring
  linarith only [hbound, hA, hB, hfinal]

/-! ## The Γ₁ tail of the random factor -/

variable {P : ProbabilityMeasure (ShellSeq d)}

/-- `e.km.Ltwo.size` read at the scale of the envelope constant. -/
theorem isBigOWith_gammaSigma_volumeAverage_sq_envelopeScale
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (m : ℕ) (Q : TriadicCube d) :
    IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 1)
      (fun omega ↦ volumeAverage (openCubeSet Q)
        (fun x ↦ Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ^ 2))
      (cutoffEnvelopeConst d * max 1 (m : ℝ)) := by
  refine (isBigOWith_gammaSigma_volumeAverage_sq_streamCutoff_max hPrefix hJ2 hJ3 hJ4 m
    (volume_openCubeSet_ne_zero Q) (volume_openCubeSet_lt_top Q).ne).mono_scale ?_
  have hmax : (0 : ℝ) ≤ max 1 (m : ℝ) := le_trans zero_le_one (le_max_left _ _)
  exact mul_le_mul_of_nonneg_right
    (two_mul_cutoffL2Const_le_cutoffEnvelopeConst d) hmax

/-- **`envelopeRatio ≤ O_{Gamma_1}(1)`.** With
`blockMatLoewnerLE_envelopeRescale_coarseBlockMatrix` this is the first
assertion `e.Enaught.vs.A.and.Ahom` of `l.bfAm.ellip`. -/
theorem isBigOWith_gammaSigma_envelopeRatio
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (m : ℕ) (Q : TriadicCube d) :
    IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 1)
      (fun omega ↦ envelopeRatio m Q omega) 1 := by
  have hZ := isBigOWith_gammaSigma_volumeAverage_sq_envelopeScale
    hPrefix hJ2 hJ3 hJ4 m Q
  intro t ht
  refine (measureReal_mono ?_).trans (hZ ht)
  intro omega hom
  have hlt : (1 : ℝ) * t < envelopeRatio m Q omega := hom
  rw [one_mul] at hlt
  rcases lt_max_iff.1 hlt with h1 | h2
  · exact absurd ht (not_le.2 h1)
  · have hmul := (lt_div_iff₀ (envelopeScale_pos d m)).1 h2
    show cutoffEnvelopeConst d * max 1 (m : ℝ) * t <
      volumeAverage (openCubeSet Q)
        (fun x ↦ Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ^ 2)
    linarith only [hmul]

/-! ## The annealed half of `l.bfAm.ellip` -/

private theorem integrable_vecDot_matVecMulE {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {M : Omega → Mat d}
    (hM : ∀ i j, Integrable (fun w ↦ M w i j) mu) (x y : Vec d) :
    Integrable (fun w ↦ vecDot x (matVecMul (M w) y)) mu :=
  integrable_finsetSum _ fun i _ ↦
    (integrable_finsetSum _ fun j _ ↦ (hM i j).mul_const (y j)).const_mul (x i)

private theorem integral_add4 {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} (f₁ f₂ f₃ f₄ : Omega → ℝ) (h1 : Integrable f₁ mu)
    (h2 : Integrable f₂ mu) (h3 : Integrable f₃ mu) (h4 : Integrable f₄ mu) :
    ∫ w, (f₁ w + f₂ w + f₃ w + f₄ w) ∂mu =
      ∫ w, f₁ w ∂mu + ∫ w, f₂ w ∂mu + ∫ w, f₃ w ∂mu + ∫ w, f₄ w ∂mu := by
  have e1 : ∫ w, (f₁ w + f₂ w) ∂mu = ∫ w, f₁ w ∂mu + ∫ w, f₂ w ∂mu :=
    integral_add h1 h2
  have e2 : ∫ w, (f₁ w + f₂ w + f₃ w) ∂mu =
      ∫ w, (f₁ w + f₂ w) ∂mu + ∫ w, f₃ w ∂mu := integral_add (h1.add h2) h3
  have e3 : ∫ w, (f₁ w + f₂ w + f₃ w + f₄ w) ∂mu =
      ∫ w, (f₁ w + f₂ w + f₃ w) ∂mu + ∫ w, f₄ w ∂mu :=
    integral_add ((h1.add h2).add h3) h4
  rw [e3, e2, e1]

/-- The expectation of the normalized `L²` size is below the deterministic
scale of the envelope. -/
theorem integral_volumeAverage_sq_le
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (m : ℕ) (Q : TriadicCube d) :
    ∫ omega, volumeAverage (openCubeSet Q)
        (fun x ↦ Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ^ 2)
      ∂P.toMeasure ≤ cutoffEnvelopeConst d * max 1 (m : ℝ) := by
  have hbig := isBigOWith_gammaSigma_volumeAverage_sq_streamCutoff hPrefix hJ2 hJ3 hJ4 m
    (volume_openCubeSet_ne_zero Q) (volume_openCubeSet_lt_top Q).ne
  have hA : 0 < cutoffL2Const d * ((m : ℝ) + 1) :=
    mul_pos (cutoffL2Const_pos hPrefix) (by positivity)
  have hnonneg : ∀ omega : ShellSeq d, 0 ≤ volumeAverage (openCubeSet Q)
      (fun x ↦ Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ^ 2) := by
    intro omega
    unfold volumeAverage
    exact mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
      (integral_nonneg fun x ↦ by positivity)
  have hmom := IndependentSums.hasGammaMomentGrowthWith_of_isBigOWith_gammaSigma
    (μ := P.toMeasure) one_pos hA hnonneg
    (measurable_volumeAverage_sq_streamCutoff m (openCubeSet Q)).aemeasurable hbig
  have h1 := (hmom (le_refl (1 : ℝ))).2
  have heq : (fun omega : ShellSeq d ↦ |volumeAverage (openCubeSet Q)
      (fun x ↦ Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ^ 2)| ^ (1 : ℝ)) =
      fun omega : ShellSeq d ↦ volumeAverage (openCubeSet Q)
        (fun x ↦ Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ^ 2) := by
    funext omega
    rw [abs_of_nonneg (hnonneg omega), Real.rpow_one]
  rw [heq] at h1
  have h2 : ∫ omega, volumeAverage (openCubeSet Q)
      (fun x ↦ Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ^ 2)
        ∂P.toMeasure ≤
      IndependentSums.gammaMomentConst 1 * (cutoffL2Const d * ((m : ℝ) + 1)) := by
    simpa only [Real.one_rpow, mul_one, Real.rpow_one] using h1
  have hmaxnn : (0 : ℝ) ≤ max 1 (m : ℝ) := le_trans zero_le_one (le_max_left _ _)
  have hm1 : (m : ℝ) + 1 ≤ 2 * max 1 (m : ℝ) := by
    have ha : (1 : ℝ) ≤ max 1 (m : ℝ) := le_max_left _ _
    have hb : (m : ℝ) ≤ max 1 (m : ℝ) := le_max_right _ _
    linarith only [ha, hb]
  have step1 : cutoffL2Const d * ((m : ℝ) + 1) ≤
      (2 * cutoffL2Const d) * max 1 (m : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hm1 (zero_le_cutoffL2Const d)
    linarith only [h]
  have step2 : IndependentSums.gammaMomentConst 1 * (cutoffL2Const d * ((m : ℝ) + 1)) ≤
      IndependentSums.gammaMomentConst 1 * ((2 * cutoffL2Const d) * max 1 (m : ℝ)) :=
    mul_le_mul_of_nonneg_left step1
      (IndependentSums.gammaMomentConst_pos one_pos).le
  have step3 : IndependentSums.gammaMomentConst 1 *
      ((2 * cutoffL2Const d) * max 1 (m : ℝ)) =
      (IndependentSums.gammaMomentConst 1 * (2 * cutoffL2Const d)) * max 1 (m : ℝ) := by
    ring
  have step4 : (IndependentSums.gammaMomentConst 1 * (2 * cutoffL2Const d)) *
      max 1 (m : ℝ) ≤ cutoffEnvelopeConst d * max 1 (m : ℝ) :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hmaxnn
  linarith only [h2, step2, step3, step4]

section AnnealedCube

variable [NeZero d] {nu : ℝ} (hnu : 0 < nu) (m : ℕ) (Q : TriadicCube d)
  (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
  (hJ4 : ShellLawJ4 d P)

include hnu hPrefix hJ2 hJ3 hJ4

/-- **`bfAhom_m(cu_Q)` is a genuine expectation**: its doubled quadratic form is
the expectation of the doubled quadratic form of `bfA_m(cu_Q)`. -/
theorem blockVecDot_annealedBlockMatrix (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (annealedBlockMatrix nu m P (cubeSet Q)) X) =
      ∫ omega, blockVecDot X (blockMatVecMul
        (coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega m).toFun) X)
        ∂P.toMeasure := by
  obtain ⟨p, q⟩ := X
  have hUL := integrable_coarseBlockMatrix_upperLeft_apply hnu m Q hPrefix hJ2 hJ3 hJ4
  have hUR := integrable_coarseBlockMatrix_upperRight_apply hnu m Q hPrefix hJ2 hJ3 hJ4
  have hLL := integrable_coarseBlockMatrix_lowerLeft_apply hnu m Q hPrefix hJ2 hJ3 hJ4
  have hLR := integrable_coarseBlockMatrix_lowerRight_apply hnu m Q hPrefix hJ2 hJ3 hJ4
  have hsplit : (fun omega : ShellSeq d ↦ blockVecDot (p, q) (blockMatVecMul
      (coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega m).toFun) (p, q))) =
      fun omega : ShellSeq d ↦
        vecDot p (matVecMul (coarseBlockMatrix (cubeSet Q)
            (coefficientCutoff nu omega m).toFun).upperLeft p) +
          vecDot p (matVecMul (coarseBlockMatrix (cubeSet Q)
            (coefficientCutoff nu omega m).toFun).upperRight q) +
          vecDot q (matVecMul (coarseBlockMatrix (cubeSet Q)
            (coefficientCutoff nu omega m).toFun).lowerLeft p) +
          vecDot q (matVecMul (coarseBlockMatrix (cubeSet Q)
            (coefficientCutoff nu omega m).toFun).lowerRight q) := by
    funext omega
    exact blockQuadratic_eq _ p q
  have eUL : vecDot p (matVecMul (annealedBlockMatrix nu m P (cubeSet Q)).upperLeft p) =
      ∫ omega, vecDot p (matVecMul (coarseBlockMatrix (cubeSet Q)
        (coefficientCutoff nu omega m).toFun).upperLeft p) ∂P.toMeasure :=
    vecDot_matVecMul_integralMat hUL p p
  have eUR : vecDot p (matVecMul (annealedBlockMatrix nu m P (cubeSet Q)).upperRight q) =
      ∫ omega, vecDot p (matVecMul (coarseBlockMatrix (cubeSet Q)
        (coefficientCutoff nu omega m).toFun).upperRight q) ∂P.toMeasure :=
    vecDot_matVecMul_integralMat hUR p q
  have eLL : vecDot q (matVecMul (annealedBlockMatrix nu m P (cubeSet Q)).lowerLeft p) =
      ∫ omega, vecDot q (matVecMul (coarseBlockMatrix (cubeSet Q)
        (coefficientCutoff nu omega m).toFun).lowerLeft p) ∂P.toMeasure :=
    vecDot_matVecMul_integralMat hLL q p
  have eLR : vecDot q (matVecMul (annealedBlockMatrix nu m P (cubeSet Q)).lowerRight q) =
      ∫ omega, vecDot q (matVecMul (coarseBlockMatrix (cubeSet Q)
        (coefficientCutoff nu omega m).toFun).lowerRight q) ∂P.toMeasure :=
    vecDot_matVecMul_integralMat hLR q q
  rw [blockQuadratic_eq, hsplit, integral_add4 _ _ _ _
    (integrable_vecDot_matVecMulE hUL p p) (integrable_vecDot_matVecMulE hUR p q)
    (integrable_vecDot_matVecMulE hLL q p) (integrable_vecDot_matVecMulE hLR q q),
    eUL, eUR, eLL, eLR]

/-- The annealed block matrix on a cube is bounded by `bfE_m`. -/
theorem blockVecDot_annealedBlockMatrix_le (p q : Vec d) :
    blockVecDot (p, q)
        (blockMatVecMul (annealedBlockMatrix nu m P (cubeSet Q)) (p, q)) ≤
      envelopeUpperScalar d nu m * vecNormSq p +
        envelopeLowerScalar d nu * vecNormSq q := by
  have hZint := integrable_volumeAverage_sq_streamCutoff hPrefix hJ2 hJ3 hJ4 m
    (U := openCubeSet Q) (volume_openCubeSet_ne_zero Q)
    (volume_openCubeSet_lt_top Q).ne
  have hUL := integrable_coarseBlockMatrix_upperLeft_apply hnu m Q hPrefix hJ2 hJ3 hJ4
  have hUR := integrable_coarseBlockMatrix_upperRight_apply hnu m Q hPrefix hJ2 hJ3 hJ4
  have hLL := integrable_coarseBlockMatrix_lowerLeft_apply hnu m Q hPrefix hJ2 hJ3 hJ4
  have hLR := integrable_coarseBlockMatrix_lowerRight_apply hnu m Q hPrefix hJ2 hJ3 hJ4
  have hLint : Integrable (fun omega : ShellSeq d ↦ blockVecDot (p, q)
      (blockMatVecMul (coarseBlockMatrix (cubeSet Q)
        (coefficientCutoff nu omega m).toFun) (p, q))) P.toMeasure := by
    have hsplit : (fun omega : ShellSeq d ↦ blockVecDot (p, q) (blockMatVecMul
        (coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega m).toFun) (p, q))) =
        fun omega : ShellSeq d ↦
          vecDot p (matVecMul (coarseBlockMatrix (cubeSet Q)
              (coefficientCutoff nu omega m).toFun).upperLeft p) +
            vecDot p (matVecMul (coarseBlockMatrix (cubeSet Q)
              (coefficientCutoff nu omega m).toFun).upperRight q) +
            vecDot q (matVecMul (coarseBlockMatrix (cubeSet Q)
              (coefficientCutoff nu omega m).toFun).lowerLeft p) +
            vecDot q (matVecMul (coarseBlockMatrix (cubeSet Q)
              (coefficientCutoff nu omega m).toFun).lowerRight q) := by
      funext omega
      exact blockQuadratic_eq _ p q
    rw [hsplit]
    exact (((integrable_vecDot_matVecMulE hUL p p).add
      (integrable_vecDot_matVecMulE hUR p q)).add
        (integrable_vecDot_matVecMulE hLL q p)).add
          (integrable_vecDot_matVecMulE hLR q q)
  have hRint : Integrable (fun omega : ShellSeq d ↦
      (2 * nu⁻¹ * vecNormSq p) * volumeAverage (openCubeSet Q)
          (fun x ↦ Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ^ 2) +
        (nu * vecNormSq p + 2 * nu⁻¹ * vecNormSq q)) P.toMeasure :=
    (hZint.const_mul _).add (integrable_const _)
  have hmono : ∫ omega, blockVecDot (p, q) (blockMatVecMul
      (coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega m).toFun) (p, q))
        ∂P.toMeasure ≤
      ∫ omega, ((2 * nu⁻¹ * vecNormSq p) * volumeAverage (openCubeSet Q)
          (fun x ↦ Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ^ 2) +
        (nu * vecNormSq p + 2 * nu⁻¹ * vecNormSq q)) ∂P.toMeasure := by
    refine integral_mono hLint hRint fun omega ↦ ?_
    have h := blockVecDot_coarseBlockMatrix_coefficientCutoff_le hnu omega m Q p q
    linarith only [h]
  have hval : ∫ omega, ((2 * nu⁻¹ * vecNormSq p) * volumeAverage (openCubeSet Q)
        (fun x ↦ Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ^ 2) +
      (nu * vecNormSq p + 2 * nu⁻¹ * vecNormSq q)) ∂P.toMeasure =
      (2 * nu⁻¹ * vecNormSq p) * (∫ omega, volumeAverage (openCubeSet Q)
        (fun x ↦ Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ^ 2)
          ∂P.toMeasure) + (nu * vecNormSq p + 2 * nu⁻¹ * vecNormSq q) := by
    rw [integral_add (hZint.const_mul _) (integrable_const _), integral_const_mul,
      integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hEZ := integral_volumeAverage_sq_le hPrefix hJ2 hJ3 hJ4 m Q
  have hp := vecNormSq_nonneg p
  have hq := vecNormSq_nonneg q
  have hcoef : (0 : ℝ) ≤ 2 * nu⁻¹ * vecNormSq p := by positivity
  have hstep := mul_le_mul_of_nonneg_left hEZ hcoef
  have hup : envelopeUpperScalar d nu m * vecNormSq p =
      (2 * nu⁻¹ * vecNormSq p) * (cutoffEnvelopeConst d * max 1 (m : ℝ)) +
        nu * vecNormSq p := by
    unfold envelopeUpperScalar
    ring
  have hlow : 2 * nu⁻¹ * vecNormSq q ≤ envelopeLowerScalar d nu * vecNormSq q := by
    have hC := one_le_cutoffEnvelopeConst d
    have hnuinv : (0 : ℝ) < nu⁻¹ := by positivity
    have hfac : 2 * nu⁻¹ ≤ envelopeLowerScalar d nu := by
      unfold envelopeLowerScalar
      have h := mul_le_mul_of_nonneg_right hC hnuinv.le
      linarith only [h]
    exact mul_le_mul_of_nonneg_right hfac hq
  rw [blockVecDot_annealedBlockMatrix hnu m Q hPrefix hJ2 hJ3 hJ4]
  rw [hval] at hmono
  linarith only [hmono, hstep, hup, hlow]

/-- **The right half of the second assertion of `l.bfAm.ellip`**:
`bfE_m^{-1/2} bfAhom_m(cu_Q) bfE_m^{-1/2} ≤ I_{2d}`. -/
theorem blockMatLoewnerLE_envelopeRescale_annealedBlockMatrix :
    BlockMatLoewnerLE
      (envelopeRescale d nu m (annealedBlockMatrix nu m P (cubeSet Q)))
      (Book.Ch02.blockIdentity d) := by
  have hupPos := envelopeUpperScalar_pos hnu d m
  have hlowPos := envelopeLowerScalar_pos hnu d
  rintro ⟨p, q⟩
  rw [blockVecDot_envelopeRescale, blockVecDot_blockIdentity]
  have h := blockVecDot_annealedBlockMatrix_le hnu m Q hPrefix hJ2 hJ3 hJ4
    ((Real.sqrt (envelopeUpperScalar d nu m))⁻¹ • p)
    ((Real.sqrt (envelopeLowerScalar d nu))⁻¹ • q)
  rw [vecNormSq_smulE, vecNormSq_smulE, inv_sqrt_sq hupPos, inv_sqrt_sq hlowPos] at h
  have hu : envelopeUpperScalar d nu m *
      ((envelopeUpperScalar d nu m)⁻¹ * vecNormSq p) = vecNormSq p := by
    rw [← mul_assoc, mul_inv_cancel₀ hupPos.ne', one_mul]
  have hl : envelopeLowerScalar d nu *
      ((envelopeLowerScalar d nu)⁻¹ * vecNormSq q) = vecNormSq q := by
    rw [← mul_assoc, mul_inv_cancel₀ hlowPos.ne', one_mul]
  rw [hu, hl] at h
  linarith only [h]

end AnnealedCube

end

end SuperdiffusionCLT.Section2.Annealed
