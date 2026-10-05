/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.WeakNorms.MaximizerBridgeC

/-!
# Package B3, deterministic-reference variant: `Λ`, `λ⁻¹` bounds linear in `1 + M⁺`

`MaximizerBridgeC.lean` bounds `Λ_{s',1}(cu_n; a)` and `λ_{s',1}(cu_n; a)⁻¹` by
`C(s',ρ)·|block of bfA(cu_h; a)|·(1 + M⁺)²`, with the event quantity `M⁺` normalized by the
**random** `bfA(cu_h; a)`. This file proves the same two bounds with

* an **arbitrary positive-definite reference** `E : BlockMat d` in place of `bfA(cu_h; a)`. The
  intended instance is the deterministic annealed `bfAhom(cu_h)`, the source's normalization
  (`e.event.moreproto`), for which package C3 (`AKHC61/Tails/MaximalMomentC.lean`,
  `akhcMM_Mplus_secondMoment_le`) supplies the second moment of `M⁺`;
* the factor `(1 + M⁺)` to the **first** power. The square in `MaximizerBridgeC.lean` is a
  deliberate weakening (`akhcWeakC2_bound_sq_le` uses `1 + M ≤ (1 + M)²`); the geometric-series
  argument gives the linear bound directly, by feeding `akhcWeakC2_tsum_sq_le` the scale
  `σ·(1 + M)` and the excess `0`.

The argument needs nothing about `E` beyond positive definiteness of its full `2d × 2d` matrix:
that makes the Loewner excess attained (`akhcWeakC_loewnerLE_of_excess_le`) and makes the two
diagonal blocks of `E` positive semidefinite (principal submatrices).

## Main results

* `akhcWeakD_blockMatLoewnerLE_of_mem`: for every cube `R` of scale `≤ n` centred in `cu_n`,
  `bfA(R; a) ≤ (1 + 3^{ρ(n - R.scale)}·M⁺)·E` in the Loewner order.
* `akhcWeakD_LambdaSqCoeffField_le`: `Λ_{s',1}(cu_n; a) ≤ C(s',ρ)·|E_{UL}|·(1 + M⁺)`.
* `akhcWeakD_lambdaSqCoeffField_inv_le`: `λ_{s',1}(cu_n; a)⁻¹ ≤ C(s',ρ)·|E_{LR}|·(1 + M⁺)`.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.WeakNorms

noncomputable section

open Homogenization
open Homogenization.Book

/-! ## Diagonal blocks of a positive-definite reference -/

/-- The upper-left block of a block matrix with positive-definite full matrix is positive
semidefinite (a principal submatrix). -/
theorem akhcWeakD_upperLeft_posSemidef {d : ℕ} {E : BlockMat d}
    (hE : (toFullBlockMat E).PosDef) : E.upperLeft.PosSemidef := by
  have h := hE.posSemidef.submatrix (Sum.inl : Fin d → BlockCoord d)
  have heq : (toFullBlockMat E).submatrix Sum.inl Sum.inl = E.upperLeft := by
    ext i j
    rfl
  rwa [heq] at h

/-- The lower-right block of a block matrix with positive-definite full matrix is positive
semidefinite (a principal submatrix). -/
theorem akhcWeakD_lowerRight_posSemidef {d : ℕ} {E : BlockMat d}
    (hE : (toFullBlockMat E).PosDef) : E.lowerRight.PosSemidef := by
  have h := hE.posSemidef.submatrix (Sum.inr : Fin d → BlockCoord d)
  have heq : (toFullBlockMat E).submatrix Sum.inr Sum.inr = E.lowerRight := by
    ext i j
    rfl
  rwa [heq] at h

/-! ## Geometry and block facts (local copies of `MaximizerBridgeC.lean`'s private helpers) -/

private theorem akhcWeakD_scale_eq_of_mem_descendantsAtScale {d : ℕ} {Q R : TriadicCube d}
    {j : ℕ} (hR : R ∈ descendantsAtScale Q (Q.scale - (j : ℤ))) :
    R.scale = Q.scale - (j : ℤ) := by
  have hk : Q.scale - (j : ℤ) ≤ Q.scale := by
    have hj0 : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg j
    linarith only [hj0]
  have h := scale_eq_sub_of_mem_descendantsAtScale hk hR
  rw [h]
  congr 1
  have : Q.scale - (Q.scale - (j : ℤ)) = (j : ℤ) := by ring
  rw [this, Int.toNat_natCast]

private theorem akhcWeakD_cubeCenter_mem_of_mem_descendantsAtScale {d : ℕ}
    {Q R : TriadicCube d} {k : ℤ} (hk : k ≤ Q.scale) (hR : R ∈ descendantsAtScale Q k) :
    cubeCenter R ∈ cubeSet Q := by
  have hopen : cubeCenter R ∈ openCubeSet R := by
    rw [← ball_cubeCenter_eq_openCubeSet]
    exact Metric.mem_ball_self (cubeRadius_pos R)
  exact cubeSet_subset_of_mem_descendantsAtScale hk hR (openCubeSet_subset_cubeSet R hopen)

private theorem akhcWeakD_posSemidef_upperLeft_sample {d : ℕ} [NeZero d] {a : RegCoeffField d}
    (ha : Ch04.AELocallyUniformlyEllipticField a) (Q : TriadicCube d) :
    (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft.PosSemidef := by
  rw [Book.Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
    ha Q]
  simpa using Book.Ch02.bCoarse_posSemidef (Book.Ch02.cubeDomain Q) _

private theorem akhcWeakD_posSemidef_lowerRight_sample {d : ℕ} [NeZero d] {a : RegCoeffField d}
    (ha : Ch04.AELocallyUniformlyEllipticField a) (Q : TriadicCube d) :
    (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight.PosSemidef := by
  rw [Book.Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
    ha Q]
  exact (Book.Ch02.sigmaStarInvCoarse_posDef (Book.Ch02.cubeDomain Q) _).posSemidef

private theorem akhcWeakD_matrixOperatorNorm_smul_of_nonneg {d : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (A : Mat d) :
    Book.Ch02.matrixOperatorNorm (c • A) = c * Book.Ch02.matrixOperatorNorm A := by
  have h : ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (c • A)‖ =
      c * ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A‖ := by
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
  simpa [Book.Ch02.matrixOperatorNorm] using h

/-- Nonnegativity of `M⁺` for an arbitrary reference. -/
theorem akhcWeakD_eventMoreprotoPlus_nonneg {d : ℕ} (n : ℤ) (ρ : ℝ) (E : BlockMat d)
    (a : CoeffField d) : 0 ≤ akhcWeakC_eventMoreprotoPlus n ρ E a := by
  unfold akhcWeakC_eventMoreprotoPlus
  refine Real.sSup_nonneg ?_
  rintro _ ⟨Q, -, -, rfl⟩
  exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (SuperdiffusionCLT.AKHC61.Tails.akhcTailEll_excess_nonneg _ _)

/-! ## The one-sided Loewner sandwich at one cube, arbitrary reference -/

/-- **Per-cube Loewner bound.** For a positive-definite reference `E` and a sample `a` whose
`M⁺`-index set is bounded above, every cube `R` of scale `≤ n` centred in `cu_n` satisfies
`bfA(R; a) ≤ (1 + 3^{ρ(n - R.scale)}·M⁺_{n,ρ}(E; a))·E`. -/
theorem akhcWeakD_blockMatLoewnerLE_of_mem {d : ℕ} [NeZero d] {E : BlockMat d}
    (hE : (toFullBlockMat E).PosDef) {a : CoeffField d} {n : ℤ} {ρ : ℝ}
    (hBdd :
      BddAbove
        {M : ℝ |
          ∃ Q : TriadicCube d,
            Q.scale ≤ n ∧
              cubeCenter Q ∈ cubeSet (originCube d n) ∧
              M =
                Real.rpow (3 : ℝ) (-ρ * ((n : ℝ) - (Q.scale : ℝ))) *
                  SuperdiffusionCLT.AKHC61.Tails.akhcTailEll_excess E
                    (coarseBlockMatrix (cubeSet Q) a)})
    {R : TriadicCube d} (hRscale : R.scale ≤ n)
    (hRcenter : cubeCenter R ∈ cubeSet (originCube d n)) :
    BlockMatLoewnerLE (coarseBlockMatrix (cubeSet R) a)
      ((1 + Real.rpow (3 : ℝ) (ρ * ((n : ℝ) - (R.scale : ℝ))) *
            akhcWeakC_eventMoreprotoPlus n ρ E a) • E) := by
  have hle :
      Real.rpow (3 : ℝ) (-ρ * ((n : ℝ) - (R.scale : ℝ))) *
          SuperdiffusionCLT.AKHC61.Tails.akhcTailEll_excess E
            (coarseBlockMatrix (cubeSet R) a) ≤
        akhcWeakC_eventMoreprotoPlus n ρ E a := by
    unfold akhcWeakC_eventMoreprotoPlus
    exact le_csSup hBdd ⟨R, hRscale, hRcenter, rfl⟩
  have hrpow_inv :
      Real.rpow (3 : ℝ) (ρ * ((n : ℝ) - (R.scale : ℝ))) *
          Real.rpow (3 : ℝ) (-ρ * ((n : ℝ) - (R.scale : ℝ))) = 1 := by
    rw [Real.rpow_eq_pow, Real.rpow_eq_pow, ← Real.rpow_add (by norm_num : (0:ℝ) < 3)]
    norm_num
  have hpow_nonneg : 0 ≤ Real.rpow (3 : ℝ) (ρ * ((n : ℝ) - (R.scale : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hmul := mul_le_mul_of_nonneg_left hle hpow_nonneg
  rw [← mul_assoc, hrpow_inv, one_mul] at hmul
  exact akhcWeakC_loewnerLE_of_excess_le hE hmul

/-! ## The per-scale block-norm bounds -/

private theorem akhcWeakD_matrixNorm_upperLeft_le {d : ℕ} [NeZero d] {E : BlockMat d}
    (hE : (toFullBlockMat E).PosDef) {a : RegCoeffField d}
    (ha : Ch04.AELocallyUniformlyEllipticField a) {n : ℤ} {ρ : ℝ}
    (hBdd :
      BddAbove
        {M : ℝ |
          ∃ Q : TriadicCube d,
            Q.scale ≤ n ∧
              cubeCenter Q ∈ cubeSet (originCube d n) ∧
              M =
                Real.rpow (3 : ℝ) (-ρ * ((n : ℝ) - (Q.scale : ℝ))) *
                  SuperdiffusionCLT.AKHC61.Tails.akhcTailEll_excess E
                    (coarseBlockMatrix (cubeSet Q) a.toFun)})
    {R : TriadicCube d} (hRscale : R.scale ≤ n)
    (hRcenter : cubeCenter R ∈ cubeSet (originCube d n)) :
    Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) a.toFun).upperLeft ≤
      (1 + Real.rpow (3 : ℝ) (ρ * ((n : ℝ) - (R.scale : ℝ))) *
            akhcWeakC_eventMoreprotoPlus n ρ E a.toFun) *
        Ch02.matrixNorm E.upperLeft := by
  have hLoewner := akhcWeakD_blockMatLoewnerLE_of_mem hE hBdd hRscale hRcenter
  set c : ℝ := Real.rpow (3 : ℝ) (ρ * ((n : ℝ) - (R.scale : ℝ))) *
    akhcWeakC_eventMoreprotoPlus n ρ E a.toFun with hcdef
  have hcnn : 0 ≤ c :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (akhcWeakD_eventMoreprotoPlus_nonneg _ _ _ _)
  have h1cnn : 0 ≤ 1 + c := by linarith only [hcnn]
  have hUL := Book.Ch04.matLoewnerLE_upperLeft_of_blockMatLoewnerLE hLoewner
  rw [Homogenization.blockSMul_upperLeft] at hUL
  have hPSD_scaled := (akhcWeakD_upperLeft_posSemidef hE).smul h1cnn
  have hnorm := Book.Ch02.matrixOperatorNorm_le_of_matLoewnerLE_of_posSemidef
    (akhcWeakD_posSemidef_upperLeft_sample ha R) hPSD_scaled hUL
  rw [Book.Ch02.matrixNorm_eq_matrixOperatorNorm, Book.Ch02.matrixNorm_eq_matrixOperatorNorm]
  rwa [akhcWeakD_matrixOperatorNorm_smul_of_nonneg h1cnn] at hnorm

private theorem akhcWeakD_matrixNorm_lowerRight_le {d : ℕ} [NeZero d] {E : BlockMat d}
    (hE : (toFullBlockMat E).PosDef) {a : RegCoeffField d}
    (ha : Ch04.AELocallyUniformlyEllipticField a) {n : ℤ} {ρ : ℝ}
    (hBdd :
      BddAbove
        {M : ℝ |
          ∃ Q : TriadicCube d,
            Q.scale ≤ n ∧
              cubeCenter Q ∈ cubeSet (originCube d n) ∧
              M =
                Real.rpow (3 : ℝ) (-ρ * ((n : ℝ) - (Q.scale : ℝ))) *
                  SuperdiffusionCLT.AKHC61.Tails.akhcTailEll_excess E
                    (coarseBlockMatrix (cubeSet Q) a.toFun)})
    {R : TriadicCube d} (hRscale : R.scale ≤ n)
    (hRcenter : cubeCenter R ∈ cubeSet (originCube d n)) :
    Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) a.toFun).lowerRight ≤
      (1 + Real.rpow (3 : ℝ) (ρ * ((n : ℝ) - (R.scale : ℝ))) *
            akhcWeakC_eventMoreprotoPlus n ρ E a.toFun) *
        Ch02.matrixNorm E.lowerRight := by
  have hLoewner := akhcWeakD_blockMatLoewnerLE_of_mem hE hBdd hRscale hRcenter
  set c : ℝ := Real.rpow (3 : ℝ) (ρ * ((n : ℝ) - (R.scale : ℝ))) *
    akhcWeakC_eventMoreprotoPlus n ρ E a.toFun with hcdef
  have hcnn : 0 ≤ c :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (akhcWeakD_eventMoreprotoPlus_nonneg _ _ _ _)
  have h1cnn : 0 ≤ 1 + c := by linarith only [hcnn]
  have hLR := Book.Ch04.matLoewnerLE_lowerRight_of_blockMatLoewnerLE hLoewner
  rw [Homogenization.blockSMul_lowerRight] at hLR
  have hPSD_scaled := (akhcWeakD_lowerRight_posSemidef hE).smul h1cnn
  have hnorm := Book.Ch02.matrixOperatorNorm_le_of_matLoewnerLE_of_posSemidef
    (akhcWeakD_posSemidef_lowerRight_sample ha R) hPSD_scaled hLR
  rw [Book.Ch02.matrixNorm_eq_matrixOperatorNorm, Book.Ch02.matrixNorm_eq_matrixOperatorNorm]
  rwa [akhcWeakD_matrixOperatorNorm_smul_of_nonneg h1cnn] at hnorm

/-- The elementary factorization `(1 + 3^{ρj}M)σ ≤ σ(1+M)(1+3^{ρj})`, stated once for both
blocks. -/
private theorem akhcWeakD_factor_le {σ M w : ℝ} (hσ : 0 ≤ σ) (hM : 0 ≤ M) (hw : 0 ≤ w) :
    (1 + w * M) * σ ≤ σ * (1 + M) * (1 + w) := by
  have h1 : 0 ≤ σ * w := mul_nonneg hσ hw
  have h2 : 0 ≤ σ * M := mul_nonneg hσ hM
  have h3 : 0 ≤ σ * M * w := mul_nonneg h2 hw
  have heq : σ * (1 + M) * (1 + w) - (1 + w * M) * σ = σ * w + σ * M := by ring
  linarith only [heq, h1, h2, h3]

/-! ## Main results -/

/-- **`Λ` bound, linear in `1 + M⁺`, arbitrary positive-definite reference.** For `s' > 0` with
`ρ/2 < s'`, `Λ_{s',1}(cu_n; a) ≤ C(s',ρ)·|E_{UL}|·(1 + M⁺_{n,ρ}(E; a))`. -/
theorem akhcWeakD_LambdaSqCoeffField_le {d : ℕ} [NeZero d] {E : BlockMat d}
    (hE : (toFullBlockMat E).PosDef) {a : RegCoeffField d}
    (ha : Ch04.AELocallyUniformlyEllipticField a) {n : ℤ} {ρ s' : ℝ} (hs' : 0 < s')
    (hgap : ρ / 2 < s')
    (hBdd :
      BddAbove
        {M : ℝ |
          ∃ Q : TriadicCube d,
            Q.scale ≤ n ∧
              cubeCenter Q ∈ cubeSet (originCube d n) ∧
              M =
                Real.rpow (3 : ℝ) (-ρ * ((n : ℝ) - (Q.scale : ℝ))) *
                  SuperdiffusionCLT.AKHC61.Tails.akhcTailEll_excess E
                    (coarseBlockMatrix (cubeSet Q) a.toFun)}) :
    Ch04.LambdaSqCoeffField (originCube d n) s' (.finite 1) a ≤
      akhcWeakC2_maximizerConst s' ρ * Ch02.matrixNorm E.upperLeft *
        (1 + akhcWeakC_eventMoreprotoPlus n ρ E a.toFun) := by
  rw [Book.Ch04.RestrictionLawCarrier.LambdaSqCoeffField_finite_one_eq_tsum_sq (originCube d n) a s']
  set M : ℝ := akhcWeakC_eventMoreprotoPlus n ρ E a.toFun with hMdef
  set σ : ℝ := Ch02.matrixNorm E.upperLeft with hσdef
  have hMnn : 0 ≤ M := akhcWeakD_eventMoreprotoPlus_nonneg _ _ _ _
  have hσnn : 0 ≤ σ := Book.Ch02.matrixNorm_nonneg _
  have h1M : 0 ≤ 1 + M := by linarith only [hMnn]
  refine le_trans (akhcWeakC2_tsum_sq_le (σ := σ * (1 + M)) (M := 0) hs' hgap
    (mul_nonneg hσnn h1M) le_rfl
    (fun j => by
      rw [Book.Ch04.RestrictionLawCarrier.maxDescendantBMatrixNormCoeffFieldAtScale_eq_finsetSupReal_ae
        ha (originCube d n) ((originCube d n).scale - (j : ℤ))]
      exact Book.Ch02.finsetSupReal_nonneg _ _ fun R _ => Book.Ch02.matrixNorm_nonneg _) ?_)
    (le_of_eq (by ring))
  intro j
  rw [Book.Ch04.RestrictionLawCarrier.maxDescendantBMatrixNormCoeffFieldAtScale_eq_finsetSupReal_ae
    ha (originCube d n) ((originCube d n).scale - (j : ℤ))]
  have hjle : (originCube d n).scale - (j : ℤ) ≤ (originCube d n).scale := by
    have hj0 : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg j
    linarith only [hj0]
  refine Book.Ch02.finsetSupReal_le _ (descendantsAtScale_nonempty (originCube d n) hjle) ?_
  intro R hR
  have hRscale' : R.scale = (originCube d n).scale - (j : ℤ) :=
    akhcWeakD_scale_eq_of_mem_descendantsAtScale hR
  have hRscale : R.scale ≤ n := by
    rw [hRscale', show (originCube d n).scale = n from rfl]
    have hj0 : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg j
    omega
  have hRcenter : cubeCenter R ∈ cubeSet (originCube d n) :=
    akhcWeakD_cubeCenter_mem_of_mem_descendantsAtScale hjle hR
  have hbound := akhcWeakD_matrixNorm_upperLeft_le hE ha hBdd hRscale hRcenter
  have hexp : (n : ℝ) - (R.scale : ℝ) = (j : ℝ) := by
    have : R.scale = n - (j : ℤ) := hRscale'
    rw [this]; push_cast; ring
  rw [hexp] at hbound
  have hw : 0 ≤ Real.rpow (3 : ℝ) (ρ * (j : ℝ)) := Real.rpow_nonneg (by norm_num) _
  have hfac := akhcWeakD_factor_le hσnn hMnn hw
  calc
    Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) a.toFun).upperLeft ≤
        (1 + Real.rpow (3 : ℝ) (ρ * (j : ℝ)) * M) * σ := hbound
    _ ≤ σ * (1 + M) * (1 + Real.rpow (3 : ℝ) (ρ * (j : ℝ))) := hfac
    _ = σ * (1 + M) * (1 + 0) * (1 + Real.rpow (3 : ℝ) (ρ * (j : ℝ))) := by ring

/-- **`λ⁻¹` bound, linear in `1 + M⁺`, arbitrary positive-definite reference.** For `s' > 0`
with `ρ/2 < s'`, `λ_{s',1}(cu_n; a)⁻¹ ≤ C(s',ρ)·|E_{LR}|·(1 + M⁺_{n,ρ}(E; a))`. -/
theorem akhcWeakD_lambdaSqCoeffField_inv_le {d : ℕ} [NeZero d] {E : BlockMat d}
    (hE : (toFullBlockMat E).PosDef) {a : RegCoeffField d}
    (ha : Ch04.AELocallyUniformlyEllipticField a) {n : ℤ} {ρ s' : ℝ} (hs' : 0 < s')
    (hgap : ρ / 2 < s')
    (hBdd :
      BddAbove
        {M : ℝ |
          ∃ Q : TriadicCube d,
            Q.scale ≤ n ∧
              cubeCenter Q ∈ cubeSet (originCube d n) ∧
              M =
                Real.rpow (3 : ℝ) (-ρ * ((n : ℝ) - (Q.scale : ℝ))) *
                  SuperdiffusionCLT.AKHC61.Tails.akhcTailEll_excess E
                    (coarseBlockMatrix (cubeSet Q) a.toFun)}) :
    (Ch04.lambdaSqCoeffField (originCube d n) s' (.finite 1) a)⁻¹ ≤
      akhcWeakC2_maximizerConst s' ρ * Ch02.matrixNorm E.lowerRight *
        (1 + akhcWeakC_eventMoreprotoPlus n ρ E a.toFun) := by
  rw [Book.Ch04.RestrictionLawCarrier.lambdaSqCoeffField_finite_one_eq_tsum_sq_inv
    (originCube d n) a hs', inv_inv]
  set M : ℝ := akhcWeakC_eventMoreprotoPlus n ρ E a.toFun with hMdef
  set σ : ℝ := Ch02.matrixNorm E.lowerRight with hσdef
  have hMnn : 0 ≤ M := akhcWeakD_eventMoreprotoPlus_nonneg _ _ _ _
  have hσnn : 0 ≤ σ := Book.Ch02.matrixNorm_nonneg _
  have h1M : 0 ≤ 1 + M := by linarith only [hMnn]
  refine le_trans (akhcWeakC2_tsum_sq_le (σ := σ * (1 + M)) (M := 0) hs' hgap
    (mul_nonneg hσnn h1M) le_rfl
    (fun j => by
      rw [Book.Ch04.RestrictionLawCarrier.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale_eq_finsetSupReal_ae
        ha (originCube d n) ((originCube d n).scale - (j : ℤ))]
      exact Book.Ch02.finsetSupReal_nonneg _ _ fun R _ => Book.Ch02.matrixNorm_nonneg _) ?_)
    (le_of_eq (by ring))
  intro j
  rw [Book.Ch04.RestrictionLawCarrier.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale_eq_finsetSupReal_ae
    ha (originCube d n) ((originCube d n).scale - (j : ℤ))]
  have hjle : (originCube d n).scale - (j : ℤ) ≤ (originCube d n).scale := by
    have hj0 : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg j
    linarith only [hj0]
  refine Book.Ch02.finsetSupReal_le _ (descendantsAtScale_nonempty (originCube d n) hjle) ?_
  intro R hR
  have hRscale' : R.scale = (originCube d n).scale - (j : ℤ) :=
    akhcWeakD_scale_eq_of_mem_descendantsAtScale hR
  have hRscale : R.scale ≤ n := by
    rw [hRscale', show (originCube d n).scale = n from rfl]
    have hj0 : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg j
    omega
  have hRcenter : cubeCenter R ∈ cubeSet (originCube d n) :=
    akhcWeakD_cubeCenter_mem_of_mem_descendantsAtScale hjle hR
  have hbound := akhcWeakD_matrixNorm_lowerRight_le hE ha hBdd hRscale hRcenter
  have hexp : (n : ℝ) - (R.scale : ℝ) = (j : ℝ) := by
    have : R.scale = n - (j : ℤ) := hRscale'
    rw [this]; push_cast; ring
  rw [hexp] at hbound
  have hw : 0 ≤ Real.rpow (3 : ℝ) (ρ * (j : ℝ)) := Real.rpow_nonneg (by norm_num) _
  have hfac := akhcWeakD_factor_le hσnn hMnn hw
  calc
    Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) a.toFun).lowerRight ≤
        (1 + Real.rpow (3 : ℝ) (ρ * (j : ℝ)) * M) * σ := hbound
    _ ≤ σ * (1 + M) * (1 + Real.rpow (3 : ℝ) (ρ * (j : ℝ))) := hfac
    _ = σ * (1 + M) * (1 + 0) * (1 + Real.rpow (3 : ℝ) (ρ * (j : ℝ))) := by ring

end

end SuperdiffusionCLT.AKHC61.WeakNorms
