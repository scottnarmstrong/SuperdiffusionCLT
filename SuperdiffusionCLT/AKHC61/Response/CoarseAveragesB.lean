/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.Response.CoarseAverages
public import Homogenization.Book.Ch05.Theorems.Section53.WeakNormsMaximizer.Basic

/-!
# Package B4, part 2: node 16, the average terms of the weak-norm maximizer RHS

Continues `CoarseAverages.lean`. This file assembles the deterministic
per-special-vector bound (RETYPE of CG's
`weighted_special_average_mismatch_le_reflected_normalized_block_fluctuation`,
`CoarseAverages.lean`) and its descendant-averaged corollary,
then the finite-sum Cauchy-Schwarz step (RETYPE of CG's `HighScaleAverages.lean`,
which is entirely law-free pure algebra) that converts the two *average* terms
of the deterministic maximizer right-hand side,
`WeakNormsMaximizer.gradientAverageTermAtScale`/`fluxAverageTermAtScale`
(`WeakNormsMaximizer/Basic.lean`, USEd as is — law-free), into node 16's
target: a weighted sum, over scales `n`, of the descendant average of
`akhcFullBlockNormalizedFluctuationAtScale`.

It also proves the stationarity/expectation bridge needed to turn the
deterministic core into node 16's `E`-level statement: the descendant average
of `akhcFullBlockNormalizedFluctuationAtScale` at scale `n` has the same
expectation as the single value at `originCube d n`
(`akhc_integral_fullBlockNormalizedFluctuation_eq_originCube_of_mem_descendantsAtScale`).
Combining that bridge with the deterministic core to reach the literal
`E ≤ (weighted sum of) E|...|²` display needs `Integrable` hypotheses for the
squared average terms and for the fluctuation, which require second-moment (P3') control;
the integral identities that feed into that display are in `CoarseAveragesC.lean`. When proving
a Bochner-integral equality in these nested definitions, state it first as a `have` and then
use a plain `rw`; `congr` on such a goal forces catastrophic `whnf` unfolding.

## Main results

* `akhc_weighted_special_average_mismatch_le_fullBlockNormalized_fluctuation`:
  the pointwise special-vector bound.
* `akhc_descendantsAverage_weighted_special_average_mismatch_le_fullBlockNormalized_fluctuation`:
  its descendant average.
* `akhc_paired_highScaleAverageTerms_special_le_weighted_fullBlockNormalized_fluctuation`:
  **node 16's deterministic core**, the direct RETYPE of CG's
  `HighScaleAverages.lean:96`.
* `akhc_integral_fullBlockNormalizedFluctuation_eq_originCube_of_mem_descendantsAtScale`:
  the stationarity bridge for the expectation-level assembly.
* `akhc_descendantsAverage_eq_of_forall_eq`, `akhc_integral_descendantsAverage`:
  reusable `descendantsAverage`/integral helpers for that assembly.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.Response

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.AKHC61.Carrier
open scoped Matrix.Norms.Elementwise BigOperators

noncomputable section

/-- **The pointwise per-special-vector bound.** RETYPE of CG's
`weighted_special_average_mismatch_le_reflected_normalized_block_fluctuation`
followed by `akhc_reflectedFullBlockNormalizedFluctuationAtScale_eq_fullBlock`,
onto the local scalars and `θ := thetaCutoff nu L P m`. -/
theorem akhc_weighted_special_average_mismatch_le_fullBlockNormalized_fluctuation
    {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ) {P : ProbabilityMeasure (ShellSeq d)}
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    (a : RegCoeffField d) (ha : Book.Ch04.AELocallyUniformlyEllipticField a)
    (m : ℕ) (R : TriadicCube d) (e : Vec d)
    (hb : 0 < sigmaBarScalar nu L P (cubeSet (originCube d (m : ℤ))))
    (hc : 0 < sigmaBarStarInvScalar nu L P (cubeSet (originCube d (m : ℤ)))) :
    let p_e := akhcSpecialPAtScale nu L P (m : ℤ) e
    let q_e := akhcSpecialQAtScale nu L P (m : ℤ) e
    let p0_e := sigmaBarStarInvScalar nu L P (cubeSet (originCube d (m : ℤ))) • q_e - p_e
    let q0_e := q_e - sigmaBarScalar nu L P (cubeSet (originCube d (m : ℤ))) • p_e
    akhcSigmaHatAtScale nu L P (m : ℤ) *
        vecNormSq (Book.Ch04.canonicalScalarResponseGradientAverageCubeSet R R p_e q_e a.toFun -
          p0_e) +
      (akhcSigmaHatAtScale nu L P (m : ℤ))⁻¹ *
        vecNormSq (Book.Ch04.canonicalScalarResponseFluxAverageCubeSet R R p_e q_e a.toFun -
          q0_e) ≤
      2 * SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m *
        akhcFullBlockNormalizedFluctuationAtScale nu L P (m : ℤ) R a *
          vecNormSq e := by
  dsimp only
  let b := sigmaBarScalar nu L P (cubeSet (originCube d (m : ℤ)))
  let c := (sigmaBarStarInvScalar nu L P (cubeSet (originCube d (m : ℤ))))⁻¹
  let σ := akhcSigmaHatAtScale nu L P (m : ℤ)
  let θ := SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m
  let p_e := akhcSpecialPAtScale nu L P (m : ℤ) e
  let q_e := akhcSpecialQAtScale nu L P (m : ℤ) e
  let p0_e := sigmaBarStarInvScalar nu L P (cubeSet (originCube d (m : ℤ))) • q_e - p_e
  let q0_e := q_e - sigmaBarScalar nu L P (cubeSet (originCube d (m : ℤ))) • p_e
  let A := coarseBlockMatrix (cubeSet R) a.toFun
  let Abar := annealedBlockMatrix nu L P (cubeSet (originCube d (m : ℤ)))
  let M : FullBlockMat d := toFullBlockMat (blockReflect A) - toFullBlockMat (blockReflect Abar)
  let P_e : BlockVec d := (-q_e, p_e)
  let X : BlockVec d :=
    (-(Book.Ch04.canonicalScalarResponseGradientAverageCubeSet R R p_e q_e a.toFun - p0_e),
      -(Book.Ch04.canonicalScalarResponseFluxAverageCubeSet R R p_e q_e a.toFun - q0_e))
  have hc' : 0 < c := inv_pos.mpr hc
  have hσ : σ = Real.sqrt (b * c) := rfl
  have hθ : θ = b * c⁻¹ := by
    show SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m = b * c⁻¹
    have hcinv : c⁻¹ = sigmaBarStarInvScalar nu L P (cubeSet (originCube d (m : ℤ))) := by
      simp [c]
    rw [hcinv, SuperdiffusionCLT.Frozen.Section4.thetaCutoff, sigmaBarSeq,
      sigmaBarStarInvSeq]
  have hid : X = blockMatVecMul (ofFullBlockMat M) P_e := by
    simpa [X, M, P_e, p_e, q_e, p0_e, q0_e, A, Abar, b, c, σ] using
      akhc_special_average_mismatch_eq_reflected_block_fluctuation hnu L hJ4 a ha m R e
  have hmulVec : Matrix.mulVec M (toFullBlockVec P_e) = toFullBlockVec X := by
    calc
      Matrix.mulVec M (toFullBlockVec P_e) =
          toFullBlockVec (blockMatVecMul (ofFullBlockMat M) P_e) := by
            rw [toFullBlockVec_blockMatVecMul]
            simp [M]
      _ = toFullBlockVec X := by
            rw [← hid]
  have hnorm_le :=
    akhc_normalized_mulVec_norm_sq_le (d := d) (b := b) (c := c) hb hc' M (toFullBlockVec P_e)
  have hnorm_le' :
      ‖(WithLp.toLp 2
          (Matrix.mulVec (Matrix.diagonal (akhcStarInvSqrtDiag (d := d) b c)) (toFullBlockVec X)) :
          PiLp 2 (fun _ : BlockCoord d => ℝ))‖ ^ 2 ≤
        ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
            (Matrix.diagonal (akhcStarInvSqrtDiag (d := d) b c) * M *
              Matrix.diagonal (akhcStarInvSqrtDiag b c))‖ ^ 2 *
          ‖(WithLp.toLp 2
            (Matrix.mulVec (Matrix.diagonal (akhcStarSqrtDiag (d := d) b c)) (toFullBlockVec P_e)) :
            PiLp 2 (fun _ : BlockCoord d => ℝ))‖ ^ 2 := by
    simpa [hmulVec] using hnorm_le
  have hP_norm :
      ‖(WithLp.toLp 2
          (Matrix.mulVec (Matrix.diagonal (akhcStarSqrtDiag (d := d) b c)) (toFullBlockVec P_e)) :
          PiLp 2 (fun _ : BlockCoord d => ℝ))‖ ^ 2 =
        2 * (σ * c⁻¹) * vecNormSq e := by
    have h :=
      akhc_norm_sq_starSqrtDiag_mulVec_specialBlockVec (d := d) hb hc' hσ e
    simpa [P_e, p_e, q_e, akhcSpecialPAtScale, akhcSpecialQAtScale, σ, mul_assoc] using h
  have hweight :=
    akhc_weighted_blockVec_norm_sq_eq_sigma_inv_star_mul_normalized_norm_sq
      (d := d) hb hc' hσ X
  have hα_nonneg : 0 ≤ σ * c⁻¹ := by
    have hσpos : 0 < σ := by
      rw [hσ]
      exact Real.sqrt_pos_of_pos (mul_pos hb hc')
    exact mul_nonneg hσpos.le (inv_pos.mpr hc').le
  have hmul_le := mul_le_mul_of_nonneg_left hnorm_le' hα_nonneg
  have hscalar :
      (σ * c⁻¹) *
          (‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
              (Matrix.diagonal (akhcStarInvSqrtDiag (d := d) b c) * M *
                Matrix.diagonal (akhcStarInvSqrtDiag b c))‖ ^ 2 *
            (2 * (σ * c⁻¹) * vecNormSq e)) =
        2 * θ *
          ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
              (Matrix.diagonal (akhcStarInvSqrtDiag (d := d) b c) * M *
                Matrix.diagonal (akhcStarInvSqrtDiag b c))‖ ^ 2 *
            vecNormSq e := by
    have hsq := akhc_sigma_mul_inv_star_sq_eq_theta hb hc' hσ hθ
    calc
      (σ * c⁻¹) *
          (‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
              (Matrix.diagonal (akhcStarInvSqrtDiag (d := d) b c) * M *
                Matrix.diagonal (akhcStarInvSqrtDiag b c))‖ ^ 2 *
            (2 * (σ * c⁻¹) * vecNormSq e)) =
          2 * (σ * c⁻¹) ^ 2 *
            ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
              (Matrix.diagonal (akhcStarInvSqrtDiag (d := d) b c) * M *
                Matrix.diagonal (akhcStarInvSqrtDiag b c))‖ ^ 2 *
            vecNormSq e := by
            ring
      _ = 2 * θ *
          ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
              (Matrix.diagonal (akhcStarInvSqrtDiag (d := d) b c) * M *
                Matrix.diagonal (akhcStarInvSqrtDiag b c))‖ ^ 2 *
            vecNormSq e := by
            rw [hsq]
  have hmain :
      σ *
          vecNormSq (Book.Ch04.canonicalScalarResponseGradientAverageCubeSet R R p_e q_e a.toFun -
            p0_e) +
        σ⁻¹ *
          vecNormSq (Book.Ch04.canonicalScalarResponseFluxAverageCubeSet R R p_e q_e a.toFun -
            q0_e)
        ≤ 2 * θ *
            akhcReflectedFullBlockNormalizedFluctuationAtScale nu L P (m : ℤ) R a * vecNormSq e := by
    calc
      σ *
          vecNormSq (Book.Ch04.canonicalScalarResponseGradientAverageCubeSet R R p_e q_e a.toFun -
            p0_e) +
        σ⁻¹ *
          vecNormSq (Book.Ch04.canonicalScalarResponseFluxAverageCubeSet R R p_e q_e a.toFun -
            q0_e)
        = σ * vecNormSq X.1 + σ⁻¹ * vecNormSq X.2 := by
            simp [X]
            rw [akhc_vecNormSq_sub_comm
                (Book.Ch04.canonicalScalarResponseGradientAverageCubeSet R R p_e q_e a.toFun) p0_e,
              akhc_vecNormSq_sub_comm
                (Book.Ch04.canonicalScalarResponseFluxAverageCubeSet R R p_e q_e a.toFun) q0_e]
      _ = (σ * c⁻¹) *
          ‖(WithLp.toLp 2
            (Matrix.mulVec (Matrix.diagonal (akhcStarInvSqrtDiag (d := d) b c)) (toFullBlockVec X)) :
            PiLp 2 (fun _ : BlockCoord d => ℝ))‖ ^ 2 := hweight
      _ ≤ (σ * c⁻¹) *
          (‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
              (Matrix.diagonal (akhcStarInvSqrtDiag (d := d) b c) * M *
                Matrix.diagonal (akhcStarInvSqrtDiag b c))‖ ^ 2 *
            ‖(WithLp.toLp 2
              (Matrix.mulVec (Matrix.diagonal (akhcStarSqrtDiag (d := d) b c))
                (toFullBlockVec P_e)) :
              PiLp 2 (fun _ : BlockCoord d => ℝ))‖ ^ 2) := hmul_le
      _ = (σ * c⁻¹) *
          (‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
              (Matrix.diagonal (akhcStarInvSqrtDiag (d := d) b c) * M *
                Matrix.diagonal (akhcStarInvSqrtDiag b c))‖ ^ 2 *
            (2 * (σ * c⁻¹) * vecNormSq e)) := by
            rw [hP_norm]
      _ = 2 * θ *
            ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
                (Matrix.diagonal (akhcStarInvSqrtDiag (d := d) b c) * M *
                  Matrix.diagonal (akhcStarInvSqrtDiag b c))‖ ^ 2 *
              vecNormSq e := hscalar
      _ = 2 * θ *
            akhcReflectedFullBlockNormalizedFluctuationAtScale nu L P (m : ℤ) R a * vecNormSq e := by
          simp [akhcReflectedFullBlockNormalizedFluctuationAtScale, M, A, Abar, b, c, θ, mul_assoc]
  rw [akhc_reflectedFullBlockNormalizedFluctuationAtScale_eq_fullBlock] at hmain
  exact hmain

/-- Unit-direction corollary of
`akhc_weighted_special_average_mismatch_le_fullBlockNormalized_fluctuation`,
dropping the `vecNormSq e` factor. -/
theorem akhc_weighted_special_average_mismatch_le_fullBlockNormalized_fluctuation_unit
    {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ) {P : ProbabilityMeasure (ShellSeq d)}
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    (a : RegCoeffField d) (ha : Book.Ch04.AELocallyUniformlyEllipticField a)
    (m : ℕ) (R : TriadicCube d) (e : Vec d)
    (hb : 0 < sigmaBarScalar nu L P (cubeSet (originCube d (m : ℤ))))
    (hc : 0 < sigmaBarStarInvScalar nu L P (cubeSet (originCube d (m : ℤ))))
    (he : vecNormSq e = 1) :
    let p_e := akhcSpecialPAtScale nu L P (m : ℤ) e
    let q_e := akhcSpecialQAtScale nu L P (m : ℤ) e
    let p0_e := sigmaBarStarInvScalar nu L P (cubeSet (originCube d (m : ℤ))) • q_e - p_e
    let q0_e := q_e - sigmaBarScalar nu L P (cubeSet (originCube d (m : ℤ))) • p_e
    akhcSigmaHatAtScale nu L P (m : ℤ) *
        vecNormSq (Book.Ch04.canonicalScalarResponseGradientAverageCubeSet R R p_e q_e a.toFun -
          p0_e) +
      (akhcSigmaHatAtScale nu L P (m : ℤ))⁻¹ *
        vecNormSq (Book.Ch04.canonicalScalarResponseFluxAverageCubeSet R R p_e q_e a.toFun -
          q0_e) ≤
      2 * SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m *
        akhcFullBlockNormalizedFluctuationAtScale nu L P (m : ℤ) R a := by
  simpa [he, mul_assoc] using
    akhc_weighted_special_average_mismatch_le_fullBlockNormalized_fluctuation
      hnu L hJ4 a ha m R e hb hc

/-- Descendant-averaged form, for a unit special direction `e`. -/
theorem akhc_descendantsAverage_weighted_special_average_mismatch_le_fullBlockNormalized_fluctuation
    {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ) {P : ProbabilityMeasure (ShellSeq d)}
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    (a : RegCoeffField d) (ha : Book.Ch04.AELocallyUniformlyEllipticField a)
    (m : ℕ) (Q : TriadicCube d) (j : ℕ) (e : Vec d)
    (hb : 0 < sigmaBarScalar nu L P (cubeSet (originCube d (m : ℤ))))
    (hc : 0 < sigmaBarStarInvScalar nu L P (cubeSet (originCube d (m : ℤ))))
    (he : vecNormSq e = 1) :
    let p_e := akhcSpecialPAtScale nu L P (m : ℤ) e
    let q_e := akhcSpecialQAtScale nu L P (m : ℤ) e
    let p0_e := sigmaBarStarInvScalar nu L P (cubeSet (originCube d (m : ℤ))) • q_e - p_e
    let q0_e := q_e - sigmaBarScalar nu L P (cubeSet (originCube d (m : ℤ))) • p_e
    descendantsAverage Q j
        (fun R =>
          akhcSigmaHatAtScale nu L P (m : ℤ) *
              vecNormSq (Book.Ch04.canonicalScalarResponseGradientAverageCubeSet R R p_e q_e
                a.toFun - p0_e) +
            (akhcSigmaHatAtScale nu L P (m : ℤ))⁻¹ *
              vecNormSq (Book.Ch04.canonicalScalarResponseFluxAverageCubeSet R R p_e q_e a.toFun -
                q0_e)) ≤
      descendantsAverage Q j
        (fun R =>
          2 * SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m *
            akhcFullBlockNormalizedFluctuationAtScale nu L P (m : ℤ) R a) := by
  dsimp only
  refine descendantsAverage_le_descendantsAverage Q j ?_
  intro R _hR
  exact
    akhc_weighted_special_average_mismatch_le_fullBlockNormalized_fluctuation_unit
      hnu L hJ4 a ha m R e hb hc he

/-! ## The finite-sum Cauchy-Schwarz layer (pure algebra, retyped from CG's
`HighScaleAverages.lean`) -/

theorem akhc_finset_weighted_sqrt_sum_sq_le_sum_mul_sum
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (w A : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hA : ∀ i, 0 ≤ A i) :
    (∑ i ∈ S, w i * Real.sqrt (A i)) ^ 2 ≤
      (∑ i ∈ S, w i) * ∑ i ∈ S, w i * A i := by
  have hsum_eq :
      (∑ i ∈ S, Real.sqrt (w i) * Real.sqrt (w i * A i)) =
        ∑ i ∈ S, w i * Real.sqrt (A i) := by
    refine Finset.sum_congr rfl ?_
    intro i _hi
    rw [Real.sqrt_mul (hw i) (A i)]
    rw [← mul_assoc, ← sq, Real.sq_sqrt (hw i)]
  have hCauchy :
      (∑ i ∈ S, w i * Real.sqrt (A i)) ≤
        Real.sqrt (∑ i ∈ S, w i) *
          Real.sqrt (∑ i ∈ S, w i * A i) := by
    simpa [hsum_eq] using
      (Real.sum_sqrt_mul_sqrt_le (s := S) (f := w) (g := fun i => w i * A i)
        hw (fun i => mul_nonneg (hw i) (hA i)))
  have hleft_nonneg : 0 ≤ ∑ i ∈ S, w i * Real.sqrt (A i) :=
    Finset.sum_nonneg fun i _hi => mul_nonneg (hw i) (Real.sqrt_nonneg _)
  have hW_nonneg : 0 ≤ ∑ i ∈ S, w i :=
    Finset.sum_nonneg fun i _hi => hw i
  have hWA_nonneg : 0 ≤ ∑ i ∈ S, w i * A i :=
    Finset.sum_nonneg fun i _hi => mul_nonneg (hw i) (hA i)
  have hsq :=
    pow_le_pow_left₀ hleft_nonneg hCauchy 2
  calc
    (∑ i ∈ S, w i * Real.sqrt (A i)) ^ 2
        ≤ (Real.sqrt (∑ i ∈ S, w i) *
            Real.sqrt (∑ i ∈ S, w i * A i)) ^ 2 := hsq
    _ = (∑ i ∈ S, w i) * ∑ i ∈ S, w i * A i := by
          rw [mul_pow, Real.sq_sqrt hW_nonneg, Real.sq_sqrt hWA_nonneg]

theorem akhc_finset_weighted_sqrt_sum_sq_le_of_weight_le
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (v w A : ι → ℝ)
    (hv : ∀ i, 0 ≤ v i) (hw : ∀ i, 0 ≤ w i) (hvw : ∀ i, v i ≤ w i)
    (hA : ∀ i, 0 ≤ A i) :
    (∑ i ∈ S, v i * Real.sqrt (A i)) ^ 2 ≤
      (∑ i ∈ S, w i) * ∑ i ∈ S, w i * A i := by
  have hsum_le :
      (∑ i ∈ S, v i * Real.sqrt (A i)) ≤
        ∑ i ∈ S, w i * Real.sqrt (A i) := by
    refine Finset.sum_le_sum ?_
    intro i _hi
    exact mul_le_mul_of_nonneg_right (hvw i) (Real.sqrt_nonneg _)
  have hleft_nonneg : 0 ≤ ∑ i ∈ S, v i * Real.sqrt (A i) :=
    Finset.sum_nonneg fun i _hi => mul_nonneg (hv i) (Real.sqrt_nonneg _)
  have hright_nonneg : 0 ≤ ∑ i ∈ S, w i * Real.sqrt (A i) :=
    Finset.sum_nonneg fun i _hi => mul_nonneg (hw i) (Real.sqrt_nonneg _)
  have hsq_le :=
    pow_le_pow_left₀ hleft_nonneg hsum_le 2
  exact hsq_le.trans
    (akhc_finset_weighted_sqrt_sum_sq_le_sum_mul_sum S w A hw hA)

theorem akhc_highScaleWeight_le_betaWeight
    (β s : ℝ) (hβs : β ≤ s) (r : ℕ) :
    Real.rpow (3 : ℝ) (-s * (r : ℝ)) ≤
      Real.rpow (3 : ℝ) (-β * (r : ℝ)) := by
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) ?_
  have hr : 0 ≤ (r : ℝ) := by positivity
  have hmul : β * (r : ℝ) ≤ s * (r : ℝ) := mul_le_mul_of_nonneg_right hβs hr
  linarith only [hmul]

theorem akhc_sigmaHatAtScale_nonneg
    {d : ℕ} [NeZero d] (nu : ℝ) (L : ℕ) (P : ProbabilityMeasure (ShellSeq d)) (m : ℤ) :
    0 ≤ akhcSigmaHatAtScale nu L P m :=
  Real.sqrt_nonneg _

/-! ## Node 16's deterministic core -/

/-- **Node 16's deterministic (samplewise) core.** RETYPE of CG's
`HighScaleAverages.lean:96`,
`paired_highScaleAverageTerms_special_le_weighted_fullBlockNormalized_fluctuation`,
onto the local scalars. The average terms of the deterministic maximizer RHS
(`WeakNormsMaximizer.gradientAverageTermAtScale`/`fluxAverageTermAtScale`,
law-free, USEd as is) are bounded, samplewise, by a `β`-weighted sum over
scales `n ∈ (k, m]` of the descendant average of `2·θ_m ·
akhcFullBlockNormalizedFluctuationAtScale`. -/
theorem akhc_paired_highScaleAverageTerms_special_le_weighted_fullBlockNormalized_fluctuation
    {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ) {P : ProbabilityMeasure (ShellSeq d)}
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    (a : RegCoeffField d) (ha : Book.Ch04.AELocallyUniformlyEllipticField a)
    {k m : ℕ} (β s t : ℝ) (hβs : β ≤ s) (hβt : β ≤ t) (e : Vec d)
    (hb : 0 < sigmaBarScalar nu L P (cubeSet (originCube d (m : ℤ))))
    (hc : 0 < sigmaBarStarInvScalar nu L P (cubeSet (originCube d (m : ℤ))))
    (he : vecNormSq e = 1) :
    let p_e := akhcSpecialPAtScale nu L P (m : ℤ) e
    let q_e := akhcSpecialQAtScale nu L P (m : ℤ) e
    let p0_e := sigmaBarStarInvScalar nu L P (cubeSet (originCube d (m : ℤ))) • q_e - p_e
    let q0_e := q_e - sigmaBarScalar nu L P (cubeSet (originCube d (m : ℤ))) • p_e
    let σ := akhcSigmaHatAtScale nu L P (m : ℤ)
    let θ := SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m
    let S := Finset.Icc ((k : ℤ) + 1) (m : ℤ)
    let wβ : ℤ → ℝ :=
      fun n => Real.rpow (3 : ℝ)
        (-β * (Int.toNat ((m : ℤ) - n) : ℝ))
    σ *
        (Book.Ch05.Section53.WeakNormsMaximizer.gradientAverageTermAtScale
          (m : ℤ) (k : ℤ) s p_e q_e p0_e a) ^ 2 +
      σ⁻¹ *
        (Book.Ch05.Section53.WeakNormsMaximizer.fluxAverageTermAtScale
          (m : ℤ) (k : ℤ) t p_e q_e q0_e a) ^ 2 ≤
      (∑ n ∈ S, wβ n) *
        ∑ n ∈ S, wβ n *
          descendantsAverage (originCube d (m : ℤ))
            (Int.toNat ((m : ℤ) - n))
            (fun R =>
              2 * θ *
                akhcFullBlockNormalizedFluctuationAtScale nu L P (m : ℤ) R a) := by
  dsimp only
  let p_e := akhcSpecialPAtScale nu L P (m : ℤ) e
  let q_e := akhcSpecialQAtScale nu L P (m : ℤ) e
  let p0_e := sigmaBarStarInvScalar nu L P (cubeSet (originCube d (m : ℤ))) • q_e - p_e
  let q0_e := q_e - sigmaBarScalar nu L P (cubeSet (originCube d (m : ℤ))) • p_e
  let σ := akhcSigmaHatAtScale nu L P (m : ℤ)
  let θ := SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m
  let S := Finset.Icc ((k : ℤ) + 1) (m : ℤ)
  let wβ : ℤ → ℝ :=
    fun n => Real.rpow (3 : ℝ)
      (-β * (Int.toNat ((m : ℤ) - n) : ℝ))
  let ws : ℤ → ℝ :=
    fun n => Real.rpow (3 : ℝ)
      (-s * (Int.toNat ((m : ℤ) - n) : ℝ))
  let wt : ℤ → ℝ :=
    fun n => Real.rpow (3 : ℝ)
      (-t * (Int.toNat ((m : ℤ) - n) : ℝ))
  let G : ℤ → ℝ :=
    fun n =>
      descendantsAverage (originCube d (m : ℤ))
        (Int.toNat ((m : ℤ) - n))
        (fun R =>
          vecNormSq
            (Book.Ch04.canonicalScalarResponseGradientAverageCubeSet R R p_e q_e a.toFun - p0_e))
  let F : ℤ → ℝ :=
    fun n =>
      descendantsAverage (originCube d (m : ℤ))
        (Int.toNat ((m : ℤ) - n))
        (fun R =>
          vecNormSq
            (Book.Ch04.canonicalScalarResponseFluxAverageCubeSet R R p_e q_e a.toFun - q0_e))
  let H : ℤ → ℝ :=
    fun n =>
      descendantsAverage (originCube d (m : ℤ))
        (Int.toNat ((m : ℤ) - n))
        (fun R =>
          2 * θ *
            akhcFullBlockNormalizedFluctuationAtScale nu L P (m : ℤ) R a)
  have hwβ : ∀ n, 0 ≤ wβ n := by
    intro n
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hws : ∀ n, 0 ≤ ws n := by
    intro n
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hwt : ∀ n, 0 ≤ wt n := by
    intro n
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hws_le : ∀ n, ws n ≤ wβ n := by
    intro n
    exact akhc_highScaleWeight_le_betaWeight β s hβs (Int.toNat ((m : ℤ) - n))
  have hwt_le : ∀ n, wt n ≤ wβ n := by
    intro n
    exact akhc_highScaleWeight_le_betaWeight β t hβt (Int.toNat ((m : ℤ) - n))
  have hG_nonneg : ∀ n, 0 ≤ G n := by
    intro n
    exact descendantsAverage_nonneg _ _ _ fun R _hR => vecNormSq_nonneg _
  have hF_nonneg : ∀ n, 0 ≤ F n := by
    intro n
    exact descendantsAverage_nonneg _ _ _ fun R _hR => vecNormSq_nonneg _
  have hσ_nonneg : 0 ≤ σ := akhc_sigmaHatAtScale_nonneg nu L P (m : ℤ)
  have hσ_inv_nonneg : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ_nonneg
  have hgrad_cauchy :
      (∑ n ∈ S, ws n * Real.sqrt (G n)) ^ 2 ≤
        (∑ n ∈ S, wβ n) * ∑ n ∈ S, wβ n * G n :=
    akhc_finset_weighted_sqrt_sum_sq_le_of_weight_le S ws wβ G hws hwβ hws_le hG_nonneg
  have hflux_cauchy :
      (∑ n ∈ S, wt n * Real.sqrt (F n)) ^ 2 ≤
        (∑ n ∈ S, wβ n) * ∑ n ∈ S, wβ n * F n :=
    akhc_finset_weighted_sqrt_sum_sq_le_of_weight_le S wt wβ F hwt hwβ hwt_le hF_nonneg
  have hgrad_scaled :
      σ * (∑ n ∈ S, ws n * Real.sqrt (G n)) ^ 2 ≤
        (∑ n ∈ S, wβ n) * (∑ n ∈ S, wβ n * (σ * G n)) := by
    have h := mul_le_mul_of_nonneg_left hgrad_cauchy hσ_nonneg
    simpa [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using h
  have hflux_scaled :
      σ⁻¹ * (∑ n ∈ S, wt n * Real.sqrt (F n)) ^ 2 ≤
        (∑ n ∈ S, wβ n) * (∑ n ∈ S, wβ n * (σ⁻¹ * F n)) := by
    have h := mul_le_mul_of_nonneg_left hflux_cauchy hσ_inv_nonneg
    simpa [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using h
  have hpaired_sums :
      σ * (∑ n ∈ S, ws n * Real.sqrt (G n)) ^ 2 +
          σ⁻¹ * (∑ n ∈ S, wt n * Real.sqrt (F n)) ^ 2 ≤
        (∑ n ∈ S, wβ n) *
          (∑ n ∈ S, wβ n * (σ * G n + σ⁻¹ * F n)) := by
    have hsum_nonneg : 0 ≤ ∑ n ∈ S, wβ n :=
      Finset.sum_nonneg fun n _hn => hwβ n
    have h := add_le_add hgrad_scaled hflux_scaled
    calc
      σ * (∑ n ∈ S, ws n * Real.sqrt (G n)) ^ 2 +
          σ⁻¹ * (∑ n ∈ S, wt n * Real.sqrt (F n)) ^ 2
          ≤
        (∑ n ∈ S, wβ n) * (∑ n ∈ S, wβ n * (σ * G n)) +
          (∑ n ∈ S, wβ n) * (∑ n ∈ S, wβ n * (σ⁻¹ * F n)) := h
      _ =
        (∑ n ∈ S, wβ n) *
          (∑ n ∈ S, wβ n * (σ * G n + σ⁻¹ * F n)) := by
          rw [← mul_add, ← Finset.sum_add_distrib]
          congr 2
          ext n
          ring
  have hpoint :
      ∀ n ∈ S, σ * G n + σ⁻¹ * F n ≤ H n := by
    intro n _hn
    let j := Int.toNat ((m : ℤ) - n)
    let Q : TriadicCube d := originCube d (m : ℤ)
    let Grad : TriadicCube d → ℝ :=
      fun R =>
        vecNormSq
          (Book.Ch04.canonicalScalarResponseGradientAverageCubeSet R R p_e q_e a.toFun - p0_e)
    let Flux : TriadicCube d → ℝ :=
      fun R =>
        vecNormSq
          (Book.Ch04.canonicalScalarResponseFluxAverageCubeSet R R p_e q_e a.toFun - q0_e)
    have hlinear :
        descendantsAverage Q j (fun R => σ * Grad R + σ⁻¹ * Flux R) =
          σ * G n + σ⁻¹ * F n := by
      rw [descendantsAverage_add, descendantsAverage_mul_left,
        descendantsAverage_mul_left]
    have hbase :=
      akhc_descendantsAverage_weighted_special_average_mismatch_le_fullBlockNormalized_fluctuation
        hnu L hJ4 a ha m Q j e hb hc he
    calc
      σ * G n + σ⁻¹ * F n =
          descendantsAverage Q j (fun R => σ * Grad R + σ⁻¹ * Flux R) := hlinear.symm
      _ ≤ H n := by
          simpa [H, Q, j, Grad, Flux, σ, θ, p_e, q_e, p0_e, q0_e] using hbase
  have hsum_point :
      (∑ n ∈ S, wβ n * (σ * G n + σ⁻¹ * F n)) ≤
        ∑ n ∈ S, wβ n * H n := by
    refine Finset.sum_le_sum ?_
    intro n hn
    exact mul_le_mul_of_nonneg_left (hpoint n hn) (hwβ n)
  have hsum_nonneg : 0 ≤ ∑ n ∈ S, wβ n :=
    Finset.sum_nonneg fun n _hn => hwβ n
  have hfluct :=
    mul_le_mul_of_nonneg_left hsum_point hsum_nonneg
  calc
    σ *
        (Book.Ch05.Section53.WeakNormsMaximizer.gradientAverageTermAtScale
          (m : ℤ) (k : ℤ) s p_e q_e p0_e a) ^ 2 +
      σ⁻¹ *
        (Book.Ch05.Section53.WeakNormsMaximizer.fluxAverageTermAtScale
          (m : ℤ) (k : ℤ) t p_e q_e q0_e a) ^ 2
      =
        σ * (∑ n ∈ S, ws n * Real.sqrt (G n)) ^ 2 +
          σ⁻¹ * (∑ n ∈ S, wt n * Real.sqrt (F n)) ^ 2 := by
          simp [Book.Ch05.Section53.WeakNormsMaximizer.gradientAverageTermAtScale,
            Book.Ch05.Section53.WeakNormsMaximizer.fluxAverageTermAtScale, S, ws, wt, G, F,
            p_e, q_e, p0_e, q0_e]
    _ ≤
        (∑ n ∈ S, wβ n) *
          (∑ n ∈ S, wβ n * (σ * G n + σ⁻¹ * F n)) := hpaired_sums
    _ ≤
        (∑ n ∈ S, wβ n) * ∑ n ∈ S, wβ n * H n := hfluct

/-! ## The expectation/stationarity bridge -/

theorem akhc_continuous_toEuclideanCLM {d : ℕ} [NeZero d] :
    Continuous (Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)) := by
  have h := LinearMap.continuous_of_finiteDimensional
    (Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)).toAlgEquiv.toLinearMap
  simpa using h

theorem akhc_continuous_fullBlockNormalizedFluctuation
    {d : ℕ} [NeZero d] (D Abar : FullBlockMat d) :
    Continuous (fun M : FullBlockMat d =>
      ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) (D * (M - Abar) * D)‖ ^ 2) := by
  have hM : Continuous (fun M : FullBlockMat d => D * (M - Abar) * D) := by
    fun_prop
  exact ((akhc_continuous_toEuclideanCLM.comp hM).norm).pow 2

/-- Measurability of the local normalized full-block fluctuation, from the
entrywise measurability of the coarse block matrix at the cutoff law (no
(P2')/(P3') needed, only `hnu`). -/
theorem akhc_aemeasurable_fullBlockNormalizedFluctuationAtScale
    {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ) (P : ProbabilityMeasure (ShellSeq d))
    (m : ℤ) (R : TriadicCube d) :
    AEStronglyMeasurable
      (fun a : RegCoeffField d => akhcFullBlockNormalizedFluctuationAtScale nu L P m R a)
      (cutoffLaw (d := d) nu L P) := by
  have hmat : AEMeasurable
      (fun a : RegCoeffField d => toFullBlockMat (coarseBlockMatrix (cubeSet R) a.toFun))
      (cutoffLaw (d := d) nu L P) := by
    refine AEMeasurable.of_eval ?_
    intro α
    refine AEMeasurable.of_eval ?_
    intro β
    exact aemeasurable_blockMatEntry_cutoffLaw hnu L P R α β
  have hcont :=
    akhc_continuous_fullBlockNormalizedFluctuation
      (Matrix.diagonal (akhcFullBlockInvSqrtDiag nu L P m))
      (toFullBlockMat (annealedBlockMatrix nu L P (cubeSet (originCube d m))))
  exact (hcont.measurable.comp_aemeasurable hmat).aestronglyMeasurable

/-- The local normalized full-block fluctuation is translation-covariant in
its deterministic set argument (the center `Abar` does not depend on `U`). -/
theorem akhc_fullBlockNormalizedFluctuation_translation_covariant
    {d : ℕ} [NeZero d] (nu : ℝ) (L : ℕ) (P : ProbabilityMeasure (ShellSeq d)) (m : ℤ) :
    IsTranslationCovariant
      (fun U : Set (Vec d) => fun a : CoeffField d =>
        akhcFullBlockNormalizedFluctuation nu L P m U a) := by
  intro U z a
  simp [akhcFullBlockNormalizedFluctuation, translateByInt,
    coarseBlockMatrix_translateSet_eq_translateCoeffField]

/-- **Stationarity transport.** Every depth-`(mp - n)` descendant of
`cu_mp` has the same expectation of `akhcFullBlockNormalizedFluctuationAtScale`
as `cu_n`. Uses only `hnu`, `ShellLawPrefix`, `ShellLawJ2` — no (P2')/(P3'). -/
theorem akhc_integral_fullBlockNormalizedFluctuation_eq_originCube_of_mem_descendantsAtScale
    {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ) {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P) (m : ℤ)
    {n mp : ℤ} (hn : 0 ≤ n) (hnm : n ≤ mp)
    {R : TriadicCube d} (hR : R ∈ descendantsAtScale (originCube d mp) n) :
    ∫ a, akhcFullBlockNormalizedFluctuationAtScale nu L P m R a ∂(cutoffLaw (d := d) nu L P) =
      ∫ a, akhcFullBlockNormalizedFluctuationAtScale nu L P m (originCube d n) a
        ∂(cutoffLaw (d := d) nu L P) := by
  have hscale : R.scale = n := Book.Ch04.scale_eq_of_mem_descendantsAtScale_originCube hnm hR
  have hR_nonneg : 0 ≤ R.scale := by simpa [hscale] using hn
  have hshift := Book.Ch04.cubeSet_eq_translateSet_originCube_of_nonneg_scale (R := R) hR_nonneg
  have hstat := restrictionStationaryLaw_cutoffLaw hPrefix hJ2 nu L
  have hmeas := akhc_aemeasurable_fullBlockNormalizedFluctuationAtScale hnu L P m
    (originCube d R.scale)
  have htransfer :
      ∫ a, akhcFullBlockNormalizedFluctuation nu L P m
          (translateSet (intVecToRealVec (Book.Ch04.scaleTranslationShift R.scale R))
            (cubeSet (originCube d R.scale))) a.toFun ∂(cutoffLaw (d := d) nu L P) =
        ∫ a, akhcFullBlockNormalizedFluctuation nu L P m (cubeSet (originCube d R.scale)) a.toFun
          ∂(cutoffLaw (d := d) nu L P) :=
    Book.Ch04.integral_comp_toFun_translation_transfer_of_restrictionStationaryLaw
      (P := cutoffLaw (d := d) nu L P) hstat hmeas
      (akhc_fullBlockNormalizedFluctuation_translation_covariant nu L P m)
      (Book.Ch04.scaleTranslationShift R.scale R)
  calc
    ∫ a, akhcFullBlockNormalizedFluctuationAtScale nu L P m R a ∂(cutoffLaw (d := d) nu L P)
        = ∫ a, akhcFullBlockNormalizedFluctuation nu L P m
            (translateSet (intVecToRealVec (Book.Ch04.scaleTranslationShift R.scale R))
              (cubeSet (originCube d R.scale))) a.toFun ∂(cutoffLaw (d := d) nu L P) := by
          simp only [akhcFullBlockNormalizedFluctuationAtScale]
          rw [hshift]
    _ = ∫ a, akhcFullBlockNormalizedFluctuation nu L P m (cubeSet (originCube d R.scale)) a.toFun
          ∂(cutoffLaw (d := d) nu L P) := htransfer
    _ = ∫ a, akhcFullBlockNormalizedFluctuationAtScale nu L P m (originCube d n) a
          ∂(cutoffLaw (d := d) nu L P) := by
          simp only [akhcFullBlockNormalizedFluctuationAtScale]
          rw [hscale]

/-! ## Assembly: node 16's expectation-level statement -/

theorem akhc_descendantsAverage_eq_of_forall_eq {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    {f : TriadicCube d → ℝ} {c : ℝ} (hf : ∀ R ∈ descendantsAtDepth Q j, f R = c) :
    descendantsAverage Q j f = c := by
  have hne : ((descendantsAtDepth Q j).card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr (descendantsAtDepth_nonempty Q j))
  calc
    descendantsAverage Q j f
        = ((descendantsAtDepth Q j).card : ℝ)⁻¹ * ∑ R ∈ descendantsAtDepth Q j, f R := rfl
    _ = ((descendantsAtDepth Q j).card : ℝ)⁻¹ * ∑ _R ∈ descendantsAtDepth Q j, c := by
        rw [Finset.sum_congr rfl hf]
    _ = c := by
        rw [Finset.sum_const, nsmul_eq_mul]
        field_simp

theorem akhc_integral_descendantsAverage {d : ℕ} {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (Q : TriadicCube d) (j : ℕ) (g : TriadicCube d → α → ℝ)
    (hg : ∀ R ∈ descendantsAtDepth Q j, Integrable (g R) μ) :
    ∫ a, descendantsAverage Q j (fun R => g R a) ∂μ =
      descendantsAverage Q j (fun R => ∫ a, g R a ∂μ) := by
  have hptwise : ∀ a, descendantsAverage Q j (fun R => g R a) =
      ((descendantsAtDepth Q j).card : ℝ)⁻¹ * ∑ R ∈ descendantsAtDepth Q j, g R a :=
    fun _ => rfl
  calc
    ∫ a, descendantsAverage Q j (fun R => g R a) ∂μ
        = ∫ a, ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
            ∑ R ∈ descendantsAtDepth Q j, g R a ∂μ := by
          simp_rw [hptwise]
    _ = ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
          ∑ R ∈ descendantsAtDepth Q j, ∫ a, g R a ∂μ := by
          rw [integral_const_mul,
            integral_finsetSum (descendantsAtDepth Q j) fun R hR => hg R hR]
    _ = descendantsAverage Q j (fun R => ∫ a, g R a ∂μ) := rfl


end

end SuperdiffusionCLT.AKHC61.Response
