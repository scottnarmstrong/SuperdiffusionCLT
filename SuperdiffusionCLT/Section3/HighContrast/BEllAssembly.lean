/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.Section2.Annealed.Integrability
public import SuperdiffusionCLT.Section3.HighContrast.BEllIndependence
public import SuperdiffusionCLT.Section3.HighContrast.BEllLocalization
public import SuperdiffusionCLT.Section3.HighContrast.BEllParameters
public import SuperdiffusionCLT.Section3.HighContrast.RangeDependence

/-!
# The homogenization comparison of the two annealed diagonal blocks

The printed proof of
`l.b.ell.homogenization` compares `shom_l(cu_n)` with `shom_{l,*}(cu_n)` by
inserting an auxiliary cutoff level `k < n`:

* at level `k` the scale separation `n - k >= C_0 log^2(nu^{-1} k)` puts the
  cube `cu_n` beyond the high-contrast entry scale of `a_k`, so
  `shom_k(cu_n) <= (3/2) shom_{k,*}(cu_n)` (`ScaleTransport.lean`);
* the localization lemma at `a = a_k` with the antisymmetric perturbation
  `k_l - k_k` gives the pathwise `bfA_l(cu_n) <= (1 + Dbar) bfA_k(cu_n)`
  (`BEllLocalization.lean`), where `Dbar` reads only the shells `k < r <= l`;
* those shells are independent of the shells `r <= k` that `bfA_k(cu_n)` reads
  (`BEllIndependence.lean`), so the expectation of the product factorizes and
  the pathwise comparison integrates to
  `bfAhom_l(cu_n) <= (1 + E[Dbar]) bfAhom_k(cu_n)`;
* the two diagonal blocks of that block comparison, together with the vanishing
  of the annealed coupling matrix, give the two scalar consequences
  `shom_l(cu_n) <= (1 + E[Dbar]) shom_k(cu_n)` and
  `shom_{k,*}(cu_n) <= (1 + E[Dbar]) shom_{l,*}(cu_n)`;
* `E[Dbar] <= C(d) nu^{-2} (l - k)^2` and `l - k <= C ((l - n) + log^2(nu^{-1} l))`
  turn the product of the three inequalities into the printed conclusion.

## Integrating a block Loewner comparison

The annealed block matrix is the entrywise Bochner integral of the coarse block
matrix, so the doubled quadratic form of the annealed matrix is the expectation
of the doubled quadratic form. Writing that form as the double sum
`sum_{alpha, beta} X_alpha (bfA_{alpha beta}) X_beta` over `BlockCoord d`
reduces the exchange of the integral and the quadratic form to finitely many
scalar identities, and an almost-sure block Loewner comparison between
integrable block observables then passes to the expectations. The right-hand
observable of the localization step carries the random factor `1 + Dbar`, whose
integrability is not automatic: it is the product of two independent integrable
observables, so `IndepFun.integrable_mul` supplies it.

## The range of dependence

The high-contrast entry step consumes `CutoffRangeDependence nu k P`, the
pointwise-restriction lane of the range of dependence, which
`RangeDependence.lean` derives from `ShellRestrictionRangeDependence d P` and
**J2**. That assumption implies **J1**
(`shellLawJ1_of_shellRestrictionRangeDependence`), so the assembled theorem
below is the printed lemma with **J1** replaced by its
restriction-lane strengthening. The restriction `1 <= n` is a correction of the
printed text (see `ERRATA.md`), and `2 <= d` is forced by
the field `two_le_dim` of the parameter record that the entry theorem consumes.

## Main results

* `blockMatLoewnerLE_of_integral`: an almost-sure block Loewner comparison of
  integrable block observables passes to the entrywise expectations.
* `blockMatLoewnerLE_annealedBlockMatrix_cutoff`:
  `bfAhom_l(cu_n) <= (1 + E[Dbar]) bfAhom_k(cu_n)`.
* `sigmaBarScalar_le_mul_sigmaBarScalar_cutoff`,
  `sigmaBarStarScalar_le_mul_sigmaBarStarScalar_cutoff`: the two diagonal
  consequences, and their forms with the explicit multiplier
  `1 + dBarMomentConst d nu^{-2} (l - k)^2`.
* `sigmaBar_le_sigmaBarStar_homogenization_of_shellRestrictionRangeDependence`:
  the assembled comparison.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.HighContrast

open Homogenization MeasureTheory ProbabilityTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## Loewner comparisons and Bochner integrals -/

/-- The doubled matrix of a block matrix reads the same entries. -/
private theorem toFullBlockMat_eq_blockMatEntry (M : BlockMat d)
    (alpha beta : BlockCoord d) :
    toFullBlockMat M alpha beta = blockMatEntry M alpha beta := by
  cases alpha <;> cases beta <;> rfl

/-- The doubled quadratic form as a double sum over the doubled coordinates. -/
theorem blockVecDot_blockMatVecMul_eq_sum (M : BlockMat d) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul M X) =
      ∑ alpha : BlockCoord d, ∑ beta : BlockCoord d,
        toFullBlockVec X alpha * (blockMatEntry M alpha beta * toFullBlockVec X beta) := by
  rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul]
  refine Finset.sum_congr rfl fun alpha _ ↦ ?_
  rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun beta _ ↦ ?_
  rw [toFullBlockMat_eq_blockMatEntry]

/-- The doubled quadratic form of a block observable with integrable entries is
integrable. -/
theorem integrable_blockVecDot_blockMatVecMul {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {A : Omega → BlockMat d}
    (hint : ∀ alpha beta, Integrable (fun w ↦ blockMatEntry (A w) alpha beta) mu)
    (X : BlockVec d) :
    Integrable (fun w ↦ blockVecDot X (blockMatVecMul (A w) X)) mu := by
  have hsum : Integrable (fun w ↦ ∑ alpha : BlockCoord d, ∑ beta : BlockCoord d,
      toFullBlockVec X alpha * (blockMatEntry (A w) alpha beta * toFullBlockVec X beta)) mu :=
    integrable_finsetSum _ fun alpha _ ↦
      integrable_finsetSum _ fun beta _ ↦
        ((hint alpha beta).mul_const (toFullBlockVec X beta)).const_mul
          (toFullBlockVec X alpha)
  exact hsum.congr
    (Filter.Eventually.of_forall fun w ↦ (blockVecDot_blockMatVecMul_eq_sum (A w) X).symm)

/-- The doubled quadratic form of an entrywise expectation is the expectation of
the doubled quadratic form. -/
theorem blockVecDot_blockMatVecMul_integral {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {A : Omega → BlockMat d} {A' : BlockMat d}
    (hint : ∀ alpha beta, Integrable (fun w ↦ blockMatEntry (A w) alpha beta) mu)
    (heq : ∀ alpha beta, blockMatEntry A' alpha beta =
      ∫ w, blockMatEntry (A w) alpha beta ∂mu) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul A' X) =
      ∫ w, blockVecDot X (blockMatVecMul (A w) X) ∂mu := by
  rw [blockVecDot_blockMatVecMul_eq_sum,
    integral_congr_ae (Filter.Eventually.of_forall fun w ↦
      blockVecDot_blockMatVecMul_eq_sum (A w) X)]
  have hrow : ∀ alpha : BlockCoord d, Integrable (fun w ↦ ∑ beta : BlockCoord d,
      toFullBlockVec X alpha * (blockMatEntry (A w) alpha beta * toFullBlockVec X beta)) mu :=
    fun alpha ↦ integrable_finsetSum _ fun beta _ ↦
      ((hint alpha beta).mul_const (toFullBlockVec X beta)).const_mul
        (toFullBlockVec X alpha)
  rw [integral_finsetSum _ fun alpha _ ↦ hrow alpha]
  refine Finset.sum_congr rfl fun alpha _ ↦ ?_
  rw [integral_finsetSum _ fun beta _ ↦
    ((hint alpha beta).mul_const (toFullBlockVec X beta)).const_mul
      (toFullBlockVec X alpha)]
  refine Finset.sum_congr rfl fun beta _ ↦ ?_
  rw [integral_const_mul, integral_mul_const, heq alpha beta]

/-- **An almost-sure block Loewner comparison passes to the entrywise
expectations.** -/
theorem blockMatLoewnerLE_of_integral {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {A B : Omega → BlockMat d} {A' B' : BlockMat d}
    (hAint : ∀ alpha beta, Integrable (fun w ↦ blockMatEntry (A w) alpha beta) mu)
    (hBint : ∀ alpha beta, Integrable (fun w ↦ blockMatEntry (B w) alpha beta) mu)
    (hA : ∀ alpha beta, blockMatEntry A' alpha beta =
      ∫ w, blockMatEntry (A w) alpha beta ∂mu)
    (hB : ∀ alpha beta, blockMatEntry B' alpha beta =
      ∫ w, blockMatEntry (B w) alpha beta ∂mu)
    (h : ∀ᵐ w ∂mu, BlockMatLoewnerLE (A w) (B w)) :
    BlockMatLoewnerLE A' B' := by
  intro X
  rw [blockVecDot_blockMatVecMul_integral hAint hA X,
    blockVecDot_blockMatVecMul_integral hBint hB X]
  have hmono : ∫ w, blockVecDot X (blockMatVecMul (A w) X) ∂mu ≤
      ∫ w, blockVecDot X (blockMatVecMul (B w) X) ∂mu := by
    refine integral_mono_ae (integrable_blockVecDot_blockMatVecMul hAint X)
      (integrable_blockVecDot_blockMatVecMul hBint X) ?_
    filter_upwards [h] with w hw
    linarith only [hw X]
  linarith only [hmono]

/-- **The product of two independent integrable observables is integrable.**
The companion of `integral_mul_of_indep_of_measurable`. -/
theorem integrable_mul_of_indep_of_measurable {Omega : Type*}
    {m1 m2 mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    (hindep : Indep m1 m2 mu) {X Y : Omega → ℝ}
    (hX : Measurable[m1] X) (hY : Measurable[m2] Y)
    (hXint : Integrable X mu) (hYint : Integrable Y mu) :
    Integrable (fun omega ↦ X omega * Y omega) mu := by
  have hXY : IndepFun X Y mu :=
    (IndepFun_iff_Indep X Y mu).2
      (indep_of_indep_of_le_right (indep_of_indep_of_le_left hindep hX.comap_le) hY.comap_le)
  exact hXY.integrable_mul hXint hYint

/-! ## The annealed comparison of the two cutoff levels -/

section Annealed

variable [NeZero d] {nu : ℝ} {k l n : ℕ} {P : ProbabilityMeasure (ShellSeq d)}

/-- The expectation of the localization multiplier. -/
theorem integral_one_add_DBar (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (hkn : k < n) (hnl : n ≤ l) :
    ∫ omega, (1 + DBar (d := d) nu k l n omega) ∂P.toMeasure =
      1 + ∫ omega, DBar (d := d) nu k l n omega ∂P.toMeasure := by
  rw [integral_add (integrable_const 1) (integrable_DBar hPrefix hJ2 hJ3 hJ4 hkn hnl)]
  simp

/-- **The annealed block comparison**:
`bfAhom_l(cu_n) <= (1 + E[Dbar]) bfAhom_k(cu_n)`. The pathwise comparison of the
localization step is integrated blockwise, and the random multiplier leaves the
expectation as `1 + E[Dbar]` because it reads only the shells `k < r <= l`,
which are independent of the shells `r <= k` read by `bfA_k(cu_n)`. -/
theorem blockMatLoewnerLE_annealedBlockMatrix_cutoff (hnu : 0 < nu)
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (hkn : k < n) (hnl : n ≤ l) :
    BlockMatLoewnerLE (annealedBlockMatrix nu l P (cubeSet (originCube d (n : ℤ))))
      ((1 + ∫ omega, DBar (d := d) nu k l n omega ∂P.toMeasure) •
        annealedBlockMatrix nu k P (cubeSet (originCube d (n : ℤ)))) := by
  have hkl : k ≤ l := le_trans hkn.le hnl
  have hYmeas : Measurable[indexSigma (fun F : ShellSeq d ↦ F) (Set.Ioc k l)]
      (fun omega : ShellSeq d ↦ 1 + DBar (d := d) nu k l n omega) :=
    measurable_const.add (measurable_DBar_indexSigma k l n)
  have hYint : Integrable (fun omega : ShellSeq d ↦ 1 + DBar (d := d) nu k l n omega)
      P.toMeasure := (integrable_const 1).add (integrable_DBar hPrefix hJ2 hJ3 hJ4 hkn hnl)
  refine blockMatLoewnerLE_of_integral
    (A := fun omega ↦ coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
      (coefficientCutoff nu omega l).toFun)
    (B := fun omega ↦ (1 + DBar (d := d) nu k l n omega) •
      coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
        (coefficientCutoff nu omega k).toFun)
    (fun alpha beta ↦ integrable_blockMatEntry_coarseBlockMatrix hnu l
      (originCube d (n : ℤ)) hPrefix hJ2 hJ3 hJ4 alpha beta)
    (fun alpha beta ↦ ?_)
    (fun alpha beta ↦ blockMatEntry_annealedBlockMatrix nu l P _ alpha beta)
    (fun alpha beta ↦ ?_)
    (Filter.Eventually.of_forall fun omega ↦
      blockMatLoewnerLE_coarseBlockMatrix_coefficientCutoff_add hnu omega hkl)
  · refine (integrable_mul_of_indep_of_measurable
      (indep_indexSigma_Iic_Ioc hJ2 k l).symm hYmeas
      (measurable_blockMatEntry_coarseBlockMatrix_coefficientCutoff_indexSigma hnu k
        (originCube d (n : ℤ)) alpha beta) hYint
      (integrable_blockMatEntry_coarseBlockMatrix hnu k (originCube d (n : ℤ))
        hPrefix hJ2 hJ3 hJ4 alpha beta)).congr ?_
    exact Filter.Eventually.of_forall fun omega ↦ (blockMatEntry_smul _ _ alpha beta).symm
  · rw [← integral_one_add_DBar hPrefix hJ2 hJ3 hJ4 hkn hnl]
    exact (blockMatEntry_integral_smul_coarseBlockMatrix_coefficientCutoff hnu hJ2
      (originCube d (n : ℤ)) hYmeas alpha beta).symm

/-! ## The two diagonal consequences -/

/-- The upper-left block of a block Loewner comparison between the two annealed
matrices at the cube `cu_n`, read as a scalar inequality. -/
theorem sigmaBarScalar_le_mul_of_blockMatLoewnerLE (hnu : 0 < nu) (hJ4 : ShellLawJ4 d P)
    {E : ℝ}
    (h : BlockMatLoewnerLE (annealedBlockMatrix nu l P (cubeSet (originCube d (n : ℤ))))
      (E • annealedBlockMatrix nu k P (cubeSet (originCube d (n : ℤ))))) :
    sigmaBarScalar nu l P (cubeSet (originCube d (n : ℤ))) ≤
      E * sigmaBarScalar nu k P (cubeSet (originCube d (n : ℤ))) := by
  have hUL := Book.Ch04.matLoewnerLE_upperLeft_of_blockMatLoewnerLE h
  rw [Homogenization.blockSMul_upperLeft,
    annealedBlockMatrix_originCube_upperLeft_eq_sigmaBar hnu l hJ4 (n : ℤ),
    annealedBlockMatrix_originCube_upperLeft_eq_sigmaBar hnu k hJ4 (n : ℤ)] at hUL
  have h0 := diag_le_of_matLoewnerLE hUL 0
  simp only [Matrix.smul_apply, smul_eq_mul] at h0
  simpa only [sigmaBarScalar] using h0

/-- The lower-right block of the same comparison, read as a scalar inequality
between the two annealed inverse diffusivities. -/
theorem sigmaBarStarInvScalar_le_mul_of_blockMatLoewnerLE {E : ℝ}
    (h : BlockMatLoewnerLE (annealedBlockMatrix nu l P (cubeSet (originCube d (n : ℤ))))
      (E • annealedBlockMatrix nu k P (cubeSet (originCube d (n : ℤ))))) :
    sigmaBarStarInvScalar nu l P (cubeSet (originCube d (n : ℤ))) ≤
      E * sigmaBarStarInvScalar nu k P (cubeSet (originCube d (n : ℤ))) := by
  have hLR := Book.Ch04.matLoewnerLE_lowerRight_of_blockMatLoewnerLE h
  rw [Homogenization.blockSMul_lowerRight] at hLR
  have h0 := diag_le_of_matLoewnerLE hLR 0
  simp only [Matrix.smul_apply, smul_eq_mul] at h0
  simpa only [sigmaBarStarInvScalar, sigmaBarStarInv] using h0

/-- **The upper-left consequence of the block comparison**:
`shom_l(cu_n) <= (1 + E[Dbar]) shom_k(cu_n)`. -/
theorem sigmaBarScalar_le_mul_sigmaBarScalar_cutoff (hnu : 0 < nu)
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (hkn : k < n) (hnl : n ≤ l) :
    sigmaBarScalar nu l P (cubeSet (originCube d (n : ℤ))) ≤
      (1 + ∫ omega, DBar (d := d) nu k l n omega ∂P.toMeasure) *
        sigmaBarScalar nu k P (cubeSet (originCube d (n : ℤ))) :=
  sigmaBarScalar_le_mul_of_blockMatLoewnerLE hnu hJ4
    (blockMatLoewnerLE_annealedBlockMatrix_cutoff hnu hPrefix hJ2 hJ3 hJ4 hkn hnl)

/-- **The lower-right consequence of the block comparison**, after inverting the two
positive scalars: `shom_{k,*}(cu_n) <= (1 + E[Dbar]) shom_{l,*}(cu_n)`. -/
theorem sigmaBarStarScalar_le_mul_sigmaBarStarScalar_cutoff (hnu : 0 < nu)
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (hkn : k < n) (hnl : n ≤ l) :
    sigmaBarStarScalar nu k P (cubeSet (originCube d (n : ℤ))) ≤
      (1 + ∫ omega, DBar (d := d) nu k l n omega ∂P.toMeasure) *
        sigmaBarStarScalar nu l P (cubeSet (originCube d (n : ℤ))) := by
  have hk := sigmaBarStarInvScalar_pos_cutoff hnu k hPrefix hJ2 hJ3 hJ4 (n : ℤ)
  have hl := sigmaBarStarInvScalar_pos_cutoff hnu l hPrefix hJ2 hJ3 hJ4 (n : ℤ)
  have hcmp := sigmaBarStarInvScalar_le_mul_of_blockMatLoewnerLE
    (blockMatLoewnerLE_annealedBlockMatrix_cutoff hnu hPrefix hJ2 hJ3 hJ4 hkn hnl)
  rw [sigmaBarStarScalar_eq_inv hnu k hJ4 (n : ℤ) hk,
    sigmaBarStarScalar_eq_inv hnu l hJ4 (n : ℤ) hl, ← one_div, ← one_div,
    mul_one_div, div_le_div_iff₀ hk hl]
  linarith only [hcmp]

/-! ## The explicit multiplier -/

/-- The localization multiplier is bounded by an explicit dimensional
polynomial in `nu^{-1}` and `l - k`. -/
theorem one_add_integral_DBar_le (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (hkn : k < n) (hnl : n ≤ l) :
    1 + ∫ omega, DBar (d := d) nu k l n omega ∂P.toMeasure ≤
      1 + dBarMomentConst d * nu⁻¹ ^ 2 * (((l - k : ℕ) : ℝ)) ^ 2 := by
  have h := integral_DBar_le (n := n) hnu hnu1 hPrefix hJ2 hJ3 hJ4 hkn hnl
  linarith only [h]

/-- `shom_l(cu_n) <= (1 + C(d) nu^{-2} (l - k)^2) shom_k(cu_n)`. -/
theorem sigmaBarScalar_le_mul_sigmaBarScalar_dBarMomentConst (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (hkn : k < n) (hnl : n ≤ l) :
    sigmaBarScalar nu l P (cubeSet (originCube d (n : ℤ))) ≤
      (1 + dBarMomentConst d * nu⁻¹ ^ 2 * (((l - k : ℕ) : ℝ)) ^ 2) *
        sigmaBarScalar nu k P (cubeSet (originCube d (n : ℤ))) := by
  have hpos := sigmaBarScalar_originCube_pos hnu k hPrefix hJ2 hJ3 hJ4 (n : ℤ)
  have hstep := sigmaBarScalar_le_mul_sigmaBarScalar_cutoff hnu hPrefix hJ2 hJ3 hJ4 hkn hnl
  have hmul := mul_le_mul_of_nonneg_right
    (one_add_integral_DBar_le hnu hnu1 hPrefix hJ2 hJ3 hJ4 hkn hnl) hpos.le
  linarith only [hstep, hmul]

/-- `shom_{k,*}(cu_n) <= (1 + C(d) nu^{-2} (l - k)^2) shom_{l,*}(cu_n)`. -/
theorem sigmaBarStarScalar_le_mul_sigmaBarStarScalar_dBarMomentConst (hnu : 0 < nu)
    (hnu1 : nu ≤ 1) (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (hkn : k < n) (hnl : n ≤ l) :
    sigmaBarStarScalar nu k P (cubeSet (originCube d (n : ℤ))) ≤
      (1 + dBarMomentConst d * nu⁻¹ ^ 2 * (((l - k : ℕ) : ℝ)) ^ 2) *
        sigmaBarStarScalar nu l P (cubeSet (originCube d (n : ℤ))) := by
  have hpos := sigmaBarStarScalar_pos hnu l hPrefix hJ2 hJ3 hJ4 (n : ℤ)
  have hstep :=
    sigmaBarStarScalar_le_mul_sigmaBarStarScalar_cutoff hnu hPrefix hJ2 hJ3 hJ4 hkn hnl
  have hmul := mul_le_mul_of_nonneg_right
    (one_add_integral_DBar_le hnu hnu1 hPrefix hJ2 hJ3 hJ4 hkn hnl) hpos.le
  linarith only [hstep, hmul]

end Annealed

/-! ## The assembled comparison -/

/-- The threshold constant of the high-contrast entry step is positive. -/
private theorem entryScaleLogSqConst_pos (xi : ℕ) {C sigma : ℝ} (hC : 0 < C) :
    0 < entryScaleLogSqConst xi C sigma := by
  have hlog : (0 : ℝ) ≤ Real.log (2 + sigma⁻¹ ^ (4 : ℕ) * (xi : ℝ)) := by
    refine Real.log_nonneg ?_
    have h : (0 : ℝ) ≤ sigma⁻¹ ^ (4 : ℕ) * (xi : ℝ) := by positivity
    linarith only [h]
  have hpre : (0 : ℝ) ≤ C * (xi : ℝ) * sigma⁻¹ ^ (4 : ℕ) * |Real.log sigma| :=
    mul_nonneg (mul_nonneg (mul_nonneg hC.le (Nat.cast_nonneg _)) (by positivity))
      (abs_nonneg _)
  have hfac : (0 : ℝ) ≤ 4 * Real.log (2 + sigma⁻¹ ^ (4 : ℕ) * (xi : ℝ)) + 2 := by
    linarith only [hlog]
  have hterm := mul_nonneg hpre hfac
  rw [entryScaleLogSqConst]
  linarith only [hC, hterm]

/-- The negative fourth real power of a positive diffusivity is the fourth
natural power of its inverse. -/
private theorem rpow_neg_four_eq_inv_pow {nu : ℝ} (hnu : 0 < nu) :
    nu ^ (-(4 : ℝ)) = nu⁻¹ ^ (4 : ℕ) := by
  have h4 : nu ^ (4 : ℝ) = nu ^ (4 : ℕ) := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [Real.rpow_neg hnu.le, h4, ← inv_pow]

/-- **`l.b.ell.homogenization` under the restriction-lane range of
dependence**. There is `C(d) > 0` such that for `nu in (0,1]`, `1 <= n`,
`n >= C log^2(nu^{-1} L)` and `n < l <= L`,

`shom_l(cu_n) <= C nu^{-4} ((l - n) + log^2(nu^{-1} l))^4 shom_{l,*}(cu_n)`,

with `C` chosen before the diffusivity and the shell law.

Three points where this differs from the printed hypothesis list. **J1**
is replaced by `ShellRestrictionRangeDependence d P`, the
pointwise-restriction lane of the same printed statement, which implies it
(`shellLawJ1_of_shellRestrictionRangeDependence`) and is what the high-contrast
entry step consumes. The restriction `1 <= n` is a correction of the printed
text (see `ERRATA.md`): the printed argument does
not cover `nu = 1, L = 1, n = 0, l = 1`. The dimension condition `2 <= d` is the
standing dimension condition of the paper (the printed lemma mentions only `C_0(d)`),
carried by the field `two_le_dim` of the
parameter record of the high-contrast entry theorem. -/
theorem sigmaBar_le_sigmaBarStar_homogenization_of_shellRestrictionRangeDependence
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ P : ProbabilityMeasure (ShellSeq d),
          ShellLawPrefix d P →
          ShellRestrictionRangeDependence d P →
          ShellLawJ2 d P →
          ShellLawJ3 d P →
          ShellLawJ4 d P →
          ∀ n L : ℕ, 1 ≤ n → C * Real.log (nu⁻¹ * (L : ℝ)) ^ 2 ≤ (n : ℝ) →
            ∀ l : ℕ, n < l → l ≤ L →
              sigmaBarScalar nu l P (cubeSet (originCube d (n : ℤ))) ≤
                C * nu ^ (-(4 : ℝ)) *
                    (((l - n : ℕ) : ℝ) + Real.log (nu⁻¹ * (l : ℝ)) ^ 2) ^ 4 *
                  sigmaBarStarScalar nu l P (cubeSet (originCube d (n : ℤ))) := by
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hc0 : 0 < dBarMomentConst d := dBarMomentConst_pos hd0
  obtain ⟨Ce, hCe, hentry⟩ :=
    sigmaBarScalar_le_mul_sigmaBarStarScalar_of_logSq_le (canonicalParams d hd)
  set xi : ℕ := (canonicalParams d hd).xi with hxidef
  have hC0 : 0 < entryScaleLogSqConst xi Ce (1 / 2 : ℝ) := entryScaleLogSqConst_pos xi hCe
  obtain ⟨Cm, hCm, hsep⟩ := exists_scaleSeparation d xi hC0
  set K : ℝ := 1 + dBarMomentConst d * Cm ^ 2 with hKdef
  have hK1 : (1 : ℝ) ≤ K := by
    have hnn : (0 : ℝ) ≤ dBarMomentConst d * Cm ^ 2 := by positivity
    linarith only [hnn]
  refine ⟨max Cm (3 / 2 * K ^ 2), lt_of_lt_of_le hCm (le_max_left _ _), ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1R hJ2 hJ3 hJ4 n L hn1 hnL l hnl hlL
  have hCmle : Cm * Real.log (nu⁻¹ * (L : ℝ)) ^ 2 ≤ (n : ℝ) := by
    have hstep := mul_le_mul_of_nonneg_right (le_max_left Cm (3 / 2 * K ^ 2))
      (sq_nonneg (Real.log (nu⁻¹ * (L : ℝ))))
    linarith only [hstep, hnL]
  have hL2 : 2 ≤ L := by omega
  obtain ⟨k, hkn, hthr, hlk⟩ := hsep nu hnu hnu1 n L hCmle l hnl hlL hL2
  have hoff : (triadicOffset d : ℝ) ≤ ((n - k : ℕ) : ℝ) := by
    have hnn : (0 : ℝ) ≤ entryScaleLogSqConst xi Ce (1 / 2 : ℝ) *
        Real.log (2 + cutoffContrastBound d xi nu k) ^ (2 : ℕ) :=
      mul_nonneg hC0.le (sq_nonneg _)
    linarith only [hthr, hnn]
  have hoffN : triadicOffset d ≤ n - k := Nat.cast_le.mp hoff
  set j : ℕ := n - k - triadicOffset d with hjdef
  have hjeq : k + triadicOffset d + j = n := by omega
  have hjcast : (j : ℝ) = ((n - k : ℕ) : ℝ) - (triadicOffset d : ℝ) := by
    rw [hjdef, Nat.cast_sub hoffN]
  have hjthr : entryScaleLogSqConst xi Ce (1 / 2 : ℝ) *
      Real.log (2 + cutoffContrastBound d xi nu k) ^ (2 : ℕ) ≤ (j : ℝ) := by
    rw [hjcast]
    linarith only [hthr]
  have hrange : CutoffRangeDependence nu k P :=
    cutoffRangeDependence_of_shellRestrictionRangeDependence hJ2 hJ1R nu k
  have hS3 := hentry nu hnu k P hPrefix hJ2 hJ3 hJ4 hrange (1 / 2 : ℝ) (by norm_num)
    le_rfl j hjthr
  rw [hjeq] at hS3
  have hS6a := sigmaBarScalar_le_mul_sigmaBarScalar_dBarMomentConst (n := n) hnu hnu1
    hPrefix hJ2 hJ3 hJ4 hkn hnl.le
  have hS6b := sigmaBarStarScalar_le_mul_sigmaBarStarScalar_dBarMomentConst (n := n) hnu hnu1
    hPrefix hJ2 hJ3 hJ4 hkn hnl.le
  set M : ℝ := 1 + dBarMomentConst d * nu⁻¹ ^ 2 * (((l - k : ℕ) : ℝ)) ^ 2 with hMdef
  set S : ℝ := ((l - n : ℕ) : ℝ) + Real.log (nu⁻¹ * (l : ℝ)) ^ 2 with hSdef
  have hM1 : (1 : ℝ) ≤ M := by
    have hnn : (0 : ℝ) ≤ dBarMomentConst d * nu⁻¹ ^ 2 * (((l - k : ℕ) : ℝ)) ^ 2 := by
      positivity
    linarith only [hnn]
  have hnuinv : (1 : ℝ) ≤ nu⁻¹ := one_le_inv_iff₀.mpr ⟨hnu, hnu1⟩
  have hS1 : (1 : ℝ) ≤ S := by
    have h1 : (1 : ℝ) ≤ ((l - n : ℕ) : ℝ) := by
      have hln : 1 ≤ l - n := by omega
      exact_mod_cast hln
    have h2 : (0 : ℝ) ≤ Real.log (nu⁻¹ * (l : ℝ)) ^ 2 := sq_nonneg _
    rw [hSdef]
    linarith only [h1, h2]
  have hT1 : (1 : ℝ) ≤ nu⁻¹ ^ 2 * S ^ 2 := by
    have ha : (1 : ℝ) ≤ nu⁻¹ ^ 2 := one_le_pow₀ hnuinv
    have hb : (1 : ℝ) ≤ S ^ 2 := one_le_pow₀ hS1
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ nu⁻¹ ^ 2 * S ^ 2 := mul_le_mul ha hb zero_le_one (by positivity)
  have hMKT : M ≤ K * (nu⁻¹ ^ 2 * S ^ 2) := by
    have hq : (((l - k : ℕ) : ℝ)) ^ 2 ≤ Cm ^ 2 * S ^ 2 := by
      calc (((l - k : ℕ) : ℝ)) ^ 2 ≤ (Cm * S) ^ 2 :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) hlk 2
        _ = Cm ^ 2 * S ^ 2 := by ring
    have hcnu : (0 : ℝ) ≤ dBarMomentConst d * nu⁻¹ ^ 2 := by positivity
    have h2 : dBarMomentConst d * nu⁻¹ ^ 2 * (((l - k : ℕ) : ℝ)) ^ 2 ≤
        dBarMomentConst d * Cm ^ 2 * (nu⁻¹ ^ 2 * S ^ 2) := by
      calc dBarMomentConst d * nu⁻¹ ^ 2 * (((l - k : ℕ) : ℝ)) ^ 2
          ≤ dBarMomentConst d * nu⁻¹ ^ 2 * (Cm ^ 2 * S ^ 2) :=
            mul_le_mul_of_nonneg_left hq hcnu
        _ = dBarMomentConst d * Cm ^ 2 * (nu⁻¹ ^ 2 * S ^ 2) := by ring
    calc M = 1 + dBarMomentConst d * nu⁻¹ ^ 2 * (((l - k : ℕ) : ℝ)) ^ 2 := hMdef
      _ ≤ nu⁻¹ ^ 2 * S ^ 2 + dBarMomentConst d * Cm ^ 2 * (nu⁻¹ ^ 2 * S ^ 2) := by
          linarith only [h2, hT1]
      _ = K * (nu⁻¹ ^ 2 * S ^ 2) := by rw [hKdef]; ring
  have hAs : 0 < sigmaBarStarScalar nu l P (cubeSet (originCube d (n : ℤ))) :=
    sigmaBarStarScalar_pos hnu l hPrefix hJ2 hJ3 hJ4 (n : ℤ)
  have hM0 : (0 : ℝ) ≤ M := le_trans zero_le_one hM1
  have hchain : sigmaBarScalar nu l P (cubeSet (originCube d (n : ℤ))) ≤
      3 / 2 * M ^ 2 * sigmaBarStarScalar nu l P (cubeSet (originCube d (n : ℤ))) := by
    have h1 : M * sigmaBarScalar nu k P (cubeSet (originCube d (n : ℤ))) ≤
        M * (3 / 2 * sigmaBarStarScalar nu k P (cubeSet (originCube d (n : ℤ)))) := by
      refine mul_le_mul_of_nonneg_left ?_ hM0
      linarith only [hS3]
    have h2 : M * (3 / 2 * sigmaBarStarScalar nu k P (cubeSet (originCube d (n : ℤ)))) ≤
        M * (3 / 2 * (M * sigmaBarStarScalar nu l P (cubeSet (originCube d (n : ℤ))))) := by
      refine mul_le_mul_of_nonneg_left ?_ hM0
      linarith only [hS6b]
    have h3 : M * (3 / 2 * (M * sigmaBarStarScalar nu l P (cubeSet (originCube d (n : ℤ))))) =
        3 / 2 * M ^ 2 * sigmaBarStarScalar nu l P (cubeSet (originCube d (n : ℤ))) := by ring
    linarith only [hS6a, h1, h2, h3]
  have hMsq : M ^ 2 ≤ K ^ 2 * (nu⁻¹ ^ 4 * S ^ 4) := by
    calc M ^ 2 ≤ (K * (nu⁻¹ ^ 2 * S ^ 2)) ^ 2 := pow_le_pow_left₀ hM0 hMKT 2
      _ = K ^ 2 * (nu⁻¹ ^ 4 * S ^ 4) := by ring
  have hfinal : 3 / 2 * M ^ 2 ≤ max Cm (3 / 2 * K ^ 2) * nu⁻¹ ^ 4 * S ^ 4 := by
    have hpos : (0 : ℝ) ≤ nu⁻¹ ^ 4 * S ^ 4 := by positivity
    calc 3 / 2 * M ^ 2 ≤ 3 / 2 * (K ^ 2 * (nu⁻¹ ^ 4 * S ^ 4)) := by linarith only [hMsq]
      _ = 3 / 2 * K ^ 2 * (nu⁻¹ ^ 4 * S ^ 4) := by ring
      _ ≤ max Cm (3 / 2 * K ^ 2) * (nu⁻¹ ^ 4 * S ^ 4) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hpos
      _ = max Cm (3 / 2 * K ^ 2) * nu⁻¹ ^ 4 * S ^ 4 := by ring
  rw [rpow_neg_four_eq_inv_pow hnu]
  calc sigmaBarScalar nu l P (cubeSet (originCube d (n : ℤ)))
      ≤ 3 / 2 * M ^ 2 * sigmaBarStarScalar nu l P (cubeSet (originCube d (n : ℤ))) := hchain
    _ ≤ max Cm (3 / 2 * K ^ 2) * nu⁻¹ ^ 4 * S ^ 4 *
          sigmaBarStarScalar nu l P (cubeSet (originCube d (n : ℤ))) :=
        mul_le_mul_of_nonneg_right hfinal hAs.le

end

end SuperdiffusionCLT.Section3.HighContrast
