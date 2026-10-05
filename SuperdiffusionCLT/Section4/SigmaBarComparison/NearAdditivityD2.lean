/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.SigmaBarComparison.NearAdditivityD

/-!
# Near-additivity, the expectation identity

Taking expectations in `sbNear_pointwise_identity` (`NearAdditivityD.lean`):
the annealed `sigmaBarSeq` at the origin cube is the expectation of the raw
upper-left entry (`annealedBlockMatrix_originCube_upperLeft_eq_sigmaBar`: under
`ShellLawJ4` the annealed Schur correction vanishes), both cross
terms have zero expectation (`a.j.indy` + `a.j.iso`), so

`sigmaBarSeq_L(n) - sigmaBarSeq_ell(n) - E[quad] - E[cross] = E[Err]`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.SigmaBarComparison

open MeasureTheory Homogenization Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The printed cross term, written with the lower-left block only. -/
theorem sbNear_crossRaw_eq (nu : ℝ) (ell L n : ℕ) (omega : ShellSeq d) :
    sbNear_crossRaw nu ell L n omega =
      -(2 * ∑ k : Fin d, sbIndep_kcgMat (d := d) nu ell n omega k 0 *
        sbIndep_hMat (d := d) ell L n omega k 0) := by
  have hUR : ∀ l : Fin d, (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
      (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega ell).toFun).upperRight
        0 l = sbIndep_kcgMat (d := d) nu ell n omega l 0 := by
    intro l
    rw [coarseBlockMatrix_upperRight_eq_transpose_lowerLeft]
    rfl
  have hcomm : (∑ k : Fin d, sbIndep_hMat (d := d) ell L n omega k 0 *
      sbIndep_kcgMat (d := d) nu ell n omega k 0) = ∑ k : Fin d,
        sbIndep_kcgMat (d := d) nu ell n omega k 0 * sbIndep_hMat (d := d) ell L n omega k 0 :=
    Finset.sum_congr rfl fun k _ => mul_comm _ _
  simp only [sbNear_crossRaw, hUR]
  rw [hcomm]
  ring

omit [NeZero d] in
private theorem sbNear_one_le_cutoffBlockEntryBound {nu : ℝ} (hnu : 0 < nu)
    (omega : ShellSeq d) (m : ℕ) (Q : TriadicCube d) :
    (1 : ℝ) ≤ cutoffBlockEntryBound nu omega m Q := by
  unfold cutoffBlockEntryBound
  have havg : 0 ≤ volumeAverage (openCubeSet Q)
      (fun x ↦ matrixOperatorNorm
        ((SuperdiffusionCLT.Frozen.Section2.streamCutoff omega m).toFun x) ^ 2) := by
    unfold volumeAverage
    exact mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
      (integral_nonneg fun x => sq_nonneg _)
  have hinv : 0 < nu⁻¹ := inv_pos.mpr hnu
  have h2 : 0 ≤ 2 * nu⁻¹ * volumeAverage (openCubeSet Q)
      (fun x ↦ matrixOperatorNorm
        ((SuperdiffusionCLT.Frozen.Section2.streamCutoff omega m).toFun x) ^ 2) :=
    mul_nonneg (mul_nonneg (by norm_num) hinv.le) havg
  rcases le_or_gt 1 nu with h1 | h1
  · linarith only [h1, h2, hinv]
  · have : 1 < nu⁻¹ := one_lt_inv₀ hnu |>.mpr h1
    linarith only [this, h2, hnu]

theorem sbNear_integrable_kcg_mul_hMat {P : ProbabilityMeasure (ShellSeq d)} {nu : ℝ}
    (hnu : 0 < nu) (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) {ell L : ℕ} (hellL : ell < L) (n : ℕ) (k : Fin d) :
    Integrable (fun omega => sbIndep_kcgMat (d := d) nu ell n omega k 0 *
      sbIndep_hMat (d := d) ell L n omega k 0) P.toMeasure := by
  have h := sbIndep_integrable_envelope_mul_envelope_mul_hMat hnu hPrefix hJ2 hJ3 hJ4 hellL n k
    (fun omega => sbIndep_kcgMat (d := d) nu ell n omega k 0) (fun _ => (1 : ℝ))
    (SuperdiffusionCLT.Section2.Annealed.measurable_blockMatEntry_coarseBlockMatrix
      hnu ell (originCube d (n : ℤ)) (Sum.inr k) (Sum.inl 0))
    measurable_const
    (fun omega => SuperdiffusionCLT.Section2.Annealed.abs_blockMatEntry_coarseBlockMatrix_le
      hnu omega ell (originCube d (n : ℤ)) (Sum.inr k) (Sum.inl 0))
    (fun omega => by
      rw [abs_one]
      exact sbNear_one_le_cutoffBlockEntryBound hnu omega ell (originCube d (n : ℤ)))
  simpa only [mul_one] using h

omit [NeZero d] in
/-- `kcg_ell(cu_n)` is measurable with respect to the shells `≤ ell`. -/
theorem sbNear_stronglyMeasurable_kcg {nu : ℝ} (hnu : 0 < nu) (ell n : ℕ) (k l : Fin d) :
    StronglyMeasurable[SuperdiffusionCLT.Probability.shellSigma (d := d)
      (SuperdiffusionCLT.Section2.Localization.localizationLowerShells ell)]
      (fun omega => sbIndep_kcgMat (d := d) nu ell n omega k l) :=
  (SuperdiffusionCLT.Section2.Localization.measurable_SS_coarseBlockMatrix_lowerLeft
    hnu (originCube d (n : ℤ)) k l).stronglyMeasurable

/-- **The printed cross term has zero expectation** (`a.j.indy` + `a.j.iso`). -/
theorem sbNear_integral_crossRaw_eq_zero {P : ProbabilityMeasure (ShellSeq d)} {nu : ℝ}
    (hnu : 0 < nu) (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) {ell L : ℕ} (hellL : ell < L) (n : ℕ) :
    ∫ omega, sbNear_crossRaw nu ell L n omega ∂P.toMeasure = 0 := by
  have hterm : ∀ k : Fin d, ∫ omega, sbIndep_kcgMat (d := d) nu ell n omega k 0 *
      sbIndep_hMat (d := d) ell L n omega k 0 ∂P.toMeasure = 0 := by
    intro k
    have h := sbIndep_integral_mul_eq_mul_integral (d := d)
      (SuperdiffusionCLT.Section2.Localization.localizationUpperShells_disjoint_lowerShells
        ell).symm hJ2 (sbNear_stronglyMeasurable_kcg hnu ell n k 0)
      (sbIndep_stronglyMeasurable_hMat_entry ell L n k 0)
      (sbIndep_integrable_hMat_entry hPrefix hJ2 hJ3 hJ4 hellL n k)
      (sbNear_integrable_kcg_mul_hMat hnu hPrefix hJ2 hJ3 hJ4 hellL n k)
    rw [h, sbIndep_integral_hMat_entry_eq_zero hJ4 ell L n k 0, mul_zero]
  simp only [sbNear_crossRaw_eq]
  rw [integral_neg, integral_const_mul,
    integral_finsetSum Finset.univ fun k _ =>
      sbNear_integrable_kcg_mul_hMat hnu hPrefix hJ2 hJ3 hJ4 hellL n k,
    Finset.sum_eq_zero fun k _ => hterm k, mul_zero, neg_zero]

/-- **This development's cross term has zero expectation**: the same argument
as in `sbIndep_integral_crossTerm_eq_zero`, with all carriers discharged. -/
theorem sbNear_integral_crossTerm_eq_zero {P : ProbabilityMeasure (ShellSeq d)} {nu : ℝ}
    (hnu : 0 < nu) (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) {ell L : ℕ} (hellL : ell < L) (n : ℕ) :
    ∫ omega, sbIndep_crossTerm (d := d) nu ell L n omega ∂P.toMeasure = 0 := by
  refine sbIndep_integral_crossTerm_eq_zero hPrefix hJ2 hJ3 hJ4 nu hellL n
    (fun k l => ⟨sbNear_stronglyMeasurable_kcg hnu ell n k l,
      (SuperdiffusionCLT.Section2.Localization.measurable_SS_coarseBlockMatrix_lowerRight
        hnu (originCube d (n : ℤ)) k l).stronglyMeasurable⟩) (fun k l => ?_) (fun k l => ?_)
  · exact sbIndep_integrable_envelope_mul_envelope_mul_hMat hnu hPrefix hJ2 hJ3 hJ4 hellL n l
      (fun omega => sbIndep_kcgMat (d := d) nu ell n omega k 0)
      (fun omega => sbIndep_sInvMat (d := d) nu ell n omega k l)
      (SuperdiffusionCLT.Section2.Annealed.measurable_blockMatEntry_coarseBlockMatrix
        hnu ell (originCube d (n : ℤ)) (Sum.inr k) (Sum.inl 0))
      (SuperdiffusionCLT.Section2.Annealed.measurable_blockMatEntry_coarseBlockMatrix
        hnu ell (originCube d (n : ℤ)) (Sum.inr k) (Sum.inr l))
      (fun omega => SuperdiffusionCLT.Section2.Annealed.abs_blockMatEntry_coarseBlockMatrix_le
        hnu omega ell (originCube d (n : ℤ)) (Sum.inr k) (Sum.inl 0))
      (fun omega => SuperdiffusionCLT.Section2.Annealed.abs_blockMatEntry_coarseBlockMatrix_le
        hnu omega ell (originCube d (n : ℤ)) (Sum.inr k) (Sum.inr l))
  · have h := sbIndep_integrable_envelope_mul_envelope_mul_hMat hnu hPrefix hJ2 hJ3 hJ4 hellL n k
      (fun omega => sbIndep_sInvMat (d := d) nu ell n omega k l)
      (fun omega => sbIndep_kcgMat (d := d) nu ell n omega l 0)
      (SuperdiffusionCLT.Section2.Annealed.measurable_blockMatEntry_coarseBlockMatrix
        hnu ell (originCube d (n : ℤ)) (Sum.inr k) (Sum.inr l))
      (SuperdiffusionCLT.Section2.Annealed.measurable_blockMatEntry_coarseBlockMatrix
        hnu ell (originCube d (n : ℤ)) (Sum.inr l) (Sum.inl 0))
      (fun omega => SuperdiffusionCLT.Section2.Annealed.abs_blockMatEntry_coarseBlockMatrix_le
        hnu omega ell (originCube d (n : ℤ)) (Sum.inr k) (Sum.inr l))
      (fun omega => SuperdiffusionCLT.Section2.Annealed.abs_blockMatEntry_coarseBlockMatrix_le
        hnu omega ell (originCube d (n : ℤ)) (Sum.inr l) (Sum.inl 0))
    refine h.congr (Filter.Eventually.of_forall fun omega => ?_)
    simp only
    ring

/-- `sigmaBarSeq` at the origin cube is the expectation of the raw upper-left
entry: under `ShellLawJ4` the annealed Schur correction vanishes. -/
theorem sbNear_sigmaBarSeq_eq_integral {P : ProbabilityMeasure (ShellSeq d)} {nu : ℝ}
    (hnu : 0 < nu) (hJ4 : ShellLawJ4 d P) (m n : ℕ) :
    sigmaBarSeq nu m P n = ∫ omega, sbNear_ul nu m n omega ∂P.toMeasure := by
  rw [sigmaBarSeq, sigmaBarScalar,
    ← annealedBlockMatrix_originCube_upperLeft_eq_sigmaBar hnu m hJ4 (n : ℤ)]
  rfl

/-- **The near-additivity expectation identity**: the left side of `hNearAdd`
is exactly the expectation of the localization error at `P = (e_0, 0)`. -/
theorem sbNear_integral_identity {P : ProbabilityMeasure (ShellSeq d)} {nu : ℝ}
    (hnu : 0 < nu) (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) {ell L : ℕ} (hellL : ell < L) (n : ℕ) :
    sigmaBarSeq nu L P n - sigmaBarSeq nu ell P n -
        (∫ omega, sbIndep_quadTerm (d := d) nu ell L n omega ∂P.toMeasure) -
        (∫ omega, sbIndep_crossTerm (d := d) nu ell L n omega ∂P.toMeasure) =
      ∫ omega, SuperdiffusionCLT.Section2.Localization.localizationT1CubeError nu ell L
        (originCube d (n : ℤ)) (sbNear_e0 (d := d)) omega ∂P.toMeasure := by
  have hUL : ∀ m : ℕ, Integrable (fun omega => sbNear_ul (d := d) nu m n omega) P.toMeasure :=
    fun m => integrable_coarseBlockMatrix_upperLeft_apply hnu m (originCube d (n : ℤ))
      hPrefix hJ2 hJ3 hJ4 0 0
  have hQ : Integrable (fun omega => sbIndep_quadTerm (d := d) nu ell L n omega) P.toMeasure :=
    integrable_finsetSum Finset.univ fun k _ => integrable_finsetSum Finset.univ fun l _ =>
      sbNear_hCI3 hnu hPrefix hJ2 hJ3 hJ4 hellL n k l
  have hX : Integrable (fun omega => sbNear_crossRaw (d := d) nu ell L n omega) P.toMeasure := by
    simp only [sbNear_crossRaw_eq]
    exact ((integrable_finsetSum Finset.univ fun k _ =>
      sbNear_integrable_kcg_mul_hMat hnu hPrefix hJ2 hJ3 hJ4 hellL n k).const_mul 2).neg
  have hD1 : Integrable (fun omega => sbNear_ul (d := d) nu L n omega -
      sbNear_ul (d := d) nu ell n omega) P.toMeasure := (hUL L).sub (hUL ell)
  have hD2 : Integrable (fun omega => sbNear_ul (d := d) nu L n omega -
      sbNear_ul (d := d) nu ell n omega - sbIndep_quadTerm (d := d) nu ell L n omega)
      P.toMeasure := hD1.sub hQ
  rw [sbNear_integral_crossTerm_eq_zero hnu hPrefix hJ2 hJ3 hJ4 hellL n,
    ← sbNear_integral_crossRaw_eq_zero hnu hPrefix hJ2 hJ3 hJ4 hellL n,
    sbNear_sigmaBarSeq_eq_integral hnu hJ4 L n, sbNear_sigmaBarSeq_eq_integral hnu hJ4 ell n,
    ← integral_sub (hUL L) (hUL ell), ← integral_sub hD1 hQ, ← integral_sub hD2 hX]
  exact integral_congr_ae (Filter.Eventually.of_forall fun omega =>
    sbNear_pointwise_identity nu ell L n omega)

end

end SuperdiffusionCLT.Section4.SigmaBarComparison
