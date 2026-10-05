/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.SigmaBarComparison.IndependenceRatioB
public import SuperdiffusionCLT.Section2.Localization.LocalizationAverageT2Final
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5

/-!
# The cross term and the quadratic term of `l.shomm.vs.shomell#independence-and-ratio`

Split out of the independence-ratio estimate for the 800-line budget: this file
carries the lower-shell carriers `kcg_ell(cu_n)`, `s_{ell,*}(cu_n)`, the
matching quadratic/cross term definitions, and the two genuine results proved
about them (`sbIndep_integral_crossTerm_eq_zero`, `E[cross term] = 0`, and
`sbIndep_integral_quadTerm_le`, the ratio estimate on the quadratic term).
`sbIndep_mainB` (`IndependenceRatioF.lean`) consumes both results directly.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.SigmaBarComparison

open MeasureTheory Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Localization (localizationUpperShells localizationLowerShells
  localizationUpperShells_disjoint_lowerShells)
open SuperdiffusionCLT.Probability (shellSigma shellSigma_le_ambient)

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## The lower-shell carriers `kcg_ell(cu_n)`, `s_{ell,*}(cu_n)` -/

/-- `s_{ell,*}(cu_n)`, as the lower-right block of the raw coarse block matrix
at the cutoff-`ell` field, matching `annealedBlockMatrix`'s own entrywise
definition so that `E[sbIndep_sInvMat nu ell n · i j] =
(annealedBlockMatrix nu ell P (cubeSet (originCube d n))).lowerRight i j`
is available directly from `annealedBlockMatrix_lowerRight_apply`. -/
def sbIndep_sInvMat (nu : ℝ) (ell n : ℕ) (omega : ShellSeq d) : Mat d :=
  (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
    (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega ell).toFun).lowerRight

/-- `kcg_ell(cu_n)`, as the lower-left block, matching `annealedBlockMatrix`'s
own entrywise definition. -/
def sbIndep_kcgMat (nu : ℝ) (ell n : ℕ) (omega : ShellSeq d) : Mat d :=
  (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
    (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega ell).toFun).lowerLeft

/-- `h^t s_{ell,*}^{-1}(cu_n) h`, at the `(0,0)` entry (this development's
`Symmetry.lean` scalar-reading convention: "the scalars are defined without
choice as the `(0,0)` entry of the matrix they scale"). -/
def sbIndep_quadTerm (nu : ℝ) (ell L n : ℕ) (omega : ShellSeq d) : ℝ :=
  ∑ k : Fin d, ∑ l : Fin d,
    sbIndep_hMat (d := d) ell L n omega k 0 * sbIndep_sInvMat (d := d) nu ell n omega k l *
      sbIndep_hMat (d := d) ell L n omega l 0

/-- `kcg_ell(cu_n)^t s_{ell,*}^{-1}(cu_n) h + h^t s_{ell,*}^{-1}(cu_n) kcg_ell(cu_n)`,
at the `(0,0)` entry. -/
def sbIndep_crossTerm (nu : ℝ) (ell L n : ℕ) (omega : ShellSeq d) : ℝ :=
  (∑ k : Fin d, ∑ l : Fin d,
      sbIndep_kcgMat (d := d) nu ell n omega k 0 * sbIndep_sInvMat (d := d) nu ell n omega k l *
        sbIndep_hMat (d := d) ell L n omega l 0) +
    (∑ k : Fin d, ∑ l : Fin d,
      sbIndep_hMat (d := d) ell L n omega k 0 * sbIndep_sInvMat (d := d) nu ell n omega k l *
        sbIndep_kcgMat (d := d) nu ell n omega l 0)

/-! ## The cross term vanishes in expectation (`a.j.indy` + `a.j.iso`) -/

private theorem sbIndep_integral_lowerFactor_mul_hEntry_eq_zero {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) {ell L : ℕ} (hellL : ell < L) (n : ℕ) (l : Fin d)
    {c : ShellSeq d → ℝ}
    (hc : StronglyMeasurable[shellSigma (d := d) (localizationLowerShells ell)] c)
    (hcInt : Integrable (fun omega => c omega * sbIndep_hMat (d := d) ell L n omega l 0) P.toMeasure) :
    ∫ omega, c omega * sbIndep_hMat (d := d) ell L n omega l 0 ∂P.toMeasure = 0 := by
  have hYmeas : StronglyMeasurable[shellSigma (d := d) (localizationUpperShells ell)]
      (fun omega => sbIndep_hMat (d := d) ell L n omega l 0) :=
    sbIndep_stronglyMeasurable_hMat_entry ell L n l 0
  have hYint : Integrable (fun omega => sbIndep_hMat (d := d) ell L n omega l 0) P.toMeasure :=
    sbIndep_integrable_hMat_entry hPrefix hJ2 hJ3 hJ4 hellL n l
  have h := sbIndep_integral_mul_eq_mul_integral (d := d)
    (localizationUpperShells_disjoint_lowerShells ell).symm hJ2 hc hYmeas hYint hcInt
  rw [h, sbIndep_integral_hMat_entry_eq_zero hJ4 ell L n l 0, mul_zero]

/-- **`E[cross term] = 0`**: the printed independence
`a.j.indy` (`h` is a functional of the upper shells, `kcg_ell(cu_n)`,
`s_{ell,*}(cu_n)` of the lower shells) together with `E[h] = 0` (`a.j.iso`)
kills both cross terms. `hCarrierMeas`/`hCarrierInt` are the printed lower-shell
regularity of `kcg_ell(cu_n)`, `s_{ell,*}(cu_n)` (see the module docstring). -/
theorem sbIndep_integral_crossTerm_eq_zero {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (nu : ℝ) {ell L : ℕ} (hellL : ell < L) (n : ℕ)
    (hCarrierMeas : ∀ k l : Fin d,
      StronglyMeasurable[shellSigma (d := d) (localizationLowerShells ell)]
        (fun omega => sbIndep_kcgMat (d := d) nu ell n omega k l) ∧
      StronglyMeasurable[shellSigma (d := d) (localizationLowerShells ell)]
        (fun omega => sbIndep_sInvMat (d := d) nu ell n omega k l))
    (hCarrierInt1 : ∀ k l : Fin d,
      Integrable (fun omega => sbIndep_kcgMat (d := d) nu ell n omega k 0 *
        sbIndep_sInvMat (d := d) nu ell n omega k l * sbIndep_hMat (d := d) ell L n omega l 0)
        P.toMeasure)
    (hCarrierInt2 : ∀ k l : Fin d,
      Integrable (fun omega => sbIndep_hMat (d := d) ell L n omega k 0 *
        sbIndep_sInvMat (d := d) nu ell n omega k l * sbIndep_kcgMat (d := d) nu ell n omega l 0)
        P.toMeasure) :
    ∫ omega, sbIndep_crossTerm (d := d) nu ell L n omega ∂P.toMeasure = 0 := by
  have hterm1 : ∀ k l : Fin d,
      ∫ omega, sbIndep_kcgMat (d := d) nu ell n omega k 0 *
        sbIndep_sInvMat (d := d) nu ell n omega k l * sbIndep_hMat (d := d) ell L n omega l 0
        ∂P.toMeasure = 0 := by
    intro k l
    have hc : StronglyMeasurable[shellSigma (d := d) (localizationLowerShells ell)]
        (fun omega => sbIndep_kcgMat (d := d) nu ell n omega k 0 *
          sbIndep_sInvMat (d := d) nu ell n omega k l) :=
      (hCarrierMeas k 0).1.mul (hCarrierMeas k l).2
    exact sbIndep_integral_lowerFactor_mul_hEntry_eq_zero hPrefix hJ2 hJ3 hJ4 hellL n l hc
      (hCarrierInt1 k l)
  have hterm2 : ∀ k l : Fin d,
      ∫ omega, sbIndep_hMat (d := d) ell L n omega k 0 *
        sbIndep_sInvMat (d := d) nu ell n omega k l * sbIndep_kcgMat (d := d) nu ell n omega l 0
        ∂P.toMeasure = 0 := by
    intro k l
    have hc : StronglyMeasurable[shellSigma (d := d) (localizationLowerShells ell)]
        (fun omega => sbIndep_sInvMat (d := d) nu ell n omega k l *
          sbIndep_kcgMat (d := d) nu ell n omega l 0) :=
      (hCarrierMeas k l).2.mul (hCarrierMeas l 0).1
    have hcInt : Integrable (fun omega => (sbIndep_sInvMat (d := d) nu ell n omega k l *
        sbIndep_kcgMat (d := d) nu ell n omega l 0) *
        sbIndep_hMat (d := d) ell L n omega k 0) P.toMeasure := by
      have heq : (fun omega => (sbIndep_sInvMat (d := d) nu ell n omega k l *
          sbIndep_kcgMat (d := d) nu ell n omega l 0) *
          sbIndep_hMat (d := d) ell L n omega k 0) =
        (fun omega => sbIndep_hMat (d := d) ell L n omega k 0 *
          sbIndep_sInvMat (d := d) nu ell n omega k l *
          sbIndep_kcgMat (d := d) nu ell n omega l 0) := by
        funext omega; ring
      rw [heq]; exact hCarrierInt2 k l
    have h := sbIndep_integral_lowerFactor_mul_hEntry_eq_zero hPrefix hJ2 hJ3 hJ4 hellL n k hc hcInt
    have heq2 : (fun omega => sbIndep_hMat (d := d) ell L n omega k 0 *
        sbIndep_sInvMat (d := d) nu ell n omega k l * sbIndep_kcgMat (d := d) nu ell n omega l 0) =
      (fun omega => (sbIndep_sInvMat (d := d) nu ell n omega k l *
        sbIndep_kcgMat (d := d) nu ell n omega l 0) *
        sbIndep_hMat (d := d) ell L n omega k 0) := by
      funext omega; ring
    rw [show (∫ omega, sbIndep_hMat (d := d) ell L n omega k 0 *
        sbIndep_sInvMat (d := d) nu ell n omega k l * sbIndep_kcgMat (d := d) nu ell n omega l 0
        ∂P.toMeasure) =
      ∫ omega, (sbIndep_sInvMat (d := d) nu ell n omega k l *
        sbIndep_kcgMat (d := d) nu ell n omega l 0) *
        sbIndep_hMat (d := d) ell L n omega k 0 ∂P.toMeasure from by rw [heq2]]
    exact h
  unfold sbIndep_crossTerm
  rw [MeasureTheory.integral_add
    (integrable_finsetSum Finset.univ fun k _ =>
      integrable_finsetSum Finset.univ fun l _ => hCarrierInt1 k l)
    (integrable_finsetSum Finset.univ fun k _ =>
      integrable_finsetSum Finset.univ fun l _ => hCarrierInt2 k l),
    MeasureTheory.integral_finsetSum Finset.univ fun k _ =>
      MeasureTheory.integrable_finsetSum Finset.univ fun l _ => hCarrierInt1 k l,
    MeasureTheory.integral_finsetSum Finset.univ fun k _ =>
      MeasureTheory.integrable_finsetSum Finset.univ fun l _ => hCarrierInt2 k l]
  have hs1 : (∑ k : Fin d, ∫ omega,
      (∑ l : Fin d, sbIndep_kcgMat (d := d) nu ell n omega k 0 *
        sbIndep_sInvMat (d := d) nu ell n omega k l * sbIndep_hMat (d := d) ell L n omega l 0)
      ∂P.toMeasure) = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [MeasureTheory.integral_finsetSum Finset.univ fun l _ => hCarrierInt1 k l]
    exact Finset.sum_eq_zero fun l _ => hterm1 k l
  have hs2 : (∑ k : Fin d, ∫ omega,
      (∑ l : Fin d, sbIndep_hMat (d := d) ell L n omega k 0 *
        sbIndep_sInvMat (d := d) nu ell n omega k l * sbIndep_kcgMat (d := d) nu ell n omega l 0)
      ∂P.toMeasure) = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [MeasureTheory.integral_finsetSum Finset.univ fun l _ => hCarrierInt2 k l]
    exact Finset.sum_eq_zero fun l _ => hterm2 k l
  rw [hs1, hs2, add_zero]

/-! ## The quadratic term: the ratio estimate (`a.j.indy` + `a.j.iso` + `e.kmn.bounds`) -/

private theorem sbIndep_sInvMat_apply_eq {P : ProbabilityMeasure (ShellSeq d)}
    {nu : ℝ} (hnu : 0 < nu) (hJ4 : ShellLawJ4 d P) (ell n : ℕ) (k l : Fin d) :
    ∫ omega, sbIndep_sInvMat (d := d) nu ell n omega k l ∂P.toMeasure =
      sigmaBarStarInvScalar nu ell P (cubeSet (originCube d (n : ℤ))) *
        (if k = l then (1 : ℝ) else 0) := by
  have h1 : ∫ omega, sbIndep_sInvMat (d := d) nu ell n omega k l ∂P.toMeasure =
      (annealedBlockMatrix nu ell P (cubeSet (originCube d (n : ℤ)))).lowerRight k l :=
    (annealedBlockMatrix_lowerRight_apply nu ell P (cubeSet (originCube d (n : ℤ))) k l).symm
  rw [h1, show (annealedBlockMatrix nu ell P (cubeSet (originCube d (n : ℤ)))).lowerRight =
      sigmaBarStarInv nu ell P (cubeSet (originCube d (n : ℤ))) from rfl,
    sigmaBarStarInv_originCube_eq_smul_one hnu ell hJ4 (n : ℤ)]
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]

/-- **`E[quad term] ≤ shom_{ell,*}^{-1}(cu_n) * Cmom * (L - ell)`**: the entrywise
independence product formula, the isotropy of `E[s_{ell,*}(cu_n)]` (`a.j.iso`), and the
second-moment bound `e.kmn.bounds` at `p = 2`
(`IndependenceRatioB.sbIndep_integral_hMat_colSq_le`). -/
theorem sbIndep_integral_quadTerm_le {P : ProbabilityMeasure (ShellSeq d)}
    {nu : ℝ} (hPrefix : ShellLawPrefix d P) (hnu : 0 < nu) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) {ell L : ℕ} (hellL : ell < L) (n : ℕ)
    (hCarrierMeas : ∀ k l : Fin d,
      StronglyMeasurable[shellSigma (d := d) (localizationLowerShells ell)]
        (fun omega => sbIndep_sInvMat (d := d) nu ell n omega k l))
    (hCarrierInt : ∀ k l : Fin d, Integrable (fun omega => sbIndep_sInvMat (d := d) nu ell n omega k l)
      P.toMeasure)
    (hCarrierInt3 : ∀ k l : Fin d,
      Integrable (fun omega => sbIndep_hMat (d := d) ell L n omega k 0 *
        sbIndep_sInvMat (d := d) nu ell n omega k l * sbIndep_hMat (d := d) ell L n omega l 0)
        P.toMeasure)
    (hSInvNonneg : 0 ≤ sigmaBarStarInvScalar nu ell P (cubeSet (originCube d (n : ℤ)))) :
      0 ≤ ∫ omega, sbIndep_quadTerm (d := d) nu ell L n omega ∂P.toMeasure ∧
      ∫ omega, sbIndep_quadTerm (d := d) nu ell L n omega ∂P.toMeasure ≤
        sigmaBarStarInvScalar nu ell P (cubeSet (originCube d (n : ℤ))) * sbIndep_Cmom0 d *
          ((L : ℝ) - (ell : ℝ)) := by
  have hCmomBound := sbIndep_integral_hMat_colSq_le hPrefix hJ2 hJ3 hJ4 hellL n
  have hterm : ∀ k l : Fin d,
      ∫ omega, sbIndep_hMat (d := d) ell L n omega k 0 *
        sbIndep_sInvMat (d := d) nu ell n omega k l * sbIndep_hMat (d := d) ell L n omega l 0
        ∂P.toMeasure =
      (∫ omega, sbIndep_hMat (d := d) ell L n omega k 0 * sbIndep_hMat (d := d) ell L n omega l 0
        ∂P.toMeasure) * (sigmaBarStarInvScalar nu ell P (cubeSet (originCube d (n : ℤ))) *
          (if k = l then (1 : ℝ) else 0)) := by
    intro k l
    have hc : StronglyMeasurable[shellSigma (d := d) (localizationUpperShells ell)]
        (fun omega => sbIndep_hMat (d := d) ell L n omega k 0 *
          sbIndep_hMat (d := d) ell L n omega l 0) :=
      (sbIndep_stronglyMeasurable_hMat_entry ell L n k 0).mul
        (sbIndep_stronglyMeasurable_hMat_entry ell L n l 0)
    have hcYint : Integrable (fun omega => (sbIndep_hMat (d := d) ell L n omega k 0 *
        sbIndep_hMat (d := d) ell L n omega l 0) * sbIndep_sInvMat (d := d) nu ell n omega k l)
        P.toMeasure := by
      have heq : (fun omega => (sbIndep_hMat (d := d) ell L n omega k 0 *
          sbIndep_hMat (d := d) ell L n omega l 0) * sbIndep_sInvMat (d := d) nu ell n omega k l) =
        (fun omega => sbIndep_hMat (d := d) ell L n omega k 0 *
          sbIndep_sInvMat (d := d) nu ell n omega k l * sbIndep_hMat (d := d) ell L n omega l 0) := by
        funext omega; ring
      rw [heq]; exact hCarrierInt3 k l
    have h := sbIndep_integral_mul_eq_mul_integral (d := d)
      (localizationUpperShells_disjoint_lowerShells ell) hJ2 hc (hCarrierMeas k l)
      (hCarrierInt k l) hcYint
    have heq2 : (fun omega => sbIndep_hMat (d := d) ell L n omega k 0 *
        sbIndep_sInvMat (d := d) nu ell n omega k l * sbIndep_hMat (d := d) ell L n omega l 0) =
      (fun omega => (sbIndep_hMat (d := d) ell L n omega k 0 *
        sbIndep_hMat (d := d) ell L n omega l 0) * sbIndep_sInvMat (d := d) nu ell n omega k l) := by
      funext omega; ring
    rw [show (∫ omega, sbIndep_hMat (d := d) ell L n omega k 0 *
        sbIndep_sInvMat (d := d) nu ell n omega k l * sbIndep_hMat (d := d) ell L n omega l 0
        ∂P.toMeasure) = ∫ omega, (sbIndep_hMat (d := d) ell L n omega k 0 *
        sbIndep_hMat (d := d) ell L n omega l 0) * sbIndep_sInvMat (d := d) nu ell n omega k l
        ∂P.toMeasure from by rw [heq2], h, sbIndep_sInvMat_apply_eq hnu hJ4 ell n k l]
  have hinner : ∀ k : Fin d, (∫ omega, (∑ l : Fin d, sbIndep_hMat (d := d) ell L n omega k 0 *
      sbIndep_sInvMat (d := d) nu ell n omega k l * sbIndep_hMat (d := d) ell L n omega l 0)
      ∂P.toMeasure) =
      sigmaBarStarInvScalar nu ell P (cubeSet (originCube d (n : ℤ))) *
        ∫ omega, (sbIndep_hMat (d := d) ell L n omega k 0) ^ 2 ∂P.toMeasure := by
    intro k
    rw [MeasureTheory.integral_finsetSum Finset.univ fun l _ => hCarrierInt3 k l,
      Finset.sum_eq_single k]
    · rw [hterm k k]
      simp only [↓reduceIte, mul_one]
      rw [show (∫ omega, sbIndep_hMat (d := d) ell L n omega k 0 *
          sbIndep_hMat (d := d) ell L n omega k 0 ∂P.toMeasure) =
          ∫ omega, (sbIndep_hMat (d := d) ell L n omega k 0) ^ 2 ∂P.toMeasure from by
        congr 1; funext omega; ring]
      ring
    · intro l _ hlk
      rw [hterm k l]
      simp only [Ne.symm hlk, ↓reduceIte, mul_zero]
    · intro hk
      simp at hk
  have hsum_eq : (∫ omega, sbIndep_quadTerm (d := d) nu ell L n omega ∂P.toMeasure) =
      sigmaBarStarInvScalar nu ell P (cubeSet (originCube d (n : ℤ))) *
        ∫ omega, (∑ k : Fin d, (sbIndep_hMat (d := d) ell L n omega k 0) ^ 2) ∂P.toMeasure := by
    unfold sbIndep_quadTerm
    rw [MeasureTheory.integral_finsetSum Finset.univ fun k _ =>
      integrable_finsetSum Finset.univ fun l _ => hCarrierInt3 k l,
      Finset.sum_congr rfl fun k _ => hinner k, ← Finset.mul_sum,
      MeasureTheory.integral_finsetSum Finset.univ fun k _ =>
        sbIndep_integrable_hMat_entry_sq hPrefix hJ2 hJ3 hJ4 hellL n k]
  have hnn : 0 ≤ ∫ omega, (∑ k : Fin d, (sbIndep_hMat (d := d) ell L n omega k 0) ^ 2)
      ∂P.toMeasure :=
    integral_nonneg fun omega => Finset.sum_nonneg fun k _ => sq_nonneg _
  refine ⟨?_, ?_⟩
  · rw [hsum_eq]; exact mul_nonneg hSInvNonneg hnn
  · rw [hsum_eq]
    calc sigmaBarStarInvScalar nu ell P (cubeSet (originCube d (n : ℤ))) *
        ∫ omega, (∑ k : Fin d, (sbIndep_hMat (d := d) ell L n omega k 0) ^ 2) ∂P.toMeasure ≤
        sigmaBarStarInvScalar nu ell P (cubeSet (originCube d (n : ℤ))) *
          (sbIndep_Cmom0 d * ((L : ℝ) - (ell : ℝ))) :=
          mul_le_mul_of_nonneg_left hCmomBound hSInvNonneg
      _ = sigmaBarStarInvScalar nu ell P (cubeSet (originCube d (n : ℤ))) * sbIndep_Cmom0 d *
          ((L : ℝ) - (ell : ℝ)) := by ring

end

end SuperdiffusionCLT.Section4.SigmaBarComparison
