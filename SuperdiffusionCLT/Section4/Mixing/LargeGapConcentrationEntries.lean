/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.Integrability
public import SuperdiffusionCLT.Section2.Cutoff.Size
public import SuperdiffusionCLT.Section4.Mixing.AnnealedComparison

/-!
# The entrywise `Γ₁` envelope and centring of `bfA_L(z + cu_n)`

Ingredients for `p.mixing.P.three.prime#large-gap-case`: a
*uniform* (translate-, block- and entry-independent) `Γ₁` envelope for every
entry of `bfA_L(z + cu_n) - bfAhom_L(cu_n)`, matching the reusable pattern of
`SuperdiffusionCLT.Section3.Terms.BlockConcentrationInputs` (there
specialized to the single test `e·(b_L(z+cu_n) - shom_L(cu_n))e` of the
upper-left block) but for *every* entry of *every* block, via the general machinery:

* `SuperdiffusionCLT.Section2.Annealed.abs_blockMatEntry_coarseBlockMatrix_le`,
  the deterministic per-sample bound `|bfA_L(z+cu_n)_{αβ}(ω)| ≤
  cutoffBlockEntryBound(ν,ω,L,z)` uniform over all four blocks (`Integrability.lean`);
* `SuperdiffusionCLT.Section2.Cutoff.isBigOWith_gammaSigma_volumeAverage_sq_streamCutoff_max`,
  the `Γ₁` envelope of the normalized `L²` size feeding `cutoffBlockEntryBound`,
  general in the domain (`Cutoff/Size.lean`);
* `SuperdiffusionCLT.Section4.Mixing.mixMain_integral_coarseBlockMatrix_*_eq`,
  stationarity for all four blocks (`AnnealedComparison.lean`).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

open Homogenization
open Homogenization.IndependentSums
open MeasureTheory ProbabilityTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

variable {d : ℕ}

/-- Subtracting/adding a bounded quantity from an `O_{Γσ}`-controlled variable
enlarges the amplitude by that bound: the same "add-const" step
`SuperdiffusionCLT.Section3.Terms.BlockConcentrationInputs`'s
`isBigO_gammaSigma_of_abs_le_add_const` proves, reproved here since that one
is `private` to its file. -/
theorem mixGap_isBigO_gammaSigma_of_abs_le_add_const {Omega : Type*}
    [MeasurableSpace Omega] {mu : Measure Omega} [IsFiniteMeasure mu]
    {X Y : Omega → ℝ} {A c sigma : ℝ} (hc : 0 ≤ c)
    (hle : ∀ omega, |Y omega| ≤ |X omega| + c)
    (hX : IsBigO mu (gammaSigma sigma) X A) :
    IsBigO mu (gammaSigma sigma) Y (A + c) := by
  rw [isBigO_gammaSigma_iff]
  intro t ht
  refine (measureReal_mono ?_).trans ((isBigO_gammaSigma_iff.1 hX) ht)
  intro omega homega
  have hY : (A + c) * t < |Y omega| := homega
  have hct : c ≤ c * t := le_mul_of_one_le_right hc ht
  have hle' := hle omega
  show A * t < |X omega|
  have hexp : (A + c) * t = A * t + c * t := by ring
  linarith only [hY, hct, hle', hexp]

/-! ## The uniform `Γ₁` envelope of a single entry -/

/-- **The uniform `Γ₁` envelope of every entry of `bfA_L(cu)`, on every
triadic cube.** `nu + 2nu⁻¹(2·cutoffL2Const d·(1∨L)) + 2nu⁻¹`, the amplitude
`cutoffBlockEntryBound` carries once its random `L²`-size summand is bounded
by its own `Γ1` envelope `2·cutoffL2Const d·(1∨L)`
(`isBigOWith_gammaSigma_volumeAverage_sq_streamCutoff_max`). -/
def mixGap_entryEnvelope (d : ℕ) (nu : ℝ) (L : ℕ) : ℝ :=
  nu + 2 * nu⁻¹ * (2 * cutoffL2Const d * max 1 (L : ℝ)) + 2 * nu⁻¹

theorem mixGap_entryEnvelope_pos {nu : ℝ} (hnu : 0 < nu) (d L : ℕ) :
    0 < mixGap_entryEnvelope d nu L := by
  have hSq : (0 : ℝ) ≤ cutoffSquareConst d := by unfold cutoffSquareConst; positivity
  have hL2 : (0 : ℝ) ≤ cutoffL2Const d := by
    unfold cutoffL2Const
    have hmom : (0 : ℝ) < IndependentSums.gammaMomentConst 1 :=
      IndependentSums.gammaMomentConst_pos one_pos
    positivity
  have hnuinv : (0 : ℝ) < nu⁻¹ := inv_pos.2 hnu
  have hmax : (0 : ℝ) ≤ max 1 (L : ℝ) := le_trans zero_le_one (le_max_left _ _)
  unfold mixGap_entryEnvelope
  have h1 : (0:ℝ) ≤ 2 * nu⁻¹ * (2 * cutoffL2Const d * max 1 (L:ℝ)) := by positivity
  linarith only [hnu, hnuinv, h1]

/-- **`cutoffBlockEntryBound` is `O_{Γ1}(mixGap_entryEnvelope d nu L)`, on
every triadic cube.** `isBigOWith_gammaSigma_volumeAverage_sq_streamCutoff_max`
supplies the envelope of the random `L²`-size summand, general in the domain
(so no translation-covariance argument is needed); the deterministic affine
transform `nu + 2nu⁻¹·(·) + 2nu⁻¹` carries the envelope along. -/
theorem mixGap_isBigO_gammaOne_cutoffBlockEntryBound [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (L : ℕ) (z : TriadicCube d) :
    IsBigO P.toMeasure (gammaSigma 1)
      (fun omega : ShellSeq d => cutoffBlockEntryBound nu omega L z)
      (mixGap_entryEnvelope d nu L) := by
  have hXbigWith := SuperdiffusionCLT.Section2.Cutoff.isBigOWith_gammaSigma_volumeAverage_sq_streamCutoff_max
    hPrefix hJ2 hJ3 hJ4 L (volume_openCubeSet_ne_zero z) (volume_openCubeSet_lt_top z).ne
  have hXnonneg : ∀ omega : ShellSeq d, 0 ≤ volumeAverage (openCubeSet z)
      (fun x => Book.Ch02.matrixOperatorNorm (streamCutoff omega L x) ^ 2) := by
    intro omega
    unfold volumeAverage
    exact mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
      (integral_nonneg fun x => by positivity)
  have hXbig : IsBigO P.toMeasure (gammaSigma 1)
      (fun omega : ShellSeq d => volumeAverage (openCubeSet z)
        (fun x => Book.Ch02.matrixOperatorNorm (streamCutoff omega L x) ^ 2))
      (2 * cutoffL2Const d * max 1 (L : ℝ)) :=
    (SuperdiffusionCLT.Probability.isBigOWith_iff_isBigO_of_nonneg hXnonneg).1 hXbigWith
  have hscaled := hXbig.const_mul (c := 2 * nu⁻¹) (by positivity)
  have hle : ∀ omega : ShellSeq d, |cutoffBlockEntryBound nu omega L z| ≤
      |2 * nu⁻¹ * volumeAverage (openCubeSet z)
        (fun x => Book.Ch02.matrixOperatorNorm (streamCutoff omega L x) ^ 2)| + (nu + 2 * nu⁻¹) := by
    intro omega
    have hnn : 0 ≤ cutoffBlockEntryBound nu omega L z := by
      unfold cutoffBlockEntryBound
      have h2 := hXnonneg omega
      have hnuinv : (0:ℝ) ≤ 2 * nu⁻¹ := by positivity
      nlinarith only [hnu.le, hnuinv, h2]
    rw [abs_of_nonneg hnn]
    have heq : cutoffBlockEntryBound nu omega L z =
        2 * nu⁻¹ * volumeAverage (openCubeSet z)
          (fun x => Book.Ch02.matrixOperatorNorm (streamCutoff omega L x) ^ 2) + (nu + 2 * nu⁻¹) := by
      unfold cutoffBlockEntryBound
      ring
    rw [heq]
    have h2 := hXnonneg omega
    have habs : |2 * nu⁻¹ * volumeAverage (openCubeSet z)
        (fun x => Book.Ch02.matrixOperatorNorm (streamCutoff omega L x) ^ 2)| =
        2 * nu⁻¹ * volumeAverage (openCubeSet z)
          (fun x => Book.Ch02.matrixOperatorNorm (streamCutoff omega L x) ^ 2) := by
      rw [abs_of_nonneg]
      positivity
    rw [habs]
  refine (mixGap_isBigO_gammaSigma_of_abs_le_add_const
    (by positivity : (0:ℝ) ≤ nu + 2 * nu⁻¹) hle hscaled).mono_scale (le_of_eq ?_)
  unfold mixGap_entryEnvelope
  ring

/-- **The uniform `Γ1` envelope, at every entry of every block.**
`abs_blockMatEntry_coarseBlockMatrix_le` bounds every entry by
`cutoffBlockEntryBound`, deterministically. -/
theorem mixGap_isBigO_gammaOne_blockMatEntry [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (L : ℕ) (z : TriadicCube d) (alpha beta : BlockCoord d) :
    IsBigO P.toMeasure (gammaSigma 1)
      (fun omega : ShellSeq d => blockMatEntry
        (coarseBlockMatrix (cubeSet z) (coefficientCutoff nu omega L).toCoeffField) alpha beta)
      (mixGap_entryEnvelope d nu L) := by
  have hbound := mixGap_isBigO_gammaOne_cutoffBlockEntryBound hnu hPrefix hJ2 hJ3 hJ4 L z
  refine hbound.of_abs_le fun omega => ?_
  have hnn : 0 ≤ cutoffBlockEntryBound nu omega L z :=
    le_trans (abs_nonneg _) (abs_blockMatEntry_coarseBlockMatrix_le hnu omega L z alpha alpha)
  rw [abs_of_nonneg hnn]
  exact abs_blockMatEntry_coarseBlockMatrix_le hnu omega L z alpha beta

/-! ## The uniform envelope of the annealed entry -/

/-- **A uniform bound on every entry of `bfAhom_L(cu_n)`.** From
`annealedBlockMatrix`'s definition as an expectation and the deterministic
domination `|entry| ≤ cutoffBlockEntryBound`. -/
theorem mixGap_abs_annealedBlockMatrixEntry_le [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (L nn : ℕ) (alpha beta : BlockCoord d) :
    |blockMatEntry (annealedBlockMatrix nu L P (cubeSet (originCube d (nn : ℤ)))) alpha beta| ≤
      IndependentSums.gammaMomentConst 1 * mixGap_entryEnvelope d nu L := by
  set z : TriadicCube d := originCube d (nn : ℤ)
  have heq : blockMatEntry (annealedBlockMatrix nu L P (cubeSet z)) alpha beta =
      ∫ omega : ShellSeq d, blockMatEntry
        (coarseBlockMatrix (cubeSet z) (coefficientCutoff nu omega L).toCoeffField) alpha beta
        ∂P.toMeasure := by
    cases alpha with
    | inl i => cases beta with
      | inl j => exact annealedBlockMatrix_upperLeft_apply nu L P (cubeSet z) i j
      | inr j => exact annealedBlockMatrix_upperRight_apply nu L P (cubeSet z) i j
    | inr i => cases beta with
      | inl j => exact annealedBlockMatrix_lowerLeft_apply nu L P (cubeSet z) i j
      | inr j => exact annealedBlockMatrix_lowerRight_apply nu L P (cubeSet z) i j
  have hbig := mixGap_isBigO_gammaOne_blockMatEntry hnu hPrefix hJ2 hJ3 hJ4 L z alpha beta
  have hInt : Integrable (fun omega : ShellSeq d => blockMatEntry
      (coarseBlockMatrix (cubeSet z) (coefficientCutoff nu omega L).toCoeffField) alpha beta)
      P.toMeasure := by
    cases alpha with
    | inl i => cases beta with
      | inl j => exact integrable_coarseBlockMatrix_upperLeft_apply hnu L z hPrefix hJ2 hJ3 hJ4 i j
      | inr j => exact integrable_coarseBlockMatrix_upperRight_apply hnu L z hPrefix hJ2 hJ3 hJ4 i j
    | inr i => cases beta with
      | inl j => exact integrable_coarseBlockMatrix_lowerLeft_apply hnu L z hPrefix hJ2 hJ3 hJ4 i j
      | inr j => exact integrable_coarseBlockMatrix_lowerRight_apply hnu L z hPrefix hJ2 hJ3 hJ4 i j
  have hEnvPos : (0 : ℝ) < mixGap_entryEnvelope d nu L := mixGap_entryEnvelope_pos hnu d L
  have hmom := mixMain_integral_abs_le_of_isBigO_gammaSigma
    (μ := P.toMeasure)
    (X := fun omega : ShellSeq d => blockMatEntry
      (coarseBlockMatrix (cubeSet z) (coefficientCutoff nu omega L).toCoeffField) alpha beta)
    (A := mixGap_entryEnvelope d nu L) (σ := 1) one_pos hEnvPos hInt.aemeasurable hbig
  rw [heq]
  set g : ShellSeq d → ℝ := fun omega => blockMatEntry
    (coarseBlockMatrix (cubeSet z) (coefficientCutoff nu omega L).toCoeffField) alpha beta
    with hg
  have hstep : |∫ omega : ShellSeq d, g omega ∂P.toMeasure| ≤ ∫ omega : ShellSeq d, |g omega| ∂P.toMeasure :=
    norm_integral_le_integral_norm g
  exact hstep.trans hmom

/-! ## The uniform `Γ1` envelope of the centred entry (the deviation) -/

/-- **The uniform `Γ1` envelope of the entrywise deviation**
`bfA_L(z+cu_n)_{αβ} - bfAhom_L(cu_n)_{αβ}`, for every `z`, `L`, `nn` and
`alpha, beta`. Combines `mixGap_isBigO_gammaOne_blockMatEntry` (the entry) and
`mixGap_abs_annealedBlockMatrixEntry_le` (the deterministic centring
constant) via `mixGap_isBigO_gammaSigma_of_abs_le_add_const`. -/
theorem mixGap_isBigO_gammaOne_entryDeviation [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (L nn : ℕ) (z : TriadicCube d) (alpha beta : BlockCoord d) :
    IsBigO P.toMeasure (gammaSigma 1)
      (fun omega : ShellSeq d => blockMatEntry
          (coarseBlockMatrix (cubeSet z) (coefficientCutoff nu omega L).toCoeffField) alpha beta -
        blockMatEntry (annealedBlockMatrix nu L P (cubeSet (originCube d (nn : ℤ)))) alpha beta)
      (mixGap_entryEnvelope d nu L +
        IndependentSums.gammaMomentConst 1 * mixGap_entryEnvelope d nu L) := by
  have hentry := mixGap_isBigO_gammaOne_blockMatEntry hnu hPrefix hJ2 hJ3 hJ4 L z alpha beta
  have hconst := mixGap_abs_annealedBlockMatrixEntry_le hnu hPrefix hJ2 hJ3 hJ4 L nn alpha beta
  refine mixGap_isBigO_gammaSigma_of_abs_le_add_const
    (mul_nonneg (IndependentSums.gammaMomentConst_pos (σ := (1:ℝ)) one_pos).le
      (mixGap_entryEnvelope_pos hnu d L).le) ?_ hentry
  intro omega
  set a : ℝ := blockMatEntry
    (coarseBlockMatrix (cubeSet z) (coefficientCutoff nu omega L).toCoeffField) alpha beta
  set c : ℝ := blockMatEntry
    (annealedBlockMatrix nu L P (cubeSet (originCube d (nn : ℤ)))) alpha beta
  have htri : |a - c| ≤ |a| + |c| := by
    rw [abs_le]
    constructor
    · linarith only [neg_abs_le a, le_abs_self c]
    · linarith only [le_abs_self a, neg_abs_le c]
  linarith only [htri, hconst]

end

end SuperdiffusionCLT.Section4.Mixing
