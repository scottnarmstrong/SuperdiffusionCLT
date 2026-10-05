/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.SigmaBarComparison.IndependenceRatioD
public import SuperdiffusionCLT.Section4.SigmaBarComparison.IndependenceRatioE

/-!
# The fourth moment of `h`'s entries, and `hCI3`

The `hGoodN` of the independence-ratio estimate carries one remaining integrability
conjunct beyond near-additivity: `hCI3`, the integrability of the two-`h`-
factor product `h_{k0} * s_{ell,*}^{-1}(cu_n)_{kl} * h_{l0}` (a summand of
`sbIndep_quadTerm`). `IndependenceRatioD.lean`'s module docstring records the
exact gap: the same domination argument used there for the one-`h`-factor
triple products (`hCI1`/`hCI2`) needs a *fourth*-moment bound on `h`'s entries
for the two-`h`-factor product, and only the first and second moments of `h`
are available (`sbIndep_integrable_hMat_entry`/`sbIndep_integrable_hMat_entry_sq`,
`IndependenceRatioB.lean`).

This file closes that gap. `h`'s fourth moment (`sbNear_integrable_hMat_entry_pow4`)
is obtained exactly as its second moment already is
(`sbIndep_integrable_hMat_entry_sq`): the same `e.kmn.bounds` display
`isBigO_gammaSigma_finiteShellIncrementPthMoment`, invoked at `p = 4` in place
of `p = 2` (the `gammaSigma`-tail control is generic in the moment order,
exactly the same genericity `IndependenceRatioD.lean` already exploits for the
envelope `cutoffBlockEntryBound`), composed with the fourth-power Jensen step
in place of the second-power one already used for the second moment (the
private helpers `sbIndep_abs_hMat_le`/`sbIndep_sq_volumeAverage_matrixOperatorNorm_le`
of `IndependenceRatioB.lean` are not importable, so their fourth-power
analogues are reproduced here as `sbNear_abs_hMat_le`/
`sbNear_pow4_volumeAverage_matrixOperatorNorm_le`).

`sbNear_hCI3` then follows by the same `2|XY| ≤ X² + Y²` domination
`IndependenceRatioD.lean` uses, with `X := s_{ell,*}^{-1}(cu_n)_{kl}`
(dominated by the fourth-power-integrable envelope
`cutoffBlockEntryBound`, `sbIndep_integrable_cutoffBlockEntryBound_pow4`,
needing only its *square* here, via the elementary `x² ≤ 1 + x⁴`) and
`Y := h_{k0} * h_{l0}` (dominated by `h`'s own fourth moment, proved below,
via `2|ab| ≤ a² + b²` applied to `a := h_{k0}²`, `b := h_{l0}²`).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.SigmaBarComparison

open MeasureTheory Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Localization (localizationUpperShells)
open SuperdiffusionCLT.Probability (shellSigma_le_ambient)

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## Bookkeeping: `cubeSet`/`openCubeSet` volume averages agree -/

omit [NeZero d] in
private theorem sbNear_volumeAverage_cubeSet_eq_openCubeSet (Q : TriadicCube d) (f : Vec d → ℝ) :
    volumeAverage (cubeSet Q) f = volumeAverage (openCubeSet Q) f := by
  simp only [volumeAverage, volume_openCubeSet_eq_volume_cubeSet]
  rw [MeasureTheory.setIntegral_congr_set (cubeSet_ae_eq_openCubeSet Q)]

/-! ## `|h_{i0}| ≤ ⨍_{cu_n} |k_L - k_ell|` -/

private theorem sbNear_abs_hMat_le (omega : ShellSeq d) (ell L n : ℕ) (i : Fin d) :
    |sbIndep_hMat (d := d) ell L n omega i 0| ≤
      volumeAverage (openCubeSet (originCube d (n : ℤ)))
        (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x)) := by
  show |volumeAverage (openCubeSet (originCube d (n : ℤ)))
      (fun x => finiteShellIncrement omega ell L x i 0)| ≤ _
  set U : Set (Vec d) := openCubeSet (originCube d (n : ℤ)) with hUdef
  have hint : IntegrableOn (fun x => finiteShellIncrement omega ell L x i 0) U volume := by
    have hg : IntegrableOn (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x))
        U volume := by
      have h := SuperdiffusionCLT.Section2.Estimates.Stream.integrableOn_matrixOperatorNorm_rpow_finiteShellIncrement
        omega ell L n (p := (1 : ℝ)) (by norm_num)
      simpa only [Real.rpow_one] using h
    have hmeas : AEStronglyMeasurable (fun x => finiteShellIncrement omega ell L x i 0)
        (volume.restrict U) :=
      ((finiteShellIncrement omega ell L).entry_measurable i 0).aestronglyMeasurable.restrict
    refine Integrable.mono' hg hmeas ?_
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet (originCube d (n : ℤ)))] with x _
    rw [Real.norm_eq_abs]
    exact abs_entry_le_matrixOperatorNorm _ i 0
  have hgint : IntegrableOn (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x))
      U volume := by
    have h := SuperdiffusionCLT.Section2.Estimates.Stream.integrableOn_matrixOperatorNorm_rpow_finiteShellIncrement
      omega ell L n (p := (1 : ℝ)) (by norm_num)
    simpa only [Real.rpow_one] using h
  have habs1 : |∫ x in U, finiteShellIncrement omega ell L x i 0 ∂volume| ≤
      ∫ x in U, |finiteShellIncrement omega ell L x i 0| ∂volume := by
    simpa only [Real.norm_eq_abs] using
      norm_integral_le_integral_norm (μ := volume.restrict U)
        (f := fun x => finiteShellIncrement omega ell L x i 0)
  have habs2 : ∫ x in U, |finiteShellIncrement omega ell L x i 0| ∂volume ≤
      ∫ x in U, matrixOperatorNorm (finiteShellIncrement omega ell L x) ∂volume := by
    refine MeasureTheory.setIntegral_mono hint.abs hgint fun x => ?_
    exact abs_entry_le_matrixOperatorNorm _ i 0
  have hcnn : (0 : ℝ) ≤ (volume U).toReal⁻¹ := inv_nonneg.2 ENNReal.toReal_nonneg
  calc |volumeAverage U (fun x => finiteShellIncrement omega ell L x i 0)|
      = (volume U).toReal⁻¹ * |∫ x in U, finiteShellIncrement omega ell L x i 0 ∂volume| := by
        rw [volumeAverage, abs_mul, abs_of_nonneg hcnn]
    _ ≤ (volume U).toReal⁻¹ * ∫ x in U, |finiteShellIncrement omega ell L x i 0| ∂volume :=
        mul_le_mul_of_nonneg_left habs1 hcnn
    _ ≤ (volume U).toReal⁻¹ *
          ∫ x in U, matrixOperatorNorm (finiteShellIncrement omega ell L x) ∂volume :=
        mul_le_mul_of_nonneg_left habs2 hcnn
    _ = volumeAverage U (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x)) := rfl

/-! ## The fourth-power Jensen step: `(⨍ g)^4 ≤ ⨍ (g^4)` -/

omit [NeZero d] in
private theorem sbNear_pow4_volumeAverage_matrixOperatorNorm_le (omega : ShellSeq d)
    (ell L n : ℕ) :
    (volumeAverage (openCubeSet (originCube d (n : ℤ)))
        (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x))) ^ 4 ≤
      volumeAverage (openCubeSet (originCube d (n : ℤ)))
        (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ 4) := by
  set U : Set (Vec d) := openCubeSet (originCube d (n : ℤ)) with hUdef
  set g : Vec d → ℝ := fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x) with hgdef
  have hg1 : IntegrableOn g U volume := by
    have h := SuperdiffusionCLT.Section2.Estimates.Stream.integrableOn_matrixOperatorNorm_rpow_finiteShellIncrement
      omega ell L n (p := (1 : ℝ)) (by norm_num)
    simpa only [Real.rpow_one] using h
  have hg4 : IntegrableOn (fun x => g x ^ 4) U volume := by
    have h := SuperdiffusionCLT.Section2.Estimates.Stream.integrableOn_matrixOperatorNorm_rpow_finiteShellIncrement
      omega ell L n (p := (4 : ℝ)) (by norm_num)
    have h2 : (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ (4 : ℝ)) =
        fun x => g x ^ (4 : ℕ) := by
      funext x
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rwa [h2] at h
  have hconv : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 4) := Even.convexOn_pow (by decide)
  have hJensen := hconv.map_set_average_le
    (hgc := (continuous_pow 4).continuousOn) (hsc := isClosed_univ)
    (h0 := volume_openCubeSet_ne_zero (originCube d (n : ℤ)))
    (ht := (volume_openCubeSet_lt_top (originCube d (n : ℤ))).ne)
    (hfs := Filter.Eventually.of_forall fun x => Set.mem_univ (g x))
    (hfi := hg1) (hgi := hg4)
  have heq : ⨍ x in U, g x ∂volume = volumeAverage U g :=
    (SuperdiffusionCLT.Probability.volumeAverage_eq_setAverage U g).symm
  have heq2 : (⨍ x in U, g x ^ 4 ∂volume) = volumeAverage U (fun x => g x ^ 4) :=
    (SuperdiffusionCLT.Probability.volumeAverage_eq_setAverage U (fun x => g x ^ 4)).symm
  rw [heq, heq2] at hJensen
  exact hJensen

/-! ## `h`'s entries to the fourth power are integrable (`e.kmn.bounds` at `p = 4`) -/

/-- **`h`'s entries to the fourth power are integrable**, the `L^4` companion
of `sbIndep_integrable_hMat_entry_sq` (`IndependenceRatioB.lean`): the same
route (`isBigO_gammaSigma_finiteShellIncrementPthMoment` at `p = 4` instead of
`p = 2`), needed for `sbNear_hCI3` below. -/
theorem sbNear_integrable_hMat_entry_pow4 {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) {ell L : ℕ} (hellL : ell < L) (n : ℕ) (i : Fin d) :
    Integrable (fun omega => (sbIndep_hMat (d := d) ell L n omega i 0) ^ 4) P.toMeasure := by
  set Y : ShellSeq d → ℝ := fun omega =>
      volumeAverage (openCubeSet (originCube d (n : ℤ)))
        (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ 4) with hYdef
  have hpoint : ∀ omega : ShellSeq d,
      (sbIndep_hMat (d := d) ell L n omega i 0) ^ 4 ≤ Y omega := by
    intro omega
    have h1 := sbNear_abs_hMat_le omega ell L n i
    have heq4 : |sbIndep_hMat (d := d) ell L n omega i 0| ^ 4 =
        (sbIndep_hMat (d := d) ell L n omega i 0) ^ 4 := Even.pow_abs (by decide) _
    have h2 : (sbIndep_hMat (d := d) ell L n omega i 0) ^ 4 ≤
        (volumeAverage (openCubeSet (originCube d (n : ℤ)))
          (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x))) ^ 4 := by
      rw [← heq4]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 4
    exact h2.trans (sbNear_pow4_volumeAverage_matrixOperatorNorm_le omega ell L n)
  have hYeq : Y = fun omega => volumeAverage (cubeSet (originCube d (n : ℤ)))
      (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ 4) := by
    funext omega
    rw [hYdef, sbNear_volumeAverage_cubeSet_eq_openCubeSet]
  set X : ShellSeq d → ℝ := fun omega => volumeAverage (cubeSet (originCube d (n : ℤ)))
      (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ (4 : ℝ)) with hXdef
  have hXnn : ∀ omega : ShellSeq d, 0 ≤ X omega := by
    intro omega
    show 0 ≤ volumeAverage (cubeSet (originCube d (n : ℤ)))
      (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ (4 : ℝ))
    rw [volumeAverage]
    exact mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
      (integral_nonneg fun x => Real.rpow_nonneg (matrixOperatorNorm_nonneg _) 4)
  have hXmeas : Measurable X :=
    sbIndep_measurable_volumeAverage_matrixOperatorNorm_rpow ell L n
      (by norm_num : (0 : ℝ) ≤ (4 : ℝ))
  have hSpos := SuperdiffusionCLT.Section2.Estimates.Stream.streamLinftyConst_pos hPrefix
  have hgm : (0 : ℝ) < Real.exp 1 * IndependentSums.gammaMomentConst (2 / 4) :=
    mul_pos (Real.exp_pos 1) (IndependentSums.gammaMomentConst_pos (by norm_num))
  have hCpos : 0 <
      SuperdiffusionCLT.Section2.Estimates.Stream.finiteShellIncrementPthMomentConst d 4 := by
    rw [SuperdiffusionCLT.Section2.Estimates.Stream.finiteShellIncrementPthMomentConst]
    exact mul_pos (Real.rpow_pos_of_pos hgm _) hSpos
  have hLellPos : (0 : ℝ) < ((L - ell : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hellL
  have hbig := SuperdiffusionCLT.Section2.Estimates.Stream.isBigO_gammaSigma_finiteShellIncrementPthMoment
    hPrefix hJ2 hJ3 hJ4 (p := (4 : ℝ)) (by norm_num) hellL (originCube d (n : ℤ))
  set K : ℝ :=
      SuperdiffusionCLT.Section2.Estimates.Stream.finiteShellIncrementPthMomentConst d 4 ^
          (4 : ℝ) *
        Real.sqrt (((L - ell : ℕ) : ℝ)) ^ (4 : ℝ) with hKdef
  have hK : 0 < K :=
    mul_pos (Real.rpow_pos_of_pos hCpos 4) (Real.rpow_pos_of_pos (Real.sqrt_pos.2 hLellPos) 4)
  have hbigWith : IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma (2 / 4 : ℝ))
      X K := by
    have heqabs : (fun omega => |X omega|) = X := funext fun omega => abs_of_nonneg (hXnn omega)
    rw [IndependentSums.IsBigO, heqabs] at hbig
    exact hbig
  have hXint1 : Integrable (fun omega => X omega ^ (1 : ℝ)) P.toMeasure :=
    IndependentSums.integrable_rpow_of_isBigOWith_gammaSigma
      (by norm_num : (0 : ℝ) < 2 / 4) hK le_rfl hXnn hXmeas.aemeasurable hbigWith
  have hXint : Integrable X P.toMeasure := by
    simpa only [Real.rpow_one] using hXint1
  have hYint : Integrable Y P.toMeasure := by
    rw [hYeq]
    have heqXY : (fun omega => volumeAverage (cubeSet (originCube d (n : ℤ)))
        (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ 4)) = X := by
      funext omega
      rw [hXdef]
      congr 1
      funext x
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [heqXY]; exact hXint
  have hmeas : AEStronglyMeasurable
      (fun omega => (sbIndep_hMat (d := d) ell L n omega i 0) ^ 4) P.toMeasure :=
    (((sbIndep_stronglyMeasurable_hMat_entry ell L n i 0).mono
      (shellSigma_le_ambient (d := d) (localizationUpperShells ell))).measurable.pow_const
      4).aestronglyMeasurable
  refine Integrable.mono' hYint hmeas ?_
  filter_upwards with omega
  rw [Real.norm_eq_abs, abs_of_nonneg (Even.pow_nonneg (by decide) _)]
  exact hpoint omega

/-! ## `hCI3`: integrability of the two-`h`-factor product -/

private theorem sbNear_sq_le_one_add_pow4 (x : ℝ) : x ^ 2 ≤ 1 + x ^ 4 := by
  nlinarith only [sq_nonneg (x ^ 2 - 1)]

/-- **`hCI3`**: integrability of `h_{k0} * s_{ell,*}^{-1}(cu_n)_{kl} * h_{l0}`,
the third and last integrability conjunct of `hGoodN`
of the independence-ratio estimate that `IndependenceRatioD.lean` leaves hypothesized.
Closed via `2|AB| ≤ A² + B²` with `A := s_{ell,*}^{-1}(cu_n)_{kl}` (dominated
by `cutoffBlockEntryBound`, whose square is dominated in turn by
`1 + cutoffBlockEntryBound^4`, already integrable) and
`B := h_{k0} * h_{l0}` (whose square is dominated by
`(h_{k0}^4 + h_{l0}^4)/2`, via `sbNear_integrable_hMat_entry_pow4`). -/
theorem sbNear_hCI3 {P : ProbabilityMeasure (ShellSeq d)} {nu : ℝ} (hnu : 0 < nu)
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) {ell L : ℕ} (hellL : ell < L) (n : ℕ) (k l : Fin d) :
    Integrable (fun omega => sbIndep_hMat (d := d) ell L n omega k 0 *
      sbIndep_sInvMat (d := d) nu ell n omega k l *
      sbIndep_hMat (d := d) ell L n omega l 0) P.toMeasure := by
  have hk4 := sbNear_integrable_hMat_entry_pow4 hPrefix hJ2 hJ3 hJ4 hellL n k
  have hl4 := sbNear_integrable_hMat_entry_pow4 hPrefix hJ2 hJ3 hJ4 hellL n l
  have hbd4 := sbIndep_integrable_cutoffBlockEntryBound_pow4 hnu hPrefix hJ2 hJ3 hJ4 ell
    (originCube d (n : ℤ))
  have hSmeas : Measurable (fun omega => sbIndep_sInvMat (d := d) nu ell n omega k l) :=
    SuperdiffusionCLT.Section2.Annealed.measurable_blockMatEntry_coarseBlockMatrix
      hnu ell (originCube d (n : ℤ)) (Sum.inr k) (Sum.inr l)
  have hSbound : ∀ omega, |sbIndep_sInvMat (d := d) nu ell n omega k l| ≤
      cutoffBlockEntryBound nu omega ell (originCube d (n : ℤ)) := fun omega =>
    SuperdiffusionCLT.Section2.Annealed.abs_blockMatEntry_coarseBlockMatrix_le
      hnu omega ell (originCube d (n : ℤ)) (Sum.inr k) (Sum.inr l)
  have hHmeas : ∀ j : Fin d, Measurable (fun omega => sbIndep_hMat (d := d) ell L n omega j 0) :=
    fun j => ((sbIndep_stronglyMeasurable_hMat_entry ell L n j 0).mono
      (shellSigma_le_ambient (d := d) (localizationUpperShells ell))).measurable
  have hS2 : Integrable (fun omega => (sbIndep_sInvMat (d := d) nu ell n omega k l) ^ 2)
      P.toMeasure := by
    have hmaj : Integrable (fun omega => 1 + cutoffBlockEntryBound nu omega ell
        (originCube d (n : ℤ)) ^ 4) P.toMeasure := (integrable_const 1).add hbd4
    refine Integrable.mono' hmaj (hSmeas.pow_const 2).aestronglyMeasurable ?_
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hxb : (sbIndep_sInvMat (d := d) nu ell n omega k l) ^ 2 ≤
        cutoffBlockEntryBound nu omega ell (originCube d (n : ℤ)) ^ 2 := by
      rw [← sq_abs (sbIndep_sInvMat (d := d) nu ell n omega k l)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hSbound omega) 2
    exact hxb.trans (sbNear_sq_le_one_add_pow4 _)
  have hHH2 : Integrable (fun omega => (sbIndep_hMat (d := d) ell L n omega k 0 *
      sbIndep_hMat (d := d) ell L n omega l 0) ^ 2) P.toMeasure := by
    have hmaj : Integrable (fun omega => (2⁻¹ : ℝ) *
        ((sbIndep_hMat (d := d) ell L n omega k 0) ^ 4 +
          (sbIndep_hMat (d := d) ell L n omega l 0) ^ 4)) P.toMeasure :=
      (hk4.add hl4).const_mul (2⁻¹ : ℝ)
    refine Integrable.mono' hmaj
      (((hHmeas k).mul (hHmeas l)).pow_const 2).aestronglyMeasurable ?_
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hexpand : (sbIndep_hMat (d := d) ell L n omega k 0 *
        sbIndep_hMat (d := d) ell L n omega l 0) ^ 2 =
        (sbIndep_hMat (d := d) ell L n omega k 0) ^ 2 *
          (sbIndep_hMat (d := d) ell L n omega l 0) ^ 2 := by ring
    rw [hexpand]
    nlinarith only [sq_nonneg ((sbIndep_hMat (d := d) ell L n omega k 0) ^ 2 -
      (sbIndep_hMat (d := d) ell L n omega l 0) ^ 2)]
  have hmaj2 : Integrable (fun omega => (2⁻¹ : ℝ) *
      ((sbIndep_sInvMat (d := d) nu ell n omega k l) ^ 2 +
        (sbIndep_hMat (d := d) ell L n omega k 0 * sbIndep_hMat (d := d) ell L n omega l 0) ^ 2))
      P.toMeasure := (hS2.add hHH2).const_mul (2⁻¹ : ℝ)
  refine Integrable.mono' hmaj2
    (((hHmeas k).mul hSmeas).mul (hHmeas l)).aestronglyMeasurable ?_
  filter_upwards with omega
  rw [Real.norm_eq_abs]
  have habs : |sbIndep_sInvMat (d := d) nu ell n omega k l *
      (sbIndep_hMat (d := d) ell L n omega k 0 * sbIndep_hMat (d := d) ell L n omega l 0)| ≤
      (2⁻¹ : ℝ) * ((sbIndep_sInvMat (d := d) nu ell n omega k l) ^ 2 +
        (sbIndep_hMat (d := d) ell L n omega k 0 * sbIndep_hMat (d := d) ell L n omega l 0) ^ 2) := by
    rw [abs_mul]
    have h2 : 2 * |sbIndep_sInvMat (d := d) nu ell n omega k l| *
        |sbIndep_hMat (d := d) ell L n omega k 0 * sbIndep_hMat (d := d) ell L n omega l 0| ≤
        |sbIndep_sInvMat (d := d) nu ell n omega k l| ^ 2 +
        |sbIndep_hMat (d := d) ell L n omega k 0 * sbIndep_hMat (d := d) ell L n omega l 0| ^ 2 := by
      nlinarith only [sq_nonneg (|sbIndep_sInvMat (d := d) nu ell n omega k l| -
        |sbIndep_hMat (d := d) ell L n omega k 0 * sbIndep_hMat (d := d) ell L n omega l 0|)]
    rw [sq_abs, sq_abs] at h2
    linarith only [h2]
  calc |sbIndep_hMat (d := d) ell L n omega k 0 * sbIndep_sInvMat (d := d) nu ell n omega k l *
      sbIndep_hMat (d := d) ell L n omega l 0| =
      |sbIndep_sInvMat (d := d) nu ell n omega k l *
        (sbIndep_hMat (d := d) ell L n omega k 0 * sbIndep_hMat (d := d) ell L n omega l 0)| := by
        rw [show sbIndep_hMat (d := d) ell L n omega k 0 *
            sbIndep_sInvMat (d := d) nu ell n omega k l *
            sbIndep_hMat (d := d) ell L n omega l 0 =
          sbIndep_sInvMat (d := d) nu ell n omega k l *
            (sbIndep_hMat (d := d) ell L n omega k 0 *
              sbIndep_hMat (d := d) ell L n omega l 0) from by ring]
    _ ≤ _ := habs

end

end SuperdiffusionCLT.Section4.SigmaBarComparison
