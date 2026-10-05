/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.SigmaBarComparison.IndependenceRatioB
public import SuperdiffusionCLT.Section2.Annealed.Integrability

/-!
# Triple-product integrability of the lower-shell carriers against `h`

`sbIndep_mainB` (`IndependenceRatioF.lean`) reads two of `hGoodN`'s conjuncts
(`hCI1`, `hCI2` there) as hypotheses: the integrability of
`kcg_ell(cu_n)_{k0} * s_{ell,*}^{-1}(cu_n)_{kl} * h_{l0}` and its mirror image
`h_{k0} * s_{ell,*}^{-1}(cu_n)_{kl} * kcg_ell(cu_n)_{l0}`. This file discharges
both directly, leaving only the third
(`hCI3`, `h_{k0} * s_{ell,*}^{-1}(cu_n)_{kl} * h_{l0}`, two `h`-factors rather
than one) as a hypothesis: the
same argument used here needs a *fourth*-moment bound on `h`'s entries, which
goes beyond the first and second moments proved in this development so far
(`sbIndep_integrable_hMat_entry`/`sbIndep_integrable_hMat_entry_sq`) and is supplied
separately by `NearAdditivityA.lean`, whereas
`hCI1`/`hCI2` only ever need a fourth-moment bound on the (already
`gammaSigma`-controlled, hence arbitrary-moment) coarse block matrix envelope
`cutoffBlockEntryBound`, never on `h` itself.

## The route

`kcg_ell(cu_n)_{k0}` and `s_{ell,*}^{-1}(cu_n)_{kl}` are both entries of the
*same* coarse block matrix `coarseBlockMatrix (cu_n) (coefficientCutoff nu
omega ell).toFun` (the lower-left and lower-right blocks respectively), so
both are pointwise dominated by the *same* envelope `cutoffBlockEntryBound nu
omega ell (cu_n)` (`Section2.Annealed.Integrability.abs_blockMatEntry_coarseBlockMatrix_le`).
That envelope is affine in the already `gammaSigma`-tail-controlled quantity
`Z := ⨍_{cu_n} |k_ell|²` (`Section2.Annealed.Integrability.cutoffBlockEntryBound`),
and `Z` satisfies an `IsBigOWith (gammaSigma 1)` bound
(`isBigOWith_gammaSigma_volumeAverage_sq_streamCutoff`) whose consuming lemma
`IndependentSums.integrable_rpow_of_isBigOWith_gammaSigma` is generic in the
moment order `p ≥ 1` — the existing tree only ever invokes it at `p = 1`, but
nothing stops invoking it at `p = 4`, giving `Z^4`, hence
`cutoffBlockEntryBound^4`, integrable (`sbIndep_integrable_cutoffBlockEntryBound_pow4`).
Since the product of the two envelope-bounded factors is then pointwise
`≤ cutoffBlockEntryBound^2`, its square is `≤ cutoffBlockEntryBound^4`, hence
integrable; the elementary bound `2|XY| ≤ X² + Y²` (`X` := that product,
`Y` := the `h`-entry, whose square is integrable by
`sbIndep_integrable_hMat_entry_sq`) then gives integrability of the full
triple product by domination — no Hölder/`MemLp` machinery needed, only
pointwise algebra and the two already-integrable squares.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.SigmaBarComparison

open MeasureTheory Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Localization (localizationUpperShells)
open SuperdiffusionCLT.Probability (shellSigma_le_ambient)

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## A pointwise majorant for `cutoffBlockEntryBound` -/

omit [NeZero d] in
private theorem sbIndep_volumeAverage_sq_streamCutoff_nonneg (omega : ShellSeq d) (m : ℕ)
    (Q : TriadicCube d) :
    (0 : ℝ) ≤ volumeAverage (openCubeSet Q)
      (fun x => matrixOperatorNorm (streamCutoff omega m x) ^ 2) := by
  rw [volumeAverage]
  exact mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) (integral_nonneg fun x => by positivity)

omit [NeZero d] in
private theorem sbIndep_cutoffBlockEntryBound_nonneg {nu : ℝ} (hnu : 0 < nu) (omega : ShellSeq d)
    (m : ℕ) (Q : TriadicCube d) : (0 : ℝ) ≤ cutoffBlockEntryBound nu omega m Q := by
  unfold cutoffBlockEntryBound
  have hnuinv : (0 : ℝ) ≤ nu⁻¹ := (inv_pos.2 hnu).le
  have hZ := sbIndep_volumeAverage_sq_streamCutoff_nonneg omega m Q
  nlinarith only [hnu.le, hnuinv, hZ, mul_nonneg hnuinv hZ]

omit [NeZero d] in
/-- **`cutoffBlockEntryBound` is dominated by `(nu + 4 nu⁻¹) * max 1 Z`**, `Z`
its own defining `⨍|k_m|²` term: on `Z ≤ 1` the `Z`-linear term is dominated
by its own coefficient, on `Z ≥ 1` the constant term is dominated by `Z` times
its own coefficient. -/
private theorem sbIndep_cutoffBlockEntryBound_le_max {nu : ℝ} (hnu : 0 < nu) (omega : ShellSeq d)
    (m : ℕ) (Q : TriadicCube d) :
    cutoffBlockEntryBound nu omega m Q ≤ (nu + 4 * nu⁻¹) *
      max 1 (volumeAverage (openCubeSet Q) (fun x => matrixOperatorNorm (streamCutoff omega m x) ^ 2)) := by
  unfold cutoffBlockEntryBound
  set Z : ℝ := volumeAverage (openCubeSet Q)
      (fun x => matrixOperatorNorm (streamCutoff omega m x) ^ 2) with hZdef
  have hZnn : (0 : ℝ) ≤ Z := sbIndep_volumeAverage_sq_streamCutoff_nonneg omega m Q
  have hnuinv : (0 : ℝ) ≤ nu⁻¹ := (inv_pos.2 hnu).le
  rcases le_total Z 1 with hZ1 | hZ1
  · rw [max_eq_left hZ1]
    nlinarith only [hnu.le, hnuinv, hZ1, mul_nonneg hnuinv (sub_nonneg.mpr hZ1)]
  · rw [max_eq_right hZ1]
    have hstep : (nu + 2 * nu⁻¹) * 1 ≤ (nu + 2 * nu⁻¹) * Z :=
      mul_le_mul_of_nonneg_left hZ1 (by linarith only [hnu.le, hnuinv])
    nlinarith only [hstep]

/-! ## `(max 1 Z) ^ 4 ≤ 1 + Z ^ 4` -/

private theorem sbIndep_max_one_pow4_le {Z : ℝ} (hZ : 0 ≤ Z) : (max 1 Z) ^ 4 ≤ 1 + Z ^ 4 := by
  rcases le_total Z 1 with h | h
  · rw [max_eq_left h, one_pow]
    linarith only [pow_nonneg hZ 4]
  · rw [max_eq_right h]
    have : (1 : ℝ) ≤ Z ^ 4 := by
      calc (1 : ℝ) = 1 ^ 4 := (one_pow 4).symm
        _ ≤ Z ^ 4 := pow_le_pow_left₀ (by norm_num) h 4
    linarith only [this]

/-! ## `Z ^ 4` is integrable (the `gammaSigma` machinery is generic in `p`) -/

omit [NeZero d] in
private theorem sbIndep_integrable_volumeAverage_sq_streamCutoff_pow4
    {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (m : ℕ) (Q : TriadicCube d) :
    Integrable (fun omega => (volumeAverage (openCubeSet Q)
      (fun x => matrixOperatorNorm (streamCutoff omega m x) ^ 2)) ^ (4 : ℕ)) P.toMeasure := by
  set Z : ShellSeq d → ℝ := fun omega => volumeAverage (openCubeSet Q)
      (fun x => matrixOperatorNorm (streamCutoff omega m x) ^ 2) with hZdef
  have hZnn : ∀ omega, (0 : ℝ) ≤ Z omega := fun omega =>
    sbIndep_volumeAverage_sq_streamCutoff_nonneg omega m Q
  have hZmeas : Measurable Z := measurable_volumeAverage_sq_streamCutoff m (openCubeSet Q)
  have hK : (0 : ℝ) < cutoffL2Const d * ((m : ℝ) + 1) :=
    mul_pos (cutoffL2Const_pos hPrefix) (by positivity)
  have hbig := isBigOWith_gammaSigma_volumeAverage_sq_streamCutoff hPrefix hJ2 hJ3 hJ4 m
    (volume_openCubeSet_ne_zero Q) (volume_openCubeSet_lt_top Q).ne
  have hZ4 : Integrable (fun omega => Z omega ^ (4 : ℝ)) P.toMeasure :=
    IndependentSums.integrable_rpow_of_isBigOWith_gammaSigma (by norm_num : (0 : ℝ) < 1) hK
      (by norm_num : (1 : ℝ) ≤ 4) hZnn hZmeas.aemeasurable hbig
  have heq : (fun omega => Z omega ^ (4 : ℝ)) = fun omega => Z omega ^ (4 : ℕ) := by
    funext omega
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rwa [heq] at hZ4

omit [NeZero d] in
/-- **`cutoffBlockEntryBound ^ 4` is integrable.** The moment-bound gap the
independence-ratio estimate used to report for `hCI1`/`hCI2`
is closed by this lemma: it needs no new probabilistic input beyond what
`Section2.Annealed.Integrability` already lands, only the same
`IndependentSums.integrable_rpow_of_isBigOWith_gammaSigma` invoked at `p = 4`
in place of the tree's existing `p = 1` use. -/
theorem sbIndep_integrable_cutoffBlockEntryBound_pow4 {P : ProbabilityMeasure (ShellSeq d)}
    {nu : ℝ} (hnu : 0 < nu) (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (m : ℕ) (Q : TriadicCube d) :
    Integrable (fun omega => cutoffBlockEntryBound nu omega m Q ^ 4) P.toMeasure := by
  have hZ4 := sbIndep_integrable_volumeAverage_sq_streamCutoff_pow4 hPrefix hJ2 hJ3 hJ4 m Q
  set C : ℝ := (nu + 4 * nu⁻¹) ^ 4 with hCdef
  have hCnn : (0 : ℝ) ≤ C := by positivity
  have hmaj : Integrable (fun omega => C + C * (volumeAverage (openCubeSet Q)
      (fun x => matrixOperatorNorm (streamCutoff omega m x) ^ 2)) ^ (4 : ℕ)) P.toMeasure :=
    (integrable_const C).add (hZ4.const_mul C)
  have hZmeas : Measurable (fun omega => volumeAverage (openCubeSet Q)
      (fun x => matrixOperatorNorm (streamCutoff omega m x) ^ 2)) :=
    measurable_volumeAverage_sq_streamCutoff m (openCubeSet Q)
  have hbdmeas : Measurable (fun omega => cutoffBlockEntryBound nu omega m Q) := by
    unfold cutoffBlockEntryBound
    exact (measurable_const.add (hZmeas.const_mul _)).add measurable_const
  refine Integrable.mono' hmaj (hbdmeas.pow_const 4).aestronglyMeasurable ?_
  filter_upwards with omega
  have hbdnn := sbIndep_cutoffBlockEntryBound_nonneg hnu omega m Q
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hbdnn 4)]
  have hZnn := sbIndep_volumeAverage_sq_streamCutoff_nonneg omega m Q
  have hle := sbIndep_cutoffBlockEntryBound_le_max hnu omega m Q
  have hpow : cutoffBlockEntryBound nu omega m Q ^ 4 ≤
      ((nu + 4 * nu⁻¹) * max 1 (volumeAverage (openCubeSet Q)
        (fun x => matrixOperatorNorm (streamCutoff omega m x) ^ 2))) ^ 4 :=
    pow_le_pow_left₀ hbdnn hle 4
  have hmaxpow : ((nu + 4 * nu⁻¹) * max 1 (volumeAverage (openCubeSet Q)
        (fun x => matrixOperatorNorm (streamCutoff omega m x) ^ 2))) ^ 4 =
      C * (max 1 (volumeAverage (openCubeSet Q)
        (fun x => matrixOperatorNorm (streamCutoff omega m x) ^ 2))) ^ 4 := by
    rw [hCdef, mul_pow]
  have hmax4 := sbIndep_max_one_pow4_le hZnn
  calc cutoffBlockEntryBound nu omega m Q ^ 4 ≤ _ := hpow
    _ = C * (max 1 (volumeAverage (openCubeSet Q)
          (fun x => matrixOperatorNorm (streamCutoff omega m x) ^ 2))) ^ 4 := hmaxpow
    _ ≤ C * (1 + (volumeAverage (openCubeSet Q)
          (fun x => matrixOperatorNorm (streamCutoff omega m x) ^ 2)) ^ 4) :=
        mul_le_mul_of_nonneg_left hmax4 hCnn
    _ = C + C * (volumeAverage (openCubeSet Q)
          (fun x => matrixOperatorNorm (streamCutoff omega m x) ^ 2)) ^ 4 := by ring

/-! ## The two `hGoodN` triple products, discharged -/

/-- **The general triple-product integrability lemma**: two factors each
pointwise dominated by the same `cutoffBlockEntryBound` envelope, times an
`h`-entry (whose square is integrable), is integrable. Both `hCI1`- and
`hCI2`-shaped conjuncts of `hGoodN` instantiate
this directly, up to `ring`-commuting the product order. -/
theorem sbIndep_integrable_envelope_mul_envelope_mul_hMat
    {P : ProbabilityMeasure (ShellSeq d)} {nu : ℝ} (hnu : 0 < nu)
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) {ell L : ℕ} (hellL : ell < L) (n : ℕ) (l : Fin d)
    (f g : ShellSeq d → ℝ) (hfmeas : Measurable f) (hgmeas : Measurable g)
    (hf : ∀ omega, |f omega| ≤ cutoffBlockEntryBound nu omega ell (originCube d (n : ℤ)))
    (hg : ∀ omega, |g omega| ≤ cutoffBlockEntryBound nu omega ell (originCube d (n : ℤ))) :
    Integrable (fun omega => f omega * g omega * sbIndep_hMat (d := d) ell L n omega l 0)
      P.toMeasure := by
  have hbd4 := sbIndep_integrable_cutoffBlockEntryBound_pow4 hnu hPrefix hJ2 hJ3 hJ4 ell
    (originCube d (n : ℤ))
  have hY2 := sbIndep_integrable_hMat_entry_sq hPrefix hJ2 hJ3 hJ4 hellL n l
  have hXmeas : Measurable (fun omega => f omega * g omega) := hfmeas.mul hgmeas
  have hYmeas : Measurable (fun omega => sbIndep_hMat (d := d) ell L n omega l 0) :=
    ((sbIndep_stronglyMeasurable_hMat_entry ell L n l 0).mono
      (shellSigma_le_ambient (d := d) (localizationUpperShells ell))).measurable
  have hX2 : Integrable (fun omega => (f omega * g omega) ^ 2) P.toMeasure := by
    refine Integrable.mono' hbd4 (hXmeas.pow_const 2).aestronglyMeasurable ?_
    filter_upwards with omega
    have henv := le_trans (abs_nonneg (f omega)) (hf omega)
    have hxy : |f omega * g omega| ≤
        cutoffBlockEntryBound nu omega ell (originCube d (n : ℤ)) ^ 2 := by
      rw [abs_mul, sq]
      exact mul_le_mul (hf omega) (hg omega) (abs_nonneg _) henv
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (f omega * g omega))]
    calc (f omega * g omega) ^ 2 = |f omega * g omega| ^ 2 := (sq_abs _).symm
      _ ≤ (cutoffBlockEntryBound nu omega ell (originCube d (n : ℤ)) ^ 2) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hxy 2
      _ = cutoffBlockEntryBound nu omega ell (originCube d (n : ℤ)) ^ 4 := by ring
  have hmaj2 : Integrable (fun omega => (2⁻¹ : ℝ) *
      ((f omega * g omega) ^ 2 + sbIndep_hMat (d := d) ell L n omega l 0 ^ 2)) P.toMeasure := by
    have h := (hX2.add hY2).const_mul (2⁻¹ : ℝ)
    simpa using h
  refine Integrable.mono' hmaj2 (hXmeas.mul hYmeas).aestronglyMeasurable ?_
  filter_upwards with omega
  rw [Real.norm_eq_abs]
  have habs : |f omega * g omega * sbIndep_hMat (d := d) ell L n omega l 0| ≤
      (2⁻¹ : ℝ) * ((f omega * g omega) ^ 2 + sbIndep_hMat (d := d) ell L n omega l 0 ^ 2) := by
    rw [abs_mul]
    have h2 : 2 * |f omega * g omega| * |sbIndep_hMat (d := d) ell L n omega l 0| ≤
        |f omega * g omega| ^ 2 + |sbIndep_hMat (d := d) ell L n omega l 0| ^ 2 := by
      nlinarith only [sq_nonneg (|f omega * g omega| - |sbIndep_hMat (d := d) ell L n omega l 0|)]
    rw [sq_abs, sq_abs] at h2
    linarith only [h2]
  exact habs

end

end SuperdiffusionCLT.Section4.SigmaBarComparison
