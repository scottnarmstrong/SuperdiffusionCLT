/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3CgCloseE

/-!
# `term3_cgBound_finalB`: the coarse-graining residual, one premise lighter

The term-3 final assembly carries the binder `_hCgBound`, which is the printed display
`e.RHS.term3.A` (Step 2 of the proof of `e.RHS.term3`; the companion display is
`e.RHS.term3.B` — there is no `e.RHS.term3.C`).  `term3_cgBound_closeE` states that display
verbatim at six residuals.

## The residual list of `term3_cgBound_closeE`, grouped by shape

| residual | one-line content | source |
|---|---|---|
| `hAnnealedSub` | `∫ energySubQCarrier = ½ σ*_n ‖e‖²` on each sub-cube `R` | printed (see below) |
| `hAnnealedBig` | `∫ energyBigQCarrier = ½ σ*_m ‖e‖²` on `cu_m` | printed (see below) |
| `hPigeon` | `|1 - (σ*_n)⁻¹ σ*_m| ≤ δ + η_L` | printed, `e.pigeon.scalar` |
| `hde1` | `δ + η_L ≤ 1` | ours: the absorbability side condition of `w_average_difference` |
| `hCerr` | `cgBoundConst (cgBoundAmpP …) (cgBoundAmpW …) (bEllipConst d) ≤ Cerr` | ours: the display's error constant |
| `hEnergyInt` | `Integrable (fun ω => ⍍_R (-(ν/2)|∇u_m|² + e·∇u_m))` on each sub-cube `R` | ours: an integrability side condition |

The two annealed residuals are the display `e.additivity.error.superdiff`.

This module removes the last of the six.  `hEnergyInt` is not an analytic input
of the printed display, it is only the integrability of an observable of the
glued field, and that integrability follows from the two bounds of
`RHSTerm3CgCloseE`:

* the sub-cube energy `A(ω) = ⍍_R |∇u_m(ω)|²` is measurable in `ω` with the
  uniform bound `K` (`measurable_vecSqAvg_gluedGradientField_self_subcube`,
  `vecSqAvg_gluedGradientField_self_subcube_le`);
* the pairing average `B(ω) = ⍍_R e·∇u_m(ω)` is measurable in `ω` through the
  `L²(cu_m)` class of the glued field
  (`measurable_gluedGradientClass`), read as an inner product, and bounded by
  `|e|²/2 + A(ω)/2` with Young's inequality.

The energy integrand is `-(ν/2) A + B`, so it is measurable with the uniform
bound `(ν+1)/2 · K + |e|²/2` and therefore integrable over a probability
measure.  Nothing is carried beyond `0 < nu` and the scale ordering.

## Main results

* `volumeAverage_vecDot_eq_inv_volume_mul_inner` and the auxiliary estimates
  `abs_volumeAverage_le_volumeAverage_abs`, `volumeAverage_mono_of_nonneg`,
  `volumeAverage_div_const`, `volumeAverage_energyInt_decomp`,
  `setIntegral_vecDot_indicator_eq`.
* `integrable_hEnergyInt_discharged`.
* `term3_cgBound_finalB`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory ProbabilityTheory
open Homogenization
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The pairing average as an inner product over the ambient cube

The average of `e·∇u_m` over a sub-cube `R` is the integral over `R` of the
zero-extension pairing, and the zero-extension over the ambient cube `cu_m`
reads as the inner product of two `L²(cu_m)` classes, the first of which is
sample-independent.  That is what makes the pairing average measurable in the
sample. -/

/-- The ambient integral of the zero-extension of the pairing field. -/
theorem setIntegral_vecDot_indicator_eq {Q R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) (f g : Vec d → Vec d) :
    ∫ x in openCubeSet Q, vecDot (Set.indicator (cubeSet R) f x) (g x) =
      ∫ x in openCubeSet R, vecDot (f x) (g x) := by
  have hpoint : (fun x => vecDot (Set.indicator (cubeSet R) f x) (g x)) =
      Set.indicator (cubeSet R) (fun y => vecDot (f y) (g y)) := by
    funext x
    by_cases hx : x ∈ cubeSet R
    · simp only [Set.indicator_of_mem hx]
    · simp only [Set.indicator_of_notMem hx]
      simp [vecDot]
  rw [hpoint, MeasureTheory.setIntegral_indicator (measurableSet_cubeSet R),
    volume_restrict_inter_cubeSet_eq_of_mem_descendantsAtDepth hR,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet R]

/-- The ambient-cube inner-product form of the sub-cube pairing mean. -/
theorem volumeAverage_vecDot_eq_inv_volume_mul_inner {Q R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) (F : Vec d) {g : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet Q) g) :
    volumeAverage (openCubeSet R) (fun x => vecDot F (g x)) =
      (MeasureTheory.volume (openCubeSet R)).toReal⁻¹ *
        inner ℝ (toHilbertVectorL2OfVecField
            (memVectorL2_indicator_cubeSet (Q := Q)
              (memVectorL2_const (U := openCubeSet R) F)))
          (toHilbertVectorL2OfVecField hg) := by
  rw [volumeAverage, ← setIntegral_vecDot_indicator_eq hR (fun _ : Vec d => F) g,
    inner_toHilbertVectorL2OfVecField_eq_integral]

/-! ## 2. Elementary estimates on the normalized average -/

/-- The absolute value of a normalized average is at most the normalized average
of the absolute value. -/
theorem abs_volumeAverage_le_volumeAverage_abs {U : Set (Vec d)} (f : Vec d → ℝ) :
    |volumeAverage U f| ≤ volumeAverage U (fun x => |f x|) := by
  rw [volumeAverage, volumeAverage, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)]
  exact mul_le_mul_of_nonneg_left MeasureTheory.abs_integral_le_integral_abs
    (inv_nonneg.mpr ENNReal.toReal_nonneg)

/-- Monotonicity of the normalized average, with only the upper function
integrable. -/
theorem volumeAverage_mono_of_nonneg {U : Set (Vec d)} {f g : Vec d → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hfg : ∀ x, f x ≤ g x) (hg : IntegrableOn g U volume) :
    volumeAverage U f ≤ volumeAverage U g := by
  rw [volumeAverage, volumeAverage]
  exact mul_le_mul_of_nonneg_left
    (MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall hf) hg
      (Filter.Eventually.of_forall hfg))
    (inv_nonneg.mpr ENNReal.toReal_nonneg)

/-- A constant divisor passes through a normalized average. -/
theorem volumeAverage_div_const {U : Set (Vec d)} (c : ℝ) (f : Vec d → ℝ) :
    volumeAverage U (fun x => f x / c) = volumeAverage U f / c := by
  have h : (fun x => f x / c) = fun x => c⁻¹ * f x := by
    funext x
    rw [div_eq_mul_inv, mul_comm]
  rw [h, SuperdiffusionCLT.Section2.Estimates.Stream.volumeAverage_const_mul U c⁻¹ f,
    div_eq_mul_inv]
  ring

/-- The energy integrand splits into its two normalized averages. -/
theorem volumeAverage_energyInt_decomp {U : Set (Vec d)} (F : Vec d) (g : Vec d → Vec d)
    (c : ℝ) (hIntG : IntegrableOn (fun y => vecNormSq (g y)) U volume)
    (hIntD : IntegrableOn (fun y => vecDot F (g y)) U volume) :
    volumeAverage U (fun y => c * vecNormSq (g y) + vecDot F (g y)) =
      c * volumeAverage U (fun y => vecNormSq (g y)) +
        volumeAverage U (fun y => vecDot F (g y)) := by
  rw [volumeAverage_add' (f := fun y => c * vecNormSq (g y))
      (g := fun y => vecDot F (g y)) (hIntG.const_mul c) hIntD,
    SuperdiffusionCLT.Section2.Estimates.Stream.volumeAverage_const_mul U c
      (fun y => vecNormSq (g y))]

/-! ## 3. The residual `hEnergyInt` of the display, discharged -/

/-- **`hEnergyInt` is not a residual.**  The cube average of
`-(nu/2)|∇u_m|² + e·∇u_m` splits into `-(nu/2)` times the sub-cube energy `A` of
the glued field and the pairing average `B`; `A` is measurable in the sample
with the uniform bound `K`, `B` is measurable in the sample through the
`L²(cu_m)` class of the glued field and bounded by `|e|²/2 + A/2` with Young's
inequality, so the sum is measurable with a uniform bound and integrable over
the probability measure.  Nothing is carried beyond `0 < nu` and the scale
ordering `S.n ≤ S.m`. -/
theorem integrable_hEnergyInt_discharged (d : ℕ) [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) (hnm : S.n ≤ S.m) (e : Vec d) :
    ∀ R ∈ largeCubeSubcubes d S.n S.m,
      Integrable (fun omega : ShellSeq d => volumeAverage (openCubeSet R)
        (fun y => -(nu / 2) * vecNormSq
            (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e) omega y) +
          vecDot (fluxSlot nu S.LPrime P S.n e)
            (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e) omega y)))
        P.toMeasure := by
  intro R hR
  classical
  set F := fluxSlot nu S.LPrime P S.n e with hFdef
  set K : ℝ := (Real.sqrt ((largeCubeSubcubes d S.n S.m).card : ℝ) *
      (nu⁻¹ * Real.sqrt (vecNormSq F))) ^ 2 with hKdef
  set A : ShellSeq d → ℝ := fun omega =>
    vecSqAvg R (fun y => gluedMaximizerGrad hnu S F omega y) with hAdef
  set B : ShellSeq d → ℝ := fun omega => volumeAverage (openCubeSet R)
    (fun y => vecDot F (gluedMaximizerGrad hnu S F omega y)) with hBdef
  have hvol : (MeasureTheory.volume (openCubeSet R)).toReal ≠ 0 := by
    rw [volume_openCubeSet_eq_volume_cubeSet]
    exact ne_of_gt (volume_cubeSet_toReal_pos R)
  have hRdesc : R ∈ descendantsAtDepth (originCube d (S.m : ℤ)) (S.m - S.n) := by
    rw [SuperdiffusionCLT.Section2.Localization.descendantsAtDepth_originCube_eq_largeCubeSubcubes]
    exact hR
  have hAm : Measurable A := by
    rw [hAdef]
    simpa only [gluedMaximizerGrad] using
      measurable_vecSqAvg_gluedGradientField_self_subcube (d := d) hnu S.LPrime S.m F
        (n := S.n) hR
  have hAle : ∀ omega, A omega ≤ K := by
    intro omega
    rw [hAdef, hKdef]
    simpa only [gluedMaximizerGrad] using
      vecSqAvg_gluedGradientField_self_subcube_le (d := d) hnu hnm F omega hR
  have hAnn : ∀ omega, 0 ≤ A omega := by
    intro omega
    rw [hAdef]
    exact vecSqAvg_nonneg R _
  have hconstMem : MemVectorL2 (openCubeSet (originCube d (S.m : ℤ)))
      ((cubeSet R).indicator (fun _ : Vec d => F)) :=
    memVectorL2_indicator_cubeSet (Q := originCube d (S.m : ℤ))
      (memVectorL2_const (U := openCubeSet R) F)
  have hgMem : ∀ omega : ShellSeq d, MemVectorL2 (openCubeSet (originCube d (S.m : ℤ)))
      (fun x => gluedMaximizerGrad hnu S F omega x) := fun omega =>
    memVectorL2_gluedGradientField hnu S.LPrime S.m S.m F omega (originCube d (S.m : ℤ))
  have hBm : Measurable B := by
    rw [hBdef]
    have hclassMeas : Measurable (fun omega : ShellSeq d =>
        toHilbertVectorL2OfVecField (hgMem omega)) :=
      measurable_gluedGradientClass hnu S.LPrime S.m S.m F
    have hinnerMeas : Measurable (fun omega : ShellSeq d =>
        inner ℝ (toHilbertVectorL2OfVecField hconstMem)
          (toHilbertVectorL2OfVecField (hgMem omega))) :=
      ((innerSL ℝ (toHilbertVectorL2OfVecField hconstMem)).continuous.measurable.comp
        hclassMeas)
    have hfun : (fun omega : ShellSeq d => volumeAverage (openCubeSet R)
        (fun y => vecDot F (gluedMaximizerGrad hnu S F omega y))) =
        fun omega : ShellSeq d => (MeasureTheory.volume (openCubeSet R)).toReal⁻¹ *
          inner ℝ (toHilbertVectorL2OfVecField hconstMem)
            (toHilbertVectorL2OfVecField (hgMem omega)) := by
      funext omega
      exact volumeAverage_vecDot_eq_inv_volume_mul_inner hRdesc F (hgMem omega)
    rw [hfun]
    exact hinnerMeas.const_mul _
  have hIntG : ∀ omega : ShellSeq d,
      IntegrableOn (fun y => vecNormSq (gluedMaximizerGrad hnu S F omega y))
        (openCubeSet R) volume := by
    intro omega
    simpa only [gluedMaximizerGrad] using
      integrableOn_vecNormSq_gluedGradientField hnu S.LPrime S.m S.m F omega R
  have hIntD : ∀ omega : ShellSeq d,
      IntegrableOn (fun y => vecDot F (gluedMaximizerGrad hnu S F omega y))
        (openCubeSet R) volume := by
    intro omega
    refine CorrectionFieldData.integrableOn_vecDot_const_left_of_memVectorL2 F ?_
    simpa only [gluedMaximizerGrad] using
      memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.m S.m F omega R
  have hBle : ∀ omega, |B omega| ≤ vecNormSq F / 2 + A omega / 2 := by
    intro omega
    have hIntB : IntegrableOn
        (fun y => vecNormSq F / 2 + vecNormSq (gluedMaximizerGrad hnu S F omega y) / 2)
        (openCubeSet R) volume :=
      (integrable_const _).add ((hIntG omega).div_const 2)
    have h1 : |B omega| ≤ volumeAverage (openCubeSet R)
        (fun y => |vecDot F (gluedMaximizerGrad hnu S F omega y)|) := by
      rw [hBdef]
      exact abs_volumeAverage_le_volumeAverage_abs _
    have h2 : volumeAverage (openCubeSet R)
          (fun y => |vecDot F (gluedMaximizerGrad hnu S F omega y)|)
        ≤ volumeAverage (openCubeSet R)
          (fun y => vecNormSq F / 2 +
            vecNormSq (gluedMaximizerGrad hnu S F omega y) / 2) :=
      volumeAverage_mono_of_nonneg (fun y => abs_nonneg _)
        (fun y => abs_vecDot_le_add_halves_vecNormSq F _) hIntB
    have h3 : volumeAverage (openCubeSet R)
          (fun y => vecNormSq F / 2 +
            vecNormSq (gluedMaximizerGrad hnu S F omega y) / 2) =
        vecNormSq F / 2 + A omega / 2 := by
      have hAeq : A omega = vecSqAvg R (fun y => gluedMaximizerGrad hnu S F omega y) := by
        simp only [hAdef]
      rw [volumeAverage_add' (f := fun y => vecNormSq F / 2)
          (g := fun y => vecNormSq (gluedMaximizerGrad hnu S F omega y) / 2)
          (integrable_const _) ((hIntG omega).div_const 2),
        volumeAverage_const (c := vecNormSq F / 2) hvol,
        volumeAverage_div_const 2 (fun y => vecNormSq (gluedMaximizerGrad hnu S F omega y)),
        hAeq, vecSqAvg_eq_volumeAverage_vecNormSq_openCubeSet]
    linarith only [h1, h2, h3]
  have hdecomp : ∀ omega : ShellSeq d,
      volumeAverage (openCubeSet R)
        (fun y => -(nu / 2) * vecNormSq (gluedMaximizerGrad hnu S F omega y) +
          vecDot F (gluedMaximizerGrad hnu S F omega y)) =
        -(nu / 2) * A omega + B omega := by
    intro omega
    have hAeq : A omega = vecSqAvg R (fun y => gluedMaximizerGrad hnu S F omega y) := by
      simp only [hAdef]
    have hBeq : B omega =
        volumeAverage (openCubeSet R) (fun y => vecDot F (gluedMaximizerGrad hnu S F omega y)) := by
      simp only [hBdef]
    rw [volumeAverage_energyInt_decomp F (gluedMaximizerGrad hnu S F omega) (-(nu / 2))
        (hIntG omega) (hIntD omega),
      hAeq, vecSqAvg_eq_volumeAverage_vecNormSq_openCubeSet, hBeq]
  have hslack : ∀ omega, |-(nu / 2) * A omega + B omega| ≤
      (nu / 2) * K + vecNormSq F / 2 + K / 2 := by
    intro omega
    have h1 : |-(nu / 2) * A omega + B omega| ≤ |-(nu / 2) * A omega| + |B omega| :=
      abs_add_le _ _
    have h2 : |-(nu / 2) * A omega| = (nu / 2) * A omega := by
      rw [abs_mul, abs_neg, abs_of_nonneg (by linarith only [hnu.le] : (0 : ℝ) ≤ nu / 2),
        abs_of_nonneg (hAnn omega)]
    have h3 : (nu / 2) * A omega ≤ (nu / 2) * K :=
      mul_le_mul_of_nonneg_left (hAle omega) (by linarith only [hnu.le])
    have h4 : A omega / 2 ≤ K / 2 := by linarith only [hAle omega]
    rw [h2] at h1
    linarith only [h1, h3, h4, hBle omega]
  have hsumMeas : Measurable (fun omega : ShellSeq d => -(nu / 2) * A omega + B omega) :=
    ((hAm.const_mul _).add hBm)
  have hInt : Integrable (fun omega : ShellSeq d => -(nu / 2) * A omega + B omega)
      P.toMeasure :=
    Integrable.of_bound hsumMeas.aestronglyMeasurable _
      (Filter.Eventually.of_forall hslack)
  refine hInt.congr (Filter.Eventually.of_forall fun omega => ?_)
  exact (hdecomp omega).symm

/-! ## 4. The display, one residual lighter -/

/-- **`term3_cgBound_finalB`.**  The printed display `e.RHS.term3.A` — the
`_hCgBound` binder of the term-3 final assembly — verbatim, from the
binders together with the five residuals of `term3_cgBound_closeE` that survive:
`hAnnealedSub`, `hAnnealedBig`, `hPigeon`, `hde1` and `hCerr`.  The sixth,
`hEnergyInt`, is discharged by `integrable_hEnergyInt_discharged`.  The
conclusion is character-for-character the display of `term3_cgBound_closeE`. -/
theorem term3_cgBound_finalB
    (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (nu : ℝ) (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P) (hJ1V2 : ShellLawJ1Restriction d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (hSorder : ScalesOrdering S)
    (hTwoHLeM : 2 * S.h ≤ S.m) (hHundredALeH : 100 * S.a ≤ S.h)
    (hWindowVsOffset : S.h + 1 ≤ 3 ^ S.a)
    (e : Vec d) (he : vecNormSq e = 1)
    (delta etaL : ℝ) (hdelta : 0 ≤ delta) (hetaL : 0 ≤ etaL)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      SuperdiffusionCLT.Section3.Setup.IsDirichletResponse
        omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega))
    (Cerr : ℝ)
    (hde1 : delta + etaL ≤ 1)
    (hCerr : cgBoundConst (cgBoundAmpP d P S w) (cgBoundAmpW nu S) (bEllipConst d) ≤ Cerr)
    (hAnnealedSub : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      ∫ omega : ShellSeq d,
          energySubQCarrier nu P S e (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e))
            (gluedSubcubeGrad hnu S (fluxSlot nu S.LPrime P S.n e)) omega R
        ∂P.toMeasure =
        (1 / 2 : ℝ) * sigmaBarStarInvSeq nu S.LPrime P S.n *
          vecNormSq (fluxSlot nu S.LPrime P S.n e))
    (hAnnealedBig : ∫ omega : ShellSeq d,
          energyBigQCarrier nu P S e
            (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e)) omega
        ∂P.toMeasure =
        (1 / 2 : ℝ) * sigmaBarStarInvSeq nu S.LPrime P S.m *
          vecNormSq (fluxSlot nu S.LPrime P S.n e))
    (hPigeon : |1 - (sigmaBarStarInvSeq nu S.LPrime P S.n)⁻¹ *
      sigmaBarStarInvSeq nu S.LPrime P S.m| ≤ delta + etaL) :
    ∫ omega : ShellSeq d,
        ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
          ∑ R ∈ largeCubeSubcubes d S.n S.m,
            vecDot (volumeAverageVec (openCubeSet R) ((w omega).toH1Function.grad))
              (volumeAverageVec (openCubeSet R)
                (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
                  (gluedGradientField hnu S.LPrime S.m S.m
                      (fluxSlot nu S.LPrime P S.n e) omega y -
                    gluedGradientField hnu S.LPrime S.n S.m
                      (fluxSlot nu S.LPrime P S.n e) omega y))) ∂P.toMeasure ≤
      (((largeCubeSubcubes d (coarseBlockScale d S) S.m).card : ℝ)⁻¹ *
          ∑ z' ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
            (((descendantsAtDepth z' (coarseBlockScale d S - S.n)).card : ℕ) : ℝ)⁻¹ *
              ∑ z ∈ descendantsAtDepth z' (coarseBlockScale d S - S.n),
                ∫ omega : ShellSeq d,
                  translatedBlockHalfWeight nu S.LPrime w omega z' z
                  ∂P.toMeasure) ^ ((1 : ℝ) / 2) *
          (delta + etaL) ^ ((1 : ℝ) / 2) +
        Cerr * (3 : ℝ) ^ (-(((S.ellPrime - S.ell : ℕ) : ℝ) / 4)) *
          ((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ) * nu ^ (-(5 : ℝ) / 2) := by
  exact term3_cgBound_closeE d hd nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder
    hTwoHLeM hHundredALeH hWindowVsOffset e he delta etaL hdelta hetaL w hw Cerr
    hde1 hCerr hAnnealedSub hAnnealedBig
    (integrable_hEnergyInt_discharged d hnu P S
      (ScalesOrdering.mem_pigeon_range hSorder).1.2 e)
    hPigeon

end

end SuperdiffusionCLT.Section3.Terms
