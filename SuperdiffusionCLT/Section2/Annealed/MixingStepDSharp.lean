/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.MixingLoewnerStepsB
public import SuperdiffusionCLT.Section2.Localization.CutoffSkewBounds
public import SuperdiffusionCLT.Section2.Localization.LocalizationWitnessPackaging
public import SuperdiffusionCLT.Section2.Localization.UnsymmetricConversion
public import SuperdiffusionCLT.Section3.ResponseFields.RegboundsInputs
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3Inputs

/-!
# The sharp `nu^{-2}` Step-D amplitude: the `min{1, .}` truncation

The direct Step-D route consumes the *uncapped* sandwich
witness `W = localizationWitness = 2 theta (1 + theta)`:

> the per-`omega` clause is `(1 - W) s^-1_{m,*}(cu_h) <= s^-1_{l,*}(cu_h)`,
> so the scalar gap is bounded by `E[W * s^-1_{m,*}(cu_h)_{00}]`, and the entry
> bound `s^-1_{m,*} <= nu^-1` pulls out a `nu^-1`, giving
> `nu^-1 * (localizationConst d * nu^-2 * 3^-(m-h)) = O(nu^-3 3^-(m-h))`.

The `nu^-2` in that inner amplitude is the *quadratic* bookkeeping term of
`W = 2 theta (1 + theta)`: the printed packaging
`localizationWitness_pair_isBigO` keeps both `theta` and `theta^2`, and since
`theta` itself carries `nu^-1`, the packaged amplitude is `nu^-2`.

The manuscript's printed Step-D display `C nu^-2 3^{-(n-h)/4}` and its `shom^-1` comparison
carry only `nu^-2`, and the printed proof reaches it by the *`min{1, .}` truncation*:

> `|s^-1_L(Q) - s^-1_{n'}(Q)| <= C nu^-1 min{1, |balanced - Id|}`.

The truncation discards the quadratic `theta^2` tail: for `1 <= theta` the crude
ellipticity bound alone absorbs the pair, so only the *linear* `min{1, theta}`
survives, and the interpolation factor `nu^-1` times that linear amplitude is
`nu^-2`, not `nu^-3`. The `min{1, .}` Loewner algebra of
`LoewnerMinAlgebra` is precisely this step
(`matLoewnerLE_add_min_smul_one_of_pair`).

This module proves the sharpened Step D at `nu^-2`:

* `stepDCapWitness := min 1 o localizationWitness` — the truncated witness;
* `stepDCapWitness_isBigO`: it is `O_{Gamma_2}(4 * theta_amp)`, i.e. at the
  *linear* amplitude `nu^-1 * gaugeAmplitudeConst d * 3^-(m-h)`, because
  `min 1 (2 theta (1 + theta)) <= 4 theta` pointwise;
* `stepDCapWitness_moment`: its first moment is at most
  `stepDSharpConst d * nu^-2 * 3^-(m-h)`;
* `stepD_exists_sharp`: the `hStepD` `Exists Y` shape at
  `stepDSharpConst d * nu^-2 * 3^-(m-h)` — the printed `nu`-power, with a
  `nu`-free constant and a *stronger* scale rate;
* `stepD_exists_sharp_printed`: the same at the printed amplitude
  `stepDSharpConst d * nu^-2 * 3^-((m-h)/2)` verbatim, since
  `3^-(m-h) <= 3^-((m-h)/2)`.

The constants are named: `stepDSharpConst d = 4 * gammaMomentConst 2 *
gaugeAmplitudeConst d`, with `gaugeAmplitudeConst d = matrixOperatorNorm_diamConst d
* gammaTriangleConst 2`. -/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Annealed

open Homogenization MeasureTheory
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Localization
open SuperdiffusionCLT.Section3.Setup

noncomputable section

variable {d : ℕ}

/-! ## The truncated witness and the sharp constant -/

/-- **The printed `min{1, .}` truncation of the sandwich witness.**  The printed
Step-D conversion bounds the per-cube gap by
`C nu^-1 min{1, |balanced - Id|}`, not by the uncapped balanced error; this is
the witness of the truncated sandwich
`matLoewnerLE_add_min_smul_one_of_pair`. -/
def stepDCapWitness (nu : ℝ) (h m l : ℕ) (omega : ShellSeq d) : ℝ :=
  min 1 (localizationWitness nu h m l omega)

/-- **The constant of the sharpened Step-D amplitude.**
`stepDSharpConst d = 4 * gammaMomentConst 2 * gaugeAmplitudeConst d`, the
`nu`-free factor of the amplitude `stepDSharpConst d * nu^-2 * 3^-(m-h)`: the
factor `4` is the pointwise domination `min 1 (2 theta (1+theta)) <= 4 theta`,
`gammaMomentConst 2` is the first-moment constant of `Gamma_2`, and
`gaugeAmplitudeConst d = matrixOperatorNorm_diamConst d * gammaTriangleConst 2`
is the `d`-part of the linear `theta` amplitude. -/
def stepDSharpConst (d : ℕ) : ℝ :=
  4 * gammaMomentConst 2 *
    SuperdiffusionCLT.Section2.Localization.gaugeAmplitudeConst d

/-- **Positivity of the sharp constant** at `d >= 1`. -/
theorem stepDSharpConst_pos [NeZero d] : 0 < stepDSharpConst d := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  unfold stepDSharpConst
  exact mul_pos (mul_pos (by norm_num) (gammaMomentConst_pos (σ := 2) two_pos))
    (SuperdiffusionCLT.Section2.Localization.gaugeAmplitudeConst_pos hd)

/-- **Nonnegativity of the truncated witness.** -/
theorem stepDCapWitness_nonneg {nu : ℝ} (hnu : 0 ≤ nu) (h m l : ℕ) (omega : ShellSeq d) :
    0 ≤ stepDCapWitness nu h m l omega :=
  le_min zero_le_one (localizationWitness_nonneg hnu h m l omega)

/-- **Measurability of the truncated witness.** -/
theorem measurable_stepDCapWitness (nu : ℝ) (h m l : ℕ) :
    Measurable (stepDCapWitness nu h m l : ShellSeq d → ℝ) :=
  measurable_min_one (measurable_localizationWitness nu h m l)

/-! ## The real-arithmetic helpers -/

/-- `(3^m)⁻¹ * 3^n = 3^(-(m-n))`, the absorption of the `3^n` prefactor into
the printed rate. -/
private theorem three_pow_mul_inv {n m : ℕ} (hnm : n ≤ m) :
    ((3 : ℝ) ^ m)⁻¹ * (3 : ℝ) ^ n = (3 : ℝ) ^ (-(((m - n : ℕ) : ℝ))) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hexp : ((n : ℕ) : ℝ) - ((m : ℕ) : ℝ) = -(((m - n : ℕ) : ℝ)) := by
    rw [Nat.cast_sub hnm]
    ring
  rw [← Real.rpow_natCast 3 m, ← Real.rpow_natCast 3 n, inv_mul_eq_div,
    ← Real.rpow_sub h3, hexp]

/-- The `3^n`-first form of `three_pow_mul_inv`. -/
private theorem three_pow_nat_sub {n m : ℕ} (hnm : n ≤ m) :
    (3 : ℝ) ^ n * ((3 : ℝ) ^ m)⁻¹ = (3 : ℝ) ^ (-(((m - n : ℕ) : ℝ))) := by
  rw [mul_comm, three_pow_mul_inv hnm]

/-- `nu^(-2) = nu⁻¹ * nu⁻¹`. -/
private theorem rpow_neg_two_of_pos {nu : ℝ} (hnu : 0 < nu) :
    nu ^ (-(2 : ℝ)) = nu⁻¹ * nu⁻¹ := by
  rw [Real.rpow_neg hnu.le, Real.rpow_two, pow_two, mul_inv]

/-- `3^(-g) <= 3^(-g/2)` for `g >= 0`. -/
private theorem three_rpow_neg_le_half (g : ℕ) :
    (3 : ℝ) ^ (-((g : ℕ) : ℝ)) ≤ (3 : ℝ) ^ (-(((g : ℕ) : ℝ) / 2)) := by
  refine (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 3)).2 ?_
  have hg : (0 : ℝ) ≤ ((g : ℕ) : ℝ) := by positivity
  linarith only [hg]

/-- A nonnegative random variable vanishes at any nonnegative amplitude. -/
private theorem isBigOWith_gammaSigma_zero (mu : Measure (ShellSeq d))
    (σ A : ℝ) (hA : 0 ≤ A) :
    IsBigOWith mu (gammaSigma σ) (fun _ : ShellSeq d => (0 : ℝ)) A := by
  intro t ht
  have hAt : 0 ≤ A * t := mul_nonneg hA (le_trans zero_le_one ht)
  have hempty : upperTailEvent (fun _ : ShellSeq d => (0 : ℝ)) (A * t) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro omega hω
    simp only [upperTailEvent, Set.mem_ofPred_eq] at hω
    exact absurd hω (not_lt.mpr hAt)
  rw [hempty, measureReal_empty]
  exact (inv_pos.mpr (Real.exp_pos _)).le

/-- A positive-semidefinite matrix dominates zero in Loewner order. -/
private theorem matLoewnerLE_zero_of_posSemidef {A : Mat d} (hpsd : A.PosSemidef) :
    MatLoewnerLE (0 : Mat d) A := by
  refine matLoewnerLE_of_quad_le fun y => ?_
  rw [quad_zero]
  exact posSemidef_quadratic_nonneg hpsd y

/-! ## The linear `theta` amplitude -/

/-- **The `theta` amplitude is linear in `nu`.**  The pointwise relative bound
`localizationTheta nu h m l = nu⁻¹ (d³ sqrt d) 3^h · upperShellDerivGauge(h,m,l)`
is `O_{Gamma_2}` at the *linear* amplitude
`nu⁻¹ * gaugeAmplitudeConst d * 3^-(m-h)`: the proved `Gamma_2` gauge bound of
the upper-shell derivative gauge at the gap `m - h` absorbs the `3^h` prefactor.
This is the `theta` that the printed `min{1, .}` truncation caps; the capped
bound below uses only this linear amplitude, never the quadratic `theta^2`. -/
private theorem localizationTheta_isBigO [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)} (hJ3 : ShellLawJ3 d P) {h m l : ℕ}
    (hhm : h < m) (hml : m ≤ l) :
    IsBigO P.toMeasure (gammaSigma 2) (localizationTheta nu h m l)
      (nu⁻¹ * SuperdiffusionCLT.Section2.Localization.gaugeAmplitudeConst d *
        (3 : ℝ) ^ (-((m - h : ℕ) : ℝ))) := by
  have hθnn : ∀ omega : ShellSeq d, 0 ≤ localizationTheta nu h m l omega :=
    fun omega => localizationTheta_nonneg nu hnu.le h m l omega
  refine (isBigOWith_iff_isBigO_of_nonneg hθnn).1 ?_
  by_cases hlt : m < l
  · have hgauge : IsBigOWith P.toMeasure (gammaSigma 2)
        (SuperdiffusionCLT.Section3.ResponseFields.upperShellDerivGauge h m l)
        (gammaTriangleConst 2 * ((3 : ℝ) ^ m)⁻¹) :=
      SuperdiffusionCLT.Section3.ResponseFields.isBigOWith_gammaSigma_upperShellDerivGauge
        (P := P) hJ3 (by omega) hlt
    have hθ1 : IsBigOWith P.toMeasure (gammaSigma 2)
        (fun omega : ShellSeq d => nu⁻¹ * (matrixOperatorNorm_diamConst d *
          (3 : ℝ) ^ h *
          SuperdiffusionCLT.Section3.ResponseFields.upperShellDerivGauge h m l omega))
        (nu⁻¹ * (matrixOperatorNorm_diamConst d * (3 : ℝ) ^ h *
          (gammaTriangleConst 2 * ((3 : ℝ) ^ m)⁻¹))) :=
      (hgauge.const_mul (c := matrixOperatorNorm_diamConst d * (3 : ℝ) ^ h)
        (mul_nonneg (matrixOperatorNorm_diamConst_nonneg d)
          (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) h))).const_mul
        (c := nu⁻¹) (inv_nonneg.mpr hnu.le)
    have hfun : (localizationTheta nu h m l : ShellSeq d → ℝ)
        = fun omega => nu⁻¹ * (matrixOperatorNorm_diamConst d * (3 : ℝ) ^ h *
          SuperdiffusionCLT.Section3.ResponseFields.upperShellDerivGauge h m l omega) := by
      funext omega
      unfold localizationTheta
      ring
    have hkey : nu⁻¹ * (matrixOperatorNorm_diamConst d * (3 : ℝ) ^ h *
        (gammaTriangleConst 2 * ((3 : ℝ) ^ m)⁻¹))
        = nu⁻¹ * SuperdiffusionCLT.Section2.Localization.gaugeAmplitudeConst d *
          (3 : ℝ) ^ (-((m - h : ℕ) : ℝ)) := by
      have hp := three_pow_nat_sub (n := h) (m := m) (le_of_lt hhm)
      simp only [SuperdiffusionCLT.Section2.Localization.gaugeAmplitudeConst]
      linear_combination (norm := ring_nf)
        (nu⁻¹ * (matrixOperatorNorm_diamConst d * gammaTriangleConst 2)) * hp
    rw [hfun]
    exact hθ1.mono_scale (le_of_eq hkey)
  · have hme : m = l := le_antisymm hml (not_lt.mp hlt)
    subst hme
    have hzero : ∀ omega : ShellSeq d,
        SuperdiffusionCLT.Section3.ResponseFields.upperShellDerivGauge h m m omega = 0 := by
      intro omega
      simp [SuperdiffusionCLT.Section3.ResponseFields.upperShellDerivGauge]
    have hfun : (localizationTheta nu h m m : ShellSeq d → ℝ)
        = fun _ : ShellSeq d => (0 : ℝ) := by
      funext omega
      unfold localizationTheta
      rw [hzero omega]
      ring
    have hA0 : 0 ≤ nu⁻¹ * SuperdiffusionCLT.Section2.Localization.gaugeAmplitudeConst d *
        (3 : ℝ) ^ (-((m - h : ℕ) : ℝ)) :=
      mul_nonneg (mul_nonneg (inv_nonneg.mpr hnu.le)
        (SuperdiffusionCLT.Section2.Localization.gaugeAmplitudeConst_nonneg d))
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
    rw [hfun]
    exact isBigOWith_gammaSigma_zero P.toMeasure 2 _ hA0

/-! ## The truncated witness at the linear amplitude -/

/-- **The truncated witness is `Gamma_2` at the *linear* amplitude.**  Pointwise
`min 1 (2 theta (1 + theta)) <= 4 theta`: for `theta <= 1` the quadratic term is
absorbed by `2 theta (1 + theta) <= 4 theta`, while for `1 <= theta` the
truncation gives `1 <= 4 theta`.  So the cap `min{1, .}` removes the quadratic
`theta^2` tail and the amplitude is the linear
`4 * (nu⁻¹ gaugeAmplitudeConst d 3^-(m-h))`, not the packaged quadratic `nu^-2`
of `localizationWitness_pair_isBigO`. -/
private theorem stepDCapWitness_isBigO [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)} (hJ3 : ShellLawJ3 d P) {h m l : ℕ}
    (hhm : h < m) (hml : m ≤ l) :
    IsBigOWith P.toMeasure (gammaSigma 2) (stepDCapWitness nu h m l)
      (4 * (nu⁻¹ * SuperdiffusionCLT.Section2.Localization.gaugeAmplitudeConst d *
        (3 : ℝ) ^ (-((m - h : ℕ) : ℝ)))) := by
  have hθ := localizationTheta_isBigO hnu hJ3 hhm hml
  have hθw : IsBigOWith P.toMeasure (gammaSigma 2) (localizationTheta nu h m l)
      (nu⁻¹ * SuperdiffusionCLT.Section2.Localization.gaugeAmplitudeConst d *
        (3 : ℝ) ^ (-((m - h : ℕ) : ℝ))) :=
    (isBigOWith_iff_isBigO_of_nonneg
      (fun omega => localizationTheta_nonneg nu hnu.le h m l omega)).2 hθ
  have h4 : IsBigOWith P.toMeasure (gammaSigma 2)
      (fun omega : ShellSeq d => 4 * localizationTheta nu h m l omega)
      (4 * (nu⁻¹ * SuperdiffusionCLT.Section2.Localization.gaugeAmplitudeConst d *
        (3 : ℝ) ^ (-((m - h : ℕ) : ℝ)))) :=
    hθw.const_mul (c := 4) (by norm_num)
  refine h4.of_le (fun omega => ?_)
  have hW : localizationWitness nu h m l omega
      = 2 * (localizationTheta nu h m l omega +
          localizationTheta nu h m l omega ^ (2 : ℝ)) := by
    unfold localizationWitness localizationD
    rw [Real.rpow_two]
    ring
  have ht : 0 ≤ localizationTheta nu h m l omega :=
    localizationTheta_nonneg nu hnu.le h m l omega
  rw [stepDCapWitness, hW]
  rcases le_total (localizationTheta nu h m l omega) 1 with ht1 | ht1
  · have hsq : localizationTheta nu h m l omega ^ (2 : ℝ)
        ≤ localizationTheta nu h m l omega := by
      rw [Real.rpow_two, pow_two]
      exact mul_le_of_le_one_right ht ht1
    calc min 1 (2 * (localizationTheta nu h m l omega +
            localizationTheta nu h m l omega ^ (2 : ℝ)))
        ≤ 2 * (localizationTheta nu h m l omega +
            localizationTheta nu h m l omega ^ (2 : ℝ)) := min_le_right _ _
      _ ≤ 4 * localizationTheta nu h m l omega := by linarith only [hsq]
  · calc min 1 (2 * (localizationTheta nu h m l omega +
            localizationTheta nu h m l omega ^ (2 : ℝ)))
        ≤ 1 := min_le_left _ _
      _ ≤ 4 * localizationTheta nu h m l omega := by linarith only [ht1]

/-- **The first moment of the truncated witness is `nu^-2`-order.**  Combining
the linear `Gamma_2` amplitude with the `Gamma_2` first-moment estimate gives
`E[min 1 W] <= gammaMomentConst 2 * 4 * (nu⁻¹ gaugeAmplitudeConst d 3^-(m-h))`;
multiplying by the entry bound `s^-1_{m,*}(cu_h)_{00} <= nu⁻¹` (the interpolation
factor of the printed proof) gives the sharpened amplitude
`stepDSharpConst d * nu^-2 * 3^-(m-h)`.  The extra `nu^-1` of the proved route is
gone: the cap discards the `nu^-2` quadratic term of the witness. -/
private theorem stepDCapWitness_moment [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)} (hJ3 : ShellLawJ3 d P) {h m l : ℕ}
    (hhm : h < m) (hml : m ≤ l) :
    ∫ omega : ShellSeq d, stepDCapWitness nu h m l omega *
        sigmaStarInvCoarse (Homogenization.openCubeSet (Homogenization.originCube d (h : ℤ)))
          (coefficientCutoff nu omega m).toCoeffField 0 0 ∂P.toMeasure
      ≤ stepDSharpConst d * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-((m - h : ℕ) : ℝ)) := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hKpos : 0 < 4 * (nu⁻¹ * SuperdiffusionCLT.Section2.Localization.gaugeAmplitudeConst d *
      (3 : ℝ) ^ (-((m - h : ℕ) : ℝ))) :=
    mul_pos (by norm_num) (mul_pos (mul_pos (inv_pos.mpr hnu)
      (SuperdiffusionCLT.Section2.Localization.gaugeAmplitudeConst_pos hd))
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _))
  have hcap := stepDCapWitness_isBigO (P := P) hnu hJ3 hhm hml
  have hcapO : IsBigO P.toMeasure (gammaSigma 2) (stepDCapWitness nu h m l)
      (4 * (nu⁻¹ * SuperdiffusionCLT.Section2.Localization.gaugeAmplitudeConst d *
        (3 : ℝ) ^ (-((m - h : ℕ) : ℝ)))) :=
    (isBigOWith_iff_isBigO_of_nonneg
      (fun omega => stepDCapWitness_nonneg hnu.le h m l omega)).1 hcap
  have hcap_int : Integrable (stepDCapWitness nu h m l) P.toMeasure := by
    have hraw := integrable_rpow_of_isBigOWith_gammaSigma (μ := P.toMeasure) (σ := 2) (p := 1)
      (K := 4 * (nu⁻¹ * SuperdiffusionCLT.Section2.Localization.gaugeAmplitudeConst d *
        (3 : ℝ) ^ (-((m - h : ℕ) : ℝ)))) two_pos hKpos le_rfl
      (fun omega => stepDCapWitness_nonneg hnu.le h m l omega)
      (measurable_stepDCapWitness nu h m l).aemeasurable hcap
    simpa only [Real.rpow_one] using hraw
  have hmom_cap : ∫ omega : ShellSeq d, stepDCapWitness nu h m l omega ∂P.toMeasure
      ≤ gammaMomentConst 2 *
        (4 * (nu⁻¹ * SuperdiffusionCLT.Section2.Localization.gaugeAmplitudeConst d *
          (3 : ℝ) ^ (-((m - h : ℕ) : ℝ)))) := by
    have hraw := integral_abs_rpow_le_of_isBigO_gammaSigma (μ := P.toMeasure) (σ := 2) (p := 1)
      (K := 4 * (nu⁻¹ * SuperdiffusionCLT.Section2.Localization.gaugeAmplitudeConst d *
        (3 : ℝ) ^ (-((m - h : ℕ) : ℝ)))) two_pos hKpos le_rfl
      (measurable_stepDCapWitness nu h m l).aemeasurable hcapO
    have haux : (fun omega : ShellSeq d => |stepDCapWitness nu h m l omega| ^ (1 : ℝ))
        = fun omega => stepDCapWitness nu h m l omega := by
      funext omega
      rw [Real.rpow_one, abs_of_nonneg (stepDCapWitness_nonneg hnu.le h m l omega)]
    rw [haux] at hraw
    simpa only [Real.rpow_one, Real.one_rpow, mul_one] using hraw
  have hpt : ∀ omega : ShellSeq d,
      stepDCapWitness nu h m l omega *
        sigmaStarInvCoarse (Homogenization.openCubeSet (Homogenization.originCube d (h : ℤ)))
          (coefficientCutoff nu omega m).toCoeffField 0 0
      ≤ stepDCapWitness nu h m l omega * nu⁻¹ := by
    intro omega
    refine mul_le_mul_of_nonneg_left ?_ (stepDCapWitness_nonneg hnu.le h m l omega)
    exact (le_abs_self _).trans (abs_entry_sigmaStarInvCoarse_openCubeSet_le hnu omega m
      (Homogenization.originCube d (h : ℤ)) 0 0)
  have hIntRhs : Integrable (fun omega : ShellSeq d => stepDCapWitness nu h m l omega * nu⁻¹)
      P.toMeasure := hcap_int.mul_const nu⁻¹
  have hIntLhs : Integrable (fun omega : ShellSeq d => stepDCapWitness nu h m l omega *
      sigmaStarInvCoarse (Homogenization.openCubeSet (Homogenization.originCube d (h : ℤ)))
        (coefficientCutoff nu omega m).toCoeffField 0 0) P.toMeasure :=
    hIntRhs.mono' ((measurable_stepDCapWitness nu h m l).mul
      (measurable_entry_sigmaStarInvCoarse_openCubeSet hnu m
        (Homogenization.originCube d (h : ℤ)) 0 0)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun omega => by
        rw [Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (stepDCapWitness_nonneg hnu.le h m l omega)]
        exact mul_le_mul_of_nonneg_left (abs_entry_sigmaStarInvCoarse_openCubeSet_le hnu omega m
          (Homogenization.originCube d (h : ℤ)) 0 0)
          (stepDCapWitness_nonneg hnu.le h m l omega))
  have hmono : ∫ omega : ShellSeq d, stepDCapWitness nu h m l omega *
        sigmaStarInvCoarse (Homogenization.openCubeSet (Homogenization.originCube d (h : ℤ)))
          (coefficientCutoff nu omega m).toCoeffField 0 0 ∂P.toMeasure
      ≤ ∫ omega : ShellSeq d, stepDCapWitness nu h m l omega * nu⁻¹ ∂P.toMeasure :=
    integral_mono hIntLhs hIntRhs hpt
  rw [integral_mul_const nu⁻¹ (fun omega : ShellSeq d => stepDCapWitness nu h m l omega)]
    at hmono
  calc ∫ omega : ShellSeq d, stepDCapWitness nu h m l omega *
        sigmaStarInvCoarse (Homogenization.openCubeSet (Homogenization.originCube d (h : ℤ)))
          (coefficientCutoff nu omega m).toCoeffField 0 0 ∂P.toMeasure
      ≤ (∫ omega : ShellSeq d, stepDCapWitness nu h m l omega ∂P.toMeasure) * nu⁻¹ := hmono
    _ ≤ (gammaMomentConst 2 *
          (4 * (nu⁻¹ * SuperdiffusionCLT.Section2.Localization.gaugeAmplitudeConst d *
            (3 : ℝ) ^ (-((m - h : ℕ) : ℝ))))) * nu⁻¹ :=
        mul_le_mul_of_nonneg_right hmom_cap (inv_nonneg.mpr hnu.le)
    _ = stepDSharpConst d * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-((m - h : ℕ) : ℝ)) := by
        rw [rpow_neg_two_of_pos hnu]
        unfold stepDSharpConst
        ring

/-! ## The capped sandwich -/

/-- **The `min{1, .}`-capped sandwich.**  Replacing the witness
`W = localizationWitness` by `min 1 W` preserves the per-`omega` relative
Loewner bound of `cutoffLoewnerClauses`: where `W <= 1` the two witnesses agree,
and where `1 <= W` the left side collapses to `(1 - 1) • s^-1_{m,*}(cu_h) = 0`,
dominated by the positive semidefinite `s^-1_{l,*}(cu_h)`.  This is the printed
truncation, and it is where the quadratic `theta^2` tail of the uncapped witness
is discarded. -/
private theorem cappedSandwich [NeZero d] {nu : ℝ} (hnu : 0 < nu) {h m l : ℕ}
    (hml : m ≤ l) (omega : ShellSeq d) :
    Homogenization.MatLoewnerLE
      ((1 - stepDCapWitness nu h m l omega) •
        sigmaStarInvCoarse (Homogenization.openCubeSet (Homogenization.originCube d (h : ℤ)))
          (coefficientCutoff nu omega m).toCoeffField)
      (sigmaStarInvCoarse (Homogenization.openCubeSet (Homogenization.originCube d (h : ℤ)))
        (coefficientCutoff nu omega l).toCoeffField) := by
  have hneU : Set.Nonempty
      (Homogenization.openCubeSet (Homogenization.originCube d (h : ℤ))) := by
    refine ⟨Homogenization.cubeCenter (Homogenization.originCube d (h : ℤ)), ?_⟩
    rw [← Homogenization.ball_cubeCenter_eq_openCubeSet, Metric.mem_ball, dist_self]
    exact Homogenization.cubeRadius_pos _
  have hclo := (cutoffLoewnerClauses nu hnu h m l hml
    (⟨Homogenization.openCubeSet (Homogenization.originCube d (h : ℤ)),
      Homogenization.isOpenBoundedConvexDomain_openCubeSet (Homogenization.originCube d (h : ℤ)),
      hneU⟩ : Homogenization.Book.Ch02.Domain d) le_rfl omega).2.2.1
  rcases le_total (localizationWitness nu h m l omega) 1 with hW1 | hW1
  · rwa [stepDCapWitness, min_eq_right hW1]
  · rw [stepDCapWitness, min_eq_left hW1, sub_self, zero_smul]
    have hpsd := SuperdiffusionCLT.Section3.Terms.posSemidef_sigmaStarInvCoarse_cutoffCube
      hnu l omega (Homogenization.originCube d (h : ℤ))
    rw [SuperdiffusionCLT.Section3.Terms.sigmaStarInvCoarse_cubeSet_eq_openCubeSet] at hpsd
    exact matLoewnerLE_zero_of_posSemidef hpsd

/-! ## The sharpened Step D at `nu^-2` -/

/-- **The sharpened Step-D scalar cutoff gap at `nu^-2`.**  Combining the capped
sandwich with the capped first moment `stepDCapWitness_moment` gives the scalar
cutoff gap at the amplitude `stepDSharpConst d * nu^-2 * 3^-(m-h)` — the printed
`nu`-power, with a `nu`-free constant.  No moment hypothesis and no `nu <= 1`
survives: the only premises are `hJ3`, `0 < nu`, and `h < m <= l`. -/
theorem stepD_scalarGap_sharp [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (hJ3 : ShellLawJ3 d P) {h m l : ℕ}
    (hhm : h < m) (hml : m ≤ l) :
    sigmaBarStarInvScalar nu m P
        (Homogenization.cubeSet (Homogenization.originCube d (h : ℤ))) ≤
      sigmaBarStarInvScalar nu l P
          (Homogenization.cubeSet (Homogenization.originCube d (h : ℤ))) +
        stepDSharpConst d * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-((m - h : ℕ) : ℝ)) := by
  have hcap_bound : ∀ ω : ShellSeq d, ‖stepDCapWitness nu h m l ω‖ ≤ (1 : ℝ) := by
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (stepDCapWitness_nonneg hnu.le h m l ω)]
    exact min_le_left _ _
  have hcap_int : Integrable (stepDCapWitness nu h m l) P.toMeasure :=
    Integrable.of_bound (measurable_stepDCapWitness nu h m l).aestronglyMeasurable 1
      (Filter.Eventually.of_forall hcap_bound)
  refine stepD_scalarGap_of_sandwich_moment hnu P (stepDCapWitness nu h m l)
    (fun ω => cappedSandwich hnu hml ω) ?_ ?_ ?_
    (stepDCapWitness_moment (P := P) hnu hJ3 hhm hml)
  · refine Integrable.of_bound (measurable_entry_sigmaStarInvCoarse_openCubeSet hnu m
      (Homogenization.originCube d (h : ℤ)) 0 0).aestronglyMeasurable nu⁻¹ ?_
    filter_upwards with ω
    simpa only [Real.norm_eq_abs] using
      abs_entry_sigmaStarInvCoarse_openCubeSet_le hnu ω m (Homogenization.originCube d (h : ℤ)) 0 0
  · refine Integrable.of_bound (measurable_entry_sigmaStarInvCoarse_openCubeSet hnu l
      (Homogenization.originCube d (h : ℤ)) 0 0).aestronglyMeasurable nu⁻¹ ?_
    filter_upwards with ω
    simpa only [Real.norm_eq_abs] using
      abs_entry_sigmaStarInvCoarse_openCubeSet_le hnu ω l (Homogenization.originCube d (h : ℤ)) 0 0
  · refine (hcap_int.mul_const nu⁻¹).mono' ((measurable_stepDCapWitness nu h m l).mul
      (measurable_entry_sigmaStarInvCoarse_openCubeSet hnu m
        (Homogenization.originCube d (h : ℤ)) 0 0)).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (stepDCapWitness_nonneg hnu.le h m l ω)]
    exact mul_le_mul_of_nonneg_left
      (abs_entry_sigmaStarInvCoarse_openCubeSet_le hnu ω m (Homogenization.originCube d (h : ℤ)) 0 0)
      (stepDCapWitness_nonneg hnu.le h m l ω)

/-- **`hStepD`'s `Exists` conclusion at `nu^-2`.**  The proved
`stepD_exists_of_scalar_gap` turns the sharpened scalar gap into the `∃ Y` shape
of the `hStepD` binder verbatim, at the `nu`-free constant `stepDSharpConst d`
and the rate `3^-(m-h)`. -/
theorem stepD_exists_sharp [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    {h m l : ℕ} (hhm : h < m) (hml : m ≤ l) :
    ∃ Y : ShellSeq d → ℝ, Measurable Y ∧
      IsBigO P.toMeasure (gammaSigma 2) Y
        (stepDSharpConst d * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-((m - h : ℕ) : ℝ))) ∧
      ∀ ω : ShellSeq d,
        Homogenization.MatLoewnerLE
          (sigmaBarStarInv nu m P
            (Homogenization.cubeSet (Homogenization.originCube d (h : ℤ))))
          (sigmaBarStarInv nu l P
              (Homogenization.cubeSet (Homogenization.originCube d (h : ℤ))) +
            Y ω • (1 : Homogenization.Mat d)) :=
  stepD_exists_of_scalar_gap hnu
    (mul_nonneg
      (mul_nonneg (stepDSharpConst_pos (d := d)).le (Real.rpow_nonneg hnu.le (-(2 : ℝ))))
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (-(((m - h : ℕ) : ℝ)))))
    P hJ4 (stepD_scalarGap_sharp hnu P hJ3 hhm hml)

/-- **`hStepD`'s `Exists` conclusion at the printed amplitude verbatim.**  The
printed display carries `3^-((m-h)/2)`; since `3^-(m-h) <= 3^-((m-h)/2)` the
sharpened conclusion dominates it, so the printed amplitude is reached with the
same `nu`-free constant `stepDSharpConst d` and the same `nu^-2` power. -/
theorem stepD_exists_sharp_printed [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    {h m l : ℕ} (hhm : h < m) (hml : m ≤ l) :
    ∃ Y : ShellSeq d → ℝ, Measurable Y ∧
      IsBigO P.toMeasure (gammaSigma 2) Y
        (stepDSharpConst d * nu ^ (-(2 : ℝ)) *
          (3 : ℝ) ^ (-(((m - h : ℕ) : ℝ) / 2))) ∧
      ∀ ω : ShellSeq d,
        Homogenization.MatLoewnerLE
          (sigmaBarStarInv nu m P
            (Homogenization.cubeSet (Homogenization.originCube d (h : ℤ))))
          (sigmaBarStarInv nu l P
              (Homogenization.cubeSet (Homogenization.originCube d (h : ℤ))) +
            Y ω • (1 : Homogenization.Mat d)) := by
  obtain ⟨Y, hYmeas, hYO, hYl⟩ := stepD_exists_sharp hnu P hJ3 hJ4 hhm hml
  refine ⟨Y, hYmeas, ?_, hYl⟩
  refine hYO.mono_scale (mul_le_mul_of_nonneg_left
    (three_rpow_neg_le_half (m - h))
    (mul_nonneg (stepDSharpConst_pos (d := d)).le (Real.rpow_nonneg hnu.le _)))

end

end SuperdiffusionCLT.Section2.Annealed
