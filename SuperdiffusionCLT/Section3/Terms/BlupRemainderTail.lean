/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Estimates.Stream.TranslatedIncrementLinfty
public import SuperdiffusionCLT.Section2.Estimates.Stream.DerivativeConcentration
public import SuperdiffusionCLT.Section3.ResponseFields.RegboundsInputs
public import SuperdiffusionCLT.Probability.OrliczPower
public import SuperdiffusionCLT.Probability.OrliczIndexWeakening

@[expose] public section

open MeasureTheory
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section2.Estimates.Stream
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open scoped ENNReal
open scoped BigOperators Matrix.Norms.Elementwise

/-!
# The D-estimate on translated cubes (`e.blupbounds.remainder`, item 4)

In the proof of `l.blupbounds`:
the localization display, applied with `a = a_m` and the centered perturbation
`h - h_U`, produces the two-sided envelope

`-D bfA_m(U) <= bfA(U; a_ℓ - h_U) - bfA_m(U) <= D bfA_m(U)`

with the printed scalar

`D = ν^{-1} ‖h - h_U‖_{L^∞(U)} + ν^{-2} ‖h - h_U‖²_{L^∞(U)}  ≤  O_{Γ₁}(C ν^{-2} 3^{n-m})`.

This module proves the probabilistic half of that estimate on the translated
cube `z + cu_n`, at the genuine carriers:

* `translatedIncrementOscBound` is the surrogate of
  `‖h - h_U‖_{L^∞(z + cu_n)}`: the operator-norm oscillation of the finite
  shell increment `k_L - k_m` about its value at the cube centre `z`, bounded
  deterministically by `C(d) 3^n` times the translated upper-shell gauge
  `∑_{k ∈ (m, L]} ‖∇ j_k‖_{L^∞(cu_n)}` after translation — the exact
  translated form of the mean-value argument of
  `matrixOperatorNorm_finiteShellIncrement_sub_center_le`
  (in `RegboundsInputs.lean`) run through the
  coordinatewise translation bridge `finiteShellIncrement_translateSequence`.
* `dEstimate_gammaSigma_one_translatedCube` packages the printed scalar
  `D = ν^{-1} M + ν^{-2} M²` into the `∃ Z` witness shape used by the
  response estimates, with the printed `Γ₁` amplitude
  `C(d) ν^{-2} 3^{-(m-n)}`.

The tail chain is: the per-shell translated `Γ₂` amplitudes
(`isBigOWith_gammaSigma_shellCubeDerivNorm_translate`,
in `TranslatedIncrementLinfty.lean`) are summed over the
shell interval `(m, L]` by the generalized `Γ₂` triangle inequality and the
geometric decay `∑_{k > m} 3^{-k} ≤ 3^{-m}`; the resulting `Γ₂` amplitude of
the gauge is weakened to `Γ₁` (`isBigO_gammaSigma_of_exponent_le`,
in `OrliczIndexWeakening.lean`) and squared through the printed power
rule `e.powerofGammasigma` (`isBigO_gammaSigma_rpow_fwd`,
in `OrliczPower.lean`) at `σ = 2`, `p = 2`, which preserves the index
`Γ₁`; the two Young amounts are summed by the `Γ₁` triangle inequality, and
the geometric decay `3^{-(m-n)} ≤ 1` (for `n < m`) together with
`ν^{-1} ≤ ν^{-2}` (for `ν ≤ 1`) folds both amplitudes into the printed
`ν^{-2} 3^{n-m}`.
-/

namespace SuperdiffusionCLT.Section3.Terms

open scoped MatrixOrder

variable {d : ℕ}

noncomputable section

/-! ## The oscillation of the finite shell increment on a translated cube -/

/-- The translated-cube carrier of the printed `L^∞(z + cu_n)` norm
`‖h - h_U‖_{L^∞(U)}` of the increment oscillation: `C(d) 3^n` times the
translated upper-shell gauge over the shells `(m, L]`, read on the common
smaller cube `cu_n`, where the cube is `cu_n` with `n < m`. -/
def translatedIncrementOscBound (z : Vec d) (n m L : ℕ) (omega : ShellSeq d) : ℝ :=
  upperShellFluxConst d * (3 : ℝ) ^ n *
    upperShellDerivGauge n m L (ShellField.translateSequence z omega)

theorem translatedIncrementOscBound_nonneg (z : Vec d) (n m L : ℕ)
    (omega : ShellSeq d) : 0 ≤ translatedIncrementOscBound z n m L omega :=
  mul_nonneg (mul_nonneg (upperShellFluxConst_nonneg d) (by positivity))
    (upperShellDerivGauge_nonneg n m L (ShellField.translateSequence z omega))

theorem measurable_translatedIncrementOscBound (z : Vec d) (n m L : ℕ) :
    Measurable (translatedIncrementOscBound z n m L : ShellSeq d → ℝ) := by
  unfold translatedIncrementOscBound
  exact Measurable.const_mul
    ((measurable_upperShellDerivGauge n m L).comp
      (ShellField.measurable_translateSequence z))
    (upperShellFluxConst d * (3 : ℝ) ^ n)

/-! ## The `Γ₂` tail of the translated upper-shell gauge -/

/-- The per-shell translated `Γ₂` amplitudes summed over the shell interval
`(m, L]` by the generalized `Γ₂` triangle inequality and the geometric decay
`∑_{k > m} 3^{-k} ≤ 3^{-m}`: the translated upper-shell gauge over `(m, L]`,
read on the common smaller cube `cu_n`, is `O_{Γ₂}(C 3^{-m})` at the genuine
translated carrier.  This is the interval-decoupled translated form of
`isBigOWith_gammaSigma_upperShellDerivGauge`
(`Section3/ResponseFields/RegboundsInputs.lean`). -/
theorem isBigO_gammaSigma_two_upperShellDerivGauge_translate
    {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P)
    {n m L : ℕ} (hnm : n < m) (hml : m < L) (z : Vec d) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d =>
        upperShellDerivGauge n m L (ShellField.translateSequence z omega))
      (gammaTriangleConst 2 * ((3 : ℝ) ^ m)⁻¹) := by
  have hs : (Finset.Ioc m L).Nonempty := Finset.nonempty_Ioc.mpr hml
  have hbigO : ∀ k ∈ Finset.Ioc m L,
      IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
        (fun omega : ShellSeq d =>
          ShellField.shellCubeDerivNorm n (ShellField.translate z (omega k)))
        (((3 : ℝ) ^ k)⁻¹) := by
    intro k hk
    have hnk : n ≤ k := le_trans hnm.le (Finset.mem_Ioc.mp hk).1.le
    have hsmall := isBigOWith_gammaSigma_shellCubeDerivNorm_translate hPrefix hJ3 hnk z
    exact (isBigOWith_iff_isBigO_of_nonneg
      (mu := P.toMeasure) (Psi := IndependentSums.gammaSigma 2)
      (X := fun omega : ShellSeq d =>
        ShellField.shellCubeDerivNorm n (ShellField.translate z (omega k)))
      (A := ((3 : ℝ) ^ k)⁻¹)
      (fun omega => ShellField.shellCubeDerivNorm_nonneg n
        (ShellField.translate z (omega k)))).1 hsmall
  have hfinite := IndependentSums.isBigO_finset_sum_of_isBigO_gammaSigma
    (μ := P.toMeasure) (Finset.Ioc m L)
    (X := fun (k : ℕ) (omega : ShellSeq d) =>
      ShellField.shellCubeDerivNorm n (ShellField.translate z (omega k)))
    (a := fun k : ℕ => ((3 : ℝ) ^ k)⁻¹) (σ := 2)
    (by norm_num) hs (fun k _ => by positivity) hbigO
    (fun k _ =>
      ((ShellField.shellCubeDerivNorm_measurable n).comp
        (ShellField.measurable_translate z)).comp
          (ShellField.measurable_shellCoordinate k))
  have hwith :
      IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 2)
        (fun omega : ShellSeq d =>
          upperShellDerivGauge n m L (ShellField.translateSequence z omega))
        (gammaTriangleConst 2 * ∑ k ∈ Finset.Ioc m L, ((3 : ℝ) ^ k)⁻¹) := by
    refine
      (isBigOWith_iff_isBigO_of_nonneg
        (mu := P.toMeasure) (Psi := IndependentSums.gammaSigma 2)
        (X := fun omega : ShellSeq d =>
          upperShellDerivGauge n m L (ShellField.translateSequence z omega))
        (A := gammaTriangleConst 2 * ∑ k ∈ Finset.Ioc m L, ((3 : ℝ) ^ k)⁻¹)
        (fun omega => upperShellDerivGauge_nonneg n m L
          (ShellField.translateSequence z omega))).2 ?_
    simpa only [upperShellDerivGauge, ShellField.translateSequence_apply] using hfinite
  refine (isBigOWith_iff_isBigO_of_nonneg
    (mu := P.toMeasure) (Psi := IndependentSums.gammaSigma 2)
    (X := fun omega : ShellSeq d =>
      upperShellDerivGauge n m L (ShellField.translateSequence z omega))
    (A := gammaTriangleConst 2 * ((3 : ℝ) ^ m)⁻¹)
    (fun omega => upperShellDerivGauge_nonneg n m L
      (ShellField.translateSequence z omega))).1
    (hwith.mono_scale
      (mul_le_mul_of_nonneg_left ?_ IndependentSums.gammaTriangleConst_pos.le))
  exact sum_Ioc_inv_pow_three_le hml.le

/-! ## The `Γ₁` tail of the translated increment oscillation -/

/-- The `d`-only tail constant of the translated increment oscillation per unit
`3^n 3^{-m}`: the deterministic `C(d)` of the oscillation bound times the `Γ₂`
triangle constant of the per-shell gauge sum. -/
def oscTailConst (d : ℕ) : ℝ := upperShellFluxConst d * gammaTriangleConst 2

/-- **The `Γ₁` tail of the translated increment oscillation** (the `Γ₂` tail of
the gauge, weakened to `Γ₁` with the same amplitude through
`isBigO_gammaSigma_of_exponent_le`): at the genuine carriers the oscillation
envelope is `O_{Γ₁}(C(d) 3^n 3^{-m})`, i.e. `O_{Γ₁}(C(d) 3^{-(m-n)})`. -/
theorem isBigO_gammaSigma_one_translatedIncrementOscBound
    {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P)
    {n m L : ℕ} (hnm : n < m) (hml : m < L) (z : Vec d) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 1)
      (translatedIncrementOscBound z n m L)
      (oscTailConst d * (3 : ℝ) ^ n * ((3 : ℝ) ^ m)⁻¹) := by
  have h2 := isBigO_gammaSigma_two_upperShellDerivGauge_translate hPrefix hJ3 hnm hml z
  have h2c := h2.const_mul
    (mul_nonneg (upperShellFluxConst_nonneg d)
      (by positivity : 0 ≤ (3 : ℝ) ^ n))
  exact isBigO_gammaSigma_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
    (h2c.mono_scale (le_of_eq (by unfold oscTailConst; ring)))

/-- **The square of the translated increment oscillation** through the printed
power rule `e.powerofGammasigma` (`isBigO_gammaSigma_rpow_fwd`) at `σ = 2`,
`p = 2`: squaring the `Γ₂`-tailed oscillation envelope preserves the `Γ₁`
index, with the amplitude squared. -/
theorem isBigO_gammaSigma_one_translatedIncrementOscBound_sq
    {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P)
    {n m L : ℕ} (hnm : n < m) (hml : m < L) (z : Vec d) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 1)
      (fun omega : ShellSeq d => translatedIncrementOscBound z n m L omega ^ 2)
      ((oscTailConst d * (3 : ℝ) ^ n * ((3 : ℝ) ^ m)⁻¹) ^ 2) := by
  have h2 := isBigO_gammaSigma_two_upperShellDerivGauge_translate hPrefix hJ3 hnm hml z
  have h2c : IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d =>
        upperShellFluxConst d * (3 : ℝ) ^ n *
          upperShellDerivGauge n m L (ShellField.translateSequence z omega))
      ((upperShellFluxConst d * (3 : ℝ) ^ n) *
        (gammaTriangleConst 2 * ((3 : ℝ) ^ m)⁻¹)) :=
    h2.const_mul (mul_nonneg (upperShellFluxConst_nonneg d)
      (by positivity : 0 ≤ (3 : ℝ) ^ n))
  have hKnonneg : 0 ≤ (upperShellFluxConst d * (3 : ℝ) ^ n) *
      (gammaTriangleConst 2 * ((3 : ℝ) ^ m)⁻¹) :=
    mul_nonneg (mul_nonneg (upperShellFluxConst_nonneg d)
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) n))
      (mul_nonneg IndependentSums.gammaTriangleConst_pos.le
        (inv_nonneg.mpr (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) m)))
  have hsq := isBigO_gammaSigma_rpow_fwd (σ := 2) (p := 2)
    (show (0 : ℝ) < 2 by norm_num) hKnonneg
    (fun omega => translatedIncrementOscBound_nonneg z n m L omega) h2c
  have hidx : ((2 : ℝ) / 2) = 1 := by norm_num
  rw [hidx] at hsq
  -- the real-exponent square is the integer-exponent square
  have hfun : (fun omega : ShellSeq d =>
      translatedIncrementOscBound z n m L omega ^ (2 : ℝ)) =
      fun omega : ShellSeq d => translatedIncrementOscBound z n m L omega ^ 2 := by
    funext omega
    exact Real.rpow_two _
  have hamp : ((upperShellFluxConst d * (3 : ℝ) ^ n) *
      (gammaTriangleConst 2 * ((3 : ℝ) ^ m)⁻¹)) ^ (2 : ℝ) =
      ((upperShellFluxConst d * (3 : ℝ) ^ n) *
        (gammaTriangleConst 2 * ((3 : ℝ) ^ m)⁻¹)) ^ 2 :=
    Real.rpow_two _
  rw [hfun, hamp] at hsq
  refine hsq.mono_scale ?_
  exact le_of_eq (by unfold oscTailConst; ring)

/-! ## The printed D-estimate envelope -/

/-- The `d`-only constant of the printed D-estimate envelope: the `Γ₁`
triangle constant times the sum of the two Young amounts' tail constants. -/
def dEstimateConst (d : ℕ) : ℝ :=
  gammaTriangleConst 1 * (oscTailConst d + oscTailConst d ^ 2)

/-- The printed scalar `D = ν^{-1} M + ν^{-2} M²` of the localization display of
`e.blupbounds`'s proof, at the translated-cube carrier
`M = translatedIncrementOscBound z n m L`. -/
def translatedIncrementD (nu : ℝ) (z : Vec d) (n m L : ℕ) (omega : ShellSeq d) : ℝ :=
  nu⁻¹ * translatedIncrementOscBound z n m L omega +
    nu ^ (-(2 : ℝ)) * translatedIncrementOscBound z n m L omega ^ 2

theorem measurable_translatedIncrementD (nu : ℝ) (z : Vec d) (n m L : ℕ) :
    Measurable (translatedIncrementD nu z n m L : ShellSeq d → ℝ) := by
  have hM := measurable_translatedIncrementOscBound z n m L
  unfold translatedIncrementD
  exact (Measurable.const_mul hM nu⁻¹).add
    (Measurable.const_mul (hM.pow_const 2) (nu ^ (-(2 : ℝ))))

/-- **The D-estimate on translated cubes** (`e.Tsizebounds`-`e.mclDsizebounds`,
the probabilistic envelope of the localization display consumed by
`e.blupbounds.remainder`):
with `M = translatedIncrementOscBound z n m L` the genuine translated-cube
carrier of `‖h - h_U‖_{L^∞(z + cu_n)}`, the printed scalar
`D = ν^{-1} M + ν^{-2} M²` has the printed `Γ₁` tail

`D = O_{Γ₁}(C(d) ν^{-2} 3^{-(m-n)})`

at the genuine carriers, in the `∃ Z` witness shape used by the response
estimates.  The two Young amounts are the `ν^{-1} M` of the localization's
linear term and the `ν^{-2} M²` of its quadratic term. -/
theorem dEstimate_gammaSigma_one_translatedCube
    {P : ProbabilityMeasure (ShellSeq d)} {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P)
    (n m L : ℕ) (hnm : n < m) (hml : m < L) (z : Vec d) :
    ∃ Z : ShellSeq d → ℝ, Measurable Z ∧
      IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 1) Z
        (dEstimateConst d * nu ^ (-(2 : ℝ)) *
          (3 : ℝ) ^ (-(((m - n : ℕ) : ℝ)))) ∧
      ∀ omega : ShellSeq d, translatedIncrementD nu z n m L omega ≤ Z omega := by
  -- the dimension is positive, which makes the tail constant positive
  have hd : (0 : ℝ) < (d : ℝ) :=
    Nat.cast_pos.mpr (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hPrefix.dimension)
  have hoscpos : 0 < oscTailConst d := by
    unfold oscTailConst
    refine mul_pos ?_ IndependentSums.gammaTriangleConst_pos
    unfold upperShellFluxConst
    exact div_pos (mul_pos (pow_pos hd 2) (Real.sqrt_pos.mpr hd))
      (by norm_num : (0 : ℝ) < 2)
  have hKpos : 0 < oscTailConst d * (3 : ℝ) ^ n * ((3 : ℝ) ^ m)⁻¹ :=
    mul_pos (mul_pos hoscpos (pow_pos (by norm_num : (0 : ℝ) < 3) n))
      (inv_pos.mpr (pow_pos (by norm_num : (0 : ℝ) < 3) m))
  -- the two exponents and their arithmetic
  have hq1nn : 0 ≤ nu⁻¹ := inv_nonneg.mpr hnu.le
  have hq1pos : 0 < nu⁻¹ := inv_pos.mpr hnu
  have hq2 : nu ^ (-(2 : ℝ)) = nu⁻¹ * nu⁻¹ := by
    rw [Real.rpow_neg (by positivity), Real.rpow_two, pow_two, mul_inv]
  have hq2nn : 0 ≤ nu ^ (-(2 : ℝ)) := by rw [hq2]; positivity
  have hq2pos : 0 < nu ^ (-(2 : ℝ)) := by rw [hq2]; positivity
  have hq1le : nu⁻¹ ≤ nu ^ (-(2 : ℝ)) := by
    have h1 : (1 : ℝ) ≤ nu⁻¹ := by
      have h := inv_anti₀ hnu hnu1
      rwa [inv_one] at h
    calc nu⁻¹ = (1 : ℝ) * nu⁻¹ := by ring
      _ ≤ nu⁻¹ * nu⁻¹ := mul_le_mul_of_nonneg_right h1 hq1nn
      _ = nu ^ (-(2 : ℝ)) := hq2.symm
  have hcast : ((m - n : ℕ) : ℝ) = (m : ℝ) - (n : ℝ) := by
    rw [Nat.cast_sub hnm.le]
  have hc3eq : (3 : ℝ) ^ (n : ℝ) * ((3 : ℝ) ^ (m : ℝ))⁻¹
      = (3 : ℝ) ^ (-(((m - n : ℕ) : ℝ))) := by
    have h1 : (3 : ℝ) ^ (-(((m - n : ℕ) : ℝ))) = (3 : ℝ) ^ ((n : ℝ) - (m : ℝ)) := by
      rw [hcast, neg_sub]
    rw [h1, Real.rpow_sub (by norm_num : (0 : ℝ) < 3), div_eq_mul_inv]
  have hKc : oscTailConst d * (3 : ℝ) ^ n * ((3 : ℝ) ^ m)⁻¹
      = oscTailConst d * (3 : ℝ) ^ (-(((m - n : ℕ) : ℝ))) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← hc3eq, mul_assoc]
  have hc3nn : 0 ≤ (3 : ℝ) ^ (-(((m - n : ℕ) : ℝ))) := by positivity
  have hc3le : (3 : ℝ) ^ (-(((m - n : ℕ) : ℝ))) ≤ 1 := by
    rw [← hc3eq, ← div_eq_mul_inv]
    exact (div_le_one
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) (m : ℝ))).2
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
        (Nat.cast_le.mpr hnm.le))
  -- the square of the amplitude drops from `3^n 3^{-m} = 3^{-(m-n)}` and
  -- `3^{-(m-n)} ≤ 1`
  have h2sq : ((oscTailConst d * (3 : ℝ) ^ n * ((3 : ℝ) ^ m)⁻¹)) ^ 2 ≤
      oscTailConst d ^ 2 * (3 : ℝ) ^ (-(((m - n : ℕ) : ℝ))) := by
    have hsq : ((oscTailConst d * (3 : ℝ) ^ n * ((3 : ℝ) ^ m)⁻¹)) ^ 2 =
        oscTailConst d ^ 2 * ((3 : ℝ) ^ (-(((m - n : ℕ) : ℝ)))) ^ 2 := by
      rw [hKc, mul_pow]
    rw [hsq]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg (oscTailConst d))
    calc ((3 : ℝ) ^ (-(((m - n : ℕ) : ℝ)))) ^ 2
        = (3 : ℝ) ^ (-(((m - n : ℕ) : ℝ))) *
          (3 : ℝ) ^ (-(((m - n : ℕ) : ℝ))) := by ring
      _ ≤ (3 : ℝ) ^ (-(((m - n : ℕ) : ℝ))) * 1 :=
          mul_le_mul_of_nonneg_left hc3le hc3nn
      _ = (3 : ℝ) ^ (-(((m - n : ℕ) : ℝ))) := by ring
  -- the two Young amounts and their `Γ₁` triangle sum
  have hT2 := isBigO_gammaSigma_one_translatedIncrementOscBound hPrefix hJ3 hnm hml z
  have hT3 := isBigO_gammaSigma_one_translatedIncrementOscBound_sq hPrefix hJ3 hnm hml z
  have hM2 : Measurable (fun omega : ShellSeq d =>
      translatedIncrementOscBound z n m L omega ^ 2) :=
    (measurable_translatedIncrementOscBound z n m L).pow_const 2
  have hXm : Measurable (fun omega : ShellSeq d =>
      nu⁻¹ * translatedIncrementOscBound z n m L omega) :=
    Measurable.const_mul (measurable_translatedIncrementOscBound z n m L) nu⁻¹
  have hYm : Measurable (fun omega : ShellSeq d =>
      nu ^ (-(2 : ℝ)) * translatedIncrementOscBound z n m L omega ^ 2) :=
    Measurable.const_mul hM2 (nu ^ (-(2 : ℝ)))
  have hX := hT2.const_mul hq1nn
  have hY := hT3.const_mul hq2nn
  refine ⟨translatedIncrementD nu z n m L, measurable_translatedIncrementD nu z n m L, ?_,
    fun _ => le_rfl⟩
  refine (isBigO_gammaSigma_add_of_isBigO (sigma := 1) (by norm_num : (0 : ℝ) < 1)
    (mul_pos hq1pos hKpos) (mul_pos hq2pos (pow_pos hKpos 2)) hX hY hXm hYm).mono_scale ?_
  have h1 : nu⁻¹ * (oscTailConst d * (3 : ℝ) ^ n * ((3 : ℝ) ^ m)⁻¹) ≤
      nu ^ (-(2 : ℝ)) * (oscTailConst d * (3 : ℝ) ^ n * ((3 : ℝ) ^ m)⁻¹) :=
    mul_le_mul_of_nonneg_right hq1le hKpos.le
  have h2 : nu ^ (-(2 : ℝ)) *
      ((oscTailConst d * (3 : ℝ) ^ n * ((3 : ℝ) ^ m)⁻¹)) ^ 2 ≤
      nu ^ (-(2 : ℝ)) * (oscTailConst d ^ 2 *
        (3 : ℝ) ^ (-(((m - n : ℕ) : ℝ)))) :=
    mul_le_mul_of_nonneg_left h2sq hq2nn
  calc gammaTriangleConst 1 * (nu⁻¹ * (oscTailConst d * (3 : ℝ) ^ n *
          ((3 : ℝ) ^ m)⁻¹) +
        nu ^ (-(2 : ℝ)) * ((oscTailConst d * (3 : ℝ) ^ n * ((3 : ℝ) ^ m)⁻¹)) ^ 2) ≤
      gammaTriangleConst 1 * (nu ^ (-(2 : ℝ)) * (oscTailConst d * (3 : ℝ) ^ n *
          ((3 : ℝ) ^ m)⁻¹) +
        nu ^ (-(2 : ℝ)) * (oscTailConst d ^ 2 *
          (3 : ℝ) ^ (-(((m - n : ℕ) : ℝ))))) := by
        refine mul_le_mul_of_nonneg_left ?_ IndependentSums.gammaTriangleConst_pos.le
        linarith only [h1, h2]
    _ = dEstimateConst d * nu ^ (-(2 : ℝ)) *
          (3 : ℝ) ^ (-(((m - n : ℕ) : ℝ))) := by
        unfold dEstimateConst
        rw [hKc]
        ring

end

end SuperdiffusionCLT.Section3.Terms