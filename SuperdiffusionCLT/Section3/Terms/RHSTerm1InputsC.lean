/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Estimates.Stream.CoefficientLinftyMoments
public import SuperdiffusionCLT.Section2.Norms.NegativeNormPairing
public import SuperdiffusionCLT.Section3.ResponseFields.RegboundsB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1Inputs

/-!
# Bridges for the carried hypotheses of `l.RHS.term1`

`RHSTerm1Inputs` reduces the two step theorems of `l.RHS.term1` to explicit
hypotheses.  This file discharges the ones that follow from the available estimates and reduces
the others to a single named input each.

## References

The paper: `l.RHS.term1` (including the annealed `L^∞` moments of `a_ℓ` and the
duality display in its proof), `l.w.basic.regbounds`, and the norm conventions of
Section 1.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Estimates.Stream
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The annealed fourth `L^∞` moment of the cutoff coefficient -/

/-- The `L^∞(cu_r)` carrier `coeffCubeLinftyENorm` of `RHSTerm1Inputs` is
dominated by `ofReal` of the measurable envelope `coeffLinftySupBound`
of the coefficient `L^∞` moment estimates: the two carriers
read the same pointwise Euclidean operator norm of `a_L = ν Id + k_L`, one
through `matrixOperatorNorm` and one through the matrix enorm. -/
theorem coeffCubeLinftyENorm_le_ofReal (nu : ℝ) (hnu : 0 ≤ nu)
    (omega : ShellSeq d) (L r : ℕ) :
    coeffCubeLinftyENorm nu L r omega ≤
      ENNReal.ofReal (coeffLinftySupBound nu L r omega) := by
  have hae : ∀ᵐ x ∂normalizedCubeMeasure (originCube d (r : ℤ)),
      ‖(fun x : Vec d =>
        matrixOperatorNorm ((coefficientCutoff nu omega L).toCoeffField x)) x‖ₑ ≤
        ENNReal.ofReal (coeffLinftySupBound nu L r omega) := by
    have hmem : ∀ᵐ x ∂normalizedCubeMeasure (originCube d (r : ℤ)),
        x ∈ cubeSet (originCube d (r : ℤ)) :=
      MeasureTheory.Measure.ae_smul_measure
        (MeasureTheory.ae_restrict_mem (measurableSet_cubeSet _)) _
    refine hmem.mono fun x hx => ?_
    have hpoint :
        matrixOperatorNorm ((coefficientCutoff nu omega L).toCoeffField x) ≤
          coeffLinftySupBound nu L r omega :=
      matrixOperatorNorm_coefficientCutoff_le_coeffLinftySupBound nu hnu omega hx
    rw [← ofReal_norm, Real.norm_eq_abs,
      abs_of_nonneg (matrixOperatorNorm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hpoint
  have hbnd := MeasureTheory.eLpNorm_le_of_ae_enorm_bound
    (μ := normalizedCubeMeasure (originCube d (r : ℤ))) (p := ∞)
    (f := fun x : Vec d =>
      matrixOperatorNorm ((coefficientCutoff nu omega L).toCoeffField x))
    (ShellField.continuous_matrixOperatorNorm.comp
      (continuous_coefficientCutoff_apply nu omega L)).aestronglyMeasurable hae
  simpa only [coeffCubeLinftyENorm, Section2.Norms.cubeLpENorm,
    normalizedCubeMeasure_apply_univ (originCube d (r : ℤ)),
    ENNReal.toReal_top, inv_zero, ENNReal.rpow_zero, smul_eq_mul,
    mul_one] using hbnd

/-- The dimensional constant of the annealed fourth `L^∞` moment of the cutoff
coefficient: the honest `Γ₂` amplitude of the envelope
`coeffLinftySupBound`, coarsened to the linear shape `K (1 + m)`. -/
def coeffCubeLinftyAmplitudeConst (d : ℕ) : ℝ :=
  1 + gammaTriangleConst 2 *
    (shellValueLargeCubeConst d + largeCubeLinftyConst d)

theorem one_le_coeffCubeLinftyAmplitudeConst
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P) :
    1 ≤ coeffCubeLinftyAmplitudeConst d := by
  have h1 : (0 : ℝ) < gammaTriangleConst 2 := IndependentSums.gammaTriangleConst_pos
  have h2 : (1 : ℝ) ≤ shellValueLargeCubeConst d :=
    one_le_shellValueLargeCubeConst d
  have h3 : (0 : ℝ) < largeCubeLinftyConst d := largeCubeLinftyConst_pos hPrefix
  have h4 : (0 : ℝ) < gammaTriangleConst 2 *
      (shellValueLargeCubeConst d + largeCubeLinftyConst d) := by
    refine mul_pos h1 ?_
    linarith only [h2, h3]
  rw [coeffCubeLinftyAmplitudeConst]
  linarith only [h4]

/-- The `Γ₂` amplitude of the `L^∞(cu_m)` envelope of `a_L` is at most
`coeffCubeLinftyAmplitudeConst d * √(1 + L) √(1 + m)`, for `ν ≤ 1`: this is the
printed shape of `e.kmn.Linfty`, `C (m − n)^{1/2}(l − n)^{1/2}`
at `n = 0`, coarsened only by `√(1 + m) ≤ √(1 + L)√(1 + m)`. -/
theorem coeffLinftyGammaTwoAmplitude_le
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    {nu : ℝ} (hnu1 : nu ≤ 1) (L m : ℕ) :
    coeffLinftyGammaTwoAmplitude nu (largeCubeLinftyConst d) d L m ≤
      coeffCubeLinftyAmplitudeConst d *
        (Real.sqrt (1 + (L : ℝ)) * Real.sqrt (1 + (m : ℝ))) := by
  have hgamma : (0 : ℝ) < gammaTriangleConst 2 := IndependentSums.gammaTriangleConst_pos
  have hc1 : (1 : ℝ) ≤ shellValueLargeCubeConst d :=
    one_le_shellValueLargeCubeConst d
  have hC : (0 : ℝ) < largeCubeLinftyConst d := largeCubeLinftyConst_pos hPrefix
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have hsL : (1 : ℝ) ≤ Real.sqrt (1 + (L : ℝ)) :=
    Real.one_le_sqrt.2 (by linarith only [hL0])
  have hsm : (1 : ℝ) ≤ Real.sqrt (1 + (m : ℝ)) :=
    Real.one_le_sqrt.2 (by linarith only [hm0])
  have hprodpos : (1 : ℝ) ≤ Real.sqrt (1 + (L : ℝ)) * Real.sqrt (1 + (m : ℝ)) := by
    nlinarith only [hsL, hsm]
  have hsqrt1 : Real.sqrt (1 + (m : ℝ)) ≤
      Real.sqrt (1 + (L : ℝ)) * Real.sqrt (1 + (m : ℝ)) := by
    nlinarith only [hsL, hsm]
  have hsqrt2 : Real.sqrt (L : ℝ) * Real.sqrt (m : ℝ) ≤
      Real.sqrt (1 + (L : ℝ)) * Real.sqrt (1 + (m : ℝ)) := by
    have ha : Real.sqrt (L : ℝ) ≤ Real.sqrt (1 + (L : ℝ)) :=
      Real.sqrt_le_sqrt (by linarith only [hL0])
    have hb : Real.sqrt (m : ℝ) ≤ Real.sqrt (1 + (m : ℝ)) :=
      Real.sqrt_le_sqrt (by linarith only [hm0])
    exact mul_le_mul ha hb (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hstream : streamCutoffLinftyGammaTwoAmplitude (largeCubeLinftyConst d) d L m ≤
      gammaTriangleConst 2 *
        ((shellValueLargeCubeConst d + largeCubeLinftyConst d) *
          (Real.sqrt (1 + (L : ℝ)) * Real.sqrt (1 + (m : ℝ)))) := by
    rw [streamCutoffLinftyGammaTwoAmplitude]
    refine mul_le_mul_of_nonneg_left ?_ hgamma.le
    have ha : shellValueLargeCubeConst d * Real.sqrt (1 + (m : ℝ)) ≤
        shellValueLargeCubeConst d *
          (Real.sqrt (1 + (L : ℝ)) * Real.sqrt (1 + (m : ℝ))) :=
      mul_le_mul_of_nonneg_left hsqrt1 (by linarith only [hc1])
    have hb : largeCubeLinftyConst d * (Real.sqrt (L : ℝ) * Real.sqrt (m : ℝ)) ≤
        largeCubeLinftyConst d *
          (Real.sqrt (1 + (L : ℝ)) * Real.sqrt (1 + (m : ℝ))) :=
      mul_le_mul_of_nonneg_left hsqrt2 hC.le
    linarith only [ha, hb]
  rw [coeffLinftyGammaTwoAmplitude, coeffCubeLinftyAmplitudeConst]
  nlinarith only [hstream, hnu1, hprodpos, hgamma, hc1, hC]

/-- The explicit constant of the annealed fourth `L^∞` moment: the square of the
linear amplitude constant times the printed moment factor `√(1 + γ(3))` of
`l.moments.gamma.psi` at `k = 4`. -/
def coeffCubeLinftyMomentConst (d : ℕ) : ℝ :=
  coeffCubeLinftyAmplitudeConst d ^ (2 : ℕ) * Real.sqrt (1 + Real.Gamma 3)

theorem one_le_coeffCubeLinftyMomentConst
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P) :
    1 ≤ coeffCubeLinftyMomentConst d := by
  have hK : (1 : ℝ) ≤ coeffCubeLinftyAmplitudeConst d :=
    one_le_coeffCubeLinftyAmplitudeConst hPrefix
  have hKsq : (1 : ℝ) ≤ coeffCubeLinftyAmplitudeConst d ^ (2 : ℕ) :=
    one_le_pow₀ hK
  have hG : (0 : ℝ) < Real.Gamma 3 := Real.Gamma_pos_of_pos (by norm_num)
  have hsq : (1 : ℝ) ≤ Real.sqrt (1 + Real.Gamma 3) :=
    Real.one_le_sqrt.2 (by linarith only [hG])
  rw [coeffCubeLinftyMomentConst]
  nlinarith only [hKsq, hsq]

/-- **The annealed fourth `L^∞` moment of the cutoff coefficient**:

`E[‖a_L‖⁴_{L^∞(cu_m)}]^{1/2} ≤ C(d) (1 + L)(1 + m)`, for `0 ≤ ν ≤ 1` and
`L ≤ m`,

in the carrier `coeffCubeLinftyENorm` of `RHSTerm1Inputs`.  The proof is
the `Γ₂` tail of the measurable envelope `coeffLinftySupBound` through the moment
bound of `l.moments.gamma.psi` at `k = 4`.

The size `(1 + L)(1 + m)` is the honest one and is the printed one: the
`e.kmn.Linfty` amplitude of `‖k_L − k_0‖_{L^∞(cu_m)}` is `C √L √m`, so
`E[‖a_L‖⁴]^{1/2}` is of order `L m`.  In particular at `L = m = ℓ` it is of
order `ℓ²`, not of order `ℓ^{3/2}`. -/
theorem sqrt_fourth_moment_coeffCubeLinftyENorm_le
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    {nu : ℝ} (hnu : 0 ≤ nu) (hnu1 : nu ≤ 1) {L m : ℕ} (hLm : L ≤ m) :
    (∫⁻ omega : ShellSeq d,
        (coeffCubeLinftyENorm nu L m omega) ^ (4 : ℕ) ∂P.toMeasure : ℝ≥0∞) ^
        ((1 : ℝ) / 2) ≤
      ENNReal.ofReal (coeffCubeLinftyMomentConst d *
        ((1 + (L : ℝ)) * (1 + (m : ℝ)))) := by
  set Z : ShellSeq d → ℝ := coeffLinftySupBound nu L m with hZ
  set A : ℝ := coeffLinftyGammaTwoAmplitude nu (largeCubeLinftyConst d) d L m with hAdef
  have hgamma : (0 : ℝ) < gammaTriangleConst 2 := IndependentSums.gammaTriangleConst_pos
  have hc1 : (1 : ℝ) ≤ shellValueLargeCubeConst d :=
    one_le_shellValueLargeCubeConst d
  have hC : (0 : ℝ) < largeCubeLinftyConst d := largeCubeLinftyConst_pos hPrefix
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hApos : 0 < A := by
    have hsq1 : (0 : ℝ) < Real.sqrt (1 + (m : ℝ)) :=
      Real.sqrt_pos.2 (by linarith only [hm0])
    have hsq2 : (0 : ℝ) ≤ Real.sqrt (L : ℝ) * Real.sqrt (m : ℝ) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    rw [hAdef, coeffLinftyGammaTwoAmplitude, streamCutoffLinftyGammaTwoAmplitude]
    have hinner : (0 : ℝ) < shellValueLargeCubeConst d * Real.sqrt (1 + (m : ℝ)) +
        largeCubeLinftyConst d * (Real.sqrt (L : ℝ) * Real.sqrt (m : ℝ)) := by
      have h1 : (0 : ℝ) < shellValueLargeCubeConst d * Real.sqrt (1 + (m : ℝ)) :=
        mul_pos (by linarith only [hc1]) hsq1
      have h2 : (0 : ℝ) ≤ largeCubeLinftyConst d *
          (Real.sqrt (L : ℝ) * Real.sqrt (m : ℝ)) := mul_nonneg hC.le hsq2
      linarith only [h1, h2]
    have := mul_pos hgamma hinner
    linarith only [this, hnu]
  have hZmeas : Measurable Z := measurable_coeffLinftySupBound nu L m
  have hbigO : IsBigO P.toMeasure (gammaSigma 2) Z A :=
    isBigO_gammaSigma_coeffLinftySupBound hPrefix hJ2 hJ3 hJ4 hnu hLm
  have hint : MeasureTheory.Integrable
      (fun omega : ShellSeq d => |Z omega| ^ (((4 : ℕ) : ℝ))) P.toMeasure :=
    SuperdiffusionCLT.Probability.integrable_abs_rpow_of_isBigO_gammaSigma_two
      hApos hZmeas.aemeasurable hbigO 4
  have hmom := SuperdiffusionCLT.Probability.abs_moment_le_of_isBigO_gammaSigma_two
    hApos hZmeas.aemeasurable hbigO 4
  have hptr : ∀ omega : ShellSeq d,
      (coeffCubeLinftyENorm nu L m omega) ^ (4 : ℕ) ≤
        ENNReal.ofReal (|Z omega| ^ (((4 : ℕ) : ℝ))) := by
    intro omega
    have habs : ENNReal.ofReal (Z omega) ≤ ENNReal.ofReal |Z omega| :=
      ENNReal.ofReal_le_ofReal (le_abs_self _)
    calc (coeffCubeLinftyENorm nu L m omega) ^ (4 : ℕ)
        ≤ (ENNReal.ofReal |Z omega|) ^ (4 : ℕ) :=
          pow_le_pow_left'
            (le_trans (coeffCubeLinftyENorm_le_ofReal nu hnu omega L m) habs) 4
      _ = ENNReal.ofReal (|Z omega| ^ (4 : ℕ)) :=
          (ENNReal.ofReal_pow (abs_nonneg _) 4).symm
      _ = ENNReal.ofReal (|Z omega| ^ (((4 : ℕ) : ℝ))) := by rw [Real.rpow_natCast]
  have hlint : (∫⁻ omega : ShellSeq d,
      (coeffCubeLinftyENorm nu L m omega) ^ (4 : ℕ) ∂P.toMeasure) ≤
      ENNReal.ofReal (A ^ (((4 : ℕ) : ℝ)) *
        (1 + Real.Gamma (((4 : ℕ) : ℝ) / 2 + 1))) := by
    calc (∫⁻ omega : ShellSeq d,
        (coeffCubeLinftyENorm nu L m omega) ^ (4 : ℕ) ∂P.toMeasure)
        ≤ ∫⁻ omega : ShellSeq d,
            ENNReal.ofReal (|Z omega| ^ (((4 : ℕ) : ℝ))) ∂P.toMeasure :=
          lintegral_mono hptr
      _ = ENNReal.ofReal (∫ omega : ShellSeq d,
            |Z omega| ^ (((4 : ℕ) : ℝ)) ∂P.toMeasure) :=
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
            (Filter.Eventually.of_forall fun omega =>
              Real.rpow_nonneg (abs_nonneg _) _)).symm
      _ ≤ ENNReal.ofReal (A ^ (((4 : ℕ) : ℝ)) *
            (1 + Real.Gamma (((4 : ℕ) : ℝ) / 2 + 1))) := ENNReal.ofReal_le_ofReal hmom
  have hGpos : (0 : ℝ) < Real.Gamma 3 := Real.Gamma_pos_of_pos (by norm_num)
  have hnn : (0 : ℝ) ≤ A ^ (((4 : ℕ) : ℝ)) *
      (1 + Real.Gamma (((4 : ℕ) : ℝ) / 2 + 1)) := by
    have h1 : (0 : ℝ) ≤ A ^ (((4 : ℕ) : ℝ)) := Real.rpow_nonneg hApos.le _
    have h2 : Real.Gamma (((4 : ℕ) : ℝ) / 2 + 1) = Real.Gamma 3 := by norm_num
    rw [h2]
    exact mul_nonneg h1 (by linarith only [hGpos])
  have hsqrt : Real.sqrt (A ^ (((4 : ℕ) : ℝ)) *
      (1 + Real.Gamma (((4 : ℕ) : ℝ) / 2 + 1))) =
      A ^ (2 : ℕ) * Real.sqrt (1 + Real.Gamma 3) := by
    have h2 : Real.Gamma (((4 : ℕ) : ℝ) / 2 + 1) = Real.Gamma 3 := by norm_num
    have h4 : A ^ (((4 : ℕ) : ℝ)) = (A ^ (2 : ℕ)) ^ (2 : ℕ) := by
      rw [Real.rpow_natCast]
      ring
    rw [h2, h4, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hAle : A ≤ coeffCubeLinftyAmplitudeConst d *
      (Real.sqrt (1 + (L : ℝ)) * Real.sqrt (1 + (m : ℝ))) :=
    coeffLinftyGammaTwoAmplitude_le hPrefix hnu1 L m
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have hfinal : A ^ (2 : ℕ) * Real.sqrt (1 + Real.Gamma 3) ≤
      coeffCubeLinftyMomentConst d * ((1 + (L : ℝ)) * (1 + (m : ℝ))) := by
    have hsq : A ^ (2 : ℕ) ≤ (coeffCubeLinftyAmplitudeConst d *
        (Real.sqrt (1 + (L : ℝ)) * Real.sqrt (1 + (m : ℝ)))) ^ (2 : ℕ) :=
      pow_le_pow_left₀ hApos.le hAle 2
    have hsr : (0 : ℝ) ≤ Real.sqrt (1 + Real.Gamma 3) := Real.sqrt_nonneg _
    have hsqL : Real.sqrt (1 + (L : ℝ)) ^ (2 : ℕ) = 1 + (L : ℝ) :=
      Real.sq_sqrt (by linarith only [hL0])
    have hsqm : Real.sqrt (1 + (m : ℝ)) ^ (2 : ℕ) = 1 + (m : ℝ) :=
      Real.sq_sqrt (by linarith only [hm0])
    have hexp : (coeffCubeLinftyAmplitudeConst d *
          (Real.sqrt (1 + (L : ℝ)) * Real.sqrt (1 + (m : ℝ)))) ^ (2 : ℕ) *
        Real.sqrt (1 + Real.Gamma 3) =
        coeffCubeLinftyMomentConst d * ((1 + (L : ℝ)) * (1 + (m : ℝ))) := by
      rw [coeffCubeLinftyMomentConst, mul_pow, mul_pow, hsqL, hsqm]
      ring
    calc A ^ (2 : ℕ) * Real.sqrt (1 + Real.Gamma 3)
        ≤ (coeffCubeLinftyAmplitudeConst d *
            (Real.sqrt (1 + (L : ℝ)) * Real.sqrt (1 + (m : ℝ)))) ^ (2 : ℕ) *
            Real.sqrt (1 + Real.Gamma 3) := mul_le_mul_of_nonneg_right hsq hsr
      _ = coeffCubeLinftyMomentConst d * ((1 + (L : ℝ)) * (1 + (m : ℝ))) := hexp
  calc (∫⁻ omega : ShellSeq d,
      (coeffCubeLinftyENorm nu L m omega) ^ (4 : ℕ) ∂P.toMeasure) ^ ((1 : ℝ) / 2)
      ≤ (ENNReal.ofReal (A ^ (((4 : ℕ) : ℝ)) *
          (1 + Real.Gamma (((4 : ℕ) : ℝ) / 2 + 1)))) ^ ((1 : ℝ) / 2) :=
        ENNReal.rpow_le_rpow hlint (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt (A ^ (((4 : ℕ) : ℝ)) *
          (1 + Real.Gamma (((4 : ℕ) : ℝ) / 2 + 1)))) := by
        rw [Real.sqrt_eq_rpow,
          ENNReal.ofReal_rpow_of_nonneg hnn (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2)]
    _ = ENNReal.ofReal (A ^ (2 : ℕ) * Real.sqrt (1 + Real.Gamma 3)) := by rw [hsqrt]
    _ ≤ ENNReal.ofReal (coeffCubeLinftyMomentConst d *
          ((1 + (L : ℝ)) * (1 + (m : ℝ)))) := ENNReal.ofReal_le_ofReal hfinal

/-! ## `hMoment`: the fourth-moment bridge in the shape Step 1 consumes -/

/-! ## `hRegL8` and `hRegH1` from `l.w.basic.regbounds` -/

/-! ## `hDuality`: the order-one pairing of Step 2 -/

end

end SuperdiffusionCLT.Section3.Terms
