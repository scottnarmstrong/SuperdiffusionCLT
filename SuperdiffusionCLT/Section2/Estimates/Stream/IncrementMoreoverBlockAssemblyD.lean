/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementMoreoverBlockAssemblyC
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementMoreoverBlockH
public import SuperdiffusionCLT.Section3.HighContrast.RangeDependenceRestriction

/-!
# The "Moreover" block of the shell-increment estimates, at the corrected amplitude

This module assembles the whole "Moreover" block of `l.ellip.k.scales.estimates` out of the
pieces proved in `IncrementMoreoverBlockF`, `IncrementMoreoverBlockG`,
`IncrementMoreoverBlockH` and the two assembly modules, at the amplitude of
`IncrementMoreoverBlockAssemblyC`.

The random scale is the print's own construction,
`K_σ = moreoverMinimalScale (moreoverEnvelope s) δ σ`: the first triadic scale
beyond which the envelope family `X_m` never again exceeds `½ δ m^σ`, joined with
the floor `27`. Its four clauses come from four separate places.

* Measurability from `measurable_moreoverMinimalScale`, and the floor
  `27 ≤ K_σ` from `le_moreoverMinimalScale`; both are properties of the
  construction and need no hypothesis.
* The `Γ_{2σ}` tail of `log K_σ` from
  `isBigO_gammaSigma_log_moreoverMinimalScale_of_le`, fed by the uniform `Γ₂`
  amplitude `isBigO_gammaSigma_moreoverEnvelope` of the envelope family and by
  the amplitude comparison
  `moreoverLogScaleAmplitude_le_moreoverAmpConst`. The amplitude carries its free
  constant **outside** the `1/σ` power; a constant inside that power tends to `1`
  as `σ → ∞` and is then below the `3 log 3` that the floor `27 ≤ K_σ` forces, so
  the shape matters and is not cosmetic.
* The full-measure event from `ae_hasGoodTailFrom_moreoverBadEvent`; on it the
  three clauses hold at every scale above `K_σ`.
* The three-term display from `moreoverDisplay_le` together with
  `moreoverEnvelope_le_of_moreoverMinimalScale_le`, the logarithmic-window clause
  from `coarseAverage_le_of_moreoverMinimalScale_le`, whose only input about the
  family is `inv_mul_centeredScaleCubeMax_le_moreoverWindowMax`, and the
  pointwise ellipticity clause from
  `sq_matrixOperatorNorm_centeredStreamField_sub_le`, whose hypothesis is the
  first summand of the display, read off by `le_self_add`.

The `J1` law is bound in the restriction lane and transported to the integral
lane that the envelope amplitude consumes by
`Section3/HighContrast/RangeDependenceRestriction.shellLawJ1_of_shellLawJ1Restriction`.

## Main results

* `moreover_block`: the whole block.

## References

* `l.ellip.k.scales.estimates`.
-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Section2
namespace Estimates
namespace Stream

open Homogenization MeasureTheory
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Carriers
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open scoped ENNReal
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- **The "Moreover" block of `l.ellip.k.scales.estimates` at the corrected
`Γ_{2σ}` amplitude**, in the exact text of the block, with the three constants
`C₀ = moreoverAmpOuterConst`, `C₁ = moreoverAmpInnerConst d s` and
`C₂ = moreoverLogArgConst` and with the block's shared constant `C` any real at
least `4`, the value the pointwise clause needs. -/
theorem moreover_block {d : ℕ}
    {P : MeasureTheory.ProbabilityMeasure
      (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {C : ℝ} (hC : (4 : ℝ) ≤ C) :
    (∀ delta : ℝ, 0 < delta → delta < 1 →
        ∀ sigma : ℝ, 0 < sigma →
          ∃ Kfun : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
            Measurable Kfun ∧
              (∀ omega, (27 : ℝ) ≤ Kfun omega) ∧
              Homogenization.IndependentSums.IsBigO P.toMeasure
                (Homogenization.IndependentSums.gammaSigma (2 * sigma))
                (fun omega => Real.log (Kfun omega))
                (moreoverAmpOuterConst *
                  (moreoverAmpInnerConst d s * delta⁻¹ *
                      Real.sqrt (sigma⁻¹ *
                        Real.log (Real.exp 1 + moreoverLogArgConst * delta⁻¹ * sigma⁻¹))) ^
                    sigma⁻¹) ∧
              ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d
                  ∂P.toMeasure,
                (∀ i : ℕ,
                    Summable fun k : ℕ =>
                      SuperdiffusionCLT.Section2.Carriers.shellDerivLinftyNorm
                        (Homogenization.openCubeSet
                          (Homogenization.originCube d (i : ℤ)))
                        (omega k)) →
                  ((∀ m : ℕ,
                      Kfun omega ≤ (3 : ℝ) ^ m →
                  (ENNReal.ofReal ((m : ℝ)⁻¹) *
                        SuperdiffusionCLT.Section2.Norms.cubeLpENorm
                          (Homogenization.originCube d (m : ℤ)) ∞
                          (SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                            omega
                            (Homogenization.cubeSet
                              (Homogenization.originCube d (m : ℤ)))) +
                      ENNReal.ofReal ((3 : ℝ) ^ m) *
                        (∑' k : ℕ,
                          ENNReal.ofReal
                            (SuperdiffusionCLT.Section2.Carriers.shellDerivLinftyNorm
                              (Homogenization.openCubeSet
                                (Homogenization.originCube d (m : ℤ)))
                              (omega (m + 1 + k)))) +
                      ENNReal.ofReal ((3 : ℝ) ^ (-(s * (m : ℝ)))) *
                        SuperdiffusionCLT.Section2.Norms.matHatNegENorm
                          (Homogenization.originCube d (m : ℤ)) s 2
                          (SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                            omega
                            (Homogenization.cubeSet
                              (Homogenization.originCube d (m : ℤ)))) ≤
                    ENNReal.ofReal (delta * (m : ℝ) ^ sigma)) ∧
                    ∀ A B : ℝ, 1 ≤ A → 1 ≤ B →
                      ∀ n : ℕ,
                        (m : ℤ) - ⌈A * Real.log (B * (m : ℝ))⌉ ≤ (n : ℤ) →
                          n ≤ m →
                            ∀ Q : Homogenization.TriadicCube d,
                              Q.scale = (n : ℤ) →
                                Homogenization.cubeCenter Q ∈
                                    Homogenization.cubeSet
                                      (Homogenization.originCube d (m : ℤ)) →
                                  Homogenization.Book.Ch02.matrixOperatorNorm
                                      (Homogenization.volumeAverageMat
                                        (Homogenization.cubeSet Q)
                                        (SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                                          omega
                                          (Homogenization.cubeSet
                                            (Homogenization.originCube d (m : ℤ))))) ≤
                                    A * Real.log (B * (m : ℝ)) * delta *
                                      (m : ℝ) ^ sigma) ∧
                    ∀ x : Homogenization.Vec d,
                Homogenization.Book.Ch02.matrixOperatorNorm
                      (SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                          omega
                          (Homogenization.cubeSet
                            (Homogenization.originCube d (0 : ℤ))) x -
                        SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                          omega
                          (Homogenization.cubeSet
                            (Homogenization.originCube d (0 : ℤ))) 0) ^ 2 ≤
                  C *
                    Real.log (Kfun omega ^ 2 + Homogenization.vecNormSq x) ^
                      (2 * (1 + sigma)))) := by
  intro delta hdelta hdelta1 sigma hsigma
  have hJ1' : ShellLawJ1 d P :=
    SuperdiffusionCLT.Section3.HighContrast.shellLawJ1_of_shellLawJ1Restriction hJ1
  have hCl : (0 : ℝ) ≤ largeCubeLinftyConst d := (largeCubeLinftyConst_pos hPrefix).le
  have hA : (1 : ℝ) ≤ moreoverEnvelopeConst d s := one_le_moreoverEnvelopeConst hCl hs
  have hApos : (0 : ℝ) < moreoverEnvelopeConst d s := lt_of_lt_of_le one_pos hA
  have hXmeas : ∀ m : ℕ, Measurable (moreoverEnvelope (d := d) s m) :=
    fun m => measurable_moreoverEnvelope s m
  have hXbig : ∀ m : ℕ, IsBigO P.toMeasure (gammaSigma 2)
      (moreoverEnvelope (d := d) s m) (moreoverEnvelopeConst d s) :=
    fun m => isBigO_gammaSigma_moreoverEnvelope hPrefix hJ1' hJ2 hJ3 hJ4 hs m
  refine ⟨moreoverMinimalScale (moreoverEnvelope (d := d) s) delta sigma,
    measurable_moreoverMinimalScale hXmeas delta sigma,
    le_moreoverMinimalScale _ delta sigma, ?_, ?_⟩
  · exact isBigO_gammaSigma_log_moreoverMinimalScale_of_le hApos hdelta hsigma hXbig
      (moreoverLogScaleAmplitude_le_moreoverAmpConst hCl hs hdelta hdelta1 hsigma)
  · filter_upwards [ae_hasGoodTailFrom_moreoverBadEvent hApos hdelta hsigma hXbig 3]
      with omega hgood
    intro hguard
    have hmnn : ∀ m : ℕ, (0 : ℝ) ≤ delta * (m : ℝ) ^ sigma := fun m =>
      mul_nonneg hdelta.le (Real.rpow_nonneg (Nat.cast_nonneg m) sigma)
    have hwindow : ∀ m h : ℕ, 0 < h → h ≤ m →
        ((h : ℝ))⁻¹ * centeredScaleCubeMax (d := d) h m omega ≤
          moreoverEnvelope (d := d) s m omega := by
      intro m h hh _
      have hw := inv_mul_centeredScaleCubeMax_le_moreoverWindowMax (h := h) (m := m)
        hh omega
      have hd0 := moreoverDisplayBound_nonneg (d := d) hs m omega
      rw [moreoverEnvelope]
      linarith only [hw, hd0]
    have hdisp : ∀ m : ℕ,
        moreoverMinimalScale (moreoverEnvelope (d := d) s) delta sigma omega ≤
            (3 : ℝ) ^ m →
          ENNReal.ofReal ((m : ℝ)⁻¹) *
                cubeLpENorm (originCube d (m : ℤ)) ∞
                  (centeredStreamField omega (cubeSet (originCube d (m : ℤ)))) +
              ENNReal.ofReal ((3 : ℝ) ^ m) *
                (∑' k : ℕ, ENNReal.ofReal
                  (shellDerivLinftyNorm (openCubeSet (originCube d (m : ℤ)))
                    (omega (m + 1 + k)))) +
            ENNReal.ofReal ((3 : ℝ) ^ (-(s * (m : ℝ)))) *
              matHatNegENorm (originCube d (m : ℤ)) s 2
                (centeredStreamField omega (cubeSet (originCube d (m : ℤ)))) ≤
          ENNReal.ofReal (delta * (m : ℝ) ^ sigma) := by
      intro m hm
      have hm3 : 3 ≤ m := three_le_of_moreoverMinimalScale_le hm
      have hsmall := moreoverEnvelope_le_of_moreoverMinimalScale_le hgood hm
      have hbound : moreoverDisplayBound (d := d) s m omega ≤ delta * (m : ℝ) ^ sigma := by
        have hw := moreoverWindowMax_nonneg (d := d) m omega
        rw [moreoverEnvelope] at hsmall
        linarith only [hsmall, hw, hmnn m]
      exact le_trans (moreoverDisplay_le omega (by omega) hs hs1 hguard)
        (ENNReal.ofReal_le_ofReal hbound)
    have hfirst : ∀ m : ℕ,
        moreoverMinimalScale (moreoverEnvelope (d := d) s) delta sigma omega ≤
            (3 : ℝ) ^ m →
          ENNReal.ofReal ((m : ℝ)⁻¹) *
              cubeLpENorm (originCube d (m : ℤ)) ∞
                (centeredStreamField omega (cubeSet (originCube d (m : ℤ)))) ≤
            ENNReal.ofReal (delta * (m : ℝ) ^ sigma) :=
      fun m hm => le_trans (le_trans le_self_add le_self_add) (hdisp m hm)
    constructor
    · intro m hm
      refine ⟨hdisp m hm, ?_⟩
      intro A B hA1 hB1 n hn1 hn2 Q hQscale hQmem
      exact coarseAverage_le_of_moreoverMinimalScale_le hdelta hgood hwindow (hguard m)
        hm hA1 hB1 hn1 hn2 hQscale hQmem
    · intro x
      have hK := le_moreoverMinimalScale (moreoverEnvelope (d := d) s) delta sigma omega
      have hpt := sq_matrixOperatorNorm_centeredStreamField_sub_le hdelta hdelta1.le
        hsigma hK hguard hfirst x
      refine le_trans hpt ?_
      have hbase : (729 : ℝ) ≤
          moreoverMinimalScale (moreoverEnvelope (d := d) s) delta sigma omega ^ 2 +
            vecNormSq x := by
        have h2 := vecNormSq_nonneg x
        nlinarith only [hK, h2]
      have hlog : (0 : ℝ) ≤ Real.log
          (moreoverMinimalScale (moreoverEnvelope (d := d) s) delta sigma omega ^ 2 +
            vecNormSq x) := Real.log_nonneg (by linarith only [hbase])
      exact mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hlog _)

end

end Stream
end Estimates
end Section2
end SuperdiffusionCLT
