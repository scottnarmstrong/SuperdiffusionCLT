/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Deterministic.MultiscaleQuantities
public import Homogenization.Probability.IndependentSums.WeakOrlicz
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5
public import SuperdiffusionCLT.Frozen.Section4.LNaught
public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.Section2.Carriers.CenteredStreamField
public import SuperdiffusionCLT.Section2.Cutoff.Centered
public import SuperdiffusionCLT.Section4.MinimalScales.SkeletonMathcalE
public import SuperdiffusionCLT.Section4.MinimalScales.NearShiftAssemblyD7
public import SuperdiffusionCLT.Section4.MinimalScales.DeepCrudePolyC
public import SuperdiffusionCLT.Section4.MinimalScales.LimitLocTerm
public import SuperdiffusionCLT.Section4.MinimalScales.RootArithOneScaleE
public import SuperdiffusionCLT.Section4.NewMixing.AssemblyMainParamUniform
public import SuperdiffusionCLT.Frozen.Section4.HomogenizationBelowCutoff

/-!
# Section 4 root closure

`mathcalE_bounds` (`p.new.mixing.attempt`) and `minimal_scales` (`p.minimal.scales`), stated
exactly as `SuperdiffusionCLT.Frozen.Section4.mathcalE_bounds` and
`SuperdiffusionCLT.Frozen.Section4.minimal_scales`. `mathcalE_bounds` is the skeleton
`srootE_mathcalE_bounds_of_inputs` fed with its four inputs: `hParam` (uniform in the skew
shift, from `homogenization_below_cutoff`), `hNear`, `hDeep` and `hLimit`. `minimal_scales`
follows from it by `srootMS_minimal_scales_of_hE`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

/-- `p.new.mixing.attempt`: the `mathcalE_bounds` statement. -/
theorem mathcalE_bounds_closed (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu cStar nondeg : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : MeasureTheory.ProbabilityMeasure
              (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
          (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
          (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
          (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar nondeg
              hPrefix hJ2 hJ3 →
          ∀ s : ℝ, 0 < s → s ≤ 1 →
            ∀ K : ℝ, C ≤ K →
              ∀ m n : ℕ,
                SuperdiffusionCLT.Frozen.Section4.lNaught C (C * s⁻¹ * K) (1 / 2) cStar nu nondeg ≤ (m : ℝ) →
                m - ⌈K * Real.log (m : ℝ)⌉₊ ≤ n →
                n ≤ m →
                ∀ k : Fin d → ℤ,
                                    (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
                        Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)) ⊆
                      Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)) →
                  ∃ X1 X2 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                    Measurable X1 ∧
                    Homogenization.IndependentSums.IsBigO P.toMeasure
                        (Homogenization.IndependentSums.gammaSigma 2) X1
                        (C * s⁻¹ * K ^ ((1 : ℝ) / 2) *
                          (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m
                              P)⁻¹ *
                          Real.log (m : ℝ) ^ ((1 : ℝ) / 2)) ∧
                    Measurable X2 ∧
                    Homogenization.IndependentSums.IsBigO P.toMeasure
                        (Homogenization.IndependentSums.gammaSigma (2 / 3)) X2
                        (C * (m : ℝ) ^ (-(1000 : ℝ))) ∧
                      ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d
                          ∂P.toMeasure,
                        ∀ L : ℕ, (m : ℝ) - C * s⁻¹ * ((⌈K * Real.log (m : ℝ)⌉₊ : ℕ) : ℝ) ≤ (L : ℝ) →
                          Homogenization.HomogenizationErrorOnCube
                              (Homogenization.originCube d (n : ℤ)) s
                              Homogenization.MultiscaleExponent.infinity
                              (Homogenization.MultiscaleExponent.finite (2 : ℝ))
                              (fun x =>
                                (SuperdiffusionCLT.Section2.Cutoff.centeredCoefficientCutoff
                                    nu omega L
                                    (Homogenization.cubeSet
                                      (Homogenization.originCube d (m : ℤ)))).toCoeffField
                                  ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))
                              (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu
                                  m P •
                                (1 : Homogenization.Mat d)) +
                            Homogenization.HomogenizationErrorOnCube
                              (Homogenization.originCube d (n : ℤ)) s
                              Homogenization.MultiscaleExponent.infinity
                              (Homogenization.MultiscaleExponent.finite (2 : ℝ))
                              (fun x =>
                                nu • (1 : Homogenization.Mat d) +
                                  SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                                    omega
                                    (Homogenization.cubeSet
                                      (Homogenization.originCube d (m : ℤ)))
                                    ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))
                              (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu
                                  m P •
                                (1 : Homogenization.Mat d)) ≤
                            C * s ^ (-((1 : ℝ) / 2)) * K ^ ((1 : ℝ) / 2) *
                                (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
                                    nu m P)⁻¹ *
                                Real.log (m : ℝ) +
                              X1 omega + X2 omega :=
  srootE_mathcalE_bounds_of_inputs d
    (SuperdiffusionCLT.Section4.NewMixing.newMixParam_main_uniform_of_inputs d hd
      (SuperdiffusionCLT.Frozen.Section4.homogenization_below_cutoff d hd))
    (srootNS_hNear d) (srootD4_hDeep d) (srootL4_hLimit d)

/-- `p.minimal.scales`: the `minimal_scales` statement. -/
theorem minimal_scales_closed (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu cStar nondeg : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : MeasureTheory.ProbabilityMeasure
              (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
          (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
          (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
          (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar nondeg
              hPrefix hJ2 hJ3 →
          ∀ (expon delta s M : ℝ),
            0 < expon → expon < 1 / 2 →
            0 < delta → delta ≤ 1 →
            0 < s → s ≤ 1 →
            1 ≤ M →
            ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
              Measurable X ∧
              Homogenization.IndependentSums.IsBigO P.toMeasure
                  (Homogenization.IndependentSums.gammaSigma (2 * expon))
                  (fun omega => Real.log (X omega))
                  (max
                    (SuperdiffusionCLT.Frozen.Section4.lNaught C
                      (C * expon⁻¹ * delta ^ (-(2 : ℝ)) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ))
                      (1 - expon) cStar nu nondeg)
                    (SuperdiffusionCLT.Frozen.Section4.lNaught C (C * M * s ^ (-(2 : ℝ))) (1 / 2 + expon) cStar nu
                      nondeg)) ∧
              ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
                ∀ m n : ℕ,
                  max
                      (SuperdiffusionCLT.Frozen.Section4.lNaught C
                        (C * expon⁻¹ * delta ^ (-(2 : ℝ)) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ))
                        (1 - expon) cStar nu nondeg)
                      (SuperdiffusionCLT.Frozen.Section4.lNaught C (C * M * s ^ (-(2 : ℝ))) (1 / 2 + expon) cStar nu
                        nondeg) ≤
                    (m : ℝ) →
                  X omega ≤ (3 : ℝ) ^ m →
                  m - ⌈C * M * s⁻¹ * Real.log (m : ℝ)⌉₊ ≤ n →
                  n ≤ m →
                  (∀ L : ℕ, m ≤ L →
                    ∀ k : Fin d → ℤ,
                                            (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
                            Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)) ⊆
                          Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)) →
                      Homogenization.HomogenizationErrorOnCube
                          (Homogenization.originCube d (n : ℤ)) s
                          Homogenization.MultiscaleExponent.infinity
                          (Homogenization.MultiscaleExponent.finite (2 : ℝ))
                          (fun x =>
                            (SuperdiffusionCLT.Section2.Cutoff.centeredCoefficientCutoff
                                nu omega L
                                (Homogenization.cubeSet
                                  (Homogenization.originCube d (m : ℤ)))).toCoeffField
                              ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))
                          (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P •
                            (1 : Homogenization.Mat d)) ≤
                        delta *
                          (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m
                              P)⁻¹ *
                          (m : ℝ) ^ expon * Real.log (m : ℝ)) ∧
                  (∀ k : Fin d → ℤ,
                                        (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
                          Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)) ⊆
                        Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)) →
                    Homogenization.HomogenizationErrorOnCube
                        (Homogenization.originCube d (n : ℤ)) s
                        Homogenization.MultiscaleExponent.infinity
                        (Homogenization.MultiscaleExponent.finite (2 : ℝ))
                        (fun x =>
                          nu • (1 : Homogenization.Mat d) +
                            SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                              omega
                              (Homogenization.cubeSet
                                (Homogenization.originCube d (m : ℤ)))
                              ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))
                        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P •
                          (1 : Homogenization.Mat d)) ≤
                      delta *
                        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m
                            P)⁻¹ *
                        (m : ℝ) ^ expon * Real.log (m : ℝ)) :=
  srootMS_minimal_scales_of_hE d (mathcalE_bounds_closed d hd)

end SuperdiffusionCLT.Section4.MinimalScales
