/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Cutoff.Centered
public import SuperdiffusionCLT.Section4.MinimalScales.RootClosure
public import SuperdiffusionCLT.Section2.Carriers.CenteredStreamField
public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5
public import Homogenization.Deterministic.MultiscaleQuantities
public import Homogenization.Probability.IndependentSums.WeakOrlicz
public import SuperdiffusionCLT.Frozen.Section4.LNaught

@[expose] public section

/-- Proposition `p.new.mixing.attempt` (Section 4). -/
theorem SuperdiffusionCLT.Frozen.Section4.mathcalE_bounds
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
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
                              X1 omega + X2 omega
    := by
  exact SuperdiffusionCLT.Section4.MinimalScales.mathcalE_bounds_closed d hd
