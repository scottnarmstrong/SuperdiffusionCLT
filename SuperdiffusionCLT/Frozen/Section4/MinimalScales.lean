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

/-- Proposition `p.minimal.scales` (Section 4).

The scale `L_0` (`e.Lnaught.def`) is `lNaught (C M alpha cStar nu K : ℝ) : ℝ`, taking the
universal constant `C` first. -/
theorem SuperdiffusionCLT.Frozen.Section4.minimal_scales
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
                        (m : ℝ) ^ expon * Real.log (m : ℝ))
    := by
  exact SuperdiffusionCLT.Section4.MinimalScales.minimal_scales_closed d hd
