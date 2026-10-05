/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Prereq.EuclidBall
public import SuperdiffusionCLT.Section6.Root.Glue
public import SuperdiffusionCLT.Frozen.Section6.C1BetaSharp
public import SuperdiffusionCLT.Section6.Prereq.FullField
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5
public import Homogenization.Probability.IndependentSums.WeakOrlicz
public import Homogenization.PDE.Harmonic
public import SuperdiffusionCLT.Section6.Prereq.GrowthSpace

@[expose] public section

open scoped ENNReal

/-- **Theorem A `t.C1beta`** (large-scale `C^{1,γ}` estimate), with `e.harmonic.coordinates`,
`e.Xgamma.Xi`, `e.flatness.at.every.scale` and `e.largescaleC1gamma`.

Readings as in `Frozen.Section6.c1beta_sharp` (field, growth space, balls, solutions).

* **Order of constants.** `C(α, γ, σ, ν, c⋆, K, d)` after all its parameters and before the
  law; `X` after the law. One `C` serves the tail and the three estimates, as printed.
* `e.Xgamma.Xi` is stated literally: `X ≥ 2` is a measurable random variable and
  `P[X > t] ≤ C exp(-C⁻¹ (log t)^σ)` for every `t ≥ 2`.
* The three statements hold almost surely.
* Every printed power is `Real.rpow`. -/
theorem SuperdiffusionCLT.Frozen.Section6.c1beta
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∀ α γ σ : ℝ, 0 < γ → γ < 1 → 0 < σ → σ < 1 → 0 < α → α < (1 - σ) / 2 →
      ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
        ∀ cStar : ℝ, 0 < cStar →
          ∀ K : ℝ,
            ∃ C : ℝ, 1 ≤ C ∧
              ∀ (P : MeasureTheory.ProbabilityMeasure
                    (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
                (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
                (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
                (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K
                    hPrefix hJ2 hJ3 →
                ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                  Measurable X ∧ (∀ omega, 2 ≤ X omega) ∧
                  -- e.Xgamma.Xi
                  (∀ t : ℝ, 2 ≤ t →
                    P.toMeasure.real {omega | t < X omega} ≤
                      C * Real.exp (-(C⁻¹ * Real.log t ^ σ))) ∧
                  ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
                    -- Liouville theorem
                    (Module.finrank ℝ
                        (Submodule.span ℝ
                          (SuperdiffusionCLT.Section6.growthSpace
                            (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega)
                            γ)) = 1 + d ∧
                      ∀ γ' : ℝ, 0 < γ' → γ' < 1 →
                        SuperdiffusionCLT.Section6.growthSpace
                            (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega)
                            γ' =
                          SuperdiffusionCLT.Section6.growthSpace
                            (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega)
                            γ) ∧
                    -- e.flatness.at.every.scale
                    (∀ φ ∈ SuperdiffusionCLT.Section6.growthSpace
                          (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega) γ,
                      ∀ r : ℝ, X omega ≤ r →
                        (⨅ e : Homogenization.Vec d,
                            SuperdiffusionCLT.Section6.ballL2 r
                              (fun x => φ x - Homogenization.vecDot e x -
                                ∫ y, φ y ∂SuperdiffusionCLT.Section6.ballMeasure r)) ≤
                          ENNReal.ofReal (C * Real.log r ^ (-α)) *
                            SuperdiffusionCLT.Section6.ballL2 r φ) ∧
                    -- e.largescaleC1gamma
                    (∀ R : ℝ, X omega ≤ R →
                      ∀ (u : Homogenization.Vec d → ℝ)
                        (g : Homogenization.Vec d → Homogenization.Vec d),
                        SuperdiffusionCLT.Section6.IsBallSolution
                            (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega)
                            R u g →
                          ∃ φ ∈ SuperdiffusionCLT.Section6.growthSpace
                              (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega)
                              γ,
                            ∃ gφ : Homogenization.Vec d → Homogenization.Vec d,
                              SuperdiffusionCLT.Section6.IsEntireSolution
                                  (SuperdiffusionCLT.Section6.fullCoefficientRecentered
                                    nu omega) φ gφ ∧
                                ∀ r : ℝ, X omega ≤ r → r < R →
                                  SuperdiffusionCLT.Section6.ballGradL2 r
                                      (fun x => g x - gφ x) ≤
                                    ENNReal.ofReal (C * (r / R) ^ γ) *
                                      SuperdiffusionCLT.Section6.ballGradL2 R g)
    := by
  exact SuperdiffusionCLT.Section6.Root.c1beta_of_sharp d
    (SuperdiffusionCLT.Frozen.Section6.c1beta_sharp d hd)
