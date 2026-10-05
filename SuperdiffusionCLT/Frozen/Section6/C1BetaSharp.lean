/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Prereq.EuclidBall
public import SuperdiffusionCLT.Section6.Engine.SharpB
public import SuperdiffusionCLT.Frozen.Section6.SharpScaleInputs
public import SuperdiffusionCLT.Section6.Prereq.FullField
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5
public import Homogenization.Probability.IndependentSums.WeakOrlicz
public import Homogenization.PDE.Harmonic
public import SuperdiffusionCLT.Section6.Prereq.GrowthSpace

@[expose] public section

open scoped ENNReal

/-- **Proposition `p.C1beta.sharp`**.

Readings.

* The coefficient field is `fullCoefficientRecentered nu ω = ν Id + (k - k(0))`, the a.s.
  locally uniform limit of `a_L - k_L(0)`; it differs from the printed `a = ν Id + k` by the
  constant skew matrix `k(0)`, which changes no solution space, and the raw series for `k`
  diverges.
* `𝒜^{1+γ}(ℝ^d)` is `growthSpace a γ`, a set of a.e.-classes; "dimension `1+d`" is the
  `finrank` of its span; "does not depend on `γ`" is equality with every `γ' ∈ (0,1)`.
* Balls are Euclidean (`euclidBall`), norms volume-normalized (`ballMeasure`); `ℓ_e(x) = e·x`;
  `(φ)_{B_r}` is the `ballMeasure r`-average.
* `u ∈ 𝒜(B_R)` is `IsBallSolution a R u g` with weak gradient `g`; `∇φ` is a gradient `gφ`
  with `IsEntireSolution a φ gφ` (a.e. unique on every ball).
* **Order of constants.** `C(d)` first, as printed; C_tail after `γ, ρ, ν, c⋆, K` and before
  the law; `X` after the law. `log X ≤ O_{Γ_ρ}(C_tail)` is the one-sided `IsBigOWith`.
* The three statements hold almost surely.
* Every printed power is `Real.rpow`. -/
theorem SuperdiffusionCLT.Frozen.Section6.c1beta_sharp
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ γ ρ : ℝ, 0 < γ → γ < 1 → 0 < ρ → ρ < 1 →
        ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
          ∀ cStar : ℝ, 0 < cStar →
            ∀ K : ℝ,
              ∃ Ctail : ℝ, 0 < Ctail ∧
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
                    Measurable X ∧ (∀ omega, 1 ≤ X omega) ∧
                    Homogenization.IndependentSums.IsBigOWith P.toMeasure
                      (Homogenization.IndependentSums.gammaSigma ρ)
                      (fun omega => Real.log (X omega)) Ctail ∧
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
                      -- flatness at every scale
                      (∀ φ ∈ SuperdiffusionCLT.Section6.growthSpace
                            (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega) γ,
                        ∀ r : ℝ, X omega ≤ r →
                          (⨅ e : Homogenization.Vec d,
                              SuperdiffusionCLT.Section6.ballL2 r
                                (fun x => φ x - Homogenization.vecDot e x -
                                  ∫ y, φ y ∂SuperdiffusionCLT.Section6.ballMeasure r)) ≤
                            ENNReal.ofReal
                                (C * Real.log r ^ (-((1 - ρ) / 2)) * Real.log (Real.log r)) *
                              SuperdiffusionCLT.Section6.ballL2 r φ) ∧
                      -- large-scale C^{1,γ} estimate
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
  exact SuperdiffusionCLT.Section6.c1beta_sharp_of_inputs d hd
    (SuperdiffusionCLT.Frozen.Section6.sharp_scale_inputs d hd)
