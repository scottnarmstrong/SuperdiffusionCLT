/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.ExitEstimateE
public import SuperdiffusionCLT.Frozen.Section7.Superdiffusivity
public import SuperdiffusionCLT.Section6.Prereq.FullField
public import SuperdiffusionCLT.Section8.Brownian.BrownianMotion
public import SuperdiffusionCLT.Section8.Brownian.HeatGenerator
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5
public import MarkovProcess.Feller.Semigroup
public import MarkovProcess.Semigroup.Generator
public import MarkovProcess.FiniteTime.ProjectiveFamily
public import MarkovProcess.Lifetime.ExitTime
public import MarkovProcess.Trajectory.Equivariance
public import MarkovProcess.Main
public import SuperdiffusionCLT.Section8.Prereq.FieldDiffusion

@[expose] public section

open scoped ZeroAtInfty NNReal ENNReal Topology

/-- **Lemma `l.exit.time.estimate`**,
with `e.tau.ep.def`, `e.tau.ep.relations` and the definition of `p^ε_U`.

Readings.

* The process is any continuous-path law `Q` of a semigroup `S` satisfying
  `IsDivergenceFormFeller (fullCoefficientRecentered nu ω) S` (the Feller process of
  `∇·(ν Id + k)∇`); `Q y` is its law started at `y`.
* `p^ε_{B₁}(t, x) = P^{x/ε}[T^ε_{B₁} ≤ t]` is read through `T^ε_U = τ_ε⁻¹ T_{ε⁻¹U}`
  (`e.tau.ep.relations`): the law `Q (ε⁻¹ • x)` of the unscaled process, the first exit time
  of the Euclidean ball `ε⁻¹ B₁ = {y | |ε y| < 1}`, and the time `τ_ε t₀`
  (`timeScale cStar ε`). `B_{1/2}` is the open Euclidean ball.
* `‖p^ε_{B₁}‖_{L^∞([0,t₀] × B_{1/2})}` is bounded at every `x ∈ B_{1/2}` and at `t = t₀`;
  `p^ε` is nondecreasing in `t`, so this is the printed supremum (and pointwise in `x`).
* "`𝒵` of `t.superdiffusivity`, enlarged if necessary" is an existential measurable `Z` with
  the printed tail `P[Z ≥ ξ] ≤ C exp(-C⁻¹ (log ξ)^β)` for `ξ ≥ 1`.
* **Order of constants.** `C(α, β, c⋆, ν, K, d)` and `c` after all their parameters and before
  the law; `Z` after the law. The printed `C` governs the tail of `Z`.
* Almost surely in the sample; the null set does
  not depend on `S`, `Q`, `ε`, `t₀`, `x`. -/
theorem SuperdiffusionCLT.Frozen.Section8.exit_time_estimate
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∀ α β : ℝ, 0 < α → α < 1 → 0 < β → β < 1 → β + 2 * α < 1 →
      ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
        ∀ cStar : ℝ, 0 < cStar →
          ∀ K : ℝ,
            ∃ C c : ℝ, 1 ≤ C ∧ 0 < c ∧
              ∀ (P : MeasureTheory.ProbabilityMeasure
                    (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
                (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
                (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
                (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K
                    hPrefix hJ2 hJ3 →
                ∃ Z : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                  Measurable Z ∧
                  (∀ ξ : ℝ, 1 ≤ ξ →
                    P.toMeasure {omega | ξ ≤ Z omega} ≤
                      ENNReal.ofReal (C * Real.exp (-(C⁻¹ * Real.log ξ ^ β)))) ∧
                  ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
                    ∀ (S : MarkovProcess.SubMarkovKernelSemigroup (Homogenization.Vec d))
                      (Q : Homogenization.Vec d →
                        MeasureTheory.Measure (MarkovProcess.ContinuousPath (Homogenization.Vec d))),
                      SuperdiffusionCLT.Section8.IsDivergenceFormFeller
                          (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega) S →
                      SuperdiffusionCLT.Section8.IsContinuousPathLaw S Q →
                      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → Z omega ≤ ε⁻¹ →
                        ∀ t₀ : ℝ, 0 < t₀ → t₀ ≤ 1 →
                          ∀ x : Homogenization.Vec d, Homogenization.vecNormSq x < (1 / 2) ^ 2 →
                            Q (ε⁻¹ • x)
                                {w | MarkovProcess.ContinuousPath.exitTime
                                    {y : Homogenization.Vec d | Homogenization.vecNormSq (ε • y) < 1} w ≤
                                  ENNReal.ofReal
                                    (SuperdiffusionCLT.Section8.timeScale cStar ε * t₀)} ≤
                              2 * ENNReal.ofReal
                                (Real.exp (-(c * min (t₀ ^ (-(1 / 2 : ℝ)))
                                  (|Real.log ε| ^ (α / 6)))))
    := by
  exact SuperdiffusionCLT.Section8.exitEst_exit_time_estimate d hd
    SuperdiffusionCLT.Frozen.Section7.superdiffusivity
